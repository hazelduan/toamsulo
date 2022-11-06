
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE   16

#define RESERV_INT_SIZE    5
#define RESERV_FP_SIZE     3
#define FU_INT_SIZE        3
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     5
#define FU_FP_LATENCY      7

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {
  bool is_done;
  if ((fetch_index == sim_insn) && (instr_queue_size == 0)) {
    is_done = true;
  } else {
    is_done = false;
  }//the num of insn is exactly the last fetch one and it is executed completely, then the simulation is completely done.
  return is_done;//ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {
  int i, j;
  if (commonDataBus != NULL) {
    if (current_cycle >= commonDataBus->tom_cdb_cycle + 1) {  //maybe 2 insns W in the same stage and need to stall for broadcast 
        
      for (i = 0; i < RESERV_FP_SIZE; i++) {
        if (reservFP[i] == commonDataBus) {
          reservFP[i] = NULL;
          continue;
        }
        for (j = 0; j < 3; j++) {
          if (reservFP[i]->Q[j] == commonDataBus) {
            reservFP[i]->Q[j] = NULL;
          }//update FP RS Qj
        }
      }//update FP RS
      for (i = 0; i < RESERV_INT_SIZE; i++) {
        if (reservINT[i] == commonDataBus) {
          reservINT[i] = NULL;
          continue;
        }
        for (j = 0; j < 3; j++) {
          if (reservINT[i]->Q[j] == commonDataBus) {
            reservINT[i]->Q[j] = NULL;
          }//update INT RS Qj
        }
      }// update INT RS
      for (i = 0; i < MD_TOTAL_REGS; i++) {
        if (map_table[i] == commonDataBus) {
          map_table[i] = NULL
        }
      }//update map table
      commonDataBus = NULL;
    }
  }
  /* ECE552: YOUR CODE GOES HERE */
}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {
//separate to INT and FP 
  int i, j;
  int oldest_num = 0, oldest_FP = 0, oldest_INT = 0;
  instruction_t* insn_FU_oldest;
  instruction_t* insn_FP_oldest;
  instruction_t* insn_INT_oldest;
  instruction_t* insn_current;
  insn_FU_oldest = NULL;//initialize oldest as NULL
  insn_FP_oldest = NULL;
  insn_INT_oldest = NULL;

  for (i = 0; i < FU_FP_SIZE; i++){
    if (current_cycle >= fuFP[i]->tom_execute_cycle + FU_FP_LATENCY ) { //maybe wait for CDB in use
      insn_current = fuFP[i];
      if (insn_FP_oldest == NULL) {
        insn_FP_oldest = fuFP[i];
      } else {
        if (insn_current->index < insn_FP_oldest->index) {
        insn_FP_oldest = insn_current;
        oldest_FP = i;
        }
      } 
    }
  }
  for (i = 0; i < FU_INT_SIZE; i++) {
    if (current_cycle >= fuINT[i]->tom_execute_cycle + FU_INT_LATENCY ) {// maybe wait for CDB in use
      if (WRITES_CDB(fuINT[i]->op)) {
        insn_current = fuINT[i];
        if (insn_INT_oldest == NULL) {
          insn_INT_oldest = fuINT[i];
        } else {
          if (insn_current->index < insn_INT_oldest->index) {
          insn_INT_oldest = insn_current;
          oldest_INT = i;
          }
        }
      } else { //store, don't need CDB, retire
        for (j = 0; j < RESERV_INT_SIZE; j++ ) {
          if (reservINT[j] == fuINT[i]) {
            reservINT[j] =0;
          }
        }
        fuINT[i] = 0;//maybe move it to push to CDB?
      }
    }
  }
  //to CDB, clear the insn in FU
  if (commonDataBus == NULL) {
    if (insn_INT_oldest->index < insn_FP_oldest->index) {
      insn_FU_oldest = insn_INT_oldest;
      oldest_num = oldest_INT;
      commonDataBus = insn_FU_oldest;
      commonDataBus->tom_cdb_cycle = current_cycle;
      fuINT[oldest_num] = NULL;
    } else {
      insn_FU_oldest = insn_FP_oldest;
      oldest_num = oldest_FP;
      commonDataBus = insn_FU_oldest;
      commonDataBus->tom_cdb_cycle = current_cycle;
      fuFP[oldest_num] = NULL;
    }
  }
}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {
//separate to FP and INT
  int i, j;
  bool operands_ready = true;
  //instruction_t* oldest_to_exe = NULL;
  instruction_t* oldest_to_exe_FP = NULL;
  instruction_t* oldest_to_exe_INT = NULL;
//find the oldest insn ready to exe
  for (i = 0; i < RESERV_FP_SIZE; i++) {
    if (current_cycle >= reservFP[i]->tom_issue_cycle + 1) {
      for (j = 0; j < 3; j++) {
        if (reservFP[i]->Q[j] != NULL) {
          if (commonDataBus != reservFP[i]->Q[j]) {
            operands_ready = false;
            break;
          }
        }
      }
      if (operands_ready) {
        if (oldest_to_exe_FP == NULL) {
          oldest_to_exe_FP = reservFP[i];
        } else {
          if (reservFP[i]->index < oldest_to_exe_FP->index) {
            oldest_to_exe_FP = reservFP[i];
          }
        }
      
      }
    }   
  }
  for (i = 0; i < RESERV_INT_SIZE; i++) {
    if (current_cycle >= reservINT[i]->tom_issue_cycle + 1) {
      for (j = 0; j < 3; j++) {
        if (reservINT[i]->Q[j] != NULL) {
          if (commonDataBus != reservINT[i]->Q[j]) {
            operands_ready = false;
            break;
          }
        }
      }
      if (operands_ready) {
        if (oldest_to_exe_INT == NULL) {
          oldest_to_exe_INT = reservFP[i];
        } else {
          if (reservFP[i]->index < oldest_to_exe_INT->index) {
            oldest_to_exe_INT = reservFP[i];
          }
        }
      }
    } 
  }
  //push to FU
  for (i = 0; i < FU_FP_SIZE; i++) {
    if (fuFP[i] == NULL) {
      if (oldest_to_exe_FP != NULL) {
        fuFP[i] = oldest_to_exe_FP;
        fuFP[i]->tom_execute_cycle = current_cycle;
      }
    }
  }
  for (i = 0; i < FU_INT_SIZE; i++) {
    if (fuINT[i] == NULL) {
      if (oldest_to_exe_INT != NULL) {
        fuINT[i] = oldest_to_exe_INT;
        fuINT[i]->tom_execute_cycle = current_cycle;
      }
    }
  }
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);

  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  
  int cycle = 1;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */

     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
  }
  
  return cycle;
}
