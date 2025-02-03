/* prof-counter.c
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *
 * Using the var ptr mechanism to store profiling data.
 */

#include "ml-base.h"
#include "ml-values.h"
#include "ml-objects.h"
#include "ml-state.h"
#include <string.h>

#define MAX_COUNTERS 128

/* PCOUNTERa heap-allocated array of length COUNTER_LEN.
 */
Word_t         PROF_COUNTERS[MAX_COUNTERS] = { 0 };
static Int_t   COUNTER_LEN = 0;

/* ml_RunT_prof_counter_init: int -> unit
 *
 * initializes an array of counters of length `arg` and installs the pointer
 * at varReg. If the argument is less than or equal to 0, nothing is allocated
 * and varReg is not touched.
 */
ml_val_t _ml_RunT_prof_counter_clear (ml_state_t *msp, ml_val_t arg)
{
    Int_t length = INT_MLtoC(arg);
    if (length > MAX_COUNTERS) {
        Error ("prof_counter_init: length > MAX_COUNTERS");
    } else if (length > 0) {
        COUNTER_LEN = length;
        memset(PROF_COUNTERS, 0, length * sizeof(*PROF_COUNTERS));
    } else {
        COUNTER_LEN = 0;
        SayDebug ("prof_counter_init: length <= 0");
    }

    return ML_unit;
}

/* ml_RunT_prof_counter_read: unit -> int list
 *
 * read and reset the counters. If the counters are initialized, it releases the
 * memory and resets the varReg. If the counters are not initialized, it leaves
 * varReg unchanged and returns an empty list.
 */
ml_val_t _ml_RunT_prof_counter_read (ml_state_t *msp, ml_val_t arg)
{
    (void) arg;
    ml_val_t lst = LIST_nil;
    for (Int_t i = COUNTER_LEN - 1; i >= 0; i--) {
        Word_t curr = PROF_COUNTERS[i];
        LIST_cons(msp, lst, INT_CtoML(curr), lst);
    }
    return lst;
}


