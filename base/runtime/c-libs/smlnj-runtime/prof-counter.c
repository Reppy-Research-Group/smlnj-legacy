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

/* ml_RunT_prof_counter_init: int -> unit
 *
 * initializes an array of counters of length `arg` and installs the pointer
 * at varReg. If the argument is less than or equal to 0, nothing is allocated
 * and varReg is not touched.
 */
ml_val_t _ml_RunT_prof_counter_clear (ml_state_t *msp, ml_val_t arg)
{
    Word_t *counters   = PTR_MLtoC(Word_t, msp->ml_varReg);
    Word_t *curr_len_p = &counters[-1];
    Int_t  new_len = INT_MLtoC(arg);
    if (counters == NULL) {
        Error ("varReg uninitialized\n");
    }
    if (new_len > MAX_PROF_COUNTERS - 1) {
        Error ("prof_counter_init: length > MAX_PROF_COUNTERS\n");
    }

    if (new_len > 0) {
        *curr_len_p = new_len;
        memset(counters, 0, new_len * sizeof(*counters));
    } else {
        *curr_len_p = 0;
        SayDebug ("prof_counter_init: length <= 0\n");
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
    Word_t *counters = PTR_MLtoC(Word_t, msp->ml_varReg);
    Word_t length    = counters[-1];
    for (Int_t i = length - 1; i >= 0; i--) {
        Word_t curr = counters[i];
        LIST_cons(msp, lst, INT_CtoML(curr), lst);
    }
    return lst;
}


