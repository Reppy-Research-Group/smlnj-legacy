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

/* COUNTER_PTR points to a heap-allocated array of length COUNTER_LEN.
 * Invariant: (COUNTER_LEN == 0) <--> (COUNTER_PTR == NULL)
 */
static Word_t *COUNTER_PTR = NULL;
static Int_t   COUNTER_LEN = 0;

/* ml_RunT_prof_counter_init: int -> unit
 *
 * initializes an array of counters of length `arg` and installs the pointer
 * at varReg. If the argument is less than or equal to 0, nothing is allocated
 * and varReg is not touched.
 */
ml_val_t _ml_RunT_prof_counter_init (ml_state_t *msp, ml_val_t arg)
{
    if (COUNTER_PTR != NULL) {
        FREE(COUNTER_PTR);
        COUNTER_PTR = NULL;
        COUNTER_LEN = 0;
    }

    Int_t length = INT_MLtoC(arg);
    if (length > 0) {
        COUNTER_PTR = NEW_VEC(Word_t, length);
        COUNTER_LEN = length;
        memset(COUNTER_PTR, 0, COUNTER_LEN * sizeof(*COUNTER_PTR));
        msp->ml_varReg = PTR_CtoML(COUNTER_PTR);
    } else {
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
    if (COUNTER_PTR != NULL
        && (PTR_MLtoC(void *, msp->ml_varReg) != (void *) COUNTER_PTR)) {
        SayDebug ("prof_counter_read: varReg and COUNTER_PTR inconsistent");
    }

    ml_val_t lst = LIST_nil;
    for (Int_t i = COUNTER_LEN - 1; i >= 0; i--) {
        ASSERT(COUNTER_PTR != NULL);

        Word_t curr = COUNTER_PTR[i];
        LIST_cons(msp, lst, INT_CtoML(curr), lst);
    }

    if (COUNTER_PTR != NULL) {
        FREE(COUNTER_PTR);
        msp->ml_varReg = ML_unit;
        COUNTER_PTR = NULL;
        COUNTER_LEN = 0;
    }

    return lst;
}


