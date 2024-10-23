/* gc-counter.c
 *
 * COPYRIGHT (c) 2022 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Some counters for measuring allocation rates, etc.  Note that these
 * are not part of the distribution, but are just defined in this branch
 * for research purposes.
 */

#include "ml-base.h"
#include "ml-values.h"
#include "ml-state.h"
#include "vproc-state.h"
#include "heap.h"
#include "ml-objects.h"
#include "cntr.h"
#include "cfun-proto-list.h"

static Unsigned32_t numGCs[MAX_NUM_GENS+1];

/* _ml_RunT_gc_counter_reset : bool -> unit
 *
 * reset the counters.  If the flag is true, the we force a GC of all
 * generations before resetting.
 */
ml_val_t _ml_RunT_gc_counter_reset (ml_state_t *msp, ml_val_t arg)
{
#ifdef GC_STATS
    heap_t	*heap = msp->ml_heap;

    /* check if a full GC is requested */
    if (arg == ML_true) {
        // collect all generations
        InvokeGCWithRoots (msp, heap->numGens, &arg, NIL(ml_val_t *));
    } else {
        // minor collection
        InvokeGCWithRoots (msp, 0, &arg, NIL(ml_val_t *));
    }

    /* we clear the allocation counters and record the number of collections so far. */
    CNTR_ZERO(&(heap->numAlloc));
    numGCs[0] = heap->numMinorGCs;
    for (int i = 0;  i < heap->numGens;  ++i) {
        gen_t *g = heap->gen[i];
        numGCs[i+1] = g->numGCs;
        for (int j = 0;  j < NUM_ARENAS;  ++j) {
            CNTR_ZERO(&(heap->numCopied[i][j]));
        }
    }

    return ML_unit;
#endif
}

/* _ml_RunT_gc_counter_read : unit -> (Word.word * Word.word * Word.word list)
 *
 * read the counters.  The results are:
 *
 *      # bytes allocated (scaled by 1024 on 32-bit machines)
 *      # bytes promoted to first generation (scaled by 1024 on 32-bit machines)
 *      # of collections in a list `[n0, n1, n2, ...]`, where ni is the number of
 *      times generation i has been collected since the "reset" call.
 */
ml_val_t _ml_RunT_gc_counter_read (ml_state_t *msp, ml_val_t arg)
{
#ifdef GC_STATS
    heap_t	*heap = msp->ml_heap;

    /* count the number of bytes allocated since the last GC or reset */
    Addr_t nbytesAlloc = (Addr_t)(msp->ml_allocPtr) - (Addr_t)(heap->allocBase);
    CNTR_INCR(&(heap->numAlloc), nbytesAlloc);

    /* count the number of bytes promoted */
    cntr_t nP;
    CNTR_ZERO(&nP);
    for (int i = 0;  i < NUM_ARENAS;  ++i) {
        CNTR_ADD(&nP, &(heap->numCopied[0][i]));
    }
#ifdef SIZE_64
    ml_val_t nAlloc = INT_CtoML(heap->numAlloc.cnt);
    ml_val_t nPromote = INT_CtoML(nP.cnt);
#else /* 32-bit */
    ml_val_t nAlloc = INT_CtoML((Unsigned32_t)((heap->numAlloc.cnt + 512) / 1024));
    ml_val_t nPromote = INT_CtoML((Unsigned32_t)((nP.cnt + 512) / 1024));
#endif
    /* allocate number of GCs list */
    ml_val_t lp = LIST_nil;
    Unsigned32_t nGCs[MAX_NUM_GENS+1];
    nGCs[0] = heap->numMinorGCs - numGCs[0];
    if (nGCs[0] > 0) {
        /* allocate the list of number of collections */
        int n = 0;
        for (int i = 1;  i <= heap->numGens;  ++i) {
            nGCs[i] = heap->gen[i-1]->numGCs - numGCs[i];
            if (nGCs[i] > 0) { n = i; } else break;
        }
        for (int i = n;  i >= 0;  --i) {
            LIST_cons(msp, lp, INT_CtoML(nGCs[i]), lp);
        }
    }

    /* allocate result tuple */
    ml_val_t res;
    REC_ALLOC3(msp, res, nAlloc, nPromote, lp);

    return res;
#else
    ml_val_t res;
    REC_ALLOC3(msp, res, INT_CtoML(0), INT_CtoML(0), LIST_nil);
    return res;
#endif
}
