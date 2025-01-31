structure Instrumentation :> sig
  datatype kind = Variable | Null | Record of shape
  withtype shape = kind list

  type info = (LambdaVar.lvar * kind) list

  val instrument : (CPS.function -> info) * CPS.function -> CPS.function
end = struct
  structure LV = LambdaVar

  datatype kind = Variable | Null | Record of shape
  withtype shape = kind list

  type info = (LambdaVar.lvar * kind) list

  datatype usage = Unused | Move | Compute | Both
  fun joinUsage (Unused, x) = x
    | joinUsage (x, Unused) = x
    | joinUsage (_, Both) = Both
    | joinUsage (Both, _) = Both
    | joinUsage (Move, Compute) = Both
    | joinUsage (Compute, Move) = Both
    | joinUsage (Compute, Compute) = Compute
    | joinUsage (Move, Move) = Move
  fun usageToString Unused = "unused"
    | usageToString Move   = "move"
    | usageToString Compute = "compute"
    | usageToString Both = "both"

  (* fun trace msgs = app print msgs *)
  fun trace _ = ()

  structure C :> sig
    type ctx

    val new : info -> ctx
    val visitSelect : ctx * int * CPS.value * LV.lvar -> ctx
    val visitRecord
      : ctx * CPS.record_kind * (CPS.value * CPS.accesspath) list * LV.lvar
     -> ctx
    val dump : ctx -> unit
    val recordCompute : ctx * LV.lvar -> ctx
    val loads : ctx -> usage LV.Map.map
    val allocs : ctx -> (LV.lvar * CPS.record_kind * int) list
  end = struct
    type ctx = {
      env: kind LV.Map.map,
      loads: usage LV.Map.map,
      allocs: (LV.lvar * CPS.record_kind * int) list
    }

    fun new (kinds: info) : ctx =
      { env=foldl LV.Map.insert' LV.Map.empty kinds,
        loads=LV.Map.empty,
        allocs=[] }

    val markUsage = LV.Map.insertWith joinUsage

    fun recordLoad (c as { env, loads, allocs }: ctx, v) =
      { env=env, loads=markUsage (loads, v, Unused), allocs=allocs }

    fun recordMove (c as { env, loads, allocs }: ctx, v) =
      if LV.Map.inDomain (loads, v) then
        { env=env, loads=markUsage (loads, v, Move), allocs=allocs }
      else
        c

    fun recordCompute (c as { env, loads, allocs }: ctx, v) =
      if LV.Map.inDomain (loads, v) then
        { env=env, loads=markUsage (loads, v, Compute), allocs=allocs }
      else
        c

    fun recordAlloc ({ env, loads, allocs }: ctx, name, kind, size) =
      { env=env, loads=loads, allocs=(name, kind, size)::allocs }

    fun visitSelect (c as { env, loads, allocs }: ctx, i, CPS.VAR src, dest) =
        (case LV.Map.find (env, src)
           of NONE => (trace [LV.lvarName src, " uninteresting\n"];
                       recordCompute (c, src))
            | SOME (Record kinds) =>
                let val kind = List.nth (kinds, i)
                               handle Subscript =>
                                 (trace [LV.lvarName src, " out of bound\n"];
                                  raise Subscript)
                in  { env=LV.Map.insert (env, dest, kind),
                      loads=markUsage (
                        markUsage (loads, src, Compute), dest, Unused
                      ),
                      allocs=allocs }
                end
            | SOME _ => (trace [LV.lvarName src, " coincidental\n"];
                         recordCompute (c, src)))
      | visitSelect (c, _, _, _) = c

    val tmpName = Symbol.varSymbol "tmpPath"
    fun mktmp () = LV.namedLvar tmpName

    fun visitRecord (c as { env, loads, allocs }: ctx, kind, fields, dest) =
      let fun doPath (k, x, CPS.OFFp 0, c) = k (c, x)
            | doPath (k, _, CPS.OFFp _, _) = raise Fail "no"
            | doPath (k, x, CPS.SELp (_, pth), c) =
                doPath (k, mktmp (), pth, recordCompute (c, x))
          fun doField k ((CPS.VAR x, pth), c) = doPath (k, x, pth, c)
            | doField k (_, c) = c
      in  case kind
            of (CPS.RK_VECTOR | CPS.RK_RECORD) =>
                 foldl (doField recordCompute) c fields
             | _ =>
                 let val c = foldl (doField recordMove) c fields
                 in  recordAlloc (c, dest, kind, List.length fields + 1)
                     (* + 1 for the header word *)
                 end
      end

    fun dump ({ env, loads, allocs }: ctx) =
      (print "== LOADS ==\n";
       LV.Map.appi (fn (name, usage) =>
         app print [LV.lvarName name, " : ", usageToString usage, "\n"]
       ) loads;
       print "== ALLOCS ==\n";
       List.app (fn (name, _, sz) =>
         app print [LV.lvarName name, " : ", Int.toString sz, "\n"]
       ) allocs;
       print "== END ==\n";
       ())

    fun loads (x: ctx) = #loads x
    fun allocs (x: ctx) = #allocs x
  end

  structure Code :> sig
    val schema1 : C.ctx -> CPS.cexp -> CPS.cexp
  end = struct
    open CPS
    val tmpName = Symbol.varSymbol "instrument"
    fun var () = LV.namedLvar tmpName

    val bogusTy = CPSUtil.BOGt
    val uintKd  = P.UINT (Target.mlValueSz)
    val uintTy  = { sz=Target.mlValueSz, tag=false }
    val uintCty = NUMt { sz=Target.mlValueSz, tag=false }

    fun getvar k =
      let val v = var ()
      in  LOOKER (P.GETVAR, [], v, bogusTy, k v)
      end

    fun num i = NUM { ival=IntInf.fromInt i, ty=uintTy }
    fun idx i = num (i * Target.mlValueSz div 8)

    fun increment (varptr, i, incr, cexp) =
      let val curr = var ()
          val new = var ()
      in  LOOKER (P.RAWLOAD { kind=uintKd }, [VAR varptr, idx i], curr, uintCty,
            PURE (P.PURE_ARITH { oper=P.ADD, kind=uintKd },
                  [VAR curr, num incr], new, uintCty,
              SETTER (P.RAWSTORE { kind=uintKd }, [VAR varptr, idx i, VAR new],
                      cexp)))
      end

    fun updateList xs =
      if List.all (fn x => x = 0) xs then
        Fn.id
      else
        fn cexp =>
         getvar (fn vptr =>
           List.foldri (fn (i, value, cexp) =>
             if value = 0 then
               cexp
             else
               increment (vptr, i, value, cexp)
           ) cexp xs
         )

    fun schema1 (ctx: C.ctx) =
      (* [#sz of closure allocation, #loads/compute, #loads/move, #loads/both] *)
      let val closureAllocs =
            foldl (fn ((_, _, sz), sum) => sz + sum) 0 (C.allocs ctx)
          val (compute, move, both) =
            LV.Map.foldl (fn (usage, (c, m, b)) =>
              (case usage
                 of Unused  => raise Fail "unused"
                  | Move    => (c, m + 1, b)
                  | Compute => (c + 1, m, b)
                  | Both    => (c, m, b + 1))
            ) (0, 0, 0) (C.loads ctx)
          val () = trace [String.concatWithMap "," Int.toString [closureAllocs,
          compute, move, both], "\n"]
      in  updateList [closureAllocs, compute, move, both]
      end
  end

  fun values (ctx, []) = ctx
    | values (ctx, CPS.VAR x :: vs) = values (C.recordCompute (ctx, x), vs)
    | values (ctx, _ :: vs) = values (ctx, vs)

  fun instrument (lookupInfo, (kind, name, args, tys, body)) =
    let fun fix (f as (kind, name, args, tys, body)) =
              let val ctx = C.new (lookupInfo f)
                  val () = trace ["IN ", LV.lvarName name, "\n"]
              in  (kind, name, args, tys, exp (ctx, body))
              end
        and exp (ctx, CPS.RECORD (kind, fields, name, e)) =
              let val e' = exp (C.visitRecord (ctx, kind, fields, name), e)
              in  CPS.RECORD (kind, fields, name, e')
              end
          | exp (ctx, CPS.SELECT (i, v, x, ty, e)) =
              let val e' = exp (C.visitSelect (ctx, i, v, x), e)
              in  CPS.SELECT (i, v, x, ty, e')
              end
          | exp (ctx, CPS.OFFSET _) = raise Fail "no"
          | exp (ctx, CPS.APP (f, args)) =
              let val ctx = values (ctx, f :: args)
                  (* val () = C.dump ctx *)
                  val hdr = Code.schema1 ctx
              in  hdr (CPS.APP (f, args))
              end
          | exp (ctx, CPS.FIX (functions, e)) =
              let val functions' = map fix functions
                  val e' = exp (ctx, e)
              in  CPS.FIX (functions', e')
              end
          | exp (ctx, CPS.SWITCH (v, id, exps)) =
              let val ctx = values (ctx, [v])
                  val exps' = map (fn e => exp (ctx, e)) exps
              in  CPS.SWITCH (v, id, exps')
              end
          | exp (ctx, CPS.BRANCH (br, args, id, e1, e2)) =
              let val ctx = values (ctx, args)
                  val e1' = exp (ctx, e1)
                  val e2' = exp (ctx, e2)
              in  CPS.BRANCH (br, args, id, e1', e2')
              end
          | exp (ctx, CPS.SETTER (st, args, e)) =
              let val ctx = values (ctx, args)
                  val e'  = exp (ctx, e)
              in  CPS.SETTER (st, args, e')
              end
          | exp (ctx, CPS.LOOKER (lk, args, x, ty, e)) =
              let val ctx = values (ctx, args)
                  val e'  = exp (ctx, e)
              in  CPS.LOOKER (lk, args, x, ty, e')
              end
          | exp (ctx, CPS.ARITH (ar, args, x, ty, e)) =
              let val ctx = values (ctx, args)
                  val e'  = exp (ctx, e)
              in  CPS.ARITH (ar, args, x, ty, e')
              end
          | exp (ctx, CPS.PURE (pr, args, x, ty, e)) =
              let val ctx = values (ctx, args)
                  val e'  = exp (ctx, e)
              in  CPS.PURE (pr, args, x, ty, e')
              end
          | exp (ctx, CPS.RCC (b, s, p, args, rets, e)) =
              let val ctx = values (ctx, args)
                  val e'  = exp (ctx, e)
              in  CPS.RCC (b, s, p, args, rets, e')
              end
        val body = exp (C.new [], body)
    in  (kind, name, args, tys, body)
    end

end
