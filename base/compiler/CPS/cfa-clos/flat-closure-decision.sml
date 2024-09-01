structure FlatClosureDecision :> sig
  val produce : LabelledCPS.function * SyntacticInfo.t -> ClosureDecision.t
end = struct

  structure D = ClosureDecision
  structure EnvID = D.EnvID
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo

  val isFloatTy =
    (* FIXME *)
    (* if unboxedFloats then *)
      (fn (CPS.FLTt _) => true | _ => false)
    (* else *)
    (*   (fn _ => false) *)

  fun isUntaggedIntTy (CPS.NUMt {tag, ...}) = not tag
    | isUntaggedIntTy _ = false

  fun isUntaggedInt syn = isUntaggedIntTy o (S.typeof syn)

  fun isFloat syn = isFloatTy o (S.typeof syn)

  fun isMLValue syn v =
    (not (isUntaggedInt syn v)) andalso (not (isFloat syn v))

  type lifetime = int * int
  datatype fv = Var of LV.lvar * CPS.cty * lifetime
              | CS  of LV.lvar * int * CPS.cty * lifetime
              | Env of D.EnvID.t * lifetime

  fun embed (Var (v, ty, _)) = D.Var (v, ty)
    | embed (CS (v, i, ty, _)) = D.Expand (v, i, ty)
    | embed (Env (e, lt)) = D.EnvID e

  val fvToS = D.slotToString o embed

  fun spill syn (group, vs: fv list) : (D.slot list * D.slot list) =
    let
      val returnCont = S.returnCont syn (S.groupExp syn group)
      fun choose []        = ([D.Null, D.Null, D.Null], [])
        | choose [x]       = ([embed x, D.Null, D.Null], [])
        | choose [x, y]    = ([embed x, embed y, D.Null], [])
        | choose [x, y, z] = ([embed x, embed y, embed z], [])
        | choose (x::y::z::rest) = ([embed x, embed y], map embed (z :: rest))
      val depthOf = S.depthOf syn and useSites = S.useSites syn
      fun mergeLT (f, NONE) =
            let val depth = depthOf f
            in  SOME (depth, depth)
            end
        | mergeLT (f, SOME (fut, lut)) =
            let val depth = depthOf f
            in  SOME (Int.min (fut, depth), Int.max (lut, depth))
            end
      fun lifetimeOf (Var (_, _, lt)) = lt
        | lifetimeOf (CS (v, _, _, lt)) =
            (case returnCont
               of SOME c => if LV.same (v, c) then
                              (~1, ~1) (* Top priority *)
                            else
                              lt
                | NONE => lt)
        | lifetimeOf (Env (_, lt)) = lt
      val vs = map (fn v => (v, lifetimeOf v)) vs
      fun gt ((v, (fut1, lut1)), (w, (fut2, lut2)))=
        if lut1 = lut2 then fut2 > fut1 else lut1 > lut2
      val vs = map #1 (ListMergeSort.sort gt vs)
    in
      choose vs
    end

  fun mapL f vector = Vector.foldr (fn (v, xs) => f v :: xs) [] vector
  val _ = mapL : ('a -> 'b) -> 'a vector -> 'b list

  fun trueFV (fv, syn, repr) =
    let val ty = CPS.PTRt CPS.VPT
        fun require (v, lifetime) =
          (case S.knownFun syn v
             of SOME f =>
                  let val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
                      val funty = (case #1 f
                                     of (CPS.KNOWN_CONT | CPS.CONT) => CPS.CNTt
                                      | _ => CPS.FUNt)
                      val fields =
                        (case env
                           of (D.Boxed _) => [Var (v, ty, lifetime)]
                            | D.Flat slots =>
                                List.mapPartiali
                                  (fn (_, (D.Code _ | D.Null)) => NONE
                                    | (i, slot) =>
                                        SOME (CS (v, i, ty, lifetime))) slots)
                      (* NEVER needs to close over the code for a known fun *)
                  in  fields
                  end
              | NONE =>
                  (case S.typeof syn v
                     of CPS.CNTt =>
                          [Var (v, CPS.CNTt, lifetime),
                           CS (v, 0, ty, lifetime), CS (v, 1, ty, lifetime),
                           CS (v, 2, ty, lifetime)]
                      | ty => [Var (v, ty, lifetime)]))
        fun collect (v, vs) = require v @ vs
    in  foldr collect [] fv
    end

  fun joinLT [] = raise Fail "No LT"
    | joinLT (lt::lts) =
        foldl
          (fn ((fut1, lut1), (fut2, lut2)) =>
            (Int.min (fut1, fut2), Int.max (lut1, lut2))) lt lts

  fun collect syn (group, (repr, allo, heap)) =
    let val functions = S.groupFun syn group
        val fv : (LV.lvar * lifetime) list =
          LV.Map.listItemsi (S.groupFV syn group)
        val (fv, ufv) = List.partition (isMLValue syn o #1) fv
        val fv = trueFV (fv, syn, repr)
        handle e => (print ("In " ^( String.concatWithMap "," (LV.lvarName o #2)
        (Vector.toList functions)) ^ "\n");raise  e)
        val (fv, envs, heap) =
          let val (floats, ints) = List.partition (isFloat syn o #1) ufv
              fun add (rk, vs, fv, envs, heap) =
                if List.null vs then
                  (fv, envs, heap)
                else
                  let val boxedE = EnvID.new ()
                      val (vs, lts) = ListPair.unzip vs
                      val heap = EnvID.Map.insert
                        (heap, boxedE, D.RawBlock (vs, rk))
                  in  (Env (boxedE, joinLT lts) :: fv, boxedE :: envs, heap)
                  end
              val (fv, envs, heap) =
                add (CPS.RK_RAWBLOCK, ints, fv, [], heap)
              val (fv, envs, heap) =
                add (CPS.RK_RAW64BLOCK, floats, fv, envs, heap)
          in  (fv, envs, heap)
          end
        fun isKnown (f: LCPS.function) =
          let val name = #2 f
              fun isCall (LCPS.APP (_, CPS.VAR v, _)) = LV.same (v, name)
                | isCall _ = false
              val uses = S.usePoints syn name
          in  LCPS.Set.all isCall uses
          end
    in  case functions
          of #[f as (CPS.CONT, name, _, _, _)] =>
               (case spill syn (group, fv) of (callees, []) =>
                       let val cl = D.Closure
                             { code=D.Pointer name, env=D.Flat callees }
                           val repr = LCPS.FunMap.insert (repr, f, cl)
                           val allo = Group.Map.insert (allo, group, envs)
                       in  (repr, allo, heap)
                       end
                   | (callees, spilled) =>
                       let val env = EnvID.new ()
                           val heap = EnvID.Map.insert (heap, env, D.Record spilled)
                           val allo = Group.Map.insert (allo, group, envs@[env])
                           val cl = D.Closure
                             { code=D.Pointer name,
                               env=D.Flat (callees@[D.EnvID env]) }
                           val repr = LCPS.FunMap.insert (repr, f, cl)
                       in  (repr, allo, heap)
                       end)
           | #[f as (_, name, _, _, _)] =>
               let val envID = EnvID.wrap name
                   val slots = map embed fv
                   val (code, slots) =
                     if isKnown f then
                       (D.Direct f, slots)
                     else
                       (D.SelectFrom {env=0, selects=[0]}, D.Code f :: slots)
                   val (heap, allo, env) =
                     (case slots
                        of [] => (heap, allo, D.Flat [])
                         | _ =>
                             let val heap =
                                  EnvID.Map.insert (heap, envID, D.Record slots)
                                 val allo =
                                  Group.Map.insert (allo, group, envs @ [envID])
                             in  (heap, allo, D.Boxed envID)
                             end)
                   val cl = D.Closure { code=code, env=env }
                   val repr = LCPS.FunMap.insert (repr, f, cl)
               in  (repr, allo, heap)
               end
           | _ => (* General mutual recursion *)
               let val (sharedE, heap) =
                     (case fv
                        of [] => ([], heap)
                         | _ =>
                             let val sharedE = EnvID.new ()
                                 val sharedV = map embed fv
                                 val heap = EnvID.Map.insert
                                   (heap, sharedE, D.Record sharedV)
                             in  ([sharedE], heap)
                             end)
                   fun clos (f as (_, name, _, _, _)) =
                     (f, EnvID.wrap name, D.Code f :: map D.EnvID sharedE)
                   val closures = Vector.map clos functions
                   val (heap, repr) =
                     Vector.foldl (fn ((f, e, s), (heap, repr)) =>
                       let val heap = EnvID.Map.insert (heap, e, D.Record s)
                           val cl = D.Closure
                             { code=D.SelectFrom { env=0, selects=[0] },
                               env=D.Boxed e }
                           val repr = LCPS.FunMap.insert (repr, f, cl)
                       in  (heap, repr)
                       end) (heap, repr) closures
                   val allo = Group.Map.insert
                     (allo, group, envs @ sharedE @ mapL #2 closures)
               in  (repr, allo, heap)
               end
    end

  fun produce (lam0, syn) =
    let
      val (repr, allo, heap) =
        Vector.foldl (collect syn)
          (LCPS.FunMap.empty, Group.Map.empty, EnvID.Map.empty)
          (S.groups syn)
    in
      D.T { repr=repr, allo=allo, heap=heap }
    end
end
