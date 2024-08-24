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

  datatype fv = Var of LV.lvar * CPS.cty
              | CS  of LV.lvar * int * CPS.cty
              | Env of D.EnvID.t * LV.lvar list

  fun embed (Var (v, ty)) = D.Var (v, ty)
    | embed (CS (v, i, ty)) = D.Expand (v, i, ty)
    | embed (Env (e, _)) = D.EnvID e

  val fvToS = D.slotToString o embed

  fun spill syn (group, vs: fv list) : (D.slot list * D.slot list) =
    let
      val returnCont = S.returnCont syn (S.groupExp syn group)
      fun choose []        = ([D.Null, D.Null, D.Null], [])
        | choose [x]       = ([embed x, D.Null, D.Null], [])
        | choose [x, y]    = ([embed x, embed y, D.Null], [])
        | choose [x, y, z] = ([embed x, embed y, embed z], [])
        | choose (x::y::z::rest) = ([embed x, embed y], map embed (z :: rest))
      fun mergeLT (f, NONE) =
            let val depth = S.depthOf syn f
            in  SOME (depth, depth)
            end
        | mergeLT (f, SOME (fut, lut)) =
            let val depth = S.depthOf syn f
            in  SOME (Int.min (fut, depth), Int.max (lut, depth))
            end
      fun lifetimeOf (Var (v, _)) =
            let val fs = S.useSites syn v
                val lifetime = LCPS.FunSet.foldl mergeLT NONE fs
            in  Option.valOf lifetime
                (* v is free in a function, so useSite cannot be empty. *)
            end
        | lifetimeOf (CS (v, _, _)) =
            (case returnCont
               of SOME c => if LV.same (v, c) then
                              (~1, ~1) (* Top priority *)
                            else
                              lifetimeOf (Var (v, CPS.CNTt))
                | NONE => lifetimeOf (Var (v, CPS.CNTt)))
        | lifetimeOf (Env (e, vs)) =
            let val fs = foldl
                  (fn (v, fs) => LCPS.FunSet.union (S.useSites syn v, fs))
                  LCPS.FunSet.empty vs
                val lifetime = LCPS.FunSet.foldl mergeLT NONE fs
            in  Option.valOf lifetime (* vs is non-empty *)
            end
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
        fun require v =
          (case S.knownFun syn v
             of SOME f =>
                  let val D.Closure {code, env} = LCPS.FunMap.lookup (repr, f)
                      handle e => (print (LV.lvarName v ^ " trying\n"); raise e)
                    val () = print (LV.lvarName v ^ "known fun\n")
                      val funty = (case #1 f
                                     of (CPS.KNOWN_CONT | CPS.CONT) => CPS.CNTt
                                      | _ => CPS.FUNt)
                      val fields =
                        (case env
                           of (D.Boxed _ | D.MutRecBox _) => [Var (v, ty)]
                            | D.Flat slots =>
                                List.mapPartiali
                                  (fn (_, (D.Code _ | D.Null)) => NONE
                                    | (i, slot) => SOME (CS (v, i, ty))) slots)
                  in  fields
                  end
              | NONE =>
                  (case S.typeof syn v
                     of CPS.CNTt =>
                          [Var (v, CPS.CNTt),
                           CS (v, 0, ty), CS (v, 1, ty), CS (v, 2, ty)]
                      | ty => [Var (v, ty)]))
        fun collect (v, vs) = require v @ vs
    in  LV.Set.foldr collect [] fv
    end

  fun collect syn (group, (repr, allo, heap)) =
    let val functions = S.groupFun syn group
        val (fv, ufv) = LV.Set.partition (isMLValue syn) (S.groupFV syn group)
        val fv = trueFV (fv, syn, repr)
        handle e => (print ("In " ^( String.concatWithMap "," (LV.lvarName o #2)
        (Vector.toList functions)) ^ "\n");raise  e)
        val (fv, envs, heap) =
          if LV.Set.isEmpty ufv then
             (fv, [], heap)
          else
             let val boxedE = EnvID.new ()
                 val ufv = LV.Set.listItems ufv
                 val heap = EnvID.Map.insert
                             (heap, boxedE, D.RawBlock (ufv, CPS.RK_RAW64BLOCK))
             in  (Env (boxedE, ufv) :: fv, [boxedE], heap)
             end
    in  case functions
          of #[f as ((CPS.CONT | CPS.KNOWN_CONT), name, _, _, _)] =>
               (case spill syn (group, fv)
                  of (callees, []) =>
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
                   val slots = D.Code f :: map embed fv
                   val heap = EnvID.Map.insert (heap, envID, D.Record slots)
                   val allo = Group.Map.insert (allo, group, envs @ [envID])
                   val cl = D.Closure
                     { code=D.SelectFrom {env=0, selects=[0]},
                       env=D.Boxed envID }
                   val repr = LCPS.FunMap.insert (repr, f, cl)
               in  (repr, allo, heap)
               end
           | _ => (* General mutual recursion *)
               let val sharedE = EnvID.new ()
                   val sharedV = map embed fv
                   val heap = EnvID.Map.insert (heap, sharedE, D.Record sharedV)
                   fun clos (f as (_, name, _, _, _)) =
                     (f, EnvID.wrap name, [D.Code f, D.EnvID sharedE])
                   val closures = Vector.map clos functions
                   val (heap, repr) =
                     Vector.foldl (fn ((f, e, s), (heap, repr)) =>
                       let val heap = EnvID.Map.insert (heap, e, D.Record s)
                           val cl = D.Closure
                             { code=D.SelectFrom { env=0, selects=[0] },
                               env=D.MutRecBox e }
                           val repr = LCPS.FunMap.insert (repr, f, cl)
                       in  (heap, repr)
                       end) (heap, repr) closures
                   val allo = Group.Map.insert
                     (allo, group, envs @ (sharedE :: mapL #2 closures))
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
