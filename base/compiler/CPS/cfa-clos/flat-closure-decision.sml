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

  datatype fv = Var of LV.lvar
              | Env of D.EnvID.t * LV.lvar list

  fun embed (Var v) = D.Var v
    | embed (Env (e, _)) = D.EnvID e

  fun spill syn (vs: fv list) : (D.slot list * D.slot list) =
    let
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
      fun lifetimeOf (Var v) =
            let val fs = S.useSites syn v
                val lifetime = LCPS.FunSet.foldl mergeLT NONE fs
            in  Option.valOf lifetime
                (* v is free in a function, so useSite cannot be empty. *)
            end
        | lifetimeOf (Env (e, vs)) =
            let val fs = foldl
                  (fn (v, fs) => LCPS.FunSet.union (S.useSites syn v, fs))
                  LCPS.FunSet.empty vs
                val lifetime = LCPS.FunSet.foldl mergeLT NONE fs
            in  Option.valOf lifetime (* vs is non-empty *)
            end
      val vs = map (fn v => (v, lifetimeOf v)) vs
      fun gt ((v, (fut1, lut1)), (w, (fut2, lut2)))=
        if lut1 = lut2 then fut2 >= fut1 else lut1 >= lut2
      val vs = map #1 (ListMergeSort.sort gt vs)
    in
      choose vs
    end

  fun mapL f vector = Vector.foldr (fn (v, xs) => f v :: xs) [] vector
  val _ = mapL : ('a -> 'b) -> 'a vector -> 'b list

  fun collect syn (group, (repr, allo, heap)) =
    let val functions = S.groupFun syn group
        val fv = LV.Set.toList (S.groupFV syn group)
        val (fv, ufv) = List.partition (isMLValue syn) fv
        val (fv, envs, heap) =
          (case ufv
             of [] => (map Var fv, [], heap)
              | _  =>
                  let val boxedE = EnvID.new ()
                      val boxedV = map Var ufv
                      val heap = EnvID.Map.insert (heap, boxedE, map D.Var ufv)
                  in  (Env (boxedE, ufv) :: map Var fv, [boxedE], heap)
                  end)
    in  case functions
          of #[f as ((CPS.CONT | CPS.KNOWN_CONT), name, _, _, _)] =>
               (case spill syn fv
                  of (callees, []) =>
                       let val slots = D.Code name :: callees
                           val repr = LCPS.FunMap.insert (repr, f, slots)
                           val allo = Group.Map.insert (allo, group, envs)
                       in  (repr, allo, heap)
                       end
                   | (callees, spilled) =>
                       let val env = EnvID.new ()
                           val heap = EnvID.Map.insert (heap, env, spilled)
                           val allo = Group.Map.insert (allo, group, envs@[env])
                           val repr = LCPS.FunMap.insert
                             (repr, f, D.Code name :: callees @ [D.EnvID env])
                       in  (repr, allo, heap)
                       end)
           | #[f as (_, name, _, _, _)] =>
               let val envID = EnvID.new ()
                   val slots = D.Code name :: map embed fv
                   val heap = EnvID.Map.insert (heap, envID, slots)
                   val allo = Group.Map.insert (allo, group, envs @ [envID])
                   val repr = LCPS.FunMap.insert (repr, f, [D.EnvID envID])
               in  (repr, allo, heap)
               end
           | _ => (* General mutual recursion *)
               let val sharedE = EnvID.new ()
                   val sharedV = map embed fv
                   val heap = EnvID.Map.insert (heap, sharedE, sharedV)
                   fun clos (f as (_, name, _, _, _)) =
                     (f, EnvID.new (), [D.Code name, D.EnvID sharedE])
                   val closures = Vector.map clos functions
                   val (heap, repr) =
                     Vector.foldl (fn ((f, e, s), (heap, repr)) =>
                       let val heap = EnvID.Map.insert (heap, e, s)
                           val repr = LCPS.FunMap.insert (repr, f, [D.EnvID e])
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
