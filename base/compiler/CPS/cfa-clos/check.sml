structure InvariantChecker :> sig
  val check : ClosureDecision.t * SyntacticInfo.t -> unit
end = struct
  structure D = ClosureDecision
  structure LCPS = LabelledCPS
  structure S = SyntacticInfo
  structure EnvID = D.EnvID
  structure LV = LambdaVar

  val pr = app print

  (* For each env record, either the function is creating it, or the parent has
   * access to it. *)
  fun checkSharing (dec as D.T {repr, allo, heap}, syn, grp) =
    let val functions = S.groupFun syn grp
        val parent = S.enclosing syn (S.groupExp syn grp)

        fun lookupEnv e =
          (case EnvID.Map.find (heap, e)
             of SOME obj => obj
              | NONE => raise Fail (concat [EnvID.toString e, " not found!"]))

        fun lookupRepr f =
          (case LCPS.FunMap.find (repr, f)
             of SOME clo => clo
              | NONE => raise Fail (concat [LV.lvarName (#2 f), " not found!"]))

        fun lookupAllo g =
          (case Group.Map.find (allo, g)
             of SOME allos => allos
              | NONE => raise Fail (concat [Group.toString g, " not found!"]))

        fun slotsOf (D.Record slots) = slots
          | slotsOf (D.RawBlock _) = []

        fun allReachableEnvs slots =
          let fun dfs (seen, []) = seen
                | dfs (seen, slot :: slots) =
                    (case slot
                       of D.EnvID e =>
                            if EnvID.Set.member (seen, e) then
                              dfs (seen, slots)
                            else
                              dfs (EnvID.Set.add (seen, e),
                                   slotsOf (lookupEnv e) @ slots)
                        | _ => dfs (seen, slots))
          in  dfs (EnvID.Set.empty, slots)
          end

        val inContext =
          let val D.Closure { code, env } = lookupRepr parent
          in  case env
                of D.Boxed e => allReachableEnvs [D.EnvID e]
                 | D.Flat slots =>  allReachableEnvs slots
          end

        val allocating = lookupAllo grp

        fun checkE env =
          if List.exists (fn e => EnvID.same (env, e)) allocating then
            ()
          else if EnvID.Set.member (inContext, env) then
            ()
          else 
            (case S.knownFun syn (EnvID.unwrap env)
               of SOME f =>
                    if LV.same (#2 (valOf (S.binderOf syn f)), #2 parent) then
                      ()
                    else
                      raise Fail (concat [
                        EnvID.toString env, " is neither being allocated nor in scope."
                      ])
                | NONE =>
                      raise Fail (concat [
                        EnvID.toString env, " is neither being allocated nor in scope."
                      ]))

        fun checkEachF f =
          let val D.Closure { code, env } = lookupRepr f
          in  case env
                of D.Boxed e => checkE e
                 | D.Flat slots =>
                     List.app (fn (D.EnvID e) => checkE e | _ => ()) slots
          end

        fun checkAllocate env =
          (case lookupEnv env
             of D.Record slots =>
                  List.app (fn (D.EnvID e) => checkE e | _ => ()) slots
              | D.RawBlock _ => ())

    in  Vector.app checkEachF functions;
        app checkAllocate allocating
    end
    handle e =>
      let val functions = S.groupFun syn grp
          val parent = S.enclosing syn (S.groupExp syn grp)
          
          val () = pr ["Parent environment:\n"]
          val () = D.dumpOne (dec, syn, S.groupOf syn parent)
          val () = pr ["\nOffending environment:\n"]
          val () = D.dumpOne (dec, syn, grp)
      in  raise e
      end

  fun checkAllSharing (dec, syn) =
    Vector.app (fn grp =>
      let val parent = S.enclosing syn (S.groupExp syn grp)
      in if LV.same (#2 parent, #2 (S.topLevel syn)) then
           ()
         else
           checkSharing (dec, syn, grp)
      end) (S.groups syn)

  fun check (dec, syn) =
    (checkAllSharing (dec, syn);
     ())
end
