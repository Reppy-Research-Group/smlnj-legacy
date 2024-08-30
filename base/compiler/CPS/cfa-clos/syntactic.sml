structure SyntacticInfo :> sig
  type t
  exception SyntacticInfo

  val calculate     : LabelledCPS.function -> t
  val typeof        : t -> LabelledCPS.lvar -> LabelledCPS.cty
  (* defSite x is the enclosing function of x's defintion site *)
  val defSite       : t -> LabelledCPS.lvar -> LabelledCPS.function
  val useSites      : t -> LabelledCPS.lvar -> LabelledCPS.FunSet.set
  val usePoints     : t -> LabelledCPS.lvar -> LabelledCPS.Set.set
  val knownFun      : t -> LabelledCPS.lvar -> LabelledCPS.function option
  val binderOf      : t -> LabelledCPS.function -> LabelledCPS.function option
  val fv            : t -> LabelledCPS.function -> LambdaVar.Set.set
  val groupOf       : t -> LabelledCPS.function -> Group.t
  val depthOf       : t -> LabelledCPS.function -> int
  val groupFV       : t -> Group.t -> LambdaVar.Set.set
  val groupFun      : t -> Group.t -> LabelledCPS.function vector
  val groupExp      : t -> Group.t -> LabelledCPS.cexp
  val enclosing     : t -> LabelledCPS.cexp -> LabelledCPS.function
  val enclosingUser : t -> LabelledCPS.cexp -> LabelledCPS.function
  val returnCont    : t -> LabelledCPS.cexp -> LabelledCPS.lvar option
  val appF          : t -> (LabelledCPS.function -> unit) -> unit
  val functions     : t -> LabelledCPS.function vector
  val groups        : t -> Group.t vector
  val numVars       : t -> int
  val dump          : t -> unit
end = struct
  structure LCPS = LabelledCPS
  structure LV   = LambdaVar

  type var_info = { ty: LCPS.cty, def: LCPS.function, uses: LCPS.Set.set,
                    knownfun: LCPS.function option }
  type fun_info = { binder: LCPS.function, fv: LV.Set.set, group: Group.t,
                    depth: int }
  type exp_info = { enclosing: LCPS.function }
  type grp_info = { functions: LCPS.function vector, fv: LV.Set.set,
                    exp: LCPS.cexp }

  datatype t = T of {
    funTbl: fun_info LCPS.FunTbl.hash_table,
    varTbl: var_info LV.Tbl.hash_table,
    expTbl: exp_info LCPS.Tbl.hash_table,
    grpTbl: grp_info Group.Tbl.hash_table,
    functions: LabelledCPS.function vector,
    groups: Group.t vector,
    lam0: LCPS.function
  }

  fun kindToCty (CPS.CONT | CPS.KNOWN_CONT) = CPS.CNTt
    | kindToCty _ = CPS.FUNt

  val add = LV.Set.add
  val subtract = LV.Set.subtract
  fun subtracts (set, xs) = foldr LV.Set.subtract' set xs
  fun addV (m, CPS.VAR v) = add (m, v)
    | addV (m, _) = m
  fun addVs (m, vs) = foldr (fn (v, m) => addV (m, v)) m vs

  exception SyntacticInfo
  fun calculate (cps: LCPS.function) : t =
    let
      val funTbl = LCPS.FunTbl.mkTable (32, SyntacticInfo)
      val varTbl = LV.Tbl.mkTable (32, SyntacticInfo)
      val expTbl = LCPS.Tbl.mkTable (32, SyntacticInfo)
      val grpTbl = Group.Tbl.mkTable (32, SyntacticInfo)
      val grps = ref ([]: Group.t list)
      fun prependGrp group = grps := group :: !grps

      fun newVar currF (var, ty) =
        LV.Tbl.insert varTbl
          (var, { ty=ty, def=currF, uses=LCPS.Set.empty, knownfun=NONE })

      fun newVarF currF (f as (kind, name, _, _, _)) =
        let val ty = kindToCty kind
        in  LV.Tbl.insert varTbl
              (name, { ty=ty, def=currF, uses=LCPS.Set.empty, knownfun=SOME f })
        end

      fun useVar exp (CPS.VAR var) =
            let val { ty, def, uses, knownfun } = LV.Tbl.lookup varTbl var
                  handle SyntacticInfo => 
                  (print (LV.lvarName var ^ " missing\n"); raise SyntacticInfo)
                val uses' = LCPS.Set.add (uses, exp)
            in  LV.Tbl.insert varTbl (var, 
                 { ty=ty, def=def, uses=uses', knownfun=knownfun })
            end
        | useVar _ _ = ()

      fun newGrp (label, bindings, fv, exp) =
        (Group.Tbl.insert grpTbl
           (Group.wrap label,
            { functions=Vector.fromList bindings, fv=fv, exp=exp }))

      fun walkF
        (parent, label, depth)
        (function as (kind, name, args, tys, body)) =
        let val () = ListPair.appEq (newVar function) (args, tys)
            val fv = subtracts (walkE (function, depth + 1) body, args)
        in  LCPS.FunTbl.insert funTbl
              (function, { binder=parent, fv=fv, group=Group.wrap label,
                           depth=depth });
            fv
        end
      and walkE (currF, depth) =
        let
          val newVar' = newVar currF
          val newVarF' = newVarF currF
          fun exp e =
            (LCPS.Tbl.insert expTbl (e, { enclosing=currF });
             case e
               of LCPS.FIX (label, bindings, cexp) =>
                    let val names = map #2 bindings
                        val () = app newVarF' bindings
                        val () = prependGrp (Group.wrap label)
                        val fvs = map (walkF (currF, label, depth)) bindings
                        val fv = foldr LV.Set.union LV.Set.empty fvs
                        val () =
                          newGrp (label, bindings, subtracts (fv, names), e)
                        val fv' = exp cexp
                    in  subtracts (LV.Set.union (fv', fv), names)
                    end
                | LCPS.APP (_, f, args) =>
                    (app (useVar e) (f :: args);
                     addVs (LV.Set.empty, f :: args))
                     (* LV.Set.fromList (f :: args)) *)
                | LCPS.RECORD (_, _, values, v, cexp) =>
                    let val used = map #2 values
                        val defd = map #1 values
                    in  newVar' (v, CPS.PTRt (CPS.RPT (List.length values)));
                        app (fn v => newVar' (v, CPSUtil.BOGt)) defd;
                        app (useVar e) used;
                        addVs (subtract (exp cexp, v), used)
                    end
                | LCPS.SELECT (_, _, arg, x, ty, cexp) =>
                    (useVar e arg; newVar' (x, ty);
                     addV (subtract (exp cexp, x), arg))
                | LCPS.OFFSET _ => raise Fail "offset"
                | LCPS.SWITCH (_, value, _, branches) =>
                    let val fvs = map exp branches
                        val fv  = foldr LV.Set.union LV.Set.empty fvs
                    in  useVar e value; addV (fv, value)
                    end
                | LCPS.BRANCH (_, _, args, _, expT, expF) =>
                    let val fv = LV.Set.union (exp expT, exp expF)
                    in  app (useVar e) args; addVs (fv, args)
                    end
                | LCPS.SETTER (_, _, args, cexp) =>
                    (app (useVar e) args; addVs (exp cexp, args))
                | LCPS.PURE   (label, CPS.P.MAKEREF, values, x, ty, cexp) =>
                    (* HACK: We need an address for the ref cell. *)
                    (* TODO: look into MKSPECIAL *)
                    (newVar' (label, CPSUtil.BOGt);
                     app (useVar e) values; newVar' (x, ty);
                     addVs (subtract (exp cexp, x), values))
                | (LCPS.LOOKER (_, _, values, x, ty, cexp) |
                   LCPS.ARITH  (_, _, values, x, ty, cexp) |
                   LCPS.PURE   (_, _, values, x, ty, cexp)) =>
                    (app (useVar e) values; newVar' (x, ty);
                     addVs (subtract (exp cexp, x), values))
                | LCPS.RCC (_, _, _, _, args, returns, cexp) =>
                    (app (useVar e) args; app newVar' returns;
                     addVs (subtracts (exp cexp, map #1 returns), args)))
        in
          exp
        end
      val (_, _, args, tys, body) = cps
    in
      ListPair.appEq (newVar cps) (args, tys);
      walkE (cps, 1) body;
      T {
        funTbl=funTbl,
        varTbl=varTbl,
        expTbl=expTbl,
        grpTbl=grpTbl,
        functions=Vector.fromList (map #1 (LCPS.FunTbl.listItemsi funTbl)),
        groups=Vector.fromList (List.rev (!grps)),
        lam0=cps
      }
    end

  fun typeof (T { varTbl, lam0, ... }) v =
    if LV.same (#2 lam0, v) then
      CPS.FUNt
    else
      #ty (LV.Tbl.lookup varTbl v)
      handle e => CPS.PTRt CPS.VPT

  fun enclosing (T { expTbl, ... }) e =
    #enclosing (LCPS.Tbl.lookup expTbl e)
    handle SyntacticInfo => (print "missing expression\n";
                             raise SyntacticInfo)

  fun enclosingUser (T { expTbl, funTbl, ...}) e =
    let fun walkUp (f as ((CPS.CONT | CPS.KNOWN_CONT), _, _, _, _)) =
              let val binder = #binder (LCPS.FunTbl.lookup funTbl f)
              in  walkUp binder
              end
          | walkUp f = f
    in  walkUp (#enclosing (LCPS.Tbl.lookup expTbl e))
    end

  fun returnCont t e =
    let val (_, _, args, tys, _) = enclosingUser t e
    in  case (args, tys)
          of (x::xs, CPS.CNTt::ts) => SOME x
           | _ => NONE
    end

  fun enclosingFs (t, usePoints) =
    LCPS.Set.foldl (fn (p, set) => LCPS.FunSet.add (set, enclosing t p))
                   LCPS.FunSet.empty
                   usePoints
  fun defSite (T { varTbl, expTbl, lam0, ... }) v =
    if LV.same (#2 lam0, v) then
      lam0
    else
      #def (LV.Tbl.lookup varTbl v)
  fun useSites (t as (T { varTbl, lam0, ... })) v =
    if LV.same (#2 lam0, v) then
      LCPS.FunSet.empty
    else
      enclosingFs (t, #uses (LV.Tbl.lookup varTbl v))
      handle SyntacticInfo => (print (LV.lvarName v ^ " missing\n");
                               raise SyntacticInfo)
  fun usePoints (t as (T { varTbl, lam0, ... })) v =
    if LV.same (#2 lam0, v) then
      LCPS.Set.empty
    else
      #uses (LV.Tbl.lookup varTbl v)
      handle SyntacticInfo => (print (LV.lvarName v ^ " missing\n");
                               raise SyntacticInfo)

  fun knownFun (t as (T { varTbl, lam0, ... })) v =
    if LV.same (#2 lam0, v) then
      SOME lam0
    else
      (* GROSS HACK *)
      #knownfun (LV.Tbl.lookup varTbl v)
      handle SyntacticInfo => (print (LV.lvarName v ^ " missing\n");
                               raise SyntacticInfo)

  fun binderOf (T { funTbl, lam0, ... }) f =
    if LV.same (#2 lam0, #2 f) then
      NONE
    else
      SOME (#binder (LCPS.FunTbl.lookup funTbl f))
  fun fv (T { funTbl, lam0, ... }) f =
    if LV.same (#2 lam0, #2 f) then
      LV.Set.empty
    else
      #fv (LCPS.FunTbl.lookup funTbl f)
  fun groupOf (T { funTbl, lam0, ... }) f =
    if LV.same (#2 lam0, #2 f) then
      raise Fail "looking up group of the top level lambda"
    else
      #group (LCPS.FunTbl.lookup funTbl f)
  fun depthOf (T { funTbl, lam0, ... }) f =
    if LV.same (#2 lam0, #2 f) then
      0
    else
      #depth (LCPS.FunTbl.lookup funTbl f)

  fun groupFV (T { grpTbl, ... }) g = #fv (Group.Tbl.lookup grpTbl g)
  fun groupFun (T { grpTbl, ... }) g = #functions (Group.Tbl.lookup grpTbl g)
  fun groupExp (T { grpTbl, ... }) g = #exp (Group.Tbl.lookup grpTbl g)

  fun appF (T { funTbl, ... }) f =
    LCPS.FunTbl.appi (fn (function, _) => f function) funTbl
  fun functions (T { functions, ... }) = functions
  fun groups (T { groups, ... }) = groups
  fun numVars (T { varTbl, ... }) = LV.Tbl.numItems varTbl

  fun dump (t as (T { funTbl, varTbl, ... })) =
    let val p = print
        fun lst xs = "[" ^ String.concatWith ", " xs ^ "]"
        val funName = LV.lvarName o (#2: LCPS.function -> LCPS.lvar)
        fun pF (function: LCPS.function, { binder, fv, group, depth }) =
          (p (concat ["fun ", funName function,
                      " of group ", Group.toString group,
                      " at depth ", Int.toString depth, ": "]);
           p ("inside " ^ funName binder);
           p "; ";
           p ("fv: " ^ lst (map LV.lvarName (LV.Set.listItems fv)));
           p "\n")
        fun pV (var, { ty, def, uses, knownfun }) =
          (p ("var " ^ LV.lvarName var ^ CPSUtil.ctyToString ty ^ ": ");
           (case knownfun
              of NONE => ()
               | SOME _ => p ("is known fun"));
           p ("defined in " ^ funName def ^ "; ");
           p ("used in " ^
              lst (map funName (LCPS.FunSet.listItems (enclosingFs (t, uses)))));
           p "\n")
    in  p "=========== Syntactic Info =============\n";
        LCPS.FunTbl.appi pF funTbl;
        LV.Tbl.appi pV varTbl;
        p "========================================\n"
    end
end
