(* /Users/byron/Documents/School/Research/master-thesis/benchmarks/programs/delta-blue/all.sml -- all sources for delta-blue *)
local
(******************** bmark.sig ********************)
(* bmark.sig
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

signature BMARK =
  sig
(* TODO: add some form of benchmark description *)

    (* the short name for the benchmark *)
    val name : string

    (* run the benchmark program for timing purposes (no output) *)
    val doit : unit -> unit

    (* run the benchmark program and direct its output to the specified
     * outstream.  This function can be used to verify that the benchmark
     * is producing the expected results.
     *)
    val testit : TextIO.outstream -> unit

  end
(******************** strength.sml ********************)
(* strength.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure Strength :> sig

    type t

    val required : t
    val strongPreferred : t
    val preferred : t
    val strongDefault : t
    val normal : t
    val weakDefault : t
    val weakest : t

    val same : t * t -> bool

    val stronger : t * t -> bool
    val weaker : t * t -> bool
    val weakestOf : t * t -> t
    val strongest : t * t -> t

    val nextWeaker : t -> t

    val toString : t -> string

  end = struct

    datatype t = Strength of int * string

    val required = Strength(0, "required")
    val strongPreferred = Strength(1, "strongPreferred")
    val preferred = Strength(2, "preferred")
    val strongDefault = Strength(3, "strongDefault")
    val normal = Strength(4, "normal")
    val weakDefault = Strength(5, "weakDefault")
    val weakest = Strength(6, "weakest")

    fun same (Strength(s1, _), Strength(s2, _)) = s1 = s2

    fun stronger (Strength(s1, _), Strength(s2, _)) = s1 < s2
    fun weaker (Strength(s1, _), Strength(s2, _)) = s1 > s2

    fun strongest (s1, s2) = if stronger(s1, s2) then s1 else s2
    fun weakestOf (s1, s2) = if weaker(s1, s2) then s1 else s2

    fun nextWeaker (Strength(0, _)) = strongPreferred
      | nextWeaker (Strength(1, _)) = preferred
      | nextWeaker (Strength(2, _)) = strongDefault
      | nextWeaker (Strength(3, _)) = normal
      | nextWeaker (Strength(4, _)) = weakDefault
      | nextWeaker (Strength(5, _)) = weakest
      | nextWeaker _ = raise Fail "Invalid call to nextWeaker()!"

    fun toString (Strength(_, name)) = name

  end
(******************** rep-types.sml ********************)
(* rep-types.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *
 * Internal representation of variables and constraints.
 *)

structure RepTypes =
  struct

    datatype variable = Variable of {
        name : string,
        value : int ref,
        constraints : constraint list ref,      (* constraints that depend on this variable *)
        determinedBy : constraint ref,          (* the constraint that determines
                                                 * the value of this variable.
                                                 *)
        walkStrength : Strength.t ref,          (* walkabout strength *)
        stay : bool ref,                        (* true if this is a planning-time constant *)
        mark : int ref                          (* used by the planner to mark constraints *)
      }

    and constraint = Constraint of {
        strength : Strength.t ref,
        isInput : bool,
        execute : constraint -> unit,
        isSatisfied : constraint -> bool,
        markUnsatisfied : constraint -> unit,
        addToGraph : constraint -> unit,
        removeFromGraph : constraint -> unit,
        chooseMethod : constraint * int -> unit,
        markInputs : constraint * int -> unit,
        inputsKnown : constraint * int -> bool,
        output : constraint -> variable,
        recalculate : constraint -> unit,
        inputsToString : constraint -> string
      }

    (* directions for binary constraints *)
    datatype direction = Backward | NoDirection | Forward

  end
(******************** constraint-base.sml ********************)
(* constraint-base.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

signature CONSTRAINT_BASE =
  sig

    type t = RepTypes.constraint

    val null : t

    val same : t * t -> bool

    val getStrength : t -> Strength.t
    val setStrength : t * Strength.t -> unit

    val isInput : t -> bool

    val execute : t -> unit
    val isSatisfied : t -> bool
    val markUnsatisfied : t -> unit
    val addToGraph : t -> unit
    val removeFromGraph : t -> unit
    val chooseMethod : t * int -> unit
    val markInputs : t * int -> unit
    val inputsKnown : t * int -> bool
    val output : t -> RepTypes.variable
    val recalculate : t -> unit
    val inputsToString : t -> string

  end

structure ConstraintBase : CONSTRAINT_BASE =
  struct

    datatype t = datatype RepTypes.constraint

    val null = let
          fun fail name _ = raise Fail name
          in
            Constraint{
                strength = ref Strength.required,
                isInput = false,
                execute = fail "execute",
                isSatisfied = fail "isSatisfied",
                markUnsatisfied = fail "markUnsatisfied",
                addToGraph = fail "addToGraph",
                removeFromGraph = fail "removeFromGraph",
                chooseMethod = fail "chooseMethod",
                markInputs = fail "markInputs",
                inputsKnown = fail "inputsKnown",
                output = fail "output",
                recalculate = fail "recalculate",
                inputsToString = fail "inputsToString"
              }
          end

    fun same (Constraint{strength=a, ...}, Constraint{strength=b, ...}) = (a = b)

    fun getStrength (Constraint{strength, ...}) = !strength
    fun setStrength (Constraint{strength, ...}, s) = strength := s

    fun isInput (Constraint{isInput, ...}) = isInput

    fun execute (c as Constraint{execute, ...}) = execute c
    fun isSatisfied (c as Constraint{isSatisfied, ...}) = isSatisfied c
    fun markUnsatisfied (c as Constraint{markUnsatisfied, ...}) = markUnsatisfied c
    fun addToGraph (c as Constraint{addToGraph, ...}) = addToGraph c
    fun removeFromGraph (c as Constraint{removeFromGraph, ...}) = removeFromGraph c
    fun chooseMethod (c as Constraint{chooseMethod, ...}, mark) = chooseMethod (c, mark)
    fun markInputs (c as Constraint{markInputs, ...}, mark) = markInputs (c, mark)
    fun inputsKnown (c as Constraint{inputsKnown, ...}, mark) = inputsKnown (c, mark)
    fun output (c as Constraint{output, ...}) = output c
    fun recalculate (c as Constraint{recalculate, ...}) = recalculate c
    fun inputsToString (c as Constraint{inputsToString, ...}) = inputsToString c

  end
(******************** variable.sml ********************)
(* variable.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure Variable : sig

    type t

    val new : string * int * Strength.t -> t

    val toString : t -> string

    val addConstraint : t * ConstraintBase.t -> unit
    val removeConstraint : t * ConstraintBase.t -> unit
    val getConstraints : t -> ConstraintBase.t list

    val getValue : t -> int
    val setValue : t * int -> unit

    val getDeterminedBy : t -> ConstraintBase.t
    val setDeterminedBy : t * ConstraintBase.t -> unit

    val getMark : t -> int
    val setMark : t * int -> unit

    val getWalkStrength : t -> Strength.t
    val setWalkStrength : t * Strength.t -> unit

    val getStay : t -> bool
    val setStay : t * bool -> unit

  end = struct

    datatype t = datatype RepTypes.variable

    fun new (name, v, s) = Variable{
            name = name,
            value = ref v,
            constraints = ref [],
            determinedBy = ref ConstraintBase.null,
            mark = ref 0,
            walkStrength = ref s,
            stay = ref true
          }

    fun toString (Variable{name, value, walkStrength, ...}) = concat [
            name, "(", Strength.toString(!walkStrength), ",",
            Int.toString(!value), ")"
          ]

    fun addConstraint (Variable{constraints, ...}, c) = constraints := c :: !constraints

    fun removeConstraint (Variable{constraints, determinedBy, ...}, c) = let
          fun remove ([], _) = ()
            | remove (c' :: cs, cs') = if ConstraintBase.same(c, c')
                then constraints := List.revAppend(cs', cs)
                else remove (cs, c'::cs')
          in
            remove (!constraints, []);
            if ConstraintBase.same(c, !determinedBy)
              then determinedBy := ConstraintBase.null
              else ()
          end

    fun getConstraints (Variable{constraints, ...}) = !constraints

    fun getValue (Variable{value, ...}) = !value
    fun setValue (Variable{value, ...}, v) = value := v

    fun getDeterminedBy (Variable{determinedBy, ...}) = !determinedBy
    fun setDeterminedBy (Variable{determinedBy, ...}, c) = determinedBy := c

    fun getMark (Variable{mark, ...}) = !mark
    fun setMark (Variable{mark, ...}, m) = mark := m

    fun getWalkStrength (Variable{walkStrength, ...}) = !walkStrength
    fun setWalkStrength (Variable{walkStrength, ...}, s) = walkStrength := s

    fun getStay (Variable{stay, ...}) = !stay
    fun setStay (Variable{stay, ...}, b) = stay := b

  end
(******************** planner.sml ********************)
(* planner.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https: *www.smlnj.org)
 * All rights reserved.
 *)

structure Planner : sig

    type t

    type plan = ConstraintBase.t list

    val new : unit -> t

    (* Attempt to satisfy the given constraint and, if successful,
     * incrementally update the dataflow graph.  Details: If satifying
     * the constraint is successful, it may override a weaker constraint
     * on its output. The algorithm attempts to resatisfy that
     * constraint using some other method. This process is repeated
     * until either a) it reaches a variable that was not previously
     * determined by any constraint or b) it reaches a constraint that
     * is too weak to be satisfied using any of its methods. The
     * variables of constraints that have been processed are marked with
     * a unique mark value so that we know where we've been. This allows
     * the algorithm to avoid getting into an infinite loop even if the
     * constraint graph has an inadvertent cycle.
     *)
    val incrementalAdd : t * ConstraintBase.t -> unit

    (* Entry point for retracting a constraint. Remove the given
     * constraint and incrementally update the dataflow graph.
     * Details: Retracting the given constraint may allow some currently
     * unsatisfiable downstream constraint to be satisfied. We therefore collect
     * a list of unsatisfied downstream constraints and attempt to
     * satisfy each one in turn. This list is traversed by constraint
     * strength, strongest first, as a heuristic for avoiding
     * unnecessarily adding and then overriding weak constraints.
     * Assume: c is satisfied.
     *)
    val incrementalRemove : t * ConstraintBase.t -> unit

    (* Extract a plan for resatisfaction starting from the outputs of
     * the given constraints, usually a set of input constraints.
     *)
    val extractPlanFromConstraints : t * ConstraintBase.t list -> plan

    val execute : plan -> unit

  end = struct

    structure V = Variable
    structure C = ConstraintBase
    structure S = Strength

    datatype t = Planner of {
        currentMark : int ref
      }

    type plan = C.t list

    fun new () = Planner{currentMark = ref 0}

    fun newMark (Planner{currentMark}) = let
          val n = !currentMark
          in currentMark := n+1; n end

    fun addConstraintsConsumingTo (x, constraints) = let
          val determiningC = V.getDeterminedBy x
          fun lp ([], constraints) = constraints
            | lp (c::cc, constraints) = if C.same(c, determiningC) andalso C.isSatisfied c
                then lp (cc, c::constraints)
                else lp (cc, constraints)
          in
            lp (V.getConstraints x, constraints)
          end

    (* Attempt to find a way to enforce this constraint. If successful,
     * record the solution, perhaps modifying the current dataflow
     * graph. Answer the constraint that this constraint overrides, if
     * there is one, or nil, if there isn't.
     * Assume: the constraint is not already satisfied.
     *)
    (* Note: in the Java implementation, this function is part of the Constraint
     * class, but that would create a cyclic depedency between it and the Planner
     * module.
     *)
    fun satisfy (planner, c, mark) = (
          C.chooseMethod (c, mark);
          if (not (C.isSatisfied c))
            then if Strength.same(C.getStrength c, Strength.required)
              then raise Fail "Could not satisfy a required constraint"
              else C.null
            else let (* constraint can be satisfied *)
              (* mark inputs to allow cycle detection in `addPropagate` *)
              val _ = C.markInputs (c, mark)
              val out = C.output c
              val overridden = V.getDeterminedBy out
              in
                if not(C.same(overridden, C.null))
                  then C.markUnsatisfied c
                  else ();
                V.setDeterminedBy (out, c);
                if addPropagate (planner, c, mark)
                  then raise Fail "Cycle encountered"
                  else ();
                V.setMark (out, mark);
                overridden
              end)

    and incrementalAdd (planner, c) = let
          val mark = newMark planner
          fun propagate overridden = if C.same(overridden, C.null)
                then ()
                else propagate (satisfy (planner, overridden, mark))
          in
            propagate (satisfy (planner, c, mark))
          end

    and removePropagateFrom (planner, out) = let
          val () = V.setDeterminedBy (out, C.null)
          val () = V.setWalkStrength (out, S.weakest)
          val () = V.setStay (out, true)
          fun loop ([], unsatisfied) = unsatisfied
            | loop (x :: todo, unsatisfied) = let
                val unsatisfied = List.foldl
                      (fn (c, u) => if C.isSatisfied c then u else c::u)
                        unsatisfied
                          (V.getConstraints x)
                val determiningC = V.getDeterminedBy x
                val todo = List.foldl
                      (fn (nextC, td) =>
                        if not(C.same(nextC, determiningC)) andalso C.isSatisfied nextC
                          then (C.recalculate nextC; C.output nextC :: td)
                          else td)
                        todo
                          (V.getConstraints x)
                in
                  loop (todo, unsatisfied)
                end
          in
            loop ([out], [])
          end

    and incrementalRemove (planner, c) = let
          val out = C.output c
          val () = C.markUnsatisfied c
          val () = C.removeFromGraph c
          val unsatisfied = removePropagateFrom (planner, out)
          fun lp strength = if S.same(strength, S.weakest)
                then ()
                else let
                  fun add c' = if S.same(strength, C.getStrength c')
                        then incrementalAdd (planner, c')
                        else ()
                  in
                    List.app add unsatisfied;
                    lp (S.nextWeaker strength)
                  end
          in
            lp Strength.required
          end

    (* Recompute the walkabout strengths and stay flags of all variables
     * downstream of the given constraint and recompute the actual
     * values of all variables whose stay flag is true. If a cycle is
     * detected, remove the given constraint and answer
     * false. Otherwise, answer true.
     * Details: Cycles are detected when a marked variable is
     * encountered downstream of the given constraint. The sender is
     * assumed to have marked the inputs of the given constraint with
     * the given mark. Thus, encountering a marked node downstream of
     * the output constraint means that there is a path from the
     * constraint's output to one of its inputs.
     *)
    and addPropagate (planner, c, mark) = let
          fun lp [] = true
            | lp (d :: todo) = if V.getMark(C.output d) = mark
                then (
                  incrementalRemove (planner, c);
                  false)
                else (
                  C.recalculate d;
                  lp (addConstraintsConsumingTo (C.output d, todo)))
          in
            lp [c]
          end

    (* Extract a plan for resatisfaction starting from the given source
     * constraints, usually a set of input constraints. This method
     * assumes that stay optimization is desired; the plan will contain
     * only constraints whose output variables are not stay. Constraints
     * that do no computation, such as stay and edit constraints, are
     * not included in the plan.
     * Details: The outputs of a constraint are marked when it is added
     * to the plan under construction. A constraint may be appended to
     * the plan when all its input variables are known. A variable is
     * known if either a) the variable is marked (indicating that has
     * been computed by a constraint appearing earlier in the plan), b)
     * the variable is 'stay' (i.e. it is a constant at plan execution
     * time), or c) the variable is not determined by any
     * constraint. The last provision is for past states of history
     * variables, which are not stay but which are also not computed by
     * any constraint.
     * Assume: sources are all satisfied.
     *)
    fun makePlan (planner, sources) = let
          val mark = newMark planner
          fun loop ([], plan) = List.rev plan
            | loop (c::todo, plan) =
                if V.getMark(C.output c) <> mark andalso C.inputsKnown(c, mark)
                  then (
                    V.setMark(C.output c, mark);
                    loop (addConstraintsConsumingTo (C.output c, todo), c::plan))
                  else loop (todo, plan)
          in
            loop (sources, [])
          end

    fun extractPlanFromConstraints (planner, constraints) =
          makePlan (
            planner,
            List.filter (fn c => C.isInput c andalso C.isSatisfied c) constraints)

    val execute = List.app C.execute

  end
(******************** constraint.sml ********************)
(* constraint.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure Constraint : sig

    include CONSTRAINT_BASE

    (* Activate the constraint and attempt to satisfy it *)
    val add : t * Planner.t -> unit

    (* Deactivate this constraint, remove it from the constraint graph,
     * possibly causing other constraints to be satisfied, and destroy it.
     *)
    val destroy : t * Planner.t -> unit

    val toString : t -> string

  end = struct

    open ConstraintBase

    (* Activate the constraint and attempt to satisfy it *)
    fun add (c, planner) = (
          addToGraph c;
          Planner.incrementalAdd(planner, c))

    fun destroy (c, planner) = (
          if (isSatisfied c) then Planner.incrementalRemove(planner, c) else ();
          removeFromGraph c)

    fun toString c =
          if isSatisfied c
            then concat [
                "Satisfied(", inputsToString c, " -> ",
                Variable.toString(output c), ")"
              ]
            else "Unsatisfied"

  end
(******************** edit-constraint.sml ********************)
(* edit-constraint.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure EditConstraint : sig

    val new : Planner.t * Variable.t * Strength.t -> Constraint.t

  end = struct

    structure V = Variable
    structure C = Constraint

    datatype t = datatype RepTypes.constraint

    fun make (out, s) = let
          val satisfied = ref false
          val strength = ref s
          in
            Constraint{
                strength = strength,
                isInput = true,
                execute = fn _ => (),
                isSatisfied = fn _ => !satisfied,
                markUnsatisfied = fn _ => satisfied := false,
                addToGraph = fn c => (
                    V.addConstraint (out, c);
                    satisfied := false),
                removeFromGraph = fn c => (
                    V.removeConstraint (out, c);
                    satisfied := false),
                chooseMethod = fn (c, mark) =>
                    satisfied := ((V.getMark out <> mark)
                      andalso Strength.stronger(!strength, V.getWalkStrength out)),
                markInputs = fn _ => (),
                inputsKnown = fn _ => true,
                output = fn _ => out,
                recalculate = fn c => (
                    (* optimized by removing call to execute *)
                    V.setWalkStrength (out, !strength);
                    V.setStay (out, false)),
                inputsToString = fn _ => ""
              }
          end

    fun new (planner, out, s) = let
          val c = make (out, s)
          in
            C.addToGraph c;
            Planner.incrementalAdd (planner, c);
            c
          end

  end
(******************** stay-constraint.sml ********************)
(* stay-constraint.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure StayConstraint : sig

    val new : Planner.t * Variable.t * Strength.t -> Constraint.t

  end = struct

    structure V = Variable
    structure C = Constraint

    datatype t = datatype RepTypes.constraint

    fun make (out, s) = let
          val satisfied = ref false
          val strength = ref s
          in
            Constraint{
                strength = strength,
                isInput = false,
                execute = fn _ => (),
                isSatisfied = fn _ => !satisfied,
                markUnsatisfied = fn _ => satisfied := false,
                addToGraph = fn c => (
                    V.addConstraint (out, c);
                    satisfied := false),
                removeFromGraph = fn c => (
                    V.removeConstraint (out, c);
                    satisfied := false),
                chooseMethod = fn (c, mark) =>
                    satisfied := ((V.getMark out <> mark)
                      andalso Strength.stronger(!strength, V.getWalkStrength out)),
                markInputs = fn _ => (),
                inputsKnown = fn _ => true,
                output = fn _ => out,
                recalculate = fn c => (
                    (* optimized by removing call to execute *)
                    V.setWalkStrength (out, !strength);
                    V.setStay (out, true)),
                inputsToString = fn _ => ""
              }
          end

    fun new (planner, out, s) = let
          val c = make (out, s)
          in
            C.addToGraph c;
            Planner.incrementalAdd (planner, c);
            c
          end

  end
(******************** equality-constraint.sml ********************)
(* equality-constraint.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure EqualityConstraint : sig

    (* the constraint `var2 = var1` *)
    val new : Planner.t * Variable.t * Variable.t * Strength.t -> Constraint.t

  end = struct

    structure V = Variable
    structure C = Constraint
    structure S = Strength

    datatype t = datatype RepTypes.constraint

    datatype direction = datatype RepTypes.direction

    fun make (var1, var2, s) = let
          val strength = ref s
          val direction = ref NoDirection
          fun output _ = (case !direction of Forward => var2 | _ => var1)
          fun input _ = (case !direction of Forward => var1 | _ => var2)
          fun execute c = V.setValue(output c, V.getValue(input c))
          fun chooseMethod (c, mark) = let
                fun setDir (a, b, dir) =
                      if (V.getMark b <> mark)
                      andalso S.stronger(!strength, V.getWalkStrength b)
                        then direction := dir
                        else direction := NoDirection
                in
                  if (V.getMark var1 = mark)
                    then setDir (var1, var2, Forward)
                  else if (V.getMark var2 = mark)
                    then setDir (var2, var1, Backward)
                  (* If we get here, neither variable is marked, so we have a choice. *)
                  else if S.weaker(V.getWalkStrength var1, V.getWalkStrength var2)
                    then if S.stronger(!strength, V.getWalkStrength var1)
                      then direction := Backward
                      else direction := NoDirection
                    else if S.stronger(!strength, V.getWalkStrength var2)
                      then direction := Forward
                      else direction := NoDirection
                end
          in
            Constraint{
                strength = strength,
                isInput = false,
                execute = execute,
                isSatisfied = fn _ => (case !direction of NoDirection => false | _ => true),
                markUnsatisfied = fn _ => direction := NoDirection,
                addToGraph = fn c => (
                    direction := NoDirection;
                    V.addConstraint (var1, c);
                    V.addConstraint (var2, c)),
                removeFromGraph = fn c => (
                    V.removeConstraint (var1, c);
                    V.removeConstraint (var2, c);
                    direction := NoDirection),
                chooseMethod = chooseMethod,
                markInputs = fn (c, mark) => V.setMark(input c, mark),
                inputsKnown = fn (c, mark) => let
                    val i = input c
                    in
                      (V.getMark i = mark) orelse V.getStay i
                        orelse C.same(V.getDeterminedBy i, C.null)
                    end,
                output = output,
                recalculate = fn c => let
                    val inp = input c
                    val outp = output c
                    in
                      V.setWalkStrength (outp, S.weakestOf(!strength, V.getWalkStrength inp));
                      V.setStay (outp, V.getStay inp);
                      if V.getStay outp then execute c else ()
                    end,
                inputsToString = fn c => V.toString(input c)
              }
          end

    fun new (planner, var1, var2, s) = let
          val c = make (var1, var2, s)
          in
            C.addToGraph c;
            Planner.incrementalAdd (planner, c);
            c
          end

  end
(******************** scale-constraint.sml ********************)
(* scale-constraint.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure ScaleConstraint : sig

    (* the constraint `dest = scale * src + offset` *)
    val new : Planner.t * {
            src : Variable.t,
            scale : Variable.t,
            offset : Variable.t,
            dest : Variable.t,
            strength : Strength.t
          } -> Constraint.t

  end = struct

    structure V = Variable
    structure C = Constraint
    structure S = Strength

    datatype t = datatype RepTypes.constraint

    datatype direction = datatype RepTypes.direction

(* var1 = src, var2 = dest *)
    fun make {src, scale, offset, dest, strength} = let
          val strength = ref strength
          val direction = ref NoDirection
          fun output _ = (case !direction of Forward => dest | _ => src)
          fun input _ = (case !direction of Forward => src | _ => dest)
          fun execute c = (case !direction
                 of Forward => V.setValue(
                      dest,
                      V.getValue src * V.getValue scale + V.getValue offset)
                  | _ => V.setValue(
                      src,
                      Int.quot(V.getValue dest - V.getValue offset, V.getValue scale))
                (* end case *))
          fun chooseMethod (c, mark) = let
                fun setDir (a, b, dir) =
                      if (V.getMark b <> mark)
                      andalso S.stronger(!strength, V.getWalkStrength b)
                        then direction := dir
                        else direction := NoDirection
                in
                  if (V.getMark src = mark)
                    then setDir (src, dest, Forward)
                  else if (V.getMark dest = mark)
                    then setDir (dest, src, Backward)
                  (* If we get here, neither variable is marked, so we have a choice. *)
                  else if S.weaker(V.getWalkStrength src, V.getWalkStrength dest)
                    then if S.stronger(!strength, V.getWalkStrength src)
                      then direction := Backward
                      else direction := NoDirection
                    else if S.stronger(!strength, V.getWalkStrength dest)
                      then direction := Forward
                      else direction := NoDirection
                end
          in
            Constraint{
                strength = strength,
                isInput = false,
                execute = execute,
                isSatisfied = fn _ => (case !direction of NoDirection => false | _ => true),
                markUnsatisfied = fn _ => direction := NoDirection,
                addToGraph = fn c => (
                    direction := NoDirection;
                    V.addConstraint (src, c);
                    V.addConstraint (scale, c);
                    V.addConstraint (offset, c);
                    V.addConstraint (dest, c)),
                removeFromGraph = fn c => (
                    V.removeConstraint (src, c);
                    V.removeConstraint (scale, c);
                    V.removeConstraint (offset, c);
                    V.removeConstraint (dest, c);
                    direction := NoDirection),
                chooseMethod = chooseMethod,
                markInputs = fn (c, mark) => V.setMark(input c, mark),
                inputsKnown = fn (c, mark) => let
                    val i = input c
                    in
                      (V.getMark i = mark) orelse V.getStay i
                        orelse C.same(V.getDeterminedBy i, C.null)
                    end,
                output = output,
                recalculate = fn c => let
                    val inp = input c
                    val outp = output c
                    in
                      V.setWalkStrength (outp, S.weakestOf(!strength, V.getWalkStrength inp));
                      V.setStay (outp, V.getStay inp);
                      if V.getStay outp then execute c else ()
                    end,
                inputsToString = fn c => V.toString(input c)
              }
          end

    fun new (planner, arg) = let
          val c = make arg
          in
            C.addToGraph c;
            Planner.incrementalAdd (planner, c);
            c
          end

  end
(******************** delta-blue.sml ********************)
(* delta-blue.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure DeltaBlue : sig

    (* This is the standard DeltaBlue benchmark. A long chain of
     * equality constraints is constructed with a stay constraint on
     * one end. An edit constraint is then added to the opposite end
     * and the time is measured for adding and removing this
     * constraint, and extracting and executing a constraint
     * satisfaction plan. There are two cases. In case 1, the added
     * constraint is stronger than the stay constraint and values must
     * propagate down the entire length of the chain. In case 2, the
     * added constraint is weaker than the stay constraint so it cannot
     * be accomodated. The cost in this case is, of course, very
     * low. Typical situations lie somewhere between these two
     * extremes.
    *)
    val chainTest : int -> unit

    (* This test constructs a two sets of variables related to each
     * other by a simple linear transformation (scale and offset). The
     * time is measured to change a variable on either side of the
     * mapping and to change the scale and offset factors.
     *)
    val projectionTest : int -> unit

  end = struct

    structure V = Variable
    structure C = Constraint
    structure S = Strength

    fun newVar (name, value) = V.new(name, value, S.weakest)

    fun chainTest n = let
          val planner = Planner.new()
          (* build a chain of `n` equality constraints *)
          val first = newVar("v0", 0)
          fun build (i, prev) = if (i <= n)
                then let
                  val x = newVar("v"^Int.toString i, 0)
                  in
                    EqualityConstraint.new(planner, prev, x, S.required);
                    build (i+1, x)
                  end
                else prev
          val last = build(1, first)
          val _ = StayConstraint.new(planner, last, S.strongDefault)
          val editC = EditConstraint.new(planner, first, S.preferred)
          val plan = Planner.extractPlanFromConstraints(planner, [editC])
          (* execute the plan 100 times *)
          fun execLp i = if (i < 100)
                then (
                  Variable.setValue(first, i);
                  Planner.execute plan;
                  if (V.getValue last <> i)
                    then raise Fail "Chain test failed!"
                    else execLp(i+1))
                else ()
          in
            execLp 0;
            C.destroy (editC, planner)
          end

    fun change (planner, x, newValue) = let
          val editC = EditConstraint.new (planner, x, S.preferred)
          val plan = Planner.extractPlanFromConstraints (planner, [editC])
          fun lp i = if (i < 10)
                then (
                  Variable.setValue (x, newValue);
                  Planner.execute plan;
                  lp (i+1))
                else ()
          in
            lp 0;
            C.destroy (editC, planner)
          end

    fun existsi pred l = let
          fun chk (_, []) = false
            | chk (i, x::xs) = pred(i, x) orelse chk(i+1, xs)
          in
            chk (0, l)
          end

    fun projectionTest n = let
          val planner = Planner.new()
          val scale = newVar("scale", 10)
          val offset = newVar("offset", 1000)
          (* set up the constraints *)
          val src = newVar ("src0", 0)
          val dst = newVar ("dst0", 0)
          fun lp (i, src, dst, dests) = if (i < n)
                then let
                  val src = newVar("src" ^ Int.toString i, i)
                  val dst = newVar("dst" ^ Int.toString i, i)
                  in
                    StayConstraint.new(planner, src, S.normal);
                    ScaleConstraint.new(planner, {
                        src=src, scale=scale, offset=offset, dest=dst,
                        strength=S.required
                      });
                    lp (i+1, src, dst, dst::dests)
                  end
                else (src, dst, List.rev dests)
          val (src, dst, dests) = lp (1, src, dst, [dst])
          in
            (* test 1 *)
            change (planner, src, 17);
            if (Variable.getValue dst <> 1170)
              then raise Fail "Projection test 1 failed!"
              else ();
            (* test 2 *)
            change (planner, dst, 1050);
            if (Variable.getValue dst <> 5)
              then raise Fail "Projection test 2 failed!"
              else ();
            (* test 3 *)
            change(planner, scale, 5);
            let fun lp (i, x::xs) = if (i < n - 1)
                      then if (Variable.getValue x <> i * 5 + 1000)
                        then raise Fail "Projection test 3 failed!"
                        else lp (i+1, xs)
                      else ()
                  | lp _ = ()
                in
                  lp (0, dests)
                end;
            (* test 4 *)
            change(planner, offset, 2000);
            let fun lp (i, x::xs) = if (i < n - 1)
                      then if (Variable.getValue x <> i * 5 + 2000)
                        then raise Fail "Projection test 4 failed!"
                        else lp (i+1, xs)
                      else ()
                  | lp _ = ()
                in
                  lp (0, dests)
                end
          end

  end
in
(* main.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *)

structure Main : BMARK =
  struct

    val name = "delta-blue"

    fun repeat n f = let
          fun lp 0 = ()
            | lp i = (f(); lp (i-1))
          in
            lp n
          end

    fun runOnce () = (DeltaBlue.chainTest 100; DeltaBlue.projectionTest 100)

    fun doit () = repeat 100 runOnce

    fun testit outS = ()

  end
end; (* local *)
