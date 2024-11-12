(* argPassing.sml
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * parameter passing convention for standard and known functions.
 *)

functor ArgPassing (
    structure C : CPSREGS
    structure MS : MACH_SPEC
  ) : ARG_PASSING =
  struct
    structure T : MLTREE = C.T

    fun error msg = ErrorMsg.impossible ("ArgPassing." ^ msg)
    fun error msg = raise Fail ("ArgPassing." ^ msg)

    val k = MS.numCalleeSaves
    val kf = MS.numFloatCalleeSaves

    fun stdlink vfp = T.GPR (C.stdlink vfp)
    fun stdclos vfp = T.GPR (C.stdclos vfp)
    fun stdarg vfp  = T.GPR (C.stdarg vfp)
    fun stdcont vfp = T.GPR (C.stdcont vfp)

    val miscRegs = map T.GPR C.miscregs
    fun gpregs vfp = stdlink vfp :: stdclos vfp :: stdarg vfp :: stdcont vfp :: miscRegs
    val fpregs = map T.FPR (C.savedfpregs @ C.floatregs)

  (* return the elements indexed i..j from the list regs *)
    fun fromto (i, j, regs) = let
	(* NOTE: the `to` function is almost `List.take`, but it does not raise
	 * an exception when k >= length regs.
	 *)
	  fun to (k, []) = []
	    | to (k, r::rs) = if k > j then [] else r::to(k+1, rs)
	  in
	    to (i, List.drop(regs, i))
            handle Subscript => (print "here0"; raise Subscript)
	  end

    fun gprfromto (i, j, vfp) = fromto(i, j, gpregs vfp)
    fun fprfromto (i, j, vfp) = fromto(i, j, fpregs)
    fun calleesaveregs vfp = List.take(miscRegs, k) @ fprfromto(0, kf-1, vfp)

    fun isFlt (CPS.FLTt _) = true
      | isFlt _ = false

    fun scan (t::z, gp, fp) = if isFlt t
	  then (case fp
	     of f::fr => f :: scan(z, gp, fr)
	      | [] => error "scan: out of floating-point registers"
                       handle e => raise e
	    (* end case *))
	  else (case gp
	     of g::gr => g :: scan(z, gr, fp)
	      | [] => error ("scan: out of registers" ^ "; stopped at " ^
              String.concatWithMap "," CPSUtil.ctyToString (t :: z))
                       handle e => raise e
	    (* end case *))
      | scan ([], _, _) = []

    fun standardEscape (vfp, args) = let
	  val rest = List.drop(args, k+kf+3)
	  val len = length args
	  val gpr = stdarg vfp :: gprfromto(k+4, len, vfp)
	  val fpr = fprfromto(kf, len, vfp)
	  in
	    stdlink vfp :: stdclos vfp :: stdcont vfp :: calleesaveregs vfp
	      @ scan(rest, gpr, fpr)
          handle e => (print (concat ["rest=[", String.concatWithMap ", "
          CPSUtil.ctyToString rest, "] gpr=", Int.toString (List.length gpr), "\n"]); raise e)
	  end
          handle e => (print (concat ["args=[", String.concatWithMap ", "
          CPSUtil.ctyToString args, "]\n"]); raise e)

    fun standardCont (vfp, args) = let
	  val rest = (if k > 0 then List.drop(args, k+kf+1) else List.drop(args,
   2))
	  val len = length args
	  val gpr = stdarg vfp :: gprfromto(k+4, 1+len, vfp)
	  val fpr = fprfromto(kf, len, vfp)
	  in
	    if k > 0
	      then stdcont vfp :: calleesaveregs vfp @ scan(rest, gpr, fpr)
              handle e => raise e
	      else stdlink vfp :: stdcont vfp :: scan(rest, gpr, fpr)
              handle e => raise e
	  end
          (* DEBUG *)
          handle e => (print (concat ["args=[", String.concatWithMap ", "
          CPSUtil.ctyToString args, "]\n"]); raise e)

    fun standard {fnTy=CPS.CNTt, vfp, argTys} = standardCont(vfp, argTys)
      | standard {vfp, argTys, ...} = standardEscape(vfp, argTys)

  (* use an arbitary but fixed set of registers. *)
    fun fixed {vfp, argTys} = let
	  fun iter (CPS.FLTt _::rest, regs, f::fregs) = f::iter(rest, regs, fregs)
	    | iter (_::rest, r::regs, fregs) = r::iter(rest, regs, fregs)
	    | iter ([], _, _) = []
	    | iter _ = error "fixed: out of registers"
                       handle e => raise e
          in
	    iter(argTys, gpregs vfp, fpregs)
          end

  end
