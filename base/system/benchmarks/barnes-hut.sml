(* /Users/byron/Documents/School/Research/master-thesis/benchmarks/programs/barnes-hut/all.sml -- all sources for barnes-hut *)
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
(******************** rand.sig ********************)
(* rand-sig.sml
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Signature for a simple random number generator.
 *
 *)

signature RAND =
  sig

    val srand : real -> unit

    val xrand : real * real -> real

  end (* RAND *)
(******************** rand.sml ********************)
(* rand.sml
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * This is the random number generator from the original Barnes-Hut C
 * code translated to SML.
 *)

structure Rand : RAND =
  struct

    val kA : Real64.real = 16807.0
    val kM : Real64.real = 2147483647.0

    val seed = ref 123.0

    fun srand s = (seed := Real.max(1.0, Real.min(s, 2147483647.0)))

    fun rand () = let
          val t = kA * !seed + 1.0
          val r = t - kM * Real.realFloor(t / kM)
          in
            seed := r;
            r
          end

    fun xrand (xl, xh) = let
          val r = rand ()
          in
            xl + (xh - xl) * r / 2147483647.0
          end

  end
(******************** vector.sig ********************)
(* vector-sig.sml
 *
 * COPYRIGHT (c) 1993, AT&T Bell Laboratories.
 *
 * The abstract interface of vectors and matrices in some dimension.
 *)

signature VECTOR =
  sig
    type 'a vec

    val dim : int	(* dimension of the vectors *)

    val tabulate : (int -> 'a) -> 'a vec

    val equal : real vec * real vec -> bool
    val zerov : real vec
    val addv : (real vec * real vec) -> real vec
    val subv : (real vec * real vec) -> real vec
    val dotvp : (real vec * real vec) -> real
    val crossvp : (real vec * real vec) -> real vec
    val addvs : (real vec * real) -> real vec
    val mulvs : (real vec * real) -> real vec
    val divvs : (real vec * real) -> real vec

    val mapv : ('a -> 'b) -> 'a vec -> 'b vec
    val map3v : (('a * 'b * 'c) -> 'd) -> ('a vec * 'b vec * 'c vec) -> 'd vec
    val foldv : ('a * 'b -> 'b) -> 'a vec -> 'b -> 'b
    val format : {lp : string, sep : string, rp : string, cvt : 'a -> string}
	  -> 'a vec -> string
    val explode : 'a vec -> 'a list
    val implode : 'a list -> 'a vec

    type matrix  (* matrices are always real valued *)

    val zerom : matrix
    val addm : (matrix * matrix) -> matrix
    val outvp : (real vec * real vec) -> matrix

  end
(******************** space.sml ********************)
(* space.sml
 *
 * COPYRIGHT (c) 1993, AT&T Bell Laboratories.
 *
 * The quad/oct-tree representation of space.
 *)

signature SPACE =
  sig

    structure V : VECTOR

    datatype body = Body of {
	mass : real,
	pos : real V.vec ref,
	vel : real V.vec ref,
	acc : real V.vec ref,
	phi : real ref
      }

    datatype cell
      = BodyCell of body
      | Cell of node Array.array

    and node
      = Empty
      | Node of {
	  mass : real ref,
	  pos : real V.vec ref,
	  cell : cell
	}

    datatype space = Space of {
	rmin : real V.vec,
	rsize : real,
	root : node
      }

    val nsub : int	(* number of sub cells / cell (2 ^ V.dim) *)

    val putCell : (cell * int * node) -> unit
    val getCell : (cell * int) -> node
    val mkCell : unit -> cell
    val mkBodyNode : body -> node
    val mkCellNode : cell -> node
    val eqBody : body * body -> bool

  (* debugging code *)
    val dumpTree : node -> unit
    val prBody : body -> string
    val prNode : node -> string

  end; (* SPACE *)

functor Space (V : VECTOR) : SPACE =
  struct

    structure V = V

    datatype body = Body of {
	mass : real,
	pos : real V.vec ref,
	vel : real V.vec ref,
	acc : real V.vec ref,
	phi : real ref
      }

    datatype cell
      = BodyCell of body
      | Cell of node Array.array

    and node
      = Empty
      | Node of {
	  mass : real ref,
	  pos : real V.vec ref,
	  cell : cell
	}

    datatype space = Space of {
	rmin : real V.vec,
	rsize : real,
	root : node
      }

    fun eqBody(Body{mass,pos,vel,acc,phi},
	       Body{mass=m1,pos=p1,vel=v1,acc=a1,phi=h1}) = 
      (Real.==(mass, m1) andalso Real.==(!phi, !h1)
       andalso V.equal(!pos, !p1) andalso V.equal(!vel, !v1)
       andalso V.equal(!acc, !a1))

  (* number of sub cells per cell (2 ^ V.dim) *)
    val nsub = Word.toInt(Word.<<(0w1, Word.fromInt V.dim))

    fun putCell (Cell a, i, nd) = Array.update(a, i, nd)
    fun getCell (Cell a, i) = Array.sub(a, i)
    fun mkCell () = Cell(Array.array(nsub, Empty))
    fun mkBodyNode (body as Body{pos, mass, ...}) = Node{
	    cell = BodyCell body,
	    mass = ref mass,
	    pos = ref (!pos)
	  }
    fun mkCellNode cell = Node{cell = cell, mass = ref 0.0, pos = ref V.zerov}

  (* debugging code *)
    local
      val rfmt = Real.toString
      val vfmt = V.format{lp="[", rp="]", sep=",", cvt = rfmt}
    in
    fun prBody (Body{mass, pos, vel, acc, phi}) = String.concat [
	    "B{m=", rfmt mass,
	    ", p=", vfmt(!pos),
	    ", v=", vfmt(!vel),
	    ", a=", vfmt(!acc),
	    ", phi=", rfmt(!phi), "}"
	  ]
    fun prNode Empty = "Empty"
      | prNode (Node{mass, pos, cell}) = let
	  val cell = (case cell
		 of (Cell _) => "Cell"
		  | (BodyCell b) => (*prBody b*) "Body"
		(* end case *))
	  in
	    String.concat [
		"N{m=", rfmt(!mass),
		", p=", vfmt(!pos),
		cell, "}"
	      ]
	  end
    end

    fun dumpTree tree = let
	  fun printf items = TextIO.output(TextIO.stdOut, String.concat items)
	  fun indent i = StringCvt.padLeft #" " (i+1) ""
	  fun dump (node, l) = let
		fun dump' (Node{cell=Cell a, ...}) = let
		      fun dump'' i = (dump(Array.sub(a, i), l+1); dump''(i+1))
		      in
			(dump'' 0) handle _ => ()
		      end
		  | dump' _ = ()
		in
		  printf [
		      StringCvt.padLeft #" " 2 (Int.toString l),
		      indent l,
		      prNode node, "\n"
		    ];
		  dump' node
		end
	  in
	    dump (tree, 0)
	  end

  end; (* Space *)

(******************** load.sml ********************)
(* load.sml
 *
 * COPYRIGHT (c) 1993, AT&T Bell Laboratories.
 *
 * Code to build the tree from a list of bodies.
 *)

signature LOAD =
  sig

    structure S : SPACE
    structure V : VECTOR
      sharing S.V = V

    val makeTree : (S.body list * real V.vec * real) -> S.space

  end; (* LOAD *)

functor Load (S : SPACE) : LOAD =
 struct

    structure S = S
    structure V = S.V

    exception NotIntCoord

    fun rshift (n, k) = Word.toInt(Word.~>>(Word.fromInt n, Word.fromInt k))

    val IMAX = 0x20000000    (* 2^29 *)
    val IMAXrs1 = rshift(IMAX, 1)
    val rIMAX = real IMAX

  (* compute integerized coordinates.  Raises the NotIntCoord exception,
   * if rp is out of bounds.
   *)
    fun intcoord (rp, rmin, rsize) = let
	  val xsc = V.divvs (V.subv(rp, rmin), rsize)
	  fun cvt x = if ((0.0 <= x) andalso (x < 1.0))
		then floor(rIMAX * x)
		else raise NotIntCoord
	  in
	    V.mapv cvt xsc
	  end

  (* determine which subcell to select. *)
    fun subindex (iv, l) = let
	  fun aux (v, (i, k)) = if (Word.andb(Word.fromInt v, Word.fromInt l) <> 0w0)
		then (i + rshift(S.nsub, k+1), k+1)
		else (i, k+1)
	  in
	    #1 (V.foldv aux iv (0, 0))
	  end

  (* enlarge cubical "box", salvaging existing tree structure. *)
    fun expandBox (nd as S.Body{pos, ...}, box as S.Space{rmin, rsize, root}) = (
	  (intcoord (!pos, rmin, rsize); box)
	    handle NotIntCoord => let
	      val rmid = V.addvs (rmin, 0.5 * rsize)
	      val rmin' = V.map3v (fn (x,y,z) =>
			      if x < y then z - rsize else z) (!pos, rmid, rmin)
	      val rsize' = 2.0 * rsize
	      fun mksub (v, r) = let
		    val x = intcoord (v, rmin', rsize')
handle ex => (
print(concat["loadTree: v = ",
V.format {lp="(", sep=",", rp=")", cvt=Real.toString} v, "\n"]);
raise ex)
		    val k = subindex (x, IMAXrs1)
		    val cell = S.mkCell ()
		    in
		      S.putCell (cell, k, r); cell
		    end
	      val box = (case root
		     of S.Empty => S.Space{rmin=rmin', rsize=rsize', root=root}
		      | _ => S.Space{
			    rmin = rmin',
			    rsize = rsize',
			    root = S.mkCellNode (mksub (rmid, root))
			  }
		    (* end case *))
	      in
	        expandBox (nd, box)
	      end)


  (* insert a single node into the tree *)
    fun loadTree (body as S.Body{pos=posp, ...}, S.Space{rmin, rsize, root}) = let
	  val xp = intcoord (!posp, rmin, rsize)
handle ex => (
print(concat["loadTree: posp = ",
V.format {lp="(", sep=",", rp=")", cvt=Real.toString} (!posp), "\n"]);
raise ex)
	  fun insert (S.Empty, _) = S.mkBodyNode body
	    | insert (n as S.Node{cell=S.BodyCell _, pos=posq, ...}, l) = let
		val xq = intcoord (!posq, rmin, rsize)
handle ex => raise ex
		val k = subindex (xq, l)
		val a = S.mkCell()
		in
		  S.putCell(a, k, n);
		  insert (S.mkCellNode a, l)
		end
	    | insert (n as S.Node{cell, ...}, l) = let
		val k = subindex (xp, l)
		val subtree = insert (S.getCell (cell, k), rshift(l, 1))
		in
		  S.putCell (cell, k, subtree);
		  n
		end
	  in
	    S.Space{rmin = rmin, rsize = rsize, root = insert (root, IMAXrs1)}
	  end

  (* descend tree finding center-of-mass coordinates. *)
    fun hackCofM S.Empty = ()
      | hackCofM (S.Node{cell = S.BodyCell _, ...}) = ()
      | hackCofM (S.Node{cell = S.Cell subcells, mass, pos}) = let
	  fun sumMass (i, totMass, cofm) = if (i < S.nsub)
		then (case Array.sub(subcells, i)
		   of S.Empty => sumMass (i+1, totMass, cofm)
		    | (nd as S.Node{mass, pos, ...}) => let
			val _ = hackCofM nd
			val m = !mass
			in
			  sumMass (i+1, totMass + m, V.addv(cofm, V.mulvs(!pos, m)))
			end
		  (* end case *))
		else (
		  mass := totMass;
		  pos := V.divvs(cofm, totMass))
	  in
	    sumMass (0, 0.0, V.zerov)
	  end

  (* initialize tree structure for hack force calculation. *)
    fun makeTree (bodies, rmin, rsize) = let
	  fun build ([], space) = space
	    | build ((body as S.Body{mass, ...}) :: r, space) =
	       if Real.==(mass, 0.0) then build (r, space)
	       else let
		   val box = expandBox (body, space)
		   val box = loadTree(body, box)
		 in build (r, box)
		 end
	  val (space as S.Space{root, ...}) =
	    build (bodies, S.Space{rmin=rmin, rsize=rsize, root=S.Empty})
	  in
	    hackCofM root;
	    space
	  end

  end; (* functor Load *)
(******************** grav.sml ********************)
(* grav.sml
 *
 * COPYRIGHT (c) 1993, AT&T Bell Laboratories.
 *
 * Gravity module for hierarchical N-body code; routines to compute gravity.
 *)

signature GRAV =
  sig

    structure S : SPACE
    structure V : VECTOR
      sharing S.V = V

    val hackGrav : {body:S.body, root:S.node, rsize:real, tol:real, eps : real}
	  -> {n2bterm:int, nbcterm:int, skipSelf:bool}

  end; (* GRAV *)

functor Grav (S : SPACE) : GRAV =
  struct

    structure S = S
    structure V = S.V

    fun walk {acc0, phi0, pos0, pskip, eps, rsize, tol, root} = let
	  val skipSelf = ref false
	  val nbcterm = ref 0 and n2bterm = ref 0
	  val tolsq = (tol * tol)
	(* compute a single body-body or body-cell interaction. *)
	  fun gravsub (S.Empty, phi0, acc0, _) = (phi0, acc0)
	    | gravsub (p as S.Node{mass, pos, cell, ...}, phi0, acc0, memo) = let
		val (dr, drsq) = (case memo
		       of NONE => let
			    val dr = V.subv(!pos, pos0)
			    in
			      (dr, V.dotvp(dr, dr) + (eps*eps))
			    end
			| SOME(dr', drsq') => (dr', drsq' + (eps*eps))
		      (* end case *))
		val phii = !mass / (Math.sqrt drsq)
		in
		  case cell
		   of (S.Cell _) => nbcterm := !nbcterm + 1
		    | _ => n2bterm := !n2bterm + 1
		  (* end case *);
		  (phi0 - phii, V.addv(acc0, V.mulvs(dr, phii / drsq)))
		end (* gravsub *)
	(* recursive routine to do hackwalk operation. This combines the
	 * subdivp and walksub routines from the C version.
	 *)
	  fun walksub (p, dsq, phi0, acc0) = (
(*print(implode["    walksub: dsq = ", makestring dsq, ", ", S.prNode p, "\n"]);*)
		case p
		 of S.Empty => (phi0, acc0)
		  | (S.Node{cell = S.BodyCell body, ...}) => 
		      if S.eqBody(body, pskip)
			then (skipSelf := true; (phi0, acc0))
			else gravsub (p, phi0, acc0, NONE)
		  | (S.Node{cell = S.Cell a, pos, ...}) => let
		      val dr = V.subv(!pos, pos0)
		      val drsq = V.dotvp(dr, dr)
		      in
			if ((tolsq * drsq) < dsq)
			  then let (* open p up *)
			    fun loop (i, phi0, acc0) = if (i < S.nsub)
				  then let
				    val (phi0', acc0') = walksub (
					    Array.sub(a, i), dsq/4.0, phi0, acc0)
				    in
				      loop (i+1, phi0', acc0')
				    end
				  else (phi0, acc0)
			    in
			      loop (0, phi0, acc0)
			    end
			  else gravsub (p, phi0, acc0, SOME(dr, drsq))
		      end
		(* end case *))
	  val (phi0, acc0) = walksub (root, rsize*rsize, phi0, acc0)
	  in
	    { phi0 = phi0, acc0 = acc0,
	      nbcterm = !nbcterm, n2bterm = !n2bterm, skip = !skipSelf
	    }
	  end (* walk *)

  (* evaluate grav field at a given particle. *)
    fun hackGrav {body as S.Body{pos, phi, acc, ...}, root, rsize, eps, tol} = let
	  val {phi0, acc0, nbcterm, n2bterm, skip} = walk {
		  acc0 = V.zerov, phi0 = 0.0, pos0 = !pos, pskip = body,
		  eps = eps, rsize = rsize, tol = tol, root = root
		}
	  in
	    phi := phi0;
	    acc := acc0;
(**
app (fn (fmt, items) => print(Format.format fmt items)) [
  ("pos = [%f %f %f]\n", map Format.REAL (V.explode(!pos))),
  ("pos = [%f %f %f]\n", map Format.REAL (V.explode acc0)),
  ("phi = %f\n", [Format.REAL phi0])
];
raise Fail "";
**)
	    {nbcterm=nbcterm, n2bterm=n2bterm, skipSelf=skip}
	  end (* hackgrav *)

  end; (* Grav *)
(******************** data-io.sml ********************)
(* data-io.sml
 *
 * COPYRIGHT (c) 1993, AT&T Bell Laboratories.
 *
 * I/O routines for export version of hierarchical N-body code.
 *)

signature DATA_IO =
  sig

    structure S : SPACE

    val inputData : string -> {
	    nbody : int,
	    bodies : S.body list,
	    tnow : real,
	    headline : string
	  }

  (* output routines *)
    val initOutputStrm : {
	    outS : TextIO.outstream, headline : string, nbody : int, tnow : real,
	    dtime : real, eps : real, tol : real, dtout : real, tstop : real
	  } -> unit
    val initOutput : {
	    outfile : string, headline : string, nbody : int, tnow : real,
	    dtime : real, eps : real, tol : real, dtout : real, tstop : real
	  } -> unit
    val output : {
	    nbody : int, bodies : S.body list, n2bcalc : int, nbccalc : int,
	    selfint : int, tnow : real
	  } -> unit
    val stopOutput : unit -> unit

  end;

functor DataIO (S : SPACE) : DATA_IO =
  struct

    structure SS = Substring
    structure S = S
    structure V = S.V

    val atoi = valOf o Int.scan StringCvt.DEC SS.getc

    fun inputData fname = let
	  val strm = TextIO.openIn fname
	  val buf = ref(SS.full "")
	  fun getLn () = (case (TextIO.inputLine strm)
		 of NONE => raise Fail "inputData: EOF"
		  | SOME s => buf := SS.full s
		(* end case *))
	  fun skipWS () = let
		val buf' = SS.dropl Char.isSpace (!buf)
		in
		  if (SS.isEmpty buf')
		    then (getLn(); skipWS())
		    else buf'
		end
	  fun readInt () = let
		val (n, ss) = atoi (skipWS ())
		in
		  buf := ss; n
		end
	  fun readReal () = let
		val (r, ss) = valOf (Real.scan SS.getc (skipWS()))
                in
                  buf := ss; r
                end
	  val nbody = readInt()
	  val _ = if (nbody < 1)
		then raise Fail "absurd nbody"
		else ()
	  val ndim = readInt()
	  val _ = if (ndim <> V.dim)
		then raise Fail "absurd ndim"
		else ()
	  val tnow = readReal()
	  fun iter f = let
		fun loop (0, l) = l
		  | loop (n, l) = loop (n-1, f() :: l)
		in
		  fn n => loop (n, [])
		end
	  fun readVec () = V.implode (rev (iter readReal ndim))
	  val massList = iter readReal nbody
	  val posList = iter readVec nbody
	  val velList = iter readVec nbody
	  fun mkBodies ([], [], [], l) = l
	    | mkBodies (m::r1, p::r2, v::r3, l) = let
		val b = S.Body{
			mass = m,
			pos = ref p,
			vel = ref v,
			acc = ref V.zerov,
			phi = ref 0.0
		      }
		in
		  mkBodies(r1, r2, r3, b::l)
		end
	  in
	    TextIO.closeIn strm;
	    { nbody = nbody,
	      bodies = mkBodies (massList, posList, velList, []),
	      tnow = tnow,
	      headline = concat["Hack code: input file ", fname, "\n"]
	    }
	  end

    type out_state = {
	tout : real,
	dtout : real,
	dtime : real,
	strm : TextIO.outstream
      }
    val outState = ref (NONE : out_state option)

    fun fprintf (strm, items) = TextIO.output(strm, String.concat items)
    fun printf items = fprintf(TextIO.stdOut, items)
    fun pad n s = StringCvt.padLeft #" " n s
    fun fmtInt (wid, i) = pad wid (Int.toString i)
    fun fmtReal (wid, prec, r) = pad wid (Real.fmt (StringCvt.FIX(SOME prec)) r)
    fun fmtRealE (wid, prec, r) = pad wid (Real.fmt (StringCvt.SCI(SOME prec)) r)
    local
      fun itemFmt r = fmtReal (9, 4, r)
      val fmt = V.format{lp="", sep="", rp="", cvt=itemFmt}
    in
    fun printvec (init, vec) = printf [
	    "\t ", pad 9 init, fmt vec, "\n"
	  ]
    end (* local *)

    fun stopOutput () = (case (! outState)
	   of NONE => ()
	    | (SOME{strm, ...}) => (TextIO.closeOut strm; outState := NONE)
	  (* end case *))

    fun initOutputStrm {outS, headline, nbody, tnow, dtime, eps, tol, dtout, tstop} = (
	  fprintf (outS, ["\n\t\t", headline, "\n\n"]);
	  fprintf (outS, map (pad 12) ["nbody", "dtime", "eps", "tol", "dtout", "tstop"]);
	  fprintf (outS, ["\n"]);
	  fprintf (outS, [fmtInt(12, nbody), fmtReal(12, 5, dtime)]);
	  fprintf (outS, [
	      fmtInt(12, nbody), fmtReal(12, 5, dtime),
	      fmtReal(12, 4, eps), fmtReal(12, 2, tol),
	      fmtReal(12, 3, dtout), fmtReal(12, 2, tstop), "\n\n"
	    ]);
	  outState := SOME{
              dtime = dtime,
              tout = tnow,
              dtout = dtout,
              strm = outS
            }
	  (* end case *))

    fun initOutput {outfile, headline, nbody, tnow, dtime, eps, tol, dtout, tstop} = (
          case outfile
           of "" => outState := NONE
            | file => initOutputStrm {
                  outS = TextIO.openOut outfile,
                  headline = headline,
                  nbody = nbody,
                  tnow = tnow,
                  dtime = dtime,
                  eps = eps,
                  tol = tol,
                  dtout = dtout,
                  tstop = tstop
                }
          (* end case *))

  (* compute set of dynamical diagnostics. *)
    fun diagnostics bodies = let
	  fun loop ([], arg) = {
		  mtot = #totM arg,		(* total mass *)
		  totKE = #totKE arg,		(* total kinetic energy *)
		  totPE = #totPE arg,		(* total potential energy *)
		  cOfMPos = #cOfMPos arg,	(* center of mass: position *)
		  cOfMVel = #cOfMVel arg,	(* center of mass: velocity *)
		  amVec = #amVec arg		(* angular momentum vector *)
		}
	    | loop (S.Body{
		  mass, pos=ref pos, vel=ref vel, acc=ref acc, phi=ref phi
	        } :: r, arg) = let
		val velsq = V.dotvp(vel, vel)
		val halfMass = 0.5 * mass
		val posXmass = V.mulvs(pos, mass)
		in
		  loop ( r, {
		      totM = (#totM arg) + mass,
		      totKE = (#totKE arg) + halfMass * velsq,
		      totPE = (#totPE arg) + halfMass * phi,
		      keTen = V.addm(#keTen arg, V.outvp(V.mulvs(vel, halfMass), vel)),
		      peTen = V.addm(#peTen arg, V.outvp(posXmass, acc)),
		      cOfMPos = V.addv(#cOfMPos arg, posXmass),
		      cOfMVel = V.addv(#cOfMVel arg, V.mulvs(vel, mass)),
		      amVec = V.addv(#amVec arg, V.mulvs(V.crossvp(pos, vel), mass))
		    })
		end
	  in
	    loop (bodies, {
		totM = 0.0, totKE = 0.0, totPE = 0.0,
		keTen = V.zerom, peTen = V.zerom,
		cOfMPos = V.zerov, cOfMVel = V.zerov,
		amVec = V.zerov
	      })
	  end (* diagnostics *)

    fun outputData (strm, tnow, nbody, bodies) = let
	  fun outInt i = fprintf(strm, ["  ", Int.toString i, "\n"])
	  fun outReal r = fprintf(strm, [" ", fmtRealE(21, 14, r), "\n"])
	  fun prReal r = fprintf(strm, [" ", fmtRealE(21, 14, r)])
	  fun outVec v = let
		fun out [] = TextIO.output(strm, "\n")
		  | out (x::r) = (prReal x; out r)
		in
		  out(V.explode v)
		end
	  in
	    outInt nbody;
	    outInt V.dim;
	    outReal tnow;
	    app (fn (S.Body{mass, ...}) => outReal mass) bodies;
	    app (fn (S.Body{pos, ...}) => outVec(!pos)) bodies;
	    app (fn (S.Body{vel, ...}) => outVec(!vel)) bodies;
	    printf ["\n\tparticle data written\n"]
	  end;

    fun output {nbody, bodies, n2bcalc, nbccalc, selfint, tnow} = let
	  val nttot = n2bcalc + nbccalc
	  val nbavg = floor(real n2bcalc / real nbody)
	  val ncavg = floor(real nbccalc / real nbody)
	  val data = diagnostics bodies
	  in
	    printf ["\n"];
	    printf (map (pad 9) [
		"tnow", "T+U", "T/U", "nttot", "nbavg", "ncavg", "selfint"
	      ]);
	    printf ["\n"];
	    printf [
		fmtReal(9, 3, tnow), fmtReal(9, 4, #totKE data + #totPE data),
		fmtReal(9, 4, #totKE data / #totPE data), fmtInt(9, nttot),
		fmtInt(9, nbavg), fmtInt(9, ncavg), fmtInt(9, selfint), "\n\n"
	      ];
	    printvec ("cm pos", #cOfMPos data);
	    printvec ("cm vel", #cOfMVel data);
	    printvec ("am pos", #amVec data);
	    case !outState
	     of NONE => ()
	      | (SOME{tout, dtout, dtime, strm}) =>
		  if ((tout - 0.01 * dtime) <= tnow)
		    then (
		      outputData (strm, tnow, nbody, bodies);
		      outState := SOME{
			  tout=tout+dtout, dtout=dtout, dtime=dtime, strm=strm
			})
		    else ()
	    (* end case *)
	  end

  end; (* DataIO *)

(******************** vector3.sml ********************)
(* vector3.sml
 *
 * COPYRIGHT (c) 1993, AT&T Bell Laboratories.
 *
 * 3 dimensional vector arithmetic.
 *)

structure Vector3 : VECTOR =
  struct

    type 'a vec = {x : 'a, y : 'a, z : 'a}
    type realvec = real vec

    val dim = 3

    fun tabulate f = {x = f 0, y = f 1, z = f 2}

    val zerov = {x = 0.0, y = 0.0, z = 0.0}
    fun equal({x, y, z}, {x=x1, y=y1, z=z1}) =
      Real.==(x, x1) andalso Real.==(y, y1) andalso Real.==(z, z1)

    fun addv ({x=x1, y=y1, z=z1} : realvec, {x=x2, y=y2, z=z2}) =
	  {x=x1+x2, y=y1+y2, z=z1+z2}

    fun subv ({x=x1, y=y1, z=z1} : realvec, {x=x2, y=y2, z=z2}) =
	  {x=x1-x2, y=y1-y2, z=z1-z2}

    fun dotvp ({x=x1, y=y1, z=z1} : realvec, {x=x2, y=y2, z=z2}) =
	  x1*x2 + y1*y2 + z1*z2

    fun crossvp ({x=x1, y=y1, z=z1} : realvec, {x=x2, y=y2, z=z2}) =
	  {x = y1*z2 - z1*y2, y = x1*z2 - z1*x2, z = x1*y2 - y1*x2}

    fun addvs ({x, y, z} : realvec, s) = {x=x+s, y=y+s, z=z+s}

    fun mulvs ({x, y, z} : realvec, s) = {x=x*s, y=y*s, z=z*s}

    fun divvs ({x, y, z} : realvec, s) = {x=x/s, y=y/s, z=z/s}

    fun mapv f {x, y, z} = {x = f x, y = f y, z = f z}

    fun map3v f ({x=x1, y=y1, z=z1}, {x=x2, y=y2, z=z2}, {x=x3, y=y3, z=z3}) =
	  {x = f(x1, x2, x3), y = f(y1, y2, y3), z = f(z1, z2, z3)}

    fun foldv f {x, y, z} init = f(z, f(y, f(x, init)))

    fun format {lp, rp, sep, cvt} {x, y, z} = String.concat[
	    lp, cvt x, sep, cvt y, sep, cvt z, rp
	  ]

    fun explode {x, y, z} = [x, y, z]

    fun implode [x, y, z] = {x=x, y=y, z=z}
      | implode _ = raise Fail "implode: bad dimension"

    type matrix = {
	    m00 : real, m01 : real, m02 : real,
	    m10 : real, m11 : real, m12 : real,
	    m20 : real, m21 : real, m22 : real
	  }

    val zerom = {
	    m00 = 0.0, m01 = 0.0, m02 = 0.0,
	    m10 = 0.0, m11 = 0.0, m12 = 0.0,
	    m20 = 0.0, m21 = 0.0, m22 = 0.0
	  }

    fun addm (a : matrix, b : matrix) = {
	    m00=(#m00 a + #m00 b), m01=(#m01 a + #m01 b), m02=(#m02 a + #m02 b),
	    m10=(#m10 a + #m10 b), m11=(#m11 a + #m11 b), m12=(#m12 a + #m12 b),
	    m20=(#m20 a + #m20 b), m21=(#m21 a + #m21 b), m22=(#m22 a + #m22 b)
	  }

    fun outvp ({x=a0, y=a1, z=a2} : realvec, {x=b0, y=b1, z=b2}) = {
	    m00=(a0*b0), m01=(a0*b1), m02=(a0*b2),
	    m10=(a1*b0), m11=(a1*b1), m12=(a1*b2),
	    m20=(a2*b0), m21=(a2*b1), m22=(a2*b2)
	  }

  end (* VectMath *)

(******************** barnes-hut3d.sml ********************)
(* barnes-hut3d.sml
 *
 * COPYRIGHT (c) 2024 The Fellowship of SML/NJ (https://www.smlnj.org)
 * All rights reserved.
 *
 * 3D version of the Barnes-Hut benchmark.
 *)

structure BarnesHut3D : sig

    structure S : SPACE
    structure V : VECTOR
    structure L : LOAD
    structure DataIO : DATA_IO

    (* reset the random number generator *)
    val srand : real -> unit

    (* generate the Plummer model data *)
    val testdata : int -> S.body list

    (* run the simulation *)
    val go : {
            output : {
                n2bcalc:int, nbccalc:int, nstep:int, selfint:int, tnow:real
              } -> unit,
	    bodies : S.body list, tnow : real, tstop : real,
	    dtime : real, eps : real, tol : real,
            rmin : real V.vec, rsize : real
	  } -> unit

  end = struct

    structure V = Vector3
    structure S = Space(V)
    structure L = Load(S)
    structure G = Grav(S)
    structure DataIO = DataIO(S)

    (* random numbers *)
    open Rand

    (* pick a random point on a sphere of specified radius. *)
    fun pickshell rad = let
          fun pickvec () = let
                val vec = V.tabulate (fn _ => xrand(~1.0, 1.0))
                val rsq = V.dotvp(vec, vec)
                in
                  if (rsq > 1.0)
                    then pickvec ()
                    else V.mulvs (vec, rad / Math.sqrt(rsq))
                end
          in
            pickvec ()
          end

    (* generate Plummer model initial conditions for test runs, scaled
     * to units such that M = -4E = G = 1 (Henon, Hegge, etc).
     * See Aarseth, SJ, Henon, M, & Wielen, R (1974) Astr & Ap, 37, 183.
     *)
    fun testdata n = let
	  val mfrac = 0.999 (* mass cut off at mfrac of total *)
	  val rn = real n
	  val rsc = (3.0 * Math.pi) / 16.0
	  val vsc = Math.sqrt(1.0 / rsc)
	  fun mkBodies (0, cmr, cmv, l) = let
                (* offset bodies by normalized cm coordinates.  Also, reverse
                 * the list to get the same order of bodies as in the C version.
                 *)
		val cmr = V.divvs(cmr, rn)
		val cmv = V.divvs(cmv, rn)
		fun norm ([], l) = l
		  | norm ((p as S.Body{pos, vel, ...}) :: r, l) = (
		      pos := V.subv(!pos, cmr);
		      vel := V.subv(!vel, cmv);
		      norm (r, p::l))
		in
		  norm (l, [])
		end
	    | mkBodies (i, cmr, cmv, l) = let
		val r = 1.0 / Math.sqrt (Math.pow(xrand(0.0, mfrac), ~2.0/3.0) - 1.0)
		val pos = pickshell (rsc * r)
		fun vN () = let		(* von Neumann technique *)
		      val x = xrand(0.0,1.0)
		      val y = xrand(0.0,0.1)
		      in
			if (y > x*x * (Math.pow (1.0-x*x, 3.5))) then vN () else x
		      end
		val v = ((Math.sqrt 2.0) * vN()) / Math.pow(1.0 + r*r, 0.25)
		val vel = pickshell (vsc * v)
		val body = S.Body{
			mass = 1.0 / rn,
			pos = ref pos,
			vel = ref vel,
			acc = ref V.zerov,
			phi = ref 0.0
		      }
		in
		  mkBodies (i-1, V.addv(cmr, pos), V.addv(cmv, vel), body :: l)
		end
	  in
	    mkBodies (n, V.zerov, V.zerov, [])
	  end (* testdata *)

    (* advance N-body system one time-step. *)
    fun stepSystem output {plist, dtime, eps, nstep, rmin, rsize, tnow, tol} = let
	  val dthf = 0.5 * dtime
	  val S.Space{rmin, rsize, root} = L.makeTree (plist, rmin, rsize)
	(* recalculate accelaration *)
	  fun recalc ([], n2bcalc, nbccalc, selfint) = (n2bcalc, nbccalc, selfint)
	    | recalc (p::r, n2bcalc, nbccalc, selfint) = let
		val S.Body{acc as ref acc1, vel, ...} = p
		val {n2bterm, nbcterm, skipSelf} = G.hackGrav {
			body = p, root = root, rsize = rsize, eps = eps, tol = tol
		      }
		in
		  if (nstep > 0)
		    then (* use change in accel to make 2nd order *)
			 (* correction to vel. *)
		      vel := V.addv(!vel, V.mulvs(V.subv(!acc, acc1), dthf))
		    else ();
		  recalc (r, n2bcalc+n2bterm, nbccalc+nbcterm,
		    if skipSelf then selfint else (selfint+1))
		end
	  (* advance bodies *)
	  fun advance (S.Body{pos, acc, vel, ...}) = let
		val dvel = V.mulvs (!acc, dthf)
		val vel1 = V.addv (!vel, dvel)
		val dpos = V.mulvs (vel1, dtime)
		in
		  pos := V.addv (!pos, dpos);
		  vel := V.addv (vel1, dvel)
		end
	  val (n2bcalc, nbccalc, selfint) = recalc (plist, 0, 0, 0)
	  in
	    output {nstep=nstep, tnow=tnow, n2bcalc=n2bcalc, nbccalc=nbccalc, selfint=selfint};
	    app advance plist;
	    (nstep+1, tnow + dtime)
	  end

    (* given an initial configuration, run the simulation *)
    fun go {
	  output, bodies, tnow, tstop,
	  dtime, eps, tol, rsize, rmin
	} = let
	  val step = stepSystem output
	  fun loop (nstep, tnow) = if (tnow < tstop + (0.1 * dtime))
		then loop (step {
		    plist = bodies, dtime = dtime, eps = eps, nstep = nstep,
		    rmin = rmin, rsize = rsize, tnow = tnow, tol = tol
		  })
		else ()
	  in
	    loop (0, tnow)
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

    structure BH = BarnesHut3D

    val name = "barnes-hut-3d"

    (* parameters *)
    val nbody = 1024
    val tnow = 0.0
    val tstop = 2.0
    val dtime = 0.025
    val eps = 0.05
    val tol = 1.0
    val dtout = 0.25
    val rmin = BH.S.V.tabulate (fn _ => ~2.0)
    val rsize = 4.0
    val headline = "Plummer model"

    fun doit () = (
	  BH.srand 123.0;
	  BH.go {
	      output = fn _ => (),
	      bodies = BH.testdata nbody,
	      tnow = tnow, tstop = tstop,
	      dtime = dtime, eps = eps, tol = tol,
	      rmin = rmin,
	      rsize = rsize
	    })

    fun testit outS = let
          val nbody = 256 (* smaller problem for testing *)
          val bodies = BarnesHut3D.testdata nbody
	  fun output {nstep, tnow, n2bcalc, nbccalc, selfint} = BH.DataIO.output{
		  bodies = bodies, nbody = nbody,
		  n2bcalc = n2bcalc, nbccalc = nbccalc,
                  selfint = selfint, tnow = tnow
		}
          in
	    BH.DataIO.initOutputStrm {
		outS = outS, headline = headline, nbody = nbody, tnow = tnow,
		dtime = dtime, eps = eps, tol = tol, dtout = dtout, tstop = tstop
	      };
	    BH.go {
		output=output, bodies=bodies, tnow=tnow, tstop=tstop,
		dtime=dtime, eps=eps, tol=tol, rsize=rsize, rmin=rmin
	      }
          end
  end;
end; (* local *)
