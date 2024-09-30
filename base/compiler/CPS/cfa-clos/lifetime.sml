structure Lifetime :> sig
  val analyze : LabelledCPS.function * SyntacticInfo.t -> unit
end = struct
  structure LCPS = LabelledCPS
  structure LV = LambdaVar
  structure S = SyntacticInfo

  datatype lifepath = MoveTo of life | Use
  withtype life = LCPS.function * lifepath list

  structure P = PrinterFn(DefaultCostModel)

  val op^^ = P.^^
  val op<$> = P.<$>
  val op<-> = P.<->
  val op<+> = P.<+>
  infix 4 ^^ <$> <-> <+>

  fun dumpLife (x: CPS.lvar, (function, paths) : life) : unit =
    let fun buildPath (MoveTo (f, p :: paths)) : P.doc =
              P.text (LV.lvarName (#2 f) ^ " ") <+>
              (foldl (fn (p, doc) => doc <$> (P.text "\\--> " ^^ buildPath p))
                     (P.text "---> " ^^ buildPath p)
                     paths)
          | buildPath (MoveTo (f, [])) = raise Fail "empty path"
          | buildPath Use = P.text "///"

        fun build (x, function, paths) : P.doc =
          P.text (LV.lvarName x ^ ": ")
          <+> buildPath (MoveTo (function, paths))

    in  P.pprint print 200 (build (x, function, paths)); print "\n\n"
    end

  (* TODO: put this in syntactic analysis *)
  fun innerFunctions ((_, _, _, _, body): LCPS.function) =
    let fun walk (LCPS.FIX (_, fs, exp)) = fs @ walk exp
          | walk (LCPS.APP _) = []
          | walk (LCPS.SWITCH (_, _, _, exps)) = List.concatMap walk exps
          | walk (LCPS.BRANCH (_, _, _, _, exp1, exp2)) = walk exp1 @ walk exp2
          | walk ( LCPS.RECORD (_, _, _, _, exp)
                 | LCPS.SELECT (_, _, _, _, _, exp)
                 | LCPS.OFFSET (_, _, _, _, exp)
                 | LCPS.SETTER (_, _, _, exp)
                 | LCPS.LOOKER (_, _, _, _, _, exp)
                 | LCPS.ARITH  (_, _, _, _, _, exp)
                 | LCPS.PURE   (_, _, _, _, _, exp)
                 | LCPS.RCC    (_, _, _, _, _, _, exp)) = walk exp
    in  walk body
    end

  fun mapPartition pred (map: 'a LV.Map.map) =
    let fun collect (key, value, (tmap, fmap)) =
          if pred key then
            (LV.Map.insert (tmap, key, value), fmap)
          else
            (tmap, LV.Map.insert (fmap, key, value))
    in  LV.Map.foldli collect (LV.Map.empty, LV.Map.empty) map
    end

  fun trueFV (f: LCPS.function, syn: S.t) =
    let val grpFV =
          if S.isTopLevel syn f then
            LV.Map.empty
          else
            S.groupFV syn (S.groupOf syn f)
        val funFV = S.fv syn f
    in  LV.Map.intersectWith #1 (grpFV, funFV)
    end

  (* This function returns the _partial_ lifetime of its free variables, and
   * side-effect adds all variables that originate at this function.
   *)
  fun calculate (function: LCPS.function, syn: S.t, tbl: life LV.Tbl.hash_table)
    : lifepath list LV.Map.map =
    let val fv = trueFV (function, syn)
        val innerFs = innerFunctions function
        fun isFree v = LV.Map.inDomain (fv, v)
        fun isUsed v = LCPS.FunSet.member (S.useSites syn v, function)
        val union = LV.Map.unionWith (op@)
        val insert = LV.Map.insertWith (op@)
        val lives = foldl (fn (f, lives) =>
          let val lives' = calculate (f, syn, tbl)
              val lives' = LV.Map.map (fn paths => [MoveTo (f, paths)]) lives'
          in  union (lives, lives')
          end) LV.Map.empty innerFs
        val lives =
          LV.Map.foldli (fn (v, _, lives) => insert (lives, v, [])) lives fv
        val lives =
          LV.Map.mapi (fn (v, ps) => if isUsed v then ps @ [Use] else ps) lives
        val (fvLives, localLives) = mapPartition isFree lives

        val () = LV.Map.appi (fn (v, paths) =>
          LV.Tbl.insert tbl (v, (function, paths))) localLives

        val () = app print ["In Function: ", LV.lvarName (#2 function), "\n"]
        val () = LV.Map.appi (fn (v, paths) =>
          dumpLife (v, (function, paths))) localLives

    in  fvLives
    end

  fun analyze (cps, syn) =
    let val tbl = LV.Tbl.mkTable (S.numVars syn div 2, Fail "lifetime")
        val lives = calculate (cps, syn, tbl)
        val () = if LV.Map.isEmpty lives then () else raise Fail "???"
    in  ()
    end
end

