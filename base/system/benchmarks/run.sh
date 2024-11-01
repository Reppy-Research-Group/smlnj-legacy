#!/bin/bash
#
# usage:
#	run.sh [ --llvm ] prog
#

unalias echo

NCOMPS=1
NRUNS=1

if [ x"$1" = "x--new" ] ; then
  CC=yes
  SML="../testml"
  OUT_SUFFIX="-new"
  shift
else
  CC=no
  SML="../testml -Ccg.new-closure-converter=false"
  OUT_SUFFIX="-old"
fi

if [ x"$1" = x ] ; then
  echo "usage: run.sh [ --llvm ] prog"
  exit 1
fi

prog=$1

OUT_FILE="$prog$OUT_SUFFIX"

echo "results in $OUT_FILE: "

echo "{bmark=\"$prog\", new=\"$CC\", " > $OUT_FILE

# first we time the compile time
#
echo "    compiling ..."
echo -n " compiles=[ " >> $OUT_FILE
$SML <<EOF 2>&1
  use "timeit.sml";
  val outS = TextIO.openAppend("$OUT_FILE");
  fun loop 0 = ()
    | loop i = (
        Timing.timeUse (outS, "$prog.sml");
        if i > 1 then TextIO.output(outS, ",") else ();
        loop (i-1));
  loop $NCOMPS;
  TextIO.flushOut outS;
  TextIO.closeOut outS;
EOF
echo " ]," >> $OUT_FILE

# then measure runtimes
#
echo "    running ..."
echo -n " runs=[" >> $OUT_FILE
$SML <<EOF 2>&1
  use "timeit.sml";
  use "$prog.sml";
  val outS = TextIO.openAppend("$OUT_FILE");
  Timing.time($NRUNS, outS, Main.doit);
  TextIO.flushOut outS;
  Measuring.measure(outS, Main.doit);
  TextIO.flushOut outS;
  TextIO.closeOut outS;
EOF
echo " ]}" >> $OUT_FILE
