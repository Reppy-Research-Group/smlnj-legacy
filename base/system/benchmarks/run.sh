#!/bin/bash
#
# usage:
#	run.sh [ --llvm ] prog
#

NCOMPS=3
NRUNS=10

SML_IMPL='../../../bin/sml'
# SML_IMPL='../../../../reference-legacy/bin/sml'

if [ x"$1" = "x--new" ] ; then
  TAG=new
  # SML="../../../bin/sml -Cnc.enable=true -Cnc.flatten-reg-limit=false"
  SML="$SML_IMPL -Cnc.enable=true"
  OUT_SUFFIX="-new"
  shift
elif [ x"$1" = "x--reg-limit" ] ; then
  TAG=reg-limit
  SML="$SML_IMPL -Cnc.enable=true"
  OUT_SUFFIX="-new"
  shift
elif [ x"$1" = "x--no-flatten" ] ; then
  TAG=no-flatten
  SML="$SML_IMPL -Cnc.enable=true -Cnc.flatten-policy=0"
  OUT_SUFFIX="-new"
  shift
elif [ x"$1" = "x--flat-closure" ] ; then
  TAG=flat-closure
  SML="$SML_IMPL -Cnc.enable=true -Cnc.flat-closure=true"
  OUT_SUFFIX="-new"
  shift
elif [ x"$1" = "x--conservative" ] ; then
  TAG=conservative
  SML="$SML_IMPL -Cnc.enable=true -Cnc.flatten-liberally=false"
  OUT_SUFFIX="-new"
  shift
elif [ x"$1" = "x--old" ] ; then
  TAG=old
  SML="../../../../reference-legacy/bin/sml -Cnc.enable=false"
  # SML="$SML_IMPL -Cnc.enable=false"
  # SML="../../../bin/sml -Cnc.enable=false"
  OUT_SUFFIX="-old"
  shift
else
  echo "usage: run.sh [ --options ] prog"
  exit 1
fi

OUT_SUFFIX='-data'

if [ x"$1" = x ] ; then
  echo "usage: run.sh [ --llvm ] prog"
  exit 1
fi

prog=$1

OUT_FILE="$prog$OUT_SUFFIX"

echo "results in $OUT_FILE: "

echo "{\"bmark\" : \"$prog\", \"tag\":\"$TAG\", " > $OUT_FILE

# first we time the compile time
#
echo "    compiling ..."
echo -n " \"compiles\" : " >> $OUT_FILE
$SML <<EOF 2>&1
  use "timeit.sml";
  val outS = TextIO.openAppend("$OUT_FILE");
  fun loop 0 = (TextIO.output (outS, "],\n"))
    | loop i = (
        Timing.timeUse (outS, "$prog.sml");
        TextIO.output(outS, ",");
        loop (i-1));
  TextIO.output (outS, "[");
  loop $NCOMPS;
  TextIO.flushOut outS;
  TextIO.closeOut outS;
EOF

# then measure runtimes
#
echo "    running ..."
# echo -n " runs=" >> $OUT_FILE
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
echo "}" >> $OUT_FILE
