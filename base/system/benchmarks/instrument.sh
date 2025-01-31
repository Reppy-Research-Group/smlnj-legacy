#!/bin/bash

# SML='../../../bin/sml'
SML='../testml'
NRUNS=5

prog="$1"
shift
out_file=$(mktemp "$prog-XXXXX")
flags=$(./presets.sh $@)

echo "{\"bmark\" : \"$prog\", \"flags\":\"$@\", " > $out_file
$SML $flags <<EOF > /dev/null 2>&1
  use "timeit.sml";
  Profiling.schema1Init ();
  Control.NC.instrument := true;
  use "$prog.sml";
  Control.NC.instrument := false;
  Main.doit ();
  val outS = TextIO.openAppend("$out_file");
  Profiling.schema1Read outS;
  TextIO.flushOut outS;
  TextIO.closeOut outS;
EOF
echo "}" >> $out_file

cat $out_file
rm $out_file
