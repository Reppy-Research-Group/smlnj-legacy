#!/bin/bash

SML='../../../bin/sml'
NRUNS=3

prog="$1"
shift
out_file=$(mktemp "$prog-XXXXX")
flags=$@

echo "{\"bmark\" : \"$prog\", \"flags\":\"$@\", " > $out_file
$SML $flags <<EOF > /dev/null 2>&1
  use "timeit.sml";
  use "$prog.sml";
  val outS = TextIO.openAppend("$out_file");
  Timing.time($NRUNS, outS, Main.doit);
  TextIO.flushOut outS;
  Measuring.measure(outS, Main.doit);
  TextIO.flushOut outS;
  TextIO.closeOut outS;
EOF
echo "}" >> $out_file

cat $out_file
rm $out_file
