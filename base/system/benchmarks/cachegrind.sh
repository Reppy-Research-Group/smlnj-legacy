#!/usr/bin/env bash

SML_IMPL='../../../bin/sml'

prog="$1"
shift
out_file=$(mktemp "$prog-XXXXX")
flags=$(./presets.sh $@)

SML="$SML_IMPL $flags"

$SML <<EOF 2>&1
  use "timeit.sml";
  use "$prog.sml";
  SMLofNJ.exportFn ("$prog", fn _ => (Main.doit (); OS.Process.success));
EOF

heap="$prog.amd64-linux"
../../../bin/heap2exec -static "$heap" "$prog"

valgrind --tool=cachegrind --instr-at-start=no --cache-sim=yes "./$prog"
