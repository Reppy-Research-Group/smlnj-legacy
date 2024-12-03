#!/usr/bin/env bash


SML_IMPL='../../../bin/sml'

if [ x"$1" = "x--new" ] ; then
  TAG=new
  SML="$SML_IMPL -Cnc.enable=true -Cnc.flatten-reg-limit=false"
  shift
elif [ x"$1" = "x--reg-limit" ] ; then
  TAG=reg-limit
  SML="$SML_IMPL -Cnc.enable=true"
  shift
elif [ x"$1" = "x--no-flatten" ] ; then
  TAG=no-flatten
  SML="$SML_IMPL -Cnc.enable=true -Cnc.flatten-policy=0"
  shift
elif [ x"$1" = "x--flat-closure" ] ; then
  TAG=flat-closure
  SML="$SML_IMPL -Cnc.enable=true -Cnc.sharing-size-cutoff=100000 -Cnc.sharing-no-thinning=true -Cnc.flatten-policy=0"
  shift
elif [ x"$1" = "x--conservative" ] ; then
  TAG=conservative
  SML="$SML_IMPL -Cnc.enable=true -Cnc.flatten-liberally=false"
  shift
elif [ x"$1" = "x--no-active-sharing" ] ; then
  TAG="no-active-sharing"
  SML="$SML_IMPL -Cnc.enable=true -Cnc.sharing-size-cutoff=100000"
  shift
elif [ x"$1" = "x--no-sharing" ] ; then
  TAG="no-sharing"
  SML="$SML_IMPL -Cnc.enable=true -Cnc.sharing-size-cutoff=100000 -Cnc.sharing-no-thinning=true"
  shift
elif [ x"$1" = "x--old" ] ; then
  TAG=old
  SML="../../../../reference-legacy/bin/sml -Cnc.enable=false"
  shift
else
  echo "usage: run.sh [ --options ] prog"
  exit 1
fi

if [ x"$1" = x ] ; then
  echo "usage: run.sh [ --llvm ] prog"
  exit 1
fi

prog=$1
if [ ! -f "$prog.sml" ]; then
  echo "$prog.sml not found"
  exit 1
fi

$SML <<EOF 2>&1
  use "timeit.sml";
  use "$prog.sml";
  SMLofNJ.exportFn ("$prog", fn _ => (Main.doit (); OS.Process.success));
EOF

heap="$prog.amd64-linux"
../../../bin/heap2exec -static "$heap" "$prog"

perf stat -e mem_inst_retired.all_loads -e mem_inst_retired.all_stores -e instructions -x, -o "$prog-profile" -- "./$prog"

python3 <<EOF 2>&1
import csv
result = {'bmark': '$prog', 'tag': '$TAG'}
with open('$prog-profile', 'r') as csvfile:
    reader = csv.reader(csvfile, delimiter=',')
    for row in reader:
        if len(row) < 3:
            continue
        count, _, name, *rest = row
        result[name] = int(count)

with open('$prog-profile', 'w') as file:
    print(repr(result), file=file)
EOF

