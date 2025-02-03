#!/bin/bash

flags=""

if [ x"$1" = "x--new" ] ; then
  flags="-Cnc.enable=true -Cnc.flatten-reg-limit=false"
  shift
elif [ x"$1" = "x--reg-limit" ] ; then
  flags="-Cnc.enable=true"
  shift
elif [ x"$1" = "x--no-flatten" ] ; then
  flags="-Cnc.enable=true -Cnc.flatten-policy=0"
  shift
elif [ x"$1" = "x--flat-closure" ] ; then
  flags="-Cnc.enable=true -Cnc.sharing-size-cutoff=100000 -Cnc.sharing-no-thinning=true -Cnc.flatten-policy=0"
  shift
elif [ x"$1" = "x--conservative" ] ; then
  flags="-Cnc.enable=true -Cnc.flatten-liberally=false"
  shift
elif [ x"$1" = "x--no-active-sharing" ] ; then
  flags="-Cnc.enable=true -Cnc.sharing-size-cutoff=100000"
  shift
elif [ x"$1" = "x--no-sharing" ] ; then
  flags="-Cnc.enable=true -Cnc.sharing-size-cutoff=100000 -Cnc.sharing-no-thinning=true"
  shift
elif [ x"$1" = "x--time" ] ; then
  flags="-Cnc.enable=true -Cnc.flatten-reg-limit=false -Cnc.sharing-size-cutoff=6 -Cnc.sharing-dist-cutoff=1 -Cnc.sharing-use-cutoff=1 -Cnc.flatten-selfref=true -Cnc.flatten-liberally=false"
  shift
elif [ x"$1" = "x--space" ] ; then
  flags="-Cnc.enable=true -Cnc.flatten-reg-limit=true -Cnc.sharing-size-cutoff=3 -Cnc.sharing-dist-cutoff=1 -Cnc.sharing-use-cutoff=1 -Cnc.flatten-selfref=false -Cnc.flatten-liberally=true"
  shift
fi

flags="$flags $@"

echo $flags
