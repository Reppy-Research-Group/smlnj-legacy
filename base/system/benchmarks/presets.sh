#!/bin/bash

if [ x"$1" = "x--new" ] ; then
  echo "Cnc.enable=true -Cnc.flatten-reg-limit=false"
elif [ x"$1" = "x--reg-limit" ] ; then
  echo "-Cnc.enable=true"
elif [ x"$1" = "x--no-flatten" ] ; then
  echo "-Cnc.enable=true -Cnc.flatten-policy=0"
elif [ x"$1" = "x--flat-closure" ] ; then
  echo "-Cnc.enable=true -Cnc.sharing-size-cutoff=100000 -Cnc.sharing-no-thinning=true -Cnc.flatten-policy=0"
elif [ x"$1" = "x--conservative" ] ; then
  echo "-Cnc.enable=true -Cnc.flatten-liberally=false"
elif [ x"$1" = "x--no-active-sharing" ] ; then
  echo "-Cnc.enable=true -Cnc.sharing-size-cutoff=100000"
elif [ x"$1" = "x--no-sharing" ] ; then
  echo "-Cnc.enable=true -Cnc.sharing-size-cutoff=100000 -Cnc.sharing-no-thinning=true"
elif [ x"$1" = "x--time" ] ; then
  echo "-Cnc.enable=true -Cnc.flatten-reg-limit=false -Cnc.sharing-size-cutoff=6 -Cnc.sharing-dist-cutoff=1 -Cnc.sharing-use-cutoff=1 -Cnc.flatten-selfref=true -Cnc.flatten-liberally=false"
elif [ x"$1" = "x--space" ] ; then
  echo "-Cnc.enable=true -Cnc.flatten-reg-limit=true -Cnc.sharing-size-cutoff=3 -Cnc.sharing-dist-cutoff=1 -Cnc.sharing-use-cutoff=1 -Cnc.flatten-selfref=false -Cnc.flatten-liberally=true"
else
  echo $@
fi
