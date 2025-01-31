#!/usr/bin/env zsh

set -x

LOGFILE=timing.txt
echo > $LOGFILE

for f in *.sml; do
  echo $f >> $LOGFILE
  echo "use \"$f\";" | ../testml | grep "Timing:" | tee /dev/tty >> $LOGFILE
  echo >> $LOGFILE
done

