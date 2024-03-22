#!/bin/bash

DDIR="statistics"

mkdir -p "$DDIR"


FFILE="$DDIR/files.txt"

if ! [ -f "$FFILE" ]; then
  echo -n "Collecting active files ..."

  isabelle build -D thys -l -n > "$FFILE"

  echo "Done"
fi

DIRS="thys/basic thys/ds thys/lib thys/sepref thys/vcg thys/examples/sorting"

for i in $DIRS; do

  j=${i%/}
  j=${j#thys/}

  FILES="$DDIR/files_${j//\//-}.txt"


  if grep "$i" $FFILE > "$FILES"; then

    echo "$j: $(cat "$FILES" | xargs cat | wc -l)"

  fi


done

