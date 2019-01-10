#!/bin/sh

all_of () {
  find "./$1" -path "*/obsolete" -prune -o -not -name "*~" -and -not -path "*/shallow/code2/*" \
    -not -name "lorem.txt" -not -name "kmp" \
    -type f -print
}


( all_of lib; all_of shallow; all_of paper/origKMPtest; echo ./README.md ) | sort > DIST_FILES

tar -czf isabelle_llvm.tgz -T DIST_FILES --transform 's|^.|isabelle_llvm|'

