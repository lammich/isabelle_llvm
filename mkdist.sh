#!/bin/bash
set -e

DIR=${PWD##*/}

cd ..
tar -czf "$DIR/dist.tgz" --exclude-ignore-recursive=.distignore --transform "s|^$DIR|isabelle-llvm|" "$DIR"
cd - >/dev/null 
