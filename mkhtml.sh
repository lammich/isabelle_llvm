#!/bin/bash

BASEDIR=$PWD

REBUILD=false
UPLOAD=false

while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -r|--rebuild)
    REBUILD=true
    ;;
    -u|--upload)
    UPLOAD=true
    ;;
    *)
    echo "Unknown command line argument $1"        # unknown option
    exit 1
    ;;
esac
shift # past argument or value
done



if $REBUILD; then
./make_artifact.sh
fi


rm -rf html
mkdir -p html


cp README.md html/
cp isabelle_llvm.tgz html/
cp LICENSE html/


pandoc -V pagetitle="Isabelle LLVM" -s README.md > html/index.html


if $UPLOAD; then
  LOCAL_DEST=~/devel/www21-lammich/isabelle_llvm
  rm -rf $LOCAL_DEST
  cp -a html $LOCAL_DEST
  cd $LOCAL_DEST
  echo ADD
  hg add .
  echo COMMIT
  hg commit -m "Automatic update of Isabelle-LLVM" .
  echo PUSH
  hg push
  echo DONE
  cd $BASEDIR
fi


