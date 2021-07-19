#!/bin/bash

set -e

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
  cd papers/ITP2019
  ./make.sh
  cd talk
  make
  cd $BASEDIR

  cd papers/IJCAR2020
  make
  cd $BASEDIR

  cd papers/2019_Rennes_Talk
  make
  cd $BASEDIR

  cd papers/2020_Enschede_Talk
  make
  cd $BASEDIR

  cd papers/2021_Enschede_Talk
  make
  cd $BASEDIR

  cd thys
  isabelle build -v -D .
#   isabelle build -v -d '$AFP' -D .
  cd $BASEDIR

  ./mkdist.sh
fi


rm -rf html
mkdir -p html

ISABELLE_BROWSER_INFO=$(isabelle getenv ISABELLE_BROWSER_INFO | sed -re 's/.*=//')

cp -a $ISABELLE_BROWSER_INFO/Unsorted/Isabelle_LLVM html/
cp index.md html/
cp dist.tgz html/
cp dist-2020.tgz html/
cp dist-v1.1.tgz html/
cp LICENSE html/
cp etc/logo/logo_200.png html/

cp papers/IJCAR2020/main.pdf html/paper_IJCAR2020.pdf
cp papers/IJCAR2020/talk/pres.pdf html/slides_IJCAR2020.pdf

cp papers/ITP2019/main.pdf html/paper_ITP2019.pdf
cp papers/ITP2019/talk/pres.pdf html/slides_ITP2019.pdf

cp papers/2019_Rennes_Talk/pres.pdf html/rennes2019.pdf
cp papers/2020_Enschede_Talk/pres.pdf html/enschede2020.pdf
cp papers/2021_Enschede_Talk/pres.pdf html/enschede2021.pdf
cp papers/2021_RF_Pres/pres.pdf html/RF_pres.pdf

pandoc -V pagetitle="Isabelle LLVM" -s index.md > html/index.html


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


