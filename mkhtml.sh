#!/bin/bash

set -e

ISABELLE=isabelle

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

  cd papers/ITP2022
  make
  cd talk
  make
  cd $BASEDIR

  cd papers/JAR_SI_ITP2022
  make
  cd $BASEDIR


  cd thys
  $ISABELLE build -v -D .
#   isabelle build -v -d '$AFP' -D .
  cd $BASEDIR

  ./mkdist.sh
fi


htmlbase=https://lammich.github.io/isabelle_llvm

sed -re "s|\(HTML:([^)]*)\)|($htmlbase/\1)|g" README.in.md > README.md


HTMLDIR=docs

rm -rf "$HTMLDIR"
mkdir -p "$HTMLDIR"

ISABELLE_BROWSER_INFO=$($ISABELLE getenv ISABELLE_BROWSER_INFO | sed -re 's/.*=//')

cp -a $ISABELLE_BROWSER_INFO "$HTMLDIR/"
cp index.md "$HTMLDIR/"
cp dist.tgz "$HTMLDIR/"
cp dist-2020.tgz "$HTMLDIR/"
cp dist-v1.1.tgz "$HTMLDIR/"
cp dist-v2.0.tgz "$HTMLDIR/"
cp LICENSE "$HTMLDIR/"
cp etc/logo/logo_*.png "$HTMLDIR/"

cp papers/IJCAR2020/main.pdf "$HTMLDIR/paper_IJCAR2020.pdf"
cp papers/IJCAR2020/talk/pres.pdf "$HTMLDIR/slides_IJCAR2020.pdf"

cp papers/ITP2019/main.pdf "$HTMLDIR/paper_ITP2019.pdf"
cp papers/ITP2019/talk/pres.pdf "$HTMLDIR/slides_ITP2019.pdf"

cp papers/2019_Rennes_Talk/pres.pdf "$HTMLDIR/rennes2019.pdf"
cp papers/2020_Enschede_Talk/pres.pdf "$HTMLDIR/enschede2020.pdf"
cp papers/2021_Enschede_Talk/pres.pdf "$HTMLDIR/enschede2021.pdf"
cp papers/2021_RF_Pres/pres.pdf "$HTMLDIR/RF_pres.pdf"

cp papers/ITP2022/main.pdf "$HTMLDIR/paper_ITP2022.pdf"
cp papers/ITP2022/talk/pres.pdf "$HTMLDIR/slides_ITP2022.pdf"

cp papers/JAR_SI_ITP2022/main.pdf "$HTMLDIR/paper_JAR_SI_ITP2022.pdf"


pandoc -V pagetitle="Isabelle LLVM Parallel" -s index.md > "$HTMLDIR/index.html"


if $UPLOAD; then
  LOCAL_DEST=~/devel/www21-lammich/isabelle_llvm
  rm -rf $LOCAL_DEST
  cp -a "$HTMLDIR" $LOCAL_DEST
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


