#!/bin/bash

for i in *.tmpl.ll; do
  o="${i%.ll}.ml"

  echo $i " --> " $o

  echo "(* Generated code, do not modify *)" > $o
  echo "(* Generated from $i on $(date) by $(whoami) *)" >> $o
  sed -re 's/\$\{([A-Za-z0-9_]*)\}/" ^ \1 ^ "/g; s/\$([A-Za-z0-9_]*)/" ^ \1 ^ "/g; s/^$|^[^&].*/"\0\\n" ^/;s/^& ?//' $i >> $o
done


