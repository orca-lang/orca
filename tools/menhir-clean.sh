#!/bin/bash

if [ -f src/parser.ml ]; then
   rm src/parser.ml
fi
if [ -f src/parser.mli ]; then
   rm src/parser.mli
fi
if [ -f src/parser.annot ]; then
   rm src/parser.annot
fi
