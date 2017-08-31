#!/bin/bash

for f in examples/*.kw
do
    if [ -f $f ]
    then
	echo $f
	./orca.byte $f
	echo "---------------"
    fi
done
