#!/bin/bash

for f in examples/*
do
    if [ -f $f ]
    then
	echo $f
	./orca.byte $f
	echo "---------------"
    fi
done
