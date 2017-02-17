#!/bin/bash

for f in examples/*
do
    echo $f
    ./orca.byte $f
    echo "---------------"
done
