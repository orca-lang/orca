#!/bin/bash

for f in examples/*
do
    echo $f
    ./nanuq.byte $f
    echo "---------------"
done
