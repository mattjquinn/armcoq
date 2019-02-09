#!/bin/sh
rm build/$1.o build/$1
arm-linux-gnueabi-as -o build/$1.o $1.s
arm-linux-gnueabi-ld -o build/$1 build/$1.o
./build/$1
