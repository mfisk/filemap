#!/bin/sh -x

# Split by first word
for w in `awk '{print $1}' $1`; do 
	grep "^$w	" $1 > $w.part
done



