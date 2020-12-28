#!/bin/sh

fm -v map -i '/test/*' "split.sh <> sort -n | uniq -c" | sort -n

