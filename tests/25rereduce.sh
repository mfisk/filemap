#!/bin/sh

fm -v map -i '/test/*' "split.sh < sort -n > sort -n -m | uniq -c" | sort -n
