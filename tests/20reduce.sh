#!/bin/sh

fm -v map -i '/test/*' "`pwd`/split.sh <> sort | uniq -c"
#fm ls /reduce/*/*
