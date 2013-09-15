#!/bin/sh

fm -v map -i '/test/*' "`pwd`/split.sh < sort > sort -m | uniq -c"
#fm ls /reduce/*/*
