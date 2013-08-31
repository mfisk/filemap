#!/bin/sh

fm -v map -qi '/test/*' "`pwd`/split.sh <"
fm -v ls /test/*/*split.sh
