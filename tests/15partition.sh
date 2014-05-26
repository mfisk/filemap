#!/bin/sh

fm -vvv map -qi '/test/*' "split.sh <"
fm -v ls -1 '/test/*/*split.sh'
