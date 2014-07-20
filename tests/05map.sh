#!/bin/sh

fm -vvv map -i '/test/*' wc | sed 's,/.*$,,'
fm ls /test/*/*
