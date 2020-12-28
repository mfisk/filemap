#!/bin/sh

fm -vvv map -i '/test/*' wc | sed -e 's,/.*$,,' -e 's,  *, ,g' | sort
fm ls /test/*/*
