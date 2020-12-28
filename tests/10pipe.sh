#!/bin/sh

fm -v map -i '/test/*' "wc | sed 's,/.*$,,'" | sed 's,  *,,g' | sort
fm ls /test/*/*/* | sort
