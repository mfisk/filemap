#!/bin/sh

fm -v map -i '/test/*' "wc | sed 's,/.*$,,'"
fm ls /test/*/*/*
