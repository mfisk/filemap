#!/bin/sh

rm -Rf /tmp/fmtest
fm -v init
find /tmp/fmtest | sort

