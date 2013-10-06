#!/bin/sh

fm -v rm -R /test
fm -v mkdir /test
fm -v store data/* /test 
fm -v ls /test
