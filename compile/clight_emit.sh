#!/bin/bash

echo "If this fails, remember to do make and make clightgen in the compcert directory!"
compcert/_build/exportclight/Clightgen.native -dc $@
