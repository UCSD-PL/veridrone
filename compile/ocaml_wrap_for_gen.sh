#!/bin/bash

#
# invoke ocaml with the right arguments so that it's able to access
# the internal compcert libraries containing the code for
# pretty-printing
#

ocaml -init clightgen_loads.ocamlinit \
    -I ./compcert/_build/driver -I ./compcert/_build/common \
    -I ./compcert/_build/backend -I ./compcert/_build/ia32 \
    -I ./compcert/_build/extraction -I ./compcert/_build/lib \
    -I ./compcert/_build/exportclight -I ./compcert/_build/cparser \
    -I ./compcert/_build/cfrontend
