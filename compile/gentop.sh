#!/bin/bash

ocamlmktop -o clightgen_shell \
    -I ./compcert/_build/driver -I ./compcert/_build/common \
    -I ./compcert/_build/backend -I ./compcert/_build/ia32 \
    -I ./compcert/_build/extraction -I ./compcert/_build/lib \
    -I ./compcert/_build/exportclight -I ./compcert/_build/cparser \
    -I ./compcert/_build/cfrontend \
    Datatypes.d.cmo Bool.d.cmo Peano.d.cmo \
    BinPos.d.cmo BinNat.d.cmo BinInt.d.cmo \
    Zpower.d.cmo Specif.d.cmo List0.d.cmo \
    ZArith_dec.d.cmo Coqlib.d.cmo Integers.d.cmo \
    Fcore_Zaux.d.cmo Zbool.d.cmo Fcalc_bracket.d.cmo \
    Fcore_digits.d.cmo Fcore_FLT.d.cmo Fcalc_round.d.cmo \
    Fappli_IEEE.d.cmo Fappli_IEEE_bits.d.cmo Fappli_IEEE_extra.d.cmo \
    Archi.d.cmo Floats.d.cmo Camlcoq.cmo AST.d.cmo Ctypes.d.cmo \
    Csyntax.d.cmo str.cma PrintCsyntax.cmo PrintAST.cmo \
    Clight.d.cmo PrintClight.cmo
