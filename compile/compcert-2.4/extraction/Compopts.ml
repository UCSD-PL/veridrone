(** val optim_for_size : unit -> bool **)

let optim_for_size = fun _ -> !Clflags.option_Osize

(** val propagate_float_constants : unit -> bool **)

let propagate_float_constants = fun _ -> !Clflags.option_ffloatconstprop >= 1

(** val generate_float_constants : unit -> bool **)

let generate_float_constants = fun _ -> !Clflags.option_ffloatconstprop >= 2

(** val va_strict : unit -> bool **)

let va_strict = fun _ -> false

(** val eliminate_tailcalls : unit -> bool **)

let eliminate_tailcalls = fun _ -> !Clflags.option_ftailcalls

