type t

val of_string : string -> t
val to_string : t -> string
  
val zero : t

val add_mod : t -> t -> t -> t
val opp_mod : t -> t -> t
val sub_mod : t -> t -> t -> t
val div_mod : t -> t -> t -> t
val powm    : t -> t -> t -> t
val random  : t -> t
