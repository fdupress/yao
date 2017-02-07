open SFE

type input =
| Rand of int
| Full of bool array

type randomness =
| OTR1 of Prime_field.gf_q array
| OTR2 of Prime_field.gf_q array * Prime_field.gf_q
| GR   of (Concrete.W.word * Concrete.W.word) array

