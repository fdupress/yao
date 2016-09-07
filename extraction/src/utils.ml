open SFE

type input =
| Rand of int
| Full of bool array

type randomness =
| OTR1 of Prime_field.top_Prime_field_gf_q array
| OTR2 of Prime_field.top_Prime_field_gf_q array * Prime_field.top_Prime_field_gf_q
| GR   of (Word.top_Concrete_W_word * Word.top_Concrete_W_word) array

