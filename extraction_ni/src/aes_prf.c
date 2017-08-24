/**
 JustGarble AES OCaml wrapper.
*/

#include <stdio.h>
#include <stdlib.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

#include "aes.h"

value aes(value in, value out,
		value kp) {
  CAMLparam3(in,out,kp);
  int i;

  unsigned char *in1 = String_val(in);
  unsigned char out1[16];
  unsigned char *kp1 = String_val(kp);

  unsigned char in2[16];
  for (i=0;i<17;i++)
    in2[i] = in1[i];
  
  AES_KEY key;

  AES_set_encrypt_key(kp,128,&key);
  
  AES_encrypt(in2,out1,&key);
  
  CAMLreturn(String_val(out1));
}
