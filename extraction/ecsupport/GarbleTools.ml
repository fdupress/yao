(* GarbleTools *)

module ForLoop = struct

(* GarbleTools.ForLoop.range *)
let top_GarbleTools_ForLoop_range i j st f =
  let st = ref st in
  for k = i to (j - 1) do
    st := f k !st;
  done;
  !st

end
