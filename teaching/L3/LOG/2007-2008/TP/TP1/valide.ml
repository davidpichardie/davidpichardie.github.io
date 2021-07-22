open Lib;;

if Array.length(Sys.argv)=2 then
  let _ = valide (charge Sys.argv.(1)) in ()
