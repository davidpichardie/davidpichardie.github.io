open Lib;;
open Graphics;;

let enleve_superflu a = a (* à modifier *) 
;;



(* Pour pouvoir tester la fonction en mode compilé avec ./enleve_superflu.ml *)
if Array.length(Sys.argv)=2 then 
  affiche (enleve_superflu (charge Sys.argv.(1)))
else print_string "un argument est necessaire";;
