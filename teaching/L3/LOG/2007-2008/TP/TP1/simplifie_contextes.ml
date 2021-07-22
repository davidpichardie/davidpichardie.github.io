open Lib;;
open Graphics;;

let simplifie_contextes a = a (* à modifier *) 
;;



(* Pour pouvoir tester la fonction en mode compilé avec ./simplifie_contexte *)
if Array.length(Sys.argv)=2 then 
  affiche (simplifie_contextes (charge Sys.argv.(1)))
else print_string "un argument est necessaire";;
