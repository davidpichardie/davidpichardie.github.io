open Lib;;
open Graphics;;

if Array.length(Sys.argv)=2 then affiche_fichier Sys.argv.(1)
else print_string "un argument est necessaire";;
