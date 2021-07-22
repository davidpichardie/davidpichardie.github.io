open Lib;;

let genSousButs seq com = 
  match (seq.contexte,seq.but,com) with
      (*  A COMPLETER *)
    | (g, Et (f1,f2), IntroEt) -> 
	[{contexte=g; but=f1};
    	 {contexte=g; but=f2}],"IntroEt"
    | (_, _, _) -> [],"erreur";;

