all : deduc affiche mytop valide enleve_superflu simplifie_contextes

deduc : deduc.ml lib.cmo genSousButs.cmo
	ocamlc -o deduc graphics.cma lib.cmo genSousButs.cmo deduc.ml

affiche : affiche.ml lib.cmo
	ocamlc -o affiche graphics.cma lib.cmo affiche.ml

valide : valide.ml lib.cmo
	ocamlc -o valide graphics.cma lib.cmo valide.ml

enleve_superflu : enleve_superflu.ml lib.cmo
	ocamlc -o enleve_superflu graphics.cma lib.cmo enleve_superflu.ml

simplifie_contextes : simplifie_contextes.ml lib.cmo
	ocamlc -o simplifie_contextes graphics.cma lib.cmo simplifie_contextes.ml

mytop : lib.cmo genSousButs.cmo
	ocamlmktop -o mytop graphics.cma lib.cmo genSousButs.cmo

genSousButs.cmo : genSousButs.ml
	ocamlc -c genSousButs.ml

lib.cmo : lib.ml lib.cmi
	ocamlc -pp camlp4o graphics.cma -c lib.ml

lib.cmi : lib.mli
	ocamlc lib.mli

clean :
	rm -f *.cm[iox] *~ deduc affiche mytop valide enleve_superflu simplifie_contextes
