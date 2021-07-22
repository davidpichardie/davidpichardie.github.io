all : tp1.html regles.html lib.html tp1.tar

tp1.html : tp1.tex
	hevea my.hva tp1.tex; imagen tp1
regles.html : regles.tex
	hevea my.hva regles.tex; imagen regles 
lib.html : ../Corrige/lib.mli
	ocamldoc -html ../Corrige/lib.mli

LIBML = Makefile lib.ml lib.mli deduc.ml valide.ml affiche.ml 
VIDEML = genSousButs.ml enleve_superflu.ml simplifie_contextes.ml

TP1 :
	mkdir TP1; \
	for i in $(LIBML); do cp ../Corrige/$$i TP1/; done; \
	for i in $(VIDEML); do cp ../Corrige/$$i.vide TP1/$$i; done

tp1.tar : TP1
	cd TP1; make clean; cd ..; tar -cf tp1.tar TP1/

clean :
	rm -f *.html *.aux *.log *~ *.gif *.htoc *.haux *.dvi *.image.tex tp1.tar
	rm -fr TP1

