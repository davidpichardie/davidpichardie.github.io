
(** Quelques fonctions pour nous aider durant ces Tps... *)

(** {6 Op�rations sur les listes }*)

val do_list : ('a -> unit) -> 'a list -> unit 
val map : ('a -> 'b) -> 'a list -> 'b list 


(** {6 Op�rations sur les ensembles }*)

type 'a ens
(** le type des ensembles d'�l�ment de type 'a quelconque. *)
val vide : 'a ens
(** l'ensemble vide. *)
val estVide : 'a ens -> bool
(** teste  si un ensemble est vide. *)
val membre : 'a -> 'a ens -> bool
(** [(membre e s)] teste si l'�l�ment [e] appartient � l'ensemble [s]. *)
val ajoute : 'a -> 'a ens -> 'a ens
(** [(ajoute e s)] renvoie un ensemble contenant tous les �l�ments de [s], plus l'�l�ment [e]. *)
val enleve : 'a -> 'a ens -> 'a ens
(** [(enleve e s)] renvoie un ensemble contenant tous les �l�ments de [s], sauf l'�l�ment [e]. *)
val union : 'a ens -> 'a ens -> 'a ens
(** union d'ensembles *)
val inter : 'a ens -> 'a ens -> 'a ens
(** intersection d'ensembles *)
val eq : 'a ens -> 'a ens -> bool
(** [(eq s1 s2)] teste si les ensembles [s1] et [s2] sont �gaux (d'un point de vue ensembliste). *)
val enumere : 'a ens -> 'a list
(** [(enumere s)] renvoie la liste des �l�ment de [s]. *)

(** {6 Op�rations sur les formules }*)

type formule =
    Faux
  | Var of string
  | Et of formule * formule
  | Ou of formule * formule
  | Imp of formule * formule


val parse : string -> formule
(** [(parse s)] calcule la formule repr�sent�e par la cha�ne de caract�re [s]. *)
val print : formule -> string
(** [(print f)] calcule la cha�ne de caract�re repr�sentant la formule [f]. *)

type sequent = {contexte : formule ens ; but : formule }

val print_sequent : sequent -> string


(** {6 Op�rations sur les arbres de preuve }*)

type arbreDePreuve =
    RegleAx of sequent
  | RegleIntroImp of sequent * arbreDePreuve
  | RegleElimImp of sequent * arbreDePreuve * arbreDePreuve
  | RegleIntroEt of sequent * arbreDePreuve * arbreDePreuve
  | RegleElimEt1 of sequent * arbreDePreuve
  | RegleElimEt2 of sequent * arbreDePreuve
  | RegleIntroOu1 of sequent * arbreDePreuve
  | RegleIntroOu2 of sequent * arbreDePreuve
  | RegleElimOu of sequent * arbreDePreuve * arbreDePreuve * arbreDePreuve
  | RegleElimFalse of sequent * arbreDePreuve
  | RegleIntroNon of sequent * arbreDePreuve * arbreDePreuve
  | RegleElimNon of sequent * arbreDePreuve * arbreDePreuve
  | RegleTiersExclu of sequent
  | RegleAbsurde of sequent * arbreDePreuve
  | RegleElimNonNon of sequent * arbreDePreuve
  | RegleLemme of sequent * string

val affiche_fichier : string -> unit
(** affiche l'arbre de preuve contenu dans un fichier. (q pour quitter)*)
val affiche : arbreDePreuve -> unit
(** affiche l'arbre de preuve (dans le mode interactif) *)
val charge : string -> arbreDePreuve
(** renvoie l'arbre de preuve contenu dans un fichier *)
val sauve : arbreDePreuve -> string -> unit
(** sauve un arbre dans un fichier *)
val fichier_existe : string -> bool
(** v�rifie si un fichier existe dans le r�pertoire courant *)
val valide : arbreDePreuve -> bool
(** v�rifie si un arbre de preuve est valide vis � vis des r�gles de la d�duction naturelle *)

(** {6 Les commandes du programme de preuve int�ractive  }*)

type commande =
    Stop      (** interrompt la preuve en cours *)
  | Saut      (** permet de r�aliser une permutation circulaire sur la liste des sous-buts *) 
  | Annule    (** annule la derni�re r�gle de d�duction appliqu�e *)
  | Centre    (** Centre la fen�tre graphique sur le but courant *)
  | Aide
  | Lemme of string
  | Ax
  | IntroImp
  | ElimImp of formule
  | IntroEt
  | ElimEt1 of formule
  | ElimEt2 of formule
  | IntroOu1
  | IntroOu2
  | ElimOu of formule*formule
  | ElimFaux
  | ElimNon of formule
  | IntroNon of formule
  | ElimNonNon
  | TiersExclu
  | Absurde

val deduc : (sequent -> commande -> sequent list * string) -> unit
(** fonction utilis�e pour construire le programme de preuve interactive. *)

