(* On considere le type suivant pour représenter en OCaml les 
   arbres binaires dont les noeuds contiennent des entiers *)
type tree =
  | Leaf                         (* Un arbre peut être une simple feuille *)
  | Node of (int * tree * tree)  (* Un arbre peut être un noeud [Node(i,t1,t2)]
                                    comprenant une valeur entière [i],
                                    un arbre fils gauche [t1] et
                                    un arbre fils droit [t2]               *)

let t1 =
  Node (1,
	Node (2,
	      Node (3,Leaf,Leaf),
	      Node (4,Leaf,Leaf)),
	Node (5,
	      Node (6,Leaf,Leaf),
	      Leaf))

let t2 =
  Node (1,
	Node (5,
	      Leaf,
	      Node (6,Leaf,Leaf)),
	Node (2,
	      Node (4,Leaf,Leaf),
	      Node (3,Leaf,Leaf)))

(* [1pt] Ecrire une fonction qui compte le nombre de noeuds dans un arbre *)
let nb_node (t:tree) : int = assert false (* TODO *)

let _ = assert (nb_node t1 = 6)
					       
(* [1pt] Ecrire une fonction qui compte le nombre de feuilles dans un arbre *)
let nb_leaf (t:tree) : int = assert false (* TODO *)

let _ = assert (nb_leaf t1 = 7)

let max (i:int) (j:int) : int =
  if i<j then j else i

(* [1pt] Ecrire une fonction [max_tree t i] qui renvoie la plus grande valeur
   présente dans l'arbre [t] ou [i] si toutes les valeurs de [t] sont plus petites
   aue [i] *)
let max_tree (t:tree) (i:int) : int = assert false (* TODO *)

let _ = assert (max_tree t1 0 = 6)

(* [1pt] Ecrire une fonction qui calcule l'image miroir d'un arbre *)
let mirror (t:tree) : tree = assert false (* TODO *)

let _ = assert (t1 = mirror t2)
			   
(* [2pt] Ecrire une fonction qui renvoie la liste des valeurs d'un arbre,
   dans un ordre non spécifié.
   De préférence, ne pas utiliser la fonction de concaténation de liste [@] *)
let to_list (t:tree) : int list = assert false (* TODO *)
						
let _ = assert (List.mem 1 (to_list t1))
let _ = assert (List.mem 4 (to_list t1))
let _ = assert (not (List.mem 0 (to_list t1)))
						
(* Les ensembles d'entiers *)
module MO=struct type t = int let compare = compare end
module ISet = Set.Make(MO)

(* [2pt] Ecrire une fonction qui renvoie l'ensemble des valeurs d'un arbre *)
let to_set (t:tree) : ISet.t = assert false (* TODO *)

let _ = assert (ISet.mem 1 (to_set t1))
let _ = assert (ISet.mem 4 (to_set t1))
let _ = assert (not (ISet.mem 0 (to_set t1)))

(* [4pt] Ecrire une fonction
   [fold : (int -> 'a -> 'a) -> 'a -> tree -> 'a]
    qui, de maniere similaire à fold_right sur les listes, applique une
    fonction sur toutes les valeurs d'un arbre.
   Utiliser cette fonction pour re-programmer les fonctions
   [nb_node], [max_tree] et [to_list], sans utiliser d'autres fonctions 
   récursives sur [fold] *)
let rec fold (f:int -> 'a -> 'a) (a:'a) (t:tree) : 'a = assert false (* TODO *)

let nb_node' (t:tree) = assert false (* fold ... TODO *)

let _ = assert (nb_node' t1 = nb_node t1)

let max_tree' (t:tree) (i:int) = assert false (* fold ... TODO *)

let _ = assert (max_tree' t1 0 = max_tree t1 0)

let to_list' (t:tree) = assert false (* fold ... TODO *)

let _ = assert (to_list' t1 = to_list t1)
