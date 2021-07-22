let string_of_char = make_string 1 ;;

let list_num = ["Pierre",4131;
                "Paul",2134;
                "Jacques",7697;
                "Arthur",2964;
                "Michel",9871];;

let rec appartient a = function
  [] -> false 
| (x,_)::q -> x=a || appartient a q
;;

let rec recherche a = function
  [] -> failwith "objet absent" 
| (x,b)::q -> if x=a then b
              else recherche a q
;;

let rec change a b l = function
     [] -> [(a,b)]
   | (x,c)::q -> if x=a then (a,b)::q
                        else (x,c)::(change_rec q)
;;

let char_list_of_string s=
  let n = string_length s in
  let l = ref [] in
  for i=1 to n do
    l:= s.[n-i] :: !l;
  done;
  !l
;;

let rec string_of_char_list = function
    [] -> ""
  | c::q -> (string_of_char c)^(string_of_char_list q)
;;

type etiquette = Mot of string
               | Prefixe of string ;;

type arbre = Noeud of etiquette * (char * arbre) list ;;

let nom_etiquette = function
    Mot s -> s
  | Prefixe s -> s
;;

let rec plus_grand_prefixe = function
    Noeud (Mot m,_) -> m
  | Noeud (Prefixe _,[c,a]) -> plus_grand_prefixe a
  | Noeud (Prefixe m,_) -> m
;;

let rec arbre_prefixe_liste = fun
 | [] a -> a
 | (c::l) (Noeud (e,fils)) -> if (appartient c fils) then 
                                arbre_prefixe_liste l (recherche c fils)
                            else failwith "ce n'est pas un préfixe"
;;

let arbre_prefixe s a = arbre_prefixe_liste (char_list_of_string s) a;;

let complete a s = plus_grand_prefixe (arbre_prefixe s a);;

let rec concat_list = function
   [] -> []
  |l::q -> l@(concat_list q)
;;

let rec liste_noms = function
   Noeud (Prefixe _,l) -> concat_list (map (fun (c,a) -> liste_noms a) l)
 | Noeud (Mot m,l) -> m::(concat_list (map (fun (c,a) -> liste_noms a) l))
;;

let trouve_complements a s = liste_noms (arbre_prefixe s a);;

let rec insere_mot_liste = fun
  | (Noeud (Prefixe s,fils)) []   -> Noeud (Mot s,fils)
  | (Noeud (Mot s,fils)) []       -> Noeud (Mot s,fils)
  | (Noeud (e,fils)) (c::l) -> 
         if (appartient c fils) then 
               let arbre_c = recherche c fils in
               let nouveau_arbre_c = (insere_mot_liste arbre_c l) in
               (Noeud (e,change c nouveau_arbre_c fils))
         else
               let prefixe = (nom_etiquette e)^(string_of_char c) in
               let arbre_c = Noeud (Prefixe prefixe,[]) in
               Noeud  (e,(c,insere_mot_liste arbre_c l)::fils)
;;

let insere_mot a s = insere_mot_liste a (char_list_of_string s);;

let rec construit_arbre = function
    [] -> Noeud (Prefixe "",[])
  | s::l -> insere_mot (construit_arbre l) s
;;

let arbre1 = construit_arbre ["caml";"café";"cafés";"carte";"java"];;

let arbre2 = construit_arbre ["cantine";"canard";"canari";"candide"];;

let arbre3 = construit_arbre  ["abricot";"allumette";"allumer";"caml";"café";"cafés";"carte";"java"; "cantine";"canard";"canari";"candide"];;









