open Graphics

type formule =
  | Faux
  | Var of string
  | Et of formule*formule
  | Ou of formule*formule
  | Imp of formule*formule

type 'a ens = Empty | Node of 'a ens * 'a * 'a ens * int

let height = function
    Empty -> 0
  | Node(_, _, _, h) -> h

let create l x r =
  let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
  Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

let bal l x r =
  let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
  if hl > hr + 2 then begin
    match l with
      Empty -> invalid_arg "Set.bal"
    | Node(ll, lv, lr, _) ->
        if height ll >= height lr then
          create ll lv (create lr x r)
        else begin
          match lr with
            Empty -> invalid_arg "Set.bal"
          | Node(lrl, lrv, lrr, _)->
              create (create ll lv lrl) lrv (create lrr x r)
        end
  end else if hr > hl + 2 then begin
    match r with
      Empty -> invalid_arg "Set.bal"
    | Node(rl, rv, rr, _) ->
        if height rr >= height rl then
          create (create l x rl) rv rr
        else begin
          match rl with
            Empty -> invalid_arg "Set.bal"
          | Node(rll, rlv, rlr, _) ->
              create (create l x rll) rlv (create rlr rv rr)
        end
  end else
    Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

let rec join l x r =
  match bal l x r with
    Empty -> invalid_arg "Set.join"
  | Node(l', x', r', _) as t' ->
      let d = height l' - height r' in
      if d < -2 || d > 2 then join l' x' r' else t'

let rec merge t1 t2 =
  match (t1, t2) with
    (Empty, t) -> t
  | (t, Empty) -> t
  | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
      bal l1 v1 (bal (merge r1 l2) v2 r2)

let rec concat t1 t2 =
  match (t1, t2) with
    (Empty, t) -> t
  | (t, Empty) -> t
  | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
      join l1 v1 (join (concat r1 l2) v2 r2)

let rec split x = function
    Empty ->
      (Empty, None, Empty)
  | Node(l, v, r, _) ->
      let c = compare x v in
      if c = 0 then (l, Some v, r)
      else if c < 0 then
        let (ll, vl, rl) = split x l in (ll, vl, join rl v r)
      else
        let (lr, vr, rr) = split x r in (join l v lr, vr, rr)

let vide = Empty

let estVide = function Empty -> true | _ -> false

let rec membre x = function
    Empty -> false
  | Node(l, v, r, _) ->
      let c = compare x v in
      c = 0 || membre x (if c < 0 then l else r)

let rec ajoute x = function
    Empty -> Node(Empty, x, Empty, 1)
  | Node(l, v, r, _) as t ->
      let c = compare x v in
      if c = 0 then t else
      if c < 0 then bal (ajoute x l) v r else bal l v (ajoute x r)

let rec enleve x = function
    Empty -> Empty
  | Node(l, v, r, _) ->
      let c = compare x v in
      if c = 0 then merge l r else
      if c < 0 then bal (enleve x l) v r else bal l v (enleve x r)

let rec union s1 s2 =
  match (s1, s2) with
    (Empty, t2) -> t2
  | (t1, Empty) -> t1
  | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
      if h1 >= h2 then
        if h2 = 1 then ajoute v2 s1 else begin
          let (l2, _, r2) = split v1 s2 in
          join (union l1 l2) v1 (union r1 r2)
        end
      else
        if h1 = 1 then ajoute v1 s2 else begin
          let (l1, _, r1) = split v2 s1 in
          join (union l1 l2) v2 (union r1 r2)
        end

let rec inter s1 s2 =
  match (s1, s2) with
    (Empty, t2) -> Empty
  | (t1, Empty) -> Empty
  | (Node(l1, v1, r1, _), t2) ->
      match split v1 t2 with
        (l2, None, r2) ->
          concat (inter l1 l2) (inter r1 r2)
      | (l2, Some _, r2) ->
          join (inter l1 l2) v1 (inter r1 r2)

let rec compare_aux l1 l2 =
  match (l1, l2) with
    ([], []) -> 0
  | ([], _)  -> -1
  | (_, []) -> 1
  | (Empty :: t1, Empty :: t2) ->
      compare_aux t1 t2
  | (Node(Empty, v1, r1, _) :: t1, Node(Empty, v2, r2, _) :: t2) ->
      let c = compare v1 v2 in
      if c <> 0 then c else compare_aux (r1::t1) (r2::t2)
  | (Node(l1, v1, r1, _) :: t1, t2) ->
      compare_aux (l1 :: Node(Empty, v1, r1, 0) :: t1) t2
  | (t1, Node(l2, v2, r2, _) :: t2) ->
      compare_aux t1 (l2 :: Node(Empty, v2, r2, 0) :: t2)

let compare s1 s2 =
  compare_aux [s1] [s2]

let eq s1 s2 =
  compare s1 s2 = 0

let rec enumere_aux accu = function
    Empty -> accu
  | Node(l, v, r, _) -> enumere_aux (v :: enumere_aux accu r) l

let enumere s =
  enumere_aux [] s

type sequent = {contexte : formule ens ; but : formule }

type arbreN =
  | Regle of arbreDePreuveNoeud
and arbreDePreuveNoeud =
 {nom : string;
  sequent : sequent;
  sousButs : (arbreN list)}

type arbreDePreuveSize =
  | Regles of arbreDePreuveNoeudSize
and arbreDePreuveNoeudSize =
 {id : int;
  mutable size : int*int*int*int;
  sizeseq : int;
  mutable name : string;
  seq : sequent;
  peres : arbreDePreuveSize list;
  mutable ssButs : (arbreDePreuveSize list)}

type arbreDePreuve =
  | RegleAx of sequent
  | RegleIntroImp of sequent*arbreDePreuve
  | RegleElimImp of sequent*arbreDePreuve*arbreDePreuve
  | RegleIntroEt of sequent*arbreDePreuve*arbreDePreuve
  | RegleElimEt1 of sequent*arbreDePreuve
  | RegleElimEt2 of sequent*arbreDePreuve
  | RegleIntroOu1 of sequent*arbreDePreuve
  | RegleIntroOu2 of sequent*arbreDePreuve
  | RegleElimOu of sequent*arbreDePreuve*arbreDePreuve*arbreDePreuve
  | RegleElimFalse of sequent*arbreDePreuve
  | RegleIntroNon of sequent*arbreDePreuve*arbreDePreuve
  | RegleElimNon of sequent*arbreDePreuve*arbreDePreuve
  | RegleTiersExclu of sequent
  | RegleAbsurde of sequent*arbreDePreuve
  | RegleElimNonNon of sequent*arbreDePreuve
  | RegleLemme of sequent*string

exception Erreur of string

let rec convertarbreN2arbre = function 
  | RegleAx s -> Regle {nom="Ax"; sequent=s; sousButs=[]}
  | RegleIntroImp (s,a1) -> Regle {nom="IntroImp"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleElimImp (s,a1,a2) -> Regle {nom="ElimImp"; sequent=s; sousButs=[convertarbreN2arbre a1; convertarbreN2arbre a2]}
  | RegleIntroEt (s,a1,a2) -> Regle {nom="IntroEt"; sequent=s; sousButs=[convertarbreN2arbre a1; convertarbreN2arbre a2]}
  | RegleElimEt1 (s,a1) -> Regle {nom="ElimEt1"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleElimEt2 (s,a1) -> Regle {nom="ElimEt2"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleIntroOu1 (s,a1) -> Regle {nom="IntroOu1"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleIntroOu2 (s,a1) -> Regle {nom="IntroOu2"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleElimOu (s,a1,a2,a3) -> Regle {nom="ElimOu"; sequent=s; sousButs=[convertarbreN2arbre a1; convertarbreN2arbre a2; convertarbreN2arbre a3]}
  | RegleElimFalse (s,a1) -> Regle {nom="ElimFalse"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleIntroNon (s,a1,a2) -> Regle {nom="IntroNon"; sequent=s; sousButs=[convertarbreN2arbre a1; convertarbreN2arbre a2]}
  | RegleElimNon (s,a1,a2) -> Regle {nom="ElimNon"; sequent=s; sousButs=[convertarbreN2arbre a1; convertarbreN2arbre a2]}
  | RegleTiersExclu s -> Regle {nom="TiersExclu"; sequent=s; sousButs=[]}
  | RegleAbsurde (s,a1) -> Regle {nom="Absurde"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleElimNonNon (s,a1) -> Regle {nom="ElimNonNon"; sequent=s; sousButs=[convertarbreN2arbre a1]}
  | RegleLemme (s,f) -> Regle {nom=f; sequent=s; sousButs=[]}

let rec testNM = function 
  | RegleAx s -> true
  | RegleIntroImp (s,a1) -> testNM a1
  | RegleElimImp (s,a1,a2) -> testNM a1 && testNM a2
  | RegleIntroEt (s,a1,a2) -> testNM a1 && testNM a2
  | RegleElimEt1 (s,a1) -> testNM a1
  | RegleElimEt2 (s,a1) -> testNM a1
  | RegleIntroOu1 (s,a1) -> testNM a1
  | RegleIntroOu2 (s,a1) -> testNM a1
  | RegleElimOu (s,a1,a2,a3) -> testNM a1 && testNM a2 && testNM a3
  | RegleElimFalse (s,a1) -> false
  | RegleIntroNon (s,a1,a2) -> testNM a1 && testNM a2
  | RegleElimNon (s,a1,a2) -> false
  | RegleTiersExclu s -> false
  | RegleAbsurde (s,a1) -> false
  | RegleElimNonNon (s,a1) -> false
  | _ -> false

let rec convertarbre2arbreN = function Regles r ->
  match r with 
      {name="Ax"; seq=s; ssButs=[]} -> RegleAx s
    | {name="Ax"; seq=s; ssButs=l} -> raise (Erreur "La règle Ax ne nécessite aucun sous-buts")

    | {name="IntroImp"; seq=s; ssButs=[r1]} -> RegleIntroImp (s,convertarbre2arbreN r1)
    | {name="IntroImp"; seq=s; ssButs=l} -> raise (Erreur "La règle IntroImp nécessite 1 sous-but")

    | {name="ElimImp"; seq=s; ssButs=[r1;r2]} -> RegleElimImp (s,convertarbre2arbreN r1,convertarbre2arbreN r2)
    | {name="ElimImp"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimImp nécessite 2 sous-buts")

    | {name="IntroEt"; seq=s; ssButs=[r1;r2]} -> RegleIntroEt (s,convertarbre2arbreN r1,convertarbre2arbreN r2)
    | {name="IntroEt"; seq=s; ssButs=l} -> raise (Erreur "La règle IntroEt nécessite 2 sous-buts")

    | {name="ElimEt1"; seq=s; ssButs=[r1]} -> RegleElimEt1 (s,convertarbre2arbreN r1)
    | {name="ElimEt1"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimEt1 nécessite 1 sous-but")
    | {name="ElimEt2"; seq=s; ssButs=[r1]} -> RegleElimEt2 (s,convertarbre2arbreN r1)
    | {name="ElimEt2"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimEt2 nécessite 1 sous-but")

    | {name="IntroOu1"; seq=s; ssButs=[r1]} -> RegleIntroOu1 (s,convertarbre2arbreN r1)
    | {name="IntroOu1"; seq=s; ssButs=l} -> raise (Erreur "La règle IntroOu1 nécessite 1 sous-but")
    | {name="IntroOu2"; seq=s; ssButs=[r1]} -> RegleIntroOu2 (s,convertarbre2arbreN r1)
    | {name="IntroOu2"; seq=s; ssButs=l} -> raise (Erreur "La règle IntroOu2 nécessite 1 sous-but")

    | {name="ElimOu"; seq=s; ssButs=[r1;r2;r3]} -> RegleElimOu (s,convertarbre2arbreN r1,convertarbre2arbreN r2,convertarbre2arbreN r3)
    | {name="ElimOu"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimOu nécessite 3 sous-buts")

    | {name="ElimFalse"; seq=s; ssButs=[r1]} -> RegleElimFalse (s,convertarbre2arbreN r1)
    | {name="ElimFalse"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimFalse nécessite 1 sous-but")

    | {name="IntroNon"; seq=s; ssButs=[r1;r2]} -> RegleIntroNon (s,convertarbre2arbreN r1,convertarbre2arbreN r2)
    | {name="IntroNon"; seq=s; ssButs=l} -> raise (Erreur "La règle IntroNon nécessite 2 sous-buts")
    | {name="ElimNon"; seq=s; ssButs=[r1;r2]} -> RegleElimNon (s,convertarbre2arbreN r1,convertarbre2arbreN r2)
    | {name="ElimNon"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimNon nécessite 2 sous-buts")

    | {name="TiersExclu"; seq=s; ssButs=[]} -> RegleTiersExclu s
    | {name="TiersExclu"; seq=s; ssButs=l} -> raise (Erreur "La règle TiersExclu ne nécessite aucun sous-buts")

    | {name="Absurde"; seq=s; ssButs=[r1]} -> RegleAbsurde (s,convertarbre2arbreN r1)
    | {name="Absurde"; seq=s; ssButs=l} -> raise (Erreur "La règle Absurde nécessite 1 sous-but")

    | {name="ElimNonNon"; seq=s; ssButs=[r1]} -> RegleElimNonNon (s,convertarbre2arbreN r1)
    | {name="ElimNonNon"; seq=s; ssButs=l} -> raise (Erreur "La règle ElimNonNon nécessite 1 sous-but")

    | _ -> raise (Erreur ("Règle "^((r.name))^" inconnue"))

type commande =
    Stop
  | Saut
  | Annule
  | Centre
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

let rec hauteur_formule = function
  | Faux -> 0
  | Var id -> 0
  | Et (f1,f2) -> 1+(max (hauteur_formule f1) (hauteur_formule f2))
  | Ou (f1,f2) -> 1+(max (hauteur_formule f1) (hauteur_formule f2))
  | Imp (f1,f2) -> 1+(max (hauteur_formule f1) (hauteur_formule f2))

let do_list f = List.fold_left (fun a b -> (f b)) ()

let map = List.map

let axApplicable = function
  | seq -> true

let introImpApplicable = function
  | seq -> true

let elimImpApplicable = function
  | seq -> true

let introEtApplicable = function
  | seq -> true

let elimEt1Applicable = function
  | seq -> true

let elimEt2Applicable = function
  | seq -> true

let introOu1Applicable = function
  | seq -> true

let introOu2Applicable = function
  | seq -> true

let elimOuApplicable = function
  | seq -> true

let elimFauxApplicable = function
  | seq -> true

let introNonApplicable = function
  | seq -> true

let elimNonApplicable = function
  | seq -> true

let tiersExcluApplicable = function
  | seq -> true

let absurdeApplicable = function
  | seq -> true

let elimNonNonApplicable = function
  | seq -> true

let listeReglesApplicables = function 
  | seq ->
      let l = ref [] 
      in
      begin
	if elimNonNonApplicable seq then l := "ElimNonNon"::!l;
	if absurdeApplicable seq then l := "Absurde"::!l;
	if tiersExcluApplicable seq then l := "TiersExclu"::!l;
	if elimNonApplicable seq then l := "ElimNon"::!l;
	if introNonApplicable seq then l := "IntroNon"::!l;
	if elimFauxApplicable seq then l := "ElimFaux"::!l;
	if elimOuApplicable seq then l := "ElimOu"::!l;
	if introOu2Applicable seq then l := "IntroOu2"::!l;
	if introOu1Applicable seq then l := "IntroOu1"::!l;
	if elimEt2Applicable seq then l := "ElimEt2"::!l;
	if elimEt1Applicable seq then l := "ElimEt1"::!l;
	if introEtApplicable seq then l := "IntroEt"::!l;
	if elimImpApplicable seq then l := "ElimImp"::!l;
	if introImpApplicable seq then l := "IntroImp"::!l;
	if axApplicable seq then l := "Ax"::!l;
	!l
      end
	
let rec print_rec = function
  | Faux -> "Faux"
  | Var id -> id
  | Imp (f,Faux) -> "~"^(print_rec f)
  | Et (f1,f2) -> "("^(print_rec f1)^"&"^(print_rec f2)^")"
  | Ou (f1,f2) -> "("^(print_rec f1)^"|"^(print_rec f2)^")"
  | Imp (f1,f2) -> "("^(print_rec f1)^"=>"^(print_rec f2)^")"

let print = function
  | Faux -> "Faux"
  | Var id -> id
  | Imp (f,Faux) -> "~"^(print_rec f)
  | Et (f1,f2) -> (print_rec f1)^"&"^(print_rec f2)
  | Ou (f1,f2) -> (print_rec f1)^"|"^(print_rec f2)
  | Imp (f1,f2) -> (print_rec f1)^"=>"^(print_rec f2)

let init_graph () =
  open_graph " 1024x300+0+0";
  Graphics.auto_synchronize false

let symbol () =
  set_font ("-adobe-symbol-*--12-*")

let courier8 () =
set_font ("-adobe-courier-*--10-*")

let symbol8 () =
  set_font ("-adobe-symbol-*--10-*")

let courier () =
set_font ("-adobe-courier-*--12-*")

let size_courier8 s =
  courier8(); text_size s
let size_symbol8 s =
  symbol8(); text_size s
let dec_symb = 2

let size_mixte a s=
  let (a,b)=size_courier8 a in
  let (c,d)=size_symbol8 s in
    (a+c,b+dec_symb)
let print_mixte a b =
  courier8(); draw_string a;
  rmoveto 0 (-dec_symb);
  symbol8(); draw_string b;
  rmoveto 0 dec_symb



let regle_size = function
    "ElimImp" -> size_mixte "e" "\222"
  | "IntroImp" -> size_mixte "i" "\222"
  | "IntroEt" -> size_mixte "i" "\217"
  | "ElimEt1" -> size_mixte "e1" "\217"
  | "ElimEt2" -> size_mixte "e2" "\217"
  | "IntroOu1" -> size_mixte "i1" "\218"
  | "IntroOu2" -> size_mixte "i2" "\218"
  | "ElimOu" -> size_mixte "e" "\218"
  | "ElimFaux" -> size_mixte "e" "\216"
  | "ElimNon" -> size_mixte "e" "\216"
  | "IntroNon" -> size_mixte "i" "\216"
  | "ElimNonNon" -> size_mixte "e" "\216\216"
  | "TiersExclu" -> size_courier8 "TE"
  | "Absurde" -> size_courier8 "Abs"
  | "?" -> courier(); text_size "?"
  | r -> size_courier8 r

let print_regle = function
    "ElimImp" -> print_mixte "e" "\222"
  | "IntroImp" -> print_mixte "i" "\222"
  | "IntroEt" -> print_mixte "i" "\217"
  | "ElimEt1" -> print_mixte "e1" "\217"
  | "ElimEt2" -> print_mixte "e2" "\217"
  | "IntroOu1" -> print_mixte "i1" "\218"
  | "IntroOu2" -> print_mixte "i2" "\218"
  | "ElimOu" -> print_mixte "e" "\218"
  | "ElimFaux" -> print_mixte "e" "\094"
  | "ElimNon" -> print_mixte "e" "\216"
  | "IntroNon" -> print_mixte "i" "\216"
  | "ElimNonNon" -> print_mixte "e" "\216\216"
  | "TiersExclu" -> courier8(); draw_string "TE"
  | "Absurde" -> courier8(); draw_string "Abs"
  | "?" -> courier(); draw_string "?"
  | r -> courier8(); draw_string r



let rec print_size_rec = function
  | Faux -> symbol(); (fst (text_size "\094"))
  | Var id -> 
      courier (); 
      let (x,_)= text_size id in
	symbol (); x
  | Imp (f,Faux) ->
      (fst (text_size "\216"))+
        (print_size_rec f)
  | Et (f1,f2) -> 
      (fst (text_size "(\217)"))+
        (print_size_rec f1) +
          (print_size_rec f2)
   | Ou (f1,f2) -> 
      (fst (text_size "(\218)"))+
        (print_size_rec f1) +
          (print_size_rec f2)
  | Imp (f1,f2) ->
      (fst (text_size "(\222)"))+
        (print_size_rec f1) +
          (print_size_rec f2)

let print_size f =
  symbol (); print_size_rec f

let rec print_size_contexte = function
    [] -> 0
  | [f] -> print_size_rec f
  | f::l -> 
      courier (); 
      let (x,_) = text_size "," in
      symbol ();
      (print_size_rec f) +
       (List.fold_left (fun a f -> (a+x+
			             ((print_size_rec f))))
        0 l)

let print_size_sequent s =
  symbol (); 
  (print_size_contexte (enumere s.contexte)) +
  11 +
  (print_size_rec s.but)

let color_syntaxe = blue

let rec print_graph_rec = function
  | Faux -> symbol(); draw_char '\094'
  | Var id -> 
      courier (); draw_string id; symbol ()
  | Imp (f,Faux) ->
      draw_char '\216';
      print_graph_rec f
  | Et (f1,f2) -> 
      set_color color_syntaxe;
      draw_char '(';
      set_color black;
      print_graph_rec f1;
      set_color color_syntaxe;
      draw_char '\217';
      set_color black;
      print_graph_rec f2;
      set_color color_syntaxe;
      draw_char ')';
      set_color black
  | Ou (f1,f2) -> 
      set_color color_syntaxe;
      draw_char '(';
      set_color black;
      print_graph_rec f1;
      set_color color_syntaxe;
      draw_char '\218';
      set_color black;
      print_graph_rec f2;
      set_color color_syntaxe;
      draw_char ')';
      set_color black
  | Imp (f1,f2) ->
      set_color color_syntaxe;
      draw_char '(';
      set_color black;
      print_graph_rec f1;
      set_color color_syntaxe;
      draw_char '\222';
      set_color black;
      print_graph_rec f2;
      set_color color_syntaxe;
      draw_char ')';
      set_color black

let print_graph f =
  symbol (); print_graph_rec f

let color_seq = magenta
let color_nom = red

let print_symb () =
  set_color color_seq;
  rmoveto 2 3;
  rlineto 0 6;
  rmoveto 0 (-3);
  rlineto 5 0;
  rmoveto 4 (-6);
  set_color black

let rec print_graph_contexte = function
    [] -> ()
  | [f] -> print_graph_rec f
  | f::l ->
      print_graph_rec f;
      do_list (fun f -> (courier ();
			 set_color color_seq;
			 draw_char ',';
			 set_color black;
			 symbol ();
			 print_graph_rec f)) l

let print_graph_sequent s =
  symbol (); 
  let n = (print_size_sequent s) in
  print_graph_contexte (enumere s.contexte);
  print_symb ();
  print_graph_rec s.but;
  rmoveto (-n) 15;
  rlineto n 0;
  rmoveto (-n) 3

let print_graph_sequent2 s =
  symbol (); 
  let n = (print_size_sequent s) in
  print_graph_contexte (enumere s.contexte);
  print_symb ();
  print_graph_rec s.but;
  rmoveto (-n) 0

let espace_arbre = 10
let espace_nom = 4

let rec print_size_arbre = function Regles r ->               (*   resultat (a,b,c,d,e)            *)
  let s = r.sizeseq in                 
  let (a,b,c) = print_size_arbre_list r.ssButs in
    courier ();
    if s>b then                                               (* _________________________________ *)
      let c'=(s-b)/2 in                                       (*          xxxxxxxxxxxxx            *)
      let a'=(max (c-c') 0) in
      let b1'=(max (a-c-b-c') 0) in
      let b2' = 2*espace_nom+(fst (regle_size r.name)) in
	begin                                                 (*        -----------------          *)	   
	  r.size <- (a',max b1' b2',c',0)
	end                                                   (*             sequent               *)
    else                                                      (* <-----><---><-----><---><-------> *)
      let d'=(b-s)/2 in                                       (*    a     d     e     d      b     *)
      let b1 = a-c-b in
      let b2 = 2*espace_nom+(fst (regle_size r.name)) in
	r.size <- (c,max b1 b2,0,d')
and print_size_arbre_list = function
    [] -> (0,0,0)
  | [Regles r] -> 
      let (a,b,c,d)= r.size in
      let e = r.sizeseq in
             (a+b+d+d+e,e,a+d)
  | (Regles r)::q -> 
            let (a,b,c,d)= r.size in
	    let e = r.sizeseq in
            let (a',b',c')= print_size_arbre_list q in
              (a'+espace_arbre+a+b+d+d+e,
               b'+c'+b+d+e+espace_arbre,
	       a+d)


let rec elimine_comment flux=
  match flux with parser
    [< ''A'..'Z'|'a'..'z'|'0'..'9'|'è'|'à'|'é'|'-'|' '|'_'|':'|'.' >] -> elimine_comment flux
  | [< ''*';'')' >] -> ();;

let rec saut_b flux= 
  match flux with parser 
    [< '' '|'\t'|'\n' >] -> saut_b flux
  | [< >] -> ();;

let rec list_char flux= 
  match flux with parser 
    [< ''A'..'Z'|'a'..'z'|'0'..'9'|'_'|'è'|'é' as c >] -> c::(list_char flux)
  | [< >]->[];;

let rec list_num flux= 
  match flux with parser 
    [< ''0'..'9' as c >] -> ((Char.code c)-(Char.code '0'))::(list_num flux)
  | [< >]->[];;

let rec list_to_string s i = function 
    [] -> () 
  | x::l -> s.[i]<-x; (list_to_string s (i+1) l);;

let rec list_to_int_rec acc = function
  [] -> acc
  | x::q -> list_to_int_rec (10*acc+x) q
let list_to_int = list_to_int_rec 0

type lexeme = 
    Ident of string 
  | Int of int
  | MC of string ;;

let lire_minus flux =
  match flux with parser 
  | [< ''0'..'9' as c >] -> 
         (let l=((Char.code c)-(Char.code '0'))::(list_num flux) in
           Int (-(list_to_int l)))
  | [< ''>'>] -> MC "Imp"

let lire_fleche flux =
  match flux with parser 
  | [< ''-' >] -> MC "<--"

let lire_brack flux =
  match flux with parser 
  | [< ''-' >] -> lire_fleche flux


let rec lire_lexeme flux = 
  saut_b flux;
  match flux with parser 
     [< '','>] -> MC ","
  |  [< ''.'>] -> MC "."
  |  [< ''A'..'Z'|'a'..'z'|'è'|'é' as c >] -> 
         (let l=c::(list_char flux) in 
          let n=(List.length l) in 
          let s=(String.create n) in 
          (list_to_string s 0 l);
	  match s with
	      "not" -> MC "Non"
	    | "non" -> MC "Non"
	    | _ -> Ident s) 
  | [< ''0'..'9' as c >] -> 
         (let l=((Char.code c)-(Char.code '0'))::(list_num flux) in
           Int (list_to_int l))
  | [< ''-' >] -> lire_minus flux
  | [< ''('|')'|':' as c >] -> MC (Char.escaped c)
  | [< ''&'>] -> MC "Et"
  | [< ''~'>] -> MC "Non"
  | [< ''|'>] -> MC "Ou"
  | [< ''=';''>'>] -> MC "Imp"
  | [< ''<' >] -> lire_brack flux

let rec analyse_lexical flux =
   match flux with parser
     [< l=lire_lexeme >] -> [< 'l ; analyse_lexical flux >]
   | [< >] -> [< >];;

let lex s =
  (analyse_lexical (Stream.of_string s));;

let rec parse_formule flux =
  match flux with parser
  | [< f1=parse_atom; f=(parse_bin f1) >] -> f
and parse_atom flux =
  match flux with parser
    [< '(Ident x) >] -> if x="Faux" then Faux else Var x
  | [< '(MC "Non"); f=parse_atom >] -> Imp (f,Faux)
  | [< '(MC "(") ; f=parse_formule ; '(MC ")") >] -> f
and parse_bin f1 flux =
  match flux with parser
    [< '(MC "Et") ; f2=parse_formule >] -> Et (f1,f2)
  | [< '(MC "Ou") ; f2=parse_formule >] -> Ou (f1,f2)
  | [< '(MC "Imp") ; f2=parse_formule >] -> Imp (f1,f2)
  | [< >] -> f1
;;

let parse s = 
 let flux = (lex s) in
 let f = parse_formule flux in
 match flux with parser
   [< '(Ident _) >]  -> failwith "formule mal formée !"
 | [< '(MC _) >] -> failwith "formule mal formée !"
 | [<>] -> f

let parse_command s = 
 let flux = (lex s) in
 let res = (
   match flux with parser
     | [< '(Ident "Ax") >]  -> Ax
     | [< '(Ident "a") >]  -> Ax
     | [< '(Ident "ElimImp"); f=parse_formule >]  -> ElimImp f
     | [< '(Ident "ei"); f=parse_formule >]  -> ElimImp f
     | [< '(Ident "IntroImp") >]  -> IntroImp
     | [< '(Ident "ii") >]  -> IntroImp
     | [< '(Ident "IntroEt") >]  -> IntroEt
     | [< '(Ident "ie") >]  -> IntroEt
     | [< '(Ident "ElimEt1"); f=parse_formule >]  -> ElimEt1 f
     | [< '(Ident "ee1"); f=parse_formule >]  -> ElimEt1 f
     | [< '(Ident "ElimEt2"); f=parse_formule >]  -> ElimEt2 f
     | [< '(Ident "ee2"); f=parse_formule >]  -> ElimEt2 f
     | [< '(Ident "IntroOu1") >]  -> IntroOu1
     | [< '(Ident "io1") >]  -> IntroOu1
     | [< '(Ident "IntroOu2") >]  -> IntroOu2
     | [< '(Ident "io2") >]  -> IntroOu2
     | [< '(Ident "ElimOu"); f1=parse_formule; f2=parse_formule >]  -> ElimOu (f1,f2)
     | [< '(Ident "eo"); f1=parse_formule; f2=parse_formule >]  -> ElimOu (f1,f2)
     | [< '(Ident "ElimFaux") >]  -> ElimFaux
     | [< '(Ident "ef") >]  -> ElimFaux
     | [< '(Ident "ElimNon"); f=parse_formule >]  -> ElimNon f
     | [< '(Ident "en"); f=parse_formule >]  -> ElimNon f
     | [< '(Ident "IntroNon"); f=parse_formule >]  -> IntroNon f
     | [< '(Ident "in"); f=parse_formule >]  -> IntroNon f
     | [< '(Ident "ElimNonNon") >]  -> ElimNonNon
     | [< '(Ident "enn") >]  -> ElimNonNon
     | [< '(Ident "TiersExclu") >]  -> TiersExclu
     | [< '(Ident "te") >]  -> TiersExclu
     | [< '(Ident "Absurde") >]  -> Absurde
     | [< '(Ident "ab") >]  -> Absurde
     | [< '(Ident "Stop") >]  -> Stop
     | [< '(Ident "s") >]  -> Stop
     | [< '(Ident "Annule") >]  -> Annule
     | [< '(Ident "an") >]  -> Annule
     | [< '(Ident "Saut") >]  -> Saut
     | [< '(Ident "sa") >]  -> Saut
     | [< '(Ident "Centre") >]  -> Centre
     | [< '(Ident "Aide") >]  -> Aide
     | [< '(Ident "ai") >]  -> Aide
     | [< '(Ident "Lemme"); '(Ident f) >]  -> Lemme f
     | [< '(Ident "l"); '(Ident f) >]  -> Lemme f
     | [<>] -> failwith "formule mal formée !"
 ) in
   match flux with parser
       [< '(Ident _) >]  -> failwith "formule mal formée !"
     | [< '(MC _) >] -> failwith "formule mal formée !"
     | [<>] -> res

let rec list_to_string s i = function 
    [] -> () 
  | x::l -> s.[i]<-x; (list_to_string s (i-1) l)

let prompt = ref "\n> "

let lireCommande () =
  let fin = ref false in
  let res = ref Stop in
    while not (!fin) do
      print_string !prompt;
      try
	res := (parse_command (read_line ()));
	fin := true
      with
	  _ -> print_string "commande incorrecte !";
    done;
    !res

let lireFormule () =
  let fin = ref false in
  let res = ref (Var "") in
    while not (!fin) do
      print_string !prompt;
      try
	res := (parse_formule (lex (read_line ())));
	fin := true
      with
	  _ -> print_string "commande incorrecte !";
    done;
    !res

let rec ouiOuNon mess =
  print_string mess;
  print_string " (o/n) [o] : ";
  match (read_line ()) with
      "o" | "" | "o;;" | ";;" -> true
    | "n" | "n;;"  -> false
    | _ -> print_string "\n"; ouiOuNon mess

let (environnement : (string*arbreN) list ref) = ref []

let ajoute_env f p1 = 
  try
    let p2= List.assoc f !environnement in
      if not (p1=p2) then
	if ouiOuNon ("Ecraser l'ancienne valeur de "^f^"?") then
	  environnement := (f,p1)::(!environnement)
  with
      Not_found -> environnement := (f,p1)::(!environnement)
  
let id_num = ref (-1)

let new_id () = incr id_num; ! id_num


let arbreVideInit f = 
  let seq = {contexte=vide;but=f} in
    Regles {id = new_id ();
	    size=(0,2*espace_nom,0,0);
	    name=""; 
	    seq=seq; 
	    sizeseq=print_size_sequent seq;
	    ssButs=[]; 
	    peres=[]}
      
let arbreVide r seq = 
  Regles {id = new_id ();
	  size=(0,2*espace_nom,0,0);
	  name=""; 
	  seq=seq; 
	  sizeseq=print_size_sequent seq;
	  ssButs=[]; 
	  peres= (Regles r)::r.peres }

let rec convert_arbre = function Regles r ->
 Regle {nom=r.name; sequent=r.seq; sousButs=List.map convert_arbre r.ssButs}

let ycourant = ref 150
let pointinitial = ref (0,0)
let xmin = ref 512
let xmax = ref 512

let rec print_graph_arbre = function Regles r ->
  let (a,b,c,d) =  r.size in
  let e = r.sizeseq in
  let line = 2*d+e in
    print_graph_sequent2 r.seq;
    rmoveto (-d) 15;
    if r.name="?" then
      begin
	set_color green;
	ycourant := current_y ();
	let x = current_x () in
	  xmin := x;
	  xmax := line+x;
	rlineto line 0;
	courier ();
	let (l,d)=(regle_size r.name) in
	  rmoveto espace_nom (-d/2+1);
	  print_regle r.name;
	  set_color black;
	  rmoveto (-l-espace_nom) (d/2-1);
	  rmoveto (-line) 3;
      end
    else if not (r.name="") then
      begin
	rlineto line 0;
	courier ();
	let (l,d)=(regle_size r.name) in
	  rmoveto espace_nom (-d/2+1);
	  set_color color_nom;
	  print_regle r.name;
	  set_color black;
	  rmoveto (-l-espace_nom) (d/2-1);
	  rmoveto (-line) 3;
      end
    else rmoveto 0 3;
    rmoveto c 0;
    print_graph_arbre_list r.ssButs;
    rmoveto (-c+d) (-18)
and print_graph_arbre_list = function
    [] -> ()
  | [r] -> print_graph_arbre r
  | r::r'::q -> 
      let (Regles arb) = r in
      let (a,b,c,d) = arb.size in
      let e = arb.sizeseq in
      let (Regles arb') = r' in
      let (a',b',c',d') = arb'.size in
      let _ = arb.sizeseq in
        rmoveto (e+d+b+espace_arbre+a'+d') 0;
	print_graph_arbre_list (r'::q);
	rmoveto (-(e+d+b+espace_arbre+a'+d')) 0;
	print_graph_arbre r


exception Fin

let rec affiche_arbre = function Regles r ->
  Graphics.clear_graph ();
  let (a,b,c,d) = r.size in
  let e = r.sizeseq in
  let n = a+b+2*d+e in
  let (x0,y0) = !pointinitial in
    Graphics.moveto ((1024-n)/2+a+d+x0) y0;
    print_graph_arbre (Regles r);
    if !xmin<0 || !xmax > 1000 || !ycourant > 250 then
      begin
	  let (x0,y0) = !pointinitial in
	  let x = (!xmin + !xmax)/2 in
	  let y' = if !ycourant < 250 then 0 else 150- !ycourant in
	    pointinitial := (512-x+x0,y'+y0);
	    ycourant:= 150- y';
	    xmin := 512 - x + !xmin;
	    xmax := 512 + !xmax - x;
	    affiche_arbre (Regles r)
      end;
    Graphics.synchronize ()

let rec hauteur = function Regles r ->
  1+(hauteur_list r.ssButs)
and hauteur_list = function
    [] -> 0
  | r::q -> max (hauteur r) (hauteur_list q)

let id (Regles x) = x.id

let rec remove x = function
   [] -> []
  | a::q -> if (id x)=(id a) then q else a::(remove x q)

let rec remove_list l1 l2 =
 match l1 with
     [] -> l2
   | a::q -> remove_list q (remove a l2)

let affiche_arbre_init f = function Regles r ->
  let (a,b,c,d) = r.size in
  let e = r.sizeseq in
  let n = a+b+2*d+e in
  let h = (hauteur (Regles r))*18+espace_nom in
    close_graph ();
    open_graph (" "^(string_of_int n)^"x"^(string_of_int h));
    set_window_title f;
    Graphics.auto_synchronize false;
    Graphics.moveto (espace_nom+a+d) espace_nom;
    print_graph_arbre (Regles r);
    Graphics.synchronize ()


let rec print_contexte_rec = function
    [] -> ""
  | f::q -> ", "^(print f)^(print_contexte_rec q)

let print_contexte = function
    [] -> ""
  | f::q -> (print f)^(print_contexte_rec q)

let print_sequent seq =
 (print_contexte (enumere seq.contexte))^" |- "^(print seq.but)



let prove_formule_graph gen f = 
  prompt := "\nRègle ? ";
  let arbreCourant = arbreVideInit f in
try
  let rec aux path = function 
      [] -> path
    | (Regles r)::q ->
    r.name <- "?";
    affiche_arbre arbreCourant;
(*    print_string (print_sequent r.seq); *)
    print_newline ();
    let comm = lireCommande () in
      if comm = Stop then raise Fin
      else if comm = Centre then
	begin
	  let x = (!xmin + !xmax)/2 in
	  let (x0,y0) = !pointinitial in
	  let y' = if !ycourant < 250 then 0 else 150- !ycourant in
	    pointinitial := (512-x+x0,y'+y0);
	    ycourant:= 150- y';
	    xmin := 512 - x + !xmin;
	    xmax := 512 + !xmax - x;
	    affiche_arbre arbreCourant;
	    aux path ((Regles r)::q)
	end
      else if comm = Saut then
	begin
	  r.name <- "";
	  aux path (q@[Regles r])
	end
      else if comm = Annule then
	begin
	  match path with
	      [] -> aux path ((Regles r)::q)
	    | r'::q' -> 
		begin 
		let new_q = remove_list r'.ssButs ((Regles r)::q) in 
(*		    Printf.printf "I have removed %d nodes !\n" ((List.length q)+1-(List.length new_q)); *)
		  (*		do_list (fun (Regles r) -> Printf.printf "{%s} " (print_sequent r.seq)) ((Regles r')::new_q); *)
		print_newline ();
		    r.name <- "";
		    r'.name <- "?";
		    r'.ssButs <- [];
		    print_size_arbre (Regles r');
		    do_list print_size_arbre r'.peres;
		    aux q' ((Regles r')::new_q)
		end
	end
      else if comm = Aide then
	begin
	  let rec print_list = function 
	      [] -> ()
	    | h::t -> 
		begin
		  print_string(h);
		  print_newline();
		  print_list(t)
		end
	  in
	  print_list(listeReglesApplicables r.seq);
	  aux path ((Regles r)::q)
	end
      else
	let (l,nom) = (gen r.seq comm) in
	  if nom="erreur" then 
	    begin
	      print_string "Règle impossible !\n";
	      aux path ((Regles r)::q)
	    end
	  else
	    begin
	      r.name <- nom;
	      r.ssButs <- (List.map (arbreVide r) l);
	      print_size_arbre (Regles r);
	      do_list print_size_arbre r.peres;
	      aux (r::path) (r.ssButs@q);
(* 	      itNum (fun n f-> aux (n::path) f) r.ssButs *)
	    end;
  in
  let _ = aux [] [arbreCourant] in
    affiche_arbre arbreCourant;
    arbreCourant
with
    Fin -> arbreCourant


let wait () =
  try 
    while true do
      let s = wait_next_event [Key_pressed] in
	if s.keypressed then
	  match s.key with
	      'q' -> raise Fin
	    | _ -> ()
     done
  with
      Fin -> close_graph ()
    | _ -> () 

let affiche_fichier f =
  try
    begin
      let file = open_in f  in
      let p = input_value file in
	affiche_arbre_init f p;
	close_in file;
	try 
	  while true do
	    let s = wait_next_event [Key_pressed] in
	      if s.keypressed then
		match s.key with
		    'q' -> raise Fin
		  | 'l' -> 
		      let (x,y) = !pointinitial in
			pointinitial := (x-100,y);
			affiche_arbre p
		  | 'k' -> 
		      let (x,y) = !pointinitial in
			pointinitial := (x+100,y);
			affiche_arbre p
		  | c -> ()
	  done
	with
	    Fin -> close_graph ()
    end
  with
      Sys_error _ -> print_string "impossible d'ouvrir ce fichier !"

let charge f =
  try
      let file = open_in f  in
      let p = input_value file in
	convertarbre2arbreN p
  with
      Sys_error _ -> failwith "impossible d'ouvrir ce fichier !"

let charge2 f =
  try
      let file = open_in f  in
      let p = input_value file in
	 convert_arbre p
  with
      Sys_error _ -> failwith "impossible d'ouvrir ce fichier !"

let fichier_existe f =
  try
      let file = open_in f  in
	close_in file;
	true
  with
      Sys_error _ -> false


let removedots s =
  let l = String.length s in
    if l>=2 then
      let fin = String.sub s (l-2) 2 in
	if fin=";;" then String.sub s 0 (l-2)
	else s
    else s

let deduc genfunction =
  init_graph ();
  id_num := -1;
  prompt := "\nBut ? ";
  let f = lireFormule () in
  let p = prove_formule_graph genfunction f in
    if (ouiOuNon "sauver cette preuve ?") then
      begin
	print_string "donnez un nom : ";
	let name = removedots (read_line ()) in
	let namefile = (name^".prf") in
	let file = open_out namefile in
	  output_value file p;
	  close_out file
      end

let convert p =
  open_graph "";
  let rec aux1 = function Regle r -> 
    Regles {id = new_id ();
	    size = (0,2*espace_nom,0,0);
	    name = r.nom; 
	    seq = r.sequent; 
	    sizeseq = print_size_sequent r.sequent;
	    ssButs = map aux1 r.sousButs; 
	    peres= [] } in
  let rec aux2 = function Regles r ->
    do_list aux2 r.ssButs;
    print_size_arbre (Regles r) in
  let res = (aux1 p) in
    aux2 res;
    close_graph ();
    res

let simpH p =
  open_graph "";
  let rec aux1 imp = function Regles r -> 
    let seq = {but = if imp then 
		 match r.seq.but with
		     Imp (a,_) -> Imp (a,Var "...")
		   | f -> f
	       else Var "...";
	      contexte = vide} in
    Regles {id = new_id ();
	    size = (0,2*espace_nom,0,0);
	    name = r.name; 
	    seq = seq; 
	    sizeseq = print_size_sequent seq;
	    ssButs = (match r.name,r.ssButs with
		"MP",[p1;p2] -> [aux1 false p1;aux1 true p2]
	      | _ -> map (aux1 false) r.ssButs); 
	    peres= [] } in
  let rec aux2 = function Regles r ->
    do_list aux2 r.ssButs;
    print_size_arbre (Regles r) in
  let res = (aux1 false p) in
    aux2 res;
    close_graph ();
    res

let affiche_fichierH f =
  try
    begin
      let file = open_in f  in
      let p = input_value file in
	affiche_arbre_init f (simpH p);
	close_in file;
	try 
	  while true do
	    let s = wait_next_event [Key_pressed] in
	      if s.keypressed then
		match s.key with
		    'q' -> raise Fin
		  | 'l' -> 
		      let (x,y) = !pointinitial in
			pointinitial := (x-100,y);
			affiche_arbre p
		  | 'k' -> 
		      let (x,y) = !pointinitial in
			pointinitial := (x+100,y);
			affiche_arbre p
		  | c -> ()
	  done
	with
	    Fin -> close_graph ()
    end
  with
      Sys_error _ -> print_string "impossible d'ouvrir ce fichier !"


let sauve p name =
  let namefile = (name^".prf") in
  let file = open_out namefile in
    output_value file (convert (convertarbreN2arbre p));
    close_out file

let print_noeud = function Regle r ->
  let ssb = List.fold_left (fun a (Regle b) -> a^"  "^(print_sequent b.sequent)) "" r.sousButs in
  let b = print_sequent r.sequent in
  let bl = String.length b in
  let ssbl = String.length ssb in
    if bl<ssbl then
      ssb^"\n"^(String.make ssbl '-')^" "^r.nom^"\n"^(String.make ((ssbl-bl)/2) ' ')^b
    else
      (String.make ((bl-ssbl)/2) ' ')^ssb^"\n"^(String.make ssbl '-')^" "^r.nom^"\n"^b
      
let valide_NM p =
let rec valide = function Regle r ->
  let b =
  match (r.nom,r.sequent.but,r.sousButs) with
    | "Ax",f,[] -> (membre f r.sequent.contexte)
    | "IntroImp",Imp (f,g),[Regle r1] -> 
	eq (ajoute f r.sequent.contexte) (r1.sequent.contexte) &&
	r1.sequent.but = g &&
	valide (Regle r1)
    | "ElimImp",f,[Regle r1;Regle r2] -> 
	  eq r.sequent.contexte (union r1.sequent.contexte r2.sequent.contexte) &&
	  ((r2.sequent.but = Imp (r1.sequent.but,f))
	   || (r1.sequent.but = Imp (r2.sequent.but,f))) &&
	  valide (Regle r1) &&
	  valide (Regle r2) 
    | "IntroEt",Et (f,g),[Regle r1;Regle r2] -> 
	eq r.sequent.contexte (union r1.sequent.contexte r2.sequent.contexte) &&
	r1.sequent.but = f &&
	r2.sequent.but = g &&
	valide (Regle r1) &&
	valide (Regle r2) 
    | "ElimEt1",f,[Regle r1] -> 
	eq r.sequent.contexte r1.sequent.contexte &&
        (match r1.sequent.but with
	     Et (g,_) -> f=g
	   | _ -> false) &&
	valide (Regle r1) 
    | "ElimEt2",f,[Regle r1] -> 
	eq r.sequent.contexte r1.sequent.contexte &&
        (match r1.sequent.but with
	     Et (_,g) -> f=g
	   | _ -> false) &&
	valide (Regle r1) 
    | "IntroOu1",Ou (f,g),[Regle r1] -> 
	eq r.sequent.contexte r1.sequent.contexte &&
	r1.sequent.but = f &&
	valide (Regle r1) 
    | "IntroOu2",Ou (f,g),[Regle r1] -> 
	eq r.sequent.contexte r1.sequent.contexte &&
	r1.sequent.but = g &&
	valide (Regle r1) 
    | "ElimOu",f,[Regle r1; Regle r2; Regle r3] -> 
	begin
	  match r1.sequent.but with
	      Ou (f1,f2) ->
		(membre f1 r2.sequent.contexte) &&
		(membre f2 r3.sequent.contexte) &&
		eq (ajoute f1 (ajoute f2 r.sequent.contexte ))
                   (union r1.sequent.contexte 
                          (union r2.sequent.contexte r3.sequent.contexte)) &&
		valide (Regle r1) &&
		valide (Regle r2) &&
		valide (Regle r3)
	    | _ -> false
	end 
    | "ElimFalse",f,[Regle r1] -> 
	eq r.sequent.contexte r1.sequent.contexte &&
	r1.sequent.but = Faux &&
	valide (Regle r1) 
    | "IntroNon",Imp (f,Faux),[Regle r1;Regle r2] -> 
	eq (ajoute f r.sequent.contexte) (union r1.sequent.contexte r2.sequent.contexte) &&
	r1.sequent.but = Imp (r2.sequent.but,Faux) &&
	valide (Regle r1) && valide (Regle r2) 
    | "ElimNon",f,[Regle r1;Regle r2] -> 
	eq r.sequent.contexte (union r1.sequent.contexte r2.sequent.contexte) &&
	r1.sequent.but = Imp (r2.sequent.but,Faux) &&
	valide (Regle r1) && valide (Regle r2) 
    | "TiersExclu",Ou (f,Imp (g,Faux)),[] -> f=g
    | "Absurde",f,[Regle r1] -> 
	eq (ajoute (Imp (f,Faux)) r.sequent.contexte) r1.sequent.contexte &&
	r1.sequent.but = Faux &&
	valide (Regle r1) 
    | "ElimNonNon",f,[Regle r1] -> 
	eq r.sequent.contexte r1.sequent.contexte &&
	r1.sequent.but = Imp (Imp (r.sequent.but,Faux),Faux) &&
	valide (Regle r1) 
    | _ -> raise (Erreur ((print_noeud (Regle r))^"\nce noeud n'est pas valide !\n")) in
    if b then true else 
      raise (Erreur ((print_noeud (Regle r))^"\nce noeud n'est pas valide !\n")) in
  try
    if valide (convertarbreN2arbre p) then 
      print_string "preuve valide\n"; true
  with
      Erreur s -> print_string s; false

let valide = valide_NM

let valide_H p =
let rec valide = function Regle r ->
  let b =
  match (r.nom,r.sequent.but,r.sousButs) with
    | "Ax",f,[] -> (membre f r.sequent.contexte)
    | "K",Imp (a1,Imp (b,a2)),[] -> a1=a2
    | "S",Imp (Imp (a1,Imp (b1,c1)),Imp (Imp (a2,b2),Imp (a3,c2))),[] -> 
	a1=a2 && a1=a3 && b1=b2 && c1=c2
    | "E1",Imp (Et (a1,b),a2),[] -> a1=a2
    | "E2",Imp (Et (a,b1),b2),[] -> b1=b2
    | "E3",Imp (a1,Imp (b1,Et (a2,b2))),[] -> a1=a2 && b1=b2
    | "O1",Imp (a2,Ou (a1,b)),[] -> a1=a2
    | "O2",Imp (b2,Ou (a,b1)),[] -> b1=b2
    | "O3",Imp (Ou (a1,b1),Imp (Imp (a2,c1),Imp (Imp (b2,c2),c3))),[] -> 
       a1=a2 && b1=b2 && c1=c2 && c2=c3
    | "MP",f,[Regle r1;Regle r2] -> 
	  eq r.sequent.contexte (union r1.sequent.contexte r2.sequent.contexte) &&
	  ((r2.sequent.but = Imp (r1.sequent.but,f))
	   || (r1.sequent.but = Imp (r2.sequent.but,f))) &&
	  valide (Regle r1) &&
	  valide (Regle r2) 
    | _ -> 
	let regles = ["Ax";"K";"S";"E1";"E2";"E3";"O1";"O2";"O3";"MP"] in
	  if not (List.mem r.nom regles) then
	    raise (Erreur ("la règle "^r.nom^" n'existe pas dans le système H!\n"))
	  else
	    raise (Erreur ((print_noeud (Regle r))^"\nce noeud n'est pas valide !\n")) in
    if b then true else 
      raise (Erreur ((print_noeud (Regle r))^"\nce noeud n'est pas valide !\n")) in
  try
    if valide p then 
      print_string "preuve valide pour le système H\n"; true
  with
      Erreur s -> print_string s; false

let affiche prf =
  let p = convert (convertarbreN2arbre prf) in
  affiche_arbre_init "" p;
    try 
      while true do
	let s = wait_next_event [Key_pressed] in
	  if s.keypressed then
	    match s.key with
		'q' -> raise Fin
	      | 'l' -> 
		  let (x,y) = !pointinitial in
		    pointinitial := (x-100,y);
		    affiche_arbre p
	      | 'k' -> 
		  let (x,y) = !pointinitial in
		    pointinitial := (x+100,y);
		    affiche_arbre p
	      | c -> ()
      done
    with
	Fin -> close_graph ()

