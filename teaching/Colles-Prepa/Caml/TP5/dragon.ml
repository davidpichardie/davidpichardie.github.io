type Etat==int;;
type automate= { initial : Etat;
	         arcs    : Etat-> char->Etat;
	         vals    : Etat->int;
  	       };;

let execute auto mot=
	let n=string_length mot in
	let s = ref auto.initial in
	for i=0 to n-1 do s := auto.arcs !s mot.[i]
	done;
	auto.vals !s;; 


let auto1 = { initial = 0;
              arcs = ( fun 
                      | 0 `b` -> 0
                      | 0 `a` -> 1
                      | 1 `b` -> 0
                      | 1 `a` -> 1
                      | _  _  -> failwith "transition non définie");
              vals = fun x -> x; };;

let auto_dragon = { initial = 0;
              arcs = ( fun 
                      | 0 `0` -> 0
                      | 0 `1` -> 1
                      | 1 `0` -> 2
                      | 1 `1` -> 3
                      | 2 `0` -> 2
                      | 2 `1` -> 2
                      | 3 `0` -> 3
                      | 3 `1` -> 3
                      | _  _  -> failwith "transition non définie");
              vals = fun 
                      | 0 -> 0
                      | 1 -> 0
                      | 2 -> 0
                      | 3 -> 1 
                      | _ -> failwith "valeur non définie"};;
                         
let rec base2 = function
 	  0 -> ""
	| 1 -> "1"
	| n -> (if (0=n mod 2) then "0" else "1") ^ (base2 (n/2));;


let nieme_dragon n = execute auto_dragon (base2 n);;

#open "graphics" ;;

open_graph "400x400" ;;

let dragon n =
  clear_graph() ;
  let dx = ref 0
  and dy = ref 1
  and x = ref 300
  and y = ref 300
  and l = 4 in
  moveto !x !y;
  x := !x + !dx * l;
  y := !y + !dy * l;
  lineto !x !y;
  for i=1 to n do
    match (nieme_dragon i) with
     |0 -> let temp = !dx in
           dx := - !dy;
           dy := temp;
           x := !x + !dx * l;
           y := !y + !dy * l;
           lineto !x !y;
     |1 -> let temp = !dx in
           dx := !dy;
           dy := -temp;
           x := !x + !dx * l;
           y := !y + !dy * l;
           lineto !x !y;
     |_ -> failwith "cas impossible"
  done;;

let inverse s =
  let n = string_length s in
  let m = create_string n in
  for i=0 to n-1 do
    match s.[i] with
      `0` -> m.[i] <- `1`
     |`1` -> m.[i] <- `0`
     | _  -> failwith "cas impossible"
  done;
  m;;

let miroir s =
  let n = string_length s in
  let m = create_string n in
  for i=0 to n-1 do
    m.[i] <- s.[n-1-i]
  done;
  m;;

let rec mot_dragon n =
  if n=1 then "0"
  else let m=(mot_dragon (n-1)) in m^"0"^(miroir (inverse m));;

let dragon n =
  clear_graph() ;
  let dx = ref 0
  and dy = ref 1
  and x = ref 300
  and y = ref 300
  and l = 4 in
  moveto !x !y;
  x := !x + !dx * l;
  y := !y + !dy * l;
  lineto !x !y;
  let m = mot_dragon n in
  let q = string_length m in 
  for i=0 to (q-1) do
    match m.[i] with
     |`0` -> let temp = !dx in
           dx := - !dy;
           dy := temp;
           x := !x + !dx * l;
           y := !y + !dy * l;
           lineto !x !y;
     |`1` -> let temp = !dx in
           dx := !dy;
           dy := -temp;
           x := !x + !dx * l;
           y := !y + !dy * l;
           lineto !x !y;
     |_ -> failwith "cas impossible"
  done;;


let rec dragon_rec n (x1,y1) (x2,y2) =
  moveto (int_of_float x1) (int_of_float y1);
  if n=0 then lineto (int_of_float x2) (int_of_float y2)
  else begin
         let (x3,y3)=((x1+.x2+.y2-.y1)/.2.,(x1-.x2+.y1+.y2)/.2.) in
         dragon_rec (n-1) (x1,y1) (x3,y3);
         dragon_rec (n-1) (x2,y2) (x3,y3); 
       end
  ;;

let dragon n = 
  clear_graph();
  dragon_rec n (200.,150.) (200.,350.);;

let rec dragon1 n (x1,y1) (x2,y2) =
  if n=0 then lineto (int_of_float x2) (int_of_float y2)
  else begin
         let (x3,y3)=((x1+.x2+.y2-.y1) /. 2. , (x1-.x2+.y1+.y2) /. 2.) in
         dragon1 (n-1) (x1,y1) (x3,y3);
         dragon2 (n-1) (x3,y3) (x2,y2); 
       end
 and dragon2 n (x1,y1) (x2,y2) =
  if n=0 then lineto (int_of_float x2) (int_of_float y2)
  else begin
         let (x3,y3)=((x1+.x2-.y2+.y1) /. 2. , (x2-.x1+.y1+.y2) /. 2.) in
         dragon1 (n-1) (x1,y1) (x3,y3);
         dragon2 (n-1) (x3,y3) (x2,y2); 
       end
;;

let dragon n = 
  clear_graph();
  moveto 200 150;
  dragon1 n (200.,150.) (200.,350.);;
