(***********************
*						*
*	    TP d'IPF		*
*						*
*	  Franck Schmitt	*
*	   ENSIIE 2018		*
*						*
************************)


#load "graphics.cma";;

(* 	____________________________________________________

 				Types and const declaration 
	____________________________________________________*)



(* Définition d'une constante pour la taille N du support de base *)
let coteCarre = 512;;

(* Définition du type point à l'aide de 2 coordonnées : x et y *)
type point = {
	x: int; 
	y: int
};;

(* Définition du type rect *)
type rect = {
	(* coordonnée en y de l'arête supérieure *)
	top: int; 
	(* coordonnée en y de l'arete inférieure *)
	bottom: int; 
	(* coordonnée en x de l'arete de gauche *)
	left: int; 
	(* coordonnée en x de l'arete de droite *)
	right: int
};;

(* Définition du type pquadtree 
 * Ordre des pquadtree: Nord-Ouest, Nord-Est, Sud-Ouest, Sud-Est 
 *)
type pquadtree =  PEmpty | PNoeud of point*rect*pquadtree*pquadtree*pquadtree*pquadtree;;

(* Définition du type couleur qui prend soit noir soit blanc *)
type couleur = Blanc | Noir ;;

(* Définition du type rquadtree 
 * L'ordre des sous rquadtree est le même que pour les pquadtree 
 *)
type rquadtree = Uni of couleur | RQ of rquadtree * rquadtree * rquadtree * rquadtree;;

(* Type bit pour l'encodage des rquadtrees *)
type bit = Zero | Un;;

(* Définition du type quadtree *)
type quadtree = Empty | Q of rect * (rect list) * (rect list) * quadtree * quadtree * quadtree * quadtree;;


(* 	____________________________________________________
	
 				UTILITARIES FUNCTIONS 
 	____________________________________________________*)



(* Fonction puissance utile pour certains calculs *)
let puissance x y =
	let rec aux xb res yb =
		match yb with
		| 0 -> res
		| _ -> aux (xb * xb) (if yb mod 2 = 1 then res * xb else res) (yb / 2)
	in aux x 1 y
;;

(* Fonction permettant l'affichage d'une liste *)
let rec affiche_liste l = 
	match l with
	| [] -> print_newline()
	| p::q -> print_string p; print_string " "; affiche_liste q
;;

(* Fonction permettant l'affichage d'une liste de bit *)
let rec affiche_bit_liste l = 
	match l with
	| [] -> print_newline()
	| Zero::q -> print_string "Zero"; print_string " "; affiche_bit_liste q;
	| Un::q -> print_string "Un"; print_string " "; affiche_bit_liste q;
;;

(* Fonction supprimant une liste li d'une liste source l *)
(* La fonction fonctionne même si des éléments sont compris entre les elements de li dans l *)
let rec deleteSubList l li =
	match l, li with
	| [], _ -> []
	| p::q, e::f when p = e -> deleteSubList q f
	| p::q, _ -> p::(deleteSubList q li)
;;

(* Fonction permettant d'afficher les valeurs d'un pquadtree dans la console *)
let rec affiche_arbre q = 
	match q with
	| PEmpty -> print_string "empty "
	| PNoeud (p, r, un, deux, trois, quatre) -> print_string "point: "; print_int p.x; print_string ";"; print_int p.y; print_newline();
												print_string "rectangle: top:"; print_int r.top; print_string " bot:"; print_int r.bottom; print_string " left:"; print_int r.left; print_string " right: "; print_int r.right; print_newline();
												print_string "affichage arbre 1: "; print_newline(); affiche_arbre un; print_newline();
												print_string "affichage arbre 2: "; print_newline(); affiche_arbre deux; print_newline();
												print_string "affichage arbre 3: "; print_newline(); affiche_arbre trois; print_newline();
												print_string "affichage arbre 4: "; print_newline(); affiche_arbre quatre; print_newline();
	print_newline();
;;


let pointContenu p r =
	if (p.x >= r.left && p.x <= r.right && p.y >= r.bottom && p.y <= r.top) then
		true
	else
		false
;;

(* Returns the North-West sub-support of the rectangle *)
let getNOsurface s =
	{top=s.top; bottom=(s.top+s.bottom)/2; left=s.left; right=(s.right+s.left)/2}
;;

(* Returns the North-East sub-support of the rectangle *)
let getNEsurface s = 
	{top=s.top; bottom=(s.top+s.bottom)/2; left=(s.right+s.left)/2; right=s.right}
;;

(* Returns the South-West sub-support of the rectangle *)
let getSOsurface s = 
	{top=(s.top/2+s.bottom); bottom=s.bottom; left=s.left; right=(s.right+s.left)/2}
;;

(* Returns the South-East sub-support of the rectangle *)
let getSEsurface s = 
	{top=(s.top+s.bottom)/2; bottom=s.bottom; left=(s.right+s.left)/2; right=s.right}
;;


(* 	____________________________________________________

 					Begining of the tp 
 	____________________________________________________*)



(* Détermine si un point (décrit par ses coordonnées) est présent dans une image représentée par un Pquadtree *)
let rec pappartient p tree = 
	match tree with
	| PEmpty -> false
	| PNoeud (a, _, _, _, _, _) when (a.x = p.x && a.y = p.y) -> true
	| PNoeud (_, _, no, ne, so, se) -> (pappartient p no) || (pappartient p ne) || (pappartient p so) || (pappartient p se)
;;

(* Retourne le chemin pour atteindre le point s'il est présent et échoue sinon *)
let pchemin po tree = 
	if not(pappartient po tree) then
			failwith "Error function pchemin: The point is not in the tree!"
	else
		let rec aux p t acc = 		
			match t with
			| PNoeud (_, _, no, _, _, _) when (pappartient p no) -> aux p no ("NO"::acc) 
			| PNoeud (_, _, _, ne, _, _) when (pappartient p ne) -> aux p ne ("NE"::acc) 
			| PNoeud (_, _, _, _, so, _) when (pappartient p so) -> aux p so ("SO"::acc) 
			| PNoeud (_, _, _, _, _, se) when (pappartient p se) -> aux p se ("SE"::acc) 
			| _ -> acc
		in List.rev( aux po tree [] )
;;

(* Insère un point p dans un pquadtree q *)
let insere p q = 
	let rec aux p q s =
		match q with
		| PEmpty when pointContenu p s -> PNoeud (p, s, PEmpty, PEmpty, PEmpty, PEmpty)
		| PNoeud (a, b, c, d, e, f) when pointContenu p (getNOsurface s) -> PNoeud (a, b, (aux p c (getNOsurface s)), d, e, f)
		| PNoeud (a, b, c, d, e, f) when pointContenu p (getNEsurface s) -> PNoeud (a, b, c, (aux p d (getNEsurface s)), e, f)
		| PNoeud (a, b, c, d, e, f) when pointContenu p (getSOsurface s) -> PNoeud (a, b, c, d, (aux p e (getSOsurface s)), f)
		| PNoeud (a, b, c, d, e, f) when pointContenu p (getSEsurface s) -> PNoeud (a, b, c, d, e, (aux p f (getSEsurface s)))
		| _ -> failwith "Error function insere: The point cannot be inserted in the tree!"
	in aux p q { top=coteCarre; bottom=0; left=0; right=coteCarre }
;; 

(* Fonction permettant de dessiner un pquadtree à l'aide de la bibliothèque graphique *)
let draw_pquadtree q = 	
	Graphics.open_graph " ";
	Graphics.set_window_title "PquadTree";
	Graphics.resize_window (coteCarre+1) (coteCarre+1);

	let rec aux q = 
		match q with
		| PEmpty -> ();
		| PNoeud (a, b, c, d, e, f) ->	(* We draw the border of the support *)
										Graphics.draw_rect b.left (b.bottom) (b.right-b.left) (b.top-b.bottom);
										(* We draw the horizontal line of the subdivision *)
										Graphics.moveto b.left ((b.top+b.bottom)/2); Graphics.lineto b.right ((b.top+b.bottom)/2);
										(* We draw the vertical line of the subdivision *)
										Graphics.moveto ((b.left+b.right)/2) b.bottom; Graphics.lineto ((b.right+b.left)/2) b.top;
										(* We draw the point in blue *)
										Graphics.set_color 255; Graphics.fill_rect (a.x-3) (a.y-3) 3 3; Graphics.set_color 0;
										(* We draw the sub-trees *)
										aux c; aux d; aux e; aux f;
	in aux q;

 	(* Wait the user closes the windows and catch the I/O Exception linked with the closure *)
	try (ignore (Graphics.read_key ()))
	with
	|  Graphics.Graphic_failure ("fatal I/O error") -> ()
;;

(* print_string "________\nArbre v1\n________";;
print_newline();;  *)

(* let pquad1 = (insere {x=5; y=5} PEmpty);;
let pquad2 = (insere {x=500; y=300} pquad1);;  
let pquad3 = (insere {x=20; y=30} pquad2);;
let pquad4 = (insere {x=160; y=170} pquad3);;
let pquad5 = (insere {x=325; y=150} pquad4);; *)

(* affiche_liste (pchemin {x=5; y=5} pquad5);;
affiche_liste (pchemin {x=500; y=300} pquad5);;
affiche_liste (pchemin {x=20; y=30} pquad5);;
affiche_liste (pchemin {x=160; y=170} pquad5);;
affiche_liste (pchemin {x=325; y=150} pquad5);;


print_newline();;
print_string "________\nArbre v2\n________";;
print_newline();;

let pquad1 = (insere {x=20; y=30} PEmpty);;
let pquad2 = (insere {x=160; y=170} pquad1);;  
let pquad3 = (insere {x=5; y=5} pquad2);;
let pquad4 = (insere {x=500; y=300} pquad3);;
let pquad5 = (insere {x=325; y=150} pquad4);;

affiche_liste (pchemin {x=5; y=5} pquad5);;
affiche_liste (pchemin {x=500; y=300} pquad5);;
affiche_liste (pchemin {x=20; y=30} pquad5);;
affiche_liste (pchemin {x=160; y=170} pquad5);;
affiche_liste (pchemin {x=325; y=150} pquad5);; *)


(* draw_pquadtree pquad5;; *)

(* let rquadn = Uni Noir;;
let rquadb = Uni Blanc;;
let rquad1 = RQ (rquadb, rquadn, rquadb, rquadn);;
let rquad2 = RQ (rquadn, rquadb, rquadb, rquad1);;
let rquad3 = RQ (rquadn, rquad2, rquadb, rquadn);;
let rquad4 = RQ (rquadb, rquadb, rquadn, rquad3);; *)
 

let draw_rquadtree r = 
	Graphics.open_graph " ";
	Graphics.set_window_title "RquadTree";
	Graphics.resize_window coteCarre coteCarre;

	let rec aux q r = 
		match q with
		| Uni Blanc -> ();
		| Uni Noir -> Graphics.set_color 0; Graphics.fill_rect r.left r.bottom (r.right-r.left) (r.top-r.bottom);
		| RQ (a, b, c, d) -> 	aux a (getNOsurface r);
								aux b (getNEsurface r);
								aux c (getSOsurface r);
								aux d (getSEsurface r);
		Graphics.set_color 0;
		Graphics.moveto r.left ((r.top+r.bottom)/2); Graphics.lineto r.right ((r.top+r.bottom)/2);
		Graphics.moveto ((r.left+r.right)/2) r.bottom; Graphics.lineto ((r.right+r.left)/2) r.top;
	in aux r { top=coteCarre; bottom=0; left=0; right=coteCarre };

	(* Wait the user closes the windows and catch the I/O Exception linked with the closure *)
	try (ignore (Graphics.read_key ()))
	with
	|  Graphics.Graphic_failure ("fatal I/O error") -> ()
;;

(* draw_rquadtree rquad4;; *)


(* Fonction permettant d'inverser les couleurs d'un rquadtree *)
let rec inverse_rquadtree r =
	match r with
	| Uni Blanc -> Uni Noir
	| Uni Noir -> Uni Blanc
	| RQ (a, b, c, d) -> RQ ((inverse_rquadtree a), (inverse_rquadtree b), (inverse_rquadtree c), (inverse_rquadtree d))
;;

(* draw_rquadtree rquad2;;
draw_rquadtree (inverse_rquadtree rquad2);;

draw_rquadtree rquad4;;
draw_rquadtree (inverse_rquadtree rquad4);; *)

(* Fonction regrouppant les RQ de la même couleur *)
let rec normalise p = 
	match p with
	| RQ (a, b, c, d) when (normalise a)=Uni Blanc && (normalise b)=Uni Blanc && (normalise c)=Uni Blanc && (normalise d)=Uni Blanc -> Uni Blanc
	| RQ (a, b, c, d) when (normalise a)=Uni Noir && (normalise b)=Uni Noir && (normalise c)=Uni Noir && (normalise d)=Uni Noir -> Uni Noir
	| RQ (a, b, c, d) -> RQ (normalise a, normalise b, normalise c, normalise d)
	| _ -> p
;;

(* Fonction renvoyant l'intersection entre deux images *)
let intersection_rquadtree p r =
	let rec intersection_rquadtree p r =
		match p, r with
		| Uni Noir, Uni Noir -> Uni Noir
		| Uni Noir, RQ (a, b, c, d) -> RQ (a, b, c, d)
		| RQ (a, b, c, d), Uni Noir -> RQ (a, b, c, d)
		| RQ (a, b, c, d), RQ (e, f, g, h) -> RQ ((intersection_rquadtree a e), (intersection_rquadtree b f), (intersection_rquadtree c g), (intersection_rquadtree d h))
		| _ -> Uni Blanc
	in normalise (intersection_rquadtree p r)
;;

(* let rquad6 = RQ (rquad1, rquadb, rquadb, rquadn);;
draw_rquadtree rquad2;;
draw_rquadtree rquad6;;

draw_rquadtree (intersection_rquadtree rquad2 rquad6);; *)


(* Fonction renvoyant l'union entre deux images *)
let union_rquadtree p r =
	let rec union_rquadtree p r =
		match p, r with
		| Uni Blanc, Uni Blanc -> Uni Blanc
		| Uni Blanc, RQ (a, b, c, d) -> RQ (a, b, c, d)
		| RQ (a, b, c, d), Uni Blanc -> RQ (a, b, c, d)
		| RQ (a, b, c, d), RQ (e, f, g, h) -> RQ ((union_rquadtree a e), (union_rquadtree b f), (union_rquadtree c g), (union_rquadtree d h))
		| _ -> Uni Noir
	in normalise (union_rquadtree p r)
;;

(* draw_rquadtree rquad3;;
draw_rquadtree rquad4;;

draw_rquadtree (union_rquadtree rquad3 rquad4);;  *)


(* Fonction renvoyant l'image symétrique verticale *)
let rec sym_hor_rquadtree r = 
	match r with
	| Uni c -> Uni c
	| RQ (a, b, c, d) -> RQ ((sym_hor_rquadtree c), (sym_hor_rquadtree d), (sym_hor_rquadtree a), (sym_hor_rquadtree b))
;;

(* Fonction renvoyant l'image symétrique horizontale *)
let rec sym_vert_rquadtree r = 
	match r with
	| Uni c -> Uni c
	| RQ (a, b, c, d) -> RQ ((sym_vert_rquadtree b), (sym_vert_rquadtree a), (sym_vert_rquadtree d), (sym_vert_rquadtree c))
;;


(* let test1 = RQ (Uni Blanc, Uni Noir, Uni Blanc, Uni Noir);;
let test2 = RQ (Uni Blanc, Uni Noir, Uni Blanc, test1);;
let test3 = RQ (test2, Uni Blanc, Uni Noir, Uni Blanc);; *)

(*
draw_rquadtree test3;;
draw_rquadtree (sym_hor_rquadtree test3);; 
draw_rquadtree (sym_vert_rquadtree test3);;  *)


let coder r = 
	let rec aux r acc =
		match r with
		| Uni Blanc -> Zero::Un::acc
		| Uni Noir -> Un::Un::acc
		| RQ (a, b, c, d) -> (aux d (aux c (aux b (aux a (Zero::acc)))))
	in List.rev(aux r [])
;;

(* let arbrerquad = RQ(Uni Noir, RQ (Uni Noir, Uni Blanc, Uni Blanc, Uni Noir), Uni Blanc, RQ (Uni Noir, Uni Blanc, Uni Blanc, Uni Noir));;

affiche_bit_liste (coder arbrerquad);; 
draw_rquadtree arbrerquad;; *)


(* Les quatres fonctions suivantes sont déclarées à la suite et uniquement séparées par des "and" car elles sont interdépendantes 
 * Elles extraient les sous-listes correspondants aux 4 coordonnées des sous arbres d'un rquadtree 
 *)
let rec extractListNo l = 
	match l with
	| Un::Un::q -> Un::Un::[]
	| Un::Zero::q -> Un::Zero::[]
	| Zero::q -> Zero::(extractListNo q)@(extractListNe q)@(extractListSo q)@(extractListSe q)
	| _ -> []

and extractListNe l = 
	let li = deleteSubList l (extractListNo l) in
		extractListNo li

and extractListSo l =
	let li = deleteSubList (deleteSubList l (extractListNo l)) (extractListNe l) in
		extractListNo li

and extractListSe l = 
	let li = deleteSubList (deleteSubList (deleteSubList l (extractListNo l)) (extractListNe l)) (extractListSo l) in
		extractListNo li
;;

(* La fonction décoder prend en paramètre une liste de bits et retourne un rquadtree correspondant
 * Une exception est levée si la liste n'est pas correctement formatée 
 *)
let rec decoder l =
	match l with
	| Un::Zero::[] -> Uni Blanc
	| Un::Un::[] -> Uni Noir
	| Zero::q -> RQ (	decoder (extractListNo q), 
						decoder (extractListNe q),
						decoder (extractListSo q), 
						decoder (extractListSe q)
					)
	| _ -> failwith "Erreur de liste"
;;


(* 
let testList = [Zero; Un; Un; Zero; Un; Un; Un; Zero; Un; Zero; Un; Un; Un; Zero; Zero; Un; Un; Un; Zero; Un; Zero; Un; Un];;
draw_rquadtree (decoder testList);; *)



let draw_quadtree q = 
	Graphics.open_graph " ";
	Graphics.set_window_title "QuadTree";
	Graphics.resize_window coteCarre coteCarre;

	let rec draw_rect_list lr = 
		Graphics.set_color 255;
		match lr with
		| [] -> ()
		| p::q -> Graphics.draw_rect p.left p.bottom (p.right-p.left) (p.top-p.bottom); 
		          draw_rect_list q;
	and aux q = 
		match q with
		| Empty -> ();
		| Q (a, b, c, d, e, f, g) -> Graphics.set_color 0;
									(* We draw the horizontal line of the subdivision *)
									Graphics.moveto a.left ((a.top+a.bottom)/2); Graphics.lineto a.right ((a.top+a.bottom)/2);
									(* We draw the vertical line of the subdivision *)
									Graphics.moveto ((a.left+a.right)/2) a.bottom; Graphics.lineto ((a.right+a.left)/2) a.top;
									(* We draw the two rectangle lists *)
									draw_rect_list b; draw_rect_list c;
									(* We draw the sub-trees *)
									aux d; aux e; aux f; aux g;
	in aux q;

 	(* Wait the user closes the windows and catch the I/O Exception linked with the closure *)
	try (ignore (Graphics.read_key ()))
	with
	|  Graphics.Graphic_failure ("fatal I/O error") -> ()
;;



(* 	____________________________________________________

 					Fonctions géométriques 
 	____________________________________________________*)


let intersection_mediane_vert rect sup =
	if (rect.left <= (sup.right-sup.left)/2 && rect.right >= (sup.right-sup.left)/2) then
		true
	else
		false
;;

let intersection_mediane_hor rect sup =
	if (rect.top >= (sup.top-sup.bottom)/2 && rect.bottom <= (sup.top-sup.bottom)/2) then
		true
	else
		false
;;

let rectangleContenu r = 
	if r.top > coteCarre || r.bottom < 0 || r.left < 0 || r.right > coteCarre then
		false
	else
		true
;;


(* 	____________________________________________________

 						Quadtrees
 	____________________________________________________*)


(* type quadtree = Empty | Q of support de type rect * (rect list) * (rect list) * quadtree * quadtree * quadtree * quadtree;; *)

let insere_quadtree r q =
	if not(rectangleContenu r) then
		failwith "Error insere_quadtree : Rectangle cannot be inserted in the QuadTree"
	else 
		let rec aux r q s =
			match q with
			| Empty when intersection_mediane_vert r s -> Q (s, r::[], [], Empty, Empty, Empty, Empty)
			| Empty when intersection_mediane_hor r s -> Q (s, [], r::[], Empty, Empty, Empty, Empty)
			| Empty when pointContenu {x=r.left; y=r.top} (getNOsurface s) -> Q (s, [], [], (aux r Empty (getNOsurface s)), Empty, Empty, Empty)
			| Empty when pointContenu {x=r.left; y=r.top} (getNEsurface s) -> Q (s, [], [], Empty, (aux r Empty (getNEsurface s)), Empty, Empty)
			| Empty when pointContenu {x=r.left; y=r.top} (getSOsurface s) -> Q (s, [], [], Empty, Empty, (aux r Empty (getSOsurface s)), Empty)
			| Empty when pointContenu {x=r.left; y=r.top} (getSEsurface s) -> Q (s, [], [], Empty, Empty, Empty, (aux r Empty (getSEsurface s)))
			| Q (su, rlv, rlh, q1, q2, q3, q4) when intersection_mediane_vert r s -> Q (s, r::rlv, rlh, q1, q2, q3, q4)
			| Q (su, rlv, rlh, q1, q2, q3, q4) when intersection_mediane_hor r s -> Q (s, rlv, r::rlh, q1, q2, q3, q4)
			| Q (su, rlv, rlh, q1, q2, q3, q4) when pointContenu {x=r.left; y=r.top} (getNOsurface s) -> Q (s, rlv, rlh, (aux r q1 (getNOsurface s)), q2, q3, q4)
			| Q (su, rlv, rlh, q1, q2, q3, q4) when pointContenu {x=r.left; y=r.top} (getNEsurface s) -> Q (s, rlv, rlh, q1, (aux r q2 (getNEsurface s)), q3, q4)
			| Q (su, rlv, rlh, q1, q2, q3, q4) when pointContenu {x=r.left; y=r.top} (getSOsurface s) -> Q (s, rlv, rlh, q1, q2, (aux r q3 (getSOsurface s)), q4)
			| Q (su, rlv, rlh, q1, q2, q3, q4) when pointContenu {x=r.left; y=r.top} (getSEsurface s) -> Q (s, rlv, rlh, q1, q2, q3, (aux r q4 (getSEsurface s)))
			| _ -> failwith "Cannot insert rect"
		in aux r q { top=coteCarre; bottom=0; left=0; right=coteCarre }
;;


(* let testquad = insere_quadtree { top=215; bottom=25; left=270; right=510 } Empty;;
let testquad2 = insere_quadtree { top=200; bottom=46; left=79; right=116 } testquad;;
let testquad3 = insere_quadtree { top=4; bottom=0; left=0; right=100 } testquad2;;
let testquad4 = insere_quadtree { top=290; bottom=250; left=360; right=470 } testquad3;;
let testquad5 = insere_quadtree { top=450; bottom=400; left=9; right=67 } testquad4;;


draw_quadtree testquad5;; *)


let rec rightRectsList po rl acc =
	match rl with
	| [] -> acc
	| p::q when pointContenu po p -> rightRectsList po q (p::acc)
	| p::q -> rightRectsList po q acc
;;

let listRectContientPoint p q =
	let rec aux p q acc =
		match q with
		| Empty -> acc
		| Q (su, rlv, rlh, q1, q2, q3, q4) -> aux p q1 (aux p q2 (aux p q3 (aux p q4 (rightRectsList p rlv (rightRectsList p rlh acc))))) 
	in aux p q []
;;

let rec affiche_liste_rectangle = function
	| [] -> ()
	| p::q -> Printf.printf "{top:%d, bot:%d, left: %d, right: %d}\n" p.top p.bottom p.left p.right; affiche_liste_rectangle q;
;;

(* let quad1recContient2 = insere_quadtree {top=50; bottom=0; left=0; right=120} Empty;;
let quad2recContient2 = insere_quadtree {top=45; bottom=0; left=5; right=125} quad1recContient2;;
let quad3recContient2 = insere_quadtree {top=400; bottom=200; left=2; right=6} quad2recContient2;;

affiche_liste_rectangle (listRectContientPoint {x=85; y=26} quad3recContient2);; 

print_newline();;
 
let quad1recContient1 = insere_quadtree {top=50; bottom=0; left=0; right=120} Empty;;
let quad2recContient1 = insere_quadtree {top=5; bottom=1; left=2; right=6} quad1recContient1;;
let quad3recContient1 = insere_quadtree {top=7; bottom=1; left=1; right=8} quad2recContient1;;

affiche_liste_rectangle (listRectContientPoint {x=120; y=30} quad3recContient1);; *)
   