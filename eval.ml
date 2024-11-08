type pterm = 
  | Var of string
  | App of pterm * pterm 
  | Abs of string * pterm
  (* Entiers natifs et opérations *)
  | Int of int
  | Add of pterm * pterm
  | Sub of pterm * pterm
  | Mul of pterm * pterm
  (* Listes natives et opérations *)
  | Nil                                (* [] *)
  | Cons of pterm * pterm              (* hd::tl *)
  | Head of pterm
  | Tail of pterm
  (* Branchements *)
  | IfZero of pterm * pterm * pterm    (* if e1=0 then e2 else e3 *)
  | IfEmpty of pterm * pterm * pterm   (* if e1=[] then e2 else e3 *)
  (* Point fixe et let *)
  | Fix of string * pterm              (* fix phi -> M *)
  | Let of string * pterm * pterm      (* let x = e1 in e2 *)
  (* Types Produits *)
  | Prod of pterm * pterm
  | ProjG of pterm                    (* projection gauche *)        
  | ProjD of pterm                    (* projection droite *)
  (* Types Sommes *)
  | G of pterm
  | D of pterm
  | Switch of pterm * string * pterm * pterm (* Représente sw M ▷ x : M + M *)
let rec print_term (t : pterm) : string =
  match t with
  | Var x -> x
  | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
  | Abs (x, t) -> "(fun " ^ x ^ " -> " ^ (print_term t) ^ ")"
  | Int n -> string_of_int n
  | Add (t1, t2) -> "(" ^ print_term t1 ^ " + " ^ print_term t2 ^ ")"
  | Sub (t1, t2) -> "(" ^ print_term t1 ^ " - " ^ print_term t2 ^ ")"
  | Mul (t1, t2) -> "(" ^ print_term t1 ^ " * " ^ print_term t2 ^ ")"
  | Nil -> "[]"
  | Cons (t1, t2) -> print_term t1 ^ "::" ^ print_term t2
  | Head t -> "head(" ^ print_term t ^ ")"
  | Tail t -> "tail(" ^ print_term t ^ ")"
  | IfZero (t1, t2, t3) -> 
      "if " ^ print_term t1 ^ "=0 then " ^ print_term t2 ^ " else " ^ print_term t3
  | IfEmpty (t1, t2, t3) -> 
      "if " ^ print_term t1 ^ "=[] then " ^ print_term t2 ^ " else " ^ print_term t3
  | Fix (x, t) -> "fix " ^ x ^ " -> " ^ print_term t
  | Let (x, t1, t2) -> "let " ^ x ^ " = " ^ print_term t1 ^ " in " ^ print_term t2
  | Prod (t1, t2) -> "(" ^ print_term t1 ^ " * " ^ print_term t2 ^ ")"
  | ProjG t -> "projG(" ^ print_term t ^ ")"
  | ProjD t -> "projD(" ^ print_term t ^ ")"
  | G t -> "G(" ^ print_term t ^ ")"
  | D t -> "D(" ^ print_term t ^ ")"
  | Switch (t, x, t1, t2) -> "sw " ^ print_term t ^ " ▷ " ^ x ^ " : " ^ print_term t1 ^ " + " ^ print_term t2
(* compteur global *)
let compteur_var : int ref = ref 0

(* création d'une nouvelle variable *)
let nouvelle_var () : string = 
  compteur_var := ! compteur_var + 1;
  "X"^( string_of_int ! compteur_var )

(* Fonction de conversion alpha *)
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x  (* Les variables libres restent inchangées *)
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)  (* Appliquer récursivement *)
  | Abs (x, t1) ->
    let new_x = nouvelle_var () in  (* Générer une nouvelle variable *)
    let new_t1 = alphaconv (substitue t1 x new_x) in  (* Appliquer l'alpha-conversion au corps *)
    Abs (new_x, new_t1)
  | Int n -> Int n  (* Ne fait rien pour les entiers *)
  | Add (t1, t2) -> Add (alphaconv t1, alphaconv t2)
  | Sub (t1, t2) -> Sub (alphaconv t1, alphaconv t2)
  | Mul (t1, t2) -> Mul (alphaconv t1, alphaconv t2)
  | Nil -> Nil
  | Cons (hd, tl) -> Cons (alphaconv hd, alphaconv tl)
  | Head l -> Head (alphaconv l)
  | Tail l -> Tail (alphaconv l)
  | IfZero (cond, t1, t2) -> IfZero (alphaconv cond, alphaconv t1, alphaconv t2)
  | IfEmpty (cond, t1, t2) -> IfEmpty (alphaconv cond, alphaconv t1, alphaconv t2)
  | Fix (phi, m) -> 
    let new_phi = nouvelle_var () in  (* Renommer phi *)
    let new_m = alphaconv (substitue m phi new_phi) in  (* Appliquer l'alpha-conversion au corps *)
    Fix (new_phi, new_m)
  | Let (x, t1, t2) -> 
    let new_x = nouvelle_var () in  (* Renommer x *)
    let new_t1 = alphaconv t1 in  (* Pas de renommage pour t1 *)
    let new_t2 = alphaconv (substitue t2 x new_x) in  (* Appliquer l'alpha-conversion au corps *)
    Let (new_x, new_t1, new_t2)
  | Prod (t1, t2) -> Prod (alphaconv t1, alphaconv t2)
  | ProjG t -> ProjG (alphaconv t)
  | ProjD t -> ProjD (alphaconv t)
  | G t -> G (alphaconv t)
  | D t -> D (alphaconv t)
  | Switch (t, x, t1, t2) -> Switch (alphaconv t, x, alphaconv t1, alphaconv t2)

(* Fonction pour substituer une variable liée par une nouvelle dans le corps de l'abstraction *)
and substitue (t : pterm) (old_var : string) (new_var : string) : pterm =
  match t with
  | Var x -> if x = old_var then Var new_var else Var x
  | App (t1, t2) -> App (substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Abs (x, t1) -> 
    if x = old_var then Abs (x, t1)  (* Ne pas changer la variable liée *)
    else Abs (x, substitue t1 old_var new_var)
  | Int n -> Int n  (* Ne fait rien pour les entiers *)
  | Add (t1, t2) -> Add (substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Sub (t1, t2) -> Sub (substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Mul (t1, t2) -> Mul (substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Nil -> Nil
  | Cons (hd, tl) -> Cons (substitue hd old_var new_var, substitue tl old_var new_var)
  | Head l -> Head (substitue l old_var new_var)
  | Tail l -> Tail (substitue l old_var new_var)
  | IfZero (cond, t1, t2) -> IfZero (substitue cond old_var new_var, substitue t1 old_var new_var, substitue t2 old_var new_var)
  | IfEmpty (cond, t1, t2) -> IfEmpty (substitue cond old_var new_var, substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Fix (phi, m) -> 
    let new_phi = if phi = old_var then new_var else phi in  (* Renommer phi si nécessaire *)
    Fix (new_phi, substitue m old_var new_var)
  | Let (x, t1, t2) ->
    let new_x = if x = old_var then new_var else x in  (* Renommer x si nécessaire *)
    Let (new_x, substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Prod (t1, t2) -> Prod (substitue t1 old_var new_var, substitue t2 old_var new_var)
  | ProjG t -> ProjG (substitue t old_var new_var)
  | ProjD t -> ProjD (substitue t old_var new_var)
  | G t -> G (substitue t old_var new_var)
  | D t -> D (substitue t old_var new_var)
  | Switch (t, y, t1, t2) -> 
    let new_y = if y = old_var then new_var else y in  (* Renommer y si nécessaire *)
    Switch (substitue t old_var new_var, new_y, substitue t1 old_var new_var, substitue t2 old_var new_var)

(* Substitution d'un terme à la place d'une variable *)
let rec substitution (x : string) (n : pterm) (t : pterm) : pterm = 
  match t with 
  | Var y -> if y = x then n else Var y
  | App (t1, t2) -> App (substitution x n t1, substitution x n t2)
  | Abs (y, t1) -> if y = x then Abs (y, t1) else Abs (y, substitution x n t1)
  | Int _ -> t
  | Add (t1, t2) -> Add (substitution x n t1, substitution x n t2)
  | Sub (t1, t2) -> Sub (substitution x n t1, substitution x n t2)
  | Mul (t1, t2) -> Mul (substitution x n t1, substitution x n t2)
  | Nil -> Nil
  | Cons (hd, tl) -> Cons (substitution x n hd, substitution x n tl)
  | Head l -> Head (substitution x n l)
  | Tail l -> Tail (substitution x n l)
  | IfZero (cond, t1, t2) -> IfZero (substitution x n cond, substitution x n t1, substitution x n t2)
  | IfEmpty (cond, t1, t2) -> IfEmpty (substitution x n cond, substitution x n t1, substitution x n t2)
  | Fix (phi, m) -> 
    if phi = x then Fix (phi, m)  (* Ne pas substituer dans le point fixe *)
    else Fix (phi, substitution x n m)
  | Let (y, t1, t2) -> 
    if y = x then Let (y, substitution x n t1, t2)  (* Ne pas substituer dans le terme lié *)
    else Let (y, substitution x n t1, substitution x n t2)
  | Prod (t1, t2) -> Prod (substitution x n t1, substitution x n t2)
  | ProjG t -> ProjG (substitution x n t)
  | ProjD t -> ProjD (substitution x n t)
  | G t -> G (substitution x n t)
  | D t -> D (substitution x n t)
  | Switch (t, y, t1, t2) -> 
    if y = x then Switch (substitution x n t, y, t1, t2)  (* Ne pas substituer dans le terme lié *)
    else Switch (substitution x n t, y, substitution x n t1, substitution x n t2)
(* ;;
   (* Test substitution *)
   let term = App ((App (Var "x", Var "z")), Abs ("y", App (Var "x", Var "y")))
   in print_string (print_term term) ;
   print_string (print_term (substitution "x" (Abs ("t", Var "t")) term)) ;; *)
(* Fonction de réduction Call-by-Value (LtR-CbV) *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  print_endline ("ltr_cbv_step: " ^ print_term t);
  match t with
  | Var _ | Abs _ | Int _ | Nil -> None  (* Les valeurs ne peuvent pas être réduites *)
  | App (t1, t2) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (App (t1', t2))  (* Réduction de la partie gauche de l'application *)
      | None ->
        match ltr_cbv_step t2 with
         | Some t2' -> Some (App (t1, t2'))  (* Réduction de l'argument *)
          | None ->
            match t1 with
            | Abs (x, body) -> Some (substitution x t2 body)  (* β-réduction *)
            | _ -> None)  (* Termes non applicables *)
  | Let (x, e1, e2) ->
    (match ltr_cbv_step e1 with
    (* Substitution de x par v dans e2 puis evaluation de e2*)
      | Some v -> Some (substitution x v e2)
      | None -> if is_value e1 then Some (substitution x e1 e2) else failwith "e1 n'est pas une valeur, ni réductible")
  | Fix (phi, m) ->
    (* on remplace phi par fix partout dans M *)
    Some (substitution phi (Fix (phi, m)) m)
  | IfZero (Int(0), t1, _) -> Some t1
  | IfZero (Int(_), _, t2) -> Some t2
  | IfZero (t1, t2, t3) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (IfZero (t1', t2, t3))
      | None -> failwith "If condition is not an integer")
  | IfEmpty (Nil, t1, _) -> Some t1
  | IfEmpty (Cons(_, _), _, t2) -> Some t2
  | IfEmpty (t1, t2, t3) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (IfEmpty (t1', t2, t3))
      | None -> failwith "If condition is not a list")
  | Add (t1, t2) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (Add (t1', t2))  (* Réduction du premier opérande *)
      | None ->
        match ltr_cbv_step t2 with
        | Some t2' -> Some (Add (t1, t2'))  (* Réduction du second opérande *)
        | None ->
          match t1, t2 with
          | Int n1, Int n2 -> Some (Int (n1 + n2))  (* Évaluation de l'addition *)
          | _ -> None)
  | Sub (t1, t2) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (Sub (t1', t2))  (* Réduction du premier opérande *)
      | None ->
        match ltr_cbv_step t2 with
        | Some t2' -> Some (Sub (t1, t2'))  (* Réduction du second opérande *)
        | None ->
          match t1, t2 with
          | Int n1, Int n2 -> Some (Int (n1 - n2))  (* Évaluation de la soustraction *)
          | _ -> None)
  | Mul (t1, t2) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (Mul (t1', t2))  (* Réduction du premier opérande *)
      | None ->
        match ltr_cbv_step t2 with
        | Some t2' -> Some (Mul (t1, t2'))  (* Réduction du second opérande *)
        | None ->
          match t1, t2 with
          | Int n1, Int n2 -> Some (Int (n1 * n2))  (* Évaluation de la multiplication *)
          | _ -> None)
  | Cons (t1, t2) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (Cons (t1', t2))  (* Réduction de la tête *)
      | None ->
        match ltr_cbv_step t2 with
        | Some t2' -> Some (Cons (t1, t2'))  (* Réduction de la queue *)
        | None -> None)
  | Head l ->
    (match ltr_cbv_step l with
      | Some l' -> Some (Head l')  (* Réduction de l'argument de Head *)
      | None ->
        match l with
        | Cons (hd, _) -> Some hd  (* Extraction de la tête de la liste *)
        | _ -> None)
  | Tail l ->
    (match ltr_cbv_step l with
      | Some l' -> Some (Tail l')  (* Réduction de l'argument de Tail *)
      | None ->
        match l with
        | Cons (_, tl) -> Some tl  (* Extraction de la queue de la liste *)
        | _ -> None)
  | ProjG (Prod (t1, _)) -> Some t1
  | ProjD (Prod (_, t2)) -> Some t2
  | Prod (t1, t2) ->
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (Prod (t1', t2))  (* Réduction du premier élément *)
      | None ->
        match ltr_cbv_step t2 with
        | Some t2' -> Some (Prod (t1, t2'))  (* Réduction du second élément *)
        | None -> None)
  | G t -> 
    (match ltr_cbv_step t with
      | Some t' -> Some (G t')  (* Réduction de l'argument *)
      | None -> None)
  | D t ->
    print_endline ("ltr_cbv_step: D " ^ print_term t);
    (match ltr_cbv_step t with
      | Some t' -> 
        print_endline ("ltr_cbv_step: D some " ^ print_term t' ^ " -> " ^ print_term (D t'));
        Some (D t')  (* Réduction de l'argument *)
      | None -> 
        None)
  | Switch (t, x, t1, t2) ->
    (match ltr_cbv_step t with
      | Some t' -> Some (Switch (t', x, t1, t2))  (* Réduction de l'argument *)
      | None ->
        match t with
        | G t' -> Some (substitution x t' t1)  (* Remplacer x par t' dans t1 *)
        | D t' -> Some (substitution x t' t2)  (* Remplacer x par t' dans t2 *)
        | _ -> None)
  | _ -> None
(* Fonction auxiliaire pour vérifier si un terme est une valeur *)
and is_value (t : pterm) : bool =
  match t with
  | Abs (_, _) -> true  (* Une abstraction est une valeur *)
  | Int _ -> true       (* Un entier est une valeur *)
  | Var _ -> true       (* Une variable est aussi une valeur *)
  | Nil -> true         (* Une liste vide est une valeur *)
  | Cons (hd, tl) -> is_value hd && is_value tl  (* Une liste est une valeur si ses éléments le sont *)
  | _ -> false  (* Les autres termes ne sont pas des valeurs *)
(* Test LtR-CbV *)
(* ;;

   let term = App (Abs ("x", Var "x"), Abs ("y", Var "y"))
   in match ltr_cbv_step term with
   | Some reduced_term -> print_string (print_term reduced_term)
   | None -> print_string "Pas de réduction possible." *)

(* normalisation *)
let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_cbv_step t with
  | Some t' -> ltr_cbv_norm t'
  | None -> t

exception Timeout  (* Exception à lever en cas de dépassement de la limite *)

(* Fonction de normalisation avec timeout pour éviter les boucles infinies *)
let rec ltr_cbv_norm_with_timeout (t : pterm) (limit : int) : pterm =
  if limit <= 0 then raise Timeout  (* Si le compteur atteint 0, on stoppe *)
  else
    match ltr_cbv_step t with
    | Some t' -> ltr_cbv_norm_with_timeout t' (limit - 1)  (* Réduire et décrémenter le compteur *)
    | None -> t  (* Si plus de réductions possibles, retourner le terme final *)


(* Test LtR-CbV *)
;;

(* Test produit *)
let test_produit = Prod (Int 2, Int 3)
in print_string (print_term test_produit) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm test_produit)) ;
print_newline () ;

(* Test de la projection gauche *)
let test_projG = ProjG (Prod (Int 2, Int 3))
in print_string (print_term test_projG) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm test_projG)) ;
print_newline () ;

(* Test de la projection droite *)
let test_projD = ProjD (Prod (Int 2, Int 3))
in print_string (print_term test_projD) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm test_projD)) ;
print_newline () ;

(* Test cours Produit*)
let i = Abs ("x", Var "x") in
let k = Abs ("x", Abs ("y", Var "x")) in
(* (λc.(projG c) (projD c)) (I , I K ) *)
let exemple = App (Abs ("c", App (ProjG (Var "c"), ProjD (Var "c"))), Prod (i, App (i, k))) in
print_string (print_term exemple) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm exemple)) ;
print_newline () ;

(* Test Somme *)
let test_somme = G (Int 2)
in print_string (print_term test_somme) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm test_somme)) ;
print_newline () ;

(* Test d *)
let test_d = D (Int 2)
in print_string (print_term test_d) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm_with_timeout test_d 100)) ;
print_newline () ;

(* Test g *)
let test_g = G (Int 2)
in print_string (print_term test_g) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm_with_timeout test_g 100)) ;


(* Test cours Sommz *)
(* (λx.sw x ▷ y : y 2 + y 3 4) (g : I ) *)
let exemple = App (Abs ("x", Switch (Var "x", "y", Add (Var "y", Int 2), Add (Var "y", Int 3))), G (Int 1)) in
print_string (print_term exemple) ;
print_string " -> " ;
print_string (print_term (ltr_cbv_norm_with_timeout exemple 100)) ;
print_newline () ;


