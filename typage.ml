open Eval

type ptype =
  | Var of string                     (* variables de type *)
  | Arr of ptype * ptype              (* type flèche T1 -> T2 *)
  | Nat                                 (* type de base *)
  | List of ptype                      (* constructeur de type pour les listes *)
  | ForAll of string * ptype           (* type polymorphe ∀X.T *)
  | Prod of ptype * ptype              (* type produit T1 * T2 *)
(* Fonction d'affichage améliorée *)
let rec print_type (t : ptype) : string =
  match t with
  | Var x -> x  (* Affiche simplement la variable de type non résolue, comme T1, T2, etc. *)
  | Nat -> "Nat"
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | List t1 -> "List(" ^ (print_type t1) ^ ")"
  | ForAll (x, t1) -> "∀" ^ x ^ "." ^ (print_type t1)
  | Prod (t1, t2) -> "(" ^ (print_type t1) ^ " * " ^ (print_type t2) ^ ")"

let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = compteur_var_t := ! compteur_var_t + 1;
"T"^( string_of_int ! compteur_var_t )

type equa = (ptype * ptype) list

type env = (string * ptype) list

let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | [] -> failwith "Variable non trouvée"
  | (x,t)::q -> if x=v then t else cherche_type v q


let rec genere_equa (te : pterm) (ty : ptype) (e : env)  : equa =
  print_endline ("Génération d'équations pour: " ^ (print_term te) ^ " : " ^ (print_type ty));
  match te with
  | Var v ->
      let tv = cherche_type v e in
      print_endline ("equation généré Var: " ^ (print_type tv) ^ " = " ^ (print_type ty));
      [(tv, ty)]
  | App (t1, t2) ->
      let ta = Var(nouvelle_var_t()) in (* type frais pour l'argument *)
      let eq1 = genere_equa t1 (Arr(ta, ty)) e in (* type de t1 doit être ta -> ty *)
      let eq2 = genere_equa t2 ta e in (* type de t2 doit être ta *)
      print_endline ("équations généré App: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;
      eq1 @ eq2
  | Abs (x, t) ->
      let ta = Var(nouvelle_var_t()) in (* type frais pour le paramètre *)
      let tr = Var(nouvelle_var_t()) in (* type frais pour le retour *)
      let eq1 = [(ty, Arr(ta, tr))] in (* le type de l'abstraction est ta -> tr *)
      let eq2 = genere_equa t tr ((x, ta)::e) in (* type du corps avec x:ta dans l'env *)
      print_endline ("équations généré Abs: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;

      eq1 @ eq2
  | Int _ ->
    print_endline ("équation généré: Nat = " ^ (print_type ty));
    [(ty, Nat)]

  | Add (t1, t2) | Sub (t1, t2) | Mul (t1, t2) ->
    let ta = Var (nouvelle_var_t ()) in  (* Nouvelle variable de type pour t1 *)
    let tr = Var (nouvelle_var_t ()) in  (* Nouvelle variable de type pour t2 *)
    let eq1 = genere_equa t1 ta e in (* t1 doit être de type Nat *)
    let eq2 = genere_equa t2 tr e in (* t2 doit être de type Nat *)
    print_endline ("équations généré Add ou autres: ");
    List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
    List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;
    print_endline ("équation généré: " ^ (print_type ty) ^ " = Nat->Nat->Nat");
    (ty,  Arr(Nat, Arr(Nat, Nat))) :: eq1 @ eq2 (* le type de l'opération est Nat -> Nat -> Nat *)
    
     (* let ta = Var (nouvelle_var_t ()) in  (* Nouvelle variable de type pour t1 *)
      let tr = Var (nouvelle_var_t ()) in  (* Nouvelle variable de type pour t2 *)
      let eq1 = genere_equa t1 ta e in (* t1 doit être de type Nat *)
      let eq2 = genere_equa t2 tr e in (* t2 doit être de type Nat *)

      [(ty, Nat)] @ eq1 @ eq2 *)
  | Nil ->
      let x = Var (nouvelle_var_t ()) in  (* Nouvelle variable de type pour X *)
      print_endline ("équation généré: " ^ (print_type ty) ^ " = List " ^ (print_type x));
      [(ty, List x)]  (* le type de Nil est [X] *)

  | Cons (t1, t2) ->
      let x = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 x e in         (* t1 doit être de type X *)
      let eq2 = genere_equa t2 (List x) e in  (* t2 doit être de type [X] *)
      let eq3 = [(ty, List x)] in             (* le type cible est [X] *)
      print_endline ("équations généré Cons: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;
      print_endline ("équation généré: " ^ (print_type ty) ^ " = List " ^ (print_type x));

      eq1 @ eq2 @ eq3

  
  | Head t1 ->
      let x = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 (List x) e in  (* t1 doit être une liste de X *)
      let eq2 = [(ty, x)] in  (* le type cible est X *)
      print_endline ("équations généré Head: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      print_endline ("équation généré: " ^ (print_type ty) ^ " = " ^ (print_type x));
      eq1 @ eq2

  | Tail t1 ->
      let x = Var (nouvelle_var_t ()) in
      let eq1 = genere_equa t1 (List x) e in  (* t1 doit être une liste *)
      let eq2 = [(ty, List x)] in             (* le type cible est une liste *)
      print_endline ("équations généré Tail: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      print_endline ("équation généré: " ^ (print_type ty) ^ " = List " ^ (print_type x));      
      eq1 @ eq2
  

  | IfZero (cond, then_branch, else_branch) ->
      let eq1 = genere_equa cond Nat e in (* condition doit être de type Nat *)
      let eq2 = genere_equa then_branch ty e in (* then_branch doit être de type T *)
      let eq3 = genere_equa else_branch ty e in (* else_branch doit aussi être de type T *)
      print_endline ("équations généré IfZero: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq3;

      eq1 @ eq2 @ eq3

  | IfEmpty (cond, then_branch, else_branch) ->
      let eq1 = genere_equa cond (List (Var (nouvelle_var_t ())) ) e in (* condition doit être de type liste *)
      let eq2 = genere_equa then_branch ty e in (* then_branch doit être de type T *)
      let eq3 = genere_equa else_branch ty e in (* else_branch doit aussi être de type T *)
      print_endline ("équations généré IfEmpty: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq3;

      eq1 @ eq2 @ eq3

  | Fix (x, body) ->
      let t1 = Var (nouvelle_var_t ()) in  (* Type du paramètre de la fonction *)
      let t2 = Var (nouvelle_var_t ()) in  (* Type de retour de la fonction *)
      let eq1 = (ty, Arr (t1, t2)) in  (* T_i = t1 -> t2 *)
      let e_new = (x, Arr (t1, t2))::e in  (* Ajouter x : t1 à l'environnement *)
      let eq2 = genere_equa body (Arr (t1, t2)) e_new in  (* Générer les équations pour le corps *)
      print_endline ("équations généré Fix: ");
      print_endline ((print_type ty) ^ " = " ^ (print_type (Arr (t1, t2))));
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;

      eq1 :: eq2  (* Retourne les équations *)

  | Let (x, e1, e2) ->
      let t0 = infer_type e1 e in  (* Inférer le type de e1 *)
    (* Généraliser t0 : obtenir ∀X1, ..., Xk.T0 *)
      let t0_gen = match t0 with
        | Some t -> generaliser t e
        | None -> failwith "Type non inférable" in
      let new_env = (x, t0_gen)::e in  (* Ajouter x : ∀X1, ..., Xk.T0 à l'environnement *)
      print_endline ("Type généralisé de " ^ x ^ ": " ^ (print_type t0_gen));
      genere_equa e2 ty new_env  (* Générer les équations pour e2 avec le nouvel environnement *)
  | Prod (e1, e2) ->
      let t1 = Var (nouvelle_var_t ()) in  (* Type de e1 *)
      let t2 = Var (nouvelle_var_t ()) in  (* Type de e2 *)
      let eq1 = genere_equa e1 t1 e in  (* Générer les équations pour e1 *)
      let eq2 = genere_equa e2 t2 e in  (* Générer les équations pour e2 *)
      let eq3 = [(ty, Prod (t1, t2))] in  (* Le type de la paire est t1 * t2 *)
      print_endline ("équations généré Prod: ");
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq2;
      print_endline ("équation généré: " ^ (print_type ty) ^ " = " ^ (print_type (Prod (t1, t2))));
      eq1 @ eq2 @ eq3
  | ProjG e1 ->
    let t1 = Var (nouvelle_var_t ()) in  (* Type de l'élément gauche de la paire *)
    let t2 = Var (nouvelle_var_t ()) in  (* Type de l'élément droit de la paire *)
    let eq1 = genere_equa e1 (Prod (t1, t2)) e in  (* Générer les équations pour e1 *)
    print_endline ("équations généré ProjG: ");
    List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
    [(ty, t1)] @ eq1  (* Le type de la projection gauche est t1 *)

  | ProjD e1 ->
    let t1 = Var (nouvelle_var_t ()) in  (* Type de l'élément gauche de la paire *)
    let t2 = Var (nouvelle_var_t ()) in  (* Type de l'élément droit de la paire *)
    let eq1 = genere_equa e1 (Prod (t1, t2)) e in  (* Générer les équations pour e1 *)
    print_endline ("équations généré ProjD: ");
    List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eq1;
    [(ty, t2)] @ eq1  (* Le type de la projection droite est t2 *)

  | _ -> failwith "Type non géré"

(* Vérifie si une variable est libre dans un type *)
and est_libre (v : string) (ty : ptype) : bool =
  match ty with
  | Var x -> x = v
  | Arr (t1, t2) -> est_libre v t1 || est_libre v t2
  | Nat -> false
  | List t -> est_libre v t
  | ForAll (x, t) -> if x = v then false else est_libre v t
  | Prod (t1, t2) -> est_libre v t1 || est_libre v t2

  

(* Fonction auxiliaire pour trouver les variables libres d'un type *)
and variables_libres (ty : ptype) : string list =
  match ty with
  | Var x -> [x]
  | Arr (t1, t2) -> (variables_libres t1) @ (variables_libres t2)
  | Nat -> []
  | List t -> variables_libres t
  | ForAll (x, t) -> List.filter (fun v -> v <> x) (variables_libres t)
  | Prod (t1, t2) -> (variables_libres t1) @ (variables_libres t2)
(* Fonction de généralisation d'un type à partir de l'environnement *)
and generaliser (ty : ptype) (env : env) : ptype =
  (* Récupérer les variables présentes dans l'environnement *)
  let env_vars = List.map fst env in
  print_endline ("Variables de l'environnement: " ^ (String.concat ", " env_vars));

  (* Trouver les variables libres dans le type qui ne sont pas dans l'environnement *)
  let libres = List.filter (fun v -> not (List.mem v env_vars)) (variables_libres ty) in
  print_endline ("Variables libres: " ^ (String.concat ", " libres));

  (* Ajouter ForAll autour de ty pour chaque variable libre trouvée *)
  let res = List.fold_right (fun x t -> ForAll (x, t)) libres ty in
  print_endline ("Type généralisé: " ^ (print_type ty));
  res



(* fonction occur check qui vérifie si une variable appartient à un type. *)
and occur_check (x : string) (t : ptype) : bool =
  match t with
  | Var y -> x = y
  | Arr (t1, t2) -> (occur_check x t1) || (occur_check x t2)
  | Nat -> false
  | List t -> occur_check x t
  | ForAll (y, t) -> if x = y then false else occur_check x t
  | Prod (t1, t2) -> (occur_check x t1) || (occur_check x t2)

(* substitue une variable de type par un type à l'intérieur d'un autre type *)
and substitution_t (x : string) (t : ptype) (ty : ptype) : ptype =
  match ty with
  | Var y -> if x = y then t else Var y
  | Arr (t1, t2) -> Arr (substitution_t x t t1, substitution_t x t t2)
  | Nat -> Nat
  | List t1 -> List (substitution_t x t t1)
  | ForAll (y, t1) -> if x = y then ForAll (y, t1) else ForAll (y, substitution_t x t t1)
  | Prod (t1, t2) -> Prod (substitution_t x t t1, substitution_t x t t2)

(* substitue une variable de type par un type partout dans un système d'équation *)
and substitution_equa (x : string) (t : ptype) (eq : equa) : equa =
  match eq with
  | [] -> []
  | (t1, t2)::q -> (substitution_t x t t1, substitution_t x t t2)::(substitution_equa x t q)

and rename_vars (t : ptype) (renaming : (string * string) list) : ptype =
  match t with
  | Var x -> 
      (match List.assoc_opt x renaming with
       | Some new_x -> Var new_x
       | None -> Var x)
  | Arr (t1, t2) -> Arr (rename_vars t1 renaming, rename_vars t2 renaming)
  | Nat -> Nat
  | List t1 -> List (rename_vars t1 renaming)
  | ForAll (x, t1) -> 
      let new_x = nouvelle_var_t () in
      ForAll (new_x, rename_vars t1 ((x, new_x)::renaming))
  | Prod (t1, t2) -> Prod (rename_vars t1 renaming, rename_vars t2 renaming)

(* 1 étape d'unification un système d'équations *)

(* Helper function to apply substitutions *)
and apply_substitutions (t : ptype) (substitutions : env) : ptype =
  match t with
  | Var x -> 
      (match List.assoc_opt x substitutions with
       | Some t' -> t'
       | None -> t)
  | Arr (t1, t2) -> 
      Arr (apply_substitutions t1 substitutions, 
           apply_substitutions t2 substitutions)
  | List t1 -> List (apply_substitutions t1 substitutions)
  | ForAll (x, t1) -> ForAll (x, apply_substitutions t1 substitutions)
  | Nat -> Nat
  | Prod (t1, t2) -> Prod (apply_substitutions t1 substitutions, apply_substitutions t2 substitutions)
(* Modified unification step with substitutions accumulator *)
and unif_step (eqs : equa) (substitutions_acc : env) : (equa * env) option =
  match eqs with
  | [] -> Some ([], substitutions_acc)
  
  | (t1, t2)::rest when t1 = t2 -> 
      print_endline ("Équation résolue: " ^ (print_type t1) ^ " = " ^ (print_type t2));
      unif_step rest substitutions_acc 
        
  | (Var x, t2)::rest when not (occur_check x t2) -> 
      print_endline ("Unification1: " ^ x ^ " avec " ^ (print_type t2));
      let new_eqs = substitution_equa x t2 rest in
      let new_substitutions = (x, t2) :: substitutions_acc in
      Some (new_eqs, new_substitutions)

  | (t1, Var x)::rest when not (occur_check x t1) -> 
      print_endline ("Unification2: " ^ (print_type t1) ^ " avec " ^ x);
      let new_eqs = substitution_equa x t1 rest in
      let new_substitutions = (x, t1) :: substitutions_acc in
      Some (new_eqs, new_substitutions)

  | (Arr (t1a, t1b), Arr (t2a, t2b))::rest ->
      print_endline ("Unification3: " ^ (print_type (Arr (t1a, t1b))) ^ " avec " ^ (print_type (Arr (t2a, t2b))));
      Some ((t1a, t2a)::(t1b, t2b)::rest, substitutions_acc)

  | (List t1, List t2)::rest ->
      print_endline ("Unification4: " ^ (print_type (List t1)) ^ " avec " ^ (print_type (List t2)));
      Some ((t1, t2)::rest, substitutions_acc)

  | (ForAll (x, t1), t2)::rest ->
      print_endline ("Unification5: " ^ (print_type (ForAll (x, t1))) ^ " avec " ^ (print_type t2));
      let t1_renamed = rename_vars t1 [] in
      let t1_opened = substitution_t x t1_renamed t2 in
      Some ((t1_opened, t2)::rest, substitutions_acc)

  | (t1, ForAll (x, t2))::rest ->
      print_endline ("Unification6: " ^ (print_type t1) ^ " avec " ^ (print_type (ForAll (x, t2))));
      let t2_renamed = rename_vars t2 [] in
      let t2_opened = substitution_t x t2_renamed t1 in
      Some ((t1, t2_opened)::rest, substitutions_acc)
  
  | (Prod (t1a, t1b), Prod (t2a, t2b))::rest ->
      print_endline ("Unification7: " ^ (print_type (Prod (t1a, t1b))) ^ " avec " ^ (print_type (Prod (t2a, t2b))));
      Some ((t1a, t2a)::(t1b, t2b)::rest, substitutions_acc)
  | _ -> None


(* Complete unification with timeout and substitutions *)
and unif (eqs : equa) (substitutions_acc : env) : (equa * env) option =
  print_endline "Équations avant unification:";
  List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eqs;

  match unif_step eqs substitutions_acc with
  | None -> None
  | Some ([], new_substitutions) -> Some ([], new_substitutions)
  | Some (new_eqs, new_substitutions) -> 
      unif new_eqs new_substitutions

(* Timeout wrapper *)

and with_timeout duration f x =
  let start_time = Sys.time () in
  let rec loop () =
    if Sys.time () -. start_time > duration then 
      raise Timeout
    else
      try f x with
      | Timeout -> raise Timeout
      | _ -> loop ()
  in
  loop ()

and solve_equations_with_timeout (eqs : equa) (timeout_duration : float) : (equa * env) option =
  try
    with_timeout timeout_duration (fun substitutions_acc -> unif eqs substitutions_acc) []
  with
  | Timeout -> None

  and contains_type target_ty t =
    t = target_ty ||
    match t with
    | Arr(t1, t2) -> contains_type target_ty t1 || contains_type target_ty t2
    | _ -> false
  
  (* Type inference function *)
  and infer_type (te : pterm) (env : env) : ptype option =
    let ty = Var (nouvelle_var_t ()) in
    print_endline ("Type cible: " ^ (print_type ty));
  
    (* Génère les équations à partir du terme et du type cible *)
    let equations = genere_equa te ty env in
  
    (* Sépare les équations contenant le type cible (ty) des autres équations *)
    let (eqs_with_ty, eqs_without_ty) =
      List.partition (fun (t1, t2) ->
          contains_type ty t1 || contains_type ty t2) equations in
  
    (* Combine les équations sans ty avec celles contenant ty à la fin *)
    let new_eqs = eqs_without_ty @ eqs_with_ty in
    
    print_endline "Équations générées:";
    List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) equations;
  
    match solve_equations_with_timeout new_eqs 2.0 with
    | None -> None
    | Some (eqs, substitutions) -> 
        let final_type = apply_substitutions ty substitutions in
        Some final_type
  


(* vérifie si un type est bien formé *)
and check_type (t : ptype) : bool =
  match t with
  | Var _ -> true (* Considère une variable de type comme valide *)
  | Arr (t1, t2) -> (check_type t1) && (check_type t2)
  | Nat -> true
  | List t1 -> check_type t1
  | ForAll (_, t1) -> check_type t1
  | Prod (t1, t2) -> (check_type t1) && (check_type t2)

  ;; (* Test *)
    (* Tests du système de typage *)
  let test_typing () =
      (* Helper pour afficher les résultats de test *)
    let test_case name term =
      print_endline ("\n=== Test: " ^ name ^ " ===");
      match infer_type term [] with
      | Some ty -> Printf.printf "Type inféré: %s\n" (print_type ty)
      | None -> print_endline "Erreur de typage"
    in
    
    (* Prod(int, int ) *)
    let prod_int_int : pterm = Prod (Int 1, Int 2) in
    test_case "Produit de deux entiers" prod_int_int;
    
    (* Prod(int, abs)*)
    let prod_int_abs : pterm = Prod (Int 1, Abs("x", Var "x")) in
    test_case "Produit d'un entier et d'une abstraction" prod_int_abs;
    
    (* ProJG (Prod(int, int)) *)
    let projg_prod_int_int : pterm = ProjG (Prod (Int 1, Int 2)) in
    test_case "Projection gauche d'un produit d'entiers" projg_prod_int_int;
    
    (* ProJD (Prod(int, int)) *)
    let projd_prod_int_int : pterm = ProjD (Prod (Int 1, Int 2)) in
    test_case "Projection droite d'un produit d'entiers" projd_prod_int_int;
    
    (* Prod(Prod(int, int), int) *)
    let prod_prod_int_int_int : pterm = Prod (Prod (Int 1, Int 2), Int 3) in
    test_case "Produit d'un produit d'entiers et d'un entier" prod_prod_int_int_int;
    
    (* ProJg (Prod (Abs("x", Var "x"), int)) *)
    let projg_prod_abs_int : pterm = ProjG (Prod (Abs("x", Var "x"), Int 1)) in
    test_case "Projection gauche d'un produit d'une abstraction et d'un entier" projg_prod_abs_int;
    
    (* ProJd (Prod (Abs("x", Var "x"), int)) *)
    let projd_prod_abs_int : pterm = ProjD (Prod (Abs("x", Var "x"), Int 1)) in
    test_case "Projection droite d'un produit d'une abstraction et d'un entier" projd_prod_abs_int;
    


    (* (I, I K) *)
    let id = Abs("x", Var "x") in
    let k = Abs ("x", Abs ("y", Var "x")) in
    let prod_id_k : pterm = Prod (id, App (id, k)) in
    test_case "Produit de l'identité et de K" prod_id_k;
    
    (* (λc.(Π1 c) (Π2 c)) (I , I K ) *)
    let c = Abs("c", App (ProjG (Var "c"), ProjD (Var "c"))) in
     (* λc.(Π1 c) (Π2 c) *)
    test_case "Fonction qui applique les projections 1 et 2 à une paire" c;

    let term = App (c, prod_id_k) in
    test_case "Application de la projection 1 et 2 à une paire" term
    
    
    (* Lancer tous les tests *)
  let _ = test_typing ()