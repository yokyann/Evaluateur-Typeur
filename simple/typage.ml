open Eval


(* 1. Définition des types simples *)
type ptype = 
  | VarT of string     (* variables de type *)
  | Arr of ptype * ptype  (* type flèche T1 -> T2 *)
  | Nat               (* type de base *)

(* 2. Pretty printer pour les types *)
let rec print_type (t : ptype) : string =
  match t with
  | VarT x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "Nat"

(* Type pour les équations de typage *)
type equa = (ptype * ptype) list
type env = (string * ptype) list

(* Compteur pour générer des variables de type fraîches *)
let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string = 
  let x = "T" ^ (string_of_int !compteur_var_t) in
  compteur_var_t := !compteur_var_t + 1;
  x

(* Recherche d'un type dans l'environnement *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | [] -> raise (Failure ("Variable " ^ v ^ " non trouvée dans l'environnement"))
  | (x, t)::rest -> if x = v then t else cherche_type v rest

(* 3. Génération d'équations de typage *)
let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with
  | Var v -> 
      let tv = cherche_type v e in
      let eq = [(tv, ty)] in
      (* print_endline ("Équation générée: " ^ (print_type tv) ^ " = " ^ (print_type ty)); *)
      eq
  | App (t1, t2) ->
      let ta = VarT(nouvelle_var_t()) in  (* type frais pour l'argument *)
      let eq1 = genere_equa t1 (Arr(ta, ty)) e in  (* type de t1 doit être ta -> ty *)
      let eq2 = genere_equa t2 ta e in  (* type de t2 doit être ta *)
      let eq = eq1 @ eq2 in
      (* List.iter (fun (t1, t2) -> print_endline ("Équation générée: " ^ (print_type t1) ^ " = " ^ (print_type t2))) eq; *)
      eq
  | Abs (x, t) ->
      let ta = VarT(nouvelle_var_t()) in  (* type frais pour le paramètre *)
      let tr = VarT(nouvelle_var_t()) in  (* type frais pour le retour *)
      let eq1 = [(ty, Arr(ta, tr))] in  (* le type de l'abstraction est ta -> tr *)
      let eq2 = genere_equa t tr ((x, ta)::e) in  (* type du corps avec x:ta dans l'env *)
      let eq = eq1 @ eq2 in
      (* List.iter (fun (t1, t2) -> print_endline ("Équation générée: " ^ (print_type t1) ^ " = " ^ (print_type t2))) eq; *)
      eq

(* 4. Occur check - vérifie si une variable apparaît dans un type *)
let rec occur_check (v : string) (t : ptype) : bool =
  match t with
  | VarT x -> x = v
  | Arr (t1, t2) -> occur_check v t1 || occur_check v t2
  | Nat -> false

(* 5. Substitution dans les types *)
let rec subst_type (v : string) (t_subst : ptype) (t : ptype) : ptype =
  match t with
  | VarT x -> if x = v then t_subst else t
  | Arr (t1, t2) -> Arr (subst_type v t_subst t1, subst_type v t_subst t2)
  | Nat -> Nat
(* Fonction pour appliquer une substitution sur un type *) 
let rec apply_substitutions (t : ptype) (substitutions : env) : ptype =
  match t with
  | VarT x -> 
      (match List.assoc_opt x substitutions with
       | Some t' -> t'  (* Si une substitution est trouvée, on l'applique *)
       | None -> t)  (* Sinon, on renvoie le type tel quel *)
  
  | Arr (t1, t2) -> 
      Arr (apply_substitutions t1 substitutions, 
           apply_substitutions t2 substitutions)  (* Applique les substitutions récursivement aux types de la fonction *)

  | _ -> t  (* Si le type est un type de base, on le renvoie tel quel *)


(* Substitution dans un système d'équations *)
let subst_equa (v : string) (t_subst : ptype) (eqs : equa) : equa =
  List.map (fun (t1, t2) -> 
      (subst_type v t_subst t1, subst_type v t_subst t2)
    ) eqs

(* 6. Une étape d'unification *)
let rec unif_step (eqs : equa) (substitutions_acc : env) : (equa * env) option =
  (* print_endline "Équations avant unification:";
  List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eqs; *)

  match eqs with
  | [] -> Some ([], substitutions_acc)
  
  | (VarT x, t)::rest when not (occur_check x t) -> 
      let new_eqs = subst_equa x t rest in
      let new_substitutions = (x, t) :: substitutions_acc in
      (* print_endline ("Unification1: " ^ (print_type (VarT x)) ^ " avec " ^ (print_type t)); *)
      Some (new_eqs, new_substitutions)

  | (t, VarT x)::rest when not (occur_check x t) -> 
      let new_eqs = subst_equa x t rest in
      let new_substitutions = (x, t) :: substitutions_acc in
      (* print_endline ("Unification2: " ^ (print_type t) ^ " avec " ^ (print_type (VarT x))); *)
      Some (new_eqs, new_substitutions)

  | (Arr(t1a, t1b), Arr(t2a, t2b))::rest ->
      Some ((t1a, t2a)::(t1b, t2b)::rest, substitutions_acc)

  | (t1, t2)::rest when t1 = t2 -> 
      (* print_endline ("Unification3: " ^ (print_type t1) ^ " avec " ^ (print_type t2)); *)
      unif_step rest substitutions_acc

  | _ -> None


(* 7. Résolution complète du système d'équations avec timeout *)
let rec unif (eqs : equa) (substitutions_acc : env) : (equa * env) option =
  (* print_endline "Équations à unifier:";

  List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eqs; *)

  match unif_step eqs substitutions_acc with
  | None -> None
  | Some ([], new_substitutions) -> Some ([], new_substitutions)  (* Retourner la liste vide et les substitutions accumulées *)
  | Some (new_eqs, new_substitutions) -> 
      (* print_endline "Nouvelles équations après unification:";
      List.iter (fun (t1, t2) -> print_endline ((print_type t1) ^ " = " ^ (print_type t2))) new_eqs; *)
      unif new_eqs new_substitutions  (* Continuez avec les nouvelles équations et substitutions *)


exception Timeout

let with_timeout duration f x =
  let start_time = Sys.time () in  (* Enregistre le temps de départ *)
  let rec loop () =
    if Sys.time () -. start_time > duration then raise Timeout  (* Vérifie si le timeout est dépassé *)
    else
      try f x with
      | Timeout -> raise Timeout  (* Relance l'exception si elle a été levée *)
      | _ -> loop ()  (* Continue si une exception autre est levée *)
  in
  loop ()
  
let solve_equations_with_timeout (eqs : equa) (timeout_duration : float) : (equa * env) option =
  try
    with_timeout timeout_duration (fun substitutions_acc -> unif eqs substitutions_acc) []  (* Passer une fonction qui appelle unif *)
  with
  | Timeout -> None

let infer_type (te : pterm) (env : env) : ptype option =
  let ty = VarT (nouvelle_var_t ()) in

  let equations = genere_equa te ty env in
  let head = List.hd equations in
  let tail = List.tl equations in
  let new_eqs = tail @ [head] in

  match solve_equations_with_timeout new_eqs 2.0 with
  | None -> None
  | Some (eqs, substitutions) -> 
      (* Affiche les équations finales après unification *)
      (* print_endline "Équations finales après unification:";
      List.iter (fun (t1, t2) -> 
          print_endline ((print_type t1) ^ " = " ^ (print_type t2))) eqs; *)

      (* Applique les substitutions au type frais *)
      let final_type = apply_substitutions ty substitutions in

      (* Vérifie s'il ne reste qu'une seule équation *)
      if List.length eqs = 1 then
        match List.hd eqs with
        | (VarT ty, t) -> 
            print_endline ("Type final: " ^ (print_type final_type));
            Some final_type  (* Retourne le type après application des substitutions *)
        | _ -> 
            print_endline "Erreur de typage: plusieurs équations restantes.";
            Some final_type  (* Retourne le type après application des substitutions *)
      else 
        Some final_type  (* Retourne le type après application des substitutions *)


(* 8. Tests *)
let test_typing () =
  (* Test 1: identité *)
  let id = Abs("x", Var "x") in
  (match infer_type id [] with
    | Some ty -> print_string ("Type de l'identité: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour l'identité.\n");

  (* delta *)
  let delta = Abs ("x", App (Var "x", Var "x")) in
  (match infer_type delta [] with
    | Some ty -> print_string ("Type de delta: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour delta.\n");

  (* Test 3: omega *)
  let omega = App (Abs("x", App(Var "x", Var "x")), Abs("x", App(Var "x", Var "x"))) in
  (match infer_type omega [] with
    | Some ty -> print_string ("Type de omega: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour omega.\n");

  let s = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var"z"), App (Var "y", Var "z"))))) in
  (match infer_type s [] with
    | Some ty -> print_string ("Type de s: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour s.\n");

  let k = Abs ("x", Abs ("y", Var "x")) in
  (match infer_type k [] with
    | Some ty -> print_string ("Type de k: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour k.\n");
  let skk = App (App (s, k), k) in
  (match infer_type skk [] with
    | Some ty -> print_string ("Type de skk: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour skk.\n");


  let kii = App (App (k, id), id) in
  (match infer_type kii [] with
    | Some ty -> print_string ("Type de kii: " ^ (print_type ty) ^ "\n")
    | None -> print_string "Erreur de typage pour kii.\n")


let _ = test_typing ()

