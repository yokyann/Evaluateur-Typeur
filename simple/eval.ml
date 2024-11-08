type pterm = 
    Var of string
  | App of pterm * pterm
  | Abs of string * pterm

let rec print_term (t : pterm) : string =
  match t with
  Var x -> x
  | App (t1 , t2) -> "(" ^ ( print_term t1) ^" "^ ( print_term t2) ^ ")"
  | Abs (x, t) -> "(fun "^ x ^" -> " ^ ( print_term t) ^")"

(* compteur global *)
let compteur_var : int ref = ref 0

(* création d'une nouvelle variable *)
let nouvelle_var () : string = 
  compteur_var := ! compteur_var + 1;
  "X"^( string_of_int ! compteur_var )

(* Fonction d'alpha-conversion *)
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x  (* Les variables libres restent inchangées *)
  | App (t1, t2) -> App (alphaconv t1, alphaconv t2)  (* Appliquer l'alpha-conversion récursivement *)
  | Abs (x, t1) ->
      let new_x = nouvelle_var () in  (* Générer une nouvelle variable pour l'abstraction *)
      let new_t1 = alphaconv (substitue t1 x new_x) in  (* Appliquer l'alpha-conversion dans le corps *)
      Abs (new_x, new_t1)

(* Fonction pour substituer une variable liée par une nouvelle dans le corps de l'abstraction *)
and substitue (t : pterm) (old_var : string) (new_var : string) : pterm =
  match t with
  | Var x -> if x = old_var then Var new_var else Var x
  | App (t1, t2) -> App (substitue t1 old_var new_var, substitue t2 old_var new_var)
  | Abs (x, t1) ->
      if x = old_var then Abs (x, t1)  (* Ne pas changer la variable liée si elle correspond à old_var *)
      else Abs (x, substitue t1 old_var new_var)

(* ;;
(* Test alpha conversion *)
let term = Abs ("x", App ( (App (Var "x", Var "z")), 
Abs ("x", App (Var "x", Var "y"))))
in print_string (print_term term) ;
print_string (print_term (alphaconv term)) *)

(* remplace toutes les occurences libres d’une variable donn´ee par
un terme. *)
let rec substitution (x:string) (n:pterm) (t:pterm) : pterm = 
  match t with 
  | Var y -> if y=x then n else Var y
  | App (t1,t2) -> App (substitution x n t1, substitution x n t2)
  | Abs (y,t1) -> if y=x then Abs (y,t1) else Abs (y,substitution x n t1)

(* ;;
(* Test substitution *)
let term = App ((App (Var "x", Var "z")), Abs ("y", App (Var "x", Var "y")))
in print_string (print_term term) ;
print_string (print_term (substitution "x" (Abs ("t", Var "t")) term)) ;; *)
(* Fonction de réduction Call-by-Value (LtR-CbV) *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with
  (* Les variables ne se réduisent pas *)
  | Var _ -> None

  (* Réduction dans une application *)
  | App (t1, t2) ->
    (* D'abord, essayer de réduire t1 (la fonction) *)
    (match ltr_cbv_step t1 with
      | Some t1_reduit -> Some (App (t1_reduit, t2))  (* Réduire la fonction *)
      | None ->
       (* Si t1 est une abstraction et t2 est une valeur, appliquer la β-réduction *)
      (match t1, is_value t2 with
        | Abs (x, body), true -> Some (substitution x t2 body)
        | _ ->
          (* Sinon, essayer de réduire l'argument t2 *)
          (match ltr_cbv_step t2 with
            | Some t2_reduit -> Some (App (t1, t2_reduit))
            | None -> None)))  (* Pas de réduction possible *)

  (* Les abstractions sont des valeurs, donc pas de réduction directe *)
  | Abs (_, _) -> None

(* Fonction auxiliaire pour vérifier si un terme est une valeur *)
and is_value (t : pterm) : bool =
  match t with
  | Abs (_, _) -> true  (* Une abstraction est une valeur *)
  | Var _ -> true        (* Une variable est aussi une valeur *)
  | _ -> false  (* Les applications ne sont pas des valeurs *)

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
(* identité *)
let i = Abs ("x", Var "x") in
let term_normal = ltr_cbv_norm_with_timeout i 200 in
print_string "test i\n";
print_string (print_term term_normal)  (* Devrait retourner "fun x -> x" *)
;
print_char('\n')

;

(* delta *)
let delta = Abs ("x", App (Var "x", Var "x")) in
let term_normal = ltr_cbv_norm_with_timeout delta 200 in
print_string "test delta\n";
print_string (print_term term_normal)  (* Devrait retourner "fun x -> x x" *);
print_char('\n')
;
(* omega *)
let omega = App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))) in
try
  print_string "test omega\n";
  let term_normal = ltr_cbv_norm_with_timeout omega 100 in
  print_string (print_term term_normal)
  ;
  print_char('\n')
with Timeout ->
  print_string "La réduction a divergé."  (* Timeout déclenché *)
  ;
  print_char('\n')
;

let s = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))) in
let term_normal = ltr_cbv_norm_with_timeout s 200 in
print_string "test s\n";
print_string (print_term term_normal)  (* Devrait retourner "fun x -> fun y -> fun z -> x z (y z)" *)
;
print_char('\n')
;

let k = Abs ("x", Abs ("y", Var "x")) in

(* combinatoire *)
let skk = App (App (s, k), k) in
let term_normal = ltr_cbv_norm_with_timeout skk 200 in
print_string "test skk\n";
print_string (print_term term_normal)  (* Devrait retourner "fun z -> z" *)
;
print_char('\n')
;
let sii = App (App (s, i), i) in
let term_normal = ltr_cbv_norm_with_timeout sii 200 in
print_string "test sii\n";
print_string (print_term term_normal)  (* Devrait retourner "fun x -> x" *)
;
print_char('\n')
;

let delta_id = App(delta, i) in
let term_normal = ltr_cbv_norm_with_timeout delta_id 200 in
print_string "test delta id\n";
print_string (print_term term_normal)  (* Devrait retourner "fun x -> x x" *)
;
print_char('\n')
;

let delta_delta = App(delta, delta) in
try 
  print_string "test delta delta\n";
  let term_normal = ltr_cbv_norm_with_timeout delta_delta 100 in
  print_string (print_term term_normal)
  ;
  print_char('\n')
with Timeout ->
  print_string "La réduction a divergé."  (* Timeout déclenché *)
  
;
print_char('\n')
;
let kii = App (App (k, i), i) in
let term_normal = ltr_cbv_norm_with_timeout kii 200 in
print_string "test kii\n";
print_string (print_term term_normal)  (* Devrait retourner "fun y -> y" *)
;
print_char('\n')
;

(* Encodage de 0 en nombre de Church *)
let zero = Abs ("f", Abs ("x", Var "x")) in 
let term_normal = ltr_cbv_norm_with_timeout zero 200 in
let result = print_term term_normal in
print_string "test zero\n";
print_string result  (* Devrait retourner "fun f -> fun x -> x" *)
;
print_char('\n')
;

(* Encodage de 1 en nombre de Church *)
let one = Abs ("f", Abs ("x", App (Var "f", Var "x"))) in
let term_normal = ltr_cbv_norm_with_timeout one 200 in
let result = print_term term_normal in
print_string "test one\n";
print_string result  (* Devrait retourner "fun f -> fun x -> f x" *)
;
print_char('\n')
;

(* Encodage de 2 en nombre de Church *)
let two = Abs ("f", Abs ("x", App (Var "f", App (Var "f", Var "x")))) in
let term_normal = ltr_cbv_norm_with_timeout two 200 in
let result = print_term term_normal in
print_string "test two\n";
print_string result  (* Devrait retourner "fun f -> fun x -> f (f x)" *)
;
print_char('\n')
;

(* Encodage de 3 en nombre de Church *)
let three = Abs ("f", Abs ("x", App (Var "f", App (Var "f", App (Var "f", Var "x"))))) in
let term_normal = ltr_cbv_norm_with_timeout three 200 in
let result = print_term term_normal in
print_string "test three\n";
print_string result  (* Devrait retourner "fun f -> fun x -> f (f (f x))" *)
;
print_char('\n')
;

(* Encodage de 4 en nombre de Church *)

(* fonction d'addition *)
let add = Abs ("m", Abs ("n", Abs ("f", Abs ("x", App (App (Var "m", Var "f"), App (App (Var "n", Var "f"), Var "x")))))) in 
(* Exemple test de normalisation : addition de 1 et 1 *)
let term = App (App (add, one), one) in
let result = ltr_cbv_norm_with_timeout term 200 in
print_string "test add 1 1\n";
print_string (print_term result)  (* Devrait donner 2 *)
;
print_char('\n')
;

(* Fonction de multiplication en lambda-calcul *)
let mul = Abs ("m", Abs ("n", Abs ("f", App (Var "m", App (Var "n", Var "f"))))) in
(* Exemple de test de normalisation : multiplication de 1 et 2 *)
let term = App (App (mul, one), two) in
let result = ltr_cbv_norm_with_timeout term 200 in
print_string "test mul 1 2\n";
print_string (print_term result)  (* Devrait donner 2 *)
;
print_char('\n')
;

(* Fonction d'exponentiation en lambda-calcul *)
let exp = Abs ("m", Abs ("n", App (Var "n", Var "m"))) in
(* Exemple de test de normalisation : 2 exposant 0 *)
let term = App (App (exp, two), zero) in
let result = ltr_cbv_norm_with_timeout term 200 in
print_string "test exp 2 0\n";
print_string (print_term result)  (* Devrait donner 1 *)
;
print_char('\n')
;

(* Fonction d'incrémentation en lambda-calcul *)
let succ = Abs ("n", Abs ("f", Abs ("x", App (Var "f", App (App (Var "n", Var "f"), Var "x")))))
in 
(* exemple de test de normalisation : successeur de 1 *)
let term = App (succ, one) in
let result = ltr_cbv_norm_with_timeout term 200 in
print_string "test succ 1\n";
print_string (print_term result)  (* Devrait donner 2 *)
;
print_char('\n')
;

(* Fonction de prédécesseur en lambda-calcul *)
let pred = Abs ("n", Abs ("f", Abs ("x", App (App (App (Var "n", Abs ("g", Abs ("h", App (Var "h", App (Var "g", Var "f"))))), Abs ("u", Var "x")), Abs ("u", Var "u")))))
in
(* exemple de test de normalisation : prédécesseur de 2 *)
let term = App (pred, two) in
let result = ltr_cbv_norm_with_timeout term 200 in
print_string "test pred 2\n";
print_string (print_term result)  (* Devrait donner 1 *)
;
print_char('\n')
;



