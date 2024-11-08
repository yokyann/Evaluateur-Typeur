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
    (* Traits Impératifs*)
    | Ref of pterm                       (* allocation *)
    | DeRef of pterm                     (* dereference *)
    | Assign of pterm * pterm            (* assignement *)
    | Unit                              (* unité *)
    | Address of int                  (* adresse d'une variable *)
  and memory = (int * pterm) list

  let address : int ref = ref 0  (* Compteur d'adresse pour la mémoire *)
  let new_address () : int =
    address := !address + 1;
    !address

  let search_memory (addr : int) (mem : memory) : pterm option =
    try Some (List.assoc addr mem) with Not_found -> None

  let search_memory_term (term : pterm) (mem : memory) : int option =
    let rec search (mem : memory) : int option =
      match mem with
      | [] -> None
      | (addr, term') :: rest -> if term = term' then Some addr else search rest
    in search mem

  let add_memory (term : pterm) (mem : memory) : (int * memory) =
    let addr = new_address () in
    (addr, (addr, term) :: mem)

  let update_memory (addr : int) (term : pterm) (mem : memory) : memory =
    (addr, term) :: List.remove_assoc addr mem

  let rec print_memory (mem : memory) : string =
    match mem with
    | [] -> ""
    | (addr, term) :: rest -> 
      "Addr: " ^ string_of_int addr ^ " => " ^ print_term term ^ "\n" ^ print_memory rest


  and print_term (t : pterm) : string =
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
    | Ref t -> "ref(" ^ print_term t ^ ")"
    | DeRef t -> "!" ^ print_term t
    | Assign (t1, t2) -> print_term t1 ^ " := " ^ print_term t2
    | Unit -> "()"

    
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
    | Ref t -> Ref (alphaconv t)
    | DeRef t -> DeRef (alphaconv t)
    | Assign (t1, t2) -> Assign (alphaconv t1, alphaconv t2)
    | Unit -> Unit

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
    | Ref t -> Ref (substitue t old_var new_var)
    | DeRef t -> DeRef (substitue t old_var new_var)
    | Assign (t1, t2) -> Assign (substitue t1 old_var new_var, substitue t2 old_var new_var)
    | Unit -> Unit

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
    | Ref t -> Ref (substitution x n t)
    | DeRef t -> DeRef (substitution x n t)
    | Assign (t1, t2) -> Assign (substitution x n t1, substitution x n t2)
    | Unit -> Unit

  (* ;;
    (* Test substitution *)
    let term = App ((App (Var "x", Var "z")), Abs ("y", App (Var "x", Var "y")))
    in print_string (print_term term) ;
    print_string (print_term (substitution "x" (Abs ("t", Var "t")) term)) ;; *)
  (* Fonction de réduction Call-by-Value (LtR-CbV) *)
  let rec ltr_cbv_step (t : pterm) (mem : memory): (pterm*memory) option =
    match t with
    | Var _ | Abs _ | Int _ | Nil -> None  (* Les valeurs ne peuvent pas être réduites *)
    | App (t1, t2) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) ->Some((App (t1', t2)), mem)  (* Réduction de la partie gauche de l'application *)
        | None ->
          match t1 with
          | Abs (x, body) ->
            (match ltr_cbv_step t2 mem with
              | Some (t2', mem) -> Some ((App (t1, t2')), mem)  (* Réduction de l'argument *)
              | None -> Some ((substitution x t2 body), mem))  (* β-réduction *)
        | _ ->
          match ltr_cbv_step t2 mem with
          | Some (t2', mem) -> Some ((App (t1, t2')), mem)
          | None -> None)
    | Let (x, e1, e2) ->
      (match ltr_cbv_step e1 mem with
      (* Substitution de x par v dans e2 puis evaluation de e2*)
        | Some (v, mem) -> Some ((substitution x v e2), mem)
        | None -> if is_value e1 then Some ((substitution x e1 e2), mem) else failwith "e1 n'est pas une valeur, ni réductible")
    | Fix (phi, m) ->
      (* on remplace phi par fix partout dans M *)
      Some ((substitution phi (Fix (phi, m)) m), mem)
    | IfZero (Int(0), t1, _) -> Some (t1, mem)
    | IfZero (Int(_), _, t2) -> Some (t2,mem)
    | IfZero (t1, t2, t3) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) -> Some ((IfZero (t1', t2, t3)), mem)
        | None -> failwith "If condition is not an integer")
    | IfEmpty (Nil, t1, _) -> Some (t1, mem)
    | IfEmpty (Cons(_, _), _, t2) -> Some (t2, mem)
    | IfEmpty (t1, t2, t3) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) -> Some ((IfEmpty (t1', t2, t3)), mem)
        | None -> failwith "If condition is not a list")
    | Add (t1, t2) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) -> Some ((Add (t1', t2)), mem)  (* Réduction du premier opérande *)
        | None ->
          match ltr_cbv_step t2 mem with
          | Some (t2', mem) -> Some ((Add (t1, t2')), mem)  (* Réduction du second opérande *)
          | None ->
            match t1, t2 with
            | Int n1, Int n2 -> Some ((Int (n1 + n2)), mem)  (* Évaluation de l'addition *)
            | _ -> None)
    | Sub (t1, t2) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) -> Some ((Sub (t1', t2)) , mem) (* Réduction du premier opérande *)
        | None ->
          match ltr_cbv_step t2 mem with
          | Some (t2', mem) -> Some ((Sub (t1, t2')), mem)  (* Réduction du second opérande *)
          | None ->
            match t1, t2 with
            | Int n1, Int n2 -> Some ((Int (n1 - n2)), mem)  (* Évaluation de la soustraction *)
            | _ -> None)
    | Mul (t1, t2) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) -> Some ((Mul (t1', t2)), mem)  (* Réduction du premier opérande *)
        | None ->
          match ltr_cbv_step t2 mem with
          | Some (t2', mem) -> Some ((Mul (t1, t2')), mem)  (* Réduction du second opérande *)
          | None ->
            match t1, t2 with
            | Int n1, Int n2 -> Some ((Int (n1 * n2)), mem)  (* Évaluation de la multiplication *)
            | _ -> None)
    | Cons (t1, t2) ->
      (match ltr_cbv_step t1 mem with
        | Some (t1', mem) -> Some ((Cons (t1', t2)), mem)  (* Réduction de la tête *)
        | None ->
          match ltr_cbv_step t2 mem with
          | Some (t2', mem) -> Some ((Cons (t1, t2')), mem)  (* Réduction de la queue *)
          | None -> None)
    | Head l ->
      (match ltr_cbv_step l mem with
        | Some (l', mem) -> Some ((Head l'), mem)  (* Réduction de l'argument de Head *)
        | None ->
          match l with
          | Cons (hd, _) -> Some (hd, mem)  (* Extraction de la tête de la liste *)
          | _ -> None)
    | Tail l ->
      (match ltr_cbv_step l mem with
        | Some (l', mem) -> Some ((Tail l'), mem)  (* Réduction de l'argument de Tail *)
        | None ->
          match l with
          | Cons (_, tl) -> Some (tl, mem)  (* Extraction de la queue de la liste *)
          | _ -> None)
    | Ref m -> 
      (match ltr_cbv_step m mem with 
      | Some (v, mem) -> if is_value v then Some (Ref v, mem) else failwith "m n'est pas une valeur"
      | None -> None)

    | DeRef e ->
      (match ltr_cbv_step e mem with
      | Some (Address addr, mem) -> 
        (match search_memory addr mem with
        | Some v -> Some (v, mem)
        | None -> None)
      | None -> None
      | _ -> None)

    | Assign (e1, e2) ->
      (match ltr_cbv_step e1 mem with
      | Some (Address addr, mem) -> 
        (match ltr_cbv_step e2 mem with
        | Some (v, mem) -> Some (Unit, update_memory addr v mem)
        | None -> None)
      | None -> None
      | _ -> None)
      
    | Unit | Address _ -> None


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
    match ltr_cbv_step t [] with
    | Some (t', mem) -> ltr_cbv_norm t'  (* Réduire et continuer *)
    | None -> t  (* Si plus de réductions possibles, retourner le terme final *)

  (* Exception à lever en cas de dépassement de la limite *)
  exception Timeout  (* Exception à lever en cas de dépassement de la limite *)

  (* Fonction de normalisation avec timeout pour éviter les boucles infinies *)
  let rec ltr_cbv_norm_with_timeout (t : pterm) (mem : memory) (timeout : int) : pterm =
    if timeout <= 0 then raise Timeout  (* Si le timeout est atteint, lever une exception *)
    else match ltr_cbv_step t mem with
      | Some (t', mem) -> ltr_cbv_norm_with_timeout t' mem (timeout - 1)  (* Réduire et continuer *)
      | None -> t  (* Si plus de réductions possibles, retourner le terme final *)

  (* Fonction de normalisation avec timeout pour éviter les boucles infinies *)
  (* Test LtR-CbV *)
  ;;
