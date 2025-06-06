(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27"]

open Type
open Minimir
open Active_borrows

(* This function computes the set of alive lifetimes at every program point. *)
let compute_lft_sets prog mir : lifetime -> PpSet.t =

  (* The [outlives] variable contains all the outlives relations between the
    lifetime variables of the function. *)
  let outlives = ref LMap.empty in

  (* Helper functions to add outlives constraints. *)
  let add_outlives (l1, l2) = outlives := add_outlives_edge l1 l2 !outlives in
  let unify_lft l1 l2 =
    add_outlives (l1, l2);
    add_outlives (l2, l1)
  in

  (* First, we add in [outlives] the constraints implied by the type of locals. *)
  Hashtbl.iter
    (fun _ typ -> outlives := outlives_union !outlives (implied_outlives prog typ))
    mir.mlocals;

  (* Then, we add the outlives relations needed for the instructions to be safe. *)

  (* 3 TODO: generate these constraints by
       - unifying types that need be equal (note that MiniRust does not support subtyping, that is,
         if a variable x: &'a i32 is used as type &'b i32, then this requires that lifetimes 'a and
         'b are equal),
       - adding constraints required by function calls,
       - generating constraints corresponding to reborrows. More precisely, if we create a borrow
         of a place that dereferences  borrows, then the lifetime of the borrow we
         create should be shorter than the lifetimes of the borrows the place dereference.
         For example, if x: &'a &'b i32, and we create a borrow y = &**x of type &'c i32,
         then 'c should be shorter than 'a and 'b.

    SUGGESTION: use functions [typ_of_place], [fields_types_fresh] and [fn_prototype_fresh].
  *)
  (*
  Ensuite, nous ajoutons les relations de survies nécessaires pour que les instructions ne soient pas dangereuses
  À FAIRE : Générer ces contraintes en :
    - unifiant les types qui nécessitent d'être égaux (notez que MiniRust ne supporte pas le sous-typage, autrement dit,
      si une variable x: &'a i32 est utilisée avec le type &'b i32, alors il est nécessaire que les durées de vie 'a et 'b
      soient égales),
    - ajoutant les contraintes requises par les appels de fonction,
    - générant les contraintes correspondant aux réemprunts. Plus précisément, si nous créons un emprunt
      sur une place qui déréférence des emprunts, alors la durée de vie de l'emprunt que l'on créé
      doit être plus courte que les durées de vie des emprunts que la place déréférence.
      Par exemple, si x: &'a &'b i32, et on créé un emprunt y = &**x de type &'c i32, alors c doit être
      plus courte que 'a et 'b.
  
  SUGGESTION: utilisez les fonctions [typ_of_place], [fields_types_fresh] et [fn_prototype_fresh].
  *)
  let rec recursive_add_borrow_constraints outliving_lft t =
    match t with
    | Tborrow (lft, _, t') ->
      add_outlives (outliving_lft, lft);
      recursive_add_borrow_constraints outliving_lft t'
    | _ -> () (*ptet qlqc à faire qd on est dans le cas struct*)
  in

  Array.iteri
    (fun _ (instr, loc) ->
      match instr with
      | Iassign (pl, rv, _) ->
      (
        let typPl = typ_of_place prog mir pl in
        match typPl with
        | Tstruct (_, l) ->
          (
            match rv with
            | RVconst _ -> () (*yes*)
            | RVunit -> () (*yes*)
            | RVplace p (*unify ?*)
            | RVborrow(_, p) (*AAAAAAAAAAAA*)
            | RVunop(_, p) ->
              (
                match typ_of_place prog mir p with
                | Tborrow _ -> failwith "Supposedly unreachable"
                | Tstruct (_, l') -> List.iter2 (fun lft lft' -> unify_lft lft lft') l l'
                | _ -> () (*Ok I believe*)
              )
            | RVbinop(_, p1, p2) ->
              (
                match typ_of_place prog mir p1, typ_of_place prog mir p2 with
                | Tstruct (_, l'), Tstruct (_, l'') ->
                  List.iter2 (fun lft lft' -> unify_lft lft lft') l l';
                  List.iter2 (fun lft lft'' -> unify_lft lft lft'') l l''
                | _ -> () (*Ok I believe*)
              )
            | RVmake(name, pList) -> (*should be okay*)
              let (tList, t) = fields_types_fresh prog name in
              List.iter2 (
              fun t' p ->
                let t = typ_of_place prog mir p in
                match t, t' with
                | Tstruct (_, l), Tstruct (_, l') ->
                  List.iter2 (fun lft lft' -> add_outlives (lft, lft')) l l'
                | Tborrow (lft, _, _), Tborrow (lft', _, _) -> add_outlives (lft, lft')
                | _ -> ()
              ) (t::tList) (pl::pList)
          )
        | Tborrow (lftPl, _, _) ->
          (
            match rv with
            | RVconst _ -> () (*yes*)
            | RVunit -> () (*yes*)
            | RVplace p (*unify ?*)
            | RVborrow(_, p) (*AAAAAAAAAAAA*)
            | RVunop(_, p) ->
              (
                let t = typ_of_place prog mir p in
                match t with
                | Tstruct _ -> failwith "Supposedly unreachable"
                | Tborrow (lft', _, _) ->
                  if contains_deref_borrow p then
                    recursive_add_borrow_constraints lftPl t
                  else
                    unify_lft lftPl lft'
                | _ -> () (*Ok I believe*)
              )
            | RVbinop(_, p1, p2) ->
              (
                let t1, t2 = typ_of_place prog mir p1, typ_of_place prog mir p2 in
                match t1, t2 with
                | Tstruct _, _ | _, Tstruct _ -> failwith "Supposedly unreachable"
                | Tborrow (lft', _, _), Tborrow(lft'', _, _) ->
                  (
                    (if contains_deref_borrow p1 then
                      recursive_add_borrow_constraints lftPl t1
                    else
                      unify_lft lftPl lft');
                    (if contains_deref_borrow p2 then
                      recursive_add_borrow_constraints lftPl t2
                    else
                      unify_lft lftPl lft'')
                  )
                | Tborrow (lft', _, _), _ ->
                  if contains_deref_borrow p1 then
                    recursive_add_borrow_constraints lftPl t1
                  else
                    unify_lft lftPl lft'
                | _, Tborrow (lft', _, _) ->
                  if contains_deref_borrow p2 then
                    recursive_add_borrow_constraints lftPl t2
                  else
                    unify_lft lftPl lft'
                | _ -> () (*Ok I believe*)
              )
            | RVmake(name, pList) -> (*should be okay*)
              let (tList, t) = fields_types_fresh prog name in
              List.iter2 (
              fun t' p ->
                let t = typ_of_place prog mir p in
                match t, t' with
                | Tstruct (_, l), Tstruct (_, l') ->
                  List.iter2 (fun lft lft' -> add_outlives (lft, lft')) l l'
                | Tborrow (lft, _, _), Tborrow (lft', _, _) -> add_outlives (lft, lft')
                | _ -> ()
              ) (t::tList) (pl::pList)
          )
        | _ -> (); (*yes*)
      )
      | Ideinit _ -> () (*I believe : c juste un déréférencement*)
      | Igoto _ -> () (*yes*)
      | Iif _ -> () (*yes*)
      | Ireturn -> () (*yes*)
      | Icall (name, pList, pla, _) ->
        let (tList, t, cstr) = fn_prototype_fresh prog name in
        List.iter (fun lftPair -> add_outlives lftPair) cstr;
        (*pour les param et le type : mess around avec unify et juste outlive*)
        List.iter2 (
          fun t' p ->
            let t = typ_of_place prog mir p in
            match t, t' with
            | Tstruct (_, l), Tstruct (_, l') ->
              List.iter2 (fun lft lft' -> add_outlives (lft, lft')) l l'
            | Tborrow (lft, _, _), Tborrow (lft', _, _) -> add_outlives (lft, lft')
            | _ -> ()
          ) (t::tList) (pla::pList)
    )
    mir.minstrs;

  (* The [living] variable contains constraints of the form "lifetime 'a should be
    alive at program point p". *)
  let living : PpSet.t LMap.t ref = ref LMap.empty in

  (* Helper function to add living constraint. *)
  let add_living pp l =
    living :=
      LMap.update l
        (fun s -> Some (PpSet.add pp (Option.value s ~default:PpSet.empty)))
        !living
  in

  (* Run the live local analysis. See module Live_locals for documentation. *)
  let live_locals = Live_locals.go mir in

  (* 3 TODO: generate living constraints:
     - Add living constraints corresponding to the fact that lifetimes appearing free
       in the type of live locals at some program point should be alive at that
       program point.
     - Add living constraints corresponding to the fact that generic lifetime variables
       (those in [mir.mgeneric_lfts]) should be alive during the whole execution of the
       function.
  *)
  (* À FAIRE : Générer les contraintes de vie :
      - Ajouter les contraintes de vies correspondant au fait que les durées de vie
        apparaissant libres dans le type des locaux en vie à un point du programme
        devraient être en vie à ce point du programme
      - Ajouter les contraintes de vie correspondant au fait que les variable génériques
        de durée de vide (celles dans [mir.mgeneric_lfts]) devraient être en vie durant
        toute l'exécution de la fonction (fait par défaut)
  *)

  (* If [lft] is a generic lifetime, [lft] is always alive at [PpInCaller lft]. *)
  List.iter (fun lft -> add_living (PpInCaller lft) lft) mir.mgeneric_lfts;
 (*c'est bien ça : itérer sur les pp et pour chaque pp, appliquer live_locals et ajouter de pplocal*)
  (* let shoudFail =
    try
      (Some (live_locals 99))
    with
    | Invalid_argument e -> None in
  Printf.printf "ahi\n"; *)
  (* Array.iteri
    (fun _ (instr, loc) ->
      match instr with
      | Iassign (pl, rv, lbl) -> () (*loc of place à g et d et utiliser live_locals sur lbl*)
      | Ideinit _ -> () (*same*)
      | Igoto _ -> () (*yes*)
      | Iif _ -> () (*verif sur la condition*)
      | Ireturn -> () (*yes*)
      | Icall (name, pList, pla, _) -> () (*itérer sur les paramètres*)
    )
    mir.minstrs; *)
  let rec rec_add_lft lbl t =
    match t with
    | Tstruct (_, lfts) ->
      List.iter (add_living (PpLocal lbl)) lfts
    | Tborrow (lft, _, t') ->
      add_living (PpLocal lbl) lft;
      rec_add_lft lbl t'
    | _ -> ()
  in

  let lbl = ref 0 in
  try
    while true do
        LocSet.iter (
          fun l ->
            let t = typ_of_place prog mir (PlLocal l) in
            rec_add_lft !lbl t
        ) (live_locals (!lbl));
        lbl := !lbl + 1
    done;
  with
  | Invalid_argument e -> ();

  (* Now, we compute lifetime sets by finding the smallest solution of the constraints, using the
    Fix library. *)
  let module Fix = Fix.Fix.ForType (struct type t = lifetime end) (Fix.Prop.Set (PpSet))
  in
  Fix.lfp (fun lft lft_sets ->
      LSet.fold
        (fun lft acc -> PpSet.union (lft_sets lft) acc)
        (Option.value ~default:LSet.empty (LMap.find_opt lft !outlives))
        (Option.value ~default:PpSet.empty (LMap.find_opt lft !living)))

let borrowck prog mir =
  (* We check initializedness requirements for every instruction. *)
  let uninitialized_places = Uninitialized_places.go prog mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      let uninit : PlaceSet.t = uninitialized_places lbl in

      let check_initialized pl =
        if PlaceSet.exists (fun pluninit -> is_subplace pluninit pl) uninit then
          Error.error loc "Use of a place which is not fully initialized at this point."
      in

      (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) -> (
          match pl with
          | PlDeref pl0 ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into an uninitialized borrow."
          | PlField (pl0, _) ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into a field of an uninitialized struct."
          | _ -> ())
      | _ -> ());

      match instr with
      | Iassign (_, RVplace pl, _) | Iassign (_, RVborrow (_, pl), _) ->
          check_initialized pl
      | Iassign (_, RVbinop (_, pl1, pl2), _) ->
          check_initialized pl1;
          check_initialized pl2
      | Iassign (_, RVunop (_, pl), _) | Iif (pl, _, _) -> check_initialized pl
      | Iassign (_, RVmake (_, pls), _) | Icall (_, pls, _, _) ->
          List.iter check_initialized pls
      | Ireturn -> check_initialized (PlLocal Lret)
      | Iassign (_, (RVunit | RVconst _), _) | Ideinit _ | Igoto _ -> ())
    mir.minstrs;

  (* We check the code honors the non-mutability of shared borrows. *)
  Array.iteri
    (fun _ (instr, loc) ->
      (*2 TODO: check that we never write to shared borrows, and that we never create mutable borrows
        below shared borrows. Function [place_mut] can be used to determine if a place is mutable, i.e., if it
        does not dereference a shared borrow. *)
      match instr with
      | Iassign (pl, rv, _) ->
        if place_mut prog mir pl = Mut then (*Incorrect maybe probably*)
          match rv with
                | RVconst _ | RVunit -> ()
                | RVplace p -> () (*sure enough*)
                | RVborrow(Mut, p) -> (*Incorrect maybe probably*)
                  if not(contains_deref_borrow p) then
                    ()
                  else
                    Error.error loc "eror zere"
                | RVborrow(_, p) -> () (*sure enough*)
                | RVbinop(_, p1, p2) -> () (*sure enough*)
                | RVunop(_, p) -> () (*sure enough*)
                | RVmake(_, plist) -> () (*sure enough*)
        else
          Error.error loc "ther iz an eror"
      | Ideinit _ -> () (*unsure*) 
      | Iif _ -> () (*unsure*)
      | Icall _ -> () (*unsure*)
      | _ -> ()
    )
    mir.minstrs;

  let lft_sets = compute_lft_sets prog mir in

  (* 4 TODO: check that outlives constraints declared in the prototype of the function are
    enough to ensure safety. I.e., if [lft_sets lft] contains program point [PpInCaller lft'], this
    means that we need that [lft] be alive when [lft'] dies, i.e., [lft'] outlives [lft]. This relation
    has to be declared in [mir.outlives_graph]. *)
  
  (*pour toutes les lifetimes, faire la vérification ci-dessus*)
  let outlives lft lft' =
    let set = LMap.find lft mir.moutlives_graph in
    LSet.mem lft' set
  in
  let check_prototype_safety lft loc =
    let pointSet = lft_sets lft in
    PpSet.iter (
      fun point ->
        match point with
        | PpInCaller lft' ->
          if outlives lft' lft then ()
          else Error.error loc "ErOr HeRe"
        | _ -> ()
    ) pointSet
  in
  let rec rec_typ_safety_check t loc =
    match t with
    | Tstruct (_, l) ->
      List.iter (fun lft -> check_prototype_safety lft loc) l
    | Tborrow (lft, _, t') ->
      check_prototype_safety lft loc;
      rec_typ_safety_check t' loc
    | _ -> ()
  in
  let check_safety_from_place pl loc =
    let t = typ_of_place prog mir pl in
    rec_typ_safety_check t loc
  in
  Array.iteri
    (fun _ (instr, loc) ->
      match instr with
      | Iassign (pl, rv, _) ->
        (match rv with
        | RVplace p
        | RVborrow(_, p)
        | RVunop(_, p) -> check_safety_from_place p loc
        | RVbinop(_, p1, p2) ->
          check_safety_from_place p1 loc;
          check_safety_from_place p2 loc
        | RVmake(_, plist) ->
          List.iter (fun p -> check_safety_from_place p loc) plist
        | _ -> ())
      | Iif (p, _, _) -> check_safety_from_place p loc
      | Icall (_, l, p, _) ->
        List.iter (fun p -> check_safety_from_place p loc) (p::l)
      | _ -> ()
    )
    mir.minstrs;

  (* We check that we never perform any operation which would conflict with an existing
    borrows. *)
  let bor_active_at = Active_borrows.go prog lft_sets mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      (* The list of bor_info for borrows active at this instruction. *)
      let active_borrows_info : bor_info list =
        List.map (get_bor_info prog mir) (BSet.to_list (bor_active_at lbl))
      in

      (* Does there exist a borrow of a place pl', which is active at program point [lbl],
        such that a *write* to [pl] conflicts with this borrow?

         If [pl] is a subplace of pl', then writing to [pl] is always conflicting, because
        it is aliasing with the borrow of pl'.

         If pl' is a subplace of [pl], the situation is more complex:
           - if pl' involves as many dereferences as [pl] (e.g., writing to [x.f1] while
            [x.f1.f2] is borrowed), then the write to [pl] will overwrite pl', hence this is
            conflicting.
           - BUT, if pl' involves more dereferences than [pl] (e.g., writing to [x.f1] while
            [*x.f1.f2] is borrowed), then writing to [pl] will *not* modify values accessible
            from pl'. Hence, subtlely, this is not a conflict. *)
      let conflicting_borrow_no_deref pl =
        List.exists
          (fun bi -> is_subplace pl bi.bplace || is_subplace_no_deref bi.bplace pl)
          active_borrows_info
      in

      (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) ->
          if conflicting_borrow_no_deref pl then
            Error.error loc "Assigning a borrowed place."
      | Ideinit (l, _) ->
          if conflicting_borrow_no_deref (PlLocal l) then
            Error.error loc
              "A local declared here leaves its scope while still being borrowed."
      | Ireturn ->
          Hashtbl.iter
            (fun l _ ->
              match l with
              | Lparam p ->
                  if conflicting_borrow_no_deref (PlLocal l) then
                    Error.error loc
                      "When returning from this function, parameter `%s` is still \
                       borrowed."
                      p
              | _ -> ())
            mir.mlocals
      | _ -> ());

      (* Variant of [conflicting_borrow_no_deref]: does there exist a borrow of a place pl',
        which is active at program point [lbl], such that a *read* to [pl] conflicts with this
        borrow? In addition, if parameter [write] is true, we consider an operation which is
        both a read and a write. *)
      let conflicting_borrow write pl =
        List.exists
          (fun bi ->
            (bi.bmut = Mut || write)
            && (is_subplace pl bi.bplace || is_subplace bi.bplace pl))
          active_borrows_info
      in

      (* Check a "use" (copy or move) of place [pl]. *)
      let check_use pl =
        let consumes = not (typ_is_copy prog (typ_of_place prog mir pl)) in
        if conflicting_borrow consumes pl then
          Error.error loc "A borrow conflicts with the use of this place.";
        if consumes && contains_deref_borrow pl then
          Error.error loc "Moving a value out of a borrow."
      in

      match instr with
      | Iassign (_, RVunop (_, pl), _) -> check_use pl
      | Iassign (_, RVborrow (mut, pl), _) ->
          if conflicting_borrow (mut = Mut) pl then
            Error.error loc "There is a borrow conflicting this borrow."
      | Iassign (_, RVbinop(_, p1, p2), _) ->
        check_use p1;
        check_use p2
      | Iassign (_, RVplace p, _) -> check_use p
      | Iassign (_, RVmake (_, plist), _) ->
        List.iter (check_use) plist
      | Iif (p, _, _) -> check_use p
      | Icall(_, plist, p, _) ->
        List.iter (check_use) (p::plist)
      | _ -> () (* 5 TODO: complete the other cases*) (*ptet qqc à faire avec Ideinit*)
    )
    mir.minstrs
