module MM = Map.Make(String);;

let rec to_string e =
  match e with
  | Expr.Application (a, b) -> "(" ^ to_string a ^ " " ^ to_string b ^ ")"
  | Expr.Abstraction (a, b) -> "(\\" ^ to_string a ^ ". " ^ to_string b ^ ")"
  | Expr.Value a -> a;;

let rec to_string_type e =
  match e with
  | Expr.Application (a, b) -> "Application(" ^ to_string_type a ^ ", " ^ to_string_type b ^ ")"
  | Expr.Abstraction (a, b) -> "Abstraction(" ^ to_string_type a ^ ", " ^ to_string_type b ^ ")"
  | Expr.Value a -> "Value(" ^ a ^ ")";;

let rec de_bruijn_to_string e =
  match e with
  | DeBruijn.Application (a, b) -> "{" ^ de_bruijn_to_string a ^ " " ^ de_bruijn_to_string b ^ "}"
  | DeBruijn.Abstraction a -> "(\\." ^ de_bruijn_to_string a ^ ")"
  | DeBruijn.Value a -> string_of_int a
  | DeBruijn.Free_Value a -> a;;

let defined = ref MM.empty;;

let get_element a =
  "qqa" ^ (string_of_int a)

let rec from_de_bruijn_to_expr e level =
  match e with
  | DeBruijn.Value v ->
    Expr.Value (get_element (level - v))
  | DeBruijn.Free_Value v ->
    Expr.Value v
  | DeBruijn.Application (a, b) -> Expr.Application (from_de_bruijn_to_expr a level, from_de_bruijn_to_expr b level)
  | DeBruijn.Abstraction a ->
      let q = Expr.Value (get_element (level + 1)) in
      let level = level + 1 in
      Expr.Abstraction (q, from_de_bruijn_to_expr a level);;


let rec to_de_bruijn expression level =
  match expression with
  | Expr.Application (f, s) -> DeBruijn.Application (to_de_bruijn f level, to_de_bruijn s level)
  | Expr.Abstraction (f, s) ->
  begin
    try
    begin
      match f with
        Expr.Value v ->
          if (MM.mem v !defined) then
            let level = level + 1 in
            let help = MM.find v !defined in
            let tmp = defined := MM.add v level !defined in
            let ans = DeBruijn.Abstraction (to_de_bruijn s level) in
            let tmp = defined := MM.add v help !defined in
            ans
          else
            let level = level + 1 in
            let tmp = defined := MM.add v level !defined in
            let ans = DeBruijn.Abstraction (to_de_bruijn s level) in
            let tmp = defined := MM.remove v !defined in
            ans
    end
    with e -> DeBruijn.Value (1)
    end
  | Expr.Value v ->
    if (MM.mem v !defined) then
      let help = MM.find v !defined in
      let lev = help in
      DeBruijn.Value (level - lev)
    else
      DeBruijn.Free_Value (v);;

let rec update_level e level up =
  match e with
  | DeBruijn.Free_Value v -> e
  | DeBruijn.Value v ->
    if (level <= v) then
      DeBruijn.Value (v + up)
    else
      e
  | DeBruijn.Application (a, b) -> DeBruijn.Application (update_level a level up, update_level b level up)
  | DeBruijn.Abstraction a -> let level = level + 1 in DeBruijn.Abstraction (update_level a level up);;

let rec reduce e s level =
  match e with
  | DeBruijn.Value v ->
    if (v == level) then
      update_level s 0 level
    else if (v > level) then
      DeBruijn.Value (v - 1)
    else
      e
  | DeBruijn.Free_Value v -> e
  | DeBruijn.Application (a, b) -> DeBruijn.Application (reduce a s level, reduce b s level)
  | DeBruijn.Abstraction a -> let level = level + 1 in DeBruijn.Abstraction (reduce a s level);;

let changed = ref false;;
let rec redex e level =
  match e with
  | DeBruijn.Value v ->
    e
  | DeBruijn.Free_Value v ->
    e
  | DeBruijn.Application (a, b) ->
    begin
      match a with
      | DeBruijn.Value v ->
        (* let q = print_endline (" (b) " ^ (de_bruijn_to_string b) ^ "  (a) " ^ (de_bruijn_to_string a) ^ " (e) " ^ (de_bruijn_to_string e)) in *)
        DeBruijn.Application (a, redex b level)
      | DeBruijn.Free_Value v ->
        (* let q = print_endline (" (b) " ^ (de_bruijn_to_string b) ^ "  (a) " ^ (de_bruijn_to_string a) ^ " (e) " ^ (de_bruijn_to_string e)) in *)
        DeBruijn.Application (a, redex b level)
      | DeBruijn.Abstraction v ->
        let tmp = changed := true in
        (* let q = print_endline ((de_bruijn_to_string v) ^ "===" ^ (de_bruijn_to_string b) ^ "  (a) " ^ (de_bruijn_to_string a) ^ " (e) " ^ (de_bruijn_to_string e) ^ "\n\n") in *)
        reduce v b 0
      | DeBruijn.Application (f, s) ->
        (* let q = print_endline (" (b) " ^ (de_bruijn_to_string b) ^ "  (a) " ^ (de_bruijn_to_string a) ^ " (e) " ^ (de_bruijn_to_string e)) in *)
        let frst = redex a level in
        if not (!changed) then
          DeBruijn.Application (frst, redex b level)
          else
          DeBruijn.Application (frst, b)
    end
  | DeBruijn.Abstraction a ->
    let level = level + 1 in
    (* let q = print_endline ("  (a) " ^ (de_bruijn_to_string a) ^ " (e) " ^ (de_bruijn_to_string e)) in *)
    DeBruijn.Abstraction (redex a level);;


let () =
  let buffer = Buffer.create 1048576 in
  try
    while true do
      begin
        Buffer.add_string buffer (read_line ());
        Buffer.add_string buffer "\n";
      end
    done;
  with e ->
    let lexbuf = Lexing.from_string (Buffer.contents buffer) in
      let result = Parser.main Lexer.token lexbuf in
      let tmp = ref (to_de_bruijn result 0) in
      let q =
      begin
        (* let q = print_endline (de_bruijn_to_string !tmp) in *)
        let flag = ref true in
        let old = ref !tmp in
        while !flag do
          tmp := redex !tmp 0;
          if (!old = !tmp) then
            flag := false;
          changed := false;
          (* print_endline (de_bruijn_to_string !tmp); *)
          old := !tmp;
        done
      end in
      print_endline (to_string (from_de_bruijn_to_expr !tmp 0));;
