let rec to_string e =
  match e with
  | Expr.Application (a, b) -> "(" ^ to_string a ^ " " ^ to_string b ^ ")"
  | Expr.Abstraction (a, b) -> "(\\" ^ to_string a ^ ". " ^ to_string b ^ ")"
  | Expr.Value a -> a;;

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
        print_endline (to_string result);;
