(* Internal module, not exposed *)

type input = {
  file : string;
  offset_to_location : int -> Loc.point;
  warnings : Warning.t list ref;
  lexbuf : Lexing.lexbuf;
  string_buffer : Buffer.t;
}

val token : input -> Lexing.lexbuf -> Token.t Loc.with_location
