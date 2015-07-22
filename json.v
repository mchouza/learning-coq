Require Import Ascii.
Require Import List.
Require Import String.
Require Import ZArith.

Open Scope Z_scope.

(* Unicode codepoint definition *)
Definition unicode_codepoint := { cp : Z | 0 <= cp <= 1114111 }.

(* Unicode string definition *)
Definition unicode_string := list unicode_codepoint.

(* Gets ASCII string to print - useful for debugging *)
Fixpoint unicode_to_ascii (s:unicode_string) : string :=
  match s with
  | nil => ""%string
  | cp :: t => 
      match cp with
      | exist cpv cp_bound =>
          match Z_le_dec cpv 127 with
          | left _ =>
              match cpv with
              | Zpos p => String (ascii_of_pos p) (unicode_to_ascii t)
              | _ => ("?" ++ (unicode_to_ascii t))%string
              end
          | right _ => ("?" ++ (unicode_to_ascii t))%string
          end
      end
  end.

(* Definitions of JSON structural characters *)
Definition LEFT_SQUARE_BRACKET : unicode_codepoint.
  exists 91; omega. (* 0x5b *)
Defined.
Definition RIGHT_SQUARE_BRACKET : unicode_codepoint.
  exists 93; omega. (* 0x5d *)
Defined.
Definition COMMA : unicode_codepoint.
  exists 44; omega. (* 0x2c *)
Defined.

(* Definition of JSON whitespace characters *)
Definition SPACE : unicode_codepoint.
  exists 32; omega. (* 0x20 *)
Defined.
Definition HORIZONTAL_TAB : unicode_codepoint.
  exists 9; omega. (* 0x09 *)
Defined.
Definition LINE_FEED : unicode_codepoint.
  exists 10; omega. (* 0x0a *)
Defined.
Definition CARRIAGE_RETURN : unicode_codepoint.
  exists 13; omega. (* 0x0d *)
Defined.

(* JSON value definition *)
Inductive json_value : Set :=
  | JSONValueFromArray : json_array -> json_value
with json_array : Set :=
  | JSONEmptyArray : json_array
  | JSONAppendToArray : json_value -> json_array -> json_array.

(* JSON token definition *)
Inductive json_token : Set :=
  | JSONArrayStartToken : json_token
  | JSONArrayEndToken : json_token
  | JSONSeparatorToken : json_token.

(* JSON serialization to tokens function *)
Fixpoint serialize_json_value_to_tokens (jv:json_value) : list json_token :=
  match jv with
  | JSONValueFromArray ja => serialize_json_array_to_tokens ja
  end
with serialize_json_array_to_tokens (ja:json_array) : list json_token :=
  match ja with
  | JSONEmptyArray => JSONArrayStartToken :: JSONArrayEndToken :: nil
  | JSONAppendToArray jhv jat =>
      (JSONArrayStartToken :: nil) ++
      (serialize_json_value_to_tokens jhv) ++
      (_aux_sjatt jat)
  end
with _aux_sjatt (ja:json_array) : list json_token :=
  match ja with
  | JSONEmptyArray => JSONArrayEndToken :: nil
  | JSONAppendToArray jhv jat => 
      (JSONSeparatorToken :: nil) ++
      (serialize_json_value_to_tokens jhv) ++
      (_aux_sjatt jat)
  end.

(* JSON token canonical serialization function *)
Definition serialize_json_token (jt:json_token) : unicode_string :=
  match jt with
  | JSONArrayStartToken => LEFT_SQUARE_BRACKET :: nil
  | JSONArrayEndToken => RIGHT_SQUARE_BRACKET :: nil
  | JSONSeparatorToken => COMMA :: nil
  end.

(* JSON value canonical serialization function *)
Definition serialize_json_value (jv:json_value) : unicode_string :=
  flat_map serialize_json_token (serialize_json_value_to_tokens jv).

Compute unicode_to_ascii (serialize_json_value (JSONValueFromArray (JSONAppendToArray (JSONValueFromArray JSONEmptyArray) (JSONAppendToArray (JSONValueFromArray JSONEmptyArray) JSONEmptyArray)))).