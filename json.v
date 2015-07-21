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

(* JSON canonical serialization function *)
Fixpoint serialize_json_value (jv:json_value) : unicode_string :=
  match jv with
  | JSONValueFromArray ja => serialize_json_array ja
  end
with serialize_json_array (ja:json_array) : unicode_string :=
  match ja with
  | JSONEmptyArray => LEFT_SQUARE_BRACKET :: RIGHT_SQUARE_BRACKET :: nil
  | JSONAppendToArray jhv jat =>
      (LEFT_SQUARE_BRACKET :: nil) ++
      (serialize_json_value jhv) ++
      (_aux_serialize_json_array jat)
  end
with _aux_serialize_json_array (ja:json_array) : unicode_string :=
  match ja with
  | JSONEmptyArray => RIGHT_SQUARE_BRACKET :: nil
  | JSONAppendToArray jhv jat =>
      (COMMA :: nil) ++
      (serialize_json_value jhv) ++
      (_aux_serialize_json_array jat)
  end.

Compute unicode_to_ascii (serialize_json_value (JSONValueFromArray (JSONAppendToArray (JSONValueFromArray JSONEmptyArray) (JSONAppendToArray (JSONValueFromArray JSONEmptyArray) JSONEmptyArray)))).