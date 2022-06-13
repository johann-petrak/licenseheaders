From Parsec Require Import
     Number.

Goal parse (liftA2 pair parseDec parseHex) "23Fa0$" = inr (23, 4000, "$")%N.
Proof. reflexivity. Qed.

Goal parse parseDec "FFF" = inl (Some "Not a decimal number.").
Proof. reflexivity. Qed.

Goal parse parseHex "???" = inl (Some "Not a hexadecimal number.").
Proof. reflexivity. Qed.
