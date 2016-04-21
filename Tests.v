
Require Import Deci Hexa BinPosDef BinNatDef BinIntDef.

Import DecNat.

Compute nat2dec 1.
Compute nat2dec 123.
Compute nat2dec (dec2nat (D1::D2::D3::D4::D5::D6::D7::D8::D9::nil)).
Time Compute nat2dec (dec2nat (D1::D2::D3::D4::D5::D6::D7::D8::D9::nil)).
(** 10s for 10^8 :-) *)

Import DecN.

Compute dec2n (D1::D0::nil).
Compute n2dec 1.
Compute n2dec 123456789123456789123456789123456789.
Compute n2dec (N.pow 2 10000).
Time Compute n2dec (N.pow 2 10000).
(** 4s for 2^10000 :-) *)

Import DecPos.

Compute dec2pos (D1::D0::nil).
Compute pos2dec 1.
Compute pos2dec 123456789123456789123456789123456789.
Compute pos2dec (Pos.pow 2 10000).
Time Compute pos2dec (Pos.pow 2 10000).
(** 4s for 2^10000 :-) *)

Import DecZ.

Compute dec2z (D1::D0::nil).
Compute z2dec 1.
Compute z2dec 123456789123456789123456789123456789.
Compute z2dec (Z.pow 2 10000).
Time Compute z2dec (Z.pow 2 10000).
(** 4s for 2^10000 :-) *)

Import HexNat.

Compute nat2hex 1.
Compute nat2hex 123.
Compute nat2hex (hex2nat (H1::H2::H3::H4::H5::H6::H7::HF::nil)).
Time Compute nat2hex (hex2nat (H1::H2::H3::H4::H5::H6::H7::HF::nil)).
(** 33s for 16^7 :-) *)

Import HexN.

Compute hex2n (H1::H0::nil).
Compute n2hex 1.
Compute n2hex 123456789123456789123456789123456789.
Compute n2hex (N.pow 2 30000).
Time Compute n2hex (N.pow 2 30000).
(** 0s for 2^30000 :-) *)

Import HexPos.

Compute hex2pos (H1::H0::nil).
Compute pos2hex 1.
Compute pos2hex 123456789123456789123456789123456789.
Compute pos2hex (Pos.pow 2 30000).
Time Compute pos2hex (Pos.pow 2 30000).
(** 0s for 2^10000 :-) *)

Import HexZ.

Compute hex2z (H1::H0::nil).
Compute z2hex 1.
Compute z2hex 123456789123456789123456789123456789.
Compute z2hex (Z.pow 2 30000).
Time Compute z2hex (Z.pow 2 30000).
(** 0s for 2^10000 :-) *)
