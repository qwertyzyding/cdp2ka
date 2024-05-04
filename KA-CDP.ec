(* KA-CDP.ec *)

(* Weak security for key agreement protocol built out of CDP for hamming distance *)

prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.

require import AllCore Distr DBool List Mu_mem.
require import StdBigop. import Bigreal BRA.
require import StdOrder. import RealOrder.
require import StdRing. import RField.
require BitWord FelTactic.
require import HammingDistance.
require CompDiffPriv KeyAgreement.

op input_len : {int | 0 < input_len} as gt0_input_len.

clone BitWord as Input with
    op n <- input_len
proof gt0_n by apply gt0_input_len.



(* CDP for hamming distance *)

clone import CompDiffPriv as CDP with
