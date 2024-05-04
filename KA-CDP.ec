(* KA-CDP.ec *)

(* Weak security for key agreement protocol built out of CDP for hamming distance *)

prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.

require import AllCore Distr DBool List Mu_mem.
require import StdBigop. import Bigreal BRA.
require import StdOrder. import RealOrder.
require import StdRing. import RField.
require BitWord FelTactic.
require import BitVec.
require CompDiffPriv KeyAgreement.

op input_len : {int | 0 < input_len} as gt0_input_len.


(* CDP for hamming distance *)

(* Alice's internal randomness *)

op CDP_randA_len : {int | 0 < CDP_randA_len} as gt0_CDP_randA_len.

clone BitWord as CDPRandA with 
    op n <- CDP_randA_len
proof gt0_n by apply gt0_CDP_randA_len.

type randA_CDP = CDPRandA.word.

op drandA_CDP : randA_CDP distr = CDPRandA.DWord.dunifin.

lemma drandA_CDP_fu : is_full drandA_CDP.
proof. apply CDPRandA.DWord.dunifin_fu. qed.

lemma drandA_CDP_uni : is_uniform drandA_CDP.
proof. apply CDPRandA.DWord.dunifin_uni. qed.

lemma drandA_CDP_ll : is_lossless drandA_CDP.
proof. apply CDPRandA.DWord.dunifin_ll. qed.


(* Bob's internal randomness *)

op CDP_randB_len : {int | 0 < CDP_randB_len} as gt0_CDP_randB_len.

clone BitWord as CDPRandB with 
    op n <- CDP_randB_len
proof gt0_n by apply gt0_CDP_randB_len.

type randB_CDP = CDPRandB.word.

op drandB_CDP : randB_CDP distr = CDPRandB.DWord.dunifin.

lemma drandB_CDP_fu : is_full drandB_CDP.
proof. apply CDPRandB.DWord.dunifin_fu. qed.

lemma drandB_CDP_uni : is_uniform drandB_CDP.
proof. apply CDPRandB.DWord.dunifin_uni. qed.

lemma drandB_CDP_ll : is_lossless drandB_CDP.
proof. apply CDPRandB.DWord.dunifin_ll. qed.


(* transcript *)

op CDP_transc_len : {int | 0 < CDP_transc_len} as gt0_CDP_transc_len.

clone BitWord as CDPTransc with 
    op n <- CDP_transc_len
proof gt0_n by apply gt0_CDP_transc_len.

type transcript = CDPTransc.word.


(* functionality of CDP *)

op T_CDP : vec -> randA_CDP -> vec -> randB_CDP -> transcript.

op outA_CDP : vec -> randA_CDP -> transcript -> int.

op outB_CDP : vec -> randB_CDP -> transcript -> int.

clone import CompDiffPriv as CDP with
    type input <- vec,
    op dinput <- dvec,
    type output <- int,
    type randA <- randA_CDP,
    op drandA <- drandA_CDP,
    type randB <- randB_CDP,
    op drandB <- drandB_CDP,
    type transcript <- transcript,
    op F <- hd,
    op adj <- adj,
    op T <- T_CDP,
    op outA <- outA_CDP,
    op outB <- outB_CDP
proof *.
realize dinput_fu. apply dvec_full. qed.
realize dinput_uni. apply dvec_uni. qed.
realize dinput_ll. apply dvec_ll. qed.
realize drandA_fu. apply drandA_CDP_fu. qed.
realize drandA_uni. apply drandA_CDP_uni. qed.
realize drandA_ll. apply drandA_CDP_ll. qed.
realize drandB_fu. apply drandB_CDP_fu. qed.
realize drandB_uni. apply drandB_CDP_uni. qed.
realize drandB_ll. apply drandB_CDP_ll. qed.

