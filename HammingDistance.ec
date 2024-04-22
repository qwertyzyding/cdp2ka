(* HammingDistance.ec *)

(* lemmas for Hamming distance *)

prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.

require import AllCore Distr DBool Mu_mem Int Xint List BitEncoding StdOrder StdBigop.
require FinType Word. import Bigint Bigint.BIA.
require BitWord FelTactic.

op vec_len : {int | 0 < vec_len} as gt0_vec_len.

clone BitWord as Vec with
    op n <- vec_len
proof gt0_n by apply gt0_vec_len.

type vec = Vec.word.

op zerov : vec = Vec.zerow.

op onev : vec = Vec.onew.

op unit (i : int) : vec = (0 <= i < vec_len) ? Vec.offun (fun j => i = j) : zerov.

op dvec : vec distr = Vec.DWord.dunifin.

lemma dvec_full : is_full dvec.
proof.
apply Vec.DWord.dunifin_fu.
qed.

lemma dvec_ll : is_lossless dvec.
proof.
apply Vec.DWord.dunifin_ll.
qed.

lemma dvec_uni : is_uniform dvec.
proof.
apply Vec.DWord.dunifin_uni.
qed.

op "_.[_]" : vec -> int -> bool = Vec."_.[_]".

op (+^) : vec -> vec -> vec = Vec.(+^).

op andv : vec -> vec -> vec = Vec.andw.

op invv : vec -> vec = Vec.invw.

op norm0(x : vec) : int = BIA.bigi predT (fun i => b2i (x.[i])) 0 vec_len.

op hd(x, y : vec) : int = norm0(x +^ y).

lemma andvDl : left_distributive andv (+^).
proof.
apply Vec.andwDl.
qed.

lemma zerovE i : zerov.[i] = false.
proof.
apply Vec.zerowE.
qed.

lemma zerov_norm0 : norm0(zerov) = 0.
proof.
admit.
qed.

lemma subset_norm0 (x r : vec) : norm0 (andv x r) + norm0 (andv x (invv r)) = norm0 x.
proof.
admit.
qed.

lemma subset_hd (x, y, r : vec) : hd (andv x r) (andv y r) + hd (andv x (invv r)) (andv y (invv r)) = hd x y.
proof.
by rewrite /hd -andvDl -andvDl subset_norm0.
qed.

lemma subset2id (x : vec, i : int) : 0 <= i < vec_len => b2i x.[i] = norm0 ( andv x (unit i)).
proof.
admit.
qed.
