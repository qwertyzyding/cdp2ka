(* HammingDistance.ec *)

(* lemmas for Hamming distance *)

prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.

require import AllCore Distr Bool DBool Mu_mem Int Xint List BitEncoding StdOrder StdBigop.
require FinType Word. import Bigint Bigint.BIA.
require BitWord FelTactic.

op vec_len : {int | 0 < vec_len} as gt0_vec_len.

clone BitWord as Vec with
    op n <- vec_len
proof gt0_n by apply gt0_vec_len.

type vec = Vec.word.

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

op zerov : vec = Vec.zerow.

lemma zerovE i : zerov.[i] = false.
proof.
apply Vec.zerowE.
qed.

op onev : vec = Vec.onew.

lemma onevE i : onev.[i] = (0 <= i < vec_len).
proof.
apply Vec.onewE.
qed.

op unitv (i : int) : vec = Vec.offun (fun j => 0 <= j < vec_len /\ i = j).

lemma unitvE i j : (unitv i ).[j] = (0 <= j < vec_len /\ i = j).
proof.
rewrite /unitv.
smt(Vec.offunifE).
qed.

op (+^) : vec -> vec -> vec = Vec.(+^).

lemma xorvE x y i : (x +^ y).[i] = x.[i] ^^ y.[i].
proof. apply Vec.xorwE. qed.

op andv : vec -> vec -> vec = Vec.andw.

lemma andvDl : left_distributive andv (+^).
proof.
apply Vec.andwDl.
qed.

op invv : vec -> vec = Vec.invw.

op norm0(x : vec) : int = BIA.bigi predT (fun i => b2i (x.[i])) 0 vec_len.

lemma norm0E x : norm0 x = BIA.bigi predT (fun i => b2i (x.[i])) 0 vec_len.
proof. by rewrite /norm0. qed.

lemma zerov_norm0 : norm0(zerov) = 0.
proof.
rewrite /norm0 big1 // => i /=.
by rewrite zerovE /b2i.
qed.


lemma onev_norm0 : norm0(onev) = vec_len.
proof.
rewrite /norm0.
admit.
(* sumr_const *)
qed.

lemma subset_norm0 (x r : vec) : norm0 (andv x r) + norm0 (andv x (invv r)) = norm0 x.
proof.
rewrite 3!norm0E sumrD.
apply eq_bigr => i _ /=.

qed.

op hd(x, y : vec) : int = norm0(x +^ y).

lemma hdE x y : hd x y = bigi predT (fun i => b2i(x.[i] ^^ y.[i])) 0 vec_len.
proof.
rewrite /hd.
rewrite /norm0.
apply eq_bigr => i _ /=.
by rewrite xorvE.
qed.

lemma hdC : commutative hd.
proof.
move => x y; rewrite 2!hdE.
apply eq_bigr => i _ /=.
by rewrite xorC.
qed.

lemma subset_hd (x, y, r : vec) : hd (andv x r) (andv y r) + hd (andv x (invv r)) (andv y (invv r)) = hd x y.
proof.
by rewrite /hd -andvDl -andvDl subset_norm0.
qed.

lemma subset2id (x : vec, i : int) : 0 <= i < vec_len => b2i x.[i] = norm0 ( andv x (unit i)).
proof.
admit.
qed.
