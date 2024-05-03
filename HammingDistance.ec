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

lemma andvE (x y : vec) i : (andv x y).[i] = (x.[i] /\ y.[i]).
proof. apply Vec.andwE. qed.

lemma andvC : commutative andv.
proof. apply Vec.andwC. qed.

lemma andvA : associative andv.
proof. apply Vec.andwA. qed.


lemma andvunit x i : andv x (unitv i) = x.[i] ? (unitv i) : zerov.
proof.
apply Vec.wordP.
move => i0 [ge_i0 le_i0].
case x.[i]; move => xi /=.
smt(andvE unitvE).
smt(andvE unitvE zerovE).
qed.

lemma andvDl : left_distributive andv (+^).
proof.
apply Vec.andwDl.
qed.

op invv : vec -> vec = Vec.invw.

lemma invvE x i : 0 <= i < vec_len => (invv x).[i] = !x.[i].
proof. apply Vec.invwE. qed.


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
have : norm0(onev) = BIA.bigi predT (fun _ => 1) 0 vec_len.
rewrite norm0E.
smt(congr_big_int onevE).
move => eq_const.
rewrite eq_const.
rewrite sumri_const //.
rewrite ltzW gt0_vec_len.
smt.
qed.

lemma norm2idx x i : 0 <= i < vec_len => b2i x.[i] = norm0 (andv x (unitv i)).
proof.
move => [ge_i le_i].
rewrite norm0E (big_cat_int (i+1)).
by rewrite ltzW ltzS.
by rewrite -ltzS ltz_add2r.
rewrite (big_cat_int i) //.
smt.
have : bigi predT (fun (i0 : int) => b2i (andv x (unitv i)).[i0]) 0 i = 0.
have : bigi predT (fun (i0 : int) => b2i (andv x (unitv i)).[i0]) 0 i =  bigi predT (fun _ => 0) 0 i.
smt(congr_big_int andvE unitvE).
rewrite sumri_const //.
smt.
move => prefix_sum.
rewrite prefix_sum add0z (big_int1 i) /= andvE unitvE ge_i le_i /=.
have : bigi predT (fun (i0 : int) => b2i (andv x (unitv i)).[i0]) (i + 1) vec_len = 0.
have : bigi predT (fun (i0 : int) => b2i (andv x (unitv i)).[i0]) (i + 1) vec_len = bigi predT (fun _ => 0) (i + 1) vec_len.
smt(congr_big_int andvE unitvE).
rewrite sumri_const //.
smt.
smt.
move => suffix_sum.
by rewrite suffix_sum.
qed.

lemma subset_norm0 (x r : vec) : norm0 (andv x r) + norm0 (andv x (invv r)) = norm0 x.
proof.
rewrite 3!norm0E sumrD.
smt(eq_bigr andvE invvE).
qed.

op hd(x, y : vec) : int = norm0(x +^ y).

lemma hdEnorm x y : hd x y = norm0(x +^ y).
proof. by rewrite /hd. qed.

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

lemma hd2idx (x, y, r : vec) i : 0 <= i < vec_len /\ r.[i] => b2i (x.[i] ^^ y.[i]) = hd (andv x r) (andv y r) - hd (andv x (r +^ unitv i)) (andv y (r +^ unitv i)).
proof.
move => [[ge_i le_i] r_i].
rewrite -xorvE norm2idx //.
rewrite andvDl -hdEnorm.
have : andv r (unitv i) = unitv i.
by rewrite andvunit r_i.
move => r_and_unitvi.
rewrite -{1}r_and_unitvi -{2}r_and_unitvi 2!andvA.
have : r +^ unitv i = andv r (invv (unitv i)).
apply Vec.wordP => i0 [ge_i0 le_i0].
smt(unitvE andvE xorvE invvE).
move => r_xor_unitvi.
rewrite r_xor_unitvi 2!andvA.
smt(subset_hd).
qed.
