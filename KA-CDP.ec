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

type transc_CDP = CDPTransc.word.


(* functionality of CDP *)

op T_CDP : vec -> randA_CDP -> vec -> randB_CDP -> transc_CDP.

op outA_CDP : vec -> randA_CDP -> transc_CDP -> int.

op outB_CDP : vec -> randB_CDP -> transc_CDP -> int.

clone import CompDiffPriv as CDP with
    type input <- vec,
    op dinput <- dvec,
    type output <- int,
    type randA <- randA_CDP,
    op drandA <- drandA_CDP,
    type randB <- randB_CDP,
    op drandB <- drandB_CDP,
    type transcript <- transc_CDP,
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



(* Key Agreement protocols *)

type randA_KA = vec * vec * randA_CDP. 

type randB_KA = vec * randB_CDP.

type transc_KA = vec * vec * vec * transc_CDP.

clone import KeyAgreement as KA with
    type randA <- randA_KA,
    type randB <- randB_KA,
    type transcript <- transc_KA,
    type key <- int.


(* KA out of CDP for hd *)

module KeyAgr : KA = {
    var ra : randA_KA
    var rb : randB_KA

    proc init_A() : unit = {
        var x, r : vec;
        var ra_CDP : randA_CDP;
        x <$ dvec;
        r <$ dvec;
        ra_CDP <$ drandA_CDP;
        ra <- (x, r, ra_CDP);
    }

    proc init_B() : unit = {
        var y : vec;
        var rb_CDP : randB_CDP;
        y <$ dvec;
        rb_CDP <$ drandB_CDP;
        rb <- (y, rb_CDP);
    }
    
    proc exec() : transc_KA = {
        var x, y, r, xr, yri : vec;
        var ra_CDP : randA_CDP;
        var rb_CDP : randB_CDP;
        var tr_CDP : transc_CDP;
        (x, r, ra_CDP) <- ra;
        (y, rb_CDP) <- rb;
        tr_CDP <- T_CDP x ra_CDP y rb_CDP;
        xr <- andv x r;
        yri <- andv y (invv r);
        return (xr, r, yri, tr_CDP);
    }

    proc key_gen_A (tr : transc_KA) : int = {
        var x, r, yri : vec;
        var ra_CDP : randA_CDP;
        var tr_CDP : transc_CDP;
        var out : int;
        (x, r, ra_CDP) <- ra;
        yri <- tr.`3;
        tr_CDP <- tr.`4;
        out <- outA_CDP x ra_CDP tr_CDP;
        return out - (hd (andv x (invv r)) yri);
    }

    proc key_gen_B (tr : transc_KA) : int = {
        var y, r, xr: vec;
        y <- rb.`1;
        xr <- tr.`1;
        r <- tr.`2;
        return hd xr (andv y r);
    }
}.


(* proving correctness of KA -- correctness of CDP implies correctness of KA *)

lemma correctness &m : Pr [Cor_KA(KeyAgr).main() @ &m : res] = Pr[Cor_CDP(CompDiffPriv).main() @ &m : res].
proof.
    byequiv => //; proc.
    inline{1}*.
    inline{2}*.
    auto.
    swap{2} 5 -2.
    swap{1} 4 1.
    swap{1} 2 -1.
    swap{1} 3 1.
    auto => /=.
    move => r _ xL _ yL _ raL _ rbL _.
    smt(subset_hd).
qed.


(* proving security of KA *)

(* Adv for CDP out of Adv for KeyAgr *)

module Adv2CDPA (Adv : ADV_KA) : ADV_CDP = {
    var x, y, r : vec
    var i : int

    proc choose() : vec * vec * vec = {
        x <$ dvec;
        y <$ dvec;
        r <$ dvec;
        i <- 0;
        while (i < vec_len && !r.[i]) i <- i + 1;
        return (x, y +^ (unitv i), y);
    }

    proc guess(tr : transc_CDP) : bool = {
        var out, outi : int;
        var tr_KA : transc_KA;
        var ri : vec;
        tr_KA <- (andv x r, r, andv y (invv r), tr);
        ri <- r +^ (unitv i);
        out <@ Adv.guess(tr_KA);
        outi <- hd (andv x ri) (andv y ri);
        return out = outi;
    }
}.

section.

declare module Adv <: ADV_KA{-Adv2CDPA, -CompDiffPriv, -KeyAgr}.

declare axiom Adv_guess_ll : islossless Adv.guess.

(* Game 0: KA game *)
(* Game 1: remove the case r = 0 *)

module G1(KA : KA, Adv : ADV_KA) = {
    proc main() : bool = {
        var tr : transc_KA; var ka, k : int;
        KA.init_A();
        KA.init_B();
        tr <@ KA.exec();
        ka <@ KA.key_gen_A(tr);
        k <@ Adv.guess(tr);
        return k = ka /\ tr.`2 <> zerov;
    }
}.

local lemma KA_G1 &m : Pr[Sec(KeyAgr, Adv).main() @ &m : res] <= Pr[G1(KeyAgr, Adv).main() @ &m : res] + 1%r / (2 ^ vec_len)%r.
proof.
admit.
qed.

(* Game 2: CDP game *)

local lemma G1_CDP &m : Pr[G1(KeyAgr, Adv).main() @ &m : res] <= Pr[RelaxedPriv(Adv2CDPA(Adv)).main() @ &m : res].
proof.
admit.
qed.

(* summing up the security loss *)

lemma security &m : Pr[Sec(KeyAgr, Adv).main() @ &m : res] <= Pr[RelaxedPriv(Adv2CDPA(Adv)).main() @ &m : res] + 1%r / (2 ^ vec_len)%r.
proof.
smt(KA_G1 G1_CDP).
qed.
end section.
