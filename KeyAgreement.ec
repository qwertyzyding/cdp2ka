(* KeyAgreement.ec *)

(* (two-party) key agreement protocols *)

prover [""].

require import AllCore Distr DBool.

type randA. (* Alice's internal randomness*)

type randB. (* Bob's internal randomness*)

type transcript. (* protocol transcript *)

type key. (* Alice & Bob's agreed key *)

module type KeyAgreement = {

    proc rand_gen_A() : randA

    proc rand_gen_B() : randB
    
    proc tr_gen(ra : randA, rb : randB) : transcript

    proc key_gen_A (ra : randA, tr : transcript) : key

    proc key_gen_B (rb : randB, tr : transcript) : key
}.

module Correctness(KA : KeyAgreement) = {
    proc main() : bool = {
        var ra : randA; var rb : randB; var tr : transcript; var ka, kb : key;
        ra <@ KA.rand_gen_A();
        rb <@ KA.rand_gen_B();
        tr <@ KA.tr_gen(ra, rb);
        ka <@ KA.key_gen_A(ra, tr);
        kb <@ KA.key_gen_B(rb, tr);
        return ka = kb;
    }
}.

module type Adversary = {
    proc guess(tr : transcript) : key
}.

module Security(KA : KeyAgreement, Adv: Adversary) = {
    proc main() : bool = {
        var ra : randA; var rb : randB; var tr : transcript; var ka, k : key;
        ra <@ KA.rand_gen_A();
        rb <@ KA.rand_gen_B();
        tr <@ KA.tr_gen(ra, rb);
        ka <@ KA.key_gen_A(ra, tr);
        k <@ Adv.guess(tr);
        return k = ka;
    }
}.
