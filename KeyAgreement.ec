(* KeyAgreement.ec *)

(* (two-party) key agreement protocols *)

prover [""].

require import AllCore Distr DBool.

type randA. (* Alice's internal randomness*)

type randB. (* Bob's internal randomness*)

type transcript. (* protocol transcript *)

type key. (* Alice & Bob's agreed key *)

module type KA = {

    proc init_A() : randA

    proc init_B() : randB
    
    proc exec() : transcript

    proc key_gen_A (tr : transcript) : key

    proc key_gen_B (tr : transcript) : key
}.

module Cor(KA : KA) = {
    proc main() : bool = {
        var tr : transcript; var ka, kb : key;
        KA.init_A();
        KA.init_B();
        tr <@ KA.exec();
        ka <@ KA.key_gen_A(tr);
        kb <@ KA.key_gen_B(tr);
        return ka = kb;
    }
}.

module type ADV = {
    proc guess(tr : transcript) : key
}.

module Sec(KA : KA, Adv: ADV) = {
    proc main() : bool = {
        var tr : transcript; var ka, k : key;
        KA.init_A();
        KA.init_B();
        tr <@ KA.exec();
        ka <@ KA.key_gen_A(tr);
        k <@ Adv.guess(tr);
        return k = ka;
    }
}.
