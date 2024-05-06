(* KeyAgreement.ec *)

(* (two-party) key agreement protocols *)

prover [""].

require import AllCore Distr DBool.

type randA. (* Alice's internal randomness*)

type randB. (* Bob's internal randomness*)

type transcript. (* protocol transcript *)

type key. (* Alice & Bob's agreed key *)

module type KA = {

    proc init_A() : unit

    proc init_B() : unit
    
    proc exec() : transcript

    proc key_gen_A (tr : transcript) : key

    proc key_gen_B (tr : transcript) : key
}.

module Cor_KA(KA : KA) = {
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

module type ADV_KA = {
    proc guess(tr : transcript) : key
}.

module Sec(KA : KA, Adv: ADV_KA) = {
    proc main() : bool = {
        var tr : transcript; var kb, k : key;
        KA.init_A();
        KA.init_B();
        tr <@ KA.exec();
        kb <@ KA.key_gen_B(tr);
        k <@ Adv.guess(tr);
        return k = kb; (* can also be define w.l.o.g. as k=ka or k=ka=kb *)
    }
}.
