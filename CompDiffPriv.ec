(* CompDiffPriv.ec *)

(* Two-party protocols for Hamming distance/inner product with computational differential privacy*)

prover [""].

require import AllCore Distr DBool.

type input.
op dinput : input distr.
axiom dinput_fu : is_full dinput.
axiom dinput_uni : is_uniform dinput.
axiom dinput_ll : is_lossless dinput.

type output.

op F : input -> input -> output. (* functionality to compute *)

op adj: input -> input -> bool. (* adjacent inputs *)

type randA.
op drandA : randA distr.
axiom drandA_fu : is_full drandA.
axiom drandA_uni : is_uniform drandA.
axiom drandA_ll : is_lossless drandA.

type randB.
op drandB : randB distr.
axiom drandB_fu : is_full drandB.
axiom drandB_uni : is_uniform drandB.
axiom drandB_ll : is_lossless drandB.

type transcript.

op T : input -> randA -> input -> randB -> transcript.

op outA : input -> randA -> transcript -> output.

op outB : input -> randB -> transcript -> output.

(* module type of CDP protocols *)

module type CDP = {
    proc init_A (x : input) : unit

    proc init_B (y : input) : unit

    proc exec () : transcript

    proc output_A (tr : transcript) : output

    proc output_B (tr : transcript) : output
}.

module Cor_CDP (CDP : CDP) = {
    proc main() : bool = {
        var x, y : input; var tr : transcript; var outA: output;
        x <$ dinput;
        y <$ dinput;
        CDP.init_A(x);
        CDP.init_B(y);
        tr <@ CDP.exec();
        outA <@ CDP.output_A(tr);
        return outA = F x y;
    }
}.

(* standard CDP protocol constructed from T, outA, outB *)

module CompDiffPriv : CDP = {
    var inpa, inpb : input
    var ra : randA
    var rb : randB
    
    proc init_A (x : input) : unit = {
        inpa <- x;
        ra <$ drandA;
    }

    proc init_B (y : input) : unit = {
        inpb <- y;
        rb <$ drandB;
    }

    proc exec () : transcript = {
        return T inpa ra inpb rb;
    }

    proc output_A (tr : transcript) : output = {
        return outA inpa ra tr;
    }

    proc output_B (tr : transcript) : output = {
        return outB inpb rb tr;
    }
}.

(* module type of CDP adversaries *)

module type ADV = {
    proc choose() : input * input * input (* Adversary chooses x and adjacent y_1, y_2 *)
    proc guess(tr : transcript) : bool
}.

module RelaxedPriv(Adv: ADV) = {
    module CDP = CompDiffPriv

    proc main() : bool = {
        var b, b' : bool;
        var x, y0, y1 : input; var tr : transcript;
        (x, y0, y1) <@ Adv.choose();
        CDP.init_A(x);
        b <$ {0,1};
        CDP.init_B(b? y1 : y0);
        tr <@ CDP.exec();
        b' <@ Adv.guess(tr);
        return (adj y0 y1) /\ b = b';
    }
}.
