(* CompDiffPriv.ec *)

(* Two-party protocols for Hamming distance/inner product with computational differential privacy*)

prover [""].

require import AllCore Distr DBool.

type input.

op dinput : input distr.

axiom dinput_fu : is_full dinput.
axiom dinput_uni : is_uniform dinput.
axiom dinput_ll : is_lossless dinput.

op prod : input -> input -> int. (* inner product *)

op adj: input -> input -> bool. (* adjacent inputs*)

(* TODO: define vectors over \pm 1 *)

type stateA. 

type stateB.

type transcript.

module type CompDiffPriv = {

    proc gen_A(x : input) : stateA

    proc gen_B(y : input) : stateB
    
    proc tr_gen(stA : stateA, stB : stateB) : transcript

    proc output_A (stA : stateA, tr : transcript) : int

    proc output_B (stB : stateB, tr : transcript) : int
}.

module Correctness(CDP : CompDiffPriv) = {
    proc main() : bool = {
        var x, y : input; var stA : stateA; var stB : stateB; var tr : transcript; var outA, outB : int;
        x <$ dinput;
        y <$ dinput;
        stA <@ CDP.gen_A(x);
        stB <@ CDP.gen_B(y);
        tr <@ CDP.tr_gen(stA, stB);
        outA <@ CDP.output_A(stA, tr);
        return outA = prod x y;
    }
}.

module type Adversary = {
    proc choose() : input * input * input (* Adversary chooses x and adjacent y_1, y_2 *)
    proc guess(tr : transcript) : bool
}.

module RelaxedPrivacy(CDP : CompDiffPriv, Adv: Adversary) = {
    proc main() : bool = {
        var b, b' : bool;
        var x, y0, y1 : input; var stA : stateA; var stB : stateB; var tr : transcript;
        (x, y0, y1) <@ Adv.choose();
        stA <@ CDP.gen_A(x);
        b <$ {0,1};
        stB <@ CDP.gen_B(b? y1 : y0);
        tr <@ CDP.tr_gen(stA, stB);
        b' <@ Adv.guess(tr);
        return (adj y0 y1) /\ b = b';
    }
}.
