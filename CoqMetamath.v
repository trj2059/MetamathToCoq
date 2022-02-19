(* 
Copyright 2022 Anthony Johnson

Permission is hereby granted, free of charge, to any person obtaining a copy 
of this software and associated documentation files (the "Software"), to deal 
in the Software without restriction, including without limitation the rights 
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell 
copies of the Software, and to permit persons to whom the Software is furnished 
to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in 
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, 
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES 
OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR 
OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR 
THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)

(*
  This file contains code that proves various theorems from the
  Metamath site (http://us.metamath.org/) in the Coq Proof Assistant 
  (https://coq.inria.fr/)
*)

(* http://us.metamath.org/ileuni/mpd.html *)

Theorem mpd : forall P Q R: Prop, ((P -> Q) /\ (P -> (Q -> R))) -> (P -> R).
Proof.
    intros P.
    intros Q.
    intros R.
    intros h1.
    destruct h1.
    intros h2.
    apply H0.
    exact h2.
    apply H.
    exact h2.
Qed.

Print mpd.

Theorem mpd2 : forall P Q R: Prop, ((P -> Q) /\ (P -> (Q -> R))) -> (P -> R).
Proof.
exact (fun (P Q R : Prop) (h1 : (P -> Q) /\ (P -> Q -> R)) => match h1 with
                                                       | conj H H0 => fun h2 : P => H0 h2 (H h2)
                                                       end).
Qed.

(* http://us.metamath.org/ileuni/mpi.html *) 
Theorem mpi : forall P Q R:Prop, (Q /\ (P -> (Q -> R))) -> (P -> R).
Proof.
  intros P.
  intros Q.
  intros R.
  intros h1.
  destruct h1.
  intros h2.
  apply H0.
  exact h2.
  exact H.
Qed.

(* http://us.metamath.org/ileuni/mpd.html *)
Theorem mpd2a : forall P Q R:Prop,(P /\ Q /\ (P -> (Q -> R))) -> R.
Proof.
  intros P.
  intros Q.
  intros R.
  intros h1.
  destruct h1.
  destruct H0.
  apply H1.
  apply H.
  apply H0.
Qed.

(* http://us.metamath.org/ileuni/3syl.html *)
Theorem threesly : forall P Q R S:Prop,((P -> Q) /\ (Q -> R) /\ (R -> S)) -> (P -> S) .
Proof.
  intros P Q R S.
  intros h1.
  intros h2.
  destruct h1.
  destruct H0.
  apply H1.
  apply H0.
  apply H.
  exact h2.   
Qed. 

(* http://us.metamath.org/ileuni/id.html *)
Theorem identity1 : forall P:Prop,P -> P.
Proof.
  intros P.
  intros h.
  exact h.
Qed.

Print identity1.

Eval cbv in (fun (P : Prop) (h : P) => h) True.

(* http://us.metamath.org/ileuni/id.html *)
Theorem identity2 : forall P:Prop,P -> P.
Proof.
  exact (fun (P : Prop) (h : P) => h).
Qed.

(* http://us.metamath.org/ileuni/idd.html *)
Theorem idd : forall P Q:Prop,P -> (Q -> Q).
Proof.
  intros P Q.
  intros H.
  intros H0.
  exact H0. 
Qed.

(* http://us.metamath.org/ileuni/a1d.html *)
Theorem ad1 : forall P Q R:Prop,(P -> Q) -> (P -> (R -> Q)).
Proof.
  intros P Q R.
  intros H.
  intros H0.
  intros H1.
  apply H.
  exact H0. 
Qed.

Print ad1.

Theorem ad1b : forall P Q R:Prop,(P -> Q) -> (P -> (R -> Q)).
Proof.
  exact (fun (P Q R : Prop) (H : P -> Q) (H0 : P) (_ : R) => H H0).
Qed.

(* http://us.metamath.org/ileuni/2a1d.html *)
Theorem TwoA1D: forall P Q R S:Prop, (P -> Q) -> (P ->(R -> (S -> Q))).
Proof.
  intros P Q R S.
  intros H.
  intros H0.
  intros H1.
  intros H2.
  apply H.
  exact H0.
Qed.

Print TwoA1D.

Theorem TwoA1Db: forall P Q R S:Prop, (P -> Q) -> (P ->(R -> (S -> Q))).
Proof.
  exact (fun (P Q R S : Prop) (H : P -> Q) (H0 : P) (_ : R) (_ : S) => H H0).
Qed.

(* http://us.metamath.org/ileuni/a1i13.html *)
Theorem a1i13: forall P Q R S:Prop, (Q -> S) -> (P -> (Q -> (R -> S))).
Proof.
  intros P Q R S.
  intros H.
  intros H0.
  intros H1.
  intros H2.
  apply H.
  exact H1.
Qed.

Print a1i13.

Theorem a1i13b: forall P Q R S:Prop, (Q -> S) -> (P -> (Q -> (R -> S))).
Proof.
  exact (fun (P Q R S : Prop) (H : Q -> S) (_ : P) (H1 : Q) (_ : R) => H H1).
Qed.


(* http://us.metamath.org/ileuni/jarr.html *)
Theorem jarr: forall P Q R:Prop,(((P -> Q) -> R) -> (Q -> R)).
Proof.
  intros P Q R.
  intros H.
  intros H0.
  apply H.
  intros H1.
  exact H0.
Qed.

Print jarr.

Theorem jarr2: forall P Q R:Prop,(((P -> Q) -> R) -> (Q -> R)).
Proof.
  exact (fun (P Q R : Prop) (H : (P -> Q) -> R) (H0 : Q) => H (fun _ : P => H0)).
Qed.

(* http://us.metamath.org/ileuni/pm2.86i.html *)
Theorem pm268i1: forall P Q R:Prop,(((P -> Q) -> (P -> R)) -> (P -> (Q -> R))).
Proof.
  intros P Q R.
  intros H0.
  intros H1.
  intros H2.
  apply H0.
  intros H3.
  exact H2.
  exact H1.
Qed.

Print pm268i1.

Theorem pm268i1b: forall P Q R:Prop,(((P -> Q) -> (P -> R)) -> (P -> (Q -> R))).
Proof.
  exact (fun (P Q R : Prop) (H0 : (P -> Q) -> P -> R) (H1 : P) (H2 : Q) =>
          H0 (fun _ : P => H2) H1).  
Qed.

(* http://us.metamath.org/ileuni/pm2.86d.html *)
(* ⊢ (𝜑 → ((𝜓 → 𝜒) → (𝜓 → 𝜃))) *)
(* ⊢ (𝜑 → (𝜓 → (𝜒 → 𝜃))) *)
Theorem pm286d: 
  forall P Q R S:Prop, ((P -> ((Q -> R) -> (Q -> S))) -> (P -> (Q -> (R -> S)))).
Proof.
  intros P Q R S.
  intros H0.
  intros H1.
  intros H2.
  intros H3.
  apply H0.
  exact H1.
  intros H4.
  exact H3.
  exact H2.
Qed.

Print pm286d.

Theorem pm286db: 
  forall P Q R S:Prop, ((P -> ((Q -> R) -> (Q -> S))) -> (P -> (Q -> (R -> S)))).
Proof.
  exact (fun (P Q R S : Prop) (H0 : P -> (Q -> R) -> Q -> S) 
          (H1 : P) (H2 : Q) (H3 : R) => H0 H1 (fun _ : Q => H3) H2).
Qed.

(* http://us.metamath.org/ileuni/pm2.86.html *)
(* ⊢ (((𝜑 → 𝜓) → (𝜑 → 𝜒)) → (𝜑 → (𝜓 → 𝜒))) *)
Theorem pm286: forall P Q R:Prop,(((P -> Q) -> (P -> R)) -> (P -> (Q -> R))).
Proof.
  intros P Q R.
  intros H0.
  intros H1.
  intros H2.
  apply H0.
  intros H3.
  apply H2.
  apply H1.
Qed.

Print pm286.

Theorem pm286b: forall P Q R:Prop,(((P -> Q) -> (P -> R)) -> (P -> (Q -> R))).
Proof.
  exact (fun (P Q R : Prop) (H0 : (P -> Q) -> P -> R) (H1 : P) (H2 : Q) =>
          H0 (fun _ : P => H2) H1).
Qed.

(* http://us.metamath.org/ileuni/loolin.html *)
(* ⊢ (((𝜑 → 𝜓) → (𝜓 → 𝜑)) → (𝜓 → 𝜑)) *)
Theorem loolin: forall P Q:Prop,(((P -> Q) -> (Q -> P)) -> (Q -> P)).
Proof.
  intros P Q.
  intros H0 H1.
  apply H0.
  intros H2.
  exact H1.
  exact H1.
Qed.

Print loolin.

Theorem loolinb: forall P Q:Prop,(((P -> Q) -> (Q -> P)) -> (Q -> P)).
Proof.
  exact (fun (P Q : Prop) (H0 : (P -> Q) -> Q -> P) (H1 : Q) =>
              H0 (fun _ : P => H1) H1).
Qed.

(* http://us.metamath.org/ileuni/loowoz.html *)
(* ⊢ (((𝜑 → 𝜓) → (𝜑 → 𝜒)) → ((𝜓 → 𝜑) → (𝜓 → 𝜒))) *)
Theorem loowoz: forall P Q R:Prop, (((P -> Q) -> (P -> R)) -> ((P -> Q) -> (P -> R))).
Proof.
  intros P Q R.
  intros H0 H1 H2.
  apply H0.
  intros H3.
  apply H1.
  exact H2.
  exact H2.
Qed.

Print loowoz.

Theorem loowozb: forall P Q R:Prop, (((P -> Q) -> (P -> R)) -> ((P -> Q) -> (P -> R))).
Proof.
  exact (fun (P Q R : Prop) (H0 : (P -> Q) -> P -> R) (H1 : P -> Q) (H2 : P) =>
          H0 (fun _ : P => H1 H2) H2).
Qed.

(* http://us.metamath.org/ileuni/ax-ia1.html *)
(* ⊢ ((𝜑 ∧ 𝜓) → 𝜑) *)
Theorem axia1: forall P Q:Prop,((P /\ Q) -> P).
Proof.
  intros P Q.
  intros H0.
  destruct H0.
  exact H.
Qed.

Print axia1.

Theorem axia1b: forall P Q:Prop,((P /\ Q) -> P).
Proof.
  exact (fun (P Q : Prop) (H0 : P /\ Q) =>
          match H0 with
          | conj x x0 => (fun (H : P) (_ : Q) => H) x x0
          end).
Qed. 







