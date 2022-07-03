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
(*
*)

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

(* http://us.metamath.org/ileuni/ax-ia3.html *)
(* ⊢ (𝜑 → (𝜓 → (𝜑 ∧ 𝜓))) *)
Theorem axia3: forall P Q:Prop,(P -> (Q -> (P /\ Q))).
Proof.
  intros P Q.
  intros H0 H1.
  split.
  exact H0.
  exact H1.
Qed.

Print axia3.

Theorem axia3_2: forall P Q:Prop,(P -> (Q -> (P /\ Q))).
Proof.
  exact (
    fun (P Q : Prop) (H0 : P) (H1 : Q) => conj H0 H1
  ).
Qed.

(* http://us.metamath.org/ileuni/simpld.html *)
(* ⊢ (𝜑 → (𝜓 ∧ 𝜒)) *)
(* ⊢ (𝜑 → 𝜓) *)
Theorem simpld: forall P Q R:Prop,(P -> (Q /\ R)) -> (P -> Q).
Proof.
  intros P Q R.
  intros H0.
  intros H1.
  destruct H0.
  exact H1.
  exact H.
Qed.

Print simpld.

Theorem simpld_2: forall P Q R:Prop,(P -> (Q /\ R)) -> (P -> Q).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P -> Q /\ R) (H1 : P) =>
      let a : Q /\ R := H0 H1 in
        match a with
        | conj x x0 => (fun (H : Q) (_ : R) => H) x x0
        end
  ).
Qed.

(* http://us.metamath.org/ileuni/ex.html *)
(* ⊢ ((𝜑 ∧ 𝜓) → 𝜒) *)
(* ⊢ (𝜑 → (𝜓 → 𝜒)) *)
Theorem ex01: forall P Q R:Prop, (((P /\ Q) -> R) -> (P -> (Q -> R))).
Proof.
  intros P Q R.
  intros H0 H1 H2.
  apply H0; split.
  exact H1.
  exact H2.
Qed.

Print ex01.

Theorem ex01_2: forall P Q R:Prop, (((P /\ Q) -> R) -> (P -> (Q -> R))).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P /\ Q -> R) (H1 : P) (H2 : Q) => H0 (conj H1 H2)
  ).
Qed.

(*http://us.metamath.org/ileuni/bi1.html*)
(* ⊢ ((𝜑 ↔ 𝜓) → (𝜑 → 𝜓)) *)
Theorem bi1: forall P Q:Prop, ((P <-> Q) -> (P -> Q)).
Proof.
  intros P Q.
  intros H0 H1.
  destruct H0.
  apply H.
  exact H1.
Qed.

Print bi1.

Theorem bi1_02: forall P Q:Prop, ((P <-> Q) -> (P -> Q)).
Proof.
  exact (
    fun (P Q : Prop) (H0 : P <-> Q) (H1 : P) =>
      match H0 with
      | conj x x0 => (fun (H : P -> Q) (_ : Q -> P) => H H1) x x0
      end
  ).
Qed.

(* http://us.metamath.org/ileuni/bi3.html *)
(* ⊢ ((𝜑 → 𝜓) → ((𝜓 → 𝜑) → (𝜑 ↔ 𝜓))) *)
Theorem bi3: forall P Q:Prop, ((P -> Q) -> ((Q -> P) -> (P <-> Q))).
Proof.
  intros P Q.
  intros H0 H1.
  split.
  intros H2.
  apply H0.
  exact H2.
  intros H3.
  apply H1.
  exact H3.
Qed.

Print bi3.

Theorem bi3_02: forall P Q:Prop, ((P -> Q) -> ((Q -> P) -> (P <-> Q))).
Proof.
  exact (
    fun (P Q : Prop) (H0 : P -> Q) (H1 : Q -> P) =>
      conj (fun H2 : P => H0 H2) (fun H3 : Q => H1 H3)
  ).
Qed.

(* http://us.metamath.org/ileuni/impbidd.html *)
(* ⊢ (𝜑 → (𝜓 → (𝜒 → 𝜃))) *)
(* ⊢ (𝜑 → (𝜓 → (𝜃 → 𝜒))) *)
(* ----------------------*)
(* ⊢ (𝜑 → (𝜓 → (𝜒 ↔ 𝜃))) *)
Theorem impidd: forall P Q R S: Prop,((P -> (Q -> (R -> S))) /\ (P -> (Q -> (S -> R)))) -> (P -> (Q -> (R <-> S))).
Proof.
  intros P Q R S.
  intros H0.
  intros H1 H2.
  split.
  destruct H0.
  intros H3.
  apply H.
  exact H1.
  exact H2.
  exact H3.
  intros H4.
  destruct H0.
  apply H0.
  exact H1.
  exact H2.
  exact H4. 
Qed.

Print impidd.

Theorem impidd_2: forall P Q R S: Prop,((P -> (Q -> (R -> S))) /\ (P -> (Q -> (S -> R)))) -> (P -> (Q -> (R <-> S))).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P -> Q -> R -> S) /\ (P -> Q -> S -> R)) 
    (H1 : P) (H2 : Q) =>
  conj
    match H0 with
    | conj x x0 =>
      (fun (H : P -> Q -> R -> S) (_ : P -> Q -> S -> R) (H4 : R) =>
         H H1 H2 H4) x x0
    end
    (fun H4 : S =>
     match H0 with
     | conj x x0 =>
         (fun (_ : P -> Q -> R -> S) (H3 : P -> Q -> S -> R) => H3 H1 H2 H4) x
           x0
     end)
  ).
Qed.

(* http://us.metamath.org/ileuni/impbid21d.html *)
(* ⊢ (𝜓 → (𝜒 → 𝜃)) *)
(* ⊢ (𝜑 → (𝜃 → 𝜒)) *)
(* =================*)
(* ⊢ (𝜑 → (𝜓 → (𝜒 ↔ 𝜃))) *)
Theorem impid21d: forall P Q R S:Prop,((P -> (Q -> R)) /\ (S -> (R -> Q))) -> (S -> (P -> (Q <-> R))).
Proof.
  intros P Q R S.
  intros H0 H1 H2.
  split.
  intros H3.
  destruct H0.
  apply H.
  exact H2.
  exact H3.
  intros H4.
  destruct H0.
  apply H0.
  exact H1.
  exact H4.
Qed.

Print impid21d.

Theorem impid21d_02: forall P Q R S:Prop,((P -> (Q -> R)) /\ (S -> (R -> Q))) -> (S -> (P -> (Q <-> R))).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P -> Q -> R) /\ (S -> R -> Q)) (H1 : S) (H2 : P)
    =>
    conj
      (fun H3 : Q =>
       match H0 with
       | conj x x0 => (fun (H : P -> Q -> R) (_ : S -> R -> Q) => H H2 H3) x x0
       end)
      (fun H4 : R =>
       match H0 with
       | conj x x0 => (fun (_ : P -> Q -> R) (H3 : S -> R -> Q) => H3 H1 H4) x x0
       end)    
  ).
Qed.

(* http://us.metamath.org/ileuni/bicomi.html *)
(* ⊢ (𝜑 ↔ 𝜓) *)
(* ===========*)
(* ⊢ (𝜓 ↔ 𝜑) *)
Theorem bicomi: forall P Q: Prop,((P <-> Q) -> (Q <-> P)).
Proof.
  intros P Q.
  intros H0.
  split.
  destruct H0.
  intros H1.
  apply H0.
  exact H1.
  intros H2.
  destruct H0.
  apply H.
  exact H2.
Qed.

Print bicomi.

Theorem bicomi_02: forall P Q: Prop,((P <-> Q) -> (Q <-> P)).
Proof.
   exact (
    fun (P Q : Prop) (H0 : P <-> Q) =>
    conj
      match H0 with
      | conj x x0 => (fun (_ : P -> Q) (H1 : Q -> P) (H2 : Q) => H1 H2) x x0
      end
      (fun H2 : P =>
       match H0 with
       | conj x x0 => (fun (H : P -> Q) (_ : Q -> P) => H H2) x x0
       end)
   ).
Qed.

Check fun (P Q:Prop) (H0 : P <-> Q) => 
        match H0 with
        | conj x x0 => x0
        end.

(* http://us.metamath.org/ileuni/3imtr3i.html *)
(* ⊢ (𝜑 → 𝜓) *)
(* ⊢ (𝜑 ↔ 𝜒) *)
(* ⊢ (𝜓 ↔ 𝜃) *)
(* ------------*)
(* ⊢ (𝜒 → 𝜃) *)
Theorem threeimtr3i: forall P Q R S:Prop,
    ((P  -> Q) /\ 
     (P <-> R) /\ 
     (Q <-> S)) -> (R -> S).
Proof.
  intros P Q R S.
  intros H0 H1.
  destruct H0.
  destruct H0.
  apply H2.
  apply H.
  destruct H2.
  destruct H0.
  apply H4.
  exact H1.
Qed.

Print threeimtr3i.

Theorem threeimtr3i_02: forall P Q R S:Prop,
    ((P  -> Q) /\ 
     (P <-> R) /\ 
     (Q <-> S)) -> (R -> S).
Proof.
 exact (
  fun (P Q R S : Prop) (H0 : (P -> Q) /\ (P <-> R) /\ (Q <-> S)) (H1 : R) =>
  match H0 with
  | conj x x0 =>
    (fun (H : P -> Q) (H2 : (P <-> R) /\ (Q <-> S)) =>
       match H2 with
       | conj x1 x2 =>
           (fun (H3 : P <-> R) (H4 : Q <-> S) =>
            let H5 : Q -> S :=
              match H4 with
              | conj x3 x4 => (fun (H5 : Q -> S) (_ : S -> Q) => H5) x3 x4
              end in
            H5
              (H
                 match H4 with
                 | conj x3 x4 =>
                     (fun (_ : Q -> S) (_ : S -> Q) =>
                      match H3 with
                      | conj x5 x6 =>
                          (fun (_ : P -> R) (H9 : R -> P) => H9 H1) x5 x6
                      end) x3 x4
                 end)) x1 x2
       end) x x0
  end
 ).
Qed.

(* http://us.metamath.org/ileuni/expd.html *)
(* ⊢ (𝜑 → ((𝜓 ∧ 𝜒) → 𝜃)) *)
(* ---------------------- *)
(* ⊢ (𝜑 → (𝜓 → (𝜒 → 𝜃))) *)
Theorem expd:forall P Q R S:Prop, 
  (P -> ((Q /\ R) -> S)) -> 
  (P -> (Q -> (R -> S))).
Proof.
  intros P Q R S.
  intros H0 H1 H2 H3.
  apply H0.
  exact H1.
  split.
  exact H2.
  exact H3.
Qed.

Print expd.

(* http://us.metamath.org/ileuni/expd.html *)
(* ⊢ (𝜑 → ((𝜓 ∧ 𝜒) → 𝜃)) *)
(* ---------------------- *)
(* ⊢ (𝜑 → (𝜓 → (𝜒 → 𝜃))) *)
Theorem expd_01:forall P Q R S:Prop, 
  (P -> ((Q /\ R) -> S)) -> 
  (P -> (Q -> (R -> S))).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : P -> Q /\ R -> S) (H1 : P) (H2 : Q) (H3 : R) =>
    H0 H1 (conj H2 H3)
  ).
Qed.

(* http://us.metamath.org/ileuni/expdimp.html *)
(* ⊢ (𝜑 → ((𝜓 ∧ 𝜒) → 𝜃)) *)
(* ---------------------- *)
(* ⊢ ((𝜑 ∧ 𝜓) → (𝜒 → 𝜃)) *)
Theorem ileuni:forall P Q R S:Prop,
      (P -> ((Q /\ R) -> S)) -> 
      ((P /\ Q) -> (R -> S)).
Proof.
  intros P Q R S.
  intros H0 H1 H2.
  apply H0.
  destruct H1.
  exact H.
  split.
  destruct H1.
  exact H1.
  exact H2.
Qed.

Print ileuni.

Theorem ileuni_02:forall P Q R S:Prop,
      (P -> ((Q /\ R) -> S)) -> 
      ((P /\ Q) -> (R -> S)).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : P -> Q /\ R -> S) (H1 : P /\ Q) (H2 : R) =>
    H0 match H1 with
       | conj x x0 => (fun (H : P) (_ : Q) => H) x x0
       end
      (conj match H1 with
          | conj x x0 => (fun (_ : P) (H3 : Q) => H3) x x0
            end H2)
  ).
Qed.

(* http://us.metamath.org/ileuni/impancom.html *)
(* ⊢ ((𝜑 ∧ 𝜓) → (𝜒 → 𝜃)) *)
(* ---------------------- *)
(* ⊢ ((𝜑 ∧ 𝜒) → (𝜓 → 𝜃)) *)
Theorem impancom: forall P Q R S:Prop,
    ((P /\ Q) -> (R -> S)) -> 
    ((P /\ R) -> (Q -> S)).
Proof.
  intros P Q R S.
  intros H0 H1 H2.
  apply H0.
  split.
  destruct H1.
  exact H.
  exact H2.
  destruct H1.
  exact H1.
Qed.

Print impancom.

Theorem impancom_01: forall P Q R S:Prop,
    ((P /\ Q) -> (R -> S)) -> 
    ((P /\ R) -> (Q -> S)).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : P /\ Q -> R -> S) (H1 : P /\ R) (H2 : Q) =>
    H0 (conj match H1 with
           | conj x x0 => (fun (H : P) (_ : R) => H) x x0
             end H2)
      match H1 with
      | conj x x0 => (fun (_ : P) (H3 : R) => H3) x x0
      end
  ).
Qed.

(* http://us.metamath.org/ileuni/pm3.3.html *)
(* ⊢ (((𝜑 ∧ 𝜓) → 𝜒) → (𝜑 → (𝜓 → 𝜒))) *)
Theorem pm33: forall P Q R:Prop,(((P /\ Q) -> R) -> (P -> (Q -> R))).
Proof.
  intros P Q R.
  intros H0 H1 H2.
  apply H0.
  split.
  exact H1.
  exact H2.
Qed.

Print pm33.

Theorem pm33_02: forall P Q R:Prop,(((P /\ Q) -> R) -> (P -> (Q -> R))).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P /\ Q -> R) (H1 : P) (H2 : Q) => H0 (conj H1 H2)
  ).
Qed.

(* http://us.metamath.org/ileuni/pm3.31.html *)
(* ⊢ ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 ∧ 𝜓) → 𝜒) *)
Theorem pm331: forall P Q R:Prop,((P -> (Q -> R)) -> ((P /\ Q) -> R)).
Proof.
  intros P Q R.
  intros H0.
  intros H1.
  apply H0.
  destruct H1.
  exact H.
  destruct H1.
  exact H1. 
Qed.

Print pm331.

Theorem pm331_02: forall P Q R:Prop,((P -> (Q -> R)) -> ((P /\ Q) -> R)).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P -> Q -> R) (H1 : P /\ Q) =>
    H0 match H1 with
       | conj x x0 => (fun (H : P) (_ : Q) => H) x x0
       end match H1 with
         | conj x x0 => (fun (_ : P) (H2 : Q) => H2) x x0
           end
  ).
Qed.

(* http://us.metamath.org/ileuni/pm3.22.html *)
(* ⊢ ((𝜑 ∧ 𝜓) → (𝜓 ∧ 𝜑)) *)
Theorem pm322: forall P Q:Prop,((P /\ Q) -> (Q /\ P)).
Proof.
  intros P Q.
  intros H0.
  split.
  destruct H0.
  exact H0.
  destruct H0.
  exact H.
Qed.

Print pm322.

Theorem pm322_02: forall P Q:Prop,((P /\ Q) -> (Q /\ P)).
Proof.
exact (
  fun (P Q : Prop) (H0 : P /\ Q) =>
  conj match H0 with
     | conj x x0 => (fun (_ : P) (H1 : Q) => H1) x x0
       end match H0 with
           | conj x x0 => (fun (H : P) (_ : Q) => H) x x0
           end
).
Qed.

(* http://us.metamath.org/ileuni/ancomd.html *)
(* ⊢ (𝜑 → (𝜓 ∧ 𝜒)) *)
(* ================ *)
(* ⊢ (𝜑 → (𝜒 ∧ 𝜓)) *)
Theorem ancomd:forall P Q R:Prop,((P -> (Q /\ R)) -> (P -> (R /\ Q))).
Proof.
  intros P Q R.
  intros H0 H1.
  split.
  destruct H0.
  exact H1.
  exact H0.
  destruct H0.
  exact H1.
  exact H.
Qed.

(* http://us.metamath.org/ileuni/ancomsd.html *)
(* ⊢ (𝜑 → ((𝜓 ∧ 𝜒) → 𝜃)) *)
(* -----------------------*)
(* ⊢ (𝜑 → ((𝜒 ∧ 𝜓) → 𝜃)) *)
Theorem ancomsd:forall P Q R S:Prop,(P -> ((Q /\ R) -> S)) -> (P -> ((R /\ Q) -> S)).
Proof.
  intros P Q R S.
  intros H0 H1 H2.
  apply H0.
  exact H1.
  split.
  destruct H2.
  exact H2.
  destruct H2.
  exact H.
Qed.

Print ancomsd.

Theorem ancomsd_01:forall P Q R S:Prop,(P -> ((Q /\ R) -> S)) -> (P -> ((R /\ Q) -> S)).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : P -> Q /\ R -> S) (H1 : P) (H2 : R /\ Q) =>
    H0 H1
      (conj match H2 with
          | conj x x0 => (fun (_ : R) (H3 : Q) => H3) x x0
            end match H2 with
                | conj x x0 => (fun (H : R) (_ : Q) => H) x x0
                end)
  ).
Qed.

(* http://us.metamath.org/ileuni/pm3.43i.html *)
(* ⊢ ((𝜑 → 𝜓) → ((𝜑 → 𝜒) → (𝜑 → (𝜓 ∧ 𝜒)))) *)
Theorem pm343i:forall P Q R S:Prop,((P -> Q) -> ((P -> R) -> (P -> (Q /\ R)))).
Proof.
  intros P Q R S.
  intros H0 H1 H2.
  split.
  apply H0.
  exact H2.
  apply H1.
  exact H2.
Qed.

Print pm343i.

Theorem pm343i_02:forall P Q R S:Prop,((P -> Q) -> ((P -> R) -> (P -> (Q /\ R)))).
Proof.
  exact (
    fun (P Q R _ : Prop) (H0 : P -> Q) (H1 : P -> R) (H2 : P) =>
    conj (H0 H2) (H1 H2)
  ).
Qed.
(* ⊢ (𝜑 ↔ (𝜓 ∧ 𝜒)) *)
(* ---------------- *)
(* ⊢ (𝜑 → 𝜓) *)
Theorem simplbi:forall P Q R:Prop,((P <-> (Q /\ R)) -> (P -> Q)).
Proof.
  intros P Q R.
  intros H0 H1.
  destruct H0.
  destruct H.
  exact H1.
  exact H.
Qed.

Print simplbi.

Theorem simplbi_02:forall P Q R:Prop,((P <-> (Q /\ R)) -> (P -> Q)).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P <-> Q /\ R) (H1 : P) =>
    match H0 with
    | conj x x0 =>
      (fun (H : P -> Q /\ R) (_ : Q /\ R -> P) =>
         let a : Q /\ R := H H1 in
         match a with
         | conj x1 x2 => (fun (H3 : Q) (_ : R) => H3) x1 x2
         end) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/simprbi.html *)
(* ⊢ (𝜑 ↔ (𝜓 ∧ 𝜒)) *)
(* ---------------- *)
(* ⊢ (𝜑 → 𝜒) *)
Theorem simprbi:forall P Q R:Prop,((P <-> (Q /\ R)) -> (P -> R)).
Proof.
  intros P Q R.
  intros H0 H1.
  destruct H0.
  destruct H.
  exact H1.
  exact H2.
Qed.

Print simprbi.

Theorem simprbi_01:forall P Q R:Prop,((P <-> (Q /\ R)) -> (P -> R)).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P <-> Q /\ R) (H1 : P) =>
    match H0 with
    | conj x x0 =>
      (fun (H : P -> Q /\ R) (_ : Q /\ R -> P) =>
         let a : Q /\ R := H H1 in
         match a with
         | conj x1 x2 => (fun (_ : Q) (H4 : R) => H4) x1 x2
         end) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/adantr.html *)
(* ⊢ (𝜑 → 𝜓) *)
(* ⊢ ((𝜑 ∧ 𝜒) → 𝜓) *)
Theorem adantr:forall P Q R:Prop,((P -> R) -> ((P /\ Q) -> R)).
Proof.
  intros P Q R.
  intros H0.
  intros H1.
  apply H0.
  destruct H1.
  exact H.
Qed.

Print adantr.

Theorem adantr_02:forall P Q R:Prop,((P -> R) -> ((P /\ Q) -> R)).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : P -> R) (H1 : P /\ Q) => H0 
      match H1 with
      | conj x x0 => (fun (H : P) (_ : Q) => H) x x0
      end
  ).
Qed.

Section proof_of_tripl_impl.
  Variables P Q S:Prop.
  Hypothesis H : ((P -> Q) -> Q) -> Q.
  Hypothesis p : P.

  Lemma Rem : (P -> Q) -> Q.
  Proof (fun H0:P -> Q => H0 p).

  Definition  Rem_f := (fun H0:P -> Q => H0 p).
  
  Eval cbv in (Rem_f).
  
End proof_of_tripl_impl.

(* https://cs.stackexchange.com/questions/80590/is-possible-to-prove-undecidability-of-the-halting-problem-in-coq *)
Record bijection A B :=
  {  to   : A -> B
  ; from : B -> A
  ; to_from : forall b, to (from b) = b
  ; from_to : forall a, from (to a) = a
  }.

Theorem cantor :
  bijection nat (nat -> nat) ->
  False.
Proof.
  destruct 1 as [seq index ? ?].
  (* define a function which differs from the nth sequence at the nth index *)
  pose (f := fun n => S (seq n n)).
  (* prove f differs from every sequence *)
  assert (forall n, f <> seq n). {
    unfold not; intros.
    assert (f n = seq n n) by congruence.
    subst f; cbn in H0.
    eapply n_Sn; eauto.
  }
  rewrite <- (to_from0 f) in H.
  apply (H (index f)).
  reflexivity.
Qed.

Print cantor.

Theorem cator_02 : (bijection nat (nat -> nat)) -> False.
Proof.
exact (
  fun H : bijection nat (nat -> nat) =>
  match H with
  | {| to := to; from := from; to_from := to_from; from_to := from_to |} =>
    (fun (seq : nat -> nat -> nat) (index : (nat -> nat) -> nat)
         (to_from0 : forall b : nat -> nat, seq (index b) = b)
         (_ : forall a : nat, index (seq a) = a) =>
       let f := fun n : nat => S (seq n n) in
       let H0 : forall n : nat, f <> seq n :=
         (fun (n : nat) (H0 : f = seq n) =>
          let H1 : f n = seq n n :=
            eq_trans (f_equal (fun f0 : nat -> nat => f0 n) H0)
              (f_equal (seq n) eq_refl) in
          n_Sn (seq n n) (eq_sym H1))
          :
          forall n : nat, f <> seq n in
        let H1 : forall n : nat, seq (index f) <> seq n :=
          eq_ind_r (fun f0 : nat -> nat => forall n : nat, f0 <> seq n) H0
            (to_from0 f) in
        H1 (index f) eq_refl) to from to_from from_to
   end
).
Qed.

(*http://us.metamath.org/ileuni/adantl.html*)
(* ⊢ (𝜑 → 𝜓) *)
(* -----------*)
(* ⊢ ((𝜒 ∧ 𝜑) → 𝜓) *)
Theorem adanl:forall P Q R:Prop, (Q -> R) -> ((P /\ Q) -> R).
Proof.
  intros P Q R.
  intros H0.
  intros H1.
  apply H0.
  destruct H1.
  trivial.
Qed.

Print adanl.

Theorem adanl_01:forall P Q R:Prop, (Q -> R) -> ((P /\ Q) -> R).
Proof.
  exact (
    fun (P Q R : Prop) (H0 : Q -> R) (H1 : P /\ Q) =>
    H0 match H1 with
       | conj x x0 => (fun (_ : P) (H2 : Q) => H2) x x0
       end
  ).
Qed.

(* http://us.metamath.org/ileuni/adantld.html *)
(* ⊢ (𝜑 → (𝜓 → 𝜒))  *)
(* ----------------- *)
(* ⊢ (𝜑 → ((𝜃 ∧ 𝜓) → 𝜒)) *)
Theorem adantld:forall P Q R S:Prop,(P -> (R -> S)) -> (P -> ((Q /\ R) -> S)).
Proof.
  intros P Q R S.
  intros H0.
  intros H1.
  intros H2.
  apply H0.
  exact H1.
  destruct H2.
  trivial.
Qed.

Print adantld.

Theorem adantld_02:forall P Q R S:Prop,(P -> (R -> S)) -> (P -> ((Q /\ R) -> S)).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : P -> R -> S) (H1 : P) (H2 : Q /\ R) =>
    H0 H1 match H2 with
        | conj x x0 => (fun (_ : Q) (H3 : R) => H3) x x0
          end
  ).
Qed.

(* http://us.metamath.org/ileuni/adantrd.html *)
(* ⊢ (𝜑 → (𝜓 → 𝜒)) *)
(* ---------------- *)
(* ⊢ (𝜑 → ((𝜓 ∧ 𝜃) → 𝜒)) *)
Theorem adantrd:forall P Q R S:Prop,(P -> (Q -> S)) -> (P -> ((Q /\ R) -> S)).
Proof.
  intros P Q R S;intros H0;intros H1;intros H2.
  apply H0.
  exact H1.
  destruct H2.
  trivial.
Qed.

Print adantrd.

Theorem adantrd_02:forall P Q R S:Prop,(P -> (Q -> S)) -> (P -> ((Q /\ R) -> S)).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : P -> Q -> S) (H1 : P) (H2 : Q /\ R) =>
    H0 H1 match H2 with
        | conj x x0 => (fun (H : Q) (_ : R) => H) x x0
          end
  ).
Qed.

(* http://us.metamath.org/ileuni/impel.html *)
(* ⊢ (P → (Q → S)) *)
(* ⊢ (R → Q) *)
(* ------------------*)
(* ⊢ ((P ∧ R) → S) *)
Theorem impel:forall P Q R S:Prop,((P -> (Q -> S)) /\ (R -> Q)) -> ((P /\ R) -> S).
Proof.
  intros P Q R S.
  intros H0.
  intros H1.
  destruct H0.
  apply H.
  destruct H1.
  exact H1.
  apply H0.
  destruct H1.
  trivial.
Qed.

Print impel.

Theorem impel2:forall P Q R S:Prop,((P -> (Q -> S)) /\ (R -> Q)) -> ((P /\ R) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P -> Q -> S) /\ (R -> Q)) (H1 : P /\ R) =>
    match H0 with
    | conj x x0 =>
      (fun (H : P -> Q -> S) (H2 : R -> Q) =>
         H match H1 with
           | conj x1 x2 => (fun (H3 : P) (_ : R) => H3) x1 x2
           end
           (H2
              match H1 with
              | conj x1 x2 => (fun (_ : P) (H4 : R) => H4) x1 x2
              end)) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/mpan9.html *)
(* ⊢ (P → R) *)
(* ⊢ (Q → (R → S)) *)
(* --------------- *)
(* ⊢ ((P ∧ Q) → S) *)
Theorem mpan9:forall P Q R S:Prop,((P -> R) /\ (Q -> (R -> S))) -> ((P /\ Q) -> S).
Proof.
  intros P Q R S.
  intros H0.
  intros H1.
  destruct H0.
  apply H0.
  destruct H1.
  exact H2.
  apply H.
  destruct H1.
  trivial.
Qed.

Print mpan9.

Theorem mpan9_01:forall P Q R S:Prop,((P -> R) /\ (Q -> (R -> S))) -> ((P /\ Q) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P -> R) /\ (Q -> R -> S)) (H1 : P /\ Q) =>
      match H0 with
      | conj x x0 =>
        (fun (H : P -> R) (H2 : Q -> R -> S) =>
          H2 match H1 with
              | conj x1 x2 => (fun (_ : P) (H4 : Q) => H4) x1 x2
              end
            (H
                match H1 with
                | conj x1 x2 => (fun (H3 : P) (_ : Q) => H3) x1 x2
                end)) x x0
      end
  ).
Qed.

(* http://us.metamath.org/ileuni/syldan.html *)
(* ⊢ ((P ∧ Q) → R) *)
(* ⊢ ((P ∧ R) → S) *)
(* ---------------- *)
(* ⊢ ((P ∧ Q) → S) *)
Theorem syldan:forall P Q R S:Prop,(((P /\ Q) -> R) /\ ((P /\ R) -> S)) -> ((P /\ Q) -> S).
Proof.
  intros P Q R S.
  intros H0.
  intros H1.
  destruct H0.
  apply H0.
  split.
  destruct H1.
  exact H1.
  apply H.
  trivial.
Qed.

Print syldan.

Theorem syldan_02:forall P Q R S:Prop,(((P /\ Q) -> R) /\ ((P /\ R) -> S)) -> ((P /\ Q) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P /\ Q -> R) /\ (P /\ R -> S)) (H1 : P /\ Q) =>
    match H0 with
    | conj x x0 =>
      (fun (H : P /\ Q -> R) (H2 : P /\ R -> S) =>
         H2
           (conj
              match H1 with
              | conj x1 x2 => (fun (H3 : P) (_ : Q) => H3) x1 x2
              end (H H1))) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/sylan.html *)
(* ⊢ (P → Q) *)
(* ⊢ ((Q ∧ R) → S) *)
(* ---------------- *)
(* ⊢ ((P ∧ R) → S) *)
Theorem sylan:forall P Q R S:Prop,
  ((P -> Q) /\ ((Q /\ R) -> S)) -> ((P /\ R) -> S).
Proof.
  intros P Q R S.
  intros H0;intros H1.
  destruct H0.
  apply H0.
  split.
  apply H.
  destruct H1.
  exact H1.
  destruct H1.
  trivial.
Qed.

Print sylan.

Theorem sylan_02:forall P Q R S:Prop,
  ((P -> Q) /\ ((Q /\ R) -> S)) -> ((P /\ R) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P -> Q) /\ (Q /\ R -> S)) (H1 : P /\ R) =>
    match H0 with
    | conj x x0 =>
      (fun (H : P -> Q) (H2 : Q /\ R -> S) =>
         H2
           (conj
              (H
                 match H1 with
                 | conj x1 x2 => (fun (H3 : P) (_ : R) => H3) x1 x2
                 end)
              match H1 with
              | conj x1 x2 => (fun (_ : P) (H4 : R) => H4) x1 x2
              end)) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/sylanb.html *)
(* ⊢ (P ↔ Q) *)
(* ⊢ ((Q ∧ R) → S) *)
(* ---------------- *)
(* ⊢ ((P ∧ R) → S) *)
Theorem sylanb:
  forall P Q R S:Prop,
  ((P <-> Q) /\
  ((Q /\ R) -> S)) 
  -> ((P /\ R) -> S).
Proof.
  intros P Q R S.
  intros H0; intros H1.
  destruct H0.
  apply H0.
  split.
  destruct H as (H2 & H3).
  apply H2.
  destruct H1 as (H4 & H5).
  exact H4.
  destruct H1 as (H4 & H5).
  trivial.
Qed.

(* http://us.metamath.org/ileuni/sylanbr.html *)
(* ⊢ (P ↔ Q) *)
(* ⊢ ((P ∧ R) → S) *)
(* ---------------- *)
(* ⊢ ((Q ∧ R) → S) *)
Theorem sylanbr:forall P Q R S:Prop,
  ((P <-> Q) /\ 
   ((P /\ Q) -> S)) -> 
  ((Q /\ R) -> S).
Proof.
  intros P Q R S.
  intros H0 H1.
  destruct H0 as (H2 & H3).
  apply H3.
  split.
  destruct H2 as (H4 & H5).
  apply H5.
  destruct H1 as (H6 & H7).
  trivial.
  destruct H1 as (H6 & H7).
  trivial.
Qed.

Print sylanbr.

Theorem sylanbr_02:forall P Q R S:Prop,
  ((P <-> Q) /\ 
   ((P /\ Q) -> S)) -> 
  ((Q /\ R) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P <-> Q) /\ (P /\ Q -> S)) (H1 : Q /\ R) =>
    match H0 with
    | conj x x0 =>
      (fun (H2 : P <-> Q) (H3 : P /\ Q -> S) =>
         H3
           (conj
              match H2 with
              | conj x1 x2 =>
                  (fun (_ : P -> Q) (H5 : Q -> P) =>
                   H5
                     match H1 with
                     | conj x3 x4 => (fun (H6 : Q) (_ : R) => H6) x3 x4
                     end) x1 x2
              end
              match H1 with
              | conj x1 x2 => (fun (H6 : Q) (_ : R) => H6) x1 x2
              end)) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/sylan2.html *)
(* ⊢ (P → Q) *)
(* ⊢ ((R ∧ Q) → S) *)
(* ---------------- *)
(* ⊢ ((R ∧ P) → S) *)
Theorem sylan2:forall P Q R S:Prop,
    ((P -> Q) /\ 
     ((R /\ Q) -> S)) ->
    ((R /\ P) -> S).
Proof.
  intros P Q R S.
  intros H0 H1.
  destruct H0 as (H2 & H3).
  apply H3.
  split.
  destruct H1 as (H4 & H5).
  trivial.
  apply H2.
  destruct H1 as (H4 & H5).
  exact H5.
Qed.

Print sylan2.

Theorem sylan2_02:forall P Q R S:Prop,
    ((P -> Q) /\ 
     ((R /\ Q) -> S)) ->
    ((R /\ P) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P -> Q) /\ (R /\ Q -> S)) (H1 : R /\ P) =>
    match H0 with
    | conj x x0 =>
      (fun (H2 : P -> Q) (H3 : R /\ Q -> S) =>
         H3
           (conj
              match H1 with
              | conj x1 x2 => (fun (H4 : R) (_ : P) => H4) x1 x2
              end
              (H2
                 match H1 with
                 | conj x1 x2 => (fun (_ : R) (H5 : P) => H5) x1 x2
                 end))) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/sylan2b.html *)
(* ⊢ (P ↔ Q) *)
(* ⊢ ((R ∧ Q) → S) *)
(* ---------------- *)
(* ⊢ ((R ∧ P) → S) *)
Theorem sylan2b:forall P Q R S:Prop,
   ((P <-> Q) /\ 
    ((R /\ Q) -> S)) -> 
   ((R /\ P) -> S).
Proof.
  intros P Q R S.
  intros H0 H1.
  destruct H0 as (H2 & H3).
  apply H3.
  destruct H2 as (H4 & H5).
  split.
  destruct H1 as (H6 & H7).
  exact H6.
  apply H4.
  destruct H1 as (H6 & H7).
  exact H7.
Qed.

Print sylan2b.

Theorem sylan2b_02:forall P Q R S:Prop,
   ((P <-> Q) /\ 
    ((R /\ Q) -> S)) -> 
   ((R /\ P) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P <-> Q) /\ (R /\ Q -> S)) (H1 : R /\ P) =>
    match H0 with
    | conj x x0 =>
      (fun (H2 : P <-> Q) (H3 : R /\ Q -> S) =>
         H3
           match H2 with
           | conj x1 x2 =>
               (fun (H4 : P -> Q) (_ : Q -> P) =>
                conj
                  match H1 with
                  | conj x3 x4 => (fun (H6 : R) (_ : P) => H6) x3 x4
                  end
                  (H4
                     match H1 with
                     | conj x3 x4 => (fun (_ : R) (H7 : P) => H7) x3 x4
                     end)) x1 x2
           end) x x0
    end
  ).
Qed.

(* http://us.metamath.org/ileuni/sylan2br.html *)
(* ⊢ (P ↔ Q) *)
(* ⊢ ((R ∧ P) → S) *)
(* ---------------- *)
(* ⊢ ((R ∧ Q) → S) *)
Theorem sylan2br:forall P Q R S:Prop,
   ((P <-> Q) /\ 
    ((R /\ P) -> S)) -> 
   ((R /\ Q) -> S).
Proof.
  intros P Q R S.  
  intros H0 H1.
  destruct H0 as (H2 & H3).
  apply H3.
  split.
  destruct H1 as (H4 & H5).
  exact H4.
  destruct H2 as (H6 & H7).
  apply H7.
  destruct H1 as (H4 & H5).
  trivial.
Qed.

Print sylan2br.

Theorem sylan2br_01:forall P Q R S:Prop,
   ((P <-> Q) /\ 
    ((R /\ P) -> S)) -> 
   ((R /\ Q) -> S).
Proof.
  exact (
    fun (P Q R S : Prop) (H0 : (P <-> Q) /\ (R /\ P -> S)) (H1 : R /\ Q) =>
    match H0 with
    | conj x x0 =>
      (fun (H2 : P <-> Q) (H3 : R /\ P -> S) =>
         H3
           (conj
              match H1 with
              | conj x1 x2 => (fun (H4 : R) (_ : Q) => H4) x1 x2
              end
              match H2 with
              | conj x1 x2 =>
                  (fun (_ : P -> Q) (H7 : Q -> P) =>
                   H7
                     match H1 with
                     | conj x3 x4 => (fun (_ : R) (H5 : Q) => H5) x3 x4
                     end) x1 x2
              end)) x x0
    end
  ).
Qed.

Print prod.
(*
Inductive prod (A B : Type) : Type :=  
   pair : A -> B -> A * B.
*)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.
Print add1.

From ReductionEffect Require Import PrintingEffect.
Eval cbv in (fun f x => f (f (f x))) (fun x => S (print_id x)) 0.
Eval cbn in (fun f x => f (f (f x))) print_id 0. (* Not so interesting *)
Eval hnf in (fun f x => f (f (f x))) print_id 0. (* Not so interesting *)
Eval simpl in (fun f x => f (f (f x))) (fun x => print_id (1+x) + 1) 0.
Eval cbv in let x := print 3 in let y := print 4 in tt.

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

  Eval cbv in (fun f x => (plus 3 2)) (fun x => S (print_id x)) 0.

  End NatPlayground2.

(* detour with https://softwarefoundations.cis.upenn.edu/*)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Theorem plus_0_n : forall n : nat,0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Print plus_0_n.

Theorem plus_0_n_02 : forall n : nat,0 + n = n.
Proof.
  exact (
    fun n : nat => eq_refl : 0 + n = n
  ).
Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
    intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
  Proof.
    intros n. simpl. reflexivity. Qed.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. 
  reflexivity. 
Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.   

Check @eq : forall A : Type, A -> A -> Prop.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
  intros n m H. 
  injection H as H1. 
  apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  Show Proof.
  - reflexivity.
  Show Proof.
  - reflexivity.
  Show Proof.
Qed.

Print and_example.
Print conj. 

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Print and_intro.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros m n.
  induction m.
  split.
  - reflexivity.
  - apply H.
  - intros H0.
  Admitted.
  

 