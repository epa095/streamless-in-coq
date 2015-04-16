Require  Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.ConstructiveEpsilon.

Section Streamless.

(* We assume that we have some sort of pairing function, enabling us to encode
pairs of natural numbers as a single natural number (and decode them again). *)

Variable encoding : nat->nat->nat.
(* Decoding functions: *)
Variable dec1:nat->nat.
Variable dec2:nat->nat.

(* We need to know that decoding works*)
Axiom com1: forall n m:nat, (dec1 (encoding n m)) = n.
Axiom com2: forall n m:nat, (dec2 (encoding n m)) = m.
Hint Resolve com1 com2.


Definition DecidableEq (A: Set) := forall a b: A, {a=b} + {~ a=b}.

(* Each of the definitions come in a pair and single number version *)

Definition StreamlessSigOneNat (A:Set):= forall g:nat->A,
                                     {ij : nat | dec1 ij < dec2 ij /\ g(dec1 ij)=g(dec2 ij)}.

Definition StreamlessSig (A:Set):= forall g:nat->A,
                                     {ij : nat*nat | fst ij < snd ij /\ g(fst ij)=g(snd ij)}.


Definition StreamlessEx(A:Set):= forall g:nat->A,exists j i, i<j /\ g(i) = g(j).
Definition StreamlessExOneNat(A:Set):= forall g:nat->A,exists i, dec1 i<dec2 i /\ g(dec1 i) = g(dec2 i).

Definition functional_extensionality (A B:Set):=
    forall (f g : A-> B), (forall x, f x = g x) -> f = g.


(* First we show that the paired/unpaired versions of streamlessEx are equvalent, and then the same for StreamlessSig *)
Theorem strExToStrExEnc(A:Set): StreamlessEx A -> StreamlessExOneNat A.
Proof.
  unfold StreamlessEx.
  unfold StreamlessExOneNat.
  intros.
  pose (H g).
  destruct e.
  destruct H0.
  exists (encoding x0 x).
  rewrite com1.
  rewrite com2.
auto.
Qed.
Hint Resolve strExToStrExEnc.

Theorem strExEncToStrEx(A:Set): StreamlessExOneNat A -> StreamlessEx A.
Proof.
  unfold StreamlessEx.
  unfold StreamlessExOneNat.
  intros.
  pose (H g).
  destruct e.
  destruct H0.
  exists (dec2 x).
  exists (dec1 x).
auto.
Qed.
Hint Resolve strExEncToStrEx.


Theorem strSetToStrSetEnc(A:Set): StreamlessSig A -> StreamlessSigOneNat A.
Proof.
  unfold StreamlessSig.
  unfold StreamlessSigOneNat.
  intros.
  pose (H g).
  destruct s.
  destruct x.
  exists (encoding n n0).
  rewrite com1.
  rewrite com2.
auto.
 Qed.
Hint Resolve strSetToStrSetEnc.

Theorem strSetEncToStrSet(A:Set): StreamlessSigOneNat A -> StreamlessSig A.
Proof.
  unfold StreamlessSig.
  unfold StreamlessSigOneNat.
  intros.
  pose (H g).
  destruct s.
  exists (dec1 x, dec2 x).
  auto.
Qed.
Hint Resolve strSetEncToStrSet.


Lemma streamlessExToStrSig(A:Set)(A_dec: DecidableEq A) : StreamlessEx A -> StreamlessSig A.
  intros.
  assert (StreamlessSigOneNat A).
  pose (strExToStrExEnc A H).
  intro.  
  apply constructive_indefinite_ground_description_nat;auto.
  intros.
  pose (lt_dec (dec1 n) (dec2 n)).
  pose (A_dec (g (dec1 n)) (g (dec2 n))).
  inversion s0;inversion s1;firstorder.
  apply (strSetEncToStrSet A H0).
Qed.


Lemma LimitedAc (A:Set) (Ma : StreamlessSig A) (g f : nat -> A) (id : g=f): proj1_sig (Ma g) = proj1_sig (Ma f).
Proof.
  rewrite id.
  auto. 
Qed. 
Hint Resolve LimitedAc.

(* A pair of natural numbers are equal if their components are *)
Lemma pairNatEqNat:(forall a b:nat*nat,{a=b}+{~a=b}).
  Proof.
  intros.
  destruct a.
  destruct b. 
  destruct ((NPeano.Nat.eq_dec n n1)); destruct ((NPeano.Nat.eq_dec n0 n2));auto;right;intro;inversion H;firstorder.
Qed.
Hint Resolve pairNatEqNat.

Lemma strSigAndFuncExtImpliesDecA (A:Set) (Ma:StreamlessSig A) (fext: functional_extensionality nat A): forall a b :A, {a=b}+{not (a=b)} .
Proof.
  intros.
  set(fa := (fun x:nat=> a)).
  pose (Ma fa).
  pose (proj1_sig s).
  set(fap := (fun x:nat=> if (NPeano.Nat.eq_dec x (fst p)) then b else a)).
  assert (a=b -> fa=fap);auto.
  intro.
  apply (fext fa fap).
  intro.
  unfold fa.
  unfold fap.  
  destruct ((NPeano.Nat.eq_dec x (fst p)));auto.
  assert (a=b -> proj1_sig (Ma fa)=proj1_sig (Ma fap));auto.
  assert ({ proj1_sig (Ma fa) = proj1_sig (Ma fap)}+{~ proj1_sig (Ma fa) = proj1_sig (Ma fap)});auto.
  inversion H1;auto.
  assert (fst (proj1_sig (Ma fa))=fst (proj1_sig (Ma fap)));auto.
  elim H2;auto.
  assert (snd (proj1_sig (Ma fa))=snd (proj1_sig (Ma fap)));auto.
  elim H2;auto.  
  unfold p in fap.
  unfold s in fap.
  left.
  pose (proj1_sig (Ma fap) ).
  pose (proj2_sig (Ma fap) ).
  pose  (fap (fst (proj1_sig (Ma fap)))).
  pose  (fap (snd (proj1_sig (Ma fap)))).

  assert (fap (fst (proj1_sig (Ma fap))) = b).
  rewrite<- H3.
  unfold fap.
  elim (NPeano.Nat.eq_dec (fst (proj1_sig (Ma fa))) (fst (proj1_sig (Ma fa))));auto.
  intros.
  contradiction b0;firstorder.
  assert (fap (snd (proj1_sig (Ma fap))) = a).
  rewrite<- H4.
  unfold fap.
  elim (NPeano.Nat.eq_dec (fst (proj1_sig (Ma fa))) (snd (proj1_sig (Ma fa))));auto;intros.
  contradict a3.
  apply NPeano.Nat.lt_neq;auto.
  apply (proj2_sig s).
  elim (NPeano.Nat.eq_dec (snd (proj1_sig (Ma fa))) (fst (proj1_sig (Ma fa))));auto;intros.
  contradict a3.
  auto.
  rewrite<- H5.
  rewrite<- H6.
  destruct a0.
  auto.
Qed.

End Streamless.