/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

-- example : false := _   -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pp,
  cases pp,
  exact pp,
  exact pp,
  assume p,
  exact (or.intro_left P p),  
end
/-
Assume that we have a proposition P. Since we are trying to prove
P ∨ P ↔ P, it suffices to prove P ∨ P → P and P → P ∨ P. To prove P ∨ P → P,
assume that P ∨ P is true. Then, we have two cases. In the first case, P is true, which
is exactly what we are trying to prove. In the second case, P is true,
which is exactly what we are trying to prove. 
To prove P → P ∨ P, assume that P is true. Then, since it suffices to prove
just the left side of P ∨ P, we are done because that is exactly P.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pp,
  exact (and.elim_right pp),
  assume p,
  exact (and.intro p p),
end

/- 
Assume that we have a proposition P. Since we are trying to prove P ∧ P ↔ P,
it suffices to prove P ∧ P → P and P → P ∧ P via the introduction rule for iff.
To prove P ∧ P → P, assume P ∧ P is true. Then, because P is
what we want to prove and this is exactly the right side of P ∧ P, we are done.
To prove P → P ∧ P, assume P is true. Because we have a proof of P ∧ P from 
knowing P is true using the introduction rule for and, 
and this is exactly a proof of our proposition P ∧ P, we are done.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  assume pq,
  cases pq,
  exact (or.inr pq),
  exact (or.inl pq),
  assume pq,
  cases pq,
  exact (or.inr pq),
  exact (or.inl pq),
end

/- 
Assume we have propositions P and Q. Since we are trying to prove P ∧ Q ↔ Q ∧ P,
it suffices to show P ∨ Q → Q ∨ P and Q ∨ P → P ∨ Q. To show P ∨ Q → Q ∨ P,
we assume P ∨ Q is true. We have two cases. In the first case, P is true, so that
we are done because this is exactly the right side of Q ∨ P. In the second case,
Q is true, so that we are done because this is exactly the left side of Q ∨ P.
To show Q ∨ P → P ∨ Q, we assume Q ∨ P is true. We have two cases. In the first case,
Q is true, so that we are done because this is exactly the right side of P ∨ Q.
In the second case, P is true, so that we are done because this is exactly the left 
side of P ∨ Q.
-/


example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pq,
  apply and.intro _ _,
  exact (and.elim_right pq),
  exact (and.elim_left pq),
  assume pq,
  apply and.intro _ _,
  exact (and.elim_right pq),
  exact (and.elim_left pq),
end

/- 
Assume we have propositions P Q. Since we wish to show P ∧ Q ↔ Q ∧ P, it suffices to
show that P ∧ Q → Q ∧ P and Q ∧ P → P ∧ Q.  To show P ∧ Q → Q ∧ P, assume P ∧ Q is true.
Then, it suffices to prove Q and P seperately. To prove Q, we are done because this is 
exactly the right side of P ∧ Q. To prove P, we are done because this is exactly the left
side of P ∧ Q.
To prove Q ∧ P → P ∧ Q, assume Q ∧ P is true. Then, it suffices to prove P and Q seprately.
To prove P, we are done because this is exactly the right side of Q ∧ P. To prove Q, we 
are done because this is exactly the left side of Q ∧ P.
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqr,
  have p : P := and.elim_left pqr,
  have qr : Q ∨ R := and.elim_right pqr,
  cases qr,
  have pq : P ∧ Q := and.intro p qr,
  exact (or.inl pq),
  have pr : P ∧ R := and.intro p qr,
  exact (or.inr pr),
  assume pqpr,
  cases pqpr,
  apply and.intro _ _,
  exact (and.elim_left pqpr),
  have q : Q := and.elim_right pqpr,
  exact (or.inl q),
  apply and.intro _ _,
  exact (and.elim_left pqpr),
  have r : R := and.elim_right pqpr,
  exact (or.inr r),
end
/- 
Assume we have propositions P Q and R. Since we want to prove P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R),
it suffices to show P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) and (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R).
to prove P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R), assume P ∧ (Q ∨ R) is true. Then, we have a proof of
P and a proof of Q ∨ R. For our proof of Q ∨ R, we have two cases. In the first case, Q is true,
so that we have a proof of P ∧ Q and are done because that is precisely the left hand side of 
(P ∧ Q) ∨ (P ∧ R). In the second case of Q ∨ R, we have a proof of R, so that we have a proof of
P ∧ R and are done because that is precisely the right hand side of (P ∧ Q) ∨ (P ∧ R).
To prove (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R), assume we have a proof of (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R).
Then, we have two cases. In the first case, P ∧ Q is true. It suffices to prove P and Q ∨ R seprately.
To see why P is true, we are done because this is precisely the left side of P ∧ Q. Now, we obtain
a proof that Q is true from the proof of P ∧ Q, so that we are done because this is precisely
the left side of P ∨ Q.  In the second case, P ∧ R is true. It suffices to prove P and Q ∨ R seprately.
To see why P is true, we are done because this is exactly the left side of P ∧ R. Now, we obtain of proof
of R from the right side of P ∧ R and are done because this is precisely the right side of Q ∨ R.
-/


example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqr,
  cases pqr,
  apply and.intro _ _,
  exact (or.inl pqr),
  exact (or.inl pqr),
  have q : Q := and.elim_left pqr,
  have r : R := and.elim_right pqr,
  apply and.intro _ _,
  exact (or.inr q),
  exact (or.inr r),
  assume pqpr,
  have pq : P ∨ Q := and.elim_left pqpr,
  have pr : P ∨ R := and.elim_right pqpr,
  cases pq,
  exact (or.inl pq),
  cases pr,
  exact (or.inl pr),
  have qr : Q ∧ R := and.intro pq pr,
  exact (or.inr qr),
end

/- 
Assume we have propositions P Q R. Since we wish to prove P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R),
we can just show P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) and (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R). To see why
P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) is true,  assume P ∨ ( Q ∧ R) is true. Then, we have two cases.
In the first case, P is true. To prove (P ∨ Q) ∧ (P ∨ R) is true, we prove P ∨ Q and P ∨ R separately.
To see why P ∨ Q is true, we are done because its left side is exactly P, which we have a proof of.
To see why P ∨ R is true, we are done because its left side is exactly P, which we have a proof of.
To see why (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R) is true, assume (P ∨ Q) ∧ (P ∨ R). Now we have a proof of
P ∨ Q and P ∨ R. In the first case of P ∨ Q, P is true, so that we are done because this is the left
side of P ∨ (Q ∧ R). In the second case of P ∨ Q, Q is true. Now, in the first case of P ∨ R, P is true,
so that we are done because this is the left side of P ∨ (Q ∧ R). In the second case of P ∨ R, R is true
so that we have a proof of Q ∧ R, and thus we are done because this is the right side of P ∨ (Q ∧ R).
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  assume ppq,
  exact (and.elim_left ppq),
  assume p,
  apply and.intro _ _,
  exact p,
  exact (or.inl p),
end
/- 
Assume we have propositions P and Q. Since we want to prove P ∧ (P ∨ Q) ↔ P, it suffices to show 
P ∧ (P ∨ Q) → P and P → P ∧ (P ∨ Q). To see why P ∧ (P ∨ Q) → P, assume we have a proof of
P ∧ (P ∨ Q), so that we are done because P is exactly the right hand side of P ∧ (P ∨ Q).
To see why P → P ∧ (P ∨ Q) is true, we assume we have a proof of P. Now, we can prove 
P and (P ∨ Q) separately. To see why P is true, we are done beause we have a proof of P. To see
why P ∨ Q is true, we are done because its left side is exactly P, which we have a proof of.
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  assume ppq,
  cases ppq,
  exact ppq,
  exact (and.elim_left ppq),
  assume p,
  exact (or.inl p),
end

/-
Assume we have propositions P and Q. To see why P ∨ (P ∧ Q) ↔ P is true, it suffices to prove 
P ∨ (P ∧ Q) → P and P → P ∨ (P ∧ Q). To see why P ∨ (P ∧ Q) → P is true, assume we have a proof of
P ∨ (P ∧ Q). Now, we have two cases. In the first case, P is true, so that we are done because P 
is what we want to prove. In the second case, P ∧ Q is true, so that we are done because P
is exactly the left hand side of P ∧ Q.
To see why P → P ∨ (P ∧ Q), we assume P is true, and then are done because this is exactly the left side
of P ∨ (P ∧ Q).
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  assume pt,
  apply true.intro,
  assume t,
  exact (or.inr t),
end
/- 
Assume we have a proposition P. To see why P ∨ true ↔ true is true, we prove P ∨ true → true
and true → P ∨ true. To see why P ∨ true → true is true, assume P ∨ true is true. Then,
we apply the fact that we know true is true. To see why true → P ∨ true, we assume we have a proof of t.
Then, we are done because we have a proof for the right side of P ∨ true.
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pf,
  cases pf,
  exact pf,
  have pp : ¬ P ∧ P := false.elim pf,
  exact (and.elim_right pp),
  assume p,
  exact (or.inl p),
end

/- 
Assume we have a proposition P. To see why P ∨ false ↔ P is true, it suffices to prove 
P ∨ false → P and P → P ∨ false. To see why  P ∨ false → P is true, assume P ∨ false is true.
Then, we haave two cases. In the first case, we are done because we have a proof for P. In the second case,
we obtain a proof of ¬ P ∧ P from the fact that we have assumed false. Now, we are done because P is exactly
the right side of ¬ P ∧ P. To see why P → P ∨ false, assume P is true. Then, we have are done because we 
have a proof of the left side of P ∨ false.
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pt,
  exact (and.elim_left pt),
  assume p,
  apply and.intro _ _,
  exact p,
  apply true.intro,
end
/- 
Assume we have a proposition P. To see why P ∧ true ↔ P, it suffices to prove P ∧ true → P and 
P → P ∧ true. To see why P ∧ true → P, we are done because P is the left side of P ∧ true.
To see why P → P ∧ true, we assume P is true and then prove P and true separately. To see why
P is true, we are done because we have a proof of P. To see why true is true, we are done because
we know true is true. 
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume pf,
  exact (and.elim_right pf),
  assume f,
  apply and.intro _ _,
  have pp : ¬ P ∧ P := false.elim f,
  exact (and.elim_right pp),
  exact f,
end

/- 
Assume we have a propositio P. To see why P ∧ false ↔ false is true, we prove
P ∧ false → false and false → P ∧ false. To see why P ∧ false → false is true, we assume
P ∧ false is true. Then, we have prove false because it is the right side of P ∧ false.
To see why false → P ∧ false, we assume false and prove P and false separately.
To prove P, we can get a proof of ¬ P ∧ P from false. Now, we have a proof of P from the right
side of ¬ P ∧ P. To see prove false, we are done because we already have a proof of false.
-/


