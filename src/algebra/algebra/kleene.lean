
/-
Copyright (c) 2022 Siddhartha Prasad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad.
-/



import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.rcases
import tactic.rewrite



/-!
# Kleene Algebras

This file defines Kleene algebras, which are used extensively in theory of computation.

A Kleene algebra is an idempotent semiring with an additional unary operator
called a Kleene star (⋆).

## References

* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleenealgebra

## Tags

kleene algebra

-/


namespace isemiring


universe u

variables {α : Type u}

/--
An isemiring is a semiring with the additional property that the addition (+)
operation is idempotent.

For some idempotent semiring S,  ∀ x ∈ S, `x + x = x`.

Additionally, the binary relation ≤ defines a partial order on isemirings.
where, a ≤ b ↔ a + b = b

-/

class isemiring  (α : Type u) extends semiring α, partial_order α :=
(idem_add : ∀ a : α, a + a = a)
(le_def : ∀ a b : α, a ≤ b ↔ a + b = b)

variables [isemiring α] {a b c: α}


/--  a = b iff a ≤ b and b ≤ a --/
lemma ineq_of_eq : a = b ↔ a ≤ b ∧ b ≤ a :=
  begin
    apply iff.intro,
    {
      intro h,
      exact antisymm_iff.mpr h,
    },
    {
      intro h,
      exact le_antisymm_iff.mpr h,
    }
  end


/-- The addition operator on isemirings is monotonic. --/
lemma le_of_add : ∀ x y : α, x ≤ x + y :=
begin
  intros x y,
  apply iff.elim_right (isemiring.le_def x (x + y)),
  have : x + (x + y) = (x + x) + y := by exact (add_assoc x x y).symm,
  rw [this],
  rw (isemiring.idem_add x),
end

/-- If c is the supremum of a and b with respect to ≤, then c
is also the supremum of a + b. -/
lemma supremum_of_add : ∀ a b c : α, a ≤ c → b ≤ c → (a + b) ≤ c
:=
begin
  intros a b c h₁ h₂,
  have ha : a ≤ a + b := by exact le_of_add a b,
  have hb : b ≤ a + b :=
  begin
    rw [add_comm a b],
    exact le_of_add b a,
  end,


  have ha₁ : a + c = c := by exact (isemiring.le_def a c).mp h₁,
  have hb₁ : b +c = c := by exact (isemiring.le_def b c).mp h₂,

  have h_inter : (a + c) + (b + c) = c :=
  begin
    simp [ha₁, hb₁],
    exact (isemiring.idem_add c),
  end,

  have h₃: (a + b) + c = c :=
  begin
    have hassoc : (a + c) + (b + c) = (a + b) + (c + c) := by finish,
    simp [isemiring.idem_add c] at hassoc,
    simp [hassoc] at h_inter,
    exact h_inter,
    end,
    exact (isemiring.le_def (a + b) c).mpr h₃
end

/-- 0 is the bottom element of an isemiring. --/
lemma partial_order_of_zero  : ∀ a : α,  (0 : α) ≤  a :=
begin
  intro a,
  have : 0 + a = a := by exact zero_add a,
  simp [isemiring.le_def],
end

/--

 c is the supremum of a and b with respect to ≤ iff
 c is the supremum of a + b.

--/
lemma ineq_of_add : a + b ≤ c ↔ a ≤ c ∧ b ≤ c  :=
begin

  apply iff.intro,
  {
    intro h,
    apply and.intro,
    {
      have h_ineq₁ : a ≤ a + b := le_of_add a b,
      exact le_trans h_ineq₁ h,
    },
    {
      have h_ineq₂ : b ≤ b + a :=  le_of_add b a,
      rw ←(add_comm a b) at h_ineq₂,
      exact le_trans h_ineq₂ h,
    }
  },
  {
    have h₁ := supremum_of_add a b c,
    intros h,
    cases' h,
    exact h₁ left right,
  }
end


/--
  Multiplication preserves the partial order defined by ≤.
--/
lemma partial_order_of_mul : a ≤ b → (c*a) ≤ (c*b)
:=
begin
  intro h,
  have h_le : b = (a + b) := by exact eq.symm ((isemiring.le_def a b).mp h),
  have h_distr : c * (a + b) = (c* a) + (c * b) := by exact mul_add c a b,

  rw [h_le, h_distr, isemiring.le_def],
  rw (add_assoc (c * a) (c * a) (c * b)).symm,
  rw isemiring.idem_add (c * a),
end


end isemiring

namespace kleene_algebra

universe u
variables {α : Type u}

/--
A Kleene Algebra is an isemiring with an additional unary operator (star), that
satisfies the following properties:

1 + a* (a ∗) ≤ (a ∗)
1 + (a ∗) * a ≤ (a ∗)

a*c + b ≤ c ⇒ (a ∗) * b ≤ c
c*a + b ≤ c ⇒ b * (a ∗) ≤ c ,

-/
class kleene_algebra (α : Type u) extends isemiring.isemiring α :=
  (star :  α → α)
  (star_unfold_right : ∀ a : α, (1 : α) + a * (star a) ≤  star a)
  (star_unfold_left :  ∀ a : α, (1 : α) + (star a) * a ≤ star a)
  (star_inf_right : ∀ a b c: α,  a*c + b ≤ c → (star a) * b ≤ c)
  (star_inf_left : ∀ a b c: α,  c*a + b ≤ c → b*(star a) ≤ c)

notation  a`∗` := kleene_algebra.star a

end kleene_algebra
