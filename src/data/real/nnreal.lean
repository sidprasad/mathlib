/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.conditionally_complete_lattice.group
import algebra.algebra.basic
import algebra.order.nonneg.field
import algebra.order.field.canonical.basic
import data.real.pointwise
import tactic.positivity

/-!
# Nonnegative real numbers

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `ordered_comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `canonically_linear_ordered_add_monoid ℝ≥0`;
  - `archimedean ℝ≥0`;
  - `conditionally_complete_linear_order_bot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`. See `algebra/order/nonneg`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/

open_locale classical big_operators

/-- Nonnegative real numbers. -/
@[derive [
  strict_ordered_semiring, comm_monoid_with_zero, -- to ensure these instances are computable
  floor_semiring, comm_semiring, semiring,
  semilattice_inf, semilattice_sup,
  distrib_lattice, densely_ordered, order_bot,
  canonically_linear_ordered_semifield, linear_ordered_comm_group_with_zero, archimedean,
  linear_ordered_semiring, ordered_comm_semiring, canonically_ordered_comm_semiring,
  has_sub, has_ordered_sub, has_div, inhabited]]
def nnreal := {r : ℝ // 0 ≤ r}
localized "notation (name := nnreal) `ℝ≥0` := nnreal" in nnreal

namespace nnreal

instance : has_coe ℝ≥0 ℝ := ⟨subtype.val⟩

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/
@[simp] lemma val_eq_coe (n : ℝ≥0) : n.val = n := rfl

instance can_lift : can_lift ℝ ℝ≥0 coe (λ r, 0 ≤ r) := subtype.can_lift _

protected lemma eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m := subtype.eq

protected lemma eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
iff.intro nnreal.eq (congr_arg coe)

lemma ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
not_iff_not_of_iff $ nnreal.eq_iff

protected lemma «forall» {p : ℝ≥0 → Prop} : (∀ x : ℝ≥0, p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
subtype.forall

protected lemma «exists» {p : ℝ≥0 → Prop} : (∃ x : ℝ≥0, p x) ↔ ∃ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
subtype.exists

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def _root_.real.to_nnreal (r : ℝ) : ℝ≥0 := ⟨max r 0, le_max_right _ _⟩

lemma _root_.real.coe_to_nnreal (r : ℝ) (hr : 0 ≤ r) : (real.to_nnreal r : ℝ) = r :=
max_eq_left hr

lemma _root_.real.to_nnreal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.to_nnreal = ⟨r, hr⟩ :=
by simp_rw [real.to_nnreal, max_eq_left hr]

lemma _root_.real.le_coe_to_nnreal (r : ℝ) : r ≤ real.to_nnreal r :=
le_max_left r 0

lemma coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r := r.2
@[norm_cast]
theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ≥0) : ℝ) = a := rfl

example : has_zero ℝ≥0  := by apply_instance
example : has_one ℝ≥0   := by apply_instance
example : has_add ℝ≥0   := by apply_instance
noncomputable example : has_sub ℝ≥0   := by apply_instance
example : has_mul ℝ≥0   := by apply_instance
noncomputable example : has_inv ℝ≥0   := by apply_instance
noncomputable example : has_div ℝ≥0   := by apply_instance
example : has_le ℝ≥0    := by apply_instance
example : has_bot ℝ≥0   := by apply_instance
example : inhabited ℝ≥0 := by apply_instance
example : nontrivial ℝ≥0 := by apply_instance

protected lemma coe_injective : function.injective (coe : ℝ≥0 → ℝ) := subtype.coe_injective
@[simp, norm_cast] protected lemma coe_eq {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
nnreal.coe_injective.eq_iff
protected lemma coe_zero : ((0 : ℝ≥0) : ℝ) = 0 := rfl
protected lemma coe_one  : ((1 : ℝ≥0) : ℝ) = 1 := rfl
protected lemma coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ := rfl
protected lemma coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ := rfl
protected lemma coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ := rfl
protected lemma coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ := rfl
@[simp, norm_cast] protected lemma coe_bit0 (r : ℝ≥0) : ((bit0 r : ℝ≥0) : ℝ) = bit0 r := rfl
@[simp, norm_cast] protected lemma coe_bit1 (r : ℝ≥0) : ((bit1 r : ℝ≥0) : ℝ) = bit1 r := rfl
protected lemma coe_two : ((2 : ℝ≥0) : ℝ) = 2 := rfl

@[simp, norm_cast] protected lemma coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) :
  ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
max_eq_left $ le_sub_comm.2 $ by simp [show (r₂ : ℝ) ≤ r₁, from h]

@[simp, norm_cast] protected lemma coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 :=
by rw [← nnreal.coe_zero, nnreal.coe_eq]

@[simp, norm_cast] protected lemma coe_eq_one (r : ℝ≥0) : ↑r = (1 : ℝ) ↔ r = 1 :=
by rw [← nnreal.coe_one, nnreal.coe_eq]

lemma coe_ne_zero {r : ℝ≥0} : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by norm_cast

example : comm_semiring ℝ≥0 := by apply_instance

/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def to_real_hom : ℝ≥0 →+* ℝ :=
⟨coe, nnreal.coe_one, nnreal.coe_mul, nnreal.coe_zero, nnreal.coe_add⟩

@[simp] lemma coe_to_real_hom : ⇑to_real_hom = coe := rfl

section actions

/-- A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type*} [mul_action ℝ M] : mul_action ℝ≥0 M :=
mul_action.comp_hom M to_real_hom.to_monoid_hom

lemma smul_def {M : Type*} [mul_action ℝ M] (c : ℝ≥0) (x : M) :
  c • x = (c : ℝ) • x := rfl

instance {M N : Type*} [mul_action ℝ M] [mul_action ℝ N] [has_smul M N]
  [is_scalar_tower ℝ M N] : is_scalar_tower ℝ≥0 M N :=
{ smul_assoc := λ r, (smul_assoc (r : ℝ) : _)}

instance smul_comm_class_left {M N : Type*} [mul_action ℝ N] [has_smul M N]
  [smul_comm_class ℝ M N] : smul_comm_class ℝ≥0 M N :=
{ smul_comm := λ r, (smul_comm (r : ℝ) : _)}

instance smul_comm_class_right {M N : Type*} [mul_action ℝ N] [has_smul M N]
  [smul_comm_class M ℝ N] : smul_comm_class M ℝ≥0 N :=
{ smul_comm := λ m r, (smul_comm m (r : ℝ) : _)}

/-- A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type*} [add_monoid M] [distrib_mul_action ℝ M] : distrib_mul_action ℝ≥0 M :=
distrib_mul_action.comp_hom M to_real_hom.to_monoid_hom

/-- A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type*} [add_comm_monoid M] [module ℝ M] : module ℝ≥0 M :=
module.comp_hom M to_real_hom

/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
instance {A : Type*} [semiring A] [algebra ℝ A] : algebra ℝ≥0 A :=
{ smul := (•),
  commutes' := λ r x, by simp [algebra.commutes],
  smul_def' := λ r x, by simp [←algebra.smul_def (r : ℝ) x, smul_def],
  to_ring_hom := ((algebra_map ℝ A).comp (to_real_hom : ℝ≥0 →+* ℝ)) }

-- verify that the above produces instances we might care about
example : algebra ℝ≥0 ℝ := by apply_instance
example : distrib_mul_action ℝ≥0ˣ ℝ := by apply_instance

end actions

example : monoid_with_zero ℝ≥0 := by apply_instance
example : comm_monoid_with_zero ℝ≥0 := by apply_instance
noncomputable example : comm_group_with_zero ℝ≥0 := by apply_instance

@[simp, norm_cast] lemma coe_indicator {α} (s : set α) (f : α → ℝ≥0) (a : α) :
  ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (λ x, f x) a :=
(to_real_hom : ℝ≥0 →+ ℝ).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (r : ℝ≥0) (n : ℕ) : ((r^n : ℝ≥0) : ℝ) = r^n :=
to_real_hom.map_pow r n

@[simp, norm_cast] lemma coe_zpow (r : ℝ≥0) (n : ℤ) : ((r^n : ℝ≥0) : ℝ) = r^n :=
by cases n; simp

@[norm_cast] lemma coe_list_sum (l : list ℝ≥0) :
  ((l.sum : ℝ≥0) : ℝ) = (l.map coe).sum :=
to_real_hom.map_list_sum l

@[norm_cast] lemma coe_list_prod (l : list ℝ≥0) :
  ((l.prod : ℝ≥0) : ℝ) = (l.map coe).prod :=
to_real_hom.map_list_prod l

@[norm_cast] lemma coe_multiset_sum (s : multiset ℝ≥0) :
  ((s.sum : ℝ≥0) : ℝ) = (s.map coe).sum :=
to_real_hom.map_multiset_sum s

@[norm_cast] lemma coe_multiset_prod (s : multiset ℝ≥0) :
  ((s.prod : ℝ≥0) : ℝ) = (s.map coe).prod :=
to_real_hom.map_multiset_prod s

@[norm_cast] lemma coe_sum {α} {s : finset α} {f : α → ℝ≥0} :
  ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
to_real_hom.map_sum _ _

lemma _root_.real.to_nnreal_sum_of_nonneg {α} {s : finset α} {f : α → ℝ}
  (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  real.to_nnreal (∑ a in s, f a) = ∑ a in s, real.to_nnreal (f a) :=
begin
  rw [←nnreal.coe_eq, nnreal.coe_sum, real.coe_to_nnreal _ (finset.sum_nonneg hf)],
  exact finset.sum_congr rfl (λ x hxs, by rw real.coe_to_nnreal _ (hf x hxs)),
end

@[norm_cast] lemma coe_prod {α} {s : finset α} {f : α → ℝ≥0} :
  ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
to_real_hom.map_prod _ _

lemma _root_.real.to_nnreal_prod_of_nonneg {α} {s : finset α} {f : α → ℝ}
  (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  real.to_nnreal (∏ a in s, f a) = ∏ a in s, real.to_nnreal (f a) :=
begin
  rw [←nnreal.coe_eq, nnreal.coe_prod, real.coe_to_nnreal _ (finset.prod_nonneg hf)],
  exact finset.prod_congr rfl (λ x hxs, by rw real.coe_to_nnreal _ (hf x hxs)),
end

lemma nsmul_coe (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r:ℝ) :=
by norm_cast

@[simp, norm_cast] protected lemma coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
map_nat_cast to_real_hom n

noncomputable example : linear_order ℝ≥0 := by apply_instance

@[simp, norm_cast] protected lemma coe_le_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_lt_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_pos {r : ℝ≥0} : (0 : ℝ) < r ↔ 0 < r := iff.rfl

protected lemma coe_mono : monotone (coe : ℝ≥0 → ℝ) := λ _ _, nnreal.coe_le_coe.2

protected lemma _root_.real.to_nnreal_mono : monotone real.to_nnreal :=
λ x y h, max_le_max h (le_refl 0)

@[simp] lemma _root_.real.to_nnreal_coe {r : ℝ≥0} : real.to_nnreal r = r :=
nnreal.eq $ max_eq_left r.2

@[simp] lemma mk_coe_nat (n : ℕ) : @eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0) n :=
nnreal.eq (nnreal.coe_nat_cast n).symm

@[simp] lemma to_nnreal_coe_nat (n : ℕ) : real.to_nnreal n = n :=
nnreal.eq $ by simp [real.coe_to_nnreal]

/-- `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : galois_insertion real.to_nnreal coe :=
galois_insertion.monotone_intro nnreal.coe_mono real.to_nnreal_mono
  real.le_coe_to_nnreal (λ _, real.to_nnreal_coe)

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
example : order_bot ℝ≥0 := by apply_instance
example : partial_order ℝ≥0 := by apply_instance
noncomputable example : canonically_linear_ordered_add_monoid ℝ≥0 := by apply_instance
noncomputable example : linear_ordered_add_comm_monoid ℝ≥0 := by apply_instance
example : distrib_lattice ℝ≥0 := by apply_instance
example : semilattice_inf ℝ≥0 := by apply_instance
example : semilattice_sup ℝ≥0 := by apply_instance
noncomputable example : linear_ordered_semiring ℝ≥0 := by apply_instance
example : ordered_comm_semiring ℝ≥0 := by apply_instance
noncomputable example : linear_ordered_comm_monoid  ℝ≥0 := by apply_instance
noncomputable example : linear_ordered_comm_monoid_with_zero ℝ≥0 := by apply_instance
noncomputable example : linear_ordered_comm_group_with_zero ℝ≥0 := by apply_instance
example : canonically_ordered_comm_semiring ℝ≥0 := by apply_instance
example : densely_ordered ℝ≥0 := by apply_instance
example : no_max_order ℝ≥0 := by apply_instance

/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `set.Iic a`. -/
@[simps apply_coe_coe] def order_iso_Icc_zero_coe (a : ℝ≥0) : set.Icc (0 : ℝ) a ≃o set.Iic a :=
{ to_equiv := equiv.set.sep (set.Ici 0) (λ x, x ≤ a),
  map_rel_iff' := λ x y, iff.rfl }

@[simp] lemma order_iso_Icc_zero_coe_symm_apply_coe (a : ℝ≥0) (b : set.Iic a) :
  ((order_iso_Icc_zero_coe a).symm b : ℝ) = b :=
rfl

-- note we need the `@` to make the `has_mem.mem` have a sensible type
lemma coe_image {s : set ℝ≥0} : coe '' s = {x : ℝ | ∃ h : 0 ≤ x, @has_mem.mem (ℝ≥0) _ _ ⟨x, h⟩ s} :=
subtype.coe_image

lemma bdd_above_coe {s : set ℝ≥0} : bdd_above ((coe : ℝ≥0 → ℝ) '' s) ↔ bdd_above s :=
iff.intro
  (assume ⟨b, hb⟩, ⟨real.to_nnreal b, assume ⟨y, hy⟩ hys, show y ≤ max b 0, from
    le_max_of_le_left $ hb $ set.mem_image_of_mem _ hys⟩)
  (assume ⟨b, hb⟩, ⟨b, assume y ⟨x, hx, eq⟩, eq ▸ hb hx⟩)

lemma bdd_below_coe (s : set ℝ≥0) : bdd_below ((coe : ℝ≥0 → ℝ) '' s) :=
⟨0, assume r ⟨q, _, eq⟩, eq ▸ q.2⟩

noncomputable instance : conditionally_complete_linear_order_bot ℝ≥0 :=
nonneg.conditionally_complete_linear_order_bot real.Sup_empty.le

@[norm_cast] lemma coe_Sup (s : set ℝ≥0) : (↑(Sup s) : ℝ) = Sup ((coe : ℝ≥0 → ℝ) '' s) :=
eq.symm $ @subset_Sup_of_within ℝ (set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s $
  real.Sup_nonneg _ $ λ y ⟨x, _, hy⟩, hy ▸ x.2

@[norm_cast] lemma coe_supr {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, (s i) :=
by rw [supr, supr, coe_Sup, set.range_comp]

@[norm_cast] lemma coe_Inf (s : set ℝ≥0) : (↑(Inf s) : ℝ) = Inf ((coe : ℝ≥0 → ℝ) '' s) :=
eq.symm $ @subset_Inf_of_within ℝ (set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s $
  real.Inf_nonneg _ $ λ y ⟨x, _, hy⟩, hy ▸ x.2

@[simp] lemma Inf_empty : Inf (∅ : set ℝ≥0) = 0 :=
by rw [← nnreal.coe_eq_zero, coe_Inf, set.image_empty, real.Inf_empty]

@[norm_cast] lemma coe_infi {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, (s i) :=
by rw [infi, infi, coe_Inf, set.range_comp]

lemma le_infi_add_infi {ι ι' : Sort*} [nonempty ι] [nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
  {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j :=
begin
  rw [← nnreal.coe_le_coe, nnreal.coe_add, coe_infi, coe_infi],
  exact le_cinfi_add_cinfi h
end

example : archimedean ℝ≥0 := by apply_instance

-- TODO: why are these three instances necessary? why aren't they inferred?
instance covariant_add : covariant_class ℝ≥0 ℝ≥0 (+) (≤) :=
ordered_add_comm_monoid.to_covariant_class_left ℝ≥0

instance contravariant_add : contravariant_class ℝ≥0 ℝ≥0 (+) (<) :=
ordered_cancel_add_comm_monoid.to_contravariant_class_left ℝ≥0

instance covariant_mul : covariant_class ℝ≥0 ℝ≥0 (*) (≤) :=
ordered_comm_monoid.to_covariant_class_left ℝ≥0

-- Why isn't `nnreal.contravariant_add` inferred?
lemma le_of_forall_pos_le_add {a b : ℝ≥0} (h : ∀ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
@le_of_forall_pos_le_add _ _ _ _ _ _ nnreal.contravariant_add _ _ h

lemma lt_iff_exists_rat_btwn (a b : ℝ≥0) :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < real.to_nnreal q ∧ real.to_nnreal q < b) :=
iff.intro
  (assume (h : (↑a:ℝ) < (↑b:ℝ)),
    let ⟨q, haq, hqb⟩ := exists_rat_btwn h in
    have 0 ≤ (q : ℝ), from le_trans a.2 $ le_of_lt haq,
    ⟨q, rat.cast_nonneg.1 this,
      by simp [real.coe_to_nnreal _ this, nnreal.coe_lt_coe.symm, haq, hqb]⟩)
  (assume ⟨q, _, haq, hqb⟩, lt_trans haq hqb)

lemma bot_eq_zero : (⊥ : ℝ≥0) = 0 := rfl

lemma mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = (a * b) ⊔ (a * c) :=
mul_max_of_nonneg _ _ $ zero_le a

lemma sup_mul (a b c : ℝ≥0) : (a ⊔ b) * c = (a * c) ⊔ (b * c) :=
max_mul_of_nonneg _ _ $ zero_le c

lemma mul_finset_sup {α} (r : ℝ≥0) (s : finset α) (f : α → ℝ≥0) :
  r * s.sup f = s.sup (λ a, r * f a) :=
(finset.comp_sup_eq_sup_comp _ (nnreal.mul_sup r) (mul_zero r))

lemma finset_sup_mul {α} (s : finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
  s.sup f * r = s.sup (λ a, f a * r) :=
(finset.comp_sup_eq_sup_comp (* r) (λ x y, nnreal.sup_mul x y r) (zero_mul r))

lemma finset_sup_div {α} {f : α → ℝ≥0} {s : finset α} (r : ℝ≥0) :
  s.sup f / r = s.sup (λ a, f a / r) :=
by simp only [div_eq_inv_mul, mul_finset_sup]

@[simp, norm_cast] lemma coe_max (x y : ℝ≥0) :
  ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
nnreal.coe_mono.map_max

@[simp, norm_cast] lemma coe_min (x y : ℝ≥0) :
  ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
nnreal.coe_mono.map_min

@[simp] lemma zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) := q.2

end nnreal

namespace real

section to_nnreal

@[simp] lemma to_nnreal_zero : real.to_nnreal 0 = 0 :=
by simp [real.to_nnreal]; refl

@[simp] lemma to_nnreal_one : real.to_nnreal 1 = 1 :=
by simp [real.to_nnreal, max_eq_left (zero_le_one : (0 :ℝ) ≤ 1)]; refl

@[simp] lemma to_nnreal_pos {r : ℝ} : 0 < real.to_nnreal r ↔ 0 < r :=
by simp [real.to_nnreal, nnreal.coe_lt_coe.symm, lt_irrefl]

@[simp] lemma to_nnreal_eq_zero {r : ℝ} : real.to_nnreal r = 0 ↔ r ≤ 0 :=
by simpa [-to_nnreal_pos] using (not_iff_not.2 (@to_nnreal_pos r))

lemma to_nnreal_of_nonpos {r : ℝ} : r ≤ 0 → real.to_nnreal r = 0 :=
to_nnreal_eq_zero.2

@[simp] lemma coe_to_nnreal' (r : ℝ) : (real.to_nnreal r : ℝ) = max r 0 := rfl

@[simp] lemma to_nnreal_le_to_nnreal_iff {r p : ℝ} (hp : 0 ≤ p) :
  real.to_nnreal r ≤ real.to_nnreal p ↔ r ≤ p :=
by simp [nnreal.coe_le_coe.symm, real.to_nnreal, hp]

@[simp] lemma to_nnreal_eq_to_nnreal_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  real.to_nnreal r = real.to_nnreal p ↔ r = p :=
by simp [← nnreal.coe_eq, coe_to_nnreal, hr, hp]

@[simp] lemma to_nnreal_lt_to_nnreal_iff' {r p : ℝ} :
  real.to_nnreal r < real.to_nnreal p ↔ r < p ∧ 0 < p :=
nnreal.coe_lt_coe.symm.trans max_lt_max_left_iff

lemma to_nnreal_lt_to_nnreal_iff {r p : ℝ} (h : 0 < p) :
  real.to_nnreal r < real.to_nnreal p ↔ r < p :=
to_nnreal_lt_to_nnreal_iff'.trans (and_iff_left h)

lemma to_nnreal_lt_to_nnreal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
  real.to_nnreal r < real.to_nnreal p ↔ r < p :=
to_nnreal_lt_to_nnreal_iff'.trans ⟨and.left, λ h, ⟨h, lt_of_le_of_lt hr h⟩⟩

@[simp] lemma to_nnreal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  real.to_nnreal (r + p) = real.to_nnreal r + real.to_nnreal p :=
nnreal.eq $ by simp [real.to_nnreal, hr, hp, add_nonneg]

lemma to_nnreal_add_to_nnreal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  real.to_nnreal r + real.to_nnreal p = real.to_nnreal (r + p) :=
(real.to_nnreal_add hr hp).symm

lemma to_nnreal_le_to_nnreal {r p : ℝ} (h : r ≤ p) :
  real.to_nnreal r ≤ real.to_nnreal p :=
real.to_nnreal_mono h

lemma to_nnreal_add_le {r p : ℝ} :
  real.to_nnreal (r + p) ≤ real.to_nnreal r + real.to_nnreal p :=
nnreal.coe_le_coe.1 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) nnreal.zero_le_coe

lemma to_nnreal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : real.to_nnreal r ≤ p ↔ r ≤ ↑p :=
nnreal.gi.gc r p

lemma le_to_nnreal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ real.to_nnreal p ↔ ↑r ≤ p :=
by rw [← nnreal.coe_le_coe, real.coe_to_nnreal p hp]

lemma le_to_nnreal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ real.to_nnreal p ↔ ↑r ≤ p :=
(le_or_lt 0 p).elim le_to_nnreal_iff_coe_le $ λ hp,
  by simp only [(hp.trans_le r.coe_nonneg).not_le, to_nnreal_eq_zero.2 hp.le, hr.not_le]

lemma to_nnreal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : real.to_nnreal r < p ↔ r < ↑p :=
by rw [← nnreal.coe_lt_coe, real.coe_to_nnreal r ha]

lemma lt_to_nnreal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < real.to_nnreal p ↔ ↑r < p :=
begin
  cases le_total 0 p,
  { rw [← nnreal.coe_lt_coe, real.coe_to_nnreal p h] },
  { rw [to_nnreal_eq_zero.2 h], split,
    { intro, have := not_lt_of_le (zero_le r), contradiction },
    { intro rp, have : ¬(p ≤ 0) := not_le_of_lt (lt_of_le_of_lt (nnreal.coe_nonneg _) rp),
      contradiction } }
end

@[simp] lemma to_nnreal_bit0 (r : ℝ) : real.to_nnreal (bit0 r) = bit0 (real.to_nnreal r) :=
begin
  cases le_total r 0 with hr hr,
  { rw [to_nnreal_of_nonpos hr, to_nnreal_of_nonpos, bit0_zero],
    exact add_nonpos hr hr },
  { exact to_nnreal_add hr hr }
end

@[simp] lemma to_nnreal_bit1 {r : ℝ} (hr : 0 ≤ r) :
  real.to_nnreal (bit1 r) = bit1 (real.to_nnreal r) :=
(real.to_nnreal_add (by simp [hr]) zero_le_one).trans (by simp [bit1])

lemma to_nnreal_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ n).to_nnreal = (x.to_nnreal) ^ n :=
by rw [← nnreal.coe_eq, nnreal.coe_pow, real.coe_to_nnreal _ (pow_nonneg hx _),
  real.coe_to_nnreal x hx]

end to_nnreal

end real

open real

namespace nnreal

section mul

lemma mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : (a * b = a * c ↔ b = c) :=
by rw [mul_eq_mul_left_iff, or_iff_left h]

lemma _root_.real.to_nnreal_mul {p q : ℝ} (hp : 0 ≤ p) :
  real.to_nnreal (p * q) = real.to_nnreal p * real.to_nnreal q :=
begin
  cases le_total 0 q with hq hq,
  { apply nnreal.eq,
    simp [real.to_nnreal, hp, hq, max_eq_left, mul_nonneg] },
  { have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq,
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, mul_zero] }
end

end mul

section pow

lemma pow_antitone_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) :
  a ^ n ≤ a ^ m :=
pow_le_pow_of_le_one (zero_le a) a1 mn

lemma exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) : ∃ n : ℕ, b ^ n < a :=
by simpa only [← coe_pow, nnreal.coe_lt_coe]
  using exists_pow_lt_of_lt_one (nnreal.coe_pos.2 ha) (nnreal.coe_lt_coe.2 hb)

lemma exists_mem_Ico_zpow
  {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
  ∃ n : ℤ, x ∈ set.Ico (y ^ n) (y ^ (n + 1)) :=
begin
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n ≤ x ∧ (x : ℝ) < y ^ (n + 1) :=
    exists_mem_Ico_zpow (bot_lt_iff_ne_bot.mpr hx) hy,
  rw ← nnreal.coe_zpow at hn h'n,
  exact ⟨n, hn, h'n⟩,
end

lemma exists_mem_Ioc_zpow
  {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
  ∃ n : ℤ, x ∈ set.Ioc (y ^ n) (y ^ (n + 1)) :=
begin
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n < x ∧ (x : ℝ) ≤ y ^ (n + 1) :=
    exists_mem_Ioc_zpow (bot_lt_iff_ne_bot.mpr hx) hy,
  rw ← nnreal.coe_zpow at hn h'n,
  exact ⟨n, hn, h'n⟩,
end

end pow

section sub
/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas
about `has_ordered_sub` in the file `algebra.order.sub`. See also `mul_tsub` and `tsub_mul`. -/

lemma sub_def {r p : ℝ≥0} : r - p = real.to_nnreal (r - p) := rfl

lemma coe_sub_def {r p : ℝ≥0} : ↑(r - p) = max (r - p : ℝ) 0 := rfl

noncomputable example : has_ordered_sub ℝ≥0 := by apply_instance

lemma sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c := tsub_div _ _ _

end sub

section inv

lemma sum_div {ι} (s : finset ι) (f : ι → ℝ≥0) (b : ℝ≥0) :
  (∑ i in s, f i) / b = ∑ i in s, (f i / b) :=
finset.sum_div

@[simp] lemma inv_pos {r : ℝ≥0} : 0 < r⁻¹ ↔ 0 < r := inv_pos

lemma div_pos {r p : ℝ≥0} (hr : 0 < r) (hp : 0 < p) : 0 < r / p := div_pos hr hp

lemma div_self_le (r : ℝ≥0) : r / r ≤ 1 := div_self_le_one r

@[simp] lemma inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
by rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]

lemma inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p :=
by by_cases r = 0; simp [*, inv_le]

@[simp] lemma le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : (r ≤ p⁻¹ ↔ r * p ≤ 1) :=
by rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

@[simp] lemma lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : (r < p⁻¹ ↔ r * p < 1) :=
by rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

lemma mul_le_iff_le_inv {a b r : ℝ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
have 0 < r, from lt_of_le_of_ne (zero_le r) hr.symm,
by rw [← mul_le_mul_left (inv_pos.mpr this), ← mul_assoc, inv_mul_cancel hr, one_mul]

lemma le_div_iff_mul_le {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b := le_div_iff₀ hr

lemma div_le_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r := div_le_iff₀ hr

lemma div_le_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
@div_le_iff' ℝ _ a r b $ pos_iff_ne_zero.2 hr

lemma div_le_of_le_mul {a b c : ℝ≥0} (h : a ≤ b * c) : a / c ≤ b :=
if h0 : c = 0 then by simp [h0] else (div_le_iff h0).2 h

lemma div_le_of_le_mul' {a b c : ℝ≥0} (h : a ≤ b * c) : a / b ≤ c :=
div_le_of_le_mul $ mul_comm b c ▸ h

lemma le_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
@le_div_iff ℝ _ a b r $ pos_iff_ne_zero.2 hr

lemma le_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
@le_div_iff' ℝ _ a b r $ pos_iff_ne_zero.2 hr

lemma div_lt_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
lt_iff_lt_of_le_iff_le (le_div_iff hr)

lemma div_lt_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
lt_iff_lt_of_le_iff_le (le_div_iff' hr)

lemma lt_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
lt_iff_lt_of_le_iff_le (div_le_iff hr)

lemma lt_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
lt_iff_lt_of_le_iff_le (div_le_iff' hr)

lemma mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
begin
  refine (lt_div_iff $ λ hr, false.elim _).1 h,
  subst r,
  simpa using h
end

lemma div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) :
  a / b ≤ a / c :=
begin
  by_cases a0 : a = 0,
  { rw [a0, zero_div, zero_div] },
  { cases a with a ha,
    replace a0 : 0 < a := lt_of_le_of_ne ha (ne_of_lt (zero_lt_iff.mpr a0)),
    exact (div_le_div_left a0 b0 c0).mpr cb }
end

lemma div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
  a / b ≤ a / c ↔ c ≤ b :=
div_le_div_left a0 b0 c0

lemma le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀a<1, a * x ≤ y) : x ≤ y :=
le_of_forall_ge_of_dense $ assume a ha,
  have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha),
  have hx' : x⁻¹ ≠ 0, by rwa [(≠), inv_eq_zero],
  have a * x⁻¹ < 1, by rwa [← lt_inv_iff_mul_lt hx', inv_inv],
  have (a * x⁻¹) * x ≤ y, from h _ this,
  by rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this

lemma div_add_div_same (a b c : ℝ≥0) : a / c + b / c = (a + b) / c := div_add_div_same _ _ _

lemma half_pos {a : ℝ≥0} (h : 0 < a) : 0 < a / 2 := half_pos h

lemma add_halves (a : ℝ≥0) : a / 2 + a / 2 = a := add_halves _

lemma half_le_self (a : ℝ≥0) : a / 2 ≤ a := half_le_self bot_le

lemma half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a := half_lt_self h.bot_lt

lemma two_inv_lt_one : (2⁻¹:ℝ≥0) < 1 := two_inv_lt_one

lemma div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 :=
begin
  rwa [div_lt_iff, one_mul],
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
end

@[field_simps] lemma div_add_div (a : ℝ≥0) {b : ℝ≥0} (c : ℝ≥0) {d : ℝ≥0}
  (hb : b ≠ 0) (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) :=
div_add_div _ _ hb hd

@[field_simps] lemma add_div' (a b c : ℝ≥0) (hc : c ≠ 0) :
  b + a / c = (b * c + a) / c :=
add_div' _ _ _ hc

@[field_simps] lemma div_add' (a b c : ℝ≥0) (hc : c ≠ 0) :
  a / c + b = (a + b * c) / c :=
div_add' _ _ _ hc

lemma _root_.real.to_nnreal_inv {x : ℝ} :
  real.to_nnreal x⁻¹ = (real.to_nnreal x)⁻¹ :=
begin
  by_cases hx : 0 ≤ x,
  { nth_rewrite 0 ← real.coe_to_nnreal x hx,
    rw [←nnreal.coe_inv, real.to_nnreal_coe], },
  { have hx' := le_of_not_ge hx,
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')], },
end

lemma _root_.real.to_nnreal_div {x y : ℝ} (hx : 0 ≤ x) :
  real.to_nnreal (x / y) = real.to_nnreal x / real.to_nnreal y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ← real.to_nnreal_inv, ← real.to_nnreal_mul hx]

lemma _root_.real.to_nnreal_div' {x y : ℝ} (hy : 0 ≤ y) :
  real.to_nnreal (x / y) = real.to_nnreal x / real.to_nnreal y :=
by rw [div_eq_inv_mul, div_eq_inv_mul, real.to_nnreal_mul (inv_nonneg.2 hy), real.to_nnreal_inv]

lemma inv_lt_one_iff {x : ℝ≥0} (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x :=
by rwa [← one_div, div_lt_iff hx, one_mul]

lemma inv_lt_one {x : ℝ≥0} (hx : 1 < x) : x⁻¹ < 1 := inv_lt_one hx

lemma zpow_pos {x : ℝ≥0} (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n :=
begin
  cases n,
  { simp [pow_pos hx.bot_lt _] },
  { simp [pow_pos hx.bot_lt _] }
end

lemma inv_lt_inv_iff {x y : ℝ≥0} (hx : x ≠ 0) (hy : y ≠ 0) : y⁻¹ < x⁻¹ ↔ x < y := inv_lt_inv₀ hy hx

lemma inv_lt_inv {x y : ℝ≥0} (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
(inv_lt_inv_iff hx ((bot_le.trans_lt h).ne')).2 h

end inv

@[simp] lemma abs_eq (x : ℝ≥0) : |(x : ℝ)| = x :=
abs_of_nonneg x.property

section csupr
open set

variables {ι : Sort*} {f : ι → ℝ≥0}

lemma le_to_nnreal_of_coe_le {x : ℝ≥0} {y : ℝ} (h : ↑x ≤ y) : x ≤ y.to_nnreal :=
(le_to_nnreal_iff_coe_le $ x.2.trans h).2 h

lemma Sup_of_not_bdd_above {s : set ℝ≥0} (hs : ¬bdd_above s) : has_Sup.Sup s = 0 :=
begin
  rw [← bdd_above_coe] at hs,
  rw [← nnreal.coe_eq, coe_Sup],
  exact Sup_of_not_bdd_above hs,
end

lemma supr_of_not_bdd_above (hf : ¬ bdd_above (range f)) : (⨆ i, f i) = 0 :=
Sup_of_not_bdd_above hf

lemma infi_empty [is_empty ι] (f : ι → ℝ≥0) : (⨅ i, f i) = 0 :=
by { rw [← nnreal.coe_eq, coe_infi], exact real.cinfi_empty _, }

@[simp] lemma infi_const_zero {α : Sort*} : (⨅ i : α, (0 : ℝ≥0)) = 0 :=
by { rw [← nnreal.coe_eq, coe_infi], exact real.cinfi_const_zero, }

lemma infi_mul (f : ι → ℝ≥0) (a : ℝ≥0)  : infi f * a = ⨅ i, f i * a :=
begin
  rw [← nnreal.coe_eq, nnreal.coe_mul, coe_infi, coe_infi],
  exact real.infi_mul_of_nonneg (nnreal.coe_nonneg _) _,
end

lemma mul_infi (f : ι → ℝ≥0) (a : ℝ≥0) : a * infi f = ⨅ i, a * f i :=
by simpa only [mul_comm] using infi_mul f a

lemma mul_supr (f : ι → ℝ≥0) (a : ℝ≥0) : a * (⨆ i, f i) = ⨆ i, a * f i :=
begin
  rw [← nnreal.coe_eq, nnreal.coe_mul, nnreal.coe_supr, nnreal.coe_supr],
  exact real.mul_supr_of_nonneg (nnreal.coe_nonneg _) _,
end

lemma supr_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a :=
by { rw [mul_comm, mul_supr], simp_rw [mul_comm] }

lemma supr_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a :=
by simp only [div_eq_mul_inv, supr_mul]

variable [nonempty ι]

lemma le_mul_infi {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * infi h :=
by { rw [mul_infi], exact le_cinfi H }

lemma mul_supr_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * supr h ≤ a :=
by { rw [mul_supr], exact csupr_le H }

lemma le_infi_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ infi g * h :=
by { rw infi_mul, exact le_cinfi H }

lemma supr_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : supr g * h ≤ a :=
by { rw supr_mul, exact csupr_le H }

lemma le_infi_mul_infi {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
  a ≤ infi g * infi h :=
le_infi_mul  $ λ i, le_mul_infi $ H i

lemma supr_mul_supr_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
  supr g * supr h ≤ a :=
supr_mul_le $ λ i, mul_supr_le $ H _

end csupr

end nnreal

namespace set
namespace ord_connected

variables {s : set ℝ} {t : set ℝ≥0}

lemma preimage_coe_nnreal_real (h : s.ord_connected) : (coe ⁻¹' s : set ℝ≥0).ord_connected :=
h.preimage_mono nnreal.coe_mono

lemma image_coe_nnreal_real (h : t.ord_connected) : (coe '' t : set ℝ).ord_connected :=
⟨ball_image_iff.2 $ λ x hx, ball_image_iff.2 $ λ y hy z hz,
  ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩

lemma image_real_to_nnreal (h : s.ord_connected) : (real.to_nnreal '' s).ord_connected :=
begin
  refine ⟨ball_image_iff.2 $ λ x hx, ball_image_iff.2 $ λ y hy z hz, _⟩,
  cases le_total y 0 with hy₀ hy₀,
  { rw [mem_Icc, real.to_nnreal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz,
    exact ⟨y, hy, (to_nnreal_of_nonpos hy₀).trans hz.2.symm⟩ },
  { lift y to ℝ≥0 using hy₀,
    rw [to_nnreal_coe] at hz,
    exact ⟨z, h.out hx hy ⟨to_nnreal_le_iff_le_coe.1 hz.1, hz.2⟩, to_nnreal_coe⟩ }
end

lemma preimage_real_to_nnreal (h : t.ord_connected) : (real.to_nnreal ⁻¹' t).ord_connected :=
h.preimage_mono real.to_nnreal_mono

end ord_connected
end set

namespace real

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot] def nnabs : ℝ →*₀ ℝ≥0 :=
{ to_fun := λ x, ⟨|x|, abs_nonneg x⟩,
  map_zero' := by { ext, simp },
  map_one' := by { ext, simp },
  map_mul' := λ x y, by { ext, simp [abs_mul] } }

@[norm_cast, simp] lemma coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
rfl

@[simp] lemma nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = to_nnreal x :=
by { ext, simp [coe_to_nnreal x h, abs_of_nonneg h] }

lemma nnabs_coe (x : ℝ≥0) : nnabs x = x := by simp

lemma coe_to_nnreal_le (x : ℝ) : (to_nnreal x : ℝ) ≤ |x| :=
max_le (le_abs_self _) (abs_nonneg _)

lemma cast_nat_abs_eq_nnabs_cast (n : ℤ) :
  (n.nat_abs : ℝ≥0) = nnabs n :=
by { ext, rw [nnreal.coe_nat_cast, int.cast_nat_abs, real.coe_nnabs] }

end real

namespace tactic
open positivity

private lemma nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ) := nnreal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity]
meta def positivity_coe_nnreal_real : expr → tactic strictness
| `(@coe _ _ %%inst %%a) := do
  unify inst `(@coe_to_lift _ _ $ @coe_base _ _ nnreal.real.has_coe),
  strictness_a ← core a,
  match strictness_a with
  | positive p := positive <$> mk_app ``nnreal_coe_pos [p]
  | _ := nonnegative <$> mk_app ``nnreal.coe_nonneg [a]
  end
| e := pp e >>= fail ∘ format.bracket "The expression "
         " is not of the form `(r : ℝ)` for `r : ℝ≥0`"

end tactic
