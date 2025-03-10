/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.dfinsupp.basic
import group_theory.submonoid.operations
/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `direct_sum`.
This notation is in the `direct_sum` locale, accessible after `open_locale direct_sum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

open_locale big_operators

universes u v w u₁

variables (ι : Type v) [dec_ι : decidable_eq ι] (β : ι → Type w)

/-- `direct_sum β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open_locale direct_sum` will enable the notation `⨁ i, β i` for `direct_sum β`. -/
@[derive [add_comm_monoid, inhabited]]
def direct_sum [Π i, add_comm_monoid (β i)] : Type* := Π₀ i, β i

instance [Π i, add_comm_monoid (β i)] : has_coe_to_fun (direct_sum ι β) (λ _, Π i : ι, β i) :=
dfinsupp.has_coe_to_fun

localized "notation (name := direct_sum)
  `⨁` binders `, ` r:(scoped f, direct_sum _ f) := r" in direct_sum

namespace direct_sum

variables {ι}

section add_comm_group

variables [Π i, add_comm_group (β i)]

instance : add_comm_group (direct_sum ι β) := dfinsupp.add_comm_group

variables {β}
@[simp] lemma sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i := rfl

end add_comm_group

variables [Π i, add_comm_monoid (β i)]

@[simp] lemma zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 := rfl

variables {β}
@[simp] lemma add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i := rfl

variables (β)
include dec_ι

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk (s : finset ι) : (Π i : (↑s : set ι), β i.1) →+ ⨁ i, β i :=
{ to_fun := dfinsupp.mk s,
  map_add' := λ _ _, dfinsupp.mk_add,
  map_zero' := dfinsupp.mk_zero, }

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of (i : ι) : β i →+ ⨁ i, β i :=
dfinsupp.single_add_hom β i

@[simp] lemma of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
dfinsupp.single_eq_same

lemma of_eq_of_ne (i j : ι) (x : β i) (h : i ≠ j) : (of _ i x) j = 0 :=
dfinsupp.single_eq_of_ne h

@[simp] lemma support_zero [Π (i : ι) (x : β i), decidable (x ≠ 0)] :
  (0 : ⨁ i, β i).support = ∅ := dfinsupp.support_zero

@[simp] lemma support_of [Π (i : ι) (x : β i), decidable (x ≠ 0)]
  (i : ι) (x : β i) (h : x ≠ 0) :
  (of _ i x).support = {i} := dfinsupp.support_single_ne_zero h

lemma support_of_subset [Π (i : ι) (x : β i), decidable (x ≠ 0)] {i : ι} {b : β i} :
  (of _ i b).support ⊆ {i} := dfinsupp.support_single_subset

lemma sum_support_of [Π (i : ι) (x : β i), decidable (x ≠ 0)] (x : ⨁ i, β i) :
  ∑ i in x.support, of β i (x i) = x := dfinsupp.sum_single

variables {β}

theorem mk_injective (s : finset ι) : function.injective (mk β s) :=
dfinsupp.mk_injective s

theorem of_injective (i : ι) : function.injective (of β i) :=
dfinsupp.single_injective

@[elab_as_eliminator]
protected theorem induction_on {C : (⨁ i, β i) → Prop}
  (x : ⨁ i, β i) (H_zero : C 0)
  (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
lemma add_hom_ext {γ : Type*} [add_monoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
  (H : ∀ (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g :=
dfinsupp.add_hom_ext H

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext] lemma add_hom_ext' {γ : Type*} [add_monoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
  (H : ∀ (i : ι), f.comp (of _ i) = g.comp (of _ i)) : f = g :=
add_hom_ext $ λ i, add_monoid_hom.congr_fun $ H i

variables {γ : Type u₁} [add_comm_monoid γ]

section to_add_monoid

variables (φ : Π i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

/-- `to_add_monoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def to_add_monoid : (⨁ i, β i) →+ γ :=
(dfinsupp.lift_add_hom φ)

@[simp] lemma to_add_monoid_of (i) (x : β i) : to_add_monoid φ (of β i x) = φ i x :=
dfinsupp.lift_add_hom_apply_single φ i x

theorem to_add_monoid.unique (f : ⨁ i, β i) :
  ψ f = to_add_monoid (λ i, ψ.comp (of β i)) f :=
by {congr, ext, simp [to_add_monoid, of]}

end to_add_monoid

section from_add_monoid

/-- `from_add_monoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def from_add_monoid : (⨁ i, γ →+ β i) →+ (γ →+ ⨁ i, β i) :=
to_add_monoid $ λ i, add_monoid_hom.comp_hom (of β i)

@[simp] lemma from_add_monoid_of (i : ι) (f : γ →+ β i) :
  from_add_monoid (of _ i f) = (of _ i).comp f :=
by { rw [from_add_monoid, to_add_monoid_of], refl }

lemma from_add_monoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
  from_add_monoid (of _ i f) x = of _ i (f x) :=
by rw [from_add_monoid_of, add_monoid_hom.coe_comp]

end from_add_monoid

variables (β)
/-- `set_to_set β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
-- TODO: generalize this to remove the assumption `S ⊆ T`.
def set_to_set (S T : set ι) (H : S ⊆ T) :
  (⨁ (i : S), β i) →+ (⨁ (i : T), β i) :=
to_add_monoid $ λ i, of (λ (i : subtype T), β i) ⟨↑i, H i.prop⟩
variables {β}

omit dec_ι

instance unique [∀ i, subsingleton (β i)] : unique (⨁ i, β i) := dfinsupp.unique

/-- A direct sum over an empty type is trivial. -/
instance unique_of_is_empty [is_empty ι] : unique (⨁ i, β i) := dfinsupp.unique_of_is_empty

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def id (M : Type v) (ι : Type* := punit) [add_comm_monoid M] [unique ι] :
  (⨁ (_ : ι), M) ≃+ M :=
{ to_fun := direct_sum.to_add_monoid (λ _, add_monoid_hom.id M),
  inv_fun := of (λ _, M) default,
  left_inv := λ x, direct_sum.induction_on x
    (by rw [add_monoid_hom.map_zero, add_monoid_hom.map_zero])
    (λ p x, by rw [unique.default_eq p, to_add_monoid_of]; refl)
    (λ x y ihx ihy, by rw [add_monoid_hom.map_add, add_monoid_hom.map_add, ihx, ihy]),
  right_inv := λ x, to_add_monoid_of _ _ _,
  ..direct_sum.to_add_monoid (λ _, add_monoid_hom.id M) }

section congr_left
variables {κ : Type*}

/--Reindexing terms of a direct sum.-/
def equiv_congr_left (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
{ map_add' := dfinsupp.comap_domain'_add _ _,
  ..dfinsupp.equiv_congr_left h }

@[simp] lemma equiv_congr_left_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
  equiv_congr_left h f k = f (h.symm k) := dfinsupp.comap_domain'_apply _ _ _ _

end congr_left

section option
variables {α : option ι → Type w} [Π i, add_comm_monoid (α i)]
include dec_ι

/--Isomorphism obtained by separating the term of index `none` of a direct sum over `option ι`.-/
@[simps] noncomputable def add_equiv_prod_direct_sum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
{ map_add' := dfinsupp.equiv_prod_dfinsupp_add, ..dfinsupp.equiv_prod_dfinsupp }

end option

section sigma
variables {α : ι → Type u} {δ : Π i, α i → Type w} [Π i j, add_comm_monoid (δ i j)]

/--The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`.-/
noncomputable def sigma_curry : (⨁ (i : Σ i, _), δ i.1 i.2) →+ ⨁ i j, δ i j :=
{ to_fun := @dfinsupp.sigma_curry _ _ δ _,
  map_zero' := dfinsupp.sigma_curry_zero,
  map_add' := λ f g, @dfinsupp.sigma_curry_add _ _ δ _ f g }

@[simp] lemma sigma_curry_apply (f : ⨁ (i : Σ i, _), δ i.1 i.2) (i : ι) (j : α i) :
  sigma_curry f i j = f ⟨i, j⟩ := @dfinsupp.sigma_curry_apply _ _ δ _ f i j

/--The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`.-/
noncomputable def sigma_uncurry : (⨁ i j, δ i j) →+ ⨁ (i : Σ i, _), δ i.1 i.2 :=
{ to_fun := dfinsupp.sigma_uncurry,
  map_zero' := dfinsupp.sigma_uncurry_zero,
  map_add' := dfinsupp.sigma_uncurry_add }

@[simp] lemma sigma_uncurry_apply (f : ⨁ i j, δ i j) (i : ι) (j : α i) :
  sigma_uncurry f ⟨i, j⟩ = f i j := dfinsupp.sigma_uncurry_apply f i j

/--The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`.-/
noncomputable def sigma_curry_equiv : (⨁ (i : Σ i, _), δ i.1 i.2) ≃+ ⨁ i j, δ i j :=
{ ..sigma_curry, ..dfinsupp.sigma_curry_equiv }

end sigma

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `add_submonoid M`
indexed by `ι`.

When `S = submodule _ M`, this is available as a `linear_map`, `direct_sum.coe_linear_map`. -/
protected def coe_add_monoid_hom {M S : Type*} [decidable_eq ι] [add_comm_monoid M]
  [set_like S M] [add_submonoid_class S M] (A : ι → S) : (⨁ i, A i) →+ M :=
to_add_monoid (λ i, add_submonoid_class.subtype (A i))

@[simp] lemma coe_add_monoid_hom_of {M S : Type*} [decidable_eq ι] [add_comm_monoid M]
  [set_like S M] [add_submonoid_class S M] (A : ι → S) (i : ι) (x : A i) :
  direct_sum.coe_add_monoid_hom A (of (λ i, A i) i x) = x :=
to_add_monoid_of _ _ _

lemma coe_of_apply {M S : Type*} [decidable_eq ι] [add_comm_monoid M]
  [set_like S M] [add_submonoid_class S M] {A : ι → S} (i j : ι) (x : A i) :
  (of _ i x j : M) = if i = j then x else 0 :=
begin
  obtain rfl | h := decidable.eq_or_ne i j,
  { rw [direct_sum.of_eq_same, if_pos rfl], },
  { rw [direct_sum.of_eq_of_ne _ _ _ _ h, if_neg h, zero_mem_class.coe_zero], },
end

/-- The `direct_sum` formed by a collection of additive submonoids (or subgroups, or submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`direct_sum.subgroup_is_internal_iff_independent_and_supr_eq_top` and
`direct_sum.is_internal_submodule_iff_independent_and_supr_eq_top`. -/
def is_internal {M S : Type*} [decidable_eq ι] [add_comm_monoid M]
  [set_like S M] [add_submonoid_class S M] (A : ι → S) : Prop :=
function.bijective (direct_sum.coe_add_monoid_hom A)

lemma is_internal.add_submonoid_supr_eq_top {M : Type*} [decidable_eq ι] [add_comm_monoid M]
  (A : ι → add_submonoid M)
  (h : is_internal A) : supr A = ⊤ :=
begin
  rw [add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom, add_monoid_hom.mrange_top_iff_surjective],
  exact function.bijective.surjective h,
end

end direct_sum
