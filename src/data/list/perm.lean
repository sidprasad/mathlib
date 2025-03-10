/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.list.dedup
import data.list.permutation
import data.list.range
import data.nat.factorial.basic

/-!
# List Permutations

This file introduces the `list.perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/

open_locale nat

universes uu vv

namespace list
variables {α : Type uu} {β : Type vv} {l₁ l₂ : list α}

/-- `perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive perm : list α → list α → Prop
| nil   : perm [] []
| cons  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

open perm (swap)

infix (name := list.perm) ` ~ `:50 := perm

@[refl] protected theorem perm.refl : ∀ (l : list α), l ~ l
| []      := perm.nil
| (x::xs) := (perm.refl xs).cons x

@[symm] protected theorem perm.symm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
perm.rec_on p
  perm.nil
  (λ x l₁ l₂ p₁ r₁, r₁.cons x)
  (λ x y l, swap y x l)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, r₂.trans r₁)

theorem perm_comm {l₁ l₂ : list α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨perm.symm, perm.symm⟩

theorem perm.swap'
  (x y : α) {l₁ l₂ : list α} (p : l₁ ~ l₂) : y::x::l₁ ~ x::y::l₂ :=
(swap _ _ _).trans ((p.cons _).cons _)

attribute [trans] perm.trans

theorem perm.eqv (α) : equivalence (@perm α) :=
mk_equivalence (@perm α) (@perm.refl α) (@perm.symm α) (@perm.trans α)

instance is_setoid (α) : setoid (list α) :=
setoid.mk (@perm α) (perm.eqv α)

theorem perm.subset {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ :=
λ a, perm.rec_on p
  (λ h, h)
  (λ x l₁ l₂ p₁ r₁ i, or.elim i
    (λ ax, by simp [ax])
    (λ al₁, or.inr (r₁ al₁)))
  (λ x y l ayxl, or.elim ayxl
    (λ ay, by simp [ay])
    (λ axl, or.elim axl
      (λ ax, by simp [ax])
      (λ al, or.inr (or.inr al))))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁, r₂ (r₁ ainl₁))

theorem perm.mem_iff {a : α} {l₁ l₂ : list α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
iff.intro (λ m, h.subset m) (λ m, h.symm.subset m)

theorem perm.append_right {l₁ l₂ : list α} (t₁ : list α) (p : l₁ ~ l₂) : l₁++t₁ ~ l₂++t₁ :=
perm.rec_on p
  (perm.refl ([] ++ t₁))
  (λ x l₁ l₂ p₁ r₁, r₁.cons x)
  (λ x y l, swap x y _)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, r₁.trans r₂)

theorem perm.append_left {t₁ t₂ : list α} : ∀ (l : list α), t₁ ~ t₂ → l++t₁ ~ l++t₂
| []      p := p
| (x::xs) p := (perm.append_left xs p).cons x

theorem perm.append {l₁ l₂ t₁ t₂ : list α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁++t₁ ~ l₂++t₂ :=
(p₁.append_right t₁).trans (p₂.append_left l₂)

theorem perm.append_cons (a : α) {h₁ h₂ t₁ t₂ : list α}
  (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) : h₁ ++ a::t₁ ~ h₂ ++ a::t₂ :=
p₁.append (p₂.cons a)

@[simp] theorem perm_middle {a : α} : ∀ {l₁ l₂ : list α}, l₁++a::l₂ ~ a::(l₁++l₂)
| []      l₂ := perm.refl _
| (b::l₁) l₂ := ((@perm_middle l₁ l₂).cons _).trans (swap a b _)

@[simp] theorem perm_append_singleton (a : α) (l : list α) : l ++ [a] ~ a::l :=
perm_middle.trans $ by rw [append_nil]

theorem perm_append_comm : ∀ {l₁ l₂ : list α}, (l₁++l₂) ~ (l₂++l₁)
| []     l₂ := by simp
| (a::t) l₂ := (perm_append_comm.cons _).trans perm_middle.symm

theorem concat_perm (l : list α) (a : α) : concat l a ~ a :: l :=
by simp

theorem perm.length_eq {l₁ l₂ : list α} (p : l₁ ~ l₂) : length l₁ = length l₂ :=
perm.rec_on p
  rfl
  (λ x l₁ l₂ p r, by simp[r])
  (λ x y l, by simp)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, eq.trans r₁ r₂)

theorem perm.eq_nil {l : list α} (p : l ~ []) : l = [] :=
eq_nil_of_length_eq_zero p.length_eq

theorem perm.nil_eq {l : list α} (p : [] ~ l) : [] = l :=
p.symm.eq_nil.symm

@[simp]
theorem perm_nil {l₁ : list α} : l₁ ~ [] ↔ l₁ = [] :=
⟨λ p, p.eq_nil, λ e, e ▸ perm.refl _⟩

@[simp]
theorem nil_perm {l₁ : list α} : [] ~ l₁ ↔ l₁ = [] :=
perm_comm.trans perm_nil

theorem not_perm_nil_cons (x : α) (l : list α) : ¬ [] ~ x::l
| p := by injection p.symm.eq_nil

@[simp] theorem reverse_perm : ∀ (l : list α), reverse l ~ l
| []     := perm.nil
| (a::l) := by { rw reverse_cons,
  exact (perm_append_singleton _ _).trans ((reverse_perm l).cons a) }

theorem perm_cons_append_cons {l l₁ l₂ : list α} (a : α) (p : l ~ l₁++l₂) :
  a::l ~ l₁++(a::l₂) :=
(p.cons a).trans perm_middle.symm

@[simp] theorem perm_repeat {a : α} {n : ℕ} {l : list α} : l ~ repeat a n ↔ l = repeat a n :=
⟨λ p, (eq_repeat.2
  ⟨p.length_eq.trans $ length_repeat _ _,
   λ b m, eq_of_mem_repeat $ p.subset m⟩),
 λ h, h ▸ perm.refl _⟩

@[simp] theorem repeat_perm {a : α} {n : ℕ} {l : list α} : repeat a n ~ l ↔ repeat a n = l :=
(perm_comm.trans perm_repeat).trans eq_comm

@[simp] theorem perm_singleton {a : α} {l : list α} : l ~ [a] ↔ l = [a] :=
@perm_repeat α a 1 l

@[simp] theorem singleton_perm {a : α} {l : list α} : [a] ~ l ↔ [a] = l :=
@repeat_perm α a 1 l

theorem perm.eq_singleton {a : α} {l : list α} (p : l ~ [a]) : l = [a] :=
perm_singleton.1 p

theorem perm.singleton_eq {a : α} {l : list α} (p : [a] ~ l) : [a] = l :=
p.symm.eq_singleton.symm

theorem singleton_perm_singleton {a b : α} : [a] ~ [b] ↔ a = b :=
by simp

theorem perm_cons_erase [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) :
  l ~ a :: l.erase a :=
let ⟨l₁, l₂, _, e₁, e₂⟩ := exists_erase_eq h in
e₂.symm ▸ e₁.symm ▸ perm_middle

@[elab_as_eliminator] theorem perm_induction_on
    {P : list α → list α → Prop} {l₁ l₂ : list α} (p : l₁ ~ l₂)
    (h₁ : P [] [])
    (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x::l₁) (x::l₂))
    (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y::x::l₁) (x::y::l₂))
    (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) :
  P l₁ l₂ :=
have P_refl : ∀ l, P l l, from
  assume l,
  list.rec_on l h₁ (λ x xs ih, h₂ x xs xs (perm.refl xs) ih),
perm.rec_on p h₁ h₂ (λ x y l, h₃ x y l l (perm.refl l) (P_refl l)) h₄

@[congr] theorem perm.filter_map (f : α → option β) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  filter_map f l₁ ~ filter_map f l₂ :=
begin
  induction p with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { simp },
  { simp only [filter_map], cases f x with a; simp [filter_map, IH, perm.cons] },
  { simp only [filter_map], cases f x with a; cases f y with b; simp [filter_map, swap] },
  { exact IH₁.trans IH₂ }
end

@[congr] theorem perm.map (f : α → β) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  map f l₁ ~ map f l₂ :=
filter_map_eq_map f ▸ p.filter_map _

theorem perm.pmap {p : α → Prop} (f : Π a, p a → β)
  {l₁ l₂ : list α} (p : l₁ ~ l₂) {H₁ H₂} : pmap f l₁ H₁ ~ pmap f l₂ H₂ :=
begin
  induction p with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂,
  { simp },
  { simp [IH, perm.cons] },
  { simp [swap] },
  { refine IH₁.trans IH₂,
    exact λ a m, H₂ a (p₂.subset m) }
end

theorem perm.filter (p : α → Prop) [decidable_pred p]
  {l₁ l₂ : list α} (s : l₁ ~ l₂) : filter p l₁ ~ filter p l₂ :=
by rw ← filter_map_eq_filter; apply s.filter_map _

theorem filter_append_perm (p : α → Prop) [decidable_pred p]
  (l : list α) : filter p l ++ filter (λ x, ¬ p x) l ~ l :=
begin
  induction l with x l ih,
  { refl },
  { by_cases h : p x,
    { simp only [h, filter_cons_of_pos, filter_cons_of_neg, not_true, not_false_iff, cons_append],
      exact ih.cons x },
    { simp only [h, filter_cons_of_neg, not_false_iff, filter_cons_of_pos],
      refine perm.trans _ (ih.cons x),
      exact perm_append_comm.trans (perm_append_comm.cons _), } }
end

theorem exists_perm_sublist {l₁ l₂ l₂' : list α}
  (s : l₁ <+ l₂) (p : l₂ ~ l₂') : ∃ l₁' ~ l₁, l₁' <+ l₂' :=
begin
  induction p with x l₂ l₂' p IH  x y l₂  l₂ m₂ r₂ p₁ p₂ IH₁ IH₂ generalizing l₁ s,
  { exact ⟨[], eq_nil_of_sublist_nil s ▸ perm.refl _, nil_sublist _⟩ },
  { cases s with _ _ _ s l₁ _ _ s,
    { exact let ⟨l₁', p', s'⟩ := IH s in ⟨l₁', p', s'.cons _ _ _⟩ },
    { exact let ⟨l₁', p', s'⟩ := IH s in ⟨x::l₁', p'.cons x, s'.cons2 _ _ _⟩ } },
  { cases s with _ _ _ s l₁ _ _ s; cases s with _ _ _ s l₁ _ _ s,
    { exact ⟨l₁, perm.refl _, (s.cons _ _ _).cons _ _ _⟩ },
    { exact ⟨x::l₁, perm.refl _, (s.cons _ _ _).cons2 _ _ _⟩ },
    { exact ⟨y::l₁, perm.refl _, (s.cons2 _ _ _).cons _ _ _⟩ },
    { exact ⟨x::y::l₁, perm.swap _ _ _, (s.cons2 _ _ _).cons2 _ _ _⟩ } },
  { exact let ⟨m₁, pm, sm⟩ := IH₁ s, ⟨r₁, pr, sr⟩ := IH₂ sm in
          ⟨r₁, pr.trans pm, sr⟩ }
end

theorem perm.sizeof_eq_sizeof [has_sizeof α] {l₁ l₂ : list α} (h : l₁ ~ l₂) :
  l₁.sizeof = l₂.sizeof :=
begin
  induction h with hd l₁ l₂ h₁₂ h_sz₁₂ a b l l₁ l₂ l₃ h₁₂ h₂₃ h_sz₁₂ h_sz₂₃,
  { refl },
  { simp only [list.sizeof, h_sz₁₂] },
  { simp only [list.sizeof, add_left_comm] },
  { simp only [h_sz₁₂, h_sz₂₃] }
end


section rel
open relator
variables {γ : Type*} {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

local infixr ` ∘r ` : 80 := relation.comp

lemma perm_comp_perm : (perm ∘r perm : list α → list α → Prop) = perm :=
begin
  funext a c, apply propext,
  split,
  { exact assume ⟨b, hab, hba⟩, perm.trans hab hba },
  { exact assume h, ⟨a, perm.refl a, h⟩ }
end

lemma perm_comp_forall₂ {l u v} (hlu : perm l u) (huv : forall₂ r u v) : (forall₂ r ∘r perm) l v :=
begin
  induction hlu generalizing v,
  case perm.nil { cases huv, exact ⟨[], forall₂.nil, perm.nil⟩ },
  case perm.cons : a l u hlu ih
  { cases huv with _ b _ v hab huv',
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩,
    exact ⟨b::l₂, forall₂.cons hab h₁₂, h₂₃.cons _⟩ },
  case perm.swap : a₁ a₂ l₁ l₂ h₂₃
  { cases h₂₃ with _ b₁ _ l₂ h₁ hr_₂₃,
    cases hr_₂₃ with _ b₂ _ l₂ h₂ h₁₂,
    exact ⟨b₂::b₁::l₂, forall₂.cons h₂ (forall₂.cons h₁ h₁₂), perm.swap _ _ _⟩ },
  case perm.trans : la₁ la₂ la₃ _ _ ih₁ ih₂
  { rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩,
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩,
    exact ⟨lb₁, hab₁, perm.trans h₁₂ h₂₃⟩ }
end

lemma forall₂_comp_perm_eq_perm_comp_forall₂ : forall₂ r ∘r perm = perm ∘r forall₂ r :=
begin
  funext l₁ l₃, apply propext,
  split,
  { assume h, rcases h with ⟨l₂, h₁₂, h₂₃⟩,
    have : forall₂ (flip r) l₂ l₁, from h₁₂.flip ,
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩,
    exact ⟨l', h₂.symm, h₁.flip⟩ },
  { exact assume ⟨l₂, h₁₂, h₂₃⟩, perm_comp_forall₂ h₁₂ h₂₃ }
end

lemma rel_perm_imp (hr : right_unique r) : (forall₂ r ⇒ forall₂ r ⇒ implies) perm perm :=
assume a b h₁ c d h₂ h,
have (flip (forall₂ r) ∘r (perm ∘r forall₂ r)) b d, from ⟨a, h₁, c, h, h₂⟩,
have ((flip (forall₂ r) ∘r forall₂ r) ∘r perm) b d,
  by rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← relation.comp_assoc] at this,
let ⟨b', ⟨c', hbc, hcb⟩, hbd⟩ := this in
have b' = b, from right_unique_forall₂' hr hcb hbc,
this ▸ hbd

lemma rel_perm (hr : bi_unique r) : (forall₂ r ⇒ forall₂ r ⇒ (↔)) perm perm :=
assume a b hab c d hcd, iff.intro
  (rel_perm_imp hr.2 hab hcd)
  (rel_perm_imp hr.left.flip hab.flip hcd.flip)

end rel

section subperm

/-- `subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
def subperm (l₁ l₂ : list α) : Prop := ∃ l ~ l₁, l <+ l₂

infix ` <+~ `:50 := subperm

theorem nil_subperm {l : list α} : [] <+~ l :=
⟨[], perm.nil, by simp⟩

theorem perm.subperm_left {l l₁ l₂ : list α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ :=
suffices ∀ {l₁ l₂ : list α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂,
from ⟨this p, this p.symm⟩,
λ l₁ l₂ p ⟨u, pu, su⟩,
  let ⟨v, pv, sv⟩ := exists_perm_sublist su p in
  ⟨v, pv.trans pu, sv⟩

theorem perm.subperm_right {l₁ l₂ l : list α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l :=
⟨λ ⟨u, pu, su⟩, ⟨u, pu.trans p, su⟩,
 λ ⟨u, pu, su⟩, ⟨u, pu.trans p.symm, su⟩⟩

theorem sublist.subperm {l₁ l₂ : list α} (s : l₁ <+ l₂) : l₁ <+~ l₂ :=
⟨l₁, perm.refl _, s⟩

theorem perm.subperm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₁ <+~ l₂ :=
⟨l₂, p.symm, sublist.refl _⟩

@[refl] theorem subperm.refl (l : list α) : l <+~ l := (perm.refl _).subperm

@[trans] theorem subperm.trans {l₁ l₂ l₃ : list α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃
| s ⟨l₂', p₂, s₂⟩ :=
  let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.2 s in ⟨l₁', p₁, s₁.trans s₂⟩

theorem subperm.length_le {l₁ l₂ : list α} : l₁ <+~ l₂ → length l₁ ≤ length l₂
| ⟨l, p, s⟩ := p.length_eq ▸ s.length_le

theorem subperm.perm_of_length_le {l₁ l₂ : list α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂
| ⟨l, p, s⟩ h := (s.eq_of_length_le $ p.symm.length_eq ▸ h) ▸ p.symm

theorem subperm.antisymm {l₁ l₂ : list α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
h₁.perm_of_length_le h₂.length_le

theorem subperm.subset {l₁ l₂ : list α} : l₁ <+~ l₂ → l₁ ⊆ l₂
| ⟨l, p, s⟩ := subset.trans p.symm.subset s.subset

lemma subperm.filter (p : α → Prop) [decidable_pred p]
  ⦃l l' : list α⦄ (h : l <+~ l') : filter p l <+~ filter p l' :=
begin
  obtain ⟨xs, hp, h⟩ := h,
  exact ⟨_, hp.filter p, h.filter p⟩
end

end subperm

theorem sublist.exists_perm_append : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
| ._ ._ sublist.slnil            := ⟨nil, perm.refl _⟩
| ._ ._ (sublist.cons l₁ l₂ a s) :=
  let ⟨l, p⟩ := sublist.exists_perm_append s in
  ⟨a::l, (p.cons a).trans perm_middle.symm⟩
| ._ ._ (sublist.cons2 l₁ l₂ a s) :=
  let ⟨l, p⟩ := sublist.exists_perm_append s in
  ⟨l, p.cons a⟩

theorem perm.countp_eq (p : α → Prop) [decidable_pred p]
  {l₁ l₂ : list α} (s : l₁ ~ l₂) : countp p l₁ = countp p l₂ :=
by rw [countp_eq_length_filter, countp_eq_length_filter];
   exact (s.filter _).length_eq

theorem subperm.countp_le (p : α → Prop) [decidable_pred p]
  {l₁ l₂ : list α} : l₁ <+~ l₂ → countp p l₁ ≤ countp p l₂
| ⟨l, p', s⟩ := p'.countp_eq p ▸ s.countp_le p

theorem perm.countp_congr (s : l₁ ~ l₂) {p p' : α → Prop} [decidable_pred p] [decidable_pred p']
  (hp : ∀ x ∈ l₁, p x = p' x) : l₁.countp p = l₂.countp p' :=
begin
  rw ← s.countp_eq p',
  clear s,
  induction l₁ with y s hs,
  { refl },
  { simp only [mem_cons_iff, forall_eq_or_imp] at hp,
    simp only [countp_cons, hs hp.2, hp.1], },
end

theorem countp_eq_countp_filter_add
  (l : list α) (p q : α → Prop) [decidable_pred p] [decidable_pred q] :
  l.countp p = (l.filter q).countp p + (l.filter (λ a, ¬ q a)).countp p :=
by { rw [← countp_append], exact perm.countp_eq _ (filter_append_perm _ _).symm }

theorem perm.count_eq [decidable_eq α] {l₁ l₂ : list α}
  (p : l₁ ~ l₂) (a) : count a l₁ = count a l₂ :=
p.countp_eq _

theorem subperm.count_le [decidable_eq α] {l₁ l₂ : list α}
  (s : l₁ <+~ l₂) (a) : count a l₁ ≤ count a l₂ :=
s.countp_le _

theorem perm.foldl_eq' {f : β → α → β} {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  (∀ (x ∈ l₁) (y ∈ l₁) z, f (f z x) y = f (f z y) x) → ∀ b, foldl f b l₁ = foldl f b l₂ :=
perm_induction_on p
  (λ H b, rfl)
  (λ x t₁ t₂ p r H b, r (λ x hx y hy, H _ (or.inr hx) _ (or.inr hy)) _)
  (λ x y t₁ t₂ p r H b,
    begin
      simp only [foldl],
      rw [H x (or.inr $ or.inl rfl) y (or.inl rfl)],
      exact r (λ x hx y hy, H _ (or.inr $ or.inr hx) _ (or.inr $ or.inr hy)) _
    end)
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ H b, eq.trans (r₁ H b)
    (r₂ (λ x hx y hy, H _ (p₁.symm.subset hx) _ (p₁.symm.subset hy)) b))

theorem perm.foldl_eq {f : β → α → β} {l₁ l₂ : list α} (rcomm : right_commutative f) (p : l₁ ~ l₂) :
  ∀ b, foldl f b l₁ = foldl f b l₂ :=
p.foldl_eq' $ λ x hx y hy z, rcomm z x y

theorem perm.foldr_eq {f : α → β → β} {l₁ l₂ : list α} (lcomm : left_commutative f) (p : l₁ ~ l₂) :
  ∀ b, foldr f b l₁ = foldr f b l₂ :=
perm_induction_on p
  (λ b, rfl)
  (λ x t₁ t₂ p r b, by simp; rw [r b])
  (λ x y t₁ t₂ p r b, by simp; rw [lcomm, r b])
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ a, eq.trans (r₁ a) (r₂ a))

lemma perm.rec_heq {β : list α → Sort*} {f : Πa l, β l → β (a::l)} {b : β []} {l l' : list α}
  (hl : perm l l')
  (f_congr : ∀{a l l' b b'}, perm l l' → b == b' → f a l b == f a l' b')
  (f_swap : ∀{a a' l b}, f a (a'::l) (f a' l b) == f a' (a::l) (f a l b)) :
  @list.rec α β b f l == @list.rec α β b f l' :=
begin
  induction hl,
  case list.perm.nil { refl },
  case list.perm.cons : a l l' h ih { exact f_congr h ih },
  case list.perm.swap : a a' l { exact f_swap },
  case list.perm.trans : l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ { exact heq.trans ih₁ ih₂ }
end

section
variables {op : α → α → α} [is_associative α op] [is_commutative α op]
local notation (name := op) a ` * ` b := op a b
local notation (name := foldl) l ` <*> ` a := foldl op a l

lemma perm.fold_op_eq {l₁ l₂ : list α} {a : α} (h : l₁ ~ l₂) : l₁ <*> a = l₂ <*> a :=
h.foldl_eq (right_comm _ is_commutative.comm is_associative.assoc) _
end

section comm_monoid

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements. -/
@[to_additive "If elements of a list additively commute with each other, then their sum does not
depend on the order of elements."]
lemma perm.prod_eq' [monoid α] {l₁ l₂ : list α} (h : l₁ ~ l₂) (hc : l₁.pairwise commute) :
  l₁.prod = l₂.prod :=
h.foldl_eq' (pairwise.forall_of_forall (λ x y h z, (h z).symm) (λ x hx z, rfl) $
  hc.imp $ λ x y h z, by simp only [mul_assoc, h.eq]) _

variable [comm_monoid α]

@[to_additive]
lemma perm.prod_eq {l₁ l₂ : list α} (h : perm l₁ l₂) : prod l₁ = prod l₂ :=
h.fold_op_eq

@[to_additive]
lemma prod_reverse (l : list α) : prod l.reverse = prod l :=
(reverse_perm l).prod_eq

end comm_monoid

theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : list α} : l₁++a::r₁ ~ l₂++a::r₂ → l₁++r₁ ~ l₂++r₂ :=
begin
  generalize e₁ : l₁++a::r₁ = s₁, generalize e₂ : l₂++a::r₂ = s₂,
  intro p, revert l₁ l₂ r₁ r₂ e₁ e₂,
  refine perm_induction_on p _ (λ x t₁ t₂ p IH, _) (λ x y t₁ t₂ p IH, _)
    (λ t₁ t₂ t₃ p₁ p₂ IH₁ IH₂, _); intros l₁ l₂ r₁ r₂ e₁ e₂,
  { apply (not_mem_nil a).elim, rw ← e₁, simp },
  { cases l₁ with y l₁; cases l₂ with z l₂;
      dsimp at e₁ e₂; injections; subst x,
    { substs t₁ t₂,     exact p },
    { substs z t₁ t₂,   exact p.trans perm_middle },
    { substs y t₁ t₂,   exact perm_middle.symm.trans p },
    { substs z t₁ t₂,   exact (IH rfl rfl).cons y } },
  { rcases l₁ with _|⟨y, _|⟨z, l₁⟩⟩; rcases l₂ with _|⟨u, _|⟨v, l₂⟩⟩;
      dsimp at e₁ e₂; injections; substs x y,
    { substs r₁ r₂,     exact p.cons a },
    { substs r₁ r₂,     exact p.cons u },
    { substs r₁ v t₂,   exact (p.trans perm_middle).cons u },
    { substs r₁ r₂,     exact p.cons y },
    { substs r₁ r₂ y u, exact p.cons a },
    { substs r₁ u v t₂, exact ((p.trans perm_middle).cons y).trans (swap _ _ _) },
    { substs r₂ z t₁,   exact (perm_middle.symm.trans p).cons y },
    { substs r₂ y z t₁, exact (swap _ _ _).trans ((perm_middle.symm.trans p).cons u) },
    { substs u v t₁ t₂, exact (IH rfl rfl).swap' _ _ } },
  { substs t₁ t₃,
    have : a ∈ t₂ := p₁.subset (by simp),
    rcases mem_split this with ⟨l₂, r₂, e₂⟩,
    subst t₂, exact (IH₁ rfl rfl).trans (IH₂ rfl rfl) }
end

theorem perm.cons_inv {a : α} {l₁ l₂ : list α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ :=
@perm_inv_core _ _ [] [] _ _

@[simp] theorem perm_cons (a : α) {l₁ l₂ : list α} : a::l₁ ~ a::l₂ ↔ l₁ ~ l₂ :=
⟨perm.cons_inv, perm.cons a⟩

theorem perm_append_left_iff {l₁ l₂ : list α} : ∀ l, l++l₁ ~ l++l₂ ↔ l₁ ~ l₂
| []     := iff.rfl
| (a::l) := (perm_cons a).trans (perm_append_left_iff l)

theorem perm_append_right_iff {l₁ l₂ : list α} (l) : l₁++l ~ l₂++l ↔ l₁ ~ l₂ :=
⟨λ p, (perm_append_left_iff _).1 $ perm_append_comm.trans $ p.trans perm_append_comm,
 perm.append_right _⟩

theorem perm_option_to_list {o₁ o₂ : option α} : o₁.to_list ~ o₂.to_list ↔ o₁ = o₂ :=
begin
  refine ⟨λ p, _, λ e, e ▸ perm.refl _⟩,
  cases o₁ with a; cases o₂ with b, {refl},
  { cases p.length_eq },
  { cases p.length_eq },
  { exact option.mem_to_list.1 (p.symm.subset $ by simp) }
end

theorem subperm_cons (a : α) {l₁ l₂ : list α} : a::l₁ <+~ a::l₂ ↔ l₁ <+~ l₂ :=
⟨λ ⟨l, p, s⟩, begin
  cases s with _ _ _ s' u _ _ s',
  { exact (p.subperm_left.2 $ (sublist_cons _ _).subperm).trans s'.subperm },
  { exact ⟨u, p.cons_inv, s'⟩ }
end, λ ⟨l, p, s⟩, ⟨a::l, p.cons a, s.cons2 _ _ _⟩⟩

alias subperm_cons ↔ subperm.of_cons subperm.cons

attribute [protected] subperm.cons

theorem cons_subperm_of_mem {a : α} {l₁ l₂ : list α} (d₁ : nodup l₁) (h₁ : a ∉ l₁) (h₂ : a ∈ l₂)
 (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ :=
begin
  rcases s with ⟨l, p, s⟩,
  induction s generalizing l₁,
  case list.sublist.slnil { cases h₂ },
  case list.sublist.cons : r₁ r₂ b s' ih
  { simp at h₂,
    cases h₂ with e m,
    { subst b, exact ⟨a::r₁, p.cons a, s'.cons2 _ _ _⟩ },
    { rcases ih m d₁ h₁ p with ⟨t, p', s'⟩, exact ⟨t, p', s'.cons _ _ _⟩ } },
  case list.sublist.cons2 : r₁ r₂ b s' ih
  { have bm : b ∈ l₁ := (p.subset $ mem_cons_self _ _),
    have am : a ∈ r₂ := h₂.resolve_left (λ e, h₁ $ e.symm ▸ bm),
    rcases mem_split bm with ⟨t₁, t₂, rfl⟩,
    have st : t₁ ++ t₂ <+ t₁ ++ b :: t₂ := by simp,
    rcases ih am (d₁.sublist st)
      (mt (λ x, st.subset x) h₁)
      (perm.cons_inv $ p.trans perm_middle) with ⟨t, p', s'⟩,
    exact ⟨b::t, (p'.cons b).trans $ (swap _ _ _).trans (perm_middle.symm.cons a), s'.cons2 _ _ _⟩ }
end

theorem subperm_append_left {l₁ l₂ : list α} : ∀ l, l++l₁ <+~ l++l₂ ↔ l₁ <+~ l₂
| []     := iff.rfl
| (a::l) := (subperm_cons a).trans (subperm_append_left l)

theorem subperm_append_right {l₁ l₂ : list α} (l) : l₁++l <+~ l₂++l ↔ l₁ <+~ l₂ :=
(perm_append_comm.subperm_left.trans perm_append_comm.subperm_right).trans (subperm_append_left l)

theorem subperm.exists_of_length_lt {l₁ l₂ : list α} :
  l₁ <+~ l₂ → length l₁ < length l₂ → ∃ a, a :: l₁ <+~ l₂
| ⟨l, p, s⟩ h :=
  suffices length l < length l₂ → ∃ (a : α), a :: l <+~ l₂, from
  (this $ p.symm.length_eq ▸ h).imp (λ a, (p.cons a).subperm_right.1),
  begin
    clear subperm.exists_of_length_lt p h l₁, rename l₂ u,
    induction s with l₁ l₂ a s IH _ _ b s IH; intro h,
    { cases h },
    { cases lt_or_eq_of_le (nat.le_of_lt_succ h : length l₁ ≤ length l₂) with h h,
      { exact (IH h).imp (λ a s, s.trans (sublist_cons _ _).subperm) },
      { exact ⟨a, s.eq_of_length h ▸ subperm.refl _⟩ } },
    { exact (IH $ nat.lt_of_succ_lt_succ h).imp
        (λ a s, (swap _ _ _).subperm_right.1 $ (subperm_cons _).2 s) }
  end

protected lemma nodup.subperm (d : nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
begin
  induction d with a l₁' h d IH,
  { exact ⟨nil, perm.nil, nil_sublist _⟩ },
  { cases forall_mem_cons.1 H with H₁ H₂,
    simp at h,
    exact cons_subperm_of_mem d h H₁ (IH H₂) }
end

theorem perm_ext {l₁ l₂ : list α} (d₁ : nodup l₁) (d₂ : nodup l₂) :
  l₁ ~ l₂ ↔ ∀a, a ∈ l₁ ↔ a ∈ l₂ :=
⟨λ p a, p.mem_iff, λ H, (d₁.subperm $ λ a, (H a).1).antisymm $ d₂.subperm $ λ a, (H a).2⟩

theorem nodup.sublist_ext {l₁ l₂ l : list α} (d : nodup l)
  (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) : l₁ ~ l₂ ↔ l₁ = l₂ :=
⟨λ h, begin
  induction s₂ with l₂ l a s₂ IH l₂ l a s₂ IH generalizing l₁,
  { exact h.eq_nil },
  { simp at d,
    cases s₁ with _ _ _ s₁ l₁ _ _ s₁,
    { exact IH d.2 s₁ h },
    { apply d.1.elim,
      exact subperm.subset ⟨_, h.symm, s₂⟩ (mem_cons_self _ _) } },
  { simp at d,
    cases s₁ with _ _ _ s₁ l₁ _ _ s₁,
    { apply d.1.elim,
      exact subperm.subset ⟨_, h, s₁⟩ (mem_cons_self _ _) },
    { rw IH d.2 s₁ h.cons_inv } }
end, λ h, by rw h⟩

section
variable [decidable_eq α]

-- attribute [congr]
theorem perm.erase (a : α) {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  l₁.erase a ~ l₂.erase a :=
if h₁ : a ∈ l₁ then
have h₂ : a ∈ l₂, from p.subset h₁,
perm.cons_inv $ (perm_cons_erase h₁).symm.trans $ p.trans (perm_cons_erase h₂)
else
have h₂ : a ∉ l₂, from mt p.mem_iff.2 h₁,
by rw [erase_of_not_mem h₁, erase_of_not_mem h₂]; exact p

theorem subperm_cons_erase (a : α) (l : list α) : l <+~ a :: l.erase a :=
begin
  by_cases h : a ∈ l,
  { exact (perm_cons_erase h).subperm },
  { rw [erase_of_not_mem h],
    exact (sublist_cons _ _).subperm }
end

theorem erase_subperm (a : α) (l : list α) : l.erase a <+~ l :=
(erase_sublist _ _).subperm

theorem subperm.erase {l₁ l₂ : list α} (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
let ⟨l, hp, hs⟩ := h in ⟨l.erase a, hp.erase _, hs.erase _⟩

theorem perm.diff_right {l₁ l₂ : list α} (t : list α) (h : l₁ ~ l₂) : l₁.diff t ~ l₂.diff t :=
by induction t generalizing l₁ l₂ h; simp [*, perm.erase]

theorem perm.diff_left (l : list α) {t₁ t₂ : list α} (h : t₁ ~ t₂) : l.diff t₁ = l.diff t₂ :=
by induction h generalizing l; simp [*, perm.erase, erase_comm]
  <|> exact (ih_1 _).trans (ih_2 _)

theorem perm.diff {l₁ l₂ t₁ t₂ : list α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
  l₁.diff t₁ ~ l₂.diff t₂ :=
ht.diff_left l₂ ▸ hl.diff_right _

theorem subperm.diff_right {l₁ l₂ : list α} (h : l₁ <+~ l₂) (t : list α) :
  l₁.diff t <+~ l₂.diff t :=
by induction t generalizing l₁ l₂ h; simp [*, subperm.erase]

theorem erase_cons_subperm_cons_erase (a b : α) (l : list α) :
  (a :: l).erase b <+~ a :: l.erase b :=
begin
  by_cases h : a = b,
  { subst b,
    rw [erase_cons_head],
    apply subperm_cons_erase },
  { rw [erase_cons_tail _ h] }
end

theorem subperm_cons_diff {a : α} : ∀ {l₁ l₂ : list α}, (a :: l₁).diff l₂ <+~ a :: l₁.diff l₂
| l₁ []      := ⟨a::l₁, by simp⟩
| l₁ (b::l₂) :=
begin
  simp only [diff_cons],
  refine ((erase_cons_subperm_cons_erase a b l₁).diff_right l₂).trans _,
  apply subperm_cons_diff
end

theorem subset_cons_diff {a : α} {l₁ l₂ : list α} : (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ :=
subperm_cons_diff.subset

theorem perm.bag_inter_right {l₁ l₂ : list α} (t : list α) (h : l₁ ~ l₂) :
  l₁.bag_inter t ~ l₂.bag_inter t :=
begin
  induction h with x _ _ _ _ x y _ _ _ _ _ _ ih_1 ih_2 generalizing t, {simp},
  { by_cases x ∈ t; simp [*, perm.cons] },
  { by_cases x = y, {simp [h]},
    by_cases xt : x ∈ t; by_cases yt : y ∈ t,
    { simp [xt, yt, mem_erase_of_ne h, mem_erase_of_ne (ne.symm h), erase_comm, swap] },
    { simp [xt, yt, mt mem_of_mem_erase, perm.cons] },
    { simp [xt, yt, mt mem_of_mem_erase, perm.cons] },
    { simp [xt, yt] } },
  { exact (ih_1 _).trans (ih_2 _) }
end

theorem perm.bag_inter_left (l : list α) {t₁ t₂ : list α} (p : t₁ ~ t₂) :
  l.bag_inter t₁ = l.bag_inter t₂ :=
begin
  induction l with a l IH generalizing t₁ t₂ p, {simp},
  by_cases a ∈ t₁,
  { simp [h, p.subset h, IH (p.erase _)] },
  { simp [h, mt p.mem_iff.2 h, IH p] }
end

theorem perm.bag_inter {l₁ l₂ t₁ t₂ : list α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
  l₁.bag_inter t₁ ~ l₂.bag_inter t₂ :=
ht.bag_inter_left l₂ ▸ hl.bag_inter_right _

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : list α} : a::l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a :=
⟨λ h, have a ∈ l₂, from h.subset (mem_cons_self a l₁),
      ⟨this, (h.trans $ perm_cons_erase this).cons_inv⟩,
 λ ⟨m, h⟩, (h.cons a).trans (perm_cons_erase m).symm⟩

theorem perm_iff_count {l₁ l₂ : list α} : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ :=
⟨perm.count_eq, λ H, begin
  induction l₁ with a l₁ IH generalizing l₂,
  { cases l₂ with b l₂, {refl},
    specialize H b, simp at H, contradiction },
  { have : a ∈ l₂ := count_pos.1 (by rw ← H; simp; apply nat.succ_pos),
    refine ((IH $ λ b, _).cons a).trans (perm_cons_erase this).symm,
    specialize H b,
    rw (perm_cons_erase this).count_eq at H,
    by_cases b = a; simp [h] at H ⊢; assumption }
end⟩

lemma subperm.cons_right {α : Type*} {l l' : list α} (x : α) (h : l <+~ l') : l <+~ x :: l' :=
h.trans (sublist_cons x l').subperm

/-- The list version of `add_tsub_cancel_of_le` for multisets. -/
lemma subperm_append_diff_self_of_count_le {l₁ l₂ : list α}
  (h : ∀ x ∈ l₁, count x l₁ ≤ count x l₂) : l₁ ++ l₂.diff l₁ ~ l₂ :=
begin
  induction l₁ with hd tl IH generalizing l₂,
  { simp },
  { have : hd ∈ l₂,
    { rw ←count_pos,
      exact lt_of_lt_of_le (count_pos.mpr (mem_cons_self _ _)) (h hd (mem_cons_self _ _)) },
    replace this : l₂ ~ hd :: l₂.erase hd := perm_cons_erase this,
    refine perm.trans _ this.symm,
    rw [cons_append, diff_cons, perm_cons],
    refine IH (λ x hx, _),
    specialize h x (mem_cons_of_mem _ hx),
    rw (perm_iff_count.mp this) at h,
    by_cases hx : x = hd,
    { subst hd,
      simpa [nat.succ_le_succ_iff] using h },
    { simpa [hx] using h } },
end

/-- The list version of `multiset.le_iff_count`. -/
lemma subperm_ext_iff {l₁ l₂ : list α} :
  l₁ <+~ l₂ ↔ ∀ x ∈ l₁, count x l₁ ≤ count x l₂ :=
begin
  refine ⟨λ h x hx, subperm.count_le h x, λ h, _⟩,
  suffices : l₁ <+~ (l₂.diff l₁ ++ l₁),
  { refine this.trans (perm.subperm _),
    exact perm_append_comm.trans (subperm_append_diff_self_of_count_le h) },
  convert (subperm_append_right _).mpr nil_subperm using 1
end

instance decidable_subperm : decidable_rel ((<+~) : list α → list α → Prop) :=
λ l₁ l₂, decidable_of_iff _ list.subperm_ext_iff.symm

@[simp] lemma subperm_singleton_iff {α} {l : list α} {a : α} : [a] <+~ l ↔ a ∈ l :=
⟨λ ⟨s, hla, h⟩, by rwa [perm_singleton.mp hla, singleton_sublist] at h,
 λ h, ⟨[a], perm.refl _, singleton_sublist.mpr h⟩⟩

lemma subperm.cons_left {l₁ l₂ : list α} (h : l₁ <+~ l₂)
  (x : α) (hx : count x l₁ < count x l₂) :
  x :: l₁ <+~ l₂  :=
begin
  rw subperm_ext_iff at h ⊢,
  intros y hy,
  by_cases hy' : y = x,
  { subst x,
    simpa using nat.succ_le_of_lt hx },
  { rw count_cons_of_ne hy',
    refine h y _,
    simpa [hy'] using hy }
end

instance decidable_perm : ∀ (l₁ l₂ : list α), decidable (l₁ ~ l₂)
| []      []      := is_true $ perm.refl _
| []      (b::l₂) := is_false $ λ h, by have := h.nil_eq; contradiction
| (a::l₁) l₂      := by haveI := decidable_perm l₁ (l₂.erase a);
                        exact decidable_of_iff' _ cons_perm_iff_perm_erase

-- @[congr]
theorem perm.dedup {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  dedup l₁ ~ dedup l₂ :=
perm_iff_count.2 $ λ a,
if h : a ∈ l₁
then by simp [nodup_dedup, h, p.subset h]
else by simp [h, mt p.mem_iff.2 h]

-- attribute [congr]
theorem perm.insert (a : α)
  {l₁ l₂ : list α} (p : l₁ ~ l₂) : insert a l₁ ~ insert a l₂ :=
if h : a ∈ l₁
then by simpa [h, p.subset h] using p
else by simpa [h, mt p.mem_iff.2 h] using p.cons a

theorem perm_insert_swap (x y : α) (l : list α) :
  insert x (insert y l) ~ insert y (insert x l) :=
begin
  by_cases xl : x ∈ l; by_cases yl : y ∈ l; simp [xl, yl],
  by_cases xy : x = y, { simp [xy] },
  simp [not_mem_cons_of_ne_of_not_mem xy xl,
        not_mem_cons_of_ne_of_not_mem (ne.symm xy) yl],
  constructor
end

theorem perm_insert_nth {α} (x : α) (l : list α) {n} (h : n ≤ l.length) :
  insert_nth n x l ~ x :: l :=
begin
  induction l generalizing n,
  { cases n, refl, cases h },
  cases n,
  { simp [insert_nth] },
  { simp only [insert_nth, modify_nth_tail],
    transitivity,
    { apply perm.cons, apply l_ih,
      apply nat.le_of_succ_le_succ h },
    { apply perm.swap } }
end

theorem perm.union_right {l₁ l₂ : list α} (t₁ : list α) (h : l₁ ~ l₂) : l₁ ∪ t₁ ~ l₂ ∪ t₁ :=
begin
  induction h with a _ _ _ ih _ _ _ _ _ _ _ _ ih_1 ih_2; try {simp},
  { exact ih.insert a },
  { apply perm_insert_swap },
  { exact ih_1.trans ih_2 }
end

theorem perm.union_left (l : list α) {t₁ t₂ : list α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ :=
by induction l; simp [*, perm.insert]

-- @[congr]
theorem perm.union {l₁ l₂ t₁ t₂ : list α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
(p₁.union_right t₁).trans (p₂.union_left l₂)

theorem perm.inter_right {l₁ l₂ : list α} (t₁ : list α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ :=
perm.filter _

theorem perm.inter_left (l : list α) {t₁ t₂ : list α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
filter_congr' (λ a _, p.mem_iff)

-- @[congr]
theorem perm.inter {l₁ l₂ t₁ t₂ : list α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
p₂.inter_left l₂ ▸ p₁.inter_right t₁

theorem perm.inter_append {l t₁ t₂ : list α} (h : disjoint t₁ t₂) :
  l ∩ (t₁ ++ t₂) ~ l ∩ t₁ ++ l ∩ t₂ :=
begin
  induction l,
  case list.nil
  { simp },
  case list.cons : x xs l_ih
  { by_cases h₁ : x ∈ t₁,
    { have h₂ : x ∉ t₂ := h h₁,
      simp * },
    by_cases h₂ : x ∈ t₂,
    { simp only [*, inter_cons_of_not_mem, false_or, mem_append, inter_cons_of_mem, not_false_iff],
      transitivity,
      { apply perm.cons _ l_ih, },
      change [x] ++ xs ∩ t₁ ++ xs ∩ t₂ ~ xs ∩ t₁ ++ ([x] ++ xs ∩ t₂),
      rw [← list.append_assoc],
      solve_by_elim [perm.append_right, perm_append_comm] },
    { simp * } },
end

end

theorem perm.pairwise_iff {R : α → α → Prop} (S : symmetric R) :
  ∀ {l₁ l₂ : list α} (p : l₁ ~ l₂), pairwise R l₁ ↔ pairwise R l₂ :=
suffices ∀ {l₁ l₂}, l₁ ~ l₂ → pairwise R l₁ → pairwise R l₂, from λ l₁ l₂ p, ⟨this p, this p.symm⟩,
λ l₁ l₂ p d, begin
  induction d with a l₁ h d IH generalizing l₂,
  { rw ← p.nil_eq, constructor },
  { have : a ∈ l₂ := p.subset (mem_cons_self _ _),
    rcases mem_split this with ⟨s₂, t₂, rfl⟩,
    have p' := (p.trans perm_middle).cons_inv,
    refine (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩),
    exact h _ (p'.symm.subset m) }
end

lemma pairwise.perm {R : α → α → Prop} {l l' : list α} (hR : l.pairwise R)
  (hl : l ~ l') (hsymm : symmetric R) : l'.pairwise R :=
(hl.pairwise_iff hsymm).mp hR

lemma perm.pairwise {R : α → α → Prop} {l l' : list α}
  (hl : l ~ l') (hR : l.pairwise R) (hsymm : symmetric R) : l'.pairwise R :=
hR.perm hl hsymm

theorem perm.nodup_iff {l₁ l₂ : list α} : l₁ ~ l₂ → (nodup l₁ ↔ nodup l₂) :=
perm.pairwise_iff $ @ne.symm α

theorem perm.join {l₁ l₂ : list (list α)} (h : l₁ ~ l₂) : l₁.join ~ l₂.join :=
perm.rec_on h
  (perm.refl _)
  (λ x xs₁ xs₂ hxs ih, ih.append_left x)
  (λ x₁ x₂ xs, by simpa only [join, append_assoc] using perm_append_comm.append_right _)
  (λ xs₁ xs₂ xs₃ h₁₂ h₂₃, perm.trans)

theorem perm.bind_right {l₁ l₂ : list α} (f : α → list β) (p : l₁ ~ l₂) :
  l₁.bind f ~ l₂.bind f :=
(p.map _).join

lemma perm.join_congr :
  ∀ {l₁ l₂ : list (list α)} (h : list.forall₂ (~) l₁ l₂), l₁.join ~ l₂.join
| _ _                 forall₂.nil          := perm.refl _
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := h₁.append (perm.join_congr h₂)

theorem perm.bind_left (l : list α) {f g : α → list β} (h : ∀ a ∈ l, f a ~ g a) :
  l.bind f ~ l.bind g :=
perm.join_congr $
  by rwa [list.forall₂_map_right_iff,list.forall₂_map_left_iff, list.forall₂_same]

theorem bind_append_perm (l : list α) (f g : α → list β) :
  l.bind f ++ l.bind g ~ l.bind (λ x, f x ++ g x) :=
begin
  induction l with a l IH; simp,
  refine (perm.trans _ (IH.append_left _)).append_left _,
  rw [← append_assoc, ← append_assoc],
  exact perm_append_comm.append_right _
end

theorem map_append_bind_perm (l : list α) (f : α → β) (g : α → list β) :
  l.map f ++ l.bind g ~ l.bind (λ x, f x :: g x) :=
by simpa [←map_eq_bind] using bind_append_perm l (λ x, [f x]) g

theorem perm.product_right {l₁ l₂ : list α} (t₁ : list β) (p : l₁ ~ l₂) :
  product l₁ t₁ ~ product l₂ t₁ :=
p.bind_right _

theorem perm.product_left (l : list α) {t₁ t₂ : list β} (p : t₁ ~ t₂) :
  product l t₁ ~ product l t₂ :=
perm.bind_left _ $ λ a ha, p.map _

@[congr] theorem perm.product {l₁ l₂ : list α} {t₁ t₂ : list β}
  (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : product l₁ t₁ ~ product l₂ t₂ :=
(p₁.product_right t₁).trans (p₂.product_left l₂)

theorem perm_lookmap (f : α → option α) {l₁ l₂ : list α}
  (H : pairwise (λ a b, ∀ (c ∈ f a) (d ∈ f b), a = b ∧ c = d) l₁)
  (p : l₁ ~ l₂) : lookmap f l₁ ~ lookmap f l₂ :=
begin
  let F := λ a b, ∀ (c ∈ f a) (d ∈ f b), a = b ∧ c = d,
  change pairwise F l₁ at H,
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {simp},
  { cases h : f a,
    { simp [h], exact IH (pairwise_cons.1 H).2 },
    { simp [lookmap_cons_some _ _ h, p] } },
  { cases h₁ : f a with c; cases h₂ : f b with d,
    { simp [h₁, h₂], apply swap },
    { simp [h₁, lookmap_cons_some _ _ h₂], apply swap },
    { simp [lookmap_cons_some _ _ h₁, h₂], apply swap },
    { simp [lookmap_cons_some _ _ h₁, lookmap_cons_some _ _ h₂],
      rcases (pairwise_cons.1 H).1 _ (or.inl rfl) _ h₂ _ h₁ with ⟨rfl, rfl⟩,
      refl } },
  { refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H)),
    exact λ a b h c h₁ d h₂, (h d h₂ c h₁).imp eq.symm eq.symm }
end

theorem perm.erasep (f : α → Prop) [decidable_pred f] {l₁ l₂ : list α}
  (H : pairwise (λ a b, f a → f b → false) l₁)
  (p : l₁ ~ l₂) : erasep f l₁ ~ erasep f l₂ :=
begin
  let F := λ a b, f a → f b → false,
  change pairwise F l₁ at H,
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {simp},
  { by_cases h : f a,
    { simp [h, p] },
    { simp [h], exact IH (pairwise_cons.1 H).2 } },
  { by_cases h₁ : f a; by_cases h₂ : f b; simp [h₁, h₂],
    { cases (pairwise_cons.1 H).1 _ (or.inl rfl) h₂ h₁ },
    { apply swap } },
  { refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H)),
    exact λ a b h h₁ h₂, h h₂ h₁ }
end

lemma perm.take_inter {α} [decidable_eq α] {xs ys : list α} (n : ℕ)
  (h : xs ~ ys) (h' : ys.nodup) :
  xs.take n ~ ys.inter (xs.take n) :=
begin
  simp only [list.inter] at *,
  induction h generalizing n,
  case list.perm.nil : n
  { simp only [not_mem_nil, filter_false, take_nil] },
  case list.perm.cons : h_x h_l₁ h_l₂ h_a h_ih n
  { cases n; simp only [mem_cons_iff, true_or, eq_self_iff_true, filter_cons_of_pos,
                        perm_cons, take, not_mem_nil, filter_false],
    cases h' with _ _ h₁ h₂,
    convert h_ih h₂ n using 1,
    apply filter_congr',
    introv h, simp only [(h₁ x h).symm, false_or], },
  case list.perm.swap : h_x h_y h_l n
  { cases h' with _ _ h₁ h₂,
    cases h₂ with _ _ h₂ h₃,
    have := h₁ _ (or.inl rfl),
    cases n; simp only [mem_cons_iff, not_mem_nil, filter_false, take],
    cases n; simp only [mem_cons_iff, false_or, true_or, filter, *, nat.nat_zero_eq_zero, if_true,
                        not_mem_nil, eq_self_iff_true, or_false, if_false, perm_cons, take],
    { rw filter_eq_nil.2, intros, solve_by_elim [ne.symm], },
    { convert perm.swap _ _ _, rw @filter_congr' _ _ (∈ take n h_l),
      { clear h₁, induction n generalizing h_l, { simp },
        cases h_l; simp only [mem_cons_iff, true_or, eq_self_iff_true, filter_cons_of_pos,
                              true_and, take, not_mem_nil, filter_false, take_nil],
        cases h₃ with _ _ h₃ h₄,
        rwa [@filter_congr' _ _ (∈ take n_n h_l_tl), n_ih],
        { introv h, apply h₂ _ (or.inr h), },
        { introv h, simp only [(h₃ x h).symm, false_or], }, },
      { introv h, simp only [(h₂ x h).symm, (h₁ x (or.inr h)).symm, false_or], } } },
  case list.perm.trans : h_l₁ h_l₂ h_l₃ h₀ h₁ h_ih₀ h_ih₁ n
  { transitivity,
    { apply h_ih₀, rwa h₁.nodup_iff },
    { apply perm.filter _ h₁, } },
end

lemma perm.drop_inter {α} [decidable_eq α] {xs ys : list α} (n : ℕ)
  (h : xs ~ ys) (h' : ys.nodup) :
  xs.drop n ~ ys.inter (xs.drop n) :=
begin
  by_cases h'' : n ≤ xs.length,
  { let n' := xs.length - n,
    have h₀ : n = xs.length - n',
    { dsimp [n'], rwa tsub_tsub_cancel_of_le, } ,
    have h₁ : n' ≤ xs.length,
    { apply tsub_le_self },
    have h₂ : xs.drop n = (xs.reverse.take n').reverse,
    { rw [reverse_take _ h₁, h₀, reverse_reverse], },
    rw [h₂],
    apply (reverse_perm _).trans,
    rw inter_reverse,
    apply perm.take_inter _ _ h',
    apply (reverse_perm _).trans; assumption, },
  { have : drop n xs = [],
    { apply eq_nil_of_length_eq_zero,
      rw [length_drop, tsub_eq_zero_iff_le],
      apply le_of_not_ge h'' },
    simp [this, list.inter], }
end

lemma perm.slice_inter {α} [decidable_eq α] {xs ys : list α} (n m : ℕ)
  (h : xs ~ ys) (h' : ys.nodup) :
  list.slice n m xs ~ ys ∩ (list.slice n m xs) :=
begin
  simp only [slice_eq],
  have : n ≤ n + m := nat.le_add_right _ _,
  have := h.nodup_iff.2 h',
  apply perm.trans _ (perm.inter_append _).symm;
  solve_by_elim [perm.append, perm.drop_inter, perm.take_inter, disjoint_take_drop, h, h']
      { max_depth := 7 },
end

/- enumerating permutations -/

section permutations

theorem perm_of_mem_permutations_aux :
  ∀ {ts is l : list α}, l ∈ permutations_aux ts is → l ~ ts ++ is :=
begin
  refine permutations_aux.rec (by simp) _,
  introv IH1 IH2 m,
  rw [permutations_aux_cons, permutations, mem_foldr_permutations_aux2] at m,
  rcases m with m | ⟨l₁, l₂, m, _, e⟩,
  { exact (IH1 m).trans perm_middle },
  { subst e,
    have p : l₁ ++ l₂ ~ is,
    { simp [permutations] at m,
      cases m with e m, {simp [e]},
      exact is.append_nil ▸ IH2 m },
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _) }
end

theorem perm_of_mem_permutations {l₁ l₂ : list α}
  (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
(eq_or_mem_of_mem_cons h).elim (λ e, e ▸ perm.refl _)
  (λ m, append_nil l₂ ▸ perm_of_mem_permutations_aux m)

theorem length_permutations_aux : ∀ ts is : list α,
  length (permutations_aux ts is) + is.length! = (length ts + length is)! :=
begin
  refine permutations_aux.rec (by simp) _,
  intros t ts is IH1 IH2,
  have IH2 : length (permutations_aux is nil) + 1 = is.length!,
  { simpa using IH2 },
  simp [-add_comm, nat.factorial, nat.add_succ, mul_comm] at IH1,
  rw [permutations_aux_cons,
      length_foldr_permutations_aux2' _ _ _ _ _
        (λ l m, (perm_of_mem_permutations m).length_eq),
      permutations, length, length, IH2,
      nat.succ_add, nat.factorial_succ, mul_comm (nat.succ _), ← IH1,
      add_comm (_*_), add_assoc, nat.mul_succ, mul_comm]
end

theorem length_permutations (l : list α) : length (permutations l) = (length l)! :=
length_permutations_aux l []

theorem mem_permutations_of_perm_lemma {is l : list α}
  (H : l ~ [] ++ is → (∃ ts' ~ [], l = ts' ++ is) ∨ l ∈ permutations_aux is [])
  : l ~ is → l ∈ permutations is :=
by simpa [permutations, perm_nil] using H

theorem mem_permutations_aux_of_perm :
  ∀ {ts is l : list α}, l ~ is ++ ts → (∃ is' ~ is, l = is' ++ ts) ∨ l ∈ permutations_aux ts is :=
begin
  refine permutations_aux.rec (by simp) _,
  intros t ts is IH1 IH2 l p,
  rw [permutations_aux_cons, mem_foldr_permutations_aux2],
  rcases IH1 (p.trans perm_middle) with ⟨is', p', e⟩ | m,
  { clear p, subst e,
    rcases mem_split (p'.symm.subset (mem_cons_self _ _)) with ⟨l₁, l₂, e⟩,
    subst is',
    have p := (perm_middle.symm.trans p').cons_inv,
    cases l₂ with a l₂',
    { exact or.inl ⟨l₁, by simpa using p⟩ },
    { exact or.inr (or.inr ⟨l₁, a::l₂',
        mem_permutations_of_perm_lemma IH2 p, by simp⟩) } },
  { exact or.inr (or.inl m) }
end

@[simp] theorem mem_permutations {s t : list α} : s ∈ permutations t ↔ s ~ t :=
⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutations_aux_of_perm⟩

theorem perm_permutations'_aux_comm (a b : α) (l : list α) :
  (permutations'_aux a l).bind (permutations'_aux b) ~
  (permutations'_aux b l).bind (permutations'_aux a) :=
begin
  induction l with c l ih, {simp [swap]},
  simp [permutations'_aux], apply perm.swap',
  have : ∀ a b,
    (map (cons c) (permutations'_aux a l)).bind (permutations'_aux b) ~
    map (cons b ∘ cons c) (permutations'_aux a l) ++
    map (cons c) ((permutations'_aux a l).bind (permutations'_aux b)),
  { intros,
    simp only [map_bind, permutations'_aux],
    refine (bind_append_perm _ (λ x, [_]) _).symm.trans _,
    rw [← map_eq_bind, ← bind_map] },
  refine (((this _ _).append_left _).trans _).trans ((this _ _).append_left _).symm,
  rw [← append_assoc, ← append_assoc],
  exact perm_append_comm.append (ih.map _),
end

theorem perm.permutations' {s t : list α} (p : s ~ t) :
  permutations' s ~ permutations' t :=
begin
  induction p with a s t p IH a b l s t u p₁ p₂ IH₁ IH₂, {simp},
  { simp only [permutations'], exact IH.bind_right _ },
  { simp only [permutations'],
    rw [bind_assoc, bind_assoc],
    apply perm.bind_left,
    intros l' hl',
    apply perm_permutations'_aux_comm },
  { exact IH₁.trans IH₂ }
end

theorem permutations_perm_permutations' (ts : list α) : ts.permutations ~ ts.permutations' :=
begin
  obtain ⟨n, h⟩ : ∃ n, length ts < n := ⟨_, nat.lt_succ_self _⟩,
  induction n with n IH generalizing ts, {cases h},
  refine list.reverse_rec_on ts (λ h, _) (λ ts t _ h, _) h, {simp [permutations]},
  rw [← concat_eq_append, length_concat, nat.succ_lt_succ_iff] at h,
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations',
  simp only [permutations_append, foldr_permutations_aux2,
    permutations_aux_nil, permutations_aux_cons, append_nil],
  refine (perm_append_comm.trans ((IH₂.bind_right _).append ((IH _ h).map _))).trans
    (perm.trans _ perm_append_comm.permutations'),
  rw [map_eq_bind, singleton_append, permutations'],
  convert bind_append_perm _ _ _, funext ys,
  rw [permutations'_aux_eq_permutations_aux2, permutations_aux2_append]
end

@[simp] theorem mem_permutations' {s t : list α} : s ∈ permutations' t ↔ s ~ t :=
(permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

theorem perm.permutations {s t : list α} (h : s ~ t) : permutations s ~ permutations t :=
(permutations_perm_permutations' _).trans $ h.permutations'.trans
(permutations_perm_permutations' _).symm

@[simp] theorem perm_permutations_iff {s t : list α} : permutations s ~ permutations t ↔ s ~ t :=
⟨λ h, mem_permutations.1 $ h.mem_iff.1 $ mem_permutations.2 (perm.refl _), perm.permutations⟩

@[simp] theorem perm_permutations'_iff {s t : list α} : permutations' s ~ permutations' t ↔ s ~ t :=
⟨λ h, mem_permutations'.1 $ h.mem_iff.1 $ mem_permutations'.2 (perm.refl _), perm.permutations'⟩

lemma nth_le_permutations'_aux (s : list α) (x : α) (n : ℕ)
  (hn : n < length (permutations'_aux x s)) :
  (permutations'_aux x s).nth_le n hn = s.insert_nth n x :=
begin
  induction s with y s IH generalizing n,
  { simp only [length, permutations'_aux, nat.lt_one_iff] at hn,
    simp [hn] },
  { cases n,
    { simp },
    { simpa using IH _ _ } }
end

lemma count_permutations'_aux_self [decidable_eq α] (l : list α) (x : α) :
  count (x :: l) (permutations'_aux x l) = length (take_while ((=) x) l) + 1 :=
begin
  induction l with y l IH generalizing x,
  { simp [take_while], },
  { rw [permutations'_aux, count_cons_self],
    by_cases hx : x = y,
    { subst hx,
      simpa [take_while, nat.succ_inj'] using IH _ },
    { rw take_while,
      rw if_neg hx,
      cases permutations'_aux x l with a as,
      { simp },
      { rw [count_eq_zero_of_not_mem, length, zero_add],
        simp [hx, ne.symm hx] } } }
end

@[simp] lemma length_permutations'_aux (s : list α) (x : α) :
  length (permutations'_aux x s) = length s + 1 :=
begin
  induction s with y s IH,
  { simp },
  { simpa using IH }
end

@[simp] lemma permutations'_aux_nth_le_zero (s : list α) (x : α)
  (hn : 0 < length (permutations'_aux x s) := by simp) :
  (permutations'_aux x s).nth_le 0 hn = x :: s :=
nth_le_permutations'_aux _ _ _ _

lemma injective_permutations'_aux (x : α) : function.injective (permutations'_aux x) :=
begin
  intros s t h,
  apply insert_nth_injective s.length x,
  have hl : s.length = t.length := by simpa using congr_arg length h,
  rw [←nth_le_permutations'_aux s x s.length (by simp),
      ←nth_le_permutations'_aux t x s.length (by simp [hl])],
  simp [h, hl]
end

lemma nodup_permutations'_aux_of_not_mem (s : list α) (x : α) (hx : x ∉ s) :
  nodup (permutations'_aux x s) :=
begin
  induction s with y s IH,
  { simp },
  { simp only [not_or_distrib, mem_cons_iff] at hx,
    simp only [not_and, exists_eq_right_right, mem_map, permutations'_aux, nodup_cons],
    refine ⟨λ _, ne.symm hx.left, _⟩,
    rw nodup_map_iff,
    { exact IH hx.right },
    { simp } }
end

lemma nodup_permutations'_aux_iff {s : list α} {x : α} :
  nodup (permutations'_aux x s) ↔ x ∉ s :=
begin
  refine ⟨λ h, _, nodup_permutations'_aux_of_not_mem _ _⟩,
  intro H,
  obtain ⟨k, hk, hk'⟩ := nth_le_of_mem H,
  rw nodup_iff_nth_le_inj at h,
  suffices : k = k + 1,
  { simpa using this },
  refine h k (k + 1) _ _ _,
  { simpa [nat.lt_succ_iff] using hk.le },
  { simpa using hk },
  rw [nth_le_permutations'_aux, nth_le_permutations'_aux],
  have hl : length (insert_nth k x s) = length (insert_nth (k + 1) x s),
  { rw [length_insert_nth _ _ hk.le, length_insert_nth _ _ (nat.succ_le_of_lt hk)] },
  refine ext_le hl (λ n hn hn', _),
  rcases lt_trichotomy n k with H|rfl|H,
  { rw [nth_le_insert_nth_of_lt _ _ _ _ H (H.trans hk),
        nth_le_insert_nth_of_lt _ _ _ _ (H.trans (nat.lt_succ_self _))] },
  { rw [nth_le_insert_nth_self _ _ _ hk.le,
        nth_le_insert_nth_of_lt _ _ _ _ (nat.lt_succ_self _) hk, hk'] },
  { rcases (nat.succ_le_of_lt H).eq_or_lt with rfl|H',
    { rw [nth_le_insert_nth_self _ _ _ (nat.succ_le_of_lt hk)],
      convert hk' using 1,
      convert nth_le_insert_nth_add_succ _ _ _ 0 _,
      simpa using hk },
    { obtain ⟨m, rfl⟩ := nat.exists_eq_add_of_lt H',
      rw [length_insert_nth _ _ hk.le, nat.succ_lt_succ_iff, nat.succ_add] at hn,
      rw nth_le_insert_nth_add_succ,
      convert nth_le_insert_nth_add_succ s x k m.succ _ using 2,
      { simp [nat.add_succ, nat.succ_add] },
      { simp [add_left_comm, add_comm] },
      { simpa [nat.add_succ] using hn },
      { simpa [nat.succ_add] using hn } } }
end

lemma nodup_permutations (s : list α) (hs : nodup s) :
  nodup s.permutations :=
begin
  rw (permutations_perm_permutations' s).nodup_iff,
  induction hs with x l h h' IH,
  { simp },
  { rw [permutations'],
    rw nodup_bind,
    split,
    { intros ys hy,
      rw mem_permutations' at hy,
      rw [nodup_permutations'_aux_iff, hy.mem_iff],
      exact λ H, h x H rfl },
    { refine IH.pairwise_of_forall_ne (λ as ha bs hb H, _),
      rw disjoint_iff_ne,
      rintro a ha' b hb' rfl,
      obtain ⟨n, hn, hn'⟩ := nth_le_of_mem ha',
      obtain ⟨m, hm, hm'⟩ := nth_le_of_mem hb',
      rw mem_permutations' at ha hb,
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq,
      simp only [nat.lt_succ_iff, length_permutations'_aux] at hn hm,
      rw nth_le_permutations'_aux at hn' hm',
      have hx : nth_le (insert_nth n x as) m
        (by rwa [length_insert_nth _ _ hn, nat.lt_succ_iff, hl]) = x,
      { simp [hn', ←hm', hm] },
      have hx' : nth_le (insert_nth m x bs) n
        (by rwa [length_insert_nth _ _ hm, nat.lt_succ_iff, ←hl]) = x,
      { simp [hm', ←hn', hn] },
      rcases lt_trichotomy n m with ht|ht|ht,
      { suffices : x ∈ bs,
        { exact h x (hb.subset this) rfl },
        rw [←hx', nth_le_insert_nth_of_lt _ _ _ _ ht (ht.trans_le hm)],
        exact nth_le_mem _ _ _ },
      { simp only [ht] at hm' hn',
        rw ←hm' at hn',
        exact H (insert_nth_injective _ _ hn') },
      { suffices : x ∈ as,
        { exact h x (ha.subset this) rfl },
        rw [←hx, nth_le_insert_nth_of_lt _ _ _ _ ht (ht.trans_le hn)],
        exact nth_le_mem _ _ _ } } }
end

-- TODO: `nodup s.permutations ↔ nodup s`
-- TODO: `count s s.permutations = (zip_with count s s.tails).prod`

end permutations

end list
