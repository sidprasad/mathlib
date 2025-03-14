/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import data.list.pairwise
import logic.relation

/-!
# Relation chain

This file provides basic results about `list.chain` (definition in `data.list.defs`).
A list `[a₂, ..., aₙ]` is a `chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `chain r a₁ [a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

universes u v

open nat

namespace list

variables {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : list α} {a b : α}

mk_iff_of_inductive_prop list.chain list.chain_iff

theorem rel_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b :: l)) : R a b :=
(chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b :: l)) : chain R b l :=
(chain_cons.1 p).2

theorem chain.imp' {S : α → α → Prop}
  (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α} (Hab : ∀ ⦃c⦄, R a c → S b c)
  {l : list α} (p : chain R a l) : chain S b l :=
by induction p with _ a c l r p IH generalizing b; constructor;
   [exact Hab r, exact IH (@HRS _)]

theorem chain.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {a : α} {l : list α} (p : chain R a l) : chain S a l :=
p.imp' H (H a)

theorem chain.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {a : α} {l : list α} : chain R a l ↔ chain S a l :=
⟨chain.imp (λ a b, (H a b).1), chain.imp (λ a b, (H a b).2)⟩

theorem chain.iff_mem {a : α} {l : list α} :
  chain R a l ↔ chain (λ x y, x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
⟨λ p, by induction p with _ a b l r p IH; constructor;
  [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩,
   exact IH.imp (λ a b ⟨am, bm, h⟩,
    ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩)],
 chain.imp (λ a b h, h.2.2)⟩

theorem chain_singleton {a b : α} : chain R a [b] ↔ R a b :=
by simp only [chain_cons, chain.nil, and_true]

theorem chain_split {a b : α} {l₁ l₂ : list α} : chain R a (l₁ ++ b :: l₂) ↔
  chain R a (l₁ ++ [b]) ∧ chain R b l₂ :=
by induction l₁ with x l₁ IH generalizing a;
simp only [*, nil_append, cons_append, chain.nil, chain_cons, and_true, and_assoc]

@[simp] theorem chain_append_cons_cons {a b c : α} {l₁ l₂ : list α} :
  chain R a (l₁ ++ b :: c :: l₂) ↔ chain R a (l₁ ++ [b]) ∧ R b c ∧ chain R c l₂ :=
by rw [chain_split, chain_cons]

theorem chain_iff_forall₂ :
  ∀ {a : α} {l : list α}, chain R a l ↔ l = [] ∨ forall₂ R (a :: init l) l
| a [] := by simp
| a [b] := by simp [init]
| a (b :: c :: l) := by simp [@chain_iff_forall₂ b]

theorem chain_append_singleton_iff_forall₂ :
  chain R a (l ++ [b]) ↔ forall₂ R (a :: l) (l ++ [b]) :=
by simp [chain_iff_forall₂, init]

theorem chain_map (f : β → α) {b : β} {l : list β} :
  chain R (f b) (map f l) ↔ chain (λ a b : β, R (f a) (f b)) b l :=
by induction l generalizing b; simp only [map, chain.nil, chain_cons, *]

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {a : α} {l : list α}
  (p : chain S (f a) (map f l)) : chain R a l :=
((chain_map f).1 p).imp H

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {a : α} {l : list α}
  (p : chain R a l) : chain S (f a) (map f l) :=
(chain_map f).2 $ p.imp H

theorem chain_pmap_of_chain {S : β → β → Prop} {p : α → Prop}
  {f : Π a, p a → β}
  (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb))
  {a : α} {l : list α}
  (hl₁ : chain R a l) (ha : p a) (hl₂ : ∀ a ∈ l, p a) :
  chain S (f a ha) (list.pmap f l hl₂) :=
begin
  induction l with lh lt l_ih generalizing a,
  { simp },
  { simp [H _ _ _ _ (rel_of_chain_cons hl₁), l_ih _ (chain_of_chain_cons hl₁)] }
end

theorem chain_of_chain_pmap {S : β → β → Prop} {p : α → Prop}
  (f : Π a, p a → β) {l : list α} (hl₁ : ∀ a ∈ l, p a)
  {a : α} (ha : p a) (hl₂ : chain S (f a ha) (list.pmap f l hl₁))
  (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) :
  chain R a l :=
begin
  induction l with lh lt l_ih generalizing a,
  { simp },
  { simp [H _ _ _ _ (rel_of_chain_cons hl₂), l_ih _ _ (chain_of_chain_cons hl₂)] }
end

protected lemma pairwise.chain (p : pairwise R (a :: l)) : chain R a l :=
begin
  cases pairwise_cons.1 p with r p', clear p,
  induction p' with b l r' p IH generalizing a, {exact chain.nil},
  simp only [chain_cons, forall_mem_cons] at r,
  exact chain_cons.2 ⟨r.1, IH r'⟩
end

protected lemma chain.pairwise [is_trans α R] :
  ∀ {a : α} {l : list α}, chain R a l → pairwise R (a :: l)
| a [] chain.nil := pairwise_singleton _ _
| a _ (@chain.cons _ _ _ b l h hb) := hb.pairwise.cons begin
    simp only [mem_cons_iff, forall_eq_or_imp, h, true_and],
    exact λ c hc, trans h (rel_of_pairwise_cons hb.pairwise hc),
  end

theorem chain_iff_pairwise [is_trans α R] {a : α} {l : list α} :
  chain R a l ↔ pairwise R (a :: l) :=
⟨chain.pairwise, pairwise.chain⟩

protected lemma chain.sublist [is_trans α R] (hl : l₂.chain R a) (h : l₁ <+ l₂) : l₁.chain R a :=
by { rw chain_iff_pairwise at ⊢ hl, exact hl.sublist (h.cons_cons a) }

protected lemma chain.rel [is_trans α R] (hl : l.chain R a) (hb : b ∈ l) : R a b :=
by { rw chain_iff_pairwise at hl, exact rel_of_pairwise_cons hl hb }

theorem chain_iff_nth_le {R} : ∀ {a : α} {l : list α},
  chain R a l ↔ (∀ h : 0 < length l, R a (nth_le l 0 h)) ∧ (∀ i (h : i < length l - 1),
    R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h)))
| a []       := by simp
| a (b :: t) :=
begin
  rw [chain_cons, chain_iff_nth_le],
  split,
  { rintro ⟨R, ⟨h0, h⟩⟩,
    split,
    { intro w, exact R },
    intros i w,
    cases i,
    { apply h0 },
    convert h i _ using 1,
    simp only [succ_eq_add_one, add_succ_sub_one, add_zero, length, add_lt_add_iff_right] at w,
    exact lt_pred_iff.mpr w, },
  rintro ⟨h0, h⟩, split,
  { apply h0, simp, },
  split,
  { apply h 0, },
  intros i w, convert h (i+1) _ using 1,
  exact lt_pred_iff.mp w,
end

theorem chain'.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {l : list α} (p : chain' R l) : chain' S l :=
by cases l; [trivial, exact p.imp H]

theorem chain'.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {l : list α} : chain' R l ↔ chain' S l :=
⟨chain'.imp (λ a b, (H a b).1), chain'.imp (λ a b, (H a b).2)⟩

theorem chain'.iff_mem : ∀ {l : list α}, chain' R l ↔ chain' (λ x y, x ∈ l ∧ y ∈ l ∧ R x y) l
| []       := iff.rfl
| (x :: l) :=
  ⟨λ h, (chain.iff_mem.1 h).imp $ λ a b ⟨h₁, h₂, h₃⟩, ⟨h₁, or.inr h₂, h₃⟩,
   chain'.imp $ λ a b h, h.2.2⟩

@[simp] theorem chain'_nil : chain' R [] := trivial

@[simp] theorem chain'_singleton (a : α) : chain' R [a] := chain.nil

@[simp] theorem chain'_cons {x y l} : chain' R (x :: y :: l) ↔ R x y ∧ chain' R (y :: l) :=
chain_cons

theorem chain'_is_infix : ∀ l : list α, chain' (λ x y, [x, y] <:+: l) l
| [] := chain'_nil
| [a] := chain'_singleton _
| (a::b::l) := chain'_cons.2 ⟨⟨[], l, by simp⟩,
  (chain'_is_infix (b::l)).imp $ λ x y h, h.trans ⟨[a], [], by simp⟩⟩

theorem chain'_split {a : α} : ∀ {l₁ l₂ : list α}, chain' R (l₁ ++ a :: l₂) ↔
  chain' R (l₁ ++ [a]) ∧ chain' R (a :: l₂)
| []        l₂ := (and_iff_right (chain'_singleton a)).symm
| (b :: l₁) l₂ := chain_split

@[simp] theorem chain'_append_cons_cons {b c : α} {l₁ l₂ : list α} :
  chain' R (l₁ ++ b :: c :: l₂) ↔ chain' R (l₁ ++ [b]) ∧ R b c ∧ chain' R (c :: l₂) :=
by rw [chain'_split, chain'_cons]

theorem chain'_map (f : β → α) {l : list β} :
  chain' R (map f l) ↔ chain' (λ a b : β, R (f a) (f b)) l :=
by cases l; [refl, exact chain_map _]

theorem chain'_of_chain'_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {l : list α}
  (p : chain' S (map f l)) : chain' R l :=
((chain'_map f).1 p).imp H

theorem chain'_map_of_chain' {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {l : list α}
  (p : chain' R l) : chain' S (map f l) :=
(chain'_map f).2 $ p.imp H

theorem pairwise.chain' : ∀ {l : list α}, pairwise R l → chain' R l
| []       _ := trivial
| (a :: l) h := pairwise.chain h

theorem chain'_iff_pairwise [is_trans α R] : ∀ {l : list α},
  chain' R l ↔ pairwise R l
| []       := (iff_true_intro pairwise.nil).symm
| (a :: l) := chain_iff_pairwise

protected lemma chain'.sublist [is_trans α R] (hl : l₂.chain' R) (h : l₁ <+ l₂) : l₁.chain' R :=
by { rw chain'_iff_pairwise at ⊢ hl, exact hl.sublist h }

theorem chain'.cons {x y l} (h₁ : R x y) (h₂ : chain' R (y :: l)) :
  chain' R (x :: y :: l) :=
chain'_cons.2 ⟨h₁, h₂⟩

theorem chain'.tail : ∀ {l} (h : chain' R l), chain' R l.tail
| []            _ := trivial
| [x]           _ := trivial
| (x :: y :: l) h := (chain'_cons.mp h).right

theorem chain'.rel_head {x y l} (h : chain' R (x :: y :: l)) : R x y :=
rel_of_chain_cons h

theorem chain'.rel_head' {x l} (h : chain' R (x :: l)) ⦃y⦄ (hy : y ∈ head' l) : R x y :=
by { rw ← cons_head'_tail hy at h, exact h.rel_head }

theorem chain'.cons' {x} :
  ∀ {l : list α},  chain' R l → (∀ y ∈ l.head', R x y) → chain' R (x :: l)
| []       _  _ := chain'_singleton x
| (a :: l) hl H := hl.cons $ H _ rfl

theorem chain'_cons' {x l} : chain' R (x :: l) ↔ (∀ y ∈ head' l, R x y) ∧ chain' R l :=
⟨λ h, ⟨h.rel_head', h.tail⟩, λ ⟨h₁, h₂⟩, h₂.cons' h₁⟩

theorem chain'_append : ∀ {l₁ l₂ : list α},
  chain' R (l₁ ++ l₂) ↔ chain' R l₁ ∧ chain' R l₂ ∧ ∀ (x ∈ l₁.last') (y ∈ l₂.head'), R x y
| [] l := by simp
| [a] l := by simp [chain'_cons', and_comm]
| (a :: b :: l₁) l₂ := by rw [cons_append, cons_append, chain'_cons, chain'_cons, ← cons_append,
  chain'_append, last', and.assoc]

theorem chain'.append (h₁ : chain' R l₁) (h₂ : chain' R l₂)
  (h : ∀ (x ∈ l₁.last') (y ∈ l₂.head'), R x y) :
  chain' R (l₁ ++ l₂) :=
chain'_append.2 ⟨h₁, h₂, h⟩

theorem chain'.left_of_append (h : chain' R (l₁ ++ l₂)) : chain' R l₁ := (chain'_append.1 h).1
theorem chain'.right_of_append (h : chain' R (l₁ ++ l₂)) : chain' R l₂ := (chain'_append.1 h).2.1

theorem chain'.infix (h : chain' R l) (h' : l₁ <:+: l) : chain' R l₁ :=
by { rcases h' with ⟨l₂, l₃, rfl⟩, exact h.left_of_append.right_of_append }

theorem chain'.suffix (h : chain' R l) (h' : l₁ <:+ l) : chain' R l₁ := h.infix h'.is_infix
theorem chain'.prefix (h : chain' R l) (h' : l₁ <+: l) : chain' R l₁ := h.infix h'.is_infix
theorem chain'.drop (h : chain' R l) (n : ℕ) : chain' R (drop n l) := h.suffix (drop_suffix _ _)
theorem chain'.init (h : chain' R l) : chain' R l.init := h.prefix l.init_prefix
theorem chain'.take (h : chain' R l) (n : ℕ) : chain' R (take n l) := h.prefix (take_prefix _ _)

theorem chain'_pair {x y} : chain' R [x, y] ↔ R x y :=
by simp only [chain'_singleton, chain'_cons, and_true]

theorem chain'.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : chain' R (x :: l)) :
  chain' R (y :: l) :=
hl.tail.cons' $ λ z hz, h $ hl.rel_head' hz

theorem chain'_reverse : ∀ {l}, chain' R (reverse l) ↔ chain' (flip R) l
| []            := iff.rfl
| [a]           := by simp only [chain'_singleton, reverse_singleton]
| (a :: b :: l) := by rw [chain'_cons, reverse_cons, reverse_cons, append_assoc, cons_append,
    nil_append, chain'_split, ← reverse_cons, @chain'_reverse (b :: l), and_comm, chain'_pair, flip]

theorem chain'_iff_nth_le {R} : ∀ {l : list α},
  chain' R l ↔ ∀ i (h : i < length l - 1),
    R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h))
| []            := by simp
| [a]           := by simp
| (a :: b :: t) :=
begin
  rw [← and_forall_succ, chain'_cons, chain'_iff_nth_le],
  simp only [length, nth_le, add_tsub_cancel_right, add_lt_add_iff_right, tsub_pos_iff_lt,
    one_lt_succ_succ, true_implies_iff],
  refl,
end

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
lemma chain'.append_overlap {l₁ l₂ l₃ : list α}
  (h₁ : chain' R (l₁ ++ l₂)) (h₂ : chain' R (l₂ ++ l₃)) (hn : l₂ ≠ []) :
  chain' R (l₁ ++ l₂ ++ l₃) :=
h₁.append h₂.right_of_append $
  by simpa only [last'_append_of_ne_nil _ hn] using (chain'_append.1 h₂).2.2

/--
If `a` and `b` are related by the reflexive transitive closure of `r`, then there is a `r`-chain
starting from `a` and ending on `b`.
The converse of `relation_refl_trans_gen_of_exists_chain`.
-/
lemma exists_chain_of_relation_refl_trans_gen (h : relation.refl_trans_gen r a b) :
  ∃ l, chain r a l ∧ last (a :: l) (cons_ne_nil _ _) = b :=
begin
  apply relation.refl_trans_gen.head_induction_on h,
  { exact ⟨[], chain.nil, rfl⟩ },
  { intros c d e t ih,
    obtain ⟨l, hl₁, hl₂⟩ := ih,
    refine ⟨d :: l, chain.cons e hl₁, _⟩,
    rwa last_cons_cons }
end

/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
lemma chain.induction (p : α → Prop)
  (l : list α) (h : chain r a l)
  (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : p b) : ∀ i ∈ a :: l, p i :=
begin
  induction l generalizing a,
  { cases hb,
    simp [final] },
  { rw chain_cons at h,
    rintro _ (rfl | _),
    apply carries h.1 (l_ih h.2 hb _ (or.inl rfl)),
    apply l_ih h.2 hb _ H }
end

/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_eliminator]
lemma chain.induction_head (p : α → Prop)
  (l : list α) (h : chain r a l)
  (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : p b) : p a :=
(chain.induction p l h hb carries final) _ (mem_cons_self _ _)

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`. The converse of `exists_chain_of_relation_refl_trans_gen`.
-/
lemma relation_refl_trans_gen_of_exists_chain (l) (hl₁ : chain r a l)
  (hl₂ : last (a :: l) (cons_ne_nil _ _) = b) :
  relation.refl_trans_gen r a b :=
chain.induction_head _ l hl₁ hl₂ (λ x y, relation.refl_trans_gen.head) relation.refl_trans_gen.refl

end list
