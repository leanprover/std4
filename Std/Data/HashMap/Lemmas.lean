/-
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF
import Std.Data.List.Lemmas
import Std.Data.List.Perm
import Std.Data.Array.Lemmas

/-- If there is at most one element with the property `p`, erasing one such element is the same
as filtering out all of them. -/
theorem List.eraseP_eq_filter_of_unique (l : List α) (p : α → Bool)
    : l.Pairwise (p · → !p ·) → l.eraseP p = l.filter (!p ·) := by
  intro h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    specialize ih (Pairwise.sublist (sublist_cons x xs) h)
    cases hP : p x with
    | true =>
      rw [Pairwise_cons] at h
      have : ∀ a ∈ xs, !p a := fun a hA => h.left a hA hP
      simp [eraseP, filter, hP, filter_eq_self.mpr this]
    | false => simp [eraseP_cons, filter, hP, ih]

theorem List.find?_eq_some {l : List α} {a : α} {p : α → Bool}
    : l.find? p = some a → a ∈ l ∧ p a := by
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    unfold find?
    cases hP : (p x)
    . intro h
      simp [List.mem_cons, ih h]
    . simp
      intro hEq
      simp [← hEq, hP]

/-- If there is at most one element with the property `p`, finding that one element is the same
as finding any. -/
theorem List.find?_eq_some_of_unique {l : List α} {a : α} {p : α → Bool}
    : l.Pairwise (p · → !p ·) → (l.find? p = some a ↔ (a ∈ l ∧ p a)) := by
  refine fun h => ⟨find?_eq_some, ?_⟩
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro ⟨hMem, hP⟩
    cases List.mem_cons.mp hMem with
    | inl hX => simp [find?, ← hX, hP]
    | inr hXs =>
      unfold find?
      cases hPX : (p x) with
      | false =>
        apply ih (List.Pairwise.sublist (List.sublist_cons x xs) h) ⟨hXs, hP⟩
      | true =>
        cases hP ▸ (Pairwise_cons.mp h |>.left a hXs hPX)

@[simp]
theorem List.foldl_cons_fn (l₁ l₂ : List α) :
    l₁.foldl (init := l₂) (fun acc x => x :: acc) = l₁.reverse ++ l₂ := by
  induction l₁ generalizing l₂ <;> simp [*]

@[simp]
theorem List.foldl_append_fn (l₁ : List α) (l₂ : List β) (f : α → List β) :
    l₁.foldl (init := l₂) (fun acc x => acc ++ f x) = l₂ ++ l₁.bind f := by
  induction l₁ generalizing l₂ <;> simp [*]

@[simp]
theorem List.map_replicate (n : Nat) (a : α) (f : α → β)
    : (replicate n a).map f = replicate n (f a) := by
  induction n <;> simp [*]

@[simp]
theorem List.get?_drop (l : List α) (n i : Nat) : (l.drop n).get? i = l.get? (n + i) :=
  go n l
where go : (n : Nat) → (l : List α) → (l.drop n).get? i = l.get? (n + i)
  | 0,   a     => by simp
  | _+1, []    => by simp
  | n+1, _::as => by
    have : n + 1 + i = n + i + 1 := by
      rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]
    simp [go n as, this]

theorem List.drop_ext (l₁ l₂ : List α) (j : Nat)
    : (∀ i ≥ j, l₁.get? i = l₂.get? i) → l₁.drop j = l₂.drop j := by
  intro H
  apply List.ext fun k => ?_
  rw [List.get?_drop, List.get?_drop]
  apply H _ (Nat.le_add_right _ _)

theorem Array.exists_get_of_mem_data {as : Array α} {a : α}
    : a ∈ as.data → ∃ (i : Fin as.size), a = as[i] := by
  rw [← Array.toList_eq, Array.toList]
  apply Array.foldr_induction
    (motive := fun _ acc => a ∈ acc → ∃ (i : Fin as.size), a = as[i])
  case h0 => intro h; cases h
  case hf =>
    intro i acc ih h
    cases List.mem_cons.mp h with
    | inl h => exact ⟨i, h⟩
    | inr h => exact ih h

namespace Std.HashMap
variable [BEq α] [Hashable α] [LawfulHashable α] [PartialEquivBEq α]

namespace Imp
open List

-- NOTE(WN): These would ideally be solved by a congruence-closure-for-PERs tactic
-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Rewriting.20congruent.20relations
private theorem beq_nonsense_1 {a b c : α} : a != b → a == c → b != c :=
  fun h₁ h₂ => Bool.bne_iff_not_beq.mpr fun h₃ =>
    Bool.bne_iff_not_beq.mp h₁ (PartialEquivBEq.trans h₂ (PartialEquivBEq.symm h₃))

private theorem beq_nonsense_2 {a b c : α} : a == b → b == c → ¬(c != a) :=
  fun h₁ h₂ h₃ => Bool.bne_iff_not_beq.mp (bne_symm h₃) (PartialEquivBEq.trans h₁ h₂)

namespace Buckets

/-- The contents of any given bucket are pairwise `bne`. -/
theorem Pairwise_bne_bucket (bkts : Buckets α β) (H : bkts.WF) (i : Nat) (h : i < bkts.val.size)
  : Pairwise (·.1 != ·.1) bkts.val[i].toList := by
  have := H.distinct bkts.val[i] (Array.getElem_mem_data _ _)
  exact List.Pairwise.imp Bool.bne_iff_not_beq.mpr this

/-- Reformulation of `Pairwise_bne_bucket` for use with `List.foo_of_unique`. -/
theorem Pairwise_bne_bucket' (bkts : Buckets α β) (H : bkts.WF) (i : Nat)
    (h : i < bkts.val.size) (a : α)
    : Pairwise (fun p q => p.1 == a → q.1 != a) bkts.val[i].toList :=
  List.Pairwise.imp beq_nonsense_1 (Pairwise_bne_bucket bkts H i h)

/-- It is a bit easier to reason about `foldl (append)` than `foldl (foldl)`, so we use this
(less efficient) variant of `toList` as the mathematical model. -/
def toListModel (bkts : Buckets α β) : List (α × β) :=
  -- Note(WN): the implementation is  `bkts.foldl` rather than `bkts.data.foldl` because we need
  -- to reason about array indices in some of the theorems.
  bkts.val.foldl (init := []) (fun acc bkt => acc ++ bkt.toList)

theorem mem_toListModel_iff_mem_bucket (bkts : Buckets α β) (H : bkts.WF) (a : α) (b : β)
    : haveI := mkIdx bkts.property a
      (a, b) ∈ bkts.toListModel ↔ (a, b) ∈ (bkts.val[this.1]'this.2).toList := by
  have : (a, b) ∈ bkts.toListModel ↔ ∃ bkt ∈ bkts.val.data, (a, b) ∈ bkt.toList := by
    simp [toListModel, Array.foldl_eq_foldl_data, List.foldl_append_fn, List.nil_append,
      List.mem_bind]
  rw [this]
  clear this
  apply Iff.intro
  . intro ⟨bkt, hBkt, hMem⟩
    have ⟨i, hGetI⟩ := Array.exists_get_of_mem_data hBkt
    simp only [getElem_fin] at hGetI
    suffices (mkIdx bkts.property a).val.toNat = i by
      simp [Array.ugetElem_eq_getElem, this, ← hGetI, hMem]
    unfold Imp.mkIdx
    dsimp
    exact H.hash_self i.val i.isLt (a, b) (hGetI ▸ hMem)
  . intro h
    refine ⟨_, Array.getElem_mem_data _ _, h⟩

/-- The map does not store duplicate (by `beq`) keys. -/
theorem Pairwise_bne_toListModel (bkts : Buckets α β) (H : bkts.WF)
    : bkts.toListModel.Pairwise (·.1 != ·.1) := by
  unfold toListModel
  refine Array.foldl_induction
    (motive := fun i (acc : List (α × β)) =>
      -- The acc has the desired property
      acc.Pairwise (·.1 != ·.1)
      -- All not-yet-accumulated buckets are pairwise disjoint with the acc
      ∧ ∀ j, i ≤ j → (_ : j < bkts.val.size) →
        ∀ p ∈ acc, ∀ r ∈ bkts.val[j].toList, p.1 != r.1)
    ?h0 ?hf |>.left
  case h0 => exact ⟨List.Pairwise.nil, fun.⟩
  case hf =>
    intro i acc h
    refine ⟨List.pairwise_append.mpr ⟨h.left, ?bkt, ?accbkt⟩, ?accbkts⟩
    case bkt => apply Pairwise_bne_bucket bkts H
    case accbkt =>
      intro a hA b hB
      exact h.right i.val (Nat.le_refl _) i.isLt a hA b hB
    case accbkts =>
      intro j hGe hLt p hP r hR
      cases List.mem_append.mp hP
      case inl hP => exact h.right j (Nat.le_of_succ_le hGe) hLt p hP r hR
      case inr hP =>
        -- Main proof 2: distinct buckets store bne keys
        refine Bool.bne_iff_not_beq.mpr fun h => ?_
        have hHashEq := LawfulHashable.hash_eq h
        have hGt := Nat.lt_of_succ_le hGe
        have hHashP := H.hash_self i (Nat.lt_trans hGt hLt) _ hP
        have hHashR := H.hash_self j hLt _ hR
        dsimp at hHashP hHashR
        have : i.val = j := by
          rw [hHashEq] at hHashP
          exact .trans hHashP.symm hHashR
        exact Nat.ne_of_lt hGt this

/-- Reformulation of `Pairwise_bne_toListModel` for use with `List.foo_of_unique`. -/
theorem Pairwise_bne_toListModel' (bkts : Buckets α β) (H : bkts.WF) (a : α)
    : bkts.toListModel.Pairwise (fun p q => p.1 == a → q.1 != a) :=
  List.Pairwise.imp beq_nonsense_1 (Pairwise_bne_toListModel bkts H)

@[simp]
theorem toListModel_mk (size : Nat) (h : 0 < size)
    : (Buckets.mk (α := α) (β := β) size h).toListModel = [] := by
  dsimp [Buckets.mk, toListModel]
  clear h
  rw [Array.foldl_eq_foldl_data]
  simp only [mkArray_data, foldl_append_fn, nil_append]
  induction size <;> simp [*]

theorem toListModel_reinsert (bkt : List (α × β)) (tgt : Buckets α β)
    : (bkt.foldl (init := tgt) fun acc x => reinsertAux acc x.fst x.snd).toListModel
    ~ tgt.toListModel ++ bkt :=
  sorry

theorem toListModel_expand (size : Nat) (bkts : Buckets α β)
    : (expand size bkts).buckets.toListModel ~ bkts.toListModel := by
  refine (go _ _ _).trans ?_
  conv => rhs; rw [toListModel]
  simp [toListModel_mk, Array.foldl_eq_foldl_data, List.Perm.refl]

where go (i : Nat) (src : Array (AssocList α β)) (target : Buckets α β)
    : (expand.go i src target).toListModel
      ~ (src.data.drop i).foldl (init := target.toListModel) (fun a b => a ++ b.toList) := by
  unfold expand.go; split
  case inl hI =>
    refine (go (i +1) _ _).trans ?_
    have h₀ : (src.data.set i AssocList.nil).drop (i + 1) = src.data.drop (i + 1) := by
      apply List.drop_ext
      intro j hJ
      apply get?_set_ne _ _ (Nat.ne_of_lt <| Nat.lt_of_succ_le hJ)
    have h₁ : (drop i src.data).bind (·.toList) = src.data[i].toList
        ++ (drop (i + 1) src.data).bind (·.toList) := by
      sorry
    simp [h₀, h₁]
    rw [← List.append_assoc]
    rw [toListModel_reinsert (AssocList.toList src[i])]
    sorry
  case inr hI =>
    sorry

end Buckets

theorem findEntry?_eq (m : Imp α β) (H : m.WF) (a : α)
    : m.findEntry? a = m.buckets.toListModel.find? (·.1 == a) := by
  have hWf := WF_iff.mp H |>.right
  have hPairwiseBkt :
      haveI := mkIdx m.buckets.property a
      Pairwise (fun p q => p.1 == a → q.1 != a) (m.buckets.val[this.1]'this.2).toList :=
    by apply Buckets.Pairwise_bne_bucket' m.buckets hWf
  apply Option.ext
  intro (a', b)
  simp only [Option.mem_def, findEntry?, Imp.findEntry?, AssocList.findEntry?_eq,
    List.find?_eq_some_of_unique (Buckets.Pairwise_bne_toListModel' m.buckets hWf a),
    List.find?_eq_some_of_unique hPairwiseBkt,
    and_congr_left_iff]
  intro hBeq
  have : hash a' = hash a := LawfulHashable.hash_eq hBeq
  simp [Buckets.mem_toListModel_iff_mem_bucket m.buckets hWf, mkIdx, this]

theorem toListModel_insert_perm_cons_eraseP (m : Imp α β) (H : m.WF) (a : α) (b : β)
    : (m.insert a b).buckets.toListModel ~ (a, b) :: m.buckets.toListModel.eraseP (·.1 == a) := by
  dsimp [insert, cond]
  split
  -- By foldl_induction probably:
  -- `insert a` leaves all the non-a buckets alone
  -- this same lemma but holds of the bucket at `a`
  -- and then when things get resized, apply `toListModel_expand`
  sorry
  sorry

theorem toListModel_erase_eq_eraseP (m : Imp α β) (H : m.WF) (a : α)
    : (m.erase a).buckets.toListModel = m.buckets.toListModel.eraseP (·.1 == a) :=
  sorry

end Imp

theorem toList_eq_reverse_toListModel (m : HashMap α β)
    : m.toList = m.val.buckets.toListModel.reverse := by
  simp only [toList, Imp.Buckets.toListModel, fold, Imp.fold, Array.foldl_eq_foldl_data,
    AssocList.foldl_eq, List.foldl_cons_fn]
  suffices ∀ (l₁ : List (AssocList α β)) (l₂ : List (α × β)),
      l₁.foldl (init := l₂.reverse) (fun d b => b.toList.reverse ++ d) =
      (l₁.foldl (init := l₂) fun acc bkt => acc ++ bkt.toList).reverse by
    apply this (l₂ := [])
  intro l₁
  induction l₁ with
  | nil => intro; rfl
  | cons a as ih =>
    intro l₂
    simp only [List.foldl, ← List.reverse_append, ih]

-- TODO: sort below later
#exit

theorem toListModel_eraseP_eq_toListModel_filter (m : HashMap α β)
    : m.val.buckets.toListModel.eraseP (·.1 == a) = m.val.buckets.toListModel.filter (·.1 != a) :=
  by
  apply List.eraseP_eq_filter_of_unique
  apply List.Pairwise.imp ?_ (Pairwise_bne_toListModel _)
  intro (a₁, _) (a₂, _) hA₁Bne hA₁Beq
  rw [Bool.not_eq_true_iff_ne_true, ← Bool.bne_iff_not_beq]
  exact beq_nonsense_1 hA₁Bne hA₁Beq

theorem find?_eq_findEntry?_map (m : HashMap α β) (a : α)
    : m.find? a = (m.findEntry? a).map (·.2) := by
  sorry

theorem findEntry?_eq_some (m : HashMap α β) (a : α) (b : β)
    : m.findEntry? a = some (a, b) ↔ (∃ a', a == a' ∧ (a', b) ∈ m.toListModel) := by
  sorry

theorem toListModel_insert (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toListModel ~ (a, b) :: m.toListModel.filter (·.1 != a) :=
  toListModel_eraseP_eq_toListModel_filter m ▸ toListModel_insert_perm_cons_eraseP m a b

theorem toListModel_erase (m : HashMap α β) (a : α)
    : (m.erase a).toListModel ~ m.toListModel.filter (·.1 != a) :=
  toListModel_eraseP_eq_toListModel_filter m ▸ toListModel_erase_perm_eraseP m a

theorem find?_of_toListModel_not_contains (m : HashMap α β) (a : α)
    : (∀ a' (b : β), a == a' → (a', b) ∉ m.toListModel) ↔ m.find? a = none := by
  apply Iff.intro
  . rw [← Option.not_isSome_iff_eq_none]
    intro h hSome
    let ⟨b, hB⟩ := Option.isSome_iff_exists.mp hSome
    let ⟨a', hA, hMem⟩ := find?_of_toListModel_contains m a b |>.mpr hB
    exact h a' b hA hMem
  . intro h a' b hA hMem
    refine Option.ne_none_iff_exists.mpr ?_ h
    exact ⟨b, find?_of_toListModel_contains m a b |>.mp ⟨a', hA, hMem⟩ |>.symm⟩

theorem find?_insert (m : HashMap α β) (a a' b)
    : a' == a → (m.insert a b).find? a' = some b := by
  intro hEq
  apply (find?_of_toListModel_contains _ _ _).mp
  refine ⟨a, hEq, ?_⟩
  rw [List.Perm.mem_iff (toListModel_insert m a b)]
  apply List.mem_cons_self

theorem find?_insert_of_ne (m : HashMap α β) (a a' : α) (b : β)
    : a != a' → (m.insert a b).find? a' = m.find? a' := by
  intro hNe
  apply Option.ext
  intro b'
  show find? (insert m a b) a' = some b' ↔ find? m a' = some b'
  simp only [← find?_of_toListModel_contains, List.Perm.mem_iff (toListModel_insert m a b),
    List.mem_cons, List.mem_filter, Prod.mk.injEq]
  apply Iff.intro
  . intro ⟨a'', hA', h⟩
    cases h with
    | inl hEq =>
      cases hEq.left
      exfalso
      exact Bool.not_bne_of_beq (PartialEquivBEq.symm hA') hNe
    | inr hMem => exact ⟨a'', hA', hMem.left⟩
  . intro ⟨a'', hA', hMem⟩
    refine ⟨a'', hA', .inr ?_⟩
    refine ⟨hMem, Bool.not_eq_true_iff_ne_true.mpr ?_⟩
    intro hA''
    exact Bool.not_bne_of_beq (PartialEquivBEq.symm (PartialEquivBEq.trans hA' hA'')) hNe

theorem find?_erase (m : HashMap α β) (a a')
    : a == a' → (m.erase a).find? a' = none := by
  intro hEq
  apply (find?_of_toListModel_not_contains _ _).mp
  intro a₂ b hA₂ hMem
  rw [List.Perm.mem_iff (toListModel_erase m a)] at hMem
  have := List.mem_filter.mp hMem |>.right
  exact beq_nonsense_2 hEq hA₂ this

end Std.HashMap
