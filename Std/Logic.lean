/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Std.Tactic.Basic
import Std.Tactic.Lint.Misc

instance {f : α → β} [DecidablePred p] : DecidablePred (p ∘ f) :=
  inferInstanceAs <| DecidablePred fun x => p (f x)

/-! ## not -/

theorem Not.intro {a : Prop} (h : a → False) : ¬a := h

/-- Ex falso for negation. From `¬a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def Not.elim {α : Sort _} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

theorem Not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

theorem not_not_not : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a := mt Not.elim

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b := mt fun h _ => h

@[simp] theorem imp_not_self : (a → ¬a) ↔ ¬a := ⟨fun h ha => h ha ha, fun h _ => h⟩

/-! ## iff -/

theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) := iff_iff_implies_and_implies ..

theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) := iff_def.trans And.comm

/-- Non-dependent eliminator for `Iff`. -/
def Iff.elim (f : (a → b) → (b → a) → α) (h : a ↔ b) : α := f h.1 h.2

theorem Eq.to_iff : a = b → (a ↔ b) | rfl => Iff.rfl

theorem iff_of_eq : a = b → (a ↔ b) := Eq.to_iff

theorem neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Eq.to_iff

theorem iff_iff_eq : (a ↔ b) ↔ a = b := ⟨propext, iff_of_eq⟩

@[simp] theorem eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) := iff_iff_eq.symm

theorem of_iff_true (h : a ↔ True) : a := h.2 ⟨⟩

theorem not_of_iff_false : (a ↔ False) → ¬a := Iff.mp

theorem iff_of_true (ha : a) (hb : b) : a ↔ b := ⟨fun _ => hb, fun _ => ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b := ⟨ha.elim, hb.elim⟩

theorem iff_true_left (ha : a) : (a ↔ b) ↔ b := ⟨fun h => h.1 ha, iff_of_true ha⟩

theorem iff_true_right (ha : a) : (b ↔ a) ↔ b := Iff.comm.trans (iff_true_left ha)

theorem iff_false_left (ha : ¬a) : (a ↔ b) ↔ ¬b := ⟨fun h => mt h.2 ha, iff_of_false ha⟩

theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b := Iff.comm.trans (iff_false_left ha)

theorem iff_true_intro (h : a) : a ↔ True := iff_of_true h ⟨⟩

theorem iff_false_intro (h : ¬a) : a ↔ False := iff_of_false h id

theorem not_iff_false_intro (h : a) : ¬a ↔ False := iff_false_intro (not_not_intro h)

theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
  ⟨fun h => h₁.symm.trans <| h.trans h₂, fun h => h₁.trans <| h.trans h₂.symm⟩

@[simp] theorem not_true : (¬True) ↔ False := iff_false_intro (not_not_intro ⟨⟩)

@[simp] theorem not_false_iff : (¬False) ↔ True := iff_true_intro not_false

theorem ne_self_iff_false (a : α) : a ≠ a ↔ False := not_iff_false_intro rfl

theorem eq_self_iff_true (a : α) : a = a ↔ True := iff_true_intro rfl

theorem heq_self_iff_true (a : α) : HEq a a ↔ True := iff_true_intro HEq.rfl

theorem iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)

@[simp] theorem not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm

theorem true_iff_false : (True ↔ False) ↔ False := iff_false_intro (fun h => h.1 ⟨⟩)

theorem false_iff_true : (False ↔ True) ↔ False := iff_false_intro (fun h => h.2 ⟨⟩)

theorem false_of_true_iff_false : (True ↔ False) → False := fun h => h.1 ⟨⟩

theorem false_of_true_eq_false : (True = False) → False := fun h => h ▸ trivial

theorem true_eq_false_of_false : False → (True = False) := False.elim

theorem eq_comm {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩

/-! ## implies -/

@[nolint unusedArguments]
theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_imp_imp {a b c d : Prop} (h₀ : c → a) (h₁ : b → d) : (a → b) → (c → d) := (h₁ ∘ · ∘ h₀)

theorem imp_iff_right {a : Prop} (ha : a) : (a → b) ↔ b := ⟨fun f => f ha, imp_intro⟩

-- This is not marked `@[simp]` because we have `implies_true : (α → True) = True` in core.
theorem imp_true_iff (α : Sort u) : (α → True) ↔ True := iff_true_intro fun _ => trivial

theorem false_imp_iff (a : Prop) : (False → a) ↔ True := iff_true_intro False.elim

theorem true_imp_iff (α : Prop) : (True → α) ↔ α := ⟨fun h => h trivial, fun h _ => h⟩

@[simp] theorem imp_self : (a → a) ↔ True := iff_true_intro id

theorem imp_false : (a → False) ↔ ¬a := Iff.rfl

theorem imp.swap : (a → b → c) ↔ (b → a → c) := ⟨flip, flip⟩

theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) := imp.swap

theorem imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) :=
  ⟨fun hac ha => hac (h.2 ha), fun hbc ha => hbc (h.1 ha)⟩

theorem imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
  ⟨fun hab ha => (h ha).1 (hab ha), fun hcd ha => (h ha).2 (hcd ha)⟩

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
  (imp_congr_left h₁).trans (imp_congr_right h₂)

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := imp_congr_ctx h₁ fun _ => h₂

theorem imp_iff_not (hb : ¬b) : a → b ↔ ¬a := imp_congr_right fun _ => iff_false_intro hb

/-! ## and -/

/-- Non-dependent eliminator for `And`. -/
abbrev And.elim (f : a → b → α) (h : a ∧ b) : α := f h.1 h.2

theorem And.symm : a ∧ b → b ∧ a | ⟨ha, hb⟩ => ⟨hb, ha⟩

theorem And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d := ⟨f h.1, g h.2⟩

theorem And.imp_left (h : a → b) : a ∧ c → b ∧ c := .imp h id

theorem And.imp_right (h : a → b) : c ∧ a → c ∧ b := .imp id h

theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  ⟨And.imp h₁.1 h₂.1, And.imp h₁.2 h₂.2⟩

theorem and_comm : a ∧ b ↔ b ∧ a := And.comm

theorem and_congr_right (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c :=
⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
  and_comm.trans <| (and_congr_right h).trans and_comm

theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := and_congr h .rfl

theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := and_congr .rfl h

theorem and_congr_right_eq (h : a → b = c) : (a ∧ b) = (a ∧ c) :=
  propext <| and_congr_right fun hc => h hc ▸ .rfl

theorem and_congr_left_eq (h : c → a = b) : (a ∧ c) = (b ∧ c) :=
  propext <| and_congr_left fun hc => h hc ▸ .rfl

theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

theorem and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) := by
  rw [← and_assoc, ← and_assoc, @and_comm a b]

theorem and_right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b := by
  simp only [and_left_comm, and_comm]; rfl

theorem and_rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  simp only [and_left_comm, and_comm]; rfl

theorem and_and_and_comm : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]

theorem and_and_left : a ∧ b ∧ c ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]

theorem and_and_right : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b ∧ c := by
  rw [and_and_and_comm, and_self]

theorem and_iff_left_of_imp (h : a → b) : (a ∧ b) ↔ a :=
  ⟨And.left, fun ha => ⟨ha, h ha⟩⟩

theorem and_iff_right_of_imp (h : b → a) : (a ∧ b) ↔ b :=
  ⟨And.right, fun hb => ⟨h hb, hb⟩⟩

theorem and_iff_left (hb : b) : a ∧ b ↔ a := and_iff_left_of_imp fun _ => hb

theorem and_iff_right (ha : a) : a ∧ b ↔ b := and_iff_right_of_imp fun _ => ha

@[simp] theorem and_iff_left_iff_imp : ((a ∧ b) ↔ a) ↔ (a → b) :=
  ⟨fun h ha => (h.2 ha).2, and_iff_left_of_imp⟩

@[simp] theorem and_iff_right_iff_imp : ((a ∧ b) ↔ b) ↔ (b → a) :=
  ⟨fun h ha => (h.2 ha).1, and_iff_right_of_imp⟩

@[simp] theorem iff_self_and : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]

@[simp] theorem iff_and_self : (p ↔ q ∧ p) ↔ (p → q) := by rw [and_comm, iff_self_and]

@[simp] theorem and_congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
  ⟨fun h ha => by simp [ha] at h; exact h, and_congr_right⟩

@[simp] theorem and_congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) := by
  simp only [and_comm, ← and_congr_right_iff]; rfl

@[simp] theorem and_self_left : a ∧ a ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1, h.2⟩⟩

@[simp] theorem and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2⟩, h.2⟩⟩

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) := mt And.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) := mt And.right

@[simp] theorem and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha

@[simp] theorem not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

theorem and_not_self_iff (a : Prop) : a ∧ ¬a ↔ False := iff_false_intro and_not_self

theorem not_and_self_iff (a : Prop) : ¬a ∧ a ↔ False := iff_false_intro not_and_self

/-! ## or -/

theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun h => h (.inr (h ∘ .inl))

theorem Or.symm : a ∨ b → b ∨ a := .rec .inr .inl

theorem Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

theorem Or.imp_left (f : a → b) : a ∨ c → b ∨ c := .imp f id

theorem Or.imp_right (f : b → c) : a ∨ b → a ∨ c := .imp id f

theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) := ⟨.imp h₁.1 h₂.1, .imp h₁.2 h₂.2⟩

theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := or_congr h .rfl

theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := or_congr .rfl h

theorem Or.comm : a ∨ b ↔ b ∨ a := ⟨Or.symm, Or.symm⟩

theorem or_comm : a ∨ b ↔ b ∨ a := Or.comm

theorem or_assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  ⟨.rec (.imp_right .inl) (.inr ∘ .inr), .rec (.inl ∘ .inl) (.imp_left .inr)⟩

theorem Or.resolve_left {a b : Prop} (h: a ∨ b) (na : ¬a) : b := h.elim (absurd · na) id

theorem Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id

theorem Or.resolve_right {a b : Prop} (h: a ∨ b) (nb : ¬b) : a := h.elim id (absurd · nb)

theorem Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

theorem or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) := by rw [← or_assoc, ← or_assoc, @or_comm a b]

theorem or_right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc, or_assoc, @or_comm b]

theorem or_or_or_comm : (a ∨ b) ∨ c ∨ d ↔ (a ∨ c) ∨ b ∨ d := by
  rw [← or_assoc, @or_right_comm a, or_assoc]

theorem or_or_distrib_left : a ∨ b ∨ c ↔ (a ∨ b) ∨ a ∨ c := by rw [or_or_or_comm, or_self]

theorem or_or_distrib_right : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b ∨ c := by rw [or_or_or_comm, or_self]

theorem or_rotate : a ∨ b ∨ c ↔ b ∨ c ∨ a := by simp only [or_left_comm, Or.comm]; rfl

theorem or_iff_right_of_imp (ha : a → b) : (a ∨ b) ↔ b := ⟨Or.rec ha id, .inr⟩

theorem or_iff_left_of_imp (hb : b → a) : (a ∨ b) ↔ a := ⟨Or.rec id hb, .inl⟩

theorem not_or_intro {a b : Prop} (ha : ¬a) (hb : ¬b) : ¬(a ∨ b) := (·.elim ha hb)

@[simp] theorem or_iff_left_iff_imp : (a ∨ b ↔ a) ↔ (b → a) :=
  ⟨fun h hb => h.1 (Or.inr hb), or_iff_left_of_imp⟩

@[simp] theorem or_iff_right_iff_imp : (a ∨ b ↔ b) ↔ (a → b) := by
  rw [or_comm, or_iff_left_iff_imp]

theorem or_iff_left (hb : ¬b) : a ∨ b ↔ a := or_iff_left_iff_imp.2 hb.elim

theorem or_iff_right (ha : ¬a) : a ∨ b ↔ b := or_iff_right_iff_imp.2 ha.elim

/-! ## distributivity -/

theorem not_imp_of_and_not : a ∧ ¬b → ¬(a → b)
  | ⟨ha, hb⟩, h => hb <| h ha

theorem imp_and {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
  ⟨fun h => ⟨fun ha => (h ha).1, fun ha => (h ha).2⟩, fun h ha => ⟨h.1 ha, h.2 ha⟩⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
  ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩

@[simp] theorem not_and : ¬(a ∧ b) ↔ (a → ¬b) := and_imp

theorem not_and' : ¬(a ∧ b) ↔ b → ¬a := not_and.trans imp_not_comm

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  ⟨fun ⟨ha, hbc⟩ => hbc.imp (.intro ha) (.intro ha), Or.rec (.imp_right .inl) (.imp_right .inr)⟩

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  simp [and_comm, and_or_left]

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  ⟨Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr),
   And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro)⟩

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  simp [or_comm, or_and_left]

theorem or_imp : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  ⟨fun h => ⟨h ∘ .inl, h ∘ .inr⟩, fun ⟨ha, hb⟩ => Or.rec ha hb⟩

theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imp

theorem not_and_of_not_or_not (h : ¬a ∨ ¬b) : ¬(a ∧ b) := h.elim (mt (·.1)) (mt (·.2))

@[simp] theorem or_self_left : a ∨ a ∨ b ↔ a ∨ b := ⟨.rec .inl id, .rec .inl (.inr ∘ .inr)⟩

@[simp] theorem or_self_right : (a ∨ b) ∨ b ↔ a ∨ b := ⟨.rec id .inr, .rec (.inl ∘ .inl) .inr⟩

/-! ## exists and forall -/

section quantifiers
variable {p q : α → Prop} {b : Prop}

theorem forall_imp (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a :=
fun h' a => h a (h' a)

theorem Exists.imp (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a
  | ⟨a, hp⟩ => ⟨a, h a hp⟩

theorem Exists.imp' {β} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a)) :
    (∃ a, p a) → ∃ b, q b
  | ⟨_, hp⟩ => ⟨_, hpq _ hp⟩

@[simp] theorem exists_imp : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
  ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

section forall_congr

-- Port note: this is `forall_congr` from Lean 3. In Lean 4, there is already something
-- with that name and a slightly different type.
theorem forall_congr' (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
  ⟨fun H a => (h a).1 (H a), fun H a => (h a).2 (H a)⟩

theorem exists_congr (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
  ⟨Exists.imp fun x => (h x).1, Exists.imp fun x => (h x).2⟩

variable {β : α → Sort _}
theorem forall₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
    (∀ a b, p a b) ↔ ∀ a b, q a b :=
  forall_congr' fun a => forall_congr' <| h a

theorem exists₂_congr {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
    (∃ a b, p a b) ↔ ∃ a b, q a b :=
  exists_congr fun a => exists_congr <| h a

variable {γ : ∀ a, β a → Sort _}
theorem forall₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∀ a b c, p a b c) ↔ ∀ a b c, q a b c :=
  forall_congr' fun a => forall₂_congr <| h a

theorem exists₃_congr {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
    (∃ a b c, p a b c) ↔ ∃ a b c, q a b c :=
  exists_congr fun a => exists₂_congr <| h a

variable {δ : ∀ a b, γ a b → Sort _}
theorem forall₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∀ a b c d, p a b c d) ↔ ∀ a b c d, q a b c d :=
  forall_congr' fun a => forall₃_congr <| h a

theorem exists₄_congr {p q : ∀ a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
    (∃ a b c d, p a b c d) ↔ ∃ a b c d, q a b c d :=
  exists_congr fun a => exists₃_congr <| h a

variable {ε : ∀ a b c, δ a b c → Sort _}
theorem forall₅_congr {p q : ∀ a b c d, ε a b c d → Prop}
    (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∀ a b c d e, p a b c d e) ↔ ∀ a b c d e, q a b c d e :=
  forall_congr' fun a => forall₄_congr <| h a

theorem exists₅_congr {p q : ∀ a b c d, ε a b c d → Prop}
    (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
    (∃ a b c d e, p a b c d e) ↔ ∃ a b c d e, q a b c d e :=
  exists_congr fun a => exists₄_congr <| h a

end forall_congr

@[simp] theorem not_exists : (¬∃ x, p x) ↔ ∀ x, ¬p x := exists_imp

theorem forall_not_of_not_exists (hne : ¬∃ x, p x) (x) : ¬p x | hp => hne ⟨x, hp⟩

theorem forall_and : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

theorem exists_or : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ ∃ x, q x :=
  ⟨fun | ⟨x, .inl h⟩ => .inl ⟨x, h⟩ | ⟨x, .inr h⟩ => .inr ⟨x, h⟩,
   fun | .inl ⟨x, h⟩ => ⟨x, .inl h⟩ | .inr ⟨x, h⟩ => ⟨x, .inr h⟩⟩

@[simp] theorem exists_false : ¬(∃ _a : α, False) := fun ⟨_, h⟩ => h

@[simp] theorem forall_const (α : Sort _) [i : Nonempty α] : (α → b) ↔ b :=
  ⟨i.elim, fun hb _ => hb⟩

theorem Exists.nonempty : (∃ x, p x) → Nonempty α | ⟨x, _⟩ => ⟨x⟩

/-- Extract an element from a existential statement, using `Classical.choose`. -/
-- This enables projection notation.
@[reducible] noncomputable def Exists.choose (P : ∃ a, p a) : α := Classical.choose P

/-- Show that an element extracted from `P : ∃ a, p a` using `P.choose` satisfies `p`. -/
theorem Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p P.choose := Classical.choose_spec P

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬p x) → ¬∀ x, p x
  | ⟨x, hn⟩, h => hn (h x)

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀ a, a = a' → p a) ↔ p a' :=
  ⟨fun h => h a' rfl, fun h _ e => e.symm ▸ h⟩

@[simp] theorem forall_eq' {a' : α} : (∀ a, a' = a → p a) ↔ p a' := by simp [@eq_comm _ a']

@[simp] theorem exists_eq : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left : (∃ a, a = a' ∧ p a) ↔ p a' :=
  ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right : (∃ a, p a ∧ a = a') ↔ p a' :=
  (exists_congr <| by exact fun a => And.comm).trans exists_eq_left

@[simp] theorem exists_and_left : (∃ x, b ∧ p x) ↔ b ∧ (∃ x, p x) :=
  ⟨fun ⟨x, h, hp⟩ => ⟨h, x, hp⟩, fun ⟨h, x, hp⟩ => ⟨x, h, hp⟩⟩

@[simp] theorem exists_and_right : (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b := by simp [And.comm]

@[simp] theorem exists_eq_left' : (∃ a, a' = a ∧ p a) ↔ p a' := by simp [@eq_comm _ a']

-- this theorem is needed to simplify the output of `list.mem_cons_iff`
@[simp] theorem forall_eq_or_imp : (∀ a, a = a' ∨ q a → p a) ↔ p a' ∧ ∀ a, q a → p a := by
  simp only [or_imp, forall_and, forall_eq]; rfl

@[simp] theorem exists_eq_or_imp : (∃ a, (a = a' ∨ q a) ∧ p a) ↔ p a' ∨ ∃ a, q a ∧ p a := by
  simp only [or_and_right, exists_or, exists_eq_left]; rfl

@[simp] theorem exists_eq_right_right : (∃ (a : α), p a ∧ b ∧ a = a') ↔ p a' ∧ b := by
  simp [← and_assoc]

@[simp] theorem exists_eq_right_right' : (∃ (a : α), p a ∧ b ∧ a' = a) ↔ p a' ∧ b := by
  (conv in _=_ => rw [eq_comm]); simp

@[simp] theorem exists_prop : (∃ _h : a, b) ↔ a ∧ b :=
  ⟨fun ⟨hp, hq⟩ => ⟨hp, hq⟩, fun ⟨hp, hq⟩ => ⟨hp, hq⟩⟩

@[simp] theorem exists_apply_eq_apply (f : α → β) (a' : α) : ∃ a, f a = f a' := ⟨a', rfl⟩

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
  @forall_const (q h) p ⟨h⟩

end quantifiers

/-! ## decidable -/

theorem Decidable.not_not [Decidable p] : ¬¬p ↔ p := ⟨of_not_not, not_not_intro⟩

/-- Construct a non-Prop by cases on an `Or`, when the left conjunct is decidable. -/
protected def Or.by_cases [Decidable p] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else h₂ (h.resolve_left hp)

/-- Construct a non-Prop by cases on an `Or`, when the right conjunct is decidable. -/
protected def Or.by_cases' [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hq : q then h₂ hq else h₁ (h.resolve_right hq)

instance exists_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 => ⟨h, h2⟩, fun ⟨_, h2⟩ => h2⟩
else isFalse fun ⟨h', _⟩ => h h'

instance forall_prop_decidable {p} (P : p → Prop)
  [Decidable p] [∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
if h : p then
  decidable_of_decidable_of_iff ⟨fun h2 _ => h2, fun al => al h⟩
else isTrue fun h2 => absurd h2 h

theorem decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by simp

@[simp] theorem decide_eq_false_iff_not (p : Prop) [Decidable p] : (decide p = false) ↔ ¬p :=
  ⟨of_decide_eq_false, decide_eq_false⟩

theorem Decidable.of_not_imp [Decidable a] (h : ¬(a → b)) : a :=
  byContradiction (not_not_of_not_imp h)

theorem Decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
  byContradiction <| hb ∘ h

theorem Decidable.not_imp_comm [Decidable a] [Decidable b] : (¬a → b) ↔ (¬b → a) :=
  ⟨not_imp_symm, not_imp_symm⟩

theorem Decidable.not_imp_self [Decidable a] : (¬a → a) ↔ a := by
  have := @imp_not_self (¬a); rwa [not_not] at this

theorem Decidable.or_iff_not_imp_left [Decidable a] : a ∨ b ↔ (¬a → b) :=
  ⟨Or.resolve_left, fun h => dite _ .inl (.inr ∘ h)⟩

theorem Decidable.or_iff_not_imp_right [Decidable b] : a ∨ b ↔ (¬b → a) :=
or_comm.trans or_iff_not_imp_left

theorem Decidable.not_imp_not [Decidable a] : (¬a → ¬b) ↔ (b → a) :=
⟨fun h hb => byContradiction (h · hb), mt⟩

theorem Decidable.not_or_of_imp [Decidable a] (h : a → b) : ¬a ∨ b :=
  if ha : a then .inr (h ha) else .inl ha

theorem Decidable.imp_iff_not_or [Decidable a] : (a → b) ↔ (¬a ∨ b) :=
  ⟨not_or_of_imp, Or.neg_resolve_left⟩

theorem Decidable.imp_iff_or_not [Decidable b] : b → a ↔ a ∨ ¬b :=
  Decidable.imp_iff_not_or.trans or_comm

theorem Decidable.imp_or [Decidable a] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := by
  by_cases a <;> simp_all

theorem Decidable.imp_or' [Decidable b] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
  if h : b then by simp [h] else by
    rw [eq_false h, false_or]; exact (or_iff_right_of_imp fun hx x => (hx x).elim).symm

theorem Decidable.not_imp [Decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
  ⟨fun h => ⟨of_not_imp h, not_of_not_imp h⟩, not_imp_of_and_not⟩

theorem Decidable.peirce (a b : Prop) [Decidable a] : ((a → b) → a) → a :=
  if ha : a then fun _ => ha else fun h => h ha.elim

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

theorem Decidable.not_iff_not [Decidable a] [Decidable b] : (¬a ↔ ¬b) ↔ (a ↔ b) := by
  rw [@iff_def (¬a), @iff_def' a]; exact and_congr not_imp_not not_imp_not

theorem Decidable.not_iff_comm [Decidable a] [Decidable b] : (¬a ↔ b) ↔ (¬b ↔ a) := by
  rw [@iff_def (¬a), @iff_def (¬b)]; exact and_congr not_imp_comm imp_not_comm

theorem Decidable.not_iff [Decidable b] : ¬(a ↔ b) ↔ (¬a ↔ b) := by
  by_cases h : b <;> simp [h, iff_true, iff_false]

theorem Decidable.iff_not_comm [Decidable a] [Decidable b] : (a ↔ ¬b) ↔ (b ↔ ¬a) := by
  rw [@iff_def a, @iff_def b]; exact and_congr imp_not_comm not_imp_comm

theorem Decidable.iff_iff_and_or_not_and_not [Decidable b] : (a ↔ b) ↔ (a ∧ b) ∨ (¬a ∧ ¬b) :=
  ⟨fun e => if h : b then .inl ⟨e.2 h, h⟩ else .inr ⟨mt e.1 h, h⟩,
   Or.rec (And.rec iff_of_true) (And.rec iff_of_false)⟩

theorem Decidable.iff_iff_not_or_and_or_not [Decidable a] [Decidable b] :
    (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) := by
  rw [iff_iff_implies_and_implies a b]; simp only [imp_iff_not_or, Or.comm]; rfl

theorem Decidable.not_and_not_right [Decidable b] : ¬(a ∧ ¬b) ↔ (a → b) :=
  ⟨fun h ha => not_imp_symm (And.intro ha) h, fun h ⟨ha, hb⟩ => hb <| h ha⟩

theorem Decidable.not_and [Decidable a] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if ha : a then .inr (h ⟨ha, ·⟩) else .inl ha, not_and_of_not_or_not⟩

theorem Decidable.not_and' [Decidable b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨fun h => if hb : b then .inl (h ⟨·, hb⟩) else .inr hb, not_and_of_not_or_not⟩

theorem Decidable.or_iff_not_and_not [Decidable a] [Decidable b] : a ∨ b ↔ ¬(¬a ∧ ¬b) := by
  rw [← not_or, not_not]

theorem Decidable.and_iff_not_or_not [Decidable a] [Decidable b] : a ∧ b ↔ ¬(¬a ∨ ¬b) := by
  rw [← not_and, not_not]

theorem Decidable.imp_iff_right_iff [Decidable a] : (a → b ↔ b) ↔ a ∨ b :=
  ⟨fun H => (Decidable.em a).imp_right fun ha' => H.1 fun ha => (ha' ha).elim,
   fun H => H.elim imp_iff_right fun hb => iff_of_true (fun _ => hb) hb⟩

theorem Decidable.and_or_imp [Decidable a] : a ∧ b ∨ (a → c) ↔ a → b ∨ c :=
  if ha : a then by simp only [ha, true_and, true_imp_iff]; rfl
  else by simp only [ha, false_or, false_and, false_imp_iff]

theorem Decidable.or_congr_left' [Decidable c] (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c := by
  rw [or_iff_not_imp_right, or_iff_not_imp_right]; exact imp_congr_right h

theorem Decidable.or_congr_right' [Decidable a] (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c := by
  rw [or_iff_not_imp_left, or_iff_not_imp_left]; exact imp_congr_right h

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `dec_trivial` will not work. -/
@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff h.symm

instance Decidable.predToBool (p : α → Prop) [DecidablePred p] :
    CoeDep (α → Prop) p (α → Bool) := ⟨fun b => decide <| p b⟩

theorem Bool.ff_ne_tt : false ≠ true := fun.

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool : ∀ (b : Bool), (b ↔ a) → Decidable a
  | true, h => isTrue (h.1 rfl)
  | false, h => isFalse (mt h.2 Bool.ff_ne_tt)

/-! ## classical logic -/

namespace Classical

/-- The Double Negation Theorem: `¬¬P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[scoped simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

end Classical

/-! ## equality -/

theorem heq_iff_eq : HEq a b ↔ a = b := ⟨eq_of_heq, heq_of_eq⟩

theorem proof_irrel_heq {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  cases propext (iff_of_true hp hq); rfl

@[simp] theorem eq_rec_constant {α : Sort _} {a a' : α} {β : Sort _} (y : β) (h : a = a') :
    (@Eq.rec α a (fun α _ => β) y a' h) = y := by cases h; rfl

theorem congrArg₂ (f : α → β → γ) {x x' : α} {y y' : β}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by subst hx hy; rfl

/-! ## membership -/

section Mem
variable [Membership α β] {s t : β} {a b : α}

theorem ne_of_mem_of_not_mem (h : a ∈ s) : b ∉ s → a ≠ b := mt fun e => e ▸ h

theorem ne_of_mem_of_not_mem' (h : a ∈ s) : a ∉ t → s ≠ t := mt fun e => e ▸ h

end Mem

/-! ## if-then-else -/

@[simp] theorem if_true {h : Decidable True} (t e : α) : ite True t e = t := if_pos trivial

@[simp] theorem if_false {h : Decidable False} (t e : α) : ite False t e = e := if_neg id

theorem ite_id [Decidable c] {α} (t : α) : (if c then t else t) = t := by split <;> rfl

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
theorem apply_dite (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α) :
    f (dite P x y) = dite P (fun h => f (x h)) (fun h => f (y h)) := by
  by_cases h : P <;> simp [h]

/-- A function applied to a `ite` is a `ite` of that function applied to each of the branches. -/
theorem apply_ite (f : α → β) (P : Prop) [Decidable P] (x y : α) :
    f (ite P x y) = ite P (f x) (f y) :=
  apply_dite f P (fun _ => x) (fun _ => y)

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] theorem dite_not (P : Prop) [Decidable P]  (x : ¬P → α) (y : ¬¬P → α) :
    dite (¬P) x y = dite P (fun h => y (not_not_intro h)) x := by
  by_cases h : P <;> simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] theorem ite_not (P : Prop) [Decidable P] (x y : α) : ite (¬P) x y = ite P y x :=
  dite_not P (fun _ => x) (fun _ => y)

/-! ## Booleans -/

theorem false_ne_true : False ≠ True := fun h => h.symm ▸ trivial

theorem Bool.eq_false_or_eq_true : (b : Bool) → b = true ∨ b = false
  | true => .inl rfl
  | false => .inr rfl

theorem Bool.eq_false_iff {b : Bool} : b = false ↔ b ≠ true :=
  ⟨ne_true_of_eq_false, eq_false_of_ne_true⟩

theorem Bool.not_eq_true_iff_ne_true {b : Bool} : (!b) = true ↔ ¬(b = true) := by
  cases b <;> decide

theorem Bool.not_bne_of_beq [BEq α] {a a' : α} : a == a' → a != a' → False :=
  fun hEq hNe => Bool.not_eq_true_iff_ne_true.mp hNe hEq

/-! ## miscellaneous -/

/-- Ex falso, the nondependent eliminator for the `Empty` type. -/
def Empty.elim : Empty → C := fun.

instance : Subsingleton Empty := ⟨fun a => a.elim⟩

instance : DecidableEq Empty := fun a => a.elim

/-- Ex falso, the nondependent eliminator for the `PEmpty` type. -/
def PEmpty.elim : PEmpty → C := fun.

instance : Subsingleton PEmpty := ⟨fun a => a.elim⟩

instance : DecidableEq PEmpty := fun a => a.elim

@[simp] theorem not_nonempty_empty : ¬Nonempty Empty := fun ⟨h⟩ => h.elim

@[simp] theorem not_nonempty_pempty : ¬Nonempty PEmpty := fun ⟨h⟩ => h.elim

instance [Subsingleton α] [Subsingleton β] : Subsingleton (α × β) :=
  ⟨fun {..} {..} => by congr <;> apply Subsingleton.elim⟩

instance : Inhabited (Sort _) := ⟨PUnit⟩

instance : Inhabited default := ⟨PUnit.unit⟩

instance {α β} [Inhabited α] : Inhabited (PSum α β) := ⟨PSum.inl default⟩

instance {α β} [Inhabited β] : Inhabited (PSum α β) := ⟨PSum.inr default⟩

-- TODO(Mario): profile first, this is a dangerous instance
-- instance (priority := 10) {α} [Subsingleton α] : DecidableEq α
--   | a, b => isTrue (Subsingleton.elim a b)

-- @[simp] -- TODO(Mario): profile
theorem eq_iff_true_of_subsingleton [Subsingleton α] (x y : α) : x = y ↔ True :=
  iff_true_intro (Subsingleton.elim ..)

/-- If all points are equal to a given point `x`, then `α` is a subsingleton. -/
theorem subsingleton_of_forall_eq (x : α) (h : ∀ y, y = x) : Subsingleton α :=
  ⟨fun a b => h a ▸ h b ▸ rfl⟩

theorem subsingleton_iff_forall_eq (x : α) : Subsingleton α ↔ ∀ y, y = x :=
  ⟨fun _ y => Subsingleton.elim y x, subsingleton_of_forall_eq x⟩

example [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by congr; exact Subsingleton.elim x y⟩

theorem ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨Ne.symm, Ne.symm⟩
