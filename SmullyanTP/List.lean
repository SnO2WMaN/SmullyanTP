import Mathlib.Order.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Use

/-
  Proof by @iehality (Palalansoukî)
  https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.E2.9C.94.20some.20lemmata.20about.20List.2EisPrefix.20I.20cannot.20proved/near/478988282
-/

namespace List

lemma IsPrefix.dilemma {s₁ s₂ t₁ t₂ : List α} (he : s₁ ++ t₁ = s₂ ++ t₂) : s₁ <+: s₂ ∨ s₂ <+: s₁ :=
  List.prefix_or_prefix_of_prefix (l₃ := s₁ ++ t₁) (prefix_append s₁ t₁) (by rw [he]; exact prefix_append s₂ t₂)


def IsProperPrefix (l₁ l₂ : List α) := ∃ t ≠ [], l₁ ++ t = l₂
infixl:50 " <+:: " => IsProperPrefix

variable {l₁ l₂ : List α}

lemma isPrefix_of_isProperPrefix : l₁ <+:: l₂ → l₁ <+: l₂ := by
  intro h;
  obtain ⟨t, _, h⟩ := h;
  use t;

lemma iff_not_isProperPrefix : ¬(l₁ <+:: l₂) ↔ (∀ t, t = [] ∨ l₁ ++ t ≠ l₂) := by
  simp only [IsProperPrefix, not_exists, not_and_or, ne_eq, not_not];

lemma isProperPrefix_iff : l₁ <+:: l₂ ↔ (l₁ <+: l₂ ∧ l₁.length < l₂.length) := by
  constructor;
  . intro h;
    constructor;
    . exact isPrefix_of_isProperPrefix h;
    . obtain ⟨t, ht, rfl⟩ := h;
      simp [List.length_append, List.length_pos_iff_ne_nil.mpr ht];
  . rintro ⟨⟨t, ht, rfl⟩, h⟩;
    use t;
    constructor;
    . simp at h;
      exact List.length_pos_iff_ne_nil.mp h;
    . tauto;

lemma IsProperPrefix.trichnomy {s₁ s₂ t₁ t₂ : List α} (he : s₁ ++ t₁ = s₂ ++ t₂) : s₁ = s₂ ∨ s₁ <+:: s₂ ∨ s₂ <+:: s₁ := by
  wlog h : s₁ <+: s₂
  · rcases IsPrefix.dilemma he with (h | h)
    · contradiction
    · simpa [eq_comm, or_comm] using this he.symm h
  rcases eq_or_lt_of_le (IsPrefix.length_le h) with (e | e)
  · left; exact append_inj_left he e
  · right; left
    exact isProperPrefix_iff.mpr ⟨h, e⟩

end List
