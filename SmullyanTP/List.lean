import Mathlib.Tactic

namespace List

lemma isPrefix.dilemma {s₁ s₂ t₁ t₂ : List α} (he : s₁ ++ t₁ = s₂ ++ t₂) : s₁ <+: s₂ ∨ s₂ <+: s₁ := by
  induction t₁ <;> induction t₂;
  case nil.nil => simp_all;
  case nil.cons => simp_all;
  case cons.nil =>
    simp only [append_nil] at he; subst he;
    left;
    apply prefix_append;
  case cons.cons h₁ t₁ h₂ t₂ ih₁ ih₂ =>
    sorry;


def IsProperPrefix (l₁ l₂ : List α) := ∃ t ≠ [], l₁ ++ t = l₂
infixl:50 " <+:: " => IsProperPrefix

variable {l₁ l₂ : List α}

lemma isPrefix_of_isProperPrefix : l₁ <+:: l₂ → l₁ <+: l₂ := by
  intro h;
  obtain ⟨t, _, h⟩ := h;
  use t;

lemma iff_not_isProperPrefix : ¬(l₁ <+:: l₂) ↔ (∀ t, t = [] ∨ l₁ ++ t ≠ l₂) := by
  simp only [IsProperPrefix, not_exists, not_and_or, ne_eq, not_not];

lemma IsProperPrefix.trichnomy {s₁ s₂ t₁ t₂ : List α} (he : s₁ ++ t₁ = s₂ ++ t₂) : s₁ = s₂ ∨ s₁ <+:: s₂ ∨ s₂ <+:: s₁ := by
  rcases isPrefix.dilemma he with ⟨t, rfl⟩ | ⟨t, rfl⟩;
  . sorry;
  . sorry;

end List
