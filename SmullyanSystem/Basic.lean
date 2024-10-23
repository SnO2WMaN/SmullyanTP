import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique
import Aesop


structure SmullyanModel where
  α : Type*
  isPredicate : List α → Prop
  isPredicate_spec : ∀ p : { x // isPredicate x }, ∀ x ≠ [], ¬isPredicate (p.val ++ x)
  valuation : { x // isPredicate x } → Set (List α)

namespace SmullyanModel

variable {M : SmullyanModel}


abbrev Word (M : SmullyanModel) := List M.α

abbrev words (M : SmullyanModel) : Set M.Word := Set.univ

abbrev epsilon (M : SmullyanModel) : M.Word := []


abbrev Predicate (M : SmullyanModel) := { P // M.isPredicate P }

abbrev predicates (M : SmullyanModel) : Set M.Predicate := Set.univ

instance : Coe (Set M.Predicate) (Set M.Word) := ⟨fun s => s.image (·.val)⟩

@[simp] lemma isPredicate_predicate {P : M.Predicate} : M.isPredicate P.val := P.property

def Predicate.valuated (P : M.Predicate) : Set M.Word := M.valuation P

def Predicate.names (P : M.Predicate) (V : Set M.Word) : Prop := P.valuated = V


structure Sentence (M : SmullyanModel) where
  P : M.Predicate
  W : M.Word

lemma Sentence.ext : ∀ {S₁ S₂ : M.Sentence}, S₁.P = S₂.P → S₁.W = S₂.W → S₁ = S₂ := by
  intros S₁ S₂ hP hW;
  cases S₁; cases S₂;
  subst hP hW;
  tauto;

abbrev sentences (M : SmullyanModel) : Set M.Sentence := Set.univ

def Sentence.toWord : M.Sentence → M.Word := fun ⟨P, W⟩ => P ++ W

lemma Sentence.exists_unique (S : M.Sentence) : ∃! P, ∃! W, ⟨P, W⟩ = S := by sorry;

@[simp]
lemma Sentence.toWord_injective : Function.Injective (Sentence.toWord (M := M)) := by
  simp [Function.Injective, Sentence.toWord];
  intro S₁ S₂ h;
  obtain ⟨P₁, ⟨W₁, rfl, hW₁⟩, hP₁⟩ := Sentence.exists_unique S₁;
  obtain ⟨P₂, ⟨W₂, rfl, hW₂⟩, hP₂⟩ := Sentence.exists_unique S₂;
  sorry;


instance : Coe (M.Sentence) (M.Word) := ⟨Sentence.toWord⟩

instance : Coe (Set M.Sentence) (Set M.Word) := ⟨fun s => s.image Sentence.toWord⟩

@[simp] lemma Sentence.iff_toWord {S : M.Sentence} : S.toWord = S.P ++ S.W := by rfl

def isSentence (W : M.Word) : Prop := ∃ S : M.Sentence, W = S

@[simp] lemma isSentence_sentence {S : M.Sentence} : M.isSentence S := ⟨S, rfl⟩



structure ProperSentence (M : SmullyanModel) extends M.Sentence where
  W_nonempty : W ≠ []

abbrev proper_sentences (M : SmullyanModel) : Set M.ProperSentence := Set.univ

def isProperSentence (W : M.Word) : Prop := M.isSentence W ∧ ¬M.isPredicate W


abbrev true_sentences (M : SmullyanModel) : Set M.Sentence := fun ⟨P, W⟩ => W ∈ P.valuated

abbrev true_proper_sentences (M : SmullyanModel) : Set M.ProperSentence := fun ⟨⟨P, W⟩, _⟩ => W ∈ M.valuation P

abbrev false_sentences (M : SmullyanModel) : Set M.Sentence := M.true_sentencesᶜ

abbrev false_proper_sentences (M : SmullyanModel) : Set M.ProperSentence := M.true_proper_sentencesᶜ


def Sentence.isTrue (S : M.Sentence) := S ∈ M.true_sentences
prefix:90 "⊨ " => Sentence.isTrue

lemma Sentence.iff_isTrue : ⊨ S ↔ S.W ∈ S.P.valuated := by rfl


def Sentence.isFalse (S : M.Sentence) := S ∈ M.false_sentences
prefix:90 "⊭ " => Sentence.isFalse

lemma Sentence.iff_isFalse_not_isTrue : ⊭ S ↔ ¬⊨ S := by simp [false_sentences, Sentence.isTrue, Sentence.isFalse]

lemma Sentence.iff_isFalse : ⊭ S ↔ S.W ∉ S.P.valuated := by simp [iff_isTrue, iff_isFalse_not_isTrue]


class IsN (M : SmullyanModel) where
  n : M.α
  n_spec₁ : ∀ P : M.Predicate, (M.isPredicate (n :: P))
  n_spec₂ : ∀ P : M.Predicate, M.valuation ⟨n :: P, n_spec₁ P⟩ = (P.valuated)ᶜ

section

variable [M.IsN]

def Predicate.negated (P : M.Predicate) : M.Predicate := ⟨IsN.n :: P.val, IsN.n_spec₁ P⟩
prefix:90 "~" => Predicate.negated

def Sentence.negated (S : M.Sentence) : M.Sentence := ⟨~S.P, S.W⟩
prefix:90 "~" => Sentence.negated

def Sentence.isNegTrue (S : M.Sentence) := ⊨ ~S

@[simp]
lemma iff_negated_valuated {P : M.Predicate} : (~P).valuated = P.valuatedᶜ := by
  simp [Predicate.valuated, Predicate.negated, IsN.n_spec₂ P];

end


class IsR (M : SmullyanModel) where
  r : M.α
  r_spec₁ : ∀ P : M.Predicate, (M.isPredicate (r :: P))
  r_spec₂ : ∀ P : M.Predicate, M.valuation ⟨r :: P, r_spec₁ P⟩ = { K : M.Predicate | K.val ++ K.val ∈ P.valuated }

section

variable [M.IsR]

def Predicate.repeated (P : M.Predicate) : M.Predicate := ⟨IsR.r :: P.val, IsR.r_spec₁ P⟩
prefix:90 "□" => Predicate.repeated

def Sentence.repeated (S : M.Sentence) : M.Sentence := ⟨□S.P, S.W⟩
prefix:90 "□" => Sentence.repeated

@[simp]
lemma iff_repeated_valuated {P : M.Predicate} : (□P).valuated = { K : M.Predicate | K.val ++ K.val ∈ P.valuated } := by
  simp [Predicate.valuated, Predicate.repeated, IsR.r_spec₂ P];

end


class IsNR (M : SmullyanModel) extends IsN M, IsR M where


variable {P : M.Predicate} {S : M.Sentence}

def Predicate.fixpoint [M.IsR] (P : M.Predicate) : M.Sentence := ⟨□P, □P⟩

lemma fixpoint_spec [M.IsR] : ⊨ P.fixpoint ↔ ⊨ (⟨P, P.fixpoint⟩) := by
  simp [Predicate.fixpoint, Sentence.iff_isTrue];

lemma iff_fixpoint_is_true [M.IsNR] : ⊨ (~P).fixpoint ↔ ↑(~P).fixpoint ∉ P.valuated := by
  simp [Predicate.fixpoint, Sentence.iff_isTrue];

lemma iff_eq {P : M.Predicate} : P.names M.true_sentences ↔ ∀ S : M.Sentence, (↑S ∈ P.valuated ↔ ⊨ S) := by
  constructor;
  . intro h S; rw [h];
    apply Function.Injective.mem_set_image Sentence.toWord_injective;
  . intro h;
    sorry;
  /-
  simp [Predicate.names, Sentence.iff_isTrue, true_sentences];
  constructor;
  . intro h S;
    replace h := subset_of_eq h;
    constructor;
    . intro h₂;
      exact Function.Injective.mem_set_image Sentence.toWord_injective |>.mp $ Set.mem_of_subset_of_mem h h₂
    . intro h₂;
      have := @Set.mem_of_subset_of_mem (M.Word) (s₁ := P.valuated) (s₂ := M.true_sentences) (a := S.W) h;
      sorry;
  . intro S;
    apply Set.eq_of_subset_of_subset;
    . sorry;
    . sorry;
  -/

lemma iff_of_names_true_sentenes {P : M.Predicate} : P.names M.true_sentences → ∀ S : M.Sentence, (↑S ∈ P.valuated ↔ ⊨ S) := by
  intro h S; rw [h];
  apply Function.Injective.mem_set_image Sentence.toWord_injective;

theorem tarski [M.IsNR] : ∀ P : M.Predicate, ¬P.names M.true_sentences := by
  intro P;
  apply not_imp_not.mpr $ iff_of_names_true_sentenes;
  apply not_forall.mpr;
  use (~P).fixpoint;
  rw [iff_fixpoint_is_true];
  tauto;

theorem goedel1 [M.IsNR] (hP : P.valuated ⊆ M.true_sentences) : ∃ S : M.Sentence, ↑S ∉ P.valuated ∧ ↑(~S) ∉ P.valuated := by
  use (~P).fixpoint;
  constructor;
  . sorry;
  . sorry;

end SmullyanModel
