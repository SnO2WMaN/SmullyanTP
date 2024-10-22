import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique
import Aesop


structure SmullyanModel where
  α : Type*
  isPredicate : List α → Prop
  isPredicate_spec : ∀ p : { x // isPredicate x }, ∀ x ≠ [], ¬isPredicate (p.val ++ x)
  val : { x // isPredicate x } → Set (List α)

namespace SmullyanModel

section

variable (M : SmullyanModel)

abbrev Word := List M.α

abbrev words : Set M.Word := Set.univ

abbrev epsilon : M.Word := []


abbrev Predicate := { P // M.isPredicate P }

abbrev predicates : Set M.Predicate := Set.univ

instance : Coe (Set M.Predicate) (Set M.Word) := ⟨fun s => s.image (·.val)⟩

@[simp] lemma isPredicate_predicate {P : M.Predicate} : M.isPredicate P.val := P.property


structure Sentence where
  P : M.Predicate
  W : M.Word

abbrev sentences : Set M.Sentence := Set.univ

abbrev Sentence.toWord {M : SmullyanModel} : M.Sentence → M.Word := fun ⟨P, W⟩ => P ++ W

instance : Coe (M.Sentence) (M.Word) := ⟨Sentence.toWord⟩

instance : Coe (Set M.Sentence) (Set M.Word) := ⟨fun s => s.image Sentence.toWord⟩

@[simp] lemma Sentence.iff_toWord {M : SmullyanModel} {S : M.Sentence} : S.toWord = S.P ++ S.W := by rfl

def isSentence (W : M.Word) : Prop := ∃ S : M.Sentence, W = S

@[simp] lemma isSentence_sentence {S : M.Sentence} : M.isSentence S := ⟨S, rfl⟩


structure ProperSentence extends M.Sentence where
  W_nonempty : W ≠ []
abbrev proper_sentences : Set M.ProperSentence := Set.univ
def isProperSentence (W : M.Word) : Prop := M.isSentence W ∧ ¬M.isPredicate W


def Predicate.names {M : SmullyanModel} (P : M.Predicate) (V : Set M.Word) := M.val P = V


def true_sentences : Set M.Sentence := fun ⟨P, W⟩ => W ∈ M.val P

def true_proper_sentences : Set M.ProperSentence := fun ⟨⟨P, W⟩, _⟩ => W ∈ M.val P

def false_sentences : Set M.Sentence := M.sentences \ M.true_sentences

def false_proper_sentences : Set M.ProperSentence := M.proper_sentences \ M.true_proper_sentences




def Sentence.isTrue {M : SmullyanModel} (S : M.Sentence) := S ∈ M.true_sentences
prefix:90 "⊨ " => Sentence.isTrue

class IsN where
  n : M.α
  n_spec₁ : ∀ P : M.Predicate, (M.isPredicate (n :: P))
  n_spec₂ : ∀ P : M.Predicate, M.val ⟨n :: P, n_spec₁ P⟩ = M.words \ M.val P

section

variable {M} [M.IsN]

abbrev Predicate.negated (P : M.Predicate) : M.Predicate := ⟨IsN.n :: P.val, IsN.n_spec₁ P⟩
prefix:90 "~" => Predicate.negated

abbrev Sentence.negated (S : M.Sentence) : M.Sentence := ⟨⟨IsN.n :: S.P, IsN.n_spec₁ S.P⟩, S.W⟩
prefix:90 "~" => Sentence.negated

def Sentence.isNegTrue (S : M.Sentence) := ⊨ ~S
prefix:50 "⊭ " => Sentence.isNegTrue

@[simp] lemma IsN.n_spec₂' {P : M.Predicate} : M.val (~P) = (M.val P)ᶜ := by simp [IsN.n_spec₂ P]; aesop;

end


class IsR where
  r : M.α
  r_spec₁ : ∀ P : M.Predicate, (M.isPredicate (r :: P))
  r_spec₂ : ∀ P : M.Predicate, M.val ⟨r :: P, r_spec₁ P⟩ = { K : M.Predicate | K.val ++ K.val ∈ M.val P }

section

variable {M} [M.IsR]

abbrev Predicate.repeated (P : M.Predicate) : M.Predicate := ⟨IsR.r :: P.val, IsR.r_spec₁ P⟩
prefix:90 "□" => Predicate.repeated

abbrev Sentence.repeated (S : M.Sentence) : M.Sentence := ⟨⟨IsR.r :: S.P.val, IsR.r_spec₁ S.P⟩, S.W⟩
prefix:90 "□" => Sentence.repeated

@[simp] lemma Predicate.repeated_isPredicate {P : M.Predicate} : M.isPredicate (□P) := IsR.r_spec₁ P
@[simp] lemma Sentence.repeated_isSentence {S : M.Sentence} : M.isSentence (□S) := by use ⟨□S.P, S.W⟩;

@[simp] lemma IsR.repeated_val {P : M.Predicate} : M.val (□P) = { K : M.Predicate | K.val ++ K.val ∈ M.val P } := by rw [IsR.r_spec₂ P];

end


class IsNR extends IsN M, IsR M where

end



variable {M : SmullyanModel}

@[simp] lemma iff_mem_true_sentences : ⊨ S ↔ S.W ∈ M.val S.P := by rfl


def Predicate.fixpoint [M.IsR] (P : M.Predicate) : M.Sentence := ⟨□P, □P⟩

theorem fixpoint_spec [M.IsR] {P : M.Predicate} : ⊨ P.fixpoint ↔ ⊨ (⟨P, P.fixpoint⟩) := by
  simp_all [Predicate.fixpoint, Predicate.repeated_isPredicate];
  intros;
  exact Predicate.repeated_isPredicate;

/-
lemma fixpoint_mem [M.IsNR] {P : M.Predicate} : ⊨ (~P).fixpoint ↔ ↑(~P).fixpoint ∉ M.val P := by
  simp [Predicate.fixpoint];
  intro;
  exact Predicate.repeated_isPredicate;
  constructor;
  . intro h;
    have := fixpoint_spec.mp h;
    simp at this;
    simp [fixpoint_spec]
    simp only [iff_mem_true_sentences] at h;
    simp only [iff_mem_true_sentences, Sentence.iff_toWord, Predicate.fixpoint];
    intro h;
    sorry;
  . sorry;

theorem tarski [M.IsNR] : ¬∃ P : M.Predicate, P.names M.true_sentences := by
  by_contra hC;
  obtain ⟨P, hP⟩ := hC;
  simp [Predicate.names] at hP;
  have := subset_of_eq hP;

  intro P;
  simp only [Predicate.names];
  suffices M.Φ P ⊂ M.true_sentences by exact ne_of_ssubset this;
  by_cases hF : P.fixpoint ∈ M.true_sentences;
  . constructor;
    . sorry;
    . sorry;
  . constructor;
    . sorry;
    . sorry;
  -- by_cases
  constructor;
  . intro W hW;
    simp;
    use ⟨P, W⟩;
    constructor;
    . sorry;
    . sorry;
  . apply Set.not_subset.mpr;
    use P.fixpoint;
    simp [fixpoint_spec];
    sorry;
  -- let F := P.fixpoint;
-/

end SmullyanModel
