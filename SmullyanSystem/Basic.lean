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

abbrev sentences (M : SmullyanModel) : Set M.Sentence := Set.univ

def Sentence.toWord : M.Sentence → M.Word := fun ⟨P, W⟩ => P ++ W

instance : Coe (M.Sentence) (M.Word) := ⟨Sentence.toWord⟩

instance : Coe (Set M.Sentence) (Set M.Word) := ⟨fun s => s.image Sentence.toWord⟩

@[simp] lemma Sentence.iff_toWord {S : M.Sentence} : S.toWord = S.P ++ S.W := by rfl

def isSentence (W : M.Word) : Prop := ∃ S : M.Sentence, W = S

@[simp] lemma isSentence_sentence {S : M.Sentence} : M.isSentence S := ⟨S, rfl⟩



structure ProperSentence (M : SmullyanModel) extends M.Sentence where
  W_nonempty : W ≠ []

abbrev proper_sentences (M : SmullyanModel) : Set M.ProperSentence := Set.univ

def isProperSentence (W : M.Word) : Prop := M.isSentence W ∧ ¬M.isPredicate W


def true_sentences (M : SmullyanModel) : Set M.Sentence := fun ⟨P, W⟩ => W ∈ P.valuated

def true_proper_sentences (M : SmullyanModel) : Set M.ProperSentence := fun ⟨⟨P, W⟩, _⟩ => W ∈ M.valuation P

def false_sentences (M : SmullyanModel) : Set M.Sentence := M.sentences \ M.true_sentences

def false_proper_sentences (M : SmullyanModel) : Set M.ProperSentence := M.proper_sentences \ M.true_proper_sentences


def Sentence.isTrue (S : M.Sentence) := S ∈ M.true_sentences
prefix:90 "⊨ " => Sentence.isTrue

@[simp] lemma iff_mem_true_sentences : ⊨ S ↔ S.W ∈ S.P.valuated := by rfl



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
prefix:50 "⊭ " => Sentence.isNegTrue

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

lemma fixpoint_spec [M.IsR] : ⊨ P.fixpoint ↔ ⊨ (⟨P, P.fixpoint⟩) := by simp [Predicate.fixpoint];

lemma iff_fixpoint_is_true [M.IsNR] : ⊨ (~P).fixpoint ↔ ↑(~P).fixpoint ∉ P.valuated := by simp [Predicate.fixpoint];

theorem tarski [M.IsNR] : ¬∃ P : M.Predicate, P.names M.true_sentences := by
  by_contra hC;
  sorry;

theorem goedel1 [M.IsNR] (hP : P.valuated ⊆ M.true_sentences) : ∃ S : M.Sentence, ↑S ∉ P.valuated ∧ ↑(~S) ∈ P.valuated := by
  by_contra hC;
  sorry;

end SmullyanModel
