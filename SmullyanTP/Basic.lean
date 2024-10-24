import Mathlib.Tactic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique
import Aesop

namespace List

def IsProperPrefix (l₁ l₂ : List α) := ∃ t ≠ [], l₁ ++ t = l₂
infixl:50 " <+:: " => IsProperPrefix

variable {l₁ l₂ : List α}

lemma isPrefix_of_isProperPrefix : l₁ <+:: l₂ → l₁ <+: l₂ := by
  intro h;
  obtain ⟨t, _, h⟩ := h;
  use t;

end List


structure SmullyanModel where
  α : Type*
  isPredicate : List α → Prop
  isPredicate_spec : ∀ P : { x // isPredicate x }, ∀ x ≠ [], ¬isPredicate (P.val ++ x)
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
  pred : M.Predicate
  word : M.Word

lemma Sentence.ext : ∀ {S₁ S₂ : M.Sentence}, S₁.pred = S₂.pred → S₁.word = S₂.word → S₁ = S₂ := by
  intros S₁ S₂ hP hW;
  cases S₁; cases S₂;
  subst hP hW;
  tauto;

abbrev sentences (M : SmullyanModel) : Set M.Sentence := Set.univ

def Sentence.toWord : M.Sentence → M.Word := fun ⟨P, W⟩ => P ++ W

lemma Sentence.exists_unique_pred_word (S : M.Sentence) : ∃! P, ∃! W, ⟨P, W⟩ = S := by
  apply exists_unique_of_exists_of_unique;
  . use S.pred;
    apply exists_unique_of_exists_of_unique;
    . use S.word;
    . rintro W₁ W₂ h₁ h₂;
      rw [←h₂] at h₁;
      simpa using h₁;
  . intro P₁ P₂ ⟨W₁, h₁, _⟩ ⟨W₂, h₂, _⟩;
    subst h₁;
    simp_all only [mk.injEq, true_and, implies_true];

lemma Sentence.exists_unique_pred (S : M.Sentence) : ∃! P, ⟨P, S.word⟩ = S := by
  apply exists_unique_of_exists_of_unique;
  . use S.pred;
  . intro P₁ P₂ h₁ h₂;
    rw [←h₂] at h₁;
    simpa using h₁;

lemma Sentence.exists_unique_pred_toWord (S : M.Sentence) : ∃! P : M.Predicate, ∃ W : M.Word, P ++ W = S.toWord := by
  simp only [Sentence.toWord];
  apply exists_unique_of_exists_of_unique;
  . use S.pred, S.word;
  . rintro P₁ P₂ ⟨W₁, h₁⟩ ⟨W₂, h₂⟩;
    wlog h : (P₁.val <+:: P₂.val);
    . refine this S P₂ P₁ W₂ h₂ W₁ h₁ ?_ |>.symm;
      simp [List.IsProperPrefix] at h;
      sorry;
    obtain ⟨t, ht, h⟩ := h;
    have := M.isPredicate_spec P₁ t ht;
    simp [h] at this;

lemma Sentence.exists_unique_word (S : M.Sentence) : ∃! W, ⟨S.pred, W⟩ = S := by
  apply exists_unique_of_exists_of_unique;
  . use S.word;
  . intro W₁ W₂ h₁ h₂;
    rw [←h₂] at h₁;
    simpa using h₁;

@[simp]
lemma Sentence.toWord_injective : Function.Injective (Sentence.toWord (M := M)) := by
  simp [Function.Injective, Sentence.toWord];
  intro S₁ S₂ h;
  obtain ⟨P₁, ⟨W₁, hw₁⟩, h₁⟩ := Sentence.exists_unique_pred_toWord S₁;
  obtain ⟨P₂, ⟨W₂, hw₂⟩, h₂⟩ := Sentence.exists_unique_pred_toWord S₂;
  simp at h₁ h₂;
  have := h₁ P₂ P₂.prop W₂;
  have := h₂ P₂ P₂.prop W₂ hw₂;
  apply Sentence.ext;
  . sorry;
  . sorry;

instance : Coe (M.Sentence) (M.Word) := ⟨Sentence.toWord⟩

instance : Coe (Set M.Sentence) (Set M.Word) := ⟨fun s => s.image Sentence.toWord⟩

@[simp] lemma Sentence.iff_toWord {S : M.Sentence} : S.toWord = S.pred ++ S.word := by rfl

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
prefix:50 "⊨ " => Sentence.isTrue

lemma Sentence.iff_isTrue {S : M.Sentence} : ⊨ S ↔ S.word ∈ S.pred.valuated := by rfl

class IsN (M : SmullyanModel) where
  n : M.α
  n_spec₁ : ∀ P : M.Predicate, (M.isPredicate (n :: P))
  n_spec₂ : ∀ P : M.Predicate, M.valuation ⟨n :: P, n_spec₁ P⟩ = (P.valuated)ᶜ

section

variable [M.IsN] {P : M.Predicate} {S : M.Sentence}

def Predicate.neg (P : M.Predicate) : M.Predicate := ⟨IsN.n :: P.val, IsN.n_spec₁ P⟩
prefix:90 "~" => Predicate.neg

def Sentence.neg (S : M.Sentence) : M.Sentence := ⟨~S.pred, S.word⟩
prefix:90 "~" => Sentence.neg

@[simp] lemma Sentence.eq_neg_pred {S : M.Sentence} : (~S).pred = ~(S.pred) := by rfl

@[simp] lemma Sentence.eq_neg_word {S : M.Sentence} : (~S).word = S.word := by rfl

def Sentence.isNegatedTrue (S : M.Sentence) := ⊨ ~S
prefix:50 "⊭ " => Sentence.isNegatedTrue

lemma Sentence.iff_isNegatedTrue {S : M.Sentence} : ⊭ S ↔ (~S).word ∈ (~S).pred.valuated := by simp [Sentence.isNegatedTrue, Sentence.iff_isTrue]

@[simp] lemma Predicate.eq_neg_valuated {P : M.Predicate} : (~P).valuated = P.valuatedᶜ := IsN.n_spec₂ P

@[simp] lemma Predicate.eq_double_neg_valuated (P : M.Predicate) : (~~P).valuated = P.valuated := by simp_all only [eq_neg_valuated, compl_compl];

lemma Sentence.iff_isNegTrue_neg_isTrue : ⊭ ~S ↔ ⊨ S := by
  simp [Sentence.iff_isTrue, Sentence.isNegatedTrue];

@[simp]
lemma Sentence.iff_isNegTrue_not_isTrue : ⊭ S ↔ ¬⊨ S := by
  simp only [Sentence.isNegatedTrue, Sentence.neg, Sentence.iff_isTrue, Predicate.eq_neg_valuated];
  tauto;

end


class IsR (M : SmullyanModel) where
  r : M.α
  r_spec₁ : ∀ P : M.Predicate, (M.isPredicate (r :: P))
  r_spec₂ : ∀ P : M.Predicate, M.valuation ⟨r :: P, r_spec₁ P⟩ = { K : M.Predicate | K.val ++ K.val ∈ P.valuated }

section

variable [M.IsR]

def Predicate.ros (P : M.Predicate) : M.Predicate := ⟨IsR.r :: P.val, IsR.r_spec₁ P⟩
prefix:90 "□" => Predicate.ros

def Sentence.ros (S : M.Sentence) : M.Sentence := ⟨□S.pred, S.word⟩
prefix:90 "□" => Sentence.ros

@[simp] lemma Sentence.eq_ros_pred {S : M.Sentence} : (□S).pred = □(S.pred) := by rfl

@[simp] lemma Sentence.eq_ros_word {S : M.Sentence} : (□S).word = S.word := by rfl

@[simp]
lemma eq_ros_valuated {P : M.Predicate} : (□P).valuated = { K : M.Predicate | K.val ++ K.val ∈ P.valuated } := by
  simp [Predicate.valuated, Predicate.ros, IsR.r_spec₂ P];

end


class IsNR (M : SmullyanModel) extends IsN M, IsR M where


variable {P : M.Predicate} {S : M.Sentence}

def Predicate.fixpoint [M.IsR] (P : M.Predicate) : M.Sentence := ⟨□P, □P⟩

lemma fixpoint_spec [M.IsR] : ⊨ P.fixpoint ↔ ⊨ (⟨P, P.fixpoint⟩) := by
  simp [Predicate.fixpoint, Sentence.iff_isTrue];


lemma iff_isTrue_neg_fixpoint [M.IsNR] : ⊨ (~P).fixpoint ↔ ↑(~P).fixpoint ∉ P.valuated := by
  simp [Predicate.fixpoint, Sentence.iff_isTrue];

lemma iff_isTrue_not_neg_fixpoint [M.IsNR] : ¬⊨ (~P).fixpoint ↔ ↑(~P).fixpoint ∈ P.valuated := by simpa using iff_isTrue_neg_fixpoint (P := P) |>.not;

lemma iff_mem_toWord_true_sentence_mem_true_sentence : (S.toWord ∈ Sentence.toWord '' M.true_sentences) ↔ (S ∈ M.true_sentences) := by
  apply Function.Injective.mem_set_image Sentence.toWord_injective;

lemma iff_of_names_true_sentenes {P : M.Predicate} : P.names M.true_sentences → ∀ S : M.Sentence, (↑S ∈ P.valuated ↔ ⊨ S) := by
  intro h S; rw [h];
  simp only [iff_mem_toWord_true_sentence_mem_true_sentence];
  tauto;

theorem tarski [M.IsNR] : ¬∃ P : M.Predicate, P.names M.true_sentences := by
  by_contra hC;
  obtain ⟨P, hP⟩ := hC;
  let S := (~P).fixpoint;
  have : ↑S ∈ P.valuated ↔ ⊨ S := iff_of_names_true_sentenes hP S;
  rw [iff_isTrue_neg_fixpoint] at this;
  tauto;

theorem goedel1 [M.IsNR] (hP : P.valuated ⊆ M.true_sentences) : ∃ S : M.Sentence, ↑S ∉ P.valuated ∧ ↑(~S) ∉ P.valuated := by
  let S := (~P).fixpoint;
  use S;
  have h : ⊨ S := by
    by_contra hC;
    have : ↑S ∈ P.valuated := iff_isTrue_not_neg_fixpoint.mp hC;
    have : ⊨ S := iff_mem_toWord_true_sentence_mem_true_sentence.mp $ hP this;
    contradiction;
  constructor;
  . exact iff_isTrue_neg_fixpoint.mp h;
  . apply Set.not_mem_subset (s := P.valuated) (t := M.true_sentences) hP;
    apply iff_mem_toWord_true_sentence_mem_true_sentence.not.mpr;
    apply Sentence.iff_isNegTrue_not_isTrue.mp;
    apply Sentence.iff_isNegTrue_neg_isTrue.mpr;
    assumption;

end SmullyanModel
