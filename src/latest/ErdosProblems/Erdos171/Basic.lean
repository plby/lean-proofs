/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Basic finite-word and combinatorial-line infrastructure for Erdős 171

This file fixes the concrete convention used in the formalization: a word in
`[t]^n` is a function `Fin n → Fin t`, and a combinatorial line is Mathlib's
proper `Combinatorics.Line (Fin t) (Fin n)`.  It also records the elementary
injectivity and composition facts used throughout the density argument.
-/

namespace Erdos171

open Set

/-- The discrete cube `[t]^n`, represented as words of length `n` over `Fin t`. -/
abbrev Word (t n : ℕ) := Fin n → Fin t

/-- A set of words contains a (proper) combinatorial line. -/
def ContainsLine {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin t) (Fin n), Set.range l ⊆ A

theorem containsLine_iff {t n : ℕ} {A : Set (Word t n)} :
    ContainsLine A ↔
      ∃ l : Combinatorics.Line (Fin t) (Fin n), ∀ a : Fin t, l a ∈ A := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, fun a ↦ hl ⟨a, rfl⟩⟩
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hl a

theorem ContainsLine.mono {t n : ℕ} {A B : Set (Word t n)}
    (hA : ContainsLine A) (hAB : A ⊆ B) : ContainsLine B := by
  obtain ⟨l, hl⟩ := hA
  exact ⟨l, hl.trans hAB⟩

theorem containsLine_coe_finset_iff {t n : ℕ} {A : Finset (Word t n)} :
    ContainsLine (A : Set (Word t n)) ↔
      ∃ l : Combinatorics.Line (Fin t) (Fin n), ∀ a : Fin t, l a ∈ A := by
  simpa only [Finset.mem_coe] using (containsLine_iff (A := (A : Set (Word t n))))

@[simp] theorem card_word (t n : ℕ) : Fintype.card (Word t n) = t ^ n := by
  simp [Word]

end Erdos171

namespace Combinatorics

namespace Line

/-- The collection of lines in a finite cube is finite. -/
noncomputable instance instFintype {α ι : Type*} [Fintype α] [Fintype ι] :
    Fintype (Line α ι) := by
  classical
  exact Fintype.ofInjective Line.idxFun fun _ _ h ↦ Line.ext h

/-- A line template without any wildcard coordinates. -/
def NoWildcard {α ι : Type*} (f : ι → Option α) : Prop :=
  ∀ i, f i ≠ none

/-- A line is exactly a template which is not wildcard-free. -/
noncomputable def templateEquiv {α ι : Type*} :
    Line α ι ≃ {f : ι → Option α // ¬ NoWildcard f} where
  toFun l := ⟨l.idxFun, by
    intro h
    obtain ⟨i, hi⟩ := l.proper
    exact h i hi⟩
  invFun f :=
    { idxFun := f
      proper := by
        classical
        simpa only [NoWildcard, not_forall, not_ne_iff] using f.property }
  left_inv l := by
    apply Line.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

/-- Wildcard-free templates are exactly ordinary words. -/
noncomputable def fixedTemplateEquiv {α ι : Type*} :
    (ι → α) ≃ {f : ι → Option α // NoWildcard f} where
  toFun x := ⟨fun i ↦ some (x i), fun _ ↦ Option.some_ne_none _⟩
  invFun f i := (f.1 i).get (Option.ne_none_iff_isSome.mp (f.2 i))
  left_inv x := by
    funext i
    rfl
  right_inv f := by
    apply Subtype.ext
    funext i
    exact Option.some_get _

/-- The number of proper line templates is the number of all templates minus
the number of wildcard-free templates. -/
theorem card_eq_templates_sub_words {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] :
    Fintype.card (Line α ι) =
      (Fintype.card α + 1) ^ Fintype.card ι -
        Fintype.card α ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (templateEquiv (α := α) (ι := ι))]
  rw [Fintype.card_subtype_compl (NoWildcard (α := α) (ι := ι))]
  rw [← Fintype.card_congr (fixedTemplateEquiv (α := α) (ι := ι))]
  simp

/-- In `[k]^m` there are `(k+1)^m-k^m` proper combinatorial lines. -/
@[simp] theorem card_fin (k m : ℕ) :
    Fintype.card (Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  simpa using
    (card_eq_templates_sub_words (α := Fin k) (ι := Fin m))

/-- A proper combinatorial line is injective in its alphabet parameter. -/
theorem parameter_injective {α ι : Type*} (l : Line α ι) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have hiab := congrFun hab i
  simpa only [l.apply_none a i hi, l.apply_none b i hi] using hiab

theorem ncard_range [Finite α] {ι : Type*} (l : Line α ι) :
    Set.ncard (Set.range l) = Nat.card α := by
  rw [Set.ncard_range_of_injective l.parameter_injective]

theorem card_range {ι : Type*} [Fintype α] [DecidableEq (ι → α)] (l : Line α ι) :
    (Finset.univ.image l).card = Fintype.card α := by
  rw [Finset.card_image_of_injective _ l.parameter_injective, Finset.card_univ]

end Line

namespace Subspace

/-- The collection of subspaces between finite cubes is finite. -/
noncomputable instance instFintype {η α ι : Type*} [Fintype η] [Fintype α]
    [Fintype ι] : Fintype (Subspace η α ι) := by
  classical
  exact Fintype.ofInjective Subspace.idxFun fun _ _ h ↦ Subspace.ext h

/-- Evaluation on a proper subspace is injective in the parameter word. -/
theorem parameter_injective {η α ι : Type*} (U : Subspace η α ι) :
    Function.Injective U := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrFun hxy i
  simpa only [U.apply_inr (x := x) hi, U.apply_inr (x := y) hi] using hcoord

/-- Compose a line in the parameter cube with a combinatorial subspace. -/
def lineMap {η α ι : Type*} (U : Subspace η α ι) (l : Line α η) : Line α ι where
  idxFun i := (U.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] theorem lineMap_idxFun_inl {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) {i : ι} {a : α} (hi : U.idxFun i = Sum.inl a) :
    (U.lineMap l).idxFun i = some a := by
  simp [lineMap, hi]

@[simp] theorem lineMap_idxFun_inr {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) {i : ι} {e : η} (hi : U.idxFun i = Sum.inr e) :
    (U.lineMap l).idxFun i = l.idxFun e := by
  simp [lineMap, hi]

/-- Distinct parameter-space lines remain distinct after composition with a proper subspace. -/
theorem lineMap_injective {η α ι : Type*} (U : Subspace η α ι) :
    Function.Injective U.lineMap := by
  intro l₁ l₂ h
  apply Line.ext
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrArg (fun l : Line α ι ↦ l.idxFun i) h
  simpa [lineMap, hi] using hcoord

@[simp] theorem lineMap_apply {η α ι : Type*} (U : Subspace η α ι)
    (l : Line α η) (a : α) : U.lineMap l a = U (l a) := by
  funext i
  cases hi : U.idxFun i with
  | inl b => simp [lineMap, Line.coe_apply, Subspace.coe_apply, hi]
  | inr e =>
      cases he : l.idxFun e <;>
        simp [lineMap, Line.coe_apply, Subspace.coe_apply, hi, he]

theorem lineMap_range {η α ι : Type*} (U : Subspace η α ι) (l : Line α η) :
    Set.range (U.lineMap l) = U '' Set.range l := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨l a, ⟨a, rfl⟩, (lineMap_apply U l a).symm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, lineMap_apply U l a⟩

theorem ncard_range [Finite η] [Finite α] {ι : Type*} (U : Subspace η α ι) :
    Set.ncard (Set.range U) = Nat.card (η → α) := by
  rw [Set.ncard_range_of_injective U.parameter_injective]

theorem card_range {ι : Type*} [Fintype η] [DecidableEq η] [Fintype α]
    [DecidableEq (ι → α)]
    (U : Subspace η α ι) :
    (Finset.univ.image U).card = Fintype.card (η → α) := by
  rw [Finset.card_image_of_injective _ U.parameter_injective, Finset.card_univ]

end Subspace

end Combinatorics

namespace Erdos171

/-- Embed a word over `Fin k` into the same-length cube over `Fin (k+1)`. -/
def restrictWord {k m : ℕ} (w : Word k m) : Word (k + 1) m :=
  fun i ↦ Fin.castSucc (w i)

theorem restrictWord_injective {k m : ℕ} : Function.Injective (restrictWord (k := k) (m := m)) := by
  intro x y h
  funext i
  exact Fin.castSucc_inj.mp (by simpa only [restrictWord] using congrFun h i)

/-- A word over `Fin (k+1)` lies entirely in its initial `Fin k` alphabet. -/
def IsRestrictedWord {k m : ℕ} (w : Word (k + 1) m) : Prop :=
  ∀ i, w i ≠ Fin.last k

/-- Ordinary `Fin k` words are equivalent to `Fin (k+1)` words which avoid the
new last letter. -/
noncomputable def restrictedWordEquiv (k m : ℕ) :
    Word k m ≃ {w : Word (k + 1) m // IsRestrictedWord w} where
  toFun w := ⟨restrictWord w, fun i ↦ Fin.castSucc_ne_last (w i)⟩
  invFun w := fun i ↦ (w.1 i).castPred (w.2 i)
  left_inv w := by
    funext i
    exact Fin.castPred_castSucc
  right_inv w := by
    apply Subtype.ext
    funext i
    exact Fin.castSucc_castPred (w.1 i) (w.2 i)

theorem range_restrictWord {k m : ℕ} :
    Set.range (restrictWord (k := k) (m := m)) =
      {w : Word (k + 1) m | IsRestrictedWord w} := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact fun i ↦ Fin.castSucc_ne_last (v i)
  · intro hw
    let w' : {w : Word (k + 1) m // IsRestrictedWord w} := ⟨w, hw⟩
    refine ⟨(restrictedWordEquiv k m).symm w', ?_⟩
    exact congrArg Subtype.val ((restrictedWordEquiv k m).apply_symm_apply w')

/-- Replace every wildcard in a line template by the new last letter.  This is
the endpoint at the additional letter in the density-Hales--Jewett argument. -/
def templateEndpoint {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Word (k + 1) m :=
  fun i ↦ finSuccEquivLast.symm (l.idxFun i)

/-- Regard an internal `Fin k` line template as a line over `Fin (k+1)` by
embedding all of its fixed letters. -/
def templateExtension {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Combinatorics.Line (Fin (k + 1)) (Fin m) :=
  l.map Fin.castSucc

@[simp] theorem templateExtension_castSucc {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) (a : Fin k) :
    templateExtension l (Fin.castSucc a) = restrictWord (l a) := by
  funext i
  cases hi : l.idxFun i with
  | none =>
      simp [templateExtension, restrictWord, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]
  | some b =>
      simp [templateExtension, restrictWord, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]

@[simp] theorem templateExtension_last {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    templateExtension l (Fin.last k) = templateEndpoint l := by
  funext i
  cases hi : l.idxFun i with
  | none =>
      simp [templateExtension, templateEndpoint, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]
  | some a =>
      simp [templateExtension, templateEndpoint, Combinatorics.Line.map,
        Combinatorics.Line.coe_apply, hi]

@[simp] theorem templateEndpoint_of_none {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) {i : Fin m}
    (hi : l.idxFun i = none) :
    templateEndpoint l i = Fin.last k := by
  simp [templateEndpoint, hi]

@[simp] theorem templateEndpoint_of_some {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) {i : Fin m} {a : Fin k}
    (hi : l.idxFun i = some a) :
    templateEndpoint l i = Fin.castSucc a := by
  simp [templateEndpoint, hi]

theorem templateEndpoint_not_restricted {k m : ℕ}
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ¬ IsRestrictedWord (templateEndpoint l) := by
  intro h
  obtain ⟨i, hi⟩ := l.proper
  exact h i (templateEndpoint_of_none l hi)

/-- Proper internal line templates are in bijection with the words which use
the new last letter in at least one coordinate. -/
noncomputable def templateEndpointEquiv (k m : ℕ) :
    Combinatorics.Line (Fin k) (Fin m) ≃
      {w : Word (k + 1) m // ¬ IsRestrictedWord w} where
  toFun l := ⟨templateEndpoint l, templateEndpoint_not_restricted l⟩
  invFun w :=
    { idxFun := fun i ↦ finSuccEquivLast (w.1 i)
      proper := by
        classical
        have hw : ∃ i, w.1 i = Fin.last k := by
          simpa only [IsRestrictedWord, not_forall, not_ne_iff] using w.2
        obtain ⟨i, hi⟩ := hw
        exact ⟨i, by simp [hi]⟩ }
  left_inv l := by
    apply Combinatorics.Line.ext
    funext i
    simp [templateEndpoint]
  right_inv w := by
    apply Subtype.ext
    funext i
    simp [templateEndpoint]

theorem templateEndpoint_injective {k m : ℕ} :
    Function.Injective (templateEndpoint (k := k) (m := m)) := by
  intro l₁ l₂ h
  apply (templateEndpointEquiv k m).injective
  apply Subtype.ext
  exact h

theorem range_templateEndpoint {k m : ℕ} :
    Set.range (templateEndpoint (k := k) (m := m)) =
      {w : Word (k + 1) m | ¬ IsRestrictedWord w} := by
  ext w
  constructor
  · rintro ⟨l, rfl⟩
    exact templateEndpoint_not_restricted l
  · intro hw
    let w' : {w : Word (k + 1) m // ¬ IsRestrictedWord w} := ⟨w, hw⟩
    refine ⟨(templateEndpointEquiv k m).symm w', ?_⟩
    exact congrArg Subtype.val ((templateEndpointEquiv k m).apply_symm_apply w')

theorem range_templateEndpoint_eq_compl_restrictWord {k m : ℕ} :
    Set.range (templateEndpoint (k := k) (m := m)) =
      (Set.range (restrictWord (k := k) (m := m)))ᶜ := by
  rw [range_templateEndpoint, range_restrictWord]
  rfl

@[simp] theorem ncard_range_templateEndpoint (k m : ℕ) :
    Set.ncard (Set.range (templateEndpoint (k := k) (m := m))) =
      (k + 1) ^ m - k ^ m := by
  rw [Set.ncard_range_of_injective templateEndpoint_injective]
  simp only [Nat.card_eq_fintype_card, Combinatorics.Line.card_fin]

/-- A line in a subspace pullback gives a line in the original set. -/
theorem containsLine_of_subspace_preimage {t m n : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    {A : Set (Word t n)} (h : ContainsLine (U ⁻¹' A)) : ContainsLine A := by
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Combinatorics.Subspace.lineMap_apply]
  exact hl ⟨a, rfl⟩

end Erdos171
