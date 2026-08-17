/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic

/-!
# Operations on combinatorial subspaces for Erdős 171

This file supplies the algebra of subspaces used by the density argument.  In
particular, it contains composition, independent products and coordinate
concatenation.  The final section records carefully the two distinct operations
involving the inclusion `Fin k → Fin (k + 1)`:

* restrict the *parameters* of a large-alphabet subspace to the old alphabet;
* lift a small-alphabet subspace by mapping all of its fixed letters into the
  large alphabet.

A large-alphabet subspace can be turned back into a small-alphabet subspace
exactly when none of its fixed letters is the new last letter.
-/

namespace Combinatorics

namespace Subspace

variable {η ζ ξ α ι κ υ : Type*}

/-- Composition of combinatorial subspaces.  The convention is functional:
`U.comp V` first evaluates `V` and then evaluates `U`. -/
def comp (U : Subspace η α ι) (V : Subspace ζ α η) : Subspace ζ α ι where
  idxFun i := (U.idxFun i).elim Sum.inl V.idxFun
  proper z := by
    obtain ⟨e, he⟩ := V.proper z
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi, he]⟩

@[simp] theorem comp_idxFun (U : Subspace η α ι) (V : Subspace ζ α η) (i : ι) :
    (U.comp V).idxFun i = (U.idxFun i).elim Sum.inl V.idxFun := rfl

@[simp] theorem comp_apply (U : Subspace η α ι) (V : Subspace ζ α η)
    (x : ζ → α) : U.comp V x = U (V x) := by
  funext i
  cases hi : U.idxFun i <;> simp [comp, coe_apply, hi]

theorem comp_assoc (U : Subspace η α ι) (V : Subspace ζ α η)
    (W : Subspace ξ α ζ) :
    (U.comp V).comp W = U.comp (V.comp W) := by
  ext i
  cases hU : U.idxFun i with
  | inl a => simp [comp, hU]
  | inr e =>
      cases hV : V.idxFun e <;> simp [comp, hU, hV]

theorem comp_parameter_injective (U : Subspace η α ι) (V : Subspace ζ α η) :
    Function.Injective (U.comp V) :=
  (U.comp V).parameter_injective

theorem range_comp (U : Subspace η α ι) (V : Subspace ζ α η) :
    Set.range (U.comp V) = U '' Set.range V := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨V x, ⟨x, rfl⟩, (comp_apply U V x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, comp_apply U V x⟩

theorem range_comp_subset_range (U : Subspace η α ι) (V : Subspace ζ α η) :
    Set.range (U.comp V) ⊆ Set.range U := by
  rw [range_comp]
  exact Set.image_subset_range U _

theorem range_comp_subset_iff (U : Subspace η α ι) (V : Subspace ζ α η)
    (A : Set (ι → α)) :
    Set.range (U.comp V) ⊆ A ↔ Set.range V ⊆ U ⁻¹' A := by
  simp only [Set.range_subset_iff, Set.mem_preimage, comp_apply]

theorem image_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (A : Set (ζ → α)) :
    U '' (V '' A) = U.comp V '' A := by
  rw [Set.image_image]
  simp only [comp_apply]

theorem preimage_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (A : Set (ι → α)) :
    U.comp V ⁻¹' A = V ⁻¹' (U ⁻¹' A) := by
  ext x
  simp [comp_apply]

@[simp] theorem lineMap_comp (U : Subspace η α ι) (V : Subspace ζ α η)
    (l : Line α ζ) :
    (U.comp V).lineMap l = U.lineMap (V.lineMap l) := by
  ext i
  cases hU : U.idxFun i with
  | inl a => simp [comp, lineMap, hU]
  | inr e =>
      cases hV : V.idxFun e <;> simp [comp, lineMap, hU, hV]

/-- Independent product of two subspaces.  Its parameter directions and its
ambient coordinates are both disjoint sums. -/
def sum (U : Subspace η α ι) (V : Subspace ζ α κ) :
    Subspace (η ⊕ ζ) α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => (U.idxFun i).map id Sum.inl
    | Sum.inr j => (V.idxFun j).map id Sum.inr
  proper
    | Sum.inl e => by
        obtain ⟨i, hi⟩ := U.proper e
        exact ⟨Sum.inl i, by simp [hi]⟩
    | Sum.inr f => by
        obtain ⟨j, hj⟩ := V.proper f
        exact ⟨Sum.inr j, by simp [hj]⟩

@[simp] theorem sum_idxFun_inl (U : Subspace η α ι) (V : Subspace ζ α κ)
    (i : ι) :
    (U.sum V).idxFun (Sum.inl i) = (U.idxFun i).map id Sum.inl := rfl

@[simp] theorem sum_idxFun_inr (U : Subspace η α ι) (V : Subspace ζ α κ)
    (j : κ) :
    (U.sum V).idxFun (Sum.inr j) = (V.idxFun j).map id Sum.inr := rfl

@[simp] theorem sum_apply_inl (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η ⊕ ζ → α) (i : ι) :
    U.sum V x (Sum.inl i) = U (x ∘ Sum.inl) i := by
  cases hi : U.idxFun i <;> simp [sum, coe_apply, hi]

@[simp] theorem sum_apply_inr (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η ⊕ ζ → α) (j : κ) :
    U.sum V x (Sum.inr j) = V (x ∘ Sum.inr) j := by
  cases hj : V.idxFun j <;> simp [sum, coe_apply, hj]

/-- Join two words on disjoint coordinate sets. -/
def sumWord (x : η → α) (y : ζ → α) : η ⊕ ζ → α :=
  Sum.elim x y

@[simp] theorem sumWord_inl (x : η → α) (y : ζ → α) (e : η) :
    sumWord x y (Sum.inl e) = x e := rfl

@[simp] theorem sumWord_inr (x : η → α) (y : ζ → α) (f : ζ) :
    sumWord x y (Sum.inr f) = y f := rfl

theorem sumWord_injective :
    Function.Injective2 (sumWord : (η → α) → (ζ → α) → η ⊕ ζ → α) := by
  intro x y x' y' h
  constructor
  · funext e
    exact congrFun h (Sum.inl e)
  · funext f
    exact congrFun h (Sum.inr f)

@[simp] theorem sum_apply_sumWord (U : Subspace η α ι) (V : Subspace ζ α κ)
    (x : η → α) (y : ζ → α) :
    U.sum V (sumWord x y) = sumWord (U x) (V y) := by
  have hx : sumWord x y ∘ Sum.inl = x := by funext e; rfl
  have hy : sumWord x y ∘ Sum.inr = y := by funext f; rfl
  funext q
  cases q with
  | inl i => simpa [hx] using sum_apply_inl U V (sumWord x y) i
  | inr j => simpa [hy] using sum_apply_inr U V (sumWord x y) j

theorem sum_parameter_injective (U : Subspace η α ι) (V : Subspace ζ α κ) :
    Function.Injective (U.sum V) :=
  (U.sum V).parameter_injective

/-- Concatenate two ambient coordinate blocks while sharing the same parameter
directions. -/
def concat (U : Subspace η α ι) (V : Subspace η α κ) :
    Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => U.idxFun i
    | Sum.inr j => V.idxFun j
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp] theorem concat_idxFun_inl (U : Subspace η α ι) (V : Subspace η α κ)
    (i : ι) : (U.concat V).idxFun (Sum.inl i) = U.idxFun i := rfl

@[simp] theorem concat_idxFun_inr (U : Subspace η α ι) (V : Subspace η α κ)
    (j : κ) : (U.concat V).idxFun (Sum.inr j) = V.idxFun j := rfl

@[simp] theorem concat_apply (U : Subspace η α ι) (V : Subspace η α κ)
    (x : η → α) :
    U.concat V x = sumWord (U x) (V x) := by
  funext q
  cases q with
  | inl i => simp [concat, coe_apply, sumWord]
  | inr j => simp [concat, coe_apply, sumWord]

theorem concat_parameter_injective (U : Subspace η α ι) (V : Subspace η α κ) :
    Function.Injective (U.concat V) :=
  (U.concat V).parameter_injective

/-- Extend a subspace by a block of fixed suffix coordinates. -/
def extendRightWord (U : Subspace η α ι) (y : κ → α) :
    Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => U.idxFun i
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp] theorem extendRightWord_idxFun_inl (U : Subspace η α ι) (y : κ → α)
    (i : ι) : (U.extendRightWord y).idxFun (Sum.inl i) = U.idxFun i := rfl

@[simp] theorem extendRightWord_idxFun_inr (U : Subspace η α ι) (y : κ → α)
    (j : κ) : (U.extendRightWord y).idxFun (Sum.inr j) = Sum.inl (y j) := rfl

@[simp] theorem extendRightWord_apply (U : Subspace η α ι) (y : κ → α)
    (x : η → α) :
    U.extendRightWord y x = sumWord (U x) y := by
  funext q
  cases q with
  | inl i => simp [extendRightWord, coe_apply, sumWord]
  | inr j => simp [extendRightWord, coe_apply, sumWord]

theorem extendRightWord_parameter_injective (U : Subspace η α ι) (y : κ → α) :
    Function.Injective (U.extendRightWord y) :=
  (U.extendRightWord y).parameter_injective

/-- The canonical coordinate face on the first `m₀` coordinates.  All later
coordinates are fixed at `default`. -/
def coordinateFace {m₀ m : ℕ} [Inhabited α] (h : m₀ ≤ m) :
    Subspace (Fin m₀) α (Fin m) where
  idxFun i := if hi : i.val < m₀ then Sum.inr ⟨i.val, hi⟩ else Sum.inl default
  proper e := by
    refine ⟨Fin.castLE h e, ?_⟩
    simp [e.isLt]

@[simp] theorem coordinateFace_idxFun_castLE {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) (e : Fin m₀) :
    (coordinateFace (α := α) h).idxFun (Fin.castLE h e) = Sum.inr e := by
  simp [coordinateFace, e.isLt]

@[simp] theorem coordinateFace_apply_castLE {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) (x : Fin m₀ → α) (e : Fin m₀) :
    coordinateFace (α := α) h x (Fin.castLE h e) = x e := by
  rw [apply_inr (coordinateFace_idxFun_castLE h e)]

theorem coordinateFace_apply {m₀ m : ℕ} [Inhabited α] (h : m₀ ≤ m)
    (x : Fin m₀ → α) (i : Fin m) :
    coordinateFace (α := α) h x i =
      if hi : i.val < m₀ then x ⟨i.val, hi⟩ else default := by
  by_cases hi : i.val < m₀ <;> simp [coordinateFace, coe_apply, hi]

theorem coordinateFace_parameter_injective {m₀ m : ℕ} [Inhabited α]
    (h : m₀ ≤ m) :
    Function.Injective (coordinateFace (α := α) h) :=
  (coordinateFace (α := α) h).parameter_injective

@[simp] theorem coordinateFace_comp {m₀ m₁ m₂ : ℕ} [Inhabited α]
    (h₀₁ : m₀ ≤ m₁) (h₁₂ : m₁ ≤ m₂) :
    (coordinateFace (α := α) h₁₂).comp (coordinateFace (α := α) h₀₁) =
      coordinateFace (α := α) (h₀₁.trans h₁₂) := by
  ext i
  by_cases h₀ : i.val < m₀
  · have h₁ : i.val < m₁ := lt_of_lt_of_le h₀ h₀₁
    simp [comp, coordinateFace, h₀, h₁]
  · by_cases h₁ : i.val < m₁ <;> simp [comp, coordinateFace, h₀, h₁]

/-- Map all fixed letters of a subspace through a function.  Variable
coordinates are unchanged. -/
def mapAlphabet (U : Subspace η α ι) (f : α → υ) : Subspace η υ ι where
  idxFun i := (U.idxFun i).map f id
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi]⟩

@[simp] theorem mapAlphabet_idxFun (U : Subspace η α ι) (f : α → υ) (i : ι) :
    (U.mapAlphabet f).idxFun i = (U.idxFun i).map f id := rfl

@[simp] theorem mapAlphabet_apply (U : Subspace η α ι) (f : α → υ)
    (x : η → α) :
    U.mapAlphabet f (f ∘ x) = f ∘ U x := by
  funext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, coe_apply, hi]

@[simp] theorem mapAlphabet_id (U : Subspace η α ι) :
    U.mapAlphabet id = U := by
  ext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, hi]

theorem mapAlphabet_comp (U : Subspace η α ι) (f : α → υ) (g : υ → ξ) :
    (U.mapAlphabet f).mapAlphabet g = U.mapAlphabet (g ∘ f) := by
  ext i
  cases hi : U.idxFun i <;> simp [mapAlphabet, hi]

end Subspace

end Combinatorics

namespace Erdos171

open Set

variable {η ζ α ι κ : Type*}

/-- The product set of two families of words on disjoint coordinate types. -/
def sumSet (A : Set (η → α)) (B : Set (ζ → α)) : Set (η ⊕ ζ → α) :=
  {x | (x ∘ Sum.inl) ∈ A ∧ (x ∘ Sum.inr) ∈ B}

@[simp] theorem mem_sumSet {A : Set (η → α)} {B : Set (ζ → α)}
    {x : η ⊕ ζ → α} :
    x ∈ sumSet A B ↔ (x ∘ Sum.inl) ∈ A ∧ (x ∘ Sum.inr) ∈ B :=
  Iff.rfl

@[simp] theorem sumWord_mem_sumSet {A : Set (η → α)} {B : Set (ζ → α)}
    {x : η → α} {y : ζ → α} :
    Combinatorics.Subspace.sumWord x y ∈ sumSet A B ↔ x ∈ A ∧ y ∈ B := by
  rfl

theorem range_sum (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α κ) :
    Set.range (U.sum V) = sumSet (Set.range U) (Set.range V) := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z ∘ Sum.inl, by funext i; simp⟩,
      ⟨z ∘ Sum.inr, by funext j; simp⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨Combinatorics.Subspace.sumWord x y, ?_⟩
    rw [Combinatorics.Subspace.sum_apply_sumWord, hx, hy]
    funext q
    cases q <;> rfl

theorem preimage_sumSet (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α κ) (A : Set (ι → α)) (B : Set (κ → α)) :
    U.sum V ⁻¹' sumSet A B = sumSet (U ⁻¹' A) (V ⁻¹' B) := by
  ext x
  have hleft : (U.sum V x) ∘ Sum.inl = U (x ∘ Sum.inl) := by
    funext i
    exact U.sum_apply_inl V x i
  have hright : (U.sum V x) ∘ Sum.inr = V (x ∘ Sum.inr) := by
    funext j
    exact U.sum_apply_inr V x j
  simp only [Set.mem_preimage, mem_sumSet, hleft, hright]

section FinAlphabet

variable {k : ℕ}

/-- Include an old-alphabet word into the alphabet with one new last letter. -/
def liftWord (x : η → Fin k) : η → Fin (k + 1) :=
  fun e ↦ (x e).castSucc

@[simp] theorem liftWord_apply (x : η → Fin k) (e : η) :
    liftWord x e = (x e).castSucc := rfl

theorem liftWord_injective : Function.Injective (liftWord : (η → Fin k) → η → Fin (k + 1)) := by
  intro x y h
  funext e
  exact Fin.castSucc_injective k (congrFun h e)

/-- Image of a set of words under inclusion of the old alphabet. -/
def liftSet (A : Set (η → Fin k)) : Set (η → Fin (k + 1)) :=
  liftWord '' A

/-- Pull a set over the enlarged alphabet back to words using only old letters. -/
def restrictSet (B : Set (η → Fin (k + 1))) : Set (η → Fin k) :=
  liftWord ⁻¹' B

@[simp] theorem mem_restrictSet {B : Set (η → Fin (k + 1))} {x : η → Fin k} :
    x ∈ restrictSet B ↔ liftWord x ∈ B :=
  Iff.rfl

@[simp] theorem liftWord_mem_liftSet {A : Set (η → Fin k)} {x : η → Fin k} :
    liftWord x ∈ liftSet A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (liftWord_injective hxy).symm ▸ hy
  · exact fun hx ↦ ⟨x, hx, rfl⟩

@[simp] theorem restrictSet_liftSet (A : Set (η → Fin k)) :
    restrictSet (liftSet A) = A := by
  ext x
  simp

theorem liftSet_restrictSet (B : Set (η → Fin (k + 1))) :
    liftSet (restrictSet B) = B ∩ Set.range liftWord := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, ⟨y, rfl⟩⟩
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, hx, rfl⟩

/-- Finset version of `liftSet`. -/
def liftFinset [DecidableEq (η → Fin (k + 1))] (A : Finset (η → Fin k)) :
    Finset (η → Fin (k + 1)) :=
  A.map ⟨liftWord, liftWord_injective⟩

@[simp] theorem mem_liftFinset [DecidableEq (η → Fin (k + 1))]
    {A : Finset (η → Fin k)} {x : η → Fin k} :
    liftWord x ∈ liftFinset A ↔ x ∈ A := by
  simp [liftFinset, liftWord_injective.eq_iff]

@[simp] theorem card_liftFinset [DecidableEq (η → Fin (k + 1))]
    (A : Finset (η → Fin k)) :
    (liftFinset A).card = A.card := by
  simp [liftFinset]

end FinAlphabet

end Erdos171

namespace Combinatorics

namespace Subspace

open Erdos171

variable {η ι : Type*} {k : ℕ}

/-- Lift a small-alphabet subspace into the alphabet with one new last letter. -/
def finLift (U : Subspace η (Fin k) ι) : Subspace η (Fin (k + 1)) ι :=
  U.mapAlphabet Fin.castSucc

@[simp] theorem finLift_apply (U : Subspace η (Fin k) ι) (x : η → Fin k) :
    U.finLift (liftWord x) = liftWord (U x) := by
  exact U.mapAlphabet_apply Fin.castSucc x

theorem finLift_parameter_injective (U : Subspace η (Fin k) ι) :
    Function.Injective U.finLift :=
  U.finLift.parameter_injective

/-- A large-alphabet subspace has only old fixed letters. -/
def FixedLettersOld (U : Subspace η (Fin (k + 1)) ι) : Prop :=
  ∀ i a, U.idxFun i = Sum.inl a → a ≠ Fin.last k

theorem FixedLettersOld.ne_last {U : Subspace η (Fin (k + 1)) ι}
    (hU : U.FixedLettersOld) {i : ι} {a : Fin (k + 1)}
    (hi : U.idxFun i = Sum.inl a) : a ≠ Fin.last k :=
  hU i a hi

theorem finLift_fixedLettersOld (U : Subspace η (Fin k) ι) :
    U.finLift.FixedLettersOld := by
  intro i a hi ha
  cases hU : U.idxFun i with
  | inl b =>
      have hab : b.castSucc = a := by simpa [finLift, mapAlphabet, hU] using hi
      rw [← hab] at ha
      exact Fin.castSucc_ne_last b ha
  | inr e =>
      simp [finLift, mapAlphabet, hU] at hi

/-- A total retraction from `Fin (k + 1)` to the old alphabet.  Its value on the
new last letter is irrelevant; on every old letter it is inverse to
`Fin.castSucc`. -/
def dropLast [Inhabited (Fin k)] (a : Fin (k + 1)) : Fin k :=
  if h : a = Fin.last k then default else a.castPred h

@[simp] theorem dropLast_castSucc [Inhabited (Fin k)] (a : Fin k) :
    dropLast a.castSucc = a := by
  simp [dropLast, Fin.castSucc_ne_last, Fin.castPred_castSucc]

theorem castSucc_dropLast [Inhabited (Fin k)] {a : Fin (k + 1)}
    (ha : a ≠ Fin.last k) :
    (dropLast a).castSucc = a := by
  simp [dropLast, ha, Fin.castSucc_castPred]

/-- Restrict the fixed letters of a large-alphabet subspace through `dropLast`.
When all fixed letters are old, `finLift` recovers the original subspace. -/
def finRestrict [Inhabited (Fin k)] (U : Subspace η (Fin (k + 1)) ι) :
    Subspace η (Fin k) ι :=
  U.mapAlphabet dropLast

@[simp] theorem finRestrict_apply
    [Inhabited (Fin k)]
    (U : Subspace η (Fin (k + 1)) ι)
    (hU : U.FixedLettersOld) (x : η → Fin k) :
    liftWord (U.finRestrict x) = U (liftWord x) := by
  funext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, mapAlphabet, coe_apply, hi,
        castSucc_dropLast (hU.ne_last hi)]
  | inr e =>
      simp [finRestrict, mapAlphabet, coe_apply, hi]

@[simp] theorem finRestrict_finLift [Inhabited (Fin k)]
    (U : Subspace η (Fin k) ι) :
    U.finLift.finRestrict = U := by
  ext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, finLift, mapAlphabet, hi]
  | inr e =>
      simp [finRestrict, finLift, mapAlphabet, hi]

@[simp] theorem finLift_finRestrict
    [Inhabited (Fin k)]
    (U : Subspace η (Fin (k + 1)) ι)
    (hU : U.FixedLettersOld) :
    U.finRestrict.finLift = U := by
  ext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [finRestrict, finLift, mapAlphabet, hi,
        castSucc_dropLast (hU.ne_last hi)]
  | inr e =>
      simp [finRestrict, finLift, mapAlphabet, hi]

end Subspace

end Combinatorics

namespace Erdos171

open Set

variable {η ι : Type*} {k : ℕ}

section FinAlphabet

/-- Pull back an ambient set along a subspace while restricting its parameters
to old-alphabet words. -/
def restrictedPreimage (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) : Set (η → Fin k) :=
  {x | U (liftWord x) ∈ A}

@[simp] theorem mem_restrictedPreimage
    {U : Combinatorics.Subspace η (Fin (k + 1)) ι}
    {A : Set (ι → Fin (k + 1))} {x : η → Fin k} :
    x ∈ restrictedPreimage U A ↔ U (liftWord x) ∈ A :=
  Iff.rfl

theorem restrictedPreimage_eq (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) :
    restrictedPreimage U A = liftWord ⁻¹' (U ⁻¹' A) :=
  rfl

theorem restricted_image_subset_iff
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) (B : Set (η → Fin k)) :
    (fun x ↦ U (liftWord x)) '' B ⊆ A ↔ B ⊆ restrictedPreimage U A := by
  rw [Set.image_subset_iff]
  rfl

theorem restricted_range_subset_iff
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Set (ι → Fin (k + 1))) :
    Set.range (fun x ↦ U (liftWord x)) ⊆ A ↔ restrictedPreimage U A = Set.univ := by
  rw [Set.range_subset_iff]
  constructor
  · intro h
    ext x
    simp [h]
  · intro h x
    have hx : x ∈ restrictedPreimage U A := by rw [h]; trivial
    exact hx

theorem restricted_parameter_injective
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι) :
    Function.Injective (fun x : η → Fin k ↦ U (liftWord x)) :=
  U.parameter_injective.comp liftWord_injective

end FinAlphabet

end Erdos171
