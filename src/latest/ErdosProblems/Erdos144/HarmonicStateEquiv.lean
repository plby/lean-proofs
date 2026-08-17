/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicStateExpectation
import ErdosProblems.Erdos144.HarmonicSubtype

/-!
# Equivalence between ten-state profiles and supported ternary pairs

The ten-state product model is just the ordinary harmonic random-set model,
together with two independent ternary labels at every selected coordinate.
This file records that statement as an explicit finite equivalence.  Keeping
the equivalence separate from the largest-coordinate estimates makes it
possible to change variables in finite sums without dependent reindexing by
hand.
-/

open scoped BigOperators

namespace Erdos144.HarmonicStateEquiv

noncomputable section

attribute [local instance] Classical.propDecidable

open HarmonicStateExpectation

/-- The selected coordinates of an ambient ten-state profile. -/
def profileSupport {I : Finset ℕ} (q : ↑I → EnergyState) : Finset ↑I :=
  Finset.univ.filter fun i ↦ Selects q i

@[simp] theorem mem_profileSupport {I : Finset ℕ}
    (q : ↑I → EnergyState) (i : ↑I) :
    i ∈ profileSupport q ↔ q i ≠ none := by
  rw [profileSupport, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ i)

/-- The ordinary-natural-number support of a ten-state profile. -/
def supportValues {I : Finset ℕ} (q : ↑I → EnergyState) : Finset ℕ :=
  (profileSupport q).image Subtype.val

theorem supportValues_subset {I : Finset ℕ} (q : ↑I → EnergyState) :
    supportValues q ⊆ I := by
  intro n hn
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
  exact i.property

@[simp] theorem mem_supportValues {I : Finset ℕ}
    (q : ↑I → EnergyState) {n : ℕ} :
    n ∈ supportValues q ↔ ∃ hn : n ∈ I, q ⟨n, hn⟩ ≠ none := by
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨i.property, (mem_profileSupport q i).mp hi⟩
  · rintro ⟨hnI, hn⟩
    let i : ↑I := ⟨n, hnI⟩
    exact Finset.mem_image.mpr ⟨i, (mem_profileSupport q i).mpr hn, rfl⟩

@[simp] theorem card_supportValues {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    (supportValues q).card = (profileSupport q).card := by
  exact Finset.card_image_iff.mpr Subtype.val_injective.injOn

theorem supportValues_eq_profileSelectedNaturals {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    supportValues q = profileSelectedNaturals q := by
  rfl

/-- A support inside `I`, together with an ordered pair of ternary states on
that support.  Since the support consists of elements of the subtype `I`, its
inclusion in `I` is part of the type. -/
abbrev SupportPairData (I : Finset ℕ) :=
  Σ S : Finset ↑I, (↑S → Fin 3) × (↑S → Fin 3)

/-- Read the selected pair of ternary labels from a profile. -/
def profileLabels {I : Finset ℕ} (q : ↑I → EnergyState) :
    (↑(profileSupport q) → Fin 3) × (↑(profileSupport q) → Fin 3) :=
  (fun i ↦ (Option.get (q i.1)
      (Option.ne_none_iff_isSome.mp ((mem_profileSupport q i.1).mp i.2))).1,
   fun i ↦ (Option.get (q i.1)
      (Option.ne_none_iff_isSome.mp ((mem_profileSupport q i.1).mp i.2))).2)

/-- Split an ambient profile into its support and its two ternary labels. -/
def profileToData {I : Finset ℕ} (q : ↑I → EnergyState) :
    SupportPairData I :=
  ⟨profileSupport q, profileLabels q⟩

/-- Reassemble a supported pair of ternary labels into an ambient profile. -/
def dataToProfile {I : Finset ℕ} (d : SupportPairData I) :
    ↑I → EnergyState := fun i ↦
  if hi : i ∈ d.1 then
    some (d.2.1 ⟨i, hi⟩, d.2.2 ⟨i, hi⟩)
  else none

@[simp] theorem dataToProfile_apply_mem {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) (i : ↑I) (hi : i ∈ S) :
    dataToProfile (⟨S, (a, b)⟩ : SupportPairData I) i =
      some (a ⟨i, hi⟩, b ⟨i, hi⟩) := by
  simp [dataToProfile, hi]

@[simp] theorem dataToProfile_apply_not_mem {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) (i : ↑I) (hi : i ∉ S) :
    dataToProfile (⟨S, (a, b)⟩ : SupportPairData I) i = none := by
  simp [dataToProfile, hi]

@[simp] theorem selects_dataToProfile_iff {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) (i : ↑I) :
    Selects (dataToProfile (⟨S, (a, b)⟩ : SupportPairData I)) i ↔ i ∈ S := by
  by_cases hi : i ∈ S <;> simp [Selects, dataToProfile, hi]

theorem dataToProfile_profileToData {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    dataToProfile (profileToData q) = q := by
  funext i
  by_cases hi : q i = none
  · simp [dataToProfile, profileToData, profileLabels, hi]
  · cases hqi : q i with
    | none => exact False.elim (hi hqi)
    | some xy =>
      simp [dataToProfile, profileToData, profileLabels, hqi]

theorem profileSupport_dataToProfile {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) :
    profileSupport (dataToProfile (⟨S, (a, b)⟩ : SupportPairData I)) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [profileSupport, Selects, dataToProfile, hi]

theorem profileToData_dataToProfile {I : Finset ℕ}
    (d : SupportPairData I) :
    profileToData (dataToProfile d) = d := by
  rcases d with ⟨S, a, b⟩
  have hS := profileSupport_dataToProfile S a b
  apply Sigma.ext hS
  let qd := dataToProfile (⟨S, (a, b)⟩ : SupportPairData I)
  change profileLabels qd ≍ (a, b)
  have hmem : ∀ x : ↑I, x ∈ profileSupport qd ↔ x ∈ S := by
    intro x
    rw [show profileSupport qd = S from hS]
  have hdom : {x : ↑I // x ∈ profileSupport qd} = {x : ↑I // x ∈ S} :=
    congrArg (fun T : Finset ↑I ↦ {x : ↑I // x ∈ T}) hS
  have ha : (profileLabels qd).1 ≍ a := by
    apply Function.hfunext hdom
    intro i j hij
    have hbase : (i.1 : ↑I) = j.1 :=
      (Subtype.heq_iff_coe_eq hmem).mp hij
    have hq : qd i.1 = some (a j, b j) := by
      simp [qd, dataToProfile, hbase, j.property]
    simp [profileLabels, hq]
  have hb : (profileLabels qd).2 ≍ b := by
    apply Function.hfunext hdom
    intro i j hij
    have hbase : (i.1 : ↑I) = j.1 :=
      (Subtype.heq_iff_coe_eq hmem).mp hij
    have hq : qd i.1 = some (a j, b j) := by
      simp [qd, dataToProfile, hbase, j.property]
    simp [profileLabels, hq]
  grind

/-- The explicit finite equivalence between ten-state profiles and a support
carrying two ordered ternary labelings. -/
def profileEquiv (I : Finset ℕ) :
    (↑I → EnergyState) ≃ SupportPairData I where
  toFun := profileToData
  invFun := dataToProfile
  left_inv := dataToProfile_profileToData
  right_inv := profileToData_dataToProfile

@[simp] theorem profileEquiv_apply_fst {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    (profileEquiv I q).1 = profileSupport q := rfl

@[simp] theorem profileEquiv_symm_apply {I : Finset ℕ}
    (d : SupportPairData I) :
    (profileEquiv I).symm d = dataToProfile d := rfl

/-- Coordinate equation for the inverse of `profileEquiv`.  This is useful
when a largest-coordinate argument starts with supported ternary data and
then returns to the ambient ten-state profile. -/
theorem profileEquiv_symm_apply_coordinate {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) (i : ↑I) :
    (profileEquiv I).symm (⟨S, (a, b)⟩ : SupportPairData I) i =
      if hi : i ∈ S then some (a ⟨i, hi⟩, b ⟨i, hi⟩) else none := by
  rfl

/-! ## Exact weight preservation -/

private theorem prod_selected_localEnergyWeight {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    (∏ i ∈ profileSupport q, localEnergyWeight i.1 (q i)) =
      (∏ i ∈ profileSupport q, 1 / (i.1 : ℝ)) /
        (9 : ℝ) ^ (profileSupport q).card := by
  calc
    (∏ i ∈ profileSupport q, localEnergyWeight i.1 (q i)) =
        ∏ i ∈ profileSupport q, (1 / (i.1 : ℝ)) / 9 := by
      apply Finset.prod_congr rfl
      intro i hi
      have hqi : q i ≠ none := (mem_profileSupport q i).mp hi
      cases h : q i with
      | none => exact False.elim (hqi h)
      | some xy =>
          simp only [localEnergyWeight]
          ring
    _ = (∏ i ∈ profileSupport q, 1 / (i.1 : ℝ)) /
        (9 : ℝ) ^ (profileSupport q).card := by
      rw [Finset.prod_div_distrib]
      simp

private theorem prod_unselected_localEnergyWeight {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    (∏ i ∈ (Finset.univ : Finset ↑I) with ¬ Selects q i,
        localEnergyWeight i.1 (q i)) =
      ∏ i ∈ (Finset.univ : Finset ↑I) \ profileSupport q,
        (1 - 1 / (i.1 : ℝ)) := by
  have hsets :
      (Finset.univ : Finset ↑I).filter (fun i ↦ ¬ Selects q i) =
        (Finset.univ : Finset ↑I) \ profileSupport q := by
    ext i
    simp [profileSupport]
  rw [hsets]
  apply Finset.prod_congr rfl
  intro i hi
  have hqi : q i = none := by
    have : i ∉ profileSupport q := (Finset.mem_sdiff.mp hi).2
    simpa [mem_profileSupport] using this
  simp [hqi, localEnergyWeight]

/-- Exact identity between ten-state profile mass and harmonic Bernoulli mass
on the selected subtype support.  Conditional on the support, the two
ternary labels are uniform among `9^|S|` ordered pairs. -/
theorem energyProfileWeight_eq_subtype_weight_div {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    energyProfileWeight I q =
      Erdos697.Bernoulli.weight (Finset.univ : Finset ↑I)
          (fun i ↦ 1 / (i.1 : ℝ)) (profileSupport q) /
        (9 : ℝ) ^ (profileSupport q).card := by
  unfold energyProfileWeight Erdos697.Bernoulli.weight
  change (∏ i ∈ (Finset.univ : Finset ↑I), localEnergyWeight i.1 (q i)) = _
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset ↑I) (fun i ↦ Selects q i)
      (fun i ↦ localEnergyWeight i.1 (q i))]
  change
    (∏ i ∈ profileSupport q, localEnergyWeight i.1 (q i)) *
        (∏ i ∈ (Finset.univ : Finset ↑I) with ¬ Selects q i,
          localEnergyWeight i.1 (q i)) = _
  rw [prod_selected_localEnergyWeight, prod_unselected_localEnergyWeight]
  ring

private def valueEmbedding (I : Finset ℕ) : ↑I ↪ ℕ where
  toFun := Subtype.val
  inj' := Subtype.val_injective

private theorem map_valueEmbedding_univ (I : Finset ℕ) :
    (Finset.univ : Finset ↑I).map (valueEmbedding I) = I := by
  ext n
  simp [valueEmbedding]

private theorem image_value_eq_map {I : Finset ℕ} (S : Finset ↑I) :
    S.image Subtype.val = S.map (valueEmbedding I) := by
  exact (Finset.map_eq_image (valueEmbedding I) S).symm

/-- Changing the subtype support to its ordinary natural-number values
preserves the Bernoulli weight. -/
theorem harmonic_weight_supportValues_eq_subtype_weight {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    HarmonicProb.weight I (supportValues q) =
      Erdos697.Bernoulli.weight (Finset.univ : Finset ↑I)
        (fun i ↦ 1 / (i.1 : ℝ)) (profileSupport q) := by
  unfold HarmonicProb.weight HarmonicProb.param supportValues
  rw [image_value_eq_map]
  unfold Erdos697.Bernoulli.weight
  have hdiff :
      I \ (profileSupport q).map (valueEmbedding I) =
        ((Finset.univ : Finset ↑I) \ profileSupport q).map
          (valueEmbedding I) := by
    rw [Finset.map_sdiff, map_valueEmbedding_univ]
  rw [hdiff]
  simp [Finset.prod_map, valueEmbedding]

/-- Natural-number formulation of the exact profile-mass identity. -/
theorem energyProfileWeight_eq_harmonic_weight_div {I : Finset ℕ}
    (q : ↑I → EnergyState) :
    energyProfileWeight I q =
      HarmonicProb.weight I (supportValues q) /
        (9 : ℝ) ^ (supportValues q).card := by
  rw [harmonic_weight_supportValues_eq_subtype_weight, card_supportValues]
  exact energyProfileWeight_eq_subtype_weight_div q

/-! ## The balanced, non-diagonal profile event -/

/-- Signed value of a ternary state whose coordinates are elements of the
ambient subtype `I`. -/
def subtypeSignedValue {I : Finset ℕ} (S : Finset ↑I)
    (a : ↑S → Fin 3) : ℤ :=
  ∑ i, HarmonicBlocks.signedTerm i.1.1 (a i)

theorem profileSignedDifference_dataToProfile {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) :
    profileSignedDifference I
        (dataToProfile (⟨S, (a, b)⟩ : SupportPairData I)) =
      subtypeSignedValue S a - subtypeSignedValue S b := by
  unfold profileSignedDifference subtypeSignedValue
  calc
    (∑ i : ↑I, localSignedDifference i.1
        (dataToProfile (⟨S, (a, b)⟩ : SupportPairData I) i)) =
        ∑ i : ↑I, if hi : i ∈ S then
          (HarmonicBlocks.signedTerm i.1 (a ⟨i, hi⟩) -
            HarmonicBlocks.signedTerm i.1 (b ⟨i, hi⟩)) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;>
        simp [dataToProfile, hi, localSignedDifference]
    _ = ∑ i : ↑S,
          (HarmonicBlocks.signedTerm i.1.1 (a i) -
            HarmonicBlocks.signedTerm i.1.1 (b i)) := by
      let A : ↑I → Fin 3 := fun i ↦ if hi : i ∈ S then a ⟨i, hi⟩ else 0
      let B : ↑I → Fin 3 := fun i ↦ if hi : i ∈ S then b ⟨i, hi⟩ else 0
      calc
        (∑ i : ↑I, if hi : i ∈ S then
            (HarmonicBlocks.signedTerm i.1 (a ⟨i, hi⟩) -
              HarmonicBlocks.signedTerm i.1 (b ⟨i, hi⟩)) else 0) =
            ∑ i : ↑I, if i ∈ S then
              (HarmonicBlocks.signedTerm i.1 (A i) -
                HarmonicBlocks.signedTerm i.1 (B i)) else 0 := by
          apply Fintype.sum_congr
          intro i
          by_cases hi : i ∈ S <;> simp [A, B, hi]
        _ = ∑ i ∈ S, (HarmonicBlocks.signedTerm i.1 (A i) -
                HarmonicBlocks.signedTerm i.1 (B i)) := by
          rw [Fintype.sum_ite_mem]
        _ = ∑ i : ↑S,
            (HarmonicBlocks.signedTerm i.1.1 (a i) -
              HarmonicBlocks.signedTerm i.1.1 (b i)) := by
          rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl)]
          apply Fintype.sum_congr
          intro i
          simp [A, B]
    _ = (∑ i : ↑S, HarmonicBlocks.signedTerm i.1.1 (a i)) -
          ∑ i : ↑S, HarmonicBlocks.signedTerm i.1.1 (b i) := by
      rw [Finset.sum_sub_distrib]

@[simp] theorem supportValues_dataToProfile {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) :
    supportValues (dataToProfile (⟨S, (a, b)⟩ : SupportPairData I)) =
      S.image Subtype.val := by
  unfold supportValues
  rw [profileSupport_dataToProfile]

theorem profileNonDiagonal_dataToProfile_iff {I : Finset ℕ}
    (S : Finset ↑I) (a b : ↑S → Fin 3) :
    ProfileNonDiagonal
        (dataToProfile (⟨S, (a, b)⟩ : SupportPairData I)) ↔ a ≠ b := by
  constructor
  · intro hQ hab
    obtain ⟨i, hi⟩ := hQ
    obtain ⟨xy, hxy, hne⟩ :=
      (Finset.mem_filter.mp hi).2
    by_cases hiS : i ∈ S
    · have hstate := dataToProfile_apply_mem S a b i hiS
      rw [hstate] at hxy
      have hp : (a ⟨i, hiS⟩, b ⟨i, hiS⟩) = xy :=
        Option.some.inj hxy
      rw [← hp] at hne
      exact hne (congrFun hab ⟨i, hiS⟩)
    · rw [dataToProfile_apply_not_mem S a b i hiS] at hxy
      simp at hxy
  · intro hab
    rw [Function.ne_iff] at hab
    obtain ⟨i, hi⟩ := hab
    refine ⟨i.1, ?_⟩
    rw [profileUnequalCoordinates, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (a i, b i),
      dataToProfile_apply_mem S a b i.1 i.2, hi⟩

@[simp] theorem supportValues_dataToProfile_pair {I : Finset ℕ}
    (S : Finset ↑I) (ab : (↑S → Fin 3) × (↑S → Fin 3)) :
    supportValues (dataToProfile (⟨S, ab⟩ : SupportPairData I)) =
      S.image Subtype.val := by
  rcases ab with ⟨a, b⟩
  exact supportValues_dataToProfile S a b

@[simp] theorem profileSignedDifference_dataToProfile_pair {I : Finset ℕ}
    (S : Finset ↑I) (ab : (↑S → Fin 3) × (↑S → Fin 3)) :
    profileSignedDifference I
        (dataToProfile (⟨S, ab⟩ : SupportPairData I)) =
      subtypeSignedValue S ab.1 - subtypeSignedValue S ab.2 := by
  rcases ab with ⟨a, b⟩
  exact profileSignedDifference_dataToProfile S a b

@[simp] theorem profileNonDiagonal_dataToProfile_pair_iff {I : Finset ℕ}
    (S : Finset ↑I) (ab : (↑S → Fin 3) × (↑S → Fin 3)) :
    ProfileNonDiagonal
        (dataToProfile (⟨S, ab⟩ : SupportPairData I)) ↔ ab.1 ≠ ab.2 := by
  rcases ab with ⟨a, b⟩
  exact profileNonDiagonal_dataToProfile_iff S a b

@[simp] theorem energyProfileWeight_dataToProfile_pair {I : Finset ℕ}
    (S : Finset ↑I) (ab : (↑S → Fin 3) × (↑S → Fin 3)) :
    energyProfileWeight I (dataToProfile (⟨S, ab⟩ : SupportPairData I)) =
      HarmonicProb.weight I (S.image Subtype.val) /
        (9 : ℝ) ^ (S.image Subtype.val).card := by
  rw [energyProfileWeight_eq_harmonic_weight_div,
    supportValues_dataToProfile_pair]

/-- The values map is an equivalence from a subtype support to its natural
number image. -/
def supportValueEquiv {I : Finset ℕ} (S : Finset ↑I) :
    ↑S ≃ ↑(S.image Subtype.val) :=
  Equiv.ofBijective
    (fun i ↦ ⟨i.1.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)
    ⟨fun i j hij ↦ by
        have hn : i.1.1 = j.1.1 :=
          congrArg (fun x : ↑(S.image Subtype.val) ↦ x.1) hij
        exact Subtype.ext (Subtype.ext hn),
      fun n ↦ by
        obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp n.2
        refine ⟨⟨i, hi⟩, ?_⟩
        exact Subtype.ext hin⟩

@[simp] theorem supportValueEquiv_apply_val {I : Finset ℕ}
    (S : Finset ↑I) (i : ↑S) :
    (supportValueEquiv S i).1 = i.1.1 := rfl

/-- Relabelling a subtype-supported ternary state by its natural values
preserves its signed sum. -/
theorem signedValue_comp_supportValueEquiv_symm {I : Finset ℕ}
    (S : Finset ↑I) (a : ↑S → Fin 3) :
    HarmonicBlocks.signedValue (S.image Subtype.val)
        (fun i ↦ a ((supportValueEquiv S).symm i)) =
      subtypeSignedValue S a := by
  unfold HarmonicBlocks.signedValue subtypeSignedValue
  rw [← (supportValueEquiv S).sum_comp]
  simp

/-- Ordered, distinct, balanced ternary pairs on a natural-number support. -/
def balancedPairs (S : Finset ℕ) :
    Finset ((↑S → Fin 3) × (↑S → Fin 3)) :=
  Finset.univ.filter fun ab ↦
    ab.1 ≠ ab.2 ∧
      HarmonicBlocks.signedValue S ab.1 = HarmonicBlocks.signedValue S ab.2

private def balancedPairToWitness {S : Finset ℕ}
    (ab : ↑(balancedPairs S)) : ↑(HarmonicDecomposition.orderedCollisionWitnesses S) := by
  let z := HarmonicBlocks.signedValue S ab.1.1
  have hab := (Finset.mem_filter.mp ab.2).2
  have hleft : ab.1.1 ∈ (HarmonicBlocks.signedStates S).filter
      (fun a ↦ HarmonicBlocks.signedValue S a = z) := by
    exact Finset.mem_filter.mpr ⟨by simp [HarmonicBlocks.signedStates], rfl⟩
  have hright : ab.1.2 ∈ (HarmonicBlocks.signedStates S).filter
      (fun a ↦ HarmonicBlocks.signedValue S a = z) := by
    exact Finset.mem_filter.mpr
      ⟨by simp [HarmonicBlocks.signedStates], hab.2.symm⟩
  let w : Σ z : ℤ,
      {q // q ∈ ((HarmonicBlocks.signedStates S).filter fun a ↦
        HarmonicBlocks.signedValue S a = z).offDiag} :=
    ⟨z, ⟨ab.1, Finset.mem_offDiag.mpr ⟨hleft, hright, hab.1⟩⟩⟩
  refine ⟨w, ?_⟩
  rw [HarmonicDecomposition.orderedCollisionWitnesses, Finset.mem_sigma]
  exact ⟨Finset.mem_image.mpr
    ⟨ab.1.1, by simp [HarmonicBlocks.signedStates], rfl⟩,
      Finset.mem_attach _ w.2⟩

private def witnessToBalancedPair {S : Finset ℕ}
    (w : ↑(HarmonicDecomposition.orderedCollisionWitnesses S)) :
    ↑(balancedPairs S) :=
  ⟨(HarmonicDecomposition.collisionWitnessLeft w.1,
      HarmonicDecomposition.collisionWitnessRight w.1),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      HarmonicDecomposition.collisionWitnessLeft_ne_right w.1,
      HarmonicDecomposition.collisionWitness_signedValue_eq w.1⟩⟩

private def balancedPairWitnessEquiv (S : Finset ℕ) :
    ↑(balancedPairs S) ≃
      ↑(HarmonicDecomposition.orderedCollisionWitnesses S) where
  toFun := balancedPairToWitness
  invFun := witnessToBalancedPair
  left_inv := by
    intro ab
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    apply Sigma.ext
    · have hw := w.1.2.2
      have hleft := Finset.mem_filter.mp (Finset.mem_offDiag.mp hw).1
      exact hleft.2
    · have hw := w.1.2.2
      have hleft := Finset.mem_filter.mp (Finset.mem_offDiag.mp hw).1
      have hz : (balancedPairToWitness (witnessToBalancedPair w)).1.1 = w.1.1 :=
        hleft.2
      apply (Subtype.heq_iff_coe_eq (fun q ↦ by rw [hz])).2
      rfl

@[simp] theorem balancedPairs_card (S : Finset ℕ) :
    (balancedPairs S).card = HarmonicOctaves.offDiagonalSignedEnergy S := by
  rw [← HarmonicDecomposition.orderedCollisionWitnesses_card S]
  simpa using Fintype.card_congr (balancedPairWitnessEquiv S)

/-- Ordered balanced pairs on a support of elements of the ambient subtype. -/
def subtypeBalancedPairs {I : Finset ℕ} (S : Finset ↑I) :
    Finset ((↑S → Fin 3) × (↑S → Fin 3)) :=
  Finset.univ.filter fun ab ↦
    ab.1 ≠ ab.2 ∧ subtypeSignedValue S ab.1 = subtypeSignedValue S ab.2

/-- Relabel a ternary function along `supportValueEquiv`. -/
def supportLabelEquiv {I : Finset ℕ} (S : Finset ↑I) :
    (↑S → Fin 3) ≃ (↑(S.image Subtype.val) → Fin 3) :=
  Equiv.arrowCongr (supportValueEquiv S) (Equiv.refl (Fin 3))

@[simp] theorem supportLabelEquiv_apply {I : Finset ℕ}
    (S : Finset ↑I) (a : ↑S → Fin 3) (i : ↑(S.image Subtype.val)) :
    supportLabelEquiv S a i = a ((supportValueEquiv S).symm i) := by
  rfl

@[simp] theorem signedValue_supportLabelEquiv {I : Finset ℕ}
    (S : Finset ↑I) (a : ↑S → Fin 3) :
    HarmonicBlocks.signedValue (S.image Subtype.val) (supportLabelEquiv S a) =
      subtypeSignedValue S a := by
  exact signedValue_comp_supportValueEquiv_symm S a

private def subtypeBalancedPairEquiv {I : Finset ℕ} (S : Finset ↑I) :
    ↑(subtypeBalancedPairs S) ≃ ↑(balancedPairs (S.image Subtype.val)) :=
  let e := Equiv.prodCongr (supportLabelEquiv S) (supportLabelEquiv S)
  e.subtypeEquiv fun ab ↦ by
    simp only [subtypeBalancedPairs, balancedPairs, Finset.mem_filter,
      Finset.mem_univ, true_and, e, Equiv.prodCongr_apply]
    change (ab.1 ≠ ab.2 ∧ subtypeSignedValue S ab.1 = subtypeSignedValue S ab.2) ↔
      (supportLabelEquiv S ab.1 ≠ supportLabelEquiv S ab.2 ∧
        HarmonicBlocks.signedValue (S.image Subtype.val) (supportLabelEquiv S ab.1) =
          HarmonicBlocks.signedValue (S.image Subtype.val) (supportLabelEquiv S ab.2))
    simp only [signedValue_supportLabelEquiv]
    exact and_congr ((supportLabelEquiv S).injective.eq_iff.not.symm) Iff.rfl

@[simp] theorem subtypeBalancedPairs_card {I : Finset ℕ} (S : Finset ↑I) :
    (subtypeBalancedPairs S).card =
      HarmonicOctaves.offDiagonalSignedEnergy (S.image Subtype.val) := by
  rw [← balancedPairs_card]
  simpa using Fintype.card_congr (subtypeBalancedPairEquiv S)

private theorem sum_profileEvent_dataToProfile
    (I : Finset ℕ) (Good : Finset ℕ → Prop) [DecidablePred Good]
    (S : Finset ↑I) :
    (∑ ab : (↑S → Fin 3) × (↑S → Fin 3),
      if Good (supportValues (dataToProfile
          (⟨S, ab⟩ : SupportPairData I))) ∧
          profileSignedDifference I (dataToProfile
            (⟨S, ab⟩ : SupportPairData I)) = 0 ∧
          ProfileNonDiagonal (dataToProfile
            (⟨S, ab⟩ : SupportPairData I)) then
        energyProfileWeight I (dataToProfile
          (⟨S, ab⟩ : SupportPairData I)) else 0) =
      if Good (S.image Subtype.val) then
        HarmonicProb.weight I (S.image Subtype.val) *
          (HarmonicOctaves.offDiagonalSignedEnergy
            (S.image Subtype.val) : ℝ) /
            (9 : ℝ) ^ (S.image Subtype.val).card
      else 0 := by
  by_cases hGood : Good (S.image Subtype.val)
  · rw [if_pos hGood]
    let c := HarmonicProb.weight I (S.image Subtype.val) /
      (9 : ℝ) ^ (S.image Subtype.val).card
    have hpoint : ∀ ab : (↑S → Fin 3) × (↑S → Fin 3),
        (if Good (supportValues (dataToProfile
            (⟨S, ab⟩ : SupportPairData I))) ∧
            profileSignedDifference I (dataToProfile
              (⟨S, ab⟩ : SupportPairData I)) = 0 ∧
            ProfileNonDiagonal (dataToProfile
              (⟨S, ab⟩ : SupportPairData I)) then
          energyProfileWeight I (dataToProfile
            (⟨S, ab⟩ : SupportPairData I)) else 0) =
          if subtypeSignedValue S ab.1 - subtypeSignedValue S ab.2 = 0 ∧
            ab.1 ≠ ab.2 then c else 0 := by
      intro ab
      rw [supportValues_dataToProfile_pair,
        profileSignedDifference_dataToProfile_pair,
        profileNonDiagonal_dataToProfile_pair_iff,
        energyProfileWeight_dataToProfile_pair]
      simp only [hGood, true_and]
      rfl
    calc
      (∑ ab : (↑S → Fin 3) × (↑S → Fin 3),
        if Good (supportValues (dataToProfile
            (⟨S, ab⟩ : SupportPairData I))) ∧
            profileSignedDifference I (dataToProfile
              (⟨S, ab⟩ : SupportPairData I)) = 0 ∧
            ProfileNonDiagonal (dataToProfile
              (⟨S, ab⟩ : SupportPairData I)) then
          energyProfileWeight I (dataToProfile
            (⟨S, ab⟩ : SupportPairData I)) else 0) =
          ∑ ab : (↑S → Fin 3) × (↑S → Fin 3), if
            subtypeSignedValue S ab.1 - subtypeSignedValue S ab.2 = 0 ∧
              ab.1 ≠ ab.2 then c else 0 := by
        apply Fintype.sum_congr
        exact hpoint
      _ = ∑ ab ∈ subtypeBalancedPairs S, c := by
        change (∑ ab ∈ (Finset.univ : Finset
          ((↑S → Fin 3) × (↑S → Fin 3))), if
            subtypeSignedValue S ab.1 - subtypeSignedValue S ab.2 = 0 ∧
              ab.1 ≠ ab.2 then c else 0) = _
        rw [← Finset.sum_filter]
        congr 1
        ext ab
        simp [subtypeBalancedPairs, sub_eq_zero, and_comm]
      _ = (subtypeBalancedPairs S).card * c := by simp
      _ = HarmonicProb.weight I (S.image Subtype.val) *
          (HarmonicOctaves.offDiagonalSignedEnergy
            (S.image Subtype.val) : ℝ) /
            (9 : ℝ) ^ (S.image Subtype.val).card := by
        rw [subtypeBalancedPairs_card]
        dsimp [c]
        push_cast
        ring
  · rw [if_neg hGood]
    apply Finset.sum_eq_zero
    intro ab _
    rw [supportValues_dataToProfile_pair]
    rw [if_neg]
    intro h
    exact hGood h.1

/-- The harmonic normalized off-diagonal energy is exactly the mass of the
balanced non-diagonal event in the ambient ten-state product model. -/
theorem normalizedOffDiagonalExpectation_eq_profile_sum
    (I : Finset ℕ) (Good : Finset ℕ → Prop) :
    HarmonicOctaves.normalizedOffDiagonalExpectation I Good =
      ∑ q : ↑I → EnergyState,
        if Good (supportValues q) ∧ profileSignedDifference I q = 0 ∧
            ProfileNonDiagonal q then
          energyProfileWeight I q else 0 := by
  let F : (↑I → EnergyState) → ℝ := fun q ↦
    if Good (supportValues q) ∧ profileSignedDifference I q = 0 ∧
        ProfileNonDiagonal q then
      energyProfileWeight I q else 0
  have hprofiles :
      (∑ q : ↑I → EnergyState, F q) =
        ∑ S : Finset ↑I,
          if Good (S.image Subtype.val) then
            HarmonicProb.weight I (S.image Subtype.val) *
                (HarmonicOctaves.offDiagonalSignedEnergy
                  (S.image Subtype.val) : ℝ) /
              (9 : ℝ) ^ (S.image Subtype.val).card
          else 0 := by
    calc
      (∑ q : ↑I → EnergyState, F q) =
          ∑ d : SupportPairData I, F ((profileEquiv I).symm d) :=
        (Equiv.sum_comp (profileEquiv I).symm F).symm
      _ = ∑ S : Finset ↑I,
          ∑ ab : (↑S → Fin 3) × (↑S → Fin 3),
            F (dataToProfile (⟨S, ab⟩ : SupportPairData I)) := by
        rw [Fintype.sum_sigma]
        rfl
      _ = ∑ S : Finset ↑I,
          if Good (S.image Subtype.val) then
            HarmonicProb.weight I (S.image Subtype.val) *
                (HarmonicOctaves.offDiagonalSignedEnergy
                  (S.image Subtype.val) : ℝ) /
              (9 : ℝ) ^ (S.image Subtype.val).card
          else 0 := by
        apply Fintype.sum_congr
        intro S
        exact sum_profileEvent_dataToProfile I Good S
  have hsupports :
      (∑ S : Finset ↑I,
          if Good (S.image Subtype.val) then
            HarmonicProb.weight I (S.image Subtype.val) *
                (HarmonicOctaves.offDiagonalSignedEnergy
                  (S.image Subtype.val) : ℝ) /
              (9 : ℝ) ^ (S.image Subtype.val).card
          else 0) =
        ∑ S ∈ I.powerset,
          if Good S then
            HarmonicProb.weight I S *
                (HarmonicOctaves.offDiagonalSignedEnergy S : ℝ) /
              (9 : ℝ) ^ S.card
          else 0 := by
    change (∑ S ∈ (Finset.univ : Finset (Finset ↑I)),
        if Good (S.image Subtype.val) then
          HarmonicProb.weight I (S.image Subtype.val) *
              (HarmonicOctaves.offDiagonalSignedEnergy
                (S.image Subtype.val) : ℝ) /
            (9 : ℝ) ^ (S.image Subtype.val).card
        else 0) = _
    refine Finset.sum_bij (fun S _ ↦ S.image Subtype.val) ?_ ?_ ?_ ?_
    · intro S _
      rw [Finset.mem_powerset]
      intro n hn
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
      exact i.property
    · intro S₁ _ S₂ _ hEq
      exact Finset.image_injective Subtype.val_injective hEq
    · intro U hU
      rw [Finset.mem_powerset] at hU
      let S := HarmonicSubtype.lift I U
      have hmap : S.image Subtype.val = U := by
        rw [HarmonicSubtype.image_value_eq_map]
        exact HarmonicSubtype.map_lift hU
      exact ⟨S, Finset.mem_univ _, hmap⟩
    · intro S _
      rfl
  unfold HarmonicOctaves.normalizedOffDiagonalExpectation
  rw [Finset.sum_filter]
  have hparam : HarmonicProb.param = fun i : ℕ ↦ 1 / (i : ℝ) := by
    funext i
    rfl
  simpa only [HarmonicProb.weight, hparam, F] using
    hsupports.symm.trans hprofiles.symm

end

end Erdos144.HarmonicStateEquiv
