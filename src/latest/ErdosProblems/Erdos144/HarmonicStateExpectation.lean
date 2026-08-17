/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicDecomposition

/-!
# The ten-state product model for normalized harmonic energy

The normalized expectation of the ordered ternary collision energy can be
viewed as a product measure with ten local states.  The state `none` means
that an integer was not selected.  A state `some (x,y)` means that it was
selected and records its values in two ordered ternary assignments.  Its
weight is the harmonic inclusion probability divided among the nine ordered
state pairs.

This file proves the exact finite normalization and marginal identities for
that model.  These are the probability-theoretic input to the
largest-differing-coordinate reindexing.
-/

open scoped BigOperators

namespace Erdos144.HarmonicStateExpectation

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The ten local states used for a pair of normalized ternary assignments. -/
abbrev EnergyState := Option (Fin 3 × Fin 3)

/-- Local mass in the normalized harmonic pair-state model. -/
def localEnergyWeight (i : ℕ) : EnergyState → ℝ
  | none => 1 - 1 / (i : ℝ)
  | some _ => 1 / (9 * (i : ℝ))

/-- Product mass of one ambient pair-state profile. -/
def energyProfileWeight (I : Finset ℕ) (q : ↑I → EnergyState) : ℝ :=
  ∏ i, localEnergyWeight i.1 (q i)

/-- A profile selects a coordinate exactly when its local state is `some`. -/
def Selects {I : Finset ℕ} (q : ↑I → EnergyState) (i : ↑I) : Prop :=
  q i ≠ none

lemma sum_localEnergyWeight (i : ℕ) :
    (∑ e : EnergyState, localEnergyWeight i e) = 1 := by
  rw [Fintype.sum_option]
  simp only [localEnergyWeight]
  norm_num [Fintype.sum_prod_type]
  ring

lemma localEnergyWeight_nonneg {i : ℕ} (hi : 1 ≤ i) (e : EnergyState) :
    0 ≤ localEnergyWeight i e := by
  cases e with
  | none =>
      simp only [localEnergyWeight]
      have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
      exact sub_nonneg.mpr ((div_le_one (by positivity)).2 hiR)
  | some q =>
      simp only [localEnergyWeight]
      positivity

lemma energyProfileWeight_nonneg {I : Finset ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i) (q : ↑I → EnergyState) :
    0 ≤ energyProfileWeight I q := by
  exact Finset.prod_nonneg fun i _ ↦
    localEnergyWeight_nonneg (hI i.1 i.2) (q i)

/-- The ten-state masses form a probability distribution. -/
theorem sum_energyProfileWeight_eq_one (I : Finset ℕ) :
    (∑ q : ↑I → EnergyState, energyProfileWeight I q) = 1 := by
  change (∑ q : ↑I → EnergyState,
    ∏ i, localEnergyWeight i.1 (q i)) = 1
  rw [← Fintype.prod_sum]
  simp only [sum_localEnergyWeight, Finset.prod_const_one]

/-- The total local mass of the nine selected states is `1/i`. -/
lemma sum_localEnergyWeight_some (i : ℕ) :
    (∑ q : Fin 3 × Fin 3, localEnergyWeight i (some q)) = 1 / (i : ℝ) := by
  simp only [localEnergyWeight]
  norm_num [Fintype.sum_prod_type]
  ring

/-- The total local mass of the three selected diagonal states is `1/(3i)`. -/
lemma sum_localEnergyWeight_diagonal (i : ℕ) :
    (∑ x : Fin 3, localEnergyWeight i (some (x, x))) =
      1 / (3 * (i : ℝ)) := by
  simp only [localEnergyWeight]
  norm_num
  ring

/-- The total local mass of the six selected unequal states is `2/(3i)`. -/
lemma sum_localEnergyWeight_unequal (i : ℕ) :
    (∑ q : Fin 3 × Fin 3,
      if q.1 ≠ q.2 then localEnergyWeight i (some q) else 0) =
      2 / (3 * (i : ℝ)) := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, localEnergyWeight]
  ring

/-- Modify one coordinate so that unselected states have mass zero. -/
def selectedLocalWeight {I : Finset ℕ} (m : ↑I)
    (i : ↑I) (e : EnergyState) : ℝ :=
  if i = m then
    match e with
    | none => 0
    | some _ => localEnergyWeight i.1 e
  else localEnergyWeight i.1 e

lemma sum_selectedLocalWeight {I : Finset ℕ} (m i : ↑I) :
    (∑ e : EnergyState, selectedLocalWeight m i e) =
      if i = m then 1 / (m.1 : ℝ) else 1 := by
  by_cases him : i = m
  · subst i
    simp only [selectedLocalWeight, if_pos]
    rw [Fintype.sum_option]
    simp only
    simpa using sum_localEnergyWeight_some m.1
  · simpa [selectedLocalWeight, him] using sum_localEnergyWeight i.1

lemma indicator_selects_mul_profileWeight_eq
    {I : Finset ℕ} (m : ↑I) (q : ↑I → EnergyState) :
    (if Selects q m then energyProfileWeight I q else 0) =
      ∏ i, selectedLocalWeight m i (q i) := by
  classical
  rw [energyProfileWeight]
  by_cases hqm : q m = none
  · have hnot : ¬ Selects q m := by simpa [Selects] using hqm
    rw [if_neg hnot]
    have hzero : selectedLocalWeight m m (q m) = 0 := by
      simp [selectedLocalWeight, hqm]
    exact (Finset.prod_eq_zero (Finset.mem_univ m) hzero).symm
  · have hsel : Selects q m := hqm
    rw [if_pos hsel]
    apply Finset.prod_congr rfl
    intro i _
    by_cases him : i = m
    · subst i
      cases hstate : q m with
      | none => exact False.elim (hqm hstate)
      | some x => simp [selectedLocalWeight]
    · simp [selectedLocalWeight, him]

/-- Selecting one prescribed coordinate has exactly harmonic mass `1/m` in
the normalized pair-state product model. -/
theorem sum_energyProfileWeight_selects_eq
    {I : Finset ℕ} (m : ↑I) :
    (∑ q : ↑I → EnergyState,
      if Selects q m then energyProfileWeight I q else 0) =
      1 / (m.1 : ℝ) := by
  simp_rw [indicator_selects_mul_profileWeight_eq m]
  rw [← Fintype.prod_sum]
  simp_rw [sum_selectedLocalWeight]
  simp

/-! ## Full-ambient hole templates -/

open HarmonicBlocks HarmonicOctaves

/-- Signed contribution of one ambient pair state. -/
def localSignedDifference (i : ℕ) : EnergyState → ℤ
  | none => 0
  | some q => signedTerm i q.1 - signedTerm i q.2

/-- Total signed difference of an ambient profile. -/
def profileSignedDifference (I : Finset ℕ)
    (q : ↑I → EnergyState) : ℤ :=
  ∑ i, localSignedDifference i.1 (q i)

/-- Fill one distinguished hole with a selected ordered pair state. -/
def fillHole {I : Finset ℕ} (q : ↑I → EnergyState)
    (n : ↑I) (xy : Fin 3 × Fin 3) : ↑I → EnergyState :=
  Function.update q n (some xy)

@[simp] theorem fillHole_apply_self {I : Finset ℕ}
    (q : ↑I → EnergyState) (n : ↑I) (xy : Fin 3 × Fin 3) :
    fillHole q n xy n = some xy := by
  simp [fillHole]

@[simp] theorem fillHole_apply_ne {I : Finset ℕ}
    (q : ↑I → EnergyState) {n i : ↑I} (h : i ≠ n)
    (xy : Fin 3 × Fin 3) :
    fillHole q n xy i = q i := by
  simp [fillHole, h]

/-- Candidate forced coordinates for a fixed ambient hole template and a
fixed unequal local pair. -/
def forcedProfileCoordinates {I : Finset ℕ} (M : ↑I)
    (q : ↑I → EnergyState) (xy : Fin 3 × Fin 3) : Finset ↑I :=
  Finset.univ.filter fun n ↦
    M < n ∧ q n = none ∧
      signedTerm n.1 xy.1 - signedTerm n.1 xy.2 =
        -profileSignedDifference I q

theorem forcedProfileCoordinates_card_le_one
    {I : Finset ℕ} (M : ↑I) (q : ↑I → EnergyState)
    {xy : Fin 3 × Fin 3} (hxy : xy.1 ≠ xy.2) :
    (forcedProfileCoordinates M q xy).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro n hn m hm
  have hnEq := (Finset.mem_filter.mp hn).2.2.2
  have hmEq := (Finset.mem_filter.mp hm).2.2.2
  apply Subtype.ext
  exact signedTerm_difference_injective hxy (hnEq.trans hmEq.symm)

theorem mem_forcedProfileCoordinates
    {I : Finset ℕ} {M n : ↑I} {q : ↑I → EnergyState}
    {xy : Fin 3 × Fin 3}
    (hn : n ∈ forcedProfileCoordinates M q xy) :
    M < n ∧ q n = none ∧
      signedTerm n.1 xy.1 - signedTerm n.1 xy.2 =
        -profileSignedDifference I q :=
  (Finset.mem_filter.mp hn).2

/-- Filling a hole balances the profile precisely when the forced-coordinate
equation holds. -/
theorem profileSignedDifference_fillHole_eq_zero
    {I : Finset ℕ} {M n : ↑I} {q : ↑I → EnergyState}
    {xy : Fin 3 × Fin 3}
    (hn : n ∈ forcedProfileCoordinates M q xy) :
    profileSignedDifference I (fillHole q n xy) = 0 := by
  have hnData := mem_forcedProfileCoordinates hn
  unfold profileSignedDifference
  unfold profileSignedDifference at hnData
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n)] at hnData
  have herase :
      (∑ i ∈ (Finset.univ : Finset ↑I).erase n,
          localSignedDifference i.1 (fillHole q n xy i)) =
        ∑ i ∈ (Finset.univ : Finset ↑I).erase n,
          localSignedDifference i.1 (q i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [fillHole_apply_ne q (Finset.ne_of_mem_erase hi)]
  rw [herase]
  simp only [fillHole_apply_self, localSignedDifference]
  have hqn : localSignedDifference n.1 (q n) = 0 := by
    rw [hnData.2.1]
    rfl
  rw [hqn, add_zero] at hnData
  calc
    (∑ i ∈ (Finset.univ : Finset ↑I).erase n,
        localSignedDifference i.1 (q i)) +
          (signedTerm n.1 xy.1 - signedTerm n.1 xy.2) =
        (∑ i ∈ (Finset.univ : Finset ↑I).erase n,
          localSignedDifference i.1 (q i)) +
          -(∑ i ∈ (Finset.univ : Finset ↑I).erase n,
            localSignedDifference i.1 (q i)) :=
      congrArg (fun z ↦
        (∑ i ∈ (Finset.univ : Finset ↑I).erase n,
          localSignedDifference i.1 (q i)) + z) hnData.2.2
    _ = 0 := add_neg_cancel _

/-- Exact normalized-weight ratio between a filled profile and its ambient
hole template. -/
theorem energyProfileWeight_fillHole_eq
    {I : Finset ℕ} {q : ↑I → EnergyState} {n : ↑I}
    (hqn : q n = none) (hn : 1 < n.1) (xy : Fin 3 × Fin 3) :
    energyProfileWeight I (fillHole q n xy) =
      (1 / (9 * ((n.1 : ℝ) - 1))) * energyProfileWeight I q := by
  unfold energyProfileWeight
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset ↑I))
      (f := fun i ↦ localEnergyWeight i.1 (fillHole q n xy i))
      (Finset.mem_univ n)]
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset ↑I))
      (f := fun i ↦ localEnergyWeight i.1 (q i))
      (Finset.mem_univ n)]
  have hprod :
      (∏ i ∈ (Finset.univ : Finset ↑I).erase n,
          localEnergyWeight i.1 (fillHole q n xy i)) =
        ∏ i ∈ (Finset.univ : Finset ↑I).erase n,
          localEnergyWeight i.1 (q i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [fillHole_apply_ne q (Finset.ne_of_mem_erase hi)]
  rw [hprod]
  simp only [fillHole_apply_self, localEnergyWeight, hqn]
  have hnR : (1 : ℝ) < n.1 := by exact_mod_cast hn
  have hn0 : (n.1 : ℝ) ≠ 0 := by positivity
  have hn1 : (n.1 : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn0, hn1]

/-- The filled-profile mass at a forced coordinate above `M` is at most
`1/(9M)` times the mass of its hole template. -/
theorem energyProfileWeight_fillHole_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {M n : ↑I} {q : ↑I → EnergyState} {xy : Fin 3 × Fin 3}
    (hn : n ∈ forcedProfileCoordinates M q xy) :
    energyProfileWeight I (fillHole q n xy) ≤
      (1 / (9 * (M.1 : ℝ))) * energyProfileWeight I q := by
  have hnData := mem_forcedProfileCoordinates hn
  have hMpos : 0 < M.1 := Nat.zero_lt_of_lt (hI M.1 M.2)
  have hnPos : 1 < n.1 := lt_of_le_of_lt (hI M.1 M.2) hnData.1
  rw [energyProfileWeight_fillHole_eq hnData.2.1 hnPos xy]
  have hpred : (M.1 : ℝ) ≤ (n.1 : ℝ) - 1 := by
    have hltNat : M.1 < n.1 := hnData.1
    have hcast : (M.1 : ℝ) + 1 ≤ n.1 := by
      exact_mod_cast (Nat.succ_le_iff.mpr hltNat)
    linarith
  have hfactor :
      1 / (9 * ((n.1 : ℝ) - 1)) ≤ 1 / (9 * (M.1 : ℝ)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  exact mul_le_mul_of_nonneg_right hfactor
    (energyProfileWeight_nonneg hI q)

/-- Mass of all forced fillings of one fixed hole template and one unequal
local pair.  Uniqueness of the forced coordinate removes the inner sum. -/
theorem forcedFill_mass_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    (M : ↑I) (q : ↑I → EnergyState)
    {xy : Fin 3 × Fin 3} (hxy : xy.1 ≠ xy.2) :
    (∑ n ∈ forcedProfileCoordinates M q xy,
        energyProfileWeight I (fillHole q n xy)) ≤
      (1 / (9 * (M.1 : ℝ))) * energyProfileWeight I q := by
  calc
    (∑ n ∈ forcedProfileCoordinates M q xy,
        energyProfileWeight I (fillHole q n xy)) ≤
        ∑ _n ∈ forcedProfileCoordinates M q xy,
          (1 / (9 * (M.1 : ℝ))) * energyProfileWeight I q := by
      gcongr with n hn
      exact energyProfileWeight_fillHole_le hI hn
    _ = ((forcedProfileCoordinates M q xy).card : ℝ) *
        ((1 / (9 * (M.1 : ℝ))) * energyProfileWeight I q) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * ((1 / (9 * (M.1 : ℝ))) *
        energyProfileWeight I q) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast forcedProfileCoordinates_card_le_one M q hxy
      · exact mul_nonneg (by positivity) (energyProfileWeight_nonneg hI q)
    _ = (1 / (9 * (M.1 : ℝ))) * energyProfileWeight I q := one_mul _

/-- Total mass of the full-ambient reconstruction fibre with predecessor
`M`.  It deliberately overcounts: every hole template and every unequal
local pair is retained. -/
def predecessorFibreMass {I : Finset ℕ} (M : ↑I) : ℝ :=
  ∑ q : ↑I → EnergyState,
      if Selects q M then
        ∑ xy ∈ unequalStatePairs,
          ∑ n ∈ forcedProfileCoordinates M q xy,
            energyProfileWeight I (fillHole q n xy)
      else 0

/-- The sharp predecessor-fibre estimate.  The six unequal local pairs cost
`6/9`, while summing hole templates which select `M` costs exactly `1/M`.
Thus the whole forced fibre has mass at most `(2/3)/M²`. -/
theorem predecessorFibre_mass_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (M : ↑I) :
    predecessorFibreMass M ≤
      (2 / 3 : ℝ) * (1 / (M.1 : ℝ) ^ 2) := by
  unfold predecessorFibreMass
  calc
    (∑ q : ↑I → EnergyState,
      if Selects q M then
        ∑ xy ∈ unequalStatePairs,
          ∑ n ∈ forcedProfileCoordinates M q xy,
            energyProfileWeight I (fillHole q n xy)
      else 0) ≤
        ∑ q : ↑I → EnergyState,
          if Selects q M then
            ∑ _xy ∈ unequalStatePairs,
              (1 / (9 * (M.1 : ℝ))) * energyProfileWeight I q
          else 0 := by
      gcongr with q
      by_cases hqM : Selects q M
      · simp only [hqM, if_true]
        gcongr with xy hxy
        exact forcedFill_mass_le hI M q
          (Finset.mem_filter.mp hxy).2
      · simp [hqM]
    _ = ∑ q : ↑I → EnergyState,
          if Selects q M then
            (2 / (3 * (M.1 : ℝ))) * energyProfileWeight I q
          else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hqM : Selects q M
      · simp only [hqM, if_true, Finset.sum_const, nsmul_eq_mul,
          unequalStatePairs_card]
        ring
      · simp [hqM]
    _ = (2 / (3 * (M.1 : ℝ))) *
        (∑ q : ↑I → EnergyState,
          if Selects q M then energyProfileWeight I q else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hqM : Selects q M <;> simp [hqM]
    _ = (2 / (3 * (M.1 : ℝ))) * (1 / (M.1 : ℝ)) := by
      rw [sum_energyProfileWeight_selects_eq]
    _ = (2 / 3 : ℝ) * (1 / (M.1 : ℝ) ^ 2) := by ring

/-- Summed form of the sharp fibre estimate over any proposed family of
predecessors. -/
theorem sum_predecessorFibreMass_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (B : Finset ↑I) :
    (∑ M ∈ B, predecessorFibreMass M) ≤
      (2 / 3 : ℝ) * ∑ M ∈ B, 1 / (M.1 : ℝ) ^ 2 := by
  calc
    (∑ M ∈ B, predecessorFibreMass M) ≤
        ∑ M ∈ B, (2 / 3 : ℝ) * (1 / (M.1 : ℝ) ^ 2) := by
      gcongr with M hM
      exact predecessorFibre_mass_le hI M
    _ = (2 / 3 : ℝ) * ∑ M ∈ B, 1 / (M.1 : ℝ) ^ 2 := by
      rw [Finset.mul_sum]

/-- Once collision mass is covered pointwise by full-ambient predecessor
fibres, no further probability reindexing is needed.  This is the exact
interface left for the collision-to-template cover. -/
theorem normalizedOffDiagonalExpectation_le_of_predecessor_cover
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hI : ∀ i ∈ I, 1 ≤ i) (B : Finset ↑I)
    (hcover : normalizedOffDiagonalExpectation I Good ≤
      ∑ M ∈ B, predecessorFibreMass M) :
    normalizedOffDiagonalExpectation I Good ≤
      (2 / 3 : ℝ) * ∑ M ∈ B, 1 / (M.1 : ℝ) ^ 2 :=
  hcover.trans (sum_predecessorFibreMass_le hI B)

/-- Forgetting subtype proofs embeds any predecessor family into its ambient
natural-number family without changing its reciprocal-square sum. -/
theorem sum_subtype_reciprocalSquare_le
    {I B : Finset ℕ} (P : Finset ↑I)
    (hP : ∀ M ∈ P, M.1 ∈ B) :
    (∑ M ∈ P, 1 / (M.1 : ℝ) ^ 2) ≤
      ∑ M ∈ B, 1 / (M : ℝ) ^ 2 := by
  have hinj : Set.InjOn (fun M : ↑I ↦ M.1) P := by
    intro a _ b _ hab
    exact Subtype.ext hab
  have himage : P.image (fun M : ↑I ↦ M.1) ⊆ B := by
    intro n hn
    obtain ⟨M, hMP, rfl⟩ := Finset.mem_image.mp hn
    exact hP M hMP
  calc
    (∑ M ∈ P, 1 / (M.1 : ℝ) ^ 2) =
        ∑ M ∈ P.image (fun M : ↑I ↦ M.1), 1 / (M : ℝ) ^ 2 := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ M ∈ B, 1 / (M : ℝ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun _ _ _ ↦ by positivity)

/-- A predecessor family contained in one eight-adic octave contributes at
most the corresponding concrete low-octave term. -/
theorem sum_predecessorFibreMass_octave_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {D r : ℕ} (P : Finset ↑I)
    (hP : ∀ M ∈ P, M.1 ∈ HarmonicDecomposition.octave D r) :
    (∑ M ∈ P, predecessorFibreMass M) ≤
      HarmonicDecomposition.lowContribution D r := by
  calc
    (∑ M ∈ P, predecessorFibreMass M) ≤
        (2 / 3 : ℝ) * ∑ M ∈ P, 1 / (M.1 : ℝ) ^ 2 :=
      sum_predecessorFibreMass_le hI P
    _ ≤ (2 / 3 : ℝ) *
        ∑ M ∈ HarmonicDecomposition.octave D r,
          1 / (M : ℝ) ^ 2 := by
      gcongr
      exact sum_subtype_reciprocalSquare_le P hP
    _ = HarmonicDecomposition.lowContribution D r := by
      rfl

/-! ## Pointwise reconstruction cover -/

/-- One ambient profile is recovered from a predecessor, a hole template,
an unequal local pair, and a forced balancing coordinate. -/
def HasPredecessorReconstruction {I : Finset ℕ}
    (Q : ↑I → EnergyState) : Prop :=
  ∃ (M : ↑I) (E : ↑I → EnergyState)
      (xy : Fin 3 × Fin 3) (n : ↑I),
    Selects E M ∧ xy ∈ unequalStatePairs ∧
      n ∈ forcedProfileCoordinates M E xy ∧ Q = fillHole E n xy

/-- Total ten-state mass of profiles for which a predecessor reconstruction
has been supplied. -/
def reconstructedProfileMass (I : Finset ℕ) : ℝ :=
  ∑ Q : ↑I → EnergyState,
    if HasPredecessorReconstruction Q then energyProfileWeight I Q else 0

/-- Equality-indicator expansion of all reconstructions of one profile. -/
def reconstructionMajorant {I : Finset ℕ} (Q : ↑I → EnergyState) : ℝ :=
  ∑ M : ↑I, ∑ E : ↑I → EnergyState,
    if Selects E M then
      ∑ xy ∈ unequalStatePairs,
        ∑ n ∈ forcedProfileCoordinates M E xy,
          if Q = fillHole E n xy then
            energyProfileWeight I (fillHole E n xy) else 0
    else 0

/-- Every reconstructible profile is bounded by its equality-indicator
expansion. -/
theorem reconstructedProfile_le_reconstructionMajorant
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    (Q : ↑I → EnergyState) :
    (if HasPredecessorReconstruction Q then energyProfileWeight I Q else 0) ≤
      reconstructionMajorant Q := by
  by_cases hQ : HasPredecessorReconstruction Q
  · simp only [hQ, if_true]
    rcases hQ with ⟨M, E, xy, n, hEM, hxy, hn, hQeq⟩
    rw [hQeq]
    unfold reconstructionMajorant
    calc
      energyProfileWeight I (fillHole E n xy) ≤
          ∑ n' ∈ forcedProfileCoordinates M E xy,
            if fillHole E n xy = fillHole E n' xy then
              energyProfileWeight I (fillHole E n' xy) else 0 := by
        calc
          energyProfileWeight I (fillHole E n xy) =
              (if fillHole E n xy = fillHole E n xy then
                energyProfileWeight I (fillHole E n xy) else 0) := by simp
          _ ≤ ∑ n' ∈ forcedProfileCoordinates M E xy,
              if fillHole E n xy = fillHole E n' xy then
                energyProfileWeight I (fillHole E n' xy) else 0 := by
            apply Finset.single_le_sum (f := fun n' ↦
              if fillHole E n xy = fillHole E n' xy then
                energyProfileWeight I (fillHole E n' xy) else 0)
            · intro n' _
              by_cases heq : fillHole E n xy = fillHole E n' xy
              · simp [heq, energyProfileWeight_nonneg hI]
              · simp [heq]
            · exact hn
      _ ≤ ∑ xy' ∈ unequalStatePairs,
          ∑ n' ∈ forcedProfileCoordinates M E xy',
            if fillHole E n xy = fillHole E n' xy' then
              energyProfileWeight I (fillHole E n' xy') else 0 := by
        apply Finset.single_le_sum (f := fun xy' ↦
          ∑ n' ∈ forcedProfileCoordinates M E xy',
            if fillHole E n xy = fillHole E n' xy' then
              energyProfileWeight I (fillHole E n' xy') else 0)
        · intro xy' _
          exact Finset.sum_nonneg fun n' _ ↦ by
            by_cases heq : fillHole E n xy = fillHole E n' xy'
            · simp [heq, energyProfileWeight_nonneg hI]
            · simp [heq]
        · exact hxy
      _ = if Selects E M then
          ∑ xy' ∈ unequalStatePairs,
            ∑ n' ∈ forcedProfileCoordinates M E xy',
              if fillHole E n xy = fillHole E n' xy' then
                energyProfileWeight I (fillHole E n' xy') else 0 else 0 := by
        simp [hEM]
      _ ≤ ∑ E' : ↑I → EnergyState,
          if Selects E' M then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M E' xy',
                if fillHole E n xy = fillHole E' n' xy' then
                  energyProfileWeight I (fillHole E' n' xy') else 0 else 0 := by
        apply Finset.single_le_sum (f := fun E' ↦
          if Selects E' M then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M E' xy',
                if fillHole E n xy = fillHole E' n' xy' then
                  energyProfileWeight I (fillHole E' n' xy') else 0 else 0)
        · intro E' _
          by_cases hE'M : Selects E' M
          · simp only [hE'M, if_true]
            exact Finset.sum_nonneg fun xy' _ ↦ Finset.sum_nonneg fun n' _ ↦ by
              by_cases heq : fillHole E n xy = fillHole E' n' xy'
              · simp [heq, energyProfileWeight_nonneg hI]
              · simp [heq]
          · simp [hE'M]
        · exact Finset.mem_univ E
      _ ≤ ∑ M' : ↑I, ∑ E' : ↑I → EnergyState,
          if Selects E' M' then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M' E' xy',
                if fillHole E n xy = fillHole E' n' xy' then
                  energyProfileWeight I (fillHole E' n' xy') else 0 else 0 := by
        apply Finset.single_le_sum (f := fun M' ↦
          ∑ E' : ↑I → EnergyState,
            if Selects E' M' then
              ∑ xy' ∈ unequalStatePairs,
                ∑ n' ∈ forcedProfileCoordinates M' E' xy',
                  if fillHole E n xy = fillHole E' n' xy' then
                    energyProfileWeight I (fillHole E' n' xy') else 0 else 0)
        · intro M' _
          exact Finset.sum_nonneg fun E' _ ↦ by
            by_cases hE'M : Selects E' M'
            · simp only [hE'M, if_true]
              exact Finset.sum_nonneg fun xy' _ ↦ Finset.sum_nonneg fun n' _ ↦ by
                by_cases heq : fillHole E n xy = fillHole E' n' xy'
                · simp [heq, energyProfileWeight_nonneg hI]
                · simp [heq]
            · simp [hE'M]
        · exact Finset.mem_univ M
  · simp only [hQ, if_false]
    unfold reconstructionMajorant
    exact Finset.sum_nonneg fun M _ ↦ Finset.sum_nonneg fun E _ ↦ by
      by_cases hEM : Selects E M
      · simp only [hEM, if_true]
        exact Finset.sum_nonneg fun xy _ ↦ Finset.sum_nonneg fun n _ ↦ by
          by_cases heq : Q = fillHole E n xy
          · simp [heq, energyProfileWeight_nonneg hI]
          · simp [heq]
      · simp [hEM]

/-- Summing equality indicators collapses to the predecessor fibres. -/
theorem sum_reconstructionMajorant_eq (I : Finset ℕ) :
    (∑ Q : ↑I → EnergyState, reconstructionMajorant Q) =
      ∑ M : ↑I, predecessorFibreMass M := by
  unfold reconstructionMajorant predecessorFibreMass
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  by_cases hEM : Selects E M
  · simp only [hEM, if_true]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xy hxy
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp
  · simp [hEM]

/-- Pointwise overcounting avoids any global dependent reindexing. -/
theorem reconstructedProfileMass_le_sum_predecessorFibreMass
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) :
    reconstructedProfileMass I ≤
      ∑ M : ↑I, predecessorFibreMass M := by
  unfold reconstructedProfileMass
  calc
    (∑ Q : ↑I → EnergyState,
      if HasPredecessorReconstruction Q then energyProfileWeight I Q else 0) ≤
        ∑ Q : ↑I → EnergyState, reconstructionMajorant Q := by
      gcongr with Q
      exact reconstructedProfile_le_reconstructionMajorant hI Q
    _ = ∑ M : ↑I, predecessorFibreMass M :=
      sum_reconstructionMajorant_eq I

/-- Combining the pointwise cover with the sharp fibre estimate gives the
unconditional reciprocal-square predecessor bound. -/
theorem reconstructedProfileMass_le_reciprocalSquare
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) :
    reconstructedProfileMass I ≤
      (2 / 3 : ℝ) * ∑ M : ↑I, 1 / (M.1 : ℝ) ^ 2 := by
  exact (reconstructedProfileMass_le_sum_predecessorFibreMass hI).trans
    (by simpa using sum_predecessorFibreMass_le hI (Finset.univ : Finset ↑I))

/-! ## Regularity-restricted predecessor fibres -/

/-- Mass of hole templates satisfying an additional regularity/diagonal
predicate and selecting the predecessor `M`. -/
def restrictedTemplateMass {I : Finset ℕ} (M : ↑I)
    (Regular : (↑I → EnergyState) → Prop) : ℝ :=
  ∑ E : ↑I → EnergyState,
    if Regular E ∧ Selects E M then energyProfileWeight I E else 0

/-- Forced reconstruction mass restricted to the same template predicate. -/
def restrictedPredecessorFibreMass {I : Finset ℕ} (M : ↑I)
    (Regular : (↑I → EnergyState) → Prop) : ℝ :=
  ∑ E : ↑I → EnergyState,
    if Regular E ∧ Selects E M then
      ∑ xy ∈ unequalStatePairs,
        ∑ n ∈ forcedProfileCoordinates M E xy,
          energyProfileWeight I (fillHole E n xy)
    else 0

/-- The forced-coordinate and six-local-state calculation is unchanged by
an arbitrary template restriction.  All high-octave information is thereby
isolated in `restrictedTemplateMass`. -/
theorem restrictedPredecessorFibreMass_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (M : ↑I)
    (Regular : (↑I → EnergyState) → Prop) :
    restrictedPredecessorFibreMass M Regular ≤
      (2 / (3 * (M.1 : ℝ))) * restrictedTemplateMass M Regular := by
  unfold restrictedPredecessorFibreMass restrictedTemplateMass
  calc
    (∑ E : ↑I → EnergyState,
      if Regular E ∧ Selects E M then
        ∑ xy ∈ unequalStatePairs,
          ∑ n ∈ forcedProfileCoordinates M E xy,
            energyProfileWeight I (fillHole E n xy) else 0) ≤
      ∑ E : ↑I → EnergyState,
        if Regular E ∧ Selects E M then
          (2 / (3 * (M.1 : ℝ))) * energyProfileWeight I E else 0 := by
      gcongr with E
      by_cases hE : Regular E ∧ Selects E M
      · simp only [hE]
        calc
          (∑ xy ∈ unequalStatePairs,
              ∑ n ∈ forcedProfileCoordinates M E xy,
                energyProfileWeight I (fillHole E n xy)) ≤
              ∑ _xy ∈ unequalStatePairs,
                (1 / (9 * (M.1 : ℝ))) * energyProfileWeight I E := by
            gcongr with xy hxy
            exact forcedFill_mass_le hI M E (Finset.mem_filter.mp hxy).2
          _ = (2 / (3 * (M.1 : ℝ))) * energyProfileWeight I E := by
            rw [Finset.sum_const, nsmul_eq_mul, unequalStatePairs_card]
            ring
      · simp [hE]
    _ = (2 / (3 * (M.1 : ℝ))) *
        ∑ E : ↑I → EnergyState,
          if Regular E ∧ Selects E M then energyProfileWeight I E else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      by_cases hE : Regular E ∧ Selects E M <;> simp [hE]

/-- Abstract high-octave conclusion.  A fixed-support diagonal enumeration
which bounds the restricted template mass by `3^{-q}/M`, together with the
regularity inequality `2k ≤ q+1`, yields the required `2·9^{-k}/M²`
predecessor contribution. -/
theorem restrictedPredecessorFibreMass_high_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (M : ↑I)
    (Regular : (↑I → EnergyState) → Prop) (q k : ℕ)
    (hq : 2 * k ≤ 1 + q)
    (htemplate : restrictedTemplateMass M Regular ≤
      (1 / (3 : ℝ) ^ q) * (1 / (M.1 : ℝ))) :
    restrictedPredecessorFibreMass M Regular ≤
      2 * (1 / (9 : ℝ) ^ k) * (1 / (M.1 : ℝ) ^ 2) := by
  have hMpos : (0 : ℝ) < M.1 := by
    exact_mod_cast Nat.zero_lt_of_lt (hI M.1 M.2)
  have hfactor : (0 : ℝ) ≤ 2 / (3 * (M.1 : ℝ)) := by positivity
  calc
    restrictedPredecessorFibreMass M Regular ≤
        (2 / (3 * (M.1 : ℝ))) * restrictedTemplateMass M Regular :=
      restrictedPredecessorFibreMass_le hI M Regular
    _ ≤ (2 / (3 * (M.1 : ℝ))) *
        ((1 / (3 : ℝ) ^ q) * (1 / (M.1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left htemplate hfactor
    _ = ((2 / 3 : ℝ) * (1 / (3 : ℝ) ^ q)) *
        (1 / (M.1 : ℝ) ^ 2) := by ring
    _ ≤ (2 * (1 / (9 : ℝ) ^ k)) *
        (1 / (M.1 : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (HarmonicDecomposition.diagonal_factor_le hq) (by positivity)
    _ = 2 * (1 / (9 : ℝ) ^ k) * (1 / (M.1 : ℝ) ^ 2) := by ring

/-! ## Tilted tail generating function -/

/-- A local pair state is either unselected or selected diagonally. -/
def IsDiagonalOrNone : EnergyState → Prop
  | none => True
  | some xy => xy.1 = xy.2

/-- Every selected state in the specified tail is diagonal. -/
def TailDiagonal {I : Finset ℕ} (T : Finset ℕ)
    (E : ↑I → EnergyState) : Prop :=
  ∀ i : ↑I, i.1 ∈ T → IsDiagonalOrNone (E i)

/-- Number of selected ambient coordinates lying in the specified tail. -/
def tailSelectedCard {I : Finset ℕ} (T : Finset ℕ)
    (E : ↑I → EnergyState) : ℕ :=
  ((Finset.univ : Finset ↑I).filter fun i ↦ i.1 ∈ T ∧ Selects E i).card

/-- Multiply selected diagonal tail states by three and kill unequal tail
states.  This is the generating-function tilt which removes the apparent
loss from summing over varying supports. -/
def tailTiltedLocalWeight (T : Finset ℕ) (i : ℕ)
    (e : EnergyState) : ℝ :=
  if i ∈ T then
    match e with
    | none => localEnergyWeight i none
    | some xy => if xy.1 = xy.2 then 3 * localEnergyWeight i (some xy) else 0
  else localEnergyWeight i e

lemma sum_tailTiltedLocalWeight (T : Finset ℕ) (i : ℕ) :
    (∑ e : EnergyState, tailTiltedLocalWeight T i e) = 1 := by
  by_cases hiT : i ∈ T
  · rw [Fintype.sum_option]
    simp only [tailTiltedLocalWeight, hiT, if_true, localEnergyWeight]
    rw [Fintype.sum_prod_type]
    simp
    ring
  · simp only [tailTiltedLocalWeight, hiT, if_false]
    exact sum_localEnergyWeight i

lemma localEnergyWeight_nonneg_all (i : ℕ) (e : EnergyState) :
    0 ≤ localEnergyWeight i e := by
  obtain rfl | hi := i.eq_zero_or_pos
  · cases e <;> simp [localEnergyWeight]
  · exact localEnergyWeight_nonneg hi e

/-- Product of the tilted local weights. -/
def tailTiltedProfileWeight {I : Finset ℕ} (T : Finset ℕ)
    (E : ↑I → EnergyState) : ℝ :=
  ∏ i, tailTiltedLocalWeight T i.1 (E i)

lemma tailTiltedProfileWeight_nonneg
    {I : Finset ℕ} (T : Finset ℕ) (E : ↑I → EnergyState) :
    0 ≤ tailTiltedProfileWeight T E := by
  unfold tailTiltedProfileWeight
  apply Finset.prod_nonneg
  intro i _
  by_cases hiT : i.1 ∈ T
  · cases hEi : E i with
    | none => simpa [tailTiltedLocalWeight, hiT, hEi] using
        localEnergyWeight_nonneg_all i.1 none
    | some xy =>
        by_cases hxy : xy.1 = xy.2
        · simp [tailTiltedLocalWeight, hiT, hxy,
            localEnergyWeight_nonneg_all]
        · simp [tailTiltedLocalWeight, hiT, hxy]
  · simpa [tailTiltedLocalWeight, hiT] using
      localEnergyWeight_nonneg_all i.1 (E i)

/-- On a tail-diagonal profile, tilting multiplies its mass by exactly one
factor three for each selected tail coordinate. -/
theorem tailTiltedProfileWeight_eq
    {I : Finset ℕ} {T : Finset ℕ} {E : ↑I → EnergyState}
    (hdiag : TailDiagonal T E) :
    tailTiltedProfileWeight T E =
      (3 : ℝ) ^ tailSelectedCard T E * energyProfileWeight I E := by
  have hlocal : ∀ i : ↑I,
      tailTiltedLocalWeight T i.1 (E i) =
        (if i.1 ∈ T ∧ Selects E i then 3 else 1) *
          localEnergyWeight i.1 (E i) := by
    intro i
    by_cases hiT : i.1 ∈ T
    · have hiDiag := hdiag i hiT
      cases hEi : E i with
      | none => simp [tailTiltedLocalWeight, hiT, Selects, hEi]
      | some xy =>
          have hxy : xy.1 = xy.2 := by
            simpa [IsDiagonalOrNone, hEi] using hiDiag
          simp [tailTiltedLocalWeight, hiT, Selects, hEi, hxy]
    · simp [tailTiltedLocalWeight, hiT]
  unfold tailTiltedProfileWeight energyProfileWeight
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp [tailSelectedCard]

/-- A non-tail-diagonal profile has zero tilted mass. -/
theorem tailTiltedProfileWeight_eq_zero_of_not_diagonal
    {I : Finset ℕ} {T : Finset ℕ} {E : ↑I → EnergyState}
    (hdiag : ¬ TailDiagonal T E) :
    tailTiltedProfileWeight T E = 0 := by
  simp only [TailDiagonal, not_forall] at hdiag
  rcases hdiag with ⟨i, hiT, hiBad⟩
  cases hEi : E i with
  | none => simp [IsDiagonalOrNone, hEi] at hiBad
  | some xy =>
      have hxy : xy.1 ≠ xy.2 := by
        simpa [IsDiagonalOrNone, hEi] using hiBad
      unfold tailTiltedProfileWeight
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [tailTiltedLocalWeight, hiT, hEi, hxy]

/-- Tail-tilted local weight with selection forced at `M`. -/
def selectedTailTiltedLocalWeight {I : Finset ℕ} (T : Finset ℕ)
    (M i : ↑I) (e : EnergyState) : ℝ :=
  if i = M then
    match e with
    | none => 0
    | some _ => tailTiltedLocalWeight T i.1 e
  else tailTiltedLocalWeight T i.1 e

lemma sum_selectedTailTiltedLocalWeight
    {I : Finset ℕ} {T : Finset ℕ} (M i : ↑I) (hMT : M.1 ∉ T) :
    (∑ e : EnergyState, selectedTailTiltedLocalWeight T M i e) =
      if i = M then 1 / (M.1 : ℝ) else 1 := by
  by_cases hiM : i = M
  · subst i
    rw [Fintype.sum_option]
    simp only [selectedTailTiltedLocalWeight, if_pos]
    simp only [tailTiltedLocalWeight, hMT, if_false]
    simpa using sum_localEnergyWeight_some M.1
  · simp only [selectedTailTiltedLocalWeight, hiM, if_false]
    exact sum_tailTiltedLocalWeight T i.1

lemma indicator_selects_mul_tailTiltedProfileWeight_eq
    {I : Finset ℕ} {T : Finset ℕ} (M : ↑I) (_hMT : M.1 ∉ T)
    (E : ↑I → EnergyState) :
    (if Selects E M then tailTiltedProfileWeight T E else 0) =
      ∏ i, selectedTailTiltedLocalWeight T M i (E i) := by
  classical
  unfold tailTiltedProfileWeight
  by_cases hEM : E M = none
  · have hnot : ¬ Selects E M := by simpa [Selects] using hEM
    rw [if_neg hnot]
    have hzero : selectedTailTiltedLocalWeight T M M (E M) = 0 := by
      simp [selectedTailTiltedLocalWeight, hEM]
    exact (Finset.prod_eq_zero (Finset.mem_univ M) hzero).symm
  · have hsel : Selects E M := hEM
    rw [if_pos hsel]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hiM : i = M
    · subst i
      cases hstate : E M with
      | none => exact False.elim (hEM hstate)
      | some xy => simp [selectedTailTiltedLocalWeight]
    · simp [selectedTailTiltedLocalWeight, hiM]

/-- The tail-diagonal generating function, with `M` selected, has total
mass exactly `1/M`. -/
theorem sum_tailTiltedProfileWeight_selects_eq
    {I : Finset ℕ} {T : Finset ℕ} (M : ↑I) (hMT : M.1 ∉ T) :
    (∑ E : ↑I → EnergyState,
      if Selects E M then tailTiltedProfileWeight T E else 0) =
      1 / (M.1 : ℝ) := by
  simp_rw [indicator_selects_mul_tailTiltedProfileWeight_eq M hMT]
  rw [← Fintype.prod_sum]
  simp_rw [sum_selectedTailTiltedLocalWeight M _ hMT]
  simp

/-- The regular tail template predicate used in the high-octave fibre. -/
def TailRegularTemplate {I : Finset ℕ} (T : Finset ℕ) (q : ℕ)
    (E : ↑I → EnergyState) : Prop :=
  TailDiagonal T E ∧ q ≤ tailSelectedCard T E

/-- Weighted-tail generating-function bound.  It is uniform over varying
selected supports and supplies the exact `3^{-q}/M` input required by
`restrictedPredecessorFibreMass_high_le`. -/
theorem restrictedTemplateMass_tailRegular_le
    {I : Finset ℕ} {T : Finset ℕ} (M : ↑I) (q : ℕ)
    (hMT : M.1 ∉ T) :
    restrictedTemplateMass M (TailRegularTemplate T q) ≤
      (1 / (3 : ℝ) ^ q) * (1 / (M.1 : ℝ)) := by
  unfold restrictedTemplateMass
  calc
    (∑ E : ↑I → EnergyState,
      if TailRegularTemplate T q E ∧ Selects E M then
        energyProfileWeight I E else 0) ≤
      ∑ E : ↑I → EnergyState,
        (1 / (3 : ℝ) ^ q) *
          (if Selects E M then tailTiltedProfileWeight T E else 0) := by
      gcongr with E
      by_cases hreg : TailRegularTemplate T q E ∧ Selects E M
      · simp only [hreg, if_true]
        have hdiag : TailDiagonal T E := hreg.1.1
        have hcard : q ≤ tailSelectedCard T E := hreg.1.2
        rw [tailTiltedProfileWeight_eq hdiag]
        have hpow : (3 : ℝ) ^ q ≤ 3 ^ tailSelectedCard T E := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hcard
        have hscale : (1 : ℝ) ≤
            (1 / (3 : ℝ) ^ q) * 3 ^ tailSelectedCard T E := by
          rw [one_div_mul_eq_div]
          exact (le_div_iff₀ (by positivity)).2 (by simpa using hpow)
        have hw : 0 ≤ energyProfileWeight I E := by
          unfold energyProfileWeight
          exact Finset.prod_nonneg fun i _ ↦ localEnergyWeight_nonneg_all i.1 (E i)
        have hmul := mul_le_mul_of_nonneg_right hscale hw
        simpa [hreg.2, mul_assoc] using hmul
      · by_cases hsel : Selects E M
        · have hnreg : ¬ TailRegularTemplate T q E := by
            intro hr
            exact hreg ⟨hr, hsel⟩
          rw [if_neg hreg, if_pos hsel]
          have hcoeff : (0 : ℝ) ≤ 1 / (3 : ℝ) ^ q := by positivity
          exact mul_nonneg hcoeff (tailTiltedProfileWeight_nonneg T E)
        · simp [hsel]
    _ = (1 / (3 : ℝ) ^ q) *
        (∑ E : ↑I → EnergyState,
          if Selects E M then tailTiltedProfileWeight T E else 0) := by
      rw [Finset.mul_sum]
    _ = (1 / (3 : ℝ) ^ q) * (1 / (M.1 : ℝ)) := by
      rw [sum_tailTiltedProfileWeight_selects_eq M hMT]

/-- Closed high-octave fibre bound obtained by combining the generating
function with the regularity-to-diagonal-factor inequality. -/
theorem tailRegular_restrictedPredecessorFibreMass_high_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {T : Finset ℕ} (M : ↑I) (q k : ℕ) (hMT : M.1 ∉ T)
    (hq : 2 * k ≤ 1 + q) :
    restrictedPredecessorFibreMass M (TailRegularTemplate T q) ≤
      2 * (1 / (9 : ℝ) ^ k) * (1 / (M.1 : ℝ) ^ 2) := by
  exact restrictedPredecessorFibreMass_high_le hI M
    (TailRegularTemplate T q) q k hq
    (restrictedTemplateMass_tailRegular_le M q hMT)

/-! ## Deterministic ambient-profile reconstruction -/

/-- Coordinates carrying an unequal selected local pair. -/
def profileUnequalCoordinates {I : Finset ℕ}
    (Q : ↑I → EnergyState) : Finset ↑I :=
  Finset.univ.filter fun i ↦
    ∃ xy : Fin 3 × Fin 3, Q i = some xy ∧ xy.1 ≠ xy.2

/-- An ambient profile is non-diagonal if some selected local pair is
unequal. -/
def ProfileNonDiagonal {I : Finset ℕ} (Q : ↑I → EnergyState) : Prop :=
  (profileUnequalCoordinates Q).Nonempty

/-- The largest unequal coordinate of a non-diagonal ambient profile. -/
def largestProfileUnequalCoordinate {I : Finset ℕ}
    (Q : ↑I → EnergyState) (hQ : ProfileNonDiagonal Q) : ↑I :=
  (profileUnequalCoordinates Q).max' hQ

theorem largestProfileUnequalCoordinate_spec
    {I : Finset ℕ} {Q : ↑I → EnergyState}
    (hQ : ProfileNonDiagonal Q) :
    ∃ xy : Fin 3 × Fin 3,
      Q (largestProfileUnequalCoordinate Q hQ) = some xy ∧
        xy.1 ≠ xy.2 := by
  exact (Finset.mem_filter.mp (Finset.max'_mem _ hQ)).2

/-- Selected coordinates strictly below the largest unequal coordinate. -/
def profileSelectedBelow {I : Finset ℕ} (Q : ↑I → EnergyState)
    (n : ↑I) : Finset ↑I :=
  Finset.univ.filter fun i ↦ i < n ∧ Selects Q i

/-- A balanced non-diagonal ambient profile has a selected coordinate below
its largest unequal coordinate.  This is the profile-level version of the
predecessor-existence lemma and is independent of any support reindexing. -/
theorem profileSelectedBelow_largest_nonempty
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0) :
    (profileSelectedBelow Q (largestProfileUnequalCoordinate Q hQ)).Nonempty := by
  let L := largestProfileUnequalCoordinate Q hQ
  obtain ⟨xy, hQL, hxy⟩ := largestProfileUnequalCoordinate_spec hQ
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hzeroAway : ∀ i : ↑I, i ≠ L → localSignedDifference i.1 (Q i) = 0 := by
    intro i hiL
    rcases lt_or_gt_of_ne hiL with hi | hi
    · have hiNotSelected : ¬ Selects Q i := by
        intro hsel
        have hiMem : i ∈ profileSelectedBelow Q L := by
          simp [profileSelectedBelow, hi, hsel]
        rw [hempty] at hiMem
        simpa using hiMem
      have hQi : Q i = none := by
        simpa [Selects] using hiNotSelected
      simp [hQi, localSignedDifference]
    · cases hQi : Q i with
      | none => simp [hQi, localSignedDifference]
      | some uv =>
          have huv : uv.1 = uv.2 := by
            by_contra huv
            have hiMem : i ∈ profileUnequalCoordinates Q := by
              rw [profileUnequalCoordinates, Finset.mem_filter]
              exact ⟨Finset.mem_univ i, uv, hQi, huv⟩
            have hiLe : i ≤ L := Finset.le_max' _ _ hiMem
            exact (not_le_of_gt hi) hiLe
          simp [hQi, localSignedDifference, huv]
  have hsum : localSignedDifference L.1 (Q L) = 0 := by
    unfold profileSignedDifference at hbal
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ L)] at hbal
    have herase :
        (∑ i ∈ (Finset.univ : Finset ↑I).erase L,
          localSignedDifference i.1 (Q i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hzeroAway i (Finset.ne_of_mem_erase hi)
    rw [herase, zero_add] at hbal
    exact hbal
  have hLpos : 0 < L.1 := Nat.zero_lt_of_lt (hI L.1 L.2)
  have htermNe : signedTerm L.1 xy.1 ≠ signedTerm L.1 xy.2 :=
    fun heq ↦ hxy (HarmonicDecomposition.signedTerm_injective_of_pos hLpos heq)
  rw [hQL] at hsum
  simp only [localSignedDifference] at hsum
  exact htermNe (sub_eq_zero.mp hsum)

/-- The greatest selected predecessor below the largest unequal coordinate. -/
def largestProfilePredecessor {I : Finset ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i) (Q : ↑I → EnergyState)
    (hQ : ProfileNonDiagonal Q) (hbal : profileSignedDifference I Q = 0) : ↑I :=
  (profileSelectedBelow Q (largestProfileUnequalCoordinate Q hQ)).max'
    (profileSelectedBelow_largest_nonempty hI hQ hbal)

theorem largestProfilePredecessor_lt
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0) :
    largestProfilePredecessor hI Q hQ hbal <
      largestProfileUnequalCoordinate Q hQ := by
  exact (Finset.mem_filter.mp (Finset.max'_mem _
    (profileSelectedBelow_largest_nonempty hI hQ hbal))).2.1

theorem largestProfilePredecessor_selects
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0) :
    Selects Q (largestProfilePredecessor hI Q hQ hbal) := by
  exact (Finset.mem_filter.mp (Finset.max'_mem _
    (profileSelectedBelow_largest_nonempty hI hQ hbal))).2.2

/-- Erase one coordinate of an ambient profile. -/
def eraseProfileCoordinate {I : Finset ℕ} (Q : ↑I → EnergyState)
    (n : ↑I) : ↑I → EnergyState :=
  Function.update Q n none

@[simp] theorem eraseProfileCoordinate_self {I : Finset ℕ}
    (Q : ↑I → EnergyState) (n : ↑I) :
    eraseProfileCoordinate Q n n = none := by
  simp [eraseProfileCoordinate]

@[simp] theorem eraseProfileCoordinate_ne {I : Finset ℕ}
    (Q : ↑I → EnergyState) {n i : ↑I} (hi : i ≠ n) :
    eraseProfileCoordinate Q n i = Q i := by
  simp [eraseProfileCoordinate, hi]

/-- If filling a genuinely empty hole gives a balanced profile, then that
hole lies in the corresponding forced-coordinate fibre. -/
theorem mem_forcedProfileCoordinates_of_fillHole_balanced
    {I : Finset ℕ} {M n : ↑I} {E : ↑I → EnergyState}
    {xy : Fin 3 × Fin 3} (hMn : M < n) (hEn : E n = none)
    (hbal : profileSignedDifference I (fillHole E n xy) = 0) :
    n ∈ forcedProfileCoordinates M E xy := by
  rw [forcedProfileCoordinates, Finset.mem_filter]
  refine ⟨Finset.mem_univ n, hMn, hEn, ?_⟩
  unfold profileSignedDifference at hbal ⊢
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n)] at hbal
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n)]
  have herase :
      (∑ i ∈ (Finset.univ : Finset ↑I).erase n,
          localSignedDifference i.1 (fillHole E n xy i)) =
        ∑ i ∈ (Finset.univ : Finset ↑I).erase n,
          localSignedDifference i.1 (E i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [fillHole_apply_ne E (Finset.ne_of_mem_erase hi)]
  rw [herase] at hbal
  simp only [fillHole_apply_self, localSignedDifference] at hbal
  simp only [hEn, localSignedDifference, add_zero]
  linarith

/-- Every balanced non-diagonal ambient profile is recovered by the
predecessor/hole reconstruction used in the mass majorant. -/
theorem hasPredecessorReconstruction_of_balanced
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0) :
    HasPredecessorReconstruction Q := by
  let L := largestProfileUnequalCoordinate Q hQ
  let M := largestProfilePredecessor hI Q hQ hbal
  obtain ⟨xy, hQL, hxy⟩ := largestProfileUnequalCoordinate_spec hQ
  let E := eraseProfileCoordinate Q L
  refine ⟨M, E, xy, L, ?_, ?_, ?_, ?_⟩
  · have hML : M < L := largestProfilePredecessor_lt hI hQ hbal
    have hne : M ≠ L := ne_of_lt hML
    unfold Selects
    change eraseProfileCoordinate Q L M ≠ none
    rw [eraseProfileCoordinate_ne Q hne]
    simpa only [Selects] using largestProfilePredecessor_selects hI hQ hbal
  · simp [unequalStatePairs, hxy]
  · apply mem_forcedProfileCoordinates_of_fillHole_balanced
    · exact largestProfilePredecessor_lt hI hQ hbal
    · simp [E]
    · have hfill : fillHole E L xy = Q := by
        funext i
        by_cases hi : i = L
        · subst i
          simpa [E] using hQL.symm
        · simp [fillHole, E, eraseProfileCoordinate, hi]
      simpa [hfill] using hbal
  · funext i
    by_cases hi : i = L
    · subst i
      simpa [E] using hQL
    · simp [fillHole, E, eraseProfileCoordinate, hi]

/-- Natural-valued support of an ambient profile. -/
def profileSelectedNaturals {I : Finset ℕ}
    (Q : ↑I → EnergyState) : Finset ℕ :=
  ((Finset.univ : Finset ↑I).filter (Selects Q)).image fun i ↦ i.1

theorem mem_profileSelectedNaturals_iff
    {I : Finset ℕ} {Q : ↑I → EnergyState} {n : ℕ} :
    n ∈ profileSelectedNaturals Q ↔
      ∃ hn : n ∈ I, Selects Q ⟨n, hn⟩ := by
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨i.2, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨hnI, hsel⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨n, hnI⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsel⟩, rfl⟩

/-- Natural-valued support of a profile restricted to a tail. -/
def profileTailSelectedNaturals {I : Finset ℕ} (T : Finset ℕ)
    (Q : ↑I → EnergyState) : Finset ℕ :=
  ((Finset.univ : Finset ↑I).filter fun i ↦
    i.1 ∈ T ∧ Selects Q i).image fun i ↦ i.1

theorem profileTailSelectedNaturals_card
    {I : Finset ℕ} (T : Finset ℕ) (Q : ↑I → EnergyState) :
    (profileTailSelectedNaturals T Q).card = tailSelectedCard T Q := by
  unfold profileTailSelectedNaturals tailSelectedCard
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- Above the largest unequal coordinate, every local ambient state is
unselected or diagonal. -/
theorem profile_diagonal_above_largest
    {I : Finset ℕ} {Q : ↑I → EnergyState}
    (hQ : ProfileNonDiagonal Q) {i : ↑I}
    (hi : largestProfileUnequalCoordinate Q hQ < i) :
    IsDiagonalOrNone (Q i) := by
  cases hQi : Q i with
  | none => simp [IsDiagonalOrNone, hQi]
  | some xy =>
      simp only [IsDiagonalOrNone, hQi]
      by_contra hxy
      have hiMem : i ∈ profileUnequalCoordinates Q := by
        rw [profileUnequalCoordinates, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, xy, hQi, hxy⟩
      have hiLe : i ≤ largestProfileUnequalCoordinate Q hQ :=
        Finset.le_max' _ _ hiMem
      exact (not_le_of_gt hi) hiLe

/-- There is no selected coordinate strictly between the chosen predecessor
and the largest unequal coordinate. -/
theorem not_selects_between_profilePredecessor_and_largest
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0) {i : ↑I}
    (hMi : largestProfilePredecessor hI Q hQ hbal < i)
    (hiL : i < largestProfileUnequalCoordinate Q hQ) :
    ¬ Selects Q i := by
  intro hsel
  have hiMem : i ∈ profileSelectedBelow Q
      (largestProfileUnequalCoordinate Q hQ) := by
    simp [profileSelectedBelow, hiL, hsel]
  have hiLe : i ≤ largestProfilePredecessor hI Q hQ hbal :=
    Finset.le_max' _ _ hiMem
  exact (not_le_of_gt hMi) hiLe

/-- Erasing the largest unequal coordinate removes at most one point from
the selected natural support in any tail. -/
theorem supportTail_erase_largest_card_le
    {I : Finset ℕ} {Q : ↑I → EnergyState}
    (hQ : ProfileNonDiagonal Q) (T : Finset ℕ) :
    ((profileSelectedNaturals Q ∩ T).erase
      (largestProfileUnequalCoordinate Q hQ).1).card ≤
        tailSelectedCard T
          (eraseProfileCoordinate Q
            (largestProfileUnequalCoordinate Q hQ)) := by
  let L := largestProfileUnequalCoordinate Q hQ
  let E := eraseProfileCoordinate Q L
  have hsubset :
      (profileSelectedNaturals Q ∩ T).erase L.1 ⊆
        profileTailSelectedNaturals T E := by
    intro n hn
    have hnData := Finset.mem_erase.mp hn
    have hnInter := Finset.mem_inter.mp hnData.2
    obtain ⟨hnI, hnSel⟩ := mem_profileSelectedNaturals_iff.mp hnInter.1
    let i : ↑I := ⟨n, hnI⟩
    have hiL : i ≠ L := by
      intro hil
      exact hnData.1 (congrArg Subtype.val hil)
    have hnSelE : Selects E i := by
      unfold Selects
      change eraseProfileCoordinate Q L i ≠ none
      rw [eraseProfileCoordinate_ne Q hiL]
      simpa only [Selects] using hnSel
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hnInter.2, hnSelE⟩, rfl⟩
  calc
    ((profileSelectedNaturals Q ∩ T).erase L.1).card ≤
        (profileTailSelectedNaturals T E).card :=
      Finset.card_le_card hsubset
    _ = tailSelectedCard T E := profileTailSelectedNaturals_card T E

/-- The regular support lower bound survives erasing the largest unequal
coordinate, with the loss of at most one selected tail point. -/
theorem regular_tail_card_le_erased_largest
    {I : Finset ℕ} {Q : ↑I → EnergyState}
    (hQ : ProfileNonDiagonal Q) {D R s r : ℕ}
    (hregular : OctaveRegular D R s (profileSelectedNaturals Q))
    (hr : r ∈ Finset.Icc s R) :
    2 * (r - s) ≤ 1 +
      tailSelectedCard (Finset.Ioc (D / 8 ^ r) D)
        (eraseProfileCoordinate Q
          (largestProfileUnequalCoordinate Q hQ)) := by
  let T := Finset.Ioc (D / 8 ^ r) D
  let L := largestProfileUnequalCoordinate Q hQ
  have htail := hregular r hr
  have herase := supportTail_erase_largest_card_le hQ T
  have hcard : (profileSelectedNaturals Q ∩ T).card ≤
      1 + ((profileSelectedNaturals Q ∩ T).erase L.1).card := by
    by_cases hLmem : L.1 ∈ profileSelectedNaturals Q ∩ T
    · have heq := Finset.card_erase_add_one hLmem
      omega
    · rw [Finset.erase_eq_self.mpr hLmem]
      omega
  dsimp [T, L] at htail herase hcard ⊢
  omega

/-- If the predecessor lies below the lower endpoint of a tail, erasing the
largest unequal coordinate makes every selected tail state diagonal. -/
theorem erase_largest_tailDiagonal
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0)
    {D r : ℕ}
    (hMupper : (largestProfilePredecessor hI Q hQ hbal).1 ≤ D / 8 ^ r) :
    TailDiagonal (Finset.Ioc (D / 8 ^ r) D)
      (eraseProfileCoordinate Q
        (largestProfileUnequalCoordinate Q hQ)) := by
  let L := largestProfileUnequalCoordinate Q hQ
  let M := largestProfilePredecessor hI Q hQ hbal
  let E := eraseProfileCoordinate Q L
  intro i hiT
  have hMi : M < i := by
    apply Subtype.mk_lt_mk.mpr
    exact lt_of_le_of_lt hMupper (Finset.mem_Ioc.mp hiT).1
  by_cases hiL : i = L
  · subst i
    change IsDiagonalOrNone (eraseProfileCoordinate Q L L)
    simp [IsDiagonalOrNone]
  rcases lt_or_gt_of_ne hiL with hi | hi
  · have hnsel : ¬ Selects Q i :=
      not_selects_between_profilePredecessor_and_largest hI hQ hbal hMi hi
    have hQi : Q i = none := by simpa [Selects] using hnsel
    change IsDiagonalOrNone (eraseProfileCoordinate Q L i)
    rw [eraseProfileCoordinate_ne Q hiL]
    simp [hQi, IsDiagonalOrNone]
  · have hdiag := profile_diagonal_above_largest hQ hi
    change IsDiagonalOrNone (eraseProfileCoordinate Q L i)
    rw [eraseProfileCoordinate_ne Q hiL]
    exact hdiag

/-- The erased largest-coordinate template satisfies the fixed high-octave
tail predicate used by the generating-function estimate. -/
theorem erase_largest_tailRegularTemplate
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0)
    {D R s r : ℕ}
    (hregular : OctaveRegular D R s (profileSelectedNaturals Q))
    (hr : r ∈ Finset.Icc s R)
    (hMupper : (largestProfilePredecessor hI Q hQ hbal).1 ≤ D / 8 ^ r) :
    TailRegularTemplate (Finset.Ioc (D / 8 ^ r) D)
      (2 * (r - s) - 1)
      (eraseProfileCoordinate Q
        (largestProfileUnequalCoordinate Q hQ)) := by
  refine ⟨erase_largest_tailDiagonal hI hQ hbal hMupper, ?_⟩
  have hcard := regular_tail_card_le_erased_largest hQ hregular hr
  omega

theorem largestProfilePredecessor_not_mem_regularTail
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0) {D r : ℕ}
    (hMupper : (largestProfilePredecessor hI Q hQ hbal).1 ≤ D / 8 ^ r) :
    (largestProfilePredecessor hI Q hQ hbal).1 ∉
      Finset.Ioc (D / 8 ^ r) D := by
  intro hmem
  exact (not_lt_of_ge hMupper) (Finset.mem_Ioc.mp hmem).1

/-! ## Restricted reconstruction majorants -/

/-- A reconstruction whose predecessor belongs to `B` and whose erased
template satisfies `Regular`. -/
def HasRestrictedPredecessorReconstruction {I : Finset ℕ}
    (B : Finset ↑I) (Regular : (↑I → EnergyState) → Prop)
    (Q : ↑I → EnergyState) : Prop :=
  ∃ (M : ↑I), M ∈ B ∧
    ∃ (E : ↑I → EnergyState) (xy : Fin 3 × Fin 3) (n : ↑I),
      Regular E ∧ Selects E M ∧ xy ∈ unequalStatePairs ∧
        n ∈ forcedProfileCoordinates M E xy ∧ Q = fillHole E n xy

/-- Total mass of profiles admitting a restricted reconstruction. -/
def restrictedReconstructedProfileMass {I : Finset ℕ}
    (B : Finset ↑I) (Regular : (↑I → EnergyState) → Prop) : ℝ :=
  ∑ Q : ↑I → EnergyState,
    if HasRestrictedPredecessorReconstruction B Regular Q then
      energyProfileWeight I Q else 0

/-- Equality-indicator majorant for restricted reconstructions. -/
def restrictedReconstructionMajorant {I : Finset ℕ}
    (B : Finset ↑I) (Regular : (↑I → EnergyState) → Prop)
    (Q : ↑I → EnergyState) : ℝ :=
  ∑ M ∈ B, ∑ E : ↑I → EnergyState,
    if Regular E ∧ Selects E M then
      ∑ xy ∈ unequalStatePairs,
        ∑ n ∈ forcedProfileCoordinates M E xy,
          if Q = fillHole E n xy then
            energyProfileWeight I (fillHole E n xy) else 0
    else 0

/-- Deterministic membership in the fixed high-octave reconstruction event.
This packages the largest-coordinate construction together with the erased
tail regularity theorem. -/
theorem hasRestrictedPredecessorReconstruction_tailRegular
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0)
    {D R s r : ℕ}
    (hregular : OctaveRegular D R s (profileSelectedNaturals Q))
    (hr : r ∈ Finset.Icc s R)
    (hMupper : (largestProfilePredecessor hI Q hQ hbal).1 ≤ D / 8 ^ r)
    (B : Finset ↑I)
    (hMB : largestProfilePredecessor hI Q hQ hbal ∈ B) :
    HasRestrictedPredecessorReconstruction B
      (TailRegularTemplate (Finset.Ioc (D / 8 ^ r) D)
        (2 * (r - s) - 1)) Q := by
  let L := largestProfileUnequalCoordinate Q hQ
  let M := largestProfilePredecessor hI Q hQ hbal
  obtain ⟨xy, hQL, hxy⟩ := largestProfileUnequalCoordinate_spec hQ
  let E := eraseProfileCoordinate Q L
  refine ⟨M, hMB, E, xy, L, ?_, ?_, ?_, ?_, ?_⟩
  · exact erase_largest_tailRegularTemplate hI hQ hbal hregular hr hMupper
  · have hML : M < L := largestProfilePredecessor_lt hI hQ hbal
    have hne : M ≠ L := ne_of_lt hML
    unfold Selects
    change eraseProfileCoordinate Q L M ≠ none
    rw [eraseProfileCoordinate_ne Q hne]
    simpa only [Selects] using largestProfilePredecessor_selects hI hQ hbal
  · simp [unequalStatePairs, hxy]
  · apply mem_forcedProfileCoordinates_of_fillHole_balanced
    · exact largestProfilePredecessor_lt hI hQ hbal
    · simp [E]
    · have hfill : fillHole E L xy = Q := by
        funext i
        by_cases hi : i = L
        · subst i
          simpa [E] using hQL.symm
        · simp [fillHole, E, eraseProfileCoordinate, hi]
      simpa [hfill] using hbal
  · funext i
    by_cases hi : i = L
    · subst i
      simpa [E] using hQL
    · simp [fillHole, E, eraseProfileCoordinate, hi]

theorem restrictedReconstructedProfile_le_majorant
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    (B : Finset ↑I) (Regular : (↑I → EnergyState) → Prop)
    (Q : ↑I → EnergyState) :
    (if HasRestrictedPredecessorReconstruction B Regular Q then
        energyProfileWeight I Q else 0) ≤
      restrictedReconstructionMajorant B Regular Q := by
  by_cases hQ : HasRestrictedPredecessorReconstruction B Regular Q
  · simp only [hQ, if_true]
    rcases hQ with ⟨M, hMB, E, xy, n, hreg, hEM, hxy, hn, hQeq⟩
    rw [hQeq]
    unfold restrictedReconstructionMajorant
    have hinner : energyProfileWeight I (fillHole E n xy) ≤
        ∑ E' : ↑I → EnergyState,
        if Regular E' ∧ Selects E' M then
          ∑ xy' ∈ unequalStatePairs,
            ∑ n' ∈ forcedProfileCoordinates M E' xy',
              if fillHole E n xy = fillHole E' n' xy' then
                energyProfileWeight I (fillHole E' n' xy') else 0
        else 0 := by
      have hchosen : energyProfileWeight I (fillHole E n xy) ≤
          (if Regular E ∧ Selects E M then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M E xy',
                if fillHole E n xy = fillHole E n' xy' then
                  energyProfileWeight I (fillHole E n' xy') else 0
          else 0) := by
        simp only [hreg, hEM, and_self, if_true]
        calc
          energyProfileWeight I (fillHole E n xy) ≤
              ∑ n' ∈ forcedProfileCoordinates M E xy,
                if fillHole E n xy = fillHole E n' xy then
                  energyProfileWeight I (fillHole E n' xy) else 0 := by
            calc
              energyProfileWeight I (fillHole E n xy) =
                  (if fillHole E n xy = fillHole E n xy then
                    energyProfileWeight I (fillHole E n xy) else 0) := by simp
              _ ≤ ∑ n' ∈ forcedProfileCoordinates M E xy,
                  if fillHole E n xy = fillHole E n' xy then
                    energyProfileWeight I (fillHole E n' xy) else 0 := by
                apply Finset.single_le_sum (f := fun n' ↦
                  if fillHole E n xy = fillHole E n' xy then
                    energyProfileWeight I (fillHole E n' xy) else 0)
                · intro n' _
                  by_cases heq : fillHole E n xy = fillHole E n' xy
                  · simp [heq, energyProfileWeight_nonneg hI]
                  · simp [heq]
                · exact hn
          _ ≤ ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M E xy',
                if fillHole E n xy = fillHole E n' xy' then
                  energyProfileWeight I (fillHole E n' xy') else 0 := by
            apply Finset.single_le_sum (f := fun xy' ↦
              ∑ n' ∈ forcedProfileCoordinates M E xy',
                if fillHole E n xy = fillHole E n' xy' then
                  energyProfileWeight I (fillHole E n' xy') else 0)
            · intro xy' _
              exact Finset.sum_nonneg fun n' _ ↦ by
                by_cases heq : fillHole E n xy = fillHole E n' xy'
                · simp [heq, energyProfileWeight_nonneg hI]
                · simp [heq]
            · exact hxy
      have hEsum :
          (if Regular E ∧ Selects E M then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M E xy',
                if fillHole E n xy = fillHole E n' xy' then
                  energyProfileWeight I (fillHole E n' xy') else 0
          else 0) ≤
            ∑ E' : ↑I → EnergyState,
              if Regular E' ∧ Selects E' M then
                ∑ xy' ∈ unequalStatePairs,
                  ∑ n' ∈ forcedProfileCoordinates M E' xy',
                    if fillHole E n xy = fillHole E' n' xy' then
                      energyProfileWeight I (fillHole E' n' xy') else 0
              else 0 := by
        apply Finset.single_le_sum (f := fun E' ↦
          if Regular E' ∧ Selects E' M then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M E' xy',
                if fillHole E n xy = fillHole E' n' xy' then
                  energyProfileWeight I (fillHole E' n' xy') else 0
          else 0)
        · intro E' _
          by_cases hE' : Regular E' ∧ Selects E' M
          · simp only [hE', if_true]
            exact Finset.sum_nonneg fun xy' _ ↦ Finset.sum_nonneg fun n' _ ↦ by
              by_cases heq : fillHole E n xy = fillHole E' n' xy'
              · simp [heq, energyProfileWeight_nonneg hI]
              · simp [heq]
          · simp [hE']
        · exact Finset.mem_univ E
      exact hchosen.trans hEsum
    calc
      energyProfileWeight I (fillHole E n xy) ≤
          ∑ E' : ↑I → EnergyState,
            if Regular E' ∧ Selects E' M then
              ∑ xy' ∈ unequalStatePairs,
                ∑ n' ∈ forcedProfileCoordinates M E' xy',
                  if fillHole E n xy = fillHole E' n' xy' then
                    energyProfileWeight I (fillHole E' n' xy') else 0
            else 0 := hinner
      _ ≤ ∑ M' ∈ B, ∑ E' : ↑I → EnergyState,
          if Regular E' ∧ Selects E' M' then
            ∑ xy' ∈ unequalStatePairs,
              ∑ n' ∈ forcedProfileCoordinates M' E' xy',
                if fillHole E n xy = fillHole E' n' xy' then
                  energyProfileWeight I (fillHole E' n' xy') else 0
          else 0 := by
        apply Finset.single_le_sum (f := fun M' ↦
          ∑ E' : ↑I → EnergyState,
            if Regular E' ∧ Selects E' M' then
              ∑ xy' ∈ unequalStatePairs,
                ∑ n' ∈ forcedProfileCoordinates M' E' xy',
                  if fillHole E n xy = fillHole E' n' xy' then
                    energyProfileWeight I (fillHole E' n' xy') else 0
            else 0)
        · intro M' _
          exact Finset.sum_nonneg fun E' _ ↦ by
            by_cases hE' : Regular E' ∧ Selects E' M'
            · simp only [hE', if_true]
              exact Finset.sum_nonneg fun xy' _ ↦
                Finset.sum_nonneg fun n' _ ↦ by
                  by_cases heq : fillHole E n xy = fillHole E' n' xy'
                  · simp [heq, energyProfileWeight_nonneg hI]
                  · simp [heq]
            · simp [hE']
        · exact hMB
  · simp only [hQ, if_false]
    unfold restrictedReconstructionMajorant
    exact Finset.sum_nonneg fun M _ ↦ Finset.sum_nonneg fun E _ ↦ by
      by_cases hE : Regular E ∧ Selects E M
      · simp only [hE, if_true]
        exact Finset.sum_nonneg fun xy _ ↦ Finset.sum_nonneg fun n _ ↦ by
          by_cases heq : Q = fillHole E n xy
          · simp [heq, energyProfileWeight_nonneg hI]
          · simp [heq]
      · simp [hE]

theorem sum_restrictedReconstructionMajorant_eq
    {I : Finset ℕ} (B : Finset ↑I)
    (Regular : (↑I → EnergyState) → Prop) :
    (∑ Q : ↑I → EnergyState,
      restrictedReconstructionMajorant B Regular Q) =
      ∑ M ∈ B, restrictedPredecessorFibreMass M Regular := by
  unfold restrictedReconstructionMajorant restrictedPredecessorFibreMass
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  by_cases hE : Regular E ∧ Selects E M
  · simp only [hE.1, hE.2, true_and, if_true]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xy _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    simp
  · simp [hE]

theorem restrictedReconstructedProfileMass_le_fibres
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    (B : Finset ↑I) (Regular : (↑I → EnergyState) → Prop) :
    restrictedReconstructedProfileMass B Regular ≤
      ∑ M ∈ B, restrictedPredecessorFibreMass M Regular := by
  unfold restrictedReconstructedProfileMass
  calc
    (∑ Q : ↑I → EnergyState,
      if HasRestrictedPredecessorReconstruction B Regular Q then
        energyProfileWeight I Q else 0) ≤
        ∑ Q : ↑I → EnergyState,
          restrictedReconstructionMajorant B Regular Q := by
      gcongr with Q
      exact restrictedReconstructedProfile_le_majorant hI B Regular Q
    _ = ∑ M ∈ B, restrictedPredecessorFibreMass M Regular :=
      sum_restrictedReconstructionMajorant_eq B Regular

/-- Summed high-octave estimate for any family of predecessors lying below
the lower tail endpoint. -/
theorem restrictedReconstructedProfileMass_tailRegular_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {T : Finset ℕ} (B : Finset ↑I) (q k : ℕ)
    (hBT : ∀ M ∈ B, M.1 ∉ T) (hq : 2 * k ≤ 1 + q) :
    restrictedReconstructedProfileMass B (TailRegularTemplate T q) ≤
      ∑ M ∈ B,
        2 * (1 / (9 : ℝ) ^ k) * (1 / (M.1 : ℝ) ^ 2) := by
  calc
    restrictedReconstructedProfileMass B (TailRegularTemplate T q) ≤
        ∑ M ∈ B,
          restrictedPredecessorFibreMass M (TailRegularTemplate T q) :=
      restrictedReconstructedProfileMass_le_fibres hI B _
    _ ≤ ∑ M ∈ B,
        2 * (1 / (9 : ℝ) ^ k) * (1 / (M.1 : ℝ) ^ 2) := by
      gcongr with M hMB
      exact tailRegular_restrictedPredecessorFibreMass_high_le
        hI M q k (hBT M hMB) hq

end

end Erdos144.HarmonicStateExpectation
