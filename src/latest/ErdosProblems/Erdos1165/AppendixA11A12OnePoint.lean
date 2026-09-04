/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileA11Tail
import ErdosProblems.Erdos1165.GaussianMultiBlockProfile

/-!
# Cycle-free A.11--A.12 constrained-profile lower bound

This module combines the shifted Taylor/energy comparison with the finite
connected Gaussian block factorization.  It produces the exact one-point
profile probability lower bound consumed by the Proposition 1.3 assembly;
no random-walk Harnack or disintegration input occurs here.
-/

open scoped BigOperators

namespace Erdos1165.AppendixA11A12OnePoint

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor ProfileA11Assembly
  ProfileA11Tail GaussianSmallBall GaussianProfileReindex
  GaussianBlockFactorization GaussianMultiBlockProfile ProfileListExponent

/-- Exact Stirling factor contributed by the centered finite prefix. -/
def centeredPrefixStirlingWeight (start : ℕ) : ℝ :=
  Real.exp (∑ l ∈ Finset.Ico 2 start,
    edgeStirlingExponent (profileCenter l) (profileCenter (l + 1)))

lemma centeredPrefixStirlingWeight_pos (start : ℕ) :
    0 < centeredPrefixStirlingWeight start := Real.exp_pos _

/-- The explicit shifted A.11 factor, excluding the multiblock spectral and
connector cost. -/
def shiftedA11Factor (start n : ℕ) (delta A B C : ℝ) : ℝ :=
  Real.exp (-(2 * (n - start : ℕ) : ℝ) -
    a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta))

lemma shiftedA11Factor_pos (start n : ℕ) (delta A B C : ℝ) :
    0 < shiftedA11Factor start n delta A B C := Real.exp_pos _

/-- Fully explicit finite A.11--A.12 lower quantity. -/
def multiblockProfileLower (n : ℕ) (delta A B C : ℝ)
    (blocks : List GaussianBlock) : ℝ :=
  match blocks with
  | [] => 0
  | b :: bs => centeredPrefixStirlingWeight b.start *
      Real.exp (-(2 * (n - b.start : ℕ) : ℝ) -
        a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) -
        gaussianBlockTotalCost (b :: bs))

lemma multiblockProfileLower_pos {n : ℕ} {delta A B C : ℝ}
    {b : GaussianBlock} {bs : List GaussianBlock} :
    0 < multiblockProfileLower n delta A B C (b :: bs) := by
  change 0 < centeredPrefixStirlingWeight b.start * Real.exp _
  exact mul_pos (centeredPrefixStirlingWeight_pos b.start) (Real.exp_pos _)

/-- Deterministic pointwise hypotheses needed by shifted A.11 for every path
in a supplied multiblock family.  These are finite inequalities, intended to
be discharged once for the explicit geometric schedule. -/
structure EmbeddedTailA11Certificate (n start : ℕ) (delta A B C : ℝ)
    (blocks : List GaussianBlock) : Prop where
  delta_pos : 0 < delta
  delta_le_third : delta ≤ 1 / 3
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  C_nonneg : 0 ≤ C
  entry_two_le : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Ico start n →
    2 ≤ centeredProfileValue l (independentBlockDeviation p l)
  taylorWindow : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Ico start n →
    InEdgeTaylorWindow
      (centeredProfileValue l (independentBlockDeviation p l))
      (centeredProfileValue (l + 1) (independentBlockDeviation p (l + 1)))
  base : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Ico start n →
    (l : ℝ) ^ 2 ≤
      (centeredProfileValue l (independentBlockDeviation p l) - 1 : ℕ)
  close : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Ico start n →
    |2 * (l : ℝ) ^ 2 -
      (centeredProfileValue l (independentBlockDeviation p l) - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta
  moderate : ∀ (l : ℕ), l ∈ Finset.Ico start n →
    A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2
  increment : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Ico start n →
    |parabolicTransitionIncrement
      (centeredProfileValue l (independentBlockDeviation p l))
      (centeredProfileValue (l + 1) (independentBlockDeviation p (l + 1)))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta
  deviation : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Icc start n →
    |(independentBlockDeviation p l : ℝ)| ≤
      B * (l : ℝ) * (l : ℝ) ^ delta
  deviationIncrement : ∀ (p : IndependentGaussianBlockPaths blocks)
    (l : ℕ), l ∈ Finset.Ico start n →
    |(independentBlockDeviation p (l + 1) : ℝ) -
      (independentBlockDeviation p l : ℝ)| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta

lemma centeredProfileValue_real_eq {l : ℕ} {x : ℤ}
    (hx : -(profileCenter l : ℤ) ≤ x) :
    (centeredProfileValue l x : ℝ) =
      2 * (l : ℝ) ^ 2 + (x : ℝ) := by
  have h := centeredProfileValue_cast hx
  exact_mod_cast h

lemma profileAtScale_embeddedMultiBlockProfile
    {n : ℕ} {blocks : List GaussianBlock}
    (p : IndependentGaussianBlockPaths blocks) {l : ℕ}
    (hlower : 2 ≤ l) (hupper : l ≤ n) :
    profileAtScale (embeddedMultiBlockProfile n p) l =
      centeredProfileValue l (independentBlockDeviation p l) := by
  unfold profileAtScale
  rw [dif_pos ⟨hlower, hupper⟩]
  let i : Fin (n - 1) := ⟨l - 2, by omega⟩
  change embeddedMultiBlockProfile n p i = _
  have hscale : scaleIndex i = l := by
    unfold scaleIndex
    dsimp only [i]
    omega
  unfold embeddedMultiBlockProfile
  rw [hscale]

/-- Tail Gaussian segment product in exponential energy-normalizer form. -/
lemma gaussianSegmentProduct_eq_exp_from {start n : ℕ}
    (hstart : 1 ≤ start) (hstartn : start ≤ n) (D : ℕ → ℤ) :
    gaussianSegmentProduct start (n - start) D =
      Real.exp (-gaussianEnergyFrom start n (fun l ↦ (D l : ℝ)) -
        gaussianNormalizerLogSumFrom start n) := by
  rw [gaussianSegmentProduct_eq_prod_Ico]
  rw [Nat.add_sub_of_le hstartn]
  have hsum :
      -gaussianEnergyFrom start n (fun l ↦ (D l : ℝ)) -
          gaussianNormalizerLogSumFrom start n =
        ∑ l ∈ Finset.Ico start n,
          (-(((D (l + 1) - D l : ℤ) : ℝ) ^ 2) /
              (8 * (l : ℝ) ^ 2) -
            Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2) := by
    unfold gaussianEnergyFrom gaussianNormalizerLogSumFrom
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    push_cast
    ring
  rw [hsum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro l hl
  exact gaussianStepWeight_eq_exp_edgeLog
    (by have := (Finset.mem_Ico.mp hl).1; omega : 0 < l)
    (D (l + 1) - D l)

lemma centeredPrefix_exponent_eq_embedded
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hbstart : 2 ≤ b.start) (hbn : b.start ≤ n)
    (p : IndependentGaussianBlockPaths (b :: bs))
    (hconsecutive : ConsecutiveBlocks (b :: bs)) :
    (∑ l ∈ Finset.Ico 2 b.start,
      edgeStirlingExponent
        (profileAtScale (embeddedMultiBlockProfile n p) l)
        (profileAtScale (embeddedMultiBlockProfile n p) (l + 1))) =
      ∑ l ∈ Finset.Ico 2 b.start,
        edgeStirlingExponent (profileCenter l) (profileCenter (l + 1)) := by
  apply Finset.sum_congr rfl
  intro l hl
  have hlb := Finset.mem_Ico.mp hl
  have hl0 := independentBlockDeviation_eq_zero_of_le_first_start
    p hconsecutive (show l ≤ b.start by omega)
  have hl1 := independentBlockDeviation_eq_zero_of_le_first_start
    p hconsecutive (show l + 1 ≤ b.start by omega)
  rw [profileAtScale_embeddedMultiBlockProfile p hlb.1
      (show l ≤ n by omega),
    profileAtScale_embeddedMultiBlockProfile p (by omega)
      (show l + 1 ≤ n by omega), hl0, hl1,
    centeredProfileValue_zero, centeredProfileValue_zero]

lemma shiftedA11Factor_mul_connected_le_tailStirling
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hn : 2 ≤ n) (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = n)
    (hcenter : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      c.radius ≤ profileCenter l)
    {delta A B C : ℝ}
    (cert : EmbeddedTailA11Certificate n b.start delta A B C (b :: bs))
    (p : IndependentGaussianBlockPaths (b :: bs)) :
    shiftedA11Factor b.start n delta A B C *
        connectedGaussianBlockWeight p ≤
      Real.exp (∑ l ∈ Finset.Ico b.start n,
        edgeStirlingExponent
          (profileAtScale (embeddedMultiBlockProfile n p) l)
          (profileAtScale (embeddedMultiBlockProfile n p) (l + 1))) := by
  have hbn : b.start ≤ n := by
    rw [← hend]
    exact gaussianBlocksEnd_ge_start hconsecutive
  let D : ℕ → ℤ := independentBlockDeviation p
  let m : ℕ → ℕ := fun l ↦ centeredProfileValue l (D l)
  have hDlower : ∀ l, -(profileCenter l : ℤ) ≤ D l :=
    independentBlockDeviation_lower p hcenter
  have hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + (D l : ℝ) :=
    fun l ↦ centeredProfileValue_real_eq (hDlower l)
  have ha11 := exp_a11Error_mul_gaussianLogWeight_le_from
    b.start n hbstart hbn m (fun l ↦ (D l : ℝ))
    cert.delta_pos cert.delta_le_third cert.A_nonneg cert.B_nonneg cert.C_nonneg
    (cert.entry_two_le p) (cert.taylorWindow p) (cert.base p)
    (cert.close p) cert.moderate (cert.increment p) hparabolic
    (cert.deviation p) (cert.deviationIncrement p)
  have hsegment := gaussianSegmentProduct_eq_exp_from (by omega) hbn D
  have hconnected := connectedGaussianBlockWeight_eq_segment p hconsecutive
  have htailValues :
      (∑ l ∈ Finset.Ico b.start n,
        edgeStirlingExponent (m l) (m (l + 1))) =
      ∑ l ∈ Finset.Ico b.start n,
        edgeStirlingExponent
          (profileAtScale (embeddedMultiBlockProfile n p) l)
          (profileAtScale (embeddedMultiBlockProfile n p) (l + 1)) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlb := Finset.mem_Ico.mp hl
    rw [profileAtScale_embeddedMultiBlockProfile p
        (hbstart.trans hlb.1) (Nat.le_of_lt hlb.2),
      profileAtScale_embeddedMultiBlockProfile p (by omega) hlb.2]
  rw [← htailValues]
  rw [show connectedGaussianBlockWeight p =
      gaussianSegmentProduct b.start (n - b.start) D by
    simpa [D, hend] using hconnected]
  rw [hsegment]
  unfold shiftedA11Factor
  rw [← Real.exp_add]
  convert ha11 using 1 <;> ring_nf

/-- Pointwise A.11 comparison for a member of the injective multiblock
family, including the exact centered prefix. -/
lemma multiblockProfileLower_pointwise
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hn : 2 ≤ n) (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = n)
    (hcenter : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      c.radius ≤ profileCenter l)
    {delta A B C : ℝ}
    (cert : EmbeddedTailA11Certificate n b.start delta A B C (b :: bs))
    (p : IndependentGaussianBlockPaths (b :: bs)) :
    centeredPrefixStirlingWeight b.start *
        shiftedA11Factor b.start n delta A B C *
        connectedGaussianBlockWeight p ≤
      stirlingLowerProduct
        (profileList (embeddedMultiBlockProfile n p)) := by
  have htail := shiftedA11Factor_mul_connected_le_tailStirling
    hn hbstart hconsecutive hend hcenter cert p
  have hmul := mul_le_mul_of_nonneg_left htail
    (centeredPrefixStirlingWeight_pos b.start).le
  let f : ℕ → ℝ := fun l ↦ edgeStirlingExponent
    (profileAtScale (embeddedMultiBlockProfile n p) l)
    (profileAtScale (embeddedMultiBlockProfile n p) (l + 1))
  have hbn : b.start ≤ n := by
    rw [← hend]
    exact gaussianBlocksEnd_ge_start hconsecutive
  have hfull :
      stirlingLowerProduct (profileList (embeddedMultiBlockProfile n p)) =
        centeredPrefixStirlingWeight b.start *
          Real.exp (∑ l ∈ Finset.Ico b.start n, f l) := by
    rw [stirlingLowerProduct_eq_exp,
      stirlingLogLower_profileList_eq_sum_edgeStirlingExponent hn]
    unfold centeredPrefixStirlingWeight
    rw [← Real.exp_add]
    congr 1
    calc
      (∑ l ∈ Finset.Ico 2 n, f l) =
          (∑ l ∈ Finset.Ico 2 b.start, f l) +
            ∑ l ∈ Finset.Ico b.start n, f l :=
        (Finset.sum_Ico_consecutive f hbstart hbn).symm
      _ = (∑ l ∈ Finset.Ico 2 b.start,
          edgeStirlingExponent (profileCenter l) (profileCenter (l + 1))) +
            ∑ l ∈ Finset.Ico b.start n, f l := by
        rw [centeredPrefix_exponent_eq_embedded hbstart hbn p hconsecutive]
  rw [hfull]
  change centeredPrefixStirlingWeight b.start *
      shiftedA11Factor b.start n delta A B C *
      connectedGaussianBlockWeight p ≤
    centeredPrefixStirlingWeight b.start * Real.exp _
  simpa only [mul_assoc] using hmul

/-- **Checked finite A.11--A.12 constrained-profile probability bound.**

All Gaussian reindexing, connector retention, shifted Taylor error, and
prefix bookkeeping are discharged.  The hypotheses are finite deterministic
properties of the chosen block schedule. -/
theorem multiblockProfileLower_le_constrainedProfileWeight
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hn : 2 ≤ n) (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = n)
    (hstart : ∀ c ∈ b :: bs, 0 < c.start)
    (hscale : ∀ c ∈ b :: bs,
      (2560 : ℝ) * (c.start + c.steps : ℕ) ^ 2 ≤ (c.radius : ℝ) ^ 2)
    {delta A B C : ℝ}
    (hcenter : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      c.radius ≤ profileCenter l)
    (hwidth : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      (c.radius : ℝ) ≤ (l : ℝ) ^ (1 + delta))
    (cert : EmbeddedTailA11Certificate n b.start delta A B C (b :: bs)) :
    multiblockProfileLower n delta A B C (b :: bs) ≤
      constrainedProfileWeight n delta := by
  have hmass := exp_neg_gaussianBlockTotalCost_le_sum_connected
    (b :: bs) hstart hscale
  have hfactor0 : 0 ≤ centeredPrefixStirlingWeight b.start *
      shiftedA11Factor b.start n delta A B C :=
    mul_nonneg (centeredPrefixStirlingWeight_pos b.start).le
      (shiftedA11Factor_pos b.start n delta A B C).le
  have hweighted := mul_le_mul_of_nonneg_left hmass hfactor0
  have hpointwise :
      (∑ p : IndependentGaussianBlockPaths (b :: bs),
        centeredPrefixStirlingWeight b.start *
          shiftedA11Factor b.start n delta A B C *
          connectedGaussianBlockWeight p) ≤
      ∑ p : IndependentGaussianBlockPaths (b :: bs),
        stirlingLowerProduct (profileList (embeddedMultiBlockProfile n p)) := by
    exact Finset.sum_le_sum fun p _ ↦
      multiblockProfileLower_pointwise hn hbstart hconsecutive hend
        hcenter cert p
  have hreindex :
      (∑ p : IndependentGaussianBlockPaths (b :: bs),
        stirlingLowerProduct (profileList (embeddedMultiBlockProfile n p))) ≤
      constrainedStirlingWeight n delta := by
    let e : IndependentGaussianBlockPaths (b :: bs) → Profile n :=
      embeddedMultiBlockProfile n
    have he : Function.Injective e :=
      embeddedMultiBlockProfile_injective n
        (consecutiveBlocks_strictlyOrdered hconsecutive)
        (fun c hc ↦ hbstart.trans (by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact le_rfl
          · have hlt := (consecutiveBlocks_strictlyOrdered hconsecutive).1 c hc
            omega))
        (fun c hc ↦ by
          rw [← hend]
          exact gaussianBlockEnd_le_blocksEnd_of_mem hconsecutive hc)
        (fun c hc ↦ hcenter c hc c.start ⟨le_rfl, by omega⟩)
    have himage : Finset.image e Finset.univ ⊆ constrainedProfiles n delta := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨p, _hp, rfl⟩ := hm
      exact embeddedMultiBlockProfile_mem_constrainedProfiles n p hcenter hwidth
    calc
      _ = ∑ m ∈ Finset.image e Finset.univ,
          stirlingLowerProduct (profileList m) := by
        symm
        exact Finset.sum_image he.injOn
      _ ≤ ∑ m ∈ constrainedProfiles n delta,
          stirlingLowerProduct (profileList m) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun m _ _ ↦ stirlingLowerProduct_nonneg _)
      _ = constrainedStirlingWeight n delta := rfl
  calc
    multiblockProfileLower n delta A B C (b :: bs) =
        (centeredPrefixStirlingWeight b.start *
          shiftedA11Factor b.start n delta A B C) *
          Real.exp (-gaussianBlockTotalCost (b :: bs)) := by
      change centeredPrefixStirlingWeight b.start * Real.exp
          (-(2 * (n - b.start : ℕ) : ℝ) -
            a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) -
            gaussianBlockTotalCost (b :: bs)) = _
      unfold shiftedA11Factor
      rw [show -(2 * (n - b.start : ℕ) : ℝ) -
          a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) -
          gaussianBlockTotalCost (b :: bs) =
        (-(2 * (n - b.start : ℕ) : ℝ) -
          a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta)) +
          (-gaussianBlockTotalCost (b :: bs)) by ring,
        Real.exp_add]
      ring
    _ ≤ (centeredPrefixStirlingWeight b.start *
          shiftedA11Factor b.start n delta A B C) *
        ∑ p : IndependentGaussianBlockPaths (b :: bs),
          connectedGaussianBlockWeight p := hweighted
    _ = ∑ p : IndependentGaussianBlockPaths (b :: bs),
        centeredPrefixStirlingWeight b.start *
          shiftedA11Factor b.start n delta A B C *
          connectedGaussianBlockWeight p := by rw [Finset.mul_sum]
    _ ≤ constrainedStirlingWeight n delta := hpointwise.trans hreindex
    _ ≤ constrainedProfileWeight n delta :=
      constrainedStirlingWeight_le n (by linarith [cert.delta_le_third])

end

end Erdos1165.AppendixA11A12OnePoint
