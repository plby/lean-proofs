import ErdosProblems.Erdos788.FiniteDistribution
import ErdosProblems.Erdos788.UpperGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The checked extractor-to-palette interface

The reconstruction module will construct `LinearExtractorFamily`.  This file
proves, without any asymptotics, that its total-variation guarantee implies
the exact set-image expansion required by `UpperGraph` and hence the
union-of-kernels palette theorem.
-/

namespace Erdos788

open scoped BigOperators

@[simp]
theorem fintypeCard_ffVec (p k : ℕ) [NeZero p] :
    Fintype.card (FFVec p k) = p ^ k := by
  simp [FFVec, ZMod.card]

/-- A finite indexed family of surjective linear maps satisfying the strong
average total-variation guarantee used in the paper. -/
structure LinearExtractorFamily (p r d s : ℕ) [Fact p.Prime] where
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedDecidableEq : DecidableEq Seed]
  [seedNonempty : Nonempty Seed]
  card_seed_le : Fintype.card Seed ≤ p ^ d
  map : Seed → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r
  surjective : ∀ y, Function.Surjective (map y)
  extracts : ∀ P : FinDist (FFVec p (2 * r)),
    P.PointBound (p ^ (r + s)) →
      (Fintype.card Seed : ℝ)⁻¹ *
          ∑ y : Seed, (P.map (map y)).tv (FinDist.uniform (FFVec p r)) <
        1 / 3

attribute [instance] LinearExtractorFamily.seedFintype
  LinearExtractorFamily.seedDecidableEq LinearExtractorFamily.seedNonempty

theorem one_third_le_one_sub_card_div_of_antipodal_bound
    {p r t : ℕ} (hp : 2 < p) (hr : 0 < r)
    (hanti : 2 * t ≤ p ^ r + 1) :
    (1 / 3 : ℝ) ≤ 1 - (t : ℝ) / (p ^ r : ℕ) := by
  have hp0 : 0 < p := by omega
  have hr1 : 1 ≤ r := hr
  have hp_le_pow : p ≤ p ^ r := by
    simpa only [pow_one] using! Nat.pow_le_pow_right hp0 hr1
  have hpow3 : 3 ≤ p ^ r := (by omega : 3 ≤ p).trans hp_le_pow
  have hthree : 3 * t ≤ 2 * p ^ r := by omega
  have hpowR : (0 : ℝ) < (p ^ r : ℕ) := by
    exact_mod_cast pow_pos hp0 r
  have hthreeR : (3 : ℝ) * t ≤ 2 * (p ^ r : ℕ) := by
    exact_mod_cast hthree
  have hratio : (t : ℝ) / (p ^ r : ℕ) ≤ 2 / 3 := by
    apply (div_le_iff₀ hpowR).2
    nlinarith
  nlinarith

/-- The strong average extractor guarantee forces the denominator-free image
expansion property used by the group palette argument. -/
theorem extractorFamily_setImageExpanding
    {p r d s : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (E : LinearExtractorFamily p r d s) :
    SetImageExpanding p r s (Finset.univ : Finset E.Seed) E.map := by
  intro A hlarge
  have hp0 : 0 < p := by omega
  have hthreshold : 0 < p ^ (r + s) := pow_pos hp0 _
  have hAcard : 0 < A.card := hthreshold.trans_le hlarge
  have hA : A.Nonempty := Finset.card_pos.mp hAcard
  by_cases hex : ∃ y ∈ (Finset.univ : Finset E.Seed),
      p ^ r + 1 < 2 * (A.image (E.map y)).card
  · exact hex
  · have hsmall : ∀ y : E.Seed,
        2 * (A.image (E.map y)).card ≤ p ^ r + 1 := by
      intro y
      exact Nat.le_of_not_gt fun h ↦ hex ⟨y, Finset.mem_univ y, h⟩
    let P : FinDist (FFVec p (2 * r)) := FinDist.uniformOn A hA
    have hpoint : P.PointBound (p ^ (r + s)) := by
      apply FinDist.pointBound_mono hthreshold hlarge
      exact FinDist.uniformOn_pointBound A hA
    have hseed : ∀ y : E.Seed, (1 / 3 : ℝ) ≤
        (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
      intro y
      let T : Finset (FFVec p r) := A.image (E.map y)
      have hsupport : ∀ z, z ∉ T → (P.map (E.map y)).mass z = 0 := by
        intro z hz
        exact FinDist.map_uniformOn_mass_eq_zero_of_notMem_image
          A hA (E.map y) hz
      have htv := FinDist.tv_uniform_ge_one_sub_support
        (P.map (E.map y)) T hsupport
      have hthird : (1 / 3 : ℝ) ≤
          1 - (T.card : ℝ) / (p ^ r : ℕ) :=
        one_third_le_one_sub_card_div_of_antipodal_bound hp hr (hsmall y)
      have hcard : Fintype.card (FFVec p r) = p ^ r :=
        fintypeCard_ffVec p r
      rw [hcard] at htv
      exact hthird.trans htv
    have hsum : (Fintype.card E.Seed : ℝ) * (1 / 3 : ℝ) ≤
        ∑ y : E.Seed, (P.map (E.map y)).tv
          (FinDist.uniform (FFVec p r)) := by
      simpa using! Finset.sum_le_sum fun y (_hy : y ∈
        (Finset.univ : Finset E.Seed)) ↦ hseed y
    have hcardpos : (0 : ℝ) < Fintype.card E.Seed := by
      exact_mod_cast Fintype.card_pos
    have havg : (1 / 3 : ℝ) ≤
        (Fintype.card E.Seed : ℝ)⁻¹ *
          ∑ y : E.Seed, (P.map (E.map y)).tv
            (FinDist.uniform (FFVec p r)) := by
      calc
        (1 / 3 : ℝ) = (Fintype.card E.Seed : ℝ)⁻¹ *
            ((Fintype.card E.Seed : ℝ) * (1 / 3 : ℝ)) := by
              field_simp
        _ ≤ (Fintype.card E.Seed : ℝ)⁻¹ *
            ∑ y : E.Seed, (P.map (E.map y)).tv
              (FinDist.uniform (FFVec p r)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcardpos.le)
    exact (not_lt_of_ge havg (E.extracts P hpoint)).elim

/-- Proposition 5.1 of the paper, obtained directly from a checked linear
extractor family. -/
theorem kernelPalette_of_linearExtractorFamily
    {p r d s : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (E : LinearExtractorFamily p r d s) :
    ∃ S : Finset (FFVec p (2 * r)),
      S.card ≤ p ^ (r + d) ∧
        (groupSumGraph S).indepNum < p ^ (r + s) := by
  apply exists_kernelPalette_of_setImageExpanding p r hp
    (Finset.univ : Finset E.Seed) E.map
  · simpa using! E.card_seed_le
  · intro y _hy
    exact E.surjective y
  · exact extractorFamily_setImageExpanding hp hr E

end Erdos788
