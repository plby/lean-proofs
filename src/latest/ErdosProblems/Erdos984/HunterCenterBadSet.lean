/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterCenterNumerics
import ErdosProblems.Erdos984.HunterCentersSeparation

/-!
# The bad set for Hunter center separation

We expose the finite union used in the center-separation argument so that it
can be combined with the orbit-hitting bad sets in one probability space.
-/

open Set Function MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Erdos984

noncomputable section

/-- Center tuples having a nontrivial second difference in the coordinate
box of radius `4ρ`. -/
def torusCenterSeparationBadSet
    {D ι : Type*} [Fintype D] [Fintype ι] [DecidableEq ι] (ρ : ℝ) :
    Set (ι → UnitAddTorus D) :=
  ⋃ p ∈ nontrivialCenterTriples ι,
    centerSecondDifferenceHom p.1 p.2.1 p.2.2 ⁻¹'
      closedBall (0 : UnitAddTorus D) (4 * ρ)

lemma measurableSet_torusCenterSeparationBadSet
    {D ι : Type*} [Fintype D] [Fintype ι] [DecidableEq ι] (ρ : ℝ) :
    MeasurableSet (torusCenterSeparationBadSet (D := D) (ι := ι) ρ) := by
  unfold torusCenterSeparationBadSet
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro _hp
  exact measurableSet_closedBall.preimage
    (continuous_centerSecondDifferenceHom p.1 p.2.1 p.2.2).measurable

lemma volume_torusCenterSeparationBadSet_le
    {D ι : Type*} [Fintype D] [Nonempty D] [Fintype ι] [DecidableEq ι]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρhalf : 4 * ρ ≤ (1 : ℝ) / 2) :
    volume (torusCenterSeparationBadSet (D := D) (ι := ι) ρ) ≤
      (Fintype.card ι ^ 3 : ENNReal) *
        (ENNReal.ofReal (8 * ρ)) ^ Fintype.card D := by
  let I := nontrivialCenterTriples ι
  let q : ENNReal := (ENNReal.ofReal (8 * ρ)) ^ Fintype.card D
  have hbad (p : ι × ι × ι) (hp : p ∈ I) :
      volume (centerSecondDifferenceHom p.1 p.2.1 p.2.2 ⁻¹'
        closedBall (0 : UnitAddTorus D) (4 * ρ)) = q := by
    have hnot : ¬(p.1 = p.2.1 ∧ p.2.1 = p.2.2) := by
      simpa only [I, nontrivialCenterTriples, Finset.mem_filter,
        Finset.mem_univ, true_and] using hp
    rw [(measurePreserving_centerSecondDifferenceHom
      p.1 p.2.1 p.2.2 hnot).measure_preimage
        measurableSet_closedBall.nullMeasurableSet]
    have hvol := volume_unitAddTorus_closedBall (D := D)
      (mul_nonneg (by norm_num) hρ0) hρhalf
    simpa only [q, show 2 * (4 * ρ) = 8 * ρ by ring] using hvol
  calc
    volume (torusCenterSeparationBadSet (D := D) (ι := ι) ρ) ≤
        ∑ p ∈ I, volume (centerSecondDifferenceHom p.1 p.2.1 p.2.2 ⁻¹'
          closedBall (0 : UnitAddTorus D) (4 * ρ)) := by
      simpa only [torusCenterSeparationBadSet, I] using
        MeasureTheory.measure_biUnion_finset_le I
          (fun p : ι × ι × ι ↦
            centerSecondDifferenceHom p.1 p.2.1 p.2.2 ⁻¹'
              closedBall (0 : UnitAddTorus D) (4 * ρ))
    _ = ∑ _p ∈ I, q := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hbad p hp
    _ = (I.card : ℕ) • q := by simp
    _ = (I.card : ENNReal) * q := by rw [nsmul_eq_mul]
    _ ≤ (Fintype.card ι ^ 3 : ENNReal) * q := by
      gcongr
      exact_mod_cast card_nontrivialCenterTriples_le ι
    _ = (Fintype.card ι ^ 3 : ENNReal) *
        (ENNReal.ofReal (8 * ρ)) ^ Fintype.card D := rfl

lemma torusCenterThreeSeparated_of_not_mem_badSet
    {D ι : Type*} [Fintype D] [Nonempty D] [Fintype ι] [DecidableEq ι]
    {ρ : ℝ} {center : ι → UnitAddTorus D}
    (hcenter : center ∉ torusCenterSeparationBadSet (D := D) (ι := ι) ρ) :
    TorusCenterThreeSeparated center ρ := by
  intro i₀ i₁ i₂ hclose
  by_contra hnot
  have hp : (i₀, i₁, i₂) ∈ nontrivialCenterTriples ι := by
    simpa only [nontrivialCenterTriples, Finset.mem_filter,
      Finset.mem_univ, true_and, Prod.fst, Prod.snd] using hnot
  apply hcenter
  apply Set.mem_iUnion_of_mem (i₀, i₁, i₂)
  apply Set.mem_iUnion_of_mem hp
  change centerSecondDifferenceHom i₀ i₁ i₂ center ∈
    closedBall (0 : UnitAddTorus D) (4 * ρ)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonempty
    (centerSecondDifferenceHom i₀ i₁ i₂ center)).2 hclose

end

end Erdos984
