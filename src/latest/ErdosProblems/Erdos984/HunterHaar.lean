/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterTorus
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Avoiding small multiples on a finite-dimensional torus

The blue-progression half of Hunter's construction needs a point `θ` whose
first `N - 1` positive multiples avoid a small ball.  Haar measure gives this
as soon as `N` times the ball volume is below one.  This file proves that
finite union-bound argument, including the exact volume of a sup-norm ball in
the unit torus.
-/

open Set Function MeasureTheory Metric
open scoped ENNReal BigOperators

namespace Erdos984

noncomputable section

/-- Multiplication by a positive natural number is onto on a unit torus. -/
lemma nsmul_surjective_unitAddTorus {D : Type*} (d : ℕ) (hd : 0 < d) :
    Surjective (nsmulAddMonoidHom d : UnitAddTorus D →+ UnitAddTorus D) := by
  intro x
  let y : UnitAddTorus D := fun i =>
    ((centeredCircleLift (x i) / (d : ℝ) : ℝ) : UnitAddCircle)
  refine ⟨y, ?_⟩
  ext i
  change d • ((centeredCircleLift (x i) / (d : ℝ) : ℝ) : UnitAddCircle) = x i
  rw [← AddCircle.coe_nsmul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [nsmul_eq_mul, mul_div_cancel₀ _ hd0]
  exact coe_centeredCircleLift (x i)

/-- A positive natural multiplication map preserves Haar volume on a finite
unit torus. -/
lemma measurePreserving_nsmul_unitAddTorus {D : Type*} [Fintype D]
    (d : ℕ) (hd : 0 < d) :
    MeasurePreserving
      (nsmulAddMonoidHom d : UnitAddTorus D →+ UnitAddTorus D)
      volume volume := by
  apply AddMonoidHom.measurePreserving
  · exact continuous_nsmul d
  · exact nsmul_surjective_unitAddTorus d hd
  · rfl

/-- The sup-norm ball of radius `τ ≤ 1/2` in a `D`-dimensional unit torus
has volume `(2τ)^D`. -/
lemma volume_unitAddTorus_closedBall {D : Type*} [Fintype D] {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτhalf : τ ≤ (1 : ℝ) / 2) :
    volume (closedBall (0 : UnitAddTorus D) τ) =
      (ENNReal.ofReal (2 * τ)) ^ Fintype.card D := by
  rw [MeasureTheory.volume_pi_closedBall _ hτ0]
  simp_rw [AddCircle.volume_closedBall]
  have hmin : min (1 : ℝ) (2 * τ) = 2 * τ := min_eq_right (by linarith)
  simp only [hmin, Finset.prod_const, Finset.card_univ]

/-- Haar volume of a finite product of unit circles is normalized to one. -/
lemma volume_unitAddTorus_univ {D : Type*} [Fintype D] :
    volume (Set.univ : Set (UnitAddTorus D)) = 1 := by
  rw [show (Set.univ : Set (UnitAddTorus D)) =
      Set.univ.pi (fun _ : D => Set.univ) by ext; simp,
    MeasureTheory.volume_pi_pi]
  simp

/-- The finite union of small-multiple events. -/
def smallMultipleBadSet {D : Type*} [Fintype D] [Nonempty D]
    (N : ℕ) (τ : ℝ) : Set (UnitAddTorus D) :=
  ⋃ d ∈ (Finset.range N).erase 0,
    (fun θ : UnitAddTorus D => d • θ) ⁻¹' closedBall 0 τ

/-- Direct union-bound estimate for the small-positive-multiple set. -/
lemma volume_smallMultipleBadSet_le
    {D : Type*} [Fintype D] [Nonempty D] (N : ℕ) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτhalf : τ ≤ (1 : ℝ) / 2) :
    volume (smallMultipleBadSet (D := D) N τ) ≤
      (N : ℝ≥0∞) * (ENNReal.ofReal (2 * τ)) ^ Fintype.card D := by
  let I := (Finset.range N).erase 0
  let q : ℝ≥0∞ := (ENNReal.ofReal (2 * τ)) ^ Fintype.card D
  have hbad (d : ℕ) (hd : d ∈ I) :
      volume ((fun θ : UnitAddTorus D => d • θ) ⁻¹' closedBall 0 τ) = q := by
    have hdpos : 0 < d := by
      have hdne : d ≠ 0 := (Finset.mem_erase.mp hd).1
      omega
    have hpre := (measurePreserving_nsmul_unitAddTorus (D := D) d hdpos).measure_preimage
      (s := closedBall (0 : UnitAddTorus D) τ)
      measurableSet_closedBall.nullMeasurableSet
    rw [show (fun θ : UnitAddTorus D => d • θ) =
        (nsmulAddMonoidHom d : UnitAddTorus D →+ UnitAddTorus D) from rfl]
    rw [hpre]
    exact volume_unitAddTorus_closedBall (D := D) hτ0 hτhalf
  calc
    volume (smallMultipleBadSet (D := D) N τ) ≤ ∑ d ∈ I,
        volume ((fun θ : UnitAddTorus D => d • θ) ⁻¹' closedBall 0 τ) := by
      exact MeasureTheory.measure_biUnion_finset_le I _
    _ = ∑ _d ∈ I, q := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hbad d hd
    _ = (I.card : ℕ) • q := by simp
    _ = (I.card : ℝ≥0∞) * q := by rw [nsmul_eq_mul]
    _ ≤ (N : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast
        ((Finset.card_erase_le (s := Finset.range N) (a := 0)).trans (by simp))

/-- If the union-bound cost is below one, some torus point has no positive
multiple `d < N` in the closed ball of radius `τ`. -/
lemma exists_torus_avoiding_small_multiples
    {D : Type*} [Fintype D] [Nonempty D] (N : ℕ) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτhalf : τ ≤ (1 : ℝ) / 2)
    (hsmall : (N : ℝ≥0∞) *
      (ENNReal.ofReal (2 * τ)) ^ Fintype.card D < 1) :
    ∃ θ : UnitAddTorus D, ∀ d : ℕ, 0 < d → d < N → τ < ‖d • θ‖ := by
  let I := (Finset.range N).erase 0
  let q : ℝ≥0∞ := (ENNReal.ofReal (2 * τ)) ^ Fintype.card D
  let U : Set (UnitAddTorus D) :=
    ⋃ d ∈ I, (fun θ : UnitAddTorus D => d • θ) ⁻¹' closedBall 0 τ
  have hbad (d : ℕ) (hd : d ∈ I) :
      volume ((fun θ : UnitAddTorus D => d • θ) ⁻¹' closedBall 0 τ) = q := by
    have hdpos : 0 < d := by
      have hdne : d ≠ 0 := (Finset.mem_erase.mp hd).1
      omega
    have hpre := (measurePreserving_nsmul_unitAddTorus (D := D) d hdpos).measure_preimage
      (s := closedBall (0 : UnitAddTorus D) τ)
      measurableSet_closedBall.nullMeasurableSet
    rw [show (fun θ : UnitAddTorus D => d • θ) =
        (nsmulAddMonoidHom d : UnitAddTorus D →+ UnitAddTorus D) from rfl]
    rw [hpre]
    exact volume_unitAddTorus_closedBall (D := D) hτ0 hτhalf
  have hU : volume U ≤ (N : ℝ≥0∞) * q := by
    calc
      volume U ≤ ∑ d ∈ I,
          volume ((fun θ : UnitAddTorus D => d • θ) ⁻¹' closedBall 0 τ) := by
        exact MeasureTheory.measure_biUnion_finset_le I _
      _ = ∑ _d ∈ I, q := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hbad d hd
      _ = (I.card : ℕ) • q := by simp
      _ = (I.card : ℝ≥0∞) * q := by rw [nsmul_eq_mul]
      _ ≤ (N : ℝ≥0∞) * q := by
        gcongr
        exact_mod_cast
          ((Finset.card_erase_le (s := Finset.range N) (a := 0)).trans (by simp))
  have hUlt : volume U < 1 := hU.trans_lt (by simpa [q] using hsmall)
  have hne : U ≠ Set.univ := by
    intro hEq
    rw [hEq, volume_unitAddTorus_univ] at hUlt
    exact (lt_self_iff_false 1).mp hUlt
  obtain ⟨θ, hθ⟩ := (Set.ne_univ_iff_exists_notMem U).mp hne
  refine ⟨θ, ?_⟩
  intro d hd hdN
  have hdI : d ∈ I := by
    simp only [I, Finset.mem_erase, Finset.mem_range]
    exact ⟨hd.ne', hdN⟩
  have hnot : d • θ ∉ closedBall (0 : UnitAddTorus D) τ := by
    intro hmem
    apply hθ
    exact Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hdI hmem)
  rw [Metric.mem_closedBall, dist_zero_right] at hnot
  exact lt_of_not_ge hnot

/-- The form consumed by the annular blue-set proof: a numerical width
below `τ²` is below every relevant centered-lift squared norm. -/
lemma exists_torus_with_step_squaredNorm_gt
    {D : Type*} [Fintype D] [Nonempty D] (N : ℕ) {τ width : ℝ}
    (hτ0 : 0 ≤ τ) (hτhalf : τ ≤ (1 : ℝ) / 2)
    (hsmall : (N : ℝ≥0∞) *
      (ENNReal.ofReal (2 * τ)) ^ Fintype.card D < 1)
    (hwidth : width < τ ^ 2) :
    ∃ θ : UnitAddTorus D, ∀ d : ℕ, 0 < d → d < N →
      width < squaredNorm (centeredTorusLift (d • θ)) := by
  obtain ⟨θ, hθ⟩ := exists_torus_avoiding_small_multiples N
    hτ0 hτhalf hsmall
  refine ⟨θ, fun d hd hdN ↦ ?_⟩
  exact hwidth.trans
    (sq_lt_squaredNorm_centeredTorusLift_of_lt_norm hτ0 (hθ d hd hdN))

end

end Erdos984
