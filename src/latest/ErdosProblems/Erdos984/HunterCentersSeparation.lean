/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterHaar
import ErdosProblems.Erdos984.HunterTorusBlue

/-!
# Haar-random separated centers

This is the first half of Hunter's center-selection proposition.  Every
nontrivial second difference of a random finite tuple of torus points is
Haar-uniform.  A finite union bound therefore produces a tuple for which no
such second difference lies in the coordinate box of radius `4ρ`.
-/

open Set Function MeasureTheory Metric
open scoped ENNReal BigOperators

namespace Erdos984

noncomputable section

/-- The second-difference homomorphism attached to three center indices. -/
def centerSecondDifferenceHom {D ι : Type*} (i₀ i₁ i₂ : ι) :
    (ι → UnitAddTorus D) →+ UnitAddTorus D where
  toFun center := center i₀ - center i₁ - center i₁ + center i₂
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply]
    abel

@[simp] lemma centerSecondDifferenceHom_apply {D ι : Type*}
    (i₀ i₁ i₂ : ι) (center : ι → UnitAddTorus D) :
    centerSecondDifferenceHom i₀ i₁ i₂ center =
      center i₀ - center i₁ - center i₁ + center i₂ := rfl

lemma continuous_centerSecondDifferenceHom {D ι : Type*} (i₀ i₁ i₂ : ι) :
    Continuous (centerSecondDifferenceHom i₀ i₁ i₂ :
      (ι → UnitAddTorus D) → UnitAddTorus D) := by
  change Continuous (fun center : ι → UnitAddTorus D ↦
    center i₀ - center i₁ - center i₁ + center i₂)
  fun_prop

/-- Unless all three indices agree, their second-difference homomorphism is
onto.  In the exceptional pattern `i₀ = i₂ ≠ i₁`, divisibility of the torus
supplies a half of the requested target. -/
lemma centerSecondDifferenceHom_surjective {D ι : Type*}
    (i₀ i₁ i₂ : ι) (hnot : ¬(i₀ = i₁ ∧ i₁ = i₂)) :
    Surjective (centerSecondDifferenceHom i₀ i₁ i₂ :
      (ι → UnitAddTorus D) → UnitAddTorus D) := by
  classical
  intro x
  by_cases h01 : i₀ = i₁
  · have h12 : i₁ ≠ i₂ := by
      intro h
      exact hnot ⟨h01, h⟩
    have h02 : i₀ ≠ i₂ := fun h ↦ h12 (h01.symm.trans h)
    let center : ι → UnitAddTorus D := Function.update 0 i₂ x
    refine ⟨center, ?_⟩
    have hc0 : center i₀ = 0 := by simp [center, h02]
    have hc1 : center i₁ = 0 := by simp [center, h12]
    have hc2 : center i₂ = x := by simp [center]
    simp only [centerSecondDifferenceHom_apply, hc0, hc1, hc2]
    simp
  · by_cases h02 : i₀ = i₂
    · obtain ⟨y, hy⟩ := nsmul_surjective_unitAddTorus 2 (by omega) x
      let center : ι → UnitAddTorus D := Function.update 0 i₀ y
      refine ⟨center, ?_⟩
      subst i₂
      have hc0 : center i₀ = y := by simp [center]
      have hc1 : center i₁ = 0 := by simp [center, Ne.symm h01]
      simp only [centerSecondDifferenceHom_apply, hc0, hc1, sub_zero]
      simpa [two_nsmul] using hy
    · let center : ι → UnitAddTorus D := Function.update 0 i₀ x
      refine ⟨center, ?_⟩
      have hc0 : center i₀ = x := by simp [center]
      have hc1 : center i₁ = 0 := by simp [center, Ne.symm h01]
      have hc2 : center i₂ = 0 := by simp [center, Ne.symm h02]
      simp only [centerSecondDifferenceHom_apply, hc0, hc1, hc2]
      simp

/-- The product Haar volume on a finite family of unit tori is normalized. -/
lemma volume_centerSpace_univ {D ι : Type*} [Fintype D] [Fintype ι] :
    volume (Set.univ : Set (ι → UnitAddTorus D)) = 1 := by
  rw [show (Set.univ : Set (ι → UnitAddTorus D)) =
      Set.univ.pi (fun _ : ι => Set.univ) by ext; simp,
    MeasureTheory.volume_pi_pi]
  simp [volume_unitAddTorus_univ (D := D)]

/-- Every nontrivial center second difference is Haar-uniform. -/
lemma measurePreserving_centerSecondDifferenceHom
    {D ι : Type*} [Fintype D] [Fintype ι]
    (i₀ i₁ i₂ : ι) (hnot : ¬(i₀ = i₁ ∧ i₁ = i₂)) :
    MeasurePreserving (centerSecondDifferenceHom i₀ i₁ i₂ :
      (ι → UnitAddTorus D) →+ UnitAddTorus D) volume volume := by
  change MeasurePreserving (centerSecondDifferenceHom i₀ i₁ i₂ :
    (ι → UnitAddTorus D) →+ UnitAddTorus D)
    (Measure.pi fun _ : ι ↦ (volume : Measure (UnitAddTorus D))) volume
  let _ : Finite ι := Finite.of_fintype ι
  let _ : Countable ι := inferInstance
  let _ : ∀ _ : ι, SecondCountableTopology (UnitAddTorus D) :=
    fun _ ↦ inferInstance
  let _ : BorelSpace (ι → UnitAddTorus D) := Pi.borelSpace
  let _ : ∀ _ : ι, SigmaFinite (volume : Measure (UnitAddTorus D)) :=
    fun _ ↦ inferInstance
  let _ : ∀ _ : ι, Measure.IsAddHaarMeasure
      (volume : Measure (UnitAddTorus D)) :=
    fun _ ↦ inferInstance
  let _ : Measure.IsAddHaarMeasure
      (Measure.pi fun _ : ι ↦ (volume : Measure (UnitAddTorus D))) :=
    Measure.pi.isAddHaarMeasure _
  apply AddMonoidHom.measurePreserving
  · exact continuous_centerSecondDifferenceHom i₀ i₁ i₂
  · exact centerSecondDifferenceHom_surjective i₀ i₁ i₂ hnot
  · change volume (Set.univ : Set (ι → UnitAddTorus D)) =
      volume (Set.univ : Set (UnitAddTorus D))
    rw [volume_centerSpace_univ, volume_unitAddTorus_univ]

/-- Nontrivial ordered triples of center indices. -/
def nontrivialCenterTriples (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset (ι × ι × ι) :=
  Finset.univ.filter fun p ↦ ¬(p.1 = p.2.1 ∧ p.2.1 = p.2.2)

lemma card_nontrivialCenterTriples_le (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (nontrivialCenterTriples ι).card ≤ Fintype.card ι ^ 3 := by
  calc
    (nontrivialCenterTriples ι).card ≤ (Finset.univ : Finset (ι × ι × ι)).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card ι ^ 3 := by simp [pow_three]

/-- A finite tuple of centers satisfying Hunter's separation property exists
whenever the direct union-bound cost is below one. -/
lemma exists_torusCenterThreeSeparated
    {D ι : Type*} [Fintype D] [Nonempty D] [Fintype ι]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρhalf : 4 * ρ ≤ (1 : ℝ) / 2)
    (hsmall : (Fintype.card ι ^ 3 : ℝ≥0∞) *
      (ENNReal.ofReal (8 * ρ)) ^ Fintype.card D < 1) :
    ∃ center : ι → UnitAddTorus D, TorusCenterThreeSeparated center ρ := by
  classical
  let I := nontrivialCenterTriples ι
  let q : ℝ≥0∞ := (ENNReal.ofReal (8 * ρ)) ^ Fintype.card D
  let U : Set (ι → UnitAddTorus D) := ⋃ p ∈ I,
    centerSecondDifferenceHom p.1 p.2.1 p.2.2 ⁻¹'
      closedBall (0 : UnitAddTorus D) (4 * ρ)
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
    simpa only [show 2 * (4 * ρ) = 8 * ρ by ring] using hvol
  have hU : volume U ≤ (Fintype.card ι ^ 3 : ℝ≥0∞) * q := by
    calc
      volume U ≤ ∑ p ∈ I,
          volume (centerSecondDifferenceHom p.1 p.2.1 p.2.2 ⁻¹'
            closedBall (0 : UnitAddTorus D) (4 * ρ)) := by
        exact MeasureTheory.measure_biUnion_finset_le I _
      _ = ∑ _p ∈ I, q := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hbad p hp
      _ = (I.card : ℕ) • q := by simp
      _ = (I.card : ℝ≥0∞) * q := by rw [nsmul_eq_mul]
      _ ≤ (Fintype.card ι ^ 3 : ℝ≥0∞) * q := by
        gcongr
        exact_mod_cast card_nontrivialCenterTriples_le ι
  have hUlt : volume U < 1 := hU.trans_lt (by simpa [q] using hsmall)
  have hne : U ≠ Set.univ := by
    intro hEq
    rw [hEq, volume_centerSpace_univ] at hUlt
    exact (lt_self_iff_false 1).mp hUlt
  obtain ⟨center, hcenter⟩ := (Set.ne_univ_iff_exists_notMem U).mp hne
  refine ⟨center, ?_⟩
  intro i₀ i₁ i₂ hclose
  by_contra hnot
  have hp : (i₀, i₁, i₂) ∈ I := by
    simpa only [I, nontrivialCenterTriples, Finset.mem_filter,
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
