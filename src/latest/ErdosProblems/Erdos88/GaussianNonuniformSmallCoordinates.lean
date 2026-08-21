import ErdosProblems.Erdos88.GaussianHypercontractiveTail

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

lemma exists_subset_sum_between_one_two_public
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (S : Finset ι)
    {c : ℝ} (hc : 0 < c) (hsmall : ∀ i ∈ S, w i < c)
    (hsum : c ≤ ∑ i ∈ S, w i) :
    ∃ T ⊆ S, c ≤ ∑ i ∈ T, w i ∧ ∑ i ∈ T, w i < 2 * c := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty] at hsum
      linarith
  | @insert a S ha ih =>
      by_cases hSc : c ≤ ∑ i ∈ S, w i
      · obtain ⟨T, hTS, hTc, hTlt⟩ := ih
          (fun i hi ↦ hsmall i (Finset.mem_insert_of_mem hi)) hSc
        exact ⟨T, hTS.trans (Finset.subset_insert a S), hTc, hTlt⟩
      · have hSlt : ∑ i ∈ S, w i < c := lt_of_not_ge hSc
        have halt : w a < c := hsmall a (Finset.mem_insert_self a S)
        refine ⟨insert a S, Finset.Subset.rfl, hsum, ?_⟩
        rw [Finset.sum_insert ha]
        linarith

lemma partialVariance_compl_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι) :
    partialVariance a lam (Finset.univ \ S) + partialVariance a lam S =
      partialVariance a lam Finset.univ := by
  unfold partialVariance
  exact Finset.sum_sdiff (Finset.subset_univ S)

lemma sum_fin_five (f : Fin 5 → ℝ) :
    ∑ h : Fin 5, f h = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
  ring

/-- Five exhaustive variance blocks in the no-influential-coordinate case.
Every block is nonzero and has variance at most one half, while every
complement has variance at least one half. -/
lemma exists_five_variance_blocks_of_small_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ)
    (hsum : partialVariance a lam Finset.univ = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 10) :
    ∃ J : Fin 5 → Finset ι,
      (∀ z, diagonalPartialSum a lam Finset.univ z =
        ∑ h : Fin 5, diagonalPartialSum a lam (J h) z) ∧
      (∀ h, 0 < partialVariance a lam (J h)) ∧
      (∀ h, partialVariance a lam (J h) ≤ 1 / 2) ∧
      ∀ h, 1 / 2 ≤ partialVariance a lam (Finset.univ \ J h) := by
  classical
  let w : ι → ℝ := fun i ↦ coordinateVariance (a i) (lam i)
  let c : ℝ := 1 / 8
  have hc : 0 < c := by norm_num [c]
  have hwsmall : ∀ i ∈ (Finset.univ : Finset ι), w i < c := by
    intro i hi
    dsimp only [w, c]
    linarith [hsmall i]
  have hsumU : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    simpa only [partialVariance, w] using hsum
  obtain ⟨B0, hB0, hB0lo, hB0hi⟩ :=
    exists_subset_sum_between_one_two_public w Finset.univ hc hwsmall
      (by rw [hsumU]; norm_num [c])
  let R1 := Finset.univ \ B0
  have hR1 : ∑ i ∈ R1, w i = 1 - ∑ i ∈ B0, w i := by
    simpa only [R1, hsumU] using Finset.sum_sdiff_eq_sub (f := w) hB0
  have hR1lo : c ≤ ∑ i ∈ R1, w i := by
    dsimp only [c] at hB0hi ⊢
    linarith
  have hwsmall1 : ∀ i ∈ R1, w i < c := fun i hi ↦
    hwsmall i (Finset.mem_univ i)
  obtain ⟨B1, hB1, hB1lo, hB1hi⟩ :=
    exists_subset_sum_between_one_two_public w R1 hc hwsmall1 hR1lo
  let R2 := R1 \ B1
  have hR2 : ∑ i ∈ R2, w i = (∑ i ∈ R1, w i) - ∑ i ∈ B1, w i := by
    exact Finset.sum_sdiff_eq_sub (f := w) hB1
  have hR2lo : c ≤ ∑ i ∈ R2, w i := by
    dsimp only [c] at hB0hi hB1hi ⊢
    linarith
  have hwsmall2 : ∀ i ∈ R2, w i < c := fun i hi ↦
    hwsmall1 i (Finset.sdiff_subset hi)
  obtain ⟨B2, hB2, hB2lo, hB2hi⟩ :=
    exists_subset_sum_between_one_two_public w R2 hc hwsmall2 hR2lo
  let R3 := R2 \ B2
  have hR3 : ∑ i ∈ R3, w i = (∑ i ∈ R2, w i) - ∑ i ∈ B2, w i := by
    exact Finset.sum_sdiff_eq_sub (f := w) hB2
  have hR3lo : c ≤ ∑ i ∈ R3, w i := by
    dsimp only [c] at hB0hi hB1hi hB2hi ⊢
    linarith
  have hwsmall3 : ∀ i ∈ R3, w i < c := fun i hi ↦
    hwsmall2 i (Finset.sdiff_subset hi)
  obtain ⟨B3, hB3, hB3lo, hB3hi⟩ :=
    exists_subset_sum_between_one_two_public w R3 hc hwsmall3 hR3lo
  let R4 := R3 \ B3
  have hR4 : ∑ i ∈ R4, w i = (∑ i ∈ R3, w i) - ∑ i ∈ B3, w i := by
    exact Finset.sum_sdiff_eq_sub (f := w) hB3
  have hR4pos : 0 < ∑ i ∈ R4, w i := by
    dsimp only [c] at hB0hi hB1hi hB2hi hB3hi
    linarith
  have hR4hi : ∑ i ∈ R4, w i ≤ 1 / 2 := by
    dsimp only [c] at hB0lo hB1lo hB2lo hB3lo
    linarith
  let J : Fin 5 → Finset ι :=
    Fin.cases B0 (Fin.cases B1 (Fin.cases B2 (Fin.cases B3 (fun _ ↦ R4))))
  have hJpos : ∀ h, 0 < partialVariance a lam (J h) := by
    intro h
    fin_cases h
    · change 0 < ∑ i ∈ B0, w i
      exact hc.trans_le hB0lo
    · change 0 < ∑ i ∈ B1, w i
      exact hc.trans_le hB1lo
    · change 0 < ∑ i ∈ B2, w i
      exact hc.trans_le hB2lo
    · change 0 < ∑ i ∈ B3, w i
      exact hc.trans_le hB3lo
    · change 0 < ∑ i ∈ R4, w i
      exact hR4pos
  have hJle : ∀ h, partialVariance a lam (J h) ≤ 1 / 2 := by
    intro h
    fin_cases h
    · change ∑ i ∈ B0, w i ≤ 1 / 2
      dsimp only [c] at hB0hi
      linarith
    · change ∑ i ∈ B1, w i ≤ 1 / 2
      dsimp only [c] at hB1hi
      linarith
    · change ∑ i ∈ B2, w i ≤ 1 / 2
      dsimp only [c] at hB2hi
      linarith
    · change ∑ i ∈ B3, w i ≤ 1 / 2
      dsimp only [c] at hB3hi
      linarith
    · change ∑ i ∈ R4, w i ≤ 1 / 2
      exact hR4hi
  refine ⟨J, ?_, hJpos, hJle, ?_⟩
  · intro z
    rw [sum_fin_five]
    simp only [J, Fin.cases_zero]
    have hz0 := Finset.sum_sdiff (f := fun i ↦
      centeredCoordinatePolynomial (a i) (lam i) (z i)) hB0
    have hz1 := Finset.sum_sdiff (f := fun i ↦
      centeredCoordinatePolynomial (a i) (lam i) (z i)) hB1
    have hz2 := Finset.sum_sdiff (f := fun i ↦
      centeredCoordinatePolynomial (a i) (lam i) (z i)) hB2
    have hz3 := Finset.sum_sdiff (f := fun i ↦
      centeredCoordinatePolynomial (a i) (lam i) (z i)) hB3
    change (∑ i ∈ (Finset.univ : Finset ι),
      centeredCoordinatePolynomial (a i) (lam i) (z i)) =
        (∑ i ∈ B0, centeredCoordinatePolynomial (a i) (lam i) (z i)) +
        (∑ i ∈ B1, centeredCoordinatePolynomial (a i) (lam i) (z i)) +
        (∑ i ∈ B2, centeredCoordinatePolynomial (a i) (lam i) (z i)) +
        (∑ i ∈ B3, centeredCoordinatePolynomial (a i) (lam i) (z i)) +
        ∑ i ∈ R4, centeredCoordinatePolynomial (a i) (lam i) (z i)
    change (∑ i ∈ R1, _) + (∑ i ∈ B0, _) = _ at hz0
    change (∑ i ∈ R2, _) + (∑ i ∈ B1, _) = _ at hz1
    change (∑ i ∈ R3, _) + (∑ i ∈ B2, _) = _ at hz2
    change (∑ i ∈ R4, _) + (∑ i ∈ B3, _) = _ at hz3
    linarith
  · intro h
    have hcomp := partialVariance_compl_add a lam (J h)
    rw [hsum] at hcomp
    linarith [hJle h]

lemma diagonalPartialSum_compl_smallBall_le_four_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 10)
    (hVhalf : 1 / 2 ≤ partialVariance a lam (Finset.univ \ S))
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam (Finset.univ \ S))) eps x ≤
      4 * eps := by
  have hVpos : 0 < partialVariance a lam (Finset.univ \ S) := by linarith
  have hcoord : ∀ i ∈ Finset.univ \ S,
      coordinateVariance (a i) (lam i) ≤
        partialVariance a lam (Finset.univ \ S) / 4 := by
    intro i hi
    linarith [hsmall i]
  have hraw := smallBall_diagonalPartialSum_le_of_small_coordinates
    a lam (Finset.univ \ S) heps hVpos hcoord x
  have hsqrt : 1 / 2 ≤ Real.sqrt (partialVariance a lam (Finset.univ \ S)) := by
    rw [Real.le_sqrt (by norm_num) hVpos.le]
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (partialVariance a lam (Finset.univ \ S)) :=
    Real.sqrt_pos.2 hVpos
  calc
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam (Finset.univ \ S))) eps x ≤
        2 * eps / Real.sqrt (partialVariance a lam (Finset.univ \ S)) := hraw
    _ ≤ 4 * eps := by
      apply (div_le_iff₀ hsqrtPos).2
      nlinarith

/-- The five-block estimate specialized to the normalized
no-influential-coordinate case. -/
lemma diagonalPartialSum_univ_smallBall_le_far_of_small_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ)
    (hsum : partialVariance a lam Finset.univ = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 10)
    {eps x : ℝ} (heps : 0 ≤ eps) (hx : eps < |x|) :
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam Finset.univ)) eps x ≤
      40 * eps * Real.exp (-((|x| - eps) / 5) / 4 + 1 / 8) := by
  obtain ⟨J, hdecomp, hJpos, hJle, hcomp⟩ :=
    exists_five_variance_blocks_of_small_coordinates a lam hsum hsmall
  have hraw := diagonalPartialSum_smallBall_le_of_five_blocks
    a lam J hdecomp hJpos (fun h ↦ (hJle h).trans (by norm_num))
    heps hx (mul_nonneg (by norm_num) heps)
    (fun h y ↦ diagonalPartialSum_compl_smallBall_le_four_mul
      a lam (J h) hsmall (hcomp h) heps y)
  unfold Erdos88.Esseen.smallBall
  rw [measureReal_def] at hraw ⊢
  rw [Measure.map_apply (continuous_diagonalPartialSum a lam Finset.univ).measurable
      measurableSet_Icc]
  convert hraw using 1
  · rfl
  · ring

/-- An explicit nonuniform small-ball estimate for the normalized diagonal
sum when no coordinate carries more than one tenth of the variance. -/
theorem diagonalPartialSum_univ_smallBall_le_nonuniform_of_small_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ)
    (hsum : partialVariance a lam Finset.univ = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 10)
    {eps : ℝ} (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam Finset.univ)) eps x ≤
      (eps / (1 / 10000)) * Real.exp (-(1 / 10000) * |x|) := by
  have hVpos : 0 < partialVariance a lam Finset.univ := by rw [hsum]; norm_num
  have hcoord : ∀ i ∈ (Finset.univ : Finset ι),
      coordinateVariance (a i) (lam i) ≤
        partialVariance a lam Finset.univ / 4 := by
    intro i hi
    rw [hsum]
    linarith [hsmall i]
  by_cases hx : |x| ≤ 1000
  · have hraw := smallBall_diagonalPartialSum_le_of_small_coordinates
      a lam Finset.univ heps hVpos hcoord x
    rw [hsum, Real.sqrt_one, div_one] at hraw
    have hexpLower : 9 / 10 ≤ Real.exp (-(1 / 10000) * |x|) := by
      have hadd := Real.add_one_le_exp (-(1 / 10000) * |x|)
      nlinarith
    calc
      Erdos88.Esseen.smallBall
          ((Measure.pi fun _ : ι ↦ standardGaussian).map
            (diagonalPartialSum a lam Finset.univ)) eps x ≤ 2 * eps := hraw
      _ ≤ (eps / (1 / 10000)) * Real.exp (-(1 / 10000) * |x|) := by
        have hexpPos : 0 < Real.exp (-(1 / 10000) * |x|) := Real.exp_pos _
        nlinarith
  · have hxFar : eps < |x| := by
      have : 1000 < |x| := lt_of_not_ge hx
      linarith
    have hraw := diagonalPartialSum_univ_smallBall_le_far_of_small_coordinates
      a lam hsum hsmall heps hxFar
    have hExpArg :
        -((|x| - eps) / 5) / 4 + 1 / 8 ≤ -(1 / 10000) * |x| := by
      have hx' : 1000 < |x| := lt_of_not_ge hx
      linarith
    have hExp := Real.exp_le_exp.mpr hExpArg
    calc
      Erdos88.Esseen.smallBall
          ((Measure.pi fun _ : ι ↦ standardGaussian).map
            (diagonalPartialSum a lam Finset.univ)) eps x ≤
          40 * eps * Real.exp (-((|x| - eps) / 5) / 4 + 1 / 8) := hraw
      _ ≤ 40 * eps * Real.exp (-(1 / 10000) * |x|) := by gcongr
      _ ≤ (eps / (1 / 10000)) * Real.exp (-(1 / 10000) * |x|) := by
        have hexpPos : 0 < Real.exp (-(1 / 10000) * |x|) := Real.exp_pos _
        nlinarith

lemma map_diagonalPartialSum_univ_eq_diagonalCenteredLaw
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a lam : ι → ℝ) :
    (Measure.pi fun _ : ι ↦ standardGaussian).map
        (diagonalPartialSum a lam Finset.univ) =
      diagonalCenteredLaw a lam := by
  rw [diagonalCenteredLaw_eq_map_diagonalCenteredSum]
  congr 1

/-- Law-level no-influential-coordinate branch of the normalized
nonuniform Gaussian small-ball theorem. -/
theorem smallBall_diagonalCenteredLaw_le_nonuniform_of_small_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 10)
    {eps : ℝ} (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      (eps / (1 / 10000)) * Real.exp (-(1 / 10000) * |x|) := by
  rw [← map_diagonalPartialSum_univ_eq_diagonalCenteredLaw a lam]
  apply diagonalPartialSum_univ_smallBall_le_nonuniform_of_small_coordinates
  · simpa only [totalVariance, partialVariance] using hsum
  · exact hsmall
  · exact heps
  · exact hepsOne

end Erdos88.GaussianQuadratic
