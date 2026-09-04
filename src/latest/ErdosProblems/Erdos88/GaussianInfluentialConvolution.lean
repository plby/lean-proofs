import ErdosProblems.Erdos88.GaussianUnivariateLower

/-!
# Convolution lower bounds for an influential Gaussian coordinate

This module combines the one-coordinate interval lower bound from KSSS
Lemma 5.8 with the complementary-block mass estimate from Lemma 5.9.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

/-- A lower Fubini bound: if every coordinate section above a measurable
remainder event has mass at least `C`, then the sum-window has mass at least
`C` times the remainder-event mass. -/
lemma measureReal_prod_snd_add_Icc_ge
    {mu nu : Measure ℝ} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {J : Set ℝ} (hJ : MeasurableSet J) {x eps C : ℝ} (hC : 0 ≤ C)
    (hsection : ∀ y ∈ J, C ≤ nu.real (Set.Icc (x - y) (x + eps - y))) :
    C * mu.real J ≤
      (mu.prod nu).real
        {p : ℝ × ℝ | p.1 ∈ J ∧ p.1 + p.2 ∈ Set.Icc x (x + eps)} := by
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 ∈ J ∧ p.1 + p.2 ∈ Set.Icc x (x + eps)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact (hJ.preimage measurable_fst).inter
      (measurableSet_Icc.preimage (measurable_fst.add measurable_snd))
  have hpoint : ∀ y : ℝ,
      J.indicator (fun _ ↦ ENNReal.ofReal C) y ≤ nu (Prod.mk y ⁻¹' E) := by
    intro y
    by_cases hy : y ∈ J
    · rw [Set.indicator_of_mem hy]
      have hset : Prod.mk y ⁻¹' E = Set.Icc (x - y) (x + eps - y) := by
        ext z
        change (y ∈ J ∧ x ≤ y + z ∧ y + z ≤ x + eps) ↔
          x - y ≤ z ∧ z ≤ x + eps - y
        constructor
        · rintro ⟨_hy, hlo, hhi⟩
          constructor <;> linarith
        · rintro ⟨hlo, hhi⟩
          exact ⟨hy, by constructor <;> linarith⟩
      rw [hset]
      have hfinite : nu (Set.Icc (x - y) (x + eps - y)) ≠ ⊤ :=
        measure_ne_top _ _
      apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfinite).mp
      rw [ENNReal.toReal_ofReal hC]
      exact hsection y hy
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  have hmeasure : ENNReal.ofReal C * mu J ≤ (mu.prod nu) E := by
    rw [Measure.prod_apply hE]
    calc
      ENNReal.ofReal C * mu J =
          ∫⁻ y : ℝ, J.indicator (fun _ ↦ ENNReal.ofReal C) y ∂mu := by
        rw [lintegral_indicator hJ, setLIntegral_const]
      _ ≤ ∫⁻ y : ℝ, nu (Prod.mk y ⁻¹' E) ∂mu := lintegral_mono hpoint
  rw [measureReal_def]
  change C * (mu J).toReal ≤ ((mu.prod nu) E).toReal
  have hto := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (measure_ne_top _ _)).2 hmeasure
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hto

/-- Convolution of the nonnegative influential coordinate with the
one-sided complementary block.  This is the probabilistic assembly of KSSS
Lemmas 5.8 and 5.9. -/
theorem measureReal_diagonalPartialSum_univ_Icc_ge_of_influential_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) {A x eps : ℝ}
    (hlam : 0 ≤ lam i) (hA : 0 ≤ A)
    (hcoord : 0 < coordinateSigma (a i) (lam i))
    (hrem : 0 < partialVariance a lam (Finset.univ.erase i))
    (heps : 0 ≤ eps) (hepsCoord : eps ≤ coordinateSigma (a i) (lam i))
    (hx : 0 ≤ x)
    (hxA : x + 2 * Real.sqrt 15 *
        Real.sqrt (partialVariance a lam (Finset.univ.erase i)) ≤
      A * coordinateSigma (a i) (lam i)) :
    (eps / ((2 * A + 7) * coordinateSigma (a i) (lam i)) *
        gaussianPDFReal 0 1 (A + 3)) * (1 / 75) ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let P : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ standardGaussian
  let S : Finset ι := Finset.univ.erase i
  let X : (ι → ℝ) → ℝ := fun z ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i)
  let Y : (ι → ℝ) → ℝ := diagonalPartialSum a lam S
  let J : Set ℝ := Set.Icc
    (-2 * Real.sqrt 15 * Real.sqrt (partialVariance a lam S)) 0
  let C : ℝ := eps / ((2 * A + 7) * coordinateSigma (a i) (lam i)) *
    gaussianPDFReal 0 1 (A + 3)
  have hXmeas : Measurable X := by
    exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
      (measurable_pi_apply i)
  have hYmeas : Measurable Y := by
    exact (continuous_diagonalPartialSum a lam S).measurable
  have hdisj : Disjoint S ({i} : Finset ι) := by
    simp only [S, Finset.disjoint_singleton_right, Finset.mem_erase, not_and_or]
    exact Or.inl fun hi ↦ hi rfl
  have hindep : IndepFun Y X P := by
    have h := diagonalPartialSum_indepFun a lam hdisj
    have hsingleton : diagonalPartialSum a lam {i} = X := by
      funext z
      simp only [diagonalPartialSum, Finset.sum_singleton, X]
    simpa only [P, Y, hsingleton] using h
  have hmapX : P.map X =
      standardGaussian.map (centeredCoordinatePolynomial (a i) (lam i)) := by
    let eval : (ι → ℝ) → ℝ := fun z ↦ z i
    have hEval : P.map eval = standardGaussian := by
      dsimp only [P, eval]
      exact (measurePreserving_eval
        (μ := fun _ : ι ↦ standardGaussian) i).map_eq
    have hfun : X = centeredCoordinatePolynomial (a i) (lam i) ∘ eval := rfl
    rw [hfun, ← Measure.map_map
      (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable
      (measurable_pi_apply i), hEval]
  let : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  have hJ : MeasurableSet J := measurableSet_Icc
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (div_nonneg heps (mul_nonneg (by linarith : 0 ≤ 2 * A + 7) hcoord.le))
      (gaussianPDFReal_nonneg 0 1 (A + 3))
  have hsection : ∀ y ∈ J,
      C ≤ (P.map X).real (Set.Icc (x - y) (x + eps - y)) := by
    intro y hy
    have hy0 : y ≤ 0 := hy.2
    have hu0 : 0 ≤ x - y := by linarith
    have huA : x - y ≤ A * coordinateSigma (a i) (lam i) := by
      dsimp only [J, S] at hy
      linarith [hy.1, hxA]
    rw [hmapX]
    have h := map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_quadratic_nonneg
      (a := a i) (lam := lam i) (A := A) (u := x - y) (eps := eps)
      hlam hA hcoord heps hepsCoord hu0 huA
    have hright : x - y + eps = x + eps - y := by ring
    simpa only [C, hright] using h
  have hremMass : 1 / 75 ≤ (P.map Y).real J := by
    have hraw := measureReal_diagonalPartialSum_oneSided_ge a lam S
      (by simpa only [S] using hrem)
    have hmap : (P.map Y).real J = P.real (Y ⁻¹' J) := by
      rw [map_measureReal_apply hYmeas hJ]
    rw [hmap]
    simpa only [P, Y, J, S] using hraw
  have hprod := measureReal_prod_snd_add_Icc_ge
    (mu := P.map Y) (nu := P.map X) hJ hC hsection
  have hlower : C * (1 / 75) ≤
      ((P.map Y).prod (P.map X)).real
        {p : ℝ × ℝ | p.1 ∈ J ∧ p.1 + p.2 ∈ Set.Icc x (x + eps)} := by
    exact (mul_le_mul_of_nonneg_left hremMass hC).trans hprod
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 ∈ J ∧ p.1 + p.2 ∈ Set.Icc x (x + eps)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact (hJ.preimage measurable_fst).inter
      (measurableSet_Icc.preimage (measurable_fst.add measurable_snd))
  have hmapPair : P.map (fun z ↦ (Y z, X z)) = (P.map Y).prod (P.map X) :=
    hindep.map_prod_eq_prod_map_map hYmeas.aemeasurable hXmeas.aemeasurable
  have hfull : ∀ z, Y z + X z = diagonalPartialSum a lam Finset.univ z := by
    intro z
    simp only [Y, X, S, diagonalPartialSum]
    exact Finset.sum_erase_add Finset.univ
      (fun j ↦ centeredCoordinatePolynomial (a j) (lam j) (z j))
      (Finset.mem_univ i)
  have hpreimage : (fun z ↦ (Y z, X z)) ⁻¹' E =
      (diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps) ∩
        Y ⁻¹' J := by
    ext z
    change (Y z ∈ J ∧ Y z + X z ∈ Set.Icc x (x + eps)) ↔
      (diagonalPartialSum a lam Finset.univ z ∈ Set.Icc x (x + eps) ∧ Y z ∈ J)
    rw [hfull]
    tauto
  have htargetSubset :
      (fun z ↦ (Y z, X z)) ⁻¹' E ⊆
        (diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps) := by
    rw [hpreimage]
    exact Set.inter_subset_left
  have hpull : ((P.map Y).prod (P.map X)).real E =
      P.real ((fun z ↦ (Y z, X z)) ⁻¹' E) := by
    rw [← hmapPair, map_measureReal_apply (hYmeas.prodMk hXmeas) hE]
  calc
    C * (1 / 75) ≤ ((P.map Y).prod (P.map X)).real E := by
      simpa only [E] using hlower
    _ = P.real ((fun z ↦ (Y z, X z)) ⁻¹' E) := hpull
    _ ≤ P.real ((diagonalPartialSum a lam Finset.univ) ⁻¹'
          Set.Icc x (x + eps)) := measureReal_mono htargetSubset
    _ = _ := rfl

/-- Generic version of the influential-coordinate convolution: any uniform
lower bound for the coordinate sections over the one-sided remainder window
lifts to the full diagonal sum. -/
theorem measureReal_diagonalPartialSum_univ_Icc_ge_of_coordinate_sections
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) {x eps C : ℝ}
    (hrem : 0 < partialVariance a lam (Finset.univ.erase i))
    (hC : 0 ≤ C)
    (hsection : ∀ y ∈ Set.Icc
        (-2 * Real.sqrt 15 *
          Real.sqrt (partialVariance a lam (Finset.univ.erase i))) 0,
      C ≤ (standardGaussian.map
        (centeredCoordinatePolynomial (a i) (lam i))).real
          (Set.Icc (x - y) (x + eps - y))) :
    C * (1 / 75) ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let P : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ standardGaussian
  let S : Finset ι := Finset.univ.erase i
  let X : (ι → ℝ) → ℝ := fun z ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i)
  let Y : (ι → ℝ) → ℝ := diagonalPartialSum a lam S
  let J : Set ℝ := Set.Icc
    (-2 * Real.sqrt 15 * Real.sqrt (partialVariance a lam S)) 0
  have hXmeas : Measurable X := by
    exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
      (measurable_pi_apply i)
  have hYmeas : Measurable Y :=
    (continuous_diagonalPartialSum a lam S).measurable
  have hdisj : Disjoint S ({i} : Finset ι) := by
    simp only [S, Finset.disjoint_singleton_right, Finset.mem_erase, not_and_or]
    exact Or.inl fun hi ↦ hi rfl
  have hindep : IndepFun Y X P := by
    have h := diagonalPartialSum_indepFun a lam hdisj
    have hsingleton : diagonalPartialSum a lam {i} = X := by
      funext z
      simp only [diagonalPartialSum, Finset.sum_singleton, X]
    simpa only [P, Y, hsingleton] using h
  have hmapX : P.map X =
      standardGaussian.map (centeredCoordinatePolynomial (a i) (lam i)) := by
    let eval : (ι → ℝ) → ℝ := fun z ↦ z i
    have hEval : P.map eval = standardGaussian := by
      dsimp only [P, eval]
      exact (measurePreserving_eval
        (μ := fun _ : ι ↦ standardGaussian) i).map_eq
    have hfun : X = centeredCoordinatePolynomial (a i) (lam i) ∘ eval := rfl
    rw [hfun, ← Measure.map_map
      (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable
      (measurable_pi_apply i), hEval]
  let : IsProbabilityMeasure (P.map Y) :=
    Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  let : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  have hJ : MeasurableSet J := measurableSet_Icc
  have hsection' : ∀ y ∈ J,
      C ≤ (P.map X).real (Set.Icc (x - y) (x + eps - y)) := by
    intro y hy
    rw [hmapX]
    exact hsection y (by simpa only [J, S] using hy)
  have hremMass : 1 / 75 ≤ (P.map Y).real J := by
    have hraw := measureReal_diagonalPartialSum_oneSided_ge a lam S
      (by simpa only [S] using hrem)
    have hmap : (P.map Y).real J = P.real (Y ⁻¹' J) := by
      rw [map_measureReal_apply hYmeas hJ]
    rw [hmap]
    simpa only [P, Y, J, S] using hraw
  have hprod := measureReal_prod_snd_add_Icc_ge
    (mu := P.map Y) (nu := P.map X) hJ hC hsection'
  have hlower : C * (1 / 75) ≤
      ((P.map Y).prod (P.map X)).real
        {p : ℝ × ℝ | p.1 ∈ J ∧ p.1 + p.2 ∈ Set.Icc x (x + eps)} :=
    (mul_le_mul_of_nonneg_left hremMass hC).trans hprod
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 ∈ J ∧ p.1 + p.2 ∈ Set.Icc x (x + eps)}
  have hE : MeasurableSet E := by
    exact (hJ.preimage measurable_fst).inter
      (measurableSet_Icc.preimage (measurable_fst.add measurable_snd))
  have hmapPair : P.map (fun z ↦ (Y z, X z)) = (P.map Y).prod (P.map X) :=
    hindep.map_prod_eq_prod_map_map hYmeas.aemeasurable hXmeas.aemeasurable
  have hfull : ∀ z, Y z + X z = diagonalPartialSum a lam Finset.univ z := by
    intro z
    simp only [Y, X, S, diagonalPartialSum]
    exact Finset.sum_erase_add Finset.univ
      (fun j ↦ centeredCoordinatePolynomial (a j) (lam j) (z j))
      (Finset.mem_univ i)
  have hpreimage : (fun z ↦ (Y z, X z)) ⁻¹' E =
      (diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps) ∩
        Y ⁻¹' J := by
    ext z
    change (Y z ∈ J ∧ Y z + X z ∈ Set.Icc x (x + eps)) ↔
      (diagonalPartialSum a lam Finset.univ z ∈ Set.Icc x (x + eps) ∧ Y z ∈ J)
    rw [hfull]
    tauto
  have htargetSubset : (fun z ↦ (Y z, X z)) ⁻¹' E ⊆
      (diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps) := by
    rw [hpreimage]
    exact Set.inter_subset_left
  have hpull : ((P.map Y).prod (P.map X)).real E =
      P.real ((fun z ↦ (Y z, X z)) ⁻¹' E) := by
    rw [← hmapPair, map_measureReal_apply (hYmeas.prodMk hXmeas) hE]
  calc
    C * (1 / 75) ≤ ((P.map Y).prod (P.map X)).real E := by
      simpa only [E] using hlower
    _ = P.real ((fun z ↦ (Y z, X z)) ⁻¹' E) := hpull
    _ ≤ P.real ((diagonalPartialSum a lam Finset.univ) ⁻¹'
          Set.Icc x (x + eps)) := measureReal_mono htargetSubset
    _ = _ := rfl

/-- Convolution form of the linearly dominated branch of KSSS Lemma 5.8. -/
theorem measureReal_diagonalPartialSum_univ_Icc_ge_of_influential_linear_dominates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) {A x eps : ℝ}
    (hA : 0 ≤ A)
    (hcoord : 0 < coordinateSigma (a i) (lam i))
    (hdom : 8 * (4 * (A + 1) + 1) * |lam i| ≤ |a i|)
    (hrem : 0 < partialVariance a lam (Finset.univ.erase i))
    (heps : 0 ≤ eps) (hepsCoord : eps ≤ coordinateSigma (a i) (lam i))
    (hx : 0 ≤ x)
    (hxA : x + 2 * Real.sqrt 15 *
        Real.sqrt (partialVariance a lam (Finset.univ.erase i)) ≤
      A * coordinateSigma (a i) (lam i)) :
    (eps / (2 * coordinateSigma (a i) (lam i)) *
        gaussianPDFReal 0 1 (4 * (A + 1) + 1)) * (1 / 75) ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let C := eps / (2 * coordinateSigma (a i) (lam i)) *
    gaussianPDFReal 0 1 (4 * (A + 1) + 1)
  apply measureReal_diagonalPartialSum_univ_Icc_ge_of_coordinate_sections
    a lam i hrem
  · exact mul_nonneg
      (div_nonneg heps (mul_nonneg (by norm_num) hcoord.le))
      (gaussianPDFReal_nonneg 0 1 (4 * (A + 1) + 1))
  · intro y hy
    have hu0 : 0 ≤ x - y := by linarith [hy.2]
    have huA : x - y ≤ A * coordinateSigma (a i) (lam i) := by
      linarith [hy.1, hxA]
    have h := map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_linear_dominates
      (a := a i) (lam := lam i) (A := A) (u := x - y) (eps := eps)
      hA hcoord hdom heps hepsCoord hu0 huA
    have hright : x - y + eps = x + eps - y := by ring
    simpa only [C, hright] using h

end Erdos88.GaussianQuadratic
