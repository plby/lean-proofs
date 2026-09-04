import ErdosProblems.Erdos88.GaussianUnivariateNonuniform
import ErdosProblems.Erdos88.GaussianDiagonalization

/-!
# Exponential tails for diagonal Gaussian quadratics

This file proves the finite-product Chernoff estimate used in the nonuniform
Gaussian small-ball argument.  The input is the exact one-coordinate moment
generating-function bound from `GaussianUnivariateNonuniform`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

/-- The centered diagonal quadratic restricted to a set of coordinates. -/
def diagonalPartialSum {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) (z : ι → ℝ) : ℝ :=
  ∑ i ∈ S, centeredCoordinatePolynomial (a i) (lam i) (z i)

/-- The variance carried by a set of diagonal coordinates. -/
def partialVariance {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, coordinateVariance (a i) (lam i)

lemma diagonalPartialSum_mgf_le_exp {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) {t : ℝ}
    (hsmall : ∀ i ∈ S, |2 * t * lam i| ≤ 1 / 2) :
    mgf (diagonalPartialSum a lam S)
        (Measure.pi fun _ : ι ↦ standardGaussian) t ≤
      Real.exp (2 * t ^ 2 * partialVariance a lam S) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let X : ι → (ι → ℝ) → ℝ := fun i z ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i)
  have hbase : iIndepFun (fun i (z : ι → ℝ) ↦ z i) P := by
    dsimp only [P]
    exact iIndepFun_pi fun _ ↦ aemeasurable_id
  have hindep : iIndepFun X P := by
    exact hbase.comp
      (fun i x ↦ centeredCoordinatePolynomial (a i) (lam i) x)
      (fun i ↦ (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable)
  have hmeas : ∀ i, Measurable (X i) := fun i ↦ by
    dsimp only [X]
    exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
      (measurable_pi_apply i)
  have hmgf : mgf (diagonalPartialSum a lam S) P t =
      ∏ i ∈ S, mgf (centeredCoordinatePolynomial (a i) (lam i))
        standardGaussian t := by
    rw [show diagonalPartialSum a lam S = ∑ i ∈ S, X i by
      funext z
      simp only [diagonalPartialSum, X, Finset.sum_apply]]
    rw [hindep.mgf_sum hmeas S]
    apply Finset.prod_congr rfl
    intro i hi
    have hiID : IdentDistrib (X i)
        (centeredCoordinatePolynomial (a i) (lam i)) P standardGaussian := by
      have hEval : IdentDistrib (fun z : ι → ℝ ↦ z i) id P standardGaussian :=
        { aemeasurable_fst := (measurable_pi_apply i).aemeasurable
          aemeasurable_snd := aemeasurable_id
          map_eq := by
            simpa only [P, Measure.map_id] using
              (measurePreserving_eval
                (μ := fun _ : ι ↦ standardGaussian) i).map_eq }
      simpa only [X, Function.comp_def, id_eq] using hEval.comp
        (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable
    exact congrFun (mgf_congr_identDistrib hiID) t
  rw [hmgf]
  calc
    (∏ i ∈ S, mgf (centeredCoordinatePolynomial (a i) (lam i))
        standardGaussian t) ≤
        ∏ i ∈ S, Real.exp (2 * t ^ 2 * coordinateVariance (a i) (lam i)) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        exact centeredCoordinate_mgf_le_exp (hsmall i hi)
    _ = Real.exp (2 * t ^ 2 * partialVariance a lam S) := by
      rw [← Real.exp_sum]
      unfold partialVariance
      rw [Finset.mul_sum]

lemma integrable_exp_mul_diagonalPartialSum {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) {t : ℝ}
    (hsmall : ∀ i ∈ S, |2 * t * lam i| ≤ 1 / 2) :
    Integrable (fun z : ι → ℝ ↦
      Real.exp (t * diagonalPartialSum a lam S z))
        (Measure.pi fun _ : ι ↦ standardGaussian) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let X : ι → (ι → ℝ) → ℝ := fun i z ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i)
  have hbase : iIndepFun (fun i (z : ι → ℝ) ↦ z i) P := by
    dsimp only [P]
    exact iIndepFun_pi fun _ ↦ aemeasurable_id
  have hindep : iIndepFun X P := by
    exact hbase.comp
      (fun i x ↦ centeredCoordinatePolynomial (a i) (lam i) x)
      (fun i ↦ (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable)
  have hmeas : ∀ i, Measurable (X i) := fun i ↦ by
    dsimp only [X]
    exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
      (measurable_pi_apply i)
  have hcoord : ∀ i ∈ S,
      Integrable (fun z : ι → ℝ ↦ Real.exp (t * X i z)) P := by
    intro i hi
    have htlam : 2 * t * lam i < 1 := by
      have hu := (abs_le.mp (hsmall i hi)).2
      exact lt_of_le_of_lt hu (by norm_num)
    have hpos : 0 < mgf (centeredCoordinatePolynomial (a i) (lam i))
        standardGaussian t := by
      rw [centeredCoordinate_mgf_formula htlam]
      positivity
    have hone : Integrable (fun x : ℝ ↦
        Real.exp (t * centeredCoordinatePolynomial (a i) (lam i) x))
        standardGaussian := (mgf_pos_iff.mp hpos)
    have hpi := integrable_comp_eval
      (μ := fun _ : ι ↦ standardGaussian) (i := i) hone
    simpa only [P, X] using hpi
  rw [show diagonalPartialSum a lam S = ∑ i ∈ S, X i by
    funext z
    simp only [diagonalPartialSum, X, Finset.sum_apply]]
  exact hindep.integrable_exp_mul_sum hmeas hcoord

lemma diagonalPartialSum_upperTail_le {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) {t x : ℝ}
    (ht : 0 ≤ t) (hsmall : ∀ i ∈ S, |2 * t * lam i| ≤ 1 / 2) :
    (Measure.pi fun _ : ι ↦ standardGaussian).real
        {z | x ≤ diagonalPartialSum a lam S z} ≤
      Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  have hint := integrable_exp_mul_diagonalPartialSum a lam S hsmall
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := P)
    (X := diagonalPartialSum a lam S) x ht hint
  calc
    P.real {z | x ≤ diagonalPartialSum a lam S z} ≤
        Real.exp (-t * x) *
          mgf (diagonalPartialSum a lam S) P t := hchernoff
    _ ≤ Real.exp (-t * x) *
        Real.exp (2 * t ^ 2 * partialVariance a lam S) := by
      gcongr
      exact diagonalPartialSum_mgf_le_exp a lam S hsmall
    _ = Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
      rw [Real.exp_add]

lemma diagonalPartialSum_lowerTail_le {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) {t x : ℝ}
    (ht : 0 ≤ t) (hsmall : ∀ i ∈ S, |2 * t * lam i| ≤ 1 / 2) :
    (Measure.pi fun _ : ι ↦ standardGaussian).real
        {z | diagonalPartialSum a lam S z ≤ -x} ≤
      Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  have hsmallNeg : ∀ i ∈ S, |2 * (-t) * lam i| ≤ 1 / 2 := by
    intro i hi
    rw [show 2 * (-t) * lam i = -(2 * t * lam i) by ring, abs_neg]
    exact hsmall i hi
  have hint := integrable_exp_mul_diagonalPartialSum a lam S hsmallNeg
  have hchernoff := measure_le_le_exp_mul_mgf (μ := P)
    (X := diagonalPartialSum a lam S) (-x) (by linarith : -t ≤ 0) hint
  calc
    P.real {z | diagonalPartialSum a lam S z ≤ -x} ≤
        Real.exp (-(-t) * (-x)) *
          mgf (diagonalPartialSum a lam S) P (-t) := hchernoff
    _ ≤ Real.exp (-t * x) *
        Real.exp (2 * (-t) ^ 2 * partialVariance a lam S) := by
      rw [show -(-t) * (-x) = -t * x by ring]
      exact mul_le_mul_of_nonneg_left
        (diagonalPartialSum_mgf_le_exp a lam S hsmallNeg)
        (Real.exp_nonneg _)
    _ = Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
      rw [Real.exp_add]
      congr 1 <;> ring_nf

lemma diagonalPartialSum_absTail_le {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) {t x : ℝ}
    (ht : 0 ≤ t) (hsmall : ∀ i ∈ S, |2 * t * lam i| ≤ 1 / 2) :
    (Measure.pi fun _ : ι ↦ standardGaussian).real
        {z | x ≤ |diagonalPartialSum a lam S z|} ≤
      2 * Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let A : Set (ι → ℝ) := {z | x ≤ diagonalPartialSum a lam S z}
  let B : Set (ι → ℝ) := {z | diagonalPartialSum a lam S z ≤ -x}
  have hsubset : {z | x ≤ |diagonalPartialSum a lam S z|} ⊆ A ∪ B := by
    intro z hz
    change x ≤ |diagonalPartialSum a lam S z| at hz
    by_cases hnonneg : 0 ≤ diagonalPartialSum a lam S z
    · left
      exact (show x ≤ diagonalPartialSum a lam S z by
        simpa only [abs_of_nonneg hnonneg] using hz)
    · right
      have hnonpos : diagonalPartialSum a lam S z ≤ 0 := le_of_not_ge hnonneg
      have hxneg : x ≤ -diagonalPartialSum a lam S z := by
        simpa only [abs_of_nonpos hnonpos] using hz
      exact (show diagonalPartialSum a lam S z ≤ -x by linarith)
  have hmono : P.real {z | x ≤ |diagonalPartialSum a lam S z|} ≤
      P.real (A ∪ B) := measureReal_mono hsubset
  have hunion : P.real (A ∪ B) ≤ P.real A + P.real B :=
    measureReal_union_le A B
  have hupper : P.real A ≤
      Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
    simpa only [P, A] using
      diagonalPartialSum_upperTail_le a lam S ht hsmall
  have hlower : P.real B ≤
      Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by
    simpa only [P, B] using
      diagonalPartialSum_lowerTail_le a lam S ht hsmall
  calc
    P.real {z | x ≤ |diagonalPartialSum a lam S z|} ≤ P.real (A ∪ B) := hmono
    _ ≤ P.real A + P.real B := hunion
    _ ≤ Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) +
        Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-t * x + 2 * t ^ 2 * partialVariance a lam S) := by ring

lemma partialVariance_nonneg {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) :
    0 ≤ partialVariance a lam S := by
  unfold partialVariance
  exact Finset.sum_nonneg fun i _ ↦ coordinateVariance_nonneg (a i) (lam i)

lemma abs_lam_le_sqrt_partialVariance {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    |lam i| ≤ Real.sqrt (partialVariance a lam S) := by
  have hcoord : coordinateVariance (a i) (lam i) ≤ partialVariance a lam S := by
    unfold partialVariance
    exact Finset.single_le_sum
      (fun j _ ↦ coordinateVariance_nonneg (a j) (lam j)) hi
  have hlamSq : (lam i) ^ 2 ≤ partialVariance a lam S := by
    unfold coordinateVariance at hcoord
    nlinarith [sq_nonneg (a i), sq_nonneg (lam i)]
  have hsqrtSq := Real.sq_sqrt (partialVariance_nonneg a lam S)
  nlinarith [sq_abs (lam i), abs_nonneg (lam i),
    Real.sqrt_nonneg (partialVariance a lam S)]

/-- The degree-two Gaussian exponential tail at the automatic variance scale. -/
lemma diagonalPartialSum_absTail_le_optimized {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι)
    (hV : 0 < partialVariance a lam S) {x : ℝ} :
    (Measure.pi fun _ : ι ↦ standardGaussian).real
        {z | x ≤ |diagonalPartialSum a lam S z|} ≤
      2 * Real.exp
        (-x / (4 * Real.sqrt (partialVariance a lam S)) + 1 / 8) := by
  let V := partialVariance a lam S
  let t : ℝ := 1 / (4 * Real.sqrt V)
  have hsqrt : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have ht : 0 ≤ t := by
    dsimp only [t]
    positivity
  have hsmall : ∀ i ∈ S, |2 * t * lam i| ≤ 1 / 2 := by
    intro i hi
    have hlam : |lam i| ≤ Real.sqrt V := by
      simpa only [V] using abs_lam_le_sqrt_partialVariance a lam S hi
    dsimp only [t]
    rw [show 2 * (1 / (4 * Real.sqrt V)) * lam i =
        lam i / (2 * Real.sqrt V) by field_simp; ring]
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos hsqrt]
    calc
      |lam i| / (2 * Real.sqrt V) ≤
          Real.sqrt V / (2 * Real.sqrt V) := by gcongr
      _ = 1 / 2 := by field_simp
  have htail := diagonalPartialSum_absTail_le a lam S ht hsmall (x := x)
  have hexp : -t * x + 2 * t ^ 2 * partialVariance a lam S =
      -x / (4 * Real.sqrt (partialVariance a lam S)) + 1 / 8 := by
    dsimp only [t, V]
    have hsqrt' : Real.sqrt (partialVariance a lam S) ≠ 0 := ne_of_gt hsqrt
    have hsqrtSq := Real.sq_sqrt hV.le
    field_simp
    nlinarith
  rwa [hexp] at htail

lemma measureReal_prod_add_Icc_le {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {eps x C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ y : ℝ, Erdos88.Esseen.smallBall ν eps y ≤ C) :
    (μ.prod ν).real {p : ℝ × ℝ | p.1 + p.2 ∈ Icc (x - eps) (x + eps)} ≤ C := by
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 + p.2 ∈ Icc (x - eps) (x + eps)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact measurableSet_Icc.preimage (measurable_fst.add measurable_snd)
  have hsection : ∀ y : ℝ,
      ν (Prod.mk y ⁻¹' E) ≤ ENNReal.ofReal C := by
    intro y
    have hset : Prod.mk y ⁻¹' E = Icc ((x - y) - eps) ((x - y) + eps) := by
      ext z
      simp only [mem_preimage, E, mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hset]
    have hfinite : ν (Icc ((x - y) - eps) ((x - y) + eps)) ≠ ⊤ :=
      measure_ne_top _ _
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hC]
    simpa only [Erdos88.Esseen.smallBall, measureReal_def] using hball (x - y)
  have hmeasure : (μ.prod ν) E ≤ ENNReal.ofReal C := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ y : ℝ, ν (Prod.mk y ⁻¹' E) ∂μ) ≤
          ∫⁻ _y : ℝ, ENNReal.ofReal C ∂μ :=
        lintegral_mono hsection
      _ = ENNReal.ofReal C := by simp
  rw [measureReal_def]
  change ((μ.prod ν) E).toReal ≤ C
  have hto :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hmeasure
  rwa [ENNReal.toReal_ofReal hC] at hto

lemma measureReal_prod_fst_mem_add_Icc_le {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set ℝ} (hA : MeasurableSet A) {eps x C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ y : ℝ, Erdos88.Esseen.smallBall ν eps y ≤ C) :
    (μ.prod ν).real
        {p : ℝ × ℝ | p.1 ∈ A ∧ p.1 + p.2 ∈ Icc (x - eps) (x + eps)} ≤
      C * μ.real A := by
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 ∈ A ∧ p.1 + p.2 ∈ Icc (x - eps) (x + eps)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact (hA.preimage measurable_fst).inter
      (measurableSet_Icc.preimage (measurable_fst.add measurable_snd))
  have hsection : ∀ y : ℝ,
      ν (Prod.mk y ⁻¹' E) ≤ A.indicator (fun _ ↦ ENNReal.ofReal C) y := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      have hset : Prod.mk y ⁻¹' E = Icc ((x - y) - eps) ((x - y) + eps) := by
        ext z
        change (y ∈ A ∧ x - eps ≤ y + z ∧ y + z ≤ x + eps) ↔
          x - y - eps ≤ z ∧ z ≤ x - y + eps
        constructor
        · rintro ⟨_hy, hlo, hhi⟩
          constructor <;> linarith
        · rintro ⟨hlo, hhi⟩
          exact ⟨hy, by constructor <;> linarith⟩
      rw [hset]
      have hfinite : ν (Icc ((x - y) - eps) ((x - y) + eps)) ≠ ⊤ :=
        measure_ne_top _ _
      apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hC]
      simpa only [Erdos88.Esseen.smallBall, measureReal_def] using hball (x - y)
    · rw [Set.indicator_of_notMem hy]
      have hempty : Prod.mk y ⁻¹' E = ∅ := by
        ext z
        change (y ∈ A ∧ y + z ∈ Icc (x - eps) (x + eps)) ↔ False
        exact iff_false_intro fun h ↦ hy h.1
      rw [hempty, measure_empty]
  have hmeasure : (μ.prod ν) E ≤ ENNReal.ofReal C * μ A := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ y : ℝ, ν (Prod.mk y ⁻¹' E) ∂μ) ≤
          ∫⁻ y : ℝ, A.indicator (fun _ ↦ ENNReal.ofReal C) y ∂μ :=
        lintegral_mono hsection
      _ = ∫⁻ _y : ℝ in A, ENNReal.ofReal C ∂μ :=
        lintegral_indicator hA _
      _ = ENNReal.ofReal C * μ A := setLIntegral_const A _
  rw [measureReal_def]
  change ((μ.prod ν) E).toReal ≤ C * (μ A).toReal
  have hto := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).2 hmeasure
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hto

lemma measureReal_add_Icc_le_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hindep : IndepFun X Y P) {eps x C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ y : ℝ, Erdos88.Esseen.smallBall (P.map Y) eps y ≤ C) :
    P.real {ω | X ω + Y ω ∈ Icc (x - eps) (x + eps)} ≤ C := by
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 + p.2 ∈ Icc (x - eps) (x + eps)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact measurableSet_Icc.preimage (measurable_fst.add measurable_snd)
  let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmap : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hindep.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hreal :
      P.real {ω | X ω + Y ω ∈ Icc (x - eps) (x + eps)} =
        (P.map (fun ω ↦ (X ω, Y ω))).real E := by
    rw [measureReal_def, measureReal_def, Measure.map_apply (hX.prodMk hY) hE]
    rfl
  rw [hreal, hmap]
  exact measureReal_prod_add_Icc_le hC hball

lemma measureReal_fst_mem_add_Icc_le_of_indepFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hindep : IndepFun X Y P) {A : Set ℝ} (hA : MeasurableSet A)
    {eps x C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ y : ℝ, Erdos88.Esseen.smallBall (P.map Y) eps y ≤ C) :
    P.real {ω | X ω ∈ A ∧ X ω + Y ω ∈ Icc (x - eps) (x + eps)} ≤
      C * (P.map X).real A := by
  let E : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.1 ∈ A ∧ p.1 + p.2 ∈ Icc (x - eps) (x + eps)}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact (hA.preimage measurable_fst).inter
      (measurableSet_Icc.preimage (measurable_fst.add measurable_snd))
  let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmap : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hindep.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hreal :
      P.real {ω | X ω ∈ A ∧ X ω + Y ω ∈ Icc (x - eps) (x + eps)} =
        (P.map (fun ω ↦ (X ω, Y ω))).real E := by
    rw [measureReal_def, measureReal_def, Measure.map_apply (hX.prodMk hY) hE]
    rfl
  rw [hreal, hmap]
  exact measureReal_prod_fst_mem_add_Icc_le hA hC hball

lemma diagonalPartialSum_indepFun {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) {S T : Finset ι} (hST : Disjoint S T) :
    IndepFun (diagonalPartialSum a lam S) (diagonalPartialSum a lam T)
      (Measure.pi fun _ : ι ↦ standardGaussian) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let X : ι → (ι → ℝ) → ℝ := fun i z ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i)
  have hbase : iIndepFun (fun i (z : ι → ℝ) ↦ z i) P := by
    dsimp only [P]
    exact iIndepFun_pi fun _ ↦ aemeasurable_id
  have hindep : iIndepFun X P := by
    exact hbase.comp
      (fun i x ↦ centeredCoordinatePolynomial (a i) (lam i) x)
      (fun i ↦ (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable)
  have hmeas : ∀ i, Measurable (X i) := fun i ↦ by
    dsimp only [X]
    exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
      (measurable_pi_apply i)
  have htuple := hindep.indepFun_finset S T hST hmeas
  have hsumS : Measurable (fun v : S → ℝ ↦ ∑ i : S, v i) := by fun_prop
  have hsumT : Measurable (fun v : T → ℝ ↦ ∑ i : T, v i) := by fun_prop
  have hcomp := htuple.comp hsumS hsumT
  convert hcomp using 1
  · funext z
    change (∑ i ∈ S, centeredCoordinatePolynomial (a i) (lam i) (z i)) =
      ∑ i : S, centeredCoordinatePolynomial (a i) (lam i) (z i)
    exact Finset.sum_subtype S (fun _ ↦ Iff.rfl) _
  · funext z
    change (∑ i ∈ T, centeredCoordinatePolynomial (a i) (lam i) (z i)) =
      ∑ i : T, centeredCoordinatePolynomial (a i) (lam i) (z i)
    exact Finset.sum_subtype T (fun _ ↦ Iff.rfl) _

lemma continuous_diagonalPartialSum {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (S : Finset ι) :
    Continuous (diagonalPartialSum a lam S) := by
  unfold diagonalPartialSum centeredCoordinatePolynomial
  fun_prop

lemma map_diagonalPartialSum_eq_diagonalCenteredLaw_subtype
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (S : Finset ι) :
    (Measure.pi fun _ : ι ↦ standardGaussian).map
        (diagonalPartialSum a lam S) =
      diagonalCenteredLaw (fun i : S ↦ a i) (fun i : S ↦ lam i) := by
  classical
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let R : (ι → ℝ) → (S → ℝ) := fun z i ↦ z i
  have hbase : iIndepFun (fun i (z : ι → ℝ) ↦ z i) P := by
    dsimp only [P]
    exact iIndepFun_pi fun _ ↦ aemeasurable_id
  have hsub : iIndepFun (fun i : S ↦ fun z : ι → ℝ ↦ z i) P :=
    hbase.precomp Subtype.val_injective
  have hR : Measurable R := by
    apply measurable_pi_lambda
    intro i
    have hi : Measurable (fun z : ι → ℝ ↦ z (i : ι)) := measurable_pi_apply _
    simpa only [R] using hi
  have hmapR : P.map R = Measure.pi (fun _ : S ↦ standardGaussian) := by
    have hmap : P.map R =
        Measure.pi (fun i : S ↦ P.map (fun z : ι → ℝ ↦ z (i : ι))) := by
      exact iIndepFun.map_fun_eq_pi_map (ι := S)
        (fun i ↦ (show Measurable (fun z : ι → ℝ ↦ z (i : ι)) from
          measurable_pi_apply _).aemeasurable) hsub
    rw [hmap]
    congr 1
    funext i
    exact (measurePreserving_eval
      (μ := fun _ : ι ↦ standardGaussian) (i : ι)).map_eq
  have hfun : diagonalPartialSum a lam S =
      diagonalCenteredSum (fun i : S ↦ a i) (fun i : S ↦ lam i) ∘ R := by
    funext z
    change (∑ i ∈ S, centeredCoordinatePolynomial (a i) (lam i) (z i)) =
      ∑ i : S, centeredCoordinatePolynomial (a i) (lam i) (z i)
    exact Finset.sum_subtype S (fun _ ↦ Iff.rfl) _
  rw [hfun, ← Measure.map_map
    (continuous_diagonalCenteredSum (fun i : S ↦ a i) (fun i : S ↦ lam i)).measurable
    hR]
  rw [hmapR]
  exact (diagonalCenteredLaw_eq_map_diagonalCenteredSum
    (fun i : S ↦ a i) (fun i : S ↦ lam i)).symm

/-- A large deviation on one coordinate block, combined with a uniform
small-ball estimate for a disjoint complementary block. -/
lemma diagonalPartialSum_large_add_smallBall_le
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) {S T : Finset ι}
    (hST : Disjoint S T) (hV : 0 < partialVariance a lam S)
    {r eps x C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((Measure.pi fun _ : ι ↦ standardGaussian).map
            (diagonalPartialSum a lam T)) eps y ≤ C) :
    (Measure.pi fun _ : ι ↦ standardGaussian).real
        {z | r ≤ |diagonalPartialSum a lam S z| ∧
          diagonalPartialSum a lam S z + diagonalPartialSum a lam T z ∈
            Icc (x - eps) (x + eps)} ≤
      C * (2 * Real.exp
        (-r / (4 * Real.sqrt (partialVariance a lam S)) + 1 / 8)) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let X := diagonalPartialSum a lam S
  let Y := diagonalPartialSum a lam T
  let A : Set ℝ := {u | r ≤ |u|}
  have hX : Measurable X := (continuous_diagonalPartialSum a lam S).measurable
  have hY : Measurable Y := (continuous_diagonalPartialSum a lam T).measurable
  have hA : MeasurableSet A := by
    exact measurableSet_Ici.preimage continuous_abs.measurable
  have hfactor := measureReal_fst_mem_add_Icc_le_of_indepFun hX hY
    (diagonalPartialSum_indepFun a lam hST) hA
    (eps := eps) (x := x) (C := C) hC hball
  have hmapTail : (P.map X).real A =
      P.real {z | r ≤ |diagonalPartialSum a lam S z|} := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hX hA]
    rfl
  have htail := diagonalPartialSum_absTail_le_optimized a lam S hV (x := r)
  calc
    P.real {z | r ≤ |diagonalPartialSum a lam S z| ∧
          diagonalPartialSum a lam S z + diagonalPartialSum a lam T z ∈
            Icc (x - eps) (x + eps)} ≤ C * (P.map X).real A := hfactor
    _ = C * P.real {z | r ≤ |diagonalPartialSum a lam S z|} := by rw [hmapTail]
    _ ≤ C * (2 * Real.exp
        (-r / (4 * Real.sqrt (partialVariance a lam S)) + 1 / 8)) :=
      mul_le_mul_of_nonneg_left htail hC

lemma diagonalPartialSum_smallBall_subtype_le
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (S : Finset ι)
    {eps C : ℝ}
    (hball : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
        (diagonalCenteredLaw (fun i : S ↦ a i) (fun i : S ↦ lam i)) eps y ≤ C) :
    ∀ y : ℝ,
      Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam S)) eps y ≤ C := by
  rw [map_diagonalPartialSum_eq_diagonalCenteredLaw_subtype]
  exact hball

lemma smallBall_map_div_eq (mu : Measure ℝ) {sigma : ℝ} (hsigma : 0 < sigma)
    (eps x : ℝ) :
    Erdos88.Esseen.smallBall (mu.map (fun y ↦ y / sigma))
        (eps / sigma) (x / sigma) =
      Erdos88.Esseen.smallBall mu eps x := by
  unfold Erdos88.Esseen.smallBall
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Icc]
  apply congrArg ENNReal.toReal
  apply congrArg mu
  ext y
  simp only [mem_preimage, mem_Icc]
  constructor
  · intro h
    rw [← sub_div, ← add_div] at h
    exact ⟨(div_le_div_iff_of_pos_right hsigma).mp h.1,
      (div_le_div_iff_of_pos_right hsigma).mp h.2⟩
  · intro h
    rw [← sub_div, ← add_div]
    exact ⟨(div_le_div_iff_of_pos_right hsigma).mpr h.1,
      (div_le_div_iff_of_pos_right hsigma).mpr h.2⟩

lemma totalVariance_subtype_eq_partialVariance
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (S : Finset ι) :
    totalVariance (fun i : S ↦ a i) (fun i : S ↦ lam i) =
      partialVariance a lam S := by
  unfold totalVariance partialVariance
  exact (Finset.sum_subtype S (fun _ ↦ Iff.rfl)
    (fun i : ι ↦ coordinateVariance (a i) (lam i))).symm

lemma smallBall_diagonalPartialSum_le_of_small_coordinates
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (S : Finset ι)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hV : 0 < partialVariance a lam S)
    (hsmall : ∀ i ∈ S,
      coordinateVariance (a i) (lam i) ≤ partialVariance a lam S / 4)
    (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam S)) eps x ≤
      2 * eps / Real.sqrt (partialVariance a lam S) := by
  rw [map_diagonalPartialSum_eq_diagonalCenteredLaw_subtype]
  let sigma := Real.sqrt (partialVariance a lam S)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hV
  have hsum : totalVariance (fun i : S ↦ a i) (fun i : S ↦ lam i) =
      sigma ^ 2 := by
    rw [totalVariance_subtype_eq_partialVariance]
    exact (Real.sq_sqrt hV.le).symm
  have hsmall' : ∀ i : S,
      coordinateVariance (a i) (lam i) ≤ sigma ^ 2 / 4 := by
    intro i
    rw [Real.sq_sqrt hV.le]
    exact hsmall i i.property
  have hraw := smallBall_diagonalCenteredLaw_map_div_le_of_small_coordinates
    (fun i : S ↦ a i) (fun i : S ↦ lam i) hsigma hsum hsmall' heps x
  rw [smallBall_map_div_eq _ hsigma] at hraw
  simpa only [sigma, mul_div_assoc] using hraw

lemma diagonalPartialSum_add_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι) (z : ι → ℝ) :
    diagonalPartialSum a lam S z +
        diagonalPartialSum a lam (Finset.univ \ S) z =
      diagonalPartialSum a lam Finset.univ z := by
  unfold diagonalPartialSum
  have h := Finset.sum_sdiff (f := fun i ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i))
    (Finset.subset_univ S)
  linarith

lemma fiveBlock_large_cover {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (J : Fin 5 → Finset ι)
    (hdecomp : ∀ z, diagonalPartialSum a lam Finset.univ z =
      ∑ h : Fin 5, diagonalPartialSum a lam (J h) z)
    {eps x : ℝ} (heps : 0 ≤ eps) (hx : eps < |x|) :
    {z | diagonalPartialSum a lam Finset.univ z ∈ Icc (x - eps) (x + eps)} ⊆
      ⋃ h : Fin 5, {z | (|x| - eps) / 5 ≤
        |diagonalPartialSum a lam (J h) z|} := by
  intro z hz
  have hdiff : |diagonalPartialSum a lam Finset.univ z - x| ≤ eps := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hlower : |x| - eps ≤ |diagonalPartialSum a lam Finset.univ z| := by
    have habs := abs_sub_abs_le_abs_sub x (diagonalPartialSum a lam Finset.univ z)
    rw [abs_sub_comm] at hdiff
    linarith
  have hsumAbs : |diagonalPartialSum a lam Finset.univ z| ≤
      ∑ h : Fin 5, |diagonalPartialSum a lam (J h) z| := by
    rw [hdecomp]
    exact Finset.abs_sum_le_sum_abs _ _
  have hexists : ∃ h : Fin 5, (|x| - eps) / 5 ≤
      |diagonalPartialSum a lam (J h) z| := by
    by_contra hnone
    push_neg at hnone
    have hsumLt : (∑ h : Fin 5, |diagonalPartialSum a lam (J h) z|) <
        ∑ _h : Fin 5, ((|x| - eps) / 5) := by
      exact Finset.sum_lt_sum (fun h _ ↦ (hnone h).le)
        ⟨0, Finset.mem_univ _, hnone 0⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsumLt
    have hxeps : 0 < |x| - eps := sub_pos.2 hx
    nlinarith
  obtain ⟨h, hh⟩ := hexists
  exact mem_iUnion.2 ⟨h, hh⟩

/-- Five-block form of the Gaussian nonuniform estimate.  Every block has
variance at most one, while every complementary block has a uniform
small-ball estimate. -/
theorem diagonalPartialSum_smallBall_le_of_five_blocks
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a lam : ι → ℝ)
    (J : Fin 5 → Finset ι)
    (hdecomp : ∀ z, diagonalPartialSum a lam Finset.univ z =
      ∑ h : Fin 5, diagonalPartialSum a lam (J h) z)
    (hVpos : ∀ h, 0 < partialVariance a lam (J h))
    (hVle : ∀ h, partialVariance a lam (J h) ≤ 1)
    {eps x C : ℝ} (heps : 0 ≤ eps) (hx : eps < |x|) (hC : 0 ≤ C)
    (hball : ∀ h (y : ℝ),
      Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam (Finset.univ \ J h))) eps y ≤ C) :
    (Measure.pi fun _ : ι ↦ standardGaussian).real
        {z | diagonalPartialSum a lam Finset.univ z ∈ Icc (x - eps) (x + eps)} ≤
      10 * C * Real.exp (-((|x| - eps) / 5) / 4 + 1 / 8) := by
  let P := Measure.pi fun _ : ι ↦ standardGaussian
  let r := (|x| - eps) / 5
  let U : Fin 5 → Set (ι → ℝ) := fun h ↦
    {z | r ≤ |diagonalPartialSum a lam (J h) z| ∧
      diagonalPartialSum a lam (J h) z +
          diagonalPartialSum a lam (Finset.univ \ J h) z ∈
        Icc (x - eps) (x + eps)}
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hsubset :
      {z | diagonalPartialSum a lam Finset.univ z ∈ Icc (x - eps) (x + eps)} ⊆
        ⋃ h, U h := by
    intro z hz
    obtain ⟨h, hh⟩ := mem_iUnion.1
      (fiveBlock_large_cover a lam J hdecomp heps hx hz)
    apply mem_iUnion.2
    refine ⟨h, hh, ?_⟩
    rw [diagonalPartialSum_add_compl]
    exact hz
  have hone (h : Fin 5) :
      Real.sqrt (partialVariance a lam (J h)) ≤ 1 := by
    have hsqrt := Real.sqrt_le_sqrt (hVle h)
    simpa only [Real.sqrt_one] using hsqrt
  have hterm (h : Fin 5) :
      P.real (U h) ≤
        C * (2 * Real.exp (-r / 4 + 1 / 8)) := by
    have hraw := diagonalPartialSum_large_add_smallBall_le
      a lam Finset.disjoint_sdiff (hVpos h) hC (hball h)
      (r := r) (eps := eps) (x := x)
    have hsqrtPos : 0 < Real.sqrt (partialVariance a lam (J h)) :=
      Real.sqrt_pos.2 (hVpos h)
    have hfrac : r / 4 ≤
        r / (4 * Real.sqrt (partialVariance a lam (J h))) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
        (mul_pos (by norm_num) hsqrtPos)).2
      nlinarith [hone h]
    have hexp : Real.exp
          (-r / (4 * Real.sqrt (partialVariance a lam (J h))) + 1 / 8) ≤
        Real.exp (-r / 4 + 1 / 8) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div]
      exact add_le_add (neg_le_neg hfrac) le_rfl
    calc
      P.real (U h) ≤ C * (2 * Real.exp
          (-r / (4 * Real.sqrt (partialVariance a lam (J h))) + 1 / 8)) := hraw
      _ ≤ C * (2 * Real.exp (-r / 4 + 1 / 8)) := by gcongr
  calc
    P.real {z | diagonalPartialSum a lam Finset.univ z ∈
          Icc (x - eps) (x + eps)} ≤ P.real (⋃ h, U h) := measureReal_mono hsubset
    _ ≤ ∑ h : Fin 5, P.real (U h) := measureReal_iUnion_fintype_le U
    _ ≤ ∑ _h : Fin 5, C * (2 * Real.exp (-r / 4 + 1 / 8)) :=
      Finset.sum_le_sum fun h _ ↦ hterm h
    _ = 10 * C * Real.exp (-((|x| - eps) / 5) / 4 + 1 / 8) := by
      dsimp only [r]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

end Erdos88.GaussianQuadratic
