import Mathlib

open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace Erdos230.Correction

def unitDir (a : ℂ) : ℂ := if a = 0 then 1 else (‖a‖ : ℂ)⁻¹ * a

lemma norm_unitDir (a : ℂ) : ‖unitDir a‖ = 1 := by
  simp only [unitDir]
  split_ifs with h
  · simp
  · rw [norm_mul, norm_inv, Complex.norm_real]
    simp [h]

lemma norm_smul_unitDir (a : ℂ) : (‖a‖ : ℂ) * unitDir a = a := by
  simp only [unitDir]
  split_ifs with h
  · simp [h]
  · have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

def chord (a : ℂ) (sgn : ℝ) : ℂ :=
  ((‖a‖ : ℂ) + sgn * (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) * Complex.I) * unitDir a

lemma chord_add (a : ℂ) : (chord a 1 + chord a (-1)) / 2 = a := by
  rw [chord, chord, ← add_mul]
  push_cast
  ring_nf
  exact norm_smul_unitDir a

def chordCorrection (a : ℂ) : ℂ :=
  (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) * Complex.I * unitDir a

lemma chord_eq_add_correction (a : ℂ) (sgn : ℝ) :
    chord a sgn = a + (sgn : ℂ) * chordCorrection a := by
  rw [chord, chordCorrection, add_mul]
  rw [norm_smul_unitDir]
  congr 1
  ring

lemma norm_chordCorrection_le_one (a : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖chordCorrection a‖ ≤ 1 := by
  rw [chordCorrection, norm_mul, norm_mul, norm_unitDir, mul_one, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hsquare : (Real.sqrt (1 - ‖a‖ ^ 2)) ^ 2 = 1 - ‖a‖ ^ 2 := by
    rw [sq_sqrt]
    nlinarith [norm_nonneg a]
  nlinarith [Real.sqrt_nonneg (1 - ‖a‖ ^ 2), norm_nonneg a]

lemma norm_chordCorrection_sq (a : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖chordCorrection a‖ ^ 2 = 1 - ‖a‖ ^ 2 := by
  rw [chordCorrection, norm_mul, norm_mul, norm_unitDir, mul_one, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_one]
  rw [sq_sqrt]
  nlinarith [norm_nonneg a]

/-- The total squared radial defect of coefficients in the closed unit disk. -/
def defect {ι : Type*} [Fintype ι] (a : ι → ℂ) : ℝ :=
  ∑ i, (1 - ‖a i‖ ^ 2)

lemma coe_sum_nnnorm_chordCorrection_sq {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ((↑(∑ i, ‖chordCorrection (a i)‖₊ ^ 2) : ℝ≥0) : ℝ) =
      defect a := by
  rw [defect]
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ norm_chordCorrection_sq (a i) (ha i)

lemma defect_term_nonneg {a : ℂ} (ha : ‖a‖ ≤ 1) : 0 ≤ 1 - ‖a‖ ^ 2 := by
  nlinarith [norm_nonneg a]

lemma norm_eq_one_of_defect_eq_zero {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (hzero : defect a = 0) (i : ι) :
    ‖a i‖ = 1 := by
  rw [defect] at hzero
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_hj : j ∈ Finset.univ) ↦ defect_term_nonneg (ha j))).mp hzero i (Finset.mem_univ i)
  nlinarith [norm_nonneg (a i)]

lemma norm_chord (a : ℂ) (ha : ‖a‖ ≤ 1) (sgn : ℝ) (hsgn : sgn ^ 2 = 1) :
    ‖chord a sgn‖ = 1 := by
  rw [chord, norm_mul, norm_unitDir, mul_one]
  rw [Complex.norm_def]
  have hsqrt : (Real.sqrt (1 - ‖a‖ ^ 2)) ^ 2 = 1 - ‖a‖ ^ 2 := by
    rw [sq_sqrt]
    nlinarith [norm_nonneg a]
  have hsq : Complex.normSq
      ((‖a‖ : ℂ) + sgn * (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) * Complex.I) = 1 := by
    rw [show sgn * (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) =
      ((sgn * Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) by norm_num]
    rw [Complex.normSq_add_mul_I]
    nlinarith
  rw [hsq, Real.sqrt_one]

abbrev coinPMF : PMF Bool := PMF.uniformOfFintype Bool

abbrev coinMeasure : Measure Bool := coinPMF.toMeasure

def sign (b : Bool) : ℝ := if b then 1 else -1

lemma integral_sign : ∫ b, sign b ∂coinMeasure = 0 := by
  change ∫ b, sign b ∂coinPMF.toMeasure = 0
  rw [PMF.integral_eq_sum]
  simp [sign, PMF.uniformOfFintype_apply]

lemma sign_mem_Icc : ∀ b, sign b ∈ Set.Icc (-1 : ℝ) 1 := by
  intro b
  cases b <;> simp [sign]

lemma hasSubgaussianMGF_sign : HasSubgaussianMGF sign 1 coinMeasure := by
  convert
    (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := sign) (a := (-1 : ℝ)) (b := 1) (by fun_prop)
      (ae_of_all _ sign_mem_Icc) integral_sign) using 1
  norm_num [NNReal.eq]

lemma subgaussian_mono {X : Ω → ℝ} [MeasurableSpace Ω] {c d : ℝ≥0} {P : Measure Ω}
    (h : HasSubgaussianMGF X c P) (hcd : c ≤ d) : HasSubgaussianMGF X d P where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := h.mgf_le t |>.trans <| by
    rw [Real.exp_le_exp]
    gcongr

lemma hasSubgaussianMGF_sign_mul (r : ℝ) (hr : |r| ≤ 1) :
    HasSubgaussianMGF (fun b ↦ r * sign b) 1 coinMeasure := by
  apply subgaussian_mono (hasSubgaussianMGF_sign.const_mul r)
  apply NNReal.coe_le_coe.mp
  change r ^ 2 * 1 ≤ (1 : ℝ)
  rcases abs_le.mp hr with ⟨hrl, hrr⟩
  nlinarith

def sqNNReal (r : ℝ) : ℝ≥0 := ⟨r ^ 2, sq_nonneg r⟩

lemma hasSubgaussianMGF_sign_mul_sq (r : ℝ) :
    HasSubgaussianMGF (fun b ↦ r * sign b) (sqNNReal r) coinMeasure := by
  convert hasSubgaussianMGF_sign.const_mul r using 1
  apply NNReal.eq
  change r ^ 2 = r ^ 2 * 1
  ring

abbrev coinProduct (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ ↦ coinMeasure)

lemma coordinate_subgaussian {ι : Type*} [Fintype ι] (i : ι) (r : ℝ) (hr : |r| ≤ 1) :
    HasSubgaussianMGF (fun ω : ι → Bool ↦ r * sign (ω i)) 1 (coinProduct ι) := by
  have hm := (measurePreserving_eval (fun _ : ι ↦ coinMeasure) i).map_eq
  change HasSubgaussianMGF
    ((fun b ↦ r * sign b) ∘ (fun ω : ι → Bool ↦ ω i)) 1 (coinProduct ι)
  apply HasSubgaussianMGF.of_map (Y := fun ω : ι → Bool ↦ ω i)
    (measurable_pi_apply i).aemeasurable
  change HasSubgaussianMGF (fun b ↦ r * sign b) 1
    (Measure.map (fun ω : ι → Bool ↦ ω i)
      (Measure.pi (fun _ : ι ↦ coinMeasure)))
  rw [hm]
  exact hasSubgaussianMGF_sign_mul r hr

lemma coordinate_subgaussian_weighted {ι : Type*} [Fintype ι]
    (i : ι) (r : ℝ) (v : ℝ≥0) (hrv : sqNNReal r ≤ v) :
    HasSubgaussianMGF (fun ω : ι → Bool ↦ r * sign (ω i)) v (coinProduct ι) := by
  have hm := (measurePreserving_eval (fun _ : ι ↦ coinMeasure) i).map_eq
  change HasSubgaussianMGF
    ((fun b ↦ r * sign b) ∘ (fun ω : ι → Bool ↦ ω i)) v (coinProduct ι)
  apply HasSubgaussianMGF.of_map (Y := fun ω : ι → Bool ↦ ω i)
    (measurable_pi_apply i).aemeasurable
  change HasSubgaussianMGF (fun b ↦ r * sign b) v
    (Measure.map (fun ω : ι → Bool ↦ ω i)
      (Measure.pi (fun _ : ι ↦ coinMeasure)))
  rw [hm]
  exact subgaussian_mono (hasSubgaussianMGF_sign_mul_sq r) hrv

lemma coordinate_iIndep {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    iIndepFun (fun i (ω : ι → Bool) ↦ r i * sign (ω i)) (coinProduct ι) := by
  exact iIndepFun_pi (X := fun i b ↦ r i * sign b)
    (μ := fun _ ↦ coinMeasure) (fun _ ↦ by fun_prop)

lemma real_rademacher_tail {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, |r i| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real
        {ω | t ≤ ∑ i, r i * sign (ω i)} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  simpa using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i (ω : ι → Bool) ↦ r i * sign (ω i))
      (c := fun _ ↦ 1) (s := Finset.univ) (coordinate_iIndep r)
      (fun i _ ↦ coordinate_subgaussian i (r i) (hr i)) ht)

lemma real_rademacher_tail_weighted {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (v : ι → ℝ≥0) (hrv : ∀ i, sqNNReal (r i) ≤ v i) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real
        {ω | t ≤ ∑ i, r i * sign (ω i)} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  simpa using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i (ω : ι → Bool) ↦ r i * sign (ω i))
      (c := v) (s := Finset.univ) (coordinate_iIndep r)
      (fun i _ ↦ coordinate_subgaussian_weighted i (r i) (v i) (hrv i)) ht)

def rademacherSum {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (g : κ) (ω : ι → Bool) : ℂ :=
  ∑ i, (sign (ω i) : ℂ) * C i g

lemma rademacher_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ (C i g).re) (fun i ↦
    (Complex.abs_re_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma rademacher_neg_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ -(C i g).re) (fun i ↦ by
    rw [abs_neg]
    exact (Complex.abs_re_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma rademacher_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ (C i g).im) (fun i ↦
    (Complex.abs_im_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma rademacher_neg_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ -(C i g).im) (fun i ↦ by
    rw [abs_neg]
    exact (Complex.abs_im_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma sqNNReal_re_le_nnnorm_sq (z : ℂ) : sqNNReal z.re ≤ ‖z‖₊ ^ 2 := by
  apply NNReal.coe_le_coe.mp
  change z.re ^ 2 ≤ ‖z‖ ^ 2
  exact sq_le_sq.mpr (by simpa using Complex.abs_re_le_norm z)

lemma sqNNReal_im_le_nnnorm_sq (z : ℂ) : sqNNReal z.im ≤ ‖z‖₊ ^ 2 := by
  apply NNReal.coe_le_coe.mp
  change z.im ^ 2 ≤ ‖z‖ ^ 2
  exact sq_le_sq.mpr (by simpa using Complex.abs_im_le_norm z)

lemma weighted_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ (C i g).re) v
    (fun i ↦ (sqNNReal_re_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma weighted_neg_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ -(C i g).re) v (fun i ↦ by
    simpa [sqNNReal] using (sqNNReal_re_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma weighted_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ (C i g).im) v
    (fun i ↦ (sqNNReal_im_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma weighted_neg_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ -(C i g).im) v (fun i ↦ by
    simpa [sqNNReal] using (sqNNReal_im_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma complex_rademacher_tail_weighted {ι κ : Type*} [Fintype ι]
    (C : ι → κ → ℂ) (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i)
    (g : κ) {R : ℝ} (hR : 0 < R) :
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖} ≤
      4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i)) := by
  let A : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).re}
  let B : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).re}
  let D : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).im}
  let E : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).im}
  have hsub : {ω | R ≤ ‖rademacherSum C g ω‖} ⊆ A ∪ B ∪ D ∪ E := by
    intro ω hnorm
    change R ≤ ‖rademacherSum C g ω‖ at hnorm
    by_contra hmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, A, B, D, E, not_le] at hmem
    rcases hmem with ⟨⟨⟨hre, hnre⟩, him⟩, hnim⟩
    have hsq := Complex.sq_norm (rademacherSum C g ω)
    rw [Complex.normSq_apply] at hsq
    have hn := norm_nonneg (rademacherSum C g ω)
    have hre_sq : (rademacherSum C g ω).re ^ 2 < (R / 2) ^ 2 := by nlinarith
    have him_sq : (rademacherSum C g ω).im ^ 2 < (R / 2) ^ 2 := by nlinarith
    have hnorm_sq : R ^ 2 ≤ ‖rademacherSum C g ω‖ ^ 2 := by nlinarith
    nlinarith
  calc
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖}
        ≤ (coinProduct ι).real (A ∪ B ∪ D ∪ E) := measureReal_mono hsub
    _ ≤ (coinProduct ι).real A + (coinProduct ι).real B +
        (coinProduct ι).real D + (coinProduct ι).real E := by
      calc
        _ ≤ (coinProduct ι).real (A ∪ B ∪ D) + (coinProduct ι).real E :=
          measureReal_union_le (A ∪ B ∪ D) E
        _ ≤ ((coinProduct ι).real (A ∪ B) + (coinProduct ι).real D) +
            (coinProduct ι).real E := by gcongr; exact measureReal_union_le (A ∪ B) D
        _ ≤ ((coinProduct ι).real A + (coinProduct ι).real B) +
            (coinProduct ι).real D + (coinProduct ι).real E := by gcongr; exact measureReal_union_le A B
    _ ≤ 4 * Real.exp (-(R / 2) ^ 2 / (2 * ∑ i, v i)) := by
      have hA := weighted_re_tail C v hC g (le_of_lt (half_pos hR))
      have hB := weighted_neg_re_tail C v hC g (le_of_lt (half_pos hR))
      have hD := weighted_im_tail C v hC g (le_of_lt (half_pos hR))
      have hE := weighted_neg_im_tail C v hC g (le_of_lt (half_pos hR))
      linarith
    _ = 4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i)) := by congr 2; ring

lemma complex_rademacher_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {R : ℝ} (hR : 0 < R) :
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖} ≤
      4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι)) := by
  let A : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).re}
  let B : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).re}
  let D : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).im}
  let E : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).im}
  have hsub : {ω | R ≤ ‖rademacherSum C g ω‖} ⊆ A ∪ B ∪ D ∪ E := by
    intro ω hnorm
    change R ≤ ‖rademacherSum C g ω‖ at hnorm
    by_contra hmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, A, B, D, E, not_le] at hmem
    rcases hmem with ⟨⟨⟨hre, hnre⟩, him⟩, hnim⟩
    have hsq := Complex.sq_norm (rademacherSum C g ω)
    rw [Complex.normSq_apply] at hsq
    have hn := norm_nonneg (rademacherSum C g ω)
    have hre_sq : (rademacherSum C g ω).re ^ 2 < (R / 2) ^ 2 := by nlinarith
    have him_sq : (rademacherSum C g ω).im ^ 2 < (R / 2) ^ 2 := by nlinarith
    have hnorm_sq : R ^ 2 ≤ ‖rademacherSum C g ω‖ ^ 2 := by nlinarith
    nlinarith
  have hA : (coinProduct ι).real A ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_re_tail C hC g (le_of_lt (half_pos hR))
  have hB : (coinProduct ι).real B ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_neg_re_tail C hC g (le_of_lt (half_pos hR))
  have hD : (coinProduct ι).real D ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_im_tail C hC g (le_of_lt (half_pos hR))
  have hE : (coinProduct ι).real E ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_neg_im_tail C hC g (le_of_lt (half_pos hR))
  calc
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖}
        ≤ (coinProduct ι).real (A ∪ B ∪ D ∪ E) := measureReal_mono hsub
    _ ≤ (coinProduct ι).real A + (coinProduct ι).real B +
        (coinProduct ι).real D + (coinProduct ι).real E := by
      calc
        _ ≤ (coinProduct ι).real (A ∪ B ∪ D) + (coinProduct ι).real E :=
          measureReal_union_le (A ∪ B ∪ D) E
        _ ≤ ((coinProduct ι).real (A ∪ B) + (coinProduct ι).real D) +
            (coinProduct ι).real E := by
          gcongr
          exact measureReal_union_le (A ∪ B) D
        _ ≤ ((coinProduct ι).real A + (coinProduct ι).real B) +
            (coinProduct ι).real D + (coinProduct ι).real E := by
          gcongr
          exact measureReal_union_le A B
    _ ≤ 4 * Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by linarith
    _ = 4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι)) := by
      congr 2
      ring

lemma exists_rademacher_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (hC : ∀ i g, ‖C i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) < 1) :
    ∃ ω : ι → Bool, ∀ g, ‖rademacherSum C g ω‖ < R := by
  let Bad : κ → Set (ι → Bool) := fun g ↦ {ω | R ≤ ‖rademacherSum C g ω‖}
  let U : Set (ι → Bool) := ⋃ g, Bad g
  have hU : (coinProduct ι).real U ≤ Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) := by
    calc
      (coinProduct ι).real U ≤ ∑ g, (coinProduct ι).real (Bad g) := by
        exact measureReal_iUnion_fintype_le Bad
      _ ≤ ∑ _g : κ, (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) := by
        exact Finset.sum_le_sum fun g _ ↦ complex_rademacher_tail C hC g hR
      _ = Fintype.card κ *
          (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) := by simp
  have hU_lt : (coinProduct ι).real U < 1 := hU.trans_lt hsmall
  have hex : ∃ ω : ι → Bool, ω ∉ U := by
    by_contra! hall
    have h_univ : U = Set.univ := Set.eq_univ_of_forall hall
    rw [h_univ, probReal_univ] at hU_lt
    exact (lt_irrefl 1) hU_lt
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun g ↦ lt_of_not_ge ?_⟩
  intro hg
  apply hω
  exact Set.mem_iUnion.2 ⟨g, hg⟩

lemma exists_rademacher_grid_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i)
    {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) < 1) :
    ∃ ω : ι → Bool, ∀ g, ‖rademacherSum C g ω‖ < R := by
  let Bad : κ → Set (ι → Bool) := fun g ↦ {ω | R ≤ ‖rademacherSum C g ω‖}
  let U : Set (ι → Bool) := ⋃ g, Bad g
  have hU : (coinProduct ι).real U ≤ Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) := by
    calc
      (coinProduct ι).real U ≤ ∑ g, (coinProduct ι).real (Bad g) :=
        measureReal_iUnion_fintype_le Bad
      _ ≤ ∑ _g : κ, (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) := by
        exact Finset.sum_le_sum fun g _ ↦ complex_rademacher_tail_weighted C v hC g hR
      _ = Fintype.card κ * (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) := by simp
  have hU_lt : (coinProduct ι).real U < 1 := hU.trans_lt hsmall
  have hex : ∃ ω : ι → Bool, ω ∉ U := by
    by_contra! hall
    have h_univ : U = Set.univ := Set.eq_univ_of_forall hall
    rw [h_univ, probReal_univ] at hU_lt
    exact (lt_irrefl 1) hU_lt
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun g ↦ lt_of_not_ge ?_⟩
  intro hg
  apply hω
  exact Set.mem_iUnion.2 ⟨g, hg⟩

lemma exists_unit_rounding_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hphase : ∀ i g, ‖phase i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) < 1) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ < R := by
  let C : ι → κ → ℂ := fun i g ↦ chordCorrection (a i) * phase i g
  have hC : ∀ i g, ‖C i g‖ ≤ 1 := by
    intro i g
    dsimp [C]
    rw [norm_mul]
    exact mul_le_one₀ (norm_chordCorrection_le_one (a i) (ha i))
      (norm_nonneg _) (hphase i g)
  obtain ⟨ω, hω⟩ := exists_rademacher_grid C hC hR hsmall
  let b : ι → ℂ := fun i ↦ chord (a i) (sign (ω i))
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply norm_chord (a i) (ha i) (sign (ω i))
    cases ω i <;> norm_num [sign]
  · intro g
    have heq : (∑ i, (b i - a i) * phase i g) = rademacherSum C g ω := by
      rw [rademacherSum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [b, C]
      rw [chord_eq_add_correction]
      simp only [add_sub_cancel_left]
      ring
    rw [heq]
    exact hω g

lemma exists_unit_rounding_grid_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hphase : ∀ i g, ‖phase i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ * (4 * Real.exp
      (-R ^ 2 / (8 * ∑ i, ‖chordCorrection (a i)‖₊ ^ 2))) < 1) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ < R := by
  let C : ι → κ → ℂ := fun i g ↦ chordCorrection (a i) * phase i g
  let v : ι → ℝ≥0 := fun i ↦ ‖chordCorrection (a i)‖₊ ^ 2
  have hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i := by
    intro i g
    apply NNReal.coe_le_coe.mp
    change ‖chordCorrection (a i) * phase i g‖ ^ 2 ≤ ‖chordCorrection (a i)‖ ^ 2
    rw [norm_mul, mul_pow]
    have hp0 := norm_nonneg (phase i g)
    have hp1 := hphase i g
    have hp2 : ‖phase i g‖ ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hp2 (sq_nonneg ‖chordCorrection (a i)‖)
  obtain ⟨ω, hω⟩ := exists_rademacher_grid_weighted C v hC hR (by simpa [v] using hsmall)
  let b : ι → ℂ := fun i ↦ chord (a i) (sign (ω i))
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply norm_chord (a i) (ha i) (sign (ω i))
    cases ω i <;> norm_num [sign]
  · intro g
    rw [show (∑ i, (b i - a i) * phase i g) = rademacherSum C g ω by
      rw [rademacherSum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [b, C]
      rw [chord_eq_add_correction]
      simp only [add_sub_cancel_left]
      ring]
    exact hω g

/-- The weighted rounding theorem with its variance parameter written as the exact coefficient
defect `∑ i, (1 - ‖a i‖²)`. -/
lemma exists_unit_rounding_grid_defect {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hphase : ∀ i g, ‖phase i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * defect a))) < 1) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ < R := by
  apply exists_unit_rounding_grid_weighted a ha phase hphase hR
  rw [coe_sum_nnnorm_chordCorrection_sq a ha]
  exact hsmall

/-- If the exact defect vanishes, no random correction is needed: all input coefficients already
have norm one. -/
lemma exists_unit_rounding_grid_of_defect_eq_zero {ι κ : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hzero : defect a = 0) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ = 0 := by
  refine ⟨a, fun i ↦ norm_eq_one_of_defect_eq_zero a ha hzero i, ?_⟩
  intro g
  simp

end Correction
