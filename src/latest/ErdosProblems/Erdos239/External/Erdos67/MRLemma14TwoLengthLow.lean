import ErdosProblems.Erdos239.External.Erdos67.MRRestrictedPerronErrorBound

/-!
# The low-frequency cancellation in the two-length Lemma 14 reduction

The source Lemma 14 compares two normalized short averages.  On the low
vertical segment their Perron kernels have the same leading term.  This
file records that cancellation with an explicit finite bound; in particular
the estimate does not use a pointwise absolute Perron truncation error.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67

noncomputable section

open MRRestrictedPerronErrorBound

/-- A one-bounded coefficient on one dyadic interval has vertical norm at
most one on `Re s = 1`. -/
theorem norm_dyadicVerticalDirichletPolynomial_le_one
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y : ℕ) (t : ℝ) :
    ‖dyadicVerticalDirichletPolynomial S f Y t‖ ≤ 1 := by
  classical
  unfold dyadicVerticalDirichletPolynomial logarithmicDirichletPolynomial
  calc
    ‖∑ n ∈ dyadicRestrictedSupport S Y,
        (f n / (n : ℂ)) * logarithmicPhase n (-t)‖ ≤
        ∑ n ∈ dyadicRestrictedSupport S Y,
          ‖(f n / (n : ℂ)) * logarithmicPhase n (-t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ dyadicRestrictedSupport S Y, ((n : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIoc : n ∈ Finset.Ioc Y (2 * Y) :=
        (Finset.mem_inter.mp hn).1
      have hnpos : 0 < n := by
        rw [Finset.mem_Ioc] at hnIoc
        omega
      rw [norm_mul, norm_logarithmicPhase, mul_one, norm_div,
        Complex.norm_natCast]
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right (hf n hnpos) (inv_nonneg.mpr (by positivity))
    _ ≤ 1 := sum_inv_dyadicRestrictedSupport_le_one S Y

/-- Pointwise low-frequency cancellation for the two normalized Perron
models.  The factor `T² (H₁+H₂)/X` is the source of the
`(log X)^(-2/15)` error after the standard parameter choice. -/
theorem norm_dyadicRestrictedPerronAverage_sub_low_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X x H₁ H₂ : ℕ}
    (hX : 0 < X) (hxmem : x ∈ Finset.Ioc X (2 * X))
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖dyadicRestrictedPerronAverage S f Y x H₁ T -
        dyadicRestrictedPerronAverage S f Y x H₂ T‖ ≤
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
        (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X) := by
  have hxnat : X < x := (Finset.mem_Ioc.mp hxmem).1
  have hx : (0 : ℝ) < x := by exact_mod_cast (hX.trans hxnat)
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hH₁r : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂r : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  let K : ℝ → ℂ := fun t ↦
    perronIncrementKernel x H₁ t - perronIncrementKernel x H₂ t
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hrewrite :
      dyadicRestrictedPerronAverage S f Y x H₁ T -
          dyadicRestrictedPerronAverage S f Y x H₂ T =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, F t * K t := by
    unfold dyadicRestrictedPerronAverage
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub
      ((continuous_mul_perronIncrementKernel_nat F hF
        (x := x) (H := H₁) (by omega) hH₁).intervalIntegrable (-T) T)
      ((continuous_mul_perronIncrementKernel_nat F hF
        (x := x) (H := H₂) (by omega) hH₂).intervalIntegrable (-T) T)]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [F, K]
    ring
  rw [hrewrite, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hpoint (t : ℝ) (ht : t ∈ Set.uIoc (-T) T) :
      ‖F t * K t‖ ≤ T * (((H₁ : ℝ) + H₂) / X) := by
    rw [Set.uIoc_of_le (by linarith)] at ht
    have habst : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hkernel := norm_perronIncrementKernel_sub_le_relative
      hx hH₁r hH₂r t
    have hxX : (X : ℝ) ≤ x := by exact_mod_cast hxnat.le
    have hratio :
        |t| * ((H₁ : ℝ) + H₂) / x ≤
          T * ((H₁ : ℝ) + H₂) / X := by
      have hsum : (0 : ℝ) ≤ (H₁ : ℝ) + H₂ := by positivity
      have hnum : |t| * ((H₁ : ℝ) + H₂) ≤
          T * ((H₁ : ℝ) + H₂) :=
        mul_le_mul_of_nonneg_right habst hsum
      calc
        |t| * ((H₁ : ℝ) + H₂) / x ≤
            T * ((H₁ : ℝ) + H₂) / x :=
          div_le_div_of_nonneg_right hnum hx.le
        _ ≤ T * ((H₁ : ℝ) + H₂) / X := by
          exact div_le_div_of_nonneg_left (mul_nonneg hT hsum) hXr hxX
    calc
      ‖F t * K t‖ = ‖F t‖ * ‖K t‖ := norm_mul _ _
      _ ≤ 1 * (|t| * ((H₁ : ℝ) + H₂) / x) := by
        gcongr
        exact norm_dyadicVerticalDirichletPolynomial_le_one S hf Y t
      _ = |t| * ((H₁ : ℝ) + H₂) / x := by ring
      _ ≤ T * ((H₁ : ℝ) + H₂) / X := hratio
      _ = T * (((H₁ : ℝ) + H₂) / X) := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ ↦ F t * K t)
    (C := T * (((H₁ : ℝ) + H₂) / X))
    (a := -T) (b := T) hpoint
  calc
    ‖∫ t in -T..T, F t * K t‖ ≤
        T * (((H₁ : ℝ) + H₂) / X) * |T - -T| := hint
    _ = 2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X := by
      rw [show T - -T = 2 * T by ring, abs_of_nonneg (by positivity)]
      ring

/-- The corresponding discrete low-frequency square mean over `(X,2X]`.
The right side retains the exact Perron normalization. -/
theorem dyadicTwoLengthPerronMeanSquare_low_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H₁ H₂ : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 ≤ T) :
    (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (dyadicRestrictedPerronAverage S f Y x H₁ T -
          dyadicRestrictedPerronAverage S f Y x H₂ T)) ≤
      (X : ℝ) *
        (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2 := by
  classical
  let C : ℝ := ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
    (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ _x ∈ Finset.Ioc X (2 * X), C ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Complex.normSq_eq_norm_sq]
      have hnorm := norm_dyadicRestrictedPerronAverage_sub_low_le
        S hf (Y := Y) hX hx hH₁ hH₂ hT
      change ‖_‖ ≤ C at hnorm
      exact (sq_le_sq₀ (norm_nonneg _) hC).2 hnorm
    _ = (X : ℝ) * C ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      simp
      omega
    _ = _ := rfl

/-- A one-bounded dyadic coefficient has norm at most one, including at
the two half-endpoints of Perron's starred convention. -/
theorem norm_dyadicRestrictedCoefficient_le_one
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (Y n : ℕ) :
    ‖dyadicRestrictedCoefficient S f Y n‖ ≤ 1 := by
  unfold dyadicRestrictedCoefficient
  split_ifs with hn
  · have hnIoc := (Finset.mem_inter.mp hn).1
    have hnpos : 0 < n := by
      rw [Finset.mem_Ioc] at hnIoc
      omega
    exact hf n hnpos
  · simp

/-- The half-endpoint correction has the expected `1/H` size. -/
theorem norm_dyadicRestrictedPerronEndpointCorrection_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Y x : ℕ) {H : ℕ} (hH : 0 < H) :
    ‖dyadicRestrictedPerronEndpointCorrection S f Y x H‖ ≤
      ((H : ℝ))⁻¹ := by
  unfold dyadicRestrictedPerronEndpointCorrection
  rw [norm_div, Complex.norm_natCast]
  have hnum :
      ‖(1 / 2 : ℂ) *
          (dyadicRestrictedCoefficient S f Y (x + H) -
            dyadicRestrictedCoefficient S f Y x)‖ ≤ 1 := by
    rw [norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    calc
      (1 / 2 : ℝ) *
          ‖dyadicRestrictedCoefficient S f Y (x + H) -
            dyadicRestrictedCoefficient S f Y x‖ ≤
          (1 / 2 : ℝ) *
            (‖dyadicRestrictedCoefficient S f Y (x + H)‖ +
              ‖dyadicRestrictedCoefficient S f Y x‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (1 / 2 : ℝ) * (1 + 1) := by
        gcongr
        · exact norm_dyadicRestrictedCoefficient_le_one S hf Y (x + H)
        · exact norm_dyadicRestrictedCoefficient_le_one S hf Y x
      _ = 1 := by norm_num
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    ‖(1 / 2 : ℂ) *
        (dyadicRestrictedCoefficient S f Y (x + H) -
          dyadicRestrictedCoefficient S f Y x)‖ / (H : ℝ) ≤
        1 / (H : ℝ) := div_le_div_of_nonneg_right hnum hHr.le
    _ = ((H : ℝ))⁻¹ := one_div _

/-- Low-frequency square mean for the endpoint-corrected Perron model.
The new term is the harmless `O(X(1/H₁+1/H₂)²)` endpoint cost. -/
theorem dyadicTwoLengthCorrectedPerronMeanSquare_low_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X H₁ H₂ : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 ≤ T) :
    dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T ≤
      2 * ((X : ℝ) *
        (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2) +
      2 * (X : ℝ) * (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := by
  classical
  unfold dyadicTwoLengthCorrectedPerronMeanSquare
    dyadicRestrictedCorrectedPerronAverage
  let A : ℕ → ℂ := fun x ↦
    dyadicRestrictedPerronAverage S f X x H₁ T -
      dyadicRestrictedPerronAverage S f X x H₂ T
  let E : ℕ → ℂ := fun x ↦
    dyadicRestrictedPerronEndpointCorrection S f X x H₁ -
      dyadicRestrictedPerronEndpointCorrection S f X x H₂
  have hraw := dyadicTwoLengthPerronMeanSquare_low_le
    S hf (Y := X) hX hH₁ hH₂ hT
  have hrawA :
      (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (A x)) ≤
        (X : ℝ) *
          (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
            (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2 := by
    simpa only [A] using hraw
  have hE (x : ℕ) : ‖E x‖ ≤
      ((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹ := by
    dsimp [E]
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_dyadicRestrictedPerronEndpointCorrection_le S hf X x hH₁)
      (norm_dyadicRestrictedPerronEndpointCorrection_le S hf X x hH₂))
  have hEsq :
      (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (E x)) ≤
        (X : ℝ) * (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := by
    calc
      _ ≤ ∑ _x ∈ Finset.Ioc X (2 * X),
          (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hE x)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp
        omega
  have hpoint (x : ℕ) :
      Complex.normSq (A x + E x) ≤
        2 * Complex.normSq (A x) + 2 * Complex.normSq (E x) := by
    convert normSq_sub_le_two_mul_add (A x) (-E x) using 1 <;>
      simp only [sub_neg_eq_add, Complex.normSq_neg] <;> ring
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          ((dyadicRestrictedPerronAverage S f X x H₁ T +
              dyadicRestrictedPerronEndpointCorrection S f X x H₁) -
            (dyadicRestrictedPerronAverage S f X x H₂ T +
              dyadicRestrictedPerronEndpointCorrection S f X x H₂))) =
        ∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (A x + E x) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 2
      dsimp [A, E]
      ring
    _ ≤ ∑ x ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (A x) + 2 * Complex.normSq (E x)) := by
      exact Finset.sum_le_sum (fun x hx ↦ hpoint x)
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (A x)) +
        2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (E x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      nlinarith [hrawA, hEsq]

/-- Parameter-ready form of the low-frequency estimate.  If the comparison
length is at most `X/K` and at least the target length, the normalized
low-frequency square error is `O(T⁴/K² + 1/H₁²)`. -/
theorem dyadicTwoLengthCorrectedPerronMeanSquare_low_le_scale
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X H₁ H₂ K : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hK : 0 < K) (hH₁H₂ : H₁ ≤ H₂) (hscale : K * H₂ ≤ X)
    {T : ℝ} (hT : 0 ≤ T) :
    dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T ≤
      (X : ℝ) *
        (32 * T ^ 4 / (K : ℝ) ^ 2 + 8 / (H₁ : ℝ) ^ 2) := by
  have hbase := dyadicTwoLengthCorrectedPerronMeanSquare_low_le
    S hf hX hH₁ hH₂ hT
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hH₁r : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have hH₂r : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hH₁H₂r : (H₁ : ℝ) ≤ H₂ := by exact_mod_cast hH₁H₂
  have hscaleR : (K : ℝ) * H₂ ≤ X := by exact_mod_cast hscale
  have hc : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply (inv_le_one₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hsum : (H₁ : ℝ) + H₂ ≤ 2 * (H₂ : ℝ) := by
    linarith
  have hratio : ((H₁ : ℝ) + H₂) / X ≤ 2 / (K : ℝ) := by
    rw [div_le_div_iff₀ hXr hKr]
    nlinarith
  have hrawFactor :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X) ≤
        4 * T ^ 2 / (K : ℝ) := by
    have hnonneg : 0 ≤ 2 * T ^ 2 * (((H₁ : ℝ) + H₂) / X) := by
      positivity
    calc
      _ ≤ 1 * (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X) := by
        gcongr
      _ = 2 * T ^ 2 * (((H₁ : ℝ) + H₂) / X) := by ring
      _ ≤ 2 * T ^ 2 * (2 / (K : ℝ)) := by
        gcongr
      _ = 4 * T ^ 2 / (K : ℝ) := by ring
  have hrawSq :
      (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2 ≤
        16 * T ^ 4 / (K : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hrawFactor
    calc
      _ ≤ (4 * T ^ 2 / (K : ℝ)) ^ 2 := hs
      _ = 16 * T ^ 4 / (K : ℝ) ^ 2 := by ring
  have hinv : ((H₂ : ℝ))⁻¹ ≤ ((H₁ : ℝ))⁻¹ := by
    exact inv_anti₀ hH₁r hH₁H₂r
  have hendFactor : ((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹ ≤
      2 * ((H₁ : ℝ))⁻¹ := by linarith
  have hendSq :
      (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 ≤
        4 / (H₁ : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hendFactor
    calc
      _ ≤ (2 * ((H₁ : ℝ))⁻¹) ^ 2 := hs
      _ = 4 / (H₁ : ℝ) ^ 2 := by
        field_simp
        norm_num
  calc
    _ ≤ 2 * ((X : ℝ) *
        (‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / X)) ^ 2) +
      2 * (X : ℝ) * (((H₁ : ℝ))⁻¹ + ((H₂ : ℝ))⁻¹) ^ 2 := hbase
    _ ≤ 2 * ((X : ℝ) * (16 * T ^ 4 / (K : ℝ) ^ 2)) +
        2 * (X : ℝ) * (4 / (H₁ : ℝ) ^ 2) := by
      gcongr
    _ = _ := by ring

end

end Erdos67
