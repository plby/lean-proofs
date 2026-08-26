import ErdosProblems.Erdos67b.MRLemma14ContinuousAdapter
import ErdosProblems.Erdos67b.MRRamarePerronProjectionL2

/-!
# Central-band energy for the continuous Perron endpoint

The source-correct continuous Perron/Fatou reduction leaves one central
Perron integral.  On that bounded band the normalized increment has norm at
most one, so two applications of Cauchy--Schwarz reduce it directly to the
vertical square energy of the original finite Dirichlet polynomial.
-/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

/-- Pointwise central Perron energy, retaining the exact normalization. -/
theorem normSq_perronKernelSegmentOn_le_verticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F)
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h) (hT : 0 ≤ T) :
    Complex.normSq (perronKernelSegmentOn F x h (-T) T) ≤
      Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        (2 * T) * (∫ t in -T..T, Complex.normSq (F t)) := by
  let g : ℝ → ℂ := fun t ↦ F t * perronIncrementKernel x h t
  have hg : Continuous g := by
    dsimp only [g]
    unfold perronIncrementKernel
    apply hF.mul
    apply Continuous.div
    · have he : Continuous (fun t : ℝ ↦ (1 : ℂ) + (t : ℂ) * Complex.I) := by
        fun_prop
      have hxHc : ((x + h : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (add_pos hx hh).ne'
      have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
      exact (he.const_cpow (Or.inl hxHc)).sub
        (he.const_cpow (Or.inl hxc))
    · fun_prop
    · intro t ht
      rcases mul_eq_zero.mp ht with hcast | hline
      · exact (Complex.ofReal_ne_zero.mpr hh.ne') hcast
      · have hre := congrArg Complex.re hline
        norm_num at hre
  have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
    hg (show -T ≤ T by linarith)
  have hmono :
      (∫ t in -T..T, Complex.normSq (g t)) ≤
        ∫ t in -T..T, Complex.normSq (F t) := by
    apply intervalIntegral.integral_mono_on (μ := volume)
      (show -T ≤ T by linarith)
      ((Complex.continuous_normSq.comp hg).intervalIntegrable
        (μ := volume) (-T) T)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := volume) (-T) T)
    intro t ht
    dsimp only [g]
    change Complex.normSq (F t * perronIncrementKernel x h t) ≤
      Complex.normSq (F t)
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    have hk := norm_perronIncrementKernel_le_one hx hh t
    have hkSq : ‖perronIncrementKernel x h t‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hk
    exact mul_le_of_le_one_right (sq_nonneg ‖F t‖) hkSq
  have henergy : 0 ≤ ∫ t in -T..T, Complex.normSq (F t) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact Complex.normSq_nonneg _
  unfold perronKernelSegmentOn
  rw [Complex.normSq_mul]
  calc
    Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        Complex.normSq (∫ t in -T..T, g t) ≤
      Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ((T - -T) * ∫ t in -T..T, Complex.normSq (g t)) := by
          exact mul_le_mul_of_nonneg_left hcs (Complex.normSq_nonneg _)
    _ ≤ Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ((T - -T) * ∫ t in -T..T, Complex.normSq (F t)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono (by linarith))
            (Complex.normSq_nonneg _)
    _ = Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        (2 * T) * (∫ t in -T..T, Complex.normSq (F t)) := by ring

/-- Spatially integrated central-band estimate on the exact unit-cell
window `[X+1,2X+1]` used by the continuous Perron reduction. -/
theorem integral_normSq_perronKernelSegmentOn_le_verticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F)
    {X H : ℕ} (hH : 0 < H) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (perronKernelSegmentOn F x H (-T) T)) ≤
      (X : ℝ) *
        (Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          (2 * T) * (∫ t in -T..T, Complex.normSq (F t))) := by
  let E : ℝ := Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    (2 * T) * (∫ t in -T..T, Complex.normSq (F t))
  have hXle : (X : ℝ) + 1 ≤ ((2 * X : ℕ) : ℝ) + 1 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hXnonneg : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    linarith
  have hleft : 0 < (X : ℝ) + 1 := by positivity
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcont : ContinuousOn
      (fun x ↦ Complex.normSq (perronKernelSegmentOn F x H (-T) T))
      (Set.uIcc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)) := by
    exact Complex.continuous_normSq.comp_continuousOn
      ((continuousOn_perronKernelSegmentOn F hF hleft hHR (-T) T).mono
        (by rw [Set.uIcc_of_le hXle]; exact Set.Icc_subset_Ici_self))
  have hconst : IntervalIntegrable (fun _x : ℝ ↦ E) volume
      ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) := intervalIntegrable_const
  have hmono :
      (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
          Complex.normSq (perronKernelSegmentOn F x H (-T) T)) ≤
        ∫ _x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1), E := by
    apply intervalIntegral.integral_mono_on (μ := volume) hXle
      hcont.intervalIntegrable hconst
    intro x hxIcc
    exact normSq_perronKernelSegmentOn_le_verticalEnergy F hF
      (hleft.trans_le hxIcc.1) hHR hT
  calc
    (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (perronKernelSegmentOn F x H (-T) T)) ≤
      ∫ _x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1), E := hmono
    _ = (X : ℝ) * E := by
      rw [intervalIntegral.integral_const]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = _ := by rfl

/-- The universal source coefficient is monotone in its right spatial
endpoint.  This lets the exact unit-cell window `[X+1,2X+1]` be enlarged to
`[X+1,2(X+1)]` before applying the scale-free coefficient estimate. -/
theorem lemma14UniversalPerronSegmentSafeWeightedCoefficient_mono_right
    {P Q₁ Q₂ h : ℝ} (hP : 0 < P) (hPQ₁ : P ≤ Q₁)
    (hQ₁Q₂ : Q₁ ≤ Q₂) (hh : 0 < h) :
    lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q₁ h ≤
      lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q₂ h := by
  let K : ℝ := lemma14UniversalFourierCauchyConstant * Real.pi
  let C : ℝ :=
    2 * Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) * (K / h ^ 3)
  let IL₁ : ℝ := ∫ u in h / Q₁..3 * h / P, (2 + u) ^ 2
  let IL₂ : ℝ := ∫ u in h / Q₂..3 * h / P, (2 + u) ^ 2
  let IR : ℝ := ∫ u in 0..2 * h / (P + h), (2 + u) ^ 2
  have hQ₁ : 0 < Q₁ := hP.trans_le hPQ₁
  have hQ₂ : 0 < Q₂ := hQ₁.trans_le hQ₁Q₂
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg lemma14UniversalFourierCauchyConstant_nonneg
      Real.pi_pos.le
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
      (div_nonneg hK (pow_nonneg hh.le 3))
  have hupper₁ : h / Q₁ ≤ 3 * h / P := by
    have hfirst : h / Q₁ ≤ h / P :=
      div_le_div_of_nonneg_left hh.le hP hPQ₁
    have hsecond : h / P ≤ 3 * h / P := by
      have : 0 ≤ h / P := by positivity
      calc
        h / P ≤ 3 * (h / P) := by nlinarith
        _ = 3 * h / P := by ring
    exact hfirst.trans hsecond
  have hupper₂ : h / Q₂ ≤ 3 * h / P := by
    exact (div_le_div_of_nonneg_left hh.le hP
      (hPQ₁.trans hQ₁Q₂)).trans (by
        have : 0 ≤ h / P := by positivity
        calc
          h / P ≤ 3 * (h / P) := by nlinarith
          _ = 3 * h / P := by ring)
  have hlow : h / Q₂ ≤ h / Q₁ :=
    div_le_div_of_nonneg_left hh.le hQ₁ hQ₁Q₂
  have hIL₁ : 0 ≤ IL₁ := by
    dsimp only [IL₁]
    exact intervalIntegral.integral_nonneg hupper₁
      (fun u hu ↦ sq_nonneg _)
  have hIL₂ : 0 ≤ IL₂ := by
    dsimp only [IL₂]
    exact intervalIntegral.integral_nonneg hupper₂
      (fun u hu ↦ sq_nonneg _)
  have hIL : IL₁ ≤ IL₂ := by
    dsimp only [IL₁, IL₂]
    exact intervalIntegral.integral_mono_interval hlow hupper₁ (le_refl _)
      (Filter.Eventually.of_forall fun u ↦ sq_nonneg _)
      ((by fun_prop : Continuous (fun u : ℝ ↦ (2 + u) ^ 2)).intervalIntegrable
        (h / Q₂) (3 * h / P))
  have hIR : 0 ≤ IR := by
    dsimp only [IR]
    exact intervalIntegral.integral_nonneg (by positivity)
      (fun u hu ↦ sq_nonneg _)
  have hpowQ : Q₁ ^ 4 ≤ Q₂ ^ 4 :=
    pow_le_pow_left₀ hQ₁.le hQ₁Q₂ 4
  have hpowQh : (Q₁ + h) ^ 4 ≤ (Q₂ + h) ^ 4 :=
    pow_le_pow_left₀ (add_nonneg hQ₁.le hh.le)
      (by simpa only [add_comm] using add_le_add_right hQ₁Q₂ h) 4
  have hleft : Q₁ ^ 4 * IL₁ ≤ Q₂ ^ 4 * IL₂ :=
    mul_le_mul hpowQ hIL hIL₁ (pow_nonneg hQ₂.le 4)
  have hright : (Q₁ + h) ^ 4 * IR ≤ (Q₂ + h) ^ 4 * IR :=
    mul_le_mul_of_nonneg_right hpowQh hIR
  have hrewrite (Q : ℝ) :
      lemma14UniversalPerronSegmentSafeWeightedCoefficient P Q h =
        C * (Q ^ 4 *
          (∫ u in h / Q..3 * h / P, (2 + u) ^ 2) +
          (Q + h) ^ 4 * IR) := by
    unfold lemma14UniversalPerronSegmentSafeWeightedCoefficient
    dsimp only [C, K, IR]
    field_simp [hh.ne']
  rw [hrewrite Q₁, hrewrite Q₂]
  change C * (Q₁ ^ 4 * IL₁ + (Q₁ + h) ^ 4 * IR) ≤
    C * (Q₂ ^ 4 * IL₂ + (Q₂ + h) ^ 4 * IR)
  exact mul_le_mul_of_nonneg_left (add_le_add hleft hright) hC

/-- Scale-free coefficient bound on the shifted unit-cell window used by
the exact real-endpoint mean-square identity. -/
theorem lemma14UniversalPerronSegmentSafeWeightedCoefficient_shifted_le
    {X H : ℕ} (hH : 0 < H) (hHX : H ≤ X) :
    lemma14UniversalPerronSegmentSafeWeightedCoefficient
        ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H ≤
      lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 / (H : ℝ) ^ 2 := by
  have hP : 0 < (X : ℝ) + 1 := by positivity
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHP : (H : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast (hHX.trans (Nat.le_add_right X 1))
  have hPQ : (X : ℝ) + 1 ≤ ((2 * X : ℕ) : ℝ) + 1 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hX0 : (0 : ℝ) ≤ X := by positivity
    linarith
  have hQtwo : (((2 * X : ℕ) : ℝ) + 1) ≤ 2 * ((X : ℝ) + 1) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  calc
    lemma14UniversalPerronSegmentSafeWeightedCoefficient
        ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H ≤
      lemma14UniversalPerronSegmentSafeWeightedCoefficient
        ((X : ℝ) + 1) (2 * ((X : ℝ) + 1)) H :=
      lemma14UniversalPerronSegmentSafeWeightedCoefficient_mono_right
        hP hPQ hQtwo hHR
    _ ≤ lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 /
        (H : ℝ) ^ 2 :=
      lemma14UniversalPerronSegmentSafeWeightedCoefficient_le hP hHR hHP

/-- Direct composition with the source-correct continuous Perron/Fatou
endpoint.  Both the central vertical energy and the safe weighted far tail
remain visible for the finite Halasz and Ramaré estimates. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_verticalEnergy_add_weightedHigh
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {X H : ℕ} (hH : 0 < H) {T Efar : ℝ}
    (hT : 0 < T) (hEfar : 0 ≤ Efar)
    (hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤ Efar) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H / (H : ℝ) ^ 2 ≤
      2 * (X : ℝ) *
        (Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          (2 * T) *
            (∫ t in -T..T,
              Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t))) +
      4 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * Efar := by
  have hbase :=
    normalized_uncenteredShortIntervalMeanSquare_le_central_add_weightedHigh
      S f Y (X := X) hH hT hEfar hfar
  have hcentral := integral_normSq_perronKernelSegmentOn_le_verticalEnergy
    (dyadicVerticalDirichletPolynomial S f Y)
    (continuous_dyadicVerticalDirichletPolynomial S f Y)
    (X := X) (H := H) hH hT.le
  calc
    uncenteredShortIntervalMeanSquare
          (dyadicRestrictedCoefficient S f Y) X H / (H : ℝ) ^ 2 ≤
        2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
          Complex.normSq (perronKernelSegmentOn
            (dyadicVerticalDirichletPolynomial S f Y) x H (-T) T)) +
        4 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * Efar := hbase
    _ ≤ 2 * ((X : ℝ) *
          (Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
            (2 * T) *
              (∫ t in -T..T,
                Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)))) +
        4 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H * Efar := by
      nlinarith [hcentral]
    _ = _ := by ring

end

end Erdos67b
