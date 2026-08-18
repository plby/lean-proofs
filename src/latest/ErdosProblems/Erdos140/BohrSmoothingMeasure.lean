import ErdosProblems.Erdos140.BohrEstimates
import ErdosProblems.Erdos140.Chang
import Mathlib.Data.Complex.BigOperators

/-!
# Convolution-power smoothing measures on finite Bohr sets

This file supplies the counting-measure probability kernels used in the
relative Chang--Sanders argument.  The normalization is the one from
`FiniteConvolution.lean`: convolution is an ordinary finite sum, while each
nonempty normalized indicator has total mass one.
-/

open Finset
open scoped BigOperators NNReal

namespace Erdos140

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Convolution powers -/

/-- The counting-convolution power of a real function.  The zeroth power is
the unit point mass at the origin. -/
def convolutionPower (f : G → ℝ) : ℕ → G → ℝ
  | 0 => normalizedIndicator {0}
  | n + 1 => normalizedConvolution (convolutionPower f n) f

@[simp] theorem convolutionPower_zero (f : G → ℝ) :
    convolutionPower f 0 = normalizedIndicator {0} := rfl

@[simp] theorem convolutionPower_succ (f : G → ℝ) (n : ℕ) :
    convolutionPower f (n + 1) =
      normalizedConvolution (convolutionPower f n) f := rfl

/-- A convolution power of a nonnegative function is nonnegative. -/
theorem convolutionPower_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ convolutionPower f n x := by
  intro n
  induction n with
  | zero =>
      exact normalizedIndicator_nonneg {0}
  | succ n ihn =>
      exact normalizedConvolution_nonneg ihn hf

/-- A convolution power of a probability density again has mass one. -/
theorem sum_convolutionPower {f : G → ℝ} (hf : ∑ x : G, f x = 1) :
    ∀ n, ∑ x : G, convolutionPower f n x = 1 := by
  intro n
  induction n with
  | zero =>
      exact sum_normalizedIndicator (singleton_nonempty 0)
  | succ n ihn =>
      rw [convolutionPower_succ, sum_normalizedConvolution, ihn, hf, one_mul]

/-- The `n`-fold convolution of the normalized measure of `B_σ` is
supported on `B_(nσ)`. -/
theorem convolutionPower_normalizedIndicator_support
    (B : BohrData G) (σ : ℝ≥0) :
    ∀ n x, convolutionPower (normalizedIndicator (B.dilate σ).carrier) n x ≠ 0 →
      x ∈ (B.dilate ((n : ℝ≥0) * σ)).carrier := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by
        simpa using
          (normalizedIndicator_ne_zero_iff (singleton_nonempty 0) x).mp hx
      subst x
      simpa using (B.dilate 0).zero_mem_carrier
  | succ n ihn =>
      intro x hx
      rw [convolutionPower_succ, normalizedConvolution] at hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hypow : convolutionPower (normalizedIndicator (B.dilate σ).carrier) n y ≠ 0 :=
        (mul_ne_zero_iff.mp hy).1
      have hysmall : normalizedIndicator (B.dilate σ).carrier (x - y) ≠ 0 :=
        (mul_ne_zero_iff.mp hy).2
      have hyB := ihn y hypow
      have hxyB : x - y ∈ (B.dilate σ).carrier :=
        (normalizedIndicator_ne_zero_iff
          (B.dilate σ).carrier_nonempty (x - y)).mp hysmall
      have hadd := BohrData.add_mem_dilate hyB hxyB
      have hxsum : y + (x - y) = x := by simp [add_comm]
      rw [hxsum] at hadd
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using hadd

/-! ## Counting-mass Fourier coefficients -/

/-- The unnormalized Fourier coefficient of a real counting-mass density.
There is deliberately no ambient factor `|G|⁻¹` here. -/
def massCoeff (w : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, (w x : ℂ) * ψ x

/-- The mass coefficient of a normalized indicator is its unnormalized
indicator Fourier sum divided by the cardinality. -/
theorem massCoeff_normalizedIndicator (A : Finset G) (ψ : AddChar G ℂ) :
    massCoeff (normalizedIndicator A) ψ =
      ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
  calc
    massCoeff (normalizedIndicator A) ψ =
        ∑ x ∈ A, ((A.card : ℝ)⁻¹ : ℂ) * ψ x := by
      rw [massCoeff, ← Finset.sum_subset (s₁ := A) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [normalizedIndicator, hx]
      · simp
      · intro x hxU hxA
        simp [normalizedIndicator, hxA]
    _ = ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
      rw [Chang.spectrumSum, Finset.mul_sum]

/-- Outside Chang's half-large spectrum, the normalized indicator has mass
Fourier coefficient strictly smaller than one half. -/
theorem norm_massCoeff_normalizedIndicator_lt_half_of_not_mem_largeSpectrum
    (C : BohrData G) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ Chang.largeSpectrum C.carrier (1 / 2)) :
    ‖massCoeff (normalizedIndicator C.carrier) ψ‖ < 1 / 2 := by
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hspectrum :
      ‖Chang.spectrumSum C.carrier ψ‖ < (1 / 2 : ℝ) * C.carrier.card := by
    apply lt_of_not_ge
    intro h
    exact hψ (Chang.mem_largeSpectrum.mpr h)
  calc
    ‖massCoeff (normalizedIndicator C.carrier) ψ‖ =
        (C.carrier.card : ℝ)⁻¹ * ‖Chang.spectrumSum C.carrier ψ‖ := by
      rw [massCoeff_normalizedIndicator, norm_mul]
      simp [norm_inv, Complex.norm_natCast]
    _ < (C.carrier.card : ℝ)⁻¹ *
        ((1 / 2 : ℝ) * C.carrier.card) :=
      mul_lt_mul_of_pos_left hspectrum (inv_pos.mpr hcard)
    _ = 1 / 2 := by field_simp

/-- Counting convolution turns into multiplication of mass Fourier
coefficients. -/
theorem massCoeff_normalizedConvolution (f g : G → ℝ) (ψ : AddChar G ℂ) :
    massCoeff (normalizedConvolution f g) ψ = massCoeff f ψ * massCoeff g ψ := by
  unfold massCoeff normalizedConvolution
  push_cast
  calc
    ∑ x : G, (∑ y : G, (f y : ℂ) * (g (x - y) : ℂ)) * ψ x =
        ∑ x : G, ∑ y : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ y : G, ∑ x : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x :=
      Finset.sum_comm
    _ =
        ∑ y : G, ((f y : ℂ) * ψ y) *
          ∑ z : G, (g z : ℂ) * ψ z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z ↦ ?_
      have hψ : ψ z = ψ y * ψ (z - y) := by
        calc
          ψ z = ψ (y + (z - y)) := congrArg ψ (by simp [add_comm])
          _ = ψ y * ψ (z - y) := AddChar.map_add_eq_mul ψ y (z - y)
      simp only [Equiv.subRight_apply]
      rw [hψ]
      ring
    _ = (∑ y : G, (f y : ℂ) * ψ y) *
        ∑ z : G, (g z : ℂ) * ψ z := by
      simpa using
        (Finset.sum_mul (univ : Finset G) (fun y ↦ (f y : ℂ) * ψ y)
          (∑ z : G, (g z : ℂ) * ψ z)).symm

/-- Fourier coefficients of convolution powers are ordinary powers. -/
theorem massCoeff_convolutionPower (f : G → ℝ) (ψ : AddChar G ℂ) :
    ∀ n, massCoeff (convolutionPower f n) ψ = massCoeff f ψ ^ n := by
  intro n
  induction n with
  | zero =>
      unfold massCoeff
      rw [Fintype.sum_eq_single 0]
      · simp [normalizedIndicator]
      · intro y hy
        simp [normalizedIndicator, hy]
  | succ n ihn =>
      rw [convolutionPower_succ, massCoeff_normalizedConvolution, ihn, pow_succ]

/-- A nonnegative mass has Fourier magnitude at most its total mass. -/
theorem norm_massCoeff_le_sum {w : G → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ψ : AddChar G ℂ) :
    ‖massCoeff w ψ‖ ≤ ∑ x : G, w x := by
  unfold massCoeff
  calc
    ‖∑ x : G, (w x : ℂ) * ψ x‖ ≤
        ∑ x : G, ‖(w x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x : G, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [norm_mul, hw x]

/-! ## The Bohr smoothing measure -/

/-- The outer Bohr probability measure smoothed by `n` copies of the inner
measure at scale `σ`. -/
def bohrSmoothingMeasure (B : BohrData G) (σ : ℝ≥0) (n : ℕ) : G → ℝ :=
  normalizedConvolution
    (normalizedIndicator (B.dilate (1 + (n : ℝ≥0) * σ)).carrier)
    (convolutionPower (normalizedIndicator (B.dilate σ).carrier) n)

/-- The Bohr smoothing measure is nonnegative. -/
theorem bohrSmoothingMeasure_nonneg (B : BohrData G) (σ : ℝ≥0) (n : ℕ) (x : G) :
    0 ≤ bohrSmoothingMeasure B σ n x := by
  exact normalizedConvolution_nonneg
    (normalizedIndicator_nonneg _)
    (convolutionPower_nonneg (normalizedIndicator_nonneg _) n) x

/-- The Bohr smoothing measure has total mass one. -/
theorem sum_bohrSmoothingMeasure (B : BohrData G) (σ : ℝ≥0) (n : ℕ) :
    ∑ x : G, bohrSmoothingMeasure B σ n x = 1 := by
  rw [bohrSmoothingMeasure, sum_normalizedConvolution,
    sum_normalizedIndicator (B.dilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty,
    sum_convolutionPower
      (sum_normalizedIndicator (B.dilate σ).carrier_nonempty), one_mul]

/-- On the central carrier, the smoothing measure is exactly the constant
value of its outer normalized Bohr measure. -/
theorem bohrSmoothingMeasure_apply_of_mem
    (B : BohrData G) (σ : ℝ≥0) (n : ℕ) {x : G} (hx : x ∈ B.carrier) :
    bohrSmoothingMeasure B σ n x =
      (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
  rw [bohrSmoothingMeasure, normalizedConvolution_comm]
  simp only [normalizedConvolution]
  calc
    ∑ t : G, convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t *
          normalizedIndicator (B.dilate (1 + (n : ℝ≥0) * σ)).carrier (x - t) =
        ∑ t : G, convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t *
          (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hνt :
          convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t = 0
      · simp [hνt]
      · have htB : t ∈ (B.dilate ((n : ℝ≥0) * σ)).carrier :=
          convolutionPower_normalizedIndicator_support B σ n t hνt
        have hxt : x - t ∈
            (B.dilate (1 + (n : ℝ≥0) * σ)).carrier := by
          exact BohrData.sub_mem_dilate
            (B := B) (s := 1) (t := (n : ℝ≥0) * σ)
            (by simpa using hx) htB
        rw [normalizedIndicator_apply_mem hxt]
    _ = (∑ t : G,
          convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t) *
        (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [sum_convolutionPower
        (sum_normalizedIndicator (B.dilate σ).carrier_nonempty)]
      simp

/-- Rank regularity bounds the carrier at the total smoothing radius by
twice the central carrier. -/
theorem card_dilate_one_add_le_two_mul
    {B : BohrData G} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0)) :
    (B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card ≤
      2 * B.carrier.card := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  let d : ℕ := max B.rank 1
  have hcards := hreg κ (by simpa [κ, d] using hsmall)
  have hfactor : (1 + 100 * (d : ℝ) * (κ : ℝ)) ≤ 2 := by
    have hsmallR : (κ : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
      exact_mod_cast (show κ ≤ 1 / (100 * (d : ℝ≥0)) by
        simpa [κ, d] using hsmall)
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
    calc
      1 + 100 * (d : ℝ) * (κ : ℝ) ≤
          1 + 100 * (d : ℝ) * (1 / (100 * (d : ℝ))) := by gcongr
      _ = 2 := by field_simp; ring
  have hcardR :
      ((B.dilate (1 + κ)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.dilate (1 + κ)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (κ : ℝ)) * (B.carrier.card : ℝ) := by
        simpa [κ, d] using hcards.2
      _ ≤ 2 * (B.carrier.card : ℝ) := by gcongr
  exact_mod_cast hcardR

/-- Under rank regularity at total smoothing radius `nσ`, the central Bohr
probability measure is pointwise at most twice the smoothing measure. -/
theorem normalizedIndicator_le_two_mul_bohrSmoothingMeasure
    {B : BohrData G} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0)) (x : G) :
    normalizedIndicator B.carrier x ≤ 2 * bohrSmoothingMeasure B σ n x := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  by_cases hx : x ∈ B.carrier
  · rw [normalizedIndicator_apply_mem hx,
      bohrSmoothingMeasure_apply_of_mem B σ n hx]
    have hcard := card_dilate_one_add_le_two_mul hreg n hsmall
    have hcardR :
        (((B.dilate (1 + κ)).carrier.card : ℕ) : ℝ) ≤
          2 * (B.carrier.card : ℝ) := by
      exact_mod_cast (show (B.dilate (1 + κ)).carrier.card ≤
        2 * B.carrier.card by simpa [κ] using hcard)
    have hBpos : (0 : ℝ) < B.carrier.card := by
      exact_mod_cast B.carrier_nonempty.card_pos
    have hOuterPos : (0 : ℝ) < (B.dilate (1 + κ)).carrier.card := by
      exact_mod_cast (B.dilate (1 + κ)).carrier_nonempty.card_pos
    rw [show (1 + (n : ℝ≥0) * σ) = 1 + κ by rfl]
    have hdiv : 1 / (B.carrier.card : ℝ) ≤
        2 / ((B.dilate (1 + κ)).carrier.card : ℝ) := by
      rw [div_le_div_iff₀ hBpos hOuterPos]
      simpa [mul_comm] using hcardR
    simpa only [one_div, div_eq_mul_inv, one_mul] using hdiv
  · rw [normalizedIndicator_apply_not_mem hx]
    exact mul_nonneg (by norm_num) (bohrSmoothingMeasure_nonneg B σ n x)

/-- The outer normalized Bohr factor has Fourier magnitude at most one, so
the smoothing measure inherits the `n`th power decay of its inner factor. -/
theorem norm_massCoeff_bohrSmoothingMeasure_le
    (B : BohrData G) (σ : ℝ≥0) (n : ℕ) (ψ : AddChar G ℂ) :
    ‖massCoeff (bohrSmoothingMeasure B σ n) ψ‖ ≤
      ‖massCoeff (normalizedIndicator (B.dilate σ).carrier) ψ‖ ^ n := by
  rw [bohrSmoothingMeasure, massCoeff_normalizedConvolution,
    massCoeff_convolutionPower, norm_mul, norm_pow]
  have houter :
      ‖massCoeff (normalizedIndicator
        (B.dilate (1 + (n : ℝ≥0) * σ)).carrier) ψ‖ ≤ 1 := by
    simpa [sum_normalizedIndicator
      (B.dilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty] using
      norm_massCoeff_le_sum
        (w := normalizedIndicator
          (B.dilate (1 + (n : ℝ≥0) * σ)).carrier)
        (normalizedIndicator_nonneg _) ψ
  exact mul_le_of_le_one_left (by positivity) houter

#print axioms Erdos140.convolutionPower_normalizedIndicator_support
#print axioms Erdos140.massCoeff_normalizedIndicator
#print axioms Erdos140.norm_massCoeff_normalizedIndicator_lt_half_of_not_mem_largeSpectrum
#print axioms Erdos140.massCoeff_normalizedConvolution
#print axioms Erdos140.normalizedIndicator_le_two_mul_bohrSmoothingMeasure
#print axioms Erdos140.norm_massCoeff_bohrSmoothingMeasure_le

end

end Erdos140
