import ErdosProblems.Erdos67b.MRPowerAmplification
import ErdosProblems.Erdos67b.MRSourceProductMoment
import ErdosProblems.Erdos67b.MRCrossBlockEnergy

/-!
# Decay on a small-current, large-preceding frequency class

The source moment and the explicit factorial cost are combined here.
All threshold and block-separation conditions remain visible as arithmetic
inequalities; no short-interval or mean-value theorem is assumed.
-/

open scoped BigOperators Interval
open MeasureTheory

namespace Erdos67b

theorem crossBlockEnergy_source_decay
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {u v alpha beta delta : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (halpha : 0 ≤ alpha) (hdelta : 0 < delta)
    (hcost : 6 * Real.log (2 * v) / u ≤ delta) (hgap : delta ≤ beta - alpha)
    (hPlo : ∀ p ∈ P, Real.exp u ≤ p)
    (hPhi : ∀ p ∈ P, (p : ℝ) ≤ 2 * Real.exp u)
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ m ∈ S, (X : ℝ) / Real.exp v ≤ m)
    (hShi : ∀ m ∈ S, (m : ℝ) ≤ 2 * X / Real.exp v)
    {F : ℝ → ℂ} (hF : Continuous F) {E : Set ℝ} (hE : MeasurableSet E)
    {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F t‖ ≤ Real.exp (-beta * v))
    (hlarge : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      Real.exp (-alpha * u) ≤ ‖logarithmicDirichletPolynomial P a t‖) :
    (∫ t in -T..T, E.indicator
      (fun t ↦ ‖F t * logarithmicDirichletPolynomial S b t‖ ^ 2) t) ≤
      32 * Real.exp 12 * (1 + Real.pi) * (T / X + 1) *
        Real.exp ((1 + 2 * alpha) * u - delta * v) := by
  let k : ℕ := Nat.ceil (v / u)
  have hY : 2 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hZ : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr (by linarith)
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have hpos : (0 : ℝ) < (X : ℝ) / Real.exp v := by positivity
    exact_mod_cast hpos.trans_le (hSlo m hm)
  have hmoment := primeCofactorPolynomial_source_intervalIntegral_le hP ha hb hY hZ hPlo hPhi
    hX hSlo hShi (k := k) (by simp only [Real.log_exp]; rfl) hT
  have hrestrict := intervalIntegral_indicator_norm_sq_mul_le_cross_power hF
    (continuous_logarithmicDirichletPolynomial P a)
    (continuous_logarithmicDirichletPolynomial S b) hE hT
    (Real.exp_pos _).le (Real.exp_pos _) hsmall hlarge k
  calc
    _ ≤ (Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
        ∫ t in -T..T,
          ‖logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t‖ ^ 2 :=
      hrestrict
    _ ≤ (Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
        (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
          (T / X + Real.pi * 2 ^ (k + 2) * Real.exp u)) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ ≤ _ := crossBlock_amplification_decay hu huv halpha hdelta (by positivity) hcost hgap rfl

/-- Exact natural-division endpoints of the Ramaré rectangle fit a
width-eight cofactor interval at the shifted logarithmic scale. -/
theorem mrDyadicCofactorRectangle_shifted_bounds
    {I : ℕ × ℕ} {X m : ℕ} {v : ℝ}
    (hlo : Real.exp v ≤ I.1) (hhi : (I.2 : ℝ) ≤ Real.exp (v + 1))
    (hI : 0 < I.2) (hm : m ∈ mrDyadicCofactorRectangle I X) :
    (X : ℝ) / Real.exp (v + 1) ≤ m ∧
      (m : ℝ) ≤ 8 * X / Real.exp (v + 1) := by
  have hIlo : 0 < I.1 := by
    exact_mod_cast (Real.exp_pos v).trans_le hlo
  obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hm
  have hmprodlo : (X : ℝ) < (m : ℝ) * I.2 := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hI).mp hmlo
  have hmprodhi : (m : ℝ) * I.1 ≤ 2 * X := by
    exact_mod_cast (Nat.le_div_iff_mul_le hIlo).mp hmhi
  constructor
  · apply (div_le_iff₀ (Real.exp_pos _)).mpr
    exact hmprodlo.le.trans (mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg _))
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hbase : (m : ℝ) * Real.exp v ≤ 2 * X :=
      (mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg _)).trans hmprodhi
    rw [Real.exp_add v 1, ← mul_assoc]
    have hexp : Real.exp 1 ≤ 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
    calc
      _ ≤ (2 * X) * Real.exp 1 := mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
      _ ≤ (2 * X) * 4 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring

/-- Cross-block energy with the enlarged cofactor support needed by the
finite Ramaré factorization. -/
theorem crossBlockEnergy_enlarged_decay
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {u v alpha beta delta : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (halpha : 0 ≤ alpha) (hbeta : beta ≤ 1 / 4) (hdelta : 0 < delta)
    (hcost : 6 * Real.log (2 * (v + 1)) / u ≤ delta) (hgap : delta ≤ beta - alpha)
    (hPlo : ∀ p ∈ P, Real.exp u ≤ p)
    (hPhi : ∀ p ∈ P, (p : ℝ) ≤ 2 * Real.exp u)
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ m ∈ S, (X : ℝ) / Real.exp (v + 1) ≤ m)
    (hShi : ∀ m ∈ S, (m : ℝ) ≤ 8 * X / Real.exp (v + 1))
    {F : ℝ → ℂ} (hF : Continuous F) {E : Set ℝ} (hE : MeasurableSet E)
    {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F t‖ ≤ Real.exp (-beta * v))
    (hlarge : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      Real.exp (-alpha * u) ≤ ‖logarithmicDirichletPolynomial P a t‖) :
    (∫ t in -T..T, E.indicator
      (fun t ↦ ‖F t * logarithmicDirichletPolynomial S b t‖ ^ 2) t) ≤
      128 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) *
        Real.exp ((1 + 2 * alpha) * u - delta * v) := by
  let k : ℕ := Nat.ceil ((v + 1) / u)
  have hY : 2 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hZ : 1 ≤ Real.exp (v + 1) := Real.one_le_exp_iff.mpr (by linarith)
  have hmoment := primeCofactorPolynomial_powerWidth_intervalIntegral_le hP ha hb hY hZ hPlo hPhi
    hX hSlo (width := 3) (by norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num]; exact hShi)
    (k := k) (by simp only [Real.log_exp]; rfl) hT
  have hrestrict := intervalIntegral_indicator_norm_sq_mul_le_cross_power hF
    (continuous_logarithmicDirichletPolynomial P a)
    (continuous_logarithmicDirichletPolynomial S b) hE hT
    (Real.exp_pos _).le (Real.exp_pos _) hsmall hlarge k
  calc
    _ ≤ (Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
        ∫ t in -T..T,
          ‖logarithmicDirichletPolynomial P a t ^ k * logarithmicDirichletPolynomial S b t‖ ^ 2 :=
      hrestrict
    _ ≤ (Real.exp (-beta * v) ^ 2 * (Real.exp (-alpha * u) ^ (2 * k))⁻¹) *
        (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 *
          (T / X + Real.pi * 2 ^ (k + 4) * Real.exp u)) := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      simpa only [Nat.add_assoc] using hmoment
    _ ≤ _ := crossBlock_amplification_enlarged_decay hu huv halpha hbeta hdelta
      (by positivity) hcost hgap rfl

end Erdos67b
