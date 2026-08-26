import ErdosProblems.Erdos747.PathwiseAggregateRegularity
import ErdosProblems.Erdos747.AggregatePresentSpread

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Vanishing normalized errors for present-edge spreading -/

def normalizedLocalSpreadError (n : ℕ) (C e : ℝ) : ℝ :=
  Real.sqrt (12 * (3 * C + 12 / Real.sqrt (n : ℝ) +
    10 * (Real.sqrt (Real.sqrt e * Real.sqrt 3) * Real.sqrt 3)))

def normalizedSpreadTolerance (n : ℕ) (C e q eta B : ℝ) : ℝ :=
  Real.sqrt (normalizedLocalSpreadError n C e / 3 + q + eta * (1 + B))

lemma normalizedLocalSpreadError_nonneg (n : ℕ) (C e : ℝ) :
    0 ≤ normalizedLocalSpreadError n C e := Real.sqrt_nonneg _

lemma normalizedLocalSpreadError_pos (n : ℕ) (C e : ℝ)
    (hn : 0 < n) (hC : 0 ≤ C) : 0 < normalizedLocalSpreadError n C e := by
  unfold normalizedLocalSpreadError
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  have ht : 0 ≤ 10 * (Real.sqrt (Real.sqrt e * Real.sqrt 3) * Real.sqrt 3) := by positivity
  apply Real.sqrt_pos.mpr
  positivity

lemma normalizedSpreadTolerance_pos (n : ℕ) (C e q eta B : ℝ)
    (hn : 0 < n) (hC : 0 ≤ C) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hB : 0 ≤ B) :
    0 < normalizedSpreadTolerance n C e q eta B := by
  unfold normalizedSpreadTolerance
  have hs := normalizedLocalSpreadError_pos n C e hn hC
  apply Real.sqrt_pos.mpr
  positivity

/-- The nested square-root entropy budget has a normalization independent
of the graph and of its edge density. -/
lemma normalizedLocalSpreadError_budget
    (n : ℕ) (C e : ℝ) (hn : 0 < n) (hC : 0 ≤ C) (he : 0 ≤ e) :
    (3 * n : ℝ) * (4 * (3 * C * n + 12 * Real.sqrt n +
      10 * (Real.sqrt (Real.sqrt (e * n) * Real.sqrt (3 * n : ℝ)) *
        Real.sqrt (3 * n : ℝ)))) =
      ((n : ℝ) * normalizedLocalSpreadError n C e)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have hsq := Real.sq_sqrt hnR.le
  have heN : Real.sqrt (e * n) = Real.sqrt e * Real.sqrt n := Real.sqrt_mul he _
  have h3N : Real.sqrt (3 * n : ℝ) = Real.sqrt 3 * Real.sqrt n :=
    Real.sqrt_mul (by norm_num) _
  have hmix : Real.sqrt (Real.sqrt (e * n) * Real.sqrt (3 * n : ℝ)) =
      Real.sqrt (Real.sqrt e * Real.sqrt 3) * Real.sqrt n := by
    rw [heN, h3N]
    have hid : (Real.sqrt e * Real.sqrt n) * (Real.sqrt 3 * Real.sqrt n) =
        (Real.sqrt e * Real.sqrt 3) * (n : ℝ) := by
      calc
        _ = (Real.sqrt e * Real.sqrt 3) * (Real.sqrt n)^2 := by ring
        _ = _ := by rw [hsq]
    rw [hid, Real.sqrt_mul (by positivity)]
  have hlocal : (normalizedLocalSpreadError n C e)^2 =
      12 * (3 * C + 12 / Real.sqrt (n : ℝ) +
        10 * (Real.sqrt (Real.sqrt e * Real.sqrt 3) * Real.sqrt 3)) := by
    exact Real.sq_sqrt (by positivity)
  rw [hmix, h3N, mul_pow, hlocal]
  field_simp [hs]
  rw [hsq]
  nlinarith [hsq]

lemma normalizedSpreadTolerance_budget
    (n : ℕ) (C e q eta B : ℝ) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hB : 0 ≤ B) :
    (n : ℝ) * normalizedLocalSpreadError n C e + (3 * n : ℝ) * (q + eta * (1 + B)) =
      3 * normalizedSpreadTolerance n C e q eta B *
        normalizedSpreadTolerance n C e q eta B * n := by
  have hsq : (normalizedSpreadTolerance n C e q eta B)^2 =
      normalizedLocalSpreadError n C e / 3 + q + eta * (1 + B) := by
    apply Real.sq_sqrt
    have hlocal := normalizedLocalSpreadError_nonneg n C e
    positivity
  nlinarith

lemma normalizedLocalSpreadError_tendsto_zero
    (C e : ℕ → ℝ) (hC : Tendsto C atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedLocalSpreadError n (C n) (e n)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hroot := ((he.sqrt.mul_const (Real.sqrt 3)).sqrt).mul_const (Real.sqrt 3)
  have hlim := (((hC.const_mul 3).add (hinv.const_mul 12)).add (hroot.const_mul 10)).const_mul 12
  have hs := hlim.sqrt
  simpa only [normalizedLocalSpreadError, div_eq_mul_inv, zero_mul, mul_zero,
    add_zero, Real.sqrt_zero] using hs

lemma normalizedSpreadTolerance_tendsto_zero
    (C e q eta : ℕ → ℝ) (B : ℝ)
    (hC : Tendsto C atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun n ↦ normalizedSpreadTolerance n (C n) (e n) (q n) (eta n) B)
      atTop (𝓝 0) := by
  have hlim := (((normalizedLocalSpreadError_tendsto_zero C e hC he).div_const 3).add hq).add
    (heta.mul_const (1 + B))
  simpa only [normalizedSpreadTolerance, zero_div, zero_mul, add_zero, Real.sqrt_zero]
    using hlim.sqrt

/-- A normalized entropy bound supplies present-edge spreading with a
single explicit tolerance used both for accuracy and exceptional density. -/
lemma kahnAggregateInsertionGood_presentWeightSpread_normalized
    {n M cap : ℕ} {C e sigma q eta B : ℝ}
    (hn : 3 ≤ n) (hM : 0 < M) (hcap : 0 < cap)
    (hC : 0 ≤ C) (he : 0 ≤ e) (hsigma : 0 < sigma)
    (hq : 0 ≤ q) (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hratio : 1 < ((3 * M : ℕ) : ℝ) * sigma / ((18 * n * cap : ℕ) : ℝ))
    (herror : (3 * n : ℝ) * Real.sqrt sigma +
      (3 * n : ℝ) * (C + 14 + Real.log 2) /
        Real.log (((3 * M : ℕ) : ℝ) * sigma / ((18 * n * cap : ℕ) : ℝ)) ≤ e * n)
    {H : Finset (Edge n)}
    (hGood : KahnAggregateInsertionGood n M cap C q eta B H) :
    PresentWeightSpread H (normalizedSpreadTolerance n C e q eta B)
      (normalizedSpreadTolerance n C e q eta B) := by
  apply kahnAggregateInsertionGood_presentWeightSpread_self
    (E := e * n) (sigma := sigma) (S := (n : ℝ) * normalizedLocalSpreadError n C e)
    hn hM hcap hC hsigma hratio herror hq hB
    (mul_nonneg (Nat.cast_nonneg n) (normalizedLocalSpreadError_nonneg n C e))
    (normalizedSpreadTolerance_pos n C e q eta B (by omega) hC hq heta hB)
    (Real.sqrt_nonneg _) _ _ hGood
  · exact (normalizedLocalSpreadError_budget n C e (by omega) hC he).le
  · exact (normalizedSpreadTolerance_budget n C e q eta B hq heta hB).le

end

end Erdos747
