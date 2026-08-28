import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit algebra for the two real normal trivializations

These are the literal lower and upper normal frames. Their transition
identity, positive denominators, inverse formulae, radius identities, and
opposite-weight equivariance are proved directly over the complex numbers.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

/-- The positive real denominator of both inverse frames. -/
def denominator (a : ℂ) : ℝ := 1 + Complex.normSq a

theorem denominator_pos (a : ℂ) : 0 < denominator a := by
  have h := Complex.normSq_nonneg a
  dsimp [denominator]
  linarith

theorem denominator_ne_zero (a : ℂ) : denominator a ≠ 0 :=
  ne_of_gt (denominator_pos a)

theorem denominator_cast (a : ℂ) : (denominator a : ℂ) = 1 + conj a * a := by
  simp only [denominator, Complex.ofReal_add, Complex.ofReal_one,
    Complex.normSq_eq_conj_mul_self]

/-- The actual lower normal frame. -/
def lowerMap (a : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.2 - conj a * conj p.1, a * p.2 + conj p.1)

/-- The actual upper normal frame. -/
def upperMap (b : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (b * p.2 - conj p.1, p.2 + conj b * conj p.1)

/-- The unscaled numerator of the lower inverse. -/
def lowerInverseNumerator (a : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (conj (p.2 - a * p.1), p.1 + conj a * p.2)

/-- The unscaled numerator of the upper inverse. -/
def upperInverseNumerator (b : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (conj (b * p.2 - p.1), p.2 + conj b * p.1)

/-- The lower inverse, with the strictly positive real denominator. -/
def lowerInverse (a : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (denominator a)⁻¹ • lowerInverseNumerator a p

/-- The upper inverse, with the strictly positive real denominator. -/
def upperInverse (b : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (denominator b)⁻¹ • upperInverseNumerator b p

@[simp] theorem lowerMap_zero (a : ℂ) : lowerMap a 0 = 0 := by
  simp [lowerMap]

@[simp] theorem upperMap_zero (b : ℂ) : upperMap b 0 = 0 := by
  simp [upperMap]

theorem lowerMap_add (a : ℂ) (p q : ℂ × ℂ) :
    lowerMap a (p + q) = lowerMap a p + lowerMap a q := by
  apply Prod.ext <;>
    simp only [lowerMap, Prod.fst_add, Prod.snd_add, map_add, mul_add] <;> ring

theorem upperMap_add (b : ℂ) (p q : ℂ × ℂ) :
    upperMap b (p + q) = upperMap b p + upperMap b q := by
  apply Prod.ext <;>
    simp only [upperMap, Prod.fst_add, Prod.snd_add, map_add, mul_add] <;> ring

theorem lowerMap_real_smul (a : ℂ) (r : ℝ) (p : ℂ × ℂ) :
    lowerMap a (r • p) = r • lowerMap a p := by
  apply Prod.ext <;>
    simp only [lowerMap, Prod.smul_fst, Prod.smul_snd, Complex.real_smul,
      map_mul, Complex.conj_ofReal] <;> ring

theorem upperMap_real_smul (b : ℂ) (r : ℝ) (p : ℂ × ℂ) :
    upperMap b (r • p) = r • upperMap b p := by
  apply Prod.ext <;>
    simp only [upperMap, Prod.smul_fst, Prod.smul_snd, Complex.real_smul,
      map_mul, Complex.conj_ofReal] <;> ring

theorem lowerInverseNumerator_lowerMap (a : ℂ) (p : ℂ × ℂ) :
    lowerInverseNumerator a (lowerMap a p) = denominator a • p := by
  apply Prod.ext <;>
    simp only [lowerInverseNumerator, lowerMap, Prod.smul_fst, Prod.smul_snd,
      Complex.real_smul, denominator_cast, map_add, map_sub, map_mul,
      starRingEnd_self_apply] <;> ring

theorem lowerMap_lowerInverseNumerator (a : ℂ) (p : ℂ × ℂ) :
    lowerMap a (lowerInverseNumerator a p) = denominator a • p := by
  apply Prod.ext <;>
    simp only [lowerInverseNumerator, lowerMap, Prod.smul_fst, Prod.smul_snd,
      Complex.real_smul, denominator_cast, map_sub, map_mul,
      starRingEnd_self_apply] <;> ring

theorem upperInverseNumerator_upperMap (b : ℂ) (p : ℂ × ℂ) :
    upperInverseNumerator b (upperMap b p) = denominator b • p := by
  apply Prod.ext <;>
    simp only [upperInverseNumerator, upperMap, Prod.smul_fst, Prod.smul_snd,
      Complex.real_smul, denominator_cast, map_add, map_sub, map_mul,
      starRingEnd_self_apply] <;> ring

theorem upperMap_upperInverseNumerator (b : ℂ) (p : ℂ × ℂ) :
    upperMap b (upperInverseNumerator b p) = denominator b • p := by
  apply Prod.ext <;>
    simp only [upperInverseNumerator, upperMap, Prod.smul_fst, Prod.smul_snd,
      Complex.real_smul, denominator_cast, map_sub, map_mul,
      starRingEnd_self_apply] <;> ring

@[simp] theorem lowerInverse_lowerMap (a : ℂ) (p : ℂ × ℂ) :
    lowerInverse a (lowerMap a p) = p := by
  rw [lowerInverse, lowerInverseNumerator_lowerMap, smul_smul,
    inv_mul_cancel₀ (denominator_ne_zero a), one_smul]

@[simp] theorem lowerMap_lowerInverse (a : ℂ) (p : ℂ × ℂ) :
    lowerMap a (lowerInverse a p) = p := by
  rw [lowerInverse, lowerMap_real_smul, lowerMap_lowerInverseNumerator, smul_smul,
    inv_mul_cancel₀ (denominator_ne_zero a), one_smul]

@[simp] theorem upperInverse_upperMap (b : ℂ) (p : ℂ × ℂ) :
    upperInverse b (upperMap b p) = p := by
  rw [upperInverse, upperInverseNumerator_upperMap, smul_smul,
    inv_mul_cancel₀ (denominator_ne_zero b), one_smul]

@[simp] theorem upperMap_upperInverse (b : ℂ) (p : ℂ × ℂ) :
    upperMap b (upperInverse b p) = p := by
  rw [upperInverse, upperMap_real_smul, upperMap_upperInverseNumerator, smul_smul,
    inv_mul_cancel₀ (denominator_ne_zero b), one_smul]

/-- Exact compatibility with the native two-chart transition. -/
theorem upper_lower_compatibility (a : ℂ) (ha : a ≠ 0) (p : ℂ × ℂ) :
    upperMap a⁻¹ (a * p.1, a * p.2) = lowerMap a p := by
  have hc : conj a⁻¹ * conj a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  apply Prod.ext
  · change a⁻¹ * (a * p.2) - conj (a * p.1) = p.2 - conj a * conj p.1
    rw [map_mul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  · change a * p.2 + conj a⁻¹ * conj (a * p.1) = a * p.2 + conj p.1
    rw [map_mul, ← mul_assoc, hc, one_mul]

/-- The squared radius in the lower frame, with its actual positive scale. -/
theorem lowerMap_normSq (a : ℂ) (p : ℂ × ℂ) :
    Complex.normSq (lowerMap a p).1 + Complex.normSq (lowerMap a p).2 =
      denominator a * (Complex.normSq p.1 + Complex.normSq p.2) := by
  apply Complex.ofReal_injective
  simp only [lowerMap, Complex.ofReal_add, Complex.ofReal_mul,
    denominator_cast, Complex.normSq_eq_conj_mul_self,
    map_add, map_sub, map_mul, starRingEnd_self_apply]
  ring

/-- The squared radius in the upper frame, with its actual positive scale. -/
theorem upperMap_normSq (b : ℂ) (p : ℂ × ℂ) :
    Complex.normSq (upperMap b p).1 + Complex.normSq (upperMap b p).2 =
      denominator b * (Complex.normSq p.1 + Complex.normSq p.2) := by
  apply Complex.ofReal_injective
  simp only [upperMap, Complex.ofReal_add, Complex.ofReal_mul,
    denominator_cast, Complex.normSq_eq_conj_mul_self,
    map_add, map_sub, map_mul, starRingEnd_self_apply]
  ring

theorem conj_inv_of_normSq_eq_one (u : ℂ) (hu : Complex.normSq u = 1) :
    conj u⁻¹ = u := by
  rw [Complex.inv_def, hu]
  simp

/-- Opposite native weights become the same scalar weight in the lower frame. -/
theorem lowerMap_oppositeWeights (a u : ℂ) (hu : Complex.normSq u = 1) (p : ℂ × ℂ) :
    lowerMap a (u⁻¹ * p.1, u * p.2) = u • lowerMap a p := by
  apply Prod.ext <;>
    simp only [lowerMap, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul,
      conj_inv_of_normSq_eq_one u hu] <;> ring

/-- Opposite native weights become the same scalar weight in the upper frame. -/
theorem upperMap_oppositeWeights (b u : ℂ) (hu : Complex.normSq u = 1) (p : ℂ × ℂ) :
    upperMap b (u⁻¹ * p.1, u * p.2) = u • upperMap b p := by
  apply Prod.ext <;>
    simp only [upperMap, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul,
      conj_inv_of_normSq_eq_one u hu] <;> ring

theorem lowerMap_oppositeWeights_of_norm_eq_one
    (a u : ℂ) (hu : ‖u‖ = 1) (p : ℂ × ℂ) :
    lowerMap a (u⁻¹ * p.1, u * p.2) = u • lowerMap a p :=
  lowerMap_oppositeWeights a u (by simp [Complex.normSq_eq_norm_sq, hu]) p

theorem upperMap_oppositeWeights_of_norm_eq_one
    (b u : ℂ) (hu : ‖u‖ = 1) (p : ℂ × ℂ) :
    upperMap b (u⁻¹ * p.1, u * p.2) = u • upperMap b p :=
  upperMap_oppositeWeights b u (by simp [Complex.normSq_eq_norm_sq, hu]) p

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
