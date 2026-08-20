module
public import ErdosProblems.Erdos515.External.Ray.Schwarz.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import ErdosProblems.Erdos515.External.Ray.Misc.Bound

/-!
## Facts about Möbius transforms

We consider only Möbius transform of the form `z ↦ (w - z) / (1 - conj w * z)`, which is what we
need to prove the Schwarz-Pick theorem.
-/

open Metric (ball isOpen_ball)
open Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section

variable {w z a : ℂ} {r : ℝ}

/-- Our Möbius denominator is nonsingular -/
public lemma norm_mobius_denom_pos (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : 0 < ‖1 - conj w * z‖ := by
  calc ‖1 - conj w * z‖
    _ ≥ ‖(1 : ℂ)‖ - ‖conj w * z‖ := by bound
    _ = 1 - ‖w‖ * ‖z‖ := by simp
    _ ≥ 1 - ‖z‖ := by bound
    _ > 0 := by linarith

/-- Our Möbius denominator is nonsingular -/
public lemma mobius_denom_ne_zero (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : 1 - conj w * z ≠ 0 :=
  norm_pos_iff.mp (norm_mobius_denom_pos w1 z1)

/-- Our Möbius transforms map the unit disk to itself -/
public lemma mapsTo_mobius (w1 : ‖w‖ < 1) : MapsTo (mobius w) (ball 0 1) (ball 0 1) := by
  intro z z1
  simp only [Metric.mem_ball, dist_zero_right] at z1
  simp only [Metric.mem_ball, dist_zero_right, mobius, Complex.norm_div,
    div_lt_iff₀ (norm_mobius_denom_pos w1 z1), one_mul]
  rw [← sq_lt_sq₀ (by bound) (by bound), ← Complex.ofReal_re (‖w - z‖ ^ 2),
    ← Complex.ofReal_re (‖1 - (starRingEnd ℂ) w * z‖ ^ 2)]
  simp only [← Complex.conj_mul', Complex.ofReal_pow, map_sub, mul_sub, sub_mul, Complex.sub_re,
    mul_one, map_one, Complex.one_re, Complex.conj_conj, map_mul, one_mul]
  rw [← sub_pos]
  ring_nf
  refine lt_of_lt_of_le (b := (1 - ‖w‖ ^ 2 : ℂ).re * (1 - ‖z‖ ^ 2 : ℂ).re) ?_ (le_of_eq ?_)
  · simp only [Complex.ofReal_re, ← Complex.ofReal_pow, Complex.sub_re, Complex.one_re]
    bound
  · simp only [Complex.conj_mul', ← mul_assoc, mul_comm _ (conj w)]
    simp only [mul_assoc, Complex.conj_mul', Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow,
      Complex.ofReal_re, ← Complex.ofReal_mul]
    ring

/-- Our Möbius transforms are analytic -/
public lemma contDiffAt_mobius {n : WithTop ℕ∞} (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) :
    ContDiffAt ℂ n (mobius w) z := by
  refine ContDiffAt.div (by fun_prop) (by fun_prop) ?_
  exact mobius_denom_ne_zero w1 z1

/-- Our Möbius transforms are analytic -/
public lemma contDiffOn_mobius {n : WithTop ℕ∞} (w1 : ‖w‖ < 1) :
    ContDiffOn ℂ n (mobius w) (ball 0 1) :=
  fun z z1 ↦ (contDiffAt_mobius w1 (by simpa using z1)).contDiffWithinAt

/-- Our Möbius transforms map the unit disk to itself -/
public lemma norm_mobius_lt_one (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : ‖mobius w z‖ < 1 := by
  simpa using mapsTo_mobius w1 (x := z) (by simpa)

/-- Our Möbius transforms are involutions -/
public lemma mobius_mobius (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : mobius w (mobius w z) = z := by
  have n1 := mobius_denom_ne_zero w1 z1
  have n2 := mobius_denom_ne_zero w1 (norm_mobius_lt_one w1 z1)
  simp only [mobius] at n1 n2 ⊢
  rw [div_eq_iff n2, ← mul_left_inj' n1]
  simp only [sub_mul, div_mul_cancel₀ _ n1, mul_assoc]
  ring

/-- Möbius transforms are homeomorphisms -/
def mobiusHom (w1 : ‖w‖ < 1) : OpenPartialHomeomorph ℂ ℂ where
  toFun := mobius w
  invFun := mobius w
  source := ball 0 1
  target := ball 0 1
  map_source' := mapsTo_mobius w1
  map_target' := mapsTo_mobius w1
  left_inv' z z1 := mobius_mobius w1 (by simpa using z1)
  right_inv' z z1 := mobius_mobius w1 (by simpa using z1)
  open_source := isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := (contDiffOn_mobius w1 (n := ω)).continuousOn
  continuousOn_invFun := (contDiffOn_mobius w1 (n := ω)).continuousOn

-- Facts pulled out of `mobiusHom`
public lemma injOn_mobius (w1 : ‖w‖ < 1) : InjOn (mobius w) (ball 0 1) := (mobiusHom w1).injOn
public lemma surjOn_mobius (w1 : ‖w‖ < 1) : SurjOn (mobius w) (ball 0 1) (ball 0 1) :=
  (mobiusHom w1).surjOn
public lemma bijOn_mobius (w1 : ‖w‖ < 1) : BijOn (mobius w) (ball 0 1) (ball 0 1) :=
  (mobiusHom w1).bijOn
@[simp] public lemma image_mobius (w1 : ‖w‖ < 1) : mobius w '' ball 0 1 = ball 0 1 :=
  (mobiusHom w1).image_source_eq_target

@[simp] public lemma mobius_zero : mobius w 0 = w := by simp [mobius]
@[simp] public lemma mobius_self : mobius w w = 0 := by simp [mobius]

public lemma mobius_eq_zero_iff (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) :
    mobius w z = 0 ↔ w = z := by
  simp only [mobius, div_eq_zero_iff, sub_eq_zero, or_iff_left_iff_imp]
  intro e
  have lt : ‖conj w * z‖ < 1 := by
    calc ‖conj w * z‖
      _ = ‖w‖ * ‖z‖ := by simp
      _ < 1 * 1 := by apply mul_lt_mul' <;> bound
      _ = 1 := by norm_num
  simp only [← e, one_mem, CStarRing.norm_of_mem_unitary, lt_self_iff_false] at lt

/-- Convenience lemma to pull a inverse scale out of a Möbius denominator -/
public lemma mobius_denom_inv_mul (r0 : r ≠ 0) (w z : ℂ) :
    (1 - conj (r⁻¹ * w) * (r⁻¹ * z)) = r⁻¹ ^ 2 * (r ^ 2 - conj w * z) := by
  rw [Complex.ofReal_inv, inv_pow, ← div_eq_inv_mul _ (_ ^ 2), eq_div_iff (by simpa)]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, sub_mul, one_mul]
  have r0' : (r : ℂ) ≠ 0 := by simp [r0]
  field_simp

/-- The derivative of a Möbius transform anywhere -/
public lemma hasDerivAt_mobius (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) :
    HasDerivAt (mobius w) ((‖w‖ ^ 2 - 1) / (1 - conj w * z) ^ 2) z := by
  suffices h : HasDerivAt (mobius w) (((-1) * (1 - conj w * z) - (w - z) * -(conj w * 1)) /
      (1 - conj w * z) ^ 2) z by
    simpa [sub_mul, Complex.mul_conj', mul_comm z] using h
  exact ((hasDerivAt_id' _).const_sub _).div (((hasDerivAt_id' _).const_mul _).const_sub _)
    (mobius_denom_ne_zero w1 z1)

/-- The derivative of a Möbius transform anywhere -/
public lemma deriv_mobius (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) :
    deriv (mobius w) z = (‖w‖ ^ 2 - 1) / (1 - conj w * z) ^ 2 :=
  (hasDerivAt_mobius w1 z1).deriv

-- Derivatives at `0` and `w`
public lemma deriv_mobius_zero (w1 : ‖w‖ < 1) : deriv (mobius w) 0 = ‖w‖ ^ 2 - 1 := by
  simpa using deriv_mobius w1 (z := 0) (by simp)
public lemma deriv_mobius_self (w1 : ‖w‖ < 1) : deriv (mobius w) w = (‖w‖ ^ 2 - 1: ℂ)⁻¹ := by
  have d := deriv_mobius w1 w1
  rw [Complex.conj_mul', sub_sq_comm 1] at d
  field_simp at d ⊢
  exact d
