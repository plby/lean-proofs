import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureDirections

/-!
# Actual exponential curves within the quaternionic complex-structure locus

Half-angle conjugation realizes a skew direction anticommuting with `J`.
The resulting curve has exact symplectic formula `J exp(tK)`. All points of
the curve are constructed in the original complex-structure space.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open Exponential

variable {n : ℕ}

private theorem real_smul_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ℝ) :
    c • (0 : V) = 0 := smul_zero c

private theorem real_neg_zero {V : Type*} [AddCommGroup V] : -(0 : V) = 0 := neg_zero

private theorem continuous_real_const_smul {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) :
    Continuous (fun v : V ↦ c • v) := continuous_const.smul continuous_id

private theorem continuous_neg_map {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] {f : X → V} (hf : Continuous f) :
    Continuous (fun x ↦ -(f x)) := hf.neg

def exponentialStep (J : Space n) (K : AntiSkewSpace J) : Space n :=
  conjugate (exp (-(antiSkewToSkew J ((1 / 2 : ℝ) • K)))) J

theorem exponentialStep_zero (J : Space n) : exponentialStep J 0 = J := by
  unfold exponentialStep
  rw [real_smul_zero (V := AntiSkewSpace J), map_zero,
    real_neg_zero (V := SkewSpace n), exp_zero, conjugate_one]

theorem exponentialStep_toSymplectic (J : Space n) (K : AntiSkewSpace J) :
    toSymplectic (exponentialStep J K) = toSymplectic J * exp (antiSkewToSkew J K) := by
  let H := antiSkewToSkew J ((1 / 2 : ℝ) • K)
  have hc : toSymplectic J * exp H = (exp H)⁻¹ * toSymplectic J := by
    rw [← exp_neg]
    exact anticommute_exp J H ((1 / 2 : ℝ) • K).property.2
  have hH : H = (1 / 2 : ℝ) • antiSkewToSkew J K :=
    (antiSkewToSkew J).map_smul _ _
  have hprod : exp H * exp H = exp (antiSkewToSkew J K) := by
    rw [hH, ← exp_add_smul]
    norm_num
  change toSymplectic (conjugate (exp (-H)) J) = _
  rw [toSymplectic_conjugate, exp_neg, inv_inv, ← hc, mul_assoc, hprod]

theorem continuous_exponentialStep (J : Space n) : Continuous (exponentialStep J) := by
  have hhalf : Continuous (fun K : AntiSkewSpace J ↦ (1 / 2 : ℝ) • K) :=
    continuous_real_const_smul (V := AntiSkewSpace J) _
  have hH : Continuous (fun K : AntiSkewSpace J ↦ antiSkewToSkew J ((1 / 2 : ℝ) • K)) :=
    (continuous_antiSkewToSkew J).comp hhalf
  have hn := continuous_neg_map (V := SkewSpace n) hH
  exact continuous_conjugate _ _ (contMDiff_exp.continuous.comp hn) continuous_const

def exponentialCurve (J : Space n) (K : AntiSkewSpace J) (t : ℝ) : Space n :=
  exponentialStep J (t • K)

theorem exponentialCurve_zero (J : Space n) (K : AntiSkewSpace J) :
    exponentialCurve J K 0 = J := by
  unfold exponentialCurve
  rw [zero_smul, exponentialStep_zero]

theorem exponentialCurve_toSymplectic (J : Space n) (K : AntiSkewSpace J) (t : ℝ) :
    toSymplectic (exponentialCurve J K t) = toSymplectic J * exp (t • antiSkewToSkew J K) := by
  rw [exponentialCurve, exponentialStep_toSymplectic, map_smul]

theorem continuous_exponentialCurve (J : Space n) (K : AntiSkewSpace J) :
    Continuous (exponentialCurve J K) := by
  have hK : Continuous (fun t : ℝ ↦ t • K) := continuous_id.smul continuous_const
  exact (continuous_exponentialStep J).comp hK

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
