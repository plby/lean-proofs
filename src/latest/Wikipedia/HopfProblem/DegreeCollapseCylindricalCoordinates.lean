import Wikipedia.HopfProblem.DegreeCollapseQuadraticCompressionSum
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Actual Euclidean normal coordinates for a cylindrical tube

The normal product has its genuine sum-of-squares norm. A specified
homeomorphism rescales only the new real coordinate. The two degenerate
quadratic forms add to the original squared Euclidean norm.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CylindricalTube

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

abbrev Normal (K : Type*) := WithLp 2 (ℝ × K)

def split : Normal K ≃L[ℝ] ℝ × K := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ K

def denominator (v : K) : ℝ := Real.sqrt (1 + ‖v‖ ^ 2)

theorem denominator_pos (v : K) : 0 < denominator v :=
  Real.sqrt_pos.mpr (by positivity)

theorem continuous_denominator : Continuous (denominator (K := K)) :=
  (continuous_const.add (continuous_norm.pow 2)).sqrt

def scaleCoordinates (r : ℝ) (hr : 0 < r) : ℝ × K ≃ₜ ℝ × K where
  toFun p := (r * (denominator p.2)⁻¹ * p.1, p.2)
  invFun p := ((denominator p.2) * r⁻¹ * p.1, p.2)
  left_inv p := by
    refine Prod.ext ?_ rfl
    change denominator p.2 * r⁻¹ * (r * (denominator p.2)⁻¹ * p.1) = p.1
    field_simp [hr.ne', (denominator_pos p.2).ne']
  right_inv p := by
    refine Prod.ext ?_ rfl
    change r * (denominator p.2)⁻¹ * (denominator p.2 * r⁻¹ * p.1) = p.1
    field_simp [hr.ne', (denominator_pos p.2).ne']
  continuous_toFun :=
    ((continuous_const.mul ((continuous_denominator.comp continuous_snd).inv₀
      (fun p ↦ (denominator_pos p.2).ne'))).mul continuous_fst).prodMk continuous_snd
  continuous_invFun :=
    (((continuous_denominator.comp continuous_snd).mul continuous_const).mul
      continuous_fst).prodMk continuous_snd

def fiberCoordinates (r : ℝ) (hr : 0 < r) : Normal K ≃ₜ ℝ × K :=
  (split (K := K)).toHomeomorph.trans (scaleCoordinates r hr)

theorem fiberCoordinates_apply (r : ℝ) (hr : 0 < r) (w : Normal K) :
    fiberCoordinates r hr w = (r * (denominator w.snd)⁻¹ * w.fst, w.snd) := rfl

variable {M : Type*}

def transverseForm (p : M × Normal K) : ℝ := ‖p.2.snd‖ ^ 2

def longitudinalForm (p : M × Normal K) : ℝ := ‖p.2.fst‖ ^ 2

theorem transverseForm_nonneg (p : M × Normal K) : 0 ≤ transverseForm p := sq_nonneg _

theorem longitudinalForm_nonneg (p : M × Normal K) : 0 ≤ longitudinalForm p := sq_nonneg _

theorem transverseForm_smul (m : M) (c : ℝ) (v : Normal K) :
    transverseForm (m, c • v) = c ^ 2 * transverseForm (m, v) := by
  change ‖c • v.snd‖ ^ 2 = c ^ 2 * ‖v.snd‖ ^ 2
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem longitudinalForm_smul (m : M) (c : ℝ) (v : Normal K) :
    longitudinalForm (m, c • v) = c ^ 2 * longitudinalForm (m, v) := by
  change ‖c • v.fst‖ ^ 2 = c ^ 2 * ‖v.fst‖ ^ 2
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem forms_sum (p : M × Normal K) :
    transverseForm p + longitudinalForm p = ‖p.2‖ ^ 2 := by
  change ‖p.2.snd‖ ^ 2 + ‖p.2.fst‖ ^ 2 = ‖p.2‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  ring

theorem compress_forms (p : M × Normal K) :
    NoExoticSixSphere.QuadraticRadialCompression.compress transverseForm
      (NoExoticSixSphere.QuadraticRadialCompression.compress longitudinalForm p) =
        NoExoticSixSphere.QuadraticRadialCompression.compress
          (fun z : M × Normal K ↦ ‖z.2‖ ^ 2) p := by
  have h := QuadraticCompression.compress_compress
    (transverseForm (M := M) (K := K)) (longitudinalForm (M := M) (K := K))
    (transverseForm_smul (M := M) (K := K))
    (transverseForm_nonneg (M := M) (K := K))
    (longitudinalForm_nonneg (M := M) (K := K)) p
  have he : (fun z : M × Normal K ↦ transverseForm z + longitudinalForm z) =
      (fun z ↦ ‖z.2‖ ^ 2) := funext forms_sum
  rw [he] at h
  exact h

variable [TopologicalSpace M]

theorem continuous_transverseForm : Continuous (transverseForm (M := M) (K := K)) :=
  (((split (K := K)).continuous.comp continuous_snd).snd.norm).pow 2

theorem continuous_longitudinalForm : Continuous (longitudinalForm (M := M) (K := K)) :=
  (((split (K := K)).continuous.comp continuous_snd).fst.norm).pow 2

end Wikipedia.HopfProblem.DegreeCollapse.CylindricalTube
