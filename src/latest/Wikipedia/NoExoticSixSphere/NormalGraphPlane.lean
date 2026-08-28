import Wikipedia.NoExoticSixSphere.SphereNormalization
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The two orthonormal columns in a normal graph plane

For a unit vector `ν` and slope `s`, normalize `(1, -s ν)` and `(s, ν)`.
These form an orthonormal pair for every real slope and reduce at slope zero
to the positive time axis followed by the original outward unit vector.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.NormalGraphPlane

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def normalRaw (ν : F) (s : ℝ) : WithLp 2 (ℝ × F) := WithLp.toLp 2 (1, -(s • ν))

def outwardRaw (ν : F) (s : ℝ) : WithLp 2 (ℝ × F) := WithLp.toLp 2 (s, ν)

theorem normalRaw_ne_zero (ν : F) (s : ℝ) : normalRaw ν s ≠ 0 := by
  intro hz
  have he := congrArg WithLp.fst hz
  exact one_ne_zero (show (1 : ℝ) = 0 from he)

omit [InnerProductSpace ℝ F] in
theorem outwardRaw_ne_zero {ν : F} (hν : ‖ν‖ = 1) (s : ℝ) : outwardRaw ν s ≠ 0 := by
  intro hz
  have he : ν = 0 := congrArg WithLp.snd hz
  rw [he, norm_zero] at hν
  exact zero_ne_one hν

def normalColumn (ν : F) (s : ℝ) : WithLp 2 (ℝ × F) :=
  NormedSpace.normalize (normalRaw ν s)

def outwardColumn (ν : F) (s : ℝ) : WithLp 2 (ℝ × F) :=
  NormedSpace.normalize (outwardRaw ν s)

theorem norm_normalColumn (ν : F) (s : ℝ) : ‖normalColumn ν s‖ = 1 :=
  NormedSpace.norm_normalize (normalRaw_ne_zero ν s)

theorem norm_outwardColumn {ν : F} (hν : ‖ν‖ = 1) (s : ℝ) : ‖outwardColumn ν s‖ = 1 :=
  NormedSpace.norm_normalize (outwardRaw_ne_zero hν s)

theorem inner_raw {ν : F} (hν : ‖ν‖ = 1) (s : ℝ) :
    inner ℝ (normalRaw ν s) (outwardRaw ν s) = 0 := by
  simp only [normalRaw, outwardRaw, WithLp.prod_inner_apply, Real.inner_apply,
    inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν,
    one_pow, mul_one, one_mul, add_neg_cancel]

theorem inner_columns {ν : F} (hν : ‖ν‖ = 1) (s : ℝ) :
    inner ℝ (normalColumn ν s) (outwardColumn ν s) = 0 := by
  simp only [normalColumn, outwardColumn, NormedSpace.normalize,
    real_inner_smul_left, real_inner_smul_right, inner_raw hν, mul_zero]

theorem time_axis_decomposition (ν : F) (s : ℝ) :
    WithLp.toLp 2 ((1 : ℝ), (0 : F)) =
      (1 / (1 + s ^ 2)) • normalRaw ν s + (s * (1 / (1 + s ^ 2))) • outwardRaw ν s := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).injective
  apply Prod.ext
  · change (1 : ℝ) = (1 / (1 + s ^ 2)) * 1 + (s * (1 / (1 + s ^ 2))) * s
    have hn : 1 + s ^ 2 ≠ 0 := by positivity
    field_simp
  · change (0 : F) = (1 / (1 + s ^ 2)) • -(s • ν) +
      (s * (1 / (1 + s ^ 2))) • ν
    rw [smul_neg, smul_smul, ← neg_smul, ← add_smul]
    rw [show -((1 / (1 + s ^ 2)) * s) + s * (1 / (1 + s ^ 2)) = 0 by ring, zero_smul]

theorem normalColumn_zero (ν : F) : normalColumn ν 0 = WithLp.toLp 2 ((1 : ℝ), (0 : F)) := by
  simp only [normalColumn, normalRaw, zero_smul, neg_zero]
  apply NormedSpace.normalize_eq_self_of_norm_eq_one
  simp only [WithLp.norm_toLp_fst, norm_one]

theorem outwardColumn_zero {ν : F} (hν : ‖ν‖ = 1) :
    outwardColumn ν 0 = WithLp.toLp 2 ((0 : ℝ), ν) := by
  apply NormedSpace.normalize_eq_self_of_norm_eq_one
  change ‖WithLp.toLp 2 ((0 : ℝ), ν)‖ = 1
  simpa only [WithLp.norm_toLp_snd] using hν

theorem normalColumn_orthogonal_lift (ν w : F) (hw : inner ℝ ν w = 0) (s : ℝ) :
    inner ℝ (normalColumn ν s) (WithLp.toLp 2 ((0 : ℝ), w)) = 0 := by
  change inner ℝ (‖normalRaw ν s‖⁻¹ • normalRaw ν s) (WithLp.toLp 2 ((0 : ℝ), w)) = 0
  rw [real_inner_smul_left]
  have he : inner ℝ (normalRaw ν s) (WithLp.toLp 2 ((0 : ℝ), w)) = 0 := by
    simp only [normalRaw, WithLp.prod_inner_apply, inner_zero_right, inner_neg_left,
      real_inner_smul_left, hw, mul_zero, neg_zero, add_zero]
  rw [he, mul_zero]

theorem outwardColumn_orthogonal_lift (ν w : F) (hw : inner ℝ ν w = 0) (s : ℝ) :
    inner ℝ (outwardColumn ν s) (WithLp.toLp 2 ((0 : ℝ), w)) = 0 := by
  change inner ℝ (‖outwardRaw ν s‖⁻¹ • outwardRaw ν s) (WithLp.toLp 2 ((0 : ℝ), w)) = 0
  rw [real_inner_smul_left]
  have he : inner ℝ (outwardRaw ν s) (WithLp.toLp 2 ((0 : ℝ), w)) = 0 := by
    simp only [outwardRaw, WithLp.prod_inner_apply, inner_zero_right, hw, add_zero]
  rw [he, mul_zero]

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem contMDiff_normalRaw {ν : X → F} {s : X → ℝ}
    (hν : ContMDiff I 𝓘(ℝ, F) ∞ ν) (hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ s) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (ℝ × F)) ∞ (fun x ↦ normalRaw (ν x) (s x)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.contDiff.contMDiff.comp
    (contMDiff_const.prodMk_space (hs.smul hν).neg)

theorem contMDiff_outwardRaw {ν : X → F} {s : X → ℝ}
    (hν : ContMDiff I 𝓘(ℝ, F) ∞ ν) (hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ s) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (ℝ × F)) ∞ (fun x ↦ outwardRaw (ν x) (s x)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.contDiff.contMDiff.comp (hs.prodMk_space hν)

theorem contMDiff_normalColumn {ν : X → F} {s : X → ℝ}
    (hν : ContMDiff I 𝓘(ℝ, F) ∞ ν) (hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ s) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (ℝ × F)) ∞ (fun x ↦ normalColumn (ν x) (s x)) :=
  contMDiff_normalize (contMDiff_normalRaw hν hs) (fun x ↦ normalRaw_ne_zero (ν x) (s x))

theorem contMDiff_outwardColumn {ν : X → F} {s : X → ℝ}
    (hν : ContMDiff I 𝓘(ℝ, F) ∞ ν) (hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ s)
    (hn : ∀ x, ‖ν x‖ = 1) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (ℝ × F)) ∞ (fun x ↦ outwardColumn (ν x) (s x)) :=
  contMDiff_normalize (contMDiff_outwardRaw hν hs) (fun x ↦ outwardRaw_ne_zero (hn x) (s x))

end NoExoticSixSphere.NormalGraphPlane
