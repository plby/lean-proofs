import Wikipedia.NoExoticSixSphere.ProductSphereAmbient

/-!
# The two actual sphere equations have independent transverse differentials

The norm equations vanish on the genuine product inclusion and their
differentials kill its tangent image. Their paired ambient differential
is surjective, witnessed by the two independent radial directions.
-/

noncomputable section

open Function
open scoped Manifold ContDiff InnerProductSpace

namespace NoExoticSixSphere.ProductSphereLevelEquations

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def normEquations (v : Ambient E G) : ℝ × ℝ := (‖v.fst‖ ^ 2 - 1, ‖v.snd‖ ^ 2 - 1)

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ G] in
theorem normEquations_inclusion (x : UnitSphere E × UnitSphere G) :
    normEquations (inclusion x) = 0 := by
  change (‖x.1.val‖ ^ 2 - 1, ‖x.2.val‖ ^ 2 - 1) = (0, 0)
  simp only [ClosedHemisphere.unit_norm, one_pow, sub_self]

theorem contDiff_normEquations : ContDiff ℝ ∞ (normEquations (E := E) (G := G)) :=
  (((WithLp.prodContinuousLinearEquiv 2 ℝ E G).contDiff.fst.norm_sq (𝕜 := ℝ)).sub
    contDiff_const).prodMk
      (((WithLp.prodContinuousLinearEquiv 2 ℝ E G).contDiff.snd.norm_sq (𝕜 := ℝ)).sub
        contDiff_const)

def normDifferential (x : UnitSphere E × UnitSphere G) : Ambient E G →L[ℝ] ℝ × ℝ :=
  ((2 • innerSL ℝ x.1.val).prodMap (2 • innerSL ℝ x.2.val)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E G).toContinuousLinearMap

theorem fderiv_normEquations (x : UnitSphere E × UnitSphere G) :
    fderiv ℝ normEquations (inclusion x) = normDifferential x := by
  have hE := (hasStrictFDerivAt_norm_sq x.1.val).hasFDerivAt.sub_const 1
  have hG := (hasStrictFDerivAt_norm_sq x.2.val).hasFDerivAt.sub_const 1
  exact ((hE.prodMap (x.1.val, x.2.val) hG).comp (inclusion x)
    (WithLp.prodContinuousLinearEquiv 2 ℝ E G).hasFDerivAt).fderiv

theorem normDifferential_apply (x : UnitSphere E × UnitSphere G) (v : Ambient E G) :
    normDifferential x v = (2 * inner ℝ x.1.val v.fst, 2 * inner ℝ x.2.val v.snd) := by
  simp [normDifferential, two_smul, two_mul]
  rfl

theorem surjective_fderiv_normEquations (x : UnitSphere E × UnitSphere G) :
    Surjective (fderiv ℝ normEquations (inclusion x)) := by
  rw [fderiv_normEquations]
  rintro ⟨r, s⟩
  refine ⟨WithLp.toLp 2 ((r / 2) • x.1.val, (s / 2) • x.2.val), ?_⟩
  rw [normDifferential_apply]
  change (2 * inner ℝ x.1.val ((r / 2) • x.1.val),
    2 * inner ℝ x.2.val ((s / 2) • x.2.val)) = (r, s)
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq,
    ClosedHemisphere.unit_norm, one_pow, mul_one]
  congr 1 <;> ring

variable {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  [Fact (Module.finrank ℝ G = n + 1)]

theorem norm_equations_comp_inclusion (x : UnitSphere E × UnitSphere G) :
    (fderiv ℝ normEquations (inclusion x)).comp
      (inclusionDifferential (m := m) (n := n) x) = 0 := by
  have he : normEquations ∘ inclusion = fun _ : UnitSphere E × UnitSphere G ↦ (0 : ℝ × ℝ) :=
    funext normEquations_inclusion
  have h := mfderiv_comp x
    (contDiff_normEquations.differentiable (by simp) (inclusion x)).mdifferentiableAt
    ((contMDiff_inclusion (m := m) (n := n)).mdifferentiableAt (by simp))
  rw [he, mfderiv_const, mfderiv_eq_fderiv] at h
  exact h.symm

end NoExoticSixSphere.ProductSphereLevelEquations
