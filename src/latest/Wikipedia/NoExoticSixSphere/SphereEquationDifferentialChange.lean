import Wikipedia.NoExoticSixSphere.SphereLevelEquations

/-!
# Actual radial sphere equations under a fixed target differential change

The chain rule computes the derivative of the original radial extension.
Adding the unchanged norm equation upgrades a target coordinate change
to a fixed equivalence of the full equation spaces. The comparison is
of the actual ambient derivatives, not an assigned normal-frame model.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereLevelEquations

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]

theorem fderiv_extend (a : UnitSphere E) (g : UnitSphere E → F) (x : UnitSphere E)
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) :
    fderiv ℝ (extend a g) x.val =
      (mfderiv (𝓡 m) 𝓘(ℝ, F) g x).comp
        (mfderiv 𝓘(ℝ, E) (𝓡 m) (SphereRadialRetraction.retract a) x.val) := by
  have hgr : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g (SphereRadialRetraction.retract a x.val) := by
    rw [SphereRadialRetraction.retract_coe]
    exact hg
  have hr := (SphereRadialRetraction.contMDiffAt_retract (n := m) a
    (ne_zero_of_mem_unit_sphere x)).mdifferentiableAt (by simp)
  have he := mfderiv_comp x.val (hgr.mdifferentiableAt (by simp)) hr
  rw [mfderiv_eq_fderiv] at he
  let D : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, E) (𝓡 m) (SphereRadialRetraction.retract a) x.val
  let dg : UnitSphere E → (EuclideanSpace ℝ (Fin m) →L[ℝ] F) :=
    fun y ↦ mfderiv (𝓡 m) 𝓘(ℝ, F) g y
  have hpoint : dg (SphereRadialRetraction.retract a x.val) = dg x :=
    congrArg dg (SphereRadialRetraction.retract_coe a x)
  exact he.trans (congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] F ↦ L.comp D) hpoint)

theorem fderiv_equations_apply (a : UnitSphere E) (g : UnitSphere E → F) (x : UnitSphere E)
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) (v : E) :
    fderiv ℝ (equations a g) x.val v = WithLp.toLp 2
      (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2 - 1) x.val v,
        mfderiv (𝓡 m) 𝓘(ℝ, F) g x
          (mfderiv 𝓘(ℝ, E) (𝓡 m) (SphereRadialRetraction.retract a) x.val v)) := by
  have hN : ContDiff ℝ ∞ (fun y : E ↦ ‖y‖ ^ 2 - 1) :=
    (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const
  have hD := (contDiffAt_extend a hg).differentiableAt (by simp)
  have hp : fderiv ℝ (rawEquations a g) x.val =
      (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2 - 1) x.val).prod (fderiv ℝ (extend a g) x.val) :=
    (((hN.differentiable (by simp) x.val).hasFDerivAt).prodMk hD.hasFDerivAt).fderiv
  rw [equations, fderiv_comp x.val
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.differentiableAt
    ((contDiffAt_rawEquations a hg).differentiableAt (by simp)),
    ContinuousLinearEquiv.fderiv, hp, fderiv_extend a g x hg]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = m + 1)] in
def equationChange (Q : F ≃L[ℝ] G) : WithLp 2 (ℝ × F) ≃L[ℝ] WithLp 2 (ℝ × G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr Q).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ G).symm)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = m + 1)] in
theorem equationChange_apply (Q : F ≃L[ℝ] G) (s : ℝ) (v : F) :
    equationChange Q (WithLp.toLp 2 (s, v)) = WithLp.toLp 2 (s, Q v) := rfl

theorem fderiv_equations_change (a : UnitSphere E)
    (g : UnitSphere E → F) (g' : UnitSphere E → G) (x : UnitSphere E)
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x)
    (hg' : ContMDiffAt (𝓡 m) 𝓘(ℝ, G) ∞ g' x) (Q : F ≃L[ℝ] G)
    (hD : mfderiv (𝓡 m) 𝓘(ℝ, G) g' x =
      Q.toContinuousLinearMap.comp (mfderiv (𝓡 m) 𝓘(ℝ, F) g x)) :
    fderiv ℝ (equations a g') x.val =
      (equationChange Q).toContinuousLinearMap.comp (fderiv ℝ (equations a g) x.val) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, fderiv_equations_apply a g' x hg' v,
    fderiv_equations_apply a g x hg v]
  let s : ℝ := fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2 - 1) x.val v
  let t : EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, E) (𝓡 m) (SphereRadialRetraction.retract a) x.val v
  let w : F := mfderiv (𝓡 m) 𝓘(ℝ, F) g x t
  let w' : G := mfderiv (𝓡 m) 𝓘(ℝ, G) g' x t
  change WithLp.toLp 2 (s, w') = equationChange Q (WithLp.toLp 2 (s, w))
  rw [equationChange_apply]
  exact congrArg (fun z : G ↦ WithLp.toLp 2 (s, z))
    (congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] G ↦ L t) hD)

end NoExoticSixSphere.SphereLevelEquations
