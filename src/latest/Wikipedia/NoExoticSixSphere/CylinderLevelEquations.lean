import Wikipedia.NoExoticSixSphere.SphereLevelEquations

/-!
# Ambient regular equations for a time-dependent sphere cylinder

Radial extension preserves time. Adding the spatial unit-sphere equation
gives a surjective ambient differential whenever the full cylinder map is
regular. No regularity of the individual spatial slices is assumed.
-/

open scoped Manifold ContDiff InnerProductSpace

namespace NoExoticSixSphere.CylinderLevelEquations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]

def inclusion (p : ℝ × UnitSphere E) : WithLp 2 (ℝ × E) := WithLp.toLp 2 (p.1, p.2.val)

noncomputable def retract (a : UnitSphere E) (p : WithLp 2 (ℝ × E)) : ℝ × UnitSphere E :=
  (p.fst, SphereRadialRetraction.retract a p.snd)

theorem retract_inclusion (a : UnitSphere E) (p : ℝ × UnitSphere E) :
    retract a (inclusion p) = p := by
  apply Prod.ext
  · rfl
  · exact SphereRadialRetraction.retract_coe a p.2

theorem contMDiff_inclusion :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, WithLp 2 (ℝ × E)) ∞
      (inclusion : ℝ × UnitSphere E → WithLp 2 (ℝ × E)) := by
  have hp : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × UnitSphere E ↦ (p.1, p.2.val)) :=
    contMDiff_fst.prodMk_space ((contMDiff_coe_sphere (n := m) (m := ∞)).comp contMDiff_snd)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff.contMDiff.comp hp

theorem contMDiffAt_retract (a : UnitSphere E) {p : WithLp 2 (ℝ × E)} (hp : p.snd ≠ 0) :
    ContMDiffAt 𝓘(ℝ, WithLp 2 (ℝ × E)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞ (retract a) p := by
  have ht : ContMDiffAt 𝓘(ℝ, WithLp 2 (ℝ × E)) 𝓘(ℝ, ℝ) ∞
      (fun q : WithLp 2 (ℝ × E) ↦ q.fst) p :=
    (WithLp.fstL 2 ℝ ℝ E).contDiff.contMDiff.contMDiffAt
  have hx : ContMDiffAt 𝓘(ℝ, WithLp 2 (ℝ × E)) 𝓘(ℝ, E) ∞
      (fun q : WithLp 2 (ℝ × E) ↦ q.snd) p :=
    (WithLp.sndL 2 ℝ ℝ E).contDiff.contMDiff.contMDiffAt
  exact ht.prodMk ((SphereRadialRetraction.contMDiffAt_retract (n := m) a hp).comp p hx)

noncomputable def inclusionDifferential (p : ℝ × UnitSphere E) :
    (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] WithLp 2 (ℝ × E) :=
  mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, WithLp 2 (ℝ × E)) inclusion p

theorem injective_inclusionDifferential (p : ℝ × UnitSphere E) :
    Function.Injective (inclusionDifferential (m := m) p) := by
  have heq : retract p.2 ∘ inclusion = (id : ℝ × UnitSphere E → ℝ × UnitSphere E) :=
    funext (retract_inclusion p.2)
  have hr := (contMDiffAt_retract (m := m) p.2
    (show (inclusion p).snd ≠ 0 from ne_zero_of_mem_unit_sphere p.2)).mdifferentiableAt (by simp)
  have hi := (contMDiff_inclusion (m := m)).mdifferentiable (by simp) p
  have h := mfderiv_comp p hr hi
  rw [heq, mfderiv_id] at h
  intro v w hvw
  have hv := congrArg (fun L : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin m)) ↦ L v) h
  have hw := congrArg (fun L : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin m)) ↦ L w) h
  exact hv.trans ((congrArg (mfderiv 𝓘(ℝ, WithLp 2 (ℝ × E))
    ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (retract p.2) (inclusion p)) hvw).trans hw.symm)

noncomputable def extend (a : UnitSphere E) (g : (ℝ × UnitSphere E) → F) :
    WithLp 2 (ℝ × E) → F := g ∘ retract a

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem extend_inclusion (a : UnitSphere E) (g : (ℝ × UnitSphere E) → F)
    (p : ℝ × UnitSphere E) : extend a g (inclusion p) = g p := by
  change g (retract a (inclusion p)) = g p
  rw [retract_inclusion]

theorem contDiffAt_extend (a : UnitSphere E) {g : (ℝ × UnitSphere E) → F}
    {p : ℝ × UnitSphere E} (hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g p) :
    ContDiffAt ℝ ∞ (extend a g) (inclusion p) := by
  have hg' : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g
      (retract a (inclusion p)) := by rw [retract_inclusion]; exact hg
  exact (hg'.comp (inclusion p) (contMDiffAt_retract (m := m) a
    (show (inclusion p).snd ≠ 0 from ne_zero_of_mem_unit_sphere p.2))).contDiffAt

theorem differential_extend_comp_inclusion (a : UnitSphere E) {g : (ℝ × UnitSphere E) → F}
    {p : ℝ × UnitSphere E} (hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g p) :
    (fderiv ℝ (extend a g) (inclusion p)).comp (inclusionDifferential (m := m) p) =
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) g p := by
  have heq : extend a g ∘ inclusion = g := funext (extend_inclusion a g)
  have h := mfderiv_comp p
    ((contDiffAt_extend a hg).differentiableAt (by simp)).mdifferentiableAt
    ((contMDiff_inclusion (m := m)).mdifferentiable (by simp) p)
  rw [heq, mfderiv_eq_fderiv] at h
  exact h.symm

def sphereEquation (y : WithLp 2 (ℝ × E)) : ℝ := ‖y.snd‖ ^ 2 - 1

theorem contDiff_sphereEquation : ContDiff ℝ ∞ (sphereEquation : WithLp 2 (ℝ × E) → ℝ) :=
  ((WithLp.sndL 2 ℝ ℝ E).contDiff.norm_sq (𝕜 := ℝ)).sub contDiff_const

theorem sphereEquation_comp_inclusion (p : ℝ × UnitSphere E) :
    (fderiv ℝ (sphereEquation : WithLp 2 (ℝ × E) → ℝ) (inclusion p)).comp
      (inclusionDifferential (m := m) p) = 0 := by
  have heq : (sphereEquation : WithLp 2 (ℝ × E) → ℝ) ∘ inclusion =
      fun _ : ℝ × UnitSphere E ↦ (0 : ℝ) := by
    funext q
    change ‖q.2.val‖ ^ 2 - 1 = 0
    simp only [ClosedHemisphere.unit_norm, one_pow, sub_self]
  have h := mfderiv_comp p
    (contDiff_sphereEquation.differentiable (by simp) (inclusion p)).mdifferentiableAt
    ((contMDiff_inclusion (m := m)).mdifferentiable (by simp) p)
  rw [heq, mfderiv_const, mfderiv_eq_fderiv] at h
  exact h.symm

noncomputable def rawEquations (a : UnitSphere E) (g : (ℝ × UnitSphere E) → F)
    (y : WithLp 2 (ℝ × E)) : ℝ × F := (sphereEquation y, extend a g y)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem rawEquations_inclusion (a : UnitSphere E) (g : (ℝ × UnitSphere E) → F)
    (p : ℝ × UnitSphere E) : rawEquations a g (inclusion p) = (0, g p) := by
  change (‖p.2.val‖ ^ 2 - 1, extend a g (inclusion p)) = (0, g p)
  rw [extend_inclusion, ClosedHemisphere.unit_norm, one_pow, sub_self]

theorem contDiffAt_rawEquations (a : UnitSphere E) {g : (ℝ × UnitSphere E) → F}
    {p : ℝ × UnitSphere E} (hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g p) :
    ContDiffAt ℝ ∞ (rawEquations a g) (inclusion p) :=
  contDiff_sphereEquation.contDiffAt.prodMk (contDiffAt_extend a hg)

theorem surjective_fderiv_rawEquations (a : UnitSphere E) {g : (ℝ × UnitSphere E) → F}
    {p : ℝ × UnitSphere E} (hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g p)
    (hreg : Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) g p)) :
    Function.Surjective (fderiv ℝ (rawEquations a g) (inclusion p)) := by
  let L := fderiv ℝ (sphereEquation : WithLp 2 (ℝ × E) → ℝ) (inclusion p)
  let D := fderiv ℝ (extend a g) (inclusion p)
  have hL : HasFDerivAt (sphereEquation : WithLp 2 (ℝ × E) → ℝ) L (inclusion p) :=
    (contDiff_sphereEquation.differentiable (by simp) _).hasFDerivAt
  have hD := ((contDiffAt_extend a hg).differentiableAt (by simp)).hasFDerivAt
  have hp : fderiv ℝ (rawEquations a g) (inclusion p) = L.prod D := (hL.prodMk hD).fderiv
  rw [hp]
  refine surjective_augmented_differential L D (inclusionDifferential (m := m) p) ?_ ?_
    (WithLp.toLp 2 (0, p.2.val)) ?_
  · intro v
    exact congrArg (fun T : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ ↦ T v)
      (sphereEquation_comp_inclusion (m := m) p)
  · rw [show D.comp (inclusionDifferential (m := m) p) =
        mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) g p from differential_extend_comp_inclusion a hg]
    exact hreg
  · have hnorm : L = (2 • innerSL ℝ p.2.val).comp (WithLp.sndL 2 ℝ ℝ E) :=
      hL.unique (((hasStrictFDerivAt_norm_sq p.2.val).hasFDerivAt.comp (inclusion p)
        (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt).sub_const 1)
    rw [hnorm]
    simp

noncomputable def equations (a : UnitSphere E) (g : (ℝ × UnitSphere E) → F) :
    WithLp 2 (ℝ × E) → WithLp 2 (ℝ × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm ∘ rawEquations a g

theorem equations_inclusion (a : UnitSphere E) (g : (ℝ × UnitSphere E) → F)
    (p : ℝ × UnitSphere E) : equations a g (inclusion p) = WithLp.toLp 2 (0, g p) := by
  change (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm (rawEquations a g (inclusion p)) = _
  rw [rawEquations_inclusion]
  rfl

theorem contDiffAt_equations (a : UnitSphere E) {g : (ℝ × UnitSphere E) → F}
    {p : ℝ × UnitSphere E} (hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g p) :
    ContDiffAt ℝ ∞ (equations a g) (inclusion p) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.contDiff.contDiffAt.comp (inclusion p)
    (contDiffAt_rawEquations a hg)

theorem surjective_fderiv_equations (a : UnitSphere E) {g : (ℝ × UnitSphere E) → F}
    {p : ℝ × UnitSphere E} (hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) ∞ g p)
    (hreg : Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) 𝓘(ℝ, F) g p)) :
    Function.Surjective (fderiv ℝ (equations a g) (inclusion p)) := by
  rw [equations, fderiv_comp (inclusion p)
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.differentiableAt
    ((contDiffAt_rawEquations a hg).differentiableAt (by simp)), ContinuousLinearEquiv.fderiv]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.surjective.comp
    (surjective_fderiv_rawEquations a hg hreg)

theorem equations_eq_of_timeIndependent (a : UnitSphere E)
    (g : (ℝ × UnitSphere E) → F) (g₀ : UnitSphere E → F) {U : Set ℝ}
    (hconstant : ∀ t ∈ U, ∀ x, g (t, x) = g₀ x)
    (p : WithLp 2 (ℝ × E)) (hp : p.fst ∈ U) :
    equations a g p = SphereLevelEquations.equations a g₀ p.snd := by
  change WithLp.toLp 2 (‖p.snd‖ ^ 2 - 1,
    g (p.fst, SphereRadialRetraction.retract a p.snd)) =
      WithLp.toLp 2 (‖p.snd‖ ^ 2 - 1, g₀ (SphereRadialRetraction.retract a p.snd))
  rw [hconstant p.fst hp]

end NoExoticSixSphere.CylinderLevelEquations
