import Wikipedia.NoExoticSixSphere.SphereFrameGerms
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates

/-!
# The actual quaternionic frame Jacobian of a local sphere reparametrization

The native derivative and the radial extension give the same derivative in
the quaternionic tangent frame. The chain rule retains the source Jacobian;
that Jacobian is invertible for an actual local sphere diffeomorphism.
Only differentiability at the points under consideration is needed.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization

def radialDerivative (x : Sphere 3) : Vector 4 →L[ℝ] Vector 3 :=
  mfderiv (𝓡 4) (𝓡 3) (SphereRadialRetraction.retract (Stiefel.pole 3)) x.val

def nativeFrame (x : Sphere 3) : Vector 3 →L[ℝ] Vector 3 :=
  (radialDerivative x).comp (operator x.val)

theorem radialDerivative_comp_inclusion (x : Sphere 3) :
    (radialDerivative x).comp (inclusionDerivative x) = ContinuousLinearMap.id ℝ _ := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have hr := SphereRadialRetraction.contMDiffAt_retract (n := 3) (Stiefel.pole 3)
    (ne_zero_of_mem_unit_sphere x)
  have he : SphereRadialRetraction.retract (Stiefel.pole 3) ∘
      (fun s : Sphere 3 ↦ s.val) = id :=
    funext (SphereRadialRetraction.retract_coe (Stiefel.pole 3))
  have hd := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  rw [he, mfderiv_id] at hd
  exact hd.symm

theorem inclusion_comp_nativeFrame (x : Sphere 3) :
    (inclusionDerivative x).comp (nativeFrame x) = operator x.val := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : operator x.val v ∈ (inclusionDerivative x).range := by
    rw [range_inclusionDerivative, ← range_operator]
    exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := hv
  change inclusionDerivative x (radialDerivative x (operator x.val v)) = operator x.val v
  rw [← hw]
  have hd := congrArg (fun A : Vector 3 →L[ℝ] Vector 3 ↦ A w)
    (radialDerivative_comp_inclusion x)
  change radialDerivative x (inclusionDerivative x w) = w at hd
  exact congrArg (inclusionDerivative x) hd

theorem nativeFrame_injective (x : Sphere 3) : Injective (nativeFrame x) := by
  intro v w h
  apply Stiefel.injective (frame x)
  have he := congrArg (inclusionDerivative x) h
  change ((inclusionDerivative x).comp (nativeFrame x)) v =
    ((inclusionDerivative x).comp (nativeFrame x)) w at he
  rwa [inclusion_comp_nativeFrame] at he

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_extension_at (f : Sphere 3 → F) (x : Sphere 3)
    (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, F) f x) :
    fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) f) x.val =
      (mfderiv (𝓡 3) 𝓘(ℝ, F) f x).comp (radialDerivative x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hr := SphereRadialRetraction.contMDiffAt_retract (n := 3) (Stiefel.pole 3)
    (ne_zero_of_mem_unit_sphere x)
  have hfr : MDifferentiableAt (𝓡 3) 𝓘(ℝ, F) f
      (SphereRadialRetraction.retract (Stiefel.pole 3) x.val) := by
    rwa [SphereRadialRetraction.retract_coe]
  have hd := mfderiv_comp x.val hfr (hr.mdifferentiableAt (by simp))
  rw [SphereRadialRetraction.retract_coe, mfderiv_eq_fderiv] at hd
  rw [(SmoothSphereAmbient.extension_eventuallyEq_radial (Stiefel.pole 3) f x).fderiv_eq]
  exact hd

theorem framedDerivative_eq_native (f : Sphere 3 → F) (x : Sphere 3)
    (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, F) f x) :
    framedDerivative f x = (mfderiv (𝓡 3) 𝓘(ℝ, F) f x).comp (nativeFrame x) := by
  unfold framedDerivative nativeFrame
  rw [fderiv_extension_at f x hf]
  rfl

def sourceJacobian (u : Sphere 3 → Sphere 3) (x : Sphere 3) : Vector 3 →L[ℝ] Vector 3 :=
  (operator (u x).val).adjoint.comp (framedDerivative (fun s ↦ (u s).val) x)

theorem framedDerivative_coe_comp (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : MDifferentiableAt (𝓡 3) (𝓡 3) u x) :
    framedDerivative (fun s ↦ (u s).val) x = (inclusionDerivative (u x)).comp
      ((mfderiv (𝓡 3) (𝓡 3) u x).comp (nativeFrame x)) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have hf := framedDerivative_eq_native ((fun s : Sphere 3 ↦ s.val) ∘ u) x
    ((hi.mdifferentiableAt (by simp)).comp x hu)
  have hd := mfderiv_comp (f := u) (g := fun s : Sphere 3 ↦ s.val) x
    (hi.mdifferentiableAt (by simp)) hu
  exact hf.trans (congrArg (fun A : Vector 3 →L[ℝ] Vector 4 ↦ A.comp (nativeFrame x)) hd)

theorem operator_comp_sourceJacobian (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : MDifferentiableAt (𝓡 3) (𝓡 3) u x) :
    (operator (u x).val).comp (sourceJacobian u x) =
      framedDerivative (fun s ↦ (u s).val) x := by
  apply ContinuousLinearMap.ext
  intro v
  apply Stiefel.RangeCoordinates.self_adjoint (frame (u x))
  rw [framedDerivative_coe_comp u x hu]
  change inclusionDerivative (u x) _ ∈ (operator (u x).val).range
  rw [range_operator, ← range_inclusionDerivative]
  exact ⟨_, rfl⟩

theorem nativeFrame_comp_sourceJacobian (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : MDifferentiableAt (𝓡 3) (𝓡 3) u x) :
    (nativeFrame (u x)).comp (sourceJacobian u x) =
      (mfderiv (𝓡 3) (𝓡 3) u x).comp (nativeFrame x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative (u x)) := by
    convert! injective_mvfderiv_subtypeVal_sphere (u x)
  apply ContinuousLinearMap.ext
  intro v
  apply hi
  have he := operator_comp_sourceJacobian u x hu
  rw [← inclusion_comp_nativeFrame (u x), framedDerivative_coe_comp u x hu] at he
  exact congrArg (fun A : Vector 3 →L[ℝ] Vector 4 ↦ A v) he

theorem framedDerivative_comp_at (f : Sphere 3 → F) (u : Sphere 3 → Sphere 3)
    (x : Sphere 3) (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, F) f (u x))
    (hu : MDifferentiableAt (𝓡 3) (𝓡 3) u x) :
    framedDerivative (f ∘ u) x = (framedDerivative f (u x)).comp (sourceJacobian u x) := by
  rw [framedDerivative_eq_native _ x (hf.comp x hu),
    framedDerivative_eq_native f (u x) hf, mfderiv_comp x hf hu]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (mfderiv (𝓡 3) 𝓘(ℝ, F) f (u x))
    (congrArg (fun A : Vector 3 →L[ℝ] Vector 3 ↦ A v)
      (nativeFrame_comp_sourceJacobian u x hu)).symm

theorem sourceJacobian_injective (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) : Injective (sourceJacobian u x) := by
  have hd := nativeFrame_comp_sourceJacobian u x (hu.mdifferentiableAt (by simp))
  intro v w h
  apply nativeFrame_injective x
  apply (hu.mfderivToContinuousLinearEquiv (by simp)).injective
  have he := congrArg (nativeFrame (u x)) h
  change ((nativeFrame (u x)).comp (sourceJacobian u x)) v =
    ((nativeFrame (u x)).comp (sourceJacobian u x)) w at he
  rwa [hd] at he

def sourceJacobianEquiv (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) : Vector 3 ≃L[ℝ] Vector 3 :=
  (LinearEquiv.ofBijective (sourceJacobian u x).toLinearMap
    ⟨sourceJacobian_injective u x hu,
      LinearMap.surjective_of_injective (sourceJacobian_injective u x hu)⟩).toContinuousLinearEquiv

theorem sourceJacobianEquiv_toContinuousLinearMap (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) :
    (sourceJacobianEquiv u x hu).toContinuousLinearMap = sourceJacobian u x := rfl

theorem contMDiffAt_framedDerivative (f : Sphere 3 → F) (x : Sphere 3)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ f x) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] F) ∞ (framedDerivative f) x := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have hr := SphereRadialRetraction.contMDiffAt_retract (n := 3) (Stiefel.pole 3)
    (ne_zero_of_mem_unit_sphere x)
  have hfr : ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ f
      (SphereRadialRetraction.retract (Stiefel.pole 3) x.val) := by
    rwa [SphereRadialRetraction.retract_coe]
  have he : ContDiffAt ℝ ∞ (SmoothSphereAmbient.extension (Stiefel.pole 3) f) x.val :=
    (hfr.comp x.val hr).contDiffAt.congr_of_eventuallyEq
      (SmoothSphereAmbient.extension_eventuallyEq_radial (Stiefel.pole 3) f x)
  exact (((he.fderiv_right (m := ∞) (by simp)).contMDiffAt.comp x hi.contMDiffAt).clm_comp
    contMDiff_frame.contMDiffAt)

theorem continuousAt_sourceJacobian (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : ContMDiffAt (𝓡 3) (𝓡 3) ∞ u x) : ContinuousAt (sourceJacobian u) x := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have hd := (contMDiffAt_framedDerivative (fun s ↦ (u s).val) x
    (hi.contMDiffAt.comp x hu)).continuousAt
  have ht := contDiff_operator.continuous.continuousAt.comp
    (hi.continuous.continuousAt.comp hu.continuousAt)
  exact (ContinuousLinearMap.adjoint.continuous.continuousAt.comp ht).clm_comp hd

theorem continuous_sourceJacobianEquiv (u : Sphere 3 → Sphere 3) (U : Set (Sphere 3))
    (hu : ∀ x : U, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x.val) :
    Continuous (fun x : U ↦ (sourceJacobianEquiv u x.val (hu x)).toContinuousLinearMap) := by
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt (fun y : U ↦ sourceJacobian u y.val) x
  exact (continuousAt_sourceJacobian u x.val (hu x).contMDiffAt).comp
    continuous_subtype_val.continuousAt

theorem continuous_inverse_sourceJacobianEquiv (u : Sphere 3 → Sphere 3) (U : Set (Sphere 3))
    (hu : ∀ x : U, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x.val) :
    Continuous (fun x : U ↦
      (sourceJacobianEquiv u x.val (hu x)).symm.toContinuousLinearMap) := by
  have he (x : U) : (sourceJacobianEquiv u x.val (hu x)).symm.toContinuousLinearMap =
      (sourceJacobian u x.val).inverse :=
    (ContinuousLinearMap.inverse_equiv (sourceJacobianEquiv u x.val (hu x))).symm
  simp_rw [he]
  rw [continuous_iff_continuousAt]
  intro x
  have hi : (sourceJacobian u x.val).IsInvertible := ⟨sourceJacobianEquiv u x.val (hu x), rfl⟩
  have hc : ContinuousAt (fun y : U ↦ sourceJacobian u y.val) x :=
    (continuous_sourceJacobianEquiv u U hu).continuousAt
  exact (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp
    (f := fun y : U ↦ sourceJacobian u y.val) hc

end NoExoticSixSphere.SphereThreeTangentFrame
