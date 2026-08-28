import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseCoordinates

/-!
# The phase family has invertible coordinate derivatives

The source-curve kernel and target-chart reconstruction apply for every real
phase, not only at cube roots. The two fixed coordinate spaces both have
dimension seven, so the derivatives are continuous linear equivalences.
-/

noncomputable section

open scoped ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

local notation "ℍ" => Quaternion ℝ

theorem phaseProjection_fderiv_kernel (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) (v : ParameterSpace z) (hv : fderiv ℝ (phaseProjection z a) 0 v = 0) :
    v = 0 := by
  have hf := (contDiff_phaseProjection z a (n := 1)).differentiable (by decide)
  have hfd : HasFDerivAt (phaseProjection z a) (fderiv ℝ (phaseProjection z a) 0)
      ((0 : ℝ) • v) := by
    simpa only [zero_smul] using (hf 0).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ phaseProjection z a (t • v))
      (0 : Fin 2 → ℍ) 0 := by
    have he := hfd.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
    convert he using 1 <;> try rfl
    simpa only [one_smul] using hv.symm
  have hs : HasDerivAt (fun t : ℝ ↦ Real.pi / 2 + (t • v).1) v.1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add (Real.pi / 2) using 1 <;>
      try rfl
    simp
  have ht : HasDerivAt (fun t : ℝ ↦ Real.pi / 2 + (t • v).2.1) v.2.1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const v.2.1).const_add (Real.pi / 2) using 1 <;>
      try rfl
    simp
  obtain ⟨h1, h2, h3⟩ := scaled_firstColumn_curve_kernel_midpoint (Circle.exp a)
    (fun t : ℝ ↦ Real.pi / 2 + (t • v).1)
    (fun t : ℝ ↦ Real.pi / 2 + (t • v).2.1)
    (fun t : ℝ ↦ localSphere z (t • v)) v.1 v.2.1 0 v.2.2.val hs ht
    (hasDerivAt_localSphere_line_entry z v) (by simp) (by simp)
    (by simpa using hz) (hasDerivAt_pi.mp hline)
  apply Prod.ext h1
  apply Prod.ext h2
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2) h3

theorem phaseCoordinates_reconstruction (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) :
    (fun p ↦ SphereCenteredCoordinates.inverse (localColumn z 0) (phaseCoordinates z a p))
      =ᶠ[𝓝 0] phaseColumn z a := by
  have hmem : ∀ᶠ p in 𝓝 (0 : ParameterSpace z),
      phaseColumn z a p ∈ (SphereCenteredCoordinates.chart (localColumn z 0)).source :=
    (continuous_phaseColumn z a).continuousAt.eventually
      ((SphereCenteredCoordinates.chart (localColumn z 0)).open_source.mem_nhds (by
        rw [phaseColumn_zero z hz]
        exact SphereCenteredCoordinates.self_mem_chart_source (localColumn z 0)))
  filter_upwards [hmem] with p hp
  exact (SphereCenteredCoordinates.chart (localColumn z 0)).left_inv hp

theorem phaseCoordinates_fderiv_kernel (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) (v : ParameterSpace z) (hv : fderiv ℝ (phaseCoordinates z a) 0 v = 0) :
    v = 0 := by
  have hf := (contDiffAt_phaseCoordinates z hz a (n := 1)).differentiableAt (by decide)
  have hi : HasFDerivAt
      (fun q : TargetSpace z ↦ (SphereCenteredCoordinates.inverse (localColumn z 0) q).val)
      (TargetSpace z).subtypeL (phaseCoordinates z a 0) := by
    simpa only [phaseCoordinates_zero z hz] using
      SphereCenteredCoordinates.hasFDerivAt_inverse_val (localColumn z 0)
  have hcomp := hi.comp 0 hf.hasFDerivAt
  have heq : (fun p ↦ (phaseColumn z a p).val) =ᶠ[𝓝 0]
      (fun p ↦ (SphereCenteredCoordinates.inverse (localColumn z 0)
        (phaseCoordinates z a p)).val) := by
    filter_upwards [phaseCoordinates_reconstruction z hz a] with p hp
    exact congrArg Subtype.val hp.symm
  have hd := hcomp.congr_of_eventuallyEq heq
  have hzero : fderiv ℝ (fun p ↦ (phaseColumn z a p).val) 0 v = 0 := by
    rw [hd.fderiv]
    change (TargetSpace z).subtypeL (fderiv ℝ (phaseCoordinates z a) 0 v) = 0
    rw [hv, map_zero]
  have ho := PiLp.contDiff_ofLp (𝕜 := ℝ) (n := 1)
    (p := 2) (E := fun _ : Fin 2 ↦ ℍ)
  have hp : ContDiff ℝ 1 (fun p : ParameterSpace z ↦ (a, p)) :=
    contDiff_const.prodMk contDiff_id
  have hcf := (contDiff_uncurry_phaseColumn_val z (n := 1)).comp hp
  have hchain := ((ho.differentiable (by decide)) ((phaseColumn z a 0).val)).hasFDerivAt.comp 0
    ((hcf.differentiable (by decide)) 0).hasFDerivAt
  change HasFDerivAt (phaseProjection z a) _ 0 at hchain
  apply phaseProjection_fderiv_kernel z hz a v
  rw [hchain.fderiv]
  change fderiv ℝ WithLp.ofLp (phaseColumn z a 0).val
    (fderiv ℝ (fun p ↦ (phaseColumn z a p).val) 0 v) = 0
  rw [hzero, map_zero]

theorem phaseCoordinates_fderiv_injective (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : Function.Injective (fderiv ℝ (phaseCoordinates z a) 0) := by
  intro v w h
  have he : fderiv ℝ (phaseCoordinates z a) 0 (v - w) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (phaseCoordinates_fderiv_kernel z hz a (v - w) he)

def phaseDerivativeEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : ParameterSpace z ≃L[ℝ] TargetSpace z :=
  ((fderiv ℝ (phaseCoordinates z a) 0).toLinearMap.linearEquivOfInjective
    (phaseCoordinates_fderiv_injective z hz a)
    (by rw [parameterSpace_finrank, targetSpace_finrank])).toContinuousLinearEquiv

theorem phaseDerivativeEquiv_apply (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) (v : ParameterSpace z) :
    phaseDerivativeEquiv z hz a v = fderiv ℝ (phaseCoordinates z a) 0 v := rfl

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
