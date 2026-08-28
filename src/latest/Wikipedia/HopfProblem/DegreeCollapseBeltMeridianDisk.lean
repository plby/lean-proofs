import Wikipedia.HopfProblem.DegreeCollapseBoundedRadialDisk

/-!
# A global smooth disk spanning the original belt meridian

Bounded radial coordinates keep the entire disk model inside the original
Morse chart. On the whole unit sphere they give exactly the previously
constructed meridian. The zero section is its prescribed belt point.
-/

noncomputable section

open Set Function Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open DiskShrinking

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

def nativeBeltDiskCoordinates (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ)
    (x : (S.data q).chart.NegativeCoordinates) :
    (S.data q).chart.NegativeCoordinates × (S.data q).chart.PositiveCoordinates :=
  ((S.data q).radius • boundedRadialDiskMap s x,
    ((S.data q).radius * Real.sqrt (1 + ‖boundedRadialDiskMap s x‖ ^ 2)) • v.val)

theorem nativeBeltDiskCoordinates_smooth (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) :
    ContDiff ℝ ∞ (nativeBeltDiskCoordinates S q v s) := by
  have hR := boundedRadialDiskMap_smooth (N := (S.data q).chart.NegativeCoordinates) s
  have hnorm : ContDiff ℝ ∞ (fun x : (S.data q).chart.NegativeCoordinates =>
      ‖boundedRadialDiskMap s x‖ ^ 2) := (contDiff_norm_sq ℝ).comp hR
  exact (hR.const_smul (S.data q).radius).prodMk
    ((contDiff_const.mul ((contDiff_const.add hnorm).sqrt (fun _ => by positivity))).smul
      contDiff_const)

theorem nativeBeltDiskCoordinates_mem_target (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (x : (S.data q).chart.NegativeCoordinates) :
    nativeBeltDiskCoordinates S q v s x ∈ (S.data q).chart.splitChart.target := by
  have hn := boundedRadialDiskMap_norm_le_one s.property.1 hs x
  have hr : Real.sqrt (1 + ‖boundedRadialDiskMap (s : ℝ) x‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg (boundedRadialDiskMap (s : ℝ) x)]⟩
  apply (S.data q).block
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(S.data q).radius • boundedRadialDiskMap (s : ℝ) x‖ ≤ 2 * (S.data q).radius
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (S.data q).radius_pos]
    have hh := mul_le_mul_of_nonneg_left hn (S.data q).radius_pos.le
    linarith [(S.data q).radius_pos]
  · rw [mem_closedBall_zero_iff]
    change ‖((S.data q).radius * Real.sqrt (1 + ‖boundedRadialDiskMap (s : ℝ) x‖ ^ 2)) •
      v.val‖ ≤ 2 * (S.data q).radius
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (S.data q).radius_pos.le (Real.sqrt_nonneg _)),
      mem_sphere_zero_iff_norm.mp v.property, mul_one]
    exact (mul_le_mul_of_nonneg_left hr (S.data q).radius_pos.le).trans_eq (mul_comm _ _)

theorem nativeBeltDiskCoordinates_derivative_injective (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    {s : ℝ} (hs : 0 < s) (x : (S.data q).chart.NegativeCoordinates) :
    Injective (fderiv ℝ (nativeBeltDiskCoordinates S q v s) x) := by
  let N := (S.data q).chart.NegativeCoordinates
  let P := (S.data q).chart.PositiveCoordinates
  let A : N →L[ℝ] N × P := fderiv ℝ (nativeBeltDiskCoordinates S q v s) x
  let B : N →L[ℝ] N := fderiv ℝ (boundedRadialDiskMap (N := N) s) x
  have hcoords := ((nativeBeltDiskCoordinates_smooth S q v s).differentiable (by simp) x).hasFDerivAt
  have hR := ((boundedRadialDiskMap_smooth (N := N) s).differentiable (by simp) x).hasFDerivAt
  have hproj : HasFDerivAt (fun y => (nativeBeltDiskCoordinates S q v s y).1)
      ((ContinuousLinearMap.fst ℝ N P).comp A) x :=
    (ContinuousLinearMap.fst ℝ N P).hasFDerivAt.comp x hcoords
  have hscaled : HasFDerivAt (fun y => (nativeBeltDiskCoordinates S q v s y).1)
      ((S.data q).radius • B) x := hR.const_smul (S.data q).radius
  have he := hproj.unique hscaled
  intro a b hab
  have hh : ((ContinuousLinearMap.fst ℝ N P).comp A) a =
      ((ContinuousLinearMap.fst ℝ N P).comp A) b := congrArg Prod.fst hab
  rw [he] at hh
  exact boundedRadialDiskMap_derivative_injective hs x
    (smul_right_injective N (S.data q).radius_pos.ne' hh)

theorem nativeBeltDisk_height (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (x : (S.data q).chart.NegativeCoordinates) :
    f ((S.data q).chart.splitChart.symm (nativeBeltDiskCoordinates S q v s x)) =
      S.toSurgeryWindows.upper q := by
  rw [(S.data q).chart.splitChart_inverse_equation
    (nativeBeltDiskCoordinates_mem_target S q v s hs x)]
  simp only [nativeBeltDiskCoordinates, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp v.property, mul_one, mul_pow, sq_abs,
    Real.sq_sqrt (show 0 ≤ 1 + ‖boundedRadialDiskMap (s : ℝ) x‖ ^ 2 by positivity),
    SurgeryWindows.upper]
  ring

def nativeBeltMeridianDisk (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : (s : ℝ) ≤ 1 / 2) (x : (S.data q).chart.NegativeCoordinates) : (S.data q).UpperLevel :=
  ⟨(S.data q).chart.splitChart.symm (nativeBeltDiskCoordinates S q v s x),
    nativeBeltDisk_height S q v s hs x⟩

theorem nativeBeltMeridianDisk_boundary (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    nativeBeltMeridianDisk S q v s hs u.val = nativeUpperMeridian S q v s u := by
  apply Subtype.ext
  change (S.data q).chart.splitChart.symm (nativeBeltDiskCoordinates S q v s u.val) =
    (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius s u.val v.val)
  congr 1
  simp only [nativeBeltDiskCoordinates, boundedRadialDiskMap_sphere _
    (mem_sphere_zero_iff_norm.mp u.property), norm_smul, Real.norm_eq_abs,
    abs_of_nonneg s.property.1, mem_sphere_zero_iff_norm.mp u.property, mul_one,
    smul_smul, BeltPassage.upper]

theorem nativeBeltMeridianDisk_zero (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) :
    nativeBeltMeridianDisk S q v s hs 0 = (S.data q).surgery.beltSphere v := by
  apply Subtype.ext
  change (S.data q).chart.splitChart.symm (nativeBeltDiskCoordinates S q v s 0) = _
  rw [(S.data q).belt_eq, (S.data q).chart.beltCoreMap_coe]
  simp only [nativeBeltDiskCoordinates, boundedRadialDiskMap_zero, smul_zero,
    norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one, mul_one]

theorem nativeBeltMeridianDisk_injective (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    Injective (nativeBeltMeridianDisk S q v s hs) := by
  intro x y hxy
  have hc := (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
    (nativeBeltDiskCoordinates_mem_target S q v s hs x)
    (nativeBeltDiskCoordinates_mem_target S q v s hs y) (congrArg Subtype.val hxy)
  exact boundedRadialDiskMap_injective hs0
    (smul_right_injective _ (S.data q).radius_pos.ne' (congrArg Prod.fst hc))

variable [FiniteDimensional ℝ E]

theorem nativeBeltMeridianDisk_smooth (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiff 𝓘(ℝ, (S.data q).chart.NegativeCoordinates) 𝓘(ℝ, RegularLevel.Model E) ∞
      (nativeBeltMeridianDisk S q v s hs) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  apply (RegularLevel.contMDiff_iff_inclusion hf (S.data q).upper_regular
    𝓘(ℝ, (S.data q).chart.NegativeCoordinates) (nativeBeltMeridianDisk S q v s hs)).mpr
  exact (S.data q).chart.splitChart.contMDiffOn_invFun.comp_contMDiff
    (nativeBeltDiskCoordinates_smooth S q v s).contMDiff
    (nativeBeltDiskCoordinates_mem_target S q v s hs)

theorem nativeBeltMeridianDisk_immersive (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀ x, Injective (mfderiv 𝓘(ℝ, (S.data q).chart.NegativeCoordinates)
      𝓘(ℝ, RegularLevel.Model E) (nativeBeltMeridianDisk S q v s hs) x) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  change ∀ x, Injective (mfderiv 𝓘(ℝ, (S.data q).chart.NegativeCoordinates)
    𝓘(ℝ, RegularLevel.Model E) (nativeBeltMeridianDisk S q v s hs) x)
  intro x
  have hamb : ContMDiff 𝓘(ℝ, (S.data q).chart.NegativeCoordinates) 𝓘(ℝ, E) ∞
      (Subtype.val ∘ nativeBeltMeridianDisk S q v s hs) :=
    (S.data q).chart.splitChart.contMDiffOn_invFun.comp_contMDiff
      (nativeBeltDiskCoordinates_smooth S q v s).contMDiff
      (nativeBeltDiskCoordinates_mem_target S q v s hs)
  apply RegularLevel.injective_mfderiv_of_inclusion hf (S.data q).upper_regular
    𝓘(ℝ, (S.data q).chart.NegativeCoordinates) (nativeBeltMeridianDisk S q v s hs) x (hamb x)
  change Injective (mfderiv 𝓘(ℝ, (S.data q).chart.NegativeCoordinates) 𝓘(ℝ, E)
    ((S.data q).chart.splitChart.symm ∘ nativeBeltDiskCoordinates S q v s) x)
  have ht := nativeBeltDiskCoordinates_mem_target S q v s hs x
  rw [mfderiv_comp x ((S.data q).chart.splitChart.symm.mdifferentiableAt (by simp) ht)
    ((nativeBeltDiskCoordinates_smooth S q v s).contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv]
  exact (PartialChart.bijective_mfderiv (S.data q).chart.splitChart.symm ht).injective.comp
    (nativeBeltDiskCoordinates_derivative_injective S q v hs0 x)

theorem nativeBeltMeridianDisk_isClosedEmbedding (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    Topology.IsClosedEmbedding (fun x : closedBall (0 : (S.data q).chart.NegativeCoordinates) 1 =>
      nativeBeltMeridianDisk S q v s hs x.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hcont : Continuous (fun x : closedBall (0 : (S.data q).chart.NegativeCoordinates) 1 =>
      nativeBeltMeridianDisk S q v s hs x.val) :=
    (nativeBeltMeridianDisk_smooth S hf q v s hs).continuous.comp continuous_subtype_val
  exact hcont.isClosedEmbedding
    ((nativeBeltMeridianDisk_injective S q v s hs hs0).comp Subtype.val_injective)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
