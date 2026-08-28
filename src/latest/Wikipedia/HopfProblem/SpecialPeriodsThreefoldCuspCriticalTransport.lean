import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry

/-!
# The actual cusp and global sphere differentials

The native cusp inclusion and the genuine sphere cusp chart are locally
biholomorphic.  Differentiating their exact projection formula therefore
relates the actual toric parameter differential to the actual global
sphere differential by two continuous linear equivalences.  Vanishing
and surjectivity are consequently equivalent, without any differential
or critical-point description being assumed.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

open ToricCharts

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] nativeChartedSpace Threefold.chartedSpace

/-- The chain rule for the exact actual cusp/sphere projection square. -/
theorem parameter_mfderiv (x : LocalSpace) :
    mfderiv I₃ 𝓘(ℂ) parameter x =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) sphereChart (Threefold.projectionSphere (inclusion x))).comp
        ((mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x)).comp
          (mfderiv I₃ IF inclusion x)) := by
  have hi : MDifferentiableAt I₃ IF inclusion x :=
    (inclusion_isLocalDiffeomorph x).mdifferentiableAt (by simp)
  have hp : MDifferentiableAt IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x) :=
    Threefold.projectionSphere_holomorphic.mdifferentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) sphereChart
      (Threefold.projectionSphere (inclusion x)) :=
    (sphereChart_isLocalDiffeomorphAt_inclusion x).mdifferentiableAt (by simp)
  have he : parameter = sphereChart ∘ (Threefold.projectionSphere ∘ inclusion) :=
    funext fun y => (sphereChart_projectionSphere_inclusion y).symm
  rw [he, mfderiv_comp x hc (hp.comp x hi), mfderiv_comp x hp hi]
  rfl

/-- Vanishing of the actual global sphere differential is equivalent
to vanishing of the original toric parameter differential. -/
theorem parameter_mfderiv_eq_zero_iff (x : LocalSpace) :
    mfderiv I₃ 𝓘(ℂ) parameter x = 0 ↔
      mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x) = 0 := by
  rw [parameter_mfderiv]
  have hB : Surjective (mfderiv I₃ IF inclusion x) :=
    ((inclusion_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)).surjective
  have hL : Injective
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) sphereChart (Threefold.projectionSphere (inclusion x))) :=
    ((sphereChart_isLocalDiffeomorphAt_inclusion x).mfderivToContinuousLinearEquiv
      (by simp)).injective
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := hB v
    apply hL
    have he := congrArg (fun L : CoordinateSpace 3 →L[ℂ] ℂ => L u) h
    change (mfderiv 𝓘(ℂ) 𝓘(ℂ) sphereChart (Threefold.projectionSphere (inclusion x)))
      ((mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x))
        ((mfderiv I₃ IF inclusion x) u)) =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) sphereChart (Threefold.projectionSphere (inclusion x))) 0
    rw [map_zero]
    exact he
  · intro h
    simp only [h, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
    rfl

/-- The same exact square preserves differential surjectivity; in
particular it compares critical points in the existing global atlas. -/
theorem parameter_mfderiv_surjective_iff (x : LocalSpace) :
    Surjective (mfderiv I₃ 𝓘(ℂ) parameter x) ↔
      Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x)) := by
  rw [parameter_mfderiv]
  have hB : Surjective (mfderiv I₃ IF inclusion x) :=
    ((inclusion_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)).surjective
  have hL : Bijective
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) sphereChart (Threefold.projectionSphere (inclusion x))) :=
    ((sphereChart_isLocalDiffeomorphAt_inclusion x).mfderivToContinuousLinearEquiv
      (by simp)).bijective
  constructor
  · intro h v
    obtain ⟨u, hu⟩ := h
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) sphereChart (Threefold.projectionSphere (inclusion x)) v)
    exact ⟨mfderiv I₃ IF inclusion x u, hL.1 hu⟩
  · intro h
    exact hL.2.comp (h.comp hB)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
