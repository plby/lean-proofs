import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticOrders
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The actual global differential on the two elliptic fibres

The genuine global elliptic projection charts have the equation
`u.1 ^ j.order`. At every central fibre point their first coordinate is
zero, so this coordinate expression has zero differential. The chain
rule and the invertible differential of the actual sphere chart then
give vanishing of the global sphere projection's manifold derivative.
-/

noncomputable section

open Function Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

open EllipticGeometry Triangle

local notation "FM" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FM

attribute [local instance] Threefold.chartedSpace

private theorem power_fst_hasFDerivAt_zero (j : Elliptic.Kind) (u : FM)
    (hu : u.1 = 0) :
    HasFDerivAt (fun v : FM => v.1 ^ j.order) (0 : FM →L[ℂ] ℂ) u := by
  have hd := (hasFDerivAt_fst (𝕜 := ℂ) (p := u)).pow j.order
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  cases j <;> simp [Elliptic.Kind.order, hu]

/-- Every point of either literal central elliptic sphere fibre has
zero differential for the actual global sphere projection. -/
theorem elliptic_mfderiv_eq_zero (j : Elliptic.Kind) (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = sphereValue j) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0 := by
  have hyproj : Threefold.projection y = puncturePoint (some j) :=
    triangleSphereUniformization.injective hy
  have hym : y ∈ range (EllipticGeometry.inclusion j) := by
    rw [EllipticGeometry.inclusion_range]
    change Threefold.projection y ∈ specialBaseCover.fillingPatch (some j)
    rw [hyproj]
    exact specialBaseCover.point_mem_fillingPatch (some j)
  obtain ⟨x, rfl⟩ := hym
  have hxpatch : EllipticGeometry.inclusion j x ∈
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) :=
    (nativePatchBiholomorph j x).property
  have hzero : sphereChart j
      (Threefold.projectionSphere (EllipticGeometry.inclusion j x)) = 0 := by
    rw [hy, sphereChart_value]
  obtain ⟨e, hex, hezero, _, hequation⟩ :=
    exists_central_projectionChart j (EllipticGeometry.inclusion j x) hxpatch hzero
  have heq : (sphereChart j ∘ Threefold.projectionSphere)
      =ᶠ[𝓝 (EllipticGeometry.inclusion j x)]
        (fun u : FM => u.1 ^ j.order) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hex] with w hw
    have hwleft : e.symm (e w) = w := e.left_inv' hw
    simpa only [hwleft, Function.comp_apply] using
      hequation (e w) (e.map_source' hw)
  have hde : MDifferentiableAt IF IF e (EllipticGeometry.inclusion j x) :=
    (e.isLocalDiffeomorphAt _ _ _ hex).mdifferentiableAt (by simp)
  have hpow := power_fst_hasFDerivAt_zero j (e (EllipticGeometry.inclusion j x)) hezero
  have hd0 := heq.mfderiv_eq (I := IF) (I' := 𝓘(ℂ))
  rw [mfderiv_comp _ hpow.differentiableAt.mdifferentiableAt hde] at hd0
  have hd : mfderiv IF 𝓘(ℂ) (sphereChart j ∘ Threefold.projectionSphere)
        (EllipticGeometry.inclusion j x) =
      (fderiv ℂ (fun u : FM => u.1 ^ j.order) (e (EllipticGeometry.inclusion j x))).comp
        (mfderiv IF IF e (EllipticGeometry.inclusion j x)) := by
    simpa only [mfderiv_eq_fderiv] using! hd0
  rw [hpow.fderiv] at hd
  have hdz : mfderiv IF 𝓘(ℂ) (sphereChart j ∘ Threefold.projectionSphere)
      (EllipticGeometry.inclusion j x) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : FM →L[ℂ] ℂ => L v) hd
  have hp : MDifferentiableAt IF 𝓘(ℂ) Threefold.projectionSphere
      (EllipticGeometry.inclusion j x) :=
    Threefold.projectionSphere_holomorphic.mdifferentiableAt (by simp)
  have hc := sphereChart_isLocalDiffeomorphAt_inclusion j x
  rw [mfderiv_comp _ (hc.mdifferentiableAt (by simp)) hp] at hdz
  have hL : Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) (sphereChart j)
      (Threefold.projectionSphere (EllipticGeometry.inclusion j x))) :=
    (hc.mfderivToContinuousLinearEquiv (by simp)).injective
  apply ContinuousLinearMap.ext
  intro v
  apply hL
  have hv := congrArg (fun L : FM →L[ℂ] ℂ => L v) hdz
  change (mfderiv 𝓘(ℂ) 𝓘(ℂ) (sphereChart j)
      (Threefold.projectionSphere (EllipticGeometry.inclusion j x)))
        ((mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (EllipticGeometry.inclusion j x)) v) =
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (sphereChart j)
      (Threefold.projectionSphere (EllipticGeometry.inclusion j x))) 0
  rw [map_zero]
  exact hv

theorem zero_mfderiv_eq_zero (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = ((0 : ℂ) : RiemannSphere)) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0 :=
  elliptic_mfderiv_eq_zero .three y (by simpa only [sphereValue_three] using hy)

theorem one_mfderiv_eq_zero (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere)) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0 :=
  elliptic_mfderiv_eq_zero .four y (by simpa only [sphereValue_four] using hy)

/-- The actual global differential is not surjective at any point of
either central elliptic fibre. -/
theorem elliptic_mfderiv_not_surjective (j : Elliptic.Kind) (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = sphereValue j) :
    ¬ Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) := by
  intro hs
  obtain ⟨v, hv⟩ := hs (1 : ℂ)
  have hzv := congrArg (fun L : FM →L[ℂ] ℂ => L v) (elliptic_mfderiv_eq_zero j y hy)
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (hv.symm.trans hzv)

theorem zero_mfderiv_not_surjective (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = ((0 : ℂ) : RiemannSphere)) :
    ¬ Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) :=
  elliptic_mfderiv_not_surjective .three y (by simpa only [sphereValue_three] using hy)

theorem one_mfderiv_not_surjective (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere)) :
    ¬ Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) :=
  elliptic_mfderiv_not_surjective .four y (by simpa only [sphereValue_four] using hy)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification
