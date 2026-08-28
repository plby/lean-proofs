import Wikipedia.HopfProblem.CuspPuncturedCovering
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Biholomorphisms between open plane domains

A bijective holomorphic map with nowhere vanishing derivative is an
analytic diffeomorphism for the inherited complex atlases on its open
source and target. The inverse is analytic by the inverse function theorem.
No manifold structure is transported along the given bijection.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannMapping

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A holomorphic map whose derivative is nonzero on an open set has a
genuine local analytic inverse at each point of that set. -/
theorem isLocalDiffeomorphAt_of_deriv_ne_zero
    (U : TopologicalSpace.Opens ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) {z : ℂ} (hz : z ∈ U) :
    IsLocalDiffeomorphAt I₁ I₁ ω f z := by
  have hfω : ContDiffOn ℂ ω f (U : Set ℂ) := hf.contDiffOn U.isOpen
  have hF (w : ℂ) (hw : w ∈ U) : ContDiffAt ℂ ω f w :=
    hfω.contDiffAt (U.isOpen.mem_nhds hw)
  have hD (w : ℂ) (hw : w ∈ U) : HasDerivAt f (deriv f w) w :=
    hf.hasDerivAt (U.isOpen.mem_nhds hw)
  let e : OpenPartialHomeomorph ℂ ℂ :=
    ((hF z hz).toOpenPartialHomeomorph f
      ((hD z hz).hasFDerivAt_equiv (hderiv z hz)) (by simp)).restr (U : Set ℂ)
  have heU : e.source ⊆ (U : Set ℂ) := by
    intro w hw
    dsimp only [e] at hw
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen] at hw
    exact hw.2
  have hze : z ∈ e.source := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.restr_source' _ _ U.isOpen]
    exact ⟨(hF z hz).mem_toOpenPartialHomeomorph_source
      ((hD z hz).hasFDerivAt_equiv (hderiv z hz)) (by simp), hz⟩
  refine ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }, hze, fun _ _ => rfl⟩
  · change ContMDiffOn I₁ I₁ ω f e.source
    exact (hfω.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro w hw
    have hwU := heU (e.map_target hw)
    exact (e.contDiffAt_symm hw
      ((hD _ hwU).hasFDerivAt_equiv (hderiv _ hwU)) (hF _ hwU)).contDiffWithinAt

/-- Restricting to open source and target gives a local biholomorphism of
their inherited complex manifolds. -/
theorem restrict_isLocalDiffeomorph
    (U V : TopologicalSpace.Opens ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U : Set ℂ))
    (hUV : MapsTo f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) :
    IsLocalDiffeomorph I₁ I₁ ω (fun z : U => (⟨f z, hUV z.property⟩ : V)) := by
  intro z
  exact isLocalDiffeomorphAt_restrictOpens I₁ I₁
    (isLocalDiffeomorphAt_of_deriv_ne_zero U hf hderiv z.property)
    U V hUV z.property

/-- A bijective holomorphic map with nowhere vanishing derivative,
bundled as a biholomorphism of the inherited open-set complex atlases. -/
def biholomorphOfBijOn
    (U V : TopologicalSpace.Opens ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U : Set ℂ))
    (hbij : BijOn f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) :
    Diffeomorph I₁ I₁ U V ω := by
  apply (restrict_isLocalDiffeomorph U V hf hbij.mapsTo hderiv).diffeomorphOfBijective
  constructor
  · intro z w hzw
    apply Subtype.ext
    exact hbij.injOn z.property w.property (congrArg Subtype.val hzw)
  · intro w
    obtain ⟨z, hz, hzw⟩ := hbij.surjOn w.property
    exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩

@[simp] theorem biholomorphOfBijOn_apply
    (U V : TopologicalSpace.Opens ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U : Set ℂ))
    (hbij : BijOn f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) (z : U) :
    biholomorphOfBijOn U V f hf hbij hderiv z = ⟨f z, hbij.mapsTo z.property⟩ := rfl

@[simp] theorem biholomorphOfBijOn_apply_coe
    (U V : TopologicalSpace.Opens ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U : Set ℂ))
    (hbij : BijOn f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) (z : U) :
    (biholomorphOfBijOn U V f hf hbij hderiv z : ℂ) = f z := rfl

end Wikipedia.HopfProblem.RiemannMapping
