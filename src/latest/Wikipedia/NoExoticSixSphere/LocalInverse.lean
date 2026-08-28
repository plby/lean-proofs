import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Smooth local inverse on an open domain

This packages the analytic inverse-function theorem as a smooth partial
diffeomorphism. The domain is restricted to points with invertible derivative,
so smoothness of the inverse is proved at every point, not merely at the center.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A smooth map with invertible derivative has a smooth local inverse on a smaller open set. -/
theorem exists_partialDiffeomorph_of_contDiffOn {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hinv : (fderiv ℝ f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ (Φ : E → F) = f := by
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨A, hA⟩ := hinv
  have hfd : HasFDerivAt f (A : E →L[ℝ] F) x := by
    rw [hA]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  let g := hfx.toOpenPartialHomeomorph f hfd (by simp)
  let W := U ∩ interior {y | (fderiv ℝ f y).IsInvertible}
  have hW : IsOpen W := hU.inter isOpen_interior
  have hxW : x ∈ W := by
    refine ⟨hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    have ho : IsOpen {L : E →L[ℝ] F | L.IsInvertible} := ContinuousLinearEquiv.isOpen
    exact (hfx.continuousAt_fderiv (by simp)) (ho.mem_nhds ⟨A, hA⟩)
  let r := g.restrOpen W hW
  have hsource : r.source ⊆ U := fun _ h ↦ h.2.1
  have hto : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ r r.source :=
    (hf.mono hsource).contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r.symm r.target := by
    intro y hy
    have hys := r.map_target hy
    have hiy : (fderiv ℝ f (r.symm y)).IsInvertible :=
      interior_subset (s := {z : E | (fderiv ℝ f z).IsInvertible}) hys.2.2
    obtain ⟨Ay, hAy⟩ := hiy
    have hfy : ContDiffAt ℝ ∞ f (r.symm y) := hf.contDiffAt (hU.mem_nhds hys.2.1)
    have hfdy : HasFDerivAt r (Ay : E →L[ℝ] F) (r.symm y) := by
      change HasFDerivAt f (Ay : E →L[ℝ] F) (r.symm y)
      rw [hAy]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    exact (r.contDiffAt_symm hy hfdy hfy).contMDiffAt.contMDiffWithinAt
  refine ⟨{ r.toPartialEquiv with
    open_source := r.open_source
    open_target := r.open_target
    contMDiffOn_toFun := hto
    contMDiffOn_invFun := hsymm }, ?_, hsource, rfl⟩
  exact ⟨hfx.mem_toOpenPartialHomeomorph_source hfd (by simp), hxW⟩

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The model coordinates used to implement a tangent fiber. -/
def tangentModelEquiv (x : M) : TangentSpace I x ≃L[ℝ] E where
  toFun v := v
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- An extended chart on a boundaryless manifold is a smooth partial diffeomorphism. -/
noncomputable def modelChartPartialDiffeomorph (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

omit [CompleteSpace F] in
/-- The inverse-function theorem for a boundaryless modeled manifold and a normed target. -/
theorem isLocalDiffeomorphAt_of_invertible_mvfderiv {f : M → F} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hinv : (mvfderiv I f x).IsInvertible) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ f x := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let fc : E → F := f ∘ c.symm
  have hfc : ContDiffOn ℝ ∞ fc c.target :=
    (hf.comp_contMDiffOn c.contMDiffOn_invFun).contDiffOn
  have hc : x ∈ c.source := mem_extChartAt_source x
  have hderiv : mvfderiv I f x = fderiv ℝ fc (c x) := by
    simpa [fc, c, modelChartPartialDiffeomorph, writtenInExtChartAt,
      extChartAt_self_eq, chartAt_self_eq, ModelWithCorners.range_eq_univ] using
      (hf.mdifferentiable (by simp) x).mvfderiv
  have hfcinv : (fderiv ℝ fc (c x)).IsInvertible := by
    obtain ⟨A, hA⟩ := hinv
    refine ⟨(tangentModelEquiv (I := I) x).symm.trans A, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : TangentSpace I x →L[ℝ] F ↦ L v) (hA.trans hderiv)
  obtain ⟨d, hd, _, hdf⟩ := exists_partialDiffeomorph_of_contDiffOn
    c.open_target (c.map_source' hc) hfc hfcinv
  refine ⟨c.trans d, ⟨hc, hd⟩, ?_⟩
  intro y hy
  change f y = d (c y)
  rw [hdf]
  change f y = f (c.symm (c y))
  exact (congrArg f (c.left_inv' hy.1)).symm

end NoExoticSixSphere
