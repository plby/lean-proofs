import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# A local smooth inverse into the original manifold

An invertible native derivative of a map defined smoothly on an open vector
domain gives a genuine smooth partial diffeomorphism into the native manifold.
Both the domain restriction and inverse are constructed using a target chart
and the analytic inverse-function theorem.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare

variable {D E M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The local inverse exists on a genuine open subdomain of the given smoothness domain. -/
theorem exists_partialDiffeomorph_into_manifold {f : D → M} {U : Set D} {x : D}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ EqOn f Φ Φ.source := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) (f x)
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  let V : Set D := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hc⟩
  have hcf : ContDiffOn ℝ ∞ (c ∘ f) V :=
    (c.contMDiffOn_toFun.comp (hf.mono inter_subset_left) (fun _ hy => hy.2)).contDiffOn
  have hcinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (f x)).IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))
  have hderiv : (fderiv ℝ (c ∘ f) x).IsInvertible := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x
      (c.mdifferentiableAt (by simp) hc)
      ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hcinv.comp hinv
  obtain ⟨d, hd, hdV, hdf⟩ :=
    NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn hV hxV hcf hderiv
  have hdx : d x ∈ c.target := by
    rw [hdf]
    exact c.map_source' hc
  refine ⟨d.trans c.symm, ⟨hd, hdx⟩, fun y hy => (hdV hy.1).1, ?_⟩
  intro y hy
  change f y = c.symm (d y)
  rw [hdf]
  exact (c.left_inv' (hdV hy.1).2).symm

/-- Invertibility of the native derivative gives a smooth local diffeomorphism. -/
theorem isLocalDiffeomorphAt_of_contMDiffOn {f : D → M} {U : Set D} {x : D}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_into_manifold hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

variable {H X : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- The inverse-function construction also retains an arbitrary native source manifold. -/
theorem exists_partialDiffeomorph_between_manifolds {f : X → M} {U : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv I 𝓘(ℝ, E) f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ EqOn f Φ Φ.source := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source' hxc
  have hleft (y : X) (hy : y ∈ c.source) : c.symm (c y) = y := c.left_inv' hy
  let V : Set D := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V :=
    c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcxV : c x ∈ V := ⟨hcx, by
    change c.symm (c x) ∈ U
    rwa [hleft x hxc]⟩
  have hgf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (f ∘ c.symm) V :=
    hf.comp (c.contMDiffOn_invFun.mono inter_subset_left) (fun _ hy => hy.2)
  have hcDiff : c.toOpenPartialHomeomorph.MDifferentiable I 𝓘(ℝ, D) :=
    ⟨c.mdifferentiableOn (by simp), c.symm.mdifferentiableOn (by simp)⟩
  have hci : (mfderiv 𝓘(ℝ, D) I c.symm (c x)).IsInvertible :=
    ⟨hcDiff.symm.mfderiv hcx, rfl⟩
  have hderiv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (f ∘ c.symm) (c x)).IsInvertible := by
    have hfx := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hfc : MDifferentiableAt I 𝓘(ℝ, E) f (c.symm (c x)) := by
      simpa only [hleft x hxc] using hfx
    rw [mfderiv_comp (c x) hfc (c.symm.mdifferentiableAt (by simp) hcx), hleft x hxc]
    exact hinv.comp hci
  obtain ⟨d, hd, hdV, heq⟩ := exists_partialDiffeomorph_into_manifold hV hcxV hgf hderiv
  refine ⟨c.trans d, ⟨hxc, hd⟩, ?_, ?_⟩
  · intro y hy
    have hh := (hdV hy.2).2
    change c.symm (c y) ∈ U at hh
    rwa [hleft y hy.1] at hh
  · intro y hy
    have hh := heq hy.2
    change f (c.symm (c y)) = d (c y) at hh
    change f y = d (c y)
    simpa only [hleft y hy.1] using hh

/-- Invertibility on native tangent spaces gives a local diffeomorphism between manifolds. -/
theorem isLocalDiffeomorphAt_between_manifolds {f : X → M} {U : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv I 𝓘(ℝ, E) f x).IsInvertible) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_between_manifolds hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

end Wikipedia.SmoothSixDPoincare
