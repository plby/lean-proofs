import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold

/-! # Native inverse functions with boundaryless models on both manifolds -/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {D E H H' X Y : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ E H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y]

/-- Both original manifold models are retained by the constructed local inverse. -/
theorem exists_partialDiffeomorph_boundaryless {f : X → Y} {U : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I J ∞ f U)
    (hinv : (mfderiv I J f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I J X Y ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ EqOn f Φ Φ.source := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  let V : Set X := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hc⟩
  have hcf : ContMDiffOn I 𝓘(ℝ, E) ∞ (c ∘ f) V :=
    c.contMDiffOn_toFun.comp (hf.mono inter_subset_left) (fun _ hy => hy.2)
  have hci : (mfderiv J 𝓘(ℝ, E) c (f x)).IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))
  have hderiv : (mfderiv I 𝓘(ℝ, E) (c ∘ f) x).IsInvertible := by
    rw [mfderiv_comp x (c.mdifferentiableAt (by simp) hc)
      ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hci.comp hinv
  obtain ⟨d, hd, hdV, hdf⟩ := exists_partialDiffeomorph_between_manifolds hV hxV hcf hderiv
  have hdx : d x ∈ c.target := by
    have heq : d x = c (f x) := (hdf hd).symm
    rw [heq]
    exact c.map_source' hc
  refine ⟨d.trans c.symm, ⟨hd, hdx⟩, fun y hy => (hdV hy.1).1, ?_⟩
  intro y hy
  have heq : d y = c (f y) := (hdf hy.1).symm
  change f y = c.symm (d y)
  rw [heq]
  exact (c.left_inv' (hdV hy.1).2).symm

/-- Invertible native differential gives a local diffeomorphism for both given models. -/
theorem isLocalDiffeomorphAt_boundaryless {f : X → Y} {U : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I J ∞ f U)
    (hinv : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_boundaryless hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

end Wikipedia.SmoothSixDPoincare
