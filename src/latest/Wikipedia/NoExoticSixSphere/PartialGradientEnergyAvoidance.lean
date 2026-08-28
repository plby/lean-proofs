import Wikipedia.NoExoticSixSphere.PartialGradientSmallAvoidance

/-!
# Slice avoidance with independent spatial and energy tolerances

An open relation between the moving point and its fixed original copy controls
the energy increase as well as ambient displacement. The initial neighborhood
does not shrink when either tolerance is reduced.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_energy_small_gradient_avoiding_homotopy (hU : IsOpen U)
    (hf : ContinuousOn f U) (p : C(M, E)) (V : Set E)
    (hV : IsOpen V) (hsource : V ⊆ C.chart.source) (hmem : ∀ x, p x ∈ V)
    (η ξ : ℝ) (hη : 0 < η) (hξ : 0 < ξ) (S : Set M) (hS : IsCompact S)
    (hSafe : ∀ x ∈ S, gradient f L (p x) ≠ 0) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ q : C(M, E), (∀ x, gradient f L (q x) ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel p q S,
        ∀ t x, G (t, x) ∈ V ∧ (C.chart (G (t, x))).2 = (C.chart (p x)).2 ∧
          C.center (G (t, x)) = C.center (p x) ∧ dist (G (t, x)) (p x) < η ∧
          f (G (t, x)) < f (p x) + ξ := by
  let R : Set (E × E) := ((U ×ˢ U) ∩ (fun z : E × E ↦ f z.1 - f z.2) ⁻¹' Iio ξ) ∩
    {z | dist z.1 z.2 < η}
  have he : ContinuousOn (fun z : E × E ↦ f z.1 - f z.2) (U ×ˢ U) :=
    (hf.comp continuous_fst.continuousOn (fun _ hz ↦ hz.1)).sub
      (hf.comp continuous_snd.continuousOn (fun _ hz ↦ hz.2))
  have hR : IsOpen R := (he.isOpen_inter_preimage (hU.prod hU) isOpen_Iio).inter
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const)
  have hdiag (x) : (p x, p x) ∈ R := by
    have hx := C.source_subset (hsource (hmem x))
    exact ⟨⟨⟨hx, hx⟩, by simpa only [mem_preimage, mem_Iio, sub_self] using hξ⟩,
      by simpa only [mem_ofPred_eq, dist_self] using hη⟩
  obtain ⟨q, hq, G, hG⟩ := C.exists_relational_gradient_avoiding_homotopy (I := I)
    p V hV hsource hmem R hR hdiag S hS hSafe hd
  refine ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.1,
    (hG t x).2.2.2.2, ?_⟩⟩
  have he' : f (G (t, x)) - f (p x) < ξ := (hG t x).2.2.2.1.2
  linarith

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
