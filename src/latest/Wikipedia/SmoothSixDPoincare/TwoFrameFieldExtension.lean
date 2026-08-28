import Wikipedia.SmoothSixDPoincare.LocalFrameFieldExtension

/-!
# Relative two-frame extension with the original column model

Transport only the two-dimensional column model to the plane for the rank
repair argument, then transport back. The output retains the entire original
field germ, not a chosen reparametrization of its range.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Extend a two-frame without changing its original two-dimensional column model. -/
theorem exists_fullRank_extension_of_local_field_finrank_two
    (hd : Module.finrank ℝ D = 2) {L : Plane → (D →L[ℝ] F)}
    {U C K : Set Plane} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hi : ∀ x ∈ K ∩ C, Injective (L x)) (hdim : 4 ≤ Module.finrank ℝ F) :
    ∃ L' : Plane → (D →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∀ x ∈ K, Injective (L' x) := by
  have heqdim : Module.finrank ℝ Plane = Module.finrank ℝ D := by
    change Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ D
    rw [Module.finrank_prod, Module.finrank_self, hd]
  let j : Plane ≃L[ℝ] D := ContinuousLinearEquiv.ofFinrankEq heqdim
  let A : Plane → (Plane →L[ℝ] F) := fun x => (L x).comp j.toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A U := hL.clm_comp contDiffOn_const
  have hiA : ∀ x ∈ K ∩ C, Injective (A x) := fun x hx => (hi x hx).comp j.injective
  obtain ⟨A', hA', heq, hi'⟩ :=
    exists_fullRank_extension_of_local_field hU hA hC hCU hK hiA hdim
  let L' : Plane → (D →L[ℝ] F) := fun x => (A' x).comp j.symm.toContinuousLinearMap
  refine ⟨L', hA'.clm_comp contDiff_const, ?_, fun x hx => (hi' x hx).comp j.symm.injective⟩
  filter_upwards [heq] with x hx
  apply ContinuousLinearMap.ext
  intro y
  change A' x (j.symm y) = L x y
  rw [hx]
  change L x (j (j.symm y)) = L x y
  rw [j.apply_symm_apply]

end Wikipedia.SmoothSixDPoincare.FrameField

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Extend the actual two columns and complete them near a compact star-convex region. -/
theorem exists_completed_frame_of_local_field_finrank_two
    (hd : Module.finrank ℝ D = 2) {L : Plane → (D →L[ℝ] F)}
    {U C K : Set Plane} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : Plane) K) (h0 : (0 : Plane) ∈ K)
    (hi : ∀ x ∈ K ∩ C, Injective (L x)) (hdim : Module.finrank ℝ F = 4) :
    ∃ L' : Plane → (D →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∃ V : Set Plane, IsOpen V ∧ K ⊆ V ∧
        ∃ B : Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
          ContDiffOn ℝ ∞ B V ∧
          (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
          ∀ x ∈ V, Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_fullRank_extension_of_local_field_finrank_two hd hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ D + 2 = Module.finrank ℝ F := by rw [hd, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

end Wikipedia.SmoothSixDPoincare.FrameField
