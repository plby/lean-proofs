import Wikipedia.SmoothSixDPoincare.RelativeFrameField
import Wikipedia.SmoothSixDPoincare.FrameFieldComplement

/-!
# Extend a prescribed local two-frame over a compact planar region

First extend the local linear-map-valued field with a smooth cutoff, keeping
its entire germ near the closed prescribed set. Then repair rank only away
from that set. This constructs the relative two-frame extension in normal
dimension at least four without assuming a Stiefel-connectivity theorem.
Constructing the sheet-compatible boundary frame remains a separate task.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend the actual local field globally smoothly, preserving its full germ near a closed set. -/
theorem exists_global_field_with_closed_germ {L : Plane → F}
    {U C : Set Plane} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    (hC : IsClosed C) (hCU : C ⊆ U) :
    ∃ L₀ : Plane → F, ContDiff ℝ ∞ L₀ ∧ L₀ =ᶠ[𝓝ˢ C] L := by
  have hdisj : Disjoint Uᶜ C := disjoint_left.mpr (fun _ hxU hxC => hxU (hCU hxC))
  obtain ⟨β, hβ0, hβ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Plane) hU.isClosed_compl hC hdisj (n := ⊤)
  let L₀ : Plane → F := fun x => β x • L x
  have hβ : ContDiff ℝ ∞ (β : Plane → ℝ) := β.contMDiff.contDiff
  have hL₀ : ContDiff ℝ ∞ L₀ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hx))
    · apply (contDiffAt_const :
        ContDiffAt ℝ ∞ (fun _ : Plane => (0 : F)) x).congr_of_eventuallyEq
      have hβx : ∀ᶠ y in 𝓝 x, β y = 0 := hβ0.filter_mono (nhds_le_nhdsSet hx)
      filter_upwards [hβx] with y hy
      change β y • L y = 0
      rw [hy, zero_smul]
  refine ⟨L₀, hL₀, ?_⟩
  filter_upwards [hβ1] with x hx
  change β x • L x = L x
  rw [hx, one_smul]

variable [FiniteDimensional ℝ F]

/-- Construct a full-rank extension over a compact region, retaining every prescribed local germ. -/
theorem exists_fullRank_extension_of_local_field {L : Plane → (Plane →L[ℝ] F)}
    {U C K : Set Plane} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hi : ∀ x ∈ K ∩ C, Injective (L x)) (hdim : 4 ≤ Module.finrank ℝ F) :
    ∃ L' : Plane → (Plane →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∀ x ∈ K, Injective (L' x) := by
  obtain ⟨L₀, hL₀, heq⟩ := exists_global_field_with_closed_germ hU hL hC hCU
  have hi₀ : ∀ x ∈ K ∩ C, Injective (L₀ x) := by
    intro x hx
    rw [heq.self_of_nhdsSet hx.2]
    exact hi x hx
  obtain ⟨L', hL', hrel, hi'⟩ := exists_fullRank_field_rel_closed hL₀ hdim hK hC hi₀
  exact ⟨L', hL', hrel.trans heq, hi'⟩

end Wikipedia.SmoothSixDPoincare.FrameField

namespace Wikipedia.SmoothSixDPoincare.FrameField

open PlaneImmersion (Plane)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Extend the prescribed two columns and construct complementary columns near a
compact star-convex planar region in a four-dimensional normal model. Only the
original two columns, not the newly chosen complement, have prescribed germs. -/
theorem exists_completed_frame_of_local_field {L : Plane → (Plane →L[ℝ] F)}
    {U C K : Set Plane} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : Plane) K) (h0 : (0 : Plane) ∈ K)
    (hi : ∀ x ∈ K ∩ C, Injective (L x)) (hdim : Module.finrank ℝ F = 4) :
    ∃ L' : Plane → (Plane →L[ℝ] F), ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧
      ∃ V : Set Plane, IsOpen V ∧ K ⊆ V ∧
        ∃ B : Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
          ContDiffOn ℝ ∞ B V ∧
          (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
          ∀ x ∈ V, Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_fullRank_extension_of_local_field hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ Plane + 2 = Module.finrank ℝ F := by
    change Module.finrank ℝ (ℝ × ℝ) + 2 = Module.finrank ℝ F
    rw [Module.finrank_prod, Module.finrank_self, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

end Wikipedia.SmoothSixDPoincare.FrameField
