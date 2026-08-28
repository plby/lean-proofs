import Wikipedia.HopfProblem.DegreeCollapseSheetEndpointOrientation
import Wikipedia.SmoothSixDPoincare.StarConvexTubularNeighborhood

/-!
# One native tube retaining both full sheet endpoint chart germs

Construct a tube along the actual embedded immersive arc. Correct the
terminal transverse determinant in its second factor, then glue the full
native endpoint chart germs. The entire axis is unchanged and has a
positive uniform transverse radius. No tube or orientation match is input.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₄" => D₂ × D₂
local notation "W₅" => ℝ × V₄

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_sheet_arc_tube {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a)
    (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞)
    (hΦ₀ : (0 : W₅) ∈ Φ₀.source) (hΦ₁ : ((1 : ℝ), (0 : V₄)) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0))
    (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : MapsTo a (Icc (0 : ℝ) 1) O) :
    ∃ (R : D₂ ≃L[ℝ] D₂) (ε : ℝ), 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V₄) ε ⊆ Φ.source ∧
        (∀ t : ℝ, Φ (t, 0) = a t) ∧
        ((Φ : W₅ → M) =ᶠ[𝓝 (0 : W₅)] Φ₀) ∧
        ((Φ : W₅ → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V₄))]
            linearTransverseChart ((ContinuousLinearEquiv.refl ℝ D₂).prodCongr R) Φ₁) ∧
        Φ.target ⊆ O := by
  have h0K : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1K : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨r, hr, Ξ, hΞprod, hΞaxis, hΞO⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      ha isCompact_Icc h0K ((convex_Icc (0 : ℝ) 1).starConvex h0K) hinj hi 4
      (by rw [Module.finrank_self, hdim]) hO haO
  let L : V₄ ≃L[ℝ] EuclideanSpace ℝ (Fin 4) := ContinuousLinearEquiv.ofFinrankEq (by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin])
  let P := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L).toDiffeomorph
  let Ψ := P.toPartialDiffeomorph.trans Ξ
  have hΨaxis (t : ℝ) : Ψ (t, 0) = a t := by
    change Ξ (t, L 0) = a t
    rw [map_zero, hΞaxis]
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V₄)} ⊆ Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change (t, (0 : V₄)) ∈ univ ∧ (t, L 0) ∈ Ξ.source
    rw [map_zero]
    exact ⟨mem_univ _, hΞprod ⟨ht, mem_closedBall_self hr.le⟩⟩
  have hΨ₀ : (0 : W₅) ∈ Ψ.source := hzero ⟨h0K, rfl⟩
  have hΨ₁ : ((1 : ℝ), (0 : V₄)) ∈ Ψ.source := hzero ⟨h1K, rfl⟩
  have haxis₀ : (fun t : ℝ => Φ₀ (t, 0)) =ᶠ[𝓝 (0 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hleft] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  have haxis₁ : (fun t : ℝ => Φ₁ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  obtain ⟨R, hsign⟩ := exists_compatible_sheet_endpoint_orientation
    (Module.finBasis ℝ D₂) ⟨0, by simp only [finrank_euclideanSpace_fin]; norm_num⟩
    Ψ Φ₀ Φ₁ hΨ₀ hΨ₁ hΦ₀ hΦ₁ haxis₀ haxis₁
  let C := (ContinuousLinearEquiv.refl ℝ D₂).prodCongr R
  let Φ₂ := linearTransverseChart C Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V₄)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source C Φ₁ 1).mpr hΦ₁
  have haxis₂ : (fun t : ℝ => Φ₂ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [haxis₁] with t ht
    exact (linearTransverseChart_axis C Φ₁ t).trans ht
  let _ : Nontrivial (Fin (Module.finrank ℝ V₄)) :=
    Fin.nontrivial_iff_two_le.mpr (by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
      norm_num)
  obtain ⟨ε, hε, Φ, hprod, htarget, haxis, hgl, hgr⟩ :=
    AxisCoordinates.exists_native_axis_chart_with_endpoint_germs (Module.finBasis ℝ V₄)
      Ψ Φ₀ Φ₂ zero_lt_one isCompact_Icc hzero hΨ₀ hΨ₁ hΦ₀ hΦ₂ haxis₀ haxis₂ hsign
  exact ⟨R, ε, hε, Φ, hprod, fun t => (haxis t).trans (hΨaxis t), hgl, hgr,
    fun z hz => hΞO (htarget hz).1⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
