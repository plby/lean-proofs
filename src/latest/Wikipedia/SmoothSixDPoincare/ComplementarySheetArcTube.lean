import Wikipedia.HopfProblem.DegreeCollapseSheetEndpointOrientation
import Wikipedia.SmoothSixDPoincare.StarConvexTubularNeighborhood

/-!
# A tube retaining complementary-sheet endpoint charts of unequal dimensions

The terminal orientation is corrected only in its second transverse factor.
That factor can have any positive dimension. The original whole axis and
both full endpoint chart germs survive the constructed gluing.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} {m n : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "P" => EuclideanSpace ℝ (Fin m)
local notation "Q" => EuclideanSpace ℝ (Fin n)
local notation "V" => P × Q
local notation "W" => ℝ × V

theorem exists_sheet_arc_tube {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hm : 0 < m) (hn : 0 < n) (hdim : Module.finrank ℝ E = m + n + 1)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    (hΦ₀ : (0 : W) ∈ Φ₀.source) (hΦ₁ : ((1 : ℝ), (0 : V)) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0))
    (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : MapsTo a (Icc (0 : ℝ) 1) O) :
    ∃ (R : Q ≃L[ℝ] Q) (ε : ℝ), 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V) ε ⊆ Φ.source ∧
        (∀ t : ℝ, Φ (t, 0) = a t) ∧
        ((Φ : W → M) =ᶠ[𝓝 (0 : W)] Φ₀) ∧
        ((Φ : W → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V))]
          linearTransverseChart ((ContinuousLinearEquiv.refl ℝ P).prodCongr R) Φ₁) ∧
        Φ.target ⊆ O := by
  have h0K : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1K : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨r, hr, Ξ, hΞprod, hΞaxis, hΞO⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      ha isCompact_Icc h0K ((convex_Icc (0 : ℝ) 1).starConvex h0K) hinj hi (m + n)
      (by rw [Module.finrank_self, hdim]; omega) hO haO
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin (m + n)) := ContinuousLinearEquiv.ofFinrankEq (by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin])
  let F := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L).toDiffeomorph
  let Ψ := F.toPartialDiffeomorph.trans Ξ
  have hΨaxis (t : ℝ) : Ψ (t, 0) = a t := by
    change Ξ (t, L 0) = a t
    rw [map_zero, hΞaxis]
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change (t, (0 : V)) ∈ univ ∧ (t, L 0) ∈ Ξ.source
    rw [map_zero]
    exact ⟨mem_univ _, hΞprod ⟨ht, mem_closedBall_self hr.le⟩⟩
  have hΨ₀ : (0 : W) ∈ Ψ.source := hzero ⟨h0K, rfl⟩
  have hΨ₁ : ((1 : ℝ), (0 : V)) ∈ Ψ.source := hzero ⟨h1K, rfl⟩
  have haxis₀ : (fun t : ℝ => Φ₀ (t, 0)) =ᶠ[𝓝 (0 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hleft] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  have haxis₁ : (fun t : ℝ => Φ₁ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.symm.trans (hΨaxis t).symm
  obtain ⟨R, hsign⟩ := exists_compatible_sheet_endpoint_orientation
    (Module.finBasis ℝ Q) ⟨0, by simp only [finrank_euclideanSpace_fin]; exact hn⟩
    Ψ Φ₀ Φ₁ hΨ₀ hΨ₁ hΦ₀ hΦ₁ haxis₀ haxis₁
  let C := (ContinuousLinearEquiv.refl ℝ P).prodCongr R
  let Φ₂ := linearTransverseChart C Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source C Φ₁ 1).mpr hΦ₁
  have haxis₂ : (fun t : ℝ => Φ₂ (t, 0)) =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0) := by
    filter_upwards [haxis₁] with t ht
    exact (linearTransverseChart_axis C Φ₁ t).trans ht
  let _ : Nontrivial (Fin (Module.finrank ℝ V)) := Fin.nontrivial_iff_two_le.mpr (by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega)
  obtain ⟨ε, hε, Φ, hprod, htarget, haxis, hgl, hgr⟩ :=
    AxisCoordinates.exists_native_axis_chart_with_endpoint_germs (Module.finBasis ℝ V)
      Ψ Φ₀ Φ₂ zero_lt_one isCompact_Icc hzero hΨ₀ hΨ₁ hΦ₀ hΦ₂ haxis₀ haxis₂ hsign
  exact ⟨R, ε, hε, Φ, hprod, fun t => (haxis t).trans (hΨaxis t), hgl, hgr,
    fun z hz => hΞO (htarget hz).1⟩

end Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage
