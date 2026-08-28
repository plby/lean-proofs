import Wikipedia.HopfProblem.DegreeCollapseCleanTubeAvoidingSheets

/-!
# Clean sheet tubes with a prescribed terminal normal change

Keep the initial endpoint chart fixed. An arbitrary automorphism of the
first terminal transverse factor can be prescribed before the second
factor corrects the ambient orientation. The same clean arc and both full
sheet equations survive, as does avoidance of the protected image.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap Topology
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₄" => D₂ × D₂
local notation "W₅" => ℝ × V₄

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_sheet_arc_tube_with_normal_change {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a)
    (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞)
    (hΦ₀ : (0 : W₅) ∈ Φ₀.source) (hΦ₁ : ((1 : ℝ), (0 : V₄)) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0))
    (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : MapsTo a (Icc (0 : ℝ) 1) O)
    (C : D₂ ≃L[ℝ] D₂) :
    ∃ (R : D₂ ≃L[ℝ] D₂) (ε : ℝ), 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V₄) ε ⊆ Φ.source ∧
        (∀ t : ℝ, Φ (t, 0) = a t) ∧
        ((Φ : W₅ → M) =ᶠ[𝓝 (0 : W₅)] Φ₀) ∧
        ((Φ : W₅ → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V₄))]
          linearTransverseChart (C.prodCongr R) Φ₁) ∧
        Φ.target ⊆ O := by
  let Φ₂ := linearTransverseChart (C.prodCongr (ContinuousLinearEquiv.refl ℝ D₂)) Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V₄)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hright₂ : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₂ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.trans (linearTransverseChart_axis _ Φ₁ t).symm
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, htarget⟩ :=
    exists_sheet_arc_tube ha hinj hi hdim Φ₀ Φ₂ hΦ₀ hΦ₂ hleft hright₂ hO haO
  refine ⟨R, ε, hε, Φ, hprod, haxis, hgl, ?_, htarget⟩
  filter_upwards [hgr] with z hz
  exact hz

theorem exists_clean_sheet_arc_tube_with_normal_change {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a)
    (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞)
    (hΦ₀ : (0 : W₅) ∈ Φ₀.source) (hΦ₁ : ((1 : ℝ), (0 : V₄)) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0))
    (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {S T O : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (hrec₀ : ∀ z ∈ Φ₀.source, Φ₀ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrec₁ : ∀ z ∈ Φ₁.source, Φ₁ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0)
    (hcount₀ : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ S ↔ t = 0)
    (hcount₁ : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ T ↔ t = 1)
    (hO : IsOpen O) (haO : MapsTo a (Icc (0 : ℝ) 1) O)
    (C : D₂ ≃L[ℝ] D₂) :
    ∃ (R : D₂ ≃L[ℝ] D₂) (ε : ℝ), 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V₄) ε ⊆ Φ.source ∧
        (∀ t : ℝ, Φ (t, 0) = a t) ∧
        ((Φ : W₅ → M) =ᶠ[𝓝 (0 : W₅)] Φ₀) ∧
        ((Φ : W₅ → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V₄))]
          linearTransverseChart (C.prodCongr R) Φ₁) ∧
        (∀ z ∈ Φ.source, Φ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
        (∀ z ∈ Φ.source, Φ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
        Φ.target ⊆ O := by
  obtain ⟨R, r, hr, Ψ, hΨprod, haxis, hgl, hgr, hΨO⟩ :=
    exists_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁
      hleft hright hO haO C
  let Φ₂ := linearTransverseChart (C.prodCongr R) Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V₄)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hrec₂ : ∀ z ∈ Φ₂.source, Φ₂ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Φ₁ (z.1, (C z.2.1, R z.2.2)) ∈ T ↔ _
    rw [hrec₁ (z.1, (C z.2.1, R z.2.2)) hz.2, map_eq_zero_iff C C.injective]
  have hlocal₀ : ∀ᶠ z : W₅ in 𝓝 (0 : W₅),
      Ψ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0 := by
    filter_upwards [hgl, Φ₀.open_source.mem_nhds hΦ₀] with z he hz
    rw [he]
    exact hrec₀ z hz
  have hlocal₁ : ∀ᶠ z : W₅ in 𝓝 ((1 : ℝ), (0 : V₄)),
      Ψ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    filter_upwards [hgr, Φ₂.open_source.mem_nhds hΦ₂] with z he hz
    rw [he]
    exact hrec₂ z hz
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V₄)} ⊆ Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΨprod ⟨ht, mem_closedBall_self hr.le⟩
  have haway₀ : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → Ψ (t, 0) ∉ S := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₀ t ht).mp hh)
  have haway₁ : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 1 → Ψ (t, 0) ∉ T := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₁ t ht).mp hh)
  obtain ⟨ε, hε, Φ, hprod, hformula, hΦΨ, hrecS, hrecT⟩ :=
    exists_clean_axis_tube_restriction Ψ isCompact_Icc hzero hS hT
      0 1 {v : V₄ | v.2 = 0} {v : V₄ | v.1 = 0} hlocal₀ hlocal₁ haway₀ haway₁
  refine ⟨R, ε, hε, Φ, hprod, fun t => (hformula _).trans (haxis t),
    ?_, ?_, hrecS, hrecT, hΦΨ.trans hΨO⟩
  · filter_upwards [hgl] with z hz
    exact (hformula z).trans hz
  · filter_upwards [hgr] with z hz
    exact (hformula z).trans hz

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
