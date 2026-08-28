import Wikipedia.SmoothSixDPoincare.ComplementarySheetArcTube
import Wikipedia.HopfProblem.DegreeCollapseCleanTubeRestriction

/-!
# Prescribe the terminal normal change for complementary sheets of unequal dimensions

The first transverse automorphism is prescribed. Only the second factor
corrects the ambient orientation. The complete axis, both endpoint germs,
full sheet recognition, and confinement to the chosen open set survive.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage

open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} {m n : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "P" => EuclideanSpace ℝ (Fin m)
local notation "Q" => EuclideanSpace ℝ (Fin n)
local notation "V" => P × Q
local notation "W" => ℝ × V

theorem exists_sheet_arc_tube_with_normal_change {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hm : 0 < m) (hn : 0 < n) (hdim : Module.finrank ℝ E = m + n + 1)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    (hΦ₀ : (0 : W) ∈ Φ₀.source) (hΦ₁ : ((1 : ℝ), (0 : V)) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0))
    (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : MapsTo a (Icc (0 : ℝ) 1) O)
    (C : P ≃L[ℝ] P) :
    ∃ (R : Q ≃L[ℝ] Q) (ε : ℝ), 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V) ε ⊆ Φ.source ∧
        (∀ t : ℝ, Φ (t, 0) = a t) ∧
        ((Φ : W → M) =ᶠ[𝓝 (0 : W)] Φ₀) ∧
        ((Φ : W → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V))]
          linearTransverseChart (C.prodCongr R) Φ₁) ∧ Φ.target ⊆ O := by
  let Φ₂ := linearTransverseChart (C.prodCongr (ContinuousLinearEquiv.refl ℝ Q)) Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hright₂ : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₂ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.trans (linearTransverseChart_axis _ Φ₁ t).symm
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, htarget⟩ :=
    exists_sheet_arc_tube ha hinj hi hm hn hdim Φ₀ Φ₂ hΦ₀ hΦ₂ hleft hright₂ hO haO
  refine ⟨R, ε, hε, Φ, hprod, haxis, hgl, ?_, htarget⟩
  filter_upwards [hgr] with z hz
  exact hz

theorem exists_clean_sheet_tube_with_normal_change {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hm : 0 < m) (hn : 0 < n) (hdim : Module.finrank ℝ E = m + n + 1)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    (hΦ₀ : (0 : W) ∈ Φ₀.source) (hΦ₁ : ((1 : ℝ), (0 : V)) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0))
    (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {S T O : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (hrec₀ : ∀ z ∈ Φ₀.source, Φ₀ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrec₁ : ∀ z ∈ Φ₁.source, Φ₁ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0)
    (haway₀ : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → a t ∉ S)
    (haway₁ : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 1 → a t ∉ T)
    (hO : IsOpen O) (haO : MapsTo a (Icc (0 : ℝ) 1) O) (C : P ≃L[ℝ] P) :
    ∃ (R : Q ≃L[ℝ] Q) (ε : ℝ), 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V) ε ⊆ Φ.source ∧
        (∀ t : ℝ, Φ (t, 0) = a t) ∧
        ((Φ : W → M) =ᶠ[𝓝 (0 : W)] Φ₀) ∧
        ((Φ : W → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V))]
          linearTransverseChart (C.prodCongr R) Φ₁) ∧
        (∀ z ∈ Φ.source, Φ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
        (∀ z ∈ Φ.source, Φ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0) ∧ Φ.target ⊆ O := by
  obtain ⟨R, r, hr, Ψ, hΨprod, haxis, hgl, hgr, hΨO⟩ :=
    exists_sheet_arc_tube_with_normal_change ha hinj hi hm hn hdim Φ₀ Φ₁ hΦ₀ hΦ₁
      hleft hright hO haO C
  let Φ₂ := linearTransverseChart (C.prodCongr R) Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hrec₂ : ∀ z ∈ Φ₂.source, Φ₂ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Φ₁ (z.1, (C z.2.1, R z.2.2)) ∈ T ↔ _
    rw [hrec₁ (z.1, (C z.2.1, R z.2.2)) hz.2, map_eq_zero_iff C C.injective]
  have hlocal₀ : ∀ᶠ z : W in 𝓝 (0 : W),
      Ψ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0 := by
    filter_upwards [hgl, Φ₀.open_source.mem_nhds hΦ₀] with z he hz
    rw [he]
    exact hrec₀ z hz
  have hlocal₁ : ∀ᶠ z : W in 𝓝 ((1 : ℝ), (0 : V)),
      Ψ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    filter_upwards [hgr, Φ₂.open_source.mem_nhds hΦ₂] with z he hz
    rw [he]
    exact hrec₂ z hz
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΨprod ⟨ht, mem_closedBall_self hr.le⟩
  have hawayS : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → Ψ (t, 0) ∉ S := by
    intro t ht hne
    rw [haxis]
    exact haway₀ t ht hne
  have hawayT : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 1 → Ψ (t, 0) ∉ T := by
    intro t ht hne
    rw [haxis]
    exact haway₁ t ht hne
  obtain ⟨ε, hε, Φ, hprod, hformula, htarget, hrecS, hrecT⟩ :=
    exists_clean_axis_tube_restriction Ψ isCompact_Icc hzero hS hT
      0 1 {v : V | v.2 = 0} {v : V | v.1 = 0} hlocal₀ hlocal₁ hawayS hawayT
  refine ⟨R, ε, hε, Φ, hprod, fun t => (hformula (t, 0)).trans (haxis t),
    ?_, ?_, hrecS, hrecT, htarget.trans hΨO⟩
  · filter_upwards [hgl] with z hz
    exact (hformula z).trans hz
  · filter_upwards [hgr] with z hz
    exact (hformula z).trans hz

end Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage
