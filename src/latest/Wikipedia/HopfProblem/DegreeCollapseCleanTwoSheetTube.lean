import Wikipedia.HopfProblem.DegreeCollapseCleanTubeRestriction

/-!
# A clean tube joining two original two-dimensional sheets in dimension five

The entire original sheet images are recognized throughout the tube:
the first is the plane at longitudinal coordinate zero with second
transverse factor zero, and the second is the complementary plane at
coordinate one. The arc, both endpoint charts, orientation correction,
germ gluing, and positive uniform tube radius are all constructed.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap Topology
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₄" => D₂ × D₂
local notation "W₅" => ℝ × V₄

variable {E M X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]

theorem exists_clean_two_sheet_tube {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hx : f x ∉ range g) (hy : g y ∉ range f) (γ : Path (f x) (g y)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
        Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V₄) ε ⊆ Φ.source ∧
        Φ 0 = f x ∧ Φ (1, 0) = g y ∧
        (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
        (∀ z ∈ Φ.source, Φ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) := by
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, -, -, hrec₀, hrec₁,
      a, ha, hleft, hright, hemb, hi, hcount₀, hcount₁⟩ :=
    exists_clean_two_sheet_arc hf hg hfe hge hfi hgi hdim x y hx hy γ
  have hinj : InjOn a (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  obtain ⟨R, r, hr, Ψ, hΨprod, haxis, hgl, hgr, -⟩ :=
    exists_sheet_arc_tube ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright
      isOpen_univ (fun _ _ => mem_univ _)
  let C := (ContinuousLinearEquiv.refl ℝ D₂).prodCongr R
  let Φ₂ := linearTransverseChart C Φ₁
  have hΦ₂ : ((1 : ℝ), (0 : V₄)) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source C Φ₁ 1).mpr hΦ₁
  have hrec₂ : ∀ z ∈ Φ₂.source, Φ₂ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Φ₁ (z.1, (z.2.1, R z.2.2)) ∈ range g ↔ _
    exact hrec₁ (z.1, (z.2.1, R z.2.2)) hz.2
  have hlocal₀ : ∀ᶠ z : W₅ in 𝓝 (0 : W₅),
      Ψ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0 := by
    filter_upwards [hgl, Φ₀.open_source.mem_nhds hΦ₀] with z he hz
    rw [he]
    exact hrec₀ z hz
  have hlocal₁ : ∀ᶠ z : W₅ in 𝓝 ((1 : ℝ), (0 : V₄)),
      Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    filter_upwards [hgr, Φ₂.open_source.mem_nhds hΦ₂] with z he hz
    rw [he]
    exact hrec₂ z hz
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V₄)} ⊆ Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΨprod ⟨ht, mem_closedBall_self hr.le⟩
  have haway₀ : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → Ψ (t, 0) ∉ range f := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₀ t ht).mp hh)
  have haway₁ : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 1 → Ψ (t, 0) ∉ range g := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₁ t ht).mp hh)
  obtain ⟨ε, hε, Φ, hprod, hformula, -, hrecf, hrecg⟩ :=
    exists_clean_axis_tube_restriction Ψ isCompact_Icc hzero
      (isCompact_range hf.continuous).isClosed (isCompact_range hg.continuous).isClosed
      0 1 {v : V₄ | v.2 = 0} {v : V₄ | v.1 = 0} hlocal₀ hlocal₁ haway₀ haway₁
  refine ⟨ε, hε, Φ, hprod, ?_, ?_, hrecf, hrecg⟩
  · change Φ (0, 0) = f x
    rw [hformula, haxis]
    exact hleft.eq_of_nhds.trans hΦx
  · rw [hformula, haxis]
    exact hright.eq_of_nhds.trans hΦy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
