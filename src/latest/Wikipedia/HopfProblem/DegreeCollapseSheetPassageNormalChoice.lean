import Wikipedia.HopfProblem.DegreeCollapsePrescribedSheetTube
import Wikipedia.HopfProblem.DegreeCollapseLongitudinalSheetTransversality

/-!
# Actual relative sheet passages retaining a chosen terminal normal frame

Choose the endpoint charts and clean arc once. For every automorphism of
the terminal normal sheet factor, construct a compactly supported passage
with the same initial chart germ and the prescribed terminal germ. All
other sheets in the protected image are fixed throughout the motion.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap Topology
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "V₄" => D₂ × D₂
local notation "W₅" => ℝ × V₄

variable {E M X Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]
  [TopologicalSpace Z] [ChartedSpace D₂ Z] [IsManifold (𝓡 2) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_relative_sheet_passages_with_normal_change
    {f : X → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (range f) (range g))
    (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b) (hbc : IsClosed (range b))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hbx : f x ∉ range b) (hby : g y ∉ range b) (γ : Path (f x) (g y)) :
    ∃ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
      (0 : W₅) ∈ Φ₀.source ∧ ((1 : ℝ), (0 : V₄)) ∈ Φ₁.source ∧
      Φ₀ 0 = f x ∧ Φ₁ (1, 0) = g y ∧
      (∀ z ∈ Φ₀.source, Φ₀ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
      (∀ z ∈ Φ₁.source, Φ₁ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
      ∀ C : D₂ ≃L[ℝ] D₂, ∃ (R : D₂ ≃L[ℝ] D₂) (ε : ℝ), 0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
          ∃ A : LongitudinalTubeMotion Φ,
            Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V₄) ε ⊆ Φ.source ∧
            Φ 0 = f x ∧ Φ (1, 0) = g y ∧
            ((Φ : W₅ → M) =ᶠ[𝓝 (0 : W₅)] Φ₀) ∧
            ((Φ : W₅ → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V₄))]
              linearTransverseChart (C.prodCongr R) Φ₁) ∧
            (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
            (∀ z ∈ Φ.source, Φ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
            Φ.target ⊆ (range b)ᶜ ∧
            (∀ t z, z ∈ range b → A.family (t, z) = z) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y,
              A.family (t, f u) = g v ↔ t = A.time ∧ u = x ∧ v = y) ∧
            NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, E)
              (fun p : ℝ × X => A.family (p.1, f p.2)) g (A.time, x) y := by
  have hx : f x ∉ range g := fun h => (disjoint_left.mp hdisj) ⟨x, rfl⟩ h
  have hy : g y ∉ range f := fun h => (disjoint_left.mp hdisj) h ⟨y, rfl⟩
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁,
      a, ha, hleft, hright, hemb, hi, hcount₀, hcount₁, haO⟩ :=
    exists_clean_two_sheet_arc_avoiding hf hg hfe hge hfi hgi hb hbc hdim
      x y hx hy hbx hby γ
  refine ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, ?_⟩
  intro C
  have hinj : InjOn a (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, hrecf, hrecg, hΦO⟩ :=
    exists_clean_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁
      hleft hright (isCompact_range hf.continuous).isClosed
      (isCompact_range hg.continuous).isClosed hrec₀ hrec₁ hcount₀ hcount₁
      hbc.isOpen_compl haO C
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V₄)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, mem_closedBall_self hε.le⟩
  have h0 : (0 : W₅) ∈ Φ.source := hzero ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have hfx : Φ 0 = f x := (haxis 0).trans (hleft.eq_of_nhds.trans hΦx)
  have hgy : Φ (1, 0) = g y := (haxis 1).trans (hright.eq_of_nhds.trans hΦy)
  obtain ⟨A⟩ := nonempty_longitudinalTubeMotion Φ hzero
  refine ⟨R, ε, hε, Φ, A, hprod, hfx, hgy, hgl, hgr, hrecf, hrecg, hΦO,
    ?_, A.whole_sheet_crossing_iff hfe.injective hge.injective hdisj hrecf hrecg
      x y hfx hgy h0,
    A.whole_sheet_transverse (hf.mdifferentiable (by simp) x)
      (hg.mdifferentiable (by simp) y) (hfi x) (hgi y) hrecf hrecg hfx hgy h0⟩
  intro t z hz
  exact A.fixed_outside_target t z (fun h => hΦO h hz)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
