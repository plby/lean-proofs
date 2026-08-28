import Wikipedia.SmoothSixDPoincare.ProtectedComplementarySheetArc
import Wikipedia.SmoothSixDPoincare.ComplementarySheetPrescribedTube
import Wikipedia.HopfProblem.DegreeCollapseLongitudinalSheetTransversality
import Wikipedia.HopfProblem.DegreeCollapseWholeSheetCrossing

/-!
# Prescribed normal changes for actual complementary sheet passages

Keep the original endpoint charts and protected image while independently
choosing the terminal normal automorphism. The complementary sheet dimensions
need not agree. In particular, this includes a three-sphere passing a
two-dimensional belt while fixing the other three-spheres in a six-level.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M X Y L H Z : Type*} {m n : ℕ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [IsManifold (𝓡 m) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [IsManifold (𝓡 n) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]
  [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
  [TopologicalSpace H] {I : ModelWithCorners ℝ L H}
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z] [SecondCountableTopology Z]

local notation "P" => EuclideanSpace ℝ (Fin m)
local notation "Q" => EuclideanSpace ℝ (Fin n)
local notation "V" => P × Q
local notation "W" => ℝ × V

theorem exists_relative_complementary_passages_with_normal_change
    {f : X → M} {g : Y → M} (hf : ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ g) (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (range f) (range g))
    (hm : 0 < m) (hn : 0 < n) (hdim : Module.finrank ℝ E = m + n + 1)
    (b : C(Z, M)) (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hbc : IsClosed (range b))
    (hbdim : 1 + Module.finrank ℝ L < Module.finrank ℝ E)
    (x : X) (y : Y) (hbx : f x ∉ range b) (hby : g y ∉ range b)
    (γ : Path (f x) (g y)) :
    ∃ Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
      (0 : W) ∈ Φ₀.source ∧ ((1 : ℝ), (0 : V)) ∈ Φ₁.source ∧
      Φ₀ 0 = f x ∧ Φ₁ (1, 0) = g y ∧
      (∀ z ∈ Φ₀.source, Φ₀ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
      (∀ z ∈ Φ₁.source, Φ₁ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
      ∀ C : P ≃L[ℝ] P, ∃ (R : Q ≃L[ℝ] Q) (ε : ℝ), 0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
          ∃ A : LongitudinalTubeMotion Φ,
            Icc (0 : ℝ) 1 ×ˢ closedBall (0 : V) ε ⊆ Φ.source ∧
            Φ 0 = f x ∧ Φ (1, 0) = g y ∧
            ((Φ : W → M) =ᶠ[𝓝 (0 : W)] Φ₀) ∧
            ((Φ : W → M) =ᶠ[𝓝 ((1 : ℝ), (0 : V))]
              linearTransverseChart (C.prodCongr R) Φ₁) ∧
            (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
            (∀ z ∈ Φ.source, Φ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
            Φ.target ⊆ (range b)ᶜ ∧
            (∀ t z, z ∈ range b → A.family (t, z) = z) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y,
              A.family (t, f u) = g v ↔ t = A.time ∧ u = x ∧ v = y) ∧
            NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓡 n) 𝓘(ℝ, E)
              (fun p : ℝ × X => A.family (p.1, f p.2)) g (A.time, x) y := by
  have hx : f x ∉ range g := fun h => Set.disjoint_left.mp hdisj (mem_range_self x) h
  have hy : g y ∉ range f := fun h => Set.disjoint_left.mp hdisj h (mem_range_self y)
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁,
      a, ha, hleft, hright, hemb, hi, hcount₀, hcount₁, haO, _⟩ :=
    ComplementarySheetPassage.exists_protected_sheet_arc_in_path_class
      hf hg hfe hge hfi hgi hm hn hdim x y hx hy γ b hb hbc hbdim hbx hby
  refine ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, ?_⟩
  intro C
  have hinj : InjOn a (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, hrecf, hrecg, hΦO⟩ :=
    ComplementarySheetPassage.exists_clean_sheet_tube_with_normal_change
      ha hinj hi hm hn hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright
      (isCompact_range hf.continuous).isClosed (isCompact_range hg.continuous).isClosed
      hrec₀ hrec₁ (fun t ht hne h => hne ((hcount₀ t ht).mp h))
      (fun t ht hne h => hne ((hcount₁ t ht).mp h)) hbc.isOpen_compl haO C
  have hzero : Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, mem_closedBall_self hε.le⟩
  have h0 : (0 : W) ∈ Φ.source := hzero ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
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
