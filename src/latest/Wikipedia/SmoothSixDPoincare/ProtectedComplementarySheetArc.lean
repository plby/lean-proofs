import Wikipedia.SmoothSixDPoincare.ComplementarySheetCleanArc
import Wikipedia.SmoothSixDPoincare.ArcSecondObstacleAvoidance

/-!
# A prescribed complementary-sheet joining arc avoiding an additional image

The additional image may have a third dimension. Its complement contains
the entire closed joining arc, not merely the interior, so a tube around
the arc can support a passage that fixes this image pointwise.
-/

noncomputable section

open Set Function Filter Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage

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

theorem exists_protected_sheet_arc_in_path_class {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) g y))
    (hm : 0 < m) (hn : 0 < n) (hdim : Module.finrank ℝ E = m + n + 1)
    (x : X) (y : Y) (hx : f x ∉ range g) (hy : g y ∉ range f)
    (γ : Path (f x) (g y)) (o : C(Z, M)) (ho : ContMDiff I 𝓘(ℝ, E) ∞ o)
    (hclosed : IsClosed (range o)) (hodim : 1 + Module.finrank ℝ L < Module.finrank ℝ E)
    (hxo : f x ∉ range o) (hyo : g y ∉ range o) :
    ∃ Φ Ψ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞,
      (0 : W) ∈ Φ.source ∧ ((1 : ℝ), (0 : V)) ∈ Ψ.source ∧
      Φ 0 = f x ∧ Ψ (1, 0) = g y ∧
      (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
      (∀ z ∈ Ψ.source, Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
      ∃ a : C(ℝ, M), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
        (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
        (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
        IsClosedEmbedding (fun t : unitInterval => a t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range f ↔ t = 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range g ↔ t = 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∉ range o) ∧
        ∃ (h0 : a 0 = f x) (h1 : a 1 = g y),
          ((CurveImmersion.intervalPath a).cast h0.symm h1.symm).Homotopic γ := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, hΦx, hΨy, _, _, hrecf, hrecg,
      a, ha, hleft, hright, hemb, hi, hcountf, hcountg, ha0, ha1, hclass⟩ :=
    exists_clean_sheet_arc_in_path_class hf hg hfe hge hfi hgi hm hn hdim x y hx hy γ
  have hfirst : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ range f ∪ range g := by
    intro t ht hh
    rcases hh with hh | hh
    · exact ht.1.ne' ((hcountf t ⟨ht.1.le, ht.2.le⟩).mp hh)
    · exact ht.2.ne ((hcountg t ⟨ht.1.le, ht.2.le⟩).mp hh)
  have ha0o : a 0 ∉ range o := by rw [ha0]; exact hxo
  have ha1o : a 1 ∉ range o := by rw [ha1]; exact hyo
  have hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ range o → t = 0 := by
    filter_upwards [a.continuous.continuousAt.eventually
      (hclosed.isOpen_compl.mem_nhds ha0o)] with t ht
    exact fun hh => (ht hh).elim
  have hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), a t ∈ range o → t = 1 := by
    filter_upwards [a.continuous.continuousAt.eventually
      (hclosed.isOpen_compl.mem_nhds ha1o)] with t ht
    exact fun hh => (ht hh).elim
  obtain ⟨b, hb, hbl, hbr, hbe, hbi, hrel, havoid⟩ :=
    ManifoldImmersion.exists_arc_avoiding_second_obstacle a ha hemb hi
      ((isCompact_range hf.continuous).isClosed.union
        (isCompact_range hg.continuous).isClosed) hfirst
      o ho hclosed (by omega) hodim hclean0 hclean1
  have hb0 : b 0 = f x := hbl.eq_of_nhds.trans ha0
  have hb1 : b 1 = g y := hbr.eq_of_nhds.trans ha1
  have hpath := (CurveImmersion.intervalPath_homotopic hrel).pathCast ha0.symm ha1.symm
  refine ⟨Φ, Ψ, hΦ, hΨ, hΦx, hΨy, hrecf, hrecg,
    b, hb, hbl.trans hleft, hbr.trans hright, hbe, hbi, ?_, ?_, ?_,
    hb0, hb1, hpath.symm.trans hclass⟩
  · intro t ht
    constructor
    · intro hh
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [hb1] at hh; exact hy hh
      exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 ht1⟩).1 (Or.inl hh)
    · rintro rfl
      rw [hb0]
      exact mem_range_self x
  · intro t ht
    constructor
    · intro hh
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [hb0] at hh; exact hx hh
      exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 ht1⟩).1 (Or.inr hh)
    · rintro rfl
      rw [hb1]
      exact mem_range_self y
  · intro t ht
    by_cases ht0 : t = 0
    · subst t; rw [hb0]; exact hxo
    by_cases ht1 : t = 1
    · subst t; rw [hb1]; exact hyo
    exact (havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
      lt_of_le_of_ne ht.2 ht1⟩).2

end Wikipedia.SmoothSixDPoincare.ComplementarySheetPassage
