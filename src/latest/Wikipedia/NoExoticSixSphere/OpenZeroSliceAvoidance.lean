import Wikipedia.NoExoticSixSphere.RelativeZeroAvoidance
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Avoiding a zero slice inside an open coordinate domain

For a compact lower-dimensional parameter manifold, the first coordinate of
a continuous family can be made nonzero while the second coordinate stays
fixed. The entire small relative homotopy remains in any given open domain
containing the original family.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {B H M F Q : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [PseudoMetricSpace Q]

include I

theorem exists_zeroSlice_avoiding_homotopy (f : C(M, F × Q))
    (U : Set (F × Q)) (hU : IsOpen U) (hmem : ∀ x, f x ∈ U)
    (ε : ℝ) (hε : 0 < ε) (S : Set M) (hS : IsCompact S)
    (hSafe : ∀ x ∈ S, (f x).1 ≠ 0) (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, F × Q), (∀ x, (g x).1 ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel f g S,
        ∀ t x, G (t, x) ∈ U ∧ dist (G (t, x)) (f x) < ε ∧
          (G (t, x)).2 = (f x).2 := by
  have hRange : range f ⊆ U := by
    rintro y ⟨x, rfl⟩
    exact hmem x
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_range f.continuous).exists_thickening_subset_open hU hRange
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  let f₁ : C(M, F) := ⟨fun x ↦ (f x).1, f.continuous.fst⟩
  obtain ⟨g₁, hg₁, G₁, hclose⟩ := exists_nonzero_homotopyRel (I := I)
    f₁ η hη S hS hSafe hd
  let g : C(M, F × Q) := ⟨fun x ↦ (g₁ x, (f x).2), g₁.continuous.prodMk f.continuous.snd⟩
  let G : ContinuousMap.HomotopyRel f g S :=
    { toFun := fun p ↦ (G₁ p, (f p.2).2)
      continuous_toFun := G₁.continuous.prodMk (f.continuous.snd.comp continuous_snd)
      map_zero_left := fun x ↦ by simp [f₁]
      map_one_left := fun x ↦ by simp [g]
      prop' := fun t x hx ↦ by
        change (G₁ (t, x), (f x).2) = f x
        rw [G₁.eq_fst t hx]
        rfl }
  have hdist (t) (x) : dist (G (t, x)) (f x) < η := by
    change dist (G₁ (t, x), (f x).2) ((f x).1, (f x).2) < η
    rw [dist_prod_same_right]
    exact hclose t x
  refine ⟨g, hg₁, G, fun t x ↦ ⟨?_, (hdist t x).trans_le (min_le_left _ _), rfl⟩⟩
  exact hthick (Metric.mem_thickening_iff.mpr
    ⟨f x, mem_range_self x, (hdist t x).trans_le (min_le_right _ _)⟩)

theorem exists_zeroSlice_avoiding_chart_homotopy {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph E (F × Q)) (f : C(M, E))
    (V : Set E) (hV : IsOpen V) (hsource : V ⊆ e.source) (hmem : ∀ x, f x ∈ V)
    (S : Set M) (hS : IsCompact S) (hSafe : ∀ x ∈ S, (e (f x)).1 ≠ 0)
    (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, E), (∀ x, (e (g x)).1 ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel f g S,
        ∀ t x, G (t, x) ∈ V ∧ (e (G (t, x))).2 = (e (f x)).2 := by
  let W := e.target ∩ e.symm ⁻¹' V
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hV
  let f' : C(M, F × Q) := ⟨fun x ↦ e (f x), continuous_iff_continuousAt.mpr
    (fun x ↦ (e.continuousAt (hsource (hmem x))).comp f.continuous.continuousAt)⟩
  have hf' (x) : f' x ∈ W := by
    refine ⟨e.map_source (hsource (hmem x)), ?_⟩
    change e.symm (e (f x)) ∈ V
    rw [e.left_inv (hsource (hmem x))]
    exact hmem x
  obtain ⟨g', hg', G', hpath⟩ := exists_zeroSlice_avoiding_homotopy (I := I)
    f' W hW hf' 1 zero_lt_one S hS hSafe hd
  have hgTarget (x) : g' x ∈ e.target := by
    have hh := (hpath 1 x).1.1
    simpa only [G'.apply_one] using hh
  let g : C(M, E) := ⟨fun x ↦ e.symm (g' x), continuous_iff_continuousAt.mpr
    (fun x ↦ (e.continuousAt_symm (hgTarget x)).comp g'.continuous.continuousAt)⟩
  let G : ContinuousMap.HomotopyRel f g S :=
    { toFun := fun p ↦ e.symm (G' p)
      continuous_toFun := continuous_iff_continuousAt.mpr (fun p ↦
        (e.continuousAt_symm (hpath p.1 p.2).1.1).comp G'.continuous.continuousAt)
      map_zero_left := fun x ↦ by
        rw [G'.apply_zero]
        exact e.left_inv (hsource (hmem x))
      map_one_left := fun x ↦ by rw [G'.apply_one]; rfl
      prop' := fun t x hx ↦ by
        change e.symm (G' (t, x)) = f x
        rw [G'.eq_fst t hx]
        exact e.left_inv (hsource (hmem x)) }
  refine ⟨g, fun x ↦ ?_, G, fun t x ↦ ⟨(hpath t x).1.2, ?_⟩⟩
  · change (e (e.symm (g' x))).1 ≠ 0
    rw [e.right_inv (hgTarget x)]
    exact hg' x
  · change (e (e.symm (G' (t, x)))).2 = (e (f x)).2
    rw [e.right_inv (hpath t x).1.1]
    exact (hpath t x).2.2

end NoExoticSixSphere
