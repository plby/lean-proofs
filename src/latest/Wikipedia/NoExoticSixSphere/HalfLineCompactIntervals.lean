import Wikipedia.NoExoticSixSphere.ReflectionQuotientCoordinate
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Small compact interval neighborhoods in the half-line

The lower endpoint is clipped at zero. Consequently the interior of the
closed interval is taken in the actual half-line topology, retaining its
zero endpoint when present. These interiors have compact closure and finite
frontier and can be chosen inside any given open neighborhood.
-/

open Set Function Metric Topology

namespace NoExoticSixSphere.HalfLineIntervals

open InvolutionQuotient

theorem halfLineOrderTopology : OrderTopology HalfLine :=
  inferInstanceAs (OrderTopology NNReal)

attribute [instance] halfLineOrderTopology

theorem coe_image_interval (a b : HalfLine) :
    (Subtype.val : HalfLine → ℝ) '' Icc a b = Icc a.val b.val := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, a.property.trans hx.1⟩, hx, rfl⟩

theorem isCompact_interval (a b : HalfLine) : IsCompact (Icc a b) := by
  apply IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [coe_image_interval]
  exact isCompact_Icc

theorem closure_interior_interval {a b : HalfLine} (hab : a < b) :
    closure (interior (Icc a b)) = Icc a b := by
  apply subset_antisymm (closure_minimal interior_subset isClosed_Icc)
  have hsub : Ioo a b ⊆ interior (Icc a b) :=
    interior_maximal Ioo_subset_Icc_self isOpen_Ioo
  simpa only [closure_Ioo hab.ne] using closure_mono hsub

theorem frontier_interior_interval_subset {a b : HalfLine} (hab : a < b) :
    frontier (interior (Icc a b)) ⊆ {a, b} := by
  rw [frontier, interior_interior, closure_interior_interval hab,
    ← Icc_sdiff_Ioo_same hab.le]
  have hsub : Ioo a b ⊆ interior (Icc a b) :=
    interior_maximal Ioo_subset_Icc_self isOpen_Ioo
  exact sdiff_subset_sdiff_right hsub

theorem finite_frontier_interior_interval {a b : HalfLine} (hab : a < b) :
    (frontier (interior (Icc a b))).Finite :=
  (toFinite {a, b}).subset (frontier_interior_interval_subset hab)

theorem exists_interval_in_open {V : Set HalfLine} (hV : IsOpen V)
    (y : HalfLine) (hy : y ∈ V) :
    ∃ a b : HalfLine, a < b ∧ y ∈ interior (Icc a b) ∧ Icc a b ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hy)
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let a : HalfLine := ⟨max 0 (y.val - ε), le_max_left _ _⟩
  let b : HalfLine := ⟨y.val + ε, add_nonneg y.property hε.le⟩
  have hab : a < b := by
    change max 0 (y.val - ε) < y.val + ε
    exact max_lt_iff.mpr ⟨by linarith [y.property], by linarith⟩
  have hball : ball y ε ⊆ Icc a b := by
    intro z hz
    have hd : |z.val - y.val| < ε := by
      simpa only [mem_ball, Subtype.dist_eq, Real.dist_eq] using hz
    have hd' := abs_lt.mp hd
    change max 0 (y.val - ε) ≤ z.val ∧ z.val ≤ y.val + ε
    exact ⟨max_le_iff.mpr ⟨z.property, by linarith⟩, by linarith⟩
  refine ⟨a, b, hab, interior_maximal hball isOpen_ball (mem_ball_self hε), ?_⟩
  intro z hz
  apply hδV
  have hlo : y.val - ε ≤ z.val := (le_max_right _ _).trans hz.1
  have hup : z.val ≤ y.val + ε := hz.2
  have hd : |z.val - y.val| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
  apply mem_ball.mpr
  change |z.val - y.val| < δ
  exact lt_of_le_of_lt hd (by dsimp [ε]; linarith)

end NoExoticSixSphere.HalfLineIntervals
