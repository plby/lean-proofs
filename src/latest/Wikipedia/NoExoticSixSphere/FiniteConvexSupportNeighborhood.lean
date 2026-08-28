import Wikipedia.NoExoticSixSphere.FiniteConvexFundamentalSupport

/-!
# Finite-convex fundamental supports around an arbitrary compact set

Inside any open neighborhood of a compact Euclidean subset, a finite
union of closed balls contains that subset in its interior. The preceding
finite-union theorem supplies the actual homological detection, vanishing,
and unique fundamental class on the constructed neighborhood. Passing
these properties to the original compact subset still requires relative
homology continuity; it is not asserted here.
-/

noncomputable section

open Set Metric
open scoped Topology

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- A compact set has arbitrarily small neighborhoods with the proved support properties. -/
theorem exists_finiteConvex_support_neighborhood (K U : Set E) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set E, CompactFundamentalSupport (E := E) n L ∧ K ⊆ interior L ∧ L ⊆ U := by
  classical
  have hradius : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall (x : E) r ⊆ U := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU x.property))
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hball⟩
  choose r hr hsub using hradius
  have hcover : K ⊆ ⋃ x : K, ball (x : E) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (r x))
    (fun _ => isOpen_ball) hcover
  let L : Set E := ⋃ x ∈ s, closedBall (x : E) (r x)
  have hinner : (⋃ x ∈ s, ball (x : E) (r x)) ⊆ L := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp hy
    obtain ⟨hx, hy⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, ball_subset_closedBall hy⟩⟩
  have hopen : IsOpen (⋃ x ∈ s, ball (x : E) (r x)) :=
    isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball))
  refine ⟨L, finiteUnion_compactConvex_support n s (fun x : K => closedBall (x : E) (r x))
    (fun x _ => isCompact_closedBall (x : E) (r x))
    (fun x _ => convex_closedBall (x : E) (r x)), hs.trans (interior_maximal hinner hopen), ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp hy
  obtain ⟨_, hy⟩ := mem_iUnion.mp hx
  exact hsub x hy

end NoExoticSixSphere.SupportedRelativeHomology
