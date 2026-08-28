import Wikipedia.NoExoticSixSphere.SmoothZeroAvoidance
import Wikipedia.NoExoticSixSphere.ZeroAvoidanceCutoff
import Mathlib.Topology.Order.Compact

/-!
# Small relative zero avoidance

A continuous vector-valued map on a lower-dimensional smooth manifold can be
perturbed to miss zero. The perturbation is joined to the original map by an
arbitrarily small homotopy, fixed on any prescribed compact set where the
original map is nonzero. No smoothness of the original map on that set is needed.

Only the endpoint is asserted to miss zero: the initial map may have zeros.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {B H M F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

include I

theorem exists_nonzero_homotopy_small (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, F), (∀ x, g x ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel f g {x | 2 * ε ≤ ‖f x‖},
        ∀ t x, dist (G (t, x)) (f x) < ε := by
  obtain ⟨h, -, hnonzero, hclose⟩ := exists_smooth_nonzero_approx (I := I) f ε hε hd
  refine ⟨ZeroAvoidanceCutoff.blend f h ε,
    ZeroAvoidanceCutoff.blend_ne_zero f h ε hε hnonzero hclose,
    ZeroAvoidanceCutoff.homotopy f h ε hε, ?_⟩
  exact ZeroAvoidanceCutoff.homotopy_dist_lt f h ε hε hclose

theorem exists_nonzero_homotopyRel (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (S : Set M) (hS : IsCompact S) (hSafe : ∀ x ∈ S, f x ≠ 0)
    (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, F), (∀ x, g x ≠ 0) ∧
      ∃ G : ContinuousMap.HomotopyRel f g S,
        ∀ t x, dist (G (t, x)) (f x) < ε := by
  obtain ⟨c, hc, hbound⟩ := hS.exists_forall_le' f.continuous.norm.continuousOn
    (fun x hx ↦ norm_pos_iff.mpr (hSafe x hx))
  let δ := min ε (c / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδc : 2 * δ ≤ c := by
    have hh : δ ≤ c / 2 := min_le_right _ _
    linarith
  obtain ⟨g, hg, G, hclose⟩ := exists_nonzero_homotopy_small (I := I) f δ hδ hd
  let G' : ContinuousMap.HomotopyRel f g S :=
    { toHomotopy := G.toHomotopy
      prop' := fun t x hx ↦ G.eq_fst t (hδc.trans (hbound x hx)) }
  exact ⟨g, hg, G', fun t x ↦ (hclose t x).trans_le hδε⟩

end NoExoticSixSphere
