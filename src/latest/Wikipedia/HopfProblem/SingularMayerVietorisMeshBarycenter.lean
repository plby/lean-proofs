import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Metric contraction at the barycenter of a finite vertex list

The barycenter is the actual normalized vector sum. Its distance to a
vertex is bounded by `n / (n + 1)` times a pairwise vertex-distance bound:
the sum of differences has `n + 1` terms, but the self term is zero.
Convexity of a closed ball extends this estimate to the whole convex hull.
-/

noncomputable section

open Set Metric
open scoped BigOperators

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/-- The actual barycenter of a nonempty ordered list of vertices. -/
def vertexBarycenter (v : Fin (n + 1) → E) : E :=
  (1 / ((n : ℝ) + 1)) • ∑ i, v i

/-- An equal-weight barycenter lies in any convex set containing its vertices. -/
theorem vertexBarycenter_mem_of_convex (v : Fin (n + 1) → E)
    {s : Set E} (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : vertexBarycenter v ∈ s := by
  simpa [vertexBarycenter, Finset.centerMass, Nat.cast_add, Nat.cast_one, one_div] using
    hs.centerMass_mem (t := Finset.univ) (w := fun _ : Fin (n + 1) => (1 : ℝ))
      (z := v) (by intro i hi; exact zero_le_one)
      (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
      (by intro i hi; exact hv i)

/-- The actual barycenter belongs to the convex hull of the actual vertices. -/
theorem vertexBarycenter_mem_convexHull (v : Fin (n + 1) → E) :
    vertexBarycenter v ∈ convexHull ℝ (range v) :=
  vertexBarycenter_mem_of_convex v (convex_convexHull ℝ _) fun i =>
    subset_convexHull ℝ _ (mem_range_self i)

/-- Subtracting a point from the barycenter averages the corresponding differences. -/
theorem vertexBarycenter_sub (v : Fin (n + 1) → E) (x : E) :
    vertexBarycenter v - x = (1 / ((n : ℝ) + 1)) • ∑ i, (v i - x) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [vertexBarycenter, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hn]

omit [NormedSpace ℝ E] in
/-- The self term is zero, leaving only `n` possible nonzero vertex distances. -/
theorem sum_norm_vertex_sub_le (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) (j : Fin (n + 1)) :
    (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * D := by
  calc
    (∑ i, ‖v i - v j‖) = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
      simpa only [sub_self, norm_zero, add_zero] using
        (Finset.sum_erase_add Finset.univ (fun i => ‖v i - v j‖)
          (Finset.mem_univ j)).symm
    _ ≤ ∑ _i ∈ Finset.univ.erase j, D := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [dist_eq_norm] using hpair i j
    _ = (n : ℝ) * D := by simp

/-- The metric contraction factor for the barycenter against each original vertex. -/
theorem dist_vertexBarycenter_vertex_le (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) (j : Fin (n + 1)) :
    dist (vertexBarycenter v) (v j) ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  have hc : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rw [dist_eq_norm, vertexBarycenter_sub, norm_smul, Real.norm_of_nonneg hc]
  calc
    _ ≤ (1 / ((n : ℝ) + 1)) * ∑ i, ‖v i - v j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc
    _ ≤ (1 / ((n : ℝ) + 1)) * ((n : ℝ) * D) :=
      mul_le_mul_of_nonneg_left (sum_norm_vertex_sub_le v hpair j) hc
    _ = (n : ℝ) / ((n : ℝ) + 1) * D := by ring

/-- Every point of the convex hull obeys the same barycenter-distance bound. -/
theorem dist_vertexBarycenter_convexHull_le (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) {x : E}
    (hx : x ∈ convexHull ℝ (range v)) :
    dist (vertexBarycenter v) x ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  have hball : range v ⊆ closedBall (vertexBarycenter v)
      ((n : ℝ) / ((n : ℝ) + 1) * D) := by
    rintro _ ⟨j, rfl⟩
    rw [mem_closedBall, dist_comm]
    exact dist_vertexBarycenter_vertex_le v hpair j
  have h := convexHull_min hball (convex_closedBall _ _) hx
  simpa only [mem_closedBall, dist_comm] using h

/-- The same contraction estimate holds against the barycenter of any vertex
family lying in the original convex hull, in particular for nested faces. -/
theorem dist_vertexBarycenter_vertexBarycenter_le {m : ℕ}
    (v : Fin (n + 1) → E) (w : Fin (m + 1) → E) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D)
    (hw : ∀ i, w i ∈ convexHull ℝ (range v)) :
    dist (vertexBarycenter v) (vertexBarycenter w) ≤
      (n : ℝ) / ((n : ℝ) + 1) * D :=
  dist_vertexBarycenter_convexHull_le v hpair
    (vertexBarycenter_mem_of_convex w (convex_convexHull ℝ _) hw)

/-- Selecting a nonempty list of original vertices gives the nested-face bound. -/
theorem dist_vertexBarycenter_reindex_le {m : ℕ} (v : Fin (n + 1) → E)
    (f : Fin (m + 1) → Fin (n + 1)) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (vertexBarycenter v) (vertexBarycenter (v ∘ f)) ≤
      (n : ℝ) / ((n : ℝ) + 1) * D :=
  dist_vertexBarycenter_vertexBarycenter_le v (v ∘ f) hpair fun i =>
    subset_convexHull ℝ _ (mem_range_self (f i))

/-- A pairwise bound on the vertices also bounds all distances in their convex hull. -/
theorem dist_convexHull_range_le (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) {x y : E}
    (hx : x ∈ convexHull ℝ (range v)) (hy : y ∈ convexHull ℝ (range v)) :
    dist x y ≤ D := by
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩ := convexHull_exists_dist_ge2 hx hy
  exact h.trans (hpair i j)

/-- The actual metric diameter of the convex hull has the same pairwise bound. -/
theorem convexHull_range_diam_le (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) :
    diam (convexHull ℝ (range v)) ≤ D := by
  rw [convexHull_diam]
  apply diam_le_of_forall_dist_le_of_nonempty (range_nonempty v)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact hpair i j

end Wikipedia.HopfProblem.SingularMayerVietoris
