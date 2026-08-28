import Wikipedia.NoExoticSixSphere.SupportedGraphEmbedding
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Embedding a disk while retaining an outer collar

A bump of outer radius `r < 1` adds a weighted copy of the source only inside
that radius. A smooth map that is already embedded and immersive on the
remaining annulus becomes a smooth embedded disk after adding coordinates.
The construction also preserves avoidance of an old ambient subset away
from the boundary.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskGraph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def cutoff (E : Type*) [NormedAddCommGroup E] (r : ℝ) (hr : 0 < r) :
    ContDiffBump (0 : E) where
  rIn := r / 2
  rOut := r
  rIn_pos := half_pos hr
  rIn_lt_rOut := half_lt_self hr

def map (f : E → F) (r : ℝ) (hr : 0 < r) : E → F × (ℝ × E) :=
  SupportedGraph.map f (cutoff E r hr)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem cutoff_eq_zero_iff (r : ℝ) (hr : 0 < r) (x : E) :
    cutoff E r hr x = 0 ↔ r ≤ ‖x‖ := by
  constructor
  · intro hx
    by_contra hn
    have hp := (cutoff E r hr).pos_of_mem_ball
      (show x ∈ ball (0 : E) (cutoff E r hr).rOut by
        simpa only [mem_ball, dist_zero_right, cutoff] using lt_of_not_ge hn)
    exact hp.ne' hx
  · intro hx
    exact (cutoff E r hr).zero_of_le_dist
      (by simpa only [dist_zero_right, cutoff] using hx)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem map_eq_on_collar (f : E → F) (r : ℝ) (hr : 0 < r) {x : E}
    (hx : r ≤ ‖x‖) : map f r hr x = (f x, 0) :=
  SupportedGraph.map_eq_of_zero f _ ((cutoff_eq_zero_iff r hr x).mpr hx)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem map_eq_on_sphere (f : E → F) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {x : E} (hx : x ∈ sphere (0 : E) 1) : map f r hr x = (f x, 0) := by
  apply map_eq_on_collar f r hr
  have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  exact hr1.trans_eq hn.symm

theorem contDiffAt_map (f : E → F) (r : ℝ) (hr : 0 < r) {x : E}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (map f r hr) x :=
  SupportedGraph.contDiffAt_map f _ hf (cutoff E r hr).contDiff.contDiffAt

theorem injective_fderiv_map (f : E → F) (r : ℝ) (hr : 0 < r) {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hi : r ≤ ‖x‖ → Injective (fderiv ℝ f x)) :
    Injective (fderiv ℝ (map f r hr) x) := by
  apply SupportedGraph.injective_fderiv_map f _ (hf.differentiableAt (by simp))
    (((cutoff E r hr).contDiff (n := 1)).differentiable (by simp) x)
  intro hx
  exact hi ((cutoff_eq_zero_iff r hr x).mp hx)

theorem isClosedEmbedding_disk [ProperSpace E] (f : E → F) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f x)
    (hi : InjOn f (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖})) :
    IsClosedEmbedding (fun x : closedBall (0 : E) 1 ↦ map f r hr x.val) := by
  apply SupportedGraph.isClosedEmbedding_restrict f _ (isCompact_closedBall _ _)
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    ((cutoff E r hr).contDiff (n := 0)).continuous.continuousOn
  simpa only [cutoff_eq_zero_iff] using hi

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Only a zero-weight point can hit the original ambient space. -/
theorem mem_oldAmbient_iff (f : E → F) (r : ℝ) (hr : 0 < r) (S : Set F) (x : E) :
    map f r hr x ∈ S ×ˢ ({0} : Set (ℝ × E)) ↔ f x ∈ S ∧ r ≤ ‖x‖ := by
  constructor
  · rintro ⟨hf, hz⟩
    have hβ : cutoff E r hr x = 0 := congrArg Prod.fst (mem_singleton_iff.mp hz)
    exact ⟨hf, (cutoff_eq_zero_iff r hr x).mp hβ⟩
  · rintro ⟨hf, hx⟩
    rw [map_eq_on_collar f r hr hx]
    exact ⟨hf, rfl⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Avoidance on the collar suffices for the whole open disk to miss the old subset. -/
theorem avoids_oldAmbient (f : E → F) (r : ℝ) (hr : 0 < r) (S : Set F)
    (ha : ∀ x ∈ ball (0 : E) 1, r ≤ ‖x‖ → f x ∉ S) :
    ∀ x ∈ ball (0 : E) 1, map f r hr x ∉ S ×ˢ ({0} : Set (ℝ × E)) := by
  intro x hx h
  obtain ⟨hS, hrx⟩ := (mem_oldAmbient_iff f r hr S x).mp h
  exact ha x hx hrx hS

end NoExoticSixSphere.DiskGraph
