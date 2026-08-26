/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceDegreeFormRootRows

/-! # Physical degree-form densities and their two threshold graphs -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceThresholdGraphs

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClusterPairPruning Erdos547b.ZhaoSourceParameterSchedule

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem host_respects :
    EdgesRespectReducedGraph (padAssignment (assignment W)) (host W) (padGraph (reduced W)) := by
  apply edgesRespect_pad
  exact respects_pruned_reduced_graph (assignment W) W.graph
    (regularityReducedGraph (pruneSmallEdges G {v | q ≤ G.degree v})
      (fun i : Index W => i.val) (epsilon α) (densityCutoff α)) (large W) W.respects_reduced

def density (x y : EvenPadding (Index W)) : ℝ :=
  (host W).edgeDensity (clusterVertices (padAssignment (assignment W)) x)
    (clusterVertices (padAssignment (assignment W)) y)

theorem density_symm (x y : EvenPadding (Index W)) : density W x y = density W y x := by
  exact congrArg (fun r : ℚ => (r : ℝ)) ((host W).edgeDensity_comm _ _)

theorem density_nonneg (x y : EvenPadding (Index W)) : 0 ≤ density W x y := by
  unfold density
  exact_mod_cast (host W).edgeDensity_nonneg
    (clusterVertices (padAssignment (assignment W)) x) (clusterVertices (padAssignment (assignment W)) y)

theorem density_le_one (x y : EvenPadding (Index W)) : density W x y ≤ 1 := by
  unfold density
  exact_mod_cast (host W).edgeDensity_le_one
    (clusterVertices (padAssignment (assignment W)) x) (clusterVertices (padAssignment (assignment W)) y)

theorem density_nonadj_zero {x y : EvenPadding (Index W)}
    (hxy : ¬(padGraph (reduced W)).Adj x y) : density W x y = 0 := by
  have hempty : (host W).interedges (clusterVertices (padAssignment (assignment W)) x)
      (clusterVertices (padAssignment (assignment W)) y) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have h := (SimpleGraph.mem_interedges_iff _).mp he
    exact hxy (host_respects W
      ((mem_clusterVertices _ _ _).mp h.1) ((mem_clusterVertices _ _ _).mp h.2.1) h.2.2)
  unfold density
  rw [SimpleGraph.edgeDensity_def, hempty]
  norm_num

def threshold (τ : ℝ) : SimpleGraph (EvenPadding (Index W)) where
  Adj x y := (padGraph (reduced W)).Adj x y ∧ τ ≤ density W x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, (density_symm W _ _) ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem threshold_le (τ : ℝ) : threshold W τ ≤ padGraph (reduced W) := fun _ _ h => h.1

theorem threshold_antitone {τ υ : ℝ} (hτυ : τ ≤ υ) : threshold W υ ≤ threshold W τ :=
  fun _ _ h => ⟨h.1, hτυ.trans h.2⟩

theorem threshold_adj_iff {τ : ℝ} (hτ : 0 < τ) (x y : EvenPadding (Index W)) :
    (threshold W τ).Adj x y ↔ τ ≤ density W x y := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hn
    rw [density_nonadj_zero W hn] at h
    exact (not_le_of_gt hτ) h

theorem eta_threshold_properties (hα : 0 < α) :
    threshold W (2 * (eta α : ℝ)) ≤ threshold W (eta α : ℝ) ∧
    threshold W (eta α : ℝ) ≤ padGraph (reduced W) ∧
    (∀ x y, (threshold W (2 * (eta α : ℝ))).Adj x y → 2 * (eta α : ℝ) ≤ density W x y) ∧
    (∀ x y, (threshold W (eta α : ℝ)).Adj x y ↔ (eta α : ℝ) ≤ density W x y) := by
  have hη : (0 : ℝ) < eta α := by exact_mod_cast (parameter_pos hα).2.2.1
  exact ⟨threshold_antitone W (by linarith only [hη]), threshold_le W _,
    fun _ _ h => h.2, threshold_adj_iff W hη⟩

end Erdos547b.ZhaoSourceThresholdGraphs

#print axioms Erdos547b.ZhaoSourceThresholdGraphs.density_nonadj_zero
#print axioms Erdos547b.ZhaoSourceThresholdGraphs.eta_threshold_properties
