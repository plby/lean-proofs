/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreedClusterGeometry
import ErdosProblems.Erdos547b.SourceMidpointReservoirs
import ErdosProblems.Erdos547b.RegularTargetRowConcentration

/-! # Actual midpoint families and the two-square-root root exclusion -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreedMidpointSystem

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceClaim617Switch Erdos547b.ZhaoSourceSwitchUnion
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingCopySupport
open Erdos547b.ZhaoSourceFreedClusterGeometry Erdos547b.ZhaoSourceMidpointReservoirs
open Erdos547b.ZhaoRegularTargetRowConcentration

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (sw : Switch W Q S O)

abbrev Data := (e : FreedIndex W Q S O sw) → Reservoirs W (freedCluster W Q S O sw e)

theorem exists_data (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) : Nonempty (Data W Q S O sw) := by
  exact ⟨fun e => Classical.choice (exists_reservoirs W hα hα1 hhost horder _
    (freedCluster_large W Q S O sw e))⟩

variable (D : Data W Q S O sw)

def raw (s : Fin 2) (e : FreedIndex W Q S O sw) : Finset (Fin hostN) :=
  if s = 0 then (D e).high else (D e).low

def pool (s : Fin 2) : Finset (Fin hostN) := Finset.univ.biUnion (raw W Q S O sw D s)

theorem raw_subset (s : Fin 2) (e : FreedIndex W Q S O sw) :
    raw W Q S O sw D s e ⊆ whole W Q S O sw e := by
  fin_cases s
  · exact (D e).high_subset
  · exact (D e).low_subset

theorem raw_disjoint (s : Fin 2) :
    (↑(Finset.univ : Finset (FreedIndex W Q S O sw)) : Set (FreedIndex W Q S O sw)).PairwiseDisjoint
      (raw W Q S O sw D s) := by
  intro e _ f _ hef
  exact (whole_disjoint W Q S O sw e f hef).mono (raw_subset W Q S O sw D s e)
    (raw_subset W Q S O sw D s f)

theorem raw_large (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (s : Fin 2) (e : FreedIndex W Q S O sw) :
    (epsilon α : ℝ) * (whole W Q S O sw e).card ≤ (raw W Q S O sw D s e).card := by
  rw [whole_card]
  fin_cases s
  · exact high_large W (D e) hα hα1
  · exact low_large W (D e) hα hα1 hhost horder

theorem pools_disjoint : Disjoint (pool W Q S O sw D 0) (pool W Q S O sw D 1) := by
  apply Finset.disjoint_left.mpr
  intro z hz0 hz1
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hz0
  obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp hz1
  by_cases hef : e = f
  · subst f
    exact Finset.disjoint_left.mp (D e).disjoint he hf
  · exact Finset.disjoint_left.mp (whole_disjoint W Q S O sw e f hef)
      (raw_subset W Q S O sw D 0 e he) (raw_subset W Q S O sw D 1 f hf)

theorem pool_disjoint_hostSupport (s : Fin 2) :
    Disjoint (pool W Q S O sw D s) (hostSupport W Q (fullMatching W Q S O sw)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hy
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hz
  exact Finset.disjoint_left.mp (whole_disjoint_hostSupport W Q S O sw e)
    (raw_subset W Q S O sw D s e he) hy

theorem high_pool_degree {z : Fin hostN} (hz : z ∈ pool W Q S O sw D 0) : q ≤ G.degree z := by
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hz
  exact (D e).high_degree z he

theorem low_pool_degree {z : Fin hostN} (hz : z ∈ pool W Q S O sw D 1) :
    (1 - 5 * (degreeError α : ℝ)) * q ≤ (G.degree z : ℝ) := by
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hz
  exact (D e).low_degree z he

def bad (s : Fin 2) : Finset (Fin hostN) :=
  targetBad (embeddingHost W) (clusterVertices (assignment W) Q.A) Finset.univ
    (whole W Q S O sw) (raw W Q S O sw D s) (epsilon α : ℝ) (rootTypicality α : ℝ)

def rootAvoid (s : Fin 2) : Finset (Fin hostN) :=
  if s = 0 then bad W Q S O sw D 0 ∪ bad W Q S O sw D 1 else ∅

theorem bad_card (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (s : Fin 2) :
    ((bad W Q S O sw D s).card : ℝ) ≤ (rootTypicality α : ℝ) * W.clusterSize := by
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have hε : (epsilon α : ℝ) ≤ 1 := by
    exact_mod_cast (show epsilon α ≤ 1 by linarith only [heSmall, hdOne])
  have h := card_targetBad_le (embeddingHost W) (clusterVertices (assignment W) Q.A) Finset.univ
    (whole W Q S O sw) (raw W Q S O sw D s) (epsilon α : ℝ) (rootTypicality α : ℝ)
    hε (by exact_mod_cast (rootTypicality_margin hα hα1).1)
    (by exact_mod_cast (rootTypicality_sq α).symm.le)
    (fun e _ => (root_pair W Q S O sw hα hα1 e).1)
    (fun e _ => raw_subset W Q S O sw D s e)
    (fun e _ => raw_large W Q S O sw D hα hα1 hhost horder s e)
  simpa only [bad, clusterVertices_partitionAssignment, W.equal_clusters Q.A.val Q.A.property] using h

theorem rootAvoid_card (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (s : Fin 2) :
    ((rootAvoid W Q S O sw D s).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * W.clusterSize := by
  unfold rootAvoid
  split_ifs
  · have hu : ((bad W Q S O sw D 0 ∪ bad W Q S O sw D 1).card : ℝ) ≤
        (bad W Q S O sw D 0).card + (bad W Q S O sw D 1).card := by
      exact_mod_cast Finset.card_union_le _ _
    linarith only [hu, bad_card W Q S O sw D hα hα1 hhost horder 0,
      bad_card W Q S O sw D hα hα1 hhost horder 1]
  · have hδ : (0 : ℝ) ≤ rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1.le
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem pool_degree_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4) (s : Fin 2)
    (L : ℝ) (hL : 0 ≤ L) (hsize : ∀ e, L ≤ (raw W Q S O sw D s e).card)
    {z : Fin hostN} (hz : z ∈ clusterVertices (assignment W) Q.A)
    (havoid : z ∉ rootAvoid W Q S O sw D 0) :
    (1 - 2 * (eta α : ℝ) - 2 * (epsilon α : ℝ)) * L *
      (1 - (rootTypicality α : ℝ)) * Fintype.card (FreedIndex W Q S O sw) ≤
        (degreeInto (embeddingHost W) z (pool W Q S O sw D s) : ℝ) := by
  have hc : 0 ≤ 1 - 2 * (eta α : ℝ) - 2 * (epsilon α : ℝ) := by
    obtain ⟨hr11, hrr1, her, _⟩ := parameter_upper_bounds hα hα1
    obtain ⟨_, _, _, _, he, hd⟩ := reservoir_cleanup_bounds hα hα1
    exact_mod_cast (show 0 ≤ 1 - 2 * eta α - 2 * epsilon α by
      linarith only [hr11, hrr1, her, he, hd])
  have hn : z ∉ bad W Q S O sw D s := by
    intro h
    apply havoid
    change z ∈ bad W Q S O sw D 0 ∪ bad W Q S O sw D 1
    fin_cases s
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have h := degree_union_lower (embeddingHost W) (clusterVertices (assignment W) Q.A) Finset.univ
    (whole W Q S O sw) (raw W Q S O sw D s) (epsilon α : ℝ) (rootTypicality α : ℝ)
    (1 - 2 * (eta α : ℝ) - 2 * (epsilon α : ℝ)) L hc hL
    (raw_disjoint W Q S O sw D s) (fun e _ => by
      have hp := (root_pair W Q S O sw hα hα1 e).2
      linarith only [hp]) (fun e _ => hsize e) hz hn
  simpa only [pool, Finset.card_univ] using h

end Erdos547b.ZhaoSourceFreedMidpointSystem

#print axioms Erdos547b.ZhaoSourceFreedMidpointSystem.exists_data
#print axioms Erdos547b.ZhaoSourceFreedMidpointSystem.pool_disjoint_hostSupport
#print axioms Erdos547b.ZhaoSourceFreedMidpointSystem.rootAvoid_card
#print axioms Erdos547b.ZhaoSourceFreedMidpointSystem.pool_degree_lower
