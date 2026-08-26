/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCoordinateMixedDynamicOnline

/-!
# Prefix-independent bounds for mixed dynamic coordinate pools

The used set of an arbitrary realized prefix is bounded by the literal
coordinate-pool load.  These lemmas turn that fact into lower bounds for a
live endpoint and for its live neighbourhood, so applications need not
quantify separate capacity estimates over every possible prefix.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u} {Pool : Type*}
variable [Fintype B] [DecidableEq B] [DecidableEq Pool]
variable (F : HierarchicalSegmentForest r s)
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (rootPool : Fin s → Pool)
variable (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
variable (pairPool : Fin s → Fin 2 → Pool)
variable (raw : Pool → Finset B)

/-- A raw endpoint is covered by its live residual together with the used
vertices of the same physical pool. -/
theorem card_raw_le_card_mixedAvailable_add_load
    (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j)
    (c : Fin 2) :
    #(raw (pairPool i c)) ≤
      #(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
  let used := mixedUsedPool F G rootPool interiorPool raw i (pairPool i c) prior
  let live := mixedAvailable F G rootPool interiorPool pairPool raw i c prior
  have hsub : raw (pairPool i c) ⊆ live ∪ used := by
    intro z hz
    by_cases hzu : z ∈ used
    · exact Finset.mem_union_right _ hzu
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hz, hzu⟩
  have hused : #used ≤
      coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
    exact card_coordinateUsedPool_le_load F G rootPool interiorPool
      (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw) i (pairPool i c) prior
  calc
    #(raw (pairPool i c)) ≤ #(live ∪ used) := Finset.card_le_card hsub
    _ ≤ #live + #used := Finset.card_union_le _ _
    _ ≤ #live + coordinatePoolLoad F rootPool interiorPool (pairPool i c) :=
      Nat.add_le_add_left hused _

/-- The same accounting after filtering by adjacency to the already embedded
parent. -/
theorem card_rawNeighbors_le_card_mixedNeighbors_add_load
    (originalImage : Fin r → B)
    (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j)
    (c : Fin 2) :
    #((raw (pairPool i c)).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
          i prior))) ≤
      #((mixedAvailable F G rootPool interiorPool pairPool raw i c prior).filter
          (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
            i prior))) +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
  let parent := mixedParentImage F G originalImage rootPool interiorPool raw
    i prior
  let used := mixedUsedPool F G rootPool interiorPool raw i (pairPool i c) prior
  let live := mixedAvailable F G rootPool interiorPool pairPool raw i c prior
  let rawN := (raw (pairPool i c)).filter (G.Adj parent)
  let liveN := live.filter (G.Adj parent)
  have hsub : rawN ⊆ liveN ∪ used := by
    intro z hz
    have hzRaw := (Finset.mem_filter.mp hz).1
    have hzAdj := (Finset.mem_filter.mp hz).2
    by_cases hzu : z ∈ used
    · exact Finset.mem_union_right _ hzu
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hzRaw, hzu⟩, hzAdj⟩
  have hused : #used ≤
      coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
    exact card_coordinateUsedPool_le_load F G rootPool interiorPool
      (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw) i (pairPool i c) prior
  calc
    #rawN ≤ #(liveN ∪ used) := Finset.card_le_card hsub
    _ ≤ #liveN + #used := Finset.card_union_le _ _
    _ ≤ #liveN + coordinatePoolLoad F rootPool interiorPool (pairPool i c) :=
      Nat.add_le_add_left hused _

/-- A static raw-cardinality margin implies the dynamic large-subset
condition for every prefix. -/
theorem mixedAvailable_large_of_load
    (whole : Pool → Finset B) (rho : ℝ)
    (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j)
    (c : Fin 2)
    (hmargin : rho * (#(whole (pairPool i c)) : ℝ) +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) ≤
      #(raw (pairPool i c))) :
    rho * (#(whole (pairPool i c)) : ℝ) ≤
      (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ) := by
  have hcard := card_raw_le_card_mixedAvailable_add_load F G rootPool
    interiorPool pairPool raw i prior c
  have hcardR : (#(raw (pairPool i c)) : ℝ) ≤
      #(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
    exact_mod_cast hcard
  linarith

/-- A static gap-times-load reserve implies the dynamic pair margin for every
prefix. -/
theorem mixedAvailable_pairMargin_of_load
    (whole : Pool → Finset B) (rho density need : ℝ)
    (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j)
    (c : Fin 2)
    (hgap : 0 ≤ density - rho)
    (hmargin : need + (density - rho) *
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) ≤
      (density - rho) * #(raw (pairPool i c))) :
    need ≤ (density - rho) *
      (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ) := by
  have hcard := card_raw_le_card_mixedAvailable_add_load F G rootPool
    interiorPool pairPool raw i prior c
  have hcardR : (#(raw (pairPool i c)) : ℝ) ≤
      #(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
    exact_mod_cast hcard
  nlinarith

/-- A static parent-neighbour reserve implies the dynamic parent condition
after deleting every earlier image in the same pool. -/
theorem mixedParent_neighbours_of_load
    (originalImage : Fin r → B) (need : ℝ)
    (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j)
    (c : Fin 2)
    (hdegree : need +
        coordinatePoolLoad F rootPool interiorPool (pairPool i c) ≤
      #((raw (pairPool i c)).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
          i prior)))) :
    need ≤
      (#((mixedAvailable F G rootPool interiorPool pairPool raw i c prior).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw i
          prior))) : ℝ) := by
  have hcard := card_rawNeighbors_le_card_mixedNeighbors_add_load F G
    rootPool interiorPool pairPool raw originalImage i prior c
  have hcardR :
      (#((raw (pairPool i c)).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw i
          prior))) : ℝ) ≤
        #((mixedAvailable F G rootPool interiorPool pairPool raw i c prior).filter
          (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw i
            prior))) +
          coordinatePoolLoad F rootPool interiorPool (pairPool i c) := by
    exact_mod_cast hcard
  linarith

/-- Strictly more raw neighbours than the pool load leaves a live neighbour
for a singleton root-only step. -/
theorem mixedSelectedRootAvailable_nonempty_of_load
    (originalImage : Fin r → B)
    (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j)
    (hdegree : coordinatePoolLoad F rootPool interiorPool (rootPool i) <
      #((raw (rootPool i)).filter
        (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
          i prior)))) :
    (mixedSelectedRootAvailable F G originalImage rootPool interiorPool raw i
      prior).Nonempty := by
  let parent := mixedParentImage F G originalImage rootPool interiorPool raw
    i prior
  let used := mixedUsedPool F G rootPool interiorPool raw i (rootPool i) prior
  let rawN := (raw (rootPool i)).filter (G.Adj parent)
  let liveN := (raw (rootPool i) \ used).filter (G.Adj parent)
  have hused : #used ≤ coordinatePoolLoad F rootPool interiorPool (rootPool i) :=
    card_coordinateUsedPool_le_load F G rootPool interiorPool
      (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw) i (rootPool i) prior
  have hsub : rawN ⊆ liveN ∪ used := by
    intro z hz
    have hzRaw := (Finset.mem_filter.mp hz).1
    have hzAdj := (Finset.mem_filter.mp hz).2
    by_cases hzu : z ∈ used
    · exact Finset.mem_union_right _ hzu
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hzRaw, hzu⟩, hzAdj⟩)
  have hcard : #rawN ≤ #liveN + #used :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  change coordinatePoolLoad F rootPool interiorPool (rootPool i) < #rawN at hdegree
  have hcard' : #rawN ≤ #liveN +
      coordinatePoolLoad F rootPool interiorPool (rootPool i) :=
    hcard.trans (Nat.add_le_add_left hused _)
  have hlive : 0 < #liveN := by omega
  rw [Finset.card_pos] at hlive
  simpa [mixedSelectedRootAvailable, mixedAvailable, liveN, used, parent] using
    hlive

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds

#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds.HierarchicalSegmentForest.mixedAvailable_large_of_load
#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds.HierarchicalSegmentForest.mixedAvailable_pairMargin_of_load
#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds.HierarchicalSegmentForest.mixedParent_neighbours_of_load
#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicBounds.HierarchicalSegmentForest.mixedSelectedRootAvailable_nonempty_of_load
