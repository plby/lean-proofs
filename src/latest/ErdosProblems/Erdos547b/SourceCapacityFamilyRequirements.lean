/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyState
import ErdosProblems.Erdos547b.SourceInitialChunkTargets

/-!
# Concrete root requirements and unused targets of actual family states

The active requirement is read from the stored graph prefix. Unused-edge
targets are read from the source family kind. No root-access promise is
stored in the state or substituted for a live-set size proof.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityFamilyState

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceGeneralizedChunk
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

def activeRequirement {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) : Requirement W Q :=
  match a with
  | none => none
  | some x => x.source.requirement W Q S C F owner kind x.copyPrefix

theorem activeRequirement_valid
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hkind : kind.Valid α)
    {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) :
    requirementValid W Q S C (activeRequirement W Q S C F owner kind a) := by
  cases a with
  | none => trivial
  | some x =>
      exact x.source.requirement_valid W Q S C F owner kind
        hα hα1 hhost horder hkind x.copyPrefix

variable {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
variable {rootImage : Fin r → Fin hostN} {stage : ℕ}
variable (A : FamilyState W Q S C F owner kind all family rootImage stage)

abbrev FamilyState.reservedItems := A.completed ++ activeItems W Q S C F owner kind A.active
abbrev FamilyState.reservedEdges := A.closedEdges ∪ activeEdges W Q S C F owner kind A.active
def FamilyState.unusedEdges := all \ A.reservedEdges W Q S C F owner kind

theorem FamilyState.reserved_edges_subset : A.reservedEdges W Q S C F owner kind ⊆ all :=
  Finset.union_subset A.closed_subset A.active_subset

theorem FamilyState.reserved_before_remaining :
    ∀ i ∈ A.reservedItems W Q S C F owner kind, ∀ j ∈ A.remaining, owner i ≤ owner j := by
  have h : (A.completed ++ activeItems W Q S C F owner kind A.active ++ A.remaining).Pairwise
      (fun i j => owner i ≤ owner j) := A.flatten.symm ▸ A.family_order
  exact (List.pairwise_append.mp h).2.2

theorem FamilyState.remaining_order : A.remaining.Pairwise (fun i j => owner i ≤ owner j) := by
  have h : (A.completed ++ activeItems W Q S C F owner kind A.active ++ A.remaining).Pairwise
      (fun i j => owner i ≤ owner j) := A.flatten.symm ▸ A.family_order
  exact (List.pairwise_append.mp h).2.1

theorem FamilyState.reserved_mass_split :
    mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner kind) +
      mass (fun i => (F.size i : ℝ)) A.remaining = mass (fun i => (F.size i : ℝ)) family := by
  have h := congrArg (mass (fun i => (F.size i : ℝ))) A.flatten
  simpa only [mass, FamilyState.reservedItems, List.map_append, List.sum_append] using h

theorem FamilyState.ledger_of_current (n : Fin r)
    (hcurrent : ∃ i ∈ A.remaining, owner i = n) :
    (∑ e ∈ A.reservedEdges W Q S C F owner kind,
      (capacity W Q S C kind e - freshBranchBound α W.clusterSize)) ≤
        mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner kind) := by
  apply A.reserved_ledger
  intro hnil
  obtain ⟨i, hi, _⟩ := hcurrent
  rw [hnil] at hi
  exact List.not_mem_nil hi

/-- A matching edge has one concrete source kind because the family
matchings are disjoint. Outside them use the harmless ordinary label. -/
def allocatedKind {k : ℕ} (kinds : Fin k → FamilyKind)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M)) (e : MatchingEdge Q.claim67.M) : FamilyKind :=
  if h : ∃ j, e ∈ allocation j then kinds (Classical.choose h) else .threshold 0

theorem allocatedKind_eq {k : ℕ} (kinds : Fin k → FamilyKind)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M))
    (hdisjoint : Pairwise (fun i j => Disjoint (allocation i) (allocation j)))
    (j : Fin k) (e : MatchingEdge Q.claim67.M) (he : e ∈ allocation j) :
    allocatedKind W Q kinds allocation e = kinds j := by
  have hex : ∃ i, e ∈ allocation i := ⟨j, he⟩
  rw [allocatedKind, dif_pos hex]
  congr 1
  by_contra hne
  exact Finset.disjoint_left.mp (hdisjoint hne) (Classical.choose_spec hex) he

def allocatedTarget {k : ℕ} (kinds : Fin k → FamilyKind)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M))
    (e : MatchingEdge Q.claim67.M) (c : Fin 2) : Finset (Fin hostN) :=
  initialTarget W Q (allocatedKind W Q kinds allocation e) e c

theorem allocatedTarget_eq {k : ℕ} (kinds : Fin k → FamilyKind)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M))
    (hdisjoint : Pairwise (fun i j => Disjoint (allocation i) (allocation j)))
    (j : Fin k) (e : MatchingEdge Q.claim67.M) (he : e ∈ allocation j) :
    allocatedTarget W Q kinds allocation e = initialTarget W Q (kinds j) e := by
  unfold allocatedTarget
  rw [allocatedKind_eq W Q kinds allocation hdisjoint j e he]

theorem allocatedTarget_subset {k : ℕ} (kinds : Fin k → FamilyKind)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M))
    (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    allocatedTarget W Q kinds allocation e c ⊆ edgeWhole W Q e c :=
  initialTarget_subset W Q _ e c

theorem allocatedTarget_large (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    {k : ℕ} (kinds : Fin k → FamilyKind)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M))
    (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    (epsilon α : ℝ) * W.clusterSize ≤ (allocatedTarget W Q kinds allocation e c).card :=
  initialTarget_large W Q hα hα1 hhost horder _ e c

end Erdos547b.ZhaoSourceCapacityFamilyState

#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.activeRequirement_valid
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.reserved_mass_split
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.ledger_of_current
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.allocatedTarget_eq
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.allocatedTarget_large
