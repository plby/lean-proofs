/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalEdgeFamilies

/-!
# One indexed physical matching for Zhao Claim 6.15

The source construction naturally produces three finite edge families:
the exceptional family `K₀`, the positive remaining `A`-family `K₁`, and
the reserved `B`-family `K_b`.  The dynamic Lemma-5.8 backend instead uses
one index `Fin k`.  This file forms the disjoint sum of the three families,
reindexes it by `Fin`, and records the exact normalization on each source
branch class.

There is no host embedding, copy, or capacity premise in this module.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalMatching

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R : SimpleGraph I} [DecidableRel R.Adj]
variable {miss : ℕ}
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)

variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

/-- The disjoint tagged union of the three physical edge families. -/
abbrev PhysicalEdge := Sum (K0 Q sourceDensity E0)
  (Sum (K1 Q sourceDensity E0 Mb) (Kb Q sourceDensity Mb))

/-- Forget the source-family tag and retain the literal matching edge. -/
def physicalEdge : PhysicalEdge Q sourceDensity E0 Mb →
    MatchingEdge Q.claim67.M
  | Sum.inl e => edge0 Q sourceDensity E0 e
  | Sum.inr (Sum.inl e) => edge1 Q sourceDensity E0 Mb e
  | Sum.inr (Sum.inr e) => edgeb Q sourceDensity Mb e

/-- The source-facing endpoint of a tagged physical edge. -/
def physicalRootSide : PhysicalEdge Q sourceDensity E0 Mb → Fin 2
  | Sum.inl e => rootSide0 Q sourceDensity E0 e
  | Sum.inr (Sum.inl e) => rootSide1 Q sourceDensity E0 Mb e
  | Sum.inr (Sum.inr e) => rootSideb Q sourceDensity Mb e

/-- The family tags are genuine: after forgetting them, the physical edges
remain pairwise distinct. -/
theorem physicalEdge_injective
    (hdisjoint : Disjoint E0.selected Mb.selected) :
    Function.Injective (physicalEdge Q sourceDensity E0 Mb) := by
  intro e f hef
  rcases e with e | e
  · rcases f with f | f
    · exact congrArg Sum.inl
        (edge0_injective Q sourceDensity E0 hef)
    · rcases f with f | f
      · exact False.elim
          ((edge1_ne_edge0 Q sourceDensity E0 Mb f e) hef.symm)
      · exact False.elim
          ((edge0_ne_edgeb Q sourceDensity E0 Mb hdisjoint e f) hef)
  · rcases e with e | e
    · rcases f with f | f
      · exact False.elim
          ((edge1_ne_edge0 Q sourceDensity E0 Mb e f) hef)
      · rcases f with f | f
        · exact congrArg (fun z => Sum.inr (Sum.inl z))
            (edge1_injective Q sourceDensity E0 Mb hef)
        · exact False.elim
            ((edge1_ne_edgeb Q sourceDensity E0 Mb e f) hef)
    · rcases f with f | f
      · exact False.elim
          ((edge0_ne_edgeb Q sourceDensity E0 Mb hdisjoint f e) hef.symm)
      · rcases f with f | f
        · exact False.elim
            ((edge1_ne_edgeb Q sourceDensity E0 Mb f e) hef.symm)
        · exact congrArg (fun z => Sum.inr (Sum.inr z))
            (edgeb_injective Q sourceDensity Mb hef)

/-- Canonical finite index type consumed by the dynamic matching backend. -/
abbrev PhysicalIndex := Fin (Fintype.card
  (PhysicalEdge Q sourceDensity E0 Mb))

/-- Literal matching edge at a canonical physical index. -/
def indexedPhysicalEdge (e : PhysicalIndex Q sourceDensity E0 Mb) :
    MatchingEdge Q.claim67.M :=
  physicalEdge Q sourceDensity E0 Mb
    ((Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).symm e)

/-- Source-facing endpoint at a canonical physical index. -/
def indexedRootSide (e : PhysicalIndex Q sourceDensity E0 Mb) : Fin 2 :=
  physicalRootSide Q sourceDensity E0 Mb
    ((Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).symm e)

theorem indexedPhysicalEdge_injective
    (hdisjoint : Disjoint E0.selected Mb.selected) :
    Function.Injective (indexedPhysicalEdge Q sourceDensity E0 Mb) :=
  (physicalEdge_injective Q sourceDensity E0 Mb hdisjoint).comp
    (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).symm.injective

section Allocation

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Tagged physical edge receiving one canonical branch. -/
def assignedPhysicalEdge
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    PhysicalEdge Q sourceDensity E0 Mb :=
  if _hj0 : j ∈ S.selected then Sum.inl (A.F0edge j)
  else if _hj1 : j ∈ majorResidualBranches P S then
    Sum.inr (Sum.inl (A.F1edge j))
  else Sum.inr (Sum.inr (A.Fbedge j))

/-- Canonical `Fin`-valued assignment used by matching-fiber assembly. -/
def assignedPhysicalIndex
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    PhysicalIndex Q sourceDensity E0 Mb :=
  Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)
    (assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j)

/-- Canonical indices of the three tagged source families. -/
def exceptionalIndex (e : K0 Q sourceDensity E0) :
    PhysicalIndex Q sourceDensity E0 Mb :=
  Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) (Sum.inl e)

def remainingIndex (e : K1 Q sourceDensity E0 Mb) :
    PhysicalIndex Q sourceDensity E0 Mb :=
  Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)
    (Sum.inr (Sum.inl e))

def reservedIndex (e : Kb Q sourceDensity Mb) :
    PhysicalIndex Q sourceDensity E0 Mb :=
  Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)
    (Sum.inr (Sum.inr e))

@[simp] theorem assignedPhysicalEdge_selected
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) :
    assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
      Sum.inl (A.F0edge j) := by
  simp [assignedPhysicalEdge, hj]

@[simp] theorem assignedPhysicalEdge_residual
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) :
    assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
      Sum.inr (Sum.inl (A.F1edge j)) := by
  have hj0 : j ∉ S.selected :=
    (mem_majorResidualBranches P S j).mp hj |>.2
  simp [assignedPhysicalEdge, hj0, hj]

@[simp] theorem assignedPhysicalEdge_minor
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) :
    assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
      Sum.inr (Sum.inr (A.Fbedge j)) := by
  have hjHalf : j ∉ halfBranches P := by
    intro hj'
    exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
      hj' hj
  have hj0 : j ∉ S.selected := fun hj' =>
    hjHalf (havailable (S.selected_available hj'))
  have hj1 : j ∉ majorResidualBranches P S := by
    intro hj'
    exact hjHalf ((mem_majorResidualBranches P S j).mp hj').1
  simp [assignedPhysicalEdge, hj0, hj1]

/-- Exact inverse classification of an exceptional matching fiber. -/
theorem assignedPhysicalEdge_eq_exceptional_iff
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (e : K0 Q sourceDensity E0) :
    assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
        Sum.inl e ↔
      j ∈ S.selected ∧ A.F0edge j = e := by
  constructor
  · intro h
    by_cases hj : j ∈ S.selected
    · refine ⟨hj, ?_⟩
      have h' : Sum.inl (A.F0edge j) =
          (Sum.inl e : PhysicalEdge Q sourceDensity E0 Mb) := by
        simpa only [assignedPhysicalEdge_selected
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) j hj] using h
      exact Sum.inl.inj h'
    · simp [assignedPhysicalEdge, hj] at h
      split at h <;> cases h
  · rintro ⟨hj, rfl⟩
    exact assignedPhysicalEdge_selected
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j hj

/-- Exact inverse classification of a positive remaining `A`-fiber. -/
theorem assignedPhysicalEdge_eq_remaining_iff
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (e : K1 Q sourceDensity E0 Mb) :
    assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
        Sum.inr (Sum.inl e) ↔
      j ∈ majorResidualBranches P S ∧ A.F1edge j = e := by
  constructor
  · intro h
    have hj0 : j ∉ S.selected := by
      intro hj
      rw [assignedPhysicalEdge_selected
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j hj] at h
      cases h
    by_cases hj1 : j ∈ majorResidualBranches P S
    · refine ⟨hj1, ?_⟩
      have h' : Sum.inr (Sum.inl (A.F1edge j)) =
          (Sum.inr (Sum.inl e) : PhysicalEdge Q sourceDensity E0 Mb) := by
        simpa only [assignedPhysicalEdge_residual
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) j hj1] using h
      exact Sum.inl.inj (Sum.inr.inj h')
    · simp [assignedPhysicalEdge, hj0, hj1] at h
  · rintro ⟨hj, rfl⟩
    exact assignedPhysicalEdge_residual
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j hj

/-- Exact inverse classification of a reserved `B`-fiber. -/
theorem assignedPhysicalEdge_eq_reserved_iff
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (e : Kb Q sourceDensity Mb) :
    assignedPhysicalEdge (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
        Sum.inr (Sum.inr e) ↔
      j ∈ minorBranches P ∧ A.Fbedge j = e := by
  constructor
  · intro h
    have hj0 : j ∉ S.selected := by
      intro hj
      rw [assignedPhysicalEdge_selected
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j hj] at h
      cases h
    have hj1 : j ∉ majorResidualBranches P S := by
      intro hj
      rw [assignedPhysicalEdge_residual
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j hj] at h
      cases h
    have hjHalf : j ∉ halfBranches P := by
      intro hj
      exact hj1 ((mem_majorResidualBranches P S j).mpr ⟨hj, hj0⟩)
    have hjMinor : j ∈ minorBranches P := by
      have hu : j ∈ halfBranches P ∪ minorBranches P := by
        rw [halfBranches_union_minorBranches]
        exact Finset.mem_univ _
      exact (Finset.mem_union.mp hu).resolve_left hjHalf
    refine ⟨hjMinor, ?_⟩
    have h' : Sum.inr (Sum.inr (A.Fbedge j)) =
        (Sum.inr (Sum.inr e) : PhysicalEdge Q sourceDensity E0 Mb) := by
      simpa only [assignedPhysicalEdge_minor
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) havailable j hjMinor] using h
    exact Sum.inr.inj (Sum.inr.inj h')
  · rintro ⟨hj, rfl⟩
    exact assignedPhysicalEdge_minor
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) havailable j hj

theorem assignedPhysicalIndex_eq_exceptional_iff
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (e : K0 Q sourceDensity E0) :
    assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
        exceptionalIndex Q sourceDensity E0 Mb e ↔
      j ∈ S.selected ∧ A.F0edge j = e := by
  rw [← assignedPhysicalEdge_eq_exceptional_iff
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) j e]
  exact (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).injective.eq_iff

theorem assignedPhysicalIndex_eq_remaining_iff
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (e : K1 Q sourceDensity E0 Mb) :
    assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
        remainingIndex Q sourceDensity E0 Mb e ↔
      j ∈ majorResidualBranches P S ∧ A.F1edge j = e := by
  rw [← assignedPhysicalEdge_eq_remaining_iff
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) j e]
  exact (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).injective.eq_iff

theorem assignedPhysicalIndex_eq_reserved_iff
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (e : Kb Q sourceDensity Mb) :
    assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j =
        reservedIndex Q sourceDensity E0 Mb e ↔
      j ∈ minorBranches P ∧ A.Fbedge j = e := by
  rw [← assignedPhysicalEdge_eq_reserved_iff
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) havailable j e]
  exact (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).injective.eq_iff

@[simp] theorem indexedPhysicalEdge_assigned_selected
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) :
    indexedPhysicalEdge Q sourceDensity E0 Mb
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j) =
      edge0 Q sourceDensity E0 (A.F0edge j) := by
  simp [indexedPhysicalEdge, assignedPhysicalIndex,
    assignedPhysicalEdge_selected (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j hj,
    physicalEdge]

@[simp] theorem indexedPhysicalEdge_assigned_residual
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) :
    indexedPhysicalEdge Q sourceDensity E0 Mb
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j) =
      edge1 Q sourceDensity E0 Mb (A.F1edge j) := by
  simp [indexedPhysicalEdge, assignedPhysicalIndex,
    assignedPhysicalEdge_residual (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j hj,
    physicalEdge]

@[simp] theorem indexedPhysicalEdge_assigned_minor
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) :
    indexedPhysicalEdge Q sourceDensity E0 Mb
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j) =
      edgeb Q sourceDensity Mb (A.Fbedge j) := by
  simp [indexedPhysicalEdge, assignedPhysicalIndex,
    assignedPhysicalEdge_minor (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)
      havailable j hj,
    physicalEdge]

@[simp] theorem indexedRootSide_assigned_selected
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) :
    indexedRootSide Q sourceDensity E0 Mb
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j) =
      rootSide0 Q sourceDensity E0 (A.F0edge j) := by
  simp [indexedRootSide, assignedPhysicalIndex,
    assignedPhysicalEdge_selected (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j hj,
    physicalRootSide]

@[simp] theorem indexedRootSide_assigned_residual
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) :
    indexedRootSide Q sourceDensity E0 Mb
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j) =
      rootSide1 Q sourceDensity E0 Mb (A.F1edge j) := by
  simp [indexedRootSide, assignedPhysicalIndex,
    assignedPhysicalEdge_residual (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j hj,
    physicalRootSide]

@[simp] theorem indexedRootSide_assigned_minor
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) :
    indexedRootSide Q sourceDensity E0 Mb
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) j) =
      rootSideb Q sourceDensity Mb (A.Fbedge j) := by
  simp [indexedRootSide, assignedPhysicalIndex,
    assignedPhysicalEdge_minor (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)
      havailable j hj,
    physicalRootSide]

end Allocation

end Erdos547b.ZhaoClaim615RichPhysicalMatching

#print axioms Erdos547b.ZhaoClaim615RichPhysicalMatching.physicalEdge_injective
#print axioms Erdos547b.ZhaoClaim615RichPhysicalMatching.indexedPhysicalEdge_injective
#print axioms Erdos547b.ZhaoClaim615RichPhysicalMatching.indexedPhysicalEdge_assigned_selected
#print axioms Erdos547b.ZhaoClaim615RichPhysicalMatching.indexedPhysicalEdge_assigned_residual
#print axioms Erdos547b.ZhaoClaim615RichPhysicalMatching.indexedPhysicalEdge_assigned_minor
