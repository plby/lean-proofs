/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicApplication
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Distinguished root reservoirs for dynamic Zhao Claim 6.15

Component roots are placed in the two quantitative reserves `A₀,B₀`
according to their tree-distance parity.  This file supplies the literal
whole/raw root reservoirs, their cardinalities and separation from every
matching endpoint, and the reduced-pair fact between opposite root sides.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicRootLayout

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)

/-- Whole distinguished cluster on one parity side. -/
def rootWholeSide (side : Fin 2) : Finset Bv :=
  clusterVertices Pcluster (if side = 0 then Q.A else Q.B)

/-- Quantitative root reserve on one parity side. -/
def rootRawSide (side : Fin 2) : Finset Bv :=
  if side = 0 then Q.A₀ else Q.B₀

theorem rootRawSide_subset (side : Fin 2) :
    rootRawSide Pcluster Gdegree threshold quota R miss Q side ⊆
      rootWholeSide Pcluster Gdegree threshold quota R miss Q side := by
  fin_cases side
  · simpa [rootRawSide, rootWholeSide] using Q.A₀_subset
  · simpa [rootRawSide, rootWholeSide] using Q.B₀_subset

@[simp] theorem card_rootRawSide (side : Fin 2) :
    #(rootRawSide Pcluster Gdegree threshold quota R miss Q side) = quota := by
  fin_cases side
  · simpa [rootRawSide] using Q.A₀_card
  · simpa [rootRawSide] using Q.B₀_card

theorem rootRawSide_disjoint_of_ne (s t : Fin 2) (hst : s ≠ t) :
    Disjoint (rootRawSide Pcluster Gdegree threshold quota R miss Q s)
      (rootRawSide Pcluster Gdegree threshold quota R miss Q t) := by
  fin_cases s <;> fin_cases t
  · exact False.elim (hst rfl)
  · exact (Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools.A₀_disjoint_B₀
      Pcluster Gdegree threshold quota R miss Q)
  · exact (Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools.A₀_disjoint_B₀
      Pcluster Gdegree threshold quota R miss Q).symm
  · exact False.elim (hst rfl)

section Physical

variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)
variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

/-- Every root reserve is disjoint from every permanently available
matching endpoint because both reserves were deleted there. -/
theorem rootRawSide_disjoint_endpoint
    (side : Fin 2) (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    Disjoint (rootRawSide Pcluster Gdegree threshold quota R miss Q side)
      (endpoint (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        e c) := by
  rw [Finset.disjoint_left]
  intro z hzRoot hzEndpoint
  have hzUnion : z ∈ Q.A₀ ∪ Q.B₀ := by
    fin_cases side
    · exact Finset.mem_union_left _ (by simpa [rootRawSide] using hzRoot)
    · exact Finset.mem_union_right _ (by simpa [rootRawSide] using hzRoot)
  exact (Finset.mem_sdiff.mp hzEndpoint).2 hzUnion

end Physical

variable (P : ZhaoForestPartition T globalRoot small)

/-- Whole cluster assigned to a literal partition root. -/
def rootWhole (q : Fin P.numParts) : Finset Bv :=
  rootWholeSide Pcluster Gdegree threshold quota R miss Q
    (componentReservoirSide P q)

/-- Quantitative reserve assigned to a literal partition root. -/
def rootRaw (q : Fin P.numParts) : Finset Bv :=
  rootRawSide Pcluster Gdegree threshold quota R miss Q
    (componentReservoirSide P q)

theorem rootRaw_subset (q : Fin P.numParts) :
    rootRaw Pcluster Gdegree threshold quota R miss Q P q ⊆
      rootWhole Pcluster Gdegree threshold quota R miss Q P q :=
  rootRawSide_subset Pcluster Gdegree threshold quota R miss Q _

@[simp] theorem card_rootRaw (q : Fin P.numParts) :
    #(rootRaw Pcluster Gdegree threshold quota R miss Q P q) = quota :=
  card_rootRawSide Pcluster Gdegree threshold quota R miss Q _

/-- Adjacent component roots have opposite reservoir sides. -/
theorem componentReservoirSide_ne_of_adj
    (hT : T.IsTree) (q r : Fin P.numParts)
    (hqr : T.Adj (P.roots q) (P.roots r)) :
    componentReservoirSide P q ≠ componentReservoirSide P r := by
  have hparity := TreePartition.rootParity_ne_of_adj hT globalRoot hqr
  unfold componentReservoirSide
  by_cases hq : T.dist globalRoot (P.roots q) % 2 = (majorParity P).val
  · by_cases hr : T.dist globalRoot (P.roots r) % 2 = (majorParity P).val
    · exact False.elim (hparity (hq.trans hr.symm))
    · simp [hq, hr]
  · by_cases hr : T.dist globalRoot (P.roots r) % 2 = (majorParity P).val
    · simp [hq, hr]
    · have hqLt := Nat.mod_lt (T.dist globalRoot (P.roots q))
          (by omega : 0 < 2)
      have hrLt := Nat.mod_lt (T.dist globalRoot (P.roots r))
          (by omega : 0 < 2)
      have hmLt := (majorParity P).isLt
      have hsame : T.dist globalRoot (P.roots q) % 2 =
          T.dist globalRoot (P.roots r) % 2 := by omega
      exact False.elim (hparity hsame)

/-- A root/root cut link therefore uses opposite root reservoirs. -/
theorem componentReservoirSide_ne_of_cutRoot
    (hT : T.IsTree) (j : Fin P.numParts) (hj : j.val ≠ 0)
    (hroot : P.parent j hj = P.roots (P.parentPart j hj)) :
    componentReservoirSide P (P.parentPart j hj) ≠
      componentReservoirSide P j := by
  apply componentReservoirSide_ne_of_adj (P := P) hT
  have hadj := (P.cut_adj j hj).symm
  simpa only [hroot] using hadj

/-- Opposite root sides form the distinguished regular pair. -/
theorem rootWholeSide_pair_of_ne
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (s t : Fin 2) (hst : s ≠ t) :
    G.IsUniform rho
        (rootWholeSide Pcluster Gdegree threshold quota R miss Q s)
        (rootWholeSide Pcluster Gdegree threshold quota R miss Q t) ∧
      density ≤ G.edgeDensity
        (rootWholeSide Pcluster Gdegree threshold quota R miss Q s)
        (rootWholeSide Pcluster Gdegree threshold quota R miss Q t) := by
  fin_cases s <;> fin_cases t
  · exact False.elim (hst rfl)
  · have hadj : (padGraph R).Adj (Sum.inl Q.A) (Sum.inl Q.B) := by
      simpa using Q.adj
    simpa [rootWholeSide, padCluster] using
      H.pair_of_adj (Sum.inl Q.A) (Sum.inl Q.B) hadj
  · have hadj : (padGraph R).Adj (Sum.inl Q.B) (Sum.inl Q.A) := by
      simpa using Q.adj.symm
    simpa [rootWholeSide, padCluster] using
      H.pair_of_adj (Sum.inl Q.B) (Sum.inl Q.A) hadj
  · exact False.elim (hst rfl)

end Erdos547b.ZhaoClaim615RichDynamicRootLayout

#print axioms Erdos547b.ZhaoClaim615RichDynamicRootLayout.rootRawSide_disjoint_endpoint
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootLayout.componentReservoirSide_ne_of_cutRoot
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootLayout.rootWholeSide_pair_of_ne
