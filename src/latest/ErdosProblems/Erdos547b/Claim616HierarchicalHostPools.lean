/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616

/-!
# Concrete physical pools for Claim 6.16

The unified hierarchical embedding backend charges each source coordinate to
a physical host pool.  In Claim 6.16 there are exactly three kinds of pools:
the two distinguished quantitative reserves, the selected `C` clusters, and
the sides of literal edges of the original Claim-6.7 matching.

The residual matchings `M_out`, `M_1`, and `M_b` are genuine submatchings
constructed by `MatchingDecomposition`, but their edge subtypes are different.
This file canonically maps all three back to `MatchingEdge C67.M`, proves that
the maps reflect equality, and establishes the source-faithful separation of
the corresponding host candidates after deleting the two exact root reserves.
No embedding, copy, continuation, or capacity hypothesis occurs here.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalHostPools

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616

universe u v

/-! ## Retyping a selected submatching edge in its parent matching -/

/-- Every edge of `edgeFinsetSubgraph M L S` is literally an edge of `M`.
The theorem records the fact at the edge-set level, where it can be used to
change the subtype of a canonical finite index. -/
theorem edgeFinsetSubgraph_edge_mem_parent
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    {e : Sym2 K} (he : e ∈ (edgeFinsetSubgraph M L S).edgeSet) :
    e ∈ M.edgeSet := by
  have hsub : (edgeFinsetSubgraph M L S).Adj e.out.1 e.out.2 := by
    rw [← Subgraph.mem_edgeSet, e.out_eq]
    exact he
  obtain ⟨f, hf, h | h⟩ :=
    (edgeFinsetSubgraph_adj M L S).mp hsub
  · rw [← e.out_eq]
    apply (Subgraph.mem_edgeSet).2
    simpa [h.1, h.2] using orientedEndpoint_adj M L f
  · rw [← e.out_eq]
    apply (Subgraph.mem_edgeSet).2
    simpa [h.1, h.2] using (orientedEndpoint_adj M L f).symm

/-- An edge of `edgeFinsetSubgraph M L S` comes from the selected finset
`S`, with literal equality of its underlying unordered edge. -/
theorem edgeFinsetSubgraph_edge_selected_witness
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    {e : Sym2 K} (he : e ∈ (edgeFinsetSubgraph M L S).edgeSet) :
    ∃ f ∈ S, e = f.1 := by
  have hsub : (edgeFinsetSubgraph M L S).Adj e.out.1 e.out.2 := by
    rw [← Subgraph.mem_edgeSet, e.out_eq]
    exact he
  obtain ⟨f, hf, h | h⟩ :=
    (edgeFinsetSubgraph_adj M L S).mp hsub
  · refine ⟨f, hf, ?_⟩
    rw [← e.out_eq, h.1, h.2, orientedEndpoint_pair_eq]
  · refine ⟨f, hf, ?_⟩
    rw [← e.out_eq, h.1, h.2, Sym2.eq_swap,
      orientedEndpoint_pair_eq]

/-- The literal parent-matching edge represented by a canonical index of a
selected edge subgraph. -/
def originalEdgeOfSubmatchingIndex
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : Fin (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset.card) :
    MatchingEdge M :=
  ⟨finsetValue (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e,
    edgeFinsetSubgraph_edge_mem_parent M L S
      (Set.Finite.mem_toFinset.mp
        (finsetValue_mem
          (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e))⟩

@[simp] theorem originalEdgeOfSubmatchingIndex_val
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : Fin (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset.card) :
    (originalEdgeOfSubmatchingIndex M L S e).1 =
      finsetValue (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e :=
  rfl

/-- Retyping an indexed submatching edge to its parent matching loses no
information. -/
theorem originalEdgeOfSubmatchingIndex_injective
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M)) :
    Function.Injective (originalEdgeOfSubmatchingIndex M L S) := by
  intro e f hef
  apply finsetValue_injective
    (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset
  exact congrArg Subtype.val hef

/-- The retyped original edge still belongs to the selected parent-edge
finset that defined the submatching. -/
theorem originalEdgeOfSubmatchingIndex_mem
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : Fin (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset.card) :
    originalEdgeOfSubmatchingIndex M L S e ∈ S := by
  obtain ⟨f, hf, hef⟩ := edgeFinsetSubgraph_edge_selected_witness M L S
    (Set.Finite.mem_toFinset.mp
      (finsetValue_mem
        (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e))
  have heq : originalEdgeOfSubmatchingIndex M L S e = f :=
    Subtype.ext hef
  rw [heq]
  exact hf

section DecompositionEdges

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate R L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)

/-- An indexed `M_out` edge, retyped as a literal edge of `C67.M`. -/
def moutOriginalEdge
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) : MatchingEdge C67.M :=
  originalEdgeOfSubmatchingIndex C67.M L
    (allMatchingEdges C67.M \ D.minEdges) e

/-- An indexed `M_1` edge, retyped as a literal edge of `C67.M`. -/
def moneOriginalEdge (C : Finset K)
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) : MatchingEdge C67.M :=
  originalEdgeOfSubmatchingIndex C67.M L (D.MoneEdges C) e

/-- An indexed `M_b` edge, retyped as a literal edge of `C67.M`. -/
def mbOriginalEdge
    (e : Fin D.Mb.edgeSet.toFinite.toFinset.card) : MatchingEdge C67.M :=
  originalEdgeOfSubmatchingIndex C67.M L D.mbEdges e

@[simp] theorem moutOriginalEdge_val
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    (moutOriginalEdge D e).1 =
      finsetValue D.Mout.edgeSet.toFinite.toFinset e :=
  rfl

@[simp] theorem moneOriginalEdge_val (C : Finset K)
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) :
    (moneOriginalEdge D C e).1 =
      finsetValue (D.Mone C).edgeSet.toFinite.toFinset e :=
  rfl

@[simp] theorem mbOriginalEdge_val
    (e : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    (mbOriginalEdge D e).1 =
      finsetValue D.Mb.edgeSet.toFinite.toFinset e :=
  rfl

theorem moutOriginalEdge_injective : Function.Injective (moutOriginalEdge D) :=
  originalEdgeOfSubmatchingIndex_injective C67.M L
    (allMatchingEdges C67.M \ D.minEdges)

theorem moneOriginalEdge_injective (C : Finset K) :
    Function.Injective (moneOriginalEdge D C) :=
  originalEdgeOfSubmatchingIndex_injective C67.M L (D.MoneEdges C)

theorem mbOriginalEdge_injective : Function.Injective (mbOriginalEdge D) :=
  originalEdgeOfSubmatchingIndex_injective C67.M L D.mbEdges

theorem moutOriginalEdge_mem_complement
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    moutOriginalEdge D e ∈ allMatchingEdges C67.M \ D.minEdges :=
  originalEdgeOfSubmatchingIndex_mem C67.M L
    (allMatchingEdges C67.M \ D.minEdges) e

theorem moneOriginalEdge_mem_moneEdges (C : Finset K)
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) :
    moneOriginalEdge D C e ∈ D.MoneEdges C :=
  originalEdgeOfSubmatchingIndex_mem C67.M L (D.MoneEdges C) e

theorem mbOriginalEdge_mem_mbEdges
    (e : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    mbOriginalEdge D e ∈ D.mbEdges :=
  originalEdgeOfSubmatchingIndex_mem C67.M L D.mbEdges e

theorem moneOriginalEdge_ne_moutOriginalEdge (C : Finset K)
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card)
    (f : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    moneOriginalEdge D C e ≠ moutOriginalEdge D f := by
  have hin : moneOriginalEdge D C e ∈ D.minEdges :=
    (Finset.mem_sdiff.mp (moneOriginalEdge_mem_moneEdges D C e)).1
  have hout : moutOriginalEdge D f ∉ D.minEdges :=
    (Finset.mem_sdiff.mp (moutOriginalEdge_mem_complement D f)).2
  intro h
  apply hout
  simpa [h] using hin

theorem moneOriginalEdge_ne_mbOriginalEdge (C : Finset K)
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    moneOriginalEdge D C e ≠ mbOriginalEdge D f := by
  have hin : moneOriginalEdge D C e ∈ D.minEdges :=
    (Finset.mem_sdiff.mp (moneOriginalEdge_mem_moneEdges D C e)).1
  have hout : mbOriginalEdge D f ∉ D.minEdges :=
    (Finset.mem_sdiff.mp (D.mb_subset (mbOriginalEdge_mem_mbEdges D f))).2
  intro h
  apply hout
  simpa [h] using hin

end DecompositionEdges

/-! ## The concrete physical pool type -/

/-- Physical pools used by the Claim-6.16 whole-tree hierarchy.  `Fin 2`
names the exact `A₀` and `B₀` reserves, `Fin C.card` names the selected
clusters, and the last summand names a literal original matching edge. -/
/-- Public pool alias consumed by the unified Claim-6.16 constructor. -/
abbrev Claim616Pool
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    (C67 : Claim67Certificate R L miss) (C : Finset K) :=
  Sum (Fin 2) (Sum (Fin C.card) (MatchingEdge C67.M))

/-- Root slots refine a matching-edge pool by the chosen endpoint side.
The occupancy pool intentionally forgets this last `Fin 2`. -/
abbrev Claim616RootSlot
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    (C67 : Claim67Certificate R L miss) (C : Finset K) :=
  Sum (Fin 2) (Sum (Fin C.card) (MatchingEdge C67.M × Fin 2))

/-- Backward-compatible descriptive name. -/
abbrev Claim616PhysicalPool
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    (C67 : Claim67Certificate R L miss) (C : Finset K) :=
  Claim616Pool C67 C

def reservePool
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K} (q : Fin 2) :
    Claim616PhysicalPool C67 C :=
  Sum.inl q

def selectedClusterPool
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K} (i : Fin C.card) :
    Claim616PhysicalPool C67 C :=
  Sum.inr (Sum.inl i)

def originalMatchingPool
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K}
    (e : MatchingEdge C67.M) : Claim616PhysicalPool C67 C :=
  Sum.inr (Sum.inr e)

def reserveRootSlot
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K} (q : Fin 2) :
    Claim616RootSlot C67 C :=
  Sum.inl q

def selectedClusterRootSlot
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K} (i : Fin C.card) :
    Claim616RootSlot C67 C :=
  Sum.inr (Sum.inl i)

def originalMatchingRootSlot
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K}
    (e : MatchingEdge C67.M) (side : Fin 2) : Claim616RootSlot C67 C :=
  Sum.inr (Sum.inr (e, side))

/-- Forget the endpoint orientation of a root slot and retain its physical
occupancy pool. -/
def rootSlotPool
    {K : Type u} {R : SimpleGraph K} {L : Finset K} {miss : ℕ}
    {C67 : Claim67Certificate R L miss} {C : Finset K} :
    Claim616RootSlot C67 C → Claim616Pool C67 C
  | Sum.inl q => reservePool q
  | Sum.inr (Sum.inl i) => selectedClusterPool i
  | Sum.inr (Sum.inr (e, _)) => originalMatchingPool e

section DecompositionPools

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate R L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (C : Finset K)

def moutPool (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    Claim616PhysicalPool C67 C :=
  originalMatchingPool (moutOriginalEdge D e)

def monePool (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) :
    Claim616PhysicalPool C67 C :=
  originalMatchingPool (moneOriginalEdge D C e)

def mbPool (e : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    Claim616PhysicalPool C67 C :=
  originalMatchingPool (mbOriginalEdge D e)

theorem moutPool_injective : Function.Injective (moutPool D C) := by
  intro e f hef
  apply moutOriginalEdge_injective D
  simpa [moutPool, originalMatchingPool] using hef

theorem monePool_injective : Function.Injective (monePool D C) := by
  intro e f hef
  apply moneOriginalEdge_injective D C
  simpa [monePool, originalMatchingPool] using hef

theorem mbPool_injective : Function.Injective (mbPool D C) := by
  intro e f hef
  apply mbOriginalEdge_injective D
  simpa [mbPool, originalMatchingPool] using hef

theorem moutPool_eq_monePool_iff
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (f : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) :
    moutPool D C e = monePool D C f ↔
      moutOriginalEdge D e = moneOriginalEdge D C f := by
  simp [moutPool, monePool, originalMatchingPool]

theorem moutPool_eq_mbPool_iff
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    moutPool D C e = mbPool D C f ↔
      moutOriginalEdge D e = mbOriginalEdge D f := by
  simp [moutPool, mbPool, originalMatchingPool]

theorem monePool_eq_mbPool_iff
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    monePool D C e = mbPool D C f ↔
      moneOriginalEdge D C e = mbOriginalEdge D f := by
  simp [monePool, mbPool, originalMatchingPool]

theorem monePool_ne_moutPool
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card)
    (f : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    monePool D C e ≠ moutPool D C f := by
  intro h
  exact moneOriginalEdge_ne_moutOriginalEdge D C e f
    ((moutPool_eq_monePool_iff D C f e).mp h.symm).symm

theorem monePool_ne_mbPool
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    monePool D C e ≠ mbPool D C f := by
  intro h
  exact moneOriginalEdge_ne_mbOriginalEdge D C e f
    ((monePool_eq_mbPool_iff D C e f).mp h)

end DecompositionPools

/-! ## Candidate deletion and elementary separation -/

/-- Delete the two exact quantitative root reserves from a possibly
overlapping cluster or matching-side candidate. -/
def IndexedHostSystem.removeRootReserves
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) : Finset B :=
  X \ (H.rootReserve ∪ H.companionReserve)

theorem IndexedHostSystem.removeRootReserves_subset
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    H.removeRootReserves X ⊆ X :=
  Finset.sdiff_subset

theorem IndexedHostSystem.rootReserve_disjoint_removed
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    Disjoint H.rootReserve (H.removeRootReserves X) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hz)

theorem IndexedHostSystem.companionReserve_disjoint_removed
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    Disjoint H.companionReserve (H.removeRootReserves X) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_right _ hz)

/-- A selected-cluster candidate after deleting the exact root reserves. -/
def IndexedHostSystem.selectedRaw
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (i : Fin C.card) : Finset B :=
  H.removeRootReserves (indexedCluster cluster C i)

/-- A side of any canonically indexed reduced submatching after deleting the
two exact root reserves. -/
def IndexedHostSystem.submatchingRaw
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree)
    (N : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Fin N.edgeSet.toFinite.toFinset.card) (side : Fin 2) : Finset B :=
  H.removeRootReserves
    (indexedMatchingSide cluster N.edgeSet.toFinite.toFinset e side)

theorem IndexedHostSystem.selectedRaw_subset
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (i : Fin C.card) :
    H.selectedRaw i ⊆ indexedCluster cluster C i :=
  H.removeRootReserves_subset _

theorem IndexedHostSystem.submatchingRaw_subset
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {G : SimpleGraph B} [DecidableRel G.Adj]
    {cluster : I → Finset B} {epsilon density : ℚ}
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    {A Broot : I} {C : Finset I}
    {M : (regularityReducedGraph G cluster epsilon density).Subgraph}
    {W : Finset I} {rhoK : ℕ} {Pcluster : ClusterAssignment B I}
    {threshold quota : ℕ} {Gdegree : SimpleGraph B}
    [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree)
    (N : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Fin N.edgeSet.toFinite.toFinset.card) (side : Fin 2) :
    H.submatchingRaw N e side ⊆
      indexedMatchingSide cluster N.edgeSet.toFinite.toFinset e side :=
  H.removeRootReserves_subset _

/-! ## Endpoint and support facts used by all cross-class separations -/

/-- Raw endpoint occurrences of a genuine matching are injective, independently
of any choice of source orientation. -/
theorem matchingEdgeEndpoint_original_injective
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} (M : R.Subgraph) (hM : M.IsMatching) :
    Function.Injective (fun ec : MatchingEdge M × Fin 2 ↦
      matchingEdgeEndpoint ec.1.1 ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ hendpoint
  let flip : Fin 2 → Fin 2 := fun q ↦ if q = 0 then 1 else 0
  have horiented (g : MatchingEdge M) (q : Fin 2) :
      orientedEndpoint M ∅ g (flip q) = matchingEdgeEndpoint g.1 q := by
    fin_cases q <;>
      simp [flip, orientedEndpoint, rawEndpoint, matchingEdgeEndpoint]
  have hpair := orientedEndpoint_injective M hM (∅ : Finset K) (show
    orientedEndpoint M ∅ e (flip c) =
        orientedEndpoint M ∅ f (flip d) by
      simpa only [horiented] using hendpoint)
  have hedge : e = f := congrArg Prod.fst hpair
  subst f
  have hside : c = d := by
    have hflip := congrArg Prod.snd hpair
    fin_cases c <;> fin_cases d <;> simp [flip] at hflip ⊢
  subst d
  rfl

theorem indexedMatchingEndpoint_mem_support
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} (M : R.Subgraph)
    (e : Fin M.edgeSet.toFinite.toFinset.card) (side : Fin 2) :
    matchingEdgeEndpoint (finsetValue M.edgeSet.toFinite.toFinset e) side ∈
      matchingSupport M := by
  apply matchingEdgeEndpoint_mem_support M
  exact Set.Finite.mem_toFinset.mp
    (finsetValue_mem M.edgeSet.toFinite.toFinset e)

/-- Both raw endpoints of a selected original matching edge belong to the
support of its source-oriented `edgeFinsetSubgraph`. -/
theorem matchingEdgeEndpoint_mem_edgeFinsetSubgraph_support
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : MatchingEdge M) (he : e ∈ S) (side : Fin 2) :
    matchingEdgeEndpoint e.1 side ∈
      matchingSupport (edgeFinsetSubgraph M L S) := by
  rw [matchingSupport_edgeFinsetSubgraph]
  apply Finset.mem_biUnion.mpr
  refine ⟨e, he, ?_⟩
  fin_cases side <;> by_cases h : e.1.out.1 ∈ L <;>
    simp [orientedEndpoint, rawEndpoint, matchingEdgeEndpoint, h]

/-! ## Claim-6.16 decomposition specialization -/

section HostSeparation

variable {B : Type u} {I : Type v}
variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (cluster : I → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (A Broot : I) (C : Finset I) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
variable (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
variable
  (H : IndexedHostSystem G cluster epsilon density A Broot C D.Mout
    (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) rhoK
    Pcluster threshold quota Gdegree)

theorem rootReserve_disjoint_selectedRaw (i : Fin C.card) :
    Disjoint H.rootReserve (H.selectedRaw i) :=
  H.rootReserve_disjoint_removed _

theorem companionReserve_disjoint_selectedRaw (i : Fin C.card) :
    Disjoint H.companionReserve (H.selectedRaw i) :=
  H.companionReserve_disjoint_removed _

theorem rootReserve_disjoint_companionReserve :
    Disjoint H.rootReserve H.companionReserve :=
  H.distinguished_cluster_disjoint.mono
    H.rootReserve_subset H.companionReserve_subset

theorem selectedRaw_disjoint_selectedRaw_of_ne
    (i j : Fin C.card) (hij : i ≠ j) :
    Disjoint (H.selectedRaw i) (H.selectedRaw j) := by
  have hcluster : finsetValue C i ≠ finsetValue C j := by
    intro h
    exact hij (finsetValue_injective C h)
  exact (H.cluster_disjoint _ _ hcluster).mono
    H.selectedRaw_subset H.selectedRaw_subset

theorem rootReserve_disjoint_submatchingRaw
    (N : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Fin N.edgeSet.toFinite.toFinset.card) (side : Fin 2) :
    Disjoint H.rootReserve (H.submatchingRaw N e side) :=
  H.rootReserve_disjoint_removed _

theorem companionReserve_disjoint_submatchingRaw
    (N : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Fin N.edgeSet.toFinite.toFinset.card) (side : Fin 2) :
    Disjoint H.companionReserve (H.submatchingRaw N e side) :=
  H.companionReserve_disjoint_removed _

/-- A selected `C` cluster and a residual `M_1` side are distinct because
`C` is covered by `M_0`, while `M_0` and `M_1` have disjoint support. -/
theorem selectedRaw_disjoint_moneRaw
    (hCV1 : C ⊆ D.V1) (i : Fin C.card)
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) (side : Fin 2) :
    Disjoint (H.selectedRaw i) (H.submatchingRaw (D.Mone C) e side) := by
  have hx0 : finsetValue C i ∈ matchingSupport (D.Mzero C) :=
    D.C_subset_Mzero_support C hCV1 (finsetValue_mem C i)
  have hy1 : matchingEdgeEndpoint
      (finsetValue (D.Mone C).edgeSet.toFinite.toFinset e) side ∈
      matchingSupport (D.Mone C) :=
    indexedMatchingEndpoint_mem_support (D.Mone C) e side
  have hne : finsetValue C i ≠ matchingEdgeEndpoint
      (finsetValue (D.Mone C).edgeSet.toFinite.toFinset e) side := by
    intro h
    apply Finset.disjoint_left.mp (D.Mzero_Mone_support_disjoint C) hx0
    simpa [h] using hy1
  exact (H.cluster_disjoint _ _ hne).mono
    H.selectedRaw_subset (H.submatchingRaw_subset (D.Mone C) e side)

/-- The indexed access matching is already disjoint from every selected `C`
cluster in `IndexedHostSystem`. -/
theorem selectedRaw_disjoint_moutRaw
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (side : Fin 2) :
    Disjoint (H.selectedRaw i) (H.submatchingRaw D.Mout e side) := by
  apply (H.cluster_matching_disjoint i e).mono H.selectedRaw_subset
  apply (H.submatchingRaw_subset D.Mout e side).trans
  fin_cases side
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

/-- `M_b` is contained in `M_out`, so its sides are disjoint from selected
`C ⊆ V(M_0)` clusters. -/
theorem selectedRaw_disjoint_mbRaw
    (hCV1 : C ⊆ D.V1) (i : Fin C.card)
    (e : Fin D.Mb.edgeSet.toFinite.toFinset.card) (side : Fin 2) :
    Disjoint (H.selectedRaw i) (H.submatchingRaw D.Mb e side) := by
  have hx0 : finsetValue C i ∈ matchingSupport (D.Mzero C) :=
    D.C_subset_Mzero_support C hCV1 (finsetValue_mem C i)
  have hyb : matchingEdgeEndpoint
      (finsetValue D.Mb.edgeSet.toFinite.toFinset e) side ∈
      matchingSupport D.Mb :=
    indexedMatchingEndpoint_mem_support D.Mb e side
  have hne : finsetValue C i ≠ matchingEdgeEndpoint
      (finsetValue D.Mb.edgeSet.toFinite.toFinset e) side := by
    intro h
    apply Finset.disjoint_left.mp (D.Mzero_Mout_support_disjoint C) hx0
    apply D.Mb_support_subset_Mout
    simpa [h] using hyb
  exact (H.cluster_disjoint _ _ hne).mono
    H.selectedRaw_subset (H.submatchingRaw_subset D.Mb e side)

/-- Residual `M_1` and access `M_out` sides lie in the disjoint `V_1` and
`V_2` supports of the matching decomposition. -/
theorem moneRaw_disjoint_moutRaw
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) (side : Fin 2)
    (f : Fin D.Mout.edgeSet.toFinite.toFinset.card) (other : Fin 2) :
    Disjoint (H.submatchingRaw (D.Mone C) e side)
      (H.submatchingRaw D.Mout f other) := by
  have hx : matchingEdgeEndpoint
      (finsetValue (D.Mone C).edgeSet.toFinite.toFinset e) side ∈
      matchingSupport (D.Mone C) :=
    indexedMatchingEndpoint_mem_support (D.Mone C) e side
  have hy : matchingEdgeEndpoint
      (finsetValue D.Mout.edgeSet.toFinite.toFinset f) other ∈
      matchingSupport D.Mout :=
    indexedMatchingEndpoint_mem_support D.Mout f other
  have hne : matchingEdgeEndpoint
      (finsetValue (D.Mone C).edgeSet.toFinite.toFinset e) side ≠
      matchingEdgeEndpoint
        (finsetValue D.Mout.edgeSet.toFinite.toFinset f) other := by
    intro h
    apply Finset.disjoint_left.mp (D.Mone_Mout_support_disjoint C) hx
    simpa [h] using hy
  exact (H.cluster_disjoint _ _ hne).mono
    (H.submatchingRaw_subset (D.Mone C) e side)
    (H.submatchingRaw_subset D.Mout f other)

/-- `M_1` is also disjoint from the optional `M_b ⊆ M_out`. -/
theorem moneRaw_disjoint_mbRaw
    (e : Fin (D.Mone C).edgeSet.toFinite.toFinset.card) (side : Fin 2)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) (other : Fin 2) :
    Disjoint (H.submatchingRaw (D.Mone C) e side)
      (H.submatchingRaw D.Mb f other) := by
  have hx : matchingEdgeEndpoint
      (finsetValue (D.Mone C).edgeSet.toFinite.toFinset e) side ∈
      matchingSupport (D.Mone C) :=
    indexedMatchingEndpoint_mem_support (D.Mone C) e side
  have hy : matchingEdgeEndpoint
      (finsetValue D.Mb.edgeSet.toFinite.toFinset f) other ∈
      matchingSupport D.Mb :=
    indexedMatchingEndpoint_mem_support D.Mb f other
  have hne : matchingEdgeEndpoint
      (finsetValue (D.Mone C).edgeSet.toFinite.toFinset e) side ≠
      matchingEdgeEndpoint
        (finsetValue D.Mb.edgeSet.toFinite.toFinset f) other := by
    intro h
    apply Finset.disjoint_left.mp (D.Mone_Mout_support_disjoint C) hx
    apply D.Mb_support_subset_Mout
    simpa [h] using hy
  exact (H.cluster_disjoint _ _ hne).mono
    (H.submatchingRaw_subset (D.Mone C) e side)
    (H.submatchingRaw_subset D.Mb f other)

/-- Candidates belonging to distinct literal original matching edges are
disjoint, even when the edges came from differently typed submatchings. -/
theorem submatchingRaw_disjoint_of_originalEdge_ne
    (N P : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Fin N.edgeSet.toFinite.toFinset.card) (side : Fin 2)
    (f : Fin P.edgeSet.toFinite.toFinset.card) (other : Fin 2)
    (e0 : MatchingEdge C67.M) (f0 : MatchingEdge C67.M)
    (heval : e0.1 = finsetValue N.edgeSet.toFinite.toFinset e)
    (hfval : f0.1 = finsetValue P.edgeSet.toFinite.toFinset f)
    (hef : e0 ≠ f0) :
    Disjoint (H.submatchingRaw N e side) (H.submatchingRaw P f other) := by
  have hne0 : matchingEdgeEndpoint e0.1 side ≠
      matchingEdgeEndpoint f0.1 other := by
    intro h
    have hp := matchingEdgeEndpoint_original_injective C67.M C67.isMatching h
    exact hef (congrArg Prod.fst hp)
  have hne : matchingEdgeEndpoint
      (finsetValue N.edgeSet.toFinite.toFinset e) side ≠
      matchingEdgeEndpoint
        (finsetValue P.edgeSet.toFinite.toFinset f) other := by
    simpa only [← heval, ← hfval] using hne0
  exact (H.cluster_disjoint _ _ hne).mono
    (H.submatchingRaw_subset N e side)
    (H.submatchingRaw_subset P f other)

theorem moutRaw_disjoint_mbRaw_of_originalEdge_ne
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) (side : Fin 2)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) (other : Fin 2)
    (hef : moutOriginalEdge D e ≠ mbOriginalEdge D f) :
    Disjoint (H.submatchingRaw D.Mout e side)
      (H.submatchingRaw D.Mb f other) :=
  submatchingRaw_disjoint_of_originalEdge_ne
    (G := G) (cluster := cluster) (epsilon := epsilon) (density := density)
    (D := D) (A := A) (Broot := Broot) (C := C) (rhoK := rhoK)
    (Pcluster := Pcluster) (threshold := threshold) (quota := quota)
    (Gdegree := Gdegree) (H := H) D.Mout D.Mb e side f other
    (moutOriginalEdge D e) (mbOriginalEdge D f) rfl rfl hef

/-! The source allocation uses only `M_out` edges whose displayed endpoint
lies in `W = V_2 ∩ (V(M_out) \ V(M_b))`.  Such an edge cannot be one of the
reserved `M_b` edges. -/
theorem moutOriginalEdge_not_mem_mbEdges_of_indexedAllowed
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i) :
    moutOriginalEdge D e ∉ D.mbEdges := by
  let side := indexedAccessSide
    (regularityReducedGraph G cluster epsilon density)
    D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
    (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e
  have hspec := indexedAccessSide_spec
    (regularityReducedGraph G cluster epsilon density)
    D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
    (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i e he
  have hyW :
      (if side = 0 then
          matchingEdgeEndpoint (finsetValue D.Mout.edgeSet.toFinite.toFinset e) 1
        else
          matchingEdgeEndpoint (finsetValue D.Mout.edgeSet.toFinite.toFinset e) 0)
        ∈ D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb) := by
    simpa [side] using hspec.1
  have hyNotMb :
      (if side = 0 then
          matchingEdgeEndpoint (finsetValue D.Mout.edgeSet.toFinite.toFinset e) 1
        else
          matchingEdgeEndpoint (finsetValue D.Mout.edgeSet.toFinite.toFinset e) 0)
        ∉ matchingSupport D.Mb :=
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp hyW).2).2
  intro heMb
  fin_cases side
  · apply hyNotMb
    simpa using
      matchingEdgeEndpoint_mem_edgeFinsetSubgraph_support C67.M L D.mbEdges
        (moutOriginalEdge D e) heMb 1
  · apply hyNotMb
    simpa using
      matchingEdgeEndpoint_mem_edgeFinsetSubgraph_support C67.M L D.mbEdges
        (moutOriginalEdge D e) heMb 0

theorem moutOriginalEdge_ne_mbOriginalEdge_of_indexedAllowed
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    moutOriginalEdge D e ≠ mbOriginalEdge D f := by
  intro hef
  apply moutOriginalEdge_not_mem_mbEdges_of_indexedAllowed
    (G := G) (cluster := cluster) (epsilon := epsilon) (density := density)
      (D := D) (C := C) i e he
  rw [hef]
  exact mbOriginalEdge_mem_mbEdges D f

theorem moutPool_ne_mbPool_of_indexedAllowed
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i)
    (f : Fin D.Mb.edgeSet.toFinite.toFinset.card) :
    moutPool D C e ≠ mbPool D C f := by
  intro h
  exact moutOriginalEdge_ne_mbOriginalEdge_of_indexedAllowed
    (G := G) (cluster := cluster) (epsilon := epsilon) (density := density)
      (D := D) (C := C) i e he f
    ((moutPool_eq_mbPool_iff D C e f).mp h)

theorem moutRaw_disjoint_mbRaw_of_indexedAllowed
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C
      (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) i)
    (side : Fin 2) (f : Fin D.Mb.edgeSet.toFinite.toFinset.card)
    (other : Fin 2) :
    Disjoint (H.submatchingRaw D.Mout e side)
      (H.submatchingRaw D.Mb f other) :=
  moutRaw_disjoint_mbRaw_of_originalEdge_ne
    (G := G) (cluster := cluster) (epsilon := epsilon) (density := density)
    (D := D) (A := A) (Broot := Broot) (C := C) (rhoK := rhoK)
    (Pcluster := Pcluster) (threshold := threshold) (quota := quota)
    (Gdegree := Gdegree) (H := H) e side f other
    (moutOriginalEdge_ne_mbOriginalEdge_of_indexedAllowed
      (G := G) (cluster := cluster) (epsilon := epsilon) (density := density)
        (D := D) (C := C) i e he f)

end HostSeparation

end Erdos547b.ZhaoClaim616HierarchicalHostPools

#print axioms Erdos547b.ZhaoClaim616HierarchicalHostPools.originalEdgeOfSubmatchingIndex_injective
#print axioms Erdos547b.ZhaoClaim616HierarchicalHostPools.moutOriginalEdge_injective
#print axioms Erdos547b.ZhaoClaim616HierarchicalHostPools.selectedRaw_disjoint_moneRaw
#print axioms Erdos547b.ZhaoClaim616HierarchicalHostPools.moneRaw_disjoint_moutRaw
#print axioms Erdos547b.ZhaoClaim616HierarchicalHostPools.moutRaw_disjoint_mbRaw_of_indexedAllowed
