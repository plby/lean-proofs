/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 570.
https://www.erdosproblems.com/forum/thread/570

Informal authors:
- Paul Erdős
- Ralph Faudree
- Cecil Rousseau
- Richard Schelp
- Wayne Goddard
- Daniel Kleitman
- Alexander Sidorenko
- C. J. Jayawardene
- Stijn Cambie
- Alberto Freschi
- Piotr Morawski
- K. Petrova
- Alexey Pokrovskiy

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos570.md
-/
import ErdosProblems.Erdos79.Core
import ErdosProblems.Erdos570.CycleCode
import ErdosProblems.Erdos570.BondyChvatal
import ErdosProblems.Erdos570.DisjointUnion
import ErdosProblems.Erdos570.Support
import ErdosProblems.Erdos570.Join
import ErdosProblems.Erdos570.Averaging
import ErdosProblems.Erdos570.Neighborhood
import ErdosProblems.Erdos570.RamseyRegion
import ErdosProblems.Erdos570.Coloring
import ErdosProblems.Erdos570.EmbeddingNeighborhood
import ErdosProblems.Erdos570.OddArithmetic
import ErdosProblems.Erdos570.OddInduction
import ErdosProblems.Erdos570.OddNeighborhoodInduction
import ErdosProblems.Erdos570.OddScale
import ErdosProblems.Erdos570.CycleCliqueDense
import ErdosProblems.Erdos570.SparseLeaf
import ErdosProblems.Erdos570.EvenSparseLeaf
import ErdosProblems.Erdos570.C4Vertex
import ErdosProblems.Erdos570.TriangleContraction
import ErdosProblems.Erdos570.TriangleIndependentTwo
import ErdosProblems.Erdos570.TriangleLeaf
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Erdős Problem 570

For every `k ≥ 3`, and every sufficiently large edge count `m`, every finite simple
graph `H` with `m` edges and no isolated vertices satisfies

`R(Cₖ, H) ≤ 2m + ⌊(k - 1) / 2⌋`.

Finite graphs and graph Ramsey numbers use the representation-independent foundations
from `ErdosProblems.Erdos79.Core`.  In particular, containment is ordinary (not
necessarily induced) containment, and the blue graph of a red graph `G` is `Gᶜ`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- A cycle of length at least three has exactly as many edges as vertices. -/
theorem cycleCode_edgeCount {k : ℕ} (hk : 3 ≤ k) :
    (cycleCode k).edgeCount = k := by
  let : DecidableRel (cycleCode k).graph.Adj :=
    SimpleGraph.instDecidableRelFinAdjCycleGraph k
  rw [GraphCode.edgeCount_eq_card_edgeFinset]
  change (SimpleGraph.cycleGraph k).edgeFinset.card = k
  have hdeg : ∀ v : Fin k, (SimpleGraph.cycleGraph k).degree v = 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    exact fun v ↦ SimpleGraph.cycleGraph_degree_three_le (n := n) (v := v)
  have hsum := (SimpleGraph.cycleGraph k).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hsum
  have htwo : 2 * k = 2 * (SimpleGraph.cycleGraph k).edgeFinset.card := by
    simpa [mul_comm] using hsum
  omega

/-- A cycle of length at least three has no isolated vertices. -/
theorem cycleCode_noIsolated {k : ℕ} (hk : 3 ≤ k) :
    NoIsolated (cycleCode k) := by
  classical
  change ∀ v : Fin k, ¬(SimpleGraph.cycleGraph k).IsIsolated v
  intro v
  rw [← (SimpleGraph.cycleGraph k).degree_pos v]
  have hdeg : (SimpleGraph.cycleGraph k).degree v = 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  omega

/-- `C₃` is the complete graph on three vertices. -/
theorem cycleCode_three_eq_completeCode :
    cycleCode 3 = completeCode 3 := by
  simp [cycleCode, completeCode, SimpleGraph.cycleGraph_three_eq_top]

/-- The canonical graph consisting of `m` pairwise disjoint edges.  The first
and second copies of `Fin m` are paired coordinatewise. -/
def matchingGraph (m : ℕ) : SimpleGraph (Fin (m + m)) :=
  SimpleGraph.fromRel fun u v ↦
    ∃ i : Fin m, u = Fin.castAdd m i ∧ v = Fin.natAdd m i

/-- The canonical coded matching with `m` edges. -/
def matchingCode (m : ℕ) : GraphCode := ⟨m + m, matchingGraph m⟩

theorem matchingGraph_adj_iff {m : ℕ} {u v : Fin (m + m)} :
    (matchingGraph m).Adj u v ↔
      (∃ i : Fin m, u = Fin.castAdd m i ∧ v = Fin.natAdd m i) ∨
      (∃ i : Fin m, v = Fin.castAdd m i ∧ u = Fin.natAdd m i) := by
  rw [matchingGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩
    · have hx := hi.symm.trans hi'
      have := congrArg Fin.val hx
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · have hx := hi'.symm.trans hi
      have := congrArg Fin.val hx
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega

/-- The `i`th canonical edge of `matchingGraph m`. -/
def matchingEdgeEmbedding (m : ℕ) : Fin m ↪ Sym2 (Fin (m + m)) where
  toFun i := s(Fin.castAdd m i, Fin.natAdd m i)
  inj' := by
    intro i j hij
    rw [Sym2.eq_iff] at hij
    rcases hij with hij | hij
    · apply Fin.ext
      have hval := congrArg (fun x : Fin (m + m) ↦ x.val) hij.1
      simpa using hval
    · have hval := congrArg Fin.val hij.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega

/-- The canonical matching has exactly `m` edges. -/
@[simp] theorem matchingCode_edgeCount (m : ℕ) :
    (matchingCode m).edgeCount = m := by
  classical
  let : DecidableRel (matchingGraph m).Adj := Classical.decRel _
  rw [GraphCode.edgeCount_eq_card_edgeFinset]
  change (matchingGraph m).edgeFinset.card = m
  have hedges : (matchingGraph m).edgeFinset =
      Finset.univ.map (matchingEdgeEmbedding m) := by
    ext e
    constructor
    · intro he
      have hadj : (matchingGraph m).Adj e.out.1 e.out.2 := by
        rw [← (matchingGraph m).mem_edgeSet, Sym2.mk, e.out_eq]
        exact SimpleGraph.mem_edgeFinset.mp he
      rw [matchingGraph_adj_iff] at hadj
      rcases hadj with ⟨i, hi, hj⟩ | ⟨i, hj, hi⟩
      · rw [Finset.mem_map]
        refine ⟨i, by simp, ?_⟩
        change s(Fin.castAdd m i, Fin.natAdd m i) = e
        rw [← hi, ← hj]
        exact Quot.out_eq e
      · rw [Finset.mem_map]
        refine ⟨i, by simp, ?_⟩
        change s(Fin.castAdd m i, Fin.natAdd m i) = e
        rw [← hi, ← hj, Sym2.eq_swap]
        exact Quot.out_eq e
    · intro he
      rw [Finset.mem_map] at he
      obtain ⟨i, -, rfl⟩ := he
      change s(Fin.castAdd m i, Fin.natAdd m i) ∈ (matchingGraph m).edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (matchingGraph_adj_iff).mpr
        (Or.inl ⟨i, by rfl, by rfl⟩)
  rw [hedges, Finset.card_map]
  simp

section FiniteMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite matching represented by its pairwise vertex-disjoint graph edges. -/
def IsFiniteMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
    (M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset

/-- The vertices covered by a finite matching. -/
def matchedVertices (M : Finset (Sym2 V)) : Finset V :=
  M.biUnion Sym2.toFinset

/-- The vertices not covered by a finite matching. -/
def unmatchedVertices (M : Finset (Sym2 V)) : Finset V :=
  Finset.univ \ matchedVertices M

@[simp] theorem mem_matchedVertices {M : Finset (Sym2 V)} {v : V} :
    v ∈ matchedVertices M ↔ ∃ e ∈ M, v ∈ e := by
  simp [matchedVertices]

@[simp] theorem mem_unmatchedVertices {M : Finset (Sym2 V)} {v : V} :
    v ∈ unmatchedVertices M ↔ ∀ e ∈ M, v ∉ e := by
  simp [unmatchedVertices]

/-- The support of a matching has exactly twice as many vertices as edges. -/
theorem card_matchedVertices {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M) :
    (matchedVertices M).card = 2 * M.card := by
  classical
  rw [matchedVertices, Finset.card_biUnion hM.2]
  have hedge : ∀ e ∈ M, e.toFinset.card = 2 := by
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeFinset (hM.1 he))
  rw [Finset.sum_const_nat hedge]
  simp [mul_comm]

/-- Exact number of vertices left uncovered by a matching. -/
theorem card_unmatchedVertices {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M) :
    (unmatchedVertices M).card + 2 * M.card = Fintype.card V := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show matchedVertices M ⊆ (Finset.univ : Finset V) from Finset.subset_univ _)
  rw [card_matchedVertices hM] at hsplit
  simpa [unmatchedVertices] using hsplit

/-- A finite matching of cardinality `m` gives an ordinary copy of the
canonical `m`-edge matching. -/
theorem matchingGraph_isContained_of_finiteMatching {G : SimpleGraph V}
    [DecidableRel G.Adj] {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M)
    {m : ℕ} (hcard : M.card = m) : matchingGraph m ⊑ G := by
  classical
  let enum : Fin m ≃ M := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let edge : Fin m → Sym2 V := fun i ↦ (enum i).1
  let left : Fin m → V := fun i ↦ (edge i).out.1
  let right : Fin m → V := fun i ↦ (edge i).out.2
  have hedge_mem (i : Fin m) : edge i ∈ M := (enum i).2
  have hedge_adj (i : Fin m) : G.Adj (left i) (right i) := by
    rw [← G.mem_edgeSet, Sym2.mk, (edge i).out_eq]
    exact SimpleGraph.mem_edgeFinset.mp (hM.1 (hedge_mem i))
  have hedge_ne {i j : Fin m} (hij : i ≠ j) : edge i ≠ edge j := by
    intro h
    exact hij (enum.injective (Subtype.ext h))
  have hleft_inj : Function.Injective left := by
    intro i j hij
    by_contra hne
    have hd := hM.2 (hedge_mem i) (hedge_mem j) (hedge_ne hne)
    change Disjoint (edge i).toFinset (edge j).toFinset at hd
    rw [Finset.disjoint_left] at hd
    exact hd (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem (edge i)))
      (by simpa [left, hij] using
        (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem (edge j))))
  have hright_inj : Function.Injective right := by
    intro i j hij
    by_contra hne
    have hd := hM.2 (hedge_mem i) (hedge_mem j) (hedge_ne hne)
    change Disjoint (edge i).toFinset (edge j).toFinset at hd
    rw [Finset.disjoint_left] at hd
    exact hd (Sym2.mem_toFinset.mpr (Sym2.out_snd_mem (edge i)))
      (by simpa [right, hij] using
        (Sym2.mem_toFinset.mpr (Sym2.out_snd_mem (edge j))))
  have hcross {i j : Fin m} : left i ≠ right j := by
    intro hij
    by_cases hEq : i = j
    · subst j
      exact (hedge_adj i).ne hij
    · have hd := hM.2 (hedge_mem i) (hedge_mem j) (hedge_ne hEq)
      change Disjoint (edge i).toFinset (edge j).toFinset at hd
      rw [Finset.disjoint_left] at hd
      exact hd (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem (edge i)))
        (by simpa [left, right, hij] using
          (Sym2.mem_toFinset.mpr (Sym2.out_snd_mem (edge j))))
  let fsum : Fin m ⊕ Fin m → V := Sum.elim left right
  have hfsum : Function.Injective fsum := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · exact congrArg Sum.inl (hleft_inj hxy)
    · exact (hcross hxy).elim
    · exact (hcross hxy.symm).elim
    · exact congrArg Sum.inr (hright_inj hxy)
  let f : Fin (m + m) → V := fsum ∘ finSumFinEquiv.symm
  have hf : Function.Injective f := hfsum.comp finSumFinEquiv.symm.injective
  let hom : matchingGraph m →g G :=
    ⟨f, by
      intro u v huv
      rw [matchingGraph_adj_iff] at huv
      rcases huv with ⟨i, hu, hv⟩ | ⟨i, hv, hu⟩
      · subst u
        subst v
        dsimp only [f, Function.comp_apply]
        rw [finSumFinEquiv_symm_apply_castAdd,
          finSumFinEquiv_symm_apply_natAdd]
        exact hedge_adj i
      · subst u
        subst v
        dsimp only [f, Function.comp_apply]
        rw [finSumFinEquiv_symm_apply_natAdd,
          finSumFinEquiv_symm_apply_castAdd]
        exact (hedge_adj i).symm⟩
  exact ⟨⟨hom, hf⟩⟩

/-- If every connected component has at most one edge, then the full edge
set is a finite matching. -/
theorem edgeFinset_isFiniteMatching_of_components_le_one
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hall : ∀ c : H.graph.ConnectedComponent,
      (componentCode H c).edgeCount ≤ 1) :
    IsFiniteMatching H.graph H.graph.edgeFinset := by
  classical
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro e he f hf hef
  change Disjoint e.toFinset f.toFinset
  rw [Finset.disjoint_left]
  intro x hxe hxf
  have hxe' : x ∈ e := Sym2.mem_toFinset.mp hxe
  have hxf' : x ∈ f := Sym2.mem_toFinset.mp hxf
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe'
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxf'
  have hxy : H.graph.Adj x y := by
    have he' : s(x, y) ∈ H.graph.edgeFinset := he
    have heSet := SimpleGraph.mem_edgeFinset.mp he'
    rwa [SimpleGraph.mem_edgeSet] at heSet
  have hxz : H.graph.Adj x z := by
    have hf' : s(x, z) ∈ H.graph.edgeFinset := hf
    have hfSet := SimpleGraph.mem_edgeFinset.mp hf'
    rwa [SimpleGraph.mem_edgeSet] at hfSet
  have hyz : y ≠ z := by
    intro hyz
    apply hef
    simp [hyz]
  let c := H.graph.connectedComponentMk x
  have hxC : x ∈ c.supp := rfl
  have hyC : y ∈ c.supp := c.mem_supp_of_adj_mem_supp hxC hxy
  have hzC : z ∈ c.supp := c.mem_supp_of_adj_mem_supp hxC hxz
  let X : c.supp := ⟨x, hxC⟩
  let Y : c.supp := ⟨y, hyC⟩
  let Z : c.supp := ⟨z, hzC⟩
  let ec := componentCodeIso H c
  let a : Sym2 (Fin (componentCode H c).vertexCount) := s(ec X, ec Y)
  let b : Sym2 (Fin (componentCode H c).vertexCount) := s(ec X, ec Z)
  let : DecidableRel (componentCode H c).graph.Adj := Classical.decRel _
  have ha : a ∈ (componentCode H c).graph.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ec.toHom.map_adj hxy
  have hb : b ∈ (componentCode H c).graph.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ec.toHom.map_adj hxz
  have hab : a ≠ b := by
    intro hab
    have hYZ : ec Y = ec Z := Sym2.congr_right.mp hab
    have hYZ' : Y = Z := ec.injective hYZ
    exact hyz (congrArg Subtype.val hYZ')
  have hsub : ({a, b} : Finset _) ⊆
      (componentCode H c).graph.edgeFinset := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ha
    · exact hb
  have htwo : 2 ≤ (componentCode H c).graph.edgeFinset.card := by
    have := Finset.card_le_card hsub
    simpa [hab] using this
  have hc := hall c
  rw [GraphCode.edgeCount_eq_card_edgeFinset] at hc
  omega

/-- An isolate-free graph whose components all have at most one edge is
isomorphic to the canonical matching with the same edge count. -/
theorem isomorphic_matchingCode_of_components_le_one
    (H : GraphCode) [DecidableRel H.graph.Adj] (hH : NoIsolated H)
    (hall : ∀ c : H.graph.ConnectedComponent,
      (componentCode H c).edgeCount ≤ 1) :
    Isomorphic (matchingCode H.edgeCount) H := by
  classical
  let M := H.graph.edgeFinset
  have hM : IsFiniteMatching H.graph M :=
    edgeFinset_isFiniteMatching_of_components_le_one H hall
  have hcopy : IsContained (matchingCode H.edgeCount) H := by
    simpa [matchingCode, M] using
      matchingGraph_isContained_of_finiteMatching hM
        (m := H.edgeCount) (by
          rw [GraphCode.edgeCount_eq_card_edgeFinset])
  have hUempty : unmatchedVertices M = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨w, hvw⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH v)
    let q : Sym2 (Fin H.vertexCount) := s(v, w)
    have hq : q ∈ M := by
      dsimp only [M, q]
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hvw
    exact (mem_unmatchedVertices.mp hv q hq) (Sym2.mem_mk_left v w)
  have hvertices := card_unmatchedVertices hM
  rw [hUempty] at hvertices
  simp only [Finset.card_empty, zero_add, Fintype.card_fin] at hvertices
  have hMcard : M.card = H.edgeCount := by
    dsimp only [M]
    rw [GraphCode.edgeCount_eq_card_edgeFinset]
  have hV : (matchingCode H.edgeCount).vertexCount = H.vertexCount := by
    change H.edgeCount + H.edgeCount = H.vertexCount
    rw [← hvertices, hMcard]
    omega
  have hE : (matchingCode H.edgeCount).edgeCount = H.edgeCount :=
    matchingCode_edgeCount H.edgeCount
  exact isomorphic_of_isContained_of_counts hcopy hV hE

/-- Structural trichotomy for an isolate-free finite graph: it is connected,
it is a matching, or it has a component containing between two and all but
one of its edges. -/
theorem connected_or_matching_or_nontrivial_component
    (H : GraphCode) (hH : NoIsolated H) :
    H.graph.Connected ∨ Isomorphic (matchingCode H.edgeCount) H ∨
      ∃ c : H.graph.ConnectedComponent,
        2 ≤ (componentCode H c).edgeCount ∧
          (componentCode H c).edgeCount < H.edgeCount := by
  classical
  let : DecidableRel H.graph.Adj := Classical.decRel _
  by_cases hconn : H.graph.Connected
  · exact Or.inl hconn
  by_cases hall : ∀ c : H.graph.ConnectedComponent,
      (componentCode H c).edgeCount ≤ 1
  · exact Or.inr (Or.inl
      (isomorphic_matchingCode_of_components_le_one H hH hall))
  · push_neg at hall
    obtain ⟨c, hc⟩ := hall
    have hsplit := componentCode_edgeCount_add_remainder H c
    have hcle : (componentCode H c).edgeCount ≤ H.edgeCount := by omega
    have hclt : (componentCode H c).edgeCount < H.edgeCount := by
      rcases hcle.eq_or_lt with hceq | hclt
      · exact (hconn (connected_of_component_edgeCount_eq hH c hceq)).elim
      · exact hclt
    exact Or.inr (Or.inr ⟨c, by omega, hclt⟩)

/-- Every finite graph has a maximum-cardinality matching. -/
theorem exists_maximum_finiteMatching (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Sym2 V), IsFiniteMatching G M ∧
      ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card := by
  classical
  let good := G.edgeFinset.powerset.filter fun (M : Finset (Sym2 V)) ↦
    (M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset
  have hgood : good.Nonempty := ⟨∅, by simp [good]⟩
  obtain ⟨M, hMgood, hMmax⟩ := good.exists_max_image Finset.card hgood
  have hMsub : M ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMgood).1
  have hMpair : (M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset :=
    (Finset.mem_filter.mp hMgood).2
  refine ⟨M, ⟨hMsub, hMpair⟩, ?_⟩
  intro N hN
  exact hMmax N (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hN.1, hN.2⟩)

/-- Inserting an edge disjoint from every edge of a matching preserves the
matching property. -/
theorem IsFiniteMatching.insert {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M) {e : Sym2 V}
    (heG : e ∈ G.edgeFinset)
    (hedisj : ∀ f ∈ M, Disjoint e.toFinset f.toFinset) :
    IsFiniteMatching G (insert e M) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heG
    · exact hM.1 hf
  · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
    refine ⟨hM.2, ?_⟩
    intro f hf hef
    exact hedisj f hf

/-- Removing an edge preserves the matching property. -/
theorem IsFiniteMatching.erase {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M) (e : Sym2 V) :
    IsFiniteMatching G (M.erase e) := by
  refine ⟨fun _ hf ↦ hM.1 (Finset.mem_of_mem_erase hf), ?_⟩
  exact hM.2.subset (by simp)

theorem unmatched_ne_of_mem_edge {M : Finset (Sym2 V)} {u : V}
    (hu : u ∈ unmatchedVertices M) {e : Sym2 V} (he : e ∈ M)
    {x : V} (hx : x ∈ e) : u ≠ x := by
  intro hux
  exact (mem_unmatchedVertices.mp hu e he) (hux ▸ hx)

/-- A maximum matching has no augmenting path whose endpoints are two
distinct unmatched vertices and whose middle edge belongs to the matching. -/
theorem maximumMatching_no_augmenting_threePath {G : SimpleGraph V}
    [DecidableRel G.Adj] {M : Finset (Sym2 V)}
    (hM : IsFiniteMatching G M)
    (hmax : ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card)
    {e : Sym2 V} (he : e ∈ M) {u v : V}
    (hu : u ∈ unmatchedVertices M) (hv : v ∈ unmatchedVertices M)
    (huv : u ≠ v) :
    ¬(G.Adj u e.out.1 ∧ G.Adj e.out.2 v) := by
  rintro ⟨hux, hyv⟩
  let x := e.out.1
  let y := e.out.2
  let e₁ : Sym2 V := s(u, x)
  let e₂ : Sym2 V := s(v, y)
  have hxmem : x ∈ e := Sym2.out_fst_mem e
  have hymem : y ∈ e := Sym2.out_snd_mem e
  have hxy : x ≠ y := by
    have hxyAdj : G.Adj e.out.1 e.out.2 := by
      rw [← G.mem_edgeSet, Sym2.mk, e.out_eq]
      exact SimpleGraph.mem_edgeFinset.mp (hM.1 he)
    simpa [x, y] using hxyAdj.ne
  have huxne : u ≠ x := unmatched_ne_of_mem_edge hu he hxmem
  have huyne : u ≠ y := unmatched_ne_of_mem_edge hu he hymem
  have hvxne : v ≠ x := unmatched_ne_of_mem_edge hv he hxmem
  have hvyne : v ≠ y := unmatched_ne_of_mem_edge hv he hymem
  have he₁G : e₁ ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hux
  have he₂G : e₂ ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hyv.symm
  have he₁notM : e₁ ∉ M := by
    intro he₁
    exact (mem_unmatchedVertices.mp hu e₁ he₁) (Sym2.mem_mk_left u x)
  have he₂notM : e₂ ∉ M := by
    intro he₂
    exact (mem_unmatchedVertices.mp hv e₂ he₂) (Sym2.mem_mk_left v y)
  have he₁disj : ∀ f ∈ M.erase e, Disjoint e₁.toFinset f.toFinset := by
    intro f hf
    obtain ⟨hfe, hfM⟩ := Finset.mem_erase.mp hf
    have hef : Disjoint e.toFinset f.toFinset := hM.2 he hfM hfe.symm
    rw [Finset.disjoint_left]
    intro z hze₁ hzf
    rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hze₁
    rcases hze₁ with rfl | rfl
    · exact (mem_unmatchedVertices.mp hu f hfM) (Sym2.mem_toFinset.mp hzf)
    · exact (Finset.disjoint_left.mp hef)
        (Sym2.mem_toFinset.mpr hxmem) hzf
  have he₂disjOld : ∀ f ∈ M.erase e, Disjoint e₂.toFinset f.toFinset := by
    intro f hf
    obtain ⟨hfe, hfM⟩ := Finset.mem_erase.mp hf
    have hef : Disjoint e.toFinset f.toFinset := hM.2 he hfM hfe.symm
    rw [Finset.disjoint_left]
    intro z hze₂ hzf
    rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hze₂
    rcases hze₂ with rfl | rfl
    · exact (mem_unmatchedVertices.mp hv f hfM) (Sym2.mem_toFinset.mp hzf)
    · exact (Finset.disjoint_left.mp hef)
        (Sym2.mem_toFinset.mpr hymem) hzf
  have he₂e₁ : Disjoint e₂.toFinset e₁.toFinset := by
    rw [Finset.disjoint_left]
    intro z hze₂ hze₁
    rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hze₂ hze₁
    rcases hze₂ with rfl | rfl <;> rcases hze₁ with h | h
    · exact huv h.symm
    · exact hvxne h
    · exact huyne h.symm
    · exact hxy h.symm
  have he₂disj : ∀ f ∈ insert e₁ (M.erase e),
      Disjoint e₂.toFinset f.toFinset := by
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact he₂e₁
    · exact he₂disjOld f hf
  let N := insert e₂ (insert e₁ (M.erase e))
  have hN : IsFiniteMatching G N :=
    ((hM.erase e).insert he₁G he₁disj).insert he₂G he₂disj
  have he₁notErase : e₁ ∉ M.erase e := fun h ↦
    he₁notM (Finset.mem_of_mem_erase h)
  have he₂ne₁ : e₂ ≠ e₁ := by
    intro h
    have hvIn : v ∈ e₁ := by
      rw [← h]
      exact Sym2.mem_mk_left v y
    have hvIn' : v ∈ s(u, x).toFinset := Sym2.mem_toFinset.mpr hvIn
    rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hvIn'
    exact hvIn'.elim (fun h ↦ huv h.symm) hvxne
  have he₂notInsert : e₂ ∉ insert e₁ (M.erase e) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨he₂ne₁, fun h ↦ he₂notM (Finset.mem_of_mem_erase h)⟩
  have hcardErase := Finset.card_erase_add_one he
  have hcard₁ := Finset.card_insert_of_notMem he₁notErase
  have hcard₂ := Finset.card_insert_of_notMem he₂notInsert
  have hle := hmax N hN
  dsimp only [N] at hle
  rw [hcard₂, hcard₁] at hle
  omega

/-- On every edge of a maximum matching, one endpoint has at most one
neighbor among the unmatched vertices. -/
theorem maximumMatching_exists_sparse_endpoint {G : SimpleGraph V}
    [DecidableRel G.Adj] {M : Finset (Sym2 V)}
    (hM : IsFiniteMatching G M)
    (hmax : ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card)
    {e : Sym2 V} (he : e ∈ M) :
    ∃ x ∈ e, ((unmatchedVertices M).filter fun u ↦ G.Adj x u).card ≤ 1 := by
  classical
  let A := (unmatchedVertices M).filter fun u ↦ G.Adj e.out.1 u
  let B := (unmatchedVertices M).filter fun u ↦ G.Adj e.out.2 u
  by_cases hA : A.card ≤ 1
  · exact ⟨e.out.1, Sym2.out_fst_mem e, by simpa [A] using hA⟩
  · have hA' : 1 < A.card := by omega
    by_cases hB : B.card ≤ 1
    · exact ⟨e.out.2, Sym2.out_snd_mem e, by simpa [B] using hB⟩
    · have hB' : 1 < B.card := by omega
      have hAnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u, huA⟩ := hAnonempty
      obtain ⟨v, hvB, hvu⟩ := B.exists_mem_ne hB' u
      have hu := (Finset.mem_filter.mp huA).1
      have hv := (Finset.mem_filter.mp hvB).1
      have hxu := (Finset.mem_filter.mp huA).2
      have hyv := (Finset.mem_filter.mp hvB).2
      exact (maximumMatching_no_augmenting_threePath hM hmax he hu hv hvu.symm
        ⟨hxu.symm, hyv⟩).elim

/-- Vertices left unmatched by a maximum matching form a clique in the
complement graph. -/
theorem unmatchedVertices_isClique_compl {G : SimpleGraph V}
    [DecidableRel G.Adj] {M : Finset (Sym2 V)}
    (hM : IsFiniteMatching G M)
    (hmax : ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card) :
    Gᶜ.IsClique (unmatchedVertices M : Set V) := by
  classical
  intro u hu v hv huv
  have hu' := (mem_unmatchedVertices.mp hu)
  have hv' := (mem_unmatchedVertices.mp hv)
  rw [SimpleGraph.compl_adj]
  refine ⟨huv, ?_⟩
  intro huvG
  let e : Sym2 V := s(u, v)
  have heG : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact huvG
  have heM : e ∉ M := by
    intro he
    exact hu' e he (Sym2.mem_mk_left u v)
  have hedisj : ∀ f ∈ M, Disjoint e.toFinset f.toFinset := by
    intro f hf
    rw [Finset.disjoint_left]
    intro x hxe hxf
    rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hxe
    rcases hxe with rfl | rfl
    · exact hu' f hf (Sym2.mem_toFinset.mp hxf)
    · exact hv' f hf (Sym2.mem_toFinset.mp hxf)
  have hins := hM.insert heG hedisj
  have hcard := hmax (insert e M) hins
  rw [Finset.card_insert_of_notMem heM] at hcard
  omega

/-- A canonical endpoint with few neighbours among the vertices missed by a
maximum matching. -/
noncomputable def sparseEndpoint {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M)
    (hmax : ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card)
    (e : Sym2 V) (he : e ∈ M) : V :=
  (maximumMatching_exists_sparse_endpoint hM hmax he).choose

theorem sparseEndpoint_mem {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M)
    (hmax : ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card)
    (e : Sym2 V) (he : e ∈ M) : sparseEndpoint hM hmax e he ∈ e :=
  (maximumMatching_exists_sparse_endpoint hM hmax he).choose_spec.1

theorem sparseEndpoint_blue_degree {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Finset (Sym2 V)} (hM : IsFiniteMatching G M)
    (hmax : ∀ N : Finset (Sym2 V), IsFiniteMatching G N → N.card ≤ M.card)
    (e : Sym2 V) (he : e ∈ M) :
    ((unmatchedVertices M).filter fun u ↦ G.Adj (sparseEndpoint hM hmax e he) u).card ≤ 1 :=
  (maximumMatching_exists_sparse_endpoint hM hmax he).choose_spec.2

/-- A finite set of known neighbours in an induced graph lower-bounds the
degree there. -/
theorem card_le_degree_induce_of_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {S T : Finset V} (hTS : T ⊆ S) (x : S)
    (hadj : ∀ y ∈ T, G.Adj x.1 y) :
    T.card ≤ (G.induce (S : Set V)).degree x := by
  classical
  let f : T ↪ S :=
    ⟨fun y ↦ ⟨y.1, hTS y.2⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : S ↦ z.1) h)⟩
  have hsub : T.attach.map f ⊆ (G.induce (S : Set V)).neighborFinset x := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj y.1 y.2
  calc
    T.card = (T.attach.map f).card := by simp
    _ ≤ ((G.induce (S : Set V)).neighborFinset x).card :=
      Finset.card_le_card hsub
    _ = (G.induce (S : Set V)).degree x :=
      SimpleGraph.card_neighborFinset_eq_degree (G.induce (S : Set V)) x

/-- If a graph on the extremal number of vertices has no matching of size
`m`, then its complement contains the required cycle.  This is the upper-bound
engine for the exact matching case of Problem 570. -/
theorem cycle_isContained_compl_of_matching_lt {G : SimpleGraph V}
    [DecidableRel G.Adj] {k m : ℕ} (hk : 3 ≤ k) (hkm : k ≤ m)
    (hV : Fintype.card V = 2 * m + (k - 1) / 2)
    (hsmall : ∀ M : Finset (Sym2 V), IsFiniteMatching G M → M.card < m) :
    SimpleGraph.cycleGraph k ⊑ Gᶜ := by
  classical
  obtain ⟨M, hM, hmax⟩ := exists_maximum_finiteMatching G
  let U := unmatchedVertices M
  have hMlt : M.card < m := hsmall M hM
  have hsplit : U.card + 2 * M.card = 2 * m + (k - 1) / 2 := by
    rw [card_unmatchedVertices hM, hV]
  have hUlower : (k - 1) / 2 + 2 ≤ U.card := by omega
  have hUclique : Gᶜ.IsClique (U : Set V) :=
    unmatchedVertices_isClique_compl hM hmax
  by_cases hUk : k ≤ U.card
  · obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq hUk
    have hTclique : Gᶜ.IsClique (T : Set V) := by
      exact hUclique.subset (by simpa using hTU)
    have hTnclique : Gᶜ.IsNClique k T := ⟨hTclique, hTcard⟩
    have htop : (⊤ : SimpleGraph (Fin k)) ⊑ Gᶜ :=
      (SimpleGraph.not_cliqueFree_iff_top_isContained k).mp
        hTnclique.not_cliqueFree
    exact (SimpleGraph.IsContained.of_le le_top).trans htop
  · have hUkt : U.card < k := Nat.lt_of_not_ge hUk
    let t := k - U.card
    have htM : t ≤ M.card := by
      dsimp only [t]
      omega
    obtain ⟨E, hEM, hEcard⟩ := Finset.exists_subset_card_eq htM
    let rep : E → V := fun e ↦
      sparseEndpoint hM hmax e.1 (hEM e.2)
    have hrep_mem (e : E) : rep e ∈ e.1 := by
      exact sparseEndpoint_mem hM hmax e.1 (hEM e.2)
    have hrep_sparse (e : E) :
        (U.filter fun u ↦ G.Adj (rep e) u).card ≤ 1 := by
      exact sparseEndpoint_blue_degree hM hmax e.1 (hEM e.2)
    have hrep_inj : Function.Injective rep := by
      intro e f hef
      by_contra hne
      have hef_ne : e.1 ≠ f.1 := fun h ↦ hne (Subtype.ext h)
      have hdisj := hM.2 (hEM e.2) (hEM f.2) hef_ne
      change Disjoint e.1.toFinset f.1.toFinset at hdisj
      rw [Finset.disjoint_left] at hdisj
      exact hdisj (Sym2.mem_toFinset.mpr (hrep_mem e))
        (Sym2.mem_toFinset.mpr (hef ▸ hrep_mem f))
    let R : Finset V := E.attach.image rep
    have hRcard : R.card = t := by
      dsimp only [R]
      rw [Finset.card_image_of_injective _ hrep_inj]
      simpa using hEcard
    have hUR : Disjoint U R := by
      rw [Finset.disjoint_left]
      intro u huU huR
      obtain ⟨e, heE, heu⟩ := Finset.mem_image.mp huR
      have heMem : rep e ∈ e.1 := hrep_mem e
      have huMem : u ∈ e.1 := by simpa [heu] using heMem
      exact (mem_unmatchedVertices.mp huU e.1 (hEM e.2)) huMem
    let S := U ∪ R
    have hScard : S.card = k := by
      dsimp only [S]
      rw [Finset.card_union_of_disjoint hUR, hRcard]
      dsimp only [t]
      omega
    have hR_not_U {x : V} (hxR : x ∈ R) : x ∉ U := by
      exact fun hxU ↦ Finset.disjoint_left.mp hUR hxU hxR
    have hred_card {x : V} (hxR : x ∈ R) :
        (U.filter fun u ↦ Gᶜ.Adj x u).card + 1 ≥ U.card := by
      obtain ⟨e, heE, hex⟩ := Finset.mem_image.mp hxR
      have hblue : (U.filter fun u ↦ G.Adj x u).card ≤ 1 := by
        simpa [hex] using hrep_sparse e
      have hred_eq :
          U.filter (fun u ↦ Gᶜ.Adj x u) =
            U \ U.filter (fun u ↦ G.Adj x u) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨huU, hxu⟩
          rw [SimpleGraph.compl_adj] at hxu
          exact ⟨huU, fun h ↦ hxu.2 h.2⟩
        · rintro ⟨huU, hnot⟩
          refine ⟨huU, ?_⟩
          rw [SimpleGraph.compl_adj]
          exact ⟨fun hxu ↦ hR_not_U hxR (hxu.symm ▸ huU),
            fun hadj ↦ hnot ⟨huU, hadj⟩⟩
      rw [hred_eq, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      omega
    have hSType : Fintype.card S = k := by
      simpa using hScard
    let K : SimpleGraph S := Gᶜ.induce (S : Set V)
    have hKdeg : ∀ x : S, Fintype.card S ≤ 2 * K.degree x := by
      intro x
      have hxS : x.1 ∈ U ∪ R := by simpa [S] using x.2
      rw [Finset.mem_union] at hxS
      rcases hxS with hxU | hxR
      · have hsub : U.erase x.1 ⊆ S := by
          intro y hy
          exact Finset.mem_union_left R (Finset.mem_of_mem_erase hy)
        have hadj : ∀ y ∈ U.erase x.1, Gᶜ.Adj x.1 y := by
          intro y hy
          have hy' := Finset.mem_erase.mp hy
          exact hUclique hxU hy'.2 hy'.1.symm
        have hdeg := card_le_degree_induce_of_adj (G := Gᶜ) hsub x hadj
        have herase : (U.erase x.1).card + 1 = U.card :=
          Finset.card_erase_add_one hxU
        dsimp only [K]
        rw [hSType]
        omega
      · let T := U.filter fun u ↦ Gᶜ.Adj x.1 u
        have hsub : T ⊆ S := by
          intro y hy
          exact Finset.mem_union_left R (Finset.mem_filter.mp hy).1
        have hadj : ∀ y ∈ T, Gᶜ.Adj x.1 y := by
          intro y hy
          exact (Finset.mem_filter.mp hy).2
        have hdeg := card_le_degree_induce_of_adj (G := Gᶜ) hsub x hadj
        have hTcard : U.card ≤ T.card + 1 := hred_card hxR
        dsimp only [K]
        rw [hSType]
        omega
    have hKham : K.IsHamiltonian := by
      apply SimpleGraph.dirac_theorem (G := K)
      · rw [hSType]
        exact hk
      · intro x
        simpa using hKdeg x
    obtain ⟨a, p, hp⟩ := hKham (by rw [hSType]; omega)
    have hcycleK : SimpleGraph.cycleGraph k ⊑ K :=
      (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
        ⟨a, p, hp.isCycle, by simpa [hSType] using hp.length_eq⟩
    exact hcycleK.trans (SimpleGraph.Embedding.induce (S : Set V)).isContained

/-- The sharp upper bound for a cycle versus a matching, expressed as an
exact-order Ramsey assertion. -/
theorem ramseyAt_cycle_matching {k m : ℕ} (hk : 3 ≤ k) (hkm : k ≤ m) :
    RamseyAt (cycleCode k) (matchingCode m)
      (2 * m + (k - 1) / 2) := by
  classical
  intro C
  let : DecidableRel C.Adj := Classical.decRel C.Adj
  let : DecidableRel Cᶜ.Adj := Classical.decRel Cᶜ.Adj
  by_cases hex : ∃ M : Finset (Sym2 (Fin (2 * m + (k - 1) / 2))),
      IsFiniteMatching Cᶜ M ∧ m ≤ M.card
  · right
    obtain ⟨M, hM, hmM⟩ := hex
    obtain ⟨E, hEM, hEcard⟩ := Finset.exists_subset_card_eq hmM
    have hE : IsFiniteMatching Cᶜ E := by
      refine ⟨hEM.trans hM.1, ?_⟩
      exact hM.2.subset (by simpa using hEM)
    simpa [matchingCode] using
      (matchingGraph_isContained_of_finiteMatching hE hEcard)
  · left
    have hsmall : ∀ M : Finset (Sym2 (Fin (2 * m + (k - 1) / 2))),
        IsFiniteMatching Cᶜ M → M.card < m := by
      intro M hM
      exact Nat.lt_of_not_ge (fun hmM ↦ hex ⟨M, hM, hmM⟩)
    have hcycle := cycle_isContained_compl_of_matching_lt
      (G := Cᶜ) hk hkm (by simp) hsmall
    simpa [cycleCode] using hcycle

theorem graphRamseyNumber_cycle_matching_le {k m : ℕ}
    (hk : 3 ≤ k) (hkm : k ≤ m) :
    graphRamseyNumber (cycleCode k) (matchingCode m) ≤
      2 * m + (k - 1) / 2 :=
  graphRamseyNumber_le_of_ramseyAt (ramseyAt_cycle_matching hk hkm)

end FiniteMatching

/-- The natural-number strengthened estimate used by the modern odd-cycle
induction.  The correction term decreases with the square root of the target
edge count and eventually becomes the sharp parity term. -/
def StrongOddCycleBound (k B : ℕ) : Prop :=
  ∀ H : GraphCode, NoIsolated H →
    graphRamseyNumber (cycleCode k) H ≤ oddBudget B (k / 2) H.edgeCount

/-- A uniform finite base constant obtained from ordinary finite Ramsey's
theorem.  No quantitative cycle--clique estimate is needed in the bounded
edge-count part of the induction. -/
def oddBaseConstant (k M₀ : ℕ) : ℕ :=
  max (k / 2)
    (graphRamseyNumber (cycleCode k) (completeCode (2 * M₀)) + Nat.sqrt M₀)

theorem oddBaseConstant_half_le (k M₀ : ℕ) :
    k / 2 ≤ oddBaseConstant k M₀ := by
  simp [oddBaseConstant]

/-- The finite base of the strengthened induction, derived solely from
finite Ramsey's theorem and the no-isolated-vertices order bound. -/
theorem graphRamseyNumber_cycle_le_oddBudget_base
    {k M₀ : ℕ} (H : GraphCode) (hH : NoIsolated H)
    (hm : H.edgeCount ≤ M₀) :
    graphRamseyNumber (cycleCode k) H ≤
      oddBudget (oddBaseConstant k M₀) (k / 2) H.edgeCount := by
  have hn : H.vertexCount ≤ 2 * M₀ :=
    (NoIsolated.vertexCount_le_twice_edgeCount hH).trans
      (Nat.mul_le_mul_left 2 hm)
  have hram := graphRamseyNumber_le_complete_of_vertexCount_le
    (cycleCode k) H hn
  have hsqrt : Nat.sqrt H.edgeCount ≤ Nat.sqrt M₀ :=
    Nat.sqrt_le_sqrt hm
  have hconst :
      graphRamseyNumber (cycleCode k) (completeCode (2 * M₀)) +
          Nat.sqrt M₀ ≤ oddBaseConstant k M₀ := by
    simp [oddBaseConstant]
  have hsub : graphRamseyNumber (cycleCode k) (completeCode (2 * M₀)) ≤
      oddBaseConstant k M₀ - Nat.sqrt H.edgeCount := by
    omega
  exact hram.trans (by
    unfold oddBudget
    exact hsub.trans ((le_max_left _ _).trans (Nat.le_add_left _ _)))

/-- The strengthened odd-cycle theorem reduced to its two published
connected-target inputs.  `hdense` handles targets below the neighborhood
scale; `hsparse` handles targets whose average degree is sufficiently close
to two.  All remaining graph theory and all rounding-sensitive arithmetic
are proved in this development. -/
theorem strongOddCycleBound_of_connected_inputs
    {k B D M₀ : ℕ}
    (hk : 5 ≤ k) (hB : k / 2 ≤ B) (hD : 2 ≤ D)
    (hkM₀ : k ≤ M₀)
    (hscale₀ : oddScaleRoot D k * oddScaleRoot D k ≤ M₀)
    (hbase : ∀ H : GraphCode, NoIsolated H → H.edgeCount ≤ M₀ →
      graphRamseyNumber (cycleCode k) H ≤
        oddBudget B (k / 2) H.edgeCount)
    (hdense : ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      H.vertexCount < 2 * D *
        (k * Nat.sqrt (2 * H.edgeCount)) →
      graphRamseyNumber (cycleCode k) H ≤
        oddBudget B (k / 2) H.edgeCount)
    (hsparse : ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      (D - 1) * H.edgeCount < D * H.vertexCount →
      (∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
        graphRamseyNumber (cycleCode k) Q ≤
          oddBudget B (k / 2) Q.edgeCount) →
      graphRamseyNumber (cycleCode k) H ≤
        oddBudget B (k / 2) H.edgeCount) :
    StrongOddCycleBound k B := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m →
      NoIsolated Q →
      graphRamseyNumber (cycleCode k) Q ≤ oddBudget B (k / 2) m by
    simpa using hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Q hQedge hQ
      subst m
      by_cases hm₀ : Q.edgeCount ≤ M₀
      · exact hbase Q hQ hm₀
      have hmLarge : M₀ < Q.edgeCount := Nat.lt_of_not_ge hm₀
      have hIH : ∀ R : GraphCode, NoIsolated R → R.edgeCount < Q.edgeCount →
          graphRamseyNumber (cycleCode k) R ≤
            oddBudget B (k / 2) R.edgeCount := by
        intro R hR hRm
        exact ih R.edgeCount hRm R rfl hR
      rcases connected_or_matching_or_nontrivial_component Q hQ with
        hconn | hmatching | ⟨c, hc₂, hcm⟩
      · let q := Nat.sqrt (2 * Q.edgeCount)
        by_cases hdenseOrder : Q.vertexCount < 2 * D * (k * q)
        · exact hdense Q hQ hconn hmLarge (by simpa [q] using hdenseOrder)
        have hlarge : 2 * D * (k * q) ≤ Q.vertexCount :=
          Nat.le_of_not_gt hdenseOrder
        by_cases hsparseDensity :
            (D - 1) * Q.edgeCount < D * Q.vertexCount
        · exact hsparse Q hQ hconn hmLarge hsparseDensity hIH
        have hdensity : D * Q.vertexCount ≤ (D - 1) * Q.edgeCount :=
          Nat.le_of_not_gt hsparseDensity
        have hrootSq : oddScaleRoot D k * oddScaleRoot D k ≤ Q.edgeCount :=
          hscale₀.trans hmLarge.le
        have hscale : oddScaleRoot D k ≤ Nat.sqrt Q.edgeCount :=
          Nat.le_sqrt.mpr hrootSq
        have hq : q = Nat.sqrt (2 * Q.edgeCount) := rfl
        have hmpos : 0 < Q.edgeCount := by omega
        have hqpos : 0 < q := by
          rw [hq, Nat.sqrt_pos]
          omega
        have hn₂ : 2 ≤ Q.vertexCount := by
          have hprodPos : 0 < D * (k * q) :=
            Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hqpos)
          have htwo : 2 ≤ 2 * (D * (k * q)) := by omega
          exact htwo.trans (by simpa [mul_assoc] using hlarge)
        have hhalf : 2 * (k * q) ≤ Q.vertexCount := by
          have hcoeff : 2 ≤ 2 * D := by omega
          have hle := Nat.mul_le_mul_right (k * q) hcoeff
          have hsmallLarge : 2 * (k * q) ≤ 2 * D * (k * q) := by
            simpa [mul_assoc] using hle
          exact hsmallLarge.trans hlarge
        have hnm : Q.vertexCount ≤ Q.edgeCount := by
          by_contra hnot
          have hmn : Q.edgeCount < Q.vertexCount := Nat.lt_of_not_ge hnot
          have hlt : D * Q.edgeCount < D * Q.vertexCount :=
            Nat.mul_lt_mul_of_pos_left hmn (by omega)
          have hcoef : D - 1 ≤ D := Nat.sub_le D 1
          have hle : (D - 1) * Q.edgeCount ≤ D * Q.edgeCount :=
            Nat.mul_le_mul_right Q.edgeCount hcoef
          omega
        have hgap : 4 * (k * q) + Nat.sqrt Q.edgeCount ≤
            Q.edgeCount - Q.vertexCount :=
          odd_gap_of_scale_and_density (by omega) hq hscale hdensity
        have hroom : OddMiddleRoom B (k / 2) k Q.edgeCount Q.vertexCount q :=
          oddMiddleRoom_of_gap hk hq hqpos hn₂ hhalf hgap
        apply graphRamseyNumber_le_of_ramseyAt
        intro C
        classical
        let : DecidableRel C.Adj := Classical.decRel _
        by_cases hred : (cycleCode k).graph ⊑ C
        · exact Or.inl hred
        by_cases hblue : Q.graph ⊑ Cᶜ
        · exact Or.inr hblue
        exact (odd_connected_middle_contradiction
          (H := Q) (B := B) (k := k) (D := D) (q := q)
          hk hQ hconn hq hB hD hnm hlarge hdensity hroom hIH
          C hred hblue).elim
      · have hkm : k ≤ Q.edgeCount := hkM₀.trans hmLarge.le
        have hmatchBound := graphRamseyNumber_cycle_matching_le
          (by omega : 3 ≤ k) hkm
        have hiso : graphRamseyNumber (cycleCode k) Q =
            graphRamseyNumber (cycleCode k) (matchingCode Q.edgeCount) := by
          rw [graphRamseyNumber_congr Isomorphic.rfl hmatching]
        rw [hiso]
        exact hmatchBound.trans (by unfold oddBudget; omega)
      · apply graphRamseyNumber_le_of_ramseyAt
        exact ramseyAt_oddBudget_of_nontrivial_component hQ rfl c hc₂ hcm hIH

/-- The connected-input reduction with its bounded-edge base discharged
canonically by finite Ramsey's theorem.  Thus the only hypotheses left are
the two genuinely asymptotic connected-target estimates. -/
theorem strongOddCycleBound_of_connected_extremes
    {k D M₀ : ℕ}
    (hk : 5 ≤ k) (hD : 2 ≤ D)
    (hkM₀ : k ≤ M₀)
    (hscale₀ : oddScaleRoot D k * oddScaleRoot D k ≤ M₀)
    (hdense : ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      H.vertexCount < 2 * D *
        (k * Nat.sqrt (2 * H.edgeCount)) →
      graphRamseyNumber (cycleCode k) H ≤
        oddBudget (oddBaseConstant k M₀) (k / 2) H.edgeCount)
    (hsparse : ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      (D - 1) * H.edgeCount < D * H.vertexCount →
      (∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
        graphRamseyNumber (cycleCode k) Q ≤
          oddBudget (oddBaseConstant k M₀) (k / 2) Q.edgeCount) →
      graphRamseyNumber (cycleCode k) H ≤
        oddBudget (oddBaseConstant k M₀) (k / 2) H.edgeCount) :
    StrongOddCycleBound k (oddBaseConstant k M₀) := by
  exact strongOddCycleBound_of_connected_inputs hk
    (oddBaseConstant_half_le k M₀) hD hkM₀ hscale₀
    graphRamseyNumber_cycle_le_oddBudget_base hdense hsparse

/-- A single explicit threshold above every constant required by the dense,
sparse, and middle branches for the odd cycle `C_(2r+3)`. -/
def oddProofThreshold (r : ℕ) : ℕ :=
  max (2 * r + 3)
    (max (oddDenseThreshold (oddSparseD r) (2 * r + 3))
      (max (oddSparseEdgeThreshold r)
        (oddScaleRoot (oddSparseD r) (2 * r + 3) ^ 2)))

theorem odd_cycle_le_oddProofThreshold (r : ℕ) :
    2 * r + 3 ≤ oddProofThreshold r := by
  simp only [oddProofThreshold, le_max_iff]
  exact Or.inl le_rfl

theorem odd_dense_le_oddProofThreshold (r : ℕ) :
    oddDenseThreshold (oddSparseD r) (2 * r + 3) ≤
      oddProofThreshold r := by
  simp only [oddProofThreshold, le_max_iff]
  exact Or.inr (Or.inl le_rfl)

theorem odd_sparse_le_oddProofThreshold (r : ℕ) :
    oddSparseEdgeThreshold r ≤ oddProofThreshold r := by
  simp only [oddProofThreshold, le_max_iff]
  exact Or.inr (Or.inr (Or.inl le_rfl))

theorem odd_scale_sq_le_oddProofThreshold (r : ℕ) :
    oddScaleRoot (oddSparseD r) (2 * r + 3) *
        oddScaleRoot (oddSparseD r) (2 * r + 3) ≤
      oddProofThreshold r := by
  rw [← pow_two]
  simp only [oddProofThreshold, le_max_iff]
  exact Or.inr (Or.inr (Or.inr le_rfl))

/-- The complete strengthened bound for every odd cycle of length at least
five, obtained by instantiating the two connected boundary theorems. -/
theorem strongOddCycleBound_two_mul_add_three
    {r : ℕ} (hr : 1 ≤ r) :
    StrongOddCycleBound (2 * r + 3)
      (oddBaseConstant (2 * r + 3) (oddProofThreshold r)) := by
  apply strongOddCycleBound_of_connected_extremes
  · omega
  · exact oddSparseD_two_le r
  · exact odd_cycle_le_oddProofThreshold r
  · exact odd_scale_sq_le_oddProofThreshold r
  · apply odd_dense_connected_input (by omega) (oddSparseD_two_le r)
    exact odd_dense_le_oddProofThreshold r
  · intro H hH hconn hm hdensity hIH
    let : DecidableRel H.graph.Adj := Classical.decRel _
    have hkhalf : (2 * r + 3) / 2 = r + 1 := by omega
    have hB : r + 1 ≤
        oddBaseConstant (2 * r + 3) (oddProofThreshold r) := by
      rw [← hkhalf]
      exact oddBaseConstant_half_le (2 * r + 3) (oddProofThreshold r)
    rw [hkhalf] at hIH ⊢
    apply graphRamseyNumber_le_of_ramseyAt
    apply ramseyAt_oddBudget_of_sparse_connected
      (r := r)
      (B := oddBaseConstant (2 * r + 3) (oddProofThreshold r))
      hB H hH hconn
    · apply (odd_sparse_le_oddProofThreshold r).trans
      exact hm.le
    · exact hdensity
    · exact hIH

/-- Any strengthened odd-cycle estimate immediately gives the eventual sharp
bound required in Problem 570. -/
theorem eventual_cycle_bound_of_strong {k B : ℕ} (hkodd : k % 2 = 1)
    (hstrong : StrongOddCycleBound k B) :
    ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
      graphRamseyNumber (cycleCode k) H ≤
        2 * H.edgeCount + (k - 1) / 2 := by
  refine ⟨B * B, ?_⟩
  intro H hH hlarge
  have hBsqrt : B ≤ Nat.sqrt H.edgeCount := Nat.le_sqrt.mpr hlarge
  have hsub : B - Nat.sqrt H.edgeCount = 0 := Nat.sub_eq_zero_of_le hBsqrt
  have hkhalf : k / 2 = (k - 1) / 2 := by omega
  simpa [oddBudget, hsub, hkhalf] using hstrong H hH

/-- The eventual sharp bound for every odd cycle of length at least five. -/
theorem eventual_odd_cycle_bound
    {k : ℕ} (hk : 5 ≤ k) (hkodd : k % 2 = 1) :
    ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
      graphRamseyNumber (cycleCode k) H ≤
        2 * H.edgeCount + (k - 1) / 2 := by
  let r := (k - 3) / 2
  have hr : 1 ≤ r := by omega
  have hkform : k = 2 * r + 3 := by
    dsimp only [r]
    omega
  simpa only [hkform] using
    eventual_cycle_bound_of_strong (k := 2 * r + 3) (by omega)
      (strongOddCycleBound_two_mul_add_three hr)

/-! ## Even cycles of length at least six -/

/-- The strengthened induction budget for `C_(2r+4)`.  Its permanent
correction is `r+1 = floor((2r+3)/2)`, exactly the parity term in Problem
570. -/
def StrongEvenCycleBound (r B : ℕ) : Prop :=
  ∀ H : GraphCode, NoIsolated H →
    graphRamseyNumber (cycleCode (2 * r + 4)) H ≤
      oddBudget B (r + 1) H.edgeCount

def evenBaseConstant (r M₀ : ℕ) : ℕ :=
  max (r + 1)
    (graphRamseyNumber (cycleCode (2 * r + 4))
      (completeCode (2 * M₀)) + Nat.sqrt M₀)

theorem evenBaseConstant_parity_le (r M₀ : ℕ) :
    r + 1 ≤ evenBaseConstant r M₀ := by
  simp [evenBaseConstant]

theorem graphRamseyNumber_even_le_budget_base
    {r M₀ : ℕ} (H : GraphCode) (hH : NoIsolated H)
    (hm : H.edgeCount ≤ M₀) :
    graphRamseyNumber (cycleCode (2 * r + 4)) H ≤
      oddBudget (evenBaseConstant r M₀) (r + 1) H.edgeCount := by
  have hn : H.vertexCount ≤ 2 * M₀ :=
    (NoIsolated.vertexCount_le_twice_edgeCount hH).trans
      (Nat.mul_le_mul_left 2 hm)
  have hram := graphRamseyNumber_le_complete_of_vertexCount_le
    (cycleCode (2 * r + 4)) H hn
  have hsqrt : Nat.sqrt H.edgeCount ≤ Nat.sqrt M₀ :=
    Nat.sqrt_le_sqrt hm
  have hconst :
      graphRamseyNumber (cycleCode (2 * r + 4))
          (completeCode (2 * M₀)) + Nat.sqrt M₀ ≤
        evenBaseConstant r M₀ := by
    simp [evenBaseConstant]
  have hsub : graphRamseyNumber (cycleCode (2 * r + 4))
        (completeCode (2 * M₀)) ≤
      evenBaseConstant r M₀ - Nat.sqrt H.edgeCount := by
    omega
  exact hram.trans (by
    unfold oddBudget
    exact hsub.trans ((le_max_left _ _).trans (Nat.le_add_left _ _)))

/-- Strong edge-count induction for an even cycle.  The dense and middle
branches are parity-independent; the sparse branch is supplied by
`ramseyAt_evenBudget_of_sparse_connected`. -/
theorem strongEvenCycleBound_of_connected_inputs
    {r D M₀ : ℕ} (hr : 1 ≤ r) (hD : 2 ≤ D)
    (hkM₀ : 2 * r + 4 ≤ M₀)
    (hscale₀ : oddScaleRoot D (2 * r + 4) *
      oddScaleRoot D (2 * r + 4) ≤ M₀)
    (hdense : ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      H.vertexCount < 2 * D *
        ((2 * r + 4) * Nat.sqrt (2 * H.edgeCount)) →
      graphRamseyNumber (cycleCode (2 * r + 4)) H ≤
        oddBudget (evenBaseConstant r M₀) (r + 1) H.edgeCount)
    (hsparse : ∀ H : GraphCode, NoIsolated H → H.graph.Connected →
      M₀ < H.edgeCount →
      (D - 1) * H.edgeCount < D * H.vertexCount →
      (∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
        graphRamseyNumber (cycleCode (2 * r + 4)) Q ≤
          oddBudget (evenBaseConstant r M₀) (r + 1) Q.edgeCount) →
      graphRamseyNumber (cycleCode (2 * r + 4)) H ≤
        oddBudget (evenBaseConstant r M₀) (r + 1) H.edgeCount) :
    StrongEvenCycleBound r (evenBaseConstant r M₀) := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m →
      NoIsolated Q →
      graphRamseyNumber (cycleCode (2 * r + 4)) Q ≤
        oddBudget (evenBaseConstant r M₀) (r + 1) m by
    simpa using hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Q hQedge hQ
      subst m
      by_cases hm₀ : Q.edgeCount ≤ M₀
      · exact graphRamseyNumber_even_le_budget_base Q hQ hm₀
      have hmLarge : M₀ < Q.edgeCount := Nat.lt_of_not_ge hm₀
      have hIH : ∀ R : GraphCode, NoIsolated R → R.edgeCount < Q.edgeCount →
          graphRamseyNumber (cycleCode (2 * r + 4)) R ≤
            oddBudget (evenBaseConstant r M₀) (r + 1) R.edgeCount := by
        intro R hR hRm
        exact ih R.edgeCount hRm R rfl hR
      rcases connected_or_matching_or_nontrivial_component Q hQ with
        hconn | hmatching | ⟨c, hc₂, hcm⟩
      · let q := Nat.sqrt (2 * Q.edgeCount)
        by_cases hdenseOrder : Q.vertexCount <
            2 * D * ((2 * r + 4) * q)
        · exact hdense Q hQ hconn hmLarge (by simpa [q] using hdenseOrder)
        have hlarge : 2 * D * ((2 * r + 4) * q) ≤ Q.vertexCount :=
          Nat.le_of_not_gt hdenseOrder
        by_cases hsparseDensity :
            (D - 1) * Q.edgeCount < D * Q.vertexCount
        · exact hsparse Q hQ hconn hmLarge hsparseDensity hIH
        have hdensity : D * Q.vertexCount ≤ (D - 1) * Q.edgeCount :=
          Nat.le_of_not_gt hsparseDensity
        have hrootSq : oddScaleRoot D (2 * r + 4) *
            oddScaleRoot D (2 * r + 4) ≤ Q.edgeCount :=
          hscale₀.trans hmLarge.le
        have hscale : oddScaleRoot D (2 * r + 4) ≤
            Nat.sqrt Q.edgeCount := Nat.le_sqrt.mpr hrootSq
        have hq : q = Nat.sqrt (2 * Q.edgeCount) := rfl
        have hmpos : 0 < Q.edgeCount := by omega
        have hqpos : 0 < q := by
          rw [hq, Nat.sqrt_pos]
          omega
        have hn₂ : 2 ≤ Q.vertexCount := by
          have hprodPos : 0 < D * ((2 * r + 4) * q) :=
            Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hqpos)
          have htwo : 2 ≤ 2 * (D * ((2 * r + 4) * q)) := by omega
          exact htwo.trans (by simpa [mul_assoc] using hlarge)
        have hhalf : 2 * ((2 * r + 4) * q) ≤ Q.vertexCount := by
          have hcoeff : 2 ≤ 2 * D := by omega
          have hle := Nat.mul_le_mul_right ((2 * r + 4) * q) hcoeff
          have hsmallLarge : 2 * ((2 * r + 4) * q) ≤
              2 * D * ((2 * r + 4) * q) := by
            simpa [mul_assoc] using hle
          exact hsmallLarge.trans hlarge
        have hnm : Q.vertexCount ≤ Q.edgeCount := by
          by_contra hnot
          have hmn : Q.edgeCount < Q.vertexCount := Nat.lt_of_not_ge hnot
          have hlt : D * Q.edgeCount < D * Q.vertexCount :=
            Nat.mul_lt_mul_of_pos_left hmn (by omega)
          have hcoef : D - 1 ≤ D := Nat.sub_le D 1
          have hle : (D - 1) * Q.edgeCount ≤ D * Q.edgeCount :=
            Nat.mul_le_mul_right Q.edgeCount hcoef
          omega
        have hgap : 4 * ((2 * r + 4) * q) + Nat.sqrt Q.edgeCount ≤
            Q.edgeCount - Q.vertexCount :=
          odd_gap_of_scale_and_density (by omega) hq hscale hdensity
        have hroom : OddMiddleRoom (evenBaseConstant r M₀) (r + 1)
            (2 * r + 4) Q.edgeCount Q.vertexCount q :=
          oddMiddleRoom_of_gap (by omega) hq hqpos hn₂ hhalf hgap
        apply graphRamseyNumber_le_of_ramseyAt
        intro C
        classical
        let : DecidableRel C.Adj := Classical.decRel _
        by_cases hred : (cycleCode (2 * r + 4)).graph ⊑ C
        · exact Or.inl hred
        by_cases hblue : Q.graph ⊑ Cᶜ
        · exact Or.inr hblue
        exact (odd_connected_middle_contradiction
          (H := Q) (B := evenBaseConstant r M₀) (s := r + 1)
          (k := 2 * r + 4) (D := D) (q := q)
          (by omega) hQ hconn hq (evenBaseConstant_parity_le r M₀)
          hD hnm hlarge hdensity hroom hIH C hred hblue).elim
      · have hkm : 2 * r + 4 ≤ Q.edgeCount := hkM₀.trans hmLarge.le
        have hmatchBound := graphRamseyNumber_cycle_matching_le
          (by omega : 3 ≤ 2 * r + 4) hkm
        have hiso : graphRamseyNumber (cycleCode (2 * r + 4)) Q =
            graphRamseyNumber (cycleCode (2 * r + 4))
              (matchingCode Q.edgeCount) := by
          rw [graphRamseyNumber_congr Isomorphic.rfl hmatching]
        rw [hiso]
        exact hmatchBound.trans (by
          unfold oddBudget
          omega)
      · apply graphRamseyNumber_le_of_ramseyAt
        exact ramseyAt_oddBudget_of_nontrivial_component hQ rfl c hc₂ hcm hIH

def evenProofThreshold (r : ℕ) : ℕ :=
  max (2 * r + 4)
    (max (oddDenseThreshold (oddSparseD (r + 1)) (2 * r + 4))
      (max (oddSparseEdgeThreshold (r + 1))
        (oddScaleRoot (oddSparseD (r + 1)) (2 * r + 4) ^ 2)))

theorem strongEvenCycleBound_two_mul_add_four {r : ℕ} (hr : 1 ≤ r) :
    StrongEvenCycleBound r (evenBaseConstant r (evenProofThreshold r)) := by
  apply strongEvenCycleBound_of_connected_inputs hr
    (oddSparseD_two_le (r + 1))
  · simp [evenProofThreshold]
  · rw [← pow_two]
    simp only [evenProofThreshold, le_max_iff]
    exact Or.inr (Or.inr (Or.inr le_rfl))
  · apply odd_dense_connected_input (s := r + 1) (by omega)
      (oddSparseD_two_le (r + 1))
    simp only [evenProofThreshold, le_max_iff]
    exact Or.inr (Or.inl le_rfl)
  · intro H hH hconn hm hdensity hIH
    let : DecidableRel H.graph.Adj := Classical.decRel _
    apply graphRamseyNumber_le_of_ramseyAt
    apply ramseyAt_evenBudget_of_sparse_connected H hH hconn
    · apply (show oddSparseEdgeThreshold (r + 1) ≤
          evenProofThreshold r by
        simp only [evenProofThreshold, le_max_iff]
        exact Or.inr (Or.inr (Or.inl le_rfl))).trans hm.le
    · exact hdensity
    · exact hIH

theorem eventual_even_cycle_bound_six_le
    {k : ℕ} (hk : 6 ≤ k) (hkeven : k % 2 = 0) :
    ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
      graphRamseyNumber (cycleCode k) H ≤
        2 * H.edgeCount + (k - 1) / 2 := by
  let r := (k - 4) / 2
  have hr : 1 ≤ r := by omega
  have hkform : k = 2 * r + 4 := by
    dsimp only [r]
    omega
  let B := evenBaseConstant r (evenProofThreshold r)
  refine ⟨B * B, ?_⟩
  intro H hH hlarge
  have hBsqrt : B ≤ Nat.sqrt H.edgeCount := Nat.le_sqrt.mpr hlarge
  have hsub : B - Nat.sqrt H.edgeCount = 0 := Nat.sub_eq_zero_of_le hBsqrt
  have hstrong := strongEvenCycleBound_two_mul_add_four hr H hH
  rw [hkform]
  have hhalf : (2 * r + 4 - 1) / 2 = r + 1 := by omega
  rw [hhalf]
  simpa [B, oddBudget, hsub] using hstrong

/-! ## The exceptional quadrilateral -/

/-- A threshold sufficient for the sparse `C₄` branch and the finite base. -/
def c4ProofThreshold : ℕ :=
  max 4 (oddSparseEdgeThreshold 1)

/-- The strengthened `C₄` estimate.  In the sparse regime it is the
specialization `r=0` of the even suspended-path/leaf argument.  Outside that
regime the target has a vertex of degree at least three, and the direct
quadrilateral deletion lemma closes the induction. -/
theorem strongC4Bound :
    ∀ H : GraphCode, NoIsolated H →
      graphRamseyNumber (cycleCode 4) H ≤
        oddBudget (evenBaseConstant 0 c4ProofThreshold) 1 H.edgeCount := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m →
      NoIsolated Q →
      graphRamseyNumber (cycleCode 4) Q ≤
        oddBudget (evenBaseConstant 0 c4ProofThreshold) 1 m by
    simpa using hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Q hQedge hQ
      subst m
      by_cases hm₀ : Q.edgeCount ≤ c4ProofThreshold
      · simpa using graphRamseyNumber_even_le_budget_base
          (r := 0) Q hQ hm₀
      have hmLarge : c4ProofThreshold < Q.edgeCount := Nat.lt_of_not_ge hm₀
      have hIH : ∀ R : GraphCode, NoIsolated R →
          R.edgeCount < Q.edgeCount →
          graphRamseyNumber (cycleCode 4) R ≤
            oddBudget (evenBaseConstant 0 c4ProofThreshold) 1 R.edgeCount := by
        intro R hR hRm
        simpa using ih R.edgeCount hRm R rfl hR
      rcases connected_or_matching_or_nontrivial_component Q hQ with
        hconn | hmatching | ⟨c, hc₂, hcm⟩
      · let : DecidableRel Q.graph.Adj := Classical.decRel _
        by_cases hsparseDensity :
            (oddSparseD 1 - 1) * Q.edgeCount <
              oddSparseD 1 * Q.vertexCount
        · apply graphRamseyNumber_le_of_ramseyAt
          apply ramseyAt_evenBudget_of_sparse_connected (r := 0) Q hQ hconn
          · exact (show oddSparseEdgeThreshold 1 ≤ c4ProofThreshold by
              simp [c4ProofThreshold]).trans hmLarge.le
          · exact hsparseDensity
          · exact hIH
        · have hdensity : oddSparseD 1 * Q.vertexCount ≤
              (oddSparseD 1 - 1) * Q.edgeCount :=
            Nat.le_of_not_gt hsparseDensity
          have hD : 2 ≤ oddSparseD 1 := oddSparseD_two_le 1
          have hnpos : 0 < Q.vertexCount := by
            have : 0 < Fintype.card (Fin Q.vertexCount) :=
              Fintype.card_pos_iff.mpr hconn.nonempty
            simpa using this
          have horder : Q.vertexCount ≤ Q.edgeCount := by
            by_contra hnot
            have hmle : Q.edgeCount < Q.vertexCount := Nat.lt_of_not_ge hnot
            have hcoef : oddSparseD 1 - 1 < oddSparseD 1 := by omega
            have hstrict : (oddSparseD 1 - 1) * Q.edgeCount <
                oddSparseD 1 * Q.vertexCount := by
              calc
                (oddSparseD 1 - 1) * Q.edgeCount ≤
                    (oddSparseD 1 - 1) * Q.vertexCount :=
                  Nat.mul_le_mul_left _ hmle.le
                _ < oddSparseD 1 * Q.vertexCount :=
                  Nat.mul_lt_mul_of_pos_right hcoef hnpos
            omega
          have hexists : ∃ v : Fin Q.vertexCount,
              3 ≤ Q.graph.degree v := by
            by_contra hnot
            push_neg at hnot
            have hsumLe : ∑ v : Fin Q.vertexCount, Q.graph.degree v ≤
                ∑ _v : Fin Q.vertexCount, 2 := by
              exact Finset.sum_le_sum fun v _ ↦ by
                have hv := hnot v
                omega
            have hsum := Q.graph.sum_degrees_eq_twice_card_edges
            have htwom : ∑ v : Fin Q.vertexCount, Q.graph.degree v =
                2 * Q.edgeCount := by
              rw [hsum, ← GraphCode.edgeCount_eq_card_edgeFinset]
            have hmle : Q.edgeCount ≤ Q.vertexCount := by
              rw [htwom] at hsumLe
              simp only [Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, Nat.nsmul_eq_mul] at hsumLe
              omega
            have hcoef : oddSparseD 1 - 1 < oddSparseD 1 := by omega
            have hstrict : (oddSparseD 1 - 1) * Q.edgeCount <
                oddSparseD 1 * Q.vertexCount := by
              calc
                (oddSparseD 1 - 1) * Q.edgeCount ≤
                    (oddSparseD 1 - 1) * Q.vertexCount :=
                  Nat.mul_le_mul_left _ hmle
                _ < oddSparseD 1 * Q.vertexCount :=
                  Nat.mul_lt_mul_of_pos_right hcoef hnpos
            omega
          obtain ⟨v, hv⟩ := hexists
          apply graphRamseyNumber_le_of_ramseyAt
          exact ramseyAt_c4_of_deletable_vertex Q v hv horder hIH
      · have hkm : 4 ≤ Q.edgeCount := by
          exact (show 4 ≤ c4ProofThreshold by simp [c4ProofThreshold]).trans
            hmLarge.le
        have hmatchBound := graphRamseyNumber_cycle_matching_le
          (by omega : 3 ≤ 4) hkm
        have hiso : graphRamseyNumber (cycleCode 4) Q =
            graphRamseyNumber (cycleCode 4) (matchingCode Q.edgeCount) := by
          rw [graphRamseyNumber_congr Isomorphic.rfl hmatching]
        rw [hiso]
        exact hmatchBound.trans (by unfold oddBudget; omega)
      · apply graphRamseyNumber_le_of_ramseyAt
        exact ramseyAt_oddBudget_of_nontrivial_component hQ rfl c hc₂ hcm hIH

/-- The sharp eventual bound for the quadrilateral. -/
theorem eventual_c4_bound :
    ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
      graphRamseyNumber (cycleCode 4) H ≤
        2 * H.edgeCount + (4 - 1) / 2 := by
  let B := evenBaseConstant 0 c4ProofThreshold
  refine ⟨B * B, ?_⟩
  intro H hH hlarge
  have hBsqrt : B ≤ Nat.sqrt H.edgeCount := Nat.le_sqrt.mpr hlarge
  have hsub : B - Nat.sqrt H.edgeCount = 0 := Nat.sub_eq_zero_of_le hBsqrt
  simpa [B, oddBudget, hsub] using strongC4Bound H hH

/-! ## The exceptional triangle -/

/-- A concrete finite base beyond the arithmetic thresholds in the
Goddard--Kleitman triangle argument. -/
def triangleProofThreshold : ℕ := 46

/-- The strengthened triangle estimate.  The connected case is split by a
minimum-degree vertex.  A leaf is restored directly; independent
minimum-degree vertices are handled by the candidate-set argument (with the
degree-two endpoint treated separately); adjacent minimum-degree vertices
are contracted. -/
theorem strongTriangleBound :
    StrongOddCycleBound 3 (oddBaseConstant 3 triangleProofThreshold) := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m →
      NoIsolated Q →
      graphRamseyNumber (cycleCode 3) Q ≤
        oddBudget (oddBaseConstant 3 triangleProofThreshold) 1 m by
    simpa using hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Q hQedge hQ
      subst m
      by_cases hm₀ : Q.edgeCount ≤ triangleProofThreshold
      · simpa using graphRamseyNumber_cycle_le_oddBudget_base
          (k := 3) Q hQ hm₀
      have hmLarge : triangleProofThreshold < Q.edgeCount :=
        Nat.lt_of_not_ge hm₀
      have hIH : ∀ R : GraphCode, NoIsolated R →
          R.edgeCount < Q.edgeCount →
          graphRamseyNumber (cycleCode 3) R ≤
            oddBudget (oddBaseConstant 3 triangleProofThreshold) 1 R.edgeCount := by
        intro R hR hRm
        simpa using ih R.edgeCount hRm R rfl hR
      rcases connected_or_matching_or_nontrivial_component Q hQ with
        hconn | hmatching | ⟨c, hc₂, hcm⟩
      · classical
        let : DecidableRel Q.graph.Adj := Classical.decRel _
        let : Nonempty (Fin Q.vertexCount) := hconn.nonempty
        obtain ⟨v, hvmin'⟩ := Q.graph.exists_minimal_degree_vertex
        have hvmin : Q.graph.degree v = Q.graph.minDegree := hvmin'.symm
        have hδpos : 0 < Q.graph.degree v := (Q.graph.degree_pos v).mpr (hQ v)
        let R := supportCode (deleteVertexCode Q v)
        have hRedge : R.edgeCount =
            Q.edgeCount - Q.graph.degree v := by
          simp [R, deleteVertexCode_edgeCount]
        have hRlt : R.edgeCount < Q.edgeCount := by
          rw [hRedge]
          omega
        have hRram : graphRamseyNumber (cycleCode 3) R ≤
            oddBudget (oddBaseConstant 3 triangleProofThreshold) 1 Q.edgeCount :=
          (hIH R (supportCode_noIsolated _) hRlt).trans
            (oddBudget_mono hRlt.le)
        have hdelete : RamseyAt (cycleCode 3) R
            (oddBudget (oddBaseConstant 3 triangleProofThreshold) 1
              Q.edgeCount) := ramseyAt_of_graphRamseyNumber_le hRram
        apply graphRamseyNumber_le_of_ramseyAt
        intro C
        let : DecidableRel C.Adj := Classical.decRel _
        by_cases hred : (cycleCode 3).graph ⊑ C
        · exact Or.inl hred
        by_cases hblue : Q.graph ⊑ Cᶜ
        · exact Or.inr hblue
        have hN : 2 * Q.edgeCount + 1 ≤
            oddBudget (oddBaseConstant 3 triangleProofThreshold) 1
              Q.edgeCount := by
          unfold oddBudget
          omega
        by_cases hδ1 : Q.graph.degree v = 1
        · exact (triangle_degree_one_contradiction C hQ hconn hN v hδ1
            (by simpa [R] using hdelete) hred hblue).elim
        have hδ2 : 2 ≤ Q.graph.degree v := by omega
        let S := minimumDegreeVertices Q.graph v
        by_cases hSind : Q.graph.IsIndepSet
            (S : Set (Fin Q.vertexCount))
        · by_cases hδeq : Q.graph.degree v = 2
          · exact (triangle_independent_degree_two_contradiction
              C hQ hN v hvmin hδeq
              (by simpa [triangleProofThreshold] using hmLarge.le)
              (by simpa [S] using hSind) (by simpa [R] using hdelete)
              hred hblue).elim
          · have hδ3 : 3 ≤ Q.graph.degree v := by omega
            exact (triangle_independent_minimum_contradiction
              C hQ hN v hvmin hδ3
              (by have : 22 ≤ triangleProofThreshold := by
                    simp [triangleProofThreshold]
                  exact this.trans hmLarge.le)
              (by simpa [S] using hSind) (by simpa [R] using hdelete)
              hred hblue).elim
        · rw [SimpleGraph.isIndepSet_iff, Set.Pairwise] at hSind
          push Not at hSind
          obtain ⟨u, huS, w, hwS, huw, huwAdj⟩ := hSind
          have humin : Q.graph.degree u = Q.graph.minDegree := by
            calc
              Q.graph.degree u = Q.graph.degree v :=
                (mem_minimumDegreeVertices Q.graph v u).mp (by simpa [S] using huS)
              _ = Q.graph.minDegree := hvmin
          have hwdeg : Q.graph.degree w = Q.graph.degree u := by
            calc
              Q.graph.degree w = Q.graph.degree v :=
                (mem_minimumDegreeVertices Q.graph v w).mp (by simpa [S] using hwS)
              _ = Q.graph.degree u := by rw [humin, hvmin]
          let K := contractionCode Q.graph u w
          have hKno : NoIsolated K := by
            dsimp only [K]
            exact contractionCode_noIsolated Q.graph huwAdj hQ
              (by rw [humin, ← hvmin]; exact hδ2)
          have hKlt : K.edgeCount < Q.edgeCount := by
            dsimp only [K]
            simpa [GraphCode.edgeCount_eq_card_edgeFinset] using
              contractionCode_edgeCount_lt Q.graph huwAdj
          have hKram : graphRamseyNumber (cycleCode 3) K ≤
              oddBudget (oddBaseConstant 3 triangleProofThreshold) 1
                Q.edgeCount :=
            (hIH K hKno hKlt).trans (oddBudget_mono hKlt.le)
          have hKalt := (ramseyAt_of_graphRamseyNumber_le hKram) C
          have hKblue : K.graph ⊑ Cᶜ := hKalt.resolve_left hred
          have hcopy : contractionGraph Q.graph u w ⊑ Cᶜ := by
            apply (recodeGraph_isContained_iff
              (contractionGraph Q.graph u w) Cᶜ).mp
            simpa [K, contractionCode] using hKblue
          exact (triangle_adjacent_contraction_contradiction
            C hQ hN u w huwAdj humin hwdeg
            (by rw [humin, ← hvmin]; exact hδ2)
            hcopy hred hblue).elim
      · have hkm : 3 ≤ Q.edgeCount := by
          have : 3 ≤ triangleProofThreshold := by simp [triangleProofThreshold]
          exact this.trans hmLarge.le
        have hmatchBound := graphRamseyNumber_cycle_matching_le
          (by omega : 3 ≤ 3) hkm
        have hiso : graphRamseyNumber (cycleCode 3) Q =
            graphRamseyNumber (cycleCode 3) (matchingCode Q.edgeCount) := by
          rw [graphRamseyNumber_congr Isomorphic.rfl hmatching]
        rw [hiso]
        exact hmatchBound.trans (by unfold oddBudget; omega)
      · apply graphRamseyNumber_le_of_ramseyAt
        exact ramseyAt_oddBudget_of_nontrivial_component hQ rfl c hc₂ hcm hIH

/-- The sharp eventual bound for the triangle. -/
theorem eventual_triangle_bound :
    ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
      graphRamseyNumber (cycleCode 3) H ≤
        2 * H.edgeCount + (3 - 1) / 2 := by
  let B := oddBaseConstant 3 triangleProofThreshold
  refine ⟨B * B, ?_⟩
  intro H hH hlarge
  have hBsqrt : B ≤ Nat.sqrt H.edgeCount := Nat.le_sqrt.mpr hlarge
  have hsub : B - Nat.sqrt H.edgeCount = 0 := Nat.sub_eq_zero_of_le hBsqrt
  simpa [B, oddBudget, hsub] using strongTriangleBound H hH

/-- The exact formal statement of Erdős Problem 570.

Natural-number division is the floor in the displayed paper statement.  The threshold
depends on `k` and is uniform over all coded finite graphs `H` satisfying the two stated
hypotheses. -/
def Erdős570Statement : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
      graphRamseyNumber (cycleCode k) H ≤
        2 * H.edgeCount + (k - 1) / 2

theorem erdos570_statement_iff : Erdős570Statement ↔
    ∀ k : ℕ, 3 ≤ k →
      ∃ M : ℕ, ∀ H : GraphCode, NoIsolated H → M ≤ H.edgeCount →
        graphRamseyNumber (cycleCode k) H ≤
          2 * H.edgeCount + (k - 1) / 2 := by
  rfl

/-- Resolution of Erdős Problem 570. -/
theorem erdos_570 : (∀ k : ℕ, 3 ≤ k →
  ∃ M : ℕ, ∀ H : Erdos79.GraphCode, Erdos79.NoIsolated H → M ≤ H.edgeCount →
    Erdos79.graphRamseyNumber (Erdos570.cycleCode k) H ≤
      2 * H.edgeCount + (k - 1) / 2) := by
  intro k hk
  by_cases hk3 : k = 3
  · subst k
    exact eventual_triangle_bound
  by_cases hk4 : k = 4
  · subst k
    exact eventual_c4_bound
  have hk5 : 5 ≤ k := by omega
  by_cases hkeven : k % 2 = 0
  · exact eventual_even_cycle_bound_six_le (by omega) hkeven
  · have hkodd : k % 2 = 1 := by omega
    exact eventual_odd_cycle_bound hk5 hkodd

#print axioms erdos_570

end Erdos570

alias _root_.Erdos570.erdos570 := _root_.Erdos570.erdos_570
