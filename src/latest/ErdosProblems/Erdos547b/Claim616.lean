/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.GallaiEdmonds
import ErdosProblems.Erdos547b.Claim616SourceBridge
import ErdosProblems.Erdos547b.Claim617BranchCount
import ErdosProblems.Erdos547b.Claim61RichFull
import ErdosProblems.Erdos547b.Claim65QuantitativeRoots
import ErdosProblems.Erdos547b.Lemma611Full
import ErdosProblems.Erdos547b.Lemma611RootAccess
import ErdosProblems.Erdos547b.LargeClusterReservoir
import ErdosProblems.Erdos547b.Section6Dichotomy
import ErdosProblems.Erdos547b.Stability

/-!
# Zhao's Claim 6.16: the reduced-graph counting step

This file formalizes the finite part of Claim 6.16 in Yi Zhao's proof of the
large `(n/2,n/2,n/2)` conjecture.  The key output is the actual cluster set
`C` used in display (6.22): it has the prescribed cardinality and every one
of its vertices still has the required reduced degree after the exceptional
submatching is deleted.

The host theorems below keep the reduced graph definitionally tied to an
actual regularity reduced graph.  They expose the concrete uniform dense
pairs and genuine matching edges needed by Lemma 5.9; no proposition-valued
embedding premise or abstract dichotomy is assumed.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616

open Finset SimpleGraph
open Erdos547EC2
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoLemma611RootAccess
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma65QuantitativeRoots
open Erdos547b.ZhaoSection6Dichotomy

universe u v

/-! ### Surviving matching edges and their canonical orientation -/

/-- Matching edges having an endpoint in `W` adjacent to `C`. -/
def matchingAccessEdges
    {E : Type*} [DecidableEq E] {ι : Type*} [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → ι)
    (C : ι) (W : Finset ι) : Finset E :=
  M.filter fun e ↦
    (endpoint e 0 ∈ W ∧ R.Adj C (endpoint e 0)) ∨
      (endpoint e 1 ∈ W ∧ R.Adj C (endpoint e 1))

def matchingEdgeEndpoint {ι : Type*} (e : Sym2 ι) (c : Fin 2) : ι :=
  if c = 0 then e.out.1 else e.out.2

theorem matchingEdgeEndpoint_pair_eq {ι : Type*} (e : Sym2 ι) :
    s(matchingEdgeEndpoint e 0, matchingEdgeEndpoint e 1) = e := by
  simp [matchingEdgeEndpoint, Sym2.mk, e.out_eq]

/-- Orient access so the side displayed by Lemma 5.9 is an endpoint in
`W` adjacent to `C`. -/
def matchingAccessSide
    {E : Type*} {ι : Type*} [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (endpoint : E → Fin 2 → ι) (C : ι) (W : Finset ι)
    (e : E) : Fin 2 :=
  if endpoint e 0 ∈ W ∧ R.Adj C (endpoint e 0) then 1 else 0

theorem matchingAccessSide_spec
    {E : Type*} [DecidableEq E] {ι : Type*} [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → ι)
    (C : ι) (W : Finset ι) (e : E)
    (he : e ∈ matchingAccessEdges R M endpoint C W) :
    let side := matchingAccessSide R endpoint C W e
    let y := if side = 0 then endpoint e 1 else endpoint e 0
    y ∈ W ∧ R.Adj C y := by
  have he' := (mem_filter.mp he).2
  by_cases hzero : endpoint e 0 ∈ W ∧ R.Adj C (endpoint e 0)
  · simpa [matchingAccessSide, hzero] using hzero
  · have hone : endpoint e 1 ∈ W ∧ R.Adj C (endpoint e 1) :=
      he'.resolve_left hzero
    simpa [matchingAccessSide, hzero] using hone

theorem matchingEdgeEndpoint_adj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} (M : R.Subgraph) (e : Sym2 ι)
    (he : e ∈ M.edgeSet) :
    R.Adj (matchingEdgeEndpoint e 0) (matchingEdgeEndpoint e 1) := by
  apply M.adj_sub
  rw [← Subgraph.mem_edgeSet, matchingEdgeEndpoint_pair_eq]
  exact he

theorem matchingSupport_covered_by_edgeEndpoints
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} (M : R.Subgraph) (hM : M.IsMatching)
    (v : ι) (hv : v ∈ matchingSupport M) :
    ∃ e ∈ M.edgeSet.toFinite.toFinset,
      v = matchingEdgeEndpoint e 0 ∨ v = matchingEdgeEndpoint e 1 := by
  classical
  have hvVerts : v ∈ M.verts := (mem_matchingSupport M v).mp hv
  obtain ⟨w, hvw, _⟩ := hM hvVerts
  let e : Sym2 ι := s(v, w)
  have heM : e ∈ M.edgeSet := (Subgraph.mem_edgeSet).2 hvw
  refine ⟨e, by simpa using heM, ?_⟩
  have hvmem : v ∈ e := by simp [e]
  rw [← e.out_eq, Sym2.mem_iff] at hvmem
  simpa [matchingEdgeEndpoint] using hvmem

/-- The same support coverage expressed in the source orientation used by
the matching-decomposition construction. -/
theorem matchingSupport_covered_by_orientedEndpoints
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} (M : R.Subgraph) (hM : M.IsMatching)
    (L : Finset I) (v : I) (hv : v ∈ matchingSupport M) :
    ∃ e : MatchingEdge M,
      v = orientedEndpoint M L e 0 ∨ v = orientedEndpoint M L e 1 := by
  classical
  obtain ⟨e, he, hv0 | hv1⟩ :=
    matchingSupport_covered_by_edgeEndpoints M hM v hv
  · let e' : MatchingEdge M :=
      ⟨e, M.edgeSet.toFinite.mem_toFinset.mp he⟩
    refine ⟨e', ?_⟩
    have hve : v ∈ e'.1 := by
      change v ∈ e
      rw [← matchingEdgeEndpoint_pair_eq e, hv0]
      simp
    rw [← orientedEndpoint_pair_eq M L e', Sym2.mem_iff] at hve
    exact hve
  · let e' : MatchingEdge M :=
      ⟨e, M.edgeSet.toFinite.mem_toFinset.mp he⟩
    refine ⟨e', ?_⟩
    have hve : v ∈ e'.1 := by
      change v ∈ e
      rw [← matchingEdgeEndpoint_pair_eq e, hv1]
      simp
    rw [← orientedEndpoint_pair_eq M L e', Sym2.mem_iff] at hve
    exact hve

theorem matchingEdgeEndpoint_mem_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} (M : R.Subgraph) (e : Sym2 ι)
    (he : e ∈ M.edgeSet) (c : Fin 2) :
    matchingEdgeEndpoint e c ∈ matchingSupport M := by
  have hadj : M.Adj (matchingEdgeEndpoint e 0)
      (matchingEdgeEndpoint e 1) := by
    rw [← Subgraph.mem_edgeSet, matchingEdgeEndpoint_pair_eq]
    exact he
  fin_cases c
  · exact (mem_matchingSupport M _).mpr hadj.fst_mem
  · exact (mem_matchingSupport M _).mpr hadj.snd_mem

/-- Eight surviving endpoint incidences give at least four genuine matching
edges. -/
theorem four_mul_le_card_matchingAccessEdges
    {E : Type*} [DecidableEq E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → ι)
    (C : ι) (W : Finset ι) (rhoK : ℕ)
    (hcovered : ∀ v ∈ W, ∃ e ∈ M,
      v = endpoint e 0 ∨ v = endpoint e 1)
    (hdegree : 8 * rhoK ≤ degreeInto R C W) :
    4 * rhoK ≤ (matchingAccessEdges R M endpoint C W).card := by
  classical
  let N := W.filter (R.Adj C)
  let A := matchingAccessEdges R M endpoint C W
  let occurrences : Finset (E × Fin 2) := A ×ˢ Finset.univ
  let value : E × Fin 2 → ι := fun ec ↦ endpoint ec.1 ec.2
  have hsubset : N ⊆ occurrences.image value := by
    intro v hv
    have hvW := (mem_filter.mp hv).1
    have hvAdj := (mem_filter.mp hv).2
    obtain ⟨e, heM, he0 | he1⟩ := hcovered v hvW
    · apply mem_image.mpr
      refine ⟨(e, 0), ?_, by simpa [value] using he0.symm⟩
      exact mem_product.mpr ⟨mem_filter.mpr
        ⟨heM, Or.inl ⟨he0 ▸ hvW, he0 ▸ hvAdj⟩⟩, mem_univ _⟩
    · apply mem_image.mpr
      refine ⟨(e, 1), ?_, by simpa [value] using he1.symm⟩
      exact mem_product.mpr ⟨mem_filter.mpr
        ⟨heM, Or.inr ⟨he1 ▸ hvW, he1 ▸ hvAdj⟩⟩, mem_univ _⟩
  have hupper : N.card ≤ 2 * A.card := by
    calc
      N.card ≤ (occurrences.image value).card := card_le_card hsubset
      _ ≤ occurrences.card := card_image_le
      _ = 2 * A.card := by simp [occurrences, mul_comm]
  have hlower : 8 * rhoK ≤ N.card := by
    simpa [N, degreeInto] using hdegree
  simpa [A] using (show 4 * rhoK ≤ A.card by omega)

theorem four_mul_le_card_genuineMatchingAccessEdges
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching)
    (C : ι) (W : Finset ι) (rhoK : ℕ)
    (hW : W ⊆ matchingSupport M)
    (hdegree : 8 * rhoK ≤ degreeInto R C W) :
    4 * rhoK ≤
      (matchingAccessEdges R M.edgeSet.toFinite.toFinset
        matchingEdgeEndpoint C W).card := by
  apply four_mul_le_card_matchingAccessEdges R
    M.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W rhoK
  · intro v hv
    exact matchingSupport_covered_by_edgeEndpoints M hM v (hW hv)
  · exact hdegree

/-- An accessible reduced edge is the actual uniform dense host pair needed
by Lemma 5.9. -/
theorem uniform_dense_accessPair
    {E : Type*} [DecidableEq E]
    {B ι : Type*} [DecidableEq ι]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : ι → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (M : Finset E) (endpoint : E → Fin 2 → ι)
    (C : ι) (W : Finset ι) (e : E)
    (he : e ∈ matchingAccessEdges
      (regularityReducedGraph G cluster epsilon density) M endpoint C W) :
    let side := matchingAccessSide
      (regularityReducedGraph G cluster epsilon density) endpoint C W e
    let y := if side = 0 then endpoint e 1 else endpoint e 0
    G.IsUniform epsilon (cluster C) (cluster y) ∧
      density ≤ G.edgeDensity (cluster C) (cluster y) := by
  have hspec := matchingAccessSide_spec
    (regularityReducedGraph G cluster epsilon density) M endpoint C W e he
  exact ⟨hspec.2.2.1, hspec.2.2.2⟩

/-- Every genuine matching edge in the reduced graph yields its actual host
regular pair. -/
theorem uniform_dense_matchingPair
    {B ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : ι → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Sym2 ι) (he : e ∈ M.edgeSet) :
    G.IsUniform epsilon
        (cluster (matchingEdgeEndpoint e 0))
        (cluster (matchingEdgeEndpoint e 1)) ∧
      density ≤ G.edgeDensity
        (cluster (matchingEdgeEndpoint e 0))
        (cluster (matchingEdgeEndpoint e 1)) := by
  have hadj := matchingEdgeEndpoint_adj M e he
  exact ⟨hadj.2.1, hadj.2.2⟩

/-! ### Canonical finite indexing for Lemma 5.9(2) -/

/-- The canonical enumeration of a finite set by a `Fin` type of the same
cardinality.  Keeping this definition local to Claim 6.16 makes the later
`Fin c`/`Fin k` specialization definitionally tied to the selected clusters
and the genuine surviving matching edges. -/
noncomputable def finsetValue {A : Type*} [DecidableEq A]
    (s : Finset A) (i : Fin s.card) : A :=
  ((Finset.equivFin s).symm i).1

/-- The host cluster at a canonical selected-cluster index. -/
def indexedCluster {B I : Type*} [DecidableEq I] (cluster : I → Finset B)
    (C : Finset I) (i : Fin C.card) : Finset B :=
  cluster (finsetValue C i)

/-- One endpoint cluster of a canonically indexed matching edge. -/
def indexedMatchingSide {B I : Type*} [DecidableEq I]
    (cluster : I → Finset B)
    (M : Finset (Sym2 I)) (e : Fin M.card) (side : Fin 2) : Finset B :=
  cluster (matchingEdgeEndpoint (finsetValue M e) side)

theorem finsetValue_mem {A : Type*} [DecidableEq A]
    (s : Finset A) (i : Fin s.card) :
    finsetValue s i ∈ s :=
  ((Finset.equivFin s).symm i).2

theorem finsetValue_injective {A : Type*} [DecidableEq A] (s : Finset A) :
    Function.Injective (finsetValue s) := by
  intro i j hij
  apply (Finset.equivFin s).symm.injective
  exact Subtype.ext hij

theorem finsetValue_surjective {A : Type*} [DecidableEq A]
    (s : Finset A) :
    ∀ x ∈ s, ∃ i : Fin s.card, finsetValue s i = x := by
  intro x hx
  refine ⟨Finset.equivFin s ⟨x, hx⟩, ?_⟩
  simp [finsetValue]

/-- The subtype-valued genuine edge behind a canonical matching index. -/
def indexedMatchingEdge
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} (M : R.Subgraph)
    (e : Fin M.edgeSet.toFinite.toFinset.card) : MatchingEdge M :=
  ⟨finsetValue M.edgeSet.toFinite.toFinset e,
    M.edgeSet.toFinite.mem_toFinset.mp
      (finsetValue_mem M.edgeSet.toFinite.toFinset e)⟩

/-- The two endpoint occurrences of the canonically indexed genuine matching
edges are all distinct. -/
theorem indexedMatchingEndpoint_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching) :
    Function.Injective (fun ec :
        Fin M.edgeSet.toFinite.toFinset.card × Fin 2 ↦
      matchingEdgeEndpoint
        (finsetValue M.edgeSet.toFinite.toFinset ec.1) ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ hendpoint
  let flip : Fin 2 → Fin 2 := fun q ↦ if q = 0 then 1 else 0
  have horiented (j : Fin M.edgeSet.toFinite.toFinset.card) (q : Fin 2) :
      orientedEndpoint M ∅ (indexedMatchingEdge M j) (flip q) =
        matchingEdgeEndpoint (finsetValue M.edgeSet.toFinite.toFinset j) q := by
    fin_cases q <;>
      simp [flip, indexedMatchingEdge, orientedEndpoint, rawEndpoint,
        matchingEdgeEndpoint]
  have horientedEq :
      orientedEndpoint M ∅ (indexedMatchingEdge M e) (flip c) =
        orientedEndpoint M ∅ (indexedMatchingEdge M f) (flip d) := by
    calc
      orientedEndpoint M ∅ (indexedMatchingEdge M e) (flip c) =
          matchingEdgeEndpoint
            (finsetValue M.edgeSet.toFinite.toFinset e) c := horiented e c
      _ = matchingEdgeEndpoint
            (finsetValue M.edgeSet.toFinite.toFinset f) d := hendpoint
      _ = orientedEndpoint M ∅ (indexedMatchingEdge M f) (flip d) :=
        (horiented f d).symm
  have h :
      (indexedMatchingEdge M e, flip c) =
        (indexedMatchingEdge M f, flip d) := by
    apply orientedEndpoint_injective M hM (∅ : Finset I)
    exact horientedEq
  have hedge : e = f := by
    apply finsetValue_injective M.edgeSet.toFinite.toFinset
    exact congrArg (fun z : MatchingEdge M × Fin 2 ↦ z.1.1) h
  subst f
  have hside : c = d := by
    have hf := congrArg (fun z : MatchingEdge M × Fin 2 ↦ z.2) h
    fin_cases c <;> fin_cases d <;> simp [flip] at hf ⊢
  subst d
  rfl

/-- The genuine surviving matching edges accessible from the `i`th selected
cluster, reindexed by `Fin M.card` as required by Lemma 5.9(2). -/
def indexedAllowedEdges
    {E : Type*} [DecidableEq E] {I : Type*} [DecidableEq I]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → I)
    (C : Finset I) (W : Finset I) (i : Fin C.card) : Finset (Fin M.card) :=
  Finset.univ.filter fun e ↦
    finsetValue M e ∈
      matchingAccessEdges R M endpoint (finsetValue C i) W

/-- The access orientation transported to the canonical `Fin` indices. -/
def indexedAccessSide
    {E : Type*} [DecidableEq E] {I : Type*} [DecidableEq I]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → I)
    (C : Finset I) (W : Finset I)
    (i : Fin C.card) (e : Fin M.card) : Fin 2 :=
  matchingAccessSide R endpoint (finsetValue C i) W (finsetValue M e)

@[simp] theorem mem_indexedAllowedEdges
    {E : Type*} [DecidableEq E] {I : Type*} [DecidableEq I]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → I)
    (C : Finset I) (W : Finset I) (i : Fin C.card) (e : Fin M.card) :
    e ∈ indexedAllowedEdges R M endpoint C W i ↔
      finsetValue M e ∈
        matchingAccessEdges R M endpoint (finsetValue C i) W := by
  simp [indexedAllowedEdges]

/-- Reindexing does not change the number of accessible matching edges. -/
theorem card_indexedAllowedEdges
    {E : Type*} [DecidableEq E] {I : Type*} [DecidableEq I]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → I)
    (C : Finset I) (W : Finset I) (i : Fin C.card) :
    #(indexedAllowedEdges R M endpoint C W i) =
      #(matchingAccessEdges R M endpoint (finsetValue C i) W) := by
  classical
  apply Finset.card_bij (fun e _ ↦ finsetValue M e)
  · intro e he
    exact (mem_indexedAllowedEdges R M endpoint C W i e).mp he
  · intro e _ f _ hef
    exact finsetValue_injective M hef
  · intro e he
    obtain ⟨j, hj⟩ := finsetValue_surjective M e (mem_filter.mp he).1
    refine ⟨j, ?_, hj⟩
    apply (mem_indexedAllowedEdges R M endpoint C W i j).mpr
    simpa [hj] using he

/-- The indexed form of the genuine-edge lower bound used as Lemma 5.9's
`hadjacent` input. -/
theorem four_mul_le_card_indexedGenuineMatchingAccessEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching)
    (C : Finset I) (W : Finset I) (rhoK : ℕ)
    (hW : W ⊆ matchingSupport M)
    (hdegree : ∀ x ∈ C, 8 * rhoK ≤ degreeInto R x W)
    (i : Fin C.card) :
    4 * rhoK ≤
      #(indexedAllowedEdges R M.edgeSet.toFinite.toFinset
        matchingEdgeEndpoint C W i) := by
  rw [card_indexedAllowedEdges]
  apply four_mul_le_card_genuineMatchingAccessEdges R M hM
    (finsetValue C i) W rhoK hW
  exact hdegree (finsetValue C i) (finsetValue_mem C i)

theorem indexedAccessSide_spec
    {E : Type*} [DecidableEq E] {I : Type*} [DecidableEq I]
    (R : SimpleGraph I) [DecidableRel R.Adj]
    (M : Finset E) (endpoint : E → Fin 2 → I)
    (C : Finset I) (W : Finset I)
    (i : Fin C.card) (e : Fin M.card)
    (he : e ∈ indexedAllowedEdges R M endpoint C W i) :
    let side := indexedAccessSide R M endpoint C W i e
    let y := if side = 0 then endpoint (finsetValue M e) 1
      else endpoint (finsetValue M e) 0
    y ∈ W ∧ R.Adj (finsetValue C i) y := by
  exact matchingAccessSide_spec R M endpoint (finsetValue C i) W
    (finsetValue M e)
    ((mem_indexedAllowedEdges R M endpoint C W i e).mp he)

/-- Indexed access edges yield the exact host pair used in Lemma 5.9(2). -/
theorem uniform_dense_indexedAccessPair
    {B I : Type*} [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (M : Finset (Sym2 I)) (C : Finset I) (W : Finset I)
    (i : Fin C.card) (e : Fin M.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density) M
      matchingEdgeEndpoint C W i) :
    G.IsUniform epsilon (cluster (finsetValue C i))
      (if indexedAccessSide
          (regularityReducedGraph G cluster epsilon density) M
          matchingEdgeEndpoint C W i e = 0
        then cluster (matchingEdgeEndpoint (finsetValue M e) 1)
        else cluster (matchingEdgeEndpoint (finsetValue M e) 0)) ∧
    density ≤ G.edgeDensity (cluster (finsetValue C i))
      (if indexedAccessSide
          (regularityReducedGraph G cluster epsilon density) M
          matchingEdgeEndpoint C W i e = 0
        then cluster (matchingEdgeEndpoint (finsetValue M e) 1)
        else cluster (matchingEdgeEndpoint (finsetValue M e) 0)) := by
  have h := uniform_dense_accessPair G cluster epsilon density M
    matchingEdgeEndpoint (finsetValue C i) W (finsetValue M e)
    ((mem_indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density) M
      matchingEdgeEndpoint C W i e).mp he)
  by_cases hs : indexedAccessSide
      (regularityReducedGraph G cluster epsilon density) M
      matchingEdgeEndpoint C W i e = 0
  · have hs' : matchingAccessSide
        (regularityReducedGraph G cluster epsilon density)
        matchingEdgeEndpoint (finsetValue C i) W (finsetValue M e) = 0 := by
      simpa only [indexedAccessSide] using hs
    simp only [if_pos hs]
    simpa only [if_pos hs'] using h
  · have hs' : matchingAccessSide
        (regularityReducedGraph G cluster epsilon density)
        matchingEdgeEndpoint (finsetValue C i) W (finsetValue M e) ≠ 0 := by
      simpa only [indexedAccessSide] using hs
    simp only [if_neg hs]
    simpa only [if_neg hs'] using h

/-- Indexed genuine matching edges retain their host uniformity and density. -/
theorem uniform_dense_indexedMatchingPair
    {B I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (e : Fin M.edgeSet.toFinite.toFinset.card) :
    G.IsUniform epsilon
        (cluster (matchingEdgeEndpoint
          (finsetValue M.edgeSet.toFinite.toFinset e) 0))
        (cluster (matchingEdgeEndpoint
          (finsetValue M.edgeSet.toFinite.toFinset e) 1)) ∧
      density ≤ G.edgeDensity
        (cluster (matchingEdgeEndpoint
          (finsetValue M.edgeSet.toFinite.toFinset e) 0))
        (cluster (matchingEdgeEndpoint
          (finsetValue M.edgeSet.toFinite.toFinset e) 1)) := by
  apply uniform_dense_matchingPair G cluster epsilon density M
  exact M.edgeSet.toFinite.mem_toFinset.mp
    (finsetValue_mem M.edgeSet.toFinite.toFinset e)

/-- A selected cluster adjacent to Zhao's distinguished cluster gives the
root-to-cluster regular pair in the concrete host. -/
theorem uniform_dense_indexedRootPair
    {B I : Type*} [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (hAC : ∀ x ∈ C,
      (regularityReducedGraph G cluster epsilon density).Adj A x)
    (i : Fin C.card) :
    G.IsUniform epsilon (cluster A) (cluster (finsetValue C i)) ∧
      density ≤ G.edgeDensity (cluster A) (cluster (finsetValue C i)) := by
  have h := hAC (finsetValue C i) (finsetValue_mem C i)
  exact ⟨h.2.1, h.2.2⟩

/-- Transport the padded Claim-6.7 certificate stored by quantitative
Claim 6.1 to the definitionally concrete padded regularity reduced graph. -/
noncomputable def changeClaim67Decidable
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} (d₁ d₂ : DecidableRel R.Adj)
    {L : Finset I} {miss : ℕ}
    (C : @Claim67Certificate I inferInstance inferInstance R d₁ L miss) :
    @Claim67Certificate I inferInstance inferInstance R d₂ L miss := by
  have hdec : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  exact C

/-- Transport a Claim-6.7 certificate along equality of its ambient graph,
then replace the transported adjacency decision procedure by the canonical
one on the target graph.  Keeping the two transports explicit avoids
dependent elimination on the implementation of `SimpleGraph.Adj`. -/
noncomputable def transportClaim67Certificate
    {I : Type*} [Fintype I] [DecidableEq I]
    {R S : SimpleGraph I} (h : R = S)
    (dR : DecidableRel R.Adj) (dS : DecidableRel S.Adj)
    {L : Finset I} {miss : ℕ}
    (C : @Claim67Certificate I inferInstance inferInstance R dR L miss) :
    @Claim67Certificate I inferInstance inferInstance S dS L miss := by
  cases h
  exact changeClaim67Decidable dR dS C

def RichClaim61Certificate.hostClaim67
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (Gdegree Hregular : SimpleGraph B)
    [DecidableRel Gdegree.Adj] [DecidableRel Hregular.Adj]
    (Pcluster : ClusterAssignment B I)
    (cluster : I → Finset B) (epsilon density : ℚ)
    (threshold quota miss : ℕ)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster epsilon density)
      (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
    (hdensity : 0 < density) :
    Claim67Certificate
      (regularityReducedGraph Hregular (padCluster cluster) epsilon density)
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota)) miss := by
  let dpad : DecidableRel
      (padGraph (regularityReducedGraph Hregular cluster epsilon density)).Adj :=
    inferInstance
  have Cpad : @Claim67Certificate (EvenPadding I) inferInstance inferInstance
      (padGraph (regularityReducedGraph Hregular cluster epsilon density)) dpad
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota)) miss :=
    Q.claim67
  have hpad :=
    padGraph_regularityReducedGraph Hregular cluster epsilon density hdensity
  exact transportClaim67Certificate hpad dpad inferInstance Cpad

/-- All regular-pair facts furnished by the Claim-6.16 reduced configuration,
packaged in the exact `Fin c`/`Fin k` coordinates used by Lemma 5.9.  This
record contains only concrete reduced adjacency, host uniformity/density, and
the genuine accessible-edge lower bound; it contains no source embedding. -/
structure IndexedHostSystem
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj] where
  cluster_eq : ∀ i, cluster i = clusterVertices Pcluster i
  pairGraph_le_degreeGraph : G ≤ Gdegree
  sourceSupport : Finset I
  selected_subset_sourceSupport : C ⊆ sourceSupport
  matching_subset_sourceSupport : matchingSupport M ⊆ sourceSupport
  root_large : A ∈ largeClustersAtLeast Pcluster Gdegree threshold quota
  companion_large : Broot ∈
    largeClustersAtLeast Pcluster Gdegree threshold quota
  /-- The exact Zhao reservoir retained from quantitative Claim 6.1. -/
  rootReserve : Finset B
  companionReserve : Finset B
  rootReserve_subset : rootReserve ⊆ cluster A
  companionReserve_subset : companionReserve ⊆ cluster Broot
  rootReserve_card : rootReserve.card = quota
  companionReserve_card : companionReserve.card = quota
  rootReserve_high : ∀ z ∈ rootReserve, threshold ≤ Gdegree.degree z
  companionReserve_high : ∀ z ∈ companionReserve,
    threshold ≤ Gdegree.degree z
  distinguished_adj :
    (regularityReducedGraph G cluster epsilon density).Adj A Broot
  cluster_card : C.card = rhoK
  cluster_disjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j)
  distinguished_cluster_disjoint : Disjoint (cluster A) (cluster Broot)
  root_cluster_disjoint : ∀ i,
    Disjoint (cluster A) (indexedCluster cluster C i)
  cluster_matching_disjoint : ∀ i e,
    Disjoint (indexedCluster cluster C i)
      (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 0 ∪
        indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 1)
  matching_disjoint : ∀ e f, e ≠ f →
    Disjoint
      (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 0 ∪
        indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 1)
      (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset f 0 ∪
        indexedMatchingSide cluster M.edgeSet.toFinite.toFinset f 1)
  root_adj : ∀ i,
    (regularityReducedGraph G cluster epsilon density).Adj A (finsetValue C i)
  root_pair : ∀ i,
    G.IsUniform epsilon (cluster A) (indexedCluster cluster C i) ∧
      density ≤ G.edgeDensity (cluster A) (indexedCluster cluster C i)
  allowed_card : ∀ i,
    4 * rhoK ≤ #(indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      M.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i)
  access_pair : ∀ i e, e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      M.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i →
    G.IsUniform epsilon (indexedCluster cluster C i)
      (if indexedAccessSide
          (regularityReducedGraph G cluster epsilon density)
          M.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e = 0
        then indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 1
        else indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 0) ∧
    density ≤ G.edgeDensity (indexedCluster cluster C i)
      (if indexedAccessSide
          (regularityReducedGraph G cluster epsilon density)
          M.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e = 0
        then indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 1
        else indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 0)
  matching_pair : ∀ e,
    G.IsUniform epsilon
        (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 0)
        (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 1) ∧
      density ≤ G.edgeDensity
        (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 0)
        (indexedMatchingSide cluster M.edgeSet.toFinite.toFinset e 1)

/-- Construct the indexed host system directly from reduced adjacency and the
surviving-degree estimate. -/
noncomputable def indexedHostSystem_of_reducedData
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (hM : M.IsMatching) (W : Finset I) (rhoK : ℕ)
    (hCcard : C.card = rhoK)
    (Pcluster : ClusterAssignment B I)
    (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (hrootLarge : A ∈ largeClustersAtLeast Pcluster Gdegree threshold quota)
    (hcompanionLarge : Broot ∈
      largeClustersAtLeast Pcluster Gdegree threshold quota)
    (hABadj :
      (regularityReducedGraph G cluster epsilon density).Adj A Broot)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (hGle : G ≤ Gdegree)
    (rootReserve companionReserve : Finset B)
    (hrootReserve_subset : rootReserve ⊆ cluster A)
    (hcompanionReserve_subset : companionReserve ⊆ cluster Broot)
    (hrootReserve_card : rootReserve.card = quota)
    (hcompanionReserve_card : companionReserve.card = quota)
    (hrootReserve_high : ∀ z ∈ rootReserve, threshold ≤ Gdegree.degree z)
    (hcompanionReserve_high : ∀ z ∈ companionReserve,
      threshold ≤ Gdegree.degree z)
    (sourceSupport : Finset I)
    (hCsource : C ⊆ sourceSupport)
    (hMsource : matchingSupport M ⊆ sourceSupport)
    (hCoutside : Disjoint C (matchingSupport M))
    (hW : W ⊆ matchingSupport M)
    (hrootAdj : ∀ x ∈ C,
      (regularityReducedGraph G cluster epsilon density).Adj A x)
    (hdegree : ∀ x ∈ C, 8 * rhoK ≤ degreeInto
      (regularityReducedGraph G cluster epsilon density) x W) :
    IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree := by
  have hclusters : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j) := by
    intro i j hij
    simpa only [hcluster] using clusterVertices_disjoint Pcluster hij
  have hendpointMem (e : Fin M.edgeSet.toFinite.toFinset.card) (c : Fin 2) :
      matchingEdgeEndpoint
          (finsetValue M.edgeSet.toFinite.toFinset e) c ∈ matchingSupport M := by
    apply matchingEdgeEndpoint_mem_support M
    exact M.edgeSet.toFinite.mem_toFinset.mp
      (finsetValue_mem M.edgeSet.toFinite.toFinset e)
  have hCne (i : Fin C.card) (e : Fin M.edgeSet.toFinite.toFinset.card)
      (c : Fin 2) :
      finsetValue C i ≠ matchingEdgeEndpoint
        (finsetValue M.edgeSet.toFinite.toFinset e) c := by
    intro h
    have heMem := hendpointMem e c
    rw [← h] at heMem
    exact Finset.disjoint_left.mp hCoutside (finsetValue_mem C i) heMem
  refine
    { cluster_eq := hcluster
      pairGraph_le_degreeGraph := hGle
      sourceSupport := sourceSupport
      selected_subset_sourceSupport := hCsource
      matching_subset_sourceSupport := hMsource
      root_large := hrootLarge
      companion_large := hcompanionLarge
      rootReserve := rootReserve
      companionReserve := companionReserve
      rootReserve_subset := hrootReserve_subset
      companionReserve_subset := hcompanionReserve_subset
      rootReserve_card := hrootReserve_card
      companionReserve_card := hcompanionReserve_card
      rootReserve_high := hrootReserve_high
      companionReserve_high := hcompanionReserve_high
      distinguished_adj := hABadj
      cluster_card := hCcard
      cluster_disjoint := hclusters
      distinguished_cluster_disjoint := hclusters A Broot hABadj.ne
      root_cluster_disjoint := ?_
      cluster_matching_disjoint := ?_
      matching_disjoint := ?_
      root_adj := ?_
      root_pair := ?_
      allowed_card := ?_
      access_pair := ?_
      matching_pair := ?_ }
  · intro i
    exact hclusters A (finsetValue C i)
      (hrootAdj (finsetValue C i) (finsetValue_mem C i)).ne
  · intro i e
    rw [Finset.disjoint_left]
    intro z hzC hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.disjoint_left.mp
        (hclusters (finsetValue C i) _ (hCne i e 0)) hzC hz
    · exact Finset.disjoint_left.mp
        (hclusters (finsetValue C i) _ (hCne i e 1)) hzC hz
  · intro e f hef
    have hne (c d : Fin 2) :
        matchingEdgeEndpoint (finsetValue M.edgeSet.toFinite.toFinset e) c ≠
          matchingEdgeEndpoint (finsetValue M.edgeSet.toFinite.toFinset f) d := by
      intro h
      have hp : (e, c) = (f, d) := by
        apply indexedMatchingEndpoint_injective M hM
        exact h
      exact hef (congrArg Prod.fst hp)
    rw [Finset.disjoint_left]
    intro z hze hzf
    rcases Finset.mem_union.mp hze with hze | hze <;>
      rcases Finset.mem_union.mp hzf with hzf | hzf
    · exact Finset.disjoint_left.mp (hclusters _ _ (hne 0 0)) hze hzf
    · exact Finset.disjoint_left.mp (hclusters _ _ (hne 0 1)) hze hzf
    · exact Finset.disjoint_left.mp (hclusters _ _ (hne 1 0)) hze hzf
    · exact Finset.disjoint_left.mp (hclusters _ _ (hne 1 1)) hze hzf
  · intro i
    exact hrootAdj (finsetValue C i) (finsetValue_mem C i)
  · intro i
    simpa [indexedCluster] using
      uniform_dense_indexedRootPair G cluster epsilon density
        A Broot C hrootAdj i
  · intro i
    exact four_mul_le_card_indexedGenuineMatchingAccessEdges
      (regularityReducedGraph G cluster epsilon density) M hM C W rhoK
      hW hdegree i
  · intro i e he
    simpa [indexedCluster, indexedMatchingSide] using
      uniform_dense_indexedAccessPair G cluster epsilon density
        M.edgeSet.toFinite.toFinset C W i e he
  · intro e
    simpa [indexedMatchingSide] using
      uniform_dense_indexedMatchingPair G cluster epsilon density M e

/-! ### The canonical quantitative root reservoir -/

/-- The distinguished root reservoir is not caller-supplied data: it is the
exact-size high-degree subreservoir retained from quantitative Claim 6.1. -/
def IndexedHostSystem.rootReservoir
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (_H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) : Finset B :=
  _H.rootReserve

/-- The second exact-size high-degree reservoir used by Zhao's two-root
completion step. -/
def IndexedHostSystem.companionReservoir
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (_H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) : Finset B :=
  _H.companionReserve

theorem IndexedHostSystem.rootReservoir_subset_rootCluster
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    H.rootReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree ⊆ cluster A := by
  exact H.rootReserve_subset

theorem IndexedHostSystem.quota_le_rootReservoir_card
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    quota ≤ (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree).card := by
  rw [rootReservoir, H.rootReserve_card]

theorem IndexedHostSystem.rootReservoir_highDegree
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) {z : B}
    (hz : z ∈ H.rootReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    threshold ≤ Gdegree.degree z :=
  H.rootReserve_high z hz

theorem IndexedHostSystem.companionReservoir_subset_companionCluster
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    H.companionReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree ⊆ cluster Broot := by
  exact H.companionReserve_subset

theorem IndexedHostSystem.quota_le_companionReservoir_card
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    quota ≤ (H.companionReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree).card := by
  rw [companionReservoir, H.companionReserve_card]

theorem IndexedHostSystem.companionReservoir_highDegree
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) {z : B}
    (hz : z ∈ H.companionReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    threshold ≤ Gdegree.degree z :=
  H.companionReserve_high z hz

theorem IndexedHostSystem.rootReservoir_card_eq
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree).card = quota :=
  H.rootReserve_card

theorem IndexedHostSystem.companionReservoir_card_eq
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    (H.companionReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree).card = quota :=
  H.companionReserve_card

/-- Removing both exact root reservoirs costs at most `2 * quota`, even when
one of the distinguished clusters is itself a matching endpoint. -/
theorem IndexedHostSystem.rootReservoir_union_companionReservoir_card_le
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    #(H.rootReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree ∪
        H.companionReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree) ≤ 2 * quota := by
  calc
    #(_ ∪ _) ≤
        #(H.rootReservoir G cluster epsilon density A Broot C M W rhoK
            Pcluster threshold quota Gdegree) +
          #(H.companionReservoir G cluster epsilon density A Broot C M W rhoK
            Pcluster threshold quota Gdegree) := Finset.card_union_le _ _
    _ = quota + quota := by
      rw [H.rootReservoir_card_eq G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree,
        H.companionReservoir_card_eq G cluster epsilon density
          A Broot C M W rhoK Pcluster threshold quota Gdegree]
    _ = 2 * quota := by omega

theorem IndexedHostSystem.card_le_card_remove_rootReservoirs_add
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    X.card ≤
      (X \ (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree ∪
        H.companionReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree)).card + 2 * quota := by
  let U := H.rootReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree ∪
    H.companionReservoir G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree
  have hsplit := Finset.card_sdiff_add_card_inter X U
  calc
    X.card = (X \ U).card + (X ∩ U).card := hsplit.symm
    _ ≤ (X \ U).card + U.card :=
      Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
    _ ≤ (X \ U).card + 2 * quota :=
      Nat.add_le_add_left
        (H.rootReservoir_union_companionReservoir_card_le G cluster epsilon density
          A Broot C M W rhoK Pcluster threshold quota Gdegree) _

theorem IndexedHostSystem.rootReservoir_disjoint_cluster_of_ne
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (x : I) (hx : A ≠ x) :
    Disjoint
      (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (cluster x) :=
  (H.cluster_disjoint A x hx).mono
    (H.rootReservoir_subset_rootCluster G cluster epsilon density
      A Broot C M W rhoK Pcluster threshold quota Gdegree) Finset.Subset.rfl

theorem IndexedHostSystem.companionReservoir_disjoint_cluster_of_ne
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (x : I) (hx : Broot ≠ x) :
    Disjoint
      (H.companionReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (cluster x) :=
  (H.cluster_disjoint Broot x hx).mono
    (H.companionReservoir_subset_companionCluster G cluster epsilon density
      A Broot C M W rhoK Pcluster threshold quota Gdegree) Finset.Subset.rfl

theorem IndexedHostSystem.rootReservoir_disjoint_companionReservoir
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) :
    Disjoint
      (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (H.companionReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree) :=
  H.distinguished_cluster_disjoint.mono
    (H.rootReservoir_subset_rootCluster G cluster epsilon density
      A Broot C M W rhoK Pcluster threshold quota Gdegree)
    (H.companionReservoir_subset_companionCluster G cluster epsilon density
      A Broot C M W rhoK Pcluster threshold quota Gdegree)

/-! Claim 6.7 does not make the odd set disjoint from its matching support:
the distinguished rich clusters may themselves be matching endpoints.  The
canonical cleaner must therefore delete the two root reservoirs from any
overlapping matching or selected-cluster candidate.  The following facts are
the unconditional separation statements consumed by that construction. -/

theorem IndexedHostSystem.rootReservoir_disjoint_after_rootRemoval
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    Disjoint
      (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (X \ H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree) :=
  Finset.disjoint_sdiff

theorem IndexedHostSystem.companionReservoir_disjoint_after_companionRemoval
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    Disjoint
      (H.companionReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (X \ H.companionReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree) :=
  Finset.disjoint_sdiff

theorem IndexedHostSystem.rootReservoir_disjoint_after_bothRemovals
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    Disjoint
      (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (X \ (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree ∪
        H.companionReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree)) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hz)

theorem IndexedHostSystem.companionReservoir_disjoint_after_bothRemovals
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree) (X : Finset B) :
    Disjoint
      (H.companionReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      (X \ (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree ∪
        H.companionReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree)) := by
  rw [Finset.disjoint_left]
  intro z hz hzX
  exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_right _ hz)

/-- Positive Claim-6.16 scale supplies the nonempty finite index types needed
by the aggregate Lemma 5.9 theorem. -/
theorem IndexedHostSystem.indexTypes_nonempty
    {B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree)
    (hrhoK : 0 < rhoK) :
    Nonempty (Fin C.card) ∧
      Nonempty (Fin M.edgeSet.toFinite.toFinset.card) := by
  have hCpos : 0 < C.card := by
    have hcard := H.cluster_card
    omega
  let i : Fin C.card := ⟨0, hCpos⟩
  have hallowed : 0 < #(indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      M.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i) := by
    have hi := H.allowed_card i
    omega
  obtain ⟨e, _he⟩ := Finset.card_pos.mp hallowed
  exact ⟨⟨i⟩, ⟨e⟩⟩

/-- Any concrete tree obtained in the regular-pair host is automatically a
copy in the original degree host. -/
theorem IndexedHostSystem.isContained_degreeGraph
    {τ B I : Type*} [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree)
    (T : SimpleGraph τ) (hT : T.IsContained G) :
    T.IsContained Gdegree :=
  hT.mono_right H.pairGraph_le_degreeGraph

/-! ### The canonical Claim-6.8 half and its selected source forest -/

/-- If the large-branch mass of the canonical parity half exceeds `target`,
select the source forest `F₀` from that same half.  This is the literal
source-side selection used in Claim 6.16; no arbitrary `partA` finset is
accepted. -/
theorem exists_selectedHalfF0
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small target slack : ℕ}
    (P : TreePartition.ZhaoForestPartition T globalRoot small)
    (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hmass : target ≤ largeHalfMass P) :
    Nonempty (SelectedF0Within
      (branchForest P) (halfBranches P) target slack) := by
  apply exists_selectedF0Within (branchForest P) (halfBranches P)
    target slack hslack hsmall
  change target ≤
    ∑ j ∈ (halfBranches P).filter
      (fun j ↦ 3 ≤ (branchForest P).branches.size j),
        (branchForest P).branches.size j at hmass
  exact hmass

/-- Contrapositive-ready form of the preceding selector. -/
theorem exists_selectedHalfF0_of_bad_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small bad slack : ℕ}
    (P : TreePartition.ZhaoForestPartition T globalRoot small)
    (hslack : 0 < slack)
    (hsmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hmass : bad < largeHalfMass P) :
    Nonempty (SelectedF0Within
      (branchForest P) (halfBranches P) (bad + 1) slack) := by
  apply exists_selectedHalfF0 P hslack hsmall
  omega

/-! ## The heavy-cluster count -/

/-- The averaging argument on p.34 of Zhao's paper.  If fewer than `r`
vertices of `S` have at least `q` neighbors in `T`, then the crossing-edge
count is at most `r * |T| + |S| * q`.  The displayed strict reverse
inequality therefore forces at least `r` heavy vertices.

The paper applies this with `r = rho0*k` and `q = 9*rho0*k`. -/
theorem card_crossHeavy_ge_of_crossing_gt
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (S T : Finset ι) (r q : ℕ)
    (hcross : r * T.card + S.card * q < (R.interedges S T).card) :
    r ≤ (crossHeavy R S T q).card := by
  classical
  let H := crossHeavy R S T q
  change r ≤ H.card
  by_contra hcard
  have hHr : H.card ≤ r := by omega
  have hsum : (R.interedges S T).card =
      (∑ x ∈ H, degreeInto R x T) +
        ∑ x ∈ S \ H, degreeInto R x T := by
    rw [← sum_degreeInto_eq_card_interedges]
    have hHS : H ⊆ S := crossHeavy_subset R S T q
    rw [← sum_sdiff hHS]
    omega
  have hheavy : (∑ x ∈ H, degreeInto R x T) ≤ H.card * T.card := by
    simpa [mul_comm] using
      Finset.sum_le_card_nsmul H (fun x => degreeInto R x T) T.card
        (fun x _ => degreeInto_le_card R x T)
  have hlight_point : ∀ x ∈ S \ H, degreeInto R x T ≤ q := by
    intro x hx
    have hxS : x ∈ S := (mem_sdiff.mp hx).1
    have hxH : x ∉ H := (mem_sdiff.mp hx).2
    have : ¬q ≤ degreeInto R x T := by
      simpa [H, crossHeavy, hxS] using hxH
    omega
  have hlight : (∑ x ∈ S \ H, degreeInto R x T) ≤ (S \ H).card * q := by
    simpa [mul_comm] using
      Finset.sum_le_card_nsmul (S \ H) (fun x => degreeInto R x T) q
        hlight_point
  have hsdiff : (S \ H).card ≤ S.card := card_le_card sdiff_subset
  have hupper : (R.interedges S T).card ≤ r * T.card + S.card * q := by
    rw [hsum]
    calc
      (∑ x ∈ H, degreeInto R x T) +
            ∑ x ∈ S \ H, degreeInto R x T
          ≤ H.card * T.card + (S \ H).card * q :=
        Nat.add_le_add hheavy hlight
      _ ≤ r * T.card + S.card * q := by
        exact Nat.add_le_add (Nat.mul_le_mul_right T.card hHr)
          (Nat.mul_le_mul_right q hsdiff)
  omega

/-! ## Passing from the total matching to `Mout` -/

/-- If the support of a total matching is the union of the supports of
`Min` and `Mout`, and `V2` is disjoint from `Min`, then every `V2`-neighbor
missed by `Mout` is also missed by the total matching.  This is the precise
set-theoretic step implicit when Claim 6.7(2) is used in Claim 6.16. -/
theorem card_neighbors_V2_missed_by_out_le
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M Min Mout : R.Subgraph) (V2 : Finset ι) (x : ι) (miss : ℕ)
    (hsupport : matchingSupport M = matchingSupport Min ∪ matchingSupport Mout)
    (hV2Min : Disjoint V2 (matchingSupport Min))
    (hmiss : (R.neighborFinset x \ matchingSupport M).card ≤ miss) :
    ((R.neighborFinset x ∩ V2) \ matchingSupport Mout).card ≤ miss := by
  apply (card_le_card ?_).trans hmiss
  intro y hy
  have hy' := mem_sdiff.mp hy
  have hyNV := mem_inter.mp hy'.1
  apply mem_sdiff.mpr
  refine ⟨hyNV.1, ?_⟩
  intro hyM
  rw [hsupport] at hyM
  rcases mem_union.mp hyM with hyMin | hyOut
  · exact (disjoint_left.mp hV2Min hyNV.2 hyMin)
  · exact hy'.2 hyOut

/-- Losing at most `miss` adjacent vertices outside `Q`, and then deleting a
set `D` of at most `removed` vertices, decreases the degree into `V2` by at
most `miss + removed`.  Unlike a bound on `V2 \ Q`, the first hypothesis only
counts *neighbors*, exactly as Claim 6.7 does. -/
theorem degreeInto_available_ge
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (x : ι) (V2 Q D : Finset ι) (miss removed lower : ℕ)
    (hdegree : lower + miss + removed ≤ degreeInto R x V2)
    (hmiss : ((R.neighborFinset x ∩ V2) \ Q).card ≤ miss)
    (hremoved : D.card ≤ removed) :
    lower ≤ degreeInto R x (V2 ∩ (Q \ D)) := by
  classical
  let N := R.neighborFinset x ∩ V2
  have hdegN : N.card = degreeInto R x V2 := by
    unfold degreeInto
    congr 1
    ext y
    simp [N, and_comm]
  have hpartition : N.card = (N ∩ Q).card + (N \ Q).card := by
    rw [← card_sdiff_add_card_inter N Q, add_comm]
  have hNQ : lower + removed ≤ (N ∩ Q).card := by
    have hmiss' : (N \ Q).card ≤ miss := by simpa [N] using hmiss
    omega
  have hremove_inter : ((N ∩ Q) \ D).card + ((N ∩ Q) ∩ D).card =
      (N ∩ Q).card := card_sdiff_add_card_inter _ _
  have hinterD : ((N ∩ Q) ∩ D).card ≤ removed := by
    exact (card_le_card inter_subset_right).trans hremoved
  have havailCard : lower ≤ ((N ∩ Q) \ D).card := by omega
  have heq : ((N ∩ Q) \ D) =
      (V2 ∩ (Q \ D)).filter (R.Adj x) := by
    ext y
    simp only [N, mem_sdiff, mem_inter, mem_neighborFinset, mem_filter]
    tauto
  rw [heq] at havailCard
  exact havailCard

/-- The support of a finite matching has twice as many vertices as it has
edges, in the exact `Finset` form needed for the deletion loss in (6.22). -/
theorem card_matchingSupport_eq_two_mul_edges
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} (M : R.Subgraph) (hM : M.IsMatching) :
    (Erdos547b.ZhaoStability.matchingSupport M).card =
      2 * M.edgeSet.ncard := by
  classical
  have himage : M.edgeSet.ncard = M.coe.edgeSet.ncard := by
    rw [← Subgraph.image_coe_edgeSet_coe M,
      Set.ncard_image_of_injective _
        (Sym2.map.injective Subtype.coe_injective)]
  rw [Erdos547b.ZhaoStability.matchingSupport,
    ← Set.ncard_eq_toFinset_card M.verts M.verts.toFinite,
    himage]
  exact GallaiEdmonds547.card_verts_eq_two_mul_card_edges hM

/-- The complementary matching constructed by Lemma 6.11 is supported in
`V2`, hence is index-disjoint from every selected `C ⊆ V1`. -/
theorem MatchingDecomposition.Mout_support_subset_V2
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj]
    {L O : Finset ι} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA) :
    matchingSupport D.Mout ⊆ D.V2 := by
  intro x hx
  have hx' : x ∈ D.Mout.verts := (mem_matchingSupport D.Mout x).mp hx
  change ∃ e ∈ allMatchingEdges C67.M \ D.minEdges,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1 at hx'
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  intro hxV1
  obtain ⟨e, he, hx0 | hx1⟩ := hx'
  · exact (Finset.mem_sdiff.mp he).2
      ((D.endpoint_mem_V1_iff e 0).mp (hx0 ▸ hxV1))
  · exact (Finset.mem_sdiff.mp he).2
      ((D.endpoint_mem_V1_iff e 1).mp (hx1 ▸ hxV1))

theorem MatchingDecomposition.Mb_support_subset_Mout
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA) :
    matchingSupport D.Mb ⊆ matchingSupport D.Mout := by
  intro x hx
  have hx' := (mem_matchingSupport D.Mb x).mp hx
  change ∃ e ∈ D.mbEdges,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1 at hx'
  apply (mem_matchingSupport D.Mout x).mpr
  change ∃ e ∈ allMatchingEdges C67.M \ D.minEdges,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1
  obtain ⟨e, he, hx0 | hx1⟩ := hx'
  · exact ⟨e, D.mb_subset he, Or.inl hx0⟩
  · exact ⟨e, D.mb_subset he, Or.inr hx1⟩

theorem MatchingDecomposition.Mb_support_subset_V2
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA) :
    matchingSupport D.Mb ⊆ D.V2 :=
  (MatchingDecomposition.Mb_support_subset_Mout D).trans
    (MatchingDecomposition.Mout_support_subset_V2 D)

/-! ### The minimum submatching of `M_in` covering `C`

In the source proof, after choosing `C ⊆ V(M_in)`, Zhao lets `M₀` be the
minimum submatching of `M_in` covering `C`.  Since `M_in` is a matching, this
is canonical: retain precisely the matching edges having an endpoint in `C`.
The following definitions construct that genuine subgraph and prove the two
facts used in (6.23), namely that it covers `C` and has at most `|C|` edges.
-/

/-- Edges of a matching having at least one endpoint in `C`. -/
def incidentCoverEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} (M : R.Subgraph) (L C : Finset I) :
    Finset (MatchingEdge M) :=
  (allMatchingEdges M).filter fun e ↦
    orientedEndpoint M L e 0 ∈ C ∨ orientedEndpoint M L e 1 ∈ C

/-- The endpoint in `C` canonically charged to a retained matching edge. -/
def incidentCoverEndpoint
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} (M : R.Subgraph) (L C : Finset I)
    (e : MatchingEdge M) : I :=
  if orientedEndpoint M L e 0 ∈ C then orientedEndpoint M L e 0
  else orientedEndpoint M L e 1

/-- The actual submatching of `M` induced by the edges incident with `C`. -/
def incidentCoverSubgraph
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (L C : Finset I) : R.Subgraph :=
  edgeFinsetSubgraph M L (incidentCoverEdges M L C)

theorem incidentCoverSubgraph_isMatching
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching)
    (L C : Finset I) :
    (incidentCoverSubgraph M L C).IsMatching := by
  exact edgeFinsetSubgraph_isMatching M hM L (incidentCoverEdges M L C)

/-- Distinct retained edges are charged to distinct vertices of `C`, because
the ambient subgraph is a matching. -/
theorem incidentCoverEdges_card_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching)
    (L C : Finset I) :
    (incidentCoverEdges M L C).card ≤ C.card := by
  classical
  apply Finset.card_le_card_of_injOn (incidentCoverEndpoint M L C)
  · intro e he
    have he' := (Finset.mem_filter.mp he).2
    by_cases hzero : orientedEndpoint M L e 0 ∈ C
    · simpa [incidentCoverEndpoint, hzero] using hzero
    · simpa [incidentCoverEndpoint, hzero] using he'.resolve_left hzero
  · intro e he f hf hef
    by_cases hezero : orientedEndpoint M L e 0 ∈ C <;>
      by_cases hfzero : orientedEndpoint M L f 0 ∈ C
    · have hp : (e, (0 : Fin 2)) = (f, (0 : Fin 2)) := by
        apply orientedEndpoint_injective M hM L
        simpa [incidentCoverEndpoint, hezero, hfzero] using hef
      exact congrArg Prod.fst hp
    · have hp : (e, (0 : Fin 2)) = (f, (1 : Fin 2)) := by
        apply orientedEndpoint_injective M hM L
        simpa [incidentCoverEndpoint, hezero, hfzero] using hef
      exact congrArg Prod.fst hp
    · have hp : (e, (1 : Fin 2)) = (f, (0 : Fin 2)) := by
        apply orientedEndpoint_injective M hM L
        simpa [incidentCoverEndpoint, hezero, hfzero] using hef
      exact congrArg Prod.fst hp
    · have hp : (e, (1 : Fin 2)) = (f, (1 : Fin 2)) := by
        apply orientedEndpoint_injective M hM L
        simpa [incidentCoverEndpoint, hezero, hfzero] using hef
      exact congrArg Prod.fst hp

/-- If `C` lies in the support of a matching, its canonical incident-edge
submatching covers every vertex of `C`. -/
theorem subset_matchingSupport_incidentCoverSubgraph
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching)
    (L C : Finset I) (hC : C ⊆ matchingSupport M) :
    C ⊆ matchingSupport (incidentCoverSubgraph M L C) := by
  classical
  intro x hxC
  have hxVerts : x ∈ M.verts := (mem_matchingSupport M x).mp (hC hxC)
  obtain ⟨y, hxy, _⟩ := hM hxVerts
  let e : MatchingEdge M := ⟨s(x, y), hxy⟩
  have hxEnds : x = orientedEndpoint M L e 0 ∨
      x = orientedEndpoint M L e 1 := by
    have hxmem : x ∈ (e.1 : Sym2 I) := Sym2.mem_mk_left x y
    rw [← orientedEndpoint_pair_eq M L e] at hxmem
    simpa using hxmem
  apply (mem_matchingSupport (incidentCoverSubgraph M L C) x).mpr
  rw [incidentCoverSubgraph, mem_edgeFinsetSubgraph_verts]
  refine ⟨e, ?_, hxEnds⟩
  apply Finset.mem_filter.mpr
  refine ⟨mem_allMatchingEdges M e, ?_⟩
  rcases hxEnds with hx0 | hx1
  · exact Or.inl (hx0 ▸ hxC)
  · exact Or.inr (hx1 ▸ hxC)

/-- The original matching edges of the canonical `M₀ ⊆ M_in`.  Keeping
the edge subtype that of `C67.M` makes Zhao's degree subtraction literal. -/
def MatchingDecomposition.MzeroEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) : Finset (MatchingEdge C67.M) :=
  D.minEdges.filter fun e ↦
    orientedEndpoint C67.M L e 0 ∈ C ∨
      orientedEndpoint C67.M L e 1 ∈ C

theorem MatchingDecomposition.MzeroEdges_subset_minEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C ⊆
      D.minEdges :=
  Finset.filter_subset _ _

/-- The canonical genuine submatching `M₀ ⊆ M_in`. -/
def MatchingDecomposition.Mzero
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) : R.Subgraph :=
  edgeFinsetSubgraph C67.M L
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C)

theorem MatchingDecomposition.Mzero_isMatching
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C).IsMatching := by
  exact edgeFinsetSubgraph_isMatching C67.M C67.isMatching L
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C)

theorem MatchingDecomposition.C_subset_Mzero_support
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) (hC : C ⊆ D.V1) :
    C ⊆ matchingSupport
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C) := by
  intro x hxC
  have hx := (mem_matchingSupport D.Min x).mp (hC hxC)
  change ∃ e ∈ D.minEdges,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1 at hx
  apply (mem_matchingSupport
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C) x).mpr
  change ∃ e ∈
      Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1
  obtain ⟨e, he, hx0 | hx1⟩ := hx
  · exact ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl (hx0 ▸ hxC)⟩,
      Or.inl hx0⟩
  · exact ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr (hx1 ▸ hxC)⟩,
      Or.inr hx1⟩

theorem MatchingDecomposition.Mzero_edge_card_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C).card ≤
      C.card := by
  apply (Finset.card_le_card ?_).trans
    (incidentCoverEdges_card_le C67.M C67.isMatching L C)
  intro e he
  have he' := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨mem_allMatchingEdges C67.M e, he'.2⟩

/-- The literal residual edge set `M₁ = M_in \ M₀`. -/
def MatchingDecomposition.MoneEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) : Finset (MatchingEdge C67.M) :=
  D.minEdges \
    Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C

def MatchingDecomposition.Mone
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) : R.Subgraph :=
  edgeFinsetSubgraph C67.M L
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C)

theorem MatchingDecomposition.Mone_isMatching
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C).IsMatching := by
  exact edgeFinsetSubgraph_isMatching C67.M C67.isMatching L
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C)

theorem MatchingDecomposition.Mzero_support_subset_V1
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) : matchingSupport
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C) ⊆ D.V1 := by
  intro x hx
  have hx' := (mem_matchingSupport
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C) x).mp hx
  change ∃ e ∈
      Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1 at hx'
  apply (mem_matchingSupport D.Min x).mpr
  change ∃ e ∈ D.minEdges,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1
  obtain ⟨e, he, hx0 | hx1⟩ := hx'
  · exact ⟨e,
      Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges_subset_minEdges
        D C he,
      Or.inl hx0⟩
  · exact ⟨e,
      Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges_subset_minEdges
        D C he,
      Or.inr hx1⟩

theorem MatchingDecomposition.Mone_support_subset_V1
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) : matchingSupport
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C) ⊆ D.V1 := by
  intro x hx
  have hx' := (mem_matchingSupport
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C) x).mp hx
  change ∃ e ∈
      Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1 at hx'
  apply (mem_matchingSupport D.Min x).mpr
  change ∃ e ∈ D.minEdges,
    x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1
  obtain ⟨e, he, hx0 | hx1⟩ := hx'
  · exact ⟨e, (Finset.mem_sdiff.mp he).1, Or.inl hx0⟩
  · exact ⟨e, (Finset.mem_sdiff.mp he).1, Or.inr hx1⟩

theorem MatchingDecomposition.Mzero_Mout_support_disjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    Disjoint
      (matchingSupport
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C))
      (matchingSupport D.Mout) := by
  rw [Finset.disjoint_left]
  intro x hx0 hxout
  exact (Finset.mem_sdiff.mp
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mout_support_subset_V2
      D hxout)).2
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_support_subset_V1
      D C hx0)

theorem MatchingDecomposition.Mone_Mout_support_disjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    Disjoint
      (matchingSupport
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C))
      (matchingSupport D.Mout) := by
  rw [Finset.disjoint_left]
  intro x hx1 hxout
  exact (Finset.mem_sdiff.mp
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mout_support_subset_V2
      D hxout)).2
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_support_subset_V1
      D C hx1)

theorem MatchingDecomposition.Mzero_Mone_support_disjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) :
    Disjoint
      (matchingSupport
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C))
      (matchingSupport
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C)) := by
  rw [Finset.disjoint_left]
  intro x hx0 hx1
  obtain ⟨e, he, hxe⟩ := (mem_matchingSupport _ x).mp hx0
  obtain ⟨f, hf, hxf⟩ := (mem_matchingSupport _ x).mp hx1
  rcases hxe with he0 | he1 <;> rcases hxf with hf0 | hf1
  · have hp : (e, (0 : Fin 2)) = (f, (0 : Fin 2)) := by
      apply orientedEndpoint_injective C67.M C67.isMatching L
      exact he0.symm.trans hf0
    have hef : e = f := congrArg Prod.fst hp
    subst f
    exact (Finset.mem_sdiff.mp hf).2 he
  · have hp : (e, (0 : Fin 2)) = (f, (1 : Fin 2)) := by
      apply orientedEndpoint_injective C67.M C67.isMatching L
      exact he0.symm.trans hf1
    have hef : e = f := congrArg Prod.fst hp
    subst f
    exact (Finset.mem_sdiff.mp hf).2 he
  · have hp : (e, (1 : Fin 2)) = (f, (0 : Fin 2)) := by
      apply orientedEndpoint_injective C67.M C67.isMatching L
      exact he1.symm.trans hf0
    have hef : e = f := congrArg Prod.fst hp
    subst f
    exact (Finset.mem_sdiff.mp hf).2 he
  · have hp : (e, (1 : Fin 2)) = (f, (1 : Fin 2)) := by
      apply orientedEndpoint_injective C67.M C67.isMatching L
      exact he1.symm.trans hf1
    have hef : e = f := congrArg Prod.fst hp
    subst f
    exact (Finset.mem_sdiff.mp hf).2 he

/-- Each matching edge contributes at most `2N` to the distinguished-cluster
degree, so the canonical cover has the source upper bound used before
(6.23).  This is an ordinary density estimate, not an embedding premise. -/
theorem sourceDegree_le_two_mul_N_mul_card
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset I)
    (density : I → I → ℝ) (N : ℝ) (A : I)
    (S : Finset (MatchingEdge M))
    (hN : 0 ≤ N)
    (hdensity : ∀ e ∈ S, ∀ c,
      density A (orientedEndpoint M L e c) ≤ 1) :
    sourceDegree M L density N A S ≤ 2 * N * S.card := by
  rw [sourceDegree_eq_sum]
  calc
    ∑ e ∈ S, N * (density A (orientedEndpoint M L e 0) +
          density A (orientedEndpoint M L e 1)) ≤
        ∑ _e ∈ S, 2 * N := by
      apply Finset.sum_le_sum
      intro e he
      have hzero := hdensity e he 0
      have hone := hdensity e he 1
      nlinarith
    _ = 2 * N * S.card := by
      simp [mul_comm, mul_left_comm, mul_assoc]

theorem MatchingDecomposition.Mzero_sourceDegree_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) (density : I → I → ℝ) (N : ℝ) (A : I)
    (hN : 0 ≤ N)
    (hdensity : ∀ e ∈
      Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C, ∀ c,
      density A (orientedEndpoint C67.M L e c) ≤ 1) :
    sourceDegree C67.M L density N A
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C) ≤
      2 * N * C.card := by
  calc
    sourceDegree C67.M L density N A
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C) ≤
        2 * N *
          (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C).card :=
      sourceDegree_le_two_mul_N_mul_card C67.M L density N A
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C)
        hN hdensity
    _ ≤ 2 * N * C.card := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast
          Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_edge_card_le D C
      · nlinarith

/-- The exact Lemma-6.14(2) subtraction for the source-faithful `M₀/M₁`
split.  Its hypotheses are only the stored total degree, the proved `M₀`
upper bound, and the numerical forest hierarchy. -/
theorem MatchingDecomposition.Mone_sourceDegree_lower
    {I : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67
      lowerV1 upperV1 upperV2 mbBound degreeA)
    (C : Finset I) (density : I → I → ℝ) (N : ℝ) (A : I)
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hMin : (1 - epsilon1) * n ≤
      sourceDegree C67.M L density N A D.minEdges)
    (hMzero : sourceDegree C67.M L density N A
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C) ≤
      f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1) :
    f1 + 3 * gamma * n ≤
      sourceDegree C67.M L density N A
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C) := by
  have hsplit := Finset.sum_sdiff
    (Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges_subset_minEdges
      D C)
    (f := fun e : MatchingEdge C67.M ↦
      N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1)))
  rw [sourceDegree_eq_sum] at hMin hMzero ⊢
  rw [Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges]
  change
    (∑ e ∈ D.minEdges \
        Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C,
      N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1))) +
      (∑ e ∈
          Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C,
        N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1))) =
      ∑ e ∈ D.minEdges,
        N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1)) at hsplit
  nlinarith

/-! ## Zhao's cluster set and display (6.22) -/

/-- The literal reduced-graph construction in Claim 6.16.

`Min` and `Mout` are the two parts of Zhao's matching, `Mb` is the optional
small exceptional submatching, `V1 = V(Min)`, and `V2` is its complement.
The conclusion constructs the actual set `C` of size `rhoK = rho0*k`.  Every
cluster in `C` lies in Zhao's set `O` and has at least `8*rhoK` neighbors in
`V2` still available after deleting `Mb`.

The three numerical hypotheses are exactly the inequalities used in the
paper: the crossing-edge averaging bound, the Claim-6.7 miss bound, and
`9*rhoK - miss - 2|Mb| >= 8*rhoK`. -/
theorem exists_claim616_cluster_set
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (L : Finset ι) (miss rhoK : ℕ)
    (C67 : Claim67Certificate R L miss)
    (Min Mout Mb : R.Subgraph) (hMb : Mb.IsMatching)
    (hsupport : matchingSupport C67.M =
      matchingSupport Min ∪ matchingSupport Mout)
    (hV1O : matchingSupport Min ⊆ C67.O)
    (badEdges : ℕ) (hMbEdges : Mb.edgeSet.ncard ≤ badEdges)
    (hhierarchy : miss + 2 * badEdges ≤ rhoK)
    (hcross : rhoK * (Finset.univ \ matchingSupport Min).card +
        (matchingSupport Min).card * (9 * rhoK) <
      (R.interedges (matchingSupport Min)
        (Finset.univ \ matchingSupport Min)).card) :
    ∃ C : Finset ι,
      C ⊆ matchingSupport Min ∧
      C ⊆ C67.O ∧
      C.card = rhoK ∧
      ∀ x ∈ C,
        8 * rhoK ≤ degreeInto R x
          ((Finset.univ \ matchingSupport Min) ∩
            (matchingSupport Mout \ matchingSupport Mb)) := by
  classical
  let V1 := matchingSupport Min
  let V2 := Finset.univ \ V1
  let H := crossHeavy R V1 V2 (9 * rhoK)
  have hHcard : rhoK ≤ H.card :=
    card_crossHeavy_ge_of_crossing_gt R V1 V2 rhoK (9 * rhoK) (by
      simpa [V1, V2] using hcross)
  obtain ⟨C, hCH, hCcard⟩ := exists_subset_card_eq hHcard
  have hCV1 : C ⊆ V1 := hCH.trans (crossHeavy_subset R V1 V2 (9 * rhoK))
  have hCO : C ⊆ C67.O := hCV1.trans hV1O
  refine ⟨C, hCV1, hCO, hCcard, ?_⟩
  intro x hxC
  have hxH : x ∈ H := hCH hxC
  have hxO : x ∈ C67.O := hCO hxC
  have hxdegree : 9 * rhoK ≤ degreeInto R x V2 := by
    simpa [H, crossHeavy] using (mem_filter.mp hxH).2
  have hV2Min : Disjoint V2 (matchingSupport Min) := by
    rw [Finset.disjoint_left]
    intro y hyV2 hyMin
    exact (mem_sdiff.mp hyV2).2 hyMin
  have hmissOut : ((R.neighborFinset x ∩ V2) \ matchingSupport Mout).card ≤ miss := by
    apply card_neighbors_V2_missed_by_out_le R C67.M Min Mout V2 x miss
      hsupport hV2Min
    exact C67.neighbors_missed x hxO
  have hMbSupport : (matchingSupport Mb).card ≤ 2 * badEdges := by
    rw [card_matchingSupport_eq_two_mul_edges Mb hMb]
    exact Nat.mul_le_mul_left 2 hMbEdges
  have hnumeric : 8 * rhoK + miss + 2 * badEdges ≤ 9 * rhoK := by
    omega
  apply degreeInto_available_ge R x V2 (matchingSupport Mout)
    (matchingSupport Mb) miss (2 * badEdges) (8 * rhoK)
  · exact hnumeric.trans hxdegree
  · exact hmissOut
  · exact hMbSupport

/-- Display (6.22) with the coefficients written exactly as in Zhao's
calculation.  Claim 6.7 loses `9 * sqrtLoss` clusters and the optional
matching covers at most `4 * fourthLoss` vertices. -/
theorem exists_claim616_cluster_set_source_constants
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (L : Finset ι) (sqrtLoss fourthLoss rhoK : ℕ)
    (C67 : Claim67Certificate R L (9 * sqrtLoss))
    (Min Mout Mb : R.Subgraph) (hMb : Mb.IsMatching)
    (hsupport : matchingSupport C67.M =
      matchingSupport Min ∪ matchingSupport Mout)
    (hV1O : matchingSupport Min ⊆ C67.O)
    (hMbEdges : Mb.edgeSet.ncard ≤ 2 * fourthLoss)
    (hnumeric : 9 * sqrtLoss + 4 * fourthLoss ≤ rhoK)
    (hcross : rhoK * (Finset.univ \ matchingSupport Min).card +
        (matchingSupport Min).card * (9 * rhoK) <
      (R.interedges (matchingSupport Min)
        (Finset.univ \ matchingSupport Min)).card) :
    ∃ C : Finset ι,
      C ⊆ matchingSupport Min ∧
      C ⊆ C67.O ∧
      C.card = rhoK ∧
      ∀ x ∈ C,
        8 * rhoK ≤ degreeInto R x
          ((Finset.univ \ matchingSupport Min) ∩
            (matchingSupport Mout \ matchingSupport Mb)) := by
  apply exists_claim616_cluster_set R L (9 * sqrtLoss) rhoK C67
    Min Mout Mb hMb hsupport hV1O (2 * fourthLoss) hMbEdges
  · omega
  · exact hcross

/-! ## Concrete host conclusion -/

/-- Host realization of display (6.22).  The reduced graph is definitionally
the regularity reduced graph of the displayed host clusters, so every partner
and matching edge in the conclusion is an actual uniform dense host pair. -/
theorem exists_claim616_host_cluster_set
    {B : Type u} {ι : Type v}
    [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (cluster : ι → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (L : Finset ι) (miss rhoK : ℕ)
    (C67 : Claim67Certificate
      (regularityReducedGraph G cluster epsilon density) L miss)
    (Min Mout Mb :
      (regularityReducedGraph G cluster epsilon density).Subgraph)
    (hMout : Mout.IsMatching) (hMb : Mb.IsMatching)
    (hsupport : matchingSupport C67.M =
      matchingSupport Min ∪ matchingSupport Mout)
    (hV1O : matchingSupport Min ⊆ C67.O)
    (badEdges : ℕ) (hMbEdges : Mb.edgeSet.ncard ≤ badEdges)
    (hhierarchy : miss + 2 * badEdges ≤ rhoK)
    (hcross : rhoK * (Finset.univ \ matchingSupport Min).card +
        (matchingSupport Min).card * (9 * rhoK) <
      ((regularityReducedGraph G cluster epsilon density).interedges
        (matchingSupport Min)
        (Finset.univ \ matchingSupport Min)).card) :
    ∃ C : Finset ι,
      C ⊆ matchingSupport Min ∧
      C ⊆ C67.O ∧
      C.card = rhoK ∧
      ∀ x ∈ C,
        let available := (Finset.univ \ matchingSupport Min) ∩
          (matchingSupport Mout \ matchingSupport Mb)
        let partners := available.filter
          ((regularityReducedGraph G cluster epsilon density).Adj x)
        8 * rhoK ≤ partners.card ∧
        (∀ y ∈ partners,
          G.IsUniform epsilon (cluster x) (cluster y) ∧
          density ≤ G.edgeDensity (cluster x) (cluster y)) ∧
        4 * rhoK ≤
          (matchingAccessEdges
            (regularityReducedGraph G cluster epsilon density)
            Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint x
            available).card := by
  classical
  let R := regularityReducedGraph G cluster epsilon density
  obtain ⟨C, hCV1, hCO, hCcard, hdegree⟩ :=
    exists_claim616_cluster_set R L miss rhoK C67 Min Mout Mb hMb
      hsupport hV1O badEdges hMbEdges hhierarchy (by simpa [R] using hcross)
  refine ⟨C, hCV1, hCO, hCcard, ?_⟩
  intro x hx
  dsimp only
  constructor
  · simpa [degreeInto, R] using hdegree x hx
  · constructor
    · intro y hy
      have hxy : R.Adj x y := (mem_filter.mp hy).2
      exact ⟨hxy.2.1, hxy.2.2⟩
    · apply four_mul_le_card_genuineMatchingAccessEdges R Mout hMout x
        ((Finset.univ \ matchingSupport Min) ∩
          (matchingSupport Mout \ matchingSupport Mb)) rhoK
      · intro y hy
        exact (mem_sdiff.mp (mem_inter.mp hy).2).1
      · exact hdegree x hx

/-- The host form specialized to the genuine matching decomposition produced
by Lemma 6.11.  In particular the `A`–`C` access required for the root layer
is derived from `D.minEdges ⊆ sourceCleanEdges`; it is not an extra
embedding or candidate hypothesis. -/
theorem exists_claim616_host_cluster_set_of_matchingDecomposition
    {B : Type u} {ι : Type v}
    [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
    (cluster : ι → Finset B) (epsilon reducedDensity : ℚ)
    (Pcluster : ClusterAssignment B ι)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (hGle : G ≤ Gdegree)
    [DecidableRel
      (regularityReducedGraph G cluster epsilon reducedDensity).Adj]
    (A Broot : ι) (L : Finset ι) (threshold quota : ℕ)
    (hLrich : L = largeClustersAtLeast Pcluster Gdegree threshold quota)
    (hAinL : A ∈ L) (hBinL : Broot ∈ L)
    (hABadj :
      (regularityReducedGraph G cluster epsilon reducedDensity).Adj A Broot)
    (rootReserve companionReserve : Finset B)
    (hrootReserve_subset : rootReserve ⊆ cluster A)
    (hcompanionReserve_subset : companionReserve ⊆ cluster Broot)
    (hrootReserve_card : rootReserve.card = quota)
    (hcompanionReserve_card : companionReserve.card = quota)
    (hrootReserve_high : ∀ z ∈ rootReserve, threshold ≤ Gdegree.degree z)
    (hcompanionReserve_high : ∀ z ∈ companionReserve,
      threshold ≤ Gdegree.degree z)
    (miss rhoK : ℕ)
    (C67 : Claim67Certificate
      (regularityReducedGraph G cluster epsilon reducedDensity) L miss)
    (sourceDensity : ι → ι → ℝ) (N eta : ℝ)
    (lowerV1 upperV1 upperV2 mbBound : ℕ)
    (D : MatchingDecomposition L C67.O miss C67
      lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L sourceDensity N A))
    (hclean : D.minEdges ⊆
      sourceCleanEdges C67.M L C67.O sourceDensity A eta D.mbEdges)
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hsourceDensityAdj : ∀ x, 0 < sourceDensity A x →
      (regularityReducedGraph G cluster epsilon reducedDensity).Adj A x)
    (hhierarchy : miss + mbBound ≤ rhoK)
    (hcross : rhoK * D.V2.card + D.V1.card * (9 * rhoK) <
      ((regularityReducedGraph G cluster epsilon reducedDensity).interedges
        D.V1 D.V2).card) :
    ∃ C : Finset ι,
      C ⊆ D.V1 ∧
      C ⊆ C67.O ∧
      C.card = rhoK ∧
      (∀ x ∈ C,
          (regularityReducedGraph G cluster epsilon reducedDensity).Adj A x ∧
          (G.IsUniform epsilon (cluster A) (cluster x) ∧
            reducedDensity ≤ G.edgeDensity (cluster A) (cluster x)) ∧
          let available := D.V2 ∩
            (matchingSupport D.Mout \ matchingSupport D.Mb)
          let partners := available.filter
            ((regularityReducedGraph G cluster epsilon reducedDensity).Adj x)
          8 * rhoK ≤ partners.card ∧
          (∀ y ∈ partners,
            G.IsUniform epsilon (cluster x) (cluster y) ∧
            reducedDensity ≤ G.edgeDensity (cluster x) (cluster y)) ∧
          4 * rhoK ≤
            (matchingAccessEdges
              (regularityReducedGraph G cluster epsilon reducedDensity)
              D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint x
              available).card) ∧
      Nonempty (IndexedHostSystem G cluster epsilon reducedDensity A Broot C D.Mout
        (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) rhoK
        Pcluster threshold quota Gdegree) := by
  let R := regularityReducedGraph G cluster epsilon reducedDensity
  have hrootLarge : A ∈
      largeClustersAtLeast Pcluster Gdegree threshold quota := by
    simpa only [hLrich] using hAinL
  have hcompanionLarge : Broot ∈
      largeClustersAtLeast Pcluster Gdegree threshold quota := by
    simpa only [hLrich] using hBinL
  have hMbLoss : 2 * D.Mb.edgeSet.ncard ≤ mbBound := by
    rw [← card_matchingSupport_eq_two_mul_edges D.Mb D.Mb_isMatching]
    exact D.Mb_support_card
  obtain ⟨C, hCV1, hCO, hCcard, hC⟩ :=
    exists_claim616_host_cluster_set G cluster epsilon reducedDensity L miss rhoK
      C67 D.Min D.Mout D.Mb D.Mout_isMatching D.Mb_isMatching
      D.support_union D.V1_subset_O D.Mb.edgeSet.ncard (le_refl _)
      (by omega) (by simpa [MatchingDecomposition.V1,
        MatchingDecomposition.V2, R] using hcross)
  have hrootAdj : ∀ x ∈ C, R.Adj A x :=
    selected_cluster_adj_distinguished D hclean heta hetaHalf
      hsourceDensityAdj hCV1
  have hCsource : C ⊆ matchingSupport C67.M := by
    intro x hx
    rw [D.support_union]
    exact Finset.mem_union_left _ (hCV1 hx)
  have hMsource : matchingSupport D.Mout ⊆ matchingSupport C67.M := by
    intro x hx
    rw [D.support_union]
    exact Finset.mem_union_right _ hx
  refine ⟨C, hCV1, hCO, hCcard, ?_, ?_⟩
  · intro x hx
    have hAx := hrootAdj x hx
    exact ⟨hAx, ⟨hAx.2.1, hAx.2.2⟩, hC x hx⟩
  · let available := D.V2 ∩
      (matchingSupport D.Mout \ matchingSupport D.Mb)
    have hW : available ⊆ matchingSupport D.Mout := by
      intro y hy
      exact (mem_sdiff.mp (mem_inter.mp hy).2).1
    have hCoutside : Disjoint C (matchingSupport D.Mout) := by
      rw [Finset.disjoint_left]
      intro y hyC hyMout
      exact Finset.disjoint_left.mp (show Disjoint D.V1 D.V2 by
        exact Finset.disjoint_sdiff) (hCV1 hyC)
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.Mout_support_subset_V2
          D hyMout)
    have hdegree : ∀ x ∈ C, 8 * rhoK ≤ degreeInto R x available := by
      intro x hx
      have hxFacts := hC x hx
      dsimp only at hxFacts
      simpa [available, MatchingDecomposition.V2, MatchingDecomposition.V1,
        degreeInto, R] using hxFacts.1
    exact ⟨indexedHostSystem_of_reducedData G cluster epsilon reducedDensity
      A Broot C D.Mout D.Mout_isMatching available rhoK hCcard Pcluster
      threshold quota Gdegree hrootLarge hcompanionLarge hABadj hcluster
      hGle
      rootReserve companionReserve hrootReserve_subset hcompanionReserve_subset
      hrootReserve_card hcompanionReserve_card hrootReserve_high
      hcompanionReserve_high
      (matchingSupport C67.M) hCsource hMsource
      hCoutside hW hrootAdj hdegree⟩

/-- Source-faithful padded specialization of the Claim-6.16 host wrapper.
The adjacent rich clusters and both quantitative reservoirs come from the
nonindependent output of quantitative Claim 6.1; callers do not supply them
as independent assumptions. -/
theorem exists_indexedHostSystem_of_richClaim61_matchingDecomposition
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (Gdegree Hregular : SimpleGraph B)
    [DecidableRel Gdegree.Adj] [DecidableRel Hregular.Adj]
    (Pcluster : ClusterAssignment B I)
    (cluster : I → Finset B) (epsilon reducedDensity : ℚ)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (hregularSub : Hregular ≤ Gdegree)
    (threshold quota miss rhoK : ℕ)
    (hquota : 0 < quota) (hreducedDensity : 0 < reducedDensity)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster epsilon reducedDensity)
      (largeClustersAtLeast Pcluster Gdegree threshold quota) miss) :
    let Lp := padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota)
    let C67 :=
      Erdos547b.ZhaoClaim616.RichClaim61Certificate.hostClaim67
        Gdegree Hregular Pcluster cluster epsilon reducedDensity
        threshold quota miss Q hreducedDensity
    ∀ (sourceDensity : EvenPadding I → EvenPadding I → ℝ) (N eta : ℝ)
      (lowerV1 upperV1 upperV2 mbBound : ℕ)
      (D : MatchingDecomposition Lp C67.O miss C67
        lowerV1 upperV1 upperV2 mbBound
        (sourceDegree C67.M Lp sourceDensity N (Sum.inl Q.A))),
      D.minEdges ⊆
        sourceCleanEdges C67.M Lp C67.O sourceDensity (Sum.inl Q.A)
          eta D.mbEdges →
      0 < eta → eta < 1 / 2 →
      (∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (regularityReducedGraph Hregular (padCluster cluster) epsilon reducedDensity).Adj
          (Sum.inl Q.A) x) →
      miss + mbBound ≤ rhoK →
      rhoK * D.V2.card + D.V1.card * (9 * rhoK) <
        ((regularityReducedGraph Hregular (padCluster cluster) epsilon reducedDensity).interedges
          D.V1 D.V2).card →
      ∃ C : Finset (EvenPadding I),
        C ⊆ D.V1 ∧ C ⊆ C67.O ∧ C.card = rhoK ∧
        Nonempty (IndexedHostSystem Hregular (padCluster cluster) epsilon reducedDensity
          (Sum.inl Q.A) (Sum.inl Q.B) C D.Mout
          (D.V2 ∩ (matchingSupport D.Mout \ matchingSupport D.Mb)) rhoK
          (padAssignment Pcluster) threshold quota Gdegree) := by
  classical
  dsimp only
  intro sourceDensity N eta lowerV1 upperV1 upperV2 mbBound D hclean
    heta hetaHalf hsourceDensityAdj hhierarchy hcross
  have hclusterPad : ∀ i,
      padCluster cluster i = clusterVertices (padAssignment Pcluster) i := by
    intro i
    rw [clusterVertices_padAssignment]
    cases i <;> simp [padCluster, hcluster]
  have hLrich :
      padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota) =
        largeClustersAtLeast (padAssignment Pcluster) Gdegree threshold quota :=
    (largeClustersAtLeast_padAssignment
      Pcluster Gdegree threshold quota hquota).symm
  have hAinL : (Sum.inl Q.A : EvenPadding I) ∈
      padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota) := by
    simpa using Q.A_mem
  have hBinL : (Sum.inl Q.B : EvenPadding I) ∈
      padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota) := by
    simpa using Q.B_mem
  have hABadj :
      (regularityReducedGraph Hregular (padCluster cluster) epsilon reducedDensity).Adj
        (Sum.inl Q.A) (Sum.inl Q.B) := by
    rw [← padGraph_regularityReducedGraph Hregular cluster epsilon reducedDensity
      hreducedDensity]
    simpa using Q.adj
  obtain ⟨C, hCV1, hCO, hCcard, _hCfacts, hHost⟩ :=
    exists_claim616_host_cluster_set_of_matchingDecomposition
      Hregular Gdegree (padCluster cluster) epsilon reducedDensity
      (padAssignment Pcluster) hclusterPad hregularSub
      (Sum.inl Q.A) (Sum.inl Q.B)
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      threshold quota hLrich hAinL hBinL hABadj
      Q.A₀ Q.B₀
      (by
        intro z hz
        simpa [padCluster, hcluster] using Q.A₀_subset hz)
      (by
        intro z hz
        simpa [padCluster, hcluster] using Q.B₀_subset hz)
      Q.A₀_card Q.B₀_card Q.A₀_high Q.B₀_high
      miss rhoK
      (Erdos547b.ZhaoClaim616.RichClaim61Certificate.hostClaim67
        Gdegree Hregular Pcluster cluster epsilon reducedDensity
        threshold quota miss Q hreducedDensity)
      sourceDensity N eta lowerV1 upperV1 upperV2 mbBound D hclean
      heta hetaHalf hsourceDensityAdj
      hhierarchy hcross
  exact ⟨C, hCV1, hCO, hCcard, hHost⟩

end Erdos547b.ZhaoClaim616

#print axioms Erdos547b.ZhaoClaim616.card_crossHeavy_ge_of_crossing_gt
#print axioms Erdos547b.ZhaoClaim616.exists_claim616_cluster_set
#print axioms Erdos547b.ZhaoClaim616.exists_claim616_cluster_set_source_constants
#print axioms Erdos547b.ZhaoClaim616.four_mul_le_card_matchingAccessEdges
#print axioms Erdos547b.ZhaoClaim616.matchingSupport_covered_by_orientedEndpoints
#print axioms Erdos547b.ZhaoClaim616.four_mul_le_card_genuineMatchingAccessEdges
#print axioms Erdos547b.ZhaoClaim616.card_indexedAllowedEdges
#print axioms Erdos547b.ZhaoClaim616.indexedMatchingEndpoint_injective
#print axioms Erdos547b.ZhaoClaim616.four_mul_le_card_indexedGenuineMatchingAccessEdges
#print axioms Erdos547b.ZhaoClaim616.uniform_dense_indexedAccessPair
#print axioms Erdos547b.ZhaoClaim616.uniform_dense_indexedMatchingPair
#print axioms Erdos547b.ZhaoClaim616.indexedHostSystem_of_reducedData
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.quota_le_rootReservoir_card
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.quota_le_companionReservoir_card
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.rootReservoir_card_eq
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.companionReservoir_card_eq
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.rootReservoir_union_companionReservoir_card_le
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.card_le_card_remove_rootReservoirs_add
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.rootReservoir_disjoint_companionReservoir
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.rootReservoir_disjoint_after_rootRemoval
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.companionReservoir_disjoint_after_companionRemoval
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.rootReservoir_disjoint_after_bothRemovals
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.companionReservoir_disjoint_after_bothRemovals
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.indexTypes_nonempty
#print axioms Erdos547b.ZhaoClaim616.IndexedHostSystem.isContained_degreeGraph
#print axioms Erdos547b.ZhaoClaim616.exists_selectedHalfF0
#print axioms Erdos547b.ZhaoClaim616.exists_selectedHalfF0_of_bad_lt
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mout_support_subset_V2
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mb_support_subset_Mout
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mb_support_subset_V2
#print axioms Erdos547b.ZhaoClaim616.incidentCoverEdges_card_le
#print axioms Erdos547b.ZhaoClaim616.subset_matchingSupport_incidentCoverSubgraph
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_isMatching
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.C_subset_Mzero_support
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_edge_card_le
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_isMatching
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_support_subset_V1
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_support_subset_V1
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_Mout_support_disjoint
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_Mout_support_disjoint
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_Mone_support_disjoint
#print axioms Erdos547b.ZhaoClaim616.sourceDegree_le_two_mul_N_mul_card
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_sourceDegree_le
#print axioms Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_sourceDegree_lower
#print axioms Erdos547b.ZhaoClaim616.exists_claim616_host_cluster_set
#print axioms Erdos547b.ZhaoClaim616.exists_claim616_host_cluster_set_of_matchingDecomposition
#print axioms Erdos547b.ZhaoClaim616.exists_indexedHostSystem_of_richClaim61_matchingDecomposition
