/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma615
import ErdosProblems.Erdos547b.Lemma612
import ErdosProblems.Erdos547b.Lemma613
import ErdosProblems.Erdos547b.Claim617
import Mathlib.Tactic

/-!
# Zhao's Lemma 6.11: the matching decomposition

This file implements the finite matching construction on pages 32--33 of
Zhao (2011).  Edges are the actual edges of the matching subgraph in the
`Claim67Certificate`.  In particular, the resulting `Min`, `Mout`, and the
optional `Mb` are genuine subgraph matchings, rather than arbitrary finsets
unrelated to the reduced graph.
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma611Full

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma615

universe u v w

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]

/-! ## Canonical orientation of the genuine matching edges -/

/-- The edge type used below is literally the edge set of a subgraph. -/
abbrev MatchingEdge (M : R.Subgraph) := M.edgeSet

/-- The two endpoints selected by `Sym2.out`. -/
def rawEndpoint (M : R.Subgraph) (e : MatchingEdge M) (c : Fin 2) : K :=
  if c = 0 then e.1.out.1 else e.1.out.2

/-- Orient an edge with an endpoint in `L` so that a large endpoint comes
first.  The definition is still total; `orientedEndpoint_zero_mem` below
uses the hypothesis that every matching edge has a large endpoint. -/
def orientedEndpoint (M : R.Subgraph) (L : Finset K)
    (e : MatchingEdge M) (c : Fin 2) : K :=
  if e.1.out.1 ∈ L then rawEndpoint M e c
  else if c = 0 then e.1.out.2 else e.1.out.1

@[simp] theorem rawEndpoint_zero (M : R.Subgraph) (e : MatchingEdge M) :
    rawEndpoint M e 0 = e.1.out.1 := by
  simp [rawEndpoint]

@[simp] theorem rawEndpoint_one (M : R.Subgraph) (e : MatchingEdge M) :
    rawEndpoint M e 1 = e.1.out.2 := by
  simp [rawEndpoint]

theorem orientedEndpoint_pair_eq (M : R.Subgraph) (L : Finset K)
    (e : MatchingEdge M) :
    s(orientedEndpoint M L e 0, orientedEndpoint M L e 1) = e.1 := by
  classical
  by_cases h : e.1.out.1 ∈ L
  · simp [orientedEndpoint, h, rawEndpoint, Sym2.mk, e.1.out_eq]
  · simp [orientedEndpoint, h, rawEndpoint, Sym2.mk, e.1.out_eq,
      Sym2.eq_swap]

theorem orientedEndpoint_adj (M : R.Subgraph) (L : Finset K)
    (e : MatchingEdge M) :
    M.Adj (orientedEndpoint M L e 0) (orientedEndpoint M L e 1) := by
  rw [← Subgraph.mem_edgeSet, orientedEndpoint_pair_eq]
  exact e.2

theorem orientedEndpoint_zero_mem (M : R.Subgraph) (L : Finset K)
    (hlarge : ∀ e : MatchingEdge M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L) (e : MatchingEdge M) :
    orientedEndpoint M L e 0 ∈ L := by
  rcases hlarge e with h | h
  · simp [orientedEndpoint, h, rawEndpoint]
  · by_cases h0 : e.1.out.1 ∈ L
    · simp [orientedEndpoint, h0, rawEndpoint]
    · simp [orientedEndpoint, h0, rawEndpoint, h]

theorem orientedEndpoint_ne (M : R.Subgraph) (L : Finset K)
    (e : MatchingEdge M) :
    orientedEndpoint M L e 0 ≠ orientedEndpoint M L e 1 :=
  (orientedEndpoint_adj M L e).ne

/-- The two endpoint occurrences of a genuine matching are all distinct.
This is the exact endpoint-injectivity hypothesis used by Claim 6.18. -/
theorem orientedEndpoint_injective
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K) :
    Function.Injective
      (fun ec : MatchingEdge M × Fin 2 => orientedEndpoint M L ec.1 ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ hcd
  change orientedEndpoint M L e c = orientedEndpoint M L f d at hcd
  have hef : e = f := by
    have heMem : orientedEndpoint M L e c ∈ M.verts := by
      fin_cases c
      · exact (orientedEndpoint_adj M L e).fst_mem
      · exact (orientedEndpoint_adj M L e).snd_mem
    have hfMem : orientedEndpoint M L f d ∈ M.verts := by
      fin_cases d
      · exact (orientedEndpoint_adj M L f).fst_mem
      · exact (orientedEndpoint_adj M L f).snd_mem
    let ve : M.verts := ⟨orientedEndpoint M L e c, heMem⟩
    let vf : M.verts := ⟨orientedEndpoint M L f d, hfMem⟩
    have hve : hM.toEdge ve = e := by
      fin_cases c
      · calc
          hM.toEdge ve = ⟨s(orientedEndpoint M L e 0,
              orientedEndpoint M L e 1), orientedEndpoint_adj M L e⟩ := by
            simpa [ve] using hM.toEdge_eq_of_adj (orientedEndpoint_adj M L e)
          _ = e := Subtype.ext (orientedEndpoint_pair_eq M L e)
      · calc
          hM.toEdge ve = ⟨s(orientedEndpoint M L e 1,
              orientedEndpoint M L e 0), (orientedEndpoint_adj M L e).symm⟩ := by
            simpa [ve] using hM.toEdge_eq_of_adj (orientedEndpoint_adj M L e).symm
          _ = e := Subtype.ext ((Sym2.eq_swap).trans
            (orientedEndpoint_pair_eq M L e))
    have hvf : hM.toEdge vf = f := by
      fin_cases d
      · calc
          hM.toEdge vf = ⟨s(orientedEndpoint M L f 0,
              orientedEndpoint M L f 1), orientedEndpoint_adj M L f⟩ := by
            simpa [vf] using hM.toEdge_eq_of_adj (orientedEndpoint_adj M L f)
          _ = f := Subtype.ext (orientedEndpoint_pair_eq M L f)
      · calc
          hM.toEdge vf = ⟨s(orientedEndpoint M L f 1,
              orientedEndpoint M L f 0), (orientedEndpoint_adj M L f).symm⟩ := by
            simpa [vf] using hM.toEdge_eq_of_adj (orientedEndpoint_adj M L f).symm
          _ = f := Subtype.ext ((Sym2.eq_swap).trans
            (orientedEndpoint_pair_eq M L f))
    calc
      e = hM.toEdge ve := hve.symm
      _ = hM.toEdge vf := by
        congr 1
        exact Subtype.ext hcd
      _ = f := hvf
  subst f
  have hfin : c = d := by
    fin_cases c <;> fin_cases d
    · rfl
    · exfalso
      exact (orientedEndpoint_ne M L e) (by simpa using hcd)
    · exfalso
      exact (orientedEndpoint_ne M L e) (by simpa using hcd.symm)
    · rfl
  subst d
  rfl

/-! ## Turning a selected edge finset into a genuine subgraph -/

/-- The subgraph consisting exactly of the selected edges of `M`, with no
isolated vertices. -/
def edgeFinsetSubgraph (M : R.Subgraph) (L : Finset K)
    (S : Finset (MatchingEdge M)) : R.Subgraph where
  verts := {x | ∃ e ∈ S,
    x = orientedEndpoint M L e 0 ∨ x = orientedEndpoint M L e 1}
  Adj x y := ∃ e ∈ S,
    (x = orientedEndpoint M L e 0 ∧ y = orientedEndpoint M L e 1) ∨
    (x = orientedEndpoint M L e 1 ∧ y = orientedEndpoint M L e 0)
  adj_sub := by
    rintro x y ⟨e, he, hxy | hxy⟩
    · simpa [hxy.1, hxy.2] using M.adj_sub (orientedEndpoint_adj M L e)
    · simpa [hxy.1, hxy.2] using M.adj_sub (orientedEndpoint_adj M L e).symm
  edge_vert := by
    rintro x y ⟨e, he, hxy | hxy⟩
    · exact ⟨e, he, Or.inl hxy.1⟩
    · exact ⟨e, he, Or.inr hxy.1⟩
  symm := ⟨by
    rintro x y ⟨e, he, hxy | hxy⟩
    · exact ⟨e, he, Or.inr ⟨hxy.2, hxy.1⟩⟩
    · exact ⟨e, he, Or.inl ⟨hxy.2, hxy.1⟩⟩⟩

@[simp] theorem mem_edgeFinsetSubgraph_verts
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M)) (x : K) :
    x ∈ (edgeFinsetSubgraph M L S).verts ↔
      ∃ e ∈ S, x = orientedEndpoint M L e 0 ∨
        x = orientedEndpoint M L e 1 := by
  rfl

theorem edgeFinsetSubgraph_adj
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    {x y : K} :
    (edgeFinsetSubgraph M L S).Adj x y ↔ ∃ e ∈ S,
      (x = orientedEndpoint M L e 0 ∧ y = orientedEndpoint M L e 1) ∨
      (x = orientedEndpoint M L e 1 ∧ y = orientedEndpoint M L e 0) := by
  rfl

theorem edgeFinsetSubgraph_isMatching
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (S : Finset (MatchingEdge M)) :
    (edgeFinsetSubgraph M L S).IsMatching := by
  intro x hx
  obtain ⟨e, he, hx0 | hx1⟩ := hx
  · refine ⟨orientedEndpoint M L e 1, ?_, ?_⟩
    · exact ⟨e, he, Or.inl ⟨hx0, rfl⟩⟩
    · intro y hxy
      obtain ⟨f, hf, hxy0 | hxy1⟩ := hxy
      · exact (hM.eq_of_adj_left
          (hx0 ▸ orientedEndpoint_adj M L e)
          (hxy0.1 ▸ hxy0.2 ▸ orientedEndpoint_adj M L f)).symm
      · exact (hM.eq_of_adj_left
          (hx0 ▸ orientedEndpoint_adj M L e)
          (hxy1.1 ▸ hxy1.2 ▸ (orientedEndpoint_adj M L f).symm)).symm
  · refine ⟨orientedEndpoint M L e 0, ?_, ?_⟩
    · exact ⟨e, he, Or.inr ⟨hx1, rfl⟩⟩
    · intro y hxy
      obtain ⟨f, hf, hxy0 | hxy1⟩ := hxy
      · exact (hM.eq_of_adj_left
          (hx1 ▸ (orientedEndpoint_adj M L e).symm)
          (hxy0.1 ▸ hxy0.2 ▸ orientedEndpoint_adj M L f)).symm
      · exact (hM.eq_of_adj_left
          (hx1 ▸ (orientedEndpoint_adj M L e).symm)
          (hxy1.1 ▸ hxy1.2 ▸ (orientedEndpoint_adj M L f).symm)).symm

theorem matchingSupport_edgeFinsetSubgraph
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M)) :
    matchingSupport (edgeFinsetSubgraph M L S) =
      S.biUnion fun e => {orientedEndpoint M L e 0,
        orientedEndpoint M L e 1} := by
  classical
  ext x
  simp [mem_matchingSupport, mem_edgeFinsetSubgraph_verts]

theorem edgeFinsetSubgraph_support_card
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (S : Finset (MatchingEdge M)) :
    (matchingSupport (edgeFinsetSubgraph M L S)).card = 2 * S.card := by
  classical
  rw [matchingSupport_edgeFinsetSubgraph]
  have hpair (e : MatchingEdge M) :
      ({orientedEndpoint M L e 0, orientedEndpoint M L e 1} : Finset K).card = 2 := by
    simp [orientedEndpoint_ne M L e]
  have hdisj : (S : Set (MatchingEdge M)).PairwiseDisjoint
      (fun e => ({orientedEndpoint M L e 0,
        orientedEndpoint M L e 1} : Finset K)) := by
    intro e he f hf hef
    change Disjoint
      ({orientedEndpoint M L e 0, orientedEndpoint M L e 1} : Finset K)
      ({orientedEndpoint M L f 0, orientedEndpoint M L f 1} : Finset K)
    rw [Finset.disjoint_left]
    intro x hxe hxf
    simp only [mem_insert, mem_singleton] at hxe hxf
    rcases hxe with rfl | rfl <;> rcases hxf with h | h
    · have := hM.eq_of_adj_left (orientedEndpoint_adj M L e)
          (h ▸ orientedEndpoint_adj M L f)
      apply hef
      apply Subtype.ext
      rw [← orientedEndpoint_pair_eq M L e,
        ← orientedEndpoint_pair_eq M L f]
      simp [h, this]
    · have := hM.eq_of_adj_left (orientedEndpoint_adj M L e)
          (h ▸ (orientedEndpoint_adj M L f).symm)
      apply hef
      apply Subtype.ext
      rw [← orientedEndpoint_pair_eq M L e,
        ← orientedEndpoint_pair_eq M L f]
      rw [h, this, Sym2.eq_swap]
    · have := hM.eq_of_adj_left (orientedEndpoint_adj M L e).symm
          (h ▸ orientedEndpoint_adj M L f)
      apply hef
      apply Subtype.ext
      rw [← orientedEndpoint_pair_eq M L e,
        ← orientedEndpoint_pair_eq M L f]
      rw [h, this, Sym2.eq_swap]
    · have := hM.eq_of_adj_left (orientedEndpoint_adj M L e).symm
          (h ▸ (orientedEndpoint_adj M L f).symm)
      apply hef
      apply Subtype.ext
      rw [← orientedEndpoint_pair_eq M L e,
        ← orientedEndpoint_pair_eq M L f]
      simp [h, this]
  rw [card_biUnion hdisj]
  simp [hpair, Nat.mul_comm]

/-! ## Edge complements and the exact support partition -/

/-- All genuine edges of a finite subgraph, as a finset of the subtype
`M.edgeSet`. -/
def allMatchingEdges (M : R.Subgraph) : Finset (MatchingEdge M) := by
  classical
  letI : Fintype (MatchingEdge M) := Fintype.ofFinite (MatchingEdge M)
  exact Finset.univ

@[simp] theorem mem_allMatchingEdges (M : R.Subgraph) (e : MatchingEdge M) :
    e ∈ allMatchingEdges M := by
  classical
  simp [allMatchingEdges]

theorem support_partition
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (S : Finset (MatchingEdge M)) :
    matchingSupport M =
      matchingSupport (edgeFinsetSubgraph M L S) ∪
      matchingSupport (edgeFinsetSubgraph M L (allMatchingEdges M \ S)) := by
  classical
  ext x
  constructor
  · intro hx
    have hxM : x ∈ M.verts := (mem_matchingSupport M x).mp hx
    obtain ⟨y, hxy, _⟩ := hM hxM
    let e : MatchingEdge M := ⟨s(x, y), hxy⟩
    have hxEnds : x = orientedEndpoint M L e 0 ∨
        x = orientedEndpoint M L e 1 := by
      have hxmem : x ∈ (e.1 : Sym2 K) := by
        exact Sym2.mem_mk_left x y
      rw [← orientedEndpoint_pair_eq M L e] at hxmem
      simpa using hxmem
    by_cases he : e ∈ S
    · exact Finset.mem_union_left _ ((mem_matchingSupport _ x).mpr ⟨e, he, hxEnds⟩)
    · exact Finset.mem_union_right _ ((mem_matchingSupport _ x).mpr
        ⟨e, by simp [he], hxEnds⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨e, he, hx0 | hx1⟩ := (mem_matchingSupport _ x).mp hx
      · exact (mem_matchingSupport M x).mpr
          (by rw [hx0]; exact (orientedEndpoint_adj M L e).fst_mem)
      · exact (mem_matchingSupport M x).mpr
          (by rw [hx1]; exact (orientedEndpoint_adj M L e).snd_mem)
    · obtain ⟨e, he, hx0 | hx1⟩ := (mem_matchingSupport _ x).mp hx
      · exact (mem_matchingSupport M x).mpr
          (by rw [hx0]; exact (orientedEndpoint_adj M L e).fst_mem)
      · exact (mem_matchingSupport M x).mpr
          (by rw [hx1]; exact (orientedEndpoint_adj M L e).snd_mem)

/-! ## The capped choice used in the source -/

/-- Keep all edges of `S` if there are at most `cap`; otherwise choose an
actual `cap`-edge submatching. -/
def cappedSubfamily {E : Type*} [DecidableEq E]
    (S : Finset E) (cap : ℕ) : Finset E := by
  classical
  by_cases h : S.card ≤ cap
  · exact S
  · exact Classical.choose (Finset.exists_subset_card_eq (Nat.le_of_not_ge h))

theorem cappedSubfamily_subset {E : Type*} [DecidableEq E]
    (S : Finset E) (cap : ℕ) : cappedSubfamily S cap ⊆ S := by
  classical
  simp only [cappedSubfamily]
  split
  · exact Subset.rfl
  · exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (Nat.le_of_not_ge ‹¬ S.card ≤ cap›))).1

theorem card_cappedSubfamily {E : Type*} [DecidableEq E]
    (S : Finset E) (cap : ℕ) :
    (cappedSubfamily S cap).card = min S.card cap := by
  classical
  simp only [cappedSubfamily]
  split
  next h => simp [h]
  next h =>
    rw [(Classical.choose_spec
      (Finset.exists_subset_card_eq (Nat.le_of_not_ge h))).2]
    simp [Nat.le_of_not_ge h]

/-! ## The source sets `V1`, `V2`, `S1`, and `L1` -/

/-- Zhao's `S1`: vertices whose partner in `Min` is large. -/
def sourceS1 (Min : R.Subgraph) (L : Finset K) : Finset K :=
  Erdos547b.ZhaoClaim617.matchingPartnerSet Min L

/-- Zhao's `L1 = V1 \ S1`. -/
def sourceL1 (Min : R.Subgraph) (L : Finset K) : Finset K :=
  matchingSupport Min \ sourceS1 Min L

theorem sourceS1_subset_support (Min : R.Subgraph) (L : Finset K) :
    sourceS1 Min L ⊆ matchingSupport Min :=
  Erdos547b.ZhaoClaim617.matchingPartnerSet_subset_support Min L

theorem sourceL1_subset_large
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (hlarge : ∀ e : MatchingEdge M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L)
    (S : Finset (MatchingEdge M)) :
    sourceL1 (edgeFinsetSubgraph M L S) L ⊆ L := by
  classical
  intro x hx
  have hxV := (Finset.mem_sdiff.mp hx).1
  have hxNotS := (Finset.mem_sdiff.mp hx).2
  obtain ⟨e, he, hx0 | hx1⟩ := (mem_matchingSupport _ x).mp hxV
  · rw [hx0]
    exact orientedEndpoint_zero_mem M L hlarge e
  · exfalso
    apply hxNotS
    rw [sourceS1, Erdos547b.ZhaoClaim617.matchingPartnerSet]
    apply Finset.mem_filter.mpr
    refine ⟨hxV, orientedEndpoint M L e 0,
      orientedEndpoint_zero_mem M L hlarge e, ?_⟩
    exact ⟨e, he, Or.inl ⟨rfl, hx1⟩⟩

theorem sourceL1_subset_large_inter
    (M : R.Subgraph) (hM : M.IsMatching) (L O : Finset K)
    (hlarge : ∀ e : MatchingEdge M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L)
    (S : Finset (MatchingEdge M))
    (hO : matchingSupport (edgeFinsetSubgraph M L S) ⊆ O) :
    sourceL1 (edgeFinsetSubgraph M L S) L ⊆ L ∩ O := by
  intro x hx
  exact Finset.mem_inter.mpr ⟨sourceL1_subset_large M hM L hlarge S hx,
    hO (Finset.mem_sdiff.mp hx).1⟩

/-- Choose the genuine matching edge whose large endpoint is `C`.  Outside
the source set `L1` the function uses the supplied genuine default edge;
Claim 6.18 only evaluates it on `L1`. -/
def sourceEdgeOf (M : R.Subgraph) (L : Finset K)
    (S : Finset (MatchingEdge M)) (default : MatchingEdge M) (C : K) :
    MatchingEdge M := by
  classical
  by_cases h : ∃ e ∈ S, orientedEndpoint M L e 0 = C
  · exact Classical.choose h
  · exact default

theorem sourceEdgeOf_spec
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (hlarge : ∀ e : MatchingEdge M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L)
    (S : Finset (MatchingEdge M)) (default : MatchingEdge M)
    {C : K} (hC : C ∈ sourceL1 (edgeFinsetSubgraph M L S) L) :
    sourceEdgeOf M L S default C ∈ S ∧
      orientedEndpoint M L (sourceEdgeOf M L S default C) 0 = C ∧
      orientedEndpoint M L (sourceEdgeOf M L S default C) 1 ∈
        sourceS1 (edgeFinsetSubgraph M L S) L := by
  classical
  have hCV := (Finset.mem_sdiff.mp hC).1
  have hCnot := (Finset.mem_sdiff.mp hC).2
  obtain ⟨e, he, hC0 | hC1⟩ := (mem_matchingSupport _ C).mp hCV
  · have hex : ∃ e ∈ S, orientedEndpoint M L e 0 = C := ⟨e, he, hC0.symm⟩
    have heOfMem : sourceEdgeOf M L S default C ∈ S := by
      simp only [sourceEdgeOf, dif_pos hex]
      exact (Classical.choose_spec hex).1
    have heOfC : orientedEndpoint M L (sourceEdgeOf M L S default C) 0 = C := by
      simp only [sourceEdgeOf, dif_pos hex]
      exact (Classical.choose_spec hex).2
    refine ⟨heOfMem, heOfC, ?_⟩
    rw [sourceS1, Erdos547b.ZhaoClaim617.matchingPartnerSet]
    apply Finset.mem_filter.mpr
    refine ⟨(mem_matchingSupport _ _).mpr
      ⟨sourceEdgeOf M L S default C, heOfMem, Or.inr rfl⟩,
      C, sourceL1_subset_large M hM L hlarge S hC, ?_⟩
    exact ⟨sourceEdgeOf M L S default C, heOfMem,
      Or.inl ⟨heOfC.symm, rfl⟩⟩
  · exfalso
    apply hCnot
    rw [sourceS1, Erdos547b.ZhaoClaim617.matchingPartnerSet]
    apply Finset.mem_filter.mpr
    refine ⟨hCV, orientedEndpoint M L e 0,
      orientedEndpoint_zero_mem M L hlarge e, ?_⟩
    exact ⟨e, he, Or.inl ⟨rfl, hC1⟩⟩

/-! ## A single package for Claims 6.16--6.18 -/

/-- The finite data produced by the source construction.  Only edge
finsets and their proved quantitative properties are stored.  All graph
objects below (`Min`, `Mout`, and `Mb`) are defined from those edge finsets,
so none can be an unrelated assumed subgraph. -/
structure MatchingDecomposition
    (L O : Finset K) (miss : ℕ) (C67 : Claim67Certificate R L miss)
    (lowerV1 upperV1 upperV2 mbBound : ℕ)
    (degreeA : Finset (MatchingEdge C67.M) → ℝ) where
  minEdges : Finset (MatchingEdge C67.M)
  mbEdges : Finset (MatchingEdge C67.M)
  min_nonempty : minEdges.Nonempty
  min_endpoint_O : ∀ e ∈ minEdges, ∀ c,
    orientedEndpoint C67.M L e c ∈ O
  min_card_lower : lowerV1 ≤ 2 * minEdges.card
  min_card_upper : 2 * minEdges.card ≤ upperV1
  complement_card_upper : Fintype.card K - 2 * minEdges.card ≤ upperV2
  /-- The literal `A`-capacity target used when `minEdges` was selected. -/
  targetA : ℝ
  /-- Unlike the older positivity-only projection below, this retains the
  quantitative margin needed by Lemma 6.14(2). -/
  degreeA_target_lower : targetA < degreeA minEdges
  degreeA_lower : degreeA minEdges > 0
  mb_subset : mbEdges ⊆ allMatchingEdges C67.M \ minEdges
  mb_card : 2 * mbEdges.card ≤ mbBound

namespace MatchingDecomposition

variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate R L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
  degreeA)

/-- The actual source submatching `M_in`. -/
def Min : R.Subgraph := edgeFinsetSubgraph C67.M L D.minEdges

/-- The actual edge complement `M_out = M \ M_in`. -/
def Mout : R.Subgraph :=
  edgeFinsetSubgraph C67.M L (allMatchingEdges C67.M \ D.minEdges)

/-- The actual optional reserved matching. -/
def Mb : R.Subgraph := edgeFinsetSubgraph C67.M L D.mbEdges

def V1 : Finset K := matchingSupport D.Min
def V2 : Finset K := Finset.univ \ D.V1
def S1 : Finset K := sourceS1 D.Min L
def L1 : Finset K := sourceL1 D.Min L

theorem Min_isMatching : D.Min.IsMatching :=
  edgeFinsetSubgraph_isMatching C67.M C67.isMatching L D.minEdges

theorem Mout_isMatching : D.Mout.IsMatching :=
  edgeFinsetSubgraph_isMatching C67.M C67.isMatching L
    (allMatchingEdges C67.M \ D.minEdges)

theorem Mb_isMatching : D.Mb.IsMatching :=
  edgeFinsetSubgraph_isMatching C67.M C67.isMatching L D.mbEdges

theorem support_union :
    matchingSupport C67.M = matchingSupport D.Min ∪ matchingSupport D.Mout :=
  support_partition C67.M C67.isMatching L D.minEdges

theorem V1_subset_O : D.V1 ⊆ O := by
  intro x hx
  obtain ⟨e, he, hx0 | hx1⟩ := (mem_matchingSupport _ x).mp hx
  · exact hx0 ▸ D.min_endpoint_O e he 0
  · exact hx1 ▸ D.min_endpoint_O e he 1

theorem V1_card : D.V1.card = 2 * D.minEdges.card :=
  edgeFinsetSubgraph_support_card C67.M C67.isMatching L D.minEdges

theorem V1_card_lower : lowerV1 ≤ D.V1.card := by
  rw [D.V1_card]
  exact D.min_card_lower

theorem V1_card_upper : D.V1.card ≤ upperV1 := by
  rw [D.V1_card]
  exact D.min_card_upper

theorem V2_card : D.V2.card = Fintype.card K - D.V1.card := by
  change (Finset.univ \ D.V1).card = Fintype.card K - D.V1.card
  rw [Finset.card_sdiff]
  simp

theorem V2_card_upper : D.V2.card ≤ upperV2 := by
  rw [D.V2_card, D.V1_card]
  exact D.complement_card_upper

theorem Mb_support_card : (matchingSupport D.Mb).card ≤ mbBound := by
  dsimp only [Mb]
  rw [edgeFinsetSubgraph_support_card C67.M C67.isMatching L D.mbEdges]
  exact D.mb_card

theorem L1_subset_large_inter
    (hlarge : ∀ e : MatchingEdge C67.M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L) :
    D.L1 ⊆ L ∩ O :=
  sourceL1_subset_large_inter C67.M C67.isMatching L O hlarge D.minEdges
    D.V1_subset_O

theorem endpoint_mem_V1_iff
    (e : MatchingEdge C67.M) (c : Fin 2) :
    orientedEndpoint C67.M L e c ∈ D.V1 ↔ e ∈ D.minEdges := by
  constructor
  · intro heV
    obtain ⟨f, hf, h0 | h1⟩ := (mem_matchingSupport _ _).mp heV
    · let hinj := orientedEndpoint_injective C67.M C67.isMatching L
      have hp : (e, c) = (f, (0 : Fin 2)) := hinj (by simpa only using h0)
      have hef : e = f := congrArg Prod.fst hp
      rw [hef]
      exact hf
    · let hinj := orientedEndpoint_injective C67.M C67.isMatching L
      have hp : (e, c) = (f, (1 : Fin 2)) := hinj (by simpa only using h1)
      have hef : e = f := congrArg Prod.fst hp
      rw [hef]
      exact hf
  · intro he
    fin_cases c
    · exact (mem_matchingSupport _ _).mpr ⟨e, he, Or.inl rfl⟩
    · exact (mem_matchingSupport _ _).mpr ⟨e, he, Or.inr rfl⟩

/-- Every original matching edge lies wholly in `V1` or wholly in `V2`.
This is Claim 6.18's `hV2pair`. -/
theorem endpoint_mem_V2_iff (e : MatchingEdge C67.M) :
    orientedEndpoint C67.M L e 0 ∈ D.V2 ↔
      orientedEndpoint C67.M L e 1 ∈ D.V2 := by
  simp only [V2, Finset.mem_sdiff, Finset.mem_univ, true_and,
    D.endpoint_mem_V1_iff]

/-- The complete matching-edge indexing covers every vertex of `C67.M`. -/
theorem support_covered (x : K) (hx : x ∈ matchingSupport C67.M) :
    ∃ e ∈ allMatchingEdges C67.M,
      x = orientedEndpoint C67.M L e 0 ∨
      x = orientedEndpoint C67.M L e 1 := by
  have hxM := (mem_matchingSupport C67.M x).mp hx
  obtain ⟨y, hxy, _⟩ := C67.isMatching hxM
  let e : MatchingEdge C67.M := ⟨s(x, y), hxy⟩
  refine ⟨e, mem_allMatchingEdges C67.M e, ?_⟩
  have hxmem : x ∈ (e.1 : Sym2 K) := Sym2.mem_mk_left x y
  rw [← orientedEndpoint_pair_eq C67.M L e] at hxmem
  simpa using hxmem

def defaultEdge : MatchingEdge C67.M := Classical.choose D.min_nonempty

def edgeOf (C : K) : MatchingEdge C67.M :=
  sourceEdgeOf C67.M L D.minEdges D.defaultEdge C

theorem edgeOf_spec
    (hlarge : ∀ e : MatchingEdge C67.M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L)
    {C : K} (hC : C ∈ D.L1) :
    D.edgeOf C ∈ allMatchingEdges C67.M ∧
      orientedEndpoint C67.M L (D.edgeOf C) 0 = C ∧
      orientedEndpoint C67.M L (D.edgeOf C) 1 ∈ D.S1 := by
  have h := sourceEdgeOf_spec C67.M C67.isMatching L hlarge D.minEdges
    D.defaultEdge hC
  exact ⟨mem_allMatchingEdges C67.M _, h.2.1, h.2.2⟩

/-- On the source set `L1`, `edgeOf` really is one of the selected
`M_in` edges.  This stronger membership fact is needed when Claim 6.14
reserves the edges indexed by its selected cluster set. -/
theorem edgeOf_mem_minEdges
    (hlarge : ∀ e : MatchingEdge C67.M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L)
    {C : K} (hC : C ∈ D.L1) :
    D.edgeOf C ∈ D.minEdges := by
  exact (sourceEdgeOf_spec C67.M C67.isMatching L hlarge D.minEdges
    D.defaultEdge hC).1

end MatchingDecomposition

variable {miss : ℕ}

/-! ## The literal filters on pages 32--33 -/

/-- `M_small` from the source: outside `M_unbal`, at least one endpoint has
density below `eta`. -/
def sourceSmallEdges (M : R.Subgraph) (L : Finset K)
    (density : K → K → ℝ) (A : K) (eta : ℝ) :
    Finset (MatchingEdge M) :=
  ((allMatchingEdges M) \
      unbalancedEdges (allMatchingEdges M)
        (fun e c => density A (orientedEndpoint M L e c)) eta).filter
    (fun e => density A (orientedEndpoint M L e 0) < eta ∨
      density A (orientedEndpoint M L e 1) < eta)

/-- Zhao's `M'_in` before the possible outside-`O` edge is removed. -/
def sourcePrecleanEdges (M : R.Subgraph) (L : Finset K)
    (density : K → K → ℝ) (A : K) (eta : ℝ)
    (Mb : Finset (MatchingEdge M)) : Finset (MatchingEdge M) :=
  (((allMatchingEdges M \
      unbalancedEdges (allMatchingEdges M)
        (fun e c => density A (orientedEndpoint M L e c)) eta) \
      nonextremeEdges (allMatchingEdges M)
        (fun e c => density A (orientedEndpoint M L e c)) eta) \
      sourceSmallEdges M L density A eta) \ Mb

/-- Remove precisely the good edges with an endpoint outside `O`.  Claim
6.7(3) says this deletes at most one edge, but defining the cleanup this way
makes `V1 ⊆ O` unconditional. -/
def sourceCleanEdges (M : R.Subgraph) (L O : Finset K)
    (density : K → K → ℝ) (A : K) (eta : ℝ)
    (Mb : Finset (MatchingEdge M)) : Finset (MatchingEdge M) :=
  (sourcePrecleanEdges M L density A eta Mb).filter fun e =>
    orientedEndpoint M L e 0 ∈ O ∧ orientedEndpoint M L e 1 ∈ O

/-- The edges deleted in the final Claim-6.7 cleanup. -/
def sourceOutsideEdges (M : R.Subgraph) (L O : Finset K)
    (density : K → K → ℝ) (A : K) (eta : ℝ)
    (Mb : Finset (MatchingEdge M)) : Finset (MatchingEdge M) :=
  (sourcePrecleanEdges M L density A eta Mb).filter fun e =>
    ¬(orientedEndpoint M L e 0 ∈ O ∧ orientedEndpoint M L e 1 ∈ O)

/-- Select an endpoint outside `O` on an edge in `sourceOutsideEdges`. -/
def outsideSide (M : R.Subgraph) (L O : Finset K)
    (e : MatchingEdge M) : Fin 2 :=
  if orientedEndpoint M L e 0 ∈ O then 1 else 0

def outsideEndpoint (M : R.Subgraph) (L O : Finset K)
    (e : MatchingEdge M) : K :=
  orientedEndpoint M L e (outsideSide M L O e)

theorem sourceCleanEdges_subset_all
    (M : R.Subgraph) (L O : Finset K) (density : K → K → ℝ)
    (A : K) (eta : ℝ) (Mb : Finset (MatchingEdge M)) :
    sourceCleanEdges M L O density A eta Mb ⊆ allMatchingEdges M := by
  intro e he
  simp only [sourceCleanEdges, sourcePrecleanEdges, Finset.mem_filter,
    Finset.mem_sdiff] at he
  exact he.1.1.1.1.1

theorem sourceCleanEdges_disjoint_reserved
    (M : R.Subgraph) (L O : Finset K) (density : K → K → ℝ)
    (A : K) (eta : ℝ) (Mb : Finset (MatchingEdge M)) :
    Disjoint (sourceCleanEdges M L O density A eta Mb) Mb := by
  rw [Finset.disjoint_left]
  intro e he hMb
  simp only [sourceCleanEdges, sourcePrecleanEdges, Finset.mem_filter,
    Finset.mem_sdiff] at he
  exact he.1.2 hMb

/-- Every edge surviving the literal filters has the endpoint estimates in
Lemma 6.11(i). -/
theorem sourceCleanEdges_density
    (M : R.Subgraph) (L O : Finset K) (density : K → K → ℝ)
    (A : K) (eta : ℝ) (heta : 0 < eta) (Mb : Finset (MatchingEdge M))
    {e : MatchingEdge M}
    (he : e ∈ sourceCleanEdges M L O density A eta Mb) :
    1 - 2 * eta < density A (orientedEndpoint M L e 0) ∧
    1 - 2 * eta < density A (orientedEndpoint M L e 1) ∧
    2 - 3 * eta <
      density A (orientedEndpoint M L e 0) +
        density A (orientedEndpoint M L e 1) := by
  classical
  let d0 := density A (orientedEndpoint M L e 0)
  let d1 := density A (orientedEndpoint M L e 1)
  have he' := he
  simp only [sourceCleanEdges, sourcePrecleanEdges, Finset.mem_filter,
    Finset.mem_sdiff] at he'
  have heAll : e ∈ allMatchingEdges M := he'.1.1.1.1.1
  have hnotUnbal : e ∉ unbalancedEdges (allMatchingEdges M)
      (fun e c => density A (orientedEndpoint M L e c)) eta := he'.1.1.1.1.2
  have hnotNonex : e ∉ nonextremeEdges (allMatchingEdges M)
      (fun e c => density A (orientedEndpoint M L e c)) eta := he'.1.1.1.2
  have hnotSmall : e ∉ sourceSmallEdges M L density A eta := he'.1.1.2
  have hbal : |d0 - d1| < eta := by
    apply lt_of_not_ge
    intro h
    exact hnotUnbal (mem_unbalancedEdges.mpr ⟨heAll, h⟩)
  have hlower : eta ≤ d0 ∧ eta ≤ d1 := by
    constructor
    · apply le_of_not_gt
      intro h
      apply hnotSmall
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨heAll, hnotUnbal⟩, Or.inl h⟩
    · apply le_of_not_gt
      intro h
      apply hnotSmall
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨heAll, hnotUnbal⟩, Or.inr h⟩
  have hhigh : 1 - eta < d0 ∨ 1 - eta < d1 := by
    by_contra h
    push Not at h
    exact hnotNonex (mem_nonextremeEdges.mpr
      ⟨heAll, hlower.1, h.1, hlower.2, h.2⟩)
  rcases abs_lt.mp hbal with ⟨hbal0, hbal1⟩
  rcases hhigh with h0 | h1
  · constructor <;> dsimp [d0, d1] at *
    · linarith
    · constructor <;> linarith
  · constructor <;> dsimp [d0, d1] at *
    · linarith
    · constructor
      · linarith
      · linarith

/-- Claim 6.7(3) deletes at most one matching edge from `M'_in`.  The proof
maps every such edge injectively to an actual vertex of
`matchingDoubleNeighborSet R C67.M A \ C67.O`. -/
theorem sourceOutsideEdges_card_le_one
    (C67 : Claim67Certificate R L miss) (A : K) (hAO : A ∈ C67.O)
    (density : K → K → ℝ) (eta : ℝ) (heta : 0 < eta)
    (hsmallEta : 2 * eta < 1)
    (Mb : Finset (MatchingEdge C67.M))
    (hdensityAdj : ∀ x, 0 < density A x → R.Adj A x) :
    (sourceOutsideEdges C67.M L C67.O density A eta Mb).card ≤ 1 := by
  classical
  let Bad := sourceOutsideEdges C67.M L C67.O density A eta Mb
  let Outside : Finset K :=
    (matchingDoubleNeighborSet R C67.M A \ (C67.O : Set K)).toFinite.toFinset
  have hOutsideCard : Outside.card ≤ 1 := by
    change ((matchingDoubleNeighborSet R C67.M A \
      (C67.O : Set K)).toFinite.toFinset).card ≤ 1
    rw [← Set.ncard_eq_toFinset_card]
    exact C67.doubleNeighbor_outside A hAO
  have hBadDensity (e : MatchingEdge C67.M) (he : e ∈ Bad) :
      0 < density A (orientedEndpoint C67.M L e 0) ∧
      0 < density A (orientedEndpoint C67.M L e 1) := by
    have hePre : e ∈ sourcePrecleanEdges C67.M L density A eta Mb :=
      (Finset.mem_filter.mp he).1
    have heCleanUniv : e ∈ sourceCleanEdges C67.M L Finset.univ density A eta Mb := by
      exact Finset.mem_filter.mpr ⟨hePre, by simp⟩
    have hd := sourceCleanEdges_density C67.M L Finset.univ density A eta heta Mb
      heCleanUniv
    constructor <;> linarith [hd.1, hd.2.1]
  have houtside (e : MatchingEdge C67.M) (he : e ∈ Bad) :
      outsideEndpoint C67.M L C67.O e ∉ C67.O := by
    have hbad := (Finset.mem_filter.mp he).2
    by_cases h0 : orientedEndpoint C67.M L e 0 ∈ C67.O
    · have h1 : orientedEndpoint C67.M L e 1 ∉ C67.O := by
        intro h1
        exact hbad ⟨h0, h1⟩
      simpa [outsideEndpoint, outsideSide, h0] using h1
    · simpa [outsideEndpoint, outsideSide, h0] using h0
  have hmap : Bad.image (outsideEndpoint C67.M L C67.O) ⊆ Outside := by
    intro x hx
    obtain ⟨e, heBad, rfl⟩ := Finset.mem_image.mp hx
    have hd := hBadDensity e heBad
    have hAdj0 := hdensityAdj _ hd.1
    have hAdj1 := hdensityAdj _ hd.2
    have hdouble0 : orientedEndpoint C67.M L e 0 ∈
        matchingDoubleNeighborSet R C67.M A := by
      exact ⟨(orientedEndpoint_adj C67.M L e).fst_mem,
        orientedEndpoint C67.M L e 1, orientedEndpoint_adj C67.M L e,
        hAdj0, hAdj1⟩
    have hdouble1 : orientedEndpoint C67.M L e 1 ∈
        matchingDoubleNeighborSet R C67.M A := by
      exact ⟨(orientedEndpoint_adj C67.M L e).snd_mem,
        orientedEndpoint C67.M L e 0, (orientedEndpoint_adj C67.M L e).symm,
        hAdj1, hAdj0⟩
    change outsideEndpoint C67.M L C67.O e ∈
      (matchingDoubleNeighborSet R C67.M A \
        (C67.O : Set K)).toFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    by_cases h0 : orientedEndpoint C67.M L e 0 ∈ C67.O
    · have hout : orientedEndpoint C67.M L e 1 ∉ C67.O := by
        simpa [outsideEndpoint, outsideSide, h0] using houtside e heBad
      simpa [outsideEndpoint, outsideSide, h0] using
        (show orientedEndpoint C67.M L e 1 ∈
          matchingDoubleNeighborSet R C67.M A \ (C67.O : Set K) from
            ⟨hdouble1, hout⟩)
    · have hout : orientedEndpoint C67.M L e 0 ∉ C67.O := by
        simpa [outsideEndpoint, outsideSide, h0] using houtside e heBad
      simpa [outsideEndpoint, outsideSide, h0] using
        (show orientedEndpoint C67.M L e 0 ∈
          matchingDoubleNeighborSet R C67.M A \ (C67.O : Set K) from
            ⟨hdouble0, hout⟩)
  have hinj : Set.InjOn (outsideEndpoint C67.M L C67.O) (Bad : Set _) := by
    intro e he f hf hef
    have hp : (e, outsideSide C67.M L C67.O e) =
        (f, outsideSide C67.M L C67.O f) :=
      orientedEndpoint_injective C67.M C67.isMatching L hef
    exact congrArg Prod.fst hp
  calc
    Bad.card = (Bad.image (outsideEndpoint C67.M L C67.O)).card := by
      symm
      rw [Finset.card_image_iff]
      exact hinj
    _ ≤ Outside.card := Finset.card_le_card hmap
    _ ≤ 1 := hOutsideCard

/-- The degree functional used by Lemma 6.11. -/
def sourceDegree (M : R.Subgraph) (L : Finset K)
    (density : K → K → ℝ) (N : ℝ) (C : K)
    (S : Finset (MatchingEdge M)) : ℝ :=
  clusterMatchingDegree S (orientedEndpoint M L) density N C

theorem sourceDegree_eq_sum (M : R.Subgraph) (L : Finset K)
    (density : K → K → ℝ) (N : ℝ) (C : K)
    (S : Finset (MatchingEdge M)) :
    sourceDegree M L density N C S =
      ∑ e ∈ S, N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)) := rfl

/-! ## The actual capped selection -/

/-- Construct `M_in` from the literal cleaned family.  `hdeletionBudget`
is the primitive arithmetic estimate proved in the source by separately
bounding `M_unbal`, `M_nonex`, `M_small`, the optional `Mb`, and the one
outside-`O` edge.  It mentions only the explicitly defined raw filters, not
the desired submatching or any embedding conclusion. -/
noncomputable def matchingDecomposition_of_source_filters
    (C67 : Claim67Certificate R L miss) (O : Finset K)
    (A : K) (density : K → K → ℝ) (N eta targetA : ℝ)
    (cap lowerV1 upperV1 upperV2 mbBound : ℕ)
    (MbEdges : Finset (MatchingEdge C67.M))
    (hN : 0 < N) (heta : 0 < eta) (htarget : 0 ≤ targetA)
    (hnonneg : ∀ e : MatchingEdge C67.M,
      0 ≤ N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1)))
    (hdeletionBudget :
      (∑ e ∈ allMatchingEdges C67.M \
          sourceCleanEdges C67.M L O density A eta MbEdges,
        N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1))) <
        sourceDegree C67.M L density N A (allMatchingEdges C67.M) - targetA)
    (hcap : 0 < cap)
    (hcapEnough : targetA < (cap : ℝ) * (N * (2 - 3 * eta)))
    (hlower : ∀ S : Finset (MatchingEdge C67.M),
      S ⊆ allMatchingEdges C67.M → targetA < sourceDegree C67.M L density N A S →
      lowerV1 ≤ 2 * S.card)
    (hupper : 2 * cap ≤ upperV1)
    (htotalCard : Fintype.card K ≤ lowerV1 + upperV2)
    (hMbSubset : MbEdges ⊆ allMatchingEdges C67.M)
    (hMbCard : 2 * MbEdges.card ≤ mbBound) :
    MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L density N A) := by
  classical
  let Clean := sourceCleanEdges C67.M L O density A eta MbEdges
  let MinEdges := cappedSubfamily Clean cap
  have hCleanAll : Clean ⊆ allMatchingEdges C67.M :=
    sourceCleanEdges_subset_all C67.M L O density A eta MbEdges
  have hMinClean : MinEdges ⊆ Clean := cappedSubfamily_subset Clean cap
  have hsumSplit := Finset.sum_sdiff hCleanAll
    (f := fun e : MatchingEdge C67.M =>
      N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1)))
  have hCleanDegree : targetA < sourceDegree C67.M L density N A Clean := by
    rw [sourceDegree_eq_sum]
    rw [sourceDegree_eq_sum] at hdeletionBudget
    linarith
  have hMinDegree : targetA < sourceDegree C67.M L density N A MinEdges := by
    by_cases hsmall : Clean.card ≤ cap
    · have hEq : MinEdges = Clean := by
        simp [MinEdges, cappedSubfamily, hsmall]
      simpa [hEq] using hCleanDegree
    · have hcard : MinEdges.card = cap := by
        rw [card_cappedSubfamily]
        exact Nat.min_eq_right (show cap ≤ Clean.card by omega)
      have hnonempty : MinEdges.Nonempty := Finset.card_pos.mp (by omega)
      rw [sourceDegree_eq_sum]
      calc
        targetA < (cap : ℝ) * (N * (2 - 3 * eta)) := hcapEnough
        _ = ∑ _e ∈ MinEdges, N * (2 - 3 * eta) := by simp [hcard]
        _ < ∑ e ∈ MinEdges,
            N * (density A (orientedEndpoint C67.M L e 0) +
              density A (orientedEndpoint C67.M L e 1)) := by
          apply Finset.sum_lt_sum_of_nonempty hnonempty
          intro e he
          have hd := sourceCleanEdges_density C67.M L O density A eta heta MbEdges
            (hMinClean he)
          exact mul_lt_mul_of_pos_left hd.2.2 hN
  have hMinNonempty : MinEdges.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hMinDegree' := hMinDegree
    rw [h] at hMinDegree'
    have : targetA < 0 := by
      simpa [sourceDegree, clusterMatchingDegree] using hMinDegree'
    linarith
  have hMinO : ∀ e ∈ MinEdges, ∀ c,
      orientedEndpoint C67.M L e c ∈ O := by
    intro e he c
    have heClean := hMinClean he
    have hends := (Finset.mem_filter.mp heClean).2
    fin_cases c
    · exact hends.1
    · exact hends.2
  have hMinCardUpper : 2 * MinEdges.card ≤ upperV1 := by
    have hc : MinEdges.card ≤ cap := by
      rw [card_cappedSubfamily]
      exact min_le_right _ _
    omega
  have hMinCardLower : lowerV1 ≤ 2 * MinEdges.card :=
    hlower MinEdges (hMinClean.trans hCleanAll) hMinDegree
  have hComplement : Fintype.card K - 2 * MinEdges.card ≤ upperV2 := by
    omega
  have hMbDisj : Disjoint MinEdges MbEdges :=
    (Finset.disjoint_of_subset_left hMinClean
      (sourceCleanEdges_disjoint_reserved C67.M L O density A eta MbEdges))
  refine {
    minEdges := MinEdges
    mbEdges := MbEdges
    min_nonempty := hMinNonempty
    min_endpoint_O := hMinO
    min_card_lower := hMinCardLower
    min_card_upper := hMinCardUpper
    complement_card_upper := hComplement
    targetA := targetA
    degreeA_target_lower := hMinDegree
    degreeA_lower := lt_of_le_of_lt htarget hMinDegree
    mb_subset := ?_
    mb_card := hMbCard }
  intro e he
  exact Finset.mem_sdiff.mpr ⟨hMbSubset he,
    fun heMin => Finset.disjoint_left.mp hMbDisj heMin he⟩

/-! ## Conditional construction of the reserved matching -/

/-- The quantitative information carried by the optional matching `M_b`.
It records the actual `B`-degree functional, rather than only the cardinality
of the selected edge set.  The implication fields mirror the two source
branches: below the cutoff `M_b` carries the required capacity, while above
the cutoff it is empty. -/
structure OptionalReservedCapacity
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (degreeB : Finset (MatchingEdge C67.M) → ℝ)
    (targetB N fb cutoff : ℝ) (mbEdgesBound : ℕ) : Prop where
  small_lower : fb < cutoff → targetB ≤ degreeB D.mbEdges
  small_upper : fb < cutoff → degreeB D.mbEdges < targetB + 2 * N
  small_card : fb < cutoff → D.mbEdges.card ≤ mbEdgesBound
  /-- Every edge selected in the small-`f_b` branch has genuinely positive
  `B`-contribution.  For the concrete `sourceDegree` functional this is the
  singleton edge contribution, and hence supplies a B-facing endpoint. -/
  small_singleton_pos : fb < cutoff → ∀ e ∈ D.mbEdges, 0 < degreeB {e}
  large_empty : ¬ fb < cutoff → D.mbEdges = ∅

/-- Source-shaped constructor combining Lemma 6.12 with the literal
Lemma-6.11 filters.  In the small-`f_b` branch it actually constructs `Mb`
by the decreasing-prefix theorem; in the other branch `Mb` is definitionally
empty.  The deletion-budget premise is uniform over every submatching of the
proved size and is the raw hierarchy calculation in the paper. -/
theorem exists_matchingDecomposition_of_claim67
    (C67 : Claim67Certificate R L miss)
    (A B : K) (density : K → K → ℝ)
    (N eta targetA targetB fb cutoff : ℝ)
    (cap lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
    (hN : 0 < N) (heta : 0 < eta) (htargetA : 0 ≤ targetA)
    (htargetB : 0 ≤ targetB)
    (hAnonneg : ∀ e : MatchingEdge C67.M,
      0 ≤ N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1)))
    (hBnonneg : ∀ e : MatchingEdge C67.M,
      0 ≤ N * (density B (orientedEndpoint C67.M L e 0) +
        density B (orientedEndpoint C67.M L e 1)))
    (hBcap : ∀ e : MatchingEdge C67.M,
      N * (density B (orientedEndpoint C67.M L e 0) +
        density B (orientedEndpoint C67.M L e 1)) ≤ 2 * N)
    (hBtotal : targetB ≤ sourceDegree C67.M L density N B
      (allMatchingEdges C67.M))
    (hBtotalPos : 0 < sourceDegree C67.M L density N B
      (allMatchingEdges C67.M))
    (hBcard : ((allMatchingEdges C67.M).card : ℝ) * (targetB + 2 * N) ≤
      (mbEdgesBound : ℝ) * sourceDegree C67.M L density N B
        (allMatchingEdges C67.M))
    (hMbSupport : 2 * mbEdgesBound ≤ mbBound)
    (hdeletionBudget : ∀ Mb : Finset (MatchingEdge C67.M),
      Mb ⊆ allMatchingEdges C67.M → Mb.card ≤ mbEdgesBound →
      (∑ e ∈ allMatchingEdges C67.M \
          sourceCleanEdges C67.M L C67.O density A eta Mb,
        N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1))) <
        sourceDegree C67.M L density N A (allMatchingEdges C67.M) - targetA)
    (hcap : 0 < cap)
    (hcapEnough : targetA < (cap : ℝ) * (N * (2 - 3 * eta)))
    (hlower : ∀ S : Finset (MatchingEdge C67.M),
      S ⊆ allMatchingEdges C67.M → targetA < sourceDegree C67.M L density N A S →
      lowerV1 ≤ 2 * S.card)
    (hupper : 2 * cap ≤ upperV1)
    (htotalCard : Fintype.card K ≤ lowerV1 + upperV2) :
    ∃ D : MatchingDecomposition L C67.O miss C67 lowerV1 upperV1 upperV2 mbBound
        (sourceDegree C67.M L density N A),
      D.minEdges ⊆ sourceCleanEdges C67.M L C67.O density A eta D.mbEdges ∧
      D.targetA = targetA ∧
      OptionalReservedCapacity D (sourceDegree C67.M L density N B)
        targetB N fb cutoff mbEdgesBound := by
  classical
  by_cases hsmall : fb < cutoff
  · obtain ⟨Mb, hMbAll, hMbLow, hMbHigh, hMbCardReal, hMbPositive⟩ :=
      Erdos547b.ZhaoLemma612.exists_small_submatching_positive
        (allMatchingEdges C67.M)
        (fun e => N * (density B (orientedEndpoint C67.M L e 0) +
          density B (orientedEndpoint C67.M L e 1)))
        targetB (2 * N) (mbEdgesBound : ℝ)
        (fun e _ => hBnonneg e) htargetB (by linarith)
        (fun e _ => hBcap e) (by
          simpa [sourceDegree, clusterMatchingDegree] using hBtotal)
        (by simpa [sourceDegree, clusterMatchingDegree] using hBtotalPos)
        (by simpa [sourceDegree, clusterMatchingDegree] using hBcard)
    have hMbCard : Mb.card ≤ mbEdgesBound := by exact_mod_cast hMbCardReal
    let D := matchingDecomposition_of_source_filters C67 C67.O A density N eta targetA
      cap lowerV1 upperV1 upperV2 mbBound Mb hN heta htargetA hAnonneg
      (hdeletionBudget Mb hMbAll hMbCard) hcap hcapEnough hlower hupper htotalCard
      hMbAll (by omega)
    refine ⟨D, ?_, rfl, ?_⟩
    · change cappedSubfamily
          (sourceCleanEdges C67.M L C67.O density A eta Mb) cap ⊆
        sourceCleanEdges C67.M L C67.O density A eta Mb
      exact cappedSubfamily_subset _ _
    · refine
        { small_lower := ?_
          small_upper := ?_
          small_card := ?_
          small_singleton_pos := ?_
          large_empty := ?_ }
      · intro _
        simpa [D, matchingDecomposition_of_source_filters, sourceDegree,
          clusterMatchingDegree] using hMbLow
      · intro _
        simpa [D, matchingDecomposition_of_source_filters, sourceDegree,
          clusterMatchingDegree] using hMbHigh
      · intro _
        exact hMbCard
      · intro _ e he
        simpa [D, matchingDecomposition_of_source_filters, sourceDegree,
          clusterMatchingDegree] using hMbPositive e he
      · intro h
        exact False.elim (h hsmall)
  · let Mb : Finset (MatchingEdge C67.M) := ∅
    have hMbAll : Mb ⊆ allMatchingEdges C67.M := by simp [Mb]
    have hMbCard : Mb.card ≤ mbEdgesBound := by simp [Mb]
    let D := matchingDecomposition_of_source_filters C67 C67.O A density N eta targetA
      cap lowerV1 upperV1 upperV2 mbBound Mb hN heta htargetA hAnonneg
      (hdeletionBudget Mb hMbAll hMbCard) hcap hcapEnough hlower hupper htotalCard
      hMbAll (by simp [Mb])
    refine ⟨D, ?_, rfl, ?_⟩
    · change cappedSubfamily
          (sourceCleanEdges C67.M L C67.O density A eta Mb) cap ⊆
        sourceCleanEdges C67.M L C67.O density A eta Mb
      exact cappedSubfamily_subset _ _
    · refine
        { small_lower := ?_
          small_upper := ?_
          small_card := ?_
          small_singleton_pos := ?_
          large_empty := ?_ }
      · intro h
        exact False.elim (hsmall h)
      · intro h
        exact False.elim (hsmall h)
      · intro h
        exact False.elim (hsmall h)
      · intro h
        exact False.elim (hsmall h)
      · intro _
        rfl

/-! ## Stability consequences supplied by the concrete Lemma 6.15 -/

variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- Under actual noncontainment, both exceptional families used in the
source construction are below the `eta*k` threshold.  This is the direct
contrapositive of the copy-valued Lemma 6.15. -/
theorem exceptional_families_lt_of_not_contained
    {globalRoot : TreeVertex} {small : ℕ}
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (C67 : Claim67Certificate R L miss)
    (A B : K) (hAB : R.Adj A B)
    (density : K → K → ℝ) (eta d n N k : ℝ)
    (hendpoints : ∀ e ∈ allMatchingEdges C67.M, ∀ c,
      orientedEndpoint C67.M L e c ≠ A ∧
      orientedEndpoint C67.M L e c ≠ B)
    (hdegreeA : (1 - 10 * Real.sqrt d) * n ≤
      sourceDegree C67.M L density N A (allMatchingEdges C67.M))
    (hdegreeB : (1 - 10 * Real.sqrt d) * n ≤
      sourceDegree C67.M L density N B (allMatchingEdges C67.M))
    (hthreshold : 0 < eta * k)
    (hforce :
      eta * k ≤ ((unbalancedEdges (allMatchingEdges C67.M)
          (fun e c => density A
            (orientedEndpoint C67.M L e c)) eta).card : ℝ) ∨
        eta * k ≤ ((nonextremeEdges (allMatchingEdges C67.M)
          (fun e c => density A
            (orientedEndpoint C67.M L e c)) eta).card : ℝ) →
        T.IsContained G)
    (hnot : ¬ T.IsContained G) :
    (((unbalancedEdges (allMatchingEdges C67.M)
      (fun e c => density A (orientedEndpoint C67.M L e c)) eta).card : ℕ) : ℝ) <
        eta * k ∧
    (((nonextremeEdges (allMatchingEdges C67.M)
      (fun e c => density A (orientedEndpoint C67.M L e c)) eta).card : ℕ) : ℝ) <
        eta * k := by
  have hmatchingAdj : ∀ e ∈ allMatchingEdges C67.M,
      R.Adj (orientedEndpoint C67.M L e 0)
        (orientedEndpoint C67.M L e 1) := by
    intro e _
    exact C67.M.adj_sub (orientedEndpoint_adj C67.M L e)
  have hmatchingDisjoint : ∀ e ∈ allMatchingEdges C67.M,
      ∀ f ∈ allMatchingEdges C67.M, e ≠ f → ∀ c t : Fin 2,
        orientedEndpoint C67.M L e c ≠ orientedEndpoint C67.M L f t := by
    intro e _ f _ hef c t heq
    have hp : (e, c) = (f, t) :=
      orientedEndpoint_injective C67.M C67.isMatching L heq
    exact hef (congrArg Prod.fst hp)
  constructor
  · by_contra h
    have hlarge : eta * k ≤
        ((unbalancedEdges (allMatchingEdges C67.M)
          (fun e c => density A (orientedEndpoint C67.M L e c)) eta).card : ℝ) :=
      le_of_not_gt h
    apply hnot
    exact hforce (Or.inl hlarge)
  · by_contra h
    have hlarge : eta * k ≤
        ((nonextremeEdges (allMatchingEdges C67.M)
          (fun e c => density A (orientedEndpoint C67.M L e c)) eta).card : ℝ) :=
      le_of_not_gt h
    apply hnot
    exact hforce (Or.inr hlarge)

/-- Full Lemma-6.13 balance with its embedding branch discharged by the
actual cut-forest constructor.  `hexcessForcesExceptional` is only the
finite numerical implication relating excess to the two explicit edge
filters; no copy or continuation is assumed. -/
theorem matching_balance_of_full_zhaoLemma615
    {E : Type*} [DecidableEq E]
    {globalRoot : TreeVertex} {small : ℕ}
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (M : Finset E) (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (a b : E → ℝ) (fb delta bound : ℝ)
    (hq : 0 < q)
    (htotal : (∑ e ∈ M, a e) = ∑ e ∈ M, b e)
    (hfb : delta ≤ fb)
    (hexcessForcesExceptional :
      bound ≤ Erdos547b.ZhaoStability.matchingPositiveExcess M a b →
        q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
        q ≤ ((nonextremeEdges M density eta).card : ℝ))
    (hforce : q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
        q ≤ ((nonextremeEdges M density eta).card : ℝ) →
      T.IsContained G)
    (hnot : ¬ T.IsContained G) :
    ∀ S : Finset E, S ⊆ M →
      |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)| < bound := by
  apply Erdos547b.ZhaoStability.zhaoLemma613_matchingDegreeBalance
    M a b fb delta bound (T.IsContained G) htotal hfb
  · intro _ hexcess
    exact hforce (hexcessForcesExceptional hexcess)
  · exact hnot

/-- The elementary final step giving Lemma 6.11(v) from the concrete
degree-balance theorem. -/
theorem degreeB_lower_of_balance
    {E : Type*} [DecidableEq E] (S : Finset E) (a b : E → ℝ)
    (targetA targetB bound : ℝ)
    (hA : targetA < ∑ e ∈ S, a e)
    (hbalance : |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)| < bound)
    (hnumeric : targetB + bound ≤ targetA) :
    targetB < ∑ e ∈ S, b e := by
  have := (abs_lt.mp hbalance).2
  linarith

end Erdos547b.ZhaoLemma611Full

#print axioms Erdos547b.ZhaoLemma611Full.edgeFinsetSubgraph_isMatching
#print axioms Erdos547b.ZhaoLemma611Full.support_partition
#print axioms Erdos547b.ZhaoLemma611Full.card_cappedSubfamily
#print axioms Erdos547b.ZhaoLemma611Full.orientedEndpoint_injective
#print axioms Erdos547b.ZhaoLemma611Full.sourceEdgeOf_spec
#print axioms Erdos547b.ZhaoLemma611Full.MatchingDecomposition.support_union
#print axioms Erdos547b.ZhaoLemma611Full.MatchingDecomposition.endpoint_mem_V2_iff
#print axioms Erdos547b.ZhaoLemma611Full.MatchingDecomposition.edgeOf_spec
#print axioms Erdos547b.ZhaoLemma611Full.matchingDecomposition_of_source_filters
#print axioms Erdos547b.ZhaoLemma611Full.exists_matchingDecomposition_of_claim67
#print axioms Erdos547b.ZhaoLemma611Full.exceptional_families_lt_of_not_contained
#print axioms Erdos547b.ZhaoLemma611Full.matching_balance_of_full_zhaoLemma615
