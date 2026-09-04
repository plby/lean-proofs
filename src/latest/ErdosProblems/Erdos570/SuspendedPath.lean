/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Recode
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Suspended paths and their interiors

A suspended path is represented by an injective sequence.  Its internal
vertices have degree exactly two in the ambient graph.  The explicit `Fin`
indexing below is designed for the shortening and reconstruction operations
in the sparse connected case.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Index of the `i`th internal vertex in a path with `t` internal vertices. -/
def suspendedMidIndex {t : ℕ} (i : Fin t) : Fin (t + 2) :=
  ⟨i.val + 1, by omega⟩

/-- Index immediately before the `i`th internal vertex. -/
def suspendedPrevIndex {t : ℕ} (i : Fin t) : Fin (t + 2) :=
  ⟨i.val, by omega⟩

/-- Index immediately after the `i`th internal vertex. -/
def suspendedNextIndex {t : ℕ} (i : Fin t) : Fin (t + 2) :=
  ⟨i.val + 2, by omega⟩

/-- The last endpoint index of a path with `t` internal vertices. -/
def suspendedLastIndex (t : ℕ) : Fin (t + 2) :=
  ⟨t + 1, by omega⟩

/-- An injective path sequence all of whose internal vertices have ambient
degree exactly two. -/
structure IsSuspendedPath {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} (p : Fin (t + 2) → V) : Prop where
  injective : Function.Injective p
  adj : ∀ i j : Fin (t + 2), i.val + 1 = j.val → G.Adj (p i) (p j)
  degree_mid : ∀ i : Fin t, G.degree (p (suspendedMidIndex i)) = 2

/-- The internal vertices of an explicitly indexed path. -/
def suspendedInterior {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : Fin (t + 2) → V) : Finset V :=
  Finset.univ.image fun i : Fin t ↦ p (suspendedMidIndex i)

@[simp] theorem mem_suspendedInterior {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} {p : Fin (t + 2) → V} {v : V} :
    v ∈ suspendedInterior p ↔
      ∃ i : Fin t, p (suspendedMidIndex i) = v := by
  simp [suspendedInterior]

theorem suspendedInterior_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    (suspendedInterior p).card = t := by
  classical
  rw [suspendedInterior, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext (by
      have hindex := Fin.ext_iff.mp (hp.injective hij)
      simp only [suspendedMidIndex] at hindex
      omega)

theorem suspended_first_not_interior {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    p 0 ∉ suspendedInterior p := by
  rw [mem_suspendedInterior]
  rintro ⟨i, hi⟩
  have := Fin.ext_iff.mp (hp.injective hi)
  simp [suspendedMidIndex] at this

theorem suspended_last_not_interior {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    p (suspendedLastIndex t) ∉ suspendedInterior p := by
  rw [mem_suspendedInterior]
  rintro ⟨i, hi⟩
  have := Fin.ext_iff.mp (hp.injective hi)
  simp [suspendedMidIndex, suspendedLastIndex] at this
  exact (Nat.ne_of_lt i.isLt) this

theorem suspended_endpoints_ne {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    p 0 ≠ p (suspendedLastIndex t) := by
  intro h
  have hi := Fin.ext_iff.mp (hp.injective h)
  simp [suspendedLastIndex] at hi

/-- The two consecutive path vertices around an internal vertex are exactly
its two ambient neighbors. -/
theorem suspended_neighbor_iff {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (i : Fin t) (v : V) :
    G.Adj (p (suspendedMidIndex i)) v ↔
      v = p (suspendedPrevIndex i) ∨
      v = p (suspendedNextIndex i) := by
  classical
  let x := p (suspendedMidIndex i)
  let a := p (suspendedPrevIndex i)
  let b := p (suspendedNextIndex i)
  have hab : a ≠ b := by
    intro h
    have hi := Fin.ext_iff.mp (hp.injective h)
    simp [a, b, suspendedPrevIndex, suspendedNextIndex] at hi
  have hxa : G.Adj x a := by
    dsimp only [x, a]
    exact (hp.adj (suspendedPrevIndex i) (suspendedMidIndex i) (by
      simp [suspendedPrevIndex, suspendedMidIndex])).symm
  have hxb : G.Adj x b := by
    dsimp only [x, b]
    exact hp.adj (suspendedMidIndex i) (suspendedNextIndex i) (by
      simp [suspendedMidIndex, suspendedNextIndex])
  have hpairSubset : ({a, b} : Finset V) ⊆ G.neighborFinset x := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [G.mem_neighborFinset]
    rcases hy with rfl | rfl
    · exact hxa
    · exact hxb
  have hpairEq : ({a, b} : Finset V) = G.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [show (G.neighborFinset x).card = G.degree x from rfl,
      hp.degree_mid i, Finset.card_pair hab]
  constructor
  · intro hxv
    have hv : v ∈ ({a, b} : Finset V) := by
      rw [hpairEq, G.mem_neighborFinset]
      exact hxv
    simpa [a, b] using hv
  · rintro (rfl | rfl)
    · exact hxa
    · exact hxb

/-- Every consecutive edge of the suspended path is an ambient edge. -/
def suspendedPathEdge {V : Type*} {t : ℕ}
    (p : Fin (t + 2) → V) (i : Fin (t + 1)) : Sym2 V :=
  s(p ⟨i.val, by omega⟩, p ⟨i.val + 1, by omega⟩)

def suspendedPathEdges {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : Fin (t + 2) → V) : Finset (Sym2 V) :=
  Finset.univ.image (suspendedPathEdge p)

theorem suspendedPathEdge_injective {V : Type*} {t : ℕ}
    {p : Fin (t + 2) → V} (hp : Function.Injective p) :
    Function.Injective (suspendedPathEdge p) := by
  intro i j hij
  unfold suspendedPathEdge at hij
  rw [Sym2.eq_iff] at hij
  rcases hij with hij | hij
  · apply Fin.ext
    have hh : (⟨i.val, by omega⟩ : Fin (t + 2)) =
        ⟨j.val, by omega⟩ := hp hij.1
    exact congrArg (fun z : Fin (t + 2) ↦ z.val) hh
  · have h₁ := Fin.ext_iff.mp (hp hij.1)
    have h₂ := Fin.ext_iff.mp (hp hij.2)
    simp only at h₁ h₂
    omega

theorem suspendedPathEdges_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    (suspendedPathEdges p).card = t + 1 := by
  classical
  rw [suspendedPathEdges,
    Finset.card_image_of_injective _ (suspendedPathEdge_injective hp.injective)]
  simp

theorem suspendedPathEdges_subset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    suspendedPathEdges p ⊆ G.edgeFinset := by
  classical
  intro e he
  rw [suspendedPathEdges, Finset.mem_image] at he
  obtain ⟨i, -, rfl⟩ := he
  unfold suspendedPathEdge
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact hp.adj ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ rfl

/-- Every path edge has an internal endpoint when the path has at least one
internal vertex. -/
theorem suspendedPathEdge_has_interior {V : Type*} [Fintype V]
    [DecidableEq V] {t : ℕ} (ht : 1 ≤ t) (p : Fin (t + 2) → V)
    (i : Fin (t + 1)) :
    ∃ v ∈ suspendedPathEdge p i, v ∈ suspendedInterior p := by
  by_cases hi : i.val < t
  · let j : Fin t := ⟨i.val, hi⟩
    refine ⟨p ⟨i.val + 1, by omega⟩, ?_, ?_⟩
    · unfold suspendedPathEdge
      rw [Sym2.mem_iff]
      exact Or.inr rfl
    · rw [mem_suspendedInterior]
      refine ⟨j, ?_⟩
      simp [j, suspendedMidIndex]
  · have hit : i.val = t := by omega
    let j : Fin t := ⟨t - 1, by omega⟩
    refine ⟨p ⟨i.val, by omega⟩, ?_, ?_⟩
    · unfold suspendedPathEdge
      rw [Sym2.mem_iff]
      exact Or.inl rfl
    · rw [mem_suspendedInterior]
      refine ⟨j, ?_⟩
      apply congrArg p
      apply Fin.ext
      simp [j, suspendedMidIndex, hit]
      omega

theorem suspended_prev_interior_or_first {V : Type*} [Fintype V]
    [DecidableEq V] {t : ℕ} (p : Fin (t + 2) → V) (i : Fin t) :
    p (suspendedPrevIndex i) ∈ suspendedInterior p ∨
      p (suspendedPrevIndex i) = p 0 := by
  by_cases hi : i.val = 0
  · right
    apply congrArg p
    apply Fin.ext
    simpa [suspendedPrevIndex] using hi
  · left
    rw [mem_suspendedInterior]
    let j : Fin t := ⟨i.val - 1, by omega⟩
    refine ⟨j, ?_⟩
    apply congrArg p
    apply Fin.ext
    simp [j, suspendedMidIndex, suspendedPrevIndex]
    omega

theorem suspended_next_interior_or_last {V : Type*} [Fintype V]
    [DecidableEq V] {t : ℕ} (p : Fin (t + 2) → V) (i : Fin t) :
    p (suspendedNextIndex i) ∈ suspendedInterior p ∨
      p (suspendedNextIndex i) = p (suspendedLastIndex t) := by
  by_cases hi : i.val + 1 = t
  · right
    apply congrArg p
    apply Fin.ext
    simp [suspendedNextIndex, suspendedLastIndex]
    omega
  · left
    have hil : i.val + 1 < t := by omega
    rw [mem_suspendedInterior]
    let j : Fin t := ⟨i.val + 1, hil⟩
    refine ⟨j, ?_⟩
    apply congrArg p
    apply Fin.ext
    simp [j, suspendedMidIndex, suspendedNextIndex]

/-- An edge from an internal path vertex to a retained vertex can only be
the first or last path edge. -/
theorem suspended_mid_adj_retained_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (i : Fin t) (x : V) (hx : x ∉ suspendedInterior p)
    (hix : G.Adj (p (suspendedMidIndex i)) x) :
    (i.val = 0 ∧ x = p 0) ∨
      (i.val + 1 = t ∧ x = p (suspendedLastIndex t)) := by
  rcases (suspended_neighbor_iff hp i x).mp hix with hprev | hnext
  · rcases suspended_prev_interior_or_first p i with hI | hfirst
    · exact (hx (hprev ▸ hI)).elim
    · left
      refine ⟨?_, hprev.trans hfirst⟩
      have hi := Fin.ext_iff.mp (hp.injective hfirst)
      simpa [suspendedPrevIndex] using hi
  · rcases suspended_next_interior_or_last p i with hI | hlast
    · exact (hx (hnext ▸ hI)).elim
    · right
      refine ⟨?_, hnext.trans hlast⟩
      have hi := Fin.ext_iff.mp (hp.injective hlast)
      simpa [suspendedNextIndex, suspendedLastIndex] using hi

/-- The internal path vertices, indexed without changing their order. -/
def suspendedInteriorEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    Fin t ≃ ↥(suspendedInterior p) := by
  let mid : Fin t → V := fun i ↦ p (suspendedMidIndex i)
  have hmid : Function.Injective mid := by
    intro i j hij
    apply Fin.ext
    have hindex := Fin.ext_iff.mp (hp.injective hij)
    simp only [mid, suspendedMidIndex] at hindex
    omega
  have hset : Set.range mid = (suspendedInterior p : Set V) := by
    ext v
    simp only [Set.mem_range, Finset.mem_coe, mem_suspendedInterior, mid]
  exact (Equiv.ofInjective mid hmid).trans (Equiv.setCongr hset)

/-- Vertices retained by shortening a suspended path. -/
abbrev SuspendedRetained {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (p : Fin (t + 2) → V) :=
  ↑((suspendedInterior p : Set V)ᶜ)

def suspendedLeft {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    SuspendedRetained p :=
  ⟨p 0, by simpa using suspended_first_not_interior hp⟩

def suspendedRight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    SuspendedRetained p :=
  ⟨p (suspendedLastIndex t), by
    simpa using suspended_last_not_interior hp⟩

/-- Delete the internal vertices of a suspended path and add one shortcut
edge between its retained endpoints. -/
def shortenSuspendedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    SimpleGraph (SuspendedRetained p) :=
  G.induce ((suspendedInterior p : Set V)ᶜ) ⊔
    SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)

/-- Canonical code of the shortened graph. -/
def shortenSuspendedCode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) : GraphCode :=
  recodeGraph (shortenSuspendedGraph G hp)

@[simp] theorem shortenSuspendedCode_vertexCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p) :
    (shortenSuspendedCode G hp).vertexCount = Fintype.card V - t := by
  rw [shortenSuspendedCode, recodeGraph_vertexCount]
  change Fintype.card {v : V // v ∉ suspendedInterior p} = _
  rw [Fintype.card_subtype_compl]
  have hcard : Fintype.card {v : V // v ∈ suspendedInterior p} = t := by
    change Fintype.card ↥(suspendedInterior p) = t
    rw [Fintype.card_coe, suspendedInterior_card hp]
  rw [hcard]

theorem shortenSuspendedGraph_edgeCount_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (ht : 1 ≤ t) :
    Nat.card (shortenSuspendedGraph G hp).edgeSet + t ≤
      G.edgeFinset.card := by
  classical
  let S : SimpleGraph (SuspendedRetained p) :=
    G.induce ((suspendedInterior p : Set V)ᶜ) ⊔
      SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)
  change Nat.card S.edgeSet + t ≤ G.edgeFinset.card
  let : DecidableRel S.Adj := inferInstance
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  let R : Set V := (suspendedInterior p : Set V)ᶜ
  let E : Finset (Sym2 V) :=
    (G.induce R).edgeFinset.map (Function.Embedding.subtype (· ∈ R)).sym2Map
  have hEcard : E.card = (G.induce R).edgeFinset.card := by
    simp [E]
  have hEeq : E = G.edgeFinset ∩ R.toFinset.sym2 := by
    exact G.map_edgeFinset_induce
  have hEsub : E ⊆ G.edgeFinset := by
    rw [hEeq]
    exact Finset.inter_subset_left
  have hdisj : Disjoint (suspendedPathEdges p) E := by
    rw [Finset.disjoint_left]
    intro e heP heE
    rw [suspendedPathEdges, Finset.mem_image] at heP
    obtain ⟨i, -, rfl⟩ := heP
    rw [hEeq, Finset.mem_inter] at heE
    obtain ⟨v, hve, hvI⟩ := suspendedPathEdge_has_interior ht p i
    rw [Finset.mem_sym2_iff] at heE
    have hvR : v ∈ R.toFinset := heE.2 v hve
    have hvNot : v ∉ suspendedInterior p := by simpa [R] using hvR
    exact hvNot hvI
  have hsum : (suspendedPathEdges p).card + E.card ≤ G.edgeFinset.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    apply Finset.card_le_card
    exact Finset.union_subset (suspendedPathEdges_subset hp) hEsub
  have hedgeCard :
      (SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)).edgeFinset.card ≤ 1 := by
    have hsubset :
        (SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)).edgeFinset ⊆
          {s(suspendedLeft hp, suspendedRight hp)} := by
      intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            SimpleGraph.edge_adj] at he
          simp only [Finset.mem_singleton]
          rw [Sym2.eq_iff]
          exact he.1
    calc
      (SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)).edgeFinset.card ≤
          ({s(suspendedLeft hp, suspendedRight hp)} :
            Finset (Sym2 (SuspendedRetained p))).card :=
        Finset.card_le_card hsubset
      _ = 1 := Finset.card_singleton _
  have hshort : S.edgeFinset.card ≤
      (G.induce R).edgeFinset.card + 1 := by
    dsimp only [S, R]
    rw [SimpleGraph.edgeFinset_sup]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left hedgeCard _)
  rw [suspendedPathEdges_card hp, hEcard] at hsum
  omega

@[simp] theorem shortenSuspendedCode_edgeCount_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (ht : 1 ≤ t) :
    (shortenSuspendedCode G hp).edgeCount + t ≤ G.edgeFinset.card := by
  classical
  unfold shortenSuspendedCode recodeGraph GraphCode.edgeCount
  have hcard :
      Nat.card ((shortenSuspendedGraph G hp).overFin rfl).edgeSet =
        Nat.card (shortenSuspendedGraph G hp).edgeSet := by
    exact (Nat.card_congr (SimpleGraph.overFinIso
      (G := shortenSuspendedGraph G hp) rfl).mapEdgeSet).symm
  rw [hcard]
  exact shortenSuspendedGraph_edgeCount_le hp ht

/-- Suppressing a suspended path preserves the absence of isolated vertices. -/
theorem shortenSuspendedCode_noIsolated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {t : ℕ} {p : Fin (t + 2) → V} (hp : IsSuspendedPath G p)
    (hG : ∀ v : V, ¬ G.IsIsolated v) :
    NoIsolated (shortenSuspendedCode G hp) := by
  apply (recodeGraph_noIsolated_iff (shortenSuspendedGraph G hp)).mpr
  intro x
  rw [← (shortenSuspendedGraph G hp).exists_adj_iff_not_isIsolated]
  have hlr : suspendedLeft hp ≠ suspendedRight hp := by
    intro h
    exact suspended_endpoints_ne hp (congrArg Subtype.val h)
  have hedge : (shortenSuspendedGraph G hp).Adj
      (suspendedLeft hp) (suspendedRight hp) := by
    change (G.induce ((suspendedInterior p : Set V)ᶜ) ⊔
      SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)).Adj
        (suspendedLeft hp) (suspendedRight hp)
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hlr⟩
  by_cases hxl : x = suspendedLeft hp
  · exact ⟨suspendedRight hp, hxl ▸ hedge⟩
  by_cases hxr : x = suspendedRight hp
  · exact ⟨suspendedLeft hp, hxr ▸ hedge.symm⟩
  obtain ⟨y, hxy⟩ := G.exists_adj_iff_not_isIsolated.mpr (hG x.1)
  have hy : y ∉ suspendedInterior p := by
    intro hyI
    rw [mem_suspendedInterior] at hyI
    obtain ⟨i, hi⟩ := hyI
    have hmid : G.Adj (p (suspendedMidIndex i)) x.1 := by
      rw [hi]
      exact hxy.symm
    rcases (suspended_neighbor_iff hp i x.1).mp hmid with hx | hx
    · rcases suspended_prev_interior_or_first p i with hxI | hx0
      · exact x.2 (by simpa [hx] using hxI)
      · apply hxl
        apply Subtype.ext
        simpa [suspendedLeft, hx] using hx0
    · rcases suspended_next_interior_or_last p i with hxI | hxlast
      · exact x.2 (by simpa [hx] using hxI)
      · apply hxr
        apply Subtype.ext
        simpa [suspendedRight, hx] using hxlast
  refine ⟨⟨y, by simpa using hy⟩, ?_⟩
  change (G.induce ((suspendedInterior p : Set V)ᶜ) ⊔
    SimpleGraph.edge (suspendedLeft hp) (suspendedRight hp)).Adj x
      ⟨y, by simpa using hy⟩
  rw [SimpleGraph.sup_adj]
  exact Or.inl hxy

end Erdos570
