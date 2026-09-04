import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Maximum paths and boosters

This file packages the finite extremal-path facts needed by Pósa's rotation
argument.  The definitions live in their own namespace so that the
probabilistic and deterministic parts of the proof can share a small API.

`maxPathLength G` is the maximum number of edges in a simple path of `G`.
It is defined to be zero when the vertex type is empty.  `maxPathOrder G` is
the corresponding maximum number of vertices, and is zero on the empty type.
-/

open scoped Sym2

namespace Erdos746.PathMax

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` contains a simple path with exactly `m` edges. -/
def HasPathLength (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = m

theorem hasPathLength_zero (G : SimpleGraph V) [Nonempty V] :
    HasPathLength G 0 := by
  let u : V := Classical.choice inferInstance
  exact ⟨u, u, .nil, by simp⟩

theorem HasPathLength.lt_card {G : SimpleGraph V} {m : ℕ}
    (h : HasPathLength G m) : m < Fintype.card V := by
  obtain ⟨u, v, p, hp, rfl⟩ := h
  exact hp.length_lt

theorem HasPathLength.mono {G H : SimpleGraph V} (hGH : G ≤ H) {m : ℕ}
    (h : HasPathLength G m) : HasPathLength H m := by
  obtain ⟨u, v, p, hp, rfl⟩ := h
  exact ⟨u, v, p.mapLe hGH, hp.mapLe hGH, by simp⟩

/-- The maximum number of edges in a simple path of `G`. -/
def maxPathLength (G : SimpleGraph V) : ℕ :=
  by
    classical
    exact Nat.findGreatest (HasPathLength G) (Fintype.card V)

theorem maxPathLength_le_card (G : SimpleGraph V) :
    maxPathLength G ≤ Fintype.card V := by
  classical
  unfold maxPathLength
  exact Nat.findGreatest_le _

theorem hasPathLength_maxPathLength (G : SimpleGraph V) [Nonempty V] :
    HasPathLength G (maxPathLength G) := by
  classical
  unfold maxPathLength
  exact Nat.findGreatest_spec (Nat.zero_le _) (hasPathLength_zero G)

theorem maxPathLength_lt_card (G : SimpleGraph V) [Nonempty V] :
    maxPathLength G < Fintype.card V :=
  (hasPathLength_maxPathLength G).lt_card

theorem path_length_le_maxPathLength {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : p.length ≤ maxPathLength G := by
  classical
  unfold maxPathLength
  exact Nat.le_findGreatest (Nat.le_of_lt hp.length_lt) ⟨u, v, p, hp, rfl⟩

/-- A path is longest if it is simple and realizes `maxPathLength G`. -/
def IsLongestPath {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ p.length = maxPathLength G

theorem IsLongestPath.isPath {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : IsLongestPath p) : p.IsPath := hp.1

theorem IsLongestPath.length_eq {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : IsLongestPath p) :
    p.length = maxPathLength G := hp.2

theorem exists_isLongestPath (G : SimpleGraph V) [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), IsLongestPath p := by
  simpa only [HasPathLength, IsLongestPath] using hasPathLength_maxPathLength G

theorem isLongestPath_iff {G : SimpleGraph V} {u v : V} {p : G.Walk u v} :
    IsLongestPath p ↔
      p.IsPath ∧ ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length := by
  constructor
  · rintro ⟨hp, hlen⟩
    refine ⟨hp, fun _ _ _ hq ↦ ?_⟩
    simpa [hlen] using path_length_le_maxPathLength hq
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (path_length_le_maxPathLength hp) ?_⟩
    by_cases hV : Nonempty V
    · let := hV
      obtain ⟨u', v', q, hq⟩ := exists_isLongestPath G
      simpa [hq.length_eq] using hmax u' v' q hq.isPath
    · exact (hV ⟨u⟩).elim

theorem maxPathLength_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    maxPathLength G ≤ maxPathLength H := by
  classical
  by_cases hV : Nonempty V
  · let := hV
    exact Nat.le_findGreatest (maxPathLength_le_card G)
      ((hasPathLength_maxPathLength G).mono hGH)
  · have : IsEmpty V := not_nonempty_iff.mp hV
    have hEq : G = H := Subsingleton.elim G H
    simpa [hEq]

/-- The maximum number of vertices in a simple path. -/
def maxPathOrder (G : SimpleGraph V) : ℕ :=
  by
    classical
    exact if Nonempty V then maxPathLength G + 1 else 0

theorem maxPathOrder_eq (G : SimpleGraph V) [Nonempty V] :
    maxPathOrder G = maxPathLength G + 1 := by
  classical
  simp [maxPathOrder]

theorem maxPathOrder_eq_zero (G : SimpleGraph V) [IsEmpty V] :
    maxPathOrder G = 0 := by
  classical
  have hV : ¬ Nonempty V := not_nonempty_iff.mpr (inferInstance : IsEmpty V)
  rw [maxPathOrder, if_neg hV]

theorem maxPathOrder_le_card (G : SimpleGraph V) :
    maxPathOrder G ≤ Fintype.card V := by
  by_cases hV : Nonempty V
  · let := hV
    rw [maxPathOrder_eq]
    exact maxPathLength_lt_card G
  · have : IsEmpty V := not_nonempty_iff.mp hV
    simp [maxPathOrder_eq_zero]

theorem maxPathOrder_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    maxPathOrder G ≤ maxPathOrder H := by
  by_cases hV : Nonempty V
  · let := hV
    simp only [maxPathOrder_eq]
    exact Nat.succ_le_succ (maxPathLength_mono hGH)
  · have : IsEmpty V := not_nonempty_iff.mp hV
    simp [maxPathOrder_eq_zero]

theorem path_order_le_maxPathOrder {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : p.length + 1 ≤ maxPathOrder G := by
  let : Nonempty V := ⟨u⟩
  rw [maxPathOrder_eq]
  exact Nat.add_le_add_right (path_length_le_maxPathLength hp) 1

theorem IsLongestPath.order_eq {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : IsLongestPath p) :
    p.length + 1 = maxPathOrder G := by
  let : Nonempty V := ⟨u⟩
  rw [maxPathOrder_eq, hp.length_eq]

theorem exists_path_of_order_maxPathOrder (G : SimpleGraph V) [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v),
      p.IsPath ∧ p.length + 1 = maxPathOrder G := by
  obtain ⟨u, v, p, hp⟩ := exists_isLongestPath G
  exact ⟨u, v, p, hp.isPath, hp.order_eq⟩

/-! ## Adding one edge -/

/-- Add the unordered pair `e` to a graph.  A diagonal pair has no effect. -/
def addEdge (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet {e}

theorem le_addEdge (G : SimpleGraph V) (e : Sym2 V) : G ≤ addEdge G e := by
  exact le_sup_left

@[simp] theorem edgeSet_addEdge (G : SimpleGraph V) (e : Sym2 V) :
    (addEdge G e).edgeSet = G.edgeSet ∪ ({e} \ Sym2.diagSet) := by
  simp [addEdge]

@[simp] theorem mem_edgeSet_addEdge {G : SimpleGraph V} {e x : Sym2 V} :
    x ∈ (addEdge G e).edgeSet ↔
      x ∈ G.edgeSet ∨ x = e ∧ ¬e.IsDiag := by
  simp only [edgeSet_addEdge, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff,
    Sym2.mem_diagSet]
  aesop

theorem mem_edgeSet_addEdge_self {G : SimpleGraph V} {e : Sym2 V}
    (he : ¬e.IsDiag) : e ∈ (addEdge G e).edgeSet := by
  simp [he]

theorem edgeSet_addEdge_of_not_isDiag {G : SimpleGraph V} {e : Sym2 V}
    (he : ¬e.IsDiag) :
    (addEdge G e).edgeSet = G.edgeSet ∪ {e} := by
  ext x
  simp only [mem_edgeSet_addEdge, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro (hx | ⟨rfl, _⟩)
    · exact Or.inl hx
    · exact Or.inr rfl
  · rintro (hx | rfl)
    · exact Or.inl hx
    · exact Or.inr ⟨rfl, he⟩

theorem addEdge_eq_self_of_isDiag {G : SimpleGraph V} {e : Sym2 V}
    (he : e.IsDiag) : addEdge G e = G := by
  apply SimpleGraph.edgeSet_injective
  ext x
  rw [mem_edgeSet_addEdge]
  constructor
  · rintro (hx | ⟨hxe, hx⟩)
    · exact hx
    · exact (hx (hxe ▸ he)).elim
  · exact fun hx ↦ Or.inl hx

theorem addEdge_eq_self_of_mem {G : SimpleGraph V} {e : Sym2 V}
    (he : e ∈ G.edgeSet) : addEdge G e = G := by
  apply SimpleGraph.edgeSet_injective
  ext x
  simp only [mem_edgeSet_addEdge]
  constructor
  · rintro (hx | ⟨rfl, _⟩)
    · exact hx
    · exact he
  · exact fun hx ↦ Or.inl hx

theorem addEdge_eq_self_iff {G : SimpleGraph V} {e : Sym2 V} :
    addEdge G e = G ↔ e.IsDiag ∨ e ∈ G.edgeSet := by
  constructor
  · intro h
    by_cases he : e.IsDiag
    · exact Or.inl he
    · exact Or.inr (by
        have : e ∈ (addEdge G e).edgeSet := mem_edgeSet_addEdge_self he
        simpa [h] using this)
  · rintro (he | he)
    · exact addEdge_eq_self_of_isDiag he
    · exact addEdge_eq_self_of_mem he

/-- A genuine edge that is absent from `G`. -/
def IsMissingEdge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∉ G.edgeSet ∧ ¬e.IsDiag

theorem IsMissingEdge.not_mem {G : SimpleGraph V} {e : Sym2 V}
    (he : IsMissingEdge G e) : e ∉ G.edgeSet := he.1

theorem IsMissingEdge.not_isDiag {G : SimpleGraph V} {e : Sym2 V}
    (he : IsMissingEdge G e) : ¬e.IsDiag := he.2

theorem isMissingEdge_iff_addEdge_ne {G : SimpleGraph V} {e : Sym2 V} :
    IsMissingEdge G e ↔ ¬e.IsDiag ∧ addEdge G e ≠ G := by
  simp only [IsMissingEdge, ne_eq, addEdge_eq_self_iff, not_or]
  tauto

theorem IsMissingEdge.addEdge_ne {G : SimpleGraph V} {e : Sym2 V}
    (he : IsMissingEdge G e) : addEdge G e ≠ G :=
  (isMissingEdge_iff_addEdge_ne.mp he).2

theorem IsMissingEdge.lt_addEdge {G : SimpleGraph V} {e : Sym2 V}
    (he : IsMissingEdge G e) : G < addEdge G e := by
  exact lt_of_le_of_ne (le_addEdge G e) (Ne.symm he.addEdge_ne)

theorem maxPathLength_le_addEdge (G : SimpleGraph V) (e : Sym2 V) :
    maxPathLength G ≤ maxPathLength (addEdge G e) :=
  maxPathLength_mono (le_addEdge G e)

/-! ## Boosters and finite adapters -/

/-- A booster is a missing genuine edge whose addition either creates a
Hamiltonian graph or strictly increases the maximum simple-path length. -/
def IsBooster (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  IsMissingEdge G e ∧
    ((addEdge G e).IsHamiltonian ∨
      maxPathLength G < maxPathLength (addEdge G e))

theorem IsBooster.isMissingEdge {G : SimpleGraph V} {e : Sym2 V}
    (he : IsBooster G e) : IsMissingEdge G e := he.1

theorem IsBooster.not_mem {G : SimpleGraph V} {e : Sym2 V}
    (he : IsBooster G e) : e ∉ G.edgeSet := he.1.1

theorem IsBooster.not_isDiag {G : SimpleGraph V} {e : Sym2 V}
    (he : IsBooster G e) : ¬e.IsDiag := he.1.2

theorem IsBooster.hamiltonian_or_length_lt {G : SimpleGraph V} {e : Sym2 V}
    (he : IsBooster G e) :
    (addEdge G e).IsHamiltonian ∨
      maxPathLength G < maxPathLength (addEdge G e) := he.2

theorem IsBooster.lt_addEdge {G : SimpleGraph V} {e : Sym2 V}
    (he : IsBooster G e) : G < addEdge G e := he.isMissingEdge.lt_addEdge

/-- Restrict the booster predicate to an arbitrary finite ambient edge set. -/
def boosterFinsetWithin (G : SimpleGraph V) (ambient : Finset (Sym2 V)) :
    Finset (Sym2 V) := by
  classical
  exact ambient.filter (IsBooster G)

@[simp] theorem mem_boosterFinsetWithin {G : SimpleGraph V}
    {ambient : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ boosterFinsetWithin G ambient ↔ e ∈ ambient ∧ IsBooster G e := by
  simp [boosterFinsetWithin]

/-- The finite set of all boosters. -/
def boosterFinset (G : SimpleGraph V) : Finset (Sym2 V) :=
  boosterFinsetWithin G Finset.univ

@[simp] theorem mem_boosterFinset {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ boosterFinset G ↔ IsBooster G e := by
  simp [boosterFinset]

theorem boosterFinsetWithin_subset (G : SimpleGraph V)
    (ambient : Finset (Sym2 V)) :
    boosterFinsetWithin G ambient ⊆ ambient := by
  intro e he
  exact (mem_boosterFinsetWithin.mp he).1

/-- The finite set of all genuine absent edges. -/
def missingEdgeFinset (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (IsMissingEdge G)

@[simp] theorem mem_missingEdgeFinset {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ missingEdgeFinset G ↔ IsMissingEdge G e := by
  simp [missingEdgeFinset]

theorem boosterFinset_subset_missingEdgeFinset (G : SimpleGraph V) :
    boosterFinset G ⊆ missingEdgeFinset G := by
  intro e he
  simpa using (mem_boosterFinset.mp he).isMissingEdge

/-! ### Adapter to the complete-graph edge subtype

The fixed-edge model represents possible edges by
`(⊤ : SimpleGraph V).edgeFinset`.  The following finset carries exactly the
same boosters as `boosterFinset`, but in that subtype.
-/

/-- Inclusion of the complete graph's edge subtype into unordered pairs. -/
def completeEdgeEmbedding :
    (⊤ : SimpleGraph V).edgeFinset ↪ Sym2 V :=
  Function.Embedding.subtype
    (fun e ↦ e ∈ (⊤ : SimpleGraph V).edgeFinset)

/-- All boosters, represented in the complete-graph edge subtype. -/
def boosterEdgeFinset (G : SimpleGraph V) :
    Finset ((⊤ : SimpleGraph V).edgeFinset) := by
  classical
  exact Finset.univ.filter (fun e ↦ IsBooster G e.1)

@[simp] theorem mem_boosterEdgeFinset {G : SimpleGraph V}
    {e : (⊤ : SimpleGraph V).edgeFinset} :
    e ∈ boosterEdgeFinset G ↔ IsBooster G e.1 := by
  simp [boosterEdgeFinset]

theorem map_boosterEdgeFinset (G : SimpleGraph V) :
    (boosterEdgeFinset G).map completeEdgeEmbedding = boosterFinset G := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨e', he', heq⟩ := Finset.mem_map.mp he
    subst e
    exact mem_boosterFinset.mpr (mem_boosterEdgeFinset.mp he')
  · intro he
    have hboost : IsBooster G e := mem_boosterFinset.mp he
    have heTop : e ∈ (⊤ : SimpleGraph V).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      simpa using hboost.not_isDiag
    let e' : (⊤ : SimpleGraph V).edgeFinset := ⟨e, heTop⟩
    exact Finset.mem_map.mpr ⟨e', mem_boosterEdgeFinset.mpr hboost, rfl⟩

theorem card_boosterEdgeFinset (G : SimpleGraph V) :
    (boosterEdgeFinset G).card = (boosterFinset G).card := by
  rw [← map_boosterEdgeFinset G, Finset.card_map]

end

end Erdos746.PathMax
