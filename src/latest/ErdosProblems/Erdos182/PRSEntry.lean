import ErdosProblems.Erdos182.Foundations
import ErdosProblems.Erdos182.Roof
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The entry reduction for the Pyber--Rödl--Szemerédi theorem

This file turns an average-degree hypothesis on a finite simple graph into a
half-regular two-sorted bipartite subgraph.  All estimates are kept over the
natural numbers.  Thus `d * |V| ≤ 2 * e(G)` is the assertion that the
average degree is at least `d`, and the extracted regular degree is
`d ⌈/⌉ 4`.
-/

namespace Erdos182

open Finset
open SimpleGraph

universe u

namespace PRSEntry

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Keep precisely the edges of `G` having both endpoints in `S`, while
retaining the original ambient vertex type. -/
def vertexRestriction (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v ∈ S ∧ w ∈ S
  symm := ⟨fun _ _ h ↦ ⟨G.symm.symm _ _ h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h ↦ G.loopless.irrefl v h.1⟩

noncomputable instance vertexRestriction.instDecidableRel (G : SimpleGraph V)
    (S : Finset V) : DecidableRel (vertexRestriction G S).Adj :=
  Classical.decRel _

@[simp]
theorem vertexRestriction_adj (G : SimpleGraph V) (S : Finset V) (v w : V) :
    (vertexRestriction G S).Adj v w ↔ G.Adj v w ∧ v ∈ S ∧ w ∈ S :=
  Iff.rfl

theorem vertexRestriction_le (G : SimpleGraph V) (S : Finset V) :
    vertexRestriction G S ≤ G := by
  intro v w h
  exact h.1

theorem vertexRestriction_erase (G : SimpleGraph V) (S : Finset V) (v : V) :
    vertexRestriction G (S.erase v) =
      (vertexRestriction G S).deleteIncidenceSet v := by
  ext x y
  simp only [vertexRestriction_adj, SimpleGraph.deleteIncidenceSet_adj,
    Finset.mem_erase]
  constructor
  · rintro ⟨hxy, ⟨hxv, hxS⟩, hyv, hyS⟩
    exact ⟨⟨hxy, hxS, hyS⟩, hxv, hyv⟩
  · rintro ⟨⟨hxy, hxS, hyS⟩, hxv, hyv⟩
    exact ⟨hxy, ⟨hxv, hxS⟩, hyv, hyS⟩

/-- Edge count without a choice of a decidable adjacency relation. -/
noncomputable def edgeNumber (G : SimpleGraph V) : ℕ := G.edgeSet.ncard

theorem edgeNumber_eq_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeNumber G = G.edgeFinset.card := by
  calc
    edgeNumber G = Fintype.card G.edgeSet := by
      exact (Set.fintypeCard_eq_ncard G.edgeSet).symm
    _ = G.edgeFinset.card := G.card_edgeSet

/-- Degree without a choice of a decidable adjacency relation. -/
noncomputable def degreeNumber (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborSet v).ncard

theorem edgeNumber_deleteIncidenceSet (G : SimpleGraph V) (v : V) :
    edgeNumber (G.deleteIncidenceSet v) = edgeNumber G - degreeNumber G v := by
  rw [edgeNumber, degreeNumber, SimpleGraph.edgeSet_deleteIncidenceSet,
    Set.ncard_sdiff' (SimpleGraph.incidenceSet_subset G v)]
  exact congrArg (fun n ↦ edgeNumber G - n)
    (Set.ncard_congr' (G.incidenceSetEquivNeighborSet v))

theorem degreeNumber_le_edgeNumber (G : SimpleGraph V) (v : V) :
    degreeNumber G v ≤ edgeNumber G := by
  rw [degreeNumber, edgeNumber,
    ← Set.ncard_congr' (G.incidenceSetEquivNeighborSet v)]
  exact Set.ncard_le_ncard (SimpleGraph.incidenceSet_subset G v)

theorem degreeNumber_eq_degree (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] : degreeNumber G v = G.degree v := by
  rw [degreeNumber, ← Set.fintypeCard_eq_ncard,
    SimpleGraph.card_neighborSet_eq_degree]

/-- The weighted score used to choose a nonempty induced subgraph of large
minimum degree.  The multiplier `|V|+1` makes an increase of one in the
potential dominate the loss of one vertex. -/
noncomputable def coreScore (G : SimpleGraph V) (d : ℕ) (S : Finset V) : ℕ :=
  (2 * edgeNumber (vertexRestriction G S) +
      d * (Fintype.card V - S.card)) * (Fintype.card V + 1) + S.card

/-- The usual deletion lemma, in a rounding-safe form: average degree at
least `d` yields a nonempty induced subgraph in which every active vertex has
degree at least `d/2` (expressed as `d ≤ 2 degree`). -/
theorem exists_nonempty_vertexRestriction_forall_degree
    (G : SimpleGraph V) (d : ℕ) [Nonempty V]
    (havg : d * Fintype.card V ≤ 2 * edgeNumber G) :
    ∃ S : Finset V, S.Nonempty ∧
      ∀ v ∈ S, d ≤ 2 * degreeNumber (vertexRestriction G S) v := by
  classical
  obtain ⟨S, hSpow, hSmax⟩ :=
    Finset.exists_max_image (Finset.univ.powerset) (coreScore G d)
      ⟨∅, by simp⟩
  have hSsub : S ⊆ (Finset.univ : Finset V) := Finset.mem_powerset.mp hSpow
  have hScard : S.card ≤ Fintype.card V := by
    simpa using Finset.card_le_card hSsub
  have hnpos : 0 < Fintype.card V := Fintype.card_pos
  have hSne : S.Nonempty := by
    by_contra h
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hcompare := hSmax (Finset.univ : Finset V) (by simp)
    simp only [coreScore, hSempty,
      Finset.card_empty, Nat.sub_zero, Finset.card_univ, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero, zero_add] at hcompare
    have hrestrict_univ : vertexRestriction G (Finset.univ : Finset V) = G := by
      ext v w
      simp
    have hedge_univ : edgeNumber (vertexRestriction G (Finset.univ : Finset V)) =
        edgeNumber G := congrArg edgeNumber hrestrict_univ
    have hrestrict_empty : vertexRestriction G (∅ : Finset V) = ⊥ := by
      ext v w
      simp
    have hedge_empty : edgeNumber (vertexRestriction G (∅ : Finset V)) = 0 := by
      rw [congrArg edgeNumber hrestrict_empty]
      simp [edgeNumber]
    rw [hedge_univ] at hcompare
    rw [hedge_empty] at hcompare
    nlinarith
  refine ⟨S, hSne, ?_⟩
  intro v hvS
  by_contra hdeg
  have hdeglt : 2 * degreeNumber (vertexRestriction G S) v < d :=
    Nat.lt_of_not_ge hdeg
  have hErasePow : S.erase v ∈ Finset.univ.powerset := by simp
  have hscore := hSmax (S.erase v) hErasePow
  have hcardErase : (S.erase v).card = S.card - 1 := by
    rw [Finset.card_erase_of_mem hvS]
  have hScardpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hcardGap : Fintype.card V - (S.erase v).card =
      (Fintype.card V - S.card) + 1 := by
    rw [hcardErase]
    omega
  have hdegreeEdge : degreeNumber (vertexRestriction G S) v ≤
      edgeNumber (vertexRestriction G S) :=
    degreeNumber_le_edgeNumber _ _
  have hedgeErase :
      edgeNumber (vertexRestriction G (S.erase v)) =
        edgeNumber (vertexRestriction G S) -
          degreeNumber (vertexRestriction G S) v := by
    rw [show edgeNumber (vertexRestriction G (S.erase v)) =
        edgeNumber ((vertexRestriction G S).deleteIncidenceSet v) from
      congrArg edgeNumber (vertexRestriction_erase G S v)]
    exact edgeNumber_deleteIncidenceSet _ _
  simp only [coreScore, hedgeErase] at hscore
  rw [hcardGap, hcardErase] at hscore
  have hsubadd :
      edgeNumber (vertexRestriction G S) - degreeNumber (vertexRestriction G S) v +
          degreeNumber (vertexRestriction G S) v = edgeNumber (vertexRestriction G S) :=
    Nat.sub_add_cancel hdegreeEdge
  nlinarith

/-- The graph consisting of the edges of `G` whose endpoints have different
Boolean colors. -/
def cutGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v ≠ c w
  symm := ⟨fun _ _ h ↦ ⟨G.symm.symm _ _ h.1, Ne.symm h.2⟩⟩
  loopless := ⟨fun v h ↦ G.loopless.irrefl v h.1⟩

noncomputable instance cutGraph.instDecidableRel (G : SimpleGraph V)
    (c : V → Bool) : DecidableRel (cutGraph G c).Adj :=
  Classical.decRel _

@[simp]
theorem cutGraph_adj (G : SimpleGraph V) (c : V → Bool) (v w : V) :
    (cutGraph G c).Adj v w ↔ G.Adj v w ∧ c v ≠ c w :=
  Iff.rfl

theorem cutGraph_le (G : SimpleGraph V) (c : V → Bool) : cutGraph G c ≤ G := by
  intro v w h
  exact h.1

/-- Toggle one vertex of a Boolean coloring. -/
def flipColor (c : V → Bool) (v : V) : V → Bool :=
  Function.update c v (!c v)

@[simp]
theorem flipColor_self (c : V → Bool) (v : V) : flipColor c v v = !c v := by
  simp [flipColor]

theorem flipColor_of_ne (c : V → Bool) {v w : V} (h : w ≠ v) :
    flipColor c v w = c w := by
  simp [flipColor, h]

theorem deleteIncidenceSet_cutGraph_flip (G : SimpleGraph V) (c : V → Bool) (v : V) :
    (cutGraph G (flipColor c v)).deleteIncidenceSet v =
      (cutGraph G c).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, cutGraph_adj]
  constructor
  · rintro ⟨⟨hxy, hc⟩, hxv, hyv⟩
    rw [flipColor_of_ne c hxv, flipColor_of_ne c hyv] at hc
    exact ⟨⟨hxy, hc⟩, hxv, hyv⟩
  · rintro ⟨⟨hxy, hc⟩, hxv, hyv⟩
    rw [flipColor_of_ne c hxv, flipColor_of_ne c hyv]
    exact ⟨⟨hxy, hc⟩, hxv, hyv⟩

theorem degree_cutGraph_flip (G : SimpleGraph V)
    (c : V → Bool) (v : V) :
    degreeNumber (cutGraph G (flipColor c v)) v =
      degreeNumber G v - degreeNumber (cutGraph G c) v := by
  classical
  have hEq : (cutGraph G (flipColor c v)).neighborSet v =
      G.neighborSet v \ (cutGraph G c).neighborSet v := by
    ext w
    by_cases hw : w = v
    · subst w
      simp
    · simp only [SimpleGraph.mem_neighborSet, cutGraph_adj,
        flipColor_self, flipColor_of_ne c hw, Set.mem_diff]
      cases hcv : c v <;> cases hcw : c w <;> simp [hcv, hcw]
  have hsub : (cutGraph G c).neighborSet v ⊆ G.neighborSet v := by
    intro w hw
    exact hw.1
  simp only [degreeNumber, hEq, Set.ncard_sdiff' hsub]

/-- A maximum Boolean cut has at least half of the degree of every vertex.
This local form is stronger than the usual statement that some cut contains
at least half of all edges. -/
theorem exists_cutGraph_forall_degree (G : SimpleGraph V) :
    ∃ c : V → Bool, ∀ v,
      degreeNumber G v ≤ 2 * degreeNumber (cutGraph G c) v := by
  classical
  obtain ⟨c, -, hcmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V → Bool))
    (fun c ↦ edgeNumber (cutGraph G c)) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  intro v
  have hmax := hcmax (flipColor c v) (by simp)
  let C := cutGraph G c
  let C' := cutGraph G (flipColor c v)
  have hdegC : degreeNumber C v ≤ edgeNumber C := by
    exact degreeNumber_le_edgeNumber _ _
  have hdegC' : degreeNumber C' v ≤ edgeNumber C' := by
    exact degreeNumber_le_edgeNumber _ _
  have hdelC : edgeNumber (C.deleteIncidenceSet v) =
      edgeNumber C - degreeNumber C v := edgeNumber_deleteIncidenceSet C v
  have hdelC' : edgeNumber (C'.deleteIncidenceSet v) =
      edgeNumber C' - degreeNumber C' v := edgeNumber_deleteIncidenceSet C' v
  have hdelEq : edgeNumber (C'.deleteIncidenceSet v) =
      edgeNumber (C.deleteIncidenceSet v) :=
    congrArg edgeNumber (deleteIncidenceSet_cutGraph_flip G c v)
  have hflip : degreeNumber C' v = degreeNumber G v - degreeNumber C v := by
    exact degree_cutGraph_flip G c v
  dsimp only [C, C'] at hmax hdegC hdegC' hdelC hdelC' hdelEq hflip ⊢
  omega

/-- The cut graph is bipartite in its two Boolean color classes. -/
theorem cutGraph_isBipartiteWith (G : SimpleGraph V) (c : V → Bool) :
    (cutGraph G c).IsBipartiteWith {v | c v = false} {v | c v = true} := by
  refine ⟨?_, ?_⟩
  · exact Set.disjoint_left.2 (by simp)
  · intro v w hvw
    rcases hvw with ⟨_, hne⟩
    cases hcv : c v <;> cases hcw : c w <;> simp_all

/-- Combining the deletion lemma with a maximum cut: an average-degree
threshold `d` produces a bipartite subgraph whose active vertices all have
degree at least `d/4`, with no rounding hidden in division. -/
theorem exists_bipartite_core (G : SimpleGraph V) (d : ℕ) [Nonempty V]
    (havg : d * Fintype.card V ≤ 2 * edgeNumber G) :
    ∃ S : Finset V, ∃ c : V → Bool,
      S.Nonempty ∧
      cutGraph (vertexRestriction G S) c ≤ G ∧
      (cutGraph (vertexRestriction G S) c).IsBipartiteWith
        {v | c v = false} {v | c v = true} ∧
      ∀ v ∈ S, d ≤ 4 * degreeNumber (cutGraph (vertexRestriction G S) c) v := by
  obtain ⟨S, hSne, hSdeg⟩ :=
    exists_nonempty_vertexRestriction_forall_degree G d havg
  obtain ⟨c, hcdeg⟩ := exists_cutGraph_forall_degree (vertexRestriction G S)
  refine ⟨S, c, hSne, ?_, cutGraph_isBipartiteWith _ _, ?_⟩
  · exact (cutGraph_le _ _).trans (vertexRestriction_le G S)
  · intro v hv
    exact (hSdeg v hv).trans (by nlinarith [hcdeg v])

/-- Regard the edges of a simple graph between two displayed parts as a
two-sorted bipartite graph. -/
def fromSimpleGraph (G : SimpleGraph V) (A B : Finset V) : BipartiteGraph A B where
  Adj a b := G.Adj a.1 b.1

@[simp]
theorem fromSimpleGraph_adj (G : SimpleGraph V) (A B : Finset V) (a : A) (b : B) :
    (fromSimpleGraph G A B).Adj a b ↔ G.Adj a.1 b.1 := Iff.rfl

theorem fromSimpleGraph_mono {G K : SimpleGraph V} (hKG : K ≤ G)
    (A B : Finset V) : fromSimpleGraph K A B ≤ fromSimpleGraph G A B := by
  intro a b hab
  exact hKG hab

/-- If every neighbor of a right vertex lies in the displayed left part,
its two-sorted right degree is its degree in the ambient simple graph. -/
theorem rightDegree_fromSimpleGraph_eq (G : SimpleGraph V) (A B : Finset V) (b : B)
    (hA : ∀ w, G.Adj b.1 w → w ∈ A) :
    (fromSimpleGraph G A B).rightDegree b = degreeNumber G b.1 := by
  classical
  let e : {a : A // G.Adj a.1 b.1} ≃ G.neighborSet b.1 :=
    { toFun := fun a ↦ ⟨a.1.1, G.symm.symm _ _ a.2⟩
      invFun := fun w ↦
        ⟨⟨w.1, hA w.1 w.2⟩, G.symm.symm _ _ w.2⟩
      left_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro w; apply Subtype.ext; rfl }
  calc
    (fromSimpleGraph G A B).rightDegree b =
        Fintype.card {a : A // G.Adj a.1 b.1} := by
          change #(Finset.univ.filter fun a : A ↦ G.Adj a.1 b.1) = _
          rw [Fintype.card_subtype]
    _ = Fintype.card (G.neighborSet b.1) := Fintype.card_congr e
    _ = degreeNumber G b.1 := by
      simpa only [degreeNumber] using
        (Set.fintypeCard_eq_ncard (G.neighborSet b.1))

/-- Independently retain `r` incident edges at every right vertex. -/
theorem exists_rightRegular_trim {A B : Type*} [Fintype A] [Fintype B]
    (G : BipartiteGraph A B) (r : ℕ)
    (hr : ∀ b, r ≤ G.rightDegree b) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧ H.IsRightRegularOn Finset.univ r := by
  classical
  choose N hNsub hNcard using fun b : B ↦
    Finset.exists_subset_card_eq (hr b)
  let H : BipartiteGraph A B :=
    ⟨fun a b ↦ G.Adj a b ∧ a ∈ N b⟩
  refine ⟨H, ?_, ?_⟩
  · intro a b hab
    exact hab.1
  · intro b _
    have hneighbors : H.leftNeighbors b = N b := by
      ext a
      constructor
      · intro ha
        exact (BipartiteGraph.mem_leftNeighbors H a b).mp ha |>.2
      · intro ha
        apply (BipartiteGraph.mem_leftNeighbors H a b).mpr
        exact ⟨(BipartiteGraph.mem_leftNeighbors G a b).mp (hNsub b ha), ha⟩
    rw [BipartiteGraph.rightDegree, hneighbors, hNcard]

/-- The maximum degree, phrased without a decidability parameter. -/
noncomputable def maximumDegreeNumber (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup (degreeNumber G)

theorem degreeNumber_le_maximumDegreeNumber (G : SimpleGraph V) (v : V) :
    degreeNumber G v ≤ maximumDegreeNumber G := by
  classical
  exact Finset.le_sup (f := degreeNumber G) (Finset.mem_univ v)

theorem degreeNumber_mono {G K : SimpleGraph V} (hKG : K ≤ G) (v : V) :
    degreeNumber K v ≤ degreeNumber G v := by
  rw [degreeNumber, degreeNumber]
  exact Set.ncard_le_ncard (fun w hw ↦ hKG hw)

/-- **PRS entry reduction.**  An average-degree lower bound `d` yields a
right-half-regular two-sorted bipartite subgraph of degree
`δ = ⌈d/4⌉`.  The two parts contain exactly the active vertices, the
subgraph lies in `G`, and its regular degree is at most the maximum degree of
`G`. -/
theorem exists_halfRegular_bipartite_entry_strong (G : SimpleGraph V) (d : ℕ)
    [Nonempty V] (hd : 0 < d)
    (havg : d * Fintype.card V ≤ 2 * edgeNumber G) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
      Disjoint (A : Set V) (B : Set V) ∧
      ∃ H : BipartiteGraph A B, ∃ δ : ℕ,
        H.IsHalfRegularSubgraphOf (fromSimpleGraph G A B)
            (Finset.univ : Finset A) (Finset.univ : Finset B) δ ∧
          δ = d ⌈/⌉ 4 ∧ d ≤ 4 * δ ∧ δ ≤ d ∧
          δ ≤ maximumDegreeNumber G := by
  classical
  obtain ⟨S, c₀, hSne, hCG₀, _hCbip, hdeg₀⟩ := exists_bipartite_core G d havg
  let c : V → Bool :=
    if (S.filter fun v ↦ c₀ v = false).card ≤
        (S.filter fun v ↦ c₀ v = true).card then c₀ else fun v ↦ !c₀ v
  have hcut : cutGraph (vertexRestriction G S) c =
      cutGraph (vertexRestriction G S) c₀ := by
    dsimp only [c]
    split_ifs
    · rfl
    · ext v w
      simp only [cutGraph_adj]
      cases hv : c₀ v <;> cases hw : c₀ w <;> simp [hv, hw]
  have hCG : cutGraph (vertexRestriction G S) c ≤ G := by
    rw [hcut]
    exact hCG₀
  have hdeg : ∀ v ∈ S,
      d ≤ 4 * degreeNumber (cutGraph (vertexRestriction G S) c) v := by
    intro v hv
    rw [hcut]
    exact hdeg₀ v hv
  let C := cutGraph (vertexRestriction G S) c
  let A : Finset V := S.filter fun v ↦ c v = false
  let B : Finset V := S.filter fun v ↦ c v = true
  have hAB : Disjoint (A : Set V) (B : Set V) := by
    rw [Set.disjoint_left]
    intro v hvA hvB
    have hvfalse : c v = false := (Finset.mem_filter.mp hvA).2
    have hvtrue : c v = true := (Finset.mem_filter.mp hvB).2
    simp_all
  have hcard : A.card ≤ B.card := by
    dsimp only [A, B, c]
    split_ifs with h
    · exact h
    · have hrev : (S.filter fun v ↦ c₀ v = true).card ≤
          (S.filter fun v ↦ c₀ v = false).card := Nat.le_of_lt (Nat.lt_of_not_ge h)
      have hfalse : (S.filter fun v ↦ (!c₀ v) = false) =
          S.filter fun v ↦ c₀ v = true := by
        ext v
        cases hv : c₀ v <;> simp [hv]
      have htrue : (S.filter fun v ↦ (!c₀ v) = true) =
          S.filter fun v ↦ c₀ v = false := by
        ext v
        cases hv : c₀ v <;> simp [hv]
      rw [hfalse, htrue]
      exact hrev
  have hparts : A.Nonempty ∧ B.Nonempty := by
    obtain ⟨v, hvS⟩ := hSne
    have hvdeg : 0 < degreeNumber C v := by
      have := hdeg v hvS
      dsimp only [C]
      nlinarith
    obtain ⟨w, hvw⟩ := ((Set.ncard_pos).mp (by simpa [degreeNumber] using hvdeg) :
      (C.neighborSet v).Nonempty)
    have hvw' : C.Adj v w := hvw
    have hvS' : v ∈ S := hvS
    have hwS : w ∈ S := by
      exact hvw'.1.2.2
    have hcolor : c v ≠ c w := hvw'.2
    cases hcv : c v <;> cases hcw : c w
    · simp_all
    · exact ⟨⟨v, by simp [A, hvS, hcv]⟩, ⟨w, by simp [B, hwS, hcw]⟩⟩
    · exact ⟨⟨w, by simp [A, hwS, hcw]⟩, ⟨v, by simp [B, hvS, hcv]⟩⟩
    · simp_all
  have hright : ∀ b : B, d ⌈/⌉ 4 ≤ (fromSimpleGraph C A B).rightDegree b := by
    intro b
    rw [rightDegree_fromSimpleGraph_eq]
    · apply (ceilDiv_le_iff_le_mul (by omega)).2
      have hbS : b.1 ∈ S := (Finset.mem_filter.mp b.2).1
      simpa [C] using hdeg b.1 hbS
    · intro w hbw
      have hwS : w ∈ S := hbw.1.2.2
      have hne : c b.1 ≠ c w := hbw.2
      have hbtrue : c b.1 = true := (Finset.mem_filter.mp b.2).2
      have hwfalse : c w = false := by
        cases hcw : c w <;> simp_all
      exact Finset.mem_filter.mpr ⟨hwS, hwfalse⟩
  obtain ⟨H, hHC, hHreg⟩ :=
    exists_rightRegular_trim (fromSimpleGraph C A B) (d ⌈/⌉ 4) hright
  have hHG : H ≤ fromSimpleGraph G A B := by
    intro a b hab
    exact hCG (hHC hab)
  have hsupport : H.SupportedOn (Finset.univ : Finset A) (Finset.univ : Finset B) := by
    intro a b _
    simp
  have hdelta : d ≤ 4 * (d ⌈/⌉ 4) := by
    simpa using (le_smul_ceilDiv (b := d) (by omega : 0 < (4 : ℕ)))
  have hdeltaSelf : d ⌈/⌉ 4 ≤ d := by
    apply (ceilDiv_le_iff_le_mul (by omega : 0 < (4 : ℕ))).2
    nlinarith
  have hdeltaMax : d ⌈/⌉ 4 ≤ maximumDegreeNumber G := by
    obtain ⟨b, hb⟩ := hparts.2
    calc
      d ⌈/⌉ 4 ≤ degreeNumber C b := by
        rw [← rightDegree_fromSimpleGraph_eq C A B ⟨b, hb⟩]
        · exact hright ⟨b, hb⟩
        · intro w hbw
          have hwS : w ∈ S := hbw.1.2.2
          have hbtrue : c b = true := (Finset.mem_filter.mp hb).2
          have hwfalse : c w = false := by
            have hne : c b ≠ c w := hbw.2
            cases hcw : c w <;> simp_all
          exact Finset.mem_filter.mpr ⟨hwS, hwfalse⟩
      _ ≤ degreeNumber G b := degreeNumber_mono hCG b
      _ ≤ maximumDegreeNumber G := degreeNumber_le_maximumDegreeNumber G b
  exact ⟨A, B, hparts.1, hparts.2, hcard, hAB, H, d ⌈/⌉ 4,
    ⟨hHG, hsupport, by simpa using hparts.2, hHreg⟩,
    rfl, hdelta, hdeltaSelf, hdeltaMax⟩

/-- Compatibility form of the PRS entry reduction.  The stronger companion
`exists_halfRegular_bipartite_entry_strong` additionally records that the
two parts are disjoint and that the extracted degree is at most `d`. -/
theorem exists_halfRegular_bipartite_entry (G : SimpleGraph V) (d : ℕ)
    [Nonempty V] (hd : 0 < d)
    (havg : d * Fintype.card V ≤ 2 * edgeNumber G) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
      ∃ H : BipartiteGraph A B, ∃ δ : ℕ,
        H.IsHalfRegularSubgraphOf (fromSimpleGraph G A B)
            (Finset.univ : Finset A) (Finset.univ : Finset B) δ ∧
          d ≤ 4 * δ ∧ δ ≤ maximumDegreeNumber G := by
  obtain ⟨A, B, hA, hB, hcard, _, H, δ, hH, _, hdδ, _, hδmax⟩ :=
    exists_halfRegular_bipartite_entry_strong G d hd havg
  exact ⟨A, B, hA, hB, hcard, H, δ, hH, hdδ, hδmax⟩

/-- A two-sorted subgraph of an ambient simple graph inherits the ambient
degree bound on every left vertex. -/
theorem leftDegree_le_degreeNumber_of_le {G : SimpleGraph V}
    {A B : Finset V} {H : BipartiteGraph A B}
    (hHG : H ≤ fromSimpleGraph G A B) (a : A) :
    H.leftDegree a ≤ degreeNumber G a.1 := by
  classical
  let f : {b : B // b ∈ H.rightNeighbors a} → G.neighborSet a.1 := fun b ↦
    ⟨b.1.1, hHG ((BipartiteGraph.mem_rightNeighbors H a b.1).mp b.2)⟩
  have hf : Function.Injective f := by
    intro b b' hbb'
    have hv : b.1.1 = b'.1.1 :=
      congrArg (fun x : G.neighborSet a.1 ↦ x.1) hbb'
    exact Subtype.ext (Subtype.ext hv)
  calc
    H.leftDegree a = Fintype.card {b : B // b ∈ H.rightNeighbors a} := by
      exact (Fintype.card_coe (H.rightNeighbors a)).symm
    _ ≤ Fintype.card (G.neighborSet a.1) :=
      Fintype.card_le_of_injective f hf
    _ = degreeNumber G a.1 := by
      simpa only [degreeNumber] using
        (Set.fintypeCard_eq_ncard (G.neighborSet a.1))

/-- The PRS entry reduction, packaged with every numerical fact needed by
the later Janzer--Sudakov degree-bucket split. -/
theorem exists_initial_halfRegular_core
    (G : SimpleGraph V) (d Δ : ℕ) [Nonempty V]
    (hd : 0 < d)
    (havg : d * Fintype.card V ≤ 2 * edgeNumber G)
    (hmax : maximumDegreeNumber G ≤ Δ) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
      Disjoint (A : Set V) (B : Set V) ∧
      ∃ H : BipartiteGraph A B, ∃ δ : ℕ,
        H.IsHalfRegularSubgraphOf (fromSimpleGraph G A B)
            (Finset.univ : Finset A) (Finset.univ : Finset B) δ ∧
        δ = d ⌈/⌉ 4 ∧ d ≤ 4 * δ ∧ δ ≤ d ∧ δ ≤ Δ ∧ 0 < δ ∧
        (∀ a : A, H.leftDegree a ≤ Δ) ∧
        H.edgeCount = B.card * δ ∧
        δ * A.card ≤ H.edgeCount := by
  classical
  obtain ⟨A, B, hA, hB, hABcard, hAB, H, δ, hH, hδeq, hdδ, hδd, hδmax⟩ :=
    exists_halfRegular_bipartite_entry_strong G d hd havg
  have hδΔ : δ ≤ Δ := hδmax.trans hmax
  have hδpos : 0 < δ := by omega
  have hleft : ∀ a : A, H.leftDegree a ≤ Δ := by
    intro a
    exact (leftDegree_le_degreeNumber_of_le hH.1 a).trans
      ((degreeNumber_le_maximumDegreeNumber G a.1).trans hmax)
  have hedge : H.edgeCount = B.card * δ := by
    simpa using
      (BipartiteGraph.edgeCount_eq_card_mul_of_rightRegularOn hH.2.1 hH.2.2.2)
  have hdensity : δ * A.card ≤ H.edgeCount := by
    rw [hedge]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left δ hABcard
  exact ⟨A, B, hA, hB, hABcard, hAB, H, δ, hH, hδeq, hdδ, hδd, hδΔ, hδpos,
    hleft, hedge, hdensity⟩

/-- Version of `exists_initial_halfRegular_core` using Mathlib's ordinary
maximum degree. -/
theorem exists_initial_halfRegular_core_of_maxDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (d Δ : ℕ) [Nonempty V]
    (hd : 0 < d)
    (havg : d * Fintype.card V ≤ 2 * G.edgeFinset.card)
    (hmax : G.maxDegree ≤ Δ) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
      Disjoint (A : Set V) (B : Set V) ∧
      ∃ H : BipartiteGraph A B, ∃ δ : ℕ,
        H.IsHalfRegularSubgraphOf (fromSimpleGraph G A B)
            (Finset.univ : Finset A) (Finset.univ : Finset B) δ ∧
        δ = d ⌈/⌉ 4 ∧ d ≤ 4 * δ ∧ δ ≤ d ∧ δ ≤ Δ ∧ 0 < δ ∧
        (∀ a : A, H.leftDegree a ≤ Δ) ∧
        H.edgeCount = B.card * δ ∧
        δ * A.card ≤ H.edgeCount := by
  have havg' : d * Fintype.card V ≤ 2 * edgeNumber G := by
    rw [edgeNumber_eq_card_edgeFinset]
    exact havg
  have hmax' : maximumDegreeNumber G ≤ Δ := by
    rw [maximumDegreeNumber, Finset.sup_le_iff]
    intro v _
    rw [degreeNumber_eq_degree]
    exact (G.degree_le_maxDegree v).trans hmax
  exact exists_initial_halfRegular_core G d Δ hd havg' hmax'

/-- The ordinary simple graph associated with a two-sorted bipartite graph. -/
def bipartiteSimpleGraph {A B : Type*} (K : BipartiteGraph A B) :
    SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inr b => K.Adj a b
    | Sum.inr b, Sum.inl a => K.Adj a b
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp_all⟩

noncomputable instance bipartiteSimpleGraph.instDecidableRel
    {A B : Type*} (K : BipartiteGraph A B) :
    DecidableRel (bipartiteSimpleGraph K).Adj := Classical.decRel _

theorem degree_bipartiteSimpleGraph_inl {A B : Type*}
    [Fintype A] [Fintype B] (K : BipartiteGraph A B) (a : A) :
    (bipartiteSimpleGraph K).degree (Sum.inl a) = K.leftDegree a := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : (bipartiteSimpleGraph K).neighborSet (Sum.inl a) ≃
      {b : B // K.Adj a b} :=
    { toFun := fun w ↦ by
        rcases w with ⟨w, hw⟩
        cases w with
        | inl a' => simp [bipartiteSimpleGraph] at hw
        | inr b => exact ⟨b, hw⟩
      invFun := fun b ↦ ⟨Sum.inr b.1, b.2⟩
      left_inv := by
        rintro ⟨w, hw⟩
        cases w with
        | inl a' => simp [bipartiteSimpleGraph] at hw
        | inr b => rfl
      right_inv := by intro b; apply Subtype.ext; rfl }
  calc
    Fintype.card ((bipartiteSimpleGraph K).neighborSet (Sum.inl a)) =
        Fintype.card {b : B // K.Adj a b} := Fintype.card_congr e
    _ = #(Finset.univ.filter fun b : B ↦ K.Adj a b) := Fintype.card_subtype _
    _ = K.leftDegree a := by
      simp [BipartiteGraph.leftDegree, BipartiteGraph.rightNeighbors]

theorem degree_bipartiteSimpleGraph_inr {A B : Type*}
    [Fintype A] [Fintype B] (K : BipartiteGraph A B) (b : B) :
    (bipartiteSimpleGraph K).degree (Sum.inr b) = K.rightDegree b := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : (bipartiteSimpleGraph K).neighborSet (Sum.inr b) ≃
      {a : A // K.Adj a b} :=
    { toFun := fun w ↦ by
        rcases w with ⟨w, hw⟩
        cases w with
        | inl a => exact ⟨a, hw⟩
        | inr b' => simp [bipartiteSimpleGraph] at hw
      invFun := fun a ↦ ⟨Sum.inl a.1, a.2⟩
      left_inv := by
        rintro ⟨w, hw⟩
        cases w with
        | inl a => rfl
        | inr b' => simp [bipartiteSimpleGraph] at hw
      right_inv := by intro a; apply Subtype.ext; rfl }
  calc
    Fintype.card ((bipartiteSimpleGraph K).neighborSet (Sum.inr b)) =
        Fintype.card {a : A // K.Adj a b} := Fintype.card_congr e
    _ = #(Finset.univ.filter fun a : A ↦ K.Adj a b) := Fintype.card_subtype _
    _ = K.rightDegree b := by
      simp [BipartiteGraph.rightDegree, BipartiteGraph.leftNeighbors]

/-- Embed two disjoint finite parts into their common ambient vertex type. -/
def sumPartsEmbedding (A B : Finset V)
    (hAB : Disjoint (A : Set V) (B : Set V)) : A ⊕ B ↪ V where
  toFun x := Sum.elim Subtype.val Subtype.val x
  inj' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' => simp_all
        | inr b =>
            exfalso
            change a.1 = b.1 at hxy
            have haB : a.1 ∈ B := by
              rw [hxy]
              exact b.2
            exact Set.disjoint_left.1 hAB a.2 haB
    | inr b =>
        cases y with
        | inl a =>
            exfalso
            change b.1 = a.1 at hxy
            have haB : a.1 ∈ B := by
              rw [← hxy]
              exact b.2
            exact Set.disjoint_left.1 hAB a.2 haB
        | inr b' => simp_all

/-- A two-sorted subgraph between disjoint ambient parts gives a genuine copy
of its associated simple graph in the ambient graph. -/
def bipartiteCopy (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint (A : Set V) (B : Set V))
    (K : BipartiteGraph A B) (hKG : K ≤ fromSimpleGraph G A B) :
    SimpleGraph.Copy (bipartiteSimpleGraph K) G where
  toHom :=
    { toFun := sumPartsEmbedding A B hAB
      map_rel' := by
        intro x y hxy
        cases x with
        | inl a =>
            cases y with
            | inl a' => exact False.elim hxy
            | inr b => exact hKG hxy
        | inr b =>
            cases y with
            | inl a => exact G.symm.symm _ _ (hKG hxy)
            | inr b' => exact False.elim hxy }
  injective' := (sumPartsEmbedding A B hAB).injective

/-- A regular two-sorted bipartite subgraph on disjoint ambient parts lifts
to a nonempty regular subgraph in the literal sense of `ContainsRegularSubgraph`.
This is the bridge used after the PRS extraction theorem. -/
theorem containsRegularSubgraph_of_bipartite {G : SimpleGraph V}
    {A B : Finset V} (hA : A.Nonempty)
    (hAB : Disjoint (A : Set V) (B : Set V))
    (K : BipartiteGraph A B) (hKG : K ≤ fromSimpleGraph G A B) (k : ℕ)
    (hleft : ∀ a, K.leftDegree a = k)
    (hright : ∀ b, K.rightDegree b = k) :
    ContainsRegularSubgraph G k := by
  classical
  let f := bipartiteCopy G A B hAB K hKG
  let H : G.Subgraph := f.toSubgraph
  have hsource : (bipartiteSimpleGraph K).IsRegularOfDegree k := by
    intro x
    cases x with
    | inl a => exact (degree_bipartiteSimpleGraph_inl K a).trans (hleft a)
    | inr b => exact (degree_bipartiteSimpleGraph_inr K b).trans (hright b)
  have hHne : H.verts.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    let x : A ⊕ B := Sum.inl ⟨a, ha⟩
    exact ⟨f x, by simp [H, SimpleGraph.Copy.toSubgraph]⟩
  refine ⟨H, hHne, ?_⟩
  intro v
  let e : bipartiteSimpleGraph K ≃g H.coe := f.isoToSubgraph
  let x : A ⊕ B := e.symm v
  have hdeg : H.coe.degree v = k := by
    have he := e.degree_eq x
    rw [e.apply_symm_apply v] at he
    exact he.trans (hsource x)
  change degreeNumber H.coe v = k
  exact (degreeNumber_eq_degree H.coe v).trans hdeg

/-- Subgraph form of `containsRegularSubgraph_of_bipartite`, convenient when
the regular graph is obtained by extraction inside a larger two-sorted
graph. -/
theorem containsRegularSubgraph_of_bipartite_subgraph {G : SimpleGraph V}
    {A B : Finset V} (hA : A.Nonempty)
    (hAB : Disjoint (A : Set V) (B : Set V))
    (K L : BipartiteGraph A B) (hKG : K ≤ fromSimpleGraph G A B)
    (hLK : L ≤ K) (k : ℕ)
    (hleft : ∀ a, L.leftDegree a = k)
    (hright : ∀ b, L.rightDegree b = k) :
    ContainsRegularSubgraph G k := by
  apply containsRegularSubgraph_of_bipartite hA hAB L _ k hleft hright
  intro a b hab
  exact hKG (hLK hab)

end PRSEntry

end Erdos182
