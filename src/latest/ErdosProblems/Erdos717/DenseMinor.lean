/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Dense connected-bag minor lemmas for Erdős Problem 717.

The numerical core is the elementary contraction argument behind the
eight-times-density version of the Bollobás--Thomason--Komlós--Szemerédi
topological-clique theorem.
-/

import ErdosProblems.Erdos717.ThomasWollan

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace DenseMinor

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### Contracting one edge in a finite simple graph -/

/-- The simple graph obtained by identifying `b` with `a` and then deleting
`b`.  The explicit inequality in the adjacency relation removes the loop
created by the contracted edge. -/
def contractAt (G : SimpleGraph V) (a b : V) :
    SimpleGraph {x : V // x ≠ b} where
  Adj x y := x ≠ y ∧
    (G.Adj x y ∨
      ((x : V) = a ∧ G.Adj b y) ∨
      ((y : V) = a ∧ G.Adj b x))
  symm.symm x y := by
    intro h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hxy | hxy | hxy
    · exact Or.inl hxy.symm
    · exact Or.inr (Or.inr ⟨hxy.1, hxy.2⟩)
    · exact Or.inr (Or.inl ⟨hxy.1, hxy.2⟩)
  loopless.irrefl x := by simp

instance contractAt.instDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : DecidableRel (contractAt G a b).Adj :=
  inferInstanceAs <| DecidableRel fun x y : {x : V // x ≠ b} =>
    x ≠ y ∧
      (G.Adj x y ∨ ((x : V) = a ∧ G.Adj b y) ∨
        ((y : V) = a ∧ G.Adj b x))

/-- Neighbors of `b` which are neither `a` nor already adjacent to `a`.
They give the genuinely new edges created by contracting `ab`. -/
def exclusiveNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : Finset V :=
  G.neighborFinset b \ insert a (G.neighborFinset a)

lemma mem_exclusiveNeighbors_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b w : V} :
    w ∈ exclusiveNeighbors G a b ↔
      G.Adj b w ∧ w ≠ a ∧ ¬G.Adj a w := by
  simp [exclusiveNeighbors, G.mem_neighborFinset]

/-- The vertices common to the two ends of the edge being contracted. -/
def commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : Finset V :=
  G.neighborFinset a ∩ G.neighborFinset b

lemma card_exclusiveNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) :
    (exclusiveNeighbors G a b).card + 1 +
        (commonNeighborFinset G a b).card = G.degree b := by
  classical
  let Na := G.neighborFinset a
  let Nb := G.neighborFinset b
  have haNb : a ∈ Nb := by simpa [Nb] using hab.symm
  have haNa : a ∉ Na := by simp [Na]
  have hinter : Nb ∩ insert a Na = insert a (Na ∩ Nb) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hwNb, rfl | hwNa⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hwNa, hwNb⟩
    · rintro (rfl | ⟨hwNa, hwNb⟩)
      · exact ⟨haNb, Or.inl rfl⟩
      · exact ⟨hwNb, Or.inr hwNa⟩
  have hcardInter : (Nb ∩ insert a Na).card = 1 + (Na ∩ Nb).card := by
    have hnot : a ∉ Na ∩ Nb := by
      intro h
      exact haNa (Finset.mem_inter.mp h).1
    rw [hinter, Finset.card_insert_of_notMem hnot, Nat.add_comm]
  have hsplit := Finset.card_sdiff_add_card_inter Nb (insert a Na)
  change (Nb \ insert a Na).card + 1 + (Na ∩ Nb).card = G.degree b
  calc
    (Nb \ insert a Na).card + 1 + (Na ∩ Nb).card =
        (Nb \ insert a Na).card + (Nb ∩ insert a Na).card := by omega
    _ = Nb.card := hsplit
    _ = G.degree b := by simpa [Nb] using G.card_neighborFinset_eq_degree b

private def newEdgeEmbedding (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) :
    exclusiveNeighbors G a b ↪ Sym2 {x : V // x ≠ b} where
  toFun w := s(⟨a, hab.ne⟩, ⟨w, by
    intro hwb
    have hbw := (mem_exclusiveNeighbors_iff G).mp w.2 |>.1
    exact hbw.ne (hwb.symm)⟩)
  inj' := by
    intro w z hwz
    rw [Sym2.eq_iff] at hwz
    rcases hwz with h | h
    · apply Subtype.ext
      exact congrArg (fun x : {x : V // x ≠ b} => (x : V)) h.2
    · exfalso
      have hza : (z : V) = a :=
        congrArg (fun x : {x : V // x ≠ b} => (x : V)) h.1.symm
      exact ((mem_exclusiveNeighbors_iff G).mp z.2).2.1 hza

lemma card_contractAt_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) :
    G.edgeFinset.card ≤ (contractAt G a b).edgeFinset.card + 1 +
      (commonNeighborFinset G a b).card := by
  classical
  let D := G.induce {x : V | x ≠ b}
  let C := contractAt G a b
  let newEdges := (Finset.univ : Finset (exclusiveNeighbors G a b)).map
    (newEdgeEmbedding G hab)
  have hDsub : D.edgeFinset ⊆ C.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he ⊢
      exact ⟨he.ne, Or.inl he⟩
  have hnewSub : newEdges ⊆ C.edgeFinset := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp he
    have hw' := (mem_exclusiveNeighbors_iff G).mp w.2
    rw [SimpleGraph.mem_edgeFinset]
    change C.Adj ⟨a, hab.ne⟩ ⟨w, by
      intro hwb
      exact hw'.1.ne hwb.symm⟩
    refine ⟨?_, Or.inr (Or.inl ⟨rfl, hw'.1⟩)⟩
    intro h
    have := congrArg (fun z : {x : V // x ≠ b} => (z : V)) h
    exact hw'.2.1 this.symm
  have hdisj : Disjoint D.edgeFinset newEdges := by
    rw [Finset.disjoint_left]
    intro e heD heNew
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp heNew
    subst e
    have heD' := SimpleGraph.mem_edgeFinset.mp heD
    change s(⟨a, hab.ne⟩, ⟨w, by
      intro hwb
      exact ((mem_exclusiveNeighbors_iff G).mp w.2).1.ne hwb.symm⟩) ∈ D.edgeSet at heD'
    rw [SimpleGraph.mem_edgeSet] at heD'
    have hadj : G.Adj a w := heD'
    exact ((mem_exclusiveNeighbors_iff G).mp w.2).2.2 hadj
  have hbaseCard : D.edgeFinset.card = G.edgeFinset.card - G.degree b := by
    exact (G.card_edgeFinset_induce_compl_singleton b).trans
      (G.card_edgeFinset_deleteIncidenceSet b)
  have hnewCard : newEdges.card = (exclusiveNeighbors G a b).card := by
    simp [newEdges]
  have hunion : (D.edgeFinset ∪ newEdges).card =
      D.edgeFinset.card + newEdges.card := by
    rw [Finset.card_union_of_disjoint hdisj]
  have hle : D.edgeFinset.card + newEdges.card ≤ C.edgeFinset.card := by
    rw [← hunion]
    exact Finset.card_le_card (Finset.union_subset hDsub hnewSub)
  have hexclusive := card_exclusiveNeighbors G hab
  have hdegreeEdge : G.degree b ≤ G.edgeFinset.card :=
    G.degree_le_card_edgeFinset b
  rw [hbaseCard, hnewCard] at hle
  calc
    G.edgeFinset.card =
        (G.edgeFinset.card - G.degree b) + G.degree b :=
      (Nat.sub_add_cancel hdegreeEdge).symm
    _ = (G.edgeFinset.card - G.degree b) +
        ((exclusiveNeighbors G a b).card + 1 +
          (commonNeighborFinset G a b).card) := by rw [hexclusive]
    _ = ((G.edgeFinset.card - G.degree b) +
          (exclusiveNeighbors G a b).card) + 1 +
          (commonNeighborFinset G a b).card := by omega
    _ ≤ C.edgeFinset.card + 1 +
          (commonNeighborFinset G a b).card := by
      exact Nat.add_le_add_right (Nat.add_le_add_right hle 1) _
    _ = (contractAt G a b).edgeFinset.card + 1 +
          (commonNeighborFinset G a b).card := by rfl

/-! ### Connected bag packings and their quotient graphs -/

/-- A nonempty finite vertex set whose induced graph is connected. -/
def IsConnectedBag (G : SimpleGraph V) (B : Finset V) : Prop :=
  B.Nonempty ∧ (G.induce (B : Set V)).Preconnected

/-- A finite family of nonempty connected, pairwise disjoint bags. -/
def IsConnectedPacking (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ B ∈ P, IsConnectedBag G B) ∧
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B)

/-- The quotient graph of a bag packing: two bags are adjacent when an edge
of the host graph joins them. -/
def quotientGraph (G : SimpleGraph V) (P : Finset (Finset V)) :
    SimpleGraph P where
  Adj A B := A ≠ B ∧ ∃ x ∈ (A : Finset V), ∃ y ∈ (B : Finset V), G.Adj x y
  symm.symm A B h := by
    obtain ⟨hne, x, hx, y, hy, hxy⟩ := h
    exact ⟨hne.symm, y, hy, x, hx, hxy.symm⟩
  loopless.irrefl A := by simp

instance quotientGraph.instDecidableRel (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Finset V)) :
    DecidableRel (quotientGraph G P).Adj :=
  inferInstanceAs <| DecidableRel fun A B : P =>
    A ≠ B ∧ ∃ x ∈ (A : Finset V), ∃ y ∈ (B : Finset V), G.Adj x y

lemma singleton_isConnectedBag (G : SimpleGraph V) (v : V) :
    IsConnectedBag G {v} := by
  constructor
  · simp
  · intro x y
    have hx : (x : V) = v := by simpa using x.2
    have hy : (y : V) = v := by simpa using y.2
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    subst y
    exact SimpleGraph.Reachable.rfl

/-- The packing into singleton bags. -/
def singletonPacking : Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

lemma mem_singletonPacking_iff {B : Finset V} :
    B ∈ (singletonPacking : Finset (Finset V)) ↔ ∃ v : V, B = {v} := by
  simp [singletonPacking, eq_comm]

lemma singletonPacking_card :
    (singletonPacking : Finset (Finset V)).card = Fintype.card V := by
  rw [singletonPacking, Finset.card_image_iff.mpr]
  · simp
  · intro x y h
    simpa using h

lemma singletonPacking_connected (G : SimpleGraph V) :
    IsConnectedPacking G singletonPacking := by
  constructor
  · intro B hB
    obtain ⟨v, rfl⟩ := mem_singletonPacking_iff.mp hB
    exact singleton_isConnectedBag G v
  · intro A hA B hB hne
    obtain ⟨a, rfl⟩ := mem_singletonPacking_iff.mp hA
    obtain ⟨b, rfl⟩ := mem_singletonPacking_iff.mp hB
    rw [Finset.disjoint_singleton]
    simpa using hne

private def singletonBagEmbedding :
    V ↪ (singletonPacking : Finset (Finset V)) where
  toFun v := ⟨{v}, mem_singletonPacking_iff.mpr ⟨v, rfl⟩⟩
  inj' := by
    intro v w h
    have h' := congrArg (fun B : (singletonPacking : Finset (Finset V)) =>
      (B : Finset V)) h
    simpa using h'

lemma singletonBagEmbedding_surjective :
    Function.Surjective (singletonBagEmbedding :
      V ↪ (singletonPacking : Finset (Finset V))) := by
  intro B
  obtain ⟨v, hv⟩ := mem_singletonPacking_iff.mp B.2
  refine ⟨v, Subtype.ext ?_⟩
  exact hv.symm

/-- The singleton quotient is canonically isomorphic to the host graph. -/
noncomputable def singletonQuotientIso (G : SimpleGraph V) :
    G ≃g quotientGraph G singletonPacking := by
  let e : V ≃ (singletonPacking : Finset (Finset V)) :=
    Equiv.ofBijective singletonBagEmbedding
      ⟨singletonBagEmbedding.injective, singletonBagEmbedding_surjective⟩
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro v w
  constructor
  · rintro ⟨_, x, hx, y, hy, hxy⟩
    have hxv : x = v := by
      change x ∈ ({v} : Finset V) at hx
      simpa using hx
    have hyw : y = w := by
      change y ∈ ({w} : Finset V) at hy
      simpa using hy
    simpa [hxv, hyw] using hxy
  · intro hvw
    refine ⟨fun h => hvw.ne (e.injective h), v, ?_, w, ?_, hvw⟩
    · change v ∈ ({v} : Finset V)
      simp
    · change w ∈ ({w} : Finset V)
      simp

lemma card_edgeFinset_singletonQuotient (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (quotientGraph G singletonPacking).edgeFinset.card = G.edgeFinset.card := by
  exact (singletonQuotientIso G).card_edgeFinset_eq.symm

lemma IsConnectedBag.union_of_adj {G : SimpleGraph V}
    {A B : Finset V} (hA : IsConnectedBag G A)
    (hB : IsConnectedBag G B) {x y : V}
    (hx : x ∈ A) (hy : y ∈ B) (hxy : G.Adj x y) :
    IsConnectedBag G (A ∪ B) := by
  constructor
  · exact ⟨x, Finset.mem_union_left _ hx⟩
  · let U : Set V := (A ∪ B : Finset V)
    have reachA {p q : V} (hp : p ∈ A) (hq : q ∈ A) :
        (G.induce U).Reachable
          ⟨p, Finset.mem_union_left B hp⟩
          ⟨q, Finset.mem_union_left B hq⟩ := by
      have hr := hA.2 ⟨p, hp⟩ ⟨q, hq⟩
      have hm := hr.map (G.induceHomOfLE (s := (A : Set V))
        (s' := U) (by
          intro z hz
          exact Finset.mem_union_left B hz)).toHom
      convert hm using 1 <;> rfl
    have reachB {p q : V} (hp : p ∈ B) (hq : q ∈ B) :
        (G.induce U).Reachable
          ⟨p, Finset.mem_union_right A hp⟩
          ⟨q, Finset.mem_union_right A hq⟩ := by
      have hr := hB.2 ⟨p, hp⟩ ⟨q, hq⟩
      have hm := hr.map (G.induceHomOfLE (s := (B : Set V))
        (s' := U) (by
          intro z hz
          exact Finset.mem_union_right A hz)).toHom
      convert hm using 1 <;> rfl
    have hedge : (G.induce U).Reachable
        ⟨x, Finset.mem_union_left B hx⟩
        ⟨y, Finset.mem_union_right A hy⟩ := by
      have hadj : (G.induce U).Adj
          ⟨x, Finset.mem_union_left B hx⟩
          ⟨y, Finset.mem_union_right A hy⟩ := hxy
      exact ⟨hadj.toWalk⟩
    intro p q
    rcases Finset.mem_union.mp p.2 with hpA | hpB
    · rcases Finset.mem_union.mp q.2 with hqA | hqB
      · exact reachA hpA hqA
      · exact (reachA hpA hx).trans (hedge.trans (reachB hy hqB))
    · rcases Finset.mem_union.mp q.2 with hqA | hqB
      · exact (reachB hpB hy).trans (hedge.symm.trans (reachA hx hqA))
      · exact reachB hpB hqB

/-- Merge two bags of a packing. -/
def mergePacking (P : Finset (Finset V)) (A B : Finset V) :
    Finset (Finset V) :=
  insert (A ∪ B) ((P.erase A).erase B)

lemma mem_mergePacking_union (P : Finset (Finset V)) (A B : Finset V) :
    A ∪ B ∈ mergePacking P A B := by
  simp [mergePacking]

lemma mem_mergePacking_of_mem {P : Finset (Finset V)} {A B C : Finset V}
    (hC : C ∈ P) (hCA : C ≠ A) (hCB : C ≠ B) :
    C ∈ mergePacking P A B := by
  simp [mergePacking, hC, hCA, hCB]

lemma union_not_mem_erased_of_packing {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    A ∪ B ∉ (P.erase A).erase B := by
  intro h
  have hU := (Finset.mem_erase.mp h).2
  have hUA := (Finset.mem_erase.mp hU).1
  have hUmem := (Finset.mem_erase.mp hU).2
  obtain ⟨x, hx⟩ := (hP.1 A hA).1
  have hdisj := hP.2 A hA (A ∪ B) hUmem hUA.symm
  exact (Finset.disjoint_left.mp hdisj) hx (Finset.mem_union_left B hx)

lemma card_mergePacking {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    (mergePacking P A B).card + 1 = P.card := by
  have hB' : B ∈ P.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hpair : ({A, B} : Finset (Finset V)) ⊆ P := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact hA
    · exact hB
  have hP2 := Finset.card_le_card hpair
  rw [Finset.card_pair hAB] at hP2
  rw [mergePacking, Finset.card_insert_of_notMem
    (union_not_mem_erased_of_packing hP hA hB hAB),
    Finset.card_erase_of_mem hB', Finset.card_erase_of_mem hA]
  omega

lemma mergePacking_connected {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hquot : (quotientGraph G P).Adj ⟨A, hA⟩ ⟨B, hB⟩) :
    IsConnectedPacking G (mergePacking P A B) := by
  obtain ⟨_, x, hx, y, hy, hxy⟩ := hquot
  constructor
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact (hP.1 A hA).union_of_adj (hP.1 B hB) hx hy hxy
    · exact hP.1 C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
  · intro C hC D hD hCD
    rcases Finset.mem_insert.mp hC with rfl | hC
    · rcases Finset.mem_insert.mp hD with h | hD
      · exact (hCD h.symm).elim
      · have hDP := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD)
        have hDinner := (Finset.mem_erase.mp hD).2
        have hDA : D ≠ A := (Finset.mem_erase.mp hDinner).1
        have hDB : D ≠ B := (Finset.mem_erase.mp hD).1
        exact Finset.disjoint_union_left.mpr
          ⟨hP.2 A hA D hDP hDA.symm, hP.2 B hB D hDP hDB.symm⟩
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · have hCP := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
        have hCinner := (Finset.mem_erase.mp hC).2
        have hCA : C ≠ A := (Finset.mem_erase.mp hCinner).1
        have hCB : C ≠ B := (Finset.mem_erase.mp hC).1
        exact (Finset.disjoint_union_left.mpr
          ⟨hP.2 A hA C hCP hCA.symm,
            hP.2 B hB C hCP hCB.symm⟩).symm
      · exact hP.2 C
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)) D
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD)) hCD

private lemma union_ne_other_of_packing {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    {A B C : Finset V} (hA : A ∈ P) (hC : C ∈ P) (hAC : A ≠ C) :
    A ∪ B ≠ C := by
  intro h
  obtain ⟨x, hx⟩ := (hP.1 A hA).1
  have hxC : x ∈ C := by rw [← h]; exact Finset.mem_union_left B hx
  exact (Finset.disjoint_left.mp (hP.2 A hA C hC hAC)) hx hxC

/-- The injective vertex map induced by merging `B` into `A`. -/
private def mergeBagEmbedding {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    (A B : P) (hAB : A ≠ B) :
    {C : P // C ≠ B} ↪ mergePacking P A B where
  toFun C := ⟨if hCA : (C.1 : Finset V) = A then
      (A : Finset V) ∪ B else C.1, by
    split
    · exact mem_mergePacking_union P A B
    · rename_i hCA
      exact mem_mergePacking_of_mem C.1.2 hCA
        (fun hCB => C.2 (Subtype.ext hCB))⟩
  inj' := by
    intro C D h
    by_cases hCA : (C.1 : Finset V) = A
    · by_cases hDA : (D.1 : Finset V) = A
      · apply Subtype.ext
        apply Subtype.ext
        exact hCA.trans hDA.symm
      · have hval := congrArg (fun E : mergePacking P A B =>
          (E : Finset V)) h
        simp only [dif_pos hCA, dif_neg hDA] at hval
        exact (union_ne_other_of_packing hP A.2 D.1.2 (Ne.symm hDA) hval).elim
    · by_cases hDA : (D.1 : Finset V) = A
      · have hval := congrArg (fun E : mergePacking P A B =>
          (E : Finset V)) h
        simp only [dif_neg hCA, dif_pos hDA] at hval
        exact (union_ne_other_of_packing hP A.2 C.1.2 (Ne.symm hCA) hval.symm).elim
      · apply Subtype.ext
        apply Subtype.ext
        have hval := congrArg (fun E : mergePacking P A B =>
          (E : Finset V)) h
        simpa only [dif_neg hCA, dif_neg hDA] using hval

private lemma mergeBagEmbedding_val {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    (A B : P) (hAB : A ≠ B) (C : {C : P // C ≠ B}) :
    ((mergeBagEmbedding hP A B hAB C : mergePacking P A B) : Finset V) =
      if hCA : (C.1 : Finset V) = A then (A : Finset V) ∪ B else C.1 := by
  rfl

private lemma mem_mergeBagEmbedding_of_mem {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    (A B : P) (hAB : A ≠ B) (C : {C : P // C ≠ B})
    {x : V} (hx : x ∈ (C.1 : Finset V)) :
    x ∈ ((mergeBagEmbedding hP A B hAB C : mergePacking P A B) : Finset V) := by
  rw [mergeBagEmbedding_val]
  split
  · rename_i hCA
    exact Finset.mem_union_left B (hCA ▸ hx)
  · exact hx

private lemma mem_mergeBagEmbedding_B {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    (A B : P) (hAB : A ≠ B) {x : V} (hx : x ∈ (B : Finset V)) :
    x ∈ ((mergeBagEmbedding hP A B hAB
      ⟨A, hAB⟩ : mergePacking P A B) : Finset V) := by
  rw [mergeBagEmbedding_val]
  rw [dif_pos rfl]
  exact Finset.mem_union_right A hx

/-- Contracting an edge of a quotient graph maps injectively into the quotient
of the merged packing. -/
private def contractQuotientHom {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    (H : SimpleGraph P) (hH : H ≤ quotientGraph G P)
    (A B : P) (hAB : A ≠ B) :
    contractAt H A B →g quotientGraph G (mergePacking P A B) where
  toFun := mergeBagEmbedding hP A B hAB
  map_rel' := by
    intro C D hCD
    refine ⟨(mergeBagEmbedding hP A B hAB).injective.ne hCD.1, ?_⟩
    rcases hCD.2 with h | h | h
    · obtain ⟨_, x, hx, y, hy, hxy⟩ := hH h
      exact ⟨x, mem_mergeBagEmbedding_of_mem hP A B hAB C hx,
        y, mem_mergeBagEmbedding_of_mem hP A B hAB D hy, hxy⟩
    · have hCA : C = (⟨A, hAB⟩ : {C : P // C ≠ B}) := by
        apply Subtype.ext
        exact h.1
      obtain ⟨_, x, hx, y, hy, hxy⟩ := hH h.2
      have hx' := mem_mergeBagEmbedding_B hP A B hAB hx
      rw [← hCA] at hx'
      exact ⟨x, hx',
        y, mem_mergeBagEmbedding_of_mem hP A B hAB D hy, hxy⟩
    · have hDA : D = (⟨A, hAB⟩ : {C : P // C ≠ B}) := by
        apply Subtype.ext
        exact h.1
      obtain ⟨_, x, hx, y, hy, hxy⟩ := hH h.2
      have hx' := mem_mergeBagEmbedding_B hP A B hAB hx
      rw [← hDA] at hx'
      exact ⟨y, mem_mergeBagEmbedding_of_mem hP A B hAB C hy,
        x, hx', hxy.symm⟩

lemma card_contractAt_le_mergedQuotient {G : SimpleGraph V}
    [DecidableRel G.Adj]
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P)
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (hH : H ≤ quotientGraph G P)
    (A B : P) (hAB : A ≠ B) :
    (contractAt H A B).edgeFinset.card ≤
      (quotientGraph G (mergePacking P A B)).edgeFinset.card := by
  classical
  let f := mergeBagEmbedding hP A B hAB
  have hmap : (contractAt H A B).edgeFinset.map f.sym2Map ⊆
      (quotientGraph G (mergePacking P A B)).edgeFinset := by
    intro z hz
    obtain ⟨e, heSource, rfl⟩ := Finset.mem_map.mp hz
    have heSource' := SimpleGraph.mem_edgeFinset.mp heSource
    rw [SimpleGraph.mem_edgeFinset]
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at heSource'
      have htarget :=
        (contractQuotientHom hP H hH A B hAB).map_rel' heSource'
      rw [Embedding.sym2Map_apply, Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact htarget
  rw [← Finset.card_map f.sym2Map]
  exact Finset.card_le_card hmap

/-! ### Edge-exact subgraphs and minimal dense packings -/

/-- The simple graph whose edge set is a prescribed finite collection of
non-diagonal unordered pairs.  We use it only for subsets of another simple
graph's edge set. -/
def edgeGraph (E : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 V))

instance edgeGraph.instDecidableRel (E : Finset (Sym2 V)) :
    DecidableRel (edgeGraph E).Adj :=
  inferInstanceAs <| DecidableRel
    (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Adj

lemma edgeGraph_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) : edgeGraph E ≤ G := by
  rw [edgeGraph, SimpleGraph.fromEdgeSet_le]
  intro e he
  exact SimpleGraph.mem_edgeFinset.mp (hE (Set.mem_of_mem_sdiff he))

lemma edgeSet_edgeGraph_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) :
    (edgeGraph E).edgeSet = (E : Set (Sym2 V)) := by
  rw [edgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact sdiff_eq_left.mpr (Set.disjoint_left.mpr fun e heE hediag =>
    (G.not_isDiag_of_mem_edgeSet
      (SimpleGraph.mem_edgeFinset.mp (hE (by exact heE))))
        (Sym2.mem_diagSet.mp hediag))

lemma edgeFinset_edgeGraph_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) :
    (edgeGraph E).edgeFinset = E := by
  apply Finset.coe_injective
  simpa only [SimpleGraph.edgeFinset, Set.coe_toFinset] using
    edgeSet_edgeGraph_eq hE

/-- A connected-bag packing whose quotient has more than `d` edges per bag. -/
def IsDensePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (P : Finset (Finset V)) : Prop :=
  IsConnectedPacking G P ∧ d * P.card < (quotientGraph G P).edgeFinset.card

lemma singleton_isDensePacking {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (h : d * Fintype.card V < G.edgeFinset.card) :
    IsDensePacking G d singletonPacking := by
  constructor
  · exact singletonPacking_connected G
  · rw [singletonPacking_card, card_edgeFinset_singletonQuotient]
    exact h

/-- A dense packing with the fewest bags.  It exists because the singleton
packing is dense whenever the host graph has more than `d |V|` edges. -/
lemma exists_minimal_densePacking {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (h : d * Fintype.card V < G.edgeFinset.card) :
    ∃ P : Finset (Finset V), IsDensePacking G d P ∧
      ∀ Q : Finset (Finset V), IsDensePacking G d Q → P.card ≤ Q.card := by
  classical
  let candidates := (Finset.univ : Finset (Finset (Finset V))).filter
    (IsDensePacking G d)
  have hcandidates : candidates.Nonempty := by
    refine ⟨singletonPacking, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact singleton_isDensePacking h
  obtain ⟨P, hPcand, hmin⟩ :=
    candidates.exists_min_image Finset.card hcandidates
  have hPdense : IsDensePacking G d P := by
    exact (Finset.mem_filter.mp hPcand).2
  refine ⟨P, hPdense, ?_⟩
  intro Q hQ
  apply hmin Q
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hQ⟩

/-- Select exactly `d |P| + 1` quotient edges. -/
lemma exists_exactEdgeGraph {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset (Finset V)} {d : ℕ}
    (h : d * P.card < (quotientGraph G P).edgeFinset.card) :
    ∃ H : SimpleGraph P,
      H ≤ quotientGraph G P ∧ H.edgeSet.ncard = d * P.card + 1 := by
  classical
  obtain ⟨E, hEQ, hEcard⟩ :=
    Finset.exists_subset_card_eq (show d * P.card + 1 ≤
      (quotientGraph G P).edgeFinset.card by omega)
  let H : SimpleGraph P := edgeGraph E
  refine ⟨H, edgeGraph_le hEQ, ?_⟩
  rw [show H.edgeSet = (E : Set (Sym2 P)) from edgeSet_edgeGraph_eq hEQ]
  simpa using hEcard

/-! Deleting a bag is the other elementary packing operation needed for
minimality. -/

lemma erase_isConnectedPacking {G : SimpleGraph V}
    {P : Finset (Finset V)} (hP : IsConnectedPacking G P) (A : Finset V) :
    IsConnectedPacking G (P.erase A) := by
  constructor
  · intro B hB
    exact hP.1 B (Finset.mem_of_mem_erase hB)
  · intro B hB C hC hBC
    exact hP.2 B (Finset.mem_of_mem_erase hB) C
      (Finset.mem_of_mem_erase hC) hBC

/-- The induced graph obtained by deleting a quotient vertex embeds into the
quotient of the packing with that bag erased. -/
private def eraseQuotientHom {G : SimpleGraph V}
    {P : Finset (Finset V)} (H : SimpleGraph P)
    (hH : H ≤ quotientGraph G P) (A : P) :
    H.induce ({A}ᶜ : Set P) →g quotientGraph G (P.erase A) where
  toFun C := ⟨C.1.1, Finset.mem_erase.mpr ⟨by
    intro h
    exact C.2 (by simpa using Subtype.ext h), C.1.2⟩⟩
  map_rel' := by
    intro C D hCD
    obtain ⟨hne, x, hx, y, hy, hxy⟩ := hH hCD
    refine ⟨?_, x, hx, y, hy, hxy⟩
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun Z : (P.erase A : Set (Finset V)) =>
      (Z : Finset V)) h

lemma card_induce_compl_singleton_le_eraseQuotient {G : SimpleGraph V}
    [DecidableRel G.Adj]
    {P : Finset (Finset V)} (H : SimpleGraph P) [DecidableRel H.Adj]
    (hH : H ≤ quotientGraph G P) (A : P) :
    (H.induce ({A}ᶜ : Set P)).edgeFinset.card ≤
      (quotientGraph G (P.erase A)).edgeFinset.card := by
  classical
  let f : ({A}ᶜ : Set P) ↪ (P.erase A : Set (Finset V)) := {
    toFun := eraseQuotientHom H hH A
    inj' := by
      intro C D h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun Z : (P.erase A : Set (Finset V)) =>
        (Z : Finset V)) h
  }
  have hmap : (H.induce ({A}ᶜ : Set P)).edgeFinset.map f.sym2Map ⊆
      (quotientGraph G (P.erase A)).edgeFinset := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hz
    have he' := SimpleGraph.mem_edgeFinset.mp he
    rw [SimpleGraph.mem_edgeFinset]
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [Embedding.sym2Map_apply, Sym2.map_mk, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.mem_edgeSet] at he'
      exact (eraseQuotientHom H hH A).map_rel' he'
  rw [← Finset.card_map f.sym2Map]
  exact Finset.card_le_card hmap

lemma minimalDense_exact_minDegree {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} {P : Finset (Finset V)}
    (hP : IsConnectedPacking G P)
    (hmin : ∀ Q : Finset (Finset V), IsDensePacking G d Q →
      P.card ≤ Q.card)
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (hH : H ≤ quotientGraph G P)
    (hHexact : H.edgeSet.ncard = d * P.card + 1) :
    ∀ A : P, d + 1 ≤ H.degree A := by
  classical
  have hHexact' : H.edgeFinset.card = d * P.card + 1 := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hHexact
  intro A
  by_contra hdegree
  have hdegree' : H.degree A ≤ d := by omega
  have hdelete :
      (H.induce ({A}ᶜ : Set P)).edgeFinset.card =
        H.edgeFinset.card - H.degree A :=
    (H.card_edgeFinset_induce_compl_singleton A).trans
      (H.card_edgeFinset_deleteIncidenceSet A)
  have hdenseErase : IsDensePacking G d (P.erase A) := by
    constructor
    · exact erase_isConnectedPacking hP A
    · calc
        d * (P.erase A).card <
            (H.induce ({A}ᶜ : Set P)).edgeFinset.card := by
          rw [Finset.card_erase_of_mem A.2, hdelete, hHexact']
          rw [Nat.lt_sub_iff_add_lt]
          have hp : 0 < P.card := Finset.card_pos.mpr ⟨A, A.2⟩
          have hmul : d * P.card = d * (P.card - 1) + d := by
            conv_lhs => rw [show P.card = (P.card - 1) + 1 by omega]
            rw [mul_add, mul_one]
          omega
        _ ≤ (quotientGraph G (P.erase A)).edgeFinset.card :=
          card_induce_compl_singleton_le_eraseQuotient H hH A
  have hcard := hmin (P.erase A) hdenseErase
  rw [Finset.card_erase_of_mem A.2] at hcard
  have hp : 0 < P.card := Finset.card_pos.mpr ⟨A, A.2⟩
  omega

lemma minimalDense_exact_commonNeighbors {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} {P : Finset (Finset V)}
    (hP : IsConnectedPacking G P)
    (hmin : ∀ Q : Finset (Finset V), IsDensePacking G d Q →
      P.card ≤ Q.card)
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (hH : H ≤ quotientGraph G P)
    (hHexact : H.edgeSet.ncard = d * P.card + 1) :
    ∀ A B : P, H.Adj A B →
      d ≤ (commonNeighborFinset H A B).card := by
  classical
  have hHexact' : H.edgeFinset.card = d * P.card + 1 := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hHexact
  intro A B hAB
  by_contra hcommon
  have hcommon' : (commonNeighborFinset H A B).card < d := by omega
  have hcontract := card_contractAt_ge H hAB
  have hcontract_le := card_contractAt_le_mergedQuotient hP H hH A B hAB.ne
  have hquotAB : (quotientGraph G P).Adj A B := hH hAB
  have hABval : (A : Finset V) ≠ (B : Finset V) := by
    intro h
    exact hAB.ne (Subtype.ext h)
  have hdenseMerge : IsDensePacking G d (mergePacking P A B) := by
    constructor
    · exact mergePacking_connected hP A.2 B.2 hABval hquotAB
    · calc
        d * (mergePacking P A B).card <
            (contractAt H A B).edgeFinset.card := by
          have hcard := card_mergePacking hP A.2 B.2 hABval
          have hmul : d * P.card =
              d * (mergePacking P A B).card + d := by
            conv_lhs => rw [← hcard]
            rw [mul_add, mul_one]
          by_contra hc
          have hc' : (contractAt H A B).edgeFinset.card ≤
              d * (mergePacking P A B).card := by omega
          have hupper : H.edgeFinset.card ≤
              d * (mergePacking P A B).card + 1 +
                (commonNeighborFinset H A B).card :=
            hcontract.trans (Nat.add_le_add_right
              (Nat.add_le_add_right hc' 1) _)
          rw [hHexact', hmul] at hupper
          omega
        _ ≤ (quotientGraph G (mergePacking P A B)).edgeFinset.card :=
          hcontract_le
  have hcardMin := hmin (mergePacking P A B) hdenseMerge
  have hcardMerge := card_mergePacking hP A.2 B.2 hABval
  omega

/-! ### The small high-minimum-degree graph -/

lemma exists_degree_le_twice_density
    {P : Finset (Finset V)} (H : SimpleGraph P) [DecidableRel H.Adj]
    {d : ℕ} (hHexact : H.edgeSet.ncard = d * P.card + 1) :
    ∃ v : P, H.degree v ≤ 2 * d + 1 := by
  classical
  have hHexact' : H.edgeFinset.card = d * P.card + 1 := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hHexact
  have hedgepos : 0 < H.edgeFinset.card := by rw [hHexact']; omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hedgepos
  have hp2 : 2 ≤ P.card := by
    have he' := SimpleGraph.mem_edgeFinset.mp he
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he'
      have hxpos : 0 < H.degree x := he'.degree_pos_left
      have hxlt : H.degree x < Fintype.card P := H.degree_lt_card_verts x
      simpa using (show 2 ≤ Fintype.card P by omega)
  by_contra hex
  push_neg at hex
  have hsumLower : P.card * (2 * d + 2) ≤ ∑ x : P, H.degree x := by
    calc
      P.card * (2 * d + 2) = ∑ _x : P, (2 * d + 2) := by simp
      _ ≤ ∑ x : P, H.degree x :=
        Finset.sum_le_sum fun x _hx => by have := hex x; omega
  rw [H.sum_degrees_eq_twice_card_edges, hHexact'] at hsumLower
  have hnorm : P.card * (2 * d + 2) =
      2 * (d * P.card) + 2 * P.card := by ring
  rw [hnorm, mul_add, mul_one] at hsumLower
  omega

lemma card_le_degree_induce_of_subset
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (S D : Finset P) (x : (S : Set P))
    (hD : ∀ y ∈ D, H.Adj x y ∧ y ∈ S) :
    D.card ≤ (H.induce (S : Set P)).degree x := by
  classical
  let f : (D : Set P) ↪ (H.induce (S : Set P)).neighborSet x := {
    toFun := fun y => ⟨⟨y, (hD y y.2).2⟩, (hD y y.2).1⟩
    inj' := by
      intro y z h
      apply Subtype.ext
      exact congrArg (fun w : (H.induce (S : Set P)).neighborSet x =>
        ((w : (S : Set P)) : P)) h
  }
  have hcard := Fintype.card_le_of_injective f f.injective
  rw [(H.induce (S : Set P)).card_neighborSet_eq_degree x] at hcard
  simpa using hcard

/-- The closed neighborhood of the low-degree vertex has at most `2d+2`
vertices and minimum degree at least `d+1`. -/
lemma exists_small_highMinDegree_induce
    {P : Finset (Finset V)} (H : SimpleGraph P) [DecidableRel H.Adj]
    {d : ℕ}
    (hminDegree : ∀ x : P, d + 1 ≤ H.degree x)
    (hcommon : ∀ x y : P, H.Adj x y →
      d ≤ (commonNeighborFinset H x y).card)
    (hHexact : H.edgeSet.ncard = d * P.card + 1) :
    ∃ S : Finset P,
      S.Nonempty ∧ S.card ≤ 2 * d + 2 ∧
      ∀ x : (S : Set P), d + 1 ≤ (H.induce (S : Set P)).degree x := by
  classical
  obtain ⟨v, hvdegree⟩ := exists_degree_le_twice_density H hHexact
  let S : Finset P := insert v (H.neighborFinset v)
  have hScard : S.card = H.degree v + 1 := by
    change (insert v (H.neighborFinset v)).card = H.degree v + 1
    rw [Finset.card_insert_of_notMem]
    · rw [H.card_neighborFinset_eq_degree]
    · simp
  refine ⟨S, ⟨v, Finset.mem_insert_self v _⟩, by omega, ?_⟩
  intro x
  by_cases hxv : (x : P) = v
  · have hsub : ∀ y ∈ H.neighborFinset x,
        H.Adj x y ∧ y ∈ S := by
      intro y hy
      refine ⟨(H.mem_neighborFinset x y).mp hy, ?_⟩
      change y ∈ insert v (H.neighborFinset v)
      rw [← hxv]
      exact Finset.mem_insert.mpr (Or.inr hy)
    calc
      d + 1 ≤ (H.neighborFinset x).card := by
        simpa only [H.card_neighborFinset_eq_degree] using hminDegree x
      _ ≤ (H.induce (S : Set P)).degree x :=
        card_le_degree_induce_of_subset H S (H.neighborFinset x) x hsub
  · have hxN : (x : P) ∈ H.neighborFinset v := by
      have hxS := x.2
      change (x : P) ∈ insert v (H.neighborFinset v) at hxS
      exact (Finset.mem_insert.mp hxS).resolve_left hxv
    have hvx : H.Adj v x := (H.mem_neighborFinset v x).mp hxN
    let C : Finset P := insert v (commonNeighborFinset H v x)
    have hvnotC : v ∉ commonNeighborFinset H v x := by
      simp [commonNeighborFinset]
    have hCcard : C.card = (commonNeighborFinset H v x).card + 1 := by
      change (insert v (commonNeighborFinset H v x)).card = _
      rw [Finset.card_insert_of_notMem hvnotC, Nat.add_comm]
    have hCsub : C ⊆ H.neighborFinset x ∩ S := by
      intro y hy
      change y ∈ insert v (commonNeighborFinset H v x) at hy
      rcases Finset.mem_insert.mp hy with hyv | hy
      · subst y
        exact Finset.mem_inter.mpr ⟨by
          exact (H.mem_neighborFinset x v).mpr hvx.symm, by
          change v ∈ insert v (H.neighborFinset v)
          exact Finset.mem_insert_self v _⟩
      · have hy' := Finset.mem_inter.mp hy
        exact Finset.mem_inter.mpr ⟨hy'.2, by
          change y ∈ insert v (H.neighborFinset v)
          exact Finset.mem_insert.mpr (Or.inr hy'.1)⟩
    calc
      d + 1 ≤ (commonNeighborFinset H v x).card + 1 :=
        Nat.add_le_add_right (hcommon v x hvx) 1
      _ = C.card := hCcard.symm
      _ ≤ (H.induce (S : Set P)).degree x := by
        apply card_le_degree_induce_of_subset H S C x
        intro y hy
        have hy' := Finset.mem_inter.mp (hCsub hy)
        exact ⟨(H.mem_neighborFinset x y).mp hy'.1, hy'.2⟩

/-! ### The linked minor model supplied by Thomas--Wollan -/

/-- A connected-bag minor model containing a `k`-linked graph.  The map into
the quotient is only required to be an injective homomorphism: extra quotient
edges are harmless. -/
structure LinkedMinorModel (G : SimpleGraph V) (k : ℕ) where
  P : Finset (Finset V)
  packing : IsConnectedPacking G P
  W : Type u
  fintypeW : Fintype W
  K : SimpleGraph W
  map : K →g quotientGraph G P
  map_injective : Function.Injective map
  enough_vertices : 2 * k ≤ Fintype.card W
  linked : Erdos718.IsKLinked K k

attribute [instance] LinkedMinorModel.fintypeW

/-- More than `(8k-1)|V|` edges force a connected-bag minor containing a
`k`-linked graph.  This is the contraction-minimal form of Thomas--Wollan's
Corollary 1.2. -/
theorem exists_linkedMinorModel_of_dense
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hV : Nonempty V)
    (hE : (8 * k - 1) * Fintype.card V < G.edgeFinset.card) :
    Nonempty (LinkedMinorModel G k) := by
  classical
  let d := 8 * k - 1
  obtain ⟨P, hPdense, hmin⟩ :=
    exists_minimal_densePacking (G := G) (d := d) hE
  obtain ⟨H, hH, hHexact⟩ :=
    exists_exactEdgeGraph (G := G) hPdense.2
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hdegree : ∀ A : P, d + 1 ≤ H.degree A :=
    minimalDense_exact_minDegree hPdense.1 hmin H hH hHexact
  have hcommon : ∀ A B : P, H.Adj A B →
      d ≤ (commonNeighborFinset H A B).card :=
    minimalDense_exact_commonNeighbors hPdense.1 hmin H hH hHexact
  obtain ⟨S, hSnonempty, hScard, hSdegree⟩ :=
    exists_small_highMinDegree_induce H hdegree hcommon hHexact
  have hcard16 : Fintype.card (S : Set P) ≤ 16 * k := by
    have hcardS : Fintype.card (S : Set P) = S.card := by simp
    rw [hcardS]
    dsimp [d] at hScard
    omega
  have hdegree8 : ∀ x : (S : Set P),
      8 * k ≤ (H.induce (S : Set P)).degree x := by
    intro x
    have hx := hSdegree x
    dsimp [d] at hx
    omega
  have hSnonemptyType : Nonempty (S : Set P) := by
    obtain ⟨x, hx⟩ := hSnonempty
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨M⟩ := ThomasWollan.exists_kLinkedSubgraph_of_minDegree_card
    (H.induce (S : Set P)) k hk hSnonemptyType (by omega) hdegree8
  let incS : H.induce (S : Set P) →g H :=
    (SimpleGraph.Embedding.induce (S : Set P)).toHom
  let map : M.H →g quotientGraph G P :=
    (SimpleGraph.Hom.ofLE hH).comp (incS.comp M.inclusion.toHom)
  have hmapInjective : Function.Injective map := by
    intro x y hxy
    apply M.inclusion.injective
    apply Subtype.ext
    exact hxy
  exact ⟨{
    P := P
    packing := hPdense.1
    W := M.W
    fintypeW := M.fintypeW
    K := M.H
    map := map
    map_injective := hmapInjective
    enough_vertices := M.enough_vertices
    linked := M.linked
  }⟩

end DenseMinor
end Erdos717
