import ErdosProblems.Erdos127.BalancedCut
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

open scoped Sym2
open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges of `G` with both endpoints in `U`. -/
def insideEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset ∩ U.sym2

/-- The induced graph on `U`, regarded as a spanning graph on the original
vertex type (all vertices outside `U` are isolated). -/
def insideGraph (G : SimpleGraph V) (U : Finset V) : SimpleGraph V :=
  (G.induce (U : Set V)).spanningCoe

@[simp] lemma insideGraph_adj (G : SimpleGraph V) (U : Finset V) (u v : V) :
    (G.insideGraph U).Adj u v ↔ G.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  constructor
  · rw [insideGraph, SimpleGraph.map_adj]
    rintro ⟨u', v', huv, rfl, rfl⟩
    exact ⟨huv, u'.property, v'.property⟩
  · rintro ⟨huv, hu, hv⟩
    rw [insideGraph, SimpleGraph.map_adj]
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, huv, rfl, rfl⟩

instance insideGraph.instDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : DecidableRel (G.insideGraph U).Adj := fun u v ↦
  decidable_of_iff (G.Adj u v ∧ u ∈ U ∧ v ∈ U) (insideGraph_adj G U u v).symm

theorem edgeFinset_insideGraph_eq_insideEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    (G.insideGraph U).edgeFinset = G.insideEdgeFinset U := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simp [insideGraph_adj, insideEdgeFinset]

@[simp] lemma mem_insideEdgeFinset_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (u v : V) :
    s(u, v) ∈ G.insideEdgeFinset U ↔ G.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  simp [insideEdgeFinset]

/-- Edges internal to `U` which cross the cut `S`. -/
def localCutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) : Finset (Sym2 V) :=
  G.insideEdgeFinset U ∩ G.cutEdgeFinset S

@[simp] lemma mem_localCutEdgeFinset_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) (u v : V) :
    s(u, v) ∈ G.localCutEdgeFinset U S ↔
      G.Adj u v ∧ u ∈ U ∧ v ∈ U ∧ ((u ∈ S) ≠ (v ∈ S)) := by
  simp [localCutEdgeFinset]
  tauto

theorem cutEdgeFinset_insideGraph_eq_localCutEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    (G.insideGraph U).cutEdgeFinset S = G.localCutEdgeFinset U S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simp [insideGraph_adj, localCutEdgeFinset, insideEdgeFinset] <;> tauto

private lemma edgeFinset_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    (G.insideEdgeFinset U ∪ G.cutEdgeFinset U) ∪ G.insideEdgeFinset Uᶜ = G.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_union, mem_insideEdgeFinset_mk, mem_cutEdgeFinset_mk,
        mem_compl, mem_edgeFinset]
      tauto

private lemma inside_disjoint_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : Disjoint (G.insideEdgeFinset U) (G.cutEdgeFinset U) := by
  rw [Finset.disjoint_left]
  intro e heI heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at heI heC
      tauto

private lemma inside_union_cut_disjoint_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    Disjoint (G.insideEdgeFinset U ∪ G.cutEdgeFinset U) (G.insideEdgeFinset Uᶜ) := by
  rw [Finset.disjoint_left]
  intro e he heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at he heC
      tauto

/-- Every edge is uniquely internal to `U`, crosses from `U` to its complement,
or is internal to the complement. -/
theorem card_edgeFinset_eq_inside_add_cut_add_inside_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    #G.edgeFinset =
      #(G.insideEdgeFinset U) + #(G.cutEdgeFinset U) + #(G.insideEdgeFinset Uᶜ) := by
  rw [← edgeFinset_partition G U,
    card_union_of_disjoint (inside_union_cut_disjoint_compl G U),
    card_union_of_disjoint (inside_disjoint_cut G U)]

private lemma cutEdgeFinset_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) :
    (G.localCutEdgeFinset U S ∪
        (G.cutEdgeFinset U ∩ G.cutEdgeFinset S)) ∪
      G.localCutEdgeFinset Uᶜ S = G.cutEdgeFinset S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_union, mem_inter, mem_localCutEdgeFinset_mk,
        mem_cutEdgeFinset_mk, mem_compl]
      tauto

private lemma local_disjoint_cross (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) :
    Disjoint (G.localCutEdgeFinset U S)
      (G.cutEdgeFinset U ∩ G.cutEdgeFinset S) := by
  rw [Finset.disjoint_left]
  intro e heI heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at heI heC
      tauto

private lemma local_union_cross_disjoint_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    Disjoint
      (G.localCutEdgeFinset U S ∪ (G.cutEdgeFinset U ∩ G.cutEdgeFinset S))
      (G.localCutEdgeFinset Uᶜ S) := by
  rw [Finset.disjoint_left]
  intro e he heC
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp at he heC
      tauto

theorem card_cutEdgeFinset_eq_local_add_cross_add_local_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    #(G.cutEdgeFinset S) =
      #(G.localCutEdgeFinset U S) +
        #(G.cutEdgeFinset U ∩ G.cutEdgeFinset S) +
          #(G.localCutEdgeFinset Uᶜ S) := by
  have h := congrArg Finset.card (cutEdgeFinset_partition G U S)
  rw [card_union_of_disjoint (local_union_cross_disjoint_compl G U S),
    card_union_of_disjoint (local_disjoint_cross G U S)] at h
  exact h.symm

private lemma localCutEdgeFinset_union_left
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hT : T ⊆ Uᶜ) :
    G.localCutEdgeFinset U (A ∪ T) = G.localCutEdgeFinset U A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union]
      have hu : u ∈ T → u ∉ U := fun huT ↦ by simpa using hT huT
      have hv : v ∈ T → v ∉ U := fun hvT ↦ by simpa using hT hvT
      tauto

private lemma localCutEdgeFinset_union_right
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) :
    G.localCutEdgeFinset Uᶜ (A ∪ T) = G.localCutEdgeFinset Uᶜ T := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union, mem_compl]
      have hu : u ∈ A → u ∈ U := fun huA ↦ hA huA
      have hv : v ∈ A → v ∈ U := fun hvA ↦ hA hvA
      tauto

private lemma localCutEdgeFinset_union_compl_sdiff_left
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V} :
    G.localCutEdgeFinset U (A ∪ (Uᶜ \ T)) = G.localCutEdgeFinset U A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union, mem_sdiff, mem_compl]
      tauto

private lemma localCutEdgeFinset_union_compl_sdiff_right
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) :
    G.localCutEdgeFinset Uᶜ (A ∪ (Uᶜ \ T)) =
      G.localCutEdgeFinset Uᶜ T := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_localCutEdgeFinset_mk, mem_union, mem_sdiff, mem_compl]
      have hu : u ∈ A → u ∈ U := fun huA ↦ hA huA
      have hv : v ∈ A → v ∈ U := fun hvA ↦ hA hvA
      tauto

private lemma oriented_cross_union
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ T)) ∪
        (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ (Uᶜ \ T))) =
      G.cutEdgeFinset U := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_union, mem_inter, mem_cutEdgeFinset_mk, mem_sdiff, mem_compl]
      have huA : u ∈ A → u ∈ U := fun h ↦ hA h
      have hvA : v ∈ A → v ∈ U := fun h ↦ hA h
      have huT : u ∈ T → u ∉ U := fun hT' ↦ by simpa using hT hT'
      have hvT : v ∈ T → v ∉ U := fun hT' ↦ by simpa using hT hT'
      tauto

private lemma oriented_cross_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    Disjoint
      (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ T))
      (G.cutEdgeFinset U ∩ G.cutEdgeFinset (A ∪ (Uᶜ \ T))) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_inter, mem_cutEdgeFinset_mk, mem_union, mem_sdiff, mem_compl] at he₁ he₂
      have huA : u ∈ A → u ∈ U := fun h ↦ hA h
      have hvA : v ∈ A → v ∈ U := fun h ↦ hA h
      have huT : u ∈ T → u ∉ U := fun hT' ↦ by simpa using hT hT'
      have hvT : v ∈ T → v ∉ U := fun hT' ↦ by simpa using hT hT'
      tauto

/-- Reversing a cut of `Uᶜ` preserves all edges internal to `U` and `Uᶜ`,
while the two orientations partition the `U`--`Uᶜ` edges. -/
theorem card_oriented_cut_add_card_oriented_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    #(G.cutEdgeFinset (A ∪ T)) +
        #(G.cutEdgeFinset (A ∪ (Uᶜ \ T))) =
      2 * #(G.localCutEdgeFinset U A) +
        2 * #(G.localCutEdgeFinset Uᶜ T) + #(G.cutEdgeFinset U) := by
  rw [card_cutEdgeFinset_eq_local_add_cross_add_local_compl G U (A ∪ T),
    card_cutEdgeFinset_eq_local_add_cross_add_local_compl G U (A ∪ (Uᶜ \ T)),
    localCutEdgeFinset_union_left G hT,
    localCutEdgeFinset_union_right G hA,
    localCutEdgeFinset_union_compl_sdiff_left G,
    localCutEdgeFinset_union_compl_sdiff_right G hA]
  have h := congrArg Finset.card (oriented_cross_union G hA hT)
  rw [card_union_of_disjoint (oriented_cross_disjoint G hA hT)] at h
  omega

/-- One of the two orientations captures at least half the `U`--`Uᶜ` edges,
in addition to both prescribed internal cut contributions. -/
theorem exists_oriented_cut_mul_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A T : Finset V}
    (hA : A ⊆ U) (hT : T ⊆ Uᶜ) :
    ∃ S : Finset V,
      (S = A ∪ T ∨ S = A ∪ (Uᶜ \ T)) ∧
        2 * (#(G.localCutEdgeFinset U A) + #(G.localCutEdgeFinset Uᶜ T)) +
            #(G.cutEdgeFinset U) ≤
          2 * #(G.cutEdgeFinset S) := by
  have hsum := card_oriented_cut_add_card_oriented_cut G hA hT
  rcases le_total (#(G.cutEdgeFinset (A ∪ T)))
      (#(G.cutEdgeFinset (A ∪ (Uᶜ \ T)))) with hle | hle
  · refine ⟨A ∪ (Uᶜ \ T), Or.inr rfl, ?_⟩
    omega
  · refine ⟨A ∪ T, Or.inl rfl, ?_⟩
    omega

private lemma image_interedges_eq_localCutEdgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V} (hA : A ⊆ U) :
    (G.interedges A (U \ A)).image (fun p : V × V ↦ s(p.1, p.2)) =
      G.localCutEdgeFinset U A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      constructor
      · intro he
        rcases Finset.mem_image.mp he with ⟨p, hp, hep⟩
        rw [SimpleGraph.mem_interedges_iff] at hp
        rcases hp with ⟨hpA, hpUA, hpAdj⟩
        have hpU : p.1 ∈ U := hA hpA
        have hpU' : p.2 ∈ U := (Finset.mem_sdiff.mp hpUA).1
        have hpnotA : p.2 ∉ A := (Finset.mem_sdiff.mp hpUA).2
        have hpLocal : s(p.1, p.2) ∈ G.localCutEdgeFinset U A := by
          rw [mem_localCutEdgeFinset_mk]
          exact ⟨hpAdj, hpU, hpU', by simp [hpA, hpnotA]⟩
        rwa [hep] at hpLocal
      · intro he
        rw [mem_localCutEdgeFinset_mk] at he
        rcases he with ⟨huv, huU, hvU, hsplit⟩
        by_cases huA : u ∈ A
        · have hvA : v ∉ A := by tauto
          apply Finset.mem_image.mpr
          refine ⟨(u, v), ?_, rfl⟩
          rw [SimpleGraph.mk_mem_interedges_iff]
          exact ⟨huA, Finset.mem_sdiff.mpr ⟨hvU, hvA⟩, huv⟩
        · have hvA : v ∈ A := by tauto
          apply Finset.mem_image.mpr
          refine ⟨(v, u), ?_, by simp⟩
          rw [SimpleGraph.mk_mem_interedges_iff]
          exact ⟨hvA, Finset.mem_sdiff.mpr ⟨huU, huA⟩, (G.adj_comm _ _).mp huv⟩

private lemma sym2OfProd_injOn_interedges
    (G : SimpleGraph V) [DecidableRel G.Adj] (U A : Finset V) :
    Set.InjOn (fun p : V × V ↦ s(p.1, p.2)) (G.interedges A (U \ A)) := by
  intro p hp q hq hpq
  rw [Sym2.mk_eq_mk_iff] at hpq
  rcases hpq with hpq | hpq
  · exact hpq
  · change p ∈ G.interedges A (U \ A) at hp
    change q ∈ G.interedges A (U \ A) at hq
    rw [SimpleGraph.mem_interedges_iff] at hp hq
    exfalso
    have hpA : p.1 ∈ A := hp.1
    have hqnotA : q.2 ∉ A := (Finset.mem_sdiff.mp hq.2.1).2
    have : q.2 ∈ A := by simpa [hpq] using hpA
    exact hqnotA this

/-- A cut internal to `U` is counted by the ordered edges from its `A` side to
its `U \ A` side; disjointness makes the unordered-pair quotient injective. -/
theorem card_localCutEdgeFinset_eq_card_interedges
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V} (hA : A ⊆ U) :
    #(G.localCutEdgeFinset U A) = #(G.interedges A (U \ A)) := by
  rw [← image_interedges_eq_localCutEdgeFinset G hA,
    Finset.card_image_of_injOn (sym2OfProd_injOn_interedges G U A)]

private lemma interedges_eq_product_of_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V}
    (hA : A ⊆ U) (hU : G.IsClique (U : Set V)) :
    G.interedges A (U \ A) = A ×ˢ (U \ A) := by
  ext p
  rw [SimpleGraph.mem_interedges_iff, Finset.mem_product]
  constructor
  · rintro ⟨hpA, hpUA, -⟩
    exact ⟨hpA, hpUA⟩
  · rintro ⟨hpA, hpUA⟩
    refine ⟨hpA, hpUA, ?_⟩
    apply hU
    · exact hA hpA
    · exact (Finset.mem_sdiff.mp hpUA).1
    · intro heq
      exact (Finset.mem_sdiff.mp hpUA).2 (heq ▸ hpA)

/-- In a clique, an internal split into parts of sizes `a` and `b` cuts
exactly `a*b` edges. -/
theorem card_localCutEdgeFinset_of_isClique
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V}
    (hA : A ⊆ U) (hU : G.IsClique (U : Set V)) :
    #(G.localCutEdgeFinset U A) = #A * #(U \ A) := by
  rw [card_localCutEdgeFinset_eq_card_interedges G hA,
    interedges_eq_product_of_isClique G hA hU, Finset.card_product]

/-- An even clique of size `2*r` admits an equal split cutting exactly `r^2`
of its internal edges (`u^2/4`, stated without division). -/
theorem exists_half_clique_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] {U : Finset V} (r : ℕ)
    (hcard : #U = 2 * r) (hU : G.IsClique (U : Set V)) :
    ∃ A ⊆ U, #A = r ∧ #(U \ A) = r ∧
      #(G.localCutEdgeFinset U A) = r * r := by
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq (s := U) (n := r) (by omega)
  refine ⟨A, hA, hAcard, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hA, hcard, hAcard]
    omega
  · rw [card_localCutEdgeFinset_of_isClique G hA hU, hAcard,
      Finset.card_sdiff_of_subset hA, hcard, hAcard]
    have hr : 2 * r - r = r := by omega
    rw [hr]

/-- Combined division-free form used in the clique-composition argument. -/
theorem exists_cut_of_even_clique_and_compl_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] {U T : Finset V} (r : ℕ)
    (hcard : #U = 2 * r) (hU : G.IsClique (U : Set V)) (hT : T ⊆ Uᶜ) :
    ∃ A S : Finset V,
      A ⊆ U ∧ #A = r ∧ #(U \ A) = r ∧
        #(G.localCutEdgeFinset U A) = r * r ∧
        (S = A ∪ T ∨ S = A ∪ (Uᶜ \ T)) ∧
        2 * (r * r + #(G.localCutEdgeFinset Uᶜ T)) + #(G.cutEdgeFinset U) ≤
          2 * #(G.cutEdgeFinset S) := by
  obtain ⟨A, hA, hAcard, hAcocard, hAlocal⟩ := exists_half_clique_cut G r hcard hU
  obtain ⟨S, hS, hbound⟩ := exists_oriented_cut_mul_bound G hA hT
  refine ⟨A, S, hA, hAcard, hAcocard, hAlocal, hS, ?_⟩
  rwa [hAlocal] at hbound

end SimpleGraph
