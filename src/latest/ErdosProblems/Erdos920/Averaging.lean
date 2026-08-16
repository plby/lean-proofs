import Mathlib
import Util.Ramsey
import ErdosProblems.Erdos202

/-!
# Finite averaging lemmas for Erdős Problem 920

This file contains the two elementary reductions used as Lemmas 2.3 and 2.4
in Bradač's proof of the off-diagonal Ramsey lower bound.

* A linear order turns the forward arcs of a digraph into an undirected graph.
  A clique in this graph gives a transitive tournament in the digraph, while
  an independent set, read in increasing order, gives a forward-independent
  tuple.
* Bernoulli sampling of the vertices of a clique-free graph, followed by
  deleting one vertex from every surviving independent set of a prescribed
  size, produces a smaller graph with neither a large clique nor a large
  independent set.

Everything below is finite and deterministic.  The Bernoulli argument is
expressed as an explicit weighted sum over the powerset.
-/

open scoped BigOperators

namespace Erdos920

section OrderedDigraph

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A tuple is forward independent in `D` if none of its earlier entries has
an arc to a later entry.  Repeated entries are allowed, as in Bradač's count. -/
def ForwardIndependent (D : V → V → Prop) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ ⦃i j : Fin k⦄, i < j → ¬ D (x i) (x j)

/-- The finite set of forward-independent `k`-tuples. -/
noncomputable def forwardIndependentFinset (D : V → V → Prop) (k : ℕ) :
    Finset (Fin k → V) := by
  classical
  exact Finset.univ.filter (ForwardIndependent D)

@[simp]
lemma mem_forwardIndependentFinset {D : V → V → Prop} {k : ℕ} {x : Fin k → V} :
    x ∈ forwardIndependentFinset D k ↔ ForwardIndependent D x := by
  classical
  simp [forwardIndependentFinset]

/-- `D` contains no (labelled) transitive tournament on `s` distinct vertices. -/
def TransitiveTournamentFree (D : V → V → Prop) (s : ℕ) : Prop :=
  ∀ x : Fin s → V, Function.Injective x →
    ¬ ∀ ⦃i j : Fin s⦄, i < j → D (x i) (x j)

/-- Keep precisely the arcs that point forwards after applying the permutation
`π`, and forget their orientation. -/
def forwardGraph (D : V → V → Prop) (π : Equiv.Perm V) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun u v => π u < π v ∧ D u v

/-- The forward graph is finite, hence its adjacency relation is decidable.
This noncomputable instance lets counting statements use arbitrary
proposition-valued digraph relations. -/
noncomputable instance instDecidableRelForwardGraph (D : V → V → Prop)
    (π : Equiv.Perm V) : DecidableRel (forwardGraph D π).Adj :=
  Classical.decRel _

lemma forwardGraph_adj_iff {D : V → V → Prop} {π : Equiv.Perm V} {u v : V} :
    (forwardGraph D π).Adj u v ↔
      u ≠ v ∧ ((π u < π v ∧ D u v) ∨ (π v < π u ∧ D v u)) :=
  Iff.rfl

/-- Reading an independent set in the order induced by `π` produces a
forward-independent tuple. -/
noncomputable def orderedTuple (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : Fin k → V :=
  fun i => π.symm ((S.map π.toEmbedding).orderEmbOfFin (by simpa using hS) i)

lemma orderedTuple_injective (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : Function.Injective (orderedTuple π S hS) := by
  intro i j hij
  apply (S.map π.toEmbedding).orderEmbOfFin (by simpa using hS) |>.injective
  simpa [orderedTuple] using congrArg π hij

lemma orderedTuple_mem (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) (i : Fin k) : orderedTuple π S hS i ∈ S := by
  have hi := (S.map π.toEmbedding).orderEmbOfFin_mem (by simpa using hS) i
  simpa [orderedTuple] using hi

@[simp]
lemma range_orderedTuple (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : Set.range (orderedTuple π S hS) = (S : Set V) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact orderedTuple_mem π S hS i
  · intro hv
    let y : S.map π.toEmbedding := ⟨π v, by simpa using hv⟩
    obtain ⟨i, hi⟩ :=
      ((S.map π.toEmbedding).orderIsoOfFin (by simpa using hS)).surjective y
    refine ⟨i, ?_⟩
    apply π.injective
    simpa [orderedTuple, y] using congrArg Subtype.val hi

lemma orderedTuple_strictMono_after (π : Equiv.Perm V) (S : Finset V) {k : ℕ}
    (hS : S.card = k) : StrictMono (fun i => π (orderedTuple π S hS i)) := by
  simpa [orderedTuple] using
    (S.map π.toEmbedding).orderEmbOfFin (by simpa using hS) |>.strictMono

/-- An increasing clique in the forward graph is a transitive tournament in
the original digraph. -/
lemma forwardGraph_cliqueFree {D : V → V → Prop} {s : ℕ}
    (hD : TransitiveTournamentFree D s) (π : Equiv.Perm V) :
    (forwardGraph D π).CliqueFree s := by
  intro C hC
  let x : Fin s → V := orderedTuple π C hC.card_eq
  have hxinj : Function.Injective x := orderedTuple_injective π C hC.card_eq
  apply hD x hxinj
  intro i j hij
  have hxi : x i ∈ C := orderedTuple_mem π C hC.card_eq i
  have hxj : x j ∈ C := orderedTuple_mem π C hC.card_eq j
  have hn : x i ≠ x j := fun h => hij.ne (hxinj h)
  have hadj : (forwardGraph D π).Adj (x i) (x j) :=
    hC.isClique hxi hxj hn
  rcases (forwardGraph_adj_iff.mp hadj).2 with h | h
  · exact h.2
  · have hlt := orderedTuple_strictMono_after π C hC.card_eq hij
    exact (lt_asymm hlt h.1).elim

lemma orderedTuple_forwardIndependent {D : V → V → Prop} (π : Equiv.Perm V)
    (S : Finset V) {k : ℕ} (hS : S.card = k)
    (hI : (forwardGraph D π).IsIndepSet (S : Set V)) :
    ForwardIndependent D (orderedTuple π S hS) := by
  intro i j hij hDij
  have hlt : π (orderedTuple π S hS i) < π (orderedTuple π S hS j) :=
    orderedTuple_strictMono_after π S hS hij
  have hn : orderedTuple π S hS i ≠ orderedTuple π S hS j :=
    fun h => hij.ne (orderedTuple_injective π S hS h)
  exact hI (orderedTuple_mem π S hS i) (orderedTuple_mem π S hS j)
    hn ((forwardGraph_adj_iff).2 ⟨hn, Or.inl ⟨hlt, hDij⟩⟩)

/-- For one fixed ordering, independent `k`-sets inject into the
forward-independent `k`-tuples.  The sharper factorial saving is obtained by
averaging this construction over all permutations. -/
lemma indepSetFinset_card_forwardGraph_le {D : V → V → Prop}
    (π : Equiv.Perm V)
    (k : ℕ) :
    ((forwardGraph D π).indepSetFinset k).card ≤
      (forwardIndependentFinset D k).card := by
  classical
  let A := (forwardGraph D π).indepSetFinset k
  let f : {S // S ∈ A} → (Fin k → V) := fun S =>
    orderedTuple π S.1 <| (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq
  rw [← Finset.card_attach (s := A)]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro S hS
    have hNS := SimpleGraph.mem_indepSetFinset_iff.mp S.2
    exact mem_forwardIndependentFinset.mpr
      (orderedTuple_forwardIndependent π S.1 hNS.card_eq hNS.isIndepSet)
  · intro S hS T hT hST
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← range_orderedTuple π S.1
          (SimpleGraph.mem_indepSetFinset_iff.mp S.2).card_eq,
      ← range_orderedTuple π T.1
          (SimpleGraph.mem_indepSetFinset_iff.mp T.2).card_eq]
    exact congrArg Set.range hST

end OrderedDigraph

section Deletion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The independent `k`-sets of `G` which survive inside `A`. -/
def survivingIndepSetFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Finset (Finset V) :=
  (G.indepSetFinset k).filter (· ⊆ A)

@[simp]
lemma mem_survivingIndepSetFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {A T : Finset V} :
    T ∈ survivingIndepSetFinset G k A ↔ G.IsNIndepSet k T ∧ T ⊆ A := by
  simp [survivingIndepSetFinset, SimpleGraph.mem_indepSetFinset_iff]

/-- Relative deletion lemma.  Starting from a sampled vertex set `A`, remove
one vertex from every independent `k`-set contained in `A`. -/
lemma exists_induced_indepSetFree_subgraph_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ U : Finset V, U ⊆ A ∧
      A.card - (survivingIndepSetFinset G k A).card ≤ U.card ∧
        (G.induce (U : Set V)).IndepSetFree k := by
  classical
  let B : Finset (Finset V) := survivingIndepSetFinset G k A
  let pick : {T // T ∈ B} → V := fun T =>
    Classical.choose <| by
      have hT : G.IsNIndepSet k T.1 :=
        (mem_survivingIndepSetFinset.mp (show T.1 ∈ B from T.2)).1
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hT : G.IsNIndepSet k T.1 :=
        (mem_survivingIndepSetFinset.mp (show T.1 ∈ B from T.2)).1
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  let deleted : Finset V := B.attach.image pick
  let U : Finset V := A \ deleted
  have hdeletedA : deleted ⊆ A := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    have hTA : T.1 ⊆ A :=
      (mem_survivingIndepSetFinset.mp (show T.1 ∈ B from T.2)).2
    exact hTA (hpick_mem T)
  have hUsub : U ⊆ A := Finset.sdiff_subset
  have hUcard : A.card - B.card ≤ U.card := by
    have hd : deleted.card ≤ B.card := by
      simpa [deleted] using Finset.card_image_le (s := B.attach) (f := pick)
    calc
      A.card - B.card ≤ A.card - deleted.card := Nat.sub_le_sub_left hd _
      _ = U.card := by
        symm
        simpa [U] using Finset.card_sdiff_of_subset hdeletedA
  have hhit : ∀ {T : Finset V}, T ∈ B → T ⊆ U → False := by
    intro T hT hTU
    let TT : {T // T ∈ B} := ⟨T, hT⟩
    have hpdel : pick TT ∈ deleted :=
      Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
    have hpU : pick TT ∈ U := hTU (hpick_mem TT)
    exact (Finset.mem_sdiff.mp hpU).2 hpdel
  have hfree : (G.induce (U : Set V)).IndepSetFree k := by
    intro T hT
    let T' : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
    have hT' : G.IsNIndepSet k T' := by
      have hTi :
          (((⊤ : SimpleGraph.Subgraph G).induce (U : Set V)).coe).IsNIndepSet k T := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hT
      simpa [T'] using
        (SimpleGraph.isNIndepSet_induce (G := G) (F := (U : Set V))
          (s := T) (n := k)).mp hTi
    have hT'U : T' ⊆ U := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact x.property
    have hT'A : T' ⊆ A := hT'U.trans hUsub
    exact hhit (by exact mem_survivingIndepSetFinset.mpr ⟨hT', hT'A⟩) hT'U
  exact ⟨U, hUsub, by simpa [B] using hUcard, hfree⟩

/-- Delete one chosen vertex from every independent `k`-set.  The remaining
induced graph has no independent `k`-set and loses at most one vertex for each
set in the original graph. -/
lemma exists_induced_indepSetFree_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ U : Finset V,
      Fintype.card V - (G.indepSetFinset k).card ≤ U.card ∧
        (G.induce (U : Set V)).IndepSetFree k := by
  classical
  let B : Finset (Finset V) := G.indepSetFinset k
  let pick : {T // T ∈ B} → V := fun T =>
    Classical.choose <| by
      have hT : G.IsNIndepSet k T.1 := by
        simpa [B] using (SimpleGraph.mem_indepSetFinset_iff.mp T.2)
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hT : G.IsNIndepSet k T.1 := by
        simpa [B] using (SimpleGraph.mem_indepSetFinset_iff.mp T.2)
      exact Finset.card_pos.mp (hT.card_eq ▸ hk)
  let deleted : Finset V := B.attach.image pick
  let U : Finset V := Finset.univ \ deleted
  have hUcard : Fintype.card V - B.card ≤ U.card := by
    have hd : deleted.card ≤ B.card := by
      simpa [deleted] using Finset.card_image_le (s := B.attach) (f := pick)
    calc
      Fintype.card V - B.card ≤ Fintype.card V - deleted.card :=
        Nat.sub_le_sub_left hd _
      _ = U.card := by
        symm
        simp [U, Finset.card_sdiff_of_subset, Finset.subset_univ]
  have hhit : ∀ {T : Finset V}, T ∈ B → T ⊆ U → False := by
    intro T hT hTU
    let TT : {T // T ∈ B} := ⟨T, hT⟩
    have hpdel : pick TT ∈ deleted :=
      Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
    have hpU : pick TT ∈ U := hTU (hpick_mem TT)
    have hpnot : pick TT ∉ deleted := by
      exact (show pick TT ∈ Finset.univ ∧ pick TT ∉ deleted by simpa [U] using hpU).2
    exact hpnot hpdel
  have hfree : (G.induce (U : Set V)).IndepSetFree k := by
    intro T hT
    let T' : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
    have hT' : G.IsNIndepSet k T' := by
      have hTi :
          (((⊤ : SimpleGraph.Subgraph G).induce (U : Set V)).coe).IsNIndepSet k T := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hT
      simpa [T'] using
        (SimpleGraph.isNIndepSet_induce (G := G) (F := (U : Set V))
          (s := T) (n := k)).mp hTi
    have hT'U : T' ⊆ U := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact x.property
    exact hhit (by simpa [B] using hT') hT'U
  exact ⟨U, by simpa [B] using hUcard, hfree⟩

/-- The deletion lemma transported to a graph on `Fin n`; clique-freeness is
preserved by taking the induced subgraph. -/
lemma exists_ramsey_graph_of_indepSet_count
    (G : SimpleGraph V) [DecidableRel G.Adj] {s k : ℕ} (hk : 1 ≤ k)
    (hcf : G.CliqueFree s) :
    ∃ n : ℕ,
      Fintype.card V - (G.indepSetFinset k).card ≤ n ∧
        ∃ H : SimpleGraph (Fin n), H.CliqueFree s ∧ H.IndepSetFree k := by
  classical
  obtain ⟨U, hUcard, hUfree⟩ := exists_induced_indepSetFree_subgraph G hk
  let G' : SimpleGraph {x // x ∈ (U : Set V)} := G.induce (U : Set V)
  have hG'cf : G'.CliqueFree s :=
    hcf.comap (SimpleGraph.Embedding.induce (G := G) (s := (U : Set V))).isContained
  let n := U.card
  have hcard : Fintype.card {x // x ∈ (U : Set V)} = n := by simp [n]
  let H : SimpleGraph (Fin n) := G'.overFin hcard
  have hi : G' ≃g H := SimpleGraph.overFinIso (G := G') hcard
  refine ⟨n, hUcard, H, ?_, ?_⟩
  · exact (SimpleGraph.Iso.cliqueFree_iff (n := s) (e := hi)).mp hG'cf
  · exact (SimpleGraph.Iso.indepSetFree_iff (n := k) (e := hi)).mp hUfree

end Deletion

section Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

open Erdos202.ParkPham

/-- In the finite Bernoulli distribution on subsets of `X`, the total weight
of samples containing a fixed `T ⊆ X` is `p ^ |T|`. -/
lemma sum_bernoulliMass_indicator_superset (X T : Finset V) (hTX : T ⊆ X)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) = p ^ T.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) =
        muP X (upClosureIn X {T}) p := by
          rw [upClosureIn_singleton X T hTX]
          simp only [muP, Finset.mem_filter, Finset.mem_powerset]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro W hW
          simp [Finset.mem_powerset.mp hW]
    _ = p ^ T.card := muP_upClosure_single X T hTX hp0 hp1

/-- Expected number of members of a uniform-cardinality family `A` which are
contained in a Bernoulli sample.  This is the finite-sum form of
`E Y = p^k |A|`. -/
lemma sum_bernoulliMass_contained_count (X : Finset V) (A : Finset (Finset V))
    {k : ℕ} (hAX : ∀ T ∈ A, T ⊆ X) (hcard : ∀ T ∈ A, T.card = k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
      p ^ k * A.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ T ∈ A, bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [← Finset.mul_sum, Finset.sum_boole]
    _ = ∑ T ∈ A,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ A, p ^ T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          exact sum_bernoulliMass_indicator_superset X T (hAX T hT) hp0 hp1
    _ = p ^ k * A.card := by
          rw [Finset.sum_congr rfl (fun T hT => by rw [hcard T hT])]
          simp [mul_comm]

/-- The expected cardinality of a Bernoulli sample of `X` is `p |X|`. -/
lemma sum_bernoulliMass_card (X : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
      p * X.card := by
  calc
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ v ∈ X, bernoulliMass X W p * (if v ∈ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            have hWX : W ⊆ X := Finset.mem_powerset.mp hW
            have hfilter : X.filter (· ∈ W) = W := by
              ext v
              simp only [Finset.mem_filter]
              constructor
              · exact And.right
              · intro hv
                exact ⟨hWX hv, hv⟩
            rw [show (W.card : ℝ) =
                ∑ v ∈ X, if v ∈ W then (1 : ℝ) else 0 by
              rw [Finset.sum_boole]
              rw [hfilter]]
            rw [Finset.mul_sum]
    _ = ∑ v ∈ X,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if ({v} : Finset V) ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro W hW
          simp
    _ = ∑ _v ∈ X, p := by
          apply Finset.sum_congr rfl
          intro v hv
          simpa using sum_bernoulliMass_indicator_superset X ({v} : Finset V)
            (by simpa using hv) hp0 hp1
    _ = p * X.card := by simp [mul_comm]

end Sampling

end Erdos920
