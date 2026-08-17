import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Erdős Problem 915

The phrase “disjoint paths” in the original problem is ambiguous.  For internally
vertex-disjoint paths the Bollobás--Erdős assertion is false.  We formalize that literal
negative resolution with an explicit graph on `17 = 1 + 4 * (5 - 1)` vertices and
`41 = 1 + 4 * Nat.choose 5 2` edges.

The mathematical reconstruction, including the positive edge-disjoint result of Mader,
is in `tex/915.tex`.
-/

namespace Erdos915

open scoped Sym2

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- The vertices of a path other than its two endpoints. -/
def internalVertices (p : G.Path u v) : Set V :=
  {x | x ∈ (p : G.Walk u v).support ∧ x ≠ u ∧ x ≠ v}

/-- Some two distinct vertices are joined by `m` distinct paths whose interiors are
pairwise disjoint.  Injectivity is essential: a direct path has empty interior and must
not be counted repeatedly. -/
def HasMInternallyVertexDisjointPaths (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧ ∃ paths : Fin m → G.Path u v,
    Function.Injective paths ∧
      Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i))

/-- The internally vertex-disjoint reading of Problem 915, quantified over every finite
simple graph with the stated vertex and edge counts. -/
def Erdos915VertexClaim : Prop :=
  ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = 1 + n * (m - 1) →
        G.edgeSet.ncard = 1 + n * Nat.choose m 2 →
          HasMInternallyVertexDisjointPaths G m

private lemma card_le_degree_of_disjoint_paths [Fintype V] [DecidableRel G.Adj]
    {m : ℕ} (huv : u ≠ v)
    (paths : Fin m → G.Path u v) (hinj : Function.Injective paths)
    (hdisj : Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i))) :
    m ≤ G.degree u := by
  classical
  let first : Fin m → G.neighborSet u := fun i ↦
    ⟨(paths i : G.Walk u v).snd,
      (paths i : G.Walk u v).adj_snd (SimpleGraph.Walk.not_nil_of_ne huv)⟩
  have hfirst : Function.Injective first := by
    intro i j hij
    have hsnd : (paths i : G.Walk u v).snd = (paths j : G.Walk u v).snd :=
      congrArg Subtype.val hij
    by_cases hv : (paths i : G.Walk u v).snd = v
    · have hiEdge : s(u, v) ∈ (paths i : G.Walk u v).edges := by
        simpa [hv] using
          (paths i : G.Walk u v).mk_start_snd_mem_edges
            (SimpleGraph.Walk.not_nil_of_ne huv)
      have hjEdge : s(u, v) ∈ (paths j : G.Walk u v).edges := by
        simpa [← hsnd, hv] using
          (paths j : G.Walk u v).mk_start_snd_mem_edges
            (SimpleGraph.Walk.not_nil_of_ne huv)
      have hiLen : (paths i : G.Walk u v).length = 1 :=
        (paths i).property.length_eq_one_of_mem_edges hiEdge
      have hjLen : (paths j : G.Walk u v).length = 1 :=
        (paths j).property.length_eq_one_of_mem_edges hjEdge
      apply hinj
      apply Subtype.ext
      exact SimpleGraph.Walk.eq_of_length_le_one (by omega) (by omega)
    · have hiAdj : G.Adj u (paths i : G.Walk u v).snd :=
        (paths i : G.Walk u v).adj_snd (SimpleGraph.Walk.not_nil_of_ne huv)
      have hiInt : (paths i : G.Walk u v).snd ∈ internalVertices (paths i) := by
        refine ⟨?_, hiAdj.ne.symm, hv⟩
        exact List.mem_of_mem_tail
          ((paths i : G.Walk u v).snd_mem_tail_support
            (SimpleGraph.Walk.not_nil_of_ne huv))
      have hjInt : (paths i : G.Walk u v).snd ∈ internalVertices (paths j) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hsnd]
          exact List.mem_of_mem_tail
            ((paths j : G.Walk u v).snd_mem_tail_support
              (SimpleGraph.Walk.not_nil_of_ne huv))
        · exact hiAdj.ne.symm
        · exact hv
      exact hdisj.elim_set (Set.mem_univ i) (Set.mem_univ j)
        (paths i : G.Walk u v).snd hiInt hjInt
  rw [← G.card_neighborSet_eq_degree]
  simpa using Fintype.card_le_of_injective first hfirst

@[simp] private lemma internalVertices_reverse (p : G.Path u v) :
    internalVertices p.reverse = internalVertices p := by
  ext x
  simp [internalVertices, and_comm]

private lemma card_le_degree_end_of_disjoint_paths [Fintype V] [DecidableRel G.Adj]
    {m : ℕ} (huv : u ≠ v) (paths : Fin m → G.Path u v)
    (hinj : Function.Injective paths)
    (hdisj : Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i))) :
    m ≤ G.degree v := by
  let reversePaths : Fin m → G.Path v u := fun i ↦ (paths i).reverse
  have hreverse : Function.Injective reversePaths := by
    intro i j hij
    apply hinj
    apply Subtype.ext
    exact SimpleGraph.Walk.reverse_injective (congrArg Subtype.val hij)
  have hreverseDisjoint :
      Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (reversePaths i)) := by
    simpa [reversePaths] using hdisj
  exact card_le_degree_of_disjoint_paths huv.symm reversePaths hreverse hreverseDisjoint

private lemma walk_side_eq_of_avoids (S : Set V) (direct : Sym2 V) (side : V → Bool)
    (hcross : ∀ ⦃x y : V⦄, G.Adj x y → x ∉ S → y ∉ S →
      s(x, y) ≠ direct → side x = side y) {a b : V} (p : G.Walk a b)
    (havoid : ∀ x ∈ p.support, x ∉ S) (hdirect : direct ∉ p.edges) :
    side a = side b := by
  induction p with
  | nil => rfl
  | @cons a c b hac p ih =>
      have haS : a ∉ S := havoid a (by simp)
      have hcS : c ∉ S := havoid c (by simp)
      have hhead : s(a, c) ≠ direct := by
        intro h
        apply hdirect
        simp [SimpleGraph.Walk.edges_cons, h]
      have htailAvoid : ∀ x ∈ p.support, x ∉ S := by
        intro x hx
        exact havoid x (by simp [hx])
      have htailDirect : direct ∉ p.edges := by
        intro h
        exact hdirect (by simp [SimpleGraph.Walk.edges_cons, h])
      exact (hcross hac haS hcS hhead).trans (ih htailAvoid htailDirect)

private lemma path_eq_singleton_or_hits_separator (huv : G.Adj u v) (S : Set V)
    (side : V → Bool) (huS : u ∉ S) (hvS : v ∉ S) (hside : side u ≠ side v)
    (hcross : ∀ ⦃x y : V⦄, G.Adj x y → x ∉ S → y ∉ S →
      s(x, y) ≠ s(u, v) → side x = side y) (p : G.Path u v) :
    p = SimpleGraph.Path.singleton huv ∨
      ∃ x, x ∈ S ∧ x ∈ internalVertices p := by
  by_cases hedge : s(u, v) ∈ (p : G.Walk u v).edges
  · left
    apply Subtype.ext
    simpa [SimpleGraph.Path.singleton] using
      p.property.eq_adj_toWalk_of_mem_edges hedge
  · right
    by_contra hhit
    have havoid : ∀ x ∈ (p : G.Walk u v).support, x ∉ S := by
      intro x hx hxS
      by_cases hxu : x = u
      · exact huS (hxu ▸ hxS)
      by_cases hxv : x = v
      · exact hvS (hxv ▸ hxS)
      exact hhit ⟨x, hxS, hx, hxu, hxv⟩
    exact hside (walk_side_eq_of_avoids S s(u, v) side hcross
      (p : G.Walk u v) havoid hedge)

private lemma not_five_disjoint_paths_of_three_separator (huv : G.Adj u v)
    (S : Finset V) (hcard : S.card = 3)
    (hcover : ∀ p : G.Path u v,
      p = SimpleGraph.Path.singleton huv ∨
        ∃ x, x ∈ S ∧ x ∈ internalVertices p) :
    ¬ ∃ paths : Fin 5 → G.Path u v,
      Function.Injective paths ∧
        Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i)) := by
  classical
  rintro ⟨paths, hinj, hdisj⟩
  have hhit (i : Fin 5) (hi : paths i ≠ SimpleGraph.Path.singleton huv) :
      ∃ x, x ∈ S ∧ x ∈ internalVertices (paths i) :=
    (hcover (paths i)).resolve_left hi
  let hit (i : Fin 5) (hi : paths i ≠ SimpleGraph.Path.singleton huv) :
      {x // x ∈ S} :=
    ⟨Classical.choose (hhit i hi), (Classical.choose_spec (hhit i hi)).1⟩
  have hit_internal (i : Fin 5) (hi : paths i ≠ SimpleGraph.Path.singleton huv) :
      (hit i hi : V) ∈ internalVertices (paths i) :=
    (Classical.choose_spec (hhit i hi)).2
  let slot : Fin 5 → Option {x // x ∈ S} := fun i ↦
    if hi : paths i = SimpleGraph.Path.singleton huv then none
    else some (hit i hi)
  have hslot : Function.Injective slot := by
    intro i j hs
    by_cases hi : paths i = SimpleGraph.Path.singleton huv
    · by_cases hj : paths j = SimpleGraph.Path.singleton huv
      · apply hinj
        exact hi.trans hj.symm
      · exfalso
        simp [slot, hi, hj] at hs
    · by_cases hj : paths j = SimpleGraph.Path.singleton huv
      · exfalso
        simp [slot, hi, hj] at hs
      · have hh : hit i hi = hit j hj := by
          simpa [slot, hi, hj] using hs
        have hv : (hit i hi : V) = (hit j hj : V) := congrArg Subtype.val hh
        exact hdisj.elim_set (Set.mem_univ i) (Set.mem_univ j) (hit i hi : V)
          (hit_internal i hi) (hv ▸ hit_internal j hj)
  have hle := Fintype.card_le_of_injective slot hslot
  simp [hcard] at hle

private def counterEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2),
   (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 13), (0, 14),
   (1, 2), (1, 3), (1, 4), (1, 9), (1, 10), (1, 11), (1, 12),
   (2, 9), (2, 10), (2, 13), (2, 14), (2, 15), (2, 16),
   (3, 5), (3, 8), (4, 6), (4, 7), (5, 6), (5, 7), (6, 8), (7, 8),
   (9, 11), (9, 12), (10, 11), (10, 12), (11, 12),
   (13, 15), (13, 16), (14, 15), (14, 16), (15, 16)]

private def counterRel (x y : Fin 17) : Prop :=
  (x.val, y.val) ∈ counterEdges

private instance counterRel_decidable : DecidableRel counterRel := fun _ _ ↦ by
  unfold counterRel
  infer_instance

/-- The explicit `17`-vertex, `41`-edge counterexample. -/
def counterexample : SimpleGraph (Fin 17) :=
  SimpleGraph.fromRel counterRel

private instance counterexample_adj_decidable : DecidableRel counterexample.Adj := by
  intro x y
  unfold counterexample
  infer_instance

private lemma counterexample_edgeFinset_card : counterexample.edgeFinset.card = 41 := by
  decide

/-- The explicit counterexample has exactly `41` edges. -/
theorem counterexample_edge_count : counterexample.edgeSet.ncard = 41 := by
  rw [Set.ncard_eq_toFinset_card']
  exact counterexample_edgeFinset_card

private lemma counterexample_low_degree (x : Fin 17)
    (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) : counterexample.degree x = 4 := by
  fin_cases x
  · exact (h0 rfl).elim
  · exact (h1 rfl).elim
  · exact (h2 rfl).elim
  all_goals decide

private def separator01 : Finset (Fin 17) := {2, 3, 4}
private def separator12 : Finset (Fin 17) := {0, 9, 10}
private def separator20 : Finset (Fin 17) := {1, 13, 14}

private def side01 (x : Fin 17) : Bool :=
  x = 1 || x = 9 || x = 10 || x = 11 || x = 12

private def side12 (x : Fin 17) : Bool :=
  x = 2 || x = 13 || x = 14 || x = 15 || x = 16

private def side20 (x : Fin 17) : Bool :=
  x = 0 || x = 3 || x = 4 || x = 5 || x = 6 || x = 7 || x = 8

private lemma crossing01 :
    ∀ ⦃x y : Fin 17⦄, counterexample.Adj x y →
      x ∉ (separator01 : Set (Fin 17)) → y ∉ (separator01 : Set (Fin 17)) →
      s(x, y) ≠ s((0 : Fin 17), 1) → side01 x = side01 y := by
  decide

private lemma crossing12 :
    ∀ ⦃x y : Fin 17⦄, counterexample.Adj x y →
      x ∉ (separator12 : Set (Fin 17)) → y ∉ (separator12 : Set (Fin 17)) →
      s(x, y) ≠ s((1 : Fin 17), 2) → side12 x = side12 y := by
  decide

private lemma crossing20 :
    ∀ ⦃x y : Fin 17⦄, counterexample.Adj x y →
      x ∉ (separator20 : Set (Fin 17)) → y ∉ (separator20 : Set (Fin 17)) →
      s(x, y) ≠ s((2 : Fin 17), 0) → side20 x = side20 y := by
  decide

private lemma noFive01 :
    ¬ ∃ paths : Fin 5 → counterexample.Path (0 : Fin 17) 1,
      Function.Injective paths ∧
        Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i)) := by
  let huv : counterexample.Adj (0 : Fin 17) 1 := by decide
  apply not_five_disjoint_paths_of_three_separator huv separator01 (by decide)
  intro p
  exact path_eq_singleton_or_hits_separator huv (separator01 : Set (Fin 17)) side01
    (by decide) (by decide) (by decide) crossing01 p

private lemma noFive12 :
    ¬ ∃ paths : Fin 5 → counterexample.Path (1 : Fin 17) 2,
      Function.Injective paths ∧
        Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i)) := by
  let huv : counterexample.Adj (1 : Fin 17) 2 := by decide
  apply not_five_disjoint_paths_of_three_separator huv separator12 (by decide)
  intro p
  exact path_eq_singleton_or_hits_separator huv (separator12 : Set (Fin 17)) side12
    (by decide) (by decide) (by decide) crossing12 p

private lemma noFive20 :
    ¬ ∃ paths : Fin 5 → counterexample.Path (2 : Fin 17) 0,
      Function.Injective paths ∧
        Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i)) := by
  let huv : counterexample.Adj (2 : Fin 17) 0 := by decide
  apply not_five_disjoint_paths_of_three_separator huv separator20 (by decide)
  intro p
  exact path_eq_singleton_or_hits_separator huv (separator20 : Set (Fin 17)) side20
    (by decide) (by decide) (by decide) crossing20 p

private lemma reverse_disjoint_path_family {m : ℕ} {u v : V}
    (h : ∃ paths : Fin m → G.Path u v,
      Function.Injective paths ∧
        Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i))) :
    ∃ paths : Fin m → G.Path v u,
      Function.Injective paths ∧
        Set.PairwiseDisjoint Set.univ (fun i ↦ internalVertices (paths i)) := by
  rcases h with ⟨paths, hinj, hdisj⟩
  let reversePaths : Fin m → G.Path v u := fun i ↦ (paths i).reverse
  refine ⟨reversePaths, ?_, ?_⟩
  · intro i j hij
    apply hinj
    apply Subtype.ext
    exact SimpleGraph.Walk.reverse_injective (congrArg Subtype.val hij)
  · simpa [reversePaths] using hdisj

/-- The explicit graph contains no pair joined by five internally vertex-disjoint paths. -/
theorem counterexample_has_no_five_paths :
    ¬ HasMInternallyVertexDisjointPaths counterexample 5 := by
  rintro ⟨u, v, huv, paths, hinj, hdisj⟩
  by_cases hu : u = 0 ∨ u = 1 ∨ u = 2
  · by_cases hv : v = 0 ∨ v = 1 ∨ v = 2
    · rcases hu with (rfl | rfl | rfl) <;> rcases hv with (rfl | rfl | rfl)
      · exact huv rfl
      · exact noFive01 ⟨paths, hinj, hdisj⟩
      · exact noFive20 (reverse_disjoint_path_family ⟨paths, hinj, hdisj⟩)
      · exact noFive01 (reverse_disjoint_path_family ⟨paths, hinj, hdisj⟩)
      · exact huv rfl
      · exact noFive12 ⟨paths, hinj, hdisj⟩
      · exact noFive20 ⟨paths, hinj, hdisj⟩
      · exact noFive12 (reverse_disjoint_path_family ⟨paths, hinj, hdisj⟩)
      · exact huv rfl
    · have hdegree : counterexample.degree v = 4 :=
        counterexample_low_degree v (by tauto) (by tauto) (by tauto)
      have hle := card_le_degree_end_of_disjoint_paths huv paths hinj hdisj
      omega
  · have hdegree : counterexample.degree u = 4 :=
      counterexample_low_degree u (by tauto) (by tauto) (by tauto)
    have hle := card_le_degree_of_disjoint_paths huv paths hinj hdisj
    omega

/-- Negative resolution of Erdős Problem 915 for the standard `k`-rail
(internally vertex-disjoint path) interpretation. -/
theorem erdos_915 : ¬ Erdos915VertexClaim := by
  intro hclaim
  apply counterexample_has_no_five_paths
  exact hclaim 5 4 (by omega) (by omega) (Fin 17) counterexample (by decide) (by
      rw [counterexample_edge_count]
      decide)

end Erdos915

#print axioms Erdos915.erdos_915
