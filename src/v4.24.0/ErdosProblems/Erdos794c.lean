/-
We construct a 3-uniform hypergraph on $3n$ vertices with at least $n^3+1$ edges that contains no subgraph on 4 vertices with 3 edges and no subgraph on 5 vertices with 7 edges.
The construction consists of a complete tripartite hypergraph plus one extra edge inside one of the parts.
We prove that this construction satisfies all the required properties.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Basic definitions for hypergraphs: uniformity, induced edges, and dense subgraphs.
-/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

def is_uniform {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H, e.card = k

def induced_edges {V : Type*} [DecidableEq V] (H : Hypergraph V) (S : Finset V) : Finset (Finset V) :=
  H.filter (λ e => e ⊆ S)

def has_dense_subgraph {V : Type*} [DecidableEq V] (H : Hypergraph V) (v_count e_count : ℕ) : Prop :=
  ∃ S : Finset V, S.card = v_count ∧ e_count ≤ (induced_edges H S).card

/-
The edges of the tripartite part of the construction. It consists of all triples with one vertex in each part.
-/
def tripartite_edges (n : ℕ) : Hypergraph (Fin 3 × Fin n) :=
  let s := (Finset.univ : Finset (Fin n))
  (s.product (s.product s)).image (λ x => {(0, x.1), (1, x.2.1), (2, x.2.2)})

/-
The extra edge added to the construction. It consists of a single edge within the first part, using the first three vertices. This is only added if $n \ge 3$.
-/
def extra_edges (n : ℕ) : Hypergraph (Fin 3 × Fin n) :=
  if h : 3 ≤ n then
    let v0 : Fin 3 × Fin n := (0, ⟨0, by omega⟩)
    let v1 : Fin 3 × Fin n := (0, ⟨1, by omega⟩)
    let v2 : Fin 3 × Fin n := (0, ⟨2, by omega⟩)
    { {v0, v1, v2} }
  else ∅

/-
The full construction is the union of the tripartite edges and the extra edge.
-/
def construction (n : ℕ) : Hypergraph (Fin 3 × Fin n) :=
  tripartite_edges n ∪ extra_edges n

/-
The set of tripartite edges and the set of extra edges are disjoint.
-/
lemma tripartite_disjoint_extra (n : ℕ) : Disjoint (tripartite_edges n) (extra_edges n) := by
  unfold tripartite_edges extra_edges;
  split_ifs <;> simp +decide [ Finset.disjoint_left ];
  rintro a x y z rfl; simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;

/-
The number of tripartite edges is $n^3$.
-/
lemma tripartite_card (n : ℕ) : (tripartite_edges n).card = n^3 := by
  convert Finset.card_image_of_injective _ _;
  · erw [ Finset.card_product, Finset.card_product, Finset.card_fin ] ; ring;
  · intro x y hxy; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    grind

/-
The number of edges in the tripartite graph induced by a set of vertices $S$ is the product of the number of vertices in $S$ from each of the three parts.
-/
lemma tripartite_induced_card (n : ℕ) (S : Finset (Fin 3 × Fin n)) :
  (induced_edges (tripartite_edges n) S).card =
    (S.filter (λ v => v.1 = 0)).card * (S.filter (λ v => v.1 = 1)).card * (S.filter (λ v => v.1 = 2)).card := by
      -- We need to show that the number of tripartite edges induced by $S$ is equal to the product of the sizes of the three parts in $S$.
      have h_induced_edges_eq : induced_edges (tripartite_edges n) S = Finset.image (fun (x : Fin n × Fin n × Fin n) => {(0, x.1), (1, x.2.1), (2, x.2.2)}) (Finset.filter (fun (x : Fin n × Fin n × Fin n) => (0, x.1) ∈ S ∧ (1, x.2.1) ∈ S ∧ (2, x.2.2) ∈ S) (Finset.univ : Finset (Fin n × Fin n × Fin n))) := by
        -- To prove equality of finite sets, we show each set is a subset of the other.
        apply Finset.ext
        intro e
        simp [induced_edges, tripartite_edges];
        grind;
      rw [ h_induced_edges_eq, Finset.card_image_of_injective ];
      · rw [ show ( Finset.filter ( fun v => v.1 = 0 ) S ) = ( Finset.image ( fun a : Fin n => ( 0, a ) ) ( Finset.filter ( fun a : Fin n => ( 0, a ) ∈ S ) Finset.univ ) ) from ?_, show ( Finset.filter ( fun v => v.1 = 1 ) S ) = ( Finset.image ( fun a : Fin n => ( 1, a ) ) ( Finset.filter ( fun a : Fin n => ( 1, a ) ∈ S ) Finset.univ ) ) from ?_, show ( Finset.filter ( fun v => v.1 = 2 ) S ) = ( Finset.image ( fun a : Fin n => ( 2, a ) ) ( Finset.filter ( fun a : Fin n => ( 2, a ) ∈ S ) Finset.univ ) ) from ?_ ];
        · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          rw [ ← Finset.card_product, ← Finset.card_product ];
          rw [ ← Finset.card_image_of_injective _ ( show Function.Injective ( fun x : Fin n × Fin n × Fin n => ( ( x.1, x.2.1 ), x.2.2 ) ) from by intros a b; aesop ) ] ; congr ; ext ; aesop;
        · ext ⟨ a, b ⟩ ; aesop;
        · ext ⟨ x, y ⟩ ; aesop;
        · ext ⟨ i, a ⟩ ; aesop;
      · intro x y; simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ; aesop

/-
The number of extra edges induced by a set $S$ is at most 1 if $S$ has at least 3 vertices in the first part, and 0 otherwise.
-/
lemma extra_induced_bound (n : ℕ) (S : Finset (Fin 3 × Fin n)) :
  (induced_edges (extra_edges n) S).card ≤ if (S.filter (λ v => v.1 = 0)).card ≥ 3 then 1 else 0 := by
    unfold extra_edges induced_edges; split_ifs <;> simp_all +decide ;
    · exact Finset.card_le_one.mpr ( by aesop_cat );
    · intro h; have := Finset.card_le_card ( show S.filter ( fun v => v.1 = 0 ) ⊇ { ( 0, ⟨ 0, by linarith ⟩ ), ( 0, ⟨ 1, by linarith ⟩ ), ( 0, ⟨ 2, by linarith ⟩ ) } by aesop_cat ) ; simp_all +decide ;
      linarith

/-
For non-negative integers $a, b, c$ summing to 4, the quantity $abc + \mathbb{I}(a \ge 3)$ is at most 2.
-/
lemma arith_lemma_4 (a b c : ℕ) (h : a + b + c = 4) :
  a * b * c + (if a ≥ 3 then 1 else 0) ≤ 2 := by
    rcases a with ( _ | _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | _ | b ) <;> rcases c with ( _ | _ | _ | _ | c ) <;> simp +arith +decide only [ * ] at *

/-
For non-negative integers $a, b, c$ summing to 5, the quantity $abc + \mathbb{I}(a \ge 3)$ is at most 4.
-/
lemma arith_lemma_5 (a b c : ℕ) (h : a + b + c = 5) :
  a * b * c + (if a ≥ 3 then 1 else 0) ≤ 4 := by
    rcases a with ( _ | _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | _ | b ) <;> rcases c with ( _ | _ | _ | _ | c ) <;> simp +arith +decide only [ * ] at *;

/-
Any set of 4 vertices in the construction induces strictly fewer than 3 edges.
-/
lemma no_dense_subgraph_4 (n : ℕ) (S : Finset (Fin 3 × Fin n)) (hS : S.card = 4) :
  (induced_edges (construction n) S).card < 3 := by
    -- Let $a = |S \cap V_0|$, $b = |S \cap V_1|$, and $c = |S \cap V_2|$.
    set a := (S.filter (fun v => v.1 = 0)).card
    set b := (S.filter (fun v => v.1 = 1)).card
    set c := (S.filter (fun v => v.1 = 2)).card;
    -- The number of induced edges is the sum of induced tripartite edges and induced extra edges.
    have h_sum : (induced_edges (construction n) S).card = (induced_edges (tripartite_edges n) S).card + (induced_edges (extra_edges n) S).card := by
      unfold induced_edges;
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with e ; unfold construction ; aesop;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( tripartite_disjoint_extra n ) ( Finset.mem_filter.mp hx₁ |>.1 ) ( Finset.mem_filter.mp hx₂ |>.1 );
    -- Since $a + b + c = 4$, we can apply the arithmetic lemma to conclude that $abc + \mathbb{I}(a \ge 3) \le 2$.
    have h_arith : a + b + c = 4 := by
      rw [ ← hS, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
      · congr with x ; simp +decide
        grind;
      · exact Finset.disjoint_left.mpr ( by aesop );
      · exact Finset.disjoint_filter.mpr ( by aesop )
    have h_ineq : a * b * c + (if a ≥ 3 then 1 else 0) ≤ 2 := by
      exact arith_lemma_4 a b c h_arith;
    have h_induced_edges : (induced_edges (tripartite_edges n) S).card = a * b * c ∧ (induced_edges (extra_edges n) S).card ≤ (if a ≥ 3 then 1 else 0) := by
      exact ⟨ by rw [ tripartite_induced_card ], by apply extra_induced_bound ⟩;
    linarith

/-
Any set of 5 vertices in the construction induces strictly fewer than 7 edges.
-/
lemma no_dense_subgraph_5 (n : ℕ) (S : Finset (Fin 3 × Fin n)) (hS : S.card = 5) :
  (induced_edges (construction n) S).card < 7 := by
    -- Let $a = |S \cap V_0|$, $b = |S \cap V_1|$, $c = |S \cap V_2|$.
    let a := (S.filter (fun v => v.1 = 0)).card
    let b := (S.filter (fun v => v.1 = 1)).card
    let c := (S.filter (fun v => v.1 = 2)).card;
    -- By `arith_lemma_5`, we have $abc + \mathbb{I}(a \ge 3) \le 4$.
    have h_abc_le_4 : a * b * c + (if a ≥ 3 then 1 else 0) ≤ 4 := by
      have h_sum : a + b + c = 5 := by
        rw [ ← hS, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ] <;> congr! 1;
        · grind;
        · exact Finset.disjoint_left.mpr ( by aesop_cat );
        · exact Finset.disjoint_filter.mpr ( by aesop_cat )
      exact arith_lemma_5 a b c h_sum;
    -- The number of induced edges is the sum of induced tripartite edges and induced extra edges.
    have h_induced_edges : (induced_edges (construction n) S).card = (induced_edges (tripartite_edges n) S).card + (induced_edges (extra_edges n) S).card := by
      rw [ show induced_edges ( construction n ) S = induced_edges ( tripartite_edges n ) S ∪ induced_edges ( extra_edges n ) S from ?_, Finset.card_union_of_disjoint ];
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( tripartite_disjoint_extra n ) ( Finset.mem_filter.mp hx₁ |>.1 ) ( Finset.mem_filter.mp hx₂ |>.1 );
      · ext; simp [induced_edges, construction];
        grind;
    -- By `tripartite_induced_card`, we have $(induced_edges (tripartite_edges n) S).card = a * b * c$.
    have h_induced_tripartite : (induced_edges (tripartite_edges n) S).card = a * b * c := by
      exact tripartite_induced_card n S;
    linarith [ extra_induced_bound n S ]

/-
The constructed hypergraph is 3-uniform, has at least $n^3+1$ edges, and avoids the forbidden subgraphs.
-/
theorem construction_properties (n : ℕ) (h : 3 ≤ n) :
  let H := construction n
  is_uniform H 3 ∧
  H.card ≥ n^3 + 1 ∧
  ¬ has_dense_subgraph H 4 3 ∧
  ¬ has_dense_subgraph H 5 7 := by
    refine' ⟨ _, _, _, _ ⟩;
    · intro e he;
      unfold construction at he;
      unfold tripartite_edges extra_edges at he ; aesop;
    · unfold construction;
      rw [ Finset.card_union_of_disjoint ];
      · rw [ tripartite_card, extra_edges ] ; aesop;
      · exact tripartite_disjoint_extra n;
    · exact fun ⟨ S, hS₁, hS₂ ⟩ => not_lt_of_ge hS₂ ( by simpa using no_dense_subgraph_4 n S hS₁ );
    · rintro ⟨ S, hS₁, hS₂ ⟩;
      exact hS₂.not_gt ( no_dense_subgraph_5 n S hS₁ )

#print axioms construction_properties
-- 'construction_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
