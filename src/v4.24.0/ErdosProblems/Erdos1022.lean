/-

This is a Lean formalization of a solution to Erdős Problem 1022.
https://www.erdosproblems.com/forum/thread/1022

The original proof was found by: KoishiChan

https://www.erdosproblems.com/forum/thread/1022#post-2004


The proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
Formalized the Erdős problem 1022 as `erdos_1022` and proved its negation `not_erdos_1022`. The proof relies on the helper lemma `c_t_le_two` which establishes that any such constant must be bounded by 2, contradicting the requirement that it tends to infinity.
-/

/-
We prove that if a constant $c_t$ ensures that every hypergraph $F$ with edge sizes at least $t$ and density condition $|F[X]| < c_t |X|$ is 2-colorable, then $c_t \le 2$.
We do this by constructing a counterexample hypergraph for any $t \ge 2$ which is not 2-colorable but satisfies the density condition for any $c_t > 2$.
-/

import Mathlib

namespace Erdos1022

set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 0

/-
A hypergraph is a finite set of finite sets. It is two-colorable (has Property B) if there exists a 2-coloring of the vertices such that no edge is monochromatic.
-/
open Finset

abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

def TwoColorable {α : Type*} [DecidableEq α] (F : Hypergraph α) : Prop :=
  ∃ (c : α → Bool), ∀ A ∈ F, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y

/-
We define the counterexample hypergraph $F$.
Vertices:
- $\Gamma$: set of size $3t$.
- $V$: set of vertices $v_{A, B}$ for pairs $A, B \subseteq \Gamma$ of size $t$.
- $W$: set of vertices $w_{Q, R}$ for $Q \subseteq \Gamma$ of size $t$ and $R \subseteq V$ of size $t$.
Edges:
- For each $v_{A, B} \in V$, $A \cup \{v_{A, B}\}$ and $B \cup \{v_{A, B}\}$.
- For each $w_{Q, R} \in W$, $Q \cup \{w_{Q, R}\}$ and $R \cup \{w_{Q, R}\}$.
-/
open Finset

variable (t : ℕ)

abbrev Gamma := Fin (3 * t)

abbrev V_node := { p : Finset (Gamma t) × Finset (Gamma t) // p.1.card = t ∧ p.2.card = t }

abbrev W_node := { p : Finset (Gamma t) × Finset (V_node t) // p.1.card = t ∧ p.2.card = t }

inductive Vert
| g (a : Gamma t)
| v (a : V_node t)
| w (a : W_node t)
deriving DecidableEq, Fintype

def counterexample_hypergraph : Hypergraph (Vert t) :=
  let v_edges := (univ : Finset (V_node t)).biUnion (λ p =>
    { p.val.1.image Vert.g ∪ {Vert.v p}, p.val.2.image Vert.g ∪ {Vert.v p} })
  let w_edges := (univ : Finset (W_node t)).biUnion (λ p =>
    { p.val.1.image Vert.g ∪ {Vert.w p}, p.val.2.image Vert.v ∪ {Vert.w p} })
  v_edges ∪ w_edges

/-
The counterexample hypergraph is $(t+1)$-uniform.
-/
theorem counterexample_uniform (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) : A.card = t + 1 := by
  unfold counterexample_hypergraph at hA;
  norm_num +zetaDelta at *;
  rcases hA with ( ⟨ a, b, h, rfl | rfl ⟩ | ⟨ a, b, h, rfl | rfl ⟩ ) <;> simp +decide [ *, Finset.card_image_of_injective, Function.Injective ]

/-
If a coloring is valid, then one color appears at least $2t$ times in $\Gamma$.
-/
theorem lemma_one_color_dominant (t : ℕ) (c : Vert t → Bool)
  (h_valid : ∀ A ∈ counterexample_hypergraph t, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y) :
  (∃ (color : Bool), (Finset.univ.filter (λ x : Gamma t => c (Vert.g x) = color)).card ≥ 2 * t) := by
    by_contra h_contra
    push_neg at h_contra
    have h_one_color : ∀ color : Bool, Finset.card (Finset.filter (fun x => c (Vert.g x) = color) (Finset.univ : Finset (Gamma t))) < t := by
      intro color
      by_cases h_two_colors : ∃ A B : Finset (Gamma t), A.card = t ∧ B.card = t ∧ (∀ x ∈ A, c (Vert.g x) = color) ∧ (∀ x ∈ B, c (Vert.g x) = !color) ∧ A ∩ B = ∅;
      · obtain ⟨ A, B, hA, hB, hA', hB', hAB ⟩ := h_two_colors;
        -- Consider the edge $A \cup \{v_{A, B}\}$.
        have h_edge_A : ∃ x y : Vert t, x ∈ A.image Vert.g ∪ {Vert.v ⟨(A, B), hA, hB⟩} ∧ y ∈ A.image Vert.g ∪ {Vert.v ⟨(A, B), hA, hB⟩} ∧ c x ≠ c y := by
          apply h_valid;
          exact Finset.mem_union_left _ ( Finset.mem_biUnion.mpr ⟨ ⟨ ( A, B ), hA, hB ⟩, Finset.mem_univ _, Finset.mem_insert_self _ _ ⟩ );
        -- Consider the edge $B \cup \{v_{A, B}\}$.
        have h_edge_B : ∃ x y : Vert t, x ∈ B.image Vert.g ∪ {Vert.v ⟨(A, B), hA, hB⟩} ∧ y ∈ B.image Vert.g ∪ {Vert.v ⟨(A, B), hA, hB⟩} ∧ c x ≠ c y := by
          convert h_valid _ _ using 1;
          simp +decide [ counterexample_hypergraph ];
          exact Or.inl ⟨ A, B, ⟨ hA, hB ⟩, Or.inr rfl ⟩;
        obtain ⟨ x, y, hx, hy, hxy ⟩ := h_edge_A; obtain ⟨ u, v, hu, hv, huv ⟩ := h_edge_B; simp_all +decide [ Finset.ext_iff ] ;
        rcases hx with ( rfl | ⟨ a, ha, rfl ⟩ ) <;> rcases hy with ( rfl | ⟨ b, hb, rfl ⟩ ) <;> simp_all +decide
        · rcases hu with ( rfl | ⟨ a, ha, rfl ⟩ ) <;> rcases hv with ( rfl | ⟨ b, hb, rfl ⟩ ) <;> simp_all +decide
        · rcases hu with ( rfl | ⟨ b, hb, rfl ⟩ ) <;> rcases hv with ( rfl | ⟨ c, hc, rfl ⟩ ) <;> simp_all +decide
      · contrapose! h_two_colors;
        -- Let $A$ be a subset of $\Gamma$ of size $t$ such that $c(x) = color$ for all $x \in A$.
        obtain ⟨A, hA⟩ : ∃ A : Finset (Gamma t), A.card = t ∧ ∀ x ∈ A, c (Vert.g x) = color := by
          exact Exists.elim ( Finset.exists_subset_card_eq h_two_colors ) fun A hA => ⟨ A, hA.2, fun x hx => by simpa using hA.1 hx ⟩;
        -- Let $B$ be a subset of $\Gamma$ of size $t$ such that $c(x) = !color$ for all $x \in B$.
        obtain ⟨B, hB⟩ : ∃ B : Finset (Gamma t), B.card = t ∧ ∀ x ∈ B, c (Vert.g x) = !color := by
          have hB : Finset.card (Finset.filter (fun x => c (Vert.g x) = !color) (Finset.univ : Finset (Gamma t))) ≥ t := by
            have hB : Finset.card (Finset.filter (fun x => c (Vert.g x) = color) (Finset.univ : Finset (Gamma t))) + Finset.card (Finset.filter (fun x => c (Vert.g x) = !color) (Finset.univ : Finset (Gamma t))) = 3 * t := by
              rw [ Finset.card_filter, Finset.card_filter ];
              rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun _ _ => by aesop, Finset.sum_const, Finset.card_univ ] ; norm_num [ Finset.card_univ ];
            linarith [ h_contra color, h_contra ( !color ) ];
          obtain ⟨ B, hB ⟩ := Finset.exists_subset_card_eq hB;
          exact ⟨ B, hB.2, fun x hx => Finset.mem_filter.mp ( hB.1 hx ) |>.2 ⟩;
        use A, B;
        grind;
    have h_card : Finset.card (Finset.univ : Finset (Gamma t)) = Finset.card (Finset.filter (fun x => c (Vert.g x) = true) (Finset.univ : Finset (Gamma t))) + Finset.card (Finset.filter (fun x => c (Vert.g x) = false) (Finset.univ : Finset (Gamma t))) := by
      rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_congr rfl fun _ _ => by aesop ] ; simp +decide ;
    have := h_one_color true; have := h_one_color false; norm_num [ Finset.card_univ ] at *; linarith;

/-
$\binom{2t}{t} \ge 2t$ for $t \ge 1$.
-/
theorem lemma_choose_ge_2t (t : ℕ) (ht : t ≥ 1) : Nat.choose (2 * t) t ≥ 2 * t := by
  induction' ht with k hk;
  · decide +revert;
  · induction' k with k ih <;> simp_all +arith +decide [ Nat.choose ] ; linarith!;

/-
If $A$ is monochromatic with color $C$, then $v_{A, B}$ cannot have color $C$.
-/
theorem lemma_v_node_color_forced (t : ℕ) (c : Vert t → Bool)
  (h_valid : ∀ A ∈ counterexample_hypergraph t, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y)
  (A B : Finset (Gamma t)) (hA : A.card = t) (hB : B.card = t)
  (color : Bool)
  (hA_mono : ∀ x ∈ A, c (Vert.g x) = color) :
  c (Vert.v ⟨(A, B), hA, hB⟩) ≠ color := by
    contrapose! h_valid;
    use A.image Vert.g ∪ {Vert.v ⟨(A, B), hA, hB⟩};
    unfold counterexample_hypergraph;
    grind

/-
If there is a monochromatic set $S$ of size $2t$, then there exists a set $R \subseteq V$ of size $t$ of the opposite color.
-/
theorem lemma_exists_monochromatic_R (t : ℕ) (ht : t ≥ 2) (c : Vert t → Bool)
  (h_valid : ∀ A ∈ counterexample_hypergraph t, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y)
  (S : Finset (Gamma t)) (hS : S.card = 2 * t)
  (color : Bool)
  (hS_mono : ∀ x ∈ S, c (Vert.g x) = color) :
  ∃ R : Finset (V_node t), R.card = t ∧ ∀ v ∈ R, c (Vert.v v) ≠ color := by
    -- Let $\mathcal{A}$ be the set of all subsets of $S$ of size $t$.
    set A := Finset.powersetCard t S with hA_def
    have hA_card : A.card ≥ t := by
      simp +zetaDelta at *;
      rw [ hS ];
      -- We can use the fact that $\binom{2t}{t} \geq 2t$ for $t \geq 1$.
      have h_binom_ge_2t : ∀ t ≥ 1, Nat.choose (2 * t) t ≥ 2 * t := by
        exact fun t a => lemma_choose_ge_2t t a;
      linarith [ h_binom_ge_2t t ( by linarith ) ];
    -- For each $A \in \mathcal{A}$, let $B = S \setminus A$. Then $(A, B)$ defines a vertex $v_{A, B} \in V$.
    have hV_nodes : ∃ R : Finset (V_node t), R.card ≥ t ∧ ∀ v ∈ R, c (Vert.v v) ≠ color := by
      have hV_nodes : ∀ A' ∈ A, ∃ v : V_node t, v.val.1 = A' ∧ v.val.2 = S \ A' ∧ c (Vert.v v) ≠ color := by
        intro A' hA'
        use ⟨(A', S \ A'), by
          aesop, by
          grind⟩
        generalize_proofs at *;
        exact ⟨ rfl, rfl, lemma_v_node_color_forced t c h_valid A' ( S \ A' ) ( by aesop ) ( by aesop ) color fun x hx => hS_mono x <| Finset.mem_of_subset ( Finset.subset_iff.mpr fun y hy => by aesop ) hx ⟩;
      choose! f hf1 hf2 hf3 using hV_nodes;
      use Finset.image ( fun x : A => f x x.2 ) Finset.univ;
      rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · grind +ring;
      · grind;
    obtain ⟨ R, hR₁, hR₂ ⟩ := hV_nodes; exact Exists.elim ( Finset.exists_subset_card_eq hR₁ ) fun R' hR' => ⟨ R', hR'.2, fun v hv => hR₂ v ( hR'.1 hv ) ⟩ ;

/-
If $Q$ is monochromatic with color $C$ and $R$ is monochromatic with color $\ne C$, then $w_{Q, R}$ leads to a contradiction.
-/
theorem lemma_w_node_contradiction (t : ℕ) (c : Vert t → Bool)
  (h_valid : ∀ A ∈ counterexample_hypergraph t, ∃ x y, x ∈ A ∧ y ∈ A ∧ c x ≠ c y)
  (Q : Finset (Gamma t)) (hQ : Q.card = t)
  (R : Finset (V_node t)) (hR : R.card = t)
  (color : Bool)
  (hQ_mono : ∀ x ∈ Q, c (Vert.g x) = color)
  (hR_mono : ∀ v ∈ R, c (Vert.v v) ≠ color) :
  False := by
    -- By assumption, $w_{Q, R}$ must be colored with a color different from $color$.
    have hw_color : c (Vert.w ⟨(Q, R), hQ, hR⟩) ≠ color := by
      contrapose! h_valid;
      refine' ⟨ Finset.image Vert.g Q ∪ { Vert.w ⟨ ( Q, R ), hQ, hR ⟩ }, _, _ ⟩ <;> simp_all +decide
      · refine' Finset.mem_union_right _ _;
        grind;
      · rintro x y ( rfl | ⟨ a, ha, rfl ⟩ ) ( rfl | ⟨ b, hb, rfl ⟩ ) <;> aesop;
    -- Since $R$ is monochromatic with $\ne$ `color`, for $E_2$ to be valid, $w$ must have color `color`.
    have hw_color_R : c (Vert.w ⟨(Q, R), hQ, hR⟩) = color := by
      -- Apply the validity condition to the edge $R \cup \{w_{Q, R}\}$.
      obtain ⟨x, y, hxR, hyR, hxy⟩ : ∃ x y, x ∈ R.image (fun v => Vert.v v) ∪ {Vert.w ⟨(Q, R), hQ, hR⟩} ∧ y ∈ R.image (fun v => Vert.v v) ∪ {Vert.w ⟨(Q, R), hQ, hR⟩} ∧ c x ≠ c y := by
        convert h_valid _ _;
        simp +decide [ counterexample_hypergraph ];
        exact Or.inr ⟨ Q, R, ⟨ hQ, hR ⟩, Or.inr rfl ⟩;
      simp +zetaDelta at *;
      rcases hxR with ( rfl | ⟨ a, b, ⟨ ha, hb ⟩, hR, rfl ⟩ ) <;> rcases hyR with ( rfl | ⟨ c, d, ⟨ hc, hd ⟩, hR', rfl ⟩ ) <;> simp_all +decide;
      · cases h : ‹Vert t → Bool› ( Vert.w ⟨ ( Q, R ), hQ, hR ⟩ ) <;> cases h' : ‹Vert t → Bool› ( Vert.v ⟨ ( c, d ), hc, hd ⟩ ) <;> specialize hR_mono c d hc hd hR' <;> aesop;
      · cases color <;> simp_all +decide only;
      · cases color <;> cases em ( ‹Vert t → Bool› ( Vert.v ⟨ ( a, b ), ha, hb ⟩ ) ) <;> cases em ( ‹Vert t → Bool› ( Vert.v ⟨ ( c, d ), hc, hd ⟩ ) ) <;> simp_all ( config := { decide := Bool.true } ) only [ ];
    contradiction

/-
The counterexample hypergraph is not 2-colorable for $t \ge 2$.
-/
theorem counterexample_not_two_colorable (t : ℕ) (ht : t ≥ 2) : ¬ TwoColorable (counterexample_hypergraph t) := by
  intro h_two_colorable
  obtain ⟨c, hc⟩ := h_two_colorable
  -- 1. Get a dominant color and a set S of size 2t
  obtain ⟨color, h_color_card⟩ := lemma_one_color_dominant t c hc
  obtain ⟨S, hS_subset, hS_card⟩ := Finset.exists_subset_card_eq h_color_card
  have hS_mono : ∀ x ∈ S, c (Vert.g x) = color := λ x hx => (Finset.mem_filter.mp (hS_subset hx)).2

  -- 2. Get a set R of size t with the opposite color
  obtain ⟨R, hR_card, hR_mono⟩ := lemma_exists_monochromatic_R t ht c hc S hS_card color hS_mono

  -- 3. Pick a subset Q of S of size t
  have h_t_le_S : t ≤ S.card := by rw [hS_card]; linarith
  obtain ⟨Q, hQ_subset, hQ_card⟩ := Finset.exists_subset_card_eq h_t_le_S
  have hQ_mono : ∀ x ∈ Q, c (Vert.g x) = color := λ x hx => hS_mono x (hQ_subset hx)

  -- 4. Derive contradiction
  exact lemma_w_node_contradiction t c hc Q hQ_card R hR_card color hQ_mono hR_mono

/-
Every edge in the counterexample hypergraph contains at most one vertex of type W.
-/
def is_W (t : ℕ) (x : Vert t) : Prop :=
  match x with
  | Vert.w _ => True
  | _ => False

def is_V (t : ℕ) (x : Vert t) : Prop :=
  match x with
  | Vert.v _ => True
  | _ => False

theorem w_unique_in_edge (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) :
  (A.filter (is_W t)).card ≤ 1 := by
    unfold counterexample_hypergraph at hA;
    simp +zetaDelta at *;
    rcases hA with ( ⟨ a, b, h, rfl | rfl ⟩ | ⟨ a, b, h, rfl | rfl ⟩ ) <;> simp +decide [ Finset.filter_insert, Finset.filter_image ];
    · unfold is_W; aesop;
    · unfold is_W; aesop;
    · unfold is_W; aesop;
    · unfold is_W; aesop;

/-
If an edge has no $W$-nodes, it has exactly one $V$-node.
-/
theorem v_unique_in_edge_of_no_w (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t)
  (h_no_w : (A.filter (is_W t)).card = 0) :
  (A.filter (is_V t)).card = 1 := by
    have := counterexample_uniform t A hA;
    -- Since there are no W-nodes in A, all elements of A must be either G-nodes or V-nodes.
    have hG_or_V : ∀ x ∈ A, is_W t x = False := by
      simp_all +decide [ Finset.ext_iff ];
    -- Since there are no W-nodes in A, all elements of A must be either G-nodes or V-nodes. Therefore, A can be written as the union of G-nodes and V-nodes.
    have h_union : A = (A.filter (fun x => is_V t x)) ∪ (A.filter (fun x => is_W t x)) ∪ (A.filter (fun x => ¬is_V t x ∧ ¬is_W t x)) := by
      ext x; by_cases hx : is_V t x <;> by_cases hx' : is_W t x <;> aesop;
    rw [ h_union ] at this;
    rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] at this <;> norm_num at *;
    · -- Since there are no W-nodes in A, all elements of A must be either G-nodes or V-nodes. Therefore, A can be written as the union of G-nodes and V-nodes, and the cardinality of A is the sum of the cardinalities of these two sets.
      have h_card_G_V : (A.filter (fun x => ¬is_V t x ∧ ¬is_W t x)).card = t := by
        unfold counterexample_hypergraph at hA;
        simp +zetaDelta at *;
        rcases hA with ( ⟨ a, b, h, rfl | rfl ⟩ | ⟨ a, b, h, rfl | rfl ⟩ ) <;> simp +decide [ Finset.filter_insert, Finset.filter_image ] at *;
        · split_ifs <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
          · tauto;
          · simp_all +decide [ Finset.filter_eq_empty_iff.mpr ];
            linarith [ show Finset.card ( Finset.filter ( fun x => is_V t ( Vert.g x ) ) a ) = 0 from Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun x hx => by cases x ; aesop ];
        · split_ifs <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
          · tauto;
          · exact Eq.symm ( by rw [ show ( Finset.filter ( fun x => ¬is_V t ( Vert.g x ) ∧ ¬is_W t ( Vert.g x ) ) b ) = b from Finset.filter_true_of_mem fun x hx => by cases x ; tauto ] ; aesop );
        · split_ifs <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
          · cases ‹¬is_V t ( Vert.w ⟨ ( a, b ), h ⟩ ) ∧ ¬is_W t ( Vert.w ⟨ ( a, b ), h ⟩ ) ›.2 trivial;
          · cases ‹_›;
        · tauto;
      norm_num [ show Finset.filter ( fun x => is_W t x ) A = ∅ from Finset.filter_eq_empty_iff.mpr fun x hx => hG_or_V x hx ] at * ; linarith;
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
    · simp +contextual [ Finset.disjoint_left ]

/-
Every edge has either exactly one $W$ node, or (no $W$ nodes and exactly one $V$ node).
-/
theorem w_or_v_in_edge (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) :
  (A.filter (is_W t)).card = 1 ∨ ((A.filter (is_W t)).card = 0 ∧ (A.filter (is_V t)).card = 1) := by
    by_cases hW : (A.filter (is_W t)).card = 0;
    · exact Or.inr ⟨ hW, v_unique_in_edge_of_no_w t A hA hW ⟩;
    · exact Or.inl ( le_antisymm ( w_unique_in_edge t A hA ) ( Nat.pos_of_ne_zero hW ) )

/-
For every edge in the counterexample hypergraph, there exists a unique "special" vertex. A vertex is special if it is a W-node, or if there are no W-nodes in the edge and it is a V-node.
-/
def is_special (t : ℕ) (A : Finset (Vert t)) (x : Vert t) : Prop :=
  (is_W t x ∧ x ∈ A) ∨ (is_V t x ∧ x ∈ A ∧ (A.filter (is_W t)).card = 0)

theorem exists_unique_special (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) :
  ∃! x, is_special t A x := by
    -- By `w_or_v_in_edge`, there are three cases: (a) `A` has exactly one $W$-node; (b) `A` has no $W$-nodes and exactly one $V$-node; or (c) `A` has neither $W$- nor $V$-nodes. Case (c) will turn out to be impossible, so we handle (a) and (b) first.
    have h_cases : (A.filter (is_W t)).card = 1 ∨ ((A.filter (is_W t)).card = 0 ∧ (A.filter (is_V t)).card = 1) := by
      exact w_or_v_in_edge t A hA;
    rcases h_cases with h|h <;> simp_all +decide [ Finset.card_eq_one ];
    · obtain ⟨ x, hx ⟩ := h; use x; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      unfold is_special; aesop;
    · cases' h with h₁ h₂; obtain ⟨ x, hx ⟩ := h₂; use x; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      unfold is_special; aesop;

/-
We define the map $\phi$ that assigns to each edge its unique special vertex.
-/
noncomputable def phi (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) : Vert t :=
  Classical.choose (exists_unique_special t A hA)

theorem phi_is_special (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) :
  is_special t A (phi t A hA) :=
  (Classical.choose_spec (exists_unique_special t A hA)).1

theorem phi_unique (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) (x : Vert t)
  (hx : is_special t A x) : x = phi t A hA :=
  (Classical.choose_spec (exists_unique_special t A hA)).2 x hx

/-
The value of $\phi(A)$ is never a vertex in $\Gamma$.
-/
theorem phi_not_gamma (t : ℕ) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) (g : Gamma t) :
  phi t A hA ≠ Vert.g g := by
    -- By definition of $phi$, we know that $phi(A)$ is either a $W$ node or a $V$ node.
    have h_phi_is_special : is_special t A (phi t A hA) := by
      exact phi_is_special t A hA;
    cases h_phi_is_special <;> aesop

/-
An edge $A$ contains the vertex $w_p$ if and only if $A$ is one of the two edges generated by $p$.
-/
theorem w_in_edge_iff (t : ℕ) (p : W_node t) (A : Finset (Vert t)) (hA : A ∈ counterexample_hypergraph t) :
  Vert.w p ∈ A ↔ A = p.val.1.image Vert.g ∪ {Vert.w p} ∨ A = p.val.2.image Vert.v ∪ {Vert.w p} := by
    constructor <;> intro h;
    · unfold counterexample_hypergraph at hA;
      simp +zetaDelta at *;
      rcases hA with ( ⟨ a, b, h, rfl | rfl ⟩ | ⟨ a, b, h, rfl | rfl ⟩ ) <;> simp_all +decide [ Finset.ext_iff ];
    · aesop

/-
For $t \ge 1$, the two edges generated by a W-node are distinct.
-/
theorem w_edges_distinct (t : ℕ) (ht : t ≥ 1) (p : W_node t) :
  p.val.1.image Vert.g ∪ {Vert.w p} ≠ p.val.2.image Vert.v ∪ {Vert.w p} := by
    intro h;
    simp_all +decide [ Finset.ext_iff ];
    specialize h ( Vert.g ( Classical.choose ( Finset.card_pos.mp ( by linarith [ p.2.1 ] ) ) ) ) ; have := Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ p.2.1 ] ) ) ; aesop

/-
For $t \ge 1$, every W-node is contained in exactly 2 edges.
-/
theorem edges_containing_w (t : ℕ) (ht : t ≥ 1) (w : Vert t) (hw : is_W t w) :
  (Finset.univ.filter (λ A : { A // A ∈ counterexample_hypergraph t } => w ∈ A.val)).card = 2 := by
    -- Since `w` is a W-node, let `w = Vert.w p`.
    obtain ⟨p, rfl⟩ : ∃ p : W_node t, w = Vert.w p := by
      cases w <;> tauto;
    -- By `w_in_edge_iff`, the edges containing `w` are exactly $E_1 = p.1 \cup \{w\}$ and $E_2 = p.2 \cup \{w\}$.
    have h_edges_containing_w : {A : Finset (Vert t) | A ∈ counterexample_hypergraph t ∧ Vert.w p ∈ A} = {p.val.1.image Vert.g ∪ {Vert.w p}, p.val.2.image Vert.v ∪ {Vert.w p}} := by
      ext A;
      constructor;
      · exact fun h => by have := w_in_edge_iff t p A h.1; aesop;
      · rintro ( rfl | rfl ) <;> simp +decide [ counterexample_hypergraph ];
        · exact Or.inr ⟨ p.val.1, p.val.2, p.prop, Or.inl rfl ⟩;
        · exact Or.inr ⟨ p.1.1, p.1.2, p.2, Or.inr rfl ⟩;
    -- Since these are the only edges containing `w`, the cardinality of the set is 2.
    have h_card : (Finset.filter (fun A => Vert.w p ∈ A) (counterexample_hypergraph t)).card = 2 := by
      convert congr_arg Finset.card ( show Finset.filter ( fun A => Vert.w p ∈ A ) ( counterexample_hypergraph t ) = { Finset.image Vert.g ( p.val.1 ) ∪ { Vert.w p }, Finset.image Vert.v ( p.val.2 ) ∪ { Vert.w p } } from ?_ ) using 1;
      · rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide [ Finset.mem_singleton ];
        intro h; have := w_edges_distinct t ht p; simp_all +decide [ Finset.ext_iff ] ;
      · grind;
    rw [ ← h_card, Finset.card_filter ];
    rw [ Finset.card_filter ];
    conv_rhs => rw [ ← Finset.sum_coe_sort ] ;

/-
There are at most 2 edges containing a given V-node and no W-nodes.
-/
theorem edges_containing_v_no_w (t : ℕ) (v : Vert t) (hv : is_V t v) :
  (Finset.univ.filter (λ A : { A // A ∈ counterexample_hypergraph t } => v ∈ A.val ∧ (A.val.filter (is_W t)).card = 0)).card ≤ 2 := by
    obtain ⟨p, hp⟩ : ∃ p : V_node t, v = Vert.v p := by
      cases v <;> aesop;
    -- Since $v$ is a V-node, the edges containing $v$ and no W-nodes must be V-edges.
    have h_v_edges : ∀ A : { A : Finset (Vert t) // A ∈ counterexample_hypergraph t }, v ∈ A.val ∧ (A.val.filter (is_W t)).card = 0 → A.val = p.val.1.image Vert.g ∪ {Vert.v p} ∨ A.val = p.val.2.image Vert.g ∪ {Vert.v p} := by
      intro A hA
      obtain ⟨hA_v, hA_no_w⟩ := hA
      have hA_v_edge : A.val ∈ (Finset.univ : Finset (V_node t)).biUnion (λ p =>
        { p.val.1.image Vert.g ∪ {Vert.v p}, p.val.2.image Vert.g ∪ {Vert.v p} }) := by
          have hA_v_edge : A.val ∈ (Finset.univ : Finset (V_node t)).biUnion (λ p =>
            { p.val.1.image Vert.g ∪ {Vert.v p}, p.val.2.image Vert.g ∪ {Vert.v p} }) ∪ (Finset.univ : Finset (W_node t)).biUnion (λ p =>
            { p.val.1.image Vert.g ∪ {Vert.w p}, p.val.2.image Vert.v ∪ {Vert.w p} }) := by
              exact A.2;
          have hA_v_edge : ∀ p : W_node t, ¬(A.val = p.val.1.image Vert.g ∪ {Vert.w p} ∨ A.val = p.val.2.image Vert.v ∪ {Vert.w p}) := by
            intro p hp
            have hA_w : Vert.w p ∈ A.val := by
              grind;
            exact absurd hA_no_w ( by rw [ Finset.card_eq_zero ] ; exact Finset.Nonempty.ne_empty ⟨ _, Finset.mem_filter.mpr ⟨ hA_w, by exact
              trivial ⟩ ⟩ );
          grind;
      simp +zetaDelta at *;
      rcases hA_v_edge with ⟨ a, b, ⟨ ha, hb ⟩, h | h ⟩ <;> simp_all +decide [ Finset.ext_iff ];
    refine' le_trans ( Finset.card_le_card <| show Finset.filter ( fun A : { A : Finset ( Vert t ) // A ∈ counterexample_hypergraph t } => v ∈ ( A : Finset ( Vert t ) ) ∧ # ( Finset.filter ( is_W t ) ( A : Finset ( Vert t ) ) ) = 0 ) Finset.univ ⊆ { ⟨ Finset.image Vert.g p.val.1 ∪ { Vert.v p }, _ ⟩, ⟨ Finset.image Vert.g p.val.2 ∪ { Vert.v p }, _ ⟩ } from _ ) _ <;> simp +decide;
    all_goals norm_num [ Finset.subset_iff ];
    any_goals exact Finset.card_insert_le _ _;
    · simp +decide [ counterexample_hypergraph ];
      grind;
    · convert Finset.mem_union_left _ ( Finset.mem_biUnion.mpr ⟨ p, _, _ ⟩ ) using 1;
      · exact Finset.mem_univ _;
      · simp +decide
    · intro A hA hv h; specialize h_v_edges ⟨ A, hA ⟩ ; aesop;

/-
For any vertex $y$, there are at most 2 edges $A$ in the counterexample hypergraph such that $\phi(A) = y$.
-/
theorem phi_preimage_le_two (t : ℕ) (ht : t ≥ 1) (y : Vert t) :
  (Finset.univ.filter (λ A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = y)).card ≤ 2 := by
    by_cases hy_gamma : ∃ g : Gamma t, y = Vert.g g;
    · obtain ⟨ g, rfl ⟩ := hy_gamma; exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = Vert.g g ) Finset.univ ⊆ Finset.filter ( fun A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = Vert.g g ) Finset.univ from Finset.Subset.refl _ ) ) ( by rw [ Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun x hx => by simpa using phi_not_gamma t _ _ _ ] ; norm_num ) ;
    · by_cases hy_w : is_W t y;
      · convert edges_containing_w t ht y hy_w |> le_of_eq using 1;
        congr! 1;
        ext A;
        constructor <;> intro hA;
        · have := phi_is_special t A.val A.property;
          unfold is_special at this; aesop;
        · convert phi_unique t A.val A.property y _;
          · grind;
          · unfold is_special; aesop;
      · by_cases hy_v : is_V t y;
        · -- If $y$ is a $V$-node, then $\phi(A) = y$ implies $y \in A$ and $A$ has no $W$-nodes (by `phi_is_special` and definition of special for $V$-nodes). By `edges_containing_v_no_w`, there are at most 2 such edges. Thus the preimage size is at most 2.
          have h_preimage_v : ∀ A : { A // A ∈ counterexample_hypergraph t }, phi t A.val A.property = y → y ∈ A.val ∧ (A.val.filter (is_W t)).card = 0 := by
            intro A hA
            have h_phi_special : is_special t A.val y := by
              exact hA ▸ phi_is_special t A.val A.property;
            unfold is_special at h_phi_special; aesop;
          exact le_trans ( Finset.card_le_card <| show Finset.filter ( fun A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = y ) Finset.univ ⊆ Finset.filter ( fun A : { A // A ∈ counterexample_hypergraph t } => y ∈ A.val ∧ ( A.val.filter ( is_W t ) ).card = 0 ) Finset.univ from fun A hA => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_preimage_v A <| Finset.mem_filter.mp hA |>.2 ⟩ ) ( edges_containing_v_no_w t y hy_v );
        · -- Since y is not a Gamma-node, W-node, or V-node, this leads to a contradiction because every vertex in the hypergraph must be one of these three types.
          have h_contradiction : ∀ y : Vert t, is_W t y ∨ is_V t y ∨ ∃ g : Gamma t, y = Vert.g g := by
            rintro ( _ | _ | _ ) <;> tauto;
          grind

/-
For any subset of vertices $Y$, the number of edges contained in $Y$ is at most $2|Y|$.
-/
theorem subset_counting_bound (t : ℕ) (ht : t ≥ 2) (Y : Finset (Vert t)) :
  ((counterexample_hypergraph t).filter (λ S => S ⊆ Y)).card ≤ 2 * Y.card := by
    -- For each vertex $y \in Y$, there are at most 2 sets in the filter.
    have h_filter_le_two_for_each_y : (Finset.univ.filter (fun S : { S // S ∈ counterexample_hypergraph t } => S.val ⊆ Y)).card ≤ ∑ y ∈ Y, (Finset.univ.filter (fun A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = y ∧ A.val ⊆ Y)).card := by
      have h_filter_le_two_for_each_y : ∀ S : { S // S ∈ counterexample_hypergraph t }, S.val ⊆ Y → ∃ y ∈ Y, phi t S.val S.property = y := by
        intro S hS;
        have := phi_is_special t S.val S.property;
        cases this <;> aesop;
      have h_filter_le_two_for_each_y : (Finset.univ.filter (fun S : { S // S ∈ counterexample_hypergraph t } => S.val ⊆ Y)).card ≤ (Finset.biUnion Y (fun y => Finset.univ.filter (fun S : { S // S ∈ counterexample_hypergraph t } => phi t S.val S.property = y ∧ S.val ⊆ Y))).card := by
        exact Finset.card_le_card fun x hx => by specialize h_filter_le_two_for_each_y x; aesop;
      exact h_filter_le_two_for_each_y.trans ( Finset.card_biUnion_le );
    -- For each vertex $y \in Y$, the number of sets in the filter is at most 2.
    have h_filter_le_two_for_each_y' : ∀ y ∈ Y, (Finset.univ.filter (fun A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = y ∧ A.val ⊆ Y)).card ≤ 2 := by
      intro y hy
      have h_filter_le_two_for_each_y'' : (Finset.univ.filter (fun A : { A // A ∈ counterexample_hypergraph t } => phi t A.val A.property = y)).card ≤ 2 := by
        convert phi_preimage_le_two t ( by linarith ) y using 1;
      exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_filter_le_two_for_each_y'';
    convert h_filter_le_two_for_each_y.trans ( Finset.sum_le_sum h_filter_le_two_for_each_y' ) using 1;
    · refine' Finset.card_bij ( fun S hS => ⟨ S, _ ⟩ ) _ _ _ <;> aesop;
    · rw [ Finset.sum_const, smul_eq_mul, mul_comm ]

/-
If a constant $c_t$ guarantees property B for hypergraphs with a certain density condition, then $c_t \le 2$.
-/
theorem c_t_le_two (t : ℕ) (ht : t ≥ 2) (c_t : ℝ)
  (h_property : ∀ (F : Hypergraph (Vert t)),
    (∀ A ∈ F, A.card ≥ t) →
    (∀ X : Finset (Vert t), X.Nonempty → ((F.filter (λ A => A ⊆ X)).card : ℝ) < c_t * (X.card : ℝ)) →
    TwoColorable F) :
  c_t ≤ 2 := by
    contrapose! h_property;
    refine' ⟨ _, _, _, _ ⟩;
    exact counterexample_hypergraph t;
    · exact fun A hA => by linarith [ counterexample_uniform t A hA ] ;
    · intro X hX_nonempty
      have h_subset_counting_bound : ((counterexample_hypergraph t).filter (λ S => S ⊆ X)).card ≤ 2 * X.card := by
        exact subset_counting_bound t ht X;
      exact lt_of_le_of_lt ( Nat.cast_le.mpr h_subset_counting_bound ) ( by norm_num; nlinarith [ show ( X.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr hX_nonempty ] );
    · exact counterexample_not_two_colorable t ht


/-
Is there a constant c_t, where c_t -> infinity as t -> infinity, such that if F is a finite family of finite sets, all of size at least t, and for every set X there are < c_t * |X| many A in F with A subset X, then F has chromatic number 2?
-/
def erdos_1022 : Prop :=
  ∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
  ∀ t, ∀ {α : Type*} [DecidableEq α] (F : Hypergraph α),
    (∀ A ∈ F, A.card ≥ t) →
    (∀ X : Finset α, X.Nonempty → (F.filter (λ A => A ⊆ X)).card < c t * (X.card : ℝ)) →
    TwoColorable F

/-
The negation of erdos_1022.
-/
theorem not_erdos_1022 : ¬ erdos_1022 := by
  -- Assume erdos_1022 is true.
  by_contra h_contra
  obtain ⟨c, hc_tendsto, hc_property⟩ := h_contra;
  -- By c_t_le_two, for all t >= 2, c_t <= 2.
  have h_c_t_le_two (t : ℕ) (ht : t ≥ 2) : c t ≤ 2 := by
    apply_rules [ c_t_le_two ];
    intro F hF hF';
    convert hc_property t ( F.image ( fun x : Finset ( Vert t ) => x.image ( fun y : Vert t => ULift.up y ) ) ) _ _ using 1;
    · constructor <;> rintro ⟨ c, hc ⟩;
      · use fun x => c x.down;
        simp +zetaDelta at *;
        exact hc;
      · use fun x => c ⟨ x ⟩;
        intro A hA; specialize hc ( A.image ( fun y => ULift.up y ) ) ( Finset.mem_image_of_mem _ hA ) ; aesop;
    · simp +zetaDelta at *;
      exact fun A hA => by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ; exact hF A hA;
    · intro X hX;
      convert hF' ( X.image ( fun x => x.down ) ) _ using 1;
      · refine' congr_arg _ ( Finset.card_bij _ _ _ _ );
        use fun a ha => a.image ( fun x => x.down );
        · simp +contextual [ Finset.subset_iff ];
          intro A hA hA'; convert hA using 1; ext; aesop;
        · simp +contextual [ Finset.ext_iff ];
        · simp +decide [ Finset.subset_iff ];
          exact fun b hb hb' => ⟨ _, ⟨ ⟨ b, hb, rfl ⟩, fun x hx => by aesop ⟩, by aesop ⟩;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
      · exact ⟨ _, Finset.mem_image_of_mem _ hX.choose_spec ⟩;
  exact absurd ( hc_tendsto.eventually_gt_atTop 2 ) fun h => by have := h.and ( Filter.eventually_ge_atTop 2 ) ; obtain ⟨ t, ht₁, ht₂ ⟩ := this.exists; linarith [ h_c_t_le_two t ht₂ ] ;

#print axioms not_erdos_1022
-- 'not_erdos_1022' depends on axioms: [propext, Classical.choice, Quot.sound]
