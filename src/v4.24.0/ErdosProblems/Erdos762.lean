/-

This is a Lean formalization of a solution to Erdős Problem 762.
https://www.erdosproblems.com/forum/thread/762

The original proof was found by: Steiner

[St24b] R. Steiner, On the difference between the chromatic and
cochromatic number. arXiv:2408.02400 (2024).


The proof was auto-formalized by Aristotle (from Harmonic) and ChatGPT
(from OpenAI).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formally proven that the graph G constructed from H satisfies the following properties:
1. The clique number of G is less than 5 (ω(G) < 5).
2. The cochromatic number of G is 4 (ζ(G) = 4).
3. The chromatic number of G is 7 (χ(G) = 7).

This confirms the theorem statement provided by the user. The proof relies on the properties of the graph H and the construction of G, specifically utilizing the fact that H is not 3-cochromatic-colorable and has specific clique and independent set covering properties.
-/

/-
We define the graph $H$ and prove that it has clique number less than 5, can be partitioned into 3 cliques, and for every proper 6-coloring, there exists a rainbow set $X$ with clique number less than 4.

The main result is `lemma_aux`, which combines:
1. `lemma_clique_free_5`: Proves $\omega(H) < 5$.
2. `lemma_partition_3_cliques`: Proves $V(H)$ can be partitioned into 3 cliques.
3. `lemma_rainbow_clique_free`: Proves that for every proper 6-coloring, there is a rainbow set $X$ with $\omega(H[X]) < 4$.

The proof of `lemma_rainbow_clique_free` relies on the structure of $H$ (two $C_5$'s connected to each other and to a central vertex $c$) and the properties of $C_5$ colorings (specifically `obs_obvious`). We split the proof into two cases based on whether the color of $c$ belongs to the set of colors used by the first $C_5$ ($A$) or the second $C_5$ ($B$).
-/

import Mathlib

namespace Erdos762

set_option linter.mathlibStandardSet false

set_option maxHeartbeats 0

open scoped Classical

inductive H_V
| a (i : Fin 5)
| b (i : Fin 5)
| c
deriving DecidableEq, Fintype

def H : SimpleGraph H_V :=
  SimpleGraph.fromRel
    (fun u v => match u, v with
      | H_V.a i, H_V.a j => (SimpleGraph.cycleGraph 5).Adj i j
      | H_V.b i, H_V.b j => (SimpleGraph.cycleGraph 5).Adj i j
      | H_V.a _, H_V.b _ => True
      | H_V.b _, H_V.a _ => True
      | H_V.c, H_V.a 0 => True
      | H_V.a 0, H_V.c => True
      | H_V.c, H_V.b 0 => True
      | H_V.b 0, H_V.c => True
      | _, _ => False)

set_option maxRecDepth 40000 in
/-
For every proper $3$-coloring $c$ of $C_5$ and for every $i \in \{1,2,3\}$, there exist two non-adjacent vertices $a,b$ on $C_5$ such that $\{c(a),c(b)\}=\{1,2,3\}\setminus \{i\}$.
-/
theorem obs_obvious (c : (SimpleGraph.cycleGraph 5).Coloring (Fin 3)) (i : Fin 3) :
    ∃ u v : Fin 5, ¬ (SimpleGraph.cycleGraph 5).Adj u v ∧ {c u, c v} = (Finset.univ.erase i) := by
  -- Let's examine the possible colorings of the cycle graph $C_5$ with $3$ colors.
  have h_colorings : ∀ (c : Fin 5 → Fin 3), (∀ u v : Fin 5, (SimpleGraph.cycleGraph 5).Adj u v → c u ≠ c v) → ∃ u v : Fin 5, ¬(SimpleGraph.cycleGraph 5).Adj u v ∧ c u ≠ c v ∧ c u ≠ i ∧ c v ≠ i := by
    decide +revert
  obtain ⟨ u, v, huv, hu, hv ⟩ := h_colorings ( fun x => c x ) ( fun u v huv => c.valid huv ) ; use u, v; simp_all +decide [ Finset.ext_iff ] ;
  grind

/-
The graph H does not contain a clique of size 5.
-/
theorem lemma_clique_free_5 : H.CliqueFree 5 := by
  -- By contradiction, assume there exists a clique $K$ of size 5 in $H$.
  by_contra h_contra;
  -- Let $K$ be a clique of size 5 in $H$.
  obtain ⟨K, hK⟩ : ∃ K : Finset H_V, K.card = 5 ∧ ∀ u v : H_V, u ∈ K → v ∈ K → u ≠ v → (SimpleGraph.fromRel (fun u v => match u, v with | H_V.a i, H_V.a j => (SimpleGraph.cycleGraph 5).Adj i j | H_V.b i, H_V.b j => (SimpleGraph.cycleGraph 5).Adj i j | H_V.a _, H_V.b _ => True | H_V.b _, H_V.a _ => True | H_V.c, H_V.a 0 => True | H_V.a 0, H_V.c => True | H_V.c, H_V.b 0 => True | H_V.b 0, H_V.c => True | _, _ => False)).Adj u v := by
    rw [ SimpleGraph.CliqueFree ] at h_contra;
    push_neg at h_contra;
    obtain ⟨ K, hK ⟩ := h_contra; use K; exact ⟨ hK.2, fun u v hu hv huv => hK.1 hu hv huv ⟩ ;
  -- Let $K_A = K \cap A$ and $K_B = K \cap B$.
  set KA := K.filter (fun u => u ∈ Finset.image (fun i => H_V.a i) (Finset.univ : Finset (Fin 5)))
  set KB := K.filter (fun u => u ∈ Finset.image (fun i => H_V.b i) (Finset.univ : Finset (Fin 5)));
  -- Since $A$ is a $C_5$, $\omega(A) = 2$. So $|K_A| \le 2$.
  have hKA : KA.card ≤ 2 := by
    -- Since $A$ is a $C_5$, $\omega(A) = 2$. So $|K_A| \le 2$. We can prove this by considering the possible subsets of $A$ that can form a clique.
    have hKA_subset : ∀ S : Finset (Fin 5), (∀ u v : Fin 5, u ∈ S → v ∈ S → u ≠ v → (SimpleGraph.cycleGraph 5).Adj u v) → S.card ≤ 2 := by
      simp +decide
    convert hKA_subset ( Finset.image ( fun u => u ) ( Finset.filter ( fun u => u ∈ Finset.image ( fun i => H_V.a i ) Finset.univ ) K |> Finset.image ( fun u => if h : ∃ i, u = H_V.a i then h.choose else 0 ) ) ) _ using 1;
    · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
      rw [ Finset.card_image_of_injOn ] ; intro u hu ; aesop;
    · simp +zetaDelta at *;
      intro u v x hx y hy hu z hz t ht hv huv; subst_vars; simp_all +decide [ SimpleGraph.cycleGraph ] ;
      grind;
  -- Since $B$ is a $C_5$, $\omega(B) = 2$. So $|K_B| \le 2$.
  have hKB : KB.card ≤ 2 := by
    -- Since $B$ is a $C_5$, $\omega(B) = 2$. So $|K_B| \le 2$ follows from the fact that any clique in $B$ can have at most 2 vertices.
    have hKB : ∀ (S : Finset (Fin 5)), (∀ u v : Fin 5, u ∈ S → v ∈ S → u ≠ v → (SimpleGraph.cycleGraph 5).Adj u v) → S.card ≤ 2 := by
      decide +revert;
    convert hKB ( Finset.image ( fun u => u ) ( Finset.filter ( fun u => u ∈ Finset.image ( fun i => H_V.b i ) Finset.univ ) K |> Finset.image ( fun u => if h : ∃ i, u = H_V.b i then Classical.choose h else 0 ) ) ) _ using 1;
    · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
      rw [ Finset.card_image_of_injOn ];
      intro u hu v hv; simp +decide [ Finset.mem_image ] at hu hv ⊢;
      split_ifs <;> simp_all +decide [ eq_comm ];
      exact fun h => by rw [ Classical.choose_spec ‹∃ i, u = H_V.b i›, Classical.choose_spec ‹∃ i, v = H_V.b i›, h ] ;
    · simp +zetaDelta at *;
      intro u v x hx y hy hu z hz t ht hv huv; subst_vars; simp_all +decide [ SimpleGraph.cycleGraph ] ;
      grind;
  -- Since $K$ is a clique of size 5, we have $|K| = |K_A| + |K_B| + |K_C|$, where $K_C = K \cap \{c\}$.
  have hKC : K.card = KA.card + KB.card + (K.filter (fun u => u = H_V.c)).card := by
    rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
    rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ];
    rw [ Finset.card_eq_sum_ones ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rcases x with ( _ | _ | _ ) <;> simp +decide ;
  simp_all +decide [ Finset.filter_eq' ];
  split_ifs at hK <;> simp_all +decide;
  · -- Since $|K_A| = 2$ and $|K_B| = 2$, we have $K_A = \{a_i, a_j\}$ and $K_B = \{b_k, b_l\}$ for some $i, j, k, l$.
    obtain ⟨i, j, hij, hi, hj⟩ : ∃ i j : Fin 5, i ≠ j ∧ H_V.a i ∈ K ∧ H_V.a j ∈ K := by
      have hKA_card : KA.card = 2 := by
        linarith;
      rw [ Finset.card_eq_two ] at hKA_card;
      obtain ⟨ x, y, hxy, h ⟩ := hKA_card; simp_all +decide [ Finset.ext_iff ] ;
      simp +zetaDelta at *;
      rcases h x |>.2 ( Or.inl rfl ) with ⟨ hx₁, i, rfl ⟩ ; rcases h y |>.2 ( Or.inr rfl ) with ⟨ hy₁, j, rfl ⟩ ; use i, j ; aesop
    obtain ⟨k, l, hkl, hk, hl⟩ : ∃ k l : Fin 5, k ≠ l ∧ H_V.b k ∈ K ∧ H_V.b l ∈ K := by
      grind;
    grind;
  · linarith

/-
The vertex set of H can be partitioned into 3 cliques.
-/
theorem lemma_partition_3_cliques :
    ∃ (s1 s2 s3 : Set H_V), s1 ∪ s2 ∪ s3 = Set.univ ∧ H.IsClique s1 ∧ H.IsClique s2 ∧ H.IsClique s3 := by
  -- Define the cliques $s1$, $s2$, and $s3$ as follows:
  use ({.a 0, .b 0, .c} : Set H_V), ({.a 1, .a 2, .b 1, .b 2} : Set H_V), ({.a 3, .a 4, .b 3, .b 4} : Set H_V);
  simp +decide [ Set.ext_iff, H ]

/-
In any proper 6-coloring of H, the colors used on A and B are disjoint and each set has size 3.
-/
def A_V : Set H_V := { v | ∃ i, v = H_V.a i }

def B_V : Set H_V := { v | ∃ i, v = H_V.b i }

theorem lemma_colors_structure (col : H.Coloring (Fin 6)) :
    Disjoint (Finset.image col (A_V.toFinset)) (Finset.image col (B_V.toFinset)) ∧
    (Finset.image col (A_V.toFinset)).card = 3 ∧
    (Finset.image col (B_V.toFinset)).card = 3 := by
  -- Since $A$ contains a 5-cycle, we need at least 3 colors for $A$.
  have hA_card : 3 ≤ (Finset.image (fun x => col x) (Finset.filter (fun v => v ∈ A_V) Finset.univ)).card := by
    -- Since $A$ contains a 5-cycle, we need at least 3 colors for $A$. Let's denote the vertices of this cycle by $v_0, v_1, v_2, v_3, v_4$.
    obtain ⟨v0, v1, v2, v3, v4, hv⟩ : ∃ v0 v1 v2 v3 v4 : H_V, v0 ∈ A_V ∧ v1 ∈ A_V ∧ v2 ∈ A_V ∧ v3 ∈ A_V ∧ v4 ∈ A_V ∧ (H.Adj v0 v1) ∧ (H.Adj v1 v2) ∧ (H.Adj v2 v3) ∧ (H.Adj v3 v4) ∧ (H.Adj v4 v0) := by
      existsi H_V.a 0, H_V.a 1, H_V.a 2, H_V.a 3, H_V.a 4;
      simp +decide [ A_V ];
      unfold H; simp +decide [ SimpleGraph.cycleGraph ] ;
    -- Since $v_0, v_1, v_2, v_3, v_4$ form a 5-cycle, they must all have different colors.
    have h_diff_colors : col v0 ≠ col v1 ∧ col v1 ≠ col v2 ∧ col v2 ≠ col v3 ∧ col v3 ≠ col v4 ∧ col v4 ≠ col v0 := by
      exact ⟨ col.valid hv.2.2.2.2.2.1, col.valid hv.2.2.2.2.2.2.1, col.valid hv.2.2.2.2.2.2.2.1, col.valid hv.2.2.2.2.2.2.2.2.1, col.valid hv.2.2.2.2.2.2.2.2.2 ⟩;
    have h_diff_colors : Finset.card ({col v0, col v1, col v2, col v3, col v4} : Finset (Fin 6)) ≥ 3 := by
      grind;
    exact h_diff_colors.trans ( Finset.card_mono <| by aesop_cat );
  -- Since $B$ contains a 5-cycle, we need at least 3 colors for $B$.
  have hB_card : 3 ≤ (Finset.image (fun x => col x) (Finset.filter (fun v => v ∈ B_V) Finset.univ)).card := by
    -- Since $B$ contains a 5-cycle, we need at least 3 colors for $B$. This follows from the fact that the chromatic number of a 5-cycle is 3.
    have hB_cycle : ∀ (col : (SimpleGraph.cycleGraph 5).Coloring (Fin 6)), 3 ≤ (Finset.image (fun x => col x) (Finset.univ : Finset (Fin 5))).card := by
      intro col
      by_contra h_contra
      have h_card : (Finset.image (fun x => col x) (Finset.univ : Finset (Fin 5))).card ≤ 2 := by
        grind;
      have h_card : ∃ c1 c2 : Fin 6, c1 ≠ c2 ∧ ∀ x : Fin 5, col x = c1 ∨ col x = c2 := by
        interval_cases _ : Finset.card ( Finset.image ( fun x => col x ) Finset.univ ) <;> simp_all +decide [ Finset.card_eq_one, Finset.card_eq_two ];
        · obtain ⟨ a, ha ⟩ := ‹_›; use a, a + 1; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
        · rcases ‹_› with ⟨ c1, c2, hne, heq ⟩ ; exact ⟨ c1, c2, hne, fun x => by simpa using Finset.ext_iff.mp heq ( col x ) ⟩ ;
      obtain ⟨ c1, c2, hne, h ⟩ := h_card; have := col.valid ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 5 ) 0 1 from by decide ) ; have := col.valid ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 5 ) 1 2 from by decide ) ; have := col.valid ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 5 ) 2 3 from by decide ) ; have := col.valid ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 5 ) 3 4 from by decide ) ; have := col.valid ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 5 ) 4 0 from by decide ) ; simp_all +decide ;
      cases h 0 <;> cases h 1 <;> cases h 2 <;> cases h 3 <;> cases h 4 <;> simp_all ( config := { decide := Bool.true } ) only [ ];
    convert hB_cycle ( SimpleGraph.Coloring.mk ?_ ?_ ) using 1;
    rotate_left;
    exact fun x => col ( H_V.b x );
    intro v w hvw; have := col.valid ( show H.Adj ( H_V.b v ) ( H_V.b w ) from ?_ ) ; simp_all +decide
    all_goals norm_num [ H ];
    decide +revert;
    congr! 1;
    ext; simp [B_V];
    exact ⟨ fun ⟨ a, ⟨ i, hi ⟩, hi' ⟩ => ⟨ i, by simpa [ hi ] using hi' ⟩, fun ⟨ i, hi ⟩ => ⟨ _, ⟨ i, rfl ⟩, hi ⟩ ⟩;
  -- Since $A$ and $B$ are disjoint, their images under $col$ are also disjoint.
  have h_disjoint : Disjoint (Finset.image (fun x => col x) (Finset.filter (fun v => v ∈ A_V) Finset.univ)) (Finset.image (fun x => col x) (Finset.filter (fun v => v ∈ B_V) Finset.univ)) := by
    simp +contextual [ Finset.disjoint_left ];
    intro a ha b hb; have := col.valid ( show H.Adj a b from ?_ ) ; aesop;
    rcases ha with ⟨ i, rfl ⟩ ; rcases hb with ⟨ j, rfl ⟩ ; simp +decide [ H ] ;
  have h_card_union : (Finset.image (fun x => col x) (Finset.filter (fun v => v ∈ A_V) Finset.univ)).card + (Finset.image (fun x => col x) (Finset.filter (fun v => v ∈ B_V) Finset.univ)).card ≤ 6 := by
    rw [ ← Finset.card_union_of_disjoint h_disjoint ] ; exact Finset.card_le_univ _;
  exact ⟨ by simpa [ Finset.disjoint_left ] using h_disjoint, by linarith! [ show Finset.card ( Finset.image ( fun x => col x ) A_V.toFinset ) = Finset.card ( Finset.image ( fun x => col x ) { v : H_V | v ∈ A_V } ) by congr; ext; aesop ], by linarith! [ show Finset.card ( Finset.image ( fun x => col x ) B_V.toFinset ) = Finset.card ( Finset.image ( fun x => col x ) { v : H_V | v ∈ B_V } ) by congr; ext; aesop ] ⟩

def A_Finset : Finset H_V := Finset.image H_V.a Finset.univ

def B_Finset : Finset H_V := Finset.image H_V.b Finset.univ

/-
Lifted observation for A.
-/
theorem lemma_obs_obvious_lifted (col : H.Coloring (Fin 6))
    (h_card : (Finset.image col A_Finset).card = 3)
    (k : Fin 6) (hk : k ∈ Finset.image col A_Finset) :
    ∃ u v : H_V, u ∈ A_Finset ∧ v ∈ A_Finset ∧ ¬ H.Adj u v ∧
    {col u, col v} = (Finset.image col A_Finset).erase k := by
  -- Since $A$ induces a 5-cycle, any proper $3$-coloring of $A$ must have two non-adjacent vertices whose colors are $\{0, 1, 2\} \setminus \{0\}$.
  have h_cycle : ∀ (c : (SimpleGraph.cycleGraph 5).Coloring (Fin 3)), ∃ u v : Fin 5, ¬(SimpleGraph.cycleGraph 5).Adj u v ∧ ({c u, c v} : Finset (Fin 3)) = Finset.univ.erase 0 := by
    exact fun c => obs_obvious c 0;
  -- Let $y : Fin 6 → Fin 3$ be the function that maps each color in $m_k$ to a unique color in $\{0,1,2\}$.
  obtain ⟨y, hy⟩ : ∃ y : Fin 6 → Fin 3, y k = 0 ∧ (∀ c ∈ Finset.image col A_Finset, c ≠ k → y c ≠ 0) ∧ (∀ c d : Fin 6, c ∈ Finset.image col A_Finset → d ∈ Finset.image col A_Finset → c ≠ d → y c ≠ y d) := by
    -- Since there are exactly 3 colors in the image of col on A_Finset and k is one of them, there are exactly 2 other colors.
    obtain ⟨c1, c2, hc⟩ : ∃ c1 c2 : Fin 6, c1 ≠ k ∧ c2 ≠ k ∧ c1 ≠ c2 ∧ Finset.image col A_Finset = {k, c1, c2} := by
      have h_card : Finset.card (Finset.image col A_Finset \ {k}) = 2 := by
        grind;
      obtain ⟨ c1, c2, hc ⟩ := Finset.card_eq_two.mp h_card;
      grind;
    use fun x => if x = k then 0 else if x = c1 then 1 else 2;
    grind +ring;
  -- Applying the hypothesis `h_cycle` to the coloring `y ∘ col` restricted to `A`.
  obtain ⟨u, v, huv⟩ : ∃ u v : Fin 5, ¬(SimpleGraph.cycleGraph 5).Adj u v ∧ ({(y ∘ col) (H_V.a u), (y ∘ col) (H_V.a v)} : Finset (Fin 3)) = Finset.univ.erase 0 := by
    convert h_cycle _;
    rotate_right;
    use fun i => y ( col ( H_V.a i ) );
    all_goals simp +decide [ SimpleGraph.cycleGraph ];
    intro a b hab h; specialize hy; have := hy.2.2 ( col ( H_V.a a ) ) ( col ( H_V.a b ) ) ; simp_all +decide [ Finset.mem_image ] ;
    exact this _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) rfl _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) rfl ( by intro t; have := col.valid ( show H.Adj ( H_V.a a ) ( H_V.a b ) from by fin_cases a <;> fin_cases b <;> trivial ) ; aesop );
  -- Since $y$ is injective on the image of $col$ restricted to $A$, we have $col (H_V.a u) \neq col (H_V.a v)$ and $col (H_V.a u), col (H_V.a v) \neq k$.
  have h_distinct : col (H_V.a u) ≠ col (H_V.a v) ∧ col (H_V.a u) ≠ k ∧ col (H_V.a v) ≠ k := by
    simp_all +decide [ Finset.ext_iff ];
    refine' ⟨ _, _, _ ⟩ <;> contrapose! hy;
    · have := huv.2 0; have := huv.2 1; have := huv.2 2; simp_all +decide [ Fin.forall_fin_succ ] ;
      grind +ring;
    · intro hy' hy''; specialize huv; have := huv.2 0; simp_all +decide ;
    · intro hy₀ hy₁; specialize huv; have := huv.2 0; simp_all +decide ;
  refine' ⟨ H_V.a u, H_V.a v, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  · exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
  · exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
  · simp_all +decide [ H ];
    exact fun h => by rw [ SimpleGraph.adj_comm ] ; exact huv.1;
  · intro a; specialize huv; have := Finset.eq_of_subset_of_card_le ( show { col ( H_V.a u ), col ( H_V.a v ), k } ⊆ Finset.image col A_Finset from ?_ ) ; simp_all +decide ;
    · replace this := Finset.ext_iff.mp this a; aesop;
    · simp_all +decide [ Finset.subset_iff ];
      exact ⟨ ⟨ H_V.a u, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), rfl ⟩, ⟨ H_V.a v, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ), rfl ⟩ ⟩

/-
Coverage lemma for B.
-/
theorem lemma_B_cover (col : H.Coloring (Fin 6))
    (h_card : (Finset.image col B_Finset).card = 3) :
    ∃ w1 w2 w3 : H_V, w1 ∈ B_Finset ∧ w2 ∈ B_Finset ∧ w3 ∈ B_Finset ∧
    {col w1, col w2, col w3} = Finset.image col B_Finset := by
  rcases Finset.card_eq_three.mp h_card with ⟨ x, y, z, hx, hy, hz, h ⟩;
  simp_all +decide [ Finset.ext_iff ];
  obtain ⟨ w1, hw1, hw1' ⟩ := h x |>.2 ( Or.inl rfl ) ; obtain ⟨ w2, hw2, hw2' ⟩ := h y |>.2 ( Or.inr ( Or.inl rfl ) ) ; obtain ⟨ w3, hw3, hw3' ⟩ := h z |>.2 ( Or.inr ( Or.inr rfl ) ) ; use w1, hw1, w2, hw2, w3, hw3; aesop;

/-
Coverage lemma for A.
-/
theorem lemma_A_cover (col : H.Coloring (Fin 6))
    (h_card : (Finset.image col A_Finset).card = 3) :
    ∃ w1 w2 w3 : H_V, w1 ∈ A_Finset ∧ w2 ∈ A_Finset ∧ w3 ∈ A_Finset ∧
    {col w1, col w2, col w3} = Finset.image col A_Finset := by
  rcases Finset.card_eq_three.mp h_card with ⟨ x, y, z, hx, hy, hz, h ⟩;
  simp_all +decide [ Finset.ext_iff ];
  obtain ⟨ w1, hw1, hw1' ⟩ := h x |>.2 ( Or.inl rfl ) ; obtain ⟨ w2, hw2, hw2' ⟩ := h y |>.2 ( Or.inr ( Or.inl rfl ) ) ; obtain ⟨ w3, hw3, hw3' ⟩ := h z |>.2 ( Or.inr ( Or.inr rfl ) ) ; use w1, hw1, w2, hw2, w3, hw3; aesop;

/-
Lifted observation for B.
-/
theorem lemma_obs_obvious_lifted_B (col : H.Coloring (Fin 6))
    (h_card : (Finset.image col B_Finset).card = 3)
    (k : Fin 6) (hk : k ∈ Finset.image col B_Finset) :
    ∃ u v : H_V, u ∈ B_Finset ∧ v ∈ B_Finset ∧ ¬ H.Adj u v ∧
    {col u, col v} = (Finset.image col B_Finset).erase k := by
      norm_num +zetaDelta at *;
      obtain ⟨ u, hu, rfl ⟩ := hk;
      -- Since $B_Finset$ is isomorphic to $C_5$, we can apply the observation to the restriction of $col$ to $B_Finset$.
      obtain ⟨u', hu'⟩ : ∃ u' ∈ Finset.univ, col (H_V.b u') = col u := by
        unfold B_Finset at hu; aesop;
      -- By the observation, there exist two non-adjacent vertices $v'$ and $w'$ in $C_5$ such that $\{c(v'), c(w')\} = \{1, 2, 3\} \setminus \{c(u')\}$.
      obtain ⟨v', w', hv', hw', h_adj⟩ : ∃ v' w' : Fin 5, v' ≠ w' ∧ ¬(SimpleGraph.cycleGraph 5).Adj v' w' ∧ {col (H_V.b v'), col (H_V.b w')} = (Finset.image (fun i => col (H_V.b i)) (Finset.univ : Finset (Fin 5))).erase (col (H_V.b u')) := by
        have h_obs : ∀ (c : Fin 5 → Fin 6), (∀ i j, (SimpleGraph.cycleGraph 5).Adj i j → c i ≠ c j) → (Finset.image c (Finset.univ : Finset (Fin 5))).card = 3 → ∀ (k : Fin 5), ∃ v' w' : Fin 5, v' ≠ w' ∧ ¬(SimpleGraph.cycleGraph 5).Adj v' w' ∧ {c v', c w'} = (Finset.image c (Finset.univ : Finset (Fin 5))).erase (c k) := by
          native_decide
        apply h_obs;
        · intro i j hij; have := col.valid ( show H.Adj ( H_V.b i ) ( H_V.b j ) from ?_ ) ; aesop;
          fin_cases i <;> fin_cases j <;> simp +decide at hij ⊢;
          all_goals unfold H; simp +decide [ SimpleGraph.cycleGraph ] ;
        · convert h_card using 2;
      refine' ⟨ H_V.b v', _, H_V.b w', _, _, _ ⟩ <;> simp_all +decide [ H ];
      · exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
      · exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
      · exact fun h => hw' <| by simpa [ SimpleGraph.adj_comm ] using h;
      · congr! 1

theorem lemma_sets_eq : A_Finset = A_V.toFinset ∧ B_Finset = B_V.toFinset := by
  constructor <;> ext x <;> simp [A_Finset, B_Finset, A_V, B_V] <;> aesop

/-
Auxiliary lemma for Case A structure.
-/
theorem lemma_clique_free_structure_A_aux (u v w1 w2 w3 : H_V)
    (hu : u ∈ A_Finset) (hv : v ∈ A_Finset)
    (hw1 : w1 ∈ B_Finset) (hw2 : w2 ∈ B_Finset) (hw3 : w3 ∈ B_Finset)
    (huv : ¬ H.Adj u v)
    (S : Finset H_V)
    (hS_subset : S ⊆ {H_V.c, u, v, w1, w2, w3})
    (hS_clique : H.IsClique S) :
    S.card ≤ 3 := by
  -- Since $S$ is a clique and $u, v \in A$, if $c \in S$, then $S \subseteq \{a_0, b_0\}$.
  have h_case_c : H_V.c ∈ S → S ⊆ {H_V.c, H_V.a 0, H_V.b 0} := by
    intro hc hS;
    intro hhS; have := hS_clique hhS hc; simp_all +decide [ H ] ;
    grind;
  by_cases hc : H_V.c ∈ S <;> simp_all +decide [ Finset.subset_iff ];
  · exact le_trans ( Finset.card_le_card ( show S ⊆ { H_V.c, H_V.a 0, H_V.b 0 } by intros x hx; simpa using h_case_c hx ) ) ( Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _ );
  · -- Since $S$ is a subset of $\{u, v, w1, w2, w3\}$ and $u$ and $v$ are not adjacent, $S$ can contain at most one of $u$ and $v$.
    have h_case_u_v : S.card ≤ 1 + Finset.card (S ∩ {w1, w2, w3}) := by
      have h_case_u_v : Finset.card (S ∩ {u, v}) ≤ 1 := by
        exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => huv <| hS_clique ( by aesop ) ( by aesop ) <| by aesop;
      have h_case_u_v : S.card ≤ Finset.card (S ∩ {u, v}) + Finset.card (S ∩ {w1, w2, w3}) := by
        rw [ ← Finset.card_union_add_card_inter ];
        exact le_add_right ( Finset.card_le_card fun x hx => by specialize hS_subset hx; aesop );
      linarith;
    have h_case_w : Finset.card (S ∩ {w1, w2, w3}) ≤ 2 := by
      have h_case_w : ∀ x y z : H_V, x ∈ B_Finset → y ∈ B_Finset → z ∈ B_Finset → x ≠ y → x ≠ z → y ≠ z → ¬(H.Adj x y ∧ H.Adj x z ∧ H.Adj y z) := by
        simp +decide [ B_Finset ];
        rintro x y z i rfl j rfl k rfl hij hik hjk; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp +decide at hij hik hjk ⊢;
        all_goals simp +decide [ H ] ;
      contrapose! h_case_w;
      obtain ⟨ x, hx, y, hy, z, hz, hxyz ⟩ := Finset.two_lt_card.mp h_case_w; use x, y, z; aesop;
    linarith

/-
Case A of the rainbow clique free lemma.
-/
theorem lemma_rainbow_clique_free_case_A (col : H.Coloring (Fin 6))
    (hA_card : (Finset.image col A_Finset).card = 3)
    (hB_card : (Finset.image col B_Finset).card = 3)
    (k : Fin 6) (hk : k = col H_V.c)
    (hk_in_A : k ∈ Finset.image col A_Finset)
    (h_union : Finset.image col A_Finset ∪ Finset.image col B_Finset = Finset.univ) :
    ∃ X : Finset H_V, (H.induce X).CliqueFree 4 ∧ (Finset.image col X) = Finset.univ := by
      -- By `lemma_obs_obvious_lifted`, there exist `u, v \in A` such that `u \not\sim v` and `{col u, col v} = col(A) \setminus \{k\}$.
      obtain ⟨u, v, huA, hvA, huv_not_adj, huv_colors⟩ : ∃ u v : H_V, u ∈ A_Finset ∧ v ∈ A_Finset ∧ ¬ H.Adj u v ∧ ({col u, col v} : Finset (Fin 6)) = (Finset.image col A_Finset).erase k := by
        convert lemma_obs_obvious_lifted col hA_card k hk_in_A using 1;
      -- By `lemma_B_cover`, there exist `w1, w2, w3 \in B` such that `{col w1, col w2, col w3} = col(B)$.
      obtain ⟨w1, w2, w3, hw1B, hw2B, hw3B, hw_colors⟩ : ∃ w1 w2 w3 : H_V, w1 ∈ B_Finset ∧ w2 ∈ B_Finset ∧ w3 ∈ B_Finset ∧ ({col w1, col w2, col w3} : Finset (Fin 6)) = Finset.image col B_Finset := by
        exact lemma_B_cover col hB_card;
      refine' ⟨ { H_V.c, u, v, w1, w2, w3 }, _, _ ⟩;
      · -- By `lemma_clique_free_structure_A_aux`, any clique in $X$ has size at most 3.
        have h_clique_size : ∀ S : Finset H_V, S ⊆ {H_V.c, u, v, w1, w2, w3} → H.IsClique S → S.card ≤ 3 := by
          intros S hS_subset hS_clique;
          convert lemma_clique_free_structure_A_aux u v w1 w2 w3 huA hvA hw1B hw2B hw3B huv_not_adj S hS_subset hS_clique using 1;
        intro S hS;
        convert h_clique_size ( Finset.image ( fun x : { x : H_V // x ∈ ( { H_V.c, u, v, w1, w2, w3 } : Finset H_V ) } => x.val ) S ) ?_ ?_ using 1;
        · rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; simp +decide [ hS.card_eq ];
        · exact Finset.image_subset_iff.mpr fun x hx => x.2;
        · intro x hx y hy hxy; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          have := hS.1 hx.2 hy.2; aesop;
      · simp +decide [ Finset.ext_iff ] at *;
        intro a; specialize h_union a; specialize huv_colors a; specialize hw_colors a; by_cases ha : a = k <;> aesop;

/-
Auxiliary lemma for Case B structure.
-/
theorem lemma_clique_free_structure_B_aux (u v w1 w2 w3 : H_V)
    (hu : u ∈ B_Finset) (hv : v ∈ B_Finset)
    (hw1 : w1 ∈ A_Finset) (hw2 : w2 ∈ A_Finset) (hw3 : w3 ∈ A_Finset)
    (huv : ¬ H.Adj u v)
    (S : Finset H_V)
    (hS_subset : S ⊆ {H_V.c, u, v, w1, w2, w3})
    (hS_clique : H.IsClique S) :
    S.card ≤ 3 := by
  by_cases hc : H_V.c ∈ S <;> simp_all +decide [ SimpleGraph.IsClique ];
  · -- By definition of $N(c)$, $S \setminus \{c\} \subseteq N(c) = \{a_0, b_0\}$.
    have hS_minus_c_subset_Nc : S \ {H_V.c} ⊆ {H_V.a 0, H_V.b 0} := by
      have hS_minus_c_subset_Nc : ∀ x ∈ S \ {H_V.c}, H.Adj H_V.c x := by
        exact fun x hx => hS_clique hc ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop );
      intro x hx; specialize hS_minus_c_subset_Nc x hx; rcases x with ( _ | _ | _ ) <;> simp_all +decide ;
      · cases hS_minus_c_subset_Nc ; aesop;
      · cases hS_minus_c_subset_Nc ; aesop;
    have := Finset.card_le_card hS_minus_c_subset_Nc; simp_all +decide ;
    grind;
  · -- Since $S \subseteq \{u, v\} \cup \{w_1, w_2, w_3\}$ and $u \not\sim v$, we have $|S \cap \{u, v\}| \leq 1$ and $|S \cap \{w_1, w_2, w_3\}| \leq 2$.
    have hS_inter_u_v : (S ∩ {u, v}).card ≤ 1 := by
      exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => huv <| hS_clique ( by aesop ) ( by aesop ) <| by aesop;
    have hS_inter_w : (S ∩ {w1, w2, w3}).card ≤ 2 := by
      by_contra h_contra;
      -- Since $S \cap \{w_1, w_2, w_3\}$ has more than 2 elements, it must contain all three elements $w_1$, $w_2$, and $w_3$.
      have hS_inter_w_all : w1 ∈ S ∧ w2 ∈ S ∧ w3 ∈ S := by
        have hS_inter_w_all : (S ∩ {w1, w2, w3}).card = 3 := by
          exact le_antisymm ( Finset.card_le_card ( Finset.inter_subset_right ) |> le_trans <| by exact Finset.card_insert_le _ _ |> le_trans <| add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ( not_le.mp h_contra );
        have := Finset.eq_of_subset_of_card_le ( show S ∩ { w1, w2, w3 } ⊆ { w1, w2, w3 } from Finset.inter_subset_right ) ; simp_all +decide ;
        exact ⟨ this ( by exact le_trans ( Finset.card_insert_le _ _ ) ( add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ) ( by simp +decide ), this ( by exact le_trans ( Finset.card_insert_le _ _ ) ( add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ) ( by simp +decide ), this ( by exact le_trans ( Finset.card_insert_le _ _ ) ( add_le_add_right ( Finset.card_insert_le _ _ ) _ ) ) ( by simp +decide ) ⟩;
      have := hS_clique hS_inter_w_all.1 hS_inter_w_all.2.1; have := hS_clique hS_inter_w_all.1 hS_inter_w_all.2.2; have := hS_clique hS_inter_w_all.2.1 hS_inter_w_all.2.2; simp_all +decide ;
      rcases w1 with ( _ | _ | w1 ) <;> rcases w2 with ( _ | _ | w2 ) <;> rcases w3 with ( _ | _ | w3 ) <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
      all_goals simp_all +decide [ A_Finset, B_Finset ] ;
      rename_i i j k; simp_all +decide [ H ] ;
      rename_i i' i''; fin_cases i' <;> fin_cases i'' <;> fin_cases i <;> simp +decide at h_contra this k j ⊢;
    have hS_inter_union : S = (S ∩ {u, v}) ∪ (S ∩ {w1, w2, w3}) := by
      grind;
    grind

/-
Case B of the rainbow clique free lemma.
-/
theorem lemma_rainbow_clique_free_case_B (col : H.Coloring (Fin 6))
    (hA_card : (Finset.image col A_Finset).card = 3)
    (hB_card : (Finset.image col B_Finset).card = 3)
    (k : Fin 6) (hk : k = col H_V.c)
    (hk_in_B : k ∈ Finset.image col B_Finset)
    (h_union : Finset.image col A_Finset ∪ Finset.image col B_Finset = Finset.univ) :
    ∃ X : Finset H_V, (H.induce X).CliqueFree 4 ∧ (Finset.image col X) = Finset.univ := by
      -- Use `lemma_A_cover` to get `w1, w2, w3 \in A` such that `{col w1, col w2, col w3} = col(A)`.
      obtain ⟨w1, w2, w3, hw1, hw2, hw3, hw⟩ : ∃ w1 w2 w3 : H_V, w1 ∈ A_Finset ∧ w2 ∈ A_Finset ∧ w3 ∈ A_Finset ∧ {col w1, col w2, col w3} = Finset.image col A_Finset := by
        convert lemma_A_cover col hA_card using 1;
      -- Use `lemma_obs_obvious_lifted_B` to get `u, v \in B` such that `u \not\sim v` and `{col u, col v} = col(B) \setminus \{k\}$.
      obtain ⟨u, v, hu, hv, huv, h_u_v⟩ : ∃ u v : H_V, u ∈ B_Finset ∧ v ∈ B_Finset ∧ ¬H.Adj u v ∧ {col u, col v} = (Finset.image col B_Finset).erase (col H_V.c) := by
        have := lemma_obs_obvious_lifted_B col hB_card ( col H_V.c ) ( by aesop ) ; aesop;
      refine' ⟨ { H_V.c, u, v, w1, w2, w3 }, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.CliqueFree ];
      · intro t ht; have := ht.card_eq; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
        -- Since $t$ is a clique in the induced subgraph, it must be a subset of $\{H_V.c, u, v, w1, w2, w3\}$.
        have ht_subset : t.image Subtype.val ⊆ {H_V.c, u, v, w1, w2, w3} := by
          exact Finset.image_subset_iff.mpr fun x hx => x.2;
        -- Since $t$ is a clique in the induced subgraph, it must be a subset of $\{H_V.c, u, v, w1, w2, w3\}$ and have cardinality 4.
        have ht_card : (Finset.image Subtype.val t).card = 4 := by
          rwa [ Finset.card_image_of_injective _ Subtype.coe_injective ];
        have := lemma_clique_free_structure_B_aux u v w1 w2 w3 hu hv hw1 hw2 hw3 huv ( Finset.image Subtype.val t ) ht_subset ( by
          intro x hx y hy hxy; simp_all +decide [ SimpleGraph.IsClique ] ;
          obtain ⟨ hx₁, hx₂ ⟩ := hx; obtain ⟨ hy₁, hy₂ ⟩ := hy; specialize ht hx₂ hy₂; aesop; ) ; simp_all +decide ;
      · simp_all +decide [ ← h_union, Finset.ext_iff ];
        intro a; specialize h_u_v a; specialize hw a; by_cases ha : a = col H_V.c <;> aesop;

/-
For every proper 6-coloring of H, there is a rainbow set X with clique number < 4.
-/
theorem lemma_rainbow_clique_free (col : H.Coloring (Fin 6)) :
    ∃ X : Finset H_V, (H.induce X).CliqueFree 4 ∧ (Finset.image col X) = Finset.univ := by
      -- By Lemma~\ref{lem:colors_structure}, we know that $(Finset.image col A_Finset).card = 3$ and $(Finset.image col B_Finset).card = 3$.
      have hA_card : (Finset.image col A_Finset).card = 3 := by
        convert lemma_colors_structure col |>.2.1;
        exact lemma_sets_eq.1
      have hB_card : (Finset.image col B_Finset).card = 3 := by
        convert lemma_colors_structure col |>.2.2;
        ext; simp [B_Finset, B_V];
        simp +decide only [eq_comm];
      -- By Lemma~\ref{lem:colors_structure}, we know that the union of the images of $A_Finset$ and $B_Finset$ is the universal set.
      have h_union : (Finset.image col A_Finset) ∪ (Finset.image col B_Finset) = Finset.univ := by
        refine' Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) _ ; simp_all +decide
        have h_union : Disjoint (Finset.image col A_Finset) (Finset.image col B_Finset) := by
          convert lemma_colors_structure col |>.1 using 1;
          · ext; simp [A_Finset, A_V];
            exact ⟨ fun ⟨ i, hi ⟩ => ⟨ _, ⟨ i, rfl ⟩, hi ⟩, by rintro ⟨ a, ⟨ i, rfl ⟩, hi ⟩ ; exact ⟨ i, hi ⟩ ⟩;
          · unfold B_Finset B_V; aesop;
        have h_union_card : (Finset.image col A_Finset ∪ Finset.image col B_Finset).card = (Finset.image col A_Finset).card + (Finset.image col B_Finset).card := by
          exact Finset.card_union_of_disjoint h_union
        rw [h_union_card, hA_card, hB_card];
      by_cases hk_in_A : col H_V.c ∈ Finset.image col A_Finset;
      · exact
        lemma_rainbow_clique_free_case_A col hA_card hB_card (col H_V.c) rfl hk_in_A h_union;
      · apply lemma_rainbow_clique_free_case_B col hA_card hB_card (col H_V.c) rfl (by
        replace h_union := Finset.ext_iff.mp h_union ( col H_V.c ) ; aesop;) h_union

/-
Definitions of cochromatic number, the collection X of subsets of H with clique number < 4, and the graph G constructed from H.
-/
open SimpleGraph

def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) {α : Type*} (c : V → α) : Prop :=
  ∀ i, G.IsClique (c ⁻¹' {i}) ∨ G.IsIndepSet (c ⁻¹' {i})

def CochromaticColorable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ c : V → Fin n, IsCochromaticColoring G c

noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  sInf { n : ℕ∞ | ∃ m : ℕ, n = m ∧ CochromaticColorable G m }

def X_collection : Set (Set H_V) := { X | (H.induce X).CliqueFree 4 }

def G_V (sizes : X_collection → ℕ) := H_V ⊕ (Σ X : X_collection, Fin (sizes X))

noncomputable def G (sizes : X_collection → ℕ) : SimpleGraph (G_V sizes) :=
  SimpleGraph.fromRel fun u v =>
    match u, v with
    | Sum.inl u, Sum.inl v => H.Adj u v
    | Sum.inl u, Sum.inr ⟨X, _⟩ => u ∈ X.val
    | Sum.inr ⟨X, _⟩, Sum.inl u => u ∈ X.val
    | _, _ => False

/-
Any clique in G contains at most one vertex from the new vertices (the independent sets added to H).
-/
theorem clique_new_vertices_card_le_one (sizes : X_collection → ℕ) (S : Finset (G_V sizes))
    (hS : (G sizes).IsClique S) :
    (S.filter (fun v => v.isRight)).card ≤ 1 := by
      -- Assume there are two distinct right vertices in S, say v1 and v2.
      by_contra h_contra
      obtain ⟨v1, v2, hv1, hv2, hv_distinct⟩ : ∃ v1 v2 : G_V sizes, v1 ∈ S ∧ v2 ∈ S ∧ v1.isRight ∧ v2.isRight ∧ v1 ≠ v2 := by
        obtain ⟨ v1, hv1, v2, hv2, hne ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra ) ; use v1, v2; aesop;
      rcases v1 with ( _ | ⟨ X, _ ⟩ ) <;> rcases v2 with ( _ | ⟨ Y, _ ⟩ ) <;> simp_all +decide [ SimpleGraph.isClique_iff ];
      have := hS hv1 hv2; simp_all +decide [ G ] ;

/-
If a clique contains a new vertex v (corresponding to X), then all old vertices in the clique are in X.
-/
theorem clique_old_vertices_subset_X (sizes : X_collection → ℕ) (S : Finset (G_V sizes))
    (hS : (G sizes).IsClique S)
    (v : G_V sizes) (hv : v ∈ S) (hv_new : v.isRight) :
    ∀ u ∈ S, u.isLeft → ∃ (h : u.isLeft), u.getLeft h ∈ (v.getRight hv_new).1.val := by
      intro u hu hu_left
      obtain ⟨k, hk⟩ : ∃ k, v = Sum.inr k := by
        cases v <;> aesop;
      -- Since $u$ is in $S$ and $S$ is a clique, $u$ must be adjacent to $v$. In the graph $G$, adjacency between $u$ (which is in $H$) and $v$ (which is a new vertex) means that $u$ is in the neighborhood of $v$, which is $X$.
      have h_adj : (G sizes).Adj u v := by
        exact hS ( by aesop ) ( by aesop ) ( by aesop );
      unfold G at h_adj; aesop;

/-
The subset of vertices in H corresponding to the old vertices in a clique S of G forms a clique in H.
-/
theorem old_vertices_form_clique_in_H (sizes : X_collection → ℕ) (S : Finset (G_V sizes))
    (hS : (G sizes).IsClique S) :
    H.IsClique (S.preimage Sum.inl (Set.injOn_of_injective Sum.inl_injective)) := by
      simp +decide [ Set.Pairwise ] at hS ⊢;
      intro x hx y hy hxy; specialize hS hx hy; simp_all +decide [ G ] ;
      cases hS ( by simpa [ Sum.inl_injective.ne_iff ] using hxy ) <;> tauto

/-
If a clique S contains a new vertex v, then the number of old vertices in S is at most 3.
-/
theorem clique_old_part_size (sizes : X_collection → ℕ) (S : Finset (G_V sizes))
    (hS : (G sizes).IsClique S)
    (v : G_V sizes) (hv : v ∈ S) (hv_new : v.isRight) :
    (S.filter (fun u => u.isLeft)).card ≤ 3 := by
      -- Let S_old = S.filter (fun u => u.isLeft).
      set S_old := S.filter (fun u => u.isLeft);

      -- The set of vertices in H corresponding to S_old is S_H = S.preimage Sum.inl.
      set S_H := S.preimage Sum.inl (Set.injOn_of_injective Sum.inl_injective) with hS_H;

      -- By `clique_old_vertices_subset_X`, S_H is a subset of X (where v corresponds to X).
      obtain ⟨X, hX⟩ : ∃ X : X_collection, ∀ u ∈ S_H, u ∈ X.val := by
        rcases v with ⟨ u, u ⟩ ; aesop;
        · cases hv_new;
        · cases hv_new;
        · have := clique_old_vertices_subset_X sizes S hS ( Sum.inr ‹_› ) hv hv_new; aesop;
      -- Since $S_H$ is a subset of $X$ and $X$ is in $X_collection$, $S_H$ is a clique in $H$ with clique number less than 4.
      have hS_H_clique : H.IsClique S_H := by
        convert old_vertices_form_clique_in_H sizes S hS using 1;
      have hS_H_card : S_H.card ≤ 3 := by
        have hS_H_card : (H.induce X.val).CliqueFree 4 := by
          exact X.2;
        contrapose! hS_H_card;
        have hS_H_card : ∃ T : Finset H_V, T ⊆ S_H ∧ T.card = 4 ∧ H.IsClique T := by
          obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq hS_H_card;
          exact ⟨ T, hT.1, hT.2, fun u hu v hv huv => hS_H_clique ( hT.1 hu ) ( hT.1 hv ) huv ⟩;
        obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := hS_H_card; simp_all +decide [ SimpleGraph.CliqueFree ] ;
        use T.subtype (fun u => u ∈ X.val);
        simp_all +decide [ SimpleGraph.isNClique_iff, Finset.subtype ];
        simp_all +decide [ Set.Pairwise, Finset.subset_iff ];
        exact ⟨ by aesop, by rw [ Finset.filter_true_of_mem fun x hx => hX x ( hT₁ hx ) ] ; linarith ⟩;
      convert hS_H_card using 1;
      refine' Finset.card_bij ( fun u hu => u.getLeft ( by aesop ) ) _ _ _ <;> aesop

/-
The graph G does not contain a clique of size 5.
-/
theorem G_clique_free_5 (sizes : X_collection → ℕ) : (G sizes).CliqueFree 5 := by
  -- Let S be a clique in G. We need to show that |S| ≤ 4.
  intro S hS
  by_contra h_contra;
  -- Let S_old = S.filter (fun v => v.isLeft) and S_new = S.filter (fun v => v.isRight).
  set S_old := S.filter (fun v => v.isLeft)
  set S_new := S.filter (fun v => v.isRight);
  -- If S_new is empty, then S = S_old. S corresponds to a clique in H via `old_vertices_form_clique_in_H`.
  by_cases hS_new_empty : S_new.card = 0;
  · -- Since S_new is empty, S corresponds to a clique in H via `old_vertices_form_clique_in_H`.
    have hS_old_clique : H.IsNClique 5 (S.preimage Sum.inl (Set.injOn_of_injective Sum.inl_injective)) := by
      have hS_old_clique : H.IsClique (S.preimage Sum.inl (Set.injOn_of_injective Sum.inl_injective)) := by
        convert old_vertices_form_clique_in_H sizes S ( hS.1 ) using 1;
      refine' ⟨ _, _ ⟩;
      · grind;
      · convert hS.2 using 1;
        rw [ Finset.card_preimage ];
        convert Finset.card_filter ( fun x => x.isLeft ) S using 1;
        · congr! 2;
          ext ( _ | _ ) <;> simp +decide;
        · rw [ Finset.sum_congr rfl fun x hx => if_pos <| by_contradiction fun hx' => by have := Finset.mem_filter.mp ( Finset.mem_filter.mpr ⟨ hx, by aesop ⟩ : x ∈ S_new ) ; aesop ] ; aesop;
    exact absurd hS_old_clique ( by exact fun h => by have := lemma_clique_free_5; exact this _ h );
  · -- If S_new is non-empty, then there exists a unique element v in S_new.
    obtain ⟨v, hv⟩ : ∃! v, v ∈ S_new := by
      have := clique_new_vertices_card_le_one sizes S hS.1;
      exact Finset.card_eq_one.mp ( le_antisymm this ( Nat.pos_of_ne_zero hS_new_empty ) ) |> fun ⟨ v, hv ⟩ => ⟨ v, by aesop ⟩;
    -- By `clique_old_part_size`, |S_old| ≤ 3.
    have hS_old_card : S_old.card ≤ 3 := by
      have := clique_old_part_size sizes S hS.1 v ( Finset.mem_filter.mp hv.1 |>.1 ) ( Finset.mem_filter.mp hv.1 |>.2 ) ; aesop;
    have := hS.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    exact absurd this ( by linarith [ show S.card ≤ 4 by exact le_trans ( Finset.card_le_card ( show S ⊆ S_old ∪ { v } from fun x hx => by by_cases hx' : Sum.isLeft x <;> aesop ) ) ( by exact le_trans ( Finset.card_union_le _ _ ) ( by norm_num; linarith ) ) ] )

/-
Any independent set in H has size at most 3.
-/
theorem H_alpha_le_3 (S : Finset H_V) (hS : H.IsIndepSet S) : S.card ≤ 3 := by
  -- By definition of $H$, we know that its vertex set can be partitioned into 3 cliques.
  have h_partition : ∃ s1 s2 s3 : Set H_V, s1 ∪ s2 ∪ s3 = Set.univ ∧ H.IsClique s1 ∧ H.IsClique s2 ∧ H.IsClique s3 := by
    exact lemma_partition_3_cliques;
  obtain ⟨ s1, s2, s3, h1, h2, h3, h4 ⟩ := h_partition;
  -- Since $S$ is an independent set, it can contain at most one vertex from each clique.
  have h_card_le_one : ∀ i ∈ [s1, s2, s3], (Finset.filter (fun v => v ∈ i) S).card ≤ 1 := by
    intros i hi
    have h_card_le_one_i : ∀ u v : H_V, u ∈ i → v ∈ i → u ≠ v → ¬H.Adj u v → False := by
      norm_num +zetaDelta at *;
      rcases hi with ( rfl | rfl | rfl ) <;> tauto;
    exact Finset.card_le_one.mpr fun u hu v hv => Classical.not_not.1 fun huv => h_card_le_one_i u v ( Finset.mem_filter.mp hu |>.2 ) ( Finset.mem_filter.mp hv |>.2 ) huv ( hS ( Finset.mem_filter.mp hu |>.1 ) ( Finset.mem_filter.mp hv |>.1 ) huv );
  have h_card_le_three : S.card ≤ (Finset.filter (fun v => v ∈ s1) S).card + (Finset.filter (fun v => v ∈ s2) S).card + (Finset.filter (fun v => v ∈ s3) S).card := by
    rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
    simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones S ▸ Finset.sum_le_sum fun x hx => by replace h1 := Set.ext_iff.mp h1 x; aesop;
  exact h_card_le_three.trans ( add_le_add_three ( h_card_le_one s1 ( by norm_num ) ) ( h_card_le_one s2 ( by norm_num ) ) ( h_card_le_one s3 ( by norm_num ) ) )

/-
The cochromatic number of G is at most 4.
-/
theorem G_cochromatic_le_4 (sizes : X_collection → ℕ) : cochromaticNumber (G sizes) ≤ 4 := by
  refine' le_trans ( csInf_le _ _ ) ( le_refl _ );
  · exact ⟨ 0, by rintro n ⟨ m, rfl, hm ⟩ ; exact zero_le _ ⟩;
  · refine' ⟨ 4, rfl, _ ⟩;
    -- Let's obtain the partition of H into 3 cliques.
    obtain ⟨s1, s2, s3, hs_union, hs1, hs2, hs3⟩ := lemma_partition_3_cliques;
    use fun v => Sum.elim ( fun x => if x ∈ s1 then 0 else if x ∈ s2 then 1 else 2 ) ( fun _ => 3 ) v; intro i; by_cases hi : i = 3 <;> simp_all +decide [ Set.ext_iff ] ;
    · refine' Or.inr _;
      intro x hx y hy hxy; simp_all +decide [ Set.preimage ] ;
      rcases x with ( x | ⟨ X, x ⟩ ) <;> rcases y with ( y | ⟨ Y, y ⟩ ) <;> simp_all +decide [ G ];
      · split_ifs at hx hy <;> contradiction;
      · split_ifs at hx <;> contradiction;
      · grind;
    · refine' Or.inl _;
      intro x hx y hy hxy; simp_all +decide [ Set.Pairwise ] ;
      rcases x with ( x | ⟨ X, i ⟩ ) <;> rcases y with ( y | ⟨ Y, j ⟩ ) <;> simp_all +decide [ G ];
      grind +ring

/-
The chromatic number of G is at least 7.
-/
theorem G_chromatic_ge_7 (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    (G sizes).chromaticNumber ≥ 7 := by
      -- Suppose for contradiction that G is 6-colorable.
      by_contra h_contra
      obtain ⟨col, hcol⟩ : ∃ col : (G sizes).Coloring (Fin 6), True := by
        simp +zetaDelta at *;
        -- By definition of chromatic number, if the chromatic number of G is less than 7, then there exists a proper coloring of G with 6 colors.
        have h_colorable : (G sizes).Colorable 6 := by
          have h_colorable : (G sizes).chromaticNumber ≤ 6 := by
            exact?;
          exact chromaticNumber_le_iff_colorable.mp h_colorable;
        exact ⟨ h_colorable.some ⟩;
      -- Restrict c to H. This is a proper 6-coloring of H.
      obtain ⟨col_H, hcol_H⟩ : ∃ col_H : H.Coloring (Fin 6), ∀ u : H_V, col (Sum.inl u) = col_H u := by
        refine' ⟨ _, _ ⟩;
        refine' ⟨ fun u => col ( Sum.inl u ), _ ⟩;
        all_goals norm_num;
        intro a b hab; have := col.valid ( show ( G sizes ).Adj ( Sum.inl a ) ( Sum.inl b ) from by
                                            -- Since $a$ and $b$ are adjacent in $H$, they are also adjacent in $G$ by definition of $G$.
                                            simp [G, hab];
                                            exact fun h => hab.ne <| by injection h; ) ; aesop;
      -- By `lemma_rainbow_clique_free`, there exists a set X in H such that H[X] is clique-free 4 (so X is in X_collection) and X is rainbow (contains all 6 colors).
      obtain ⟨X, hX⟩ : ∃ X : Finset H_V, (H.induce X).CliqueFree 4 ∧ (Finset.image col_H X) = Finset.univ := by
        convert lemma_rainbow_clique_free col_H;
      -- Since X is in X_collection, there is a vertex v_X in G (in the independent set V_X).
      obtain ⟨v_X, hv_X⟩ : ∃ v_X : G_V sizes, v_X.isRight ∧ ∃ X' : X_collection, v_X = Sum.inr ⟨X', Fin.mk 0 (by
      exact h_sizes X')⟩ ∧ X'.val = X := by
        exact ⟨ Sum.inr ⟨ ⟨ X, hX.1 ⟩, ⟨ 0, h_sizes ⟨ X, hX.1 ⟩ ⟩ ⟩, by simp +decide, ⟨ X, hX.1 ⟩, rfl, rfl ⟩
      generalize_proofs at *;
      -- Since $v_X$ is adjacent to all vertices in $X$, and $X$ is rainbow, there must be a vertex $u \in X$ such that $col(u) = col(v_X)$.
      obtain ⟨u, hu⟩ : ∃ u ∈ X, col (Sum.inl u) = col v_X := by
        have := Finset.mem_image.mp ( hX.2.symm ▸ Finset.mem_univ ( col v_X ) ) ; aesop;
      -- Since $v_X$ is adjacent to all vertices in $X$, and $X$ is rainbow, there must be a vertex $u \in X$ such that $col(u) = col(v_X)$. This contradicts the assumption that $col$ is a proper coloring.
      have h_adj : (G sizes).Adj (Sum.inl u) v_X := by
        unfold G; aesop;
      exact absurd ( col.valid h_adj ) ( by aesop )

/-
The graph H is 6-colorable.
-/
theorem H_colorable_6 : H.Colorable 6 := by
  -- Define the coloring function for H.
  use fun v => match v with
    | H_V.a i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 0 else 1
    | H_V.b i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 3 else 4
    | H_V.c => 2;
  rintro ( _ | _ | _ ) ( _ | _ | _ ) <;> simp +decide [ H ];
  all_goals rename_i i; fin_cases i <;> simp +decide ;
  all_goals rename_i i; fin_cases i <;> simp +decide ;

/-
The number of vertices in H is 11.
-/
theorem H_card_eq_11 : Fintype.card H_V = 11 := by
  decide +revert

/-
H cannot be covered by 1 clique and 2 independent sets.
-/
theorem H_no_cover_1K_2I : ¬ ∃ (k1 i1 i2 : Set H_V), k1 ∪ i1 ∪ i2 = Set.univ ∧ H.IsClique k1 ∧ H.IsIndepSet i1 ∧ H.IsIndepSet i2 := by
  simp +zetaDelta at *;
  intro k1 i1 i2 h_union h_clique h_ind1 h_ind2dep2;
  -- Since $i1$ and $i2$ are independent sets in $H$, they can each contain at most 3 vertices.
  have h_i1_card : i1.ncard ≤ 3 := by
    have h_i1_card : ∀ (S : Finset H_V), H.IsIndepSet S → S.card ≤ 3 := by
      exact fun S a => H_alpha_le_3 S a;
    convert h_i1_card ( Finset.filter ( fun x => x ∈ i1 ) Finset.univ ) _;
    · rw [ ← Set.ncard_coe_finset ] ; aesop;
    · aesop
  have h_i2_card : i2.ncard ≤ 3 := by
    have h_i2_card : ∀ S : Finset H_V, H.IsIndepSet S → S.card ≤ 3 := by
      exact fun S a => H_alpha_le_3 S a;
    contrapose! h_i2_card;
    obtain ⟨ S, hS ⟩ := Set.Finite.exists_finset_coe ( show Set.Finite i2 from Set.finite_of_ncard_pos ( pos_of_gt h_i2_card ) ) ; use S; aesop;
  -- Since $k1$ is a clique in $H$, it can contain at most 4 vertices.
  have h_k1_card : k1.ncard ≤ 4 := by
    have h_k1_card : ∀ (S : Finset H_V), H.IsClique S → S.card ≤ 4 := by
      intro S hSique
      have hS_card : S.card ≤ 4 := by
        have hS_clique_free : H.CliqueFree 5 := by
          exact lemma_clique_free_5
        contrapose! hS_clique_free;
        simp +decide [ SimpleGraph.CliqueFree ];
        obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq hS_clique_free;
        exact ⟨ t, by exact ⟨ by exact fun u hu v hv huv => hSique ( ht.1 hu ) ( ht.1 hv ) huv, by aesop ⟩ ⟩;
      exact hS_card;
    convert h_k1_card ( k1.toFinset ) _;
    · rw [ ← Set.ncard_coe_finset, Set.coe_toFinset ];
    · aesop;
  have h_total_card : Set.ncard (k1 ∪ i1 ∪ i2) ≤ Set.ncard k1 + Set.ncard i1 + Set.ncard i2 := by
    exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add_right ( Set.ncard_union_le _ _ ) _ );
  simp_all +decide [ Set.ncard_univ ];
  exact h_total_card.not_lt ( by rw [ show Fintype.card H_V = 11 by rfl ] ; linarith )

/-
The chromatic number of G is at most 7.
-/
theorem G_chromatic_le_7 (sizes : X_collection → ℕ) : (G sizes).chromaticNumber ≤ 7 := by
  -- Let $c_H$ be a 6-coloring of $H$.
  obtain ⟨c_H, hc_H⟩ : ∃ c_H : H_V → Fin 6, ∀ u v, H.Adj u v → c_H u ≠ c_H v := by
    have h_colorable : H.Colorable 6 := by
      exact H_colorable_6
    obtain ⟨c_H, hc_H⟩ := h_colorable
    use c_H
    aesop
    skip;
  refine' le_trans ( ciInf_le _ 7 ) _;
  · exact ⟨ 0, Set.forall_mem_range.2 fun n => by exact zero_le _ ⟩;
  · refine' ciInf_le_of_le _ _ _ <;> norm_num;
    -- Let $c$ be a 7-coloring of $G$.
    use fun u => Sum.elim (fun u => Fin.castLE (by decide) (c_H u)) (fun ⟨X, i⟩ => 6) u;
    rintro ( u | ⟨ X, i ⟩ ) ( v | ⟨ Y, j ⟩ ) <;> simp +decide [ *, SimpleGraph.fromRel_adj ];
    · unfold G; aesop;
    · exact fun h => ne_of_lt ( Fin.castSucc_lt_last _ );
    · exact fun h => ne_of_gt ( Fin.castSucc_lt_last _ );
    · unfold G; aesop;

/-
H cannot be covered by 2 cliques.
-/
theorem H_no_cover_2K : ¬ ∃ (k1 k2 : Set H_V), k1 ∪ k2 = Set.univ ∧ H.IsClique k1 ∧ H.IsClique k2 := by
  by_contra h_contra
  obtain ⟨k1, k2, hk1k2, hk1, hk2⟩ := h_contra
  have h_card : k1.ncard ≤ 4 ∧ k2.ncard ≤ 4 := by
    have h_card : ∀ k : Set H_V, H.IsClique k → k.ncard ≤ 4 := by
      intro k hk; have := @lemma_clique_free_5; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
      contrapose! this;
      simp_all +decide [ SimpleGraph.CliqueFree ];
      -- Since $k$ is � a� clique and has more than 4 elements, we can choose any 5 elements from $k$ to form a 5-clique.
      obtain ⟨x, hx⟩ : ∃ x : Finset H_V, x.card = 5 ∧ x ⊆ Finset.filter (Membership.mem k) Finset.univ := by
        exact Exists.imp ( by aesop ) ( Finset.exists_subset_card_eq this );
      use x; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      intro u hu v hv huv; have := hk ( show u ∈ k from Finset.mem_filter.mp ( hx.2 hu ) |>.2 ) ( show v ∈ k from Finset.mem_filter.mp ( hx.2 hv ) |>.2 ) ; aesop;
    exact ⟨h_card k1 hk1, h_card k2 hk2⟩;
  -- Since $k1$ and $k �2�$ are cliques, their union $k1 \cup k2$ has at most $4 + 4 = 8$ vertices.
  have h_union_card : (k1 ∪ k2).ncard ≤ 8 := by
    exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add h_card.1 h_card.2 );
  simp_all +decide [ Set.ncard_univ ]

/-
H cannot be covered by 3 independent sets.
-/
theorem H_no_cover_3I : ¬ ∃ (i1 i2 i3 : Set H_V), i1 ∪ i2 ∪ i3 = Set.univ ∧ H.IsIndepSet i1 ∧ H.IsIndepSet i2 ∧ H.IsIndepSet i3 := by
  push_neg;
  intro i1 i2 i3 h1 h2 h3 h4;
  -- By `H_alpha_le_3`, the maximum size of an independent set in H is 3.
  have h_alpha_le_3 : ∀ i : Set H_V, H.IsIndepSet i → i.ncard ≤ 3 := by
    intro i hi
    have h_card_i : (Set.toFinset i).card ≤ 3 := by
      convert H_alpha_le_3 ( Set.toFinset i ) ( by simpa [ Set.Pairwise ] using hi ) using 1;
    rwa [ Set.ncard_eq_toFinset_card' ];
  -- Since $i1 \cup i �2� \cup i �3� = \text{Set.univ}$, we have $|i1 \cup i2 \cup i3| = |H_V| = 11$.
  have h_union_card : (i1 ∪ i2 ∪ i3).ncard = 11 := by
    simp +decide [ h1, Set.ncard_univ ];
  exact h_union_card.not_lt ( lt_of_le_of_lt ( Set.ncard_union_le _ _ ) ( lt_of_le_of_lt ( add_le_add ( Set.ncard_union_le _ _ ) le_rfl ) ( by linarith [ h_alpha_le_3 i1 h2, h_alpha_le_3 i2 h3, h_alpha_le_3 i3 h4 ] ) ) )

/-
The empty set is in the collection X.
-/
theorem empty_mem_X_collection : ∅ ∈ X_collection := by
  -- The empty set is trivially 4-clique-free because a clique of size 4 would require at least one vertex, but the empty set has no vertices.
  simp [X_collection, SimpleGraph.IsNClique];
  -- The empty set has no vertices, so any subset of the empty set has size 0, which is less than 4. Therefore, the empty set is clique-free for any n.
  simp [SimpleGraph.CliqueFree];
  simp +decide [ SimpleGraph.isNClique_iff ]

/-
If G is covered by 3 cliques, one of them is disjoint from H.
-/
theorem lemma_exists_clique_disjoint_H_of_cover_3K (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0)
    (k1 k2 k3 : Set (G_V sizes))
    (h_cover : k1 ∪ k2 ∪ k3 = Set.univ)
    (hk1 : (G sizes).IsClique k1)
    (hk2 : (G sizes).IsClique k2)
    (hk3 : (G sizes).IsClique k3) :
    (k1 ∩ Set.range Sum.inl = ∅) ∨ (k2 ∩ Set.range Sum.inl = ∅) ∨ (k3 ∩ Set.range Sum.inl = ∅) := by
      norm_num [ Set.ext_iff ] at *;
      cases' h_cover ( Sum.inr ⟨ ⟨ ∅, by
        exact empty_mem_X_collection ⟩, ⟨ 0, by
        exact h_sizes _ _ ⟩ ⟩ ) with h h
      all_goals generalize_proofs at *;
      · cases' h with h h;
        · left;
          intro x hx y hy; have := hk1 hx h; simp_all +decide [ G ] ;
          subst hy; simp_all +decide ;
        · right;
          left;
          intro x hx y hy; have := hk2 h hx; simp_all +decide [ G ] ;
          subst hy; simp_all +decide [ G ] ;
      · refine Or.inr <| Or.inr <| fun x hx y hy => ?_;
        subst hy;
        exact absurd ( hk3 hx h ) ( by simp +decide [ G ] )

/-
If one clique in a 3-clique cover of G is disjoint from H, then H is covered by 2 cliques.
-/
theorem lemma_H_covered_by_2K_of_disjoint_clique (sizes : X_collection → ℕ)
    (k1 k2 k3 : Set (G_V sizes))
    (h_cover : k1 ∪ k2 ∪ k3 = Set.univ)
    (h_disjoint : k1 ∩ Set.range Sum.inl = ∅)
    (hk2 : (G sizes).IsClique k2)
    (hk3 : (G sizes).IsClique k3) :
    ∃ (c2 c3 : Set H_V), c2 ∪ c3 = Set.univ ∧ H.IsClique c2 ∧ H.IsClique c3 := by
      -- Since $k2$ and $k3$ are cliques in $G$, and $H$ is a subgraph of $G$, $k2 \cap H$ and $k3 \cap H$ are cliques in $H$.
      have h_clique_k2 : H.IsClique (k2 ∩ Set.range Sum.inl |> Set.preimage Sum.inl) := by
        simp_all +decide [ Set.subset_def, SimpleGraph.IsClique ];
        intro u hu v hv huv; have := hk2 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
        simp +decide [ G ];
        simp +decide [ SimpleGraph.adj_comm, huv ];
        exact fun _ => by simpa [ Sum.inl_injective.ne_iff ] using huv;
      have h_clique_k3 : H.IsClique (k3 ∩ Set.range Sum.inl |> Set.preimage Sum.inl) := by
        intro x hx y hy; simp_all +decide [ Set.preimage ] ;
        have := hk3 hx hy; simp_all +decide [ G ] ;
        cases eq_or_ne x y <;> simp_all +decide [ SimpleGraph.adj_comm ];
        grind;
      refine' ⟨ _, _, _, h_clique_k2, h_clique_k3 ⟩ ; simp_all +decide [ Set.ext_iff ];
      intro x; specialize h_cover ( Sum.inl x ) ; contrapose! h_disjoint; aesop;

/-
G cannot be covered by 3 cliques.
-/
theorem lemma_G_no_cover_3K (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    ¬ ∃ (k1 k2 k3 : Set (G_V sizes)), k1 ∪ k2 ∪ k3 = Set.univ ∧
    (G sizes).IsClique k1 ∧ (G sizes).IsClique k2 ∧ (G sizes).IsClique k3 := by
      intro h
      obtain ⟨k1, k2, k3, h_cover, hk1, hk2, hk3⟩ := h
      have h_disjoint : (k1 ∩ Set.range Sum.inl = ∅) ∨ (k2 ∩ Set.range Sum.inl = ∅) ∨ (k3 ∩ Set.range Sum.inl = ∅) := by
        exact lemma_exists_clique_disjoint_H_of_cover_3K sizes h_sizes k1 k2 k3 h_cover hk1 hk2 hk3;
      rcases h_disjoint with ( h | h | h );
      · have := lemma_H_covered_by_2K_of_disjoint_clique sizes k1 k2 k3 h_cover h hk2 hk3;
        exact H_no_cover_2K this;
      · have := lemma_H_covered_by_2K_of_disjoint_clique sizes k2 k1 k3 ?_ h hk1 hk3;
        · exact H_no_cover_2K this;
        · grind;
      · -- Apply `lemma_H_covered_by_2K_of_disjoint_clique` with $k3, k1, k2$.
        have h_contradiction : ∃ (c2 c3 : Set H_V), c2 ∪ c3 = Set.univ ∧ H.IsClique c2 ∧ H.IsClique c3 := by
          apply lemma_H_covered_by_2K_of_disjoint_clique;
          rotate_left;
          exact h;
          exacts [ hk1, hk2, by simpa only [ Set.union_comm, Set.union_left_comm ] using h_cover ];
        exact H_no_cover_2K h_contradiction

/-
If I is an independent set in G, X is its restriction to H, X is non-empty, and v corresponds to X, then v is not in I.
-/
theorem lemma_indep_inter_H_eq_X_implies_v_not_in_I (sizes : X_collection → ℕ)
    (I : Set (G_V sizes)) (hI : (G sizes).IsIndepSet I)
    (X : Set H_V) (hX : X = I.preimage Sum.inl)
    (hX_nonempty : X.Nonempty)
    (v : G_V sizes) (hv_new : v.isRight)
    (hv_X : (v.getRight hv_new).1.val = X) :
    v ∉ I := by
      -- Since $X$ is non-empty, there exists some � $�u \in H_V$ such that $u \in X$.
      obtain ⟨u, hu⟩ : ∃ u : H_V, u ∈ X := hX_nonempty;
      have := @hI;
      intro hvI; have := this ( show v ∈ I from hvI ) ( show Sum.inl u ∈ I from by aesop ) ; simp_all +decide [ G ] ;
      rcases v with ( _ | ⟨ X, _ ⟩ ) <;> simp_all +decide;
      cases hv_new

/-
G cannot be covered by 3 independent sets.
-/
theorem lemma_G_no_cover_3I (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    ¬ ∃ (i1 i2 i3 : Set (G_V sizes)), i1 ∪ i2 ∪ i3 = Set.univ ∧
    (G sizes).IsIndepSet i1 ∧ (G sizes).IsIndepSet i2 ∧ (G sizes).IsIndepSet i3 := by
      intro h
      obtain ⟨i1, i2, i3, h_cover, h_i1, h_i2, h_i3⟩ := h
      set j1 := i1.preimage Sum.inl
      set j2 := i2.preimage Sum.inl
      set j3 := i3.preimage Sum.inl
      have h_j1 : H.IsIndepSet j1 := by
        intro u hu v hv huv;
        have := h_i1 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        simp_all +decide [ SimpleGraph.fromRel_adj, G ];
        grind
      have h_j2 : H.IsIndepSet j2 := by
        intro u hu v hv huv; have := h_i2 hu hv; simp_all +decide [ H ] ;
        unfold G at this; simp_all +decide [ SimpleGraph.fromRel ] ;
        unfold H at this; simp_all +decide [ SimpleGraph.fromRel ] ;
        grind +ring
      have h_j3 : H.IsIndepSet j3 := by
        intro x hx y hy hxy; have := h_i3; simp_all +decide [ Set.preimage ] ;
        have := this ( show Sum.inl x ∈ i3 from hx ) ( show Sum.inl y ∈ i3 from hy ) ; simp +decide [ G, hxy ] at this;
        exact this ( by simpa [ Sum.inl_injective.ne_iff ] using hxy ) |>.1
      have h_union : j1 ∪ j2 ∪ j3 = Set.univ := by
        ext x; replace h_cover := Set.ext_iff.mp h_cover ( Sum.inl x ) ; aesop;
      exact H_no_cover_3I ⟨j1, j2, j3, h_union, h_j1, h_j2, h_j3⟩

/-
G cannot be covered by 1 clique and 2 independent sets.
-/
theorem lemma_G_no_cover_1K_2I (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    ¬ ∃ (k1 i1 i2 : Set (G_V sizes)), k1 ∪ i1 ∪ i2 = Set.univ ∧
    (G sizes).IsClique k1 ∧ (G sizes).IsIndepSet i1 ∧ (G sizes).IsIndepSet i2 := by
      by_contra h_contra
      obtain ⟨k1, i1, i2, h_cover, hk1, hi1, hi2⟩ := h_contra;
      have h_cover_H : (k1.preimage Sum.inl) ∪ (i1.preimage Sum.inl) ∪ (i2.preimage Sum.inl) = Set.univ := by
        simp_all +decide [ Set.ext_iff ];
      have h_clique : H.IsClique (k1.preimage Sum.inl) := by
        intro u hu v hv huv; have := hk1 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
        unfold G; simp +decide [ SimpleGraph.fromRel_adj ] ;
        simp +decide [ SimpleGraph.adj_comm, huv ];
        exact fun _ => by simpa [ Sum.inl_injective.ne_iff ] using huv;
      have h_indep1 : H.IsIndepSet (i1.preimage Sum.inl) := by
        intro u hu v hv huv; have := hi1 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
        simp +decide [ G ];
        exact ⟨ fun h => ⟨ by simpa [ Sum.inl_injective.eq_iff ] using huv, Or.inl h ⟩, fun h => h.2.resolve_right ( by rintro h'; exact huv <| by have := h'.symm; tauto ) ⟩
      have h_indep2 : H.IsIndepSet (i2.preimage Sum.inl) := by
        intro x hx y hy hxy; have := hi2; simp_all +decide [ Set.Pairwise ] ;
        specialize this hx hy ; simp_all +decide [ G ];
        grind;
      exact H_no_cover_1K_2I ⟨ _, _, _, h_cover_H, h_clique, h_indep1, h_indep2 ⟩

/-
If a clique contains a vertex corresponding to an independent set X, its intersection with H has size at most 1.
-/
theorem lemma_clique_inter_H_le_one_of_mem_V_indep (sizes : X_collection → ℕ)
    (K : Set (G_V sizes)) (hK : (G sizes).IsClique K)
    (X : Set H_V) (hX : H.IsIndepSet X)
    (v : G_V sizes) (hv : v ∈ K) (hv_new : v.isRight)
    (hv_X : (v.getRight hv_new).1.val = X) :
    (K ∩ Set.range Sum.inl).ncard ≤ 1 := by
      rw [ Set.ncard_eq_toFinset_card _ ];
      refine' Finset.card_le_one.mpr _;
      simp +zetaDelta at *;
      intro a ha x hx b hb y hy; subst_vars; have := hK ha hb; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
      unfold G at this; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
      contrapose! this; simp_all +decide [ SimpleGraph.adj_comm ] ;
      have := hX ( show x ∈ ( Sum.getRight v hv_new ).fst.val from ?_ ) ( show y ∈ ( Sum.getRight v hv_new ).fst.val from ?_ ) ; aesop;
      · have := hK hv ha; have := hK hv hb; unfold G at *; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        cases v <;> tauto;
      · have := hK hv hb; unfold G at this; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        cases v <;> tauto

/-
H cannot be covered by a clique of size at most 1, another clique, and an independent set.
-/
theorem lemma_H_not_covered_by_small_cliques_and_indep (k1 k2 i1 : Set H_V)
    (h_cover : k1 ∪ k2 ∪ i1 = Set.univ)
    (hk1 : H.IsClique k1) (hk2 : H.IsClique k2) (hi1 : H.IsIndepSet i1)
    (hk1_size : k1.ncard ≤ 1) : False := by
      -- We know $|k2| \le 4$ (since max clique size in H is 4).
      have hk2_size : k2.ncard ≤ 4 := by
        have hk2_card : ∀ (s : Finset H_V), H.IsClique s → s.card ≤ 4 := by
          intro s hs; have := @lemma_clique_free_5; simp_all +decide [ SimpleGraph.IsClique ] ;
          contrapose! this;
          obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq this;
          exact fun h => h t ⟨ by
            exact fun x hx y hy hxy => hs ( ht.1 hx ) ( ht.1 hy ) hxy, by
            linarith ⟩;
        convert hk2_card ( Set.toFinset k2 ) _;
        · rw [ Set.ncard_eq_toFinset_card' ];
        · aesop;
      -- We know $|i1| \le 3$ (since max indep set size in H is 3).
      have hi1_size : i1.ncard ≤ 3 := by
        have := H_alpha_le_3 ( i1.toFinset ) ; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
      -- So $|k1 \cup k �2� \cup i �1�| \le |k1| + |k2| + |i1| \le 1 + 4 + 3 = 8$.
      have h_union_size : (k1 ∪ k2 ∪ i1).ncard ≤ 8 := by
        exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add ( le_trans ( Set.ncard_union_le _ _ ) ( add_le_add hk1_size hk2_size ) ) hi1_size );
      simp_all +decide [ Set.ncard_univ ]

/-
If G is covered by 2 cliques and 1 independent set, and the independent set intersects H, then False.
-/
theorem lemma_G_no_cover_2K_1I_nonempty_I (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0)
    (k1 k2 i1 : Set (G_V sizes)) (h_cover : k1 ∪ k2 ∪ i1 = Set.univ)
    (hk1 : (G sizes).IsClique k1) (hk2 : (G sizes).IsClique k2) (hi1 : (G sizes).IsIndepSet i1)
    (h_nonempty : (i1.preimage Sum.inl).Nonempty) : False := by
      -- Let $I_1 = i1.preimage Sum.inl$.
      set I1 := i1.preimage Sum.inl with hI1_def;
      -- Let $X = I1$.
      set X : Set H_V := I1 with hX_def;
      -- Since $I_1$ is non-empty, $X$ is in $X_collection$, so there exists a vertex $v \in V_X$.
      obtain ⟨X_mem, v, hv⟩ : ∃ X_mem : X_collection, X_mem.val = X ∧ ∃ v : Σ X : X_collection, Fin (sizes X), (v.1.val = X_mem.val) ∧ (Sum.inr v) ∉ i1 := by
        -- Since $X$ is non-empty and independent, there � exists� a vertex $v \in V_X$.
        obtain ⟨v, hv⟩ : ∃ v : Σ X : X_collection, Fin (sizes X), (v.1.val = X) := by
          have hX_indep : H.IsIndepSet X := by
            intro u hu v hv huv; have := hi1 hu hv; simp_all +decide [ SimpleGraph.fromRel ] ;
            convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
            unfold G; simp +decide [ SimpleGraph.fromRel ] ;
            simp +decide [ SimpleGraph.adj_comm, huv ];
            exact fun _ => by simpa [ Sum.inl_injective.eq_iff ] using huv;
          have hX_card : (Finset.univ.filter (fun u => u ∈ X)).card < 4 := by
            exact lt_of_le_of_lt ( H_alpha_le_3 _ <| by simpa [ Set.Pairwise ] using hX_indep ) ( by decide )
          have hX_in_X_collection : ∃ X_mem : X_collection, X_mem.val = X := by
            have hX_in_X_collection : (H.induce X).CliqueFree 4 := by
              intro S hS;
              have := Finset.card_le_card ( show S.image ( fun x : ↥X => x.val ) ⊆ Finset.filter ( fun u => u ∈ X ) Finset.univ from Finset.image_subset_iff.mpr fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, x.2 ⟩ ) ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
              exact absurd ( hS.2 ) ( by linarith );
            exact CanLift.prf X hX_in_X_collection
          obtain ⟨X_mem, hX_mem⟩ := hX_in_X_collection
          use ⟨X_mem, ⟨0, h_sizes X_mem⟩⟩;
        refine' ⟨ _, hv, v, rfl, _ ⟩;
        apply_rules [ lemma_indep_inter_H_eq_X_implies_v_not_in_I ];
      -- Without loss of generality, assume $v \in k1$.
      wlog hv_k1 : Sum.inr hv.choose ∈ k1 generalizing k1 k2 i1 X_mem v;
      · -- Since $v \notin k1$, we have $v \in k2$.
        have hv_k2 : Sum.inr hv.choose ∈ k2 := by
          replace h_cover := Set.ext_iff.mp h_cover ( Sum.inr hv.choose ) ; simp_all +decide ;
          exact h_cover.resolve_right ( by simpa [ ← v ] using hv.choose_spec.2 );
        specialize this k2 k1 i1 ; simp_all +decide [ Set.ext_iff ];
        grind +ring;
      · -- By `lemma_clique_inter_H_le_one_of_mem_V_indep`, $|k1 \cap H| \le 1$.
        have h_k1_inter_H_le_one : (k1.preimage Sum.inl).ncard ≤ 1 := by
          convert lemma_clique_inter_H_le_one_of_mem_V_indep sizes k1 hk1 X_mem.1 (by
          have h_indep : H.IsIndepSet X := by
            intro u hu v hv; have := hi1 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
            convert this using 1;
            · grind;
            · tauto;
          aesop) (Sum.inr hv.choose) hv_k1 (by
          rfl) (by
          exact hv.choose_spec.1) using 1;
          rw [ ← Set.ncard_image_of_injective _ Sum.inl_injective ] ; congr ; ext ; aesop;
        -- Let $K_1 = k1.preimage Sum.inl$, $K_2 = k2.preimage Sum.inl$, and $I_1 = i1.preimage Sum.inl$.
        set K1 := k1.preimage Sum.inl with hK1_def
        set K2 := k2.preimage Sum.inl with hK2_def
        set I1 := i1.preimage Sum.inl with hI1_def;
        -- $K_1, K_2$ are cliques in H.
        have hK1_clique : H.IsClique K1 := by
          intro u hu v hv huv; have := hk1 hu hv; simp_all +decide [ SimpleGraph.adj_comm ] ;
          exact False.elim (huv (h_k1_inter_H_le_one hu hv))
        have hK2_clique : H.IsClique K2 := by
          intro u hu v hv huv; have := hk2 ( show Sum.inl u ∈ k2 from hu ) ( show Sum.inl v ∈ k2 from hv ) ; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
          convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
          unfold G; simp +decide [ SimpleGraph.fromRel_adj ] ;
          simp +decide [ SimpleGraph.adj_comm, huv ];
          exact fun _ => by simpa [ Sum.inl_injective.ne_iff ] using huv;
        have hI1_indep : H.IsIndepSet I1 := by
          intro u hu v hv huv; have := hi1 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
          convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
          unfold G; simp +decide [ SimpleGraph.fromRel_adj ] ;
          simp +decide [ SimpleGraph.adj_comm, huv ];
          exact fun _ => by simpa [ Sum.inl_injective.ne_iff ] using huv;
        have h_cover_H : K1 ∪ K2 ∪ I1 = Set.univ := by
          ext x; replace h_cover := Set.ext_iff.mp h_cover ( Sum.inl x ) ; aesop;
        have hK1_card : K1.ncard ≤ 1 := by
          exact h_k1_inter_H_le_one
        exact lemma_H_not_covered_by_small_cliques_and_indep K1 K2 I1 h_cover_H hK1_clique hK2_clique hI1_indep hK1_card

/-
G cannot be covered by 2 cliques and 1 independent set.
-/
theorem lemma_G_no_cover_2K_1I (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    ¬ ∃ (k1 k2 i1 : Set (G_V sizes)), k1 ∪ k2 ∪ i1 = Set.univ ∧
    (G sizes).IsClique k1 ∧ (G sizes).IsClique k2 ∧ (G sizes).IsIndepSet i1 := by
      by_contra h_contra
      obtain ⟨k1, k2, i1, h_cover, hk1, hk2, hi1⟩ := h_contra;
      have h_empty : (i1.preimage Sum.inl).Nonempty → False := by
        exact fun h => lemma_G_no_cover_2K_1I_nonempty_I sizes h_sizes k1 k2 i1 h_cover hk1 hk2 hi1 h;
      -- Since $i1 \cap H = \emptyset$, we have $H \subseteq k1 \ �cup� k2$.
      have h_subset : (Set.range Sum.inl) ⊆ k1 ∪ k2 := by
        simp_all +decide [ Set.subset_def, Set.ext_iff ];
        exact fun x => Or.resolve_right ( h_cover _ ) fun hx => h_empty ⟨ x, hx ⟩;
      -- Let $c1 = k1 \cap H$ and $c2 = k2 \cap H$. Then $c1$ and $c2$ are cliques in $H$.
      set c1 := k1.preimage Sum.inl
      set c2 := k2.preimage Sum.inl
      have hc1 : H.IsClique c1 := by
        intro u hu v hv huv;
        have := hk1 hu hv; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
        convert this ( by simpa [ Sum.inl_injective.ne_iff ] using huv ) using 1;
        unfold G; simp +decide [ SimpleGraph.fromRel_adj ] ;
        simp +decide [ SimpleGraph.adj_comm, huv ];
        exact fun _ => by simpa [ Sum.inl_injective.ne_iff ] using huv;
      have hc2 : H.IsClique c2 := by
        intro u hu v hv huv; have := hk2; simp_all +decide [ SimpleGraph.IsClique ] ;
        convert this hu hv using 1;
        simp +decide [ H, G ];
        grind
      have hc1c2 : c1 ∪ c2 = Set.univ := by
        ext x; specialize h_subset ( Set.mem_range_self x ) ; aesop;
      have h_contra : ∃ (k1 k2 : Set H_V), k1 ∪ k2 = Set.univ ∧ H.IsClique k1 ∧ H.IsClique k2 := by
        exact ⟨ c1, c2, hc1c2, hc1, hc2 ⟩
      exact H_no_cover_2K h_contra

/-
G is not 3-cochromatic-colorable.
-/
theorem lemma_G_not_cochromatic_3 (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    ¬ CochromaticColorable (G sizes) 3 := by
      intro h;
      -- Let `S_0 := c ⁻¹' {0}`, `S_1 := c ⁻¹' {1}`, `S_2 := c ⁻¹' {2}`.
      obtain ⟨c, hc⟩ := h
      set S0 := c ⁻¹' {0}
      set S1 := c ⁻¹' {1}
      set S2 := c ⁻¹' {2};
      -- For each `i`, let `is_clique_i` � be� true if ` �S�_i` is a clique, and false otherwise (in which case it is an independent set).
      have h_clique_indep : ∀ i : Fin 3, (G sizes).IsClique (c ⁻¹' {i}) ∨ (G sizes).IsIndepSet (c ⁻¹' {i}) := by
        exact fun i => hc i;
      -- We can count the number of cliques.
      by_cases h0 : (G sizes).IsClique S0
      by_cases h1 : (G sizes).IsClique S1
      by_cases h2 : (G sizes).IsClique S2;
      · apply lemma_G_no_cover_3K sizes h_sizes;
        grind;
      · apply lemma_G_no_cover_2K_1I sizes h_sizes;
        grind;
      · by_cases h2 : (G sizes).IsClique S2;
        · -- Then `S0, � S�2` are � cli�ques, `S1` is independent. This contradicts `lemma_G_no_cover_2K_1I`.
          have h_contradiction : ∃ (k1 k2 i1 : Set (G_V sizes)), k1 ∪ k2 ∪ i1 = Set.univ ∧ (G sizes).IsClique k1 ∧ (G sizes).IsClique k2 ∧ (G sizes).IsIndepSet i1 := by
            grind;
          exact absurd h_contradiction ( by simpa using lemma_G_no_cover_2K_1I sizes h_sizes );
        · -- Since S1 and S �2� are independent sets �,� their union with S0 (the clique) should cover the entire graph. But since S0 is a clique, any two vertices in S0 are adjacent. However, if S1 and S2 are independent, they can't have any edges between them. This leads to a contradiction because the union of S0, S1, and S2 should cover all vertices, but the presence of edges in S0 and the independence of S1 and S2 makes it impossible.
          have h_contradiction : ¬(S0 ∪ S1 ∪ S2 = Set.univ) := by
            exact fun h => lemma_G_no_cover_1K_2I sizes h_sizes ⟨ S0, S1, S2, h, h0, by simpa using h_clique_indep 1 |> Or.resolve_left <| h1, by simpa using h_clique_indep 2 |> Or.resolve_left <| h2 ⟩;
          grind;
      · cases h_clique_indep 0 <;> cases h_clique_indep 1 <;> cases h_clique_indep 2 <;> simp_all +decide only [Fin.forall_fin_succ];
        grind;
        grind;
        grind +ring;
        · contradiction;
        · have := lemma_G_no_cover_2K_1I sizes h_sizes;
          grind;
        · apply lemma_G_no_cover_1K_2I sizes h_sizes;
          grind;
        · apply lemma_G_no_cover_1K_2I sizes h_sizes;
          grind;
        · exact lemma_G_no_cover_3I sizes h_sizes ⟨ S0, S1, S2, by
            grind, by assumption, by assumption, by assumption ⟩

/-
The cochromatic number of G is at least 4.
-/
theorem G_cochromatic_ge_4 (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    cochromaticNumber (G sizes) ≥ 4 := by
      -- By definition of cochromatic number, if there exists an n < 4 such that the graph is cochromatic-colorable with n colors, then this contradicts the fact that it's not 3-colorable.
      have h_contra : ¬∃ n < 4, CochromaticColorable (G sizes) n := by
        intro h
        obtain ⟨n, hn_lt, hn_colorable⟩ := h
        have h_contra : CochromaticColorable (G sizes) 3 := by
          obtain ⟨c, hc⟩ := hn_colorable;
          interval_cases n <;> simp_all +decide [ IsCochromaticColoring ];
          · exact False.elim <| Fin.elim0 <| c <| Sum.inl H_V.c;
          · use fun x => 0; simp +decide [ IsCochromaticColoring ] ;
            simp +decide [ Fin.forall_fin_succ, Set.preimage ];
            convert hc using 2 <;> ext x <;> simp +decide [ Fin.eq_zero ];
          · use fun x => Fin.castLE ( by decide ) ( c x );
            intro i; fin_cases i <;> simp_all +decide [ IsCochromaticColoring ] ;
            · convert hc.1 using 1;
              · simp +decide [ Set.preimage, Fin.castLE ];
              · simp +decide [ Set.preimage, Fin.castLE ];
            · convert hc.2 using 1;
              · simp +decide [ Set.preimage, Fin.castLE ];
                simp +decide [ Fin.ext_iff, Set.ext_iff ];
              · simp +decide [ Set.preimage, Fin.ext_iff ];
            · simp +decide [ Fin.castLE, Set.preimage ];
              simp +decide [ Fin.ext_iff, Set.ext_iff ];
              exact Or.inl fun x hx y hy hxy => by have := Fin.is_lt ( c x ) ; have := Fin.is_lt ( c y ) ; aesop;
          · exact ⟨ c, hc ⟩
        exact lemma_G_not_cochromatic_3 sizes h_sizes h_contra;
      contrapose! h_contra;
      unfold cochromaticNumber at h_contra;
      -- Since the infimum is the greatest lower bound, if it's less than 4, there must be some element in the set that is less than 4.
      obtain ⟨n, hn⟩ : ∃ n ∈ {n : ℕ∞ | ∃ m : ℕ, n = m ∧ CochromaticColorable (G sizes) m}, n < 4 := by
        exact exists_lt_of_csInf_lt ( by exact Set.nonempty_iff_ne_empty.2 <| by aesop_cat ) h_contra;
      aesop

/-
The graph G satisfies: clique number < 5, cochromatic number = 4, and chromatic number = 7.
-/
theorem main_theorem (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    (G sizes).CliqueFree 5 ∧
    cochromaticNumber (G sizes) = 4 ∧
    (G sizes).chromaticNumber = 7 := by
      -- G is not 3-cochromatic-colorable, so its co �chrom�atic number is at least 4.
      have h_cochromatic_ge_4 : 4 ≤ cochromaticNumber (G sizes) := by
        exact G_cochromatic_ge_4 sizes h_sizes
      exact ⟨G_clique_free_5 sizes, by
        exact le_antisymm ( G_cochromatic_le_4 sizes ) h_cochromatic_ge_4, by
        exact le_antisymm ( G_chromatic_le_7 sizes ) ( G_chromatic_ge_7 sizes h_sizes )⟩

/-
The graph H contains a clique of size 4.
-/
theorem lemma_H_has_clique_4 : ∃ K : Finset H_V, H.IsClique K ∧ K.card = 4 := by
  -- Consider the set $K = \{a_0, a_1, b_0, b_1\}$.
  use {H_V.a 0, H_V.a 1, H_V.b 0, H_V.b 1};
  simp +decide [ H, SimpleGraph.IsClique ]

/-
The graph G satisfies: clique number = 4, cochromatic number = 4, and chromatic number = 7.
-/
theorem steiner_graph (sizes : X_collection → ℕ) (h_sizes : ∀ X, sizes X > 0) :
    (G sizes).cliqueNum = 4 ∧
    cochromaticNumber (G sizes) = 4 ∧
    (G sizes).chromaticNumber = 7 := by
  refine' ⟨ _, _, _ ⟩;
  · refine' le_antisymm ( csSup_le _ _ ) ( le_csSup _ _ );
    · refine' ⟨ 0, ⟨ ∅, _ ⟩ ⟩ ; simp +decide [ SimpleGraph.IsNClique ];
    · rintro n ⟨ s, hs ⟩;
      have := G_clique_free_5 sizes;
      contrapose! this;
      simp_all +decide [ SimpleGraph.CliqueFree ];
      obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( show 5 ≤ s.card from by linarith [ hs.2 ] );
      exact ⟨ t, by have := hs.1; exact ⟨ by aesop_cat, ht.2 ⟩ ⟩;
    · use 4;
      intro n hn
      obtain ⟨s, hs⟩ := hn
      have h_clique_size : s.card ≤ 4 := by
        have h_clique_size : (G sizes).CliqueFree 5 := by
          exact?;
        contrapose! h_clique_size;
        simp_all +decide [ SimpleGraph.CliqueFree ];
        exact Exists.elim ( Finset.exists_subset_card_eq h_clique_size ) fun t ht => ⟨ t, hs.1.subset ht.1, ht.2 ⟩;
      cases hs ; aesop;
    · -- By definition of $G$, � we� know that it contains a clique of size 4.
      obtain ⟨K, hK⟩ : ∃ K : Finset H_V, H.IsClique K ∧ K.card = 4 := by
        exact?;
      refine' ⟨ Finset.image ( fun v => Sum.inl v ) K, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isClique_iff, Finset.card_image_of_injective, Function.Injective ];
      · simp_all +decide [ Set.Pairwise ];
        unfold G; aesop;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by injection hxy, hK.2 ];
  · exact le_antisymm ( G_cochromatic_le_4 sizes ) ( G_cochromatic_ge_4 sizes h_sizes );
  · exact le_antisymm ( G_chromatic_le_7 sizes ) ( G_chromatic_ge_7 sizes h_sizes )

def erdos_762 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  G.CliqueFree 5 →
  4 ≤ cochromaticNumber G →
  G.chromaticNumber ≤ cochromaticNumber G + 2

theorem not_erdos_762 : ¬ erdos_762 := by
  classical
  intro hE
  let sizes : X_collection → ℕ := fun _ => 1
  have h_sizes : ∀ X, sizes X > 0 := by
    intro X
    simp [sizes]
  rcases main_theorem sizes h_sizes with ⟨hCliqueFree5, hCochrom, hChrom⟩
  have hfinite_setHV : Finite (Set H_V) := by
    refine Finite.of_injective
      (f := fun s : Set H_V => fun v : H_V => decide (v ∈ s)) ?_
    intro s t hst
    ext v
    have hv : decide (v ∈ s) = decide (v ∈ t) := by
      simpa using congrArg (fun f : H_V → Bool => f v) hst
    constructor
    · intro hs
      have hs' : decide (v ∈ s) = true := by exact decide_eq_true hs
      have ht' : decide (v ∈ t) = true := hv.symm.trans hs'
      exact (Set.mem_iff_boolIndicator t v).mpr ht'
    · intro ht
      have ht' : decide (v ∈ t) = true := by exact decide_eq_true ht
      have hs' : decide (v ∈ s) = true := hv.trans ht'
      exact (Set.mem_iff_boolIndicator s v).mpr hs'
  haveI : Finite (Set H_V) := hfinite_setHV
  haveI : Finite X_collection := by infer_instance
  haveI : Finite (G_V sizes) := by
    unfold G_V
    infer_instance
  letI : Fintype (G_V sizes) := Fintype.ofFinite (G_V sizes)
  have h4le : (4 : ℕ∞) ≤ cochromaticNumber (G sizes) := by
    simp [hCochrom]
  have hbound :
      (G sizes).chromaticNumber ≤ cochromaticNumber (G sizes) + 2 := by
    exact hE (V := G_V sizes) (G := G sizes) hCliqueFree5 h4le
  have hcontra : (7 : ℕ∞) ≤ (4 : ℕ∞) + 2 := by
    simpa [hChrom, hCochrom] using hbound
  have : ¬ ((7 : ℕ∞) ≤ (4 : ℕ∞) + 2) := by decide
  exact this hcontra

#print axioms not_erdos_762
-- 'Erdos762.not_erdos_762' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]

#show_unused not_erdos_762 main_theorem steiner_graph

end Erdos762
