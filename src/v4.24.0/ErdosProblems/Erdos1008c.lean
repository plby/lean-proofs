import Mathlib

set_option maxHeartbeats 0

/-
A set of edges forms a C4 if it has size 4 and the graph formed by these edges contains a C4.
-/
def is_C4 {V : Type} [DecidableEq V] (s : Finset (Sym2 V)) : Prop :=
  s.card = 4 ∧ ¬ (SimpleGraph.cycleGraph 4).Free (SimpleGraph.fromEdgeSet (s : Set (Sym2 V)))

/-
Defines `disjoint_pairs` as the set of pairs of disjoint edges, and proves that the number of such pairs is at most half the square of the number of edges.
-/
open SimpleGraph Finset Classical

def is_disjoint_pair {V : Type} (s : Finset (Sym2 V)) : Prop :=
  s.card = 2 ∧ ∀ e ∈ s, ∀ f ∈ s, e ≠ f → ∀ v, v ∈ e → v ∉ f

noncomputable def disjoint_pairs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  (G.edgeFinset.powersetCard 2).filter is_disjoint_pair

lemma disjoint_pairs_card_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  (disjoint_pairs G).card ≤ (G.edgeFinset.card) ^ 2 / 2 := by
    -- The set `disjoint_pairs` is a subset of all pairs of edges.
    have h_disjoint_le_all_pairs : (disjoint_pairs G).card ≤ Finset.card (Finset.powersetCard 2 G.edgeFinset) := by
      refine Finset.card_le_card ?_;
      unfold disjoint_pairs; aesop;
    refine le_trans h_disjoint_le_all_pairs ?_;
    norm_num [ sq, Nat.mul_div_assoc ];
    exact Nat.le_div_iff_mul_le zero_lt_two |>.2 ( by induction' ( Finset.card ( Finset.filter ( Membership.mem G.edgeSet ) Finset.univ ) ) with n ih <;> norm_num [ Nat.choose ] at * ; nlinarith )

/-
Defines `C4s` as the set of C4 subgraphs. Proves that every C4 subgraph contains exactly 2 disjoint pairs of edges.
-/
noncomputable def C4s {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  (G.edgeFinset.powersetCard 4).filter is_C4

lemma c4_contains_two_disjoint_pairs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∀ c ∈ C4s G, ((disjoint_pairs G).filter (λ p => p ⊆ c)).card = 2 := by
    intro c hc;
    -- By definition of $C4s$, there exist vertices $v₁$, $v₂$, $v₃$, and $v₄$ such that $c = \{\{v₁, v₂\}, \{v₂, v₃\}, \{v₃, v₄\}, \{v₄, v₁\}\}$.
    obtain ⟨v₁, v₂, v₃, v₄, hv⟩ : ∃ v₁ v₂ v₃ v₄ : V, c = {Sym2.mk (v₁, v₂), Sym2.mk (v₂, v₃), Sym2.mk (v₃, v₄), Sym2.mk (v₄, v₁)} ∧ v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₃ ≠ v₄ ∧ v₄ ≠ v₁ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₄ := by
      unfold C4s at hc;
      unfold is_C4 at hc;
      simp_all +decide [ SimpleGraph.fromEdgeSet ];
      rcases hc.2.2 with ⟨ f, hf ⟩;
      use f 0, f 1, f 2, f 3;
      have h_edges : c = {Sym2.mk (f 0, f 1), Sym2.mk (f 1, f 2), Sym2.mk (f 2, f 3), Sym2.mk (f 3, f 0)} := by
        have h_edges : c ⊇ {Sym2.mk (f 0, f 1), Sym2.mk (f 1, f 2), Sym2.mk (f 2, f 3), Sym2.mk (f 3, f 0)} := by
          simp_all +decide [ Finset.subset_iff, Set.subset_def ];
          exact ⟨ f.map_adj ( by decide ) |>.1, f.map_adj ( by decide ) |>.1, f.map_adj ( by decide ) |>.1, f.map_adj ( by decide ) |>.1 ⟩;
        have h_card : Finset.card ({Sym2.mk (f 0, f 1), Sym2.mk (f 1, f 2), Sym2.mk (f 2, f 3), Sym2.mk (f 3, f 0)} : Finset (Sym2 V)) = 4 := by
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> simp +decide [ hf.eq_iff ];
        rw [ Finset.eq_of_subset_of_card_le h_edges ] ; aesop;
      exact ⟨ h_edges, hf.ne ( by decide ), hf.ne ( by decide ), hf.ne ( by decide ), hf.ne ( by decide ), hf.ne ( by decide ), hf.ne ( by decide ) ⟩;
    -- The set of pairs of edges in $c$ that are disjoint is exactly $\{\{ \{v₁, v₂\}, \{v₃, v₄\} \}, \{ \{v₂, v₃\}, \{v₄, v₁\} \}\}$.
    have h_disjoint_pairs : Finset.filter (fun p => p ⊆ c) (disjoint_pairs G) = { {Sym2.mk (v₁, v₂), Sym2.mk (v₃, v₄)}, {Sym2.mk (v₂, v₃), Sym2.mk (v₄, v₁)} } := by
      ext p;
      constructor;
      · simp [disjoint_pairs];
        intro hp hp' hp'' hp'''; rw [ Finset.card_eq_two ] at hp'; obtain ⟨ e₁, e₂, he₁, he₂, rfl ⟩ := hp'; simp_all +decide [ Finset.subset_iff ] ;
        rcases hp''' with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> simp_all +decide
        all_goals unfold is_disjoint_pair at hp''; simp_all +decide
        · exact Or.inl <| Finset.pair_comm _ _;
        · exact Or.inr ( Finset.pair_comm _ _ );
      · simp [hv];
        rintro ( rfl | rfl ) <;> simp_all +decide [ Finset.subset_iff ];
        · refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
          · simp_all +decide [ Finset.subset_iff, C4s ];
          · constructor <;> simp +decide [ * ];
            grind;
        · refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
          · simp_all +decide [ Finset.subset_iff, C4s ];
          · unfold is_disjoint_pair; aesop;
    rw [ h_disjoint_pairs, Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide
    simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff, hv ];
    aesop

/-
Proves that if a C4 graph contains two disjoint edges $\{u, v\}$ and $\{x, y\}$, then the edge set must be either $\{\{u, v\}, \{x, y\}, \{u, x\}, \{v, y\}\}$ or $\{\{u, v\}, \{x, y\}, \{u, y\}, \{v, x\}\}$.
-/
lemma C4_containing_disjoint_pair_structure {V : Type} [DecidableEq V] (c : Finset (Sym2 V)) (u v x y : V) :
  is_C4 c →
  {Sym2.mk (u, v), Sym2.mk (x, y)} ⊆ c →
  u ≠ v → x ≠ y →
  ({u, v} : Finset V) ∩ {x, y} = ∅ →
  c = {Sym2.mk (u, v), Sym2.mk (x, y), Sym2.mk (u, x), Sym2.mk (v, y)} ∨
  c = {Sym2.mk (u, v), Sym2.mk (x, y), Sym2.mk (u, y), Sym2.mk (v, x)} := by
    unfold is_C4;
    intro h hc huv hxy hxy';
    -- Since $c$ is a C4, it must be isomorphic to the cycle graph $C_4$. Let $\phi$ be an isomorphism from $C_4$ to the subgraph induced by $c$.
    obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : Fin 4 → V, c = {Sym2.mk (ϕ 0, ϕ 1), Sym2.mk (ϕ 1, ϕ 2), Sym2.mk (ϕ 2, ϕ 3), Sym2.mk (ϕ 3, ϕ 0)} := by
      simp_all +decide [ SimpleGraph.Free ];
      obtain ⟨ ϕ, hϕ ⟩ := h.2;
      refine' ⟨ fun i => ϕ i, _ ⟩;
      have h_edges : ∀ i : Fin 4, Sym2.mk (ϕ i, ϕ (i + 1)) ∈ c := by
        intro i; have := ϕ.map_adj ( show SimpleGraph.Adj ( SimpleGraph.cycleGraph 4 ) i ( i + 1 ) from by fin_cases i <;> trivial ) ; aesop;
      have h_edges_subset : {Sym2.mk (ϕ 0, ϕ 1), Sym2.mk (ϕ 1, ϕ 2), Sym2.mk (ϕ 2, ϕ 3), Sym2.mk (ϕ 3, ϕ 0)} ⊆ c := by
        simp_all +decide [ Finset.insert_subset_iff ];
        exact ⟨ h_edges 0, h_edges 1, h_edges 2, h_edges 3 ⟩;
      have h_edges_card : ({Sym2.mk (ϕ 0, ϕ 1), Sym2.mk (ϕ 1, ϕ 2), Sym2.mk (ϕ 2, ϕ 3), Sym2.mk (ϕ 3, ϕ 0)} : Finset (Sym2 V)).card = 4 := by
        rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> simp +decide [ hϕ.eq_iff ];
      rw [ Finset.eq_of_subset_of_card_le h_edges_subset ] ; aesop;
    simp_all +decide [ Finset.subset_iff ];
    simp_all +decide [ Finset.ext_iff ];
    rcases hc with ⟨ ⟨ ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ⟩, huv, hxy, hxy' ⟩ <;> simp_all +decide [ Sym2.eq_swap ];
    · rcases ‹_› with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
      · grind;
      · grind;
    · rcases ‹_› with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
      · grind;
      · exact Or.inr fun a => by tauto;
    · rcases ‹u = ϕ 2 ∧ v = ϕ 3 ∨ u = ϕ 3 ∧ v = ϕ 2› with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
      · exact Or.inr fun a => by tauto;
      · grind;
    · rcases ‹u = ϕ 2 ∧ v = ϕ 3 ∨ u = ϕ 3 ∧ v = ϕ 2› with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
      · grind;
      · exact Or.inr fun a => by tauto;
    · rcases ‹ ( u = ϕ 1 ∧ v = ϕ 2 ∨ u = ϕ 2 ∧ v = ϕ 1 ) ∨ ( u = ϕ 2 ∧ v = ϕ 3 ∨ u = ϕ 3 ∧ v = ϕ 2 ) ∨ u = ϕ 3 ∧ v = ϕ 0 ∨ u = ϕ 0 ∧ v = ϕ 3 › with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
      all_goals rcases ‹ ( x = ϕ 1 ∧ y = ϕ 2 ∨ x = ϕ 2 ∧ y = ϕ 1 ) ∨ ( x = ϕ 2 ∧ y = ϕ 3 ∨ x = ϕ 3 ∧ y = ϕ 2 ) ∨ x = ϕ 3 ∧ y = ϕ 0 ∨ x = ϕ 0 ∧ y = ϕ 3 › with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ] ;
      all_goals simp_all +decide [ or_comm, or_left_comm ] ;

/-
Proves that any disjoint pair of edges is contained in at most 2 C4 subgraphs.
-/
lemma disjoint_pair_in_at_most_two_C4s {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∀ p ∈ disjoint_pairs G, ((C4s G).filter (λ c => p ⊆ c)).card ≤ 2 := by
    intro p hp;
    -- Let $p \in disjoint\_pairs(G)$. Then $p = \{e_1, e_2\}$ where $e_1, e_2$ are disjoint edges. Let $e_1 = \{u, v\}$ and $e_2 = \{x, y\}$.
    obtain ⟨u, v, x, y, huv, hxy, h_disjoint⟩ : ∃ u v x y : V, u ≠ v ∧ x ≠ y ∧ ({u, v} : Finset V) ∩ {x, y} = ∅ ∧ p = {Sym2.mk (u, v), Sym2.mk (x, y)} := by
      unfold disjoint_pairs at hp;
      unfold is_disjoint_pair at hp;
      simp +zetaDelta at *;
      rcases Finset.card_eq_two.mp hp.2.1 with ⟨ e₁, e₂, hne, rfl ⟩ ; rcases e₁ with ⟨ u, v ⟩ ; rcases e₂ with ⟨ x, y ⟩ ; use u, v, by
        intro h; simp_all +decide [ SimpleGraph.edgeSet ] ;
        simp_all +decide [ Set.insert_subset_iff ], x, y, by
        intro h; simp_all +decide
        simp_all +decide [ Set.insert_subset_iff ] ; ; aesop;
    -- By `C4_containing_disjoint_pair_structure`, any $c \in C4s(G)$ containing $p$ must be equal to $C_1 = \{e_1, e_2, \{u, x\}, \{v, y\}\}$ or $C_2 = \{e_1, e_2, \{u, y\}, \{v, x\}\}$.
    have h_c4_structure : ∀ c ∈ C4s G, p ⊆ c → c = {Sym2.mk (u, v), Sym2.mk (x, y), Sym2.mk (u, x), Sym2.mk (v, y)} ∨ c = {Sym2.mk (u, v), Sym2.mk (x, y), Sym2.mk (u, y), Sym2.mk (v, x)} := by
      intros c hc hpc
      have h_c4_structure : is_C4 c ∧ {Sym2.mk (u, v), Sym2.mk (x, y)} ⊆ c ∧ u ≠ v ∧ x ≠ y ∧ ({u, v} : Finset V) ∩ {x, y} = ∅ := by
        unfold C4s at hc; aesop;
      exact C4_containing_disjoint_pair_structure c u v x y h_c4_structure.1 h_c4_structure.2.1 h_c4_structure.2.2.1 h_c4_structure.2.2.2.1 h_c4_structure.2.2.2.2;
    exact le_trans ( Finset.card_le_card ( show { c ∈ C4s G | p ⊆ c } ⊆ { { s(u, v), s(x, y), s(u, x), s(v, y) }, { s(u, v), s(x, y), s(u, y), s(v, x) } } by intros c hc; aesop ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by norm_num;

/-
Proves that the number of C4s is at most the number of disjoint pairs of edges, using double counting.
-/
lemma card_C4s_le_disjoint_pairs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  (C4s G).card ≤ (disjoint_pairs G).card := by
    -- By double counting, we have $S = \sum_{c \in C4s(G)} |\{p \in disjoint_pairs(G) \mid p \subseteq c\}| = \sum_{p \in disjoint_pairs(G)} |\{c \in C4s(G) \mid p \subseteq c\}|$.
    have h_double_counting : ∑ c ∈ C4s G, ((disjoint_pairs G).filter (λ p => p ⊆ c)).card = ∑ p ∈ disjoint_pairs G, ((C4s G).filter (λ c => p ⊆ c)).card := by
      simp +decide only [card_eq_sum_ones, sum_filter];
      exact Finset.sum_comm;
    -- By definition of $c4_contains_two_disjoint_pairs$, for every $c \in C4s(G)$, the term in the sum is 2.
    have h_sum_c4 : ∀ c ∈ C4s G, ((disjoint_pairs G).filter (λ p => p ⊆ c)).card = 2 := by
      exact fun c a => c4_contains_two_disjoint_pairs G c a;
    -- By definition of $disjoint_pair_in_at_most_two_C4s$, for every $p \in disjoint_pairs(G)$, the term in the sum is at most 2.
    have h_sum_disjoint_pairs : ∀ p ∈ disjoint_pairs G, ((C4s G).filter (λ c => p ⊆ c)).card ≤ 2 := by
      exact fun p a => disjoint_pair_in_at_most_two_C4s G p a;
    simp_all +decide
    exact le_of_mul_le_mul_right ( h_double_counting.le.trans <| Finset.sum_le_card_nsmul _ _ _ fun x hx => h_sum_disjoint_pairs x hx ) zero_lt_two

/-
Proves that the number of C4s is at most half the square of the number of edges.
-/
lemma card_C4s_le_m_sq_div_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  (C4s G).card ≤ (G.edgeFinset.card) ^ 2 / 2 := by
    convert card_C4s_le_disjoint_pairs G |> le_trans <| disjoint_pairs_card_le G using 1

/-
Proves that for any set $E$ and collection of subsets $C$ of size $k$, there exists a subset $S \subseteq E$ such that $|S| - |\{c \in C : c \subseteq S\}| \ge p |E| - p^k |C|$.
-/
lemma probabilistic_exists {α : Type} [DecidableEq α] (E : Finset α) (C : Finset (Finset α)) (k : ℕ) (p : ℝ)
    (hk : ∀ c ∈ C, c.card = k) (hc : ∀ c ∈ C, c ⊆ E) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
  ∃ S ⊆ E, (S.card : ℝ) - (C.filter (λ c => c ⊆ S)).card ≥ p * E.card - p^k * C.card := by
    -- By linearity of expectation, $\mathbb{E}[X] = \sum_{e \in E} \mathbb{P}(e \in S) = |E| p$.
    have h_exp_X : (Finset.sum (Finset.powerset E) (fun S => (Finset.card S : ℝ) * (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) = (Finset.card E : ℝ) * p := by
      -- We'll use the fact that $\sum_{x \in \text{powerset}(E)} |x| p^{|x|} (1 - p)^{|E| - |x|}$ is the expected number of elements in a random subset of $E$.
      have h_exp : ∑ x ∈ Finset.powerset E, (Finset.card x : ℝ) * p ^ (Finset.card x) * (1 - p) ^ (Finset.card E - Finset.card x) = ∑ x ∈ Finset.range (Finset.card E + 1), (x : ℝ) * Nat.choose (Finset.card E) x * p ^ x * (1 - p) ^ (Finset.card E - x) := by
        rw [ Finset.sum_powerset ];
        exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      -- We'll use the fact that $\sum_{x=0}^{n} x \binom{n}{x} p^x (1-p)^{n-x}$ is the expected value of a binomial distribution with parameters $n$ and $p$.
      have h_binom : ∑ x ∈ Finset.range (Finset.card E + 1), (x : ℝ) * Nat.choose (Finset.card E) x * p ^ x * (1 - p) ^ (Finset.card E - x) = Finset.card E * p * ∑ x ∈ Finset.range (Finset.card E), Nat.choose (Finset.card E - 1) x * p ^ x * (1 - p) ^ (Finset.card E - 1 - x) := by
        norm_num [ Finset.sum_range_succ' ];
        rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rcases n : Finset.card E with ( _ | n ) <;> simp_all +decide [ add_comm ] ; ring_nf;
        rw [ Nat.add_comm 1, Nat.add_comm 1 ] ; rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
        field_simp;
        rw [ Nat.factorial_succ, Nat.factorial_succ ] ; push_cast [ Nat.succ_sub ( by linarith : x ≤ _ ) ] ; ring;
      rcases n : Finset.card E with ( _ | n ) <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      exact Or.inl ( by rw [ show ( ∑ x ∈ Finset.range ( _ + 1 ), p ^ x * ( ( Nat.choose _ x : ℝ ) * ( 1 - p ) ^ ( _ - x ) ) ) = ( p + ( 1 - p ) ) ^ ( ‹_› : ℕ ) by rw [ add_pow ] ; congr ; ext ; ring ] ; norm_num );
    -- By linearity of expectation, $\mathbb{E}[Y] = \sum_{c \in C} \mathbb{P}(c \subseteq S) = |C| p^k$.
    have h_exp_Y : (Finset.sum (Finset.powerset E) (fun S => (Finset.card (Finset.filter (fun c => c ⊆ S) C) : ℝ) * (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) = (Finset.card C : ℝ) * (p ^ k) := by
      -- For each $c \in C$, let $I_c$ be the indicator variable that $c \subseteq S$.
      have h_indicator : ∀ c ∈ C, (Finset.sum (Finset.powerset E) (fun S => (if c ⊆ S then 1 else 0) * (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) = p ^ k := by
        intro c hc'
        have h_indicator : ∑ x ∈ Finset.powerset E, (if c ⊆ x then p ^ (Finset.card x) * (1 - p) ^ (Finset.card E - Finset.card x) else 0) = p ^ (Finset.card c) * ∑ x ∈ Finset.powerset (E \ c), p ^ (Finset.card x) * (1 - p) ^ (Finset.card E - Finset.card c - Finset.card x) := by
          have h_indicator : ∑ x ∈ Finset.powerset E, (if c ⊆ x then p ^ (Finset.card x) * (1 - p) ^ (Finset.card E - Finset.card x) else 0) = ∑ x ∈ Finset.powerset (E \ c), p ^ (Finset.card (c ∪ x)) * (1 - p) ^ (Finset.card E - Finset.card (c ∪ x)) := by
            rw [ ← Finset.sum_filter ];
            refine' Finset.sum_bij ( fun x hx => x \ c ) _ _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
            · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; ext x; by_cases hx : x ∈ c <;> simp_all +decide [ Finset.ext_iff ] ;
            · exact fun b hb => ⟨ b ∪ c, ⟨ fun x hx => by aesop, fun x hx => by aesop ⟩, by aesop ⟩;
            · intro a ha₁ ha₂; rw [ Finset.union_eq_right.mpr ha₂ ] ;
          rw [ h_indicator, Finset.mul_sum _ _ _ ];
          refine' Finset.sum_congr rfl fun x hx => _;
          rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun y hy₁ hy₂ => by have := Finset.mem_sdiff.mp ( Finset.mem_powerset.mp hx hy₂ ) ; aesop ) ] ; ring_nf;
          rw [ Nat.sub_sub ];
        -- The sum $\sum_{x \in \text{powerset}(E \setminus c)} p^{|x|} (1 - p)^{|E \setminus c| - |x|}$ is the binomial expansion of $(p + (1 - p))^{|E \setminus c|}$.
        have h_binom : ∑ x ∈ Finset.powerset (E \ c), p ^ (Finset.card x) * (1 - p) ^ (Finset.card (E \ c) - Finset.card x) = (p + (1 - p)) ^ (Finset.card (E \ c)) := by
          exact sum_pow_mul_eq_add_pow p (1 - p) (E \ c);
        simp_all +decide [ Finset.card_sdiff ];
        rw [ show c ∩ E = c by rw [ Finset.inter_eq_left.mpr ( hc c hc' ) ] ] at h_binom ; aesop;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ x ∈ Finset.powerset E, (∑ c ∈ C, (if c ⊆ x then 1 else 0)) * (p ^ (Finset.card x) * (1 - p) ^ (Finset.card E - Finset.card x)) = ∑ c ∈ C, ∑ x ∈ Finset.powerset E, (if c ⊆ x then 1 else 0) * (p ^ (Finset.card x) * (1 - p) ^ (Finset.card E - Finset.card x)) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_mul _ _ _ ];
      simp_all +decide [ Finset.sum_ite ];
    by_contra! h_contra;
    have h_exp_diff : (Finset.sum (Finset.powerset E) (fun S => ((Finset.card S : ℝ) - (Finset.card (Finset.filter (fun c => c ⊆ S) C) : ℝ)) * (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) < (Finset.card E : ℝ) * p - (Finset.card C : ℝ) * (p ^ k) := by
      have h_exp_diff : (Finset.sum (Finset.powerset E) (fun S => ((Finset.card S : ℝ) - (Finset.card (Finset.filter (fun c => c ⊆ S) C) : ℝ)) * (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) < (Finset.sum (Finset.powerset E) (fun S => (p * (Finset.card E : ℝ) - p ^ k * (Finset.card C : ℝ)) * (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) := by
        apply Finset.sum_lt_sum;
        · exact fun x hx => mul_le_mul_of_nonneg_right ( le_of_lt ( h_contra x ( Finset.mem_powerset.mp hx ) ) ) ( mul_nonneg ( pow_nonneg hp0 _ ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) );
        · by_cases h : p = 0 <;> by_cases h' : 1 - p = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
          · exact ⟨ ∅, Finset.empty_subset _, by simpa using h_contra ∅ ( Finset.empty_subset _ ) ⟩;
          · norm_num [ show p = 1 by linarith ] at *;
            specialize h_contra E ; aesop;
          · exact ⟨ ∅, Finset.empty_subset _, by simpa using mul_lt_mul_of_pos_left ( h_contra ∅ ( Finset.empty_subset _ ) ) ( mul_pos ( pow_pos ( lt_of_le_of_ne hp0 ( Ne.symm h ) ) 0 ) ( pow_pos ( lt_of_le_of_ne ( sub_nonneg.mpr hp1 ) ( Ne.symm h' ) ) ( Finset.card E - 0 ) ) ) |> lt_of_lt_of_le <| by ring_nf; norm_num ⟩;
      -- The sum of the probabilities over all subsets is 1.
      have h_sum_prob : (Finset.sum (Finset.powerset E) (fun S => (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) = 1 := by
        have h_sum_prob : (Finset.sum (Finset.powerset E) (fun S => (p ^ (Finset.card S) * (1 - p) ^ (Finset.card E - Finset.card S)))) = (p + (1 - p)) ^ (Finset.card E) := by
          rw [ add_pow ];
          rw [ Finset.sum_powerset ];
          exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_comm, mul_left_comm ] ;
        aesop;
      simp_all +decide [ ← Finset.mul_sum _ _ _ ];
      linarith;
    simp_all +decide [ sub_mul ]

/-
Every graph with m edges contains a C4-free subgraph with at least (1/2) * m^(2/3) edges.
-/
theorem exists_C4_free_subgraph_with_many_edges {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ (S' : Finset (Sym2 V)), S' ⊆ G.edgeFinset ∧
  (∀ s, s ⊆ S' → ¬is_C4 s) ∧
  (S'.card : ℝ) ≥ ((1 : ℝ) / 2) * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) :=
  by
    by_contra h_contra;
    -- Applying the probabilistic method to find such a subset $S'$.
    obtain ⟨S, hS⟩ : ∃ S ⊆ G.edgeFinset, (S.card : ℝ) - (C4s G |>.filter (fun c => c ⊆ S)).card ≥ (1 / (G.edgeFinset.card : ℝ) ^ (1 / 3 : ℝ)) * (G.edgeFinset.card : ℝ) - (1 / (G.edgeFinset.card : ℝ) ^ (4 / 3 : ℝ)) * (C4s G).card := by
      have h_probabilistic : ∃ S ⊆ G.edgeFinset, (S.card : ℝ) - (C4s G |>.filter (fun c => c ⊆ S)).card ≥ (1 / (G.edgeFinset.card : ℝ) ^ (1 / 3 : ℝ)) * (G.edgeFinset.card : ℝ) - (1 / (G.edgeFinset.card : ℝ) ^ (4 / 3 : ℝ)) * (C4s G).card := by
        have h_card_C4s : ∀ c ∈ C4s G, c.card = 4 := by
          unfold C4s; aesop;
        have h_subset_C4s : ∀ c ∈ C4s G, c ⊆ G.edgeFinset := by
          unfold C4s; aesop;
        convert probabilistic_exists G.edgeFinset ( C4s G ) 4 ( 1 / ( G.edgeFinset.card : ℝ ) ^ ( 1 / 3 : ℝ ) ) h_card_C4s h_subset_C4s _ _ using 1 <;> norm_num;
        · norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ];
        · positivity;
        · exact inv_le_one_of_one_le₀ <| Real.one_le_rpow ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec <| show ∃ e, e ∈ G.edgeSet from by
                                                                                                                                                                    by_cases h_empty : G.edgeFinset = ∅;
                                                                                                                                                                    · simp_all +decide [ is_C4 ];
                                                                                                                                                                    · exact Exists.elim ( Finset.nonempty_of_ne_empty h_empty ) fun e he => ⟨ e, by simpa using he ⟩ ⟩ ⟩ ) ( by norm_num );
      exact h_probabilistic;
    -- Let $C_S = \{c \in C4s(G) : c \subseteq S\}$.
    set C_S := (C4s G |>.filter (fun c => c ⊆ S)) with hC_S;
    -- We construct $S'$ by removing one edge from each $c \in C_S$. Specifically, for each $c \in C_S$, choose an edge $e_c \in c$. Let $R = \{e_c : c \in C_S\}$. Let $S' = S \setminus R$.
    obtain ⟨R, hR⟩ : ∃ R : Finset (Sym2 V), R ⊆ S ∧ R.card ≤ C_S.card ∧ ∀ c ∈ C_S, ∃ e ∈ R, e ∈ c := by
      have hR : ∀ c ∈ C_S, ∃ e ∈ S, e ∈ c := by
        simp +zetaDelta at *;
        intro c hc hcs; have := Finset.card_pos.mp ( show 0 < Finset.card c from by rw [ show c.card = 4 from by { exact Finset.mem_powersetCard.mp ( Finset.mem_filter.mp hc |>.1 ) |>.2 } ] ; norm_num ) ; obtain ⟨ e, he ⟩ := this; exact ⟨ e, hcs he, he ⟩ ;
      choose! f hf₁ hf₂ using hR;
      use Finset.image (fun c => f c.1 c.2) (Finset.attach C_S);
      exact ⟨ Finset.image_subset_iff.mpr fun x hx => hf₁ _ _, Finset.card_image_le.trans ( by simp ), fun c hc => ⟨ f c hc, Finset.mem_image.mpr ⟨ ⟨ c, hc ⟩, Finset.mem_attach _ _, rfl ⟩, hf₂ _ _ ⟩ ⟩;
    -- Then $S' = S \setminus R$ is a C4-free subgraph of $G$.
    have hS'_free : ∀ s ⊆ S \ R, ¬is_C4 s := by
      intro s hs hcs; have := hR.2.2 s; simp_all +decide [ Finset.subset_iff ] ;
      obtain ⟨ e, he₁, he₂ ⟩ := hR.2.2 s ( by
        exact Finset.mem_filter.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ Finset.subset_iff.mpr fun x hx => by have := hs hx; aesop, hcs.1 ⟩, hcs ⟩ ) ( by
        exact fun x hx => hs hx |>.1 ) ; exact hs he₂ |>.2 he₁;
    -- Using the inequality from `probabilistic_exists`:
    have hS'_size : (S \ R).card ≥ (1 / (G.edgeFinset.card : ℝ) ^ (1 / 3 : ℝ)) * (G.edgeFinset.card : ℝ) - (1 / (G.edgeFinset.card : ℝ) ^ (4 / 3 : ℝ)) * (C4s G).card := by
      have hS'_size : (S \ R).card ≥ S.card - C_S.card := by
        grind;
      refine le_trans hS.2 ?_;
      norm_cast;
      rw [ Int.subNatNat_eq_coe ] ; omega;
    -- Using `card_C4s_le_m_sq_div_2`, $|C4s(G)| \le m^2/2$.
    have hC4s_le : (C4s G).card ≤ (G.edgeFinset.card : ℝ) ^ 2 / 2 := by
      have := card_C4s_le_m_sq_div_2 G;
      rw [ le_div_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_mul_le_self ( #G.edgeFinset ^ 2 ) 2 ];
    -- Substitute $|C4s(G)| \le m^2/2$ into the inequality for $|S'|$.
    have hS'_size_subst : (S \ R).card ≥ (1 / (G.edgeFinset.card : ℝ) ^ (1 / 3 : ℝ)) * (G.edgeFinset.card : ℝ) - (1 / (G.edgeFinset.card : ℝ) ^ (4 / 3 : ℝ)) * ((G.edgeFinset.card : ℝ) ^ 2 / 2) := by
      exact le_trans ( sub_le_sub_left ( mul_le_mul_of_nonneg_left hC4s_le <| by positivity ) _ ) hS'_size;
    refine h_contra ⟨ S \ R, Finset.sdiff_subset.trans hS.1, hS'_free, hS'_size_subst.trans' ?_ ⟩ ; ring_nf ; norm_num;
    by_cases h : ( Finset.card ( Finset.filter ( Membership.mem G.edgeSet ) Finset.univ ) : ℝ ) = 0 <;> simp_all +decide [ sq, mul_assoc, ← Real.rpow_neg ] ; ring_nf ; norm_num;
    · norm_num [ Finset.filter_eq_empty_iff.mpr, h ];
    · rw [ show ( - ( 4 / 3 : ℝ ) ) = -3⁻¹ - 1 by norm_num, Real.rpow_sub ] <;> norm_num ; ring_nf ; norm_num;
      · rw [ show ( 2 / 3 : ℝ ) = -1 / 3 + 1 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf ; norm_num;
        norm_num [ sq, mul_assoc, ne_of_gt ( show 0 < ( Finset.card ( Finset.filter ( Membership.mem G.edgeSet ) Finset.univ ) : ℝ ) from Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h.choose_spec ⟩ ⟩ ) ] ; ring_nf ; norm_num;
      · exact ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h.choose_spec ⟩ ⟩
