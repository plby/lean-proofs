import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.Assembly
import ErdosProblems.Erdos550.Reservoirs
import ErdosProblems.Erdos550.OffTuranDirectProof
import ErdosProblems.Erdos550.EFRS
import ErdosProblems.Erdos550.ProfileForest

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Outer (analytic) layer of the main-theorem assembly

This file assembles the analytic outer layer of the Erdős 550 proof on top of the
purely combinatorial `assembly_core` (file `Assembly.lean`).  It supplies:

* `ramsey_iso` — Ramsey numbers are invariant under graph isomorphism of the
  second argument;
* `ramsey_Kmult_reindex`, `ramsey_Kmult2_Kbip` — the index/graph bookkeeping
  relating `Kmult k m`, `Kmult (q+1) m'` and `Kbip`;
* `card_le_ramsey` — the trivial lower bound `n ≤ R(T,H)` for an `n`-vertex tree
  `T` and a graph `H` with an edge;
* `profile_to_A1` — the red-profile lower bound (`A1`) from the profile lemma and
  the absence of a blue `T`;
* `erdos_550_large_core` — the clean form of the main theorem (over `Kbip`), the
  analytic core combining EFRS scaling, the off-Turán red density, the clean
  reservoir decomposition, `profile_to_A1` and `assembly_core`.
-/

open SimpleGraph Finset

namespace Erdos550

/-- Ramsey numbers are invariant under isomorphism of the second graph. -/
theorem ramsey_iso {VT : Type*} (T : SimpleGraph VT) {α β : Type*}
    (J : SimpleGraph α) (J' : SimpleGraph β) (e : J ≃g J') :
    ramsey T J = ramsey T J' := by
  unfold ramsey
  congr 1
  ext N
  constructor <;> intro h G <;> rcases h G with h1 | h2
  · exact Or.inl h1
  · exact Or.inr ((show J' ⊑ J from ⟨e.symm.toCopy⟩).trans h2)
  · exact Or.inl h1
  · exact Or.inr ((show J ⊑ J' from ⟨e.toCopy⟩).trans h2)

/-
`Kmult 2 g` is isomorphic to the complete bipartite graph `K_{g0,g1}`.
-/
theorem Kmult2_iso_Kbip (g : Fin 2 → ℕ) : Nonempty (Kmult 2 g ≃g Kbip (g 0) (g 1)) := by
  refine' ⟨ _, _ ⟩;
  refine' Equiv.ofBijective ( fun x => match x with | ⟨ 0, x ⟩ => Sum.inl x | ⟨ 1, x ⟩ => Sum.inr x ) ⟨ fun x y h => _, fun x => _ ⟩;
  all_goals norm_num [ Kbip, Kmult ];
  · rcases x with ⟨ i, x ⟩ ; rcases y with ⟨ j, y ⟩ ; fin_cases i <;> fin_cases j <;> simp +decide at h ⊢; all_goals exact h;
  · cases x <;> aesop;
  · intro a b; rcases a with ⟨ i, a ⟩ ; rcases b with ⟨ j, b ⟩ ; fin_cases i <;> fin_cases j <;> simp +decide ;

/-
Reindexing the parts of a complete multipartite graph along an index
equivalence preserves the Ramsey number.
-/
theorem ramsey_Kmult_reindex {VT : Type*} (T : SimpleGraph VT) {k k' : ℕ}
    (e : Fin k ≃ Fin k') (m : Fin k → ℕ) (m' : Fin k' → ℕ)
    (h : ∀ i, m i = m' (e i)) :
    ramsey T (Kmult k m) = ramsey T (Kmult k' m') := by
  apply Erdos550.ramsey_iso;
  refine' ⟨ Equiv.sigmaCongr e _, _ ⟩;
  exact fun i => Fintype.equivOfCardEq ( by simp +decide [ h i ] );
  simp +decide [ Kmult, SimpleGraph.completeMultipartiteGraph ];
  simp +decide [ Equiv.sigmaCongr ]

/-- `R(T, Kmult 2 g) = R(T, K_{g0,g1})`. -/
theorem ramsey_Kmult2_Kbip {VT : Type*} (T : SimpleGraph VT) (g : Fin 2 → ℕ) :
    ramsey T (Kmult 2 g) = ramsey T (Kbip (g 0) (g 1)) := by
  obtain ⟨e⟩ := Kmult2_iso_Kbip g
  exact ramsey_iso T _ _ e

/-
**Red-profile lower bound (`A1`).**  For `q ≥ 2` and tolerance `ε > 0` there
is `κ' > 0` such that, in any reservoir configuration with the size sandwich
`(1-κ')n ≤ |W i| ≤ (1+κ')n` (where `n = card VT`) and blue induced minimum degree
`≥ (1-κ')n`, if there is no blue `T` then every remainder vertex `x ∈ X` has
total red profile `∑ᵢ |N_red(x)∩W_i|/|W_i| ≥ q-1-ε`.
-/
theorem profile_to_A1 (q : ℕ) (hq : 2 ≤ q) (ε : ℝ) (hε : 0 < ε) :
    ∃ κ' : ℝ, 0 < κ' ∧
      ∀ {VT : Type} [Fintype VT] [DecidableEq VT] {V : Type} [Fintype V] [DecidableEq V]
        (T : SimpleGraph VT) [DecidableRel T.Adj] (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
        (W : Fin q → Finset V) (X : Finset V),
        T.IsTree → 2 ≤ Fintype.card VT →
        (∀ i, Disjoint X (W i)) → (∀ i j, i ≠ j → Disjoint (W i) (W j)) →
        ¬ (T ⊑ Grᶜ) →
        (∀ i, (1 - κ') * (Fintype.card VT : ℝ) ≤ (W i).card ∧
              ((W i).card : ℝ) ≤ (1 + κ') * Fintype.card VT) →
        (∀ i, ∀ v ∈ W i,
          (1 - κ') * (Fintype.card VT : ℝ) ≤ ((Grᶜ.neighborFinset v ∩ W i).card : ℝ)) →
        ∀ x ∈ X, (q : ℝ) - 1 - ε ≤
          ∑ i, ((commonRedNbhd Gr {x} (W i)).card : ℝ) / (W i).card := by
  by_contra! h_contra;
  obtain ⟨κ, δ0, hκ, hδ0, Hprof⟩ := profile_lemma q hq (ε / 4) (by positivity);
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ κ' ≤ δ0 ∧ κ' ≤ ε / (2 * (1 + ε)) := by
    exact ⟨ Min.min ( Min.min κ δ0 ) ( ε / ( 2 * ( 1 + ε ) ) ), lt_min ( lt_min hκ hδ0 ) ( by positivity ), min_le_of_left_le ( min_le_left _ _ ), min_le_of_left_le ( min_le_right _ _ ), min_le_right _ _ ⟩;
  obtain ⟨ VT, inst, inst_1, V, inst_2, inst_3, T, inst_4, Gr, inst_5, W, X, hT, hcardVT, hdisjXW, hdisjW, hNoBlueT, hsize, hbluedeg, x, hx, hsum ⟩ := h_contra κ' hκ'.1;
  have hsumblue : (1 + ε / 4) * (Fintype.card VT : ℝ) ≤ ∑ i, ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) := by
    have hsumblue : ∑ i, ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) ≥ (1 - κ') * (Fintype.card VT : ℝ) * (q - ∑ i, ((commonRedNbhd Gr {x} (W i)).card : ℝ) / (W i).card) := by
      have hsumblue : ∀ i, ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) ≥ (1 - κ') * (Fintype.card VT : ℝ) * (1 - ((commonRedNbhd Gr {x} (W i)).card : ℝ) / (W i).card) := by
        intro i
        have hblue_eq : ((Grᶜ.neighborFinset x ∩ W i).card : ℝ) = (W i).card - ((commonRedNbhd Gr {x} (W i)).card : ℝ) := by
          rw [ eq_sub_iff_add_eq', ← Nat.cast_add ];
          rw [ ← Finset.card_union_of_disjoint ];
          · congr with v ; simp +decide [ SimpleGraph.compl_adj ];
            by_cases hv : v ∈ W i <;> simp +decide [ hv, commonRedNbhd ];
            exact Classical.or_iff_not_imp_left.2 fun h => ⟨ by rintro rfl; exact Finset.disjoint_left.mp ( hdisjXW i ) hx hv, h ⟩;
          · simp +decide [ Finset.disjoint_left, commonRedNbhd ];
            tauto;
        by_cases hi : W i = ∅ <;> simp +decide [ hi, mul_sub, sub_mul ] at hblue_eq ⊢;
        · specialize hsize i ; norm_num [ hi ] at hsize ; nlinarith [ show ( Fintype.card VT : ℝ ) ≥ 2 by norm_cast ];
        · field_simp;
          rw [ add_div', div_add', le_div_iff₀ ] <;> nlinarith [ hsize i, show ( Finset.card ( W i ) : ℝ ) > 0 from Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hi ) ) ];
      refine' le_trans _ ( Finset.sum_le_sum fun i _ => hsumblue i );
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    have hsumblue : (1 - κ') * (q - ∑ i, ((commonRedNbhd Gr {x} (W i)).card : ℝ) / (W i).card) ≥ (1 + ε / 4) := by
      rw [ le_div_iff₀ ] at hκ' <;> nlinarith [ show ( q : ℝ ) ≥ 2 by norm_cast ];
    nlinarith [ show ( Fintype.card VT : ℝ ) ≥ 2 by norm_cast ];
  have := @Hprof VT inst inst_1 V inst_2 inst_3 T inst_4 Grᶜ;
  contrapose! this;
  use inferInstance, x, W;
  refine' ⟨ hT, hcardVT, _, hdisjW, _, hsumblue, _, hNoBlueT ⟩;
  · exact fun i => Finset.disjoint_left.mp ( hdisjXW i ) hx;
  · intro i;
    refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ( 1 + δ0 ) ≥ ( 1 + κ' ) by linarith ) ( Nat.cast_nonneg _ ) );
    exact le_trans ( Nat.cast_le.mpr ( Finset.card_le_card ( Finset.inter_subset_right ) ) ) ( hsize i |>.2 );
  · exact fun i v hv => le_trans ( mul_le_mul_of_nonneg_right ( by linarith ) ( Nat.cast_nonneg _ ) ) ( hbluedeg i v hv )

/-
Ramsey numbers are symmetric (swap the two colours via complementation).
-/
theorem ramsey_symm {α β : Type*} (J : SimpleGraph α) (L : SimpleGraph β) :
    ramsey J L = ramsey L J := by
  unfold ramsey;
  congr! 3;
  constructor <;> intro h G <;> specialize h Gᶜ <;> aesop

/-
**Finite Ramsey theorem (clique form).**  For all `s t`, there is `N` such
that every finite graph on `≥ N` vertices has a clique of size `s` in `G` or a
clique of size `t` in `Gᶜ`.
-/
set_option maxHeartbeats 1000000 in
theorem exists_ramsey (s t : ℕ) :
    ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V →
      (∃ K : Finset V, G.IsClique ↑K ∧ s ≤ K.card) ∨
        (∃ K : Finset V, Gᶜ.IsClique ↑K ∧ t ≤ K.card) := by
  induction' s with s ih generalizing t;
  · exact ⟨ 0, fun { V } _ _ G _ h => Or.inl ⟨ ∅, by simp +decide ⟩ ⟩;
  · induction' t with t ih';
    · exact ⟨ 0, fun { V } _ _ G _ h => Or.inr ⟨ ∅, by simp +decide ⟩ ⟩;
    · obtain ⟨ N₁, hN₁ ⟩ := ih ( t + 1 ) ; obtain ⟨ N₂, hN₂ ⟩ := ih' ; use N₁ + N₂ + 1 ; intros V _ _ G _ hV ; by_cases h : ∃ v : V, ( Finset.card ( Finset.filter ( fun w => G.Adj v w ) Finset.univ ) ) ≥ N₁ <;> simp_all +decide [  ] ;
      · obtain ⟨ v, hv ⟩ := h; specialize hN₁ ( G.induce { w | G.Adj v w } ) ; simp_all +decide [ Fintype.card_subtype ] ;
        rcases hN₁ with ( ⟨ K, hK₁, hK₂ ⟩ | ⟨ K, hK₁, hK₂ ⟩ );
        · refine Or.inl ⟨ Finset.image ( fun x : { x // G.Adj v x } => x.val ) K ∪ { v }, ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
          intro x hx y hy hxy; obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; specialize hK₁ hu hv; aesop;
        · refine Or.inr ⟨ K.image Subtype.val, ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.IsIndepSet ];
          · exact fun x hx y hy hxy => by obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; exact hK₁ hu hv ( by aesop ) ;
          · rwa [ Finset.card_image_of_injective _ Subtype.coe_injective ];
      · obtain ⟨ v, hv ⟩ : ∃ v : V, ( Finset.card ( Finset.filter ( fun w => w ≠ v ∧ ¬G.Adj v w ) Finset.univ ) ) ≥ N₂ := by
          have h_card : ∀ v : V, (Finset.card (Finset.filter (fun w => w ≠ v ∧ ¬G.Adj v w) Finset.univ)) = (Fintype.card V - 1) - (Finset.card (Finset.filter (fun w => G.Adj v w) Finset.univ)) := by
            intro v; rw [ show ( Finset.univ.filter fun w => w ≠ v ∧ ¬G.Adj v w ) = Finset.univ \ ( { v } ∪ Finset.filter ( fun w => G.Adj v w ) Finset.univ ) by ext w; by_cases hw : w = v <;> aesop ] ; simp +decide [ Finset.card_sdiff, Finset.card_univ ] ;
            rw [ Nat.sub_sub, add_comm ];
          exact ⟨ Classical.choose ( Finset.card_pos.mp ( pos_of_gt hV ) ), by rw [ h_card ] ; exact le_tsub_of_add_le_left <| le_tsub_of_add_le_left <| by linarith [ h ( Classical.choose ( Finset.card_pos.mp ( pos_of_gt hV ) ) ) ] ⟩;
        specialize hN₂ (G.induce {w : V | w ≠ v ∧ ¬G.Adj v w})
          (by simpa only [Fintype.card_subtype, Set.mem_setOf_eq] using hv)
        simp_all +decide [SimpleGraph.IsClique, SimpleGraph.IsIndepSet]
        rcases hN₂ with (⟨K, hK₁, hK₂⟩ | ⟨K, hK₁, hK₂⟩)
        · refine Or.inl ⟨K.image Subtype.val, ?_, ?_⟩ <;>
            simp_all +decide [Finset.card_image_of_injective, Function.Injective]
          exact Set.Pairwise.image hK₁
        · refine Or.inr ⟨Insert.insert v (Finset.image Subtype.val K), ?_, ?_⟩ <;>
            simp_all +decide [Finset.card_image_of_injective, Function.Injective]
          simp_all +decide [Set.Pairwise]
          exact fun a ha₁ ha₂ ha₃ => by rwa [SimpleGraph.adj_comm]

/-
The Ramsey witness set is nonempty: a sufficiently large complete graph,
however 2-coloured, contains a red `J` or a blue `L`.
-/
theorem ramseyGood_nonempty {α β : Type} [Fintype α] [Fintype β]
    (J : SimpleGraph α) (L : SimpleGraph β) [DecidableRel J.Adj] [DecidableRel L.Adj] :
    (RamseyGood J L).Nonempty := by
  -- Obtain `⟨N, HN⟩ := exists_ramsey s t`.
  obtain ⟨N, HN⟩ := exists_ramsey (Fintype.card α) (Fintype.card β);
  refine' ⟨ N, fun G => _ ⟩;
  simp +zetaDelta at *;
  specialize HN G ( by simp );
  rcases HN with ( ⟨ K, hK₁, hK₂ ⟩ | ⟨ K, hK₁, hK₂ ⟩ );
  · -- Since $K$ is a clique in $G$ and $|K| \geq |α|$, there exists an injective function $f : α → K$.
    obtain ⟨f, hf_inj⟩ : ∃ f : α → K, Function.Injective f := by
      have := Fintype.truncEquivFin K;
      obtain ⟨ e ⟩ := Trunc.exists_rep this;
      exact ⟨ fun x => e.symm ( Fin.castLE ( by simpa using! hK₂ ) ( Fintype.equivFin α x ) ), fun x y hxy => by simpa [ Fin.ext_iff ] using! Fintype.equivFin α |>.injective <| Fin.castLE_injective _ <| e.symm.injective hxy ⟩;
    refine' Or.inl ⟨ _, _ ⟩;
    use fun x => f x |>.1;
    exact fun { a b } hab => hK₁ ( f a |>.2 ) ( f b |>.2 ) ( by simpa [ hf_inj.eq_iff ] using! hab.ne );
    exact fun x y hxy => hf_inj <| Subtype.ext hxy;
  · -- Since $K$ is an independent set in $G$, it is a clique in $Gᶜ$.
    have hK_clique : Gᶜ.IsClique ↑K := by
      intro u hu v hv huv; specialize hK₁ hu hv; aesop;
    -- Since $K$ is a clique in $Gᶜ$, we can find an injection $f : β → K$.
    obtain ⟨f, hf⟩ : ∃ f : β → Fin N, Function.Injective f ∧ ∀ i, f i ∈ K := by
      have := Finset.exists_subset_card_eq hK₂;
      obtain ⟨ t, ht₁, ht₂ ⟩ := this;
      have := Finset.equivOfCardEq ( by aesop : Finset.card t = Fintype.card β );
      exact ⟨ fun i => this.symm ⟨ i, Finset.mem_univ i ⟩ |>.1, fun i j hij => by simpa [ Subtype.ext_iff ] using! this.symm.injective ( Subtype.ext hij ), fun i => ht₁ <| this.symm ⟨ i, Finset.mem_univ i ⟩ |>.2 ⟩;
    refine' Or.inr ⟨ _, _ ⟩;
    use f;
    exact fun { a b } hab => hK_clique ( hf.2 a ) ( hf.2 b ) ( hf.1.ne hab.ne );
    exact hf.1

/-
**Ramsey witness on an induced set.**  If `R(J,L)` exists (its witness set is
nonempty) then any vertex subset `S` with `|S| ≥ R(J,L)` induces, in the
red/blue colouring `Gr`, a red `J` or a blue `L`.
-/
theorem ramsey_induce_witness {α β : Type} [Fintype α] [Fintype β]
    (J : SimpleGraph α) (L : SimpleGraph β) [DecidableRel J.Adj] [DecidableRel L.Adj]
    (hne : (RamseyGood J L).Nonempty) {V : Type} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (S : Finset V)
    (hS : ramsey J L ≤ S.card) :
    J ⊑ Gr.induce (↑S) ∨ L ⊑ (Gr.induce (↑S))ᶜ := by
  convert! ramsey_mem J L hne using 1;
  obtain ⟨ S', hS', hS'' ⟩ := Finset.exists_subset_card_eq hS;
  have h_equiv : Nonempty (Fin (ramsey J L) ≃ {x // x ∈ S'}) := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ hS'' ] ⟩;
  obtain ⟨ e ⟩ := h_equiv;
  constructor <;> intro h;
  · exact ramsey_mem J L hne;
  · obtain ⟨ f, hf ⟩ := h ( SimpleGraph.comap ( fun x : Fin ( ramsey J L ) => ( e x : V ) ) Gr );
    · refine' Or.inl ⟨ _, _ ⟩;
      use fun x => ⟨ e ( f x ), hS' ( e ( f x ) |>.2 ) ⟩;
      all_goals simp_all +decide [ Function.Injective ];
      · intro a b hab; have := f.map_rel' hab; aesop;
      · exact hf;
    · right;
      refine' ‹L ⊑ ( SimpleGraph.comap ( fun x => ( e x : V ) ) Gr ) ᶜ›.trans _;
      refine' ⟨ _, _ ⟩;
      use fun x => ⟨ e x, hS' ( e x |>.2 ) ⟩;
      all_goals simp +decide [ Function.Injective ];
      exact fun { a b } hab h => ⟨ hab, h ⟩

/-- Partition bound: every reservoir vertex is `v` itself, a red neighbour of `v`,
or a blue neighbour of `v`, so `|W i| ≤ 1 + (red deg in W i) + (blue deg in W i)`. -/
theorem blue_inter_lower {V : Type} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (Wi : Finset V) (v : V) :
    ((Wi.card : ℝ)) ≤ 1 + ((Wi.filter (fun u => Gr.Adj v u)).card : ℝ)
      + ((Grᶜ.neighborFinset v ∩ Wi).card : ℝ) := by
  have hsub : Wi ⊆ insert v ((Wi.filter (fun u => Gr.Adj v u)) ∪ (Grᶜ.neighborFinset v ∩ Wi)) := by
    intro u hu
    by_cases huv : u = v
    · subst huv; exact Finset.mem_insert_self _ _
    · rcases em (Gr.Adj v u) with h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, h⟩))
      · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨?_, hu⟩))
        rw [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj]
        exact ⟨fun e => huv e.symm, h⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le v ((Wi.filter (fun u => Gr.Adj v u)) ∪ (Grᶜ.neighborFinset v ∩ Wi))
  have h3 := Finset.card_union_le (Wi.filter (fun u => Gr.Adj v u)) (Grᶜ.neighborFinset v ∩ Wi)
  have hnat : Wi.card ≤ 1 + (Wi.filter (fun u => Gr.Adj v u)).card + (Grᶜ.neighborFinset v ∩ Wi).card := by
    omega
  exact_mod_cast hnat

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- **Clean core of Erdős 550** (over `Kbip`).  Fix `q ≥ 2` and class sizes
`m' : Fin (q+1) → ℕ` (monotone, positive).  For all sufficiently large `n` and
every `n`-vertex tree `T`,
`R(T, K_{m'0,…,m'q}) ≤ q·(R(T, K_{m'0,m'1}) − 1) + m'0`. -/
theorem erdos_550_large_core (q : ℕ) (hq : 2 ≤ q) (m' : Fin (q + 1) → ℕ)
    (hmono : Monotone m') (hpos : 1 ≤ m' 0) :
    ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → Fintype.card V = n →
      ramsey T (Kmult (q + 1) m') ≤
        q * (ramsey T (Kbip (m' 0) (m' 1)) - 1) + m' 0 := by
  classical
  set a := m' 0 with ha
  have hpos' : ∀ i, 1 ≤ m' i := fun i => le_trans hpos (hmono (Fin.zero_le i))
  obtain ⟨ε, sThr, ζThr, hε, hζThr, Hac⟩ := assembly_core q a hq m' hmono hpos rfl
  obtain ⟨κ', hκ'pos, Hprof⟩ := profile_to_A1 q hq ε hε
  set η := min (min (ζThr/2) (κ'/8)) (1/4) with hη_def
  have hη : 0 < η := by rw [hη_def]; positivity
  obtain ⟨δ, hδ, N₀crd, Hcrd⟩ := clean_reservoir_decomposition q hq m' hmono hpos η hη
  set θ := min (κ'/8) (1/4) with hθ_def
  have hθ : 0 < θ := by rw [hθ_def]; positivity
  obtain ⟨n_efrs, Hefrs⟩ := efrs_bipartite (m' 0) (m' 1) hpos (hpos' 1) θ hθ
  obtain ⟨n_nt, Hnt⟩ :=
    near_turan_red_density_direct q hq m' hmono hpos δ hδ
  refine ⟨max (max n_efrs n_nt) (max (2*(sThr+2)) (max (2*(N₀crd+q+2)) (⌈200*((a:ℝ)+1)/κ'⌉₊ + 200))), ?_⟩
  intro n hn V _ T hT hcard
  set r := ramsey T (Kbip (m' 0) (m' 1)) with hr
  apply ramsey_le_of_mem T (Kmult (q+1) m')
  rw [RamseyGood]
  intro G
  by_contra hcon
  have hT_G : ¬ (T ⊑ G) := fun h => hcon (Or.inl h)
  have hF : ¬ (Kmult (q+1) m' ⊑ Gᶜ) := fun h => hcon (Or.inr h)
  have hθ4 : θ ≤ 1/4 := by rw [hθ_def]; exact min_le_right _ _
  have hθκ : θ ≤ κ'/8 := by rw [hθ_def]; exact min_le_left _ _
  have hθ0 : 0 ≤ θ := hθ.le
  have hη4 : η ≤ 1/4 := by rw [hη_def]; exact min_le_right _ _
  have hηκ : η ≤ κ'/8 := by rw [hη_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hηζ : η ≤ ζThr/2 := by rw [hη_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hη0 : 0 ≤ η := hη.le
  have hqR : (0:ℝ) < (q:ℝ) := by positivity
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.one_le_of_lt hq
  have hnA : max n_efrs n_nt ≤ n := le_trans (le_max_left _ _) hn
  have hn_efrs : n_efrs ≤ n := le_trans (le_max_left _ _) hnA
  have hn_nt : n_nt ≤ n := le_trans (le_max_right _ _) hnA
  have hnBCD : max (2*(sThr+2)) (max (2*(N₀crd+q+2)) (⌈200*((a:ℝ)+1)/κ'⌉₊ + 200)) ≤ n :=
    le_trans (le_max_right _ _) hn
  have hnB : 2*(sThr+2) ≤ n := le_trans (le_max_left _ _) hnBCD
  have hnCD : max (2*(N₀crd+q+2)) (⌈200*((a:ℝ)+1)/κ'⌉₊+200) ≤ n := le_trans (le_max_right _ _) hnBCD
  have hnC : 2*(N₀crd+q+2) ≤ n := le_trans (le_max_left _ _) hnCD
  have hnD : ⌈200*((a:ℝ)+1)/κ'⌉₊+200 ≤ n := le_trans (le_max_right _ _) hnCD
  have hn2R : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
  have hnBR : (2*(sThr+2):ℝ) ≤ (n:ℝ) := by exact_mod_cast hnB
  have hnCR : (2*(N₀crd+q+2):ℝ) ≤ (n:ℝ) := by exact_mod_cast hnC
  have hnκ : 200*((a:ℝ)+1) ≤ (n:ℝ)*κ' := by
    have hceil : 200*((a:ℝ)+1)/κ' ≤ (⌈200*((a:ℝ)+1)/κ'⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈200*((a:ℝ)+1)/κ'⌉₊ : ℝ) ≤ (n:ℝ) := by
      have : ⌈200*((a:ℝ)+1)/κ'⌉₊ ≤ n := le_trans (Nat.le_add_right _ 200) hnD
      exact_mod_cast this
    rw [div_le_iff₀ hκ'pos] at hceil; nlinarith [hceil, h2, hκ'pos]
  have hcardVR : (Fintype.card V : ℝ) = (n:ℝ) := by exact_mod_cast hcard
  have hefrs := Hefrs n hn_efrs T hT hcard
  rw [abs_le] at hefrs
  have hrlo : (1-θ)*(n:ℝ) ≤ (r:ℝ) := by nlinarith [hefrs.1]
  have hrhi : (r:ℝ) ≤ (1+θ)*(n:ℝ) := by nlinarith [hefrs.2]
  have hr1R : (1:ℝ) ≤ (r:ℝ) := by nlinarith [hrlo, hθ4, hn2R]
  have hr1 : 1 ≤ r := by exact_mod_cast hr1R
  have hcardfin : Fintype.card (Fin (q*(r-1)+a)) = q*(r-1)+a := Fintype.card_fin _
  have hNcast : ((q*(r-1)+a : ℕ):ℝ) = (q:ℝ)*((r:ℝ)-1)+(a:ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr1]; push_cast; ring
  have haR : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg _
  have hN0 : N₀crd ≤ Fintype.card (Fin (q*(r-1)+a)) := by
    rw [hcardfin]
    have hreal : (N₀crd:ℝ) ≤ ((q*(r-1)+a:ℕ):ℝ) := by
      rw [hNcast]; nlinarith [hrlo, hθ4, hn2R, hqR1, haR, hnCR]
    exact_mod_cast hreal
  have hcardV2 : 2 ≤ Fintype.card V := by rw [hcard]; omega
  have hdens := Hnt T hT (by rw [hcard]; exact hn_nt) (W := Fin (q*(r-1)+a)) G
    (by rw [hcardfin, ha]) hT_G hF
  obtain ⟨W, hWdisj, hsize, hred, hcross, hHfree, hleftover⟩ := Hcrd (Gᶜ) hN0 hF hdens
  set Xset := Finset.univ \ (Finset.univ.biUnion W) with hXdef
  have hdisjXW : ∀ i, Disjoint Xset (W i) := by
    intro i; rw [hXdef, Finset.disjoint_left]
    intro x hx hxw; rw [Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxw⟩)
  have hcover : (Finset.univ.biUnion W) ∪ Xset = Finset.univ := by
    rw [hXdef, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  set nqv := (Fintype.card (Fin (q*(r-1)+a)):ℝ)/q with hnqv_def
  have hnqv_eq : nqv = ((r:ℝ)-1)+(a:ℝ)/q := by
    rw [hnqv_def, hcardfin, hNcast]; field_simp
  have hnqv_lo : (1-θ)*(n:ℝ) - 1 ≤ nqv := by
    rw [hnqv_eq]; have hge : (0:ℝ) ≤ (a:ℝ)/q := by positivity
    nlinarith [hrlo, hge]
  have hnqv_hi : nqv ≤ (1+θ)*(n:ℝ) + a := by
    rw [hnqv_eq]; have haq : (a:ℝ)/q ≤ a := by rw [div_le_iff₀ hqR]; nlinarith [haR, hqR1]
    nlinarith [hrhi, haq]
  have hnqv_pos : 0 ≤ nqv := by rw [hnqv_def]; positivity
  have hnR0 : (0:ℝ) ≤ (n:ℝ) := by linarith
  have hsThr : ∀ i, sThr ≤ (W i).card := by
    intro i
    have hge : (1-η)*((1-θ)*(n:ℝ) - 1) ≤ ((W i).card:ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hnqv_lo (by linarith)) (hsize i).1
    have hprod : (1/2:ℝ) ≤ (1-η)*(1-θ) := by nlinarith [mul_nonneg hη0 hθ0, hη4, hθ4]
    have hp : (1/2)*(n:ℝ) ≤ (1-η)*(1-θ)*(n:ℝ) := mul_le_mul_of_nonneg_right hprod hnR0
    have hreal : (sThr:ℝ) ≤ ((W i).card:ℝ) := by nlinarith [hge, hp, hnBR, hη0]
    exact_mod_cast hreal
  have hslack : ∀ i j, i ≠ j → ∀ w ∈ W i,
      (((W j).filter (fun v => ¬ (Gᶜ).Adj w v)).card : ℝ) ≤ ζThr * (W j).card := by
    intro i j hij w hw
    nlinarith [hcross i j hij w hw, (hsize j).1, hηζ, hη4, hnqv_pos, hζThr.le, hη0,
      mul_le_mul_of_nonneg_left (hsize j).1 hζThr.le, mul_nonneg hζThr.le hnqv_pos]
  have hsand : ∀ i, (1 - κ') * (Fintype.card V : ℝ) ≤ (W i).card ∧
      ((W i).card : ℝ) ≤ (1 + κ') * Fintype.card V := by
    intro i
    rw [hcardVR]
    refine ⟨?_, ?_⟩
    · nlinarith [(hsize i).1, hnqv_lo, hηκ, hθκ, hη4, hθ4, hη0, hθ0, hnκ, hκ'pos, hn2R,
        mul_le_mul_of_nonneg_left hnqv_lo (by linarith : (0:ℝ) ≤ 1-η)]
    · have hprod : (1+η)*(1+θ) ≤ 1 + κ'/2 := by
        nlinarith [mul_nonneg hη0 hθ0, hηκ, hθκ, hη4, hθ0, hκ'pos]
      have hstep1 : ((W i).card:ℝ) ≤ (1+η)*((1+θ)*(n:ℝ) + a) :=
        le_trans (hsize i).2 (mul_le_mul_of_nonneg_left hnqv_hi (by linarith))
      have hp2 : (1+η)*(1+θ)*(n:ℝ) ≤ (1+κ'/2)*(n:ℝ) := mul_le_mul_of_nonneg_right hprod hnR0
      have ha2 : (1+η)*(a:ℝ) ≤ (5/4)*(a:ℝ) := mul_le_mul_of_nonneg_right (by linarith) haR
      nlinarith [hstep1, hp2, ha2, hnκ]
  have hmindeg : ∀ i, ∀ v ∈ W i,
      (1 - κ') * (Fintype.card V : ℝ) ≤ (((Gᶜ)ᶜ.neighborFinset v ∩ W i).card : ℝ) := by
    intro i v hv
    rw [hcardVR]
    nlinarith [blue_inter_lower (Gᶜ) (W i) v, hred i v hv, (hsize i).1, hnqv_lo, hηκ, hθκ,
      hη4, hθ4, hη0, hθ0, hnκ, hκ'pos, hn2R,
      mul_le_mul_of_nonneg_left hnqv_lo (by linarith : (0:ℝ) ≤ 1-η), mul_nonneg hη0 hθ0,
      mul_nonneg hη0 hnR0]
  have hA1 := Hprof T (Gᶜ) W Xset hT hcardV2 hdisjXW hWdisj
    (by rw [compl_compl]; exact hT_G) hsand hmindeg
  have hRamsey : ∀ S : Finset (Fin (q*(r-1)+a)), r ≤ S.card →
      Kbip (m' 0) (m' 1) ⊑ (Gᶜ).induce ↑S ∨ T ⊑ ((Gᶜ).induce ↑S)ᶜ := by
    intro S hS
    have hS' : ramsey (Kbip (m' 0) (m' 1)) T ≤ S.card := by rw [ramsey_symm]; exact hS
    exact ramsey_induce_witness (Kbip (m' 0) (m' 1)) T (ramseyGood_nonempty _ _) (Gᶜ) S hS'
  exact Hac (Gᶜ) T W Xset r hWdisj hdisjXW hcover hsThr hslack hHfree hF
    (by rw [compl_compl]; exact hT_G) hA1 hRamsey (by rw [hcardfin, ha])

end Erdos550
