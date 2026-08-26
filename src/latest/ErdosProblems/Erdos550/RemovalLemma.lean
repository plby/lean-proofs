import Mathlib
import ErdosProblems.Erdos550.Basic
import ErdosProblems.Erdos550.GreedyEmbedding
import ErdosProblems.Erdos550.RegularitySlicing

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The `K_{q+1}` graph removal lemma (regularity based)

This file builds the ingredients needed to discharge `removal_to_clique`:
the graph removal lemma specialised to the clique `K_{q+1}`.  Mathlib only has
the triangle case; here we develop the general clique case from Szemerédi's
regularity lemma (`SimpleGraph.szemeredi_regularity`) plus a counting/embedding
lemma for `K_{q+1}(t)` in a system of pairwise `ε`-regular dense pairs.
-/

open SimpleGraph Finset

namespace Erdos550

/-
**Blow-up embedding.**  A `(q+1)`-colourable graph on `≤ t` vertices embeds
into the `t`-fold blow-up of `K_{q+1}` (the complete `(q+1)`-partite graph with
all parts of size `t`).
-/
lemma colorable_embeds_Kmult {W : Type} [Fintype W] (F : SimpleGraph W)
    (q t : ℕ) (hcol : F.Colorable (q + 1)) (ht : Fintype.card W ≤ t) :
    F ⊑ Kmult (q + 1) (fun _ => t) := by
  obtain ⟨f, hf⟩ : ∃ f : W ↪ Fin t, True := by
    obtain ⟨f, hf⟩ : ∃ f : W ↪ Fin (Fintype.card W), True := by
      exact ⟨ Fintype.equivFin W |> Equiv.toEmbedding, trivial ⟩;
    exact ⟨ f.trans ( Fin.castLEEmb ht ), trivial ⟩;
  refine' ⟨ _, _ ⟩;
  refine' ⟨ fun w => ⟨ hcol.some w, f w ⟩, _ ⟩;
  all_goals simp +decide [ Function.Injective, Kmult ];
  exact fun { a b } hab => hcol.some.valid hab

/-
**Common-neighbourhood selection (inner induction on `t`).**  Choose `t`
vertices `S` in a pool `L` that is `ε`-uniform and of density `≥ d` to every pool
`A i`, keeping in each `A i` a subset `A' i` of at least a `(d/2)^t`-fraction all
of whose vertices are adjacent to every chosen vertex.
-/
set_option maxHeartbeats 1000000 in
lemma exists_common_nbhd {V : Type} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    [DecidableRel Gr.Adj] (k t : ℕ) {ε d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hε : 0 < ε)
    (hεs : ε ≤ (d / 2) ^ (t + 1) / (4 * (k + 1)))
    (L : Finset V) (A : Fin k → Finset V)
    (hL : 2 * t + 1 ≤ L.card)
    (_hA : ∀ i, (2 * t + 1 : ℝ) ≤ (d / 2) ^ t * (A i).card)
    (hunif : ∀ i, Gr.IsUniform ε L (A i))
    (hdens : ∀ i, (d : ℝ) ≤ (Gr.edgeDensity L (A i) : ℝ)) :
    ∃ S : Finset V, S ⊆ L ∧ S.card = t ∧ ∃ A' : Fin k → Finset V,
      (∀ i, A' i ⊆ A i) ∧ (∀ i, (d / 2) ^ t * (A i).card ≤ (A' i).card) ∧
      (∀ i, ∀ w ∈ A' i, ∀ v ∈ S, Gr.Adj v w) := by
  have h_ind : ∀ t' ≤ t, ∃ S' ⊆ L, S'.card = t' ∧ ∃ A' : Fin k → Finset V, (∀ i, A' i ⊆ A i) ∧ (∀ i, (d / 2) ^ t' * (A i).card ≤ (A' i).card) ∧ (∀ i, ∀ w ∈ A' i, ∀ v ∈ S', Gr.Adj v w) := by
    intro t' ht';
    induction' t' with t' ih;
    · exact ⟨ ∅, Finset.empty_subset _, rfl, fun i => A i, fun i => Finset.Subset.refl _, fun i => by norm_num, by norm_num ⟩;
    · obtain ⟨S', hS'⟩ := ih (Nat.le_of_succ_le ht');
      obtain ⟨A', hA'⟩ := hS'.right.right
      have hA'_card : ∀ i, (d / 2) ^ t' * (A i).card ≤ (A' i).card := by
        exact hA'.2.1
      have hA'_adj : ∀ i, ∀ w ∈ A' i, ∀ v ∈ S', Gr.Adj v w := by
        exact hA'.2.2
      have hA'_uniform : ∀ i, Gr.IsUniform (2 * ε / (d / 2) ^ t') L (A' i) := by
        intro i
        have hA'_uniform_i : Gr.IsUniform ε L (A i) := hunif i
        have hA'_uniform_i' : Gr.IsUniform (2 * ε / (d / 2) ^ t') L (A' i) := by
          have := isUniform_slice Gr ( show 0 < ( d / 2 ) ^ t' by positivity ) ( show ε ≤ ( d / 2 ) ^ t' by
                                                                                  refine le_trans hεs ?_;
                                                                                  exact le_trans ( div_le_self ( by positivity ) ( by linarith ) ) ( pow_le_pow_of_le_one ( by positivity ) ( by linarith ) ( by linarith ) ) ) hA'_uniform_i ( Finset.Subset.refl L ) ( hA'.1 i ) ( by
                                                                                  exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( pow_le_one₀ ( by positivity ) ( by linarith ) ) ) ( by
                                                                                  exact hA'_card i ) ; aesop;
        exact hA'_uniform_i'
      have hA'_density : ∀ i, (d - ε) ≤ (Gr.edgeDensity L (A' i) : ℝ) := by
        intro i
        have hA'_density_i : |(Gr.edgeDensity L (A' i) : ℝ) - (Gr.edgeDensity L (A i) : ℝ)| ≤ ε := by
          have := isUniform_slice Gr ( show 0 < ( d / 2 ) ^ t' by positivity ) ( show ε ≤ ( d / 2 ) ^ t' by
                                                                                  refine le_trans hεs ?_;
                                                                                  exact le_trans ( div_le_self ( by positivity ) ( by linarith ) ) ( pow_le_pow_of_le_one ( by positivity ) ( by linarith ) ( by linarith ) ) ) ( hunif i ) ( Finset.Subset.refl _ ) ( hA'.1 i ) ( by
                                                                                  exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( pow_le_one₀ ( by positivity ) ( by linarith ) ) ) ( by
                                                                                  exact hA'_card i ) ; aesop;
        linarith [ abs_le.mp hA'_density_i, hdens i ]
      have hA'_good : ∃ v ∈ L \ S', ∀ i, ((A' i).filter (fun w => Gr.Adj v w)).card ≥ (d / 2) * (A' i).card := by
        have hA'_good : ∀ i, ((L.filter (fun v => ((A' i).filter (fun w => Gr.Adj v w)).card < (d / 2) * (A' i).card)).card : ℝ) ≤ (2 * ε / (d / 2) ^ t') * L.card := by
          intro i
          have hA'_good_i : ((L.filter (fun v => ((A' i).filter (fun w => Gr.Adj v w)).card < (d / 2) * (A' i).card)).card : ℝ) ≤ (2 * ε / (d / 2) ^ t') * L.card := by
            have hA'_density_i : (d - ε) ≤ (Gr.edgeDensity L (A' i) : ℝ) := hA'_density i
            have := @regular_defect V _ _ Gr _ ( 2 * ε / ( d / 2 ) ^ t' ) ( d - ε ) ?_ L ( A' i ) ?_ ?_ <;> norm_num at *;
            · refine le_trans ?_ this;
              refine' Nat.cast_le.mpr ( Finset.card_mono _ );
              intro v hv; simp_all +decide [ Finset.subset_iff ] ;
              refine lt_of_lt_of_le hv.2 ?_;
              refine' mul_le_mul_of_nonneg_right _ ( Nat.cast_nonneg _ );
              rw [ le_sub_iff_add_le, le_sub_iff_add_le ];
              rw [ add_div', div_add', div_le_iff₀ ] <;> try positivity;
              rw [ le_div_iff₀ ( by positivity ) ] at hεs;
              rw [ pow_succ' ] at hεs;
              nlinarith [ show ( d / 2 ) ^ t' ≥ ( d / 2 ) ^ t by exact pow_le_pow_of_le_one ( by positivity ) ( by linarith ) ( by linarith ), show ( d / 2 ) ^ t' ≤ 1 by exact pow_le_one₀ ( by positivity ) ( by linarith ), show ( k : ℝ ) ≥ 1 by norm_cast; exact Fin.pos i ];
            · rw [ div_le_iff₀ ( by positivity ) ];
              rw [ le_div_iff₀ ] at hεs <;> try positivity;
              rw [ pow_succ' ] at hεs;
              nlinarith [ pow_pos ( by positivity : 0 < d / 2 ) t', pow_le_pow_of_le_one ( by positivity : 0 ≤ d / 2 ) ( by linarith : d / 2 ≤ 1 ) ( by linarith : t' ≤ t ) ];
            · exact hA'_uniform i;
            · exact hA'_density_i
          exact hA'_good_i;
        have hA'_good : ((L \ S').filter (fun v => ∃ i, ((A' i).filter (fun w => Gr.Adj v w)).card < (d / 2) * (A' i).card)).card < L.card - S'.card := by
          have hA'_good : ((L \ S').filter (fun v => ∃ i, ((A' i).filter (fun w => Gr.Adj v w)).card < (d / 2) * (A' i).card)).card ≤ k * (2 * ε / (d / 2) ^ t') * L.card := by
            have hA'_good : ((L \ S').filter (fun v => ∃ i, ((A' i).filter (fun w => Gr.Adj v w)).card < (d / 2) * (A' i).card)).card ≤ ∑ i, ((L.filter (fun v => ((A' i).filter (fun w => Gr.Adj v w)).card < (d / 2) * (A' i).card)).card : ℝ) := by
              norm_cast;
              refine' le_trans _ ( Finset.card_biUnion_le );
              exact Finset.card_le_card fun x hx => by aesop;
            exact hA'_good.trans ( le_trans ( Finset.sum_le_sum fun _ _ => by solve_by_elim ) ( by norm_num; linarith ) );
          have hA'_good : k * (2 * ε / (d / 2) ^ t') * L.card < L.card - S'.card := by
            have hA'_good : k * (2 * ε / (d / 2) ^ t') < 1 / 2 := by
              rw [ mul_div, div_lt_iff₀ ] <;> try positivity;
              rw [ le_div_iff₀ ] at hεs <;> try positivity;
              rw [ pow_succ' ] at hεs ; nlinarith [ pow_pos ( by positivity : 0 < d / 2 ) t', pow_le_pow_of_le_one ( by positivity : 0 ≤ d / 2 ) ( by linarith : d / 2 ≤ 1 ) ( by linarith : t' ≤ t ) ];
            nlinarith [ show ( L.card : ℝ ) ≥ 2 * t + 1 by exact_mod_cast hL, show ( S'.card : ℝ ) = t' by exact_mod_cast hS'.2.1, show ( t' : ℝ ) + 1 ≤ t by exact_mod_cast ht' ];
          rw [ lt_tsub_iff_left ] at * ; norm_cast at *;
          exact_mod_cast ( by linarith : ( #S' : ℝ ) + # ( Finset.filter ( fun v => ∃ i, ( # ( Finset.filter ( fun w => Gr.Adj v w ) ( A' i ) ) : ℝ ) < d / 2 * # ( A' i ) ) ( L \ S' ) ) < #L );
        contrapose! hA'_good;
        rw [ Finset.filter_true_of_mem hA'_good ] ; simp +decide [ Finset.card_sdiff, * ];
        rw [ Finset.inter_eq_left.mpr hS'.1, hS'.2.1, Nat.sub_add_cancel ( by linarith ) ]
      obtain ⟨v, hvL, hvA'⟩ := hA'_good
      use insert v S';
      refine' ⟨ _, _, _ ⟩;
      · exact Finset.insert_subset_iff.mpr ⟨ Finset.mem_sdiff.mp hvL |>.1, hS'.1 ⟩;
      · grind;
      · use fun i => Finset.filter (fun w => Gr.Adj v w) (A' i);
        simp_all +decide [ Finset.subset_iff ];
        exact ⟨ fun i => by rw [ pow_succ' ] ; nlinarith [ hA'_card i, hvA' i ], fun i w hw hw' a ha => hA'_adj i w hw a ha ⟩;
  exact h_ind t le_rfl

/-
**Inductive cross-complete embedding.**  For `k` pairwise-disjoint,
pairwise-`ε`-uniform pools of density `≥ d` and size `≥ M`, one finds a
cross-complete family of `t`-subsets (a copy of `K_k(t)`), for suitably small
`ε` and large `M`.
-/
set_option maxHeartbeats 1000000 in
lemma embed_cross_complete (k t : ℕ) (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ M : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (A : Fin k → Finset V),
      (∀ i, M ≤ (A i).card) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      (∀ i j, i ≠ j → Gr.IsUniform ε (A i) (A j)) →
      (∀ i j, i ≠ j → (d : ℝ) ≤ (Gr.edgeDensity (A i) (A j) : ℝ)) →
      ∃ S : Fin k → Finset V, (∀ i, (S i).card = t) ∧ (∀ i, S i ⊆ A i) ∧
        (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ CrossComplete Gr S := by
  induction' k with k ih generalizing d;
  · exact ⟨ 1, by norm_num, by norm_num, 0, by simp +decide [ CrossComplete ] ⟩;
  · obtain ⟨εₖ, hεₖ, hεₖ1, Mₖ, hMₖ⟩ := ih (d / 2) (by positivity) (by linarith);
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε ≤ 1 ∧ ε ≤ d / 2 ∧ 2 * ε / (d / 2) ^ t ≤ εₖ ∧ ε ≤ (d / 2) ^ (t + 1) / (4 * (k + 1)) := by
      refine' ⟨ Min.min ( Min.min ( d / 2 ) ( εₖ * ( d / 2 ) ^ t / 2 ) ) ( ( d / 2 ) ^ ( t + 1 ) / ( 4 * ( k + 1 ) ) ), _, _, _, _, _ ⟩ <;> norm_num [ hd, hd1, hεₖ, hεₖ1 ];
      · positivity;
      · exact Or.inl <| Or.inl <| by linarith;
      · rw [ div_le_iff₀ ( by positivity ) ];
        exact le_trans ( mul_le_mul_of_nonneg_left ( min_le_left _ _ ) zero_le_two ) ( by linarith [ min_le_right ( d / 2 ) ( εₖ * ( d / 2 ) ^ t / 2 ) ] );
    obtain ⟨C, hC⟩ : ∃ C : ℕ, 1 ≤ (d / 2) ^ t * C := by
      exact ⟨ ⌈ ( d / 2 ) ⁻¹ ^ t⌉₊, by nlinarith [ Nat.le_ceil ( ( d / 2 ) ⁻¹ ^ t ), show 0 < ( d / 2 ) ^ t by positivity, show ( d / 2 ) ^ t * ( d / 2 ) ⁻¹ ^ t = 1 by rw [ ← mul_pow, mul_inv_cancel₀ ( by positivity ), one_pow ] ] ⟩;
    refine' ⟨ ε, hε_pos, hε.1, ( Mₖ + 2 * t + 1 ) * C + 2 * t + 1, _ ⟩;
    intro V _ _ Gr _ A hA hdisj hunif hdens
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset V, S₀ ⊆ A (Fin.last k) ∧ S₀.card = t ∧ ∃ A' : Fin k → Finset V, (∀ i, A' i ⊆ A (Fin.castSucc i)) ∧ (∀ i, (d / 2) ^ t * (A (Fin.castSucc i)).card ≤ (A' i).card) ∧ (∀ i, ∀ w ∈ A' i, ∀ v ∈ S₀, Gr.Adj v w) := by
      apply exists_common_nbhd Gr k t hd hd1 hε_pos hε.2.2.2 (A (Fin.last k)) (fun i => A (Fin.castSucc i)) (by
      grind +qlia) (by
      intro i
      have h_card : (A (Fin.castSucc i)).card ≥ (Mₖ + 2 * t + 1) * C + 2 * t + 1 := by
        exact hA _;
      nlinarith [ show ( # ( A ( Fin.castSucc i ) ) : ℝ ) ≥ ( Mₖ + 2 * t + 1 ) * C + 2 * t + 1 by exact_mod_cast h_card ]) (by
      exact fun i => hunif _ _ ( ne_of_gt ( Fin.castSucc_lt_last i ) )) (by
      exact fun i => hdens _ _ ( ne_of_gt ( Fin.castSucc_lt_last i ) ));
    obtain ⟨A', hA'⟩ := hS₀.right.right;
    obtain ⟨S', hS'⟩ := hMₖ Gr A' (by
    intro i
    have h_card : (d / 2) ^ t * (A (Fin.castSucc i)).card ≤ (A' i).card := by
      exact hA'.2.1 i;
    have h_card : (d / 2) ^ t * ((Mₖ + 2 * t + 1) * C + 2 * t + 1) ≤ (A' i).card := by
      exact le_trans ( mul_le_mul_of_nonneg_left ( mod_cast hA _ ) ( by positivity ) ) h_card;
    exact_mod_cast ( by nlinarith [ show ( 0 : ℝ ) ≤ ( d / 2 ) ^ t * ( 2 * t + 1 ) by positivity ] : ( Mₖ : ℝ ) ≤ # ( A' i ) )) (by
    exact fun i j hij => Disjoint.mono ( hA'.1 i ) ( hA'.1 j ) ( hdisj _ _ <| by simpa [ Fin.ext_iff ] using! hij )) (by
    intros i j hij;
    have := isUniform_slice Gr ( show 0 < ( d / 2 ) ^ t by positivity ) ( show ε ≤ ( d / 2 ) ^ t by
                                                                            exact le_trans hε.2.2.2 ( div_le_self ( by positivity ) ( by linarith ) |> le_trans <| pow_le_pow_of_le_one ( by positivity ) ( by linarith ) <| by linarith ) ) ( hunif ( Fin.castSucc i ) ( Fin.castSucc j ) ( by simpa [ Fin.ext_iff ] using! hij ) ) ( hA'.1 i ) ( hA'.1 j ) ( by
                                                                            exact hA'.2.1 i ) ( by
                                                                            exact hA'.2.1 j );
    exact this.2.mono ( by linarith )) (by
    intros i j hij;
    have := isUniform_slice Gr ( show 0 < ( d / 2 ) ^ t by positivity ) ( show ε ≤ ( d / 2 ) ^ t by
                                                                            exact le_trans hε.2.2.2 ( div_le_self ( by positivity ) ( by linarith ) |> le_trans <| pow_le_pow_of_le_one ( by positivity ) ( by linarith ) <| by linarith ) ) ( hunif ( Fin.castSucc i ) ( Fin.castSucc j ) ( by simpa [ Fin.ext_iff ] using! hij ) ) ( hA'.1 i ) ( hA'.1 j ) ( by
                                                                            exact hA'.2.1 i ) ( by
                                                                            exact hA'.2.1 j );
    linarith [ abs_le.mp this.1, hdens ( Fin.castSucc i ) ( Fin.castSucc j ) ( by simpa [ Fin.ext_iff ] using! hij ) ]);
    refine' ⟨ Fin.snoc S' S₀, _, _, _, _ ⟩;
    · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
    · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
      exact fun i => Finset.Subset.trans ( hS'.2.1 i ) ( hA'.1 i );
    · intro i j hij;
      by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp +decide [ Fin.snoc, hi, hj ] at hij ⊢;
      · exact hS'.2.2.1 _ _ ( by simpa [ Fin.ext_iff ] using! hij );
      · refine' Finset.disjoint_left.mpr _;
        intro v hv hv';
        exact Finset.disjoint_left.mp ( hdisj ( Fin.castSucc ( i.castLT hi ) ) ( Fin.last k ) ( ne_of_lt ( Fin.castSucc_lt_last _ ) ) ) ( hA'.1 _ ( hS'.2.1 _ hv ) ) ( hS₀.1 hv' );
      · refine' Finset.disjoint_left.mpr _;
        intro v hv₁ hv₂;
        exact Finset.disjoint_left.mp ( hdisj _ _ <| ne_of_gt <| Fin.castSucc_lt_last _ ) ( hS₀.1 hv₁ ) ( hA'.1 _ <| hS'.2.1 _ hv₂ );
      · grind +splitImp;
    · intro i j hij x hx y hy;
      by_cases hi : i.val < k <;> by_cases hj : j.val < k <;> simp +decide [ Fin.snoc, * ] at hx hy ⊢;
      · exact hS'.2.2.2 _ _ ( by simpa [ Fin.ext_iff ] using! hij ) _ hx _ hy;
      · exact hA'.2.2 _ _ ( hS'.2.1 _ hx ) _ hy |> fun h => h.symm;
      · exact hA'.2.2 _ _ ( hS'.2.1 _ hy ) _ hx |> fun h => by simpa [ SimpleGraph.adj_comm ] using! h;
      · grind

/-- **Counting / embedding lemma for `K_{q+1}(t)`.**  For fixed `q`, `t` and a
density `d > 0`, there is a uniformity threshold `ε₀ > 0` and a size threshold
`m₀` so that whenever `P 0, …, P q` are pairwise-disjoint vertex sets, each of
size `≥ m₀`, pairwise `ε₀`-uniform and of pairwise edge density `≥ d`, then the
graph contains a copy of the `t`-fold blow-up of `K_{q+1}`. -/
lemma exists_blowup_of_regular (q t : ℕ) (d : ℝ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (P : Fin (q + 1) → Finset V),
      (∀ i, m₀ ≤ (P i).card) →
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      (∀ i j, i ≠ j → Gr.IsUniform ε₀ (P i) (P j)) →
      (∀ i j, i ≠ j → (d : ℝ) ≤ (Gr.edgeDensity (P i) (P j) : ℝ)) →
      Kmult (q + 1) (fun _ => t) ⊑ Gr := by
  obtain ⟨ε, hε, hε1, M, hM⟩ :=
    embed_cross_complete (q + 1) t (min d 1) (lt_min hd (by norm_num)) (min_le_right _ _)
  refine ⟨ε, hε, M, ?_⟩
  intro V _ _ Gr _ P hcard hdisj hunif hdens
  obtain ⟨S, hScard, _, hSdisj, hScross⟩ :=
    hM Gr P hcard hdisj hunif
      (fun i j hij => le_trans (min_le_left _ _) (hdens i j hij))
  exact kmult_contained_of_sets Gr (q + 1) (fun _ => t) S hScard hSdisj hScross

/-
**Cleaned-graph clique-freeness.**  If `F` (which is `(q+1)`-colourable) is
not contained in `J`, then for a small enough uniformity `su` and large enough
parts, the reduced graph `J.regularityReduced P su d` has no `K_{q+1}`.
-/
lemma reduced_cliqueFree {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) {d : ℝ} (hd : 0 < d) :
    ∃ su : ℝ, 0 < su ∧ ∃ m₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) [DecidableRel J.Adj] (P : Finpartition (univ : Finset V)),
      ¬ (F ⊑ J) → (∀ X ∈ P.parts, m₀ ≤ X.card) →
      (J.regularityReduced P su d).CliqueFree (q + 1) := by
  have := @exists_blowup_of_regular q ( Fintype.card W ) d hd;
  obtain ⟨ ε₀, hε₀, m₀, hm₀ ⟩ := this;
  refine' ⟨ ε₀, hε₀, m₀, fun { V } _ _ J _ P hF hP => _ ⟩;
  intro s hs;
  obtain ⟨g, hg⟩ : ∃ g : Fin (q + 1) → V, Function.Injective g ∧ ∀ i, g i ∈ s := by
    have := Finset.equivFinOfCardEq hs.2;
    exact ⟨ _, Subtype.val_injective.comp this.symm.injective, fun i => this.symm i |>.2 ⟩;
  have h_pools : ∀ i j, i ≠ j → P.part (g i) ≠ P.part (g j) ∧ J.IsUniform ε₀ (P.part (g i)) (P.part (g j)) ∧ (d : ℝ) ≤ (J.edgeDensity (P.part (g i)) (P.part (g j)) : ℝ) := by
    intros i j hij
    have h_adj : (regularityReduced P J ε₀ d).Adj (g i) (g j) := by
      exact hs.1 ( hg.2 i ) ( hg.2 j ) ( hg.1.ne hij );
    grind +suggestions;
  have h_pools : ∀ i, m₀ ≤ (P.part (g i)).card := by
    grind +suggestions;
  have h_pools : ∀ i j, i ≠ j → Disjoint (P.part (g i)) (P.part (g j)) := by
    intros i j hij;
    apply P.disjoint;
    · grind +suggestions;
    · grind;
    · grind +suggestions;
  have h_pools : F ⊑ Kmult (q + 1) (fun _ => Fintype.card W) := by
    apply colorable_embeds_Kmult F q (Fintype.card W) hcol (le_refl (Fintype.card W));
  exact hF <| h_pools.trans <| hm₀ J _ ‹_› ‹_› ( fun i j hij => by aesop ) ( fun i j hij => by aesop )

/-
**General cleaning subset.**  Every ordered adjacent pair deleted by the
reduction lies in a non-uniform pair, within a part, or in a sparse pair.
-/
lemma unreduced_edges_subset_gen {V : Type} [Fintype V] [DecidableEq V]
    {J : SimpleGraph V} [DecidableRel J.Adj] {P : Finpartition (univ : Finset V)}
    {su δ : ℝ} :
    ((univ ×ˢ univ).filter (fun xy : V × V =>
        J.Adj xy.1 xy.2 ∧ ¬ (J.regularityReduced P su δ).Adj xy.1 xy.2))
      ⊆ ((P.nonUniforms J su).biUnion (fun UV => UV.1 ×ˢ UV.2))
          ∪ P.parts.biUnion offDiag
          ∪ ((P.sparsePairs J δ).biUnion (fun UV => J.interedges UV.1 UV.2)) := by
  intro x; simp +decide [  ] ;
  intro h₁ h₂; rcases P.exists_mem ( Finset.mem_univ x.1 ) with ⟨ a, ha, ha' ⟩ ; rcases P.exists_mem ( Finset.mem_univ x.2 ) with ⟨ b, hb, hb' ⟩ ; by_cases hab : a = b <;> simp_all +decide [ SimpleGraph.interedges ] ;
  · exact Or.inr <| Or.inl ⟨ b, hb, ha', hb', h₁.ne ⟩;
  · grind +suggestions

/-
**Edge-count bound for the reduction.**  The number of deleted edges is
controlled by the non-uniform, within-part and sparse contributions.
-/
lemma reduced_edge_bound {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] {su δ : ℝ} (hsu : 0 < su) (hδ : 0 ≤ δ)
    (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition)
    (hunif : P.IsUniform J su) (hne : (univ : Finset V).Nonempty) :
    2 * ((J.edgeFinset \ (J.regularityReduced P su δ).edgeFinset).card : ℝ)
      ≤ 4 * su * (Fintype.card V) ^ 2
        + (Fintype.card V) * ((Fintype.card V) + P.parts.card) / P.parts.card
        + 4 * δ * (Fintype.card V) ^ 2 := by
  have h_card : ((univ ×ˢ univ).filter (fun xy : V × V => J.Adj xy.1 xy.2 ∧ ¬ (J.regularityReduced P su δ).Adj xy.1 xy.2)).card ≤ 4 * su * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) + P.parts.card) / P.parts.card + 4 * δ * (Fintype.card V : ℝ) ^ 2 := by
    refine le_trans ( Nat.cast_le.mpr ( Finset.card_le_card ( unreduced_edges_subset_gen ) ) ) ?_;
    refine' le_trans ( Nat.cast_le.mpr ( Finset.card_union_le _ _ ) ) _;
    refine' le_trans ( Nat.cast_add _ _ |> le_of_eq ) ( add_le_add ( le_trans ( Nat.cast_le.mpr <| Finset.card_union_le _ _ ) _ ) _ );
    · refine' le_trans ( Nat.cast_add _ _ |> le_of_eq ) ( add_le_add _ _ );
      · have := Finpartition.IsEquipartition.sum_nonUniforms_lt hne hsu hP hunif;
        exact le_of_lt this;
      · convert! hP.card_biUnion_offDiag_le';
        infer_instance;
    · convert! hP.card_interedges_sparsePairs_le hδ using 1;
  convert! h_card using 1;
  rw [ ← Nat.cast_two, ← Nat.cast_mul ];
  convert! congr_arg ( ( ↑ ) : ℕ → ℝ ) ( SimpleGraph.two_mul_card_edgeFinset ( J ⊓ ( ( regularityReduced P J su δ ) ᶜ ) ) ) using 1;
  · congr with x ; simp +decide [  ];
    cases x ; aesop;
  · congr with x ; simp +decide [  ];
    exact fun h1 h2 => h1.ne

/-
**Clique removal lemma.**  For a `(q+1)`-colourable graph `F` and tolerance
`ε > 0`, every sufficiently large `F`-free graph `J` becomes `K_{q+1}`-free after
deleting at most `ε·N²` edges.
-/
set_option maxHeartbeats 1000000 in
theorem clique_removal {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) [DecidableRel J.Adj],
      N₀ ≤ Fintype.card V → ¬ (F ⊑ J) →
      ∃ D : Finset (Sym2 V), D ⊆ J.edgeFinset ∧
        (D.card : ℝ) ≤ ε * (Fintype.card V) ^ 2 ∧
        ¬ ((⊤ : SimpleGraph (Fin (q + 1))) ⊑ J.deleteEdges ↑D) := by
  -- Apply the lemma `reduced_cliqueFree` to obtain the uniformity threshold `su` and size threshold `m₀`.
  obtain ⟨su, hsu_pos, m₀, hm₀⟩ := reduced_cliqueFree F q hcol (by
  positivity : 0 < min (1 / 2) (ε / 13));
  refine' ⟨ Max.max ( Max.max ( SzemerediRegularity.bound ( Min.min su ( ε / 13 ) ) ⌈13 / ε⌉₊ * m₀ + 1 ) ( ⌈13 / ε⌉₊ ) ) 1, fun { V } _ _ J _ hN hF => _ ⟩;
  obtain ⟨ P, hP₁, hP₂, hP₃, hP₄ ⟩ := szemeredi_regularity J ( show 0 < Min.min su ( ε / 13 ) by positivity ) ( show ⌈13 / ε⌉₊ ≤ Fintype.card V by exact le_trans ( le_max_of_le_left <| le_max_right _ _ ) hN );
  refine' ⟨ J.edgeFinset \ ( J.regularityReduced P ( Min.min su ( ε / 13 ) ) ( Min.min ( 1 / 2 ) ( ε / 13 ) ) ).edgeFinset, _, _, _ ⟩;
  · grind;
  · have := @reduced_edge_bound V _ _ J _ ( Min.min su ( ε / 13 ) ) ( Min.min ( 1 / 2 ) ( ε / 13 ) ) ?_ ?_ P hP₁ hP₄ ?_;
    · -- Simplify the right-hand side of the inequality.
      have h_simplify : (Fintype.card V : ℝ) * (Fintype.card V + P.parts.card) / P.parts.card ≤ (ε / 13) * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) := by
        rw [ div_le_iff₀ ];
        · have := Nat.ceil_le.mp hP₂;
          rw [ div_le_iff₀ ] at this <;> nlinarith [ show ( Fintype.card V : ℝ ) ≥ 1 by norm_cast; exact Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( pos_of_gt ( lt_of_lt_of_le ( Nat.ceil_pos.mpr ( by positivity ) ) hP₂ ) );
      have h_simplify : (Fintype.card V : ℝ) ≤ (ε / 13) * (Fintype.card V : ℝ) ^ 2 := by
        have h_simplify : (Fintype.card V : ℝ) ≥ 13 / ε := by
          exact le_trans ( Nat.le_ceil _ ) ( mod_cast hN.trans' ( le_max_of_le_left ( le_max_right _ _ ) ) );
        rw [ ge_iff_le, div_le_iff₀ ] at h_simplify <;> nlinarith;
      cases min_cases su ( ε / 13 ) <;> cases min_cases ( 1 / 2 ) ( ε / 13 ) <;> nlinarith;
    · positivity;
    · positivity;
    · exact Finset.card_pos.mp ( by simpa using! hN.trans_lt' ( by positivity ) );
  · have h_parts : ∀ X ∈ P.parts, m₀ ≤ X.card := by
      intro X hX;
      have := hP₁.average_le_card_part hX;
      simp +zetaDelta at *;
      exact le_trans ( Nat.le_div_iff_mul_le ( Finset.card_pos.mpr ⟨ _, hX ⟩ ) |>.2 <| by nlinarith ) this;
    have h_clique_free : (J.regularityReduced P (Min.min su (ε / 13)) (Min.min (1 / 2) (ε / 13))).CliqueFree (q + 1) := by
      refine' SimpleGraph.CliqueFree.anti _ ( hm₀ J P hF h_parts );
      apply_rules [ SimpleGraph.regularityReduced_mono ];
      exact min_le_left _ _;
    have h_delete_edges : J.deleteEdges (J.edgeFinset \ (J.regularityReduced P (Min.min su (ε / 13)) (Min.min (1 / 2) (ε / 13))).edgeFinset) = J.regularityReduced P (Min.min su (ε / 13)) (Min.min (1 / 2) (ε / 13)) := by
      ext v w; simp [SimpleGraph.deleteEdges];
    simp_all +decide [  ];
    convert! h_clique_free using 1;
    constructor;
    · intro h t ht; exact h_clique_free t ht;
    · intro h;
      constructor;
      rintro ⟨ f, hf ⟩;
      exact h ( Finset.image f Finset.univ ) ( by
        simp +decide [ SimpleGraph.isNClique_iff ];
        exact ⟨ fun x hx y hy hxy => by obtain ⟨ i, rfl ⟩ := hx; obtain ⟨ j, rfl ⟩ := hy; exact f.map_rel ( by aesop ), by rw [ Finset.card_image_of_injective _ hf ] ; simp +decide ⟩ )

end Erdos550
