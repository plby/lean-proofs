import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Slicing a regular pair

This small foundational module isolates the inheritance lemma for regular
pairs.  Keeping it independent of graph removal lets the
direct off-Turán embedding use regular matching slices without importing the
substantially heavier clique-counting machinery.
-/

open SimpleGraph Finset

namespace Erdos550

/-- If `(s,t)` is `ε`-uniform and `s',t'` occupy at least an `α` fraction
of the corresponding sides, then the new density differs by at most `ε` and
the sliced pair is `(2ε/α)`-uniform. -/
lemma isUniform_slice {V : Type*} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
    {ε α : ℝ} {s t : Finset V} (hα : 0 < α) (hεα : ε ≤ α)
    (hst : Gr.IsUniform ε s t) {s' t' : Finset V}
    (hs' : s' ⊆ s) (ht' : t' ⊆ t)
    (hsc : α * s.card ≤ s'.card) (htc : α * t.card ≤ t'.card) :
    |(Gr.edgeDensity s' t' : ℝ) - (Gr.edgeDensity s t : ℝ)| ≤ ε ∧
      Gr.IsUniform (2 * ε / α) s' t' := by
  refine' ⟨ _, fun s'' hs'' t'' ht'' hs''_card ht''_card => _ ⟩;
  · refine' le_of_lt ( hst hs' ht' _ _ ); all_goals nlinarith;
  · have h_triangle : |(Gr.edgeDensity s'' t'' : ℝ) - (Gr.edgeDensity s t : ℝ)| < ε ∧ |(Gr.edgeDensity s' t' : ℝ) - (Gr.edgeDensity s t : ℝ)| < ε := by
      refine' ⟨ hst ( Finset.Subset.trans hs'' hs' ) ( Finset.Subset.trans ht'' ht' ) _ _, hst hs' ht' _ _ ⟩;
      · by_cases hε : ε ≤ 0;
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( Nat.cast_nonneg _ ) hε ) ( Nat.cast_nonneg _ );
        · nlinarith [ show ( 0 : ℝ ) ≤ #s' by positivity, show ( 0 : ℝ ) ≤ #s'' by positivity, mul_div_cancel₀ ( 2 * ε ) hα.ne' ];
      · by_cases hε : ε = 0;
        · aesop;
        · nlinarith [ show 0 < ε by exact lt_of_le_of_ne ( by
                        contrapose! hst;
                        norm_num [ SimpleGraph.IsUniform ];
                        exact ⟨ s, Finset.Subset.refl _, t, Finset.Subset.refl _, by nlinarith, by nlinarith, by linarith [ abs_nonneg ( Gr.edgeDensity s t - Gr.edgeDensity s t : ℝ ) ] ⟩ ) ( Ne.symm hε ), show ( #t' : ℝ ) ≤ #t by exact_mod_cast Finset.card_le_card ht', mul_div_cancel₀ ( 2 * ε ) hα.ne' ];
      · nlinarith [ show ( s'.card : ℝ ) ≤ s.card by exact_mod_cast Finset.card_le_card hs', show ( t'.card : ℝ ) ≤ t.card by exact_mod_cast Finset.card_le_card ht' ];
      · nlinarith [ show ( t'.card : ℝ ) ≤ t.card by exact_mod_cast Finset.card_le_card ht' ];
    by_cases hs : s = ∅
    · have hs'0 : s' = ∅ := Finset.subset_empty.mp (hs ▸ hs')
      have hs''0 : s'' = ∅ := Finset.subset_empty.mp (hs'0 ▸ hs'')
      have hε0 : 0 < ε := by
        simpa [hs, hs'0, hs''0] using h_triangle.1
      simpa [hs'0, hs''0] using div_pos (mul_pos (by norm_num) hε0) hα
    by_cases ht : t = ∅
    · have ht'0 : t' = ∅ := Finset.subset_empty.mp (ht ▸ ht')
      have ht''0 : t'' = ∅ := Finset.subset_empty.mp (ht'0 ▸ ht'')
      have hε0 : 0 < ε := by
        simpa [ht, ht'0, ht''0] using h_triangle.1
      simpa [ht'0, ht''0] using div_pos (mul_pos (by norm_num) hε0) hα
    have h_alpha_le_one : α ≤ 1 := by
      exact le_of_not_gt fun h => by nlinarith [ show ( s'.card : ℝ ) ≤ s.card from mod_cast Finset.card_le_card hs', show ( t'.card : ℝ ) ≤ t.card from mod_cast Finset.card_le_card ht', show ( s.card : ℝ ) > 0 from mod_cast Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hs ), show ( t.card : ℝ ) > 0 from mod_cast Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ht ) ] ;
    rw [lt_div_iff₀ hα]
    cases abs_cases ((Gr.edgeDensity s'' t'' : ℝ) - Gr.edgeDensity s' t') <;>
      nlinarith [abs_lt.mp h_triangle.1, abs_lt.mp h_triangle.2]

set_option maxHeartbeats 1000000 in
/-- In an `ε`-uniform pair of density at least `d`, at most an
`ε`-fraction of the first side has degree below `(d-ε)` into the second. -/
lemma regular_defect {V : Type*} [Fintype V] [DecidableEq V]
    (Gr : SimpleGraph V) [DecidableRel Gr.Adj]
    {ε d : ℝ} (hε1 : ε ≤ 1) {s t : Finset V}
    (hst : Gr.IsUniform ε s t)
    (hd : d ≤ (Gr.edgeDensity s t : ℝ)) :
    ((s.filter (fun v => ((t.filter (fun w => Gr.Adj v w)).card : ℝ)
        < (d - ε) * t.card)).card : ℝ) ≤ ε * s.card := by
  by_contra h_contra
  have h_uniform :
      |(Gr.edgeDensity
          {v ∈ s | ((t.filter (fun w => Gr.Adj v w)).card : ℝ)
            < (d - ε) * t.card} t : ℝ) -
        (Gr.edgeDensity s t : ℝ)| < ε := by
    apply hst
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
    · linarith
    · exact mul_le_of_le_one_right (Nat.cast_nonneg _) hε1
  have h_edge_density_B :
      (Gr.edgeDensity
        {v ∈ s | ((t.filter (fun w => Gr.Adj v w)).card : ℝ)
          < (d - ε) * t.card} t : ℝ) ≤ d - ε := by
    have h_edge_density_B :
        (Gr.edgeDensity
          {v ∈ s | ((t.filter (fun w => Gr.Adj v w)).card : ℝ)
            < (d - ε) * t.card} t : ℝ) =
          (∑ v ∈ {v ∈ s |
              ((t.filter (fun w => Gr.Adj v w)).card : ℝ)
                < (d - ε) * t.card},
            ((t.filter (fun w => Gr.Adj v w)).card : ℝ)) /
          ({v ∈ s | ((t.filter (fun w => Gr.Adj v w)).card : ℝ)
              < (d - ε) * t.card}.card * t.card) := by
      convert! Rat.cast_div _ _ using 2
      · simp +decide only [Rat.cast_natCast]
        rw [Rel.interedges]
        rw_mod_cast [Finset.card_filter]
        rw [Finset.sum_product]
        aesop
      · norm_cast
      · infer_instance
    rw [h_edge_density_B, div_le_iff₀]
    · refine' le_trans
        (Finset.sum_le_sum fun x hx =>
          le_of_lt <| Finset.mem_filter.mp hx |>.2) _
      norm_num [mul_assoc, mul_comm, mul_left_comm]
    · by_cases ht : t = ∅ <;>
        simp_all +decide [SimpleGraph.edgeDensity]
      · exact h_contra.not_ge
          (mul_nonneg h_uniform.le (Nat.cast_nonneg _))
      · exact mul_pos
          (lt_of_le_of_lt
            (mul_nonneg
              (show 0 ≤ ε by linarith [abs_lt.mp h_uniform])
              (Nat.cast_nonneg _))
            h_contra)
          (Nat.cast_pos.mpr
            (Finset.card_pos.mpr (Finset.nonempty_of_ne_empty ht)))
  linarith [abs_lt.mp h_uniform]

end Erdos550
