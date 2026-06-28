/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1026.
https://www.erdosproblems.com/forum/thread/1026

Informal authors:
- Desmond Weisenberg
- Stijn Cambie
- Wouter van Doorn
- Thomas Bloom
- Boris Alexeev
- KoishiChan
- Terence Tao
- Lawrence Wu
- Jineon Baek
- Junnosuke Koizumi
- Takahiro Ueoro
- Iwan Praton
- Adam Zsolt Wagner
- J. Michael Steele
- Abraham Seidenberg
- Aristotle
- AlphaEvolve

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1026.md
-/
import Mathlib

namespace List

abbrev Sorted {α : Type*} (r : α → α → Prop) (l : List α) : Prop :=
  l.Pairwise r

@[simp]
theorem sorted_nil {α : Type*} {r : α → α → Prop} : List.Sorted r [] := by
  simp [List.Sorted]

namespace Sorted

theorem tail {α : Type*} {r : α → α → Prop} {a : α} {l : List α}
    (h : List.Sorted r (a :: l)) : List.Sorted r l := by
  simpa [List.Sorted] using (List.pairwise_cons.mp h).2

theorem filter {α : Type*} {r : α → α → Prop} (p : α → Bool) {l : List α}
    (h : List.Sorted r l) : List.Sorted r (l.filter p) := by
  simpa [List.Sorted] using List.Pairwise.filter p h

end Sorted

end List

namespace Erdos1026

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.deprecated false
set_option linter.flexible false
set_option linter.unusedVariables false

set_option aesop.warn.nonterminal false
set_option maxHeartbeats 50000000
-- Several generated monotone-subsequence estimates time out at the default heartbeat limit.

theorem sum_sq_gt_one_div_k_sq (k : ℕ) (hk : k ≥ 2) (x : Fin (k^2) → ℝ)
  (h_pos : ∀ i, 0 < x i) (h_inj : Function.Injective x) (h_sum : ∑ i, x i = 1) :
  ∑ i, (x i)^2 > 1 / (k^2 : ℝ) := by
    -- Since the x_i's are distinct, the variance is positive, which implies that ∑ x_i^2 > 1/k².
    have h_var : (∑ i, (x i - 1 / (k ^ 2 : ℝ)) ^ 2) > 0 := by
      by_contra h_var_zero;
      -- If the variance is zero, then all the x_i's must be equal to their mean.
      have h_eq_mean : ∀ i, x i = 1 / (k ^ 2 : ℝ) := by
        exact fun i => eq_of_sub_eq_zero ( sq_eq_zero_iff.mp <| le_antisymm ( le_of_not_gt fun hi => h_var_zero <| hi.trans_le <| Finset.single_le_sum ( fun i _ => sq_nonneg <| x i - 1 / ( k : ℝ ) ^ 2 ) <| Finset.mem_univ _ ) <| sq_nonneg _ );
      cases h_inj ( h_eq_mean ⟨ 0, by positivity ⟩ ▸ h_eq_mean ⟨ 1, by nlinarith ⟩ );
    -- Expanding the square and using the fact that $\sum x_i = 1$, we can simplify the expression.
    have h_expand : ∑ i, (x i - 1 / (k ^ 2 : ℝ)) ^ 2 = ∑ i, x i ^ 2 - 2 * (1 / (k ^ 2 : ℝ)) * ∑ i, x i + (k ^ 2 : ℝ) * (1 / (k ^ 2 : ℝ)) ^ 2 := by
      simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
      grind;
    simp_all +decide [ sq, mul_assoc, ne_of_gt ( zero_lt_two.trans_le hk ) ];
    linarith

theorem area_inequality {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) (S T : Fin n → ℝ)
  (h_pos : ∀ i, 0 < x i)
  (h_inj : Function.Injective x)
  (hS : ∀ i j, i < j → x i < x j → S j ≥ S i + x j)
  (hT : ∀ i j, i < j → x i > x j → T j ≥ T i + x j)
  (hS_base : ∀ i, S i ≥ x i)
  (hT_base : ∀ i, T i ≥ x i) :
  ∃ S_max T_max, (∀ i, S i ≤ S_max) ∧ (∀ i, T i ≤ T_max) ∧ ∑ i, (x i)^2 ≤ S_max * T_max := by
    simp +zetaDelta at *;
    use ∑ i, S i, fun i => Finset.single_le_sum ( fun a _ => le_of_lt <| by linarith [ h_pos a, hS_base a ] ) ( Finset.mem_univ i ), ∑ i, T i, fun i => Finset.single_le_sum ( fun a _ => le_of_lt <| by linarith [ h_pos a, hT_base a ] ) ( Finset.mem_univ i );
    rw [ Finset.sum_mul _ _ _ ];
    exact Finset.sum_le_sum fun i _ => by nlinarith only [ h_pos i, hS_base i, hT_base i, Finset.single_le_sum ( fun a _ => le_of_lt <| h_pos a ) ( Finset.mem_univ i ), Finset.single_le_sum ( fun a _ => le_of_lt <| h_pos a ) ( Finset.mem_univ i ), Finset.single_le_sum ( fun a _ => le_of_lt <| show 0 < T a from lt_of_lt_of_le ( h_pos a ) ( hT_base a ) ) ( Finset.mem_univ i ) ] ;

theorem exists_max_increasing_subseq_sum {n : ℕ} (x : Fin n → ℝ) :
  ∃ (S : Fin n → ℝ),
    (∀ i, ∃ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s ∧ Monotone (x ∘ s) ∧ s (Fin.last m) = i ∧ ∑ j, x (s j) = S i) ∧
    (∀ i j, i < j → x i < x j → S j ≥ S i + x j) ∧
    (∀ i, S i ≥ x i) := by
      -- Define $S_i$ as the maximum sum of an increasing subsequence ending at $i$.
      set S : Fin n → ℝ := fun i => sSup {s : ℝ | ∃ m : ℕ, ∃ s' : Fin (m + 1) → Fin n, StrictMono s' ∧ Monotone (x ∘ s') ∧ s' (Fin.last m) = i ∧ s = ∑ j, x (s' j)};
      refine ⟨ S, ?_, ?_, fun i => ?_ ⟩;
      · -- Since the set of possible sums is finite, the supremum must be achieved by some element in the set.
        have h_finite : ∀ i, ∃ m : ℕ, ∃ s' : Fin (m + 1) → Fin n, StrictMono s' ∧ Monotone (x ∘ s') ∧ s' (Fin.last m) = i ∧ ∑ j, x (s' j) = S i := by
          intro i
          have h_finite_set : Set.Finite {s : ℝ | ∃ m : ℕ, ∃ s' : Fin (m + 1) → Fin n, StrictMono s' ∧ Monotone (x ∘ s') ∧ s' (Fin.last m) = i ∧ s = ∑ j, x (s' j)} := by
            -- Since $m$ is bounded by $n$, there are only finitely many possible values for $m$.
            have h_m_finite : Set.Finite {m : ℕ | ∃ s' : Fin (m + 1) → Fin n, StrictMono s' ∧ Monotone (x ∘ s') ∧ s' (Fin.last m) = i} := by
              refine Set.finite_iff_bddAbove.mpr ⟨ n, fun m hm => ?_ ⟩ ; aesop;
              have := Finset.card_le_univ ( Finset.image w Finset.univ ) ; simp_all +decide [ Finset.card_image_of_injective _ left.injective ] ;
              linarith;
            refine Set.Finite.subset ( h_m_finite.biUnion fun m hm => Set.Finite.image ( fun s' : Fin ( m + 1 ) → Fin n => ∑ j : Fin ( m + 1 ), x ( s' j ) ) ( Set.finite_Iic ( fun _ => i ) ) ) ?_;
            intro s hs; obtain ⟨ m, s', hs₁, hs₂, hs₃, rfl ⟩ := hs; exact Set.mem_iUnion₂.mpr ⟨ m, ⟨ s', hs₁, hs₂, hs₃ ⟩, Set.mem_image_of_mem _ <| fun j => hs₃ ▸ hs₁.monotone ( Fin.le_last _ ) ⟩ ;
          have := h_finite_set.isCompact.sSup_mem;
          -- Since the set is nonempty, we can apply the hypothesis this to conclude that the supremum is in the set.
          have h_nonempty : {s : ℝ | ∃ m : ℕ, ∃ s' : Fin (m + 1) → Fin n, StrictMono s' ∧ Monotone (x ∘ s') ∧ s' (Fin.last m) = i ∧ s = ∑ j, x (s' j)}.Nonempty := by
            exact ⟨ _, ⟨ 0, fun _ => i, by simp +decide [ StrictMono ], by simp +decide [ Monotone ], by simp +decide, rfl ⟩ ⟩;
          exact this h_nonempty |> fun ⟨ m, s', hs₁, hs₂, hs₃, hs₄ ⟩ => ⟨ m, s', hs₁, hs₂, hs₃, hs₄.symm ⟩;
        assumption;
      · -- Take any subsequence ending at i and show that adding j to it gives a subsequence ending at j with sum S i + x j.
        intros i j hij hxij
        have h_subseq : ∀ m : ℕ, ∀ s' : Fin (m + 1) → Fin n, StrictMono s' → Monotone (x ∘ s') → s' (Fin.last m) = i → ∃ m' : ℕ, ∃ s'' : Fin (m' + 1) → Fin n, StrictMono s'' ∧ Monotone (x ∘ s'') ∧ s'' (Fin.last m') = j ∧ ∑ j, x (s'' j) = ∑ j, x (s' j) + x j := by
          intros m s' hs'_mono hs'_mono' hs'_last
          use m + 1
          use Fin.snoc s' j
          aesop;
          · intro i j hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> aesop;
            · exact False.elim <| (not_lt_of_ge (Fin.le_last i.castSucc)) hij;
            · exact lt_of_le_of_lt ( hs'_mono.monotone ( Fin.le_last _ ) ) hij_1;
          · intro i j hij; induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> aesop;
            exact le_trans ( hs'_mono' ( show i ≤ Fin.last m from Fin.le_last _ ) ) hxij.le;
          · simp +decide [ Fin.sum_univ_castSucc, Fin.snoc ];
        -- Take any subsequence ending at i and show that adding j to it gives a subsequence ending at j with sum at least S i + x j.
        have h_sum_ge : ∀ s ∈ {s : ℝ | ∃ m : ℕ, ∃ s' : Fin (m + 1) → Fin n, StrictMono s' ∧ Monotone (x ∘ s') ∧ s' (Fin.last m) = i ∧ s = ∑ j, x (s' j)}, s + x j ≤ S j := by
          -- By definition of $S$, we know that for any $s$ in the set, $s + x j$ is less than or equal to $S j$.
          intros s hs
          obtain ⟨m, s', hs_mono, hs_monotone, hs_last, rfl⟩ := hs
          obtain ⟨m', s'', hs''_mono, hs''_monotone, hs''_last, hs''_sum⟩ := h_subseq m s' hs_mono hs_monotone hs_last
          have h_le_S : ∑ j, x (s'' j) ≤ S j := by
            apply le_csSup;
            · refine ⟨ ∑ i, |x i|, fun s hs => ?_ ⟩ ; aesop;
              have h_sum_le : ∑ j : Fin (w + 1), x (w_1 j) ≤ ∑ i ∈ Finset.image w_1 Finset.univ, |x i| := by
                rw [ Finset.sum_image <| by intros i hi j hj hij; exact left.injective hij ];
                exact Finset.sum_le_sum fun _ _ => le_abs_self _;
              exact h_sum_le.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.image_subset_iff.mpr fun i _ => Finset.mem_univ _ ) fun _ _ _ => abs_nonneg _ );
            · exact ⟨ m', s'', hs''_mono, hs''_monotone, hs''_last, rfl ⟩;
          linarith;
        -- Since $S_i$ is the supremum of the set, we have $S_i \leq S_j - x_j$.
        have h_Si_le_Sj_minus_xj : S i ≤ S j - x j := by
          refine csSup_le ?_ ?_ <;> norm_num;
          · exact ⟨ _, ⟨ 0, fun _ => i, by simp +decide [ StrictMono ], by simp +decide [ Monotone ], by simp +decide, rfl ⟩ ⟩;
          · exact fun b m s' hs' hs'' hs''' hb => by linarith [ h_sum_ge _ ⟨ m, s', hs', hs'', hs''', hb ⟩ ] ;
        linarith;
      · refine le_csSup ?_ ?_;
        · refine ⟨ ∑ j : Fin n, |x j|, fun s hs => ?_ ⟩ ; aesop;
          refine le_trans ?_ ( Finset.sum_le_sum_of_subset_of_nonneg
            ( Finset.subset_univ ( Finset.image w_1 Finset.univ ) )
            fun i _ _ => abs_nonneg (x i) );
          rw [ Finset.sum_image <| by intros i hi j hj hij; exact left.injective hij ] ; exact Finset.sum_le_sum fun i _ => le_abs_self _;
        · exact ⟨ 0, fun _ => i, by simp +decide [ StrictMono ], by simp +decide [ Monotone ], by simp +decide, by simp +decide ⟩

set_option maxHeartbeats 50000000 in
-- The decreasing-subsequence sum construction needs extra heartbeats.
theorem exists_max_decreasing_subseq_sum {n : ℕ} (x : Fin n → ℝ) :
  ∃ (T : Fin n → ℝ),
    (∀ i, ∃ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s ∧ Antitone (x ∘ s) ∧ s (Fin.last m) = i ∧ ∑ j, x (s j) = T i) ∧
    (∀ i j, i < j → x i > x j → T j ≥ T i + x j) ∧
    (∀ i, T i ≥ x i) := by
      -- Define T i as the maximum sum of a decreasing subsequence ending at i.
      have hT_def : ∀ i, ∃ (T_i : ℝ), (∃ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s ∧ Antitone (x ∘ s) ∧ s (Fin.last m) = i ∧ ∑ j, x (s j) = T_i) ∧ (∀ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s → Antitone (x ∘ s) → s (Fin.last m) = i → ∑ j, x (s j) ≤ T_i) := by
        -- Fix an index $i$.
        intro i
        -- Define the set of sums of decreasing subsequences ending at $i$.
        set S_i := {t | ∃ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s ∧ Antitone (x ∘ s) ∧ s (Fin.last m) = i ∧ ∑ j, x (s j) = t};
        have hS_i_finite : S_i.Finite := by
          -- Since Fin n is finite, the number of possible subsequences is finite. For each m, the number of possible s functions is finite because there are only finitely many ways to choose m elements from Fin n. Therefore, the total number of possible sums is finite.
          have h_finite_subseq : ∀ m : ℕ, Set.Finite {s : Fin (m + 1) → Fin n | StrictMono s ∧ Antitone (x ∘ s) ∧ s (Fin.last m) = i} := by
            exact fun m => Set.toFinite _;
          refine Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_le_nat n ) fun m hm => Set.Finite.image ( fun s : Fin ( m + 1 ) → Fin n => ∑ j : Fin ( m + 1 ), x ( s j ) ) ( h_finite_subseq m ) ) ?_ ; intro ; aesop;
          exact ⟨ w, Nat.le_of_lt_succ ( by linarith [ show w < n from by simpa using Finset.card_le_univ ( Finset.image w_1 Finset.univ ) |> fun h => by simpa [ Finset.card_image_of_injective _ left.injective ] using h ] ), w_1, ⟨ left, left_1, rfl ⟩, rfl ⟩;
        -- The singleton sequence {i} is a valid decreasing subsequence, so its sum x i is in S_i.
        have h_singleton : x i ∈ S_i := by
          exact ⟨ 0, fun _ => i, by simp ( config := { decide := Bool.true } ) [ StrictMono, Antitone ] ⟩;
        exact ⟨ Finset.max' ( hS_i_finite.toFinset ) ⟨ _, hS_i_finite.mem_toFinset.mpr h_singleton ⟩, hS_i_finite.mem_toFinset.mp ( Finset.max'_mem _ _ ), fun m s hs hs' hi => Finset.le_max' _ _ ( hS_i_finite.mem_toFinset.mpr ⟨ m, s, hs, hs', hi, rfl ⟩ ) ⟩;
      choose T hT₁ hT₂ using hT_def;
      refine ⟨ T, ?_, ?_, ?_ ⟩ <;> aesop;
      · obtain ⟨ m, s, hs₁, hs₂, hs₃, hs₄ ⟩ := hT₁ i;
        refine le_trans ?_ ( hT₂ j ( m + 1 ) ( Fin.snoc s j ) ?_ ?_ ?_ );
        · simp +decide [ Fin.sum_univ_castSucc, hs₄ ];
        · intro i j hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> aesop;
          · exact False.elim <| (not_lt_of_ge (Fin.le_last i_1.castSucc)) hij;
          · exact lt_of_le_of_lt ( hs₁.monotone ( Fin.le_last _ ) ) a;
        · intro i j hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> aesop;
          exact le_trans a_1.le ( hs₂ <| Fin.le_last _ );
        · simp +decide [ Fin.snoc ];
      · specialize hT₁ i ; aesop;
        specialize hT₂ ( w_1 ( Fin.last w ) ) 0 ( fun _ => w_1 ( Fin.last w ) ) ; aesop;
        exact hT₂ ( by simp ( config := { decide := Bool.true } ) [ StrictMono ] ) ( by simp ( config := { decide := Bool.true } ) [ Antitone ] )

set_option maxHeartbeats 50000000 in
-- The tight area inequality expands several generated subsequence goals.
theorem area_inequality_tight {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) (S T : Fin n → ℝ)
  (h_pos : ∀ i, 0 < x i)
  (h_inj : Function.Injective x)
  (hS : ∀ i j, i < j → x i < x j → S j ≥ S i + x j)
  (hT : ∀ i j, i < j → x i > x j → T j ≥ T i + x j)
  (hS_base : ∀ i, S i ≥ x i)
  (hT_base : ∀ i, T i ≥ x i) :
  ∃ S_max T_max, (∀ i, S i ≤ S_max) ∧ (∀ i, T i ≤ T_max) ∧ (∃ i, S i = S_max) ∧ (∃ i, T i = T_max) ∧ ∑ i, (x i)^2 ≤ S_max * T_max := by
    -- Let $S_{max} = \max_i S_i$ and $T_{max} = \max_i T_i$. These exist since $n \ne 0$.
    obtain ⟨S_max, hS_max⟩ : ∃ S_max, (∀ i, S i ≤ S_max) ∧ (∃ i, S i = S_max) := by
      cases n <;> aesop
    obtain ⟨T_max, hT_max⟩ : ∃ T_max, (∀ i, T i ≤ T_max) ∧ (∃ i, T i = T_max) := by
      cases n <;> aesop;
    -- The rectangles $R_i$ are pairwise disjoint and contained within $[0, S_{max}) \times [0, T_{max})$.
    have h_disjoint : ∀ i j, i ≠ j → Disjoint (Set.Ico (S i - x i) (S i) ×ˢ Set.Ico (T i - x i) (T i)) (Set.Ico (S j - x j) (S j) ×ˢ Set.Ico (T j - x j) (T j)) := by
      intro i j hij; cases lt_or_gt_of_ne hij <;> simp_all +decide [ Set.disjoint_left ] ;
      · by_cases h_cases : x i < x j;
        · intro a b ha hb hc hd he hf hg; linarith [ hS i j ‹_› h_cases, hS_base i, hS_base j, hT_base i, hT_base j ] ;
        · intro a b ha hb hc hd he hf hg; linarith [ hT i j ‹_› ( lt_of_le_of_ne ( le_of_not_gt h_cases ) ( Ne.symm ( h_inj.ne hij ) ) ) ] ;
      · by_cases h_cases : x i < x j;
        · intros; linarith [ hT _ _ ‹_› ( by linarith ) ] ;
        · aesop;
          by_cases h_cases : x j < x i;
          · grind;
          · exact False.elim <| h_cases <| lt_of_le_of_ne ‹_› <| h_inj.ne <| by aesop;
    -- The rectangles $R_i$ are contained within $[0, S_{max}) \times [0, T_{max})$.
    have h_contained : ∀ i, Set.Ico (S i - x i) (S i) ×ˢ Set.Ico (T i - x i) (T i) ⊆ Set.Ico 0 S_max ×ˢ Set.Ico 0 T_max := by
      exact fun i => Set.prod_mono ( Set.Ico_subset_Ico ( by linarith [ hS_base i, h_pos i ] ) ( by linarith [ hS_max.1 i ] ) ) ( Set.Ico_subset_Ico ( by linarith [ hT_base i, h_pos i ] ) ( by linarith [ hT_max.1 i ] ) );
    -- The total area of the rectangles is $\sum_{i=1}^n x_i^2$.
    have h_total_area : ∑ i, (MeasureTheory.volume (Set.Ico (S i - x i) (S i) ×ˢ Set.Ico (T i - x i) (T i))).toReal = ∑ i, (x i)^2 := by
      erw [ Finset.sum_congr rfl ] ; intros i _ ; erw [ MeasureTheory.Measure.prod_prod ] ; norm_num [ sq, h_pos i |> le_of_lt ] ;
    -- The total area of the rectangles is less than or equal to the area of the rectangle $[0, S_{max}) \times [0, T_{max})$.
    have h_total_area_le : ∑ i, (MeasureTheory.volume (Set.Ico (S i - x i) (S i) ×ˢ Set.Ico (T i - x i) (T i))).toReal ≤ (MeasureTheory.volume (Set.Ico 0 S_max ×ˢ Set.Ico 0 T_max)).toReal := by
      rw [ ← ENNReal.toReal_sum ];
      · gcongr;
        · erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
          exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top );
        · rw [ ← MeasureTheory.measure_biUnion_finset ];
          · exact MeasureTheory.measure_mono <| Set.iUnion₂_subset fun i _ => h_contained i;
          · exact fun i _ j _ hij => h_disjoint i j hij;
          · exact fun i _ => measurableSet_Ico.prod measurableSet_Ico;
      · exact fun i _ => ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( h_contained i ) ) ( by erw [ MeasureTheory.Measure.prod_prod ] ; exact ENNReal.mul_lt_top ( by norm_num ) ( by norm_num ) ) );
    simp_all +decide [ MeasureTheory.Measure.volume_eq_prod ];
    obtain ⟨iS, hiS⟩ := hS_max.2
    obtain ⟨iT, hiT⟩ := hT_max.2
    have h_area : ∑ i, (x i)^2 ≤ S_max * T_max := by
      rwa [ ENNReal.toReal_ofReal ( show 0 ≤ S_max by obtain ⟨ i, hi ⟩ := hS_max.2; linarith [ h_pos i, hS_base i ] ), ENNReal.toReal_ofReal ( show 0 ≤ T_max by obtain ⟨ i, hi ⟩ := hT_max.2; linarith [ h_pos i, hT_base i ] ) ] at h_total_area_le
    refine ⟨iS, ?_, iT, ?_, ?_⟩
    · intro i
      simpa [hiS] using hS_max.1 i
    · intro i
      simpa [hiT] using hT_max.1 i
    · simpa [hiS, hiT] using h_area

/-- If `x : Fin (k^2) → ℝ` is a sequence of `k^2` distinct positive real numbers
with total sum `1`, then there is a nonempty monotone (nondecreasing or nonincreasing)
subsequence whose sum is at least `1 / k`. -/
theorem exists_monotone_subseq_sum_ge
    (k : ℕ) (hk : 0 < k)
    (x : Fin (k ^ 2) → ℝ)
    (h_pos : ∀ i, 0 < x i)
    (h_inj : Function.Injective x)
    (h_sum : ∑ i, x i = (1 : ℝ)) :
    ∃ (n : ℕ) (s : Fin (n + 1) → Fin (k^2)),
      StrictMono s ∧
      (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) ∧
      (∑ i, x (s i)) ≥ (1 : ℝ) / (k : ℝ) := by
  -- If $k=1$, the sequence has length 1 and sum 1, so the single element is a subsequence with sum $1 \ge 1/1$.
  by_cases hk1 : k = 1;
  · aesop;
    refine ⟨ 0, fun _ => 0, by simp +decide, Or.inl <| fun _ _ _ => by simp +decide, by simp +decide [ h_sum ] ⟩;
  · -- Let $S$ be the function from `exists_max_increasing_subseq_sum`.
    obtain ⟨S, hS⟩ := exists_max_increasing_subseq_sum x
    -- Let $T$ be the function from `exists_max_decreasing_subseq_sum`.
    obtain ⟨T, hT⟩ := exists_max_decreasing_subseq_sum x;
    -- Apply `area_inequality_tight` to get $S_{max}, T_{max}$ such that $\sum x_i^2 \le S_{max} T_{max}$.
    obtain ⟨S_max, T_max, hS_max, hT_max, hS_max_eq, hT_max_eq, h_sum_sq⟩ := area_inequality_tight (by
    positivity) x S T h_pos h_inj hS.right.left hT.right.left hS.right.right hT.right.right;
    -- This implies $S_{max} > 1/k$ or $T_{max} > 1/k$.
    have h_max_gt : S_max > 1 / (k : ℝ) ∨ T_max > 1 / (k : ℝ) := by
      -- Since $S_{max} * T_{max} > 1/k^2$, and both $S_{max}$ and $T_{max}$ are positive, at least one of them must be greater than $1/k$.
      have h_max_gt : S_max * T_max > 1 / (k : ℝ)^2 := by
        have h_sum_sq_gt : ∑ i, (x i)^2 > 1 / (k : ℝ)^2 := by
          convert sum_sq_gt_one_div_k_sq k ( Nat.lt_of_le_of_ne hk ( Ne.symm hk1 ) ) x h_pos h_inj h_sum using 1;
        exact h_sum_sq_gt.trans_le h_sum_sq;
      -- By contradiction, assume both $S_{max}$ and $T_{max}$ are less than or equal to $1/k$.
      by_contra h_contra
      push Not at h_contra;
      exact (not_le_of_gt h_max_gt) ( by convert mul_le_mul h_contra.1 h_contra.2 ( show 0 ≤ T_max by obtain ⟨ i, rfl ⟩ := hT_max_eq; exact le_trans ( le_of_lt ( h_pos i ) ) ( hT.2.2 i ) ) ( show 0 ≤ ( 1 : ℝ ) / k by positivity ) using 1 ; ring );
    rcases h_max_gt with h | h;
    · obtain ⟨ i, hi ⟩ := hS_max_eq;
      -- Since $S i = S_max$ and $S_max > 1/k$, there exists an increasing subsequence ending at $i$ with sum $S i$.
      obtain ⟨m, s, hs_mono, hs_monotone, hs_last, hs_sum⟩ := hS.left i;
      exact ⟨ m, s, hs_mono, Or.inl hs_monotone, by linarith [ hS_max i ] ⟩;
    · rcases hT_max_eq with ⟨ i, rfl ⟩;
      rcases hT.1 i with ⟨ m, s, hs₁, hs₂, hs₃, hs₄ ⟩ ; exact ⟨ m, s, hs₁, Or.inr hs₂, by linarith ⟩

/-
Defines the Erdos-Szekeres sequence `es_seq` of length `k^2`.
-/
def es_seq (k : ℕ) (i : Fin (k^2)) : ℕ :=
  (i.val % k) * k + (k - 1 - i.val / k)

/-
Proves that the Erdos-Szekeres sequence `es_seq` is injective.
-/
theorem es_seq_injective (k : ℕ) (hk : 0 < k) : Function.Injective (es_seq k) := by
  -- To prove injectivity, assume es_seq k i = es_seq k j. Then, (i.val % k) * k + (k - 1 - i.val / k) = (j.val % k) * k + (k - 1 - j.val / k).
  intro i j hij
  have h_mod : i.val % k = j.val % k := by
    unfold es_seq at hij;
    nlinarith [ Nat.mod_lt ( i : ℕ ) hk, Nat.mod_lt ( j : ℕ ) hk, Nat.sub_le ( k - 1 ) ( ( i : ℕ ) / k ), Nat.sub_le ( k - 1 ) ( ( j : ℕ ) / k ), Nat.div_mul_le_self ( i : ℕ ) k, Nat.div_mul_le_self ( j : ℕ ) k, Nat.sub_add_cancel ( show 1 ≤ k from hk ) ]
  have h_div : i.val / k = j.val / k := by
    unfold es_seq at hij; aesop;
    rw [ tsub_right_inj ] at hij <;> try omega;
    · exact Nat.le_sub_one_of_lt ( Nat.div_lt_of_lt_mul <| by nlinarith [ Fin.is_lt i ] );
    · exact Nat.le_sub_one_of_lt ( Nat.div_lt_of_lt_mul <| by nlinarith [ Fin.is_lt j ] )
  have h_eq : i.val = j.val := by
    rw [ ← Nat.mod_add_div i k, ← Nat.mod_add_div j k, h_mod ] ; simp +decide [ h_div ]
  exact Fin.ext h_eq

/-
Proves that any monotone subsequence of the Erdos-Szekeres sequence `es_seq` has length at most `k`.
-/
theorem es_seq_monotone_subseq_le (k : ℕ) (hk : 0 < k)
    (n : ℕ) (s : Fin (n + 1) → Fin (k^2))
    (hs : StrictMono s)
    (h_mono : Monotone (es_seq k ∘ s) ∨ Antitone (es_seq k ∘ s)) :
    n + 1 ≤ k := by
      cases h_mono;
      ·
        have h_diff : ∀ p q : Fin (n + 1), p < q → es_seq k (s p) < es_seq k (s q) := by
          have h_diff : ∀ p q : Fin (n + 1), p < q → es_seq k (s p) ≠ es_seq k (s q) := by
            intro p q hpq h
            exact hpq.ne (hs.injective ((es_seq_injective k hk) h))
          intros p q hpq
          have h_le : es_seq k (s p) ≤ es_seq k (s q) := by
            exact ‹Monotone ( es_seq k ∘ s ) › hpq.le;
          exact lt_of_le_of_ne h_le ( h_diff p q hpq );
        have h_distinct : Finset.card (Finset.image (fun p : Fin (n + 1) => (s p).val % k) Finset.univ) = n + 1 := by
          rw [ Finset.card_image_of_injective _ _, Finset.card_fin ];
          intros p q hpq;
          cases lt_trichotomy p q <;> aesop;
          · have := h_diff p q h_1; unfold es_seq at this; aesop;
            exact absurd this ( not_lt_of_ge ( Nat.sub_le_sub_left ( Nat.div_le_div_right <| le_of_lt <| hs h_1 ) _ ) );
          · have := h_diff _ _ h_3; simp_all +decide [ es_seq ] ;
            exact False.elim <|
              (not_le_of_gt (Nat.lt_of_succ_le this)) <|
                Nat.sub_le_sub_left (Nat.div_le_div_right <| le_of_lt <| hs h_3) _;
        exact h_distinct ▸ le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun p _ => Finset.mem_range.mpr ( Nat.mod_lt _ hk ) ) ) ( by simp );
      ·
        set u : Fin (k ^ 2) → ℕ := fun i => i.val / k
        set v : Fin (k ^ 2) → ℕ := fun i => i.val % k;
        have h_u_mono : ∀ p q : Fin (n + 1), p < q → u (s p) < u (s q) := by
          intros p q hpq
          have h_u_lt : u (s p) ≤ u (s q) := by
            exact Nat.div_le_div_right ( le_of_lt ( hs hpq ) );
          cases eq_or_lt_of_le h_u_lt <;> aesop;
          have := h hpq.le; unfold es_seq at this; aesop;
          have := hs hpq; ( have := Nat.mod_add_div ( s p ) k; have := Nat.mod_add_div ( s q ) k; aesop; );
          grind +ring;
        have h_u_distinct : Finset.card (Finset.image (fun p => u (s p)) Finset.univ) ≤ k := by
          exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun p _ => Finset.mem_range.mpr <| Nat.div_lt_of_lt_mul <| by nlinarith [ Fin.is_lt ( s p ) ] ) ( by simp );
        rw [ Finset.card_image_of_injective _ fun p q hpq => le_antisymm ( le_of_not_gt fun h => by linarith [ h_u_mono _ _ h ] ) ( le_of_not_gt fun h => by linarith [ h_u_mono _ _ h ] ) ] at h_u_distinct ; aesop

/-
Proves that the sum of the Erdos-Szekeres sequence is `k^2 * (k^2 - 1) / 2`.
-/
theorem es_seq_sum_eq (k : ℕ) (hk : 0 < k) :
  ∑ i : Fin (k^2), (es_seq k i : ℝ) = (k^2 * (k^2 - 1)) / 2 := by
    -- Since `es_seq` is a permutation of the numbers from `0` to `k^2 - 1`, their sum is the same as the sum of the first `k^2` natural numbers.
    have h_perm : Finset.image (fun i : Fin (k^2) => es_seq k i) Finset.univ = Finset.range (k^2) := by
      refine Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.2 fun i _ => Finset.mem_range.2 ?_ ) ?_;
      · unfold es_seq; aesop;
        nlinarith [ Nat.mod_lt ( i : ℕ ) hk, Nat.sub_le ( k - 1 ) ( ( i : ℕ ) / k ), Nat.div_mul_le_self ( i : ℕ ) k, Nat.sub_add_cancel hk ];
      · -- Since `es_seq k` is injective, the image of `es_seq k` over `Finset.univ` has cardinality `k^2`.
        have h_inj : Function.Injective (es_seq k) := by
          exact es_seq_injective k hk;
        rw [ Finset.card_image_of_injective _ h_inj, Finset.card_fin ];
        norm_num;
    -- Since `es_seq` is a permutation of the numbers from `0` to `k^2 - 1`, their sum is the same as the sum of the first `k^2` natural numbers, which is `k^2 * (k^2 - 1) / 2`.
    have h_sum_eq : ∑ i : Fin (k^2), (es_seq k i : ℝ) = ∑ i ∈ Finset.range (k^2), (i : ℝ) := by
      -- Since `es_seq k` is a permutation of the numbers from `0` to `k^2 - 1`, the sum over the image of `es_seq k` is the same as the sum over `Finset.range (k^2)`.
      have h_sum_eq : ∑ i ∈ Finset.image (fun i : Fin (k^2) => es_seq k i) Finset.univ, (i : ℝ) = ∑ i ∈ Finset.range (k^2), (i : ℝ) := by
        rw [h_perm];
      rw [ ← h_sum_eq, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ];
    rw [ h_sum_eq, ← Nat.cast_sum, Finset.sum_range_id ];
    cases k <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
    rw [ Nat.cast_div ] <;> norm_num ; exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )

set_option maxHeartbeats 50000000 in
-- The approximate-sharpness construction needs extra heartbeats for generated bounds.
/-- Approximate sharpness of the bound `1 / k` from `exists_monotone_subseq_sum_ge`:
for every `ε > 0`, there exists a sequence `x : Fin (k^2) → ℝ` of `k^2` distinct
positive real numbers with total sum `1` such that every nonempty monotone
(nondecreasing or nonincreasing) subsequence has sum at most `ε + 1 / k`. -/
theorem exists_seq_with_monotone_subseq_sum_le
    (k : ℕ) (hk : 0 < k) :
    ∀ ε > (0 : ℝ),
      ∃ (x : Fin (k ^ 2) → ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∑ i, x i = (1 : ℝ)) ∧
        (∀ (n : ℕ) (s : Fin (n + 1) → Fin (k ^ 2)),
          StrictMono s →
          (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
          (∑ i, x (s i)) ≤ ε + (1 : ℝ) / (k : ℝ)) := by
  intro ε hεpos
  let δ : ℝ := ε / k
  let y_fun : Fin (k^2) → ℝ := fun i => 1 + δ * (es_seq k i : ℝ)
  let S : ℝ := ∑ i : Fin (k^2), y_fun i
  let x_fun : Fin (k^2) → ℝ := fun i => y_fun i / S
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkR_one : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
  have hδ_pos : 0 < δ := div_pos hεpos hkR_pos
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hS_pos : 0 < S := by
    exact Finset.sum_pos
      (fun _ _ => add_pos_of_pos_of_nonneg zero_lt_one <|
        mul_nonneg hδ_nonneg <| Nat.cast_nonneg _)
      ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩
  use x_fun
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact div_pos
      (add_pos_of_pos_of_nonneg zero_lt_one <|
        mul_nonneg hδ_nonneg <| Nat.cast_nonneg _)
      hS_pos
  ·
    intro i j hij
    dsimp [x_fun, y_fun] at hij
    field_simp [hS_pos.ne'] at hij
    have h_eq_real : (es_seq k i : ℝ) = es_seq k j := by
      nlinarith [hδ_pos]
    apply es_seq_injective k hk
    exact_mod_cast h_eq_real
  ·
    dsimp [x_fun, S]
    rw [← Finset.sum_div, div_self hS_pos.ne']
  · intro n s hs h_mono
    have h_mono_es :
        Monotone (fun i => es_seq k (s i)) ∨ Antitone (fun i => es_seq k (s i)) := by
      rcases h_mono with h_mono | h_anti
      · left
        intro a b hab
        have hx_le := h_mono hab
        have hy_le : y_fun (s a) ≤ y_fun (s b) := by
          exact (div_le_div_iff_of_pos_right hS_pos).mp hx_le
        dsimp [y_fun] at hy_le
        have h_real : (es_seq k (s a) : ℝ) ≤ es_seq k (s b) := by
          nlinarith [hδ_pos]
        exact_mod_cast h_real
      · right
        intro a b hab
        have hx_le := h_anti hab
        have hy_le : y_fun (s b) ≤ y_fun (s a) := by
          exact (div_le_div_iff_of_pos_right hS_pos).mp hx_le
        dsimp [y_fun] at hy_le
        have h_real : (es_seq k (s b) : ℝ) ≤ es_seq k (s a) := by
          nlinarith [hδ_pos]
        exact_mod_cast h_real
    have h_len : n + 1 ≤ k :=
      es_seq_monotone_subseq_le k hk n s hs h_mono_es
    have h_es_seq_bound : ∀ i : Fin (k^2), es_seq k i ≤ k^2 := by
      intro i
      unfold es_seq
      have hmod_lt : i.val % k < k := Nat.mod_lt _ hk
      have hmod_le : i.val % k ≤ k - 1 := Nat.le_pred_of_lt hmod_lt
      have hleft : (i.val % k) * k ≤ (k - 1) * k := Nat.mul_le_mul_right k hmod_le
      have hright : k - 1 - i.val / k ≤ k - 1 := Nat.sub_le _ _
      have htotal : (k - 1) * k + (k - 1) ≤ k^2 := by
        have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr hk
        calc
          (k - 1) * k + (k - 1) ≤ (k - 1) * k + k := by
            exact Nat.add_le_add_left (Nat.sub_le _ _) _
          _ = k * k := by
            have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk1
            nlinarith
          _ = k^2 := by
            rw [pow_two]
      exact le_trans (Nat.add_le_add hleft hright) htotal
    have h_y_bound : ∀ i : Fin (n + 1), y_fun (s i) ≤ 1 + δ * (k : ℝ)^2 := by
      intro i
      dsimp [y_fun]
      have h_es_real : (es_seq k (s i) : ℝ) ≤ (k : ℝ)^2 := by
        exact_mod_cast h_es_seq_bound (s i)
      have hmul := mul_le_mul_of_nonneg_left h_es_real hδ_nonneg
      nlinarith
    have h_sum_y_bound :
        (∑ i : Fin (n + 1), y_fun (s i)) ≤
          (k : ℝ) * (1 + δ * (k : ℝ)^2) := by
      calc
        (∑ i : Fin (n + 1), y_fun (s i)) ≤
            ∑ _ : Fin (n + 1), (1 + δ * (k : ℝ)^2) := by
          exact Finset.sum_le_sum fun i _ => h_y_bound i
        _ = ((n + 1 : ℕ) : ℝ) * (1 + δ * (k : ℝ)^2) := by
          simp
          ring
        _ ≤ (k : ℝ) * (1 + δ * (k : ℝ)^2) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_len)
            (add_nonneg zero_le_one <| mul_nonneg hδ_nonneg <| sq_nonneg (k : ℝ))
    have hS_ge : (k : ℝ)^2 ≤ S := by
      dsimp [S, y_fun]
      calc
        (k : ℝ)^2 = (k^2 : ℝ) := by
          norm_num [pow_two]
        _ = ∑ _ : Fin (k^2), (1 : ℝ) := by
          simp
        _ ≤ ∑ i : Fin (k^2), (1 + δ * (es_seq k i : ℝ)) := by
          exact Finset.sum_le_sum fun i _ =>
            le_add_of_nonneg_right <| mul_nonneg hδ_nonneg <| Nat.cast_nonneg _
    have h_num_nonneg : 0 ≤ (k : ℝ) * (1 + δ * (k : ℝ)^2) := by
      exact mul_nonneg (le_of_lt hkR_pos)
        (add_nonneg zero_le_one <| mul_nonneg hδ_nonneg <| sq_nonneg (k : ℝ))
    have h_sum_x :
        (∑ i : Fin (n + 1), x_fun (s i)) =
          (∑ i : Fin (n + 1), y_fun (s i)) / S := by
      dsimp [x_fun]
      rw [← Finset.sum_div]
    calc
      (∑ i : Fin (n + 1), x_fun (s i))
          = (∑ i : Fin (n + 1), y_fun (s i)) / S := h_sum_x
      _ ≤ ((k : ℝ) * (1 + δ * (k : ℝ)^2)) / S := by
        exact div_le_div_of_nonneg_right h_sum_y_bound hS_pos.le
      _ ≤ ((k : ℝ) * (1 + δ * (k : ℝ)^2)) / (k : ℝ)^2 := by
        exact div_le_div_of_nonneg_left h_num_nonneg (by positivity) hS_ge
      _ = (1 : ℝ) / k + δ * k := by
        field_simp [hkR_pos.ne']
      _ = ε + (1 : ℝ) / k := by
        dsimp [δ]
        field_simp [hkR_pos.ne']
        ring

/-- Approximate sharpness of the bound `k / (k^2 - 1)` in the special case
corresponding informally to `a = -1` in the more general statement:

If `n = k^2 - 1`, then for every `ε > 0` there exists a sequence
`x : Fin n → ℝ` of `n` distinct positive real numbers with total sum `1` such
that every nonempty monotone (nondecreasing or nonincreasing) subsequence has
sum at most `ε + k / (k^2 - 1)`.

Subsequences are encoded by strictly increasing maps `s : Fin (m + 1) → Fin n`;
`StrictMono s` ensures we have a genuine subsequence, and `Fin (m + 1)` ensures
the subsequence is nonempty. -/
theorem exists_seq_with_monotone_subseq_sum_le_minus_one
    (k n : ℕ)
    (hk : 1 < k)
    (hn : n = k ^ 2 - 1) :
    ∀ ε > (0 : ℝ),
      ∃ (x : Fin n → ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∑ i, x i = (1 : ℝ)) ∧
        (∀ (m : ℕ) (s : Fin (m + 1) → Fin n),
          StrictMono s →
          (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
          (∑ i, x (s i)) ≤
            ε + (k : ℝ) / ((k ^ 2 - 1 : ℕ) : ℝ)) := by
  intros ε hε_pos
  subst n
  obtain ⟨x, hx_pos, hx_inj, hx_sum, hx_bound⟩ :
      ∃ (x : Fin (k ^ 2) → ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∑ i, x i = 1) ∧
        (∀ m : ℕ, ∀ s : Fin (m + 1) → Fin (k ^ 2),
          StrictMono s →
          (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
          (∑ i, x (s i)) ≤ ε / 2 + (1 : ℝ) / (k : ℝ)) := by
    exact exists_seq_with_monotone_subseq_sum_le k (by linarith) (ε / 2) (half_pos hε_pos)
  obtain ⟨i_min, hi_min⟩ : ∃ i_min : Fin (k ^ 2), ∀ i : Fin (k ^ 2), x i_min ≤ x i := by
    simpa [ge_iff_le] using
      Finset.exists_min_image Finset.univ (fun i => x i) ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩
  have hcard_erase : (Finset.univ.erase i_min).card = k ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i_min), Finset.card_univ, Fintype.card_fin]
  let emb : Fin (k ^ 2 - 1) ↪o Fin (k ^ 2) :=
    (Finset.univ.erase i_min).orderEmbOfFin hcard_erase
  let x' : Fin (k ^ 2 - 1) → ℝ := fun i => x (emb i) / (1 - x i_min)
  have hk_sq_gt_one : 1 < k ^ 2 := by nlinarith
  have hcard_erase_pos : 0 < (Finset.univ.erase i_min).card := by
    rw [hcard_erase]
    exact Nat.sub_pos_of_lt hk_sq_gt_one
  have hsum_erase_pos : 0 < ∑ i ∈ Finset.univ.erase i_min, x i :=
    Finset.sum_pos (fun i _ => hx_pos i) (Finset.card_pos.mp hcard_erase_pos)
  have hsum_erase_add : (∑ i ∈ Finset.univ.erase i_min, x i) + x i_min = 1 := by
    simp [hx_sum]
  have hx_min_lt_one : x i_min < 1 := by
    linarith
  have hden_pos : 0 < 1 - x i_min := sub_pos.mpr hx_min_lt_one
  have hden_ne : 1 - x i_min ≠ 0 := ne_of_gt hden_pos
  have hsum_erase_eq : ∑ i ∈ Finset.univ.erase i_min, x i = 1 - x i_min := by
    linarith
  have h_image : Finset.image emb Finset.univ = Finset.univ.erase i_min := by
    apply Finset.ext
    intro a
    simp [emb]
  have hsum_emb : (∑ i : Fin (k ^ 2 - 1), x (emb i)) = ∑ i ∈ Finset.univ.erase i_min, x i := by
    rw [← Finset.sum_image]
    · rw [h_image]
    · intro a _ b _ h
      exact emb.injective h
  refine ⟨x', ?_, ?_, ?_, ?_⟩
  · intro i
    exact div_pos (hx_pos (emb i)) hden_pos
  · intro i j hij
    have hnum : x (emb i) = x (emb j) := by
      have hmul := congrArg (fun t : ℝ => t * (1 - x i_min)) hij
      simpa [x', hden_ne] using hmul
    exact emb.injective (hx_inj hnum)
  · calc
      ∑ i : Fin (k ^ 2 - 1), x' i = (∑ i : Fin (k ^ 2 - 1), x (emb i)) / (1 - x i_min) := by
        simp [x', Finset.sum_div]
      _ = (∑ i ∈ Finset.univ.erase i_min, x i) / (1 - x i_min) := by
        rw [hsum_emb]
      _ = 1 := by
        rw [hsum_erase_eq]
        exact div_self hden_ne
  · intro m s hs_mono hs_monotone
    have hs_mono_emb : StrictMono (fun i : Fin (m + 1) => emb (s i)) :=
      emb.strictMono.comp hs_mono
    have hs_monotone_x :
        Monotone (fun i => x (emb (s i))) ∨ Antitone (fun i => x (emb (s i))) := by
      cases hs_monotone with
      | inl h =>
          left
          intro a b hab
          have hle := h hab
          exact (div_le_div_iff_of_pos_right hden_pos).mp (by simpa [x'] using hle)
      | inr h =>
          right
          intro a b hab
          have hle := h hab
          exact (div_le_div_iff_of_pos_right hden_pos).mp (by simpa [x'] using hle)
    have h_sum_x' :
        ∑ i : Fin (m + 1), x' (s i) ≤ (ε / 2 + 1 / (k : ℝ)) / (1 - x i_min) := by
      calc
        ∑ i : Fin (m + 1), x' (s i) =
            (∑ i : Fin (m + 1), x (emb (s i))) / (1 - x i_min) := by
          simp [x', Finset.sum_div]
        _ ≤ (ε / 2 + 1 / (k : ℝ)) / (1 - x i_min) := by
          exact div_le_div_of_nonneg_right
            (hx_bound m (fun i => emb (s i)) hs_mono_emb hs_monotone_x)
            (le_of_lt hden_pos)
    have h_x_min_le : x i_min ≤ 1 / (k ^ 2 : ℝ) := by
      have hsum_le : ∑ i : Fin (k ^ 2), x i_min ≤ ∑ i : Fin (k ^ 2), x i :=
        Finset.sum_le_sum (fun i _ => hi_min i)
      have hmul : (k ^ 2 : ℝ) * x i_min ≤ 1 := by
        simpa [hx_sum, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le
      have hk_sq_pos : 0 < (k ^ 2 : ℝ) := by positivity
      rw [le_div_iff₀ hk_sq_pos]
      simpa [mul_comm] using hmul
    have hkR2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk_pos : 0 < (k : ℝ) := by nlinarith
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have hk_sq_pos_real : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero hk_ne
    have hsq_sub_pos : 0 < (k : ℝ) ^ 2 - 1 := by nlinarith
    have hsq_sub_ne : (k : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt hsq_sub_pos
    have hden_lower : ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 ≤ 1 - x i_min := by
      have hle : 1 - 1 / (k ^ 2 : ℝ) ≤ 1 - x i_min := by
        linarith
      calc
        ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 = 1 - 1 / (k ^ 2 : ℝ) := by
          field_simp [hk_ne]
        _ ≤ 1 - x i_min := hle
    have hden_lower_pos : 0 < ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 :=
      div_pos hsq_sub_pos hk_sq_pos_real
    have h_subst :
        (ε / 2 + 1 / (k : ℝ)) / (1 - x i_min) ≤
          (ε / 2 + 1 / (k : ℝ)) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) := by
      calc
        (ε / 2 + 1 / (k : ℝ)) / (1 - x i_min) ≤
            (ε / 2 + 1 / (k : ℝ)) / (((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2) := by
          exact div_le_div_of_nonneg_left (by positivity) hden_lower_pos hden_lower
        _ = (ε / 2 + 1 / (k : ℝ)) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) := by
          field_simp [hk_ne, hsq_sub_ne]
    have h_final :
        (ε / 2 + 1 / (k : ℝ)) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) ≤
          ε + (k : ℝ) / (((k ^ 2 - 1 : ℕ) : ℝ)) := by
      have hcast : (((k ^ 2 - 1 : ℕ) : ℝ)) = (k : ℝ) ^ 2 - 1 := by
        norm_num [Nat.cast_sub (show 1 ≤ k ^ 2 from by nlinarith)]
      have hfactor_le_two : ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) ≤ 2 := by
        rw [div_le_iff₀ hsq_sub_pos]
        nlinarith
      have h_eps_part : (ε / 2) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) ≤ ε := by
        calc
          (ε / 2) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) ≤ (ε / 2) * 2 := by
            exact mul_le_mul_of_nonneg_left hfactor_le_two (by positivity)
          _ = ε := by ring
      have h_one_part :
          (1 / (k : ℝ)) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) =
            (k : ℝ) / ((k : ℝ) ^ 2 - 1) := by
        field_simp [hk_ne, hsq_sub_ne]
      rw [hcast]
      calc
        (ε / 2 + 1 / (k : ℝ)) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) =
            (ε / 2) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) +
              (1 / (k : ℝ)) * ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) := by
          ring
        _ ≤ ε + (k : ℝ) / ((k : ℝ) ^ 2 - 1) := add_le_add h_eps_part (le_of_eq h_one_part)
    exact le_trans h_sum_x' (le_trans h_subst h_final)

/-
===
-/

/-
M(L) is the maximum sum of a monotone subsequence of L. M_inc(L) and M_dec(L) are the maximum sums of increasing and decreasing subsequences, respectively.
-/
noncomputable def M_inc (L : List ℝ) : ℝ :=
  (L.sublists.filter (fun S => Decidable.decide (S.Sorted (· < ·)))).map List.sum |>.maximum.getD 0

noncomputable def M_dec (L : List ℝ) : ℝ :=
  (L.sublists.filter (fun S => Decidable.decide (S.Sorted (· > ·)))).map List.sum |>.maximum.getD 0

noncomputable def M (L : List ℝ) : ℝ := max (M_inc L) (M_dec L)

/-
c_set(n) is the set of ratios M(L)/sum(L) for all valid sequences L of length n. c(n) is the infimum of this set.
-/
def c_set (n : ℕ) : Set ℝ :=
  { r | ∃ (L : List ℝ), L.length = n ∧ L.Pairwise (· ≠ ·) ∧ (∀ x ∈ L, 0 < x) ∧ r = M L / L.sum }

noncomputable def c (n : ℕ) : ℝ := sInf (c_set n)

/-
If every element in A is less than every element in B, then the maximum sum of an increasing subsequence of A ++ B is the sum of the maximum sums of increasing subsequences of A and B.
-/
theorem M_inc_append_of_lt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
  M_inc (A ++ B) = M_inc A + M_inc B := by
  unfold M_inc
  let good : List ℝ → List (List ℝ) := fun L =>
    L.sublists.filter (fun S => Decidable.decide (S.Sorted (· < ·)))
  let sums : List ℝ → List ℝ := fun L => (good L).map List.sum
  change (sums (A ++ B)).maximum.getD 0 =
    (sums A).maximum.getD 0 + (sums B).maximum.getD 0
  have zero_mem_sums : ∀ L : List ℝ, (0 : ℝ) ∈ sums L := by
    intro L
    refine List.mem_map.mpr ?_
    refine ⟨[], ?_, by simp⟩
    simp [good, List.mem_sublists, List.Sorted, List.Pairwise.nil]
  have le_max_getD :
      ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → ∀ x ∈ xs, x ≤ xs.maximum.getD 0 := by
    intro xs h0 x hx
    have hxle : (x : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' hx
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        simp [hm] at hxle ⊢
        exact hxle
  have max_getD_mem : ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → xs.maximum.getD 0 ∈ xs := by
    intro xs h0
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        have hmem : m ∈ xs := (List.maximum_eq_coe_iff.mp hm).1
        simpa [hm] using hmem
  have mem_sums_append :
      ∀ x : ℝ, x ∈ sums (A ++ B) ↔
        ∃ xA ∈ sums A, ∃ xB ∈ sums B, x = xA + xB := by
    intro x
    constructor
    · intro hx
      rcases List.mem_map.mp hx with ⟨S, hSgood, rfl⟩
      have hS : S.Sublist (A ++ B) ∧ S.Sorted (· < ·) := by
        simpa [sums, good, List.mem_sublists] using hSgood
      rcases hS with ⟨hSsub, hSsort⟩
      have hSmem : S ∈ (A ++ B).sublists := by
        simpa [List.mem_sublists] using hSsub
      rw [List.sublists_append] at hSmem
      simp at hSmem
      rcases hSmem with ⟨T₂, hT₂sub, T₁, hT₁sub, hEq⟩
      have hEq' : S = T₁ ++ T₂ := hEq.symm
      have hsort12 : T₁.Sorted (· < ·) ∧ T₂.Sorted (· < ·) := by
        rw [hEq', List.Sorted, List.pairwise_append] at hSsort
        exact ⟨hSsort.1, hSsort.2.1⟩
      have hT₁mem : T₁.sum ∈ sums A := by
        refine List.mem_map.mpr ?_
        refine ⟨T₁, ?_, rfl⟩
        simpa [sums, good, List.mem_sublists] using And.intro hT₁sub hsort12.1
      have hT₂mem : T₂.sum ∈ sums B := by
        refine List.mem_map.mpr ?_
        refine ⟨T₂, ?_, rfl⟩
        simpa [sums, good, List.mem_sublists] using And.intro hT₂sub hsort12.2
      refine ⟨T₁.sum, hT₁mem, T₂.sum, hT₂mem, ?_⟩
      simp [hEq', List.sum_append]
    · rintro ⟨xA, hxA, xB, hxB, rfl⟩
      rcases List.mem_map.mp hxA with ⟨T₁, hT₁good, rfl⟩
      rcases List.mem_map.mp hxB with ⟨T₂, hT₂good, rfl⟩
      have hT₁ : T₁.Sublist A ∧ T₁.Sorted (· < ·) := by
        simpa [sums, good, List.mem_sublists] using hT₁good
      have hT₂ : T₂.Sublist B ∧ T₂.Sorted (· < ·) := by
        simpa [sums, good, List.mem_sublists] using hT₂good
      refine List.mem_map.mpr ?_
      refine ⟨T₁ ++ T₂, ?_, by simp [List.sum_append]⟩
      have hsorted : (T₁ ++ T₂).Sorted (· < ·) := by
        rw [List.Sorted, List.pairwise_append]
        refine ⟨hT₁.2, hT₂.2, ?_⟩
        intro a ha b hb
        exact h a (hT₁.1.subset ha) b (hT₂.1.subset hb)
      have hsub : (T₁ ++ T₂).Sublist (A ++ B) :=
        List.Sublist.append hT₁.1 hT₂.1
      simpa [sums, good, List.mem_sublists] using And.intro hsub hsorted
  apply le_antisymm
  · have hABmem : (sums (A ++ B)).maximum.getD 0 ∈ sums (A ++ B) :=
      max_getD_mem (sums (A ++ B)) (zero_mem_sums (A ++ B))
    rcases (mem_sums_append ((sums (A ++ B)).maximum.getD 0)).mp hABmem with
      ⟨xA, hxA, xB, hxB, hEq⟩
    have hxAle : xA ≤ (sums A).maximum.getD 0 :=
      le_max_getD (sums A) (zero_mem_sums A) xA hxA
    have hxBle : xB ≤ (sums B).maximum.getD 0 :=
      le_max_getD (sums B) (zero_mem_sums B) xB hxB
    linarith
  · have hAmem : (sums A).maximum.getD 0 ∈ sums A :=
      max_getD_mem (sums A) (zero_mem_sums A)
    have hBmem : (sums B).maximum.getD 0 ∈ sums B :=
      max_getD_mem (sums B) (zero_mem_sums B)
    have hpair : (sums A).maximum.getD 0 + (sums B).maximum.getD 0 ∈ sums (A ++ B) :=
      (mem_sums_append ((sums A).maximum.getD 0 + (sums B).maximum.getD 0)).mpr
        ⟨(sums A).maximum.getD 0, hAmem,
          (sums B).maximum.getD 0, hBmem, rfl⟩
    exact le_max_getD (sums (A ++ B)) (zero_mem_sums (A ++ B))
      ((sums A).maximum.getD 0 + (sums B).maximum.getD 0) hpair

/-
If every element in A is less than every element in B, then the maximum sum of a decreasing subsequence of A ++ B is the maximum of the sums of decreasing subsequences of A and B.
-/
theorem M_dec_append_of_lt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
  M_dec (A ++ B) = max (M_dec A) (M_dec B) := by
  unfold M_dec
  let good : List ℝ → List (List ℝ) := fun L =>
    L.sublists.filter (fun S => Decidable.decide (S.Sorted (· > ·)))
  let sums : List ℝ → List ℝ := fun L => (good L).map List.sum
  change (sums (A ++ B)).maximum.getD 0 =
    max ((sums A).maximum.getD 0) ((sums B).maximum.getD 0)
  have zero_mem_sums : ∀ L : List ℝ, (0 : ℝ) ∈ sums L := by
    intro L
    refine List.mem_map.mpr ?_
    refine ⟨[], ?_, by simp⟩
    simp [good, List.mem_sublists, List.Sorted, List.Pairwise.nil]
  have le_max_getD :
      ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → ∀ x ∈ xs, x ≤ xs.maximum.getD 0 := by
    intro xs h0 x hx
    have hxle : (x : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' hx
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        simp [hm] at hxle ⊢
        exact hxle
  have max_getD_mem : ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → xs.maximum.getD 0 ∈ xs := by
    intro xs h0
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        have hmem : m ∈ xs := (List.maximum_eq_coe_iff.mp hm).1
        simpa [hm] using hmem
  have mem_sums_append :
      ∀ x : ℝ, x ∈ sums (A ++ B) ↔ x ∈ sums A ∨ x ∈ sums B := by
    intro x
    constructor
    · intro hx
      rcases List.mem_map.mp hx with ⟨S, hSgood, rfl⟩
      have hS : S.Sublist (A ++ B) ∧ S.Sorted (· > ·) := by
        simpa [sums, good, List.mem_sublists] using hSgood
      rcases hS with ⟨hSsub, hSsort⟩
      have hSmem : S ∈ (A ++ B).sublists := by
        simpa [List.mem_sublists] using hSsub
      rw [List.sublists_append] at hSmem
      simp at hSmem
      rcases hSmem with ⟨T₂, hT₂sub, T₁, hT₁sub, hEq⟩
      have hEq' : S = T₁ ++ T₂ := hEq.symm
      have hSsort' : (T₁ ++ T₂).Sorted (· > ·) := by
        simpa [hEq'] using hSsort
      have hparts : T₁.Sorted (· > ·) ∧ T₂.Sorted (· > ·) := by
        rw [List.Sorted, List.pairwise_append] at hSsort'
        exact ⟨hSsort'.1, hSsort'.2.1⟩
      have hcross : ∀ a ∈ T₁, ∀ b ∈ T₂, a > b := by
        rw [List.Sorted, List.pairwise_append] at hSsort'
        exact hSsort'.2.2
      cases T₁ with
      | nil =>
          right
          refine List.mem_map.mpr ?_
          refine ⟨T₂, ?_, by simp [hEq']⟩
          simpa [sums, good, List.mem_sublists] using And.intro hT₂sub hparts.2
      | cons a T₁t =>
          cases T₂ with
          | nil =>
              left
              refine List.mem_map.mpr ?_
              refine ⟨a :: T₁t, ?_, by simp [hEq']⟩
              simpa [sums, good, List.mem_sublists] using And.intro hT₁sub hparts.1
          | cons b T₂t =>
              have haA : a ∈ A := hT₁sub.subset (by simp)
              have hbB : b ∈ B := hT₂sub.subset (by simp)
              have hgt : a > b := hcross a (by simp) b (by simp)
              have hlt : a < b := h a haA b hbB
              linarith
    · intro hx
      rcases hx with hxA | hxB
      · rcases List.mem_map.mp hxA with ⟨T₁, hT₁good, rfl⟩
        have hT₁ : T₁.Sublist A ∧ T₁.Sorted (· > ·) := by
          simpa [sums, good, List.mem_sublists] using hT₁good
        refine List.mem_map.mpr ?_
        refine ⟨T₁ ++ [], ?_, by simp⟩
        have hsub : (T₁ ++ []).Sublist (A ++ B) :=
          List.Sublist.append hT₁.1 (List.nil_sublist B)
        have hsorted : (T₁ ++ []).Sorted (· > ·) := by
          simpa using hT₁.2
        simpa [sums, good, List.mem_sublists] using And.intro hsub hsorted
      · rcases List.mem_map.mp hxB with ⟨T₂, hT₂good, rfl⟩
        have hT₂ : T₂.Sublist B ∧ T₂.Sorted (· > ·) := by
          simpa [sums, good, List.mem_sublists] using hT₂good
        refine List.mem_map.mpr ?_
        refine ⟨[] ++ T₂, ?_, by simp⟩
        have hsub : ([] ++ T₂).Sublist (A ++ B) :=
          List.Sublist.append (List.nil_sublist A) hT₂.1
        have hsorted : ([] ++ T₂).Sorted (· > ·) := by
          simpa using hT₂.2
        simpa [sums, good, List.mem_sublists] using And.intro hsub hsorted
  apply le_antisymm
  · have hABmem : (sums (A ++ B)).maximum.getD 0 ∈ sums (A ++ B) :=
      max_getD_mem (sums (A ++ B)) (zero_mem_sums (A ++ B))
    rcases (mem_sums_append ((sums (A ++ B)).maximum.getD 0)).mp hABmem with hAmax | hBmax
    · have hle : (sums (A ++ B)).maximum.getD 0 ≤ (sums A).maximum.getD 0 :=
        le_max_getD (sums A) (zero_mem_sums A)
          ((sums (A ++ B)).maximum.getD 0) hAmax
      exact le_trans hle (le_max_left _ _)
    · have hle : (sums (A ++ B)).maximum.getD 0 ≤ (sums B).maximum.getD 0 :=
        le_max_getD (sums B) (zero_mem_sums B)
          ((sums (A ++ B)).maximum.getD 0) hBmax
      exact le_trans hle (le_max_right _ _)
  · apply max_le
    · have hAmem : (sums A).maximum.getD 0 ∈ sums A :=
        max_getD_mem (sums A) (zero_mem_sums A)
      have hABmem : (sums A).maximum.getD 0 ∈ sums (A ++ B) :=
        (mem_sums_append ((sums A).maximum.getD 0)).mpr (Or.inl hAmem)
      exact le_max_getD (sums (A ++ B)) (zero_mem_sums (A ++ B))
        ((sums A).maximum.getD 0) hABmem
    · have hBmem : (sums B).maximum.getD 0 ∈ sums B :=
        max_getD_mem (sums B) (zero_mem_sums B)
      have hABmem : (sums B).maximum.getD 0 ∈ sums (A ++ B) :=
        (mem_sums_append ((sums B).maximum.getD 0)).mpr (Or.inr hBmem)
      exact le_max_getD (sums (A ++ B)) (zero_mem_sums (A ++ B))
        ((sums B).maximum.getD 0) hABmem

/-
If every element in A is greater than every element in B, then the maximum sum of an increasing subsequence of A ++ B is the maximum of the sums of increasing subsequences of A and B.
-/
theorem M_inc_append_of_gt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a > b) :
  M_inc (A ++ B) = max (M_inc A) (M_inc B) := by
    let cand : List ℝ → List ℝ := fun L =>
      (L.sublists.filter (fun s => Decidable.decide (s.Sorted (· < ·)))).map List.sum
    have hmem_of_sublist :
        ∀ {L s : List ℝ}, s.Sublist L → s.Sorted (· < ·) → s.sum ∈ cand L := by
      intro L s hs hsort
      dsimp [cand]
      exact List.mem_map.mpr
        ⟨s, List.mem_filter.mpr ⟨List.mem_sublists.mpr hs, by simpa⟩, rfl⟩
    have hnil_mem : ∀ L : List ℝ, (0 : ℝ) ∈ cand L := by
      intro L
      simpa using hmem_of_sublist (L := L) (s := []) (List.nil_sublist L) (List.sorted_nil)
    have h_cases : ∀ s : List ℝ, s.Sublist (A ++ B) → s.Sorted (· < ·) → s.Sublist A ∨ s.Sublist B := by
      intro s hs hs'
      rw [List.sublist_append_iff] at hs
      rcases hs with ⟨sA, sB, rfl, hsA, hsB⟩
      rcases sA with _ | ⟨x, xs⟩
      · right
        simpa using hsB
      rcases sB with _ | ⟨y, ys⟩
      · left
        simpa using hsA
      exfalso
      have hxy : x < y := hs'.rel_of_mem_append (by simp) (by simp)
      have hyx : y < x := h x (hsA.subset (by simp)) y (hsB.subset (by simp))
      linarith
    have hAB_cases : ∀ {x : ℝ}, x ∈ cand (A ++ B) → x ∈ cand A ∨ x ∈ cand B := by
      intro x hx
      dsimp [cand] at hx
      rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
      rcases List.mem_filter.mp hs with ⟨hs_sub, hs_sort⟩
      have hs_sub' : s.Sublist (A ++ B) := List.mem_sublists.mp hs_sub
      have hs_sort' : s.Sorted (· < ·) := of_decide_eq_true hs_sort
      rcases h_cases s hs_sub' hs_sort' with hsA | hsB
      · exact Or.inl (hmem_of_sublist hsA hs_sort')
      · exact Or.inr (hmem_of_sublist hsB hs_sort')
    have hA_subset : cand A ⊆ cand (A ++ B) := by
      intro x hx
      dsimp [cand] at hx
      rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
      rcases List.mem_filter.mp hs with ⟨hs_sub, hs_sort⟩
      have hs_sort' : s.Sorted (· < ·) := of_decide_eq_true hs_sort
      exact hmem_of_sublist ((List.mem_sublists.mp hs_sub).trans (List.sublist_append_left A B)) hs_sort'
    have hB_subset : cand B ⊆ cand (A ++ B) := by
      intro x hx
      dsimp [cand] at hx
      rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
      rcases List.mem_filter.mp hs with ⟨hs_sub, hs_sort⟩
      have hs_sort' : s.Sorted (· < ·) := of_decide_eq_true hs_sort
      exact hmem_of_sublist ((List.mem_sublists.mp hs_sub).trans (List.sublist_append_right A B)) hs_sort'
    have hmaxeq :
        (cand (A ++ B)).maximum = max (cand A).maximum (cand B).maximum := by
      apply le_antisymm
      · apply List.maximum_le_of_forall_le
        intro x hx
        rcases hAB_cases hx with hxA | hxB
        · exact le_trans (List.le_maximum_of_mem' hxA) (le_max_left _ _)
        · exact le_trans (List.le_maximum_of_mem' hxB) (le_max_right _ _)
      · exact max_le (List.maximum_mono hA_subset) (List.maximum_mono hB_subset)
    have hA_ne : (cand A).maximum ≠ ⊥ := by
      exact List.maximum_ne_bot_of_ne_nil (by
        intro hnil
        have := hnil_mem A
        simp [hnil] at this)
    have hB_ne : (cand B).maximum ≠ ⊥ := by
      exact List.maximum_ne_bot_of_ne_nil (by
        intro hnil
        have := hnil_mem B
        simp [hnil] at this)
    unfold M_inc
    change (cand (A ++ B)).maximum.getD 0 =
      max ((cand A).maximum.getD 0) ((cand B).maximum.getD 0)
    rw [hmaxeq]
    cases hAmax : (cand A).maximum with
    | bot => simp_all
    | coe a =>
      cases hBmax : (cand B).maximum with
      | bot => simp_all
      | coe b =>
        have hga : Option.getD (↑a : WithBot ℝ) 0 = a := rfl
        have hgb : Option.getD (↑b : WithBot ℝ) 0 = b := rfl
        simp_all [max_def]
        by_cases hab : a ≤ b
        · simp [hab, hgb]
        · simp [hab, hga]

/-
If every element in A is greater than every element in B, then the maximum sum of a decreasing subsequence of A ++ B is the sum of the maximum sums of decreasing subsequences of A and B.
-/
theorem M_dec_append_of_gt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a > b) :
  M_dec (A ++ B) = M_dec A + M_dec B := by
  unfold M_dec
  let good : List ℝ → List (List ℝ) := fun L =>
    L.sublists.filter (fun S => Decidable.decide (S.Sorted (· > ·)))
  let sums : List ℝ → List ℝ := fun L => (good L).map List.sum
  change (sums (A ++ B)).maximum.getD 0 =
    (sums A).maximum.getD 0 + (sums B).maximum.getD 0
  have zero_mem_sums : ∀ L : List ℝ, (0 : ℝ) ∈ sums L := by
    intro L
    refine List.mem_map.mpr ?_
    refine ⟨[], ?_, by simp⟩
    simp [good, List.mem_sublists, List.Sorted, List.Pairwise.nil]
  have le_max_getD :
      ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → ∀ x ∈ xs, x ≤ xs.maximum.getD 0 := by
    intro xs h0 x hx
    have hxle : (x : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' hx
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        simp [hm] at hxle ⊢
        exact hxle
  have max_getD_mem : ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → xs.maximum.getD 0 ∈ xs := by
    intro xs h0
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        have hmem : m ∈ xs := (List.maximum_eq_coe_iff.mp hm).1
        simpa [hm] using hmem
  have mem_sums_append :
      ∀ x : ℝ, x ∈ sums (A ++ B) ↔
        ∃ xA ∈ sums A, ∃ xB ∈ sums B, x = xA + xB := by
    intro x
    constructor
    · intro hx
      rcases List.mem_map.mp hx with ⟨S, hSgood, rfl⟩
      have hS : S.Sublist (A ++ B) ∧ S.Sorted (· > ·) := by
        simpa [sums, good, List.mem_sublists] using hSgood
      rcases hS with ⟨hSsub, hSsort⟩
      have hSmem : S ∈ (A ++ B).sublists := by
        simpa [List.mem_sublists] using hSsub
      rw [List.sublists_append] at hSmem
      simp at hSmem
      rcases hSmem with ⟨T₂, hT₂sub, T₁, hT₁sub, hEq⟩
      have hEq' : S = T₁ ++ T₂ := hEq.symm
      have hsort12 : T₁.Sorted (· > ·) ∧ T₂.Sorted (· > ·) := by
        rw [hEq', List.Sorted, List.pairwise_append] at hSsort
        exact ⟨hSsort.1, hSsort.2.1⟩
      have hT₁mem : T₁.sum ∈ sums A := by
        refine List.mem_map.mpr ?_
        refine ⟨T₁, ?_, rfl⟩
        simpa [sums, good, List.mem_sublists] using And.intro hT₁sub hsort12.1
      have hT₂mem : T₂.sum ∈ sums B := by
        refine List.mem_map.mpr ?_
        refine ⟨T₂, ?_, rfl⟩
        simpa [sums, good, List.mem_sublists] using And.intro hT₂sub hsort12.2
      refine ⟨T₁.sum, hT₁mem, T₂.sum, hT₂mem, ?_⟩
      simp [hEq', List.sum_append]
    · rintro ⟨xA, hxA, xB, hxB, rfl⟩
      rcases List.mem_map.mp hxA with ⟨T₁, hT₁good, rfl⟩
      rcases List.mem_map.mp hxB with ⟨T₂, hT₂good, rfl⟩
      have hT₁ : T₁.Sublist A ∧ T₁.Sorted (· > ·) := by
        simpa [sums, good, List.mem_sublists] using hT₁good
      have hT₂ : T₂.Sublist B ∧ T₂.Sorted (· > ·) := by
        simpa [sums, good, List.mem_sublists] using hT₂good
      refine List.mem_map.mpr ?_
      refine ⟨T₁ ++ T₂, ?_, by simp [List.sum_append]⟩
      have hsorted : (T₁ ++ T₂).Sorted (· > ·) := by
        rw [List.Sorted, List.pairwise_append]
        refine ⟨hT₁.2, hT₂.2, ?_⟩
        intro a ha b hb
        exact h a (hT₁.1.subset ha) b (hT₂.1.subset hb)
      have hsub : (T₁ ++ T₂).Sublist (A ++ B) :=
        List.Sublist.append hT₁.1 hT₂.1
      simpa [sums, good, List.mem_sublists] using And.intro hsub hsorted
  apply le_antisymm
  · have hABmem : (sums (A ++ B)).maximum.getD 0 ∈ sums (A ++ B) :=
      max_getD_mem (sums (A ++ B)) (zero_mem_sums (A ++ B))
    rcases (mem_sums_append ((sums (A ++ B)).maximum.getD 0)).mp hABmem with
      ⟨xA, hxA, xB, hxB, hEq⟩
    have hxAle : xA ≤ (sums A).maximum.getD 0 :=
      le_max_getD (sums A) (zero_mem_sums A) xA hxA
    have hxBle : xB ≤ (sums B).maximum.getD 0 :=
      le_max_getD (sums B) (zero_mem_sums B) xB hxB
    linarith
  · have hAmem : (sums A).maximum.getD 0 ∈ sums A :=
      max_getD_mem (sums A) (zero_mem_sums A)
    have hBmem : (sums B).maximum.getD 0 ∈ sums B :=
      max_getD_mem (sums B) (zero_mem_sums B)
    have hpair : (sums A).maximum.getD 0 + (sums B).maximum.getD 0 ∈ sums (A ++ B) :=
      (mem_sums_append ((sums A).maximum.getD 0 + (sums B).maximum.getD 0)).mpr
        ⟨(sums A).maximum.getD 0, hAmem,
          (sums B).maximum.getD 0, hBmem, rfl⟩
    exact le_max_getD (sums (A ++ B)) (zero_mem_sums (A ++ B))
      ((sums A).maximum.getD 0 + (sums B).maximum.getD 0) hpair

/-
Definition of the sequence construction parameterized by epsilon, following the user's Python code.
-/
def es_part (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) : List ℝ :=
  (List.range num_blocks).flatMap fun b =>
    (List.range block_size).map fun i =>
      let local_idx := (num_blocks - 1 - b) * block_size + i
      base_val + (start_idx + local_idx) * eps

def seq_eps (k : ℤ) (a : ℤ) (eps : ℝ) : List ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let num_blocks1 := red
  let block_size1 := k.toNat - red
  let num_blocks2 := blue
  let block_size2 := blue
  let num_blocks3 := k.toNat - red
  let block_size3 := k.toNat
  let len1 := num_blocks1 * block_size1
  let len2 := num_blocks2 * block_size2
  let len3 := num_blocks3 * block_size3
  let start3 := 0
  let start2 := len3
  let start1 := len3 + len2
  let part1 := es_part num_blocks1 block_size1 blue start1 eps
  let part2 := es_part num_blocks2 block_size2 red start2 eps
  let part3 := es_part num_blocks3 block_size3 blue start3 eps
  part1 ++ part2 ++ part3

/-
If L is sorted increasing and has positive elements, then M_inc(L) is the sum of L.
-/
theorem M_inc_sorted {L : List ℝ} (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, 0 < x) :
  M_inc L = L.sum := by
  let sums := (L.sublists.filter (fun S => Decidable.decide (S.Sorted (· < ·)))).map List.sum
  have hmax : sums.maximum = (L.sum : WithBot ℝ) := by
    rw [List.maximum_eq_coe_iff]
    constructor
    · refine List.mem_map.mpr ?_
      refine ⟨L, ?_, rfl⟩
      rw [List.mem_filter]
      constructor
      · exact List.mem_sublists.mpr (List.Sublist.refl L)
      · exact decide_eq_true h_sorted
    · intro a ha
      rcases List.mem_map.mp ha with ⟨S, hSfilt, rfl⟩
      rw [List.mem_filter] at hSfilt
      have hSub : S.Sublist L := List.mem_sublists.mp hSfilt.1
      exact List.Sublist.sum_le_sum hSub (fun x hx => le_of_lt (h_pos x hx))
  rw [M_inc]
  change Option.getD sums.maximum 0 = L.sum
  rw [hmax]
  rw [← WithBot.some_eq_coe (L.sum)]
  rfl

/-
If L is sorted increasing and has positive elements, then M_dec(L) is the maximum element of L.
-/
theorem M_dec_sorted {L : List ℝ} (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, 0 < x) :
  M_dec L = L.maximum.getD 0 := by
  by_cases hL : L = []
  · subst L
    norm_num [M_dec, List.Sorted]
    rfl
  · have hlen : 0 < L.length := List.length_pos_iff.mpr hL
    let m := L.maximum_of_length_pos hlen
    let D : List ℝ :=
      (L.sublists.filter (fun S => Decidable.decide (S.Sorted (· > ·)))).map List.sum
    have hm_mem : m ∈ L := List.maximum_of_length_pos_mem hlen
    have hm_pos : 0 < m := h_pos m hm_mem
    have h_upper : ∀ y ∈ D, y ≤ m := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨S, hS, rfl⟩
      rcases List.mem_filter.mp hS with ⟨hSsub_mem, hSdec⟩
      have hSsub : S.Sublist L := List.mem_sublists.mp hSsub_mem
      have hSsorted : S.Sorted (fun x y => x > y) := of_decide_eq_true hSdec
      have hSlen : S.length ≤ 1 := by
        cases S with
        | nil => simp
        | cons a T =>
          cases T with
          | nil => simp
          | cons b U =>
            exfalso
            have hdec : b < a := by
              simpa using
                (List.Pairwise.rel_get_of_lt hSsorted
                  (a := ⟨0, by simp⟩) (b := ⟨1, by simp⟩)
                  (Fin.mk_lt_mk.mpr Nat.zero_lt_one))
            have hinc : a < b := by
              have hSinc := h_sorted.sublist hSsub
              simpa using
                (List.Pairwise.rel_get_of_lt hSinc
                  (a := ⟨0, by simp⟩) (b := ⟨1, by simp⟩)
                  (Fin.mk_lt_mk.mpr Nat.zero_lt_one))
            exact (lt_asymm hinc hdec).elim
      cases S with
      | nil =>
        simp [le_of_lt hm_pos]
      | cons a T =>
        cases T with
        | nil =>
          have ha_mem : a ∈ L := hSsub.subset (by simp)
          have hle : a ≤ L.maximum_of_length_pos hlen :=
            List.le_maximum_of_length_pos_of_mem ha_mem hlen
          simpa [m] using hle
        | cons b U =>
          simp at hSlen
    have hmD : m ∈ D := by
      apply List.mem_map.mpr
      refine ⟨[m], ?_, by simp⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_sublists.mpr (List.singleton_sublist.mpr hm_mem),
        decide_eq_true (show [m].Pairwise (fun x y => y < x) by simp)⟩
    have hDmax : D.maximum = (m : WithBot ℝ) :=
      List.maximum_eq_coe_iff.mpr ⟨hmD, h_upper⟩
    have hLmax : L.maximum = (m : WithBot ℝ) := by
      simp [m]
    simp [M_dec, D, hDmax, hLmax]

/-
es_part_blocks constructs the list of blocks for the Erdős–Szekeres pattern. Each block is a list of real numbers.
-/
def es_part_blocks (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) : List (List ℝ) :=
  (List.range num_blocks).map fun b =>
    (List.range block_size).map fun i =>
      let local_idx := (num_blocks - 1 - b) * block_size + i
      base_val + (start_idx + local_idx) * eps

/-
es_part is the flattening of es_part_blocks.
-/
theorem es_part_eq_join (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) :
  es_part num_blocks block_size base_val start_idx eps = (es_part_blocks num_blocks block_size base_val start_idx eps).flatten := by
    rfl

/-
Each block in es_part_blocks is sorted increasing.
-/
theorem es_part_blocks_sorted (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) :
  ∀ B ∈ es_part_blocks num_blocks block_size base_val start_idx eps, B.Sorted (· < ·) := by
  intro B hB
  unfold es_part_blocks at hB
  rcases List.mem_map.mp hB with ⟨b, _hb, rfl⟩
  change List.Pairwise (fun x1 x2 : ℝ => x1 < x2)
    (List.map
      (fun i =>
        let local_idx := (num_blocks - 1 - b) * block_size + i
        base_val + (start_idx + local_idx) * eps)
      (List.range block_size))
  rw [List.pairwise_map]
  refine List.Pairwise.imp ?_ (List.pairwise_lt_range)
  intro i j hij
  have hnat :
      start_idx + ((num_blocks - 1 - b) * block_size + i) <
        start_idx + ((num_blocks - 1 - b) * block_size + j) := by
    omega
  have hcast :
      ((start_idx + ((num_blocks - 1 - b) * block_size + i) : ℕ) : ℝ) <
        ((start_idx + ((num_blocks - 1 - b) * block_size + j) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hmul :
      ((start_idx + ((num_blocks - 1 - b) * block_size + i) : ℕ) : ℝ) * eps <
        ((start_idx + ((num_blocks - 1 - b) * block_size + j) : ℕ) : ℝ) * eps :=
    mul_lt_mul_of_pos_right hcast h_eps
  simpa using add_lt_add_left hmul base_val

/-
Blocks in es_part_blocks are pairwise decreasing: every element in an earlier block is greater than every element in a later block.
-/
theorem es_part_blocks_decreasing (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) :
  ∀ i j, i < j → j < num_blocks →
    let B := es_part_blocks num_blocks block_size base_val start_idx eps
    ∀ x ∈ B[i]!, ∀ y ∈ B[j]!, x > y := by
      unfold es_part_blocks; aesop;
      rw [ List.getElem?_range ] at a_2
      focus aesop
      · norm_cast;
        nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ num_blocks ), Nat.sub_add_cancel ( by omega : j ≤ num_blocks - 1 ), Nat.sub_add_cancel ( by omega : i ≤ num_blocks - 1 ) ];
      · linarith

/-
If L is a list of lists such that blocks are pairwise decreasing, then M_inc(L.flatten) is the maximum of M_inc of the blocks.
-/
theorem M_inc_flatten_of_pairwise_decreasing (L : List (List ℝ))
  (h_dec : ∀ i j, i < j → j < L.length → ∀ x ∈ L[i]!, ∀ y ∈ L[j]!, x > y) :
  M_inc L.flatten = (L.map M_inc).maximum.getD 0 := by
  have M_inc_nonneg : ∀ A : List ℝ, 0 ≤ M_inc A := by
    intro A
    unfold M_inc
    let xs :=
      (A.sublists.filter (fun S => Decidable.decide (S.Sorted (· < ·)))).map List.sum
    change 0 ≤ xs.maximum.getD 0
    have h0 : (0 : ℝ) ∈ xs := by
      dsimp [xs]
      exact List.mem_map.mpr
        ⟨[], List.mem_filter.mpr
          ⟨List.mem_sublists.mpr (List.nil_sublist A), by simp [List.Sorted]⟩, rfl⟩
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hmax : xs.maximum with
    | bot =>
        rw [hmax] at h0le
        simp at h0le
    | coe m =>
        rw [hmax] at h0le
        have hm : 0 ≤ m := by
          simpa using h0le
        change 0 ≤ Option.getD (↑m : WithBot ℝ) 0
        simpa using hm
  have maximum_getD_cons :
      ∀ (a : ℝ) (l : List ℝ), 0 ≤ a →
        ((a :: l).maximum).getD 0 = max a (l.maximum.getD 0) := by
    intro a l ha
    rw [List.maximum_cons]
    cases h : l.maximum with
    | bot =>
        have hmax : max (↑a : WithBot ℝ) ⊥ = ↑a := max_eq_left bot_le
        rw [hmax]
        have hbot : Option.getD (⊥ : WithBot ℝ) 0 = (0 : ℝ) := rfl
        have ha' : Option.getD (↑a : WithBot ℝ) 0 = a := rfl
        rw [hbot, ha', max_eq_left ha]
    | coe b =>
        have hb' : Option.getD (↑b : WithBot ℝ) 0 = b := rfl
        by_cases hab : a ≤ b
        · have hmax : max (↑a : WithBot ℝ) (↑b : WithBot ℝ) = ↑b :=
            max_eq_right (by simpa using hab)
          rw [hmax, hb', max_eq_right hab]
        · have hba : b ≤ a := le_of_not_ge hab
          have hmax : max (↑a : WithBot ℝ) (↑b : WithBot ℝ) = ↑a :=
            max_eq_left (by simpa using hba)
          have ha' : Option.getD (↑a : WithBot ℝ) 0 = a := rfl
          rw [hmax, hb', ha', max_eq_left hba]
  induction L with
  | nil =>
      unfold M_inc
      norm_num [List.Sorted]
      rfl
  | cons A T ih =>
      have h_tail :
          ∀ i j, i < j → j < T.length → ∀ x ∈ T[i]!, ∀ y ∈ T[j]!, x > y := by
        intro i j hij hj x hx y hy
        exact h_dec (i + 1) (j + 1) (Nat.succ_lt_succ hij)
          (by simpa using Nat.succ_lt_succ hj) x
          (by
            rw [getElem!_pos (c := A :: T) (i := i + 1)
              (h := Nat.succ_lt_succ (lt_trans hij hj))]
            rw [List.getElem_cons_succ A T i
              (Nat.succ_lt_succ (lt_trans hij hj))]
            rw [← getElem!_pos (c := T) (i := i) (h := lt_trans hij hj)]
            exact hx)
          y
          (by
            rw [getElem!_pos (c := A :: T) (i := j + 1)
              (h := Nat.succ_lt_succ hj)]
            rw [List.getElem_cons_succ A T j (Nat.succ_lt_succ hj)]
            rw [← getElem!_pos (c := T) (i := j) (h := hj)]
            exact hy)
      have h_cross : ∀ a ∈ A, ∀ b ∈ T.flatten, a > b := by
        intro a ha b hb
        rcases List.mem_flatten.mp hb with ⟨B, hB, hbB⟩
        rcases List.mem_iff_get.mp hB with ⟨n, hn⟩
        exact h_dec 0 (n.val + 1) (Nat.succ_pos n.val)
          (by simp) a
          (by
            rw [getElem!_pos (c := A :: T) (i := 0) (h := by simp)]
            simpa using ha)
          b
          (by
            rw [getElem!_pos (c := A :: T) (i := n.val + 1)
              (h := Nat.succ_lt_succ n.isLt)]
            rw [List.getElem_cons_succ A T n.val (Nat.succ_lt_succ n.isLt)]
            rw [← List.get_eq_getElem]
            rw [hn]
            exact hbB)
      rw [List.flatten_cons]
      rw [M_inc_append_of_gt h_cross]
      rw [ih h_tail]
      exact (maximum_getD_cons (M_inc A) (T.map M_inc) (M_inc_nonneg A)).symm

/-
If L is a list of lists such that blocks are pairwise decreasing, then M_dec(L.flatten) is the sum of M_dec of the blocks.
-/
theorem M_dec_flatten_of_pairwise_decreasing (L : List (List ℝ))
  (h_dec : ∀ i j, i < j → j < L.length → ∀ x ∈ L[i]!, ∀ y ∈ L[j]!, x > y) :
  M_dec L.flatten = (L.map M_dec).sum := by
  induction L with
  | nil =>
      unfold M_dec
      norm_num [List.Sorted]
      rfl
  | cons A T ih =>
      have h_tail :
          ∀ i j, i < j → j < T.length → ∀ x ∈ T[i]!, ∀ y ∈ T[j]!, x > y := by
        intro i j hij hj x hx y hy
        exact h_dec (i + 1) (j + 1) (Nat.succ_lt_succ hij)
          (by simpa using Nat.succ_lt_succ hj) x
          (by
            rw [getElem!_pos (c := A :: T) (i := i + 1)
              (h := Nat.succ_lt_succ (lt_trans hij hj))]
            rw [List.getElem_cons_succ A T i
              (Nat.succ_lt_succ (lt_trans hij hj))]
            rw [← getElem!_pos (c := T) (i := i) (h := lt_trans hij hj)]
            exact hx)
          y
          (by
            rw [getElem!_pos (c := A :: T) (i := j + 1)
              (h := Nat.succ_lt_succ hj)]
            rw [List.getElem_cons_succ A T j (Nat.succ_lt_succ hj)]
            rw [← getElem!_pos (c := T) (i := j) (h := hj)]
            exact hy)
      have h_cross : ∀ a ∈ A, ∀ b ∈ T.flatten, a > b := by
        intro a ha b hb
        rcases List.mem_flatten.mp hb with ⟨B, hB, hbB⟩
        rcases List.mem_iff_get.mp hB with ⟨n, hn⟩
        exact h_dec 0 (n.val + 1) (Nat.succ_pos n.val)
          (by simp) a
          (by
            rw [getElem!_pos (c := A :: T) (i := 0) (h := by simp)]
            simpa using ha)
          b
          (by
            rw [getElem!_pos (c := A :: T) (i := n.val + 1)
              (h := Nat.succ_lt_succ n.isLt)]
            rw [List.getElem_cons_succ A T n.val (Nat.succ_lt_succ n.isLt)]
            rw [← List.get_eq_getElem]
            rw [hn]
            exact hbB)
      rw [List.flatten_cons]
      rw [M_dec_append_of_gt h_cross]
      rw [ih h_tail]
      simp

/-
For any block in es_part_blocks, M_inc of the block is equal to its sum, assuming base_val > 0.
-/
theorem M_inc_of_es_part_block_eq_sum (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  ∀ B ∈ es_part_blocks num_blocks block_size base_val start_idx eps, M_inc B = B.sum := by
    -- By definition of `es_part_blocks`, each block is sorted increasing and has positive elements.
    intros B hB
    have hB_sorted : B.Sorted (· < ·) := by
      convert es_part_blocks_sorted num_blocks block_size base_val start_idx eps h_eps _ hB
    have hB_pos : ∀ x ∈ B, 0 < x := by
      unfold es_part_blocks at hB; aesop;
      positivity;
    exact M_inc_sorted hB_sorted hB_pos

/-
M_inc of es_part is the maximum of the sums of its blocks.
-/
theorem M_inc_es_part_eq_max_sum (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  M_inc (es_part num_blocks block_size base_val start_idx eps) =
  ((es_part_blocks num_blocks block_size base_val start_idx eps).map List.sum).maximum.getD 0 := by
    rw [ es_part_eq_join ];
    rw [ M_inc_flatten_of_pairwise_decreasing ];
    · rw [ List.map_congr_left ];
      exact fun a a_1 ↦ M_inc_of_es_part_block_eq_sum num_blocks block_size base_val start_idx eps h_eps h_base a a_1;
    · aesop;
      convert es_part_blocks_decreasing num_blocks block_size base_val start_idx eps h_eps i j a _ x _ y _ using 1;
      · exact lt_of_lt_of_le a_1 ( by simp +decide [ es_part_blocks ] );
      · cases h : ( es_part_blocks num_blocks block_size base_val start_idx eps)[i]? <;> aesop;
      · aesop

/-
Mapping M_inc over es_part_blocks is the same as mapping List.sum, since M_inc of each block is its sum.
-/
theorem map_M_inc_eq_map_sum (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  (es_part_blocks num_blocks block_size base_val start_idx eps).map M_inc =
  (es_part_blocks num_blocks block_size base_val start_idx eps).map List.sum := by
    -- Apply the equality of M_inc and sum to each block in the blocks list.
    have h_eq_blocks : ∀ B ∈ es_part_blocks num_blocks block_size base_val start_idx eps, M_inc B = B.sum := by
      exact fun B a ↦ M_inc_of_es_part_block_eq_sum num_blocks block_size base_val start_idx eps h_eps h_base B a;
    exact List.map_eq_map_iff.mpr h_eq_blocks

/-
M_inc of es_part is the maximum of the sums of its blocks.
-/
theorem M_inc_es_part_eq_max_sum_v2 (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  M_inc (es_part num_blocks block_size base_val start_idx eps) =
  ((es_part_blocks num_blocks block_size base_val start_idx eps).map List.sum).maximum.getD 0 := by
    exact M_inc_es_part_eq_max_sum num_blocks block_size base_val start_idx eps h_eps h_base

/-
M_dec of es_part is the sum of the maximums of its blocks.
-/
theorem M_dec_es_part_eq_sum_max (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  M_dec (es_part num_blocks block_size base_val start_idx eps) =
  ((es_part_blocks num_blocks block_size base_val start_idx eps).map (fun b => b.maximum.getD 0)).sum := by
    -- Apply the theorem M_dec_flatten_of_pairwise_decreasing with the hypothesis h_dec.
    have h_M_dec_flatten : M_dec (es_part num_blocks block_size base_val start_idx eps) = (List.map M_dec (es_part_blocks num_blocks block_size base_val start_idx eps)).sum := by
      convert M_dec_flatten_of_pairwise_decreasing ( es_part_blocks num_blocks block_size base_val start_idx eps ) _ using 1;
      intros i j hij hj_lt_len x hx y hy;
      convert es_part_blocks_decreasing num_blocks block_size base_val start_idx eps h_eps i j hij _ x hx y hy using 1;
      unfold es_part_blocks at hj_lt_len; aesop;
    -- For each block in `es_part_blocks`, if the block is non-empty, then `M_dec` of the block is equal to the maximum of the block. If the block is empty, then `M_dec` is zero, and the maximum is also zero.
    have h_M_dec_block : ∀ B ∈ es_part_blocks num_blocks block_size base_val start_idx eps, M_dec B = B.maximum.getD 0 := by
      intros B hB;
      apply M_dec_sorted;
      · exact es_part_blocks_sorted num_blocks block_size base_val start_idx eps h_eps B hB;
      · unfold es_part_blocks at hB; aesop;
        positivity;
    rw [ h_M_dec_flatten, List.map_congr_left h_M_dec_block ]

/-
Structure to hold sequence parameters and definitions of parts. seq_eps is equivalent to seq_of_data.
-/
structure SeqData where
  k : ℤ
  a : ℤ
  eps : ℝ
  red : ℕ := a.natAbs
  blue : ℕ := (a + 1).natAbs
  num_blocks1 : ℕ := red
  block_size1 : ℕ := k.toNat - red
  num_blocks2 : ℕ := blue
  block_size2 : ℕ := blue
  num_blocks3 : ℕ := k.toNat - red
  block_size3 : ℕ := k.toNat
  len1 : ℕ := num_blocks1 * block_size1
  len2 : ℕ := num_blocks2 * block_size2
  len3 : ℕ := num_blocks3 * block_size3
  start3 : ℕ := 0
  start2 : ℕ := len3
  start1 : ℕ := len3 + len2

def part1 (d : SeqData) : List ℝ := es_part d.num_blocks1 d.block_size1 d.blue d.start1 d.eps

def part2 (d : SeqData) : List ℝ := es_part d.num_blocks2 d.block_size2 d.red d.start2 d.eps

def part3 (d : SeqData) : List ℝ := es_part d.num_blocks3 d.block_size3 d.blue d.start3 d.eps

def seq_of_data (d : SeqData) : List ℝ := part1 d ++ part2 d ++ part3 d

theorem seq_eps_eq_seq_of_data (k : ℤ) (a : ℤ) (eps : ℝ) :
  seq_eps k a eps = seq_of_data { k := k, a := a, eps := eps } := by
                                    exact List.toList_toArray

/-
Elements in es_part are bounded by base_val + start_idx * eps and base_val + (start_idx + len - 1) * eps.
-/
theorem es_part_bounds (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_blocks : 0 < num_blocks) (h_size : 0 < block_size) :
  let L := es_part num_blocks block_size base_val start_idx eps
  let len := num_blocks * block_size
  ∀ x ∈ L, base_val + start_idx * eps ≤ x ∧ x ≤ base_val + (start_idx + len - 1) * eps := by
    unfold es_part; aesop;
    · positivity;
    · rw [ Nat.cast_sub <| Nat.le_sub_one_of_lt left ] ; rw [ Nat.cast_sub <| Nat.one_le_iff_ne_zero.mpr <| by linarith ] ; push_cast ; nlinarith [ ( by norm_cast : ( w :ℝ ) + 1 ≤ num_blocks ), ( by norm_cast : ( w_1 :ℝ ) + 1 ≤ block_size ) ]

/-
Every element in part3 is strictly less than every element in part1, for the sequence constructed from k, a, eps.
-/
theorem part3_lt_part1 (k : ℤ) (a : ℤ) (eps : ℝ) (h_eps_pos : 0 < eps) :
  let d : SeqData := { k := k, a := a, eps := eps }
  ∀ x ∈ part3 d, ∀ y ∈ part1 d, x < y := by
    unfold part1 part3 at *; aesop;
    unfold es_part at * ; aesop;
    repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat omega;
    cases abs_cases a <;> simp +decide [ * ] at *;
    · rw [ lt_tsub_iff_left ] at * ; norm_cast at * ; aesop;
      cases max_cases k 0 <;> nlinarith [ abs_of_nonneg h ];
    · rw [ lt_tsub_iff_left ] at * ; norm_cast at * ; aesop;
      cases max_cases k 0 <;> nlinarith [ abs_of_neg right ]

/-
Every element in part3 is strictly less than every element in part2, given the constraints on k and a.
-/
theorem part3_lt_part2 (k : ℤ) (a : ℤ) (eps : ℝ) (h_eps_pos : 0 < eps) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  let d : SeqData := { k := k, a := a, eps := eps }
  ∀ x ∈ part3 d, ∀ y ∈ part2 d, x < y := by
    aesop;
    -- By definition of part3 and part2, we know that their elements are constructed with different base values and start indices.
    have h_base3 : x ∈ es_part (k.toNat - Int.natAbs a) (k.toNat) (Int.natAbs (a + 1)) 0 eps := by
      exact Multiset.mem_coe.mp a_1
    have h_base2 : y ∈ es_part (Int.natAbs (a + 1)) (Int.natAbs (a + 1)) (Int.natAbs a) (k.toNat * (k.toNat - Int.natAbs a)) eps := by
      simpa only [ mul_comm ] using a_2;
    have h_base3_lt_base2 : x < (Int.natAbs a : ℝ) + (k.toNat * (k.toNat - Int.natAbs a)) * eps := by
      have h_base3_lt_base2 : x ≤ (Int.natAbs (a + 1) : ℝ) + (k.toNat * (k.toNat - Int.natAbs a) - 1) * eps := by
        have := @es_part_bounds ( k.toNat - Int.natAbs a ) k.toNat ( Int.natAbs ( a + 1 ) ) 0 eps h_eps_pos;
        by_cases h : 0 < k.toNat - a.natAbs <;> aesop;
        · convert this ( by linarith ) x h_base3 |>.2 using 1;
          rw [ Nat.cast_sub ( by cases abs_cases a <;> linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ) ] ; norm_num;
          exact Or.inl <| mul_comm _ _;
        · unfold es_part at h_base3 ; aesop;
      norm_num [ abs_of_neg ( by linarith : a < 0 ), abs_of_neg ( by linarith : a + 1 < 0 ) ] at *;
      nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ k ), ( by norm_cast : ( a : ℝ ) < -1 ) ];
    have h_base2_ge : ∀ y ∈ es_part (Int.natAbs (a + 1)) (Int.natAbs (a + 1)) (Int.natAbs a) (k.toNat * (k.toNat - Int.natAbs a)) eps, (Int.natAbs a : ℝ) + (k.toNat * (k.toNat - Int.natAbs a)) * eps ≤ y := by
      unfold es_part; aesop;
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num;
      · exact add_nonneg ( mul_nonneg ( sub_nonneg_of_le ( mod_cast Nat.le_sub_one_of_lt left ) ) ( abs_nonneg _ ) ) ( Nat.cast_nonneg _ );
      · exact Nat.le_sub_one_of_lt left;
      · cases abs_cases a <;> linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ];
    exact lt_of_lt_of_le h_base3_lt_base2 ( h_base2_ge y h_base2 )

/-
Every element in part1 is strictly less than every element in part2, given that epsilon is small enough.
-/
theorem part1_lt_part2 (k : ℤ) (a : ℤ) (eps : ℝ) (h_eps_pos : 0 < eps) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  let d : SeqData := { k := k, a := a, eps := eps }
  (d.len1 + d.len2) * eps < 1 →
  ∀ x ∈ part1 d, ∀ y ∈ part2 d, x < y := by
    unfold part1 part2;
    intros d hd x hx y hy;
    -- By definition of `es_part`, we know that `x` is in the range `[d.blue + (d.start1) * eps, d.blue + (d.start1 + d.len1 - 1) * eps]` and `y` is in the range `[d.red + (d.start2) * eps, d.red + (d.start2 + d.len2 - 1) * eps]`.
    have hx_range : d.blue + (d.start1) * eps ≤ x ∧ x ≤ d.blue + (d.start1 + d.len1 - 1) * eps := by
      apply es_part_bounds;
      · exact RCLike.ofReal_pos.mp h_eps_pos;
      · omega;
      · contrapose! hd; aesop;
        unfold es_part at hx hy; aesop;
      · exact hx
    have hy_range : d.red + (d.start2) * eps ≤ y ∧ y ≤ d.red + (d.start2 + d.len2 - 1) * eps := by
      apply es_part_bounds;
      · exact RCLike.ofReal_pos.mp h_eps_pos;
      · omega;
      · omega;
      · exact hy;
    aesop;
    cases abs_cases ( a + 1 : ℝ ) <;> cases abs_cases ( a : ℝ ) <;> push_cast [ * ] at * <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ), ( by norm_cast : ( -k :ℝ ) ≤ a ), ( by norm_cast : ( a :ℝ ) < -1 ) ]

/-
M_inc of the full sequence decomposes into max(M_inc(part1) + M_inc(part2), M_inc(part3)).
-/
theorem M_inc_seq_decomposition (d : SeqData)
  (h12 : ∀ x ∈ part1 d, ∀ y ∈ part2 d, x < y)
  (h31 : ∀ x ∈ part3 d, ∀ y ∈ part1 d, x < y)
  (h32 : ∀ x ∈ part3 d, ∀ y ∈ part2 d, x < y) :
  M_inc (seq_of_data d) = max (M_inc (part1 d) + M_inc (part2 d)) (M_inc (part3 d)) := by
    unfold seq_of_data;
    -- Apply the lemma about maximum sums of concatenated lists.
    have hM_inc_append : M_inc (part1 d ++ part2 d) = M_inc (part1 d) + M_inc (part2 d) := by
      exact M_inc_append_of_lt h12;
    rw [ ← hM_inc_append, M_inc_append_of_gt ];
    grind

/-
M_dec of the full sequence decomposes into max(M_dec(part1), M_dec(part2)) + M_dec(part3).
-/
theorem M_dec_seq_decomposition (d : SeqData)
  (h12 : ∀ x ∈ part1 d, ∀ y ∈ part2 d, x < y)
  (h31 : ∀ x ∈ part3 d, ∀ y ∈ part1 d, x < y)
  (h32 : ∀ x ∈ part3 d, ∀ y ∈ part2 d, x < y) :
  M_dec (seq_of_data d) = max (M_dec (part1 d)) (M_dec (part2 d)) + M_dec (part3 d) := by
    -- Apply the lemmas about M_dec of concatenated lists.
    have h1 : M_dec (part1 d ++ part2 d) = max (M_dec (part1 d)) (M_dec (part2 d)) := by
      apply M_dec_append_of_lt; assumption
    have h2 : M_dec ((part1 d ++ part2 d) ++ part3 d) = M_dec (part1 d ++ part2 d) + M_dec (part3 d) := by
      apply_rules [ M_dec_append_of_gt ];
      grind +ring;
    exact h1 ▸ h2

/-
The sum of es_part is given by the formula involving base_val, start_idx, and eps.
-/
theorem sum_es_part_eq (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) :
  (es_part num_blocks block_size base_val start_idx eps).sum =
  (num_blocks * block_size : ℝ) * base_val +
  eps * ((num_blocks * block_size : ℝ) * start_idx + (num_blocks * block_size) * (num_blocks * block_size - 1) / 2) := by
    unfold es_part;
    norm_num [ List.flatMap ];
    -- Let's simplify the expression for the sum of the elements in each block.
    have h_block_sum : ∀ b < num_blocks, List.sum (List.map (fun i : ℕ => base_val + ((start_idx : ℝ) + ((num_blocks - 1 - b) * block_size + i)) * eps) (List.range block_size)) = block_size * base_val + eps * (block_size * start_idx + (num_blocks - 1 - b) * block_size^2 + block_size * (block_size - 1) / 2) := by
      intro b hb
      induction block_size with
      | zero =>
        simp_all +decide
      | succ block_size ih =>
        simp_all +decide [ List.range_succ ] ; ring_nf
        norm_num [ List.sum_map_add, List.sum_range_succ' ] at * ; ring_nf at * ; aesop
        linarith
    convert Finset.sum_congr rfl fun b hb => h_block_sum b ( Finset.mem_range.mp hb ) using 1;
    · refine congr_arg ?_ ( List.ext_get ?_ ?_ ) <;> aesop;
      convert h_block_sum n h₁ using 3 ; rw [ Nat.cast_sub <| Nat.le_sub_one_of_lt h₁ ] ; rw [ Nat.cast_sub <| by linarith ] ; push_cast ; ring;
    · norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
      norm_num [ ← Finset.sum_mul _ _ _ ] ; ring_nf;
      exact Nat.recOn num_blocks ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith;

/-
Formula for M_inc of an es_part.
-/
theorem M_inc_es_part_value (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ)
  (h_eps : 0 < eps) (h_base : 0 < base_val) (h_blocks : 0 < num_blocks) (h_size : 0 < block_size) :
  M_inc (es_part num_blocks block_size base_val start_idx eps) =
  (block_size : ℝ) * base_val +
  eps * (block_size * start_idx + block_size * ((num_blocks - 1) * block_size) + (block_size * (block_size - 1)) / 2) := by
  let target : ℝ :=
    (block_size : ℝ) * base_val +
      eps * (block_size * start_idx + block_size * ((num_blocks - 1) * block_size) +
        (block_size * (block_size - 1)) / 2)
  let blocks := es_part_blocks num_blocks block_size base_val start_idx eps
  let xs := blocks.map List.sum
  have h_block_sum :
      ∀ b < num_blocks,
        (List.map
            (fun i : ℕ =>
              base_val +
                ((start_idx : ℝ) + (((num_blocks - 1 - b) * block_size + i : ℕ) : ℝ)) *
                  eps)
            (List.range block_size)).sum =
          (block_size : ℝ) * base_val +
            eps * (block_size * start_idx +
              block_size * ((num_blocks - 1 - b) * block_size) +
              block_size * (block_size - 1) / 2) := by
    intro b hb
    norm_num [List.sum_map_add, List.sum_map_mul_right]
    rw [show (List.map Nat.cast (List.range block_size)).sum =
        (block_size : ℝ) * (block_size - 1) / 2 from
      Nat.recOn block_size (by norm_num) fun n ih => by
        norm_num [List.range_succ] at *
        linarith]
    rw [Nat.cast_sub (Nat.le_sub_one_of_lt hb)]
    rw [Nat.cast_sub (by omega : 1 ≤ num_blocks)]
    push_cast
    ring
  have h_first :
      (List.map
          (fun i : ℕ =>
            base_val +
              ((start_idx : ℝ) + (((num_blocks - 1 - 0) * block_size + i : ℕ) : ℝ)) *
                eps)
          (List.range block_size)).sum = target := by
    dsimp [target]
    simpa [Nat.sub_zero] using h_block_sum 0 h_blocks
  have h_max : xs.maximum = (target : WithBot ℝ) := by
    rw [List.maximum_eq_coe_iff]
    constructor
    · dsimp [xs, blocks, es_part_blocks]
      simp only [List.map_map, Function.comp_apply, List.mem_map, List.mem_range]
      exact ⟨0, h_blocks, h_first⟩
    · intro a ha
      dsimp [xs, blocks, es_part_blocks] at ha
      simp only [List.map_map, Function.comp_apply, List.mem_map, List.mem_range] at ha
      rcases ha with ⟨b, hb, rfl⟩
      rw [h_block_sum b hb]
      dsimp [target]
      have hblock_nonneg : (0 : ℝ) ≤ (block_size : ℝ) := by positivity
      have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := by positivity
      have hinner :
          ((num_blocks : ℝ) - 1 - b) * (block_size : ℝ) ≤
            ((num_blocks : ℝ) - 1) * (block_size : ℝ) := by
        nlinarith
      have hprod' :
          (block_size : ℝ) * (((num_blocks : ℝ) - 1 - b) * (block_size : ℝ)) ≤
            (block_size : ℝ) * (((num_blocks : ℝ) - 1) * (block_size : ℝ)) := by
        nlinarith [hinner, hblock_nonneg]
      nlinarith [h_eps, hprod']
  rw [M_inc_es_part_eq_max_sum_v2 num_blocks block_size base_val start_idx eps h_eps h_base]
  change xs.maximum.getD 0 = target
  rw [h_max]
  rfl

/-
Formula for M_dec of an es_part.
-/
theorem M_dec_es_part_value (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ)
  (h_eps : 0 < eps) (h_base : 0 < base_val) (h_blocks : 0 < num_blocks) (h_size : 0 < block_size) :
  M_dec (es_part num_blocks block_size base_val start_idx eps) =
  (num_blocks : ℝ) * base_val +
  eps * (num_blocks * start_idx + block_size * (num_blocks * (num_blocks - 1) / 2) + num_blocks * (block_size - 1)) := by
  have h_block_max :
      ∀ b ∈ List.range num_blocks,
        ((List.range block_size).map (fun i : ℕ =>
          base_val + (↑start_idx + ↑((num_blocks - 1 - b) * block_size + i)) * eps)).maximum.getD 0 =
          base_val + ((start_idx : ℝ) +
            (((num_blocks : ℝ) - 1 - b) * block_size + ((block_size : ℝ) - 1))) * eps := by
    intro b hbmem
    have hb : b < num_blocks := List.mem_range.mp hbmem
    let f : ℕ → ℝ := fun i =>
      base_val + (↑start_idx + ↑((num_blocks - 1 - b) * block_size + i)) * eps
    have hlast_mem : f (block_size - 1) ∈ (List.range block_size).map f := by
      exact List.mem_map.mpr
        ⟨block_size - 1, List.mem_range.mpr (Nat.sub_lt h_size zero_lt_one), rfl⟩
    have hle : ∀ a ∈ (List.range block_size).map f, a ≤ f (block_size - 1) := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
      have hi_le : i ≤ block_size - 1 := Nat.le_sub_one_of_lt (List.mem_range.mp hi)
      have hidx_le :
          (((num_blocks - 1 - b) * block_size + i : ℕ) : ℝ) ≤
            ((num_blocks - 1 - b) * block_size + (block_size - 1) : ℕ) := by
        exact_mod_cast Nat.add_le_add_left hi_le ((num_blocks - 1 - b) * block_size)
      dsimp [f]
      nlinarith [h_eps, hidx_le]
    have hmax : ((List.range block_size).map f).maximum = (f (block_size - 1) : WithBot ℝ) := by
      rw [List.maximum_eq_coe_iff]
      exact ⟨hlast_mem, hle⟩
    have hget : ((List.range block_size).map f).maximum.getD 0 = f (block_size - 1) := by
      rw [hmax]
      rfl
    rw [show
      ((List.range block_size).map (fun i : ℕ =>
        base_val + (↑start_idx + ↑((num_blocks - 1 - b) * block_size + i)) * eps)).maximum.getD 0 =
        ((List.range block_size).map f).maximum.getD 0 by rfl]
    rw [hget]
    dsimp [f]
    have hb1 : 1 ≤ num_blocks := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le b) hb)
    have hbsub : b ≤ num_blocks - 1 := Nat.le_sub_one_of_lt hb
    have hbs1 : 1 ≤ block_size := Nat.succ_le_of_lt h_size
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbs1, Nat.cast_sub hbsub,
      Nat.cast_sub hb1]
  have h_list_sum :
      ∀ n (f : ℕ → ℝ), (List.map f (List.range n)).sum = ∑ b ∈ Finset.range n, f b := by
    intro n f
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
        simp
  have hsum_id : (∑ b ∈ Finset.range num_blocks, (b : ℝ)) =
      (num_blocks : ℝ) * ((num_blocks : ℝ) - 1) / 2 := by
    have h2 : (∑ b ∈ Finset.range num_blocks, (b : ℝ)) * 2 =
        (num_blocks : ℝ) * ((num_blocks : ℝ) - 1) := by
      cases num_blocks with
      | zero => simp
      | succ n =>
          have hnat := Finset.sum_range_id_mul_two (n + 1)
          rw [← Nat.cast_sum]
          change ((↑(∑ x ∈ Finset.range (n + 1), x) : ℝ) * (↑(2 : ℕ) : ℝ) =
            (↑(n + 1) : ℝ) * ((↑(n + 1) : ℝ) - 1))
          rw [← Nat.cast_mul, hnat]
          norm_num
    nlinarith
  have hsum_sub : (∑ b ∈ Finset.range num_blocks, ((num_blocks : ℝ) - 1 - b)) =
      (num_blocks : ℝ) * ((num_blocks : ℝ) - 1) / 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul]
    rw [hsum_id]
    ring
  rw [M_dec_es_part_eq_sum_max num_blocks block_size base_val start_idx eps h_eps h_base]
  unfold es_part_blocks
  simp only [List.map_map]
  change (List.map (fun b =>
    ((List.range block_size).map (fun i : ℕ =>
      base_val + (↑start_idx + ↑((num_blocks - 1 - b) * block_size + i)) * eps)).maximum.getD 0)
    (List.range num_blocks)).sum =
      (num_blocks : ℝ) * base_val +
        eps * (num_blocks * start_idx + block_size * (num_blocks * (num_blocks - 1) / 2) +
          num_blocks * (block_size - 1))
  rw [List.map_congr_left h_block_max]
  rw [h_list_sum]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.sum_mul, hsum_sub]
  ring

/-
The limit values of M_inc, M_dec, and sum match the algebraic derivation.
-/
def limit_M_inc (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let block_size1 := k.toNat - red
  let block_size2 := blue
  let block_size3 := k.toNat
  let base_val1 := blue
  let base_val2 := red
  let base_val3 := blue
  max ((block_size1 : ℝ) * base_val1 + (block_size2 : ℝ) * base_val2) ((block_size3 : ℝ) * base_val3)

def limit_M_dec (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let num_blocks1 := red
  let num_blocks2 := blue
  let num_blocks3 := k.toNat - red
  let base_val1 := blue
  let base_val2 := red
  let base_val3 := blue
  max ((num_blocks1 : ℝ) * base_val1) ((num_blocks2 : ℝ) * base_val2) + (num_blocks3 : ℝ) * base_val3

def limit_sum (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let len1 := red * (k.toNat - red)
  let len2 := blue * blue
  let len3 := (k.toNat - red) * k.toNat
  (len1 : ℝ) * blue + (len2 : ℝ) * red + (len3 : ℝ) * blue

theorem limit_values_eq (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  limit_M_inc k a = k * (a + 1).natAbs ∧
  limit_M_dec k a = k * (a + 1).natAbs ∧
  limit_sum k a = (a + 1).natAbs * (k * k + a) := by
    unfold limit_M_inc limit_M_dec limit_sum;
    refine ⟨ ?_, ?_, ?_ ⟩;
    · norm_num +zetaDelta at *;
      rw [ max_eq_right ] <;> norm_cast;
      · rw [ Int.toNat_of_nonneg ( by linarith ) ];
      · cases abs_cases ( a + 1 ) <;> cases abs_cases a <;> nlinarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ), Nat.sub_add_cancel ( show a.natAbs ≤ k.toNat from by omega ) ];
    · cases abs_cases ( a + 1 : ℝ ) <;> cases abs_cases ( a : ℝ ) <;> simp +decide [ * ] <;> ring_nf;
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · rw [ Nat.cast_sub ] <;> norm_cast;
        · rw [ Int.subNatNat_eq_coe ] ; norm_num ; ring_nf;
          rw [ max_eq_left ] <;> cases abs_cases a <;> nlinarith;
        · grind;
    · simp +zetaDelta at *;
      rw [ Nat.cast_sub ] <;> norm_num;
      · rw [ abs_of_nonpos, abs_of_nonpos ] <;> norm_cast <;> try linarith;
        rw [ Int.toNat_of_nonneg ( by linarith ) ] ; ring;
      · cases abs_cases a <;> linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ]

/-
The sum of the sequence converges to limit_sum as epsilon goes to 0.
-/
noncomputable def target_c (k : ℤ) (a : ℤ) : ℝ := (k : ℝ) / ((k : ℝ)^2 + (a : ℝ))

theorem limit_sum_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => (seq_eps k a eps).sum) (nhds 0) (nhds (limit_sum k a)) := by
    -- The sum of the sequence is a linear function of `eps`, so it is continuous.
    have h_cont : Continuous (fun eps => (seq_eps k a eps).sum) := by
      simp +zetaDelta at *;
      have h_cont : ∀ (L : List ℝ), Continuous (fun eps : ℝ => (List.map (fun x => x * eps) L).sum) := by
        fun_prop;
      unfold seq_eps;
      unfold es_part;
      simp +decide [ List.flatMap ];
      fun_prop;
    convert h_cont.tendsto 0 using 1 ; norm_num [ limit_sum ];
    rw [ seq_eps_eq_seq_of_data ] ; ring_nf;
    unfold seq_of_data; norm_num [ part1, part2, part3, sum_es_part_eq ] ; ring;

/-
For small positive epsilon, M_inc decomposes.
-/
theorem M_inc_seq_eventually_eq_right (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Eventually (fun eps => M_inc (seq_eps k a eps) =
    max (M_inc (part1 { k := k, a := a, eps := eps }) + M_inc (part2 { k := k, a := a, eps := eps }))
        (M_inc (part3 { k := k, a := a, eps := eps }))) (nhdsWithin 0 (Set.Ioi 0)) := by
                          -- By combining the results from h31, h32, and h12, we can conclude the proof.
                          have h_combined : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part1 { k := k, a := a, eps := eps }, x < y) ∧ (∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y) ∧ (∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y) := by
                                                                                                                                                                                                                                                                                                                                                have h_combined : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part1 { k := k, a := a, eps := eps }, x < y) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  filter_upwards [ self_mem_nhdsWithin ] with eps heps using part3_lt_part1 k a eps heps;
                                                                                                                                                                                                                                                                                                                                                have h_combined : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => part3_lt_part2 k a x hx h_k h_a_le h_a_lt;
                                                                                                                                                                                                                                                                                                                                                have h_combined : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (let d : SeqData := { k := k, a := a, eps := eps };
                                                                                                                                                                                                                                                                                                                                                  (d.len1 + d.len2) * eps < 1) := by
                                                                                                                                                                                                                                                                                                                                                    have h_combined : Filter.Tendsto (fun eps : ℝ => (let d : SeqData := { k := k, a := a, eps := eps };
                                                                                                                                                                                                                                                                                                                                                      (d.len1 + d.len2) * eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
                                                                                                                                                                                                                                                                                                                                                        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
                                                                                                                                                                                                                                                                                                                                                    exact h_combined.eventually ( gt_mem_nhds zero_lt_one );
                                                                                                                                                                                                                                                                                                                                                filter_upwards [ ‹∀ᶠ ( eps : ℝ ) in nhdsWithin 0 ( Set.Ioi 0 ), ∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part1 { k := k, a := a, eps := eps }, x < y›, ‹∀ᶠ ( eps : ℝ ) in nhdsWithin 0 ( Set.Ioi 0 ), ∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y›, h_combined, self_mem_nhdsWithin ] with eps h1 h2 h3 h4 using ⟨ h1, h2, fun x hx y hy => part1_lt_part2 k a eps h4 h_k h_a_le h_a_lt h3 x hx y hy ⟩;
                          filter_upwards [ h_combined ] with eps h_eps using by rw [ seq_eps_eq_seq_of_data ] ; exact M_inc_seq_decomposition _ h_eps.2.2 h_eps.1 h_eps.2.1;

/-
Limit of M_inc of es_part as epsilon goes to 0 from above.
-/
theorem limit_M_inc_es_part (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ)
  (h_base : 0 < base_val) (h_blocks : 0 < num_blocks) :
  Filter.Tendsto (fun eps => M_inc (es_part num_blocks block_size base_val start_idx eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((block_size : ℝ) * base_val)) := by
    by_cases h : block_size = 0;
    · subst block_size
      have h_es : ∀ eps, es_part num_blocks 0 base_val start_idx eps = [] := by
        intro eps
        unfold es_part
        induction (List.range num_blocks) with
        | nil => simp
        | cons b bs ih => simp
      have h_M_nil : M_inc ([] : List ℝ) = 0 := by
        simpa using (M_inc_sorted (L := ([] : List ℝ)) (List.Pairwise.nil) (by simp))
      simp [h_es, h_M_nil]
    · have h_cont : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), M_inc (es_part num_blocks block_size base_val start_idx eps) = (block_size : ℝ) * base_val + eps * (block_size * start_idx + block_size * ((num_blocks - 1) * block_size) + (block_size * (block_size - 1)) / 2) := by
        filter_upwards [ self_mem_nhdsWithin ] with eps h_eps using M_inc_es_part_value num_blocks block_size base_val start_idx eps h_eps.out h_base h_blocks ( Nat.pos_of_ne_zero h );
      rw [ Filter.tendsto_congr' h_cont ] ; exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by aesop ) ;

/-
The combination of part limits equals the total limit.
-/
def limit_part1 (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let block_size1 := k.toNat - red
  if block_size1 > 0 then (block_size1 : ℝ) * blue else 0

def limit_part2 (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  (blue : ℝ) * red

def limit_part3 (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let num_blocks3 := k.toNat - red
  if num_blocks3 > 0 then (k.toNat : ℝ) * blue else 0

theorem limit_parts_eq_limit_M_inc (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  max (limit_part1 k a + limit_part2 k a) (limit_part3 k a) = limit_M_inc k a := by
    unfold limit_part1 limit_part2 limit_part3 limit_M_inc; aesop;
    rw [ max_eq_left ( by positivity ) ];
    rw [ max_eq_left ];
    rw [ mul_comm ] ; gcongr ; norm_cast;
    cases max_cases k 0 <;> cases abs_cases a <;> linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ]

/-
Limit of M_inc of part1.
-/
theorem limit_M_inc_part1_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_inc (part1 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_part1 k a)) := by
                                              unfold part1;
                                              field_simp;
                                              convert limit_M_inc_es_part _ _ _ _ _ _ using 1;
                                              · unfold limit_part1; aesop;
                                              · exact Nat.cast_pos.mpr ( Int.natAbs_pos.mpr ( by linarith ) );
                                              · omega

/-
Limit of M_inc of part2.
-/
theorem limit_M_inc_part2_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_inc (part2 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_part2 k a)) := by
  convert limit_M_inc_es_part _ _ _ _ _ _ using 1
  · congr! 1
  · exact_mod_cast (Int.natAbs_pos.mpr (by linarith : a ≠ 0))
  · exact Int.natAbs_pos.mpr (by linarith : a + 1 ≠ 0)

/-
Limit of M_inc of part3.
-/
theorem limit_M_inc_part3_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_inc (part3 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_part3 k a)) := by
                                              by_cases h : 0 < k.toNat - a.natAbs;
                                              · have h_limit_M_inc_part3 : Filter.Tendsto (fun eps => M_inc (es_part (k.toNat - a.natAbs) k.toNat (a + 1).natAbs 0 eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((k.toNat : ℝ) * (a + 1).natAbs)) := by
                                                  convert limit_M_inc_es_part ( k.toNat - a.natAbs ) k.toNat ( a + 1 |> Int.natAbs : ℝ ) 0 _ _ using 1 <;> aesop;
                                                  norm_cast at a_1 ; omega;
                                                convert h_limit_M_inc_part3 using 1;
                                                unfold limit_part3; aesop;
                                              · have hzero : k.toNat - a.natAbs = 0 := Nat.eq_zero_of_not_pos h
                                                have hMnil : M_inc ([] : List ℝ) = 0 := by
                                                  simpa using (M_inc_sorted (L := ([] : List ℝ)) (List.Pairwise.nil) (by simp))
                                                have h_part3_nil :
                                                    ∀ eps, part3 { k := k, a := a, eps := eps } = ([] : List ℝ) := by
                                                  intro eps
                                                  unfold part3 es_part
                                                  simp [hzero]
                                                have h_fun :
                                                    (fun eps => M_inc (part3 { k := k, a := a, eps := eps })) =
                                                      (fun _ => (0 : ℝ)) := by
                                                  funext eps
                                                  simp [h_part3_nil eps, hMnil]
                                                have h_lim : limit_part3 k a = 0 := by
                                                  unfold limit_part3
                                                  simp [h]
                                                rw [h_fun, h_lim]
                                                exact tendsto_const_nhds

/-
M_inc of the sequence converges to limit_M_inc as epsilon goes to 0 from above.
-/
theorem limit_M_inc_correct_right (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_inc (seq_eps k a eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_M_inc k a)) := by
    -- By the properties of limits, if the limits of the parts exist, then the limit of their combination also exists.
    have h_limit_comb : Filter.Tendsto (fun eps => max (M_inc (part1 { k := k, a := a, eps := eps }) + M_inc (part2 { k := k, a := a, eps := eps })) (M_inc (part3 { k := k, a := a, eps := eps }))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (limit_part1 k a + limit_part2 k a) (limit_part3 k a))) := by
                                                                                                                                                                      exact Filter.Tendsto.max ( Filter.Tendsto.add ( limit_M_inc_part1_correct k a h_k h_a_le h_a_lt ) ( limit_M_inc_part2_correct k a h_k h_a_le h_a_lt ) ) ( limit_M_inc_part3_correct k a h_k h_a_le h_a_lt );
    refine Filter.Tendsto.congr' ?_ ( h_limit_comb.trans ?_ );
    · filter_upwards [ M_inc_seq_eventually_eq_right k a h_k h_a_le h_a_lt ] with eps h_eps using h_eps.symm;
    · rw [ limit_parts_eq_limit_M_inc k a h_k h_a_le h_a_lt ]

/-
For small positive epsilon, M_dec decomposes.
-/
theorem M_dec_seq_eventually_eq_right (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Eventually (fun eps => M_dec (seq_eps k a eps) =
    max (M_dec (part1 { k := k, a := a, eps := eps })) (M_dec (part2 { k := k, a := a, eps := eps })) +
    M_dec (part3 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) := by
                    -- Apply the decomposition of M_dec.
                    have h_decomp : ∀ᶠ (eps : ℝ) in nhdsWithin 0 (Set.Ioi 0), M_dec (seq_eps k a eps) = max (M_dec (part1 { k := k, a := a, eps := eps })) (M_dec (part2 { k := k, a := a, eps := eps })) + M_dec (part3 { k := k, a := a, eps := eps }) := by
                      have h_parts : ∀ᶠ (eps : ℝ) in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part1 { k := k, a := a, eps := eps }, x < y := by
                                                                                                                                          filter_upwards [ self_mem_nhdsWithin ] with eps hε using part3_lt_part1 k a eps hε.out
                      have h_parts2 : ∀ᶠ (eps : ℝ) in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part3 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y := by
                                                                                                                                            exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => part3_lt_part2 k a x hx h_k h_a_le h_a_lt
                      have h_parts3 : ∀ᶠ (eps : ℝ) in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y := by
                                                                                                                                            have h_parts3 : ∀ᶠ (eps : ℝ) in nhdsWithin 0 (Set.Ioi 0), ( (let d : SeqData := { k := k, a := a, eps := eps }
                                                                                                                                              (d.len1 + d.len2) * eps < 1)) := by
                                                                                                                                                have h_eps_small : Filter.Tendsto (fun eps : ℝ => ( (let d : SeqData := { k := k, a := a, eps := eps }
                                                                                                                                                    (d.len1 + d.len2)) * eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
                                                                                                                                                      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
                                                                                                                                                exact h_eps_small.eventually ( gt_mem_nhds zero_lt_one ) |> fun h => h.mono fun x hx => by simpa using hx;
                                                                                                                                            filter_upwards [ h_parts3, self_mem_nhdsWithin ] with eps h_eps h_eps' using part1_lt_part2 k a eps h_eps' h_k h_a_le h_a_lt h_eps
                      filter_upwards [ h_parts, h_parts2, h_parts3 ] with eps h1 h2 h3 using by rw [ seq_eps_eq_seq_of_data ] ; exact M_dec_seq_decomposition _ h3 h1 h2;
                    exact h_decomp

/-
Limit of M_dec of es_part as epsilon goes to 0 from above.
-/
theorem limit_M_dec_es_part (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ)
  (h_base : 0 < base_val) (h_blocks : 0 < num_blocks) (h_size : 0 < block_size) :
  Filter.Tendsto (fun eps => M_dec (es_part num_blocks block_size base_val start_idx eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((num_blocks : ℝ) * base_val)) := by
    -- By definition of $M_dec$, we know that it is a linear function of $\epsilon$.
    have h_M_dec_linear : ∀ eps : ℝ, 0 < eps → M_dec (es_part num_blocks block_size base_val start_idx eps) = (num_blocks : ℝ) * base_val + eps * ((num_blocks : ℝ) * start_idx + block_size * (num_blocks * (num_blocks - 1) / 2) + num_blocks * (block_size - 1)) := by
      exact fun eps a ↦ M_dec_es_part_value num_blocks block_size base_val start_idx eps a h_base h_blocks h_size;
    exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_M_dec_linear x hx ] ) ( tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) )

/-
The combination of part limits for M_dec equals the total limit.
-/
def limit_part1_dec (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let block_size1 := k.toNat - red
  if block_size1 > 0 then (red : ℝ) * blue else 0

def limit_part2_dec (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  (blue : ℝ) * red

def limit_part3_dec (k : ℤ) (a : ℤ) : ℝ :=
  let red := a.natAbs
  let blue := (a + 1).natAbs
  let num_blocks3 := k.toNat - red
  if num_blocks3 > 0 then (num_blocks3 : ℝ) * blue else 0

theorem limit_parts_dec_eq_limit_M_dec (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  max (limit_part1_dec k a) (limit_part2_dec k a) + limit_part3_dec k a = limit_M_dec k a := by
    unfold limit_part1_dec limit_part2_dec limit_part3_dec limit_M_dec; aesop;
    norm_num [ mul_comm ];
    positivity

/-
Limit of M_dec of part1.
-/
theorem limit_M_dec_part1_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_dec (part1 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_part1_dec k a)) := by
                                              by_cases h_size : k.toNat - a.natAbs > 0 <;> simp_all +decide [ limit_part1_dec ];
                                              · unfold part1; aesop;
                                                convert limit_M_dec_es_part _ _ _ _ _ _ _ using 2;
                                                · norm_cast;
                                                  norm_num;
                                                · exact abs_pos.mpr ( by norm_cast; linarith );
                                                · omega;
                                                · exact Nat.sub_pos_of_lt ( by linarith [ abs_of_neg ( by linarith : a < 0 ), Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] );
                                              · unfold part1;
                                                unfold M_dec;
                                                unfold es_part;
                                                simp;
                                                have hflat :
                                                    List.flatMap (fun _ : ℕ => ([] : List ℝ)) (List.range a.natAbs) = ([] : List ℝ) := by
                                                  induction (List.range a.natAbs) with
                                                  | nil => rfl
                                                  | cons b bs ih => simp [List.flatMap]
                                                rw [hflat];
                                                simp [List.Sorted];
                                                rfl

/-
Limit of M_dec of part2.
-/
theorem limit_M_dec_part2_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_dec (part2 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_part2_dec k a)) := by
                                              convert limit_M_dec_es_part _ _ _ _ _ _ _ using 1;
                                              all_goals norm_cast;
                                              · omega;
                                              · omega;
                                              · cases a <;> aesop;
                                                · linarith;
                                                · cases a <;> cases n_1 <;> norm_num [ Int.negSucc_eq ] at * ; linarith

/-
Limit of M_dec of part3.
-/
theorem limit_M_dec_part3_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_dec (part3 { k := k, a := a, eps := eps })) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_part3_dec k a)) := by
                                              unfold part3 limit_part3_dec;
                                              simp +zetaDelta at *;
                                              split_ifs;
                                              · convert limit_M_dec_es_part ( k.toNat - a.natAbs ) k.toNat |↑a + 1| 0 _ _ _ using 1 <;> norm_num;
                                                · norm_cast ; linarith;
                                                · linarith;
                                                · linarith;
                                              · rename_i hnot;
                                                have h_zero : k.toNat - a.natAbs = 0 := by
                                                  rw [Nat.sub_eq_zero_iff_le];
                                                  have hk_nonneg : 0 ≤ k := by linarith;
                                                  have hcast : (k.toNat : ℤ) ≤ (a.natAbs : ℤ) := by
                                                    rw [Int.toNat_of_nonneg hk_nonneg, Int.natCast_natAbs];
                                                    exact le_of_not_gt hnot;
                                                  exact_mod_cast hcast;
                                                rw [h_zero];
                                                unfold es_part M_dec;
                                                have hfilter :
                                                    List.filter (fun S : List ℝ => Decidable.decide (S.Sorted (fun x1 x2 => x2 < x1))) [[]] = [[]] := by
                                                  simp;
                                                simp [hfilter];
                                                rfl;

/-
M_dec of the sequence converges to limit_M_dec as epsilon goes to 0 from above.
-/
theorem limit_M_dec_correct_right (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_dec (seq_eps k a eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_M_dec k a)) := by
    have := @limit_M_dec_part1_correct k a h_k h_a_le h_a_lt;
    have := @limit_M_dec_part2_correct k a h_k h_a_le h_a_lt;
    have := @limit_M_dec_part3_correct k a h_k h_a_le h_a_lt; ( have := @limit_parts_dec_eq_limit_M_dec k a h_k h_a_le h_a_lt; aesop; );
    have := M_dec_seq_eventually_eq_right k a h_k h_a_le h_a_lt;
    rw [ Filter.tendsto_congr' this ] ; exact Filter.Tendsto.add ( Filter.Tendsto.max this_1 this_2 ) this_3 |> fun h => h.trans ( by aesop ) ;

/-
The ratio M/sum converges to the target value.
-/
theorem limit_ratio_correct (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M (seq_eps k a eps) / (seq_eps k a eps).sum) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((k : ℝ) / (k^2 + a))) := by
    -- By definition of $M$, we know that $M(\text{seq\_eps } k a \text{ eps})$ converges to $\max(\text{limit\_M\_inc } k a, \text{limit\_M\_dec } k a)$.
    have h_lim_M : Filter.Tendsto (fun eps => M (seq_eps k a eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (limit_M_inc k a) (limit_M_dec k a))) := by
      convert Filter.Tendsto.max ( limit_M_inc_correct_right k a h_k h_a_le h_a_lt ) ( limit_M_dec_correct_right k a h_k h_a_le h_a_lt ) using 1;
    convert h_lim_M.div ( show Filter.Tendsto ( fun eps => ( seq_eps k a eps |> List.sum ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( limit_sum k a ) ) from ?_ ) _ using 1;
    · have := limit_values_eq k a h_k h_a_le h_a_lt; aesop;
      rw [ ← mul_div_mul_left _ _ ( by norm_cast; cases abs_cases ( a + 1 ) <;> linarith : ( |↑a + 1| : ℝ ) ≠ 0 ) ] ; ring;
    · convert limit_sum_correct k a h_k h_a_le h_a_lt |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds using 1;
    · have := limit_values_eq k a h_k h_a_le h_a_lt; aesop;
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ k ), ( by norm_cast : ( -k : ℝ ) ≤ a ), ( by norm_cast : ( a : ℝ ) < -1 ) ]

/-
The sequence is valid for small positive epsilon.
-/
theorem seq_eps_eventually_valid (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Eventually (fun eps =>
    let L := seq_eps k a eps
    L.Pairwise (· ≠ ·) ∧ ∀ x ∈ L, 0 < x) (nhdsWithin 0 (Set.Ioi 0)) := by
      -- We'll use that `seq_eps k a eps` is valid for small positive `eps` to show that the ratio converges to the target value.
      have h_valid : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (seq_eps k a eps).Pairwise (· ≠ ·) ∧ ∀ x ∈ (seq_eps k a eps), 0 < x := by
        have h_pos : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ (seq_eps k a eps), 0 < x := by
          refine Filter.eventually_of_mem self_mem_nhdsWithin fun eps h_eps => ?_;
          unfold seq_eps;
          unfold es_part; aesop;
          · exact add_pos_of_pos_of_nonneg ( abs_pos.mpr ( by linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ] ) ) ( mul_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( by nlinarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ] ) ) ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) ) h_eps.le );
          · exact add_pos_of_pos_of_nonneg ( abs_pos.mpr ( by norm_cast; linarith ) ) ( mul_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( abs_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) ) h_eps.le );
          · exact add_pos_of_pos_of_nonneg ( abs_pos.mpr ( by linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ] ) ) ( mul_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) h_eps.le )
        have h_distinct : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (seq_eps k a eps).Pairwise (· ≠ ·) := by
          -- For small positive eps, the parts of seq_eps are constructed such that their elements are distinct.
          have h_distinct_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (part1 { k := k, a := a, eps := eps }).Pairwise (· ≠ ·) ∧ (part2 { k := k, a := a, eps := eps }).Pairwise (· ≠ ·) ∧ (part3 { k := k, a := a, eps := eps }).Pairwise (· ≠ ·) := by
                                                                                                                                                                                                    have h_distinct_parts : ∀ num_blocks block_size : ℕ, ∀ base_val : ℝ, ∀ start_idx : ℕ, ∀ eps : ℝ, 0 < eps → List.Pairwise (· ≠ ·) (es_part num_blocks block_size base_val start_idx eps) := by
                                                                                                                                                                                                      unfold es_part;
                                                                                                                                                                                                      intros num_blocks block_size base_val start_idx eps h_eps_pos
                                                                                                                                                                                                      simp [List.pairwise_flatMap, List.pairwise_map];
                                                                                                                                                                                                      aesop;
                                                                                                                                                                                                      · exact List.Pairwise.imp_of_mem ( by aesop ) ( List.nodup_range );
                                                                                                                                                                                                      · rw [ List.pairwise_iff_get ] ; aesop;
                                                                                                                                                                                                        norm_cast at *;
                                                                                                                                                                                                        nlinarith [ show ( i : ℕ ) < j from _hij, Nat.sub_add_cancel ( show ( i : ℕ ) ≤ num_blocks - 1 from Nat.le_sub_one_of_lt <| by simpa using i.2 ), Nat.sub_add_cancel ( show ( j : ℕ ) ≤ num_blocks - 1 from Nat.le_sub_one_of_lt <| by simpa using j.2 ) ];
                                                                                                                                                                                                    exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => ⟨ h_distinct_parts _ _ _ _ _ hx, h_distinct_parts _ _ _ _ _ hx, h_distinct_parts _ _ _ _ _ hx ⟩;
          -- For small positive eps, the parts of seq_eps are constructed such that their elements are distinct and the parts themselves are disjoint.
          have h_disjoint_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), Disjoint (part1 { k := k, a := a, eps := eps }).toFinset (part2 { k := k, a := a, eps := eps }).toFinset ∧ Disjoint (part1 { k := k, a := a, eps := eps }).toFinset (part3 { k := k, a := a, eps := eps }).toFinset ∧ Disjoint (part2 { k := k, a := a, eps := eps }).toFinset (part3 { k := k, a := a, eps := eps }).toFinset := by
                                                                                                                                                                                                                                                                                                                                                                have h_disjoint_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x ≠ y := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        have h_disjoint_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x < y := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                have h_disjoint_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (let d : SeqData := { k := k, a := a, eps := eps }; (d.len1 + d.len2) * eps < 1) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    rw [ eventually_nhdsWithin_iff ];
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    rw [ Metric.eventually_nhds_iff ];
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    simp +zetaDelta at *;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    exact ⟨ 1 / ( |↑a| * ↑( k.toNat - a.natAbs ) + ( ↑a + 1 ) * ( ↑a + 1 ) + 1 ), by exact one_div_pos.mpr ( by nlinarith [ abs_nonneg ( a : ℝ ), show ( k.toNat : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( by aesop ) ] ), fun y hy₁ hy₂ => by rw [ abs_of_pos hy₂ ] at *; rw [ lt_div_iff₀ ] at * <;> nlinarith [ abs_nonneg ( a : ℝ ), show ( k.toNat : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( by aesop ) ] ⟩;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                filter_upwards [ h_disjoint_parts, self_mem_nhdsWithin ] with eps h_eps h_eps' using part1_lt_part2 k a eps h_eps' h_k h_a_le h_a_lt h_eps;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        filter_upwards [ h_disjoint_parts ] with eps h_eps x hx y hy using ne_of_lt ( h_eps x hx y hy );
                                                                                                                                                                                                                                                                                                                                                                have h_disjoint_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part3 { k := k, a := a, eps := eps }, x ≠ y := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        have := part3_lt_part1 k a;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        filter_upwards [ self_mem_nhdsWithin ] with eps heps using fun x hx y hy => ne_of_gt <| this eps heps y hy x hx;
                                                                                                                                                                                                                                                                                                                                                                have h_disjoint_parts : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ part2 { k := k, a := a, eps := eps }, ∀ y ∈ part3 { k := k, a := a, eps := eps }, x ≠ y := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        have := part3_lt_part2 k a;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        filter_upwards [ self_mem_nhdsWithin ] with eps h_eps using fun x hx y hy => ne_of_gt <| this eps h_eps h_k h_a_le h_a_lt y hy x hx;
                                                                                                                                                                                                                                                                                                                                                                filter_upwards [ ‹∀ᶠ eps in nhdsWithin 0 ( Set.Ioi 0 ), ∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part2 { k := k, a := a, eps := eps }, x ≠ y›, ‹∀ᶠ eps in nhdsWithin 0 ( Set.Ioi 0 ), ∀ x ∈ part1 { k := k, a := a, eps := eps }, ∀ y ∈ part3 { k := k, a := a, eps := eps }, x ≠ y›, h_disjoint_parts ] with eps h₁ h₂ h₃ using ⟨ Finset.disjoint_left.mpr fun x hx₁ hx₂ => h₁ x ( List.mem_toFinset.mp hx₁ ) x ( List.mem_toFinset.mp hx₂ ) rfl, Finset.disjoint_left.mpr fun x hx₁ hx₂ => h₂ x ( List.mem_toFinset.mp hx₁ ) x ( List.mem_toFinset.mp hx₂ ) rfl, Finset.disjoint_left.mpr fun x hx₁ hx₂ => h₃ x ( List.mem_toFinset.mp hx₁ ) x ( List.mem_toFinset.mp hx₂ ) rfl ⟩;
          filter_upwards [ h_distinct_parts, h_disjoint_parts ] with ε hε₁ hε₂;
          have h_pairwise_append : ∀ {L1 L2 L3 : List ℝ}, List.Pairwise (· ≠ ·) L1 → List.Pairwise (· ≠ ·) L2 → List.Pairwise (· ≠ ·) L3 → Disjoint L1.toFinset L2.toFinset → Disjoint L1.toFinset L3.toFinset → Disjoint L2.toFinset L3.toFinset → List.Pairwise (· ≠ ·) (L1 ++ L2 ++ L3) := by
            simp +contextual [ List.pairwise_append, Finset.disjoint_left ];
            grind;
          exact h_pairwise_append hε₁.1 hε₁.2.1 hε₁.2.2 hε₂.1 hε₂.2.1 hε₂.2.2
        exact h_distinct.and h_pos;
      exact h_valid

/-
If a sequence of valid lists has ratios converging to target, then c(n) <= target.
-/
lemma c_le_of_limit {n : ℕ} {target : ℝ} (f : ℝ → List ℝ)
  (h_len : ∀ eps, (f eps).length = n)
  (h_valid : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (f eps).Pairwise (· ≠ ·) ∧ ∀ x ∈ f eps, 0 < x)
  (h_limit : Filter.Tendsto (fun eps => M (f eps) / (f eps).sum) (nhdsWithin 0 (Set.Ioi 0)) (nhds target)) :
  c n ≤ target := by
    have h_inf : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), c n ≤ M (f eps) / (f eps).sum := by
      filter_upwards [ h_valid ] with eps h_eps;
      exact csInf_le ⟨ 0, fun x hx => by rcases hx with ⟨ L, hL₁, hL₂, hL₃, rfl ⟩ ; exact div_nonneg ( le_max_of_le_left <| by
        unfold M_inc;
        unfold Option.getD; aesop;
        have := List.maximum_mem heq; aesop;
        exact List.sum_nonneg fun x hx => le_of_lt <| hL₃ x <| left_2.subset hx ) <| List.sum_nonneg fun x hx => le_of_lt <| by aesop ⟩ ⟨ f eps, h_len eps, h_eps.1, h_eps.2, rfl ⟩;
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit h_inf

/-
The length of the sequence is n.
-/
theorem seq_eps_length (k : ℤ) (a : ℤ) (eps : ℝ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  (seq_eps k a eps).length = (k^2 + 2*a + 1).toNat := by
    unfold seq_eps;
    unfold es_part;
    simp +zetaDelta at *;
    zify;
    rw [ Nat.cast_sub ] <;> norm_num [ abs_of_nonpos ( by linarith : a ≤ 0 ), abs_of_nonpos ( by linarith : a + 1 ≤ 0 ) ];
    · rw [ max_eq_left ( by nlinarith ) ] ; rw [ max_eq_left ( by nlinarith ) ] ; ring;
    · grind

/-
c(n) is less than or equal to the ratio for any valid sequence.
-/
theorem c_le_ratio {n : ℕ} (L : List ℝ) (h_len : L.length = n) (h_valid : L.Pairwise (· ≠ ·) ∧ ∀ x ∈ L, 0 < x) :
  c n ≤ M L / L.sum := by
    exact csInf_le ⟨ 0, by rintro x ⟨ L', hL₁, hL₂, hL₃, rfl ⟩ ; exact div_nonneg ( show 0 ≤ M L' by
                                                                                      unfold M; aesop;
                                                                                      unfold M_inc; unfold M_dec; aesop;
                                                                                      unfold Option.getD; aesop;
                                                                                      have := List.maximum_mem heq; aesop;
                                                                                      exact Or.inl ( List.sum_nonneg fun x hx => le_of_lt ( hL₃ x ( left_1.subset hx ) ) ) ) ( show 0 ≤ L'.sum by
                                                                                                                exact List.sum_nonneg fun x hx => le_of_lt ( hL₃ x hx ) ) ⟩ ⟨ L, h_len, h_valid.1, h_valid.2, rfl ⟩

/-
The upper bound for c(n) holds.
-/
theorem thm_main (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  let n := k^2 + 2*a + 1
  c n.toNat ≤ (k : ℝ) / (k^2 + a) := by
    -- Let's choose any $\epsilon > 0$ and show that $c(n.toNat) \leq k / (k^2 + a)$.
    apply c_le_of_limit;
    case f => exact fun eps => seq_eps k a eps;
    · exact fun eps ↦ seq_eps_length k a eps h_k h_a_le h_a_lt;
    · exact seq_eps_eventually_valid k a h_k h_a_le h_a_lt;
    · exact limit_ratio_correct k a h_k h_a_le h_a_lt

/-
If a sequence of valid lists has ratios converging to target, then c(n) <= target.
-/
lemma c_le_of_limit_v2 {n : ℕ} {target : ℝ} (f : ℝ → List ℝ)
  (h_len : ∀ eps, (f eps).length = n)
  (h_valid : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), (f eps).Pairwise (· ≠ ·) ∧ ∀ x ∈ f eps, 0 < x)
  (h_limit : Filter.Tendsto (fun eps => M (f eps) / (f eps).sum) (nhdsWithin 0 (Set.Ioi 0)) (nhds target)) :
  c n ≤ target := by
    apply c_le_of_limit f h_len h_valid h_limit

/-
The upper bound for c(n) holds.
-/
theorem thm_main_v2 (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  let n := k^2 + 2*a + 1
  c n.toNat ≤ (k : ℝ) / (k^2 + a) := by
    apply c_le_of_limit_v2 (fun eps => seq_eps k a eps);
    · intro eps; exact seq_eps_length k a eps h_k h_a_le h_a_lt;
    · exact seq_eps_eventually_valid k a h_k h_a_le h_a_lt;
    · exact limit_ratio_correct k a h_k h_a_le h_a_lt

/-

-/

/-
M(x_1,...,x_n) is the maximum of the sums of monotone subsequences of x_1,...,x_n.
-/
noncomputable def Mp (L : List ℝ) : ℝ :=
  ((L.sublists.filter (fun s => Decidable.decide (List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s))).map List.sum).maximum.getD 0

/-
c(n) is the infimum of M(x)/sum(x) over all sequences x of n positive distinct real numbers.
-/
noncomputable def cp (n : ℕ) : ℝ :=
  sInf { r | ∃ (L : List ℝ), L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ r = Mp L / L.sum }

/-
Define the sequence construction based on the Python code using List.flatMap.
-/
def es_block (base : ℝ) (start_idx : ℕ) (size : ℕ) (eps : ℝ) : List ℝ :=
  (List.range size).map (fun i => base + (start_idx + (size - 1 - i)) * eps)

def es_partp (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) : List ℝ :=
  (List.range num_blocks).flatMap (fun b => es_block base (start_idx + b * size) size eps)

noncomputable def construction (k a : ℕ) (eps : ℝ) : List ℝ :=
  let n := k^2 + 2*a + 1
  let part1p := es_partp (a + 1) 0 a (k - a) eps
  let part2p := es_partp a (a * (k - a)) (a + 1) (a + 1) eps
  let part3p := es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps
  part1p ++ part2p ++ part3p

/-
The length of an es_block is equal to its size parameter.
-/
lemma es_block_length (base : ℝ) (start_idx : ℕ) (size : ℕ) (eps : ℝ) :
  (es_block base start_idx size eps).length = size := by
    simp [es_block]

/-
The length of an es_partp is equal to num_blocks * size.
-/
lemma es_partp_length (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) :
  (es_partp base start_idx num_blocks size eps).length = num_blocks * size := by
    unfold es_partp; aesop;
    norm_num [ es_block_length ]

/-
The length of the constructed sequence is k^2 + 2a + 1, assuming a <= k.
-/
lemma construction_length (k a : ℕ) (eps : ℝ) (hak : a ≤ k) :
  (construction k a eps).length = k^2 + 2*a + 1 := by
    unfold construction;
    simp +zetaDelta at *;
    erw [ es_partp_length, es_partp_length, es_partp_length ] ; nlinarith [ Nat.sub_add_cancel hak ]

/-
Define max_inc_sum and max_dec_sum, and show Mp is the max of these two.
-/
noncomputable def max_inc_sum (L : List ℝ) : ℝ :=
  ((L.sublists.filter (fun s => Decidable.decide (List.Sorted (· < ·) s))).map List.sum).maximum.getD 0

noncomputable def max_dec_sum (L : List ℝ) : ℝ :=
  ((L.sublists.filter (fun s => Decidable.decide (List.Sorted (· > ·) s))).map List.sum).maximum.getD 0

lemma M_eq_max (L : List ℝ) : Mp L = max (max_inc_sum L) (max_dec_sum L) := by
  unfold Mp max_inc_sum max_dec_sum
  let both : List ℝ :=
    ((L.sublists.filter
      (fun s => Decidable.decide (List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s))).map
        List.sum)
  let inc : List ℝ :=
    ((L.sublists.filter (fun s => Decidable.decide (List.Sorted (· < ·) s))).map
      List.sum)
  let dec : List ℝ :=
    ((L.sublists.filter (fun s => Decidable.decide (List.Sorted (· > ·) s))).map
      List.sum)
  have hnil : ([] : List ℝ) ∈ L.sublists :=
    List.mem_sublists.2 (List.nil_sublist L)
  have hinc0 : 0 ∈ inc := by
    simp only [inc, List.mem_map, List.mem_filter]
    exact ⟨[], ⟨hnil, by simp⟩, by simp⟩
  have hdec0 : 0 ∈ dec := by
    simp only [dec, List.mem_map, List.mem_filter]
    exact ⟨[], ⟨hnil, by simp⟩, by simp⟩
  have hmax : both.maximum = (inc ++ dec).maximum := by
    apply le_antisymm
    · apply List.maximum_mono
      intro x hx
      simp only [both, inc, dec, List.mem_map, List.mem_filter, List.mem_append] at hx ⊢
      rcases hx with ⟨s, ⟨hsL, hs⟩, rfl⟩
      have hs' : List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s := by
        simpa using hs
      rcases hs' with hs | hs
      · left
        exact ⟨s, ⟨hsL, by simpa using hs⟩, rfl⟩
      · right
        exact ⟨s, ⟨hsL, by simpa using hs⟩, rfl⟩
    · apply List.maximum_mono
      intro x hx
      simp only [both, inc, dec, List.mem_map, List.mem_filter, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · rcases hx with ⟨s, ⟨hsL, hs⟩, rfl⟩
        have hs' : List.Sorted (· < ·) s := by
          simpa using hs
        exact ⟨s, ⟨hsL, by simpa using (Or.inl hs' :
          List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s)⟩, rfl⟩
      · rcases hx with ⟨s, ⟨hsL, hs⟩, rfl⟩
        have hs' : List.Sorted (· > ·) s := by
          simpa using hs
        exact ⟨s, ⟨hsL, by simpa using (Or.inr hs' :
          List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s)⟩, rfl⟩
  have hget :
      (inc ++ dec).maximum.getD 0 = max (inc.maximum.getD 0) (dec.maximum.getD 0) := by
    rw [List.maximum_append]
    cases hi : inc.maximum with
    | bot =>
        have : inc = [] := List.maximum_eq_bot.mp hi
        simp [this] at hinc0
    | coe mi =>
        cases hd : dec.maximum with
        | bot =>
            have : dec = [] := List.maximum_eq_bot.mp hd
            simp [this] at hdec0
        | coe md =>
            rw [← WithBot.coe_max]
            rfl
  change both.maximum.getD 0 = max (inc.maximum.getD 0) (dec.maximum.getD 0)
  rw [hmax]
  exact hget

/-
The sum of an es_block.
-/
lemma es_block_sum (base : ℝ) (start_idx : ℕ) (size : ℕ) (eps : ℝ) :
  (es_block base start_idx size eps).sum = (size : ℝ) * base + eps * ((size : ℝ) * (start_idx : ℝ) + (size : ℝ) * ((size : ℝ) - 1) / 2) := by
  unfold es_block
  simp only [List.bind_eq_flatMap]
  have hcast :
      List.flatMap (fun a : ℕ => (pure ((a : ℝ)) : List ℝ)) (List.range size) =
        List.map (fun a : ℕ => (a : ℝ)) (List.range size) := by
    simp [List.map_eq_flatMap]
  rw [hcast, List.map_map]
  clear hcast
  change (List.map (fun i : ℕ => base + ((start_idx : ℝ) + ((size : ℝ) - 1 - (i : ℝ))) * eps) (List.range size)).sum = _
  induction size generalizing start_idx with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      have hprefix :
          (List.map (fun i : ℕ => base + ((start_idx : ℝ) + (((n + 1 : ℕ) : ℝ) - 1 - (i : ℝ))) * eps) (List.range n)).sum =
            (List.map (fun i : ℕ => base + (((start_idx + 1 : ℕ) : ℝ) + ((n : ℝ) - 1 - (i : ℝ))) * eps) (List.range n)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro i hi
        norm_num [Nat.cast_add, Nat.cast_one]
        left
        ring
      rw [hprefix, ih (start_idx + 1)]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/-
The sum of a flatMap is the sum of the sums of the mapped lists.
-/
lemma sum_flatMap {α : Type*} (l : List α) (f : α → List ℝ) :
  (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
    induction l <;> aesop

/-
The sum of an es_partp.
-/
lemma es_partp_sum (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) :
  (es_partp base start_idx num_blocks size eps).sum =
    (num_blocks : ℝ) * ((size : ℝ) * base + eps * ((size : ℝ) * (start_idx : ℝ) + (size : ℝ) * ((size : ℝ) - 1) / 2)) +
    (eps * (size : ℝ)^2) * ((num_blocks : ℝ) * ((num_blocks : ℝ) - 1) / 2) := by
      induction num_blocks with
      | zero =>
        aesop
      | succ d ih =>
        -- By definition of `es_partp`, we can split the sum into the sum of the first `d` blocks and the sum of the last block.
        have h_split : (es_partp base start_idx (d + 1) size eps).sum = (es_partp base start_idx d size eps).sum + (es_block base (start_idx + d * size) size eps).sum := by
          unfold es_partp;
          simp [List.range_succ];
        rw [ h_split, ih, es_block_sum ] ; push_cast ; ring

/-
The sum of the constructed sequence is (a+1)(k^2+a) + eps * n(n-1)/2.
-/
lemma construction_sum (k a : ℕ) (eps : ℝ) (hak : a ≤ k) :
  (construction k a eps).sum = ((a : ℝ) + 1) * ((k : ℝ)^2 + (a : ℝ)) + eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) * (((k^2 + 2*a + 1 : ℕ) : ℝ) - 1) / 2 := by
    exact Eq.symm ( by rw [ show construction k a eps = es_partp ( a + 1 ) 0 a ( k - a ) eps ++ es_partp a ( a * ( k - a ) ) ( a + 1 ) ( a + 1 ) eps ++ es_partp ( a + 1 ) ( a * ( k - a ) + ( a + 1 ) * ( a + 1 ) ) ( k - a ) k eps from rfl ] ; rw [ List.sum_append, List.sum_append ] ; rw [ es_partp_sum, es_partp_sum, es_partp_sum ] ; push_cast [ Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub hak ] ; ring )

/-
Define a positive version of the construction by shifting by epsilon.
-/
noncomputable def construction_pos (k a : ℕ) (eps : ℝ) : List ℝ :=
  (construction k a eps).map (fun x => x + eps)

/-
The constructed sequence has no duplicates if epsilon is small enough.
-/
lemma construction_nodup (k a : ℕ) (eps : ℝ) (h_eps_pos : 0 < eps) (h_eps_small : eps * (k^2 + 2*a + 1 : ℕ) < 1) :
  (construction k a eps).Nodup := by
    -- Each part of the construction is nodup, and the parts are disjoint.
    have h_part1p_nodup : (es_partp (a + 1) 0 a (k - a) eps).Nodup := by
      unfold es_partp; norm_num [ List.nodup_flatMap ] ; aesop;
      · unfold es_block;
        rw [ List.nodup_map_iff_inj_on ]
        focus aesop
        induction ( k - a ) <;> simp_all +decide [ List.range_succ ];
        rw [ List.nodup_append ] ; aesop;
      · refine List.Pairwise.imp_of_mem (R := fun x y => x < y) ?_ ?_;
        · intros; rw [ Function.onFun, List.disjoint_iff_ne ] ; aesop;
          unfold es_block at *; aesop;
          norm_cast at h;
          rw [ Int.subNatNat_eq_coe ] at h ; push_cast at h ; nlinarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_pos ( by linarith ) ) ) ];
        · exact List.pairwise_lt_range
    have h_part2p_nodup : (es_partp a (a * (k - a)) (a + 1) (a + 1) eps).Nodup := by
      erw [ List.nodup_flatMap ];
      unfold es_block; aesop;
      · induction a + 1 <;> simp_all +decide [ List.range_succ ];
        rw [ List.nodup_append ] ; aesop;
      · rw [ List.pairwise_iff_get ] ; aesop;
        rw [ Function.onFun, List.disjoint_left ] ; aesop;
        have hij : (i : ℝ) + 1 ≤ j := by exact_mod_cast _hij
        have hx_le : (x : ℝ) ≤ a := by exact_mod_cast a_3
        have hx_nonneg : 0 ≤ (x : ℝ) := by positivity
        have hw_nonneg : 0 ≤ (w : ℝ) := by positivity
        have hw_le : (w : ℝ) ≤ a := by exact_mod_cast left
        nlinarith
    have h_part3p_nodup : (es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps).Nodup := by
      refine List.nodup_flatMap.mpr ?_;
      unfold es_block; aesop;
      · rw [ List.nodup_map_iff_inj_on ]
        focus aesop
        rw [ List.nodup_flatMap ] ; aesop;
        norm_num [ List.pairwise_iff_get ];
        exact fun i j hij => ne_of_gt hij;
      · rw [ List.pairwise_iff_get ] ; aesop;
        rw [ Function.onFun, List.disjoint_left ] ; aesop;
        nlinarith [ show ( i : ℝ ) + 1 ≤ j from mod_cast _hij, show ( x : ℝ ) < k from mod_cast a_3, show ( w : ℝ ) < k from mod_cast left ]
    have h_parts_disjoint : Disjoint (es_partp (a + 1) 0 a (k - a) eps).toFinset (es_partp a (a * (k - a)) (a + 1) (a + 1) eps).toFinset ∧ Disjoint (es_partp a (a * (k - a)) (a + 1) (a + 1) eps).toFinset (es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps).toFinset ∧ Disjoint (es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps).toFinset (es_partp (a + 1) 0 a (k - a) eps).toFinset := by
      unfold es_partp; aesop;
      · norm_num [ List.disjoint_left, es_block ];
        aesop;
        -- Since $eps$ is positive and less than 1, the term $((a - x) * (k - a) + x_3 * (a + 1) + (a - x_5) + x_2 - k + a + 1) * eps$ must be less than 1.
        have h_coeff : ((a - x) * (k - a) + x_3 * (a + 1) + (a - x_5) + x_2 - k + a + 1) * eps < 1 := by
          refine lt_of_le_of_lt ?_ h_eps_small;
          field_simp;
          nlinarith only [ show ( x : ℝ ) + 1 ≤ a by norm_cast, show ( x_2 : ℝ ) + 1 ≤ k - a by exact le_tsub_of_add_le_left ( by norm_cast; linarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) ) ) ] ), show ( x_3 : ℝ ) + 1 ≤ a + 1 by exact_mod_cast Nat.succ_le_succ a_6, show ( x_5 : ℝ ) + 1 ≤ a + 1 by exact_mod_cast Nat.succ_le_succ a_7 ];
        rw [ Nat.cast_sub ( by linarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_pos ( by linarith ) ) ) ] ) ] at * ; nlinarith;
      · norm_num [ List.disjoint_left, es_block ];
        aesop;
        have h_left_coeff_gt :
            (a : ℝ) * ((k - a : ℕ) : ℝ) + ((a : ℝ) + 1) * ((a : ℝ) + 1) + (x_3 : ℝ) * k + ((k : ℝ) - 1 - x_5) >
              (a : ℝ) * ((k - a : ℕ) : ℝ) + (x : ℝ) * ((a : ℝ) + 1) + ((a : ℝ) - x_2) := by
          have hx_le : (x : ℝ) ≤ a := by exact_mod_cast a_2
          have hx2_nonneg : 0 ≤ (x_2 : ℝ) := by positivity
          have hx2_sub_le : (a : ℝ) - x_2 ≤ a := by nlinarith
          have hx_mul_le : (x : ℝ) * ((a : ℝ) + 1) ≤ a * ((a : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hx_le (by positivity)
          have hx5_tail_nonneg : 0 ≤ (k : ℝ) - 1 - x_5 := by
            nlinarith [show (x_5 : ℝ) + 1 ≤ k by exact_mod_cast Nat.succ_le_of_lt a_7]
          have hx3_term_nonneg : 0 ≤ (x_3 : ℝ) * k := by positivity
          nlinarith
        have h_left_coeff_lt :
            (a : ℝ) * ((k - a : ℕ) : ℝ) + (x : ℝ) * ((a : ℝ) + 1) + ((a : ℝ) - x_2) <
              (a : ℝ) * ((k - a : ℕ) : ℝ) + ((a : ℝ) + 1) * ((a : ℝ) + 1) + (x_3 : ℝ) * k + ((k : ℝ) - 1 - x_5) :=
          h_left_coeff_gt
        have h_coeff_mul :
            (↑a * ↑(k - a) + ↑x * (↑a + 1) + (↑a - ↑x_2)) * eps <
              (↑a * ↑(k - a) + (↑a + 1) * (↑a + 1) + ↑x_3 * ↑k + (↑k - 1 - ↑x_5)) * eps :=
          mul_lt_mul_of_pos_right h_left_coeff_lt h_eps_pos
        nlinarith [a_1, h_coeff_mul];
      · norm_num [ List.disjoint_left, es_block ];
        aesop;
        nlinarith only [ show ( x_3 : ℝ ) + 1 ≤ a by norm_cast, show ( x_5 : ℝ ) + 1 ≤ k - a by exact le_tsub_of_add_le_left ( by norm_cast; omega ), show ( x : ℝ ) + 1 ≤ k - a by exact le_tsub_of_add_le_left ( by norm_cast; omega ), show ( x_2 : ℝ ) + 1 ≤ k by norm_cast, a_1, h_eps_small ];
    unfold construction; aesop;
    rw [ List.nodup_append, List.nodup_append ] ; aesop

/-
The maximum value in an es_partp.
-/
def es_partp_max_val (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) : ℝ :=
  base + (start_idx + num_blocks * size) * eps

/-
Every element in an es_partp is bounded by es_partp_max_val.
-/
lemma es_partp_bound (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
  ∀ x ∈ es_partp base start_idx num_blocks size eps, x ≤ es_partp_max_val base start_idx num_blocks size eps := by
  intro x hx
  unfold es_partp at hx
  rw [List.mem_flatMap] at hx
  rcases hx with ⟨b, hb, hx⟩
  simp only [es_block, List.mem_map] at hx
  rcases hx with ⟨i, hi, rfl⟩
  rw [List.bind_eq_flatMap, List.mem_flatMap] at hi
  rcases hi with ⟨j, hj, hji⟩
  simp only [List.mem_range] at hj
  rw [List.mem_pure] at hji
  subst i
  simp only [List.mem_range] at hb
  unfold es_partp_max_val
  have hprod : (b + 1) * size ≤ num_blocks * size :=
    Nat.mul_le_mul_right size (Nat.succ_le_of_lt hb)
  have hidx :
      (↑(start_idx + b * size) + (↑size - 1 - (j : ℝ))) ≤
        (↑start_idx + ↑num_blocks * ↑size) := by
    have hprodR : ((b + 1 : ℕ) : ℝ) * (size : ℝ) ≤
        (num_blocks : ℝ) * (size : ℝ) := by
      exact_mod_cast hprod
    norm_num [Nat.cast_add, Nat.cast_mul] at hprodR ⊢
    nlinarith [hprodR, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  nlinarith [mul_le_mul_of_nonneg_right hidx heps]

/-
es_block is strictly decreasing if epsilon is positive.
-/
lemma es_block_decreasing (base : ℝ) (start_idx : ℕ) (size : ℕ) (eps : ℝ) (heps : 0 < eps) :
  List.Sorted (· > ·) (es_block base start_idx size eps) := by
    unfold es_block;
    refine List.pairwise_iff_get.mpr ?_ ; aesop;
    -- The flatMap of the range size is just the list of natural numbers from 0 to size-1.
    have h_flatMap : List.flatMap (fun (a : ℕ) => [(↑a : ℝ)]) (List.range size) = List.map (fun (a : ℕ) => ↑a) (List.range size) := by
      exact Eq.symm List.map_eq_flatMap;
    aesop

/-
Any increasing subsequence of an es_partp has length at most num_blocks.
-/
lemma es_partp_inc_length_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 < eps) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· < ·) s →
  s.length ≤ num_blocks := by
    unfold es_partp;
    -- Since each element in es_block is strictly decreasing, any increasing subsequence can contain at most one element from each block.
    have h_block : ∀ b : ℕ, ∀ s : List ℝ, s.Sublist (es_block base (start_idx + b * size) size eps) → s.Pairwise (· < ·) → s.length ≤ 1 := by
      intro b s hs_sub hs_sorted
      have h_block_sorted : s.Pairwise (· > ·) := by
        exact List.Pairwise.sublist hs_sub <| es_block_decreasing base (start_idx + b * size) size eps heps
      rcases s with _ | ⟨x, _ | ⟨y, t⟩⟩
      · simp
      · simp
      · have hxy_lt : x < y := (List.pairwise_cons.mp hs_sorted).1 y (by simp)
        have hxy_gt : x > y := (List.pairwise_cons.mp h_block_sorted).1 y (by simp)
        linarith
    induction num_blocks with
    | zero =>
      intro s hs hs_sorted
      simp [List.eq_nil_of_sublist_nil hs]
    | succ n ih =>
      intro s hs hs_sorted
      simp [List.range_succ, List.flatMap_append, List.sublist_append_iff] at hs
      rcases hs with ⟨s₁, s₂, rfl, hs₁, hs₂⟩
      rw [List.length_append]
      exact add_le_add
        (ih s₁ hs₁ (hs_sorted.sublist (List.sublist_append_left s₁ s₂)))
        (h_block n s₂ hs₂ (hs_sorted.sublist (List.sublist_append_right s₁ s₂)))

/-
The sum of any increasing subsequence in an es_partp is bounded by num_blocks * max_val.
-/
lemma es_partp_inc_sum_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hbase : 0 ≤ base) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· < ·) s →
  List.sum s ≤ (num_blocks : ℝ) * es_partp_max_val base start_idx num_blocks size eps := by
    intros s hs_sub hs_sorted
    have hs_len : s.length ≤ num_blocks := by
      by_cases h_eps_pos : 0 < eps;
      · exact es_partp_inc_length_le base start_idx num_blocks size eps h_eps_pos s hs_sub hs_sorted
      · have h_eps_eq : eps = 0 := le_antisymm (le_of_not_gt h_eps_pos) heps
        subst eps
        by_cases h_num_blocks : num_blocks = 0
        · subst num_blocks
          exact (by simpa [es_partp] using hs_sub.length_le)
        · have h_s_len_one : s.length ≤ 1 := by
            have h_mem_eq : ∀ z ∈ es_partp base start_idx num_blocks size 0, z = base := by
              intro z hz
              simp [es_partp, es_block] at hz
              exact hz.2.2
            rcases s with _ | ⟨x, _ | ⟨y, t⟩⟩
            · simp
            · simp
            · have hxy_lt : x < y := (List.pairwise_cons.mp hs_sorted).1 y (by simp)
              have hx_eq : x = base := h_mem_eq x (hs_sub.subset (by simp))
              have hy_eq : y = base := h_mem_eq y (hs_sub.subset (by simp))
              linarith
          exact le_trans h_s_len_one (Nat.succ_le_iff.mp (Nat.pos_of_ne_zero h_num_blocks))
    have h_max_sum : ∀ x ∈ s, x ≤ es_partp_max_val base start_idx num_blocks size eps := by
      exact fun x hx => es_partp_bound base start_idx num_blocks size eps heps x ( hs_sub.subset hx );
    exact le_trans ( List.sum_le_card_nsmul _ _ h_max_sum ) ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hs_len ) ( show 0 ≤ es_partp_max_val base start_idx num_blocks size eps by unfold es_partp_max_val; positivity ) )

/-
Any decreasing subsequence of an es_partp has length at most size.
-/
lemma es_partp_dec_length_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 < eps) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· > ·) s →
  s.length ≤ size := by
  unfold es_partp
  induction num_blocks with
  | zero =>
    intro s hs hs_sorted
    simp [List.eq_nil_of_sublist_nil hs]
  | succ n ih =>
    intro s hs hs_sorted
    simp [List.range_succ, List.flatMap_append, List.sublist_append_iff] at hs
    rcases hs with ⟨s₁, s₂, rfl, hs₁, hs₂⟩
    by_cases h₁ : s₁ = []
    · have hlen₂ := List.Sublist.length_le hs₂
      rw [es_block_length] at hlen₂
      simpa [h₁] using hlen₂
    · by_cases h₂ : s₂ = []
      · have hsorted₁ : List.Sorted (· > ·) s₁ :=
          hs_sorted.sublist (List.sublist_append_left s₁ s₂)
        simpa [h₂] using ih s₁ hs₁ hsorted₁
      · rcases List.exists_mem_of_ne_nil s₁ h₁ with ⟨x, hx⟩
        rcases List.exists_mem_of_ne_nil s₂ h₂ with ⟨y, hy⟩
        have hxy_gt : x > y :=
          (List.pairwise_append.mp hs_sorted).2.2 x hx y hy
        have hx_bound : x ≤ base + (start_idx + n * size) * eps := by
          have hx_part : x ∈ es_partp base start_idx n size eps := by
            unfold es_partp
            exact hs₁.subset hx
          simpa [es_partp_max_val] using
            es_partp_bound base start_idx n size eps heps.le x hx_part
        have hy_bound : base + (start_idx + n * size) * eps ≤ y := by
          have hy_block : y ∈ es_block base (start_idx + n * size) size eps :=
            hs₂.subset hy
          unfold es_block at hy_block
          rw [List.mem_map] at hy_block
          rcases hy_block with ⟨i, hi, hy_eq⟩
          have hi' : ∃ j ∈ List.range size, i ∈ [((j : ℕ) : ℝ)] := by
            simpa [List.mem_flatMap] using hi
          rcases hi' with ⟨j, hj, hij⟩
          rw [List.mem_singleton] at hij
          rw [hij] at hy_eq
          rw [← hy_eq]
          have hj_lt : j < size := by
            simpa using hj
          have hj_le : (j : ℝ) + 1 ≤ (size : ℝ) := by
            have hj_succ : j + 1 ≤ size := Nat.succ_le_iff.mpr hj_lt
            exact_mod_cast hj_succ
          have harg :
              ((start_idx + n * size : ℕ) : ℝ) ≤
                ((start_idx + n * size : ℕ) : ℝ) + ((size : ℝ) - 1 - (j : ℝ)) := by
            linarith
          have hmul := mul_le_mul_of_nonneg_right harg heps.le
          have hstart :
              ((start_idx + n * size : ℕ) : ℝ) =
                (start_idx : ℝ) + (n : ℝ) * (size : ℝ) := by
            norm_num
          calc
            base + ((start_idx : ℝ) + (n : ℝ) * (size : ℝ)) * eps
                = base + ((start_idx + n * size : ℕ) : ℝ) * eps := by
              rw [hstart]
            _ ≤ base + (((start_idx + n * size : ℕ) : ℝ) + ((size : ℝ) - 1 - (j : ℝ))) * eps := by
              linarith
        linarith

/-
The sum of any decreasing subsequence in an es_partp is bounded by size * max_val.
-/
lemma es_partp_dec_sum_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hbase : 0 ≤ base) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· > ·) s →
  List.sum s ≤ (size : ℝ) * es_partp_max_val base start_idx num_blocks size eps := by
    intro s hs_sub hs_sorted
    have h_length : s.length ≤ size := by
      by_cases heps_pos : 0 < eps;
      · exact es_partp_dec_length_le base start_idx num_blocks size eps heps_pos s hs_sub hs_sorted;
      · cases eq_or_lt_of_le heps <;> aesop;
        unfold es_partp at hs_sub;
        unfold es_block at hs_sub; aesop;
        have := hs_sorted; rcases s with ( _ | ⟨ x, _ | ⟨ y, s ⟩ ⟩ ) <;> simp_all +decide [ List.Sorted ] ;
        · exact Nat.pos_of_ne_zero hs_sub.2.1;
        · have := hs_sub.subset; aesop;
    have h_sum_le : ∀ x ∈ s, x ≤ es_partp_max_val base start_idx num_blocks size eps := by
      exact fun x hx => es_partp_bound base start_idx num_blocks size eps heps x <| by simpa using hs_sub.subset hx;
    exact le_trans ( List.sum_le_card_nsmul _ _ h_sum_le ) ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_length ) ( show 0 ≤ es_partp_max_val base start_idx num_blocks size eps from by unfold es_partp_max_val; positivity ) )

/-
Define the three parts of the construction and show the construction is their concatenation.
-/
def part1p (k a : ℕ) (eps : ℝ) : List ℝ := es_partp (a + 1) 0 a (k - a) eps

def part2p (k a : ℕ) (eps : ℝ) : List ℝ := es_partp a (a * (k - a)) (a + 1) (a + 1) eps

def part3p (k a : ℕ) (eps : ℝ) : List ℝ := es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps

lemma construction_eq_parts (k a : ℕ) (eps : ℝ) :
  construction k a eps = part1p k a eps ++ part2p k a eps ++ part3p k a eps := by rfl

/-
If L1 < L2, then max_inc_sum(L1 ++ L2) = max_inc_sum(L1) + max_inc_sum(L2).
-/
lemma max_inc_sum_append_of_lt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x < y) :
  max_inc_sum (L1 ++ L2) = max_inc_sum L1 + max_inc_sum L2 := by
  unfold max_inc_sum
  let good : List ℝ → List (List ℝ) := fun L =>
    L.sublists.filter (fun S => Decidable.decide (S.Sorted (· < ·)))
  let sums : List ℝ → List ℝ := fun L => (good L).map List.sum
  change (sums (L1 ++ L2)).maximum.getD 0 =
    (sums L1).maximum.getD 0 + (sums L2).maximum.getD 0
  have zero_mem_sums : ∀ L : List ℝ, (0 : ℝ) ∈ sums L := by
    intro L
    refine List.mem_map.mpr ?_
    refine ⟨[], ?_, by simp⟩
    simp [good, List.mem_sublists, List.Sorted, List.Pairwise.nil]
  have le_max_getD :
      ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → ∀ x ∈ xs, x ≤ xs.maximum.getD 0 := by
    intro xs h0 x hx
    have hxle : (x : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' hx
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        simp [hm] at hxle ⊢
        exact hxle
  have max_getD_mem : ∀ (xs : List ℝ), (0 : ℝ) ∈ xs → xs.maximum.getD 0 ∈ xs := by
    intro xs h0
    have h0le : ((0 : ℝ) : WithBot ℝ) ≤ xs.maximum := List.le_maximum_of_mem' h0
    cases hm : xs.maximum with
    | bot =>
        simp [hm] at h0le
    | coe m =>
        have hmem : m ∈ xs := (List.maximum_eq_coe_iff.mp hm).1
        simpa [hm] using hmem
  have mem_sums_append :
      ∀ x : ℝ, x ∈ sums (L1 ++ L2) ↔
        ∃ x1 ∈ sums L1, ∃ x2 ∈ sums L2, x = x1 + x2 := by
    intro x
    constructor
    · intro hx
      rcases List.mem_map.mp hx with ⟨S, hSgood, rfl⟩
      have hS : S.Sublist (L1 ++ L2) ∧ S.Sorted (· < ·) := by
        simpa [sums, good, List.mem_sublists] using hSgood
      rcases hS with ⟨hSsub, hSsort⟩
      have hSmem : S ∈ (L1 ++ L2).sublists := by
        simpa [List.mem_sublists] using hSsub
      rw [List.sublists_append] at hSmem
      simp at hSmem
      rcases hSmem with ⟨T₂, hT₂sub, T₁, hT₁sub, hEq⟩
      have hEq' : S = T₁ ++ T₂ := hEq.symm
      have hsort12 : T₁.Sorted (· < ·) ∧ T₂.Sorted (· < ·) := by
        rw [hEq', List.Sorted, List.pairwise_append] at hSsort
        exact ⟨hSsort.1, hSsort.2.1⟩
      have hT₁mem : T₁.sum ∈ sums L1 := by
        refine List.mem_map.mpr ?_
        refine ⟨T₁, ?_, rfl⟩
        simpa [sums, good, List.mem_sublists] using And.intro hT₁sub hsort12.1
      have hT₂mem : T₂.sum ∈ sums L2 := by
        refine List.mem_map.mpr ?_
        refine ⟨T₂, ?_, rfl⟩
        simpa [sums, good, List.mem_sublists] using And.intro hT₂sub hsort12.2
      refine ⟨T₁.sum, hT₁mem, T₂.sum, hT₂mem, ?_⟩
      simp [hEq', List.sum_append]
    · rintro ⟨x1, hx1, x2, hx2, rfl⟩
      rcases List.mem_map.mp hx1 with ⟨T₁, hT₁good, rfl⟩
      rcases List.mem_map.mp hx2 with ⟨T₂, hT₂good, rfl⟩
      have hT₁ : T₁.Sublist L1 ∧ T₁.Sorted (· < ·) := by
        simpa [sums, good, List.mem_sublists] using hT₁good
      have hT₂ : T₂.Sublist L2 ∧ T₂.Sorted (· < ·) := by
        simpa [sums, good, List.mem_sublists] using hT₂good
      refine List.mem_map.mpr ?_
      refine ⟨T₁ ++ T₂, ?_, by simp [List.sum_append]⟩
      have hsorted : (T₁ ++ T₂).Sorted (· < ·) := by
        rw [List.Sorted, List.pairwise_append]
        refine ⟨hT₁.2, hT₂.2, ?_⟩
        intro a ha b hb
        exact h a (hT₁.1.subset ha) b (hT₂.1.subset hb)
      have hsub : (T₁ ++ T₂).Sublist (L1 ++ L2) :=
        List.Sublist.append hT₁.1 hT₂.1
      simpa [sums, good, List.mem_sublists] using And.intro hsub hsorted
  apply le_antisymm
  · have hABmem : (sums (L1 ++ L2)).maximum.getD 0 ∈ sums (L1 ++ L2) :=
      max_getD_mem (sums (L1 ++ L2)) (zero_mem_sums (L1 ++ L2))
    rcases (mem_sums_append ((sums (L1 ++ L2)).maximum.getD 0)).mp hABmem with
      ⟨x1, hx1, x2, hx2, hEq⟩
    have hx1le : x1 ≤ (sums L1).maximum.getD 0 :=
      le_max_getD (sums L1) (zero_mem_sums L1) x1 hx1
    have hx2le : x2 ≤ (sums L2).maximum.getD 0 :=
      le_max_getD (sums L2) (zero_mem_sums L2) x2 hx2
    linarith
  · have h1mem : (sums L1).maximum.getD 0 ∈ sums L1 :=
      max_getD_mem (sums L1) (zero_mem_sums L1)
    have h2mem : (sums L2).maximum.getD 0 ∈ sums L2 :=
      max_getD_mem (sums L2) (zero_mem_sums L2)
    have hpair : (sums L1).maximum.getD 0 + (sums L2).maximum.getD 0 ∈ sums (L1 ++ L2) :=
      (mem_sums_append ((sums L1).maximum.getD 0 + (sums L2).maximum.getD 0)).mpr
        ⟨(sums L1).maximum.getD 0, h1mem,
          (sums L2).maximum.getD 0, h2mem, rfl⟩
    exact le_max_getD (sums (L1 ++ L2)) (zero_mem_sums (L1 ++ L2))
      ((sums L1).maximum.getD 0 + (sums L2).maximum.getD 0) hpair

/-
Every element in an es_partp corresponds to an index in the range.
-/
lemma exists_idx_of_mem_es_partp (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) :
  ∀ x ∈ es_partp base start_idx num_blocks size eps, ∃ i : ℕ, start_idx ≤ i ∧ i < start_idx + num_blocks * size ∧ x = base + i * eps := by
  intro x hx
  unfold es_partp at hx
  rcases List.mem_flatMap.mp hx with ⟨b, hb, hx⟩
  have hb_lt : b < num_blocks := by
    simpa using hb
  unfold es_block at hx
  rcases List.mem_map.mp hx with ⟨jr, hjr, hx_eq⟩
  have hjr' : ∃ j < size, jr = (j : ℝ) := by
    simpa [List.mem_map, List.mem_range] using hjr
  rcases hjr' with ⟨j, hj_lt, hj_eq⟩
  subst jr
  refine ⟨start_idx + b * size + (size - 1 - j), ?_, ?_, ?_⟩
  · omega
  · have hblock_le : (b + 1) * size ≤ num_blocks * size :=
      Nat.mul_le_mul_right size (Nat.succ_le_of_lt hb_lt)
    have hlocal_lt : size - 1 - j < size := by
      omega
    have hinner : b * size + (size - 1 - j) < num_blocks * size := by
      calc
        b * size + (size - 1 - j) < b * size + size :=
          Nat.add_lt_add_left hlocal_lt (b * size)
        _ = (b + 1) * size := by
          rw [Nat.add_mul, one_mul]
        _ ≤ num_blocks * size := hblock_le
    simpa [Nat.add_assoc] using Nat.add_lt_add_left hinner start_idx
  · rw [← hx_eq]
    have hcast_local : ((size - 1 - j : ℕ) : ℝ) = (size : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega : j ≤ size - 1),
        Nat.cast_sub (by omega : 1 ≤ size)]
      ring
    simp only [Nat.cast_add, Nat.cast_mul, hcast_local]

/-
If L1 > L2, then max_inc_sum(L1 ++ L2) = max(max_inc_sum(L1), max_inc_sum(L2)).
-/
lemma max_inc_sum_append_of_gt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x > y) :
  max_inc_sum (L1 ++ L2) = max (max_inc_sum L1) (max_inc_sum L2) := by
  let cand : List ℝ → List ℝ := fun L =>
    (L.sublists.filter (fun s => Decidable.decide (List.Sorted (· < ·) s))).map List.sum
  have hmem_of_sublist :
      ∀ {L s : List ℝ}, s.Sublist L → List.Sorted (· < ·) s → s.sum ∈ cand L := by
    intro L s hs hsort
    dsimp [cand]
    exact List.mem_map.mpr
      ⟨s, List.mem_filter.mpr ⟨List.mem_sublists.mpr hs, by simpa⟩, rfl⟩
  have hnil_mem : ∀ L : List ℝ, (0 : ℝ) ∈ cand L := by
    intro L
    simpa using hmem_of_sublist (L := L) (s := []) (List.nil_sublist L) (List.sorted_nil)
  have h_cases :
      ∀ s : List ℝ, s.Sublist (L1 ++ L2) → List.Sorted (· < ·) s →
        s.Sublist L1 ∨ s.Sublist L2 := by
    intro s hs hs'
    rw [List.sublist_append_iff] at hs
    rcases hs with ⟨sA, sB, rfl, hsA, hsB⟩
    rcases sA with _ | ⟨x, xs⟩
    · right
      simpa using hsB
    rcases sB with _ | ⟨y, ys⟩
    · left
      simpa using hsA
    exfalso
    have hxy : x < y := hs'.rel_of_mem_append (by simp) (by simp)
    have hyx : y < x := h x (hsA.subset (by simp)) y (hsB.subset (by simp))
    linarith
  have hAB_cases : ∀ {x : ℝ}, x ∈ cand (L1 ++ L2) → x ∈ cand L1 ∨ x ∈ cand L2 := by
    intro x hx
    dsimp [cand] at hx
    rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
    rcases List.mem_filter.mp hs with ⟨hs_sub, hs_sort⟩
    have hs_sub' : s.Sublist (L1 ++ L2) := List.mem_sublists.mp hs_sub
    have hs_sort' : List.Sorted (· < ·) s := of_decide_eq_true hs_sort
    rcases h_cases s hs_sub' hs_sort' with hsL1 | hsL2
    · exact Or.inl (hmem_of_sublist hsL1 hs_sort')
    · exact Or.inr (hmem_of_sublist hsL2 hs_sort')
  have hL1_subset : cand L1 ⊆ cand (L1 ++ L2) := by
    intro x hx
    dsimp [cand] at hx
    rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
    rcases List.mem_filter.mp hs with ⟨hs_sub, hs_sort⟩
    have hs_sort' : List.Sorted (· < ·) s := of_decide_eq_true hs_sort
    exact hmem_of_sublist ((List.mem_sublists.mp hs_sub).trans (List.sublist_append_left L1 L2)) hs_sort'
  have hL2_subset : cand L2 ⊆ cand (L1 ++ L2) := by
    intro x hx
    dsimp [cand] at hx
    rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
    rcases List.mem_filter.mp hs with ⟨hs_sub, hs_sort⟩
    have hs_sort' : List.Sorted (· < ·) s := of_decide_eq_true hs_sort
    exact hmem_of_sublist ((List.mem_sublists.mp hs_sub).trans (List.sublist_append_right L1 L2)) hs_sort'
  have hmaxeq :
      (cand (L1 ++ L2)).maximum = max (cand L1).maximum (cand L2).maximum := by
    apply le_antisymm
    · apply List.maximum_le_of_forall_le
      intro x hx
      rcases hAB_cases hx with hxL1 | hxL2
      · exact le_trans (List.le_maximum_of_mem' hxL1) (le_max_left _ _)
      · exact le_trans (List.le_maximum_of_mem' hxL2) (le_max_right _ _)
    · exact max_le (List.maximum_mono hL1_subset) (List.maximum_mono hL2_subset)
  have hL1_ne : (cand L1).maximum ≠ ⊥ := by
    exact List.maximum_ne_bot_of_ne_nil (by
      intro hnil
      have := hnil_mem L1
      simp [hnil] at this)
  have hL2_ne : (cand L2).maximum ≠ ⊥ := by
    exact List.maximum_ne_bot_of_ne_nil (by
      intro hnil
      have := hnil_mem L2
      simp [hnil] at this)
  unfold max_inc_sum
  change (cand (L1 ++ L2)).maximum.getD 0 =
    max ((cand L1).maximum.getD 0) ((cand L2).maximum.getD 0)
  rw [hmaxeq]
  cases hL1max : (cand L1).maximum with
  | bot => simp_all
  | coe a =>
    cases hL2max : (cand L2).maximum with
    | bot => simp_all
    | coe b =>
      have hga : Option.getD (↑a : WithBot ℝ) 0 = a := rfl
      have hgb : Option.getD (↑b : WithBot ℝ) 0 = b := rfl
      simp_all [max_def]
      by_cases hab : a ≤ b
      · simp [hab, hgb]
      · simp [hab, hga]

/-
If L1 < L2, then max_dec_sum(L1 ++ L2) = max(max_dec_sum(L1), max_dec_sum(L2)).
-/
lemma max_dec_sum_append_of_lt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x < y) :
  max_dec_sum (L1 ++ L2) = max (max_dec_sum L1) (max_dec_sum L2) := by
  simpa [max_dec_sum, M_dec] using (M_dec_append_of_lt (A := L1) (B := L2) h)

/-
If L1 > L2, then max_dec_sum(L1 ++ L2) = max_dec_sum(L1) + max_dec_sum(L2).
-/
lemma max_dec_sum_append_of_gt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x > y) :
  max_dec_sum (L1 ++ L2) = max_dec_sum L1 + max_dec_sum L2 := by
  simpa [max_dec_sum, M_dec] using (M_dec_append_of_gt (A := L1) (B := L2) h)

/-
Elements of part1p are greater than elements of part2p.
-/
lemma part1p_gt_part2p (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  ∀ x ∈ part1p k a eps, ∀ y ∈ part2p k a eps, x > y := by
    unfold part1p part2p; aesop;
    obtain ⟨ i, hi₁, hi₂, rfl ⟩ := exists_idx_of_mem_es_partp ( a + 1 ) 0 a ( k - a ) eps _ a_1 ; obtain ⟨ j, hj₁, hj₂, rfl ⟩ := exists_idx_of_mem_es_partp a ( a * ( k - a ) ) ( a + 1 ) ( a + 1 ) eps _ a_2;
    -- Since $j < a * (k - a) + (a + 1) * (a + 1)$ and $eps * (k^2 + 2 * a + 1) < 1$, we have $j * eps < 1$.
    have h_j_eps_lt_1 : (j : ℝ) * eps < 1 := by
      refine lt_of_le_of_lt ?_ heps_small;
      rw [ mul_comm ] ; gcongr ; norm_cast ; nlinarith only [ hj₂, Nat.sub_add_cancel hak ];
    nlinarith

/-
Elements of part3p are greater than elements of part2p.
-/
lemma part3p_gt_part2p (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  ∀ x ∈ part3p k a eps, ∀ y ∈ part2p k a eps, x > y := by
    -- By definition of part3p and part2p, we know that every element in part3p is greater than every element in part2p.
    intros x hx y hy
    obtain ⟨i, hi⟩ := exists_idx_of_mem_es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps x hx
    obtain ⟨j, hj⟩ := exists_idx_of_mem_es_partp a (a * (k - a)) (a + 1) (a + 1) eps y hy;
    aesop;
    nlinarith [ ( by norm_cast : ( a : ℝ ) * ( k - a ) + ( a + 1 ) * ( a + 1 ) ≤ i ), ( by norm_cast : ( a : ℝ ) * ( k - a ) ≤ j ), ( by norm_cast : ( j : ℝ ) < a * ( k - a ) + ( a + 1 ) * ( a + 1 ) ) ]

/-
Elements of part3p are greater than elements of part1p.
-/
lemma part3p_gt_part1p (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  ∀ x ∈ part3p k a eps, ∀ y ∈ part1p k a eps, x > y := by
    aesop;
    -- By definition of `part1p` and `part3p`, we know that every element in `part1p` is less than every element in `part3p`.
    obtain ⟨i, hi⟩ : ∃ i : ℕ, 0 ≤ i ∧ i < a * (k - a) ∧ y = (a + 1) + i * eps := by
      have := exists_idx_of_mem_es_partp ( a + 1 ) 0 a ( k - a ) eps y a_2; aesop;
    obtain ⟨j, hj⟩ : ∃ j : ℕ, a * (k - a) + (a + 1) * (a + 1) ≤ j ∧ j < a * (k - a) + (a + 1) * (a + 1) + (k - a) * k ∧ x = (a + 1) + j * eps := by
      have := exists_idx_of_mem_es_partp ( a + 1 ) ( a * ( k - a ) + ( a + 1 ) * ( a + 1 ) ) ( k - a ) k eps x a_1; aesop;
    aesop;
    nlinarith

/-
Elements of part1p ++ part2p are less than elements of part3p.
-/
lemma part1p_part2p_lt_part3p (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  ∀ x ∈ part1p k a eps ++ part2p k a eps, ∀ y ∈ part3p k a eps, x < y := by
    have := part3p_gt_part1p k a eps hak heps_pos heps_small;
    have := part3p_gt_part2p k a eps hak heps_pos heps_small; aesop;

/-
Decomposition of max_inc_sum for the construction.
-/
lemma max_inc_sum_construction (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  max_inc_sum (construction k a eps) = max (max_inc_sum (part1p k a eps)) (max_inc_sum (part2p k a eps)) + max_inc_sum (part3p k a eps) := by
    rw [ construction_eq_parts ];
    rw [ max_inc_sum_append_of_lt, max_inc_sum_append_of_gt ];
    · exact fun x a_1 y a_2 ↦ part1p_gt_part2p k a eps hak heps_pos heps_small x a_1 y a_2;
    · exact fun x a_1 y a_2 ↦ part1p_part2p_lt_part3p k a eps hak heps_pos heps_small x a_1 y a_2

/-
Decomposition of max_dec_sum for the construction.
-/
lemma max_dec_sum_construction (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  max_dec_sum (construction k a eps) = max (max_dec_sum (part1p k a eps) + max_dec_sum (part2p k a eps)) (max_dec_sum (part3p k a eps)) := by
    rw [ construction_eq_parts ];
    rw [ max_dec_sum_append_of_lt ];
    · rw [ max_dec_sum_append_of_gt ];
      · exact part1p_gt_part2p k a eps hak heps_pos heps_small;
    · exact part1p_part2p_lt_part3p k a eps hak heps_pos heps_small

/-
M(construction) is bounded by k(a+1) + O(eps).
-/
lemma M_construction_le (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  Mp (construction k a eps) ≤ (k : ℝ) * ((a : ℝ) + 1) + eps * ((k^2 + 2*a + 1 : ℕ) : ℝ)^3 := by
    refine le_trans ( M_eq_max (construction k a eps) |> Eq.le ) ?_;
    -- Applying the lemmas for max_inc_sum and max_dec_sum constructions:
    have h_max_inc : max_inc_sum (construction k a eps) ≤ (k : ℝ) * (a + 1) + eps * (k^2 + 2*a + 1)^3 := by
      -- By Lemma 2, we know that the maximum increasing subsequence sum is bounded by the sum of the maximum increasing subsequences of each part.
      have h_part1p : max_inc_sum (part1p k a eps) ≤ (a : ℝ) * ((a + 1) + (a * (k - a)) * eps) := by
        have := es_partp_inc_sum_le ( a + 1 ) 0 a ( k - a ) eps ( by positivity ) ( by positivity );
        unfold max_inc_sum; aesop;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
          convert this_1 w left right_1 using 1 ; unfold es_partp_max_val ; ring_nf;
          rw [ Nat.cast_sub ] <;> linarith;
        · exact mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg ( add_nonneg ( Nat.cast_nonneg _ ) zero_le_one ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.cast_le.mpr hak ) ) ) heps_pos.le ) )
      have h_part2p : max_inc_sum (part2p k a eps) ≤ (a + 1 : ℝ) * (a + (a * (k - a) + (a + 1) * (a + 1)) * eps) := by
        have h_part2p : ∀ s : List ℝ, List.Sublist s (part2p k a eps) → List.Sorted (· < ·) s → List.sum s ≤ (a + 1 : ℝ) * (a + (a * (k - a) + (a + 1) * (a + 1)) * eps) := by
          intros s hs_sub hs_sorted;
          have := es_partp_inc_sum_le a ( a * ( k - a ) ) ( a + 1 ) ( a + 1 ) eps ( by positivity ) ( by positivity ) s hs_sub hs_sorted;
          simp_all +decide [ es_partp_max_val ];
        unfold max_inc_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact mul_nonneg ( by positivity ) ( add_nonneg ( by positivity ) ( mul_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.cast_le.mpr hak ) ) ) ( mul_nonneg ( by positivity ) ( by positivity ) ) ) heps_pos.le ) )
      have h_part3p : max_inc_sum (part3p k a eps) ≤ (k - a : ℝ) * ((a + 1) + (a * (k - a) + (a + 1) * (a + 1) + (k - a) * k) * eps) := by
        have h_part3p : ∀ s : List ℝ, s.Sublist (part3p k a eps) → s.Sorted (· < ·) → s.sum ≤ (k - a : ℝ) * ((a + 1) + (a * (k - a) + (a + 1) * (a + 1) + (k - a) * k) * eps) := by
          intro s hs hs'; have := es_partp_inc_sum_le ( a + 1 ) ( a * ( k - a ) + ( a + 1 ) * ( a + 1 ) ) ( k - a ) k eps ( by positivity ) ( by positivity ) s hs hs'; aesop;
          convert this using 2 ; ring_nf;
          unfold es_partp_max_val; norm_num [ hak ] ; ring;
        unfold max_inc_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact mul_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr hak ) ) ( add_nonneg ( by positivity ) ( mul_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.cast_le.mpr hak ) ) ) ( mul_nonneg ( by positivity ) ( by positivity ) ) ) ( mul_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr hak ) ) ( Nat.cast_nonneg _ ) ) ) heps_pos.le ) );
      -- Substitute the bounds from h_part1p, h_part2p, and h_part3p into the expression for max_inc_sum (construction k a eps).
      have h_max_inc_sum : max_inc_sum (construction k a eps) ≤ max (a * ((a + 1) + (a * (k - a)) * eps)) ((a + 1) * (a + (a * (k - a) + (a + 1) * (a + 1)) * eps)) + (k - a) * ((a + 1) + (a * (k - a) + (a + 1) * (a + 1) + (k - a) * k) * eps) := by
        exact le_trans ( max_inc_sum_construction k a eps hak heps_pos heps_small ▸ add_le_add ( max_le_max h_part1p h_part2p ) h_part3p ) ( by norm_num );
      refine le_trans h_max_inc_sum ?_;
      rw [ max_def_lt ] ; split_ifs <;> ring_nf at * <;> norm_num at *;
      · rcases a with ( _ | a ) <;> rcases k with ( _ | k ) <;> norm_num at *;
        · exact le_of_sub_nonneg ( by ring_nf; positivity );
        · exact le_of_sub_nonneg ( by ring_nf; positivity );
      · nlinarith [ ( by positivity : 0 ≤ ( a : ℝ ) * k * eps ), ( by positivity : 0 ≤ ( a : ℝ ) * k ^ 2 * eps ), ( by positivity : 0 ≤ ( a : ℝ ) ^ 2 * k * eps ), ( by positivity : 0 ≤ ( a : ℝ ) ^ 2 * k ^ 2 * eps ), ( by positivity : 0 ≤ ( a : ℝ ) ^ 3 * eps ), ( by positivity : 0 ≤ ( k : ℝ ) * eps ), ( by positivity : 0 ≤ ( k : ℝ ) ^ 2 * eps ), ( by positivity : 0 ≤ ( k : ℝ ) ^ 3 * eps ), ( by positivity : 0 ≤ ( k : ℝ ) ^ 4 * eps ), ( by positivity : 0 ≤ ( k : ℝ ) ^ 6 * eps ) ];
    have h_max_dec : max_dec_sum (construction k a eps) ≤ (k : ℝ) * (a + 1) + eps * (k^2 + 2*a + 1)^3 := by
      have h_max_dec : max_dec_sum (part1p k a eps) + max_dec_sum (part2p k a eps) ≤ (k : ℝ) * (a + 1) + eps * (k^2 + 2*a + 1)^3 := by
        -- Applying the bounds for max_dec_sum for part1p and part2p:
        have h_max_dec_part1p : max_dec_sum (part1p k a eps) ≤ (k - a : ℝ) * (es_partp_max_val (a + 1) 0 a (k - a) eps) := by
          have h_max_dec_part1p : ∀ s : List ℝ, List.Sublist s (part1p k a eps) → List.Sorted (· > ·) s → List.sum s ≤ (k - a : ℝ) * (es_partp_max_val (a + 1) 0 a (k - a) eps) := by
            intro s hs hs'; have := es_partp_dec_sum_le ( a + 1 ) 0 a ( k - a ) eps heps_pos.le ( by positivity ) s hs hs'; aesop;
          unfold max_dec_sum; aesop;
          unfold Option.getD; aesop;
          · have := List.maximum_mem heq; aesop;
          · exact mul_nonneg ( sub_nonneg_of_le ( Nat.cast_le.mpr hak ) ) ( by unfold es_partp_max_val; positivity )
        have h_max_dec_part2p : max_dec_sum (part2p k a eps) ≤ (a + 1 : ℝ) * (es_partp_max_val a (a * (k - a)) (a + 1) (a + 1) eps) := by
          have h_max_dec_part2p : ∀ (s : List ℝ), List.Sublist s (part2p k a eps) → List.Sorted (· > ·) s → List.sum s ≤ (a + 1 : ℝ) * (es_partp_max_val a (a * (k - a)) (a + 1) (a + 1) eps) := by
            intros s hs_sub hs_sorted;
            have := es_partp_dec_sum_le ( a : ℝ ) ( a * ( k - a ) ) ( a + 1 ) ( a + 1 ) eps heps_pos.le ( by positivity ) s hs_sub hs_sorted;
            aesop;
          unfold max_dec_sum;
          unfold Option.getD; aesop;
          · have := List.maximum_mem heq; aesop;
          · exact mul_nonneg ( by positivity ) ( by unfold es_partp_max_val; positivity );
        unfold es_partp_max_val at *;
        refine le_trans ( add_le_add h_max_dec_part1p h_max_dec_part2p ) ?_;
        rw [ Nat.cast_sub hak ] ; push_cast ; ring_nf at * ; aesop;
        nlinarith only [ show 0 ≤ ( k : ℝ ) ^ 4 * eps by positivity, show 0 ≤ ( k : ℝ ) ^ 6 * eps by positivity, show 0 ≤ ( a : ℝ ) ^ 3 * eps by positivity, show 0 ≤ ( a : ℝ ) ^ 2 * eps by positivity, show 0 ≤ ( a : ℝ ) * eps by positivity, show 0 ≤ ( k : ℝ ) ^ 2 * eps by positivity, show 0 ≤ ( k : ℝ ) * eps by positivity, heps_small, show ( a : ℝ ) ≤ k by norm_cast ];
      have h_max_dec_part3p : max_dec_sum (part3p k a eps) ≤ (k : ℝ) * (a + 1) + eps * (k^2 + 2*a + 1)^3 := by
        have h_max_dec_part3p : max_dec_sum (part3p k a eps) ≤ (k : ℝ) * es_partp_max_val (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps := by
          have h_max_dec_part3p : ∀ s : List ℝ, List.Sublist s (part3p k a eps) → List.Sorted (· > ·) s → List.sum s ≤ (k : ℝ) * es_partp_max_val (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps := by
            intros s hs_sub hs_sorted;
            apply es_partp_dec_sum_le;
            · positivity;
            · positivity;
            · exact hs_sub;
            · exact ((fun a ↦ hs_sorted) ∘ fun a ↦ k) k;
          unfold max_dec_sum;
          unfold Option.getD; aesop;
          · have := List.maximum_mem heq; aesop;
          · exact mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg ( by positivity ) ( mul_nonneg ( by positivity ) ( by positivity ) ) );
        refine le_trans h_max_dec_part3p ?_;
        unfold es_partp_max_val; norm_num; ring_nf at *; aesop;
        nlinarith [ show ( 0 : ℝ ) ≤ k * a * eps by positivity, show ( 0 : ℝ ) ≤ k * eps by positivity, show ( 0 : ℝ ) ≤ k ^ 2 * a * eps by positivity, show ( 0 : ℝ ) ≤ k ^ 2 * eps by positivity, show ( 0 : ℝ ) ≤ k ^ 4 * a * eps by positivity, show ( 0 : ℝ ) ≤ k ^ 4 * eps by positivity, show ( 0 : ℝ ) ≤ k ^ 6 * eps by positivity, show ( 0 : ℝ ) ≤ a * eps by positivity, show ( 0 : ℝ ) ≤ a ^ 2 * eps by positivity, show ( 0 : ℝ ) ≤ a ^ 3 * eps by positivity ];
      rw [ max_dec_sum_construction ];
      · exact max_le h_max_dec h_max_dec_part3p;
      · bound;
      · exact RCLike.ofReal_pos.mp heps_pos;
      · exact RCLike.ofReal_lt_ofReal.mp heps_small;
    aesop

/-
M(L + c) <= M(L) + length(L) * cp for cp >= 0.
-/
lemma M_shift (L : List ℝ) (cp : ℝ) (hc : 0 ≤ cp) :
  Mp (L.map (· + cp)) ≤ Mp L + L.length * cp := by
  unfold Mp
  let P : List ℝ → Prop := fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s
  let A : List ℝ := (L.sublists.filter (fun s => decide (P s))).map List.sum
  let B : List ℝ := ((L.map (fun x => x + cp)).sublists.filter (fun s => decide (P s))).map List.sum
  change B.maximum.getD 0 ≤ A.maximum.getD 0 + (L.length : ℝ) * cp
  have h_bound : ∀ b ∈ B, b ≤ A.maximum.getD 0 + (L.length : ℝ) * cp := by
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    rw [List.mem_filter] at hs
    rcases hs with ⟨hs_sub_mem, hs_sorted_decide⟩
    have hs_sorted : P s := of_decide_eq_true hs_sorted_decide
    have hs_sub : s.Sublist (L.map (fun x => x + cp)) := by
      simpa using (List.mem_sublists.mp hs_sub_mem)
    obtain ⟨s', hs'_sub, hs_eq⟩ := List.sublist_map_iff.mp hs_sub
    have hs'_sorted : P s' := by
      subst s
      rcases hs_sorted with hs_inc | hs_dec
      · left
        simpa [P, List.Sorted, List.pairwise_map] using hs_inc
      · right
        simpa [P, List.Sorted, List.pairwise_map] using hs_dec
    have hs'_mem_filter : s' ∈ L.sublists.filter (fun s => decide (P s)) := by
      rw [List.mem_filter]
      exact ⟨List.mem_sublists.mpr hs'_sub, decide_eq_true hs'_sorted⟩
    have hs'_sum_mem : s'.sum ∈ A := by
      exact List.mem_map.mpr ⟨s', hs'_mem_filter, rfl⟩
    have hs'_sum_le : s'.sum ≤ A.maximum.getD 0 := by
      cases hA : A.maximum with
      | bot =>
          have hA_nil : A = [] := List.maximum_eq_bot.mp hA
          simp [hA_nil] at hs'_sum_mem
      | coe a =>
          have hle : s'.sum ≤ a := List.le_maximum_of_mem hs'_sum_mem hA
          simpa [hA] using hle
    have hlen : (s'.length : ℝ) * cp ≤ (L.length : ℝ) * cp := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs'_sub.length_le) hc
    have hsum : (s'.map (fun x => x + cp)).sum = s'.sum + (s'.length : ℝ) * cp := by
      rw [List.sum_map_add]
      simp
    calc
      s.sum = s'.sum + (s'.length : ℝ) * cp := by simp [hs_eq]
      _ ≤ A.maximum.getD 0 + (L.length : ℝ) * cp := add_le_add hs'_sum_le hlen
  have hzero_mem : (0 : ℝ) ∈ B := by
    apply List.mem_map.mpr
    refine ⟨[], ?_, by simp⟩
    rw [List.mem_filter]
    exact ⟨by simp, decide_eq_true (Or.inl (by simp [List.Sorted]))⟩
  cases hB : B.maximum with
  | bot =>
      have hB_nil : B = [] := List.maximum_eq_bot.mp hB
      simp [hB_nil] at hzero_mem
  | coe b =>
      have hb_mem : b ∈ B := List.maximum_mem hB
      have hb_le := h_bound b hb_mem
      simpa [hB] using hb_le

/-
Elements of construction are non-negative.
-/
lemma construction_nonneg (k a : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
  ∀ x ∈ construction k a eps, 0 ≤ x := by
  intro x hx
  rw [construction_eq_parts] at hx
  simp only [part1p, part2p, part3p, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨i, _hi0, _hi1, rfl⟩ :=
      exists_idx_of_mem_es_partp ((a : ℝ) + 1) 0 a (k - a) eps x hx
    exact add_nonneg (add_nonneg (Nat.cast_nonneg a) zero_le_one)
      (mul_nonneg (Nat.cast_nonneg i) heps)
  · obtain ⟨i, _hi0, _hi1, rfl⟩ :=
      exists_idx_of_mem_es_partp (a : ℝ) (a * (k - a)) (a + 1) (a + 1) eps x hx
    exact add_nonneg (Nat.cast_nonneg a) (mul_nonneg (Nat.cast_nonneg i) heps)
  · obtain ⟨i, _hi0, _hi1, rfl⟩ :=
      exists_idx_of_mem_es_partp ((a : ℝ) + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps x hx
    exact add_nonneg (add_nonneg (Nat.cast_nonneg a) zero_le_one)
      (mul_nonneg (Nat.cast_nonneg i) heps)

/-
M(construction_pos) is bounded by k(a+1) + eps * (n^3 + n).
-/
lemma M_construction_pos_le (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  Mp (construction_pos k a eps) ≤ (k : ℝ) * ((a : ℝ) + 1) + eps * ((k^2 + 2*a + 1 : ℕ) : ℝ)^3 + ((k^2 + 2*a + 1 : ℕ) : ℝ) * eps := by
    unfold construction_pos;
    have h_len : (construction k a eps).length = k^2 + 2*a + 1 := construction_length k a eps hak;
    rw [ ← h_len ];
    refine le_trans ( M_shift (construction k a eps) eps heps_pos.le ) ?_;
    rw [ h_len ];
    have := M_construction_le k a eps hak heps_pos heps_small;
    linarith

/-
Theorem: Let k >= 1 and 0 <= a <= k be integers, and n = k^2 + 2a + 1. Then c(n) <= k / (k^2 + a). Proof: We construct a sequence L_eps = construction_pos k a eps. We show that for small enough eps, L_eps is a valid sequence (length n, distinct, positive). We then bound M(L_eps) / S(L_eps). Taking the limit as eps -> 0, we get the desired bound.
-/
theorem main_theorem (k a : ℕ) (hk : 1 ≤ k) (hak : a ≤ k) :
  let n := k^2 + 2*a + 1
  cp n ≤ (k : ℝ) / (k^2 + a) := by
    -- Consider the limit of $r_{\epsilon}$ as $\epsilon \to 0$.
    have h_limit : Filter.Tendsto (fun (ε' : ℝ) => (k * (a + 1) + ε' * ((k^2 + 2*a + 1 : ℕ) : ℝ)^3 + ((k^2 + 2*a + 1 : ℕ) : ℝ) * ε') / (((a : ℝ) + 1) * ((k : ℝ)^2 + (a : ℝ)) + ε' * ((k^2 + 2*a + 1 : ℕ) : ℝ) * (((k^2 + 2*a + 1 : ℕ) : ℝ) - 1) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (k / ((k^2 + a : ℝ)))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_;
      convert Filter.Tendsto.div ( Continuous.tendsto _ _ ) ( Continuous.tendsto _ _ ) _ using 2 <;> norm_num;
      exacts [ by rw [ div_eq_div_iff ] <;> ring_nf <;> positivity, by infer_instance, by infer_instance, by continuity, by continuity, ⟨ by positivity, by positivity ⟩ ];
    refine le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ?_;
    rw [ Filter.EventuallyLE, eventually_nhdsWithin_iff ];
    filter_upwards [ gt_mem_nhds <| show 0 < 1 / ( ( k^2 + 2*a + 1 : ℝ ) ) from by positivity ] with x hx₁ hx₂ ; aesop;
    refine le_trans ( csInf_le ?_ ⟨ construction_pos k a x, ?_, ?_, ?_, rfl ⟩ ) ?_;
    · exact ⟨ 0, by rintro _ ⟨ L, hL₁, hL₂, hL₃, rfl ⟩ ; exact div_nonneg ( by
        unfold Mp;
        unfold Option.getD; aesop;
        have := List.maximum_mem heq; aesop;
        · exact List.sum_nonneg fun x hx => le_of_lt ( hL₃ x ( left.subset hx ) );
        · exact List.sum_nonneg fun x hx => le_of_lt ( hL₃ x ( left.subset hx ) ) ) ( List.sum_nonneg fun x hx => le_of_lt ( hL₃ x hx ) ) ⟩;
    · unfold construction_pos;
      rw [ List.length_map, construction_length ] ; linarith;
    · refine List.Nodup.map ?_ ?_;
      · exact add_left_injective x;
      · refine construction_nodup k a x hx₂ ?_;
        rw [ inv_eq_one_div, lt_div_iff₀ ] at hx₁ <;> norm_cast at * ; nlinarith;
    · unfold construction_pos; aesop;
      exact add_pos_of_nonneg_of_pos ( construction_nonneg k a x ( by positivity ) _ left ) hx₂;
    · gcongr;
      · convert M_construction_pos_le k a x hak hx₂ _ using 1;
        · norm_cast;
        · rw [ inv_eq_one_div, lt_div_iff₀ ] at hx₁ <;> norm_num at * <;> nlinarith;
      · unfold construction_pos; aesop;
        rw [ construction_sum, construction_length ];
        · norm_num ; nlinarith;
        · linarith;
        · linarith

/-
M(L) is always non-negative.
-/
lemma M_nonneg (L : List ℝ) : 0 ≤ Mp L := by
  unfold Mp
  let sums :=
    (L.sublists.filter
      (fun s => Decidable.decide (List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s))).map
        List.sum
  have h_empty_mem :
      ([] : List ℝ) ∈
        L.sublists.filter
          (fun s => Decidable.decide (List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s)) := by
    have h_empty_sorted :
        List.Sorted (· < ·) ([] : List ℝ) ∨ List.Sorted (· > ·) ([] : List ℝ) := by
      left
      exact List.Pairwise.nil
    rw [List.mem_filter]
    constructor
    · exact List.mem_sublists.mpr (List.nil_sublist L)
    · rw [decide_eq_true_iff]
      exact h_empty_sorted
  have h_zero_mem : (0 : ℝ) ∈ sums := by
    refine List.mem_map.mpr ?_
    exact ⟨[], h_empty_mem, by simp [List.sum]⟩
  have hle : (0 : WithBot ℝ) ≤ sums.maximum :=
    List.le_maximum_of_mem' h_zero_mem
  cases hmax : sums.maximum with
  | bot =>
      exact le_rfl
  | coe x =>
      have hx : (0 : ℝ) ≤ x := by
        simpa [hmax] using hle
      simpa using hx

/-
Theorem: Let k >= 1 and 0 <= a <= k be integers, and n = k^2 + 2a + 1. Then c(n) <= k / (k^2 + a).
-/
theorem main_theorem_final (k a : ℕ) (hk : 1 ≤ k) (hak : a ≤ k) :
  let n := k^2 + 2*a + 1
  cp n ≤ (k : ℝ) / (k^2 + a) := by
    -- Apply the main theorem to conclude the proof.
    apply main_theorem k a hk hak

/-
Theorem: Let k >= 1 and 0 <= a <= k be integers, and n = k^2 + 2a + 1. Then c(n) <= k / (k^2 + a).
-/
theorem main_theorem_proven (k a : ℕ) (hk : 1 ≤ k) (hak : a ≤ k) :
  let n := k^2 + 2*a + 1
  cp n ≤ (k : ℝ) / (k^2 + a) := by
    -- Apply the main theorem with the given k and a.
    apply main_theorem_final k a hk hak

/-

-/

/-
We define an axis-aligned square inside the unit square [0,1]x[0,1] by its bottom-left corner (x,y) and side length s.
Two squares are disjoint if their interiors are disjoint.
A packing of n squares is a collection of n squares that are pairwise disjoint.
g(n) is the supremum of the total side length of a valid packing of n squares.
-/
structure Square where
  x : ℝ
  y : ℝ
  s : ℝ
  s_nonneg : 0 ≤ s
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  x_plus_s_le_one : x + s ≤ 1
  y_plus_s_le_one : y + s ≤ 1

def Square.disjoint (sq1 sq2 : Square) : Prop :=
  (sq1.x + sq1.s ≤ sq2.x) ∨ (sq2.x + sq2.s ≤ sq1.x) ∨
  (sq1.y + sq1.s ≤ sq2.y) ∨ (sq2.y + sq2.s ≤ sq1.y)

def Packing (n : ℕ) := Fin n → Square

def Packing.is_valid {n : ℕ} (P : Packing n) : Prop :=
  ∀ i j, i ≠ j → (P i).disjoint (P j)

def Packing.total_side_length {n : ℕ} (P : Packing n) : ℝ :=
  ∑ i, (P i).s

noncomputable def g (n : ℕ) : ℝ :=
  sSup {L | ∃ P : Packing n, P.is_valid ∧ P.total_side_length = L}

/-
For non-negative integers p, q with |p-q| <= 1, pq >= p+q-1.
-/
lemma algebraic_lemma (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) (h_diff : |p - q| ≤ 1) : p * q ≥ p + q - 1 := by
  cases abs_cases ( p - q ) <;> rcases lt_trichotomy p 1 with ( hp' | rfl | hp' ) <;> rcases lt_trichotomy q 1 with ( hq' | rfl | hq' ) <;> nlinarith

noncomputable def num_points (a b x : ℝ) : ℤ := ⌊b - x⌋ - ⌈a - x⌉ + 1

/-
The integral of the number of integers in [a-x, b-x] over x in [0, 1) is equal to the length b-a.
-/
lemma integral_num_points (a b : ℝ) (hab : a ≤ b) :
    ∫ x in Set.Ioo 0 1, (num_points a b x : ℝ) = b - a := by
      -- We can rewrite the integral using the fact that num_points a b x is equal to the number of integers in [a-x, b-x].
      have h_integral : ∫ x in Set.Ioo 0 1, (num_points a b x : ℝ) = ∫ x in Set.Ioo 0 1, (⌊b - x⌋ - ⌈a - x⌉ + 1 : ℝ) := by
        norm_cast;
      -- We'll use the fact that $\int_0^1 \lfloor b-x \rfloor dx = b - 1$ and $\int_0^1 \lceil a-x \rceil dx = a$.
      have h_floor : ∫ x in Set.Ioo 0 1, (⌊b - x⌋ : ℝ) = b - 1 := by
        -- Let $b = k + \delta$ with $k \in \mathbb{Z}, \delta \in [0, 1)$.
        obtain ⟨k, δ, hk, hδ⟩ : ∃ k : ℤ, ∃ δ : ℝ, b = k + δ ∧ 0 ≤ δ ∧ δ < 1 := by
          exact ⟨ ⌊b⌋, b - ⌊b⌋, by ring, Int.fract_nonneg _, Int.fract_lt_one _ ⟩;
        -- We can split the integral into two parts: $\int_0^\delta \lfloor b-x \rfloor dx$ and $\int_\delta^1 \lfloor b-x \rfloor dx$.
        have h_split : ∫ x in Set.Ioo 0 1, (⌊b - x⌋ : ℝ) = (∫ x in Set.Ioo 0 δ, (⌊b - x⌋ : ℝ)) + (∫ x in Set.Ioo δ 1, (⌊b - x⌋ : ℝ)) := by
          rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.setIntegral_union ] <;> norm_num [ hδ.1, hδ.2.le ];
          · refine MeasureTheory.Integrable.mono'
              (g := fun x => 1 + |b| + |x|) ?_ ?_ ?_;
            · exact Continuous.integrableOn_Ioc ( by continuity );
            · apply_rules [ Measurable.aestronglyMeasurable, measurable_const ];
              exact Measurable.comp ( by measurability ) ( Measurable.floor ( measurable_const.sub measurable_id' ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using abs_le.mpr ⟨ by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ], by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ] ⟩;
          · refine MeasureTheory.Integrable.mono'
              (g := fun x => 1 + |b| + |x|) ?_ ?_ ?_;
            · exact Continuous.integrableOn_Ioc ( by continuity );
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( measurable_id'.const_sub _ |> Measurable.floor ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using abs_le.mpr ⟨ by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ], by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ] ⟩;
        -- In the first interval, $\lfloor b-x \rfloor = k$ and in the second interval, $\lfloor b-x \rfloor = k-1$.
        have h_floor_values : (∫ x in Set.Ioo 0 δ, (⌊b - x⌋ : ℝ)) = (∫ x in Set.Ioo 0 δ, (k : ℝ)) ∧ (∫ x in Set.Ioo δ 1, (⌊b - x⌋ : ℝ)) = (∫ x in Set.Ioo δ 1, (k - 1 : ℝ)) := by
          constructor <;> refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_ <;> aesop;
          · exact Int.floor_eq_iff.mpr ⟨ by linarith, by linarith ⟩;
          · exact_mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩;
        aesop;
        rw [ max_eq_left ] <;> linarith
      have h_ceil : ∫ x in Set.Ioo 0 1, (⌈a - x⌉ : ℝ) = a := by
        -- Let $a = m + \epsilon$ with $m \in \mathbb{Z}$ and $\epsilon \in [0, 1)$.
        obtain ⟨m, ε, hm, hε⟩ : ∃ m : ℤ, ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ a = m + ε := by
          exact ⟨ ⌊a⌋, a - ⌊a⌋, Int.fract_nonneg _, Int.fract_lt_one _, by ring ⟩;
        -- We can split the integral into two parts: $\int_0^\epsilon \lceil a-x \rceil dx$ and $\int_\epsilon^1 \lceil a-x \rceil dx$.
        have h_split : ∫ x in Set.Ioo 0 1, (⌈a - x⌉ : ℝ) = (∫ x in Set.Ioo 0 ε, (⌈a - x⌉ : ℝ)) + (∫ x in Set.Ioo ε 1, (⌈a - x⌉ : ℝ)) := by
          rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.setIntegral_union ] <;> norm_num [ hm, hε.1.le ];
          · refine MeasureTheory.Integrable.mono'
              (g := fun x => 2 + |a| + ε) ?_ ?_ ?_;
            · norm_num;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact Measurable.ceil ( by exact measurable_const.sub measurable_id' ) ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> cases abs_cases a <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ), hx.1, hx.2 ] ;
          · refine MeasureTheory.Integrable.mono'
              (g := fun x => 2 + |a| + |x|) ?_ ?_ ?_;
            · exact Continuous.integrableOn_Ioc ( by continuity );
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( measurable_id'.const_sub _ |> Measurable.ceil ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using abs_le.mpr ⟨ by cases abs_cases a <;> cases abs_cases x <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ) ], by cases abs_cases a <;> cases abs_cases x <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ) ] ⟩;
        -- In the first interval $(0, \epsilon)$, $\lceil a - x \rceil = m + 1$.
        have h_first : ∫ x in Set.Ioo 0 ε, (⌈a - x⌉ : ℝ) = (m + 1) * ε := by
          rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [ show ⌈a - x⌉ = m + 1 from Int.ceil_eq_iff.mpr ⟨ by norm_num; linarith [ hx.1, hx.2 ], by norm_num; linarith [ hx.1, hx.2 ] ⟩ ] ] ; norm_num [ mul_comm, hm ];
        -- In the second interval $(\epsilon, 1)$, $\lceil a - x \rceil = m$.
        have h_second : ∫ x in Set.Ioo ε 1, (⌈a - x⌉ : ℝ) = m * (1 - ε) := by
          rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [ show ⌈a - x⌉ = m by exact Int.ceil_eq_iff.mpr ⟨ by linarith [ hx.1, hx.2 ], by norm_num; linarith [ hx.1, hx.2 ] ⟩ ] ] ; norm_num [ hε.1.le ] ; ring;
        linarith;
      rw [ h_integral, MeasureTheory.integral_add, MeasureTheory.integral_sub ] <;> norm_num [ h_floor, h_ceil ];
      · ring;
      · refine MeasureTheory.Integrable.mono'
          (g := fun x => |b - x| + 1) ?_ ?_ ?_;
        · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.Ioo_subset_Icc_self;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact measurable_id'.const_sub _ |> Measurable.floor ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using abs_le.mpr ⟨ by cases abs_cases ( b - x ) <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ], by cases abs_cases ( b - x ) <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ] ⟩;
      · refine MeasureTheory.Integrable.mono'
          (g := fun x => 2 + |a| + |b|) ?_ ?_ ?_;
        · norm_num;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact measurable_id'.const_sub _ |> Measurable.ceil ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ), hx.1, hx.2 ] ;
      · refine MeasureTheory.Integrable.sub ?_ ?_;
        · refine MeasureTheory.Integrable.mono'
            (g := fun x => 2 + |b|) ?_ ?_ ?_;
          · norm_num;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact measurable_id'.const_sub _ |> Measurable.floor ) );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using abs_le.mpr ⟨ by cases abs_cases b <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ), hx.1, hx.2 ], by cases abs_cases b <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ), hx.1, hx.2 ] ⟩;
        · refine MeasureTheory.Integrable.mono'
            (g := fun x => 2 + |a| + |b|) ?_ ?_ ?_;
          · norm_num;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact Measurable.ceil ( measurable_const.sub measurable_id' ) ) );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using abs_le.mpr ⟨ by cases abs_cases a <;> cases abs_cases b <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ), hx.1, hx.2 ], by cases abs_cases a <;> cases abs_cases b <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ), hx.1, hx.2 ] ⟩

/-
There exists a shift x avoiding a finite bad set such that the sum of counts is at least the sum of lengths.
-/
lemma exists_shift_sum_ge (n : ℕ) (a b : Fin n → ℝ) (hab : ∀ i, a i ≤ b i) (Bad : Set ℝ) (hBad : Bad.Finite) :
  ∃ x, 0 ≤ x ∧ x < 1 ∧ x ∉ Bad ∧ (∑ i, (num_points (a i) (b i) x : ℝ)) ≥ ∑ i, (b i - a i) := by
    -- By `integral_num_points` and linearity of the integral, $\int_0^1 f(x) dx = \sum (b_i - a_i)$.
    have h_integral : ∫ x in (Set.Ioo 0 1), (∑ i, (num_points (a i) (b i) x : ℝ)) = ∑ i, (b i - a i) := by
      rw [ MeasureTheory.integral_finset_sum ] <;> aesop;
      · rw [ ← Finset.sum_sub_distrib, Finset.sum_congr rfl ] ; intros ; rw [ integral_num_points ] ; aesop_cat;
      · refine MeasureTheory.Integrable.mono'
          (g := fun x => |b i - a i| + 1) ?_ ?_ ?_;
        · norm_num;
        · -- The function num_points is a composition of measurable functions (floor and ceiling), hence it is measurable.
          have h_num_points_measurable : Measurable (fun x => num_points (a i) (b i) x) := by
            exact Measurable.add ( Measurable.sub ( Measurable.floor ( measurable_const.sub measurable_id' ) ) ( Measurable.ceil ( measurable_const.sub measurable_id' ) ) ) measurable_const;
          exact Measurable.aestronglyMeasurable ( by measurability );
        · filter_upwards with a_1
          refine abs_le.mpr ⟨ ?_, ?_ ⟩ <;> norm_num [ num_points ] <;> cases abs_cases ( b i - a i ) <;> linarith [ Int.floor_le ( b i - a_1 ), Int.lt_floor_add_one ( b i - a_1 ), Int.le_ceil ( a i - a_1 ), Int.ceil_lt_add_one ( a i - a_1 ) ] ;
    -- By contradiction, assume that for all $x \in [0, 1) \setminus Bad$, $\sum_{i=1}^n num\_points(a_i, b_i, x) < \sum_{i=1}^n (b_i - a_i)$.
    by_contra h_contra;
    have h_integral_lt : ∫ x in (Set.Ioo 0 1) \ Bad, (∑ i, (num_points (a i) (b i) x : ℝ)) < ∫ x in (Set.Ioo 0 1) \ Bad, (∑ i, (b i - a i) : ℝ) := by
      apply lt_of_sub_pos;
      rw [ ← MeasureTheory.integral_sub ];
      · rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
        · simp_all ( config := { decide := Bool.true } ) [ Function.support ];
          refine lt_of_lt_of_le
            ( b := (MeasureTheory.volume.restrict (Set.Ioo 0 1 \ Bad)) (Set.Ioo 0 1 \ Bad) )
            ?_ ( MeasureTheory.measure_mono ?_ );
          · simp +zetaDelta at *;
            rw [ MeasureTheory.measure_diff_null ] <;> norm_num;
            exact hBad.measure_zero MeasureTheory.MeasureSpace.volume;
          · exact fun x hx => ne_of_gt <| sub_pos_of_lt <| by linarith [ h_contra x hx.1.1.le hx.1.2 hx.2 ] ;
        · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioo.diff hBad.measurableSet ) ] with x hx using sub_nonneg_of_le <| le_of_not_ge fun hx' => h_contra ⟨ x, hx.1.1.le, hx.1.2, hx.2, hx' ⟩;
        · refine MeasureTheory.Integrable.sub ?_ ?_;
          · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.diff_subset.trans <| Set.Ioo_subset_Icc_self;
          · refine MeasureTheory.Integrable.mono'
              (g := fun x => ∑ i, ( b i - a i + 2 )) ?_ ?_ ?_;
            · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.diff_subset.trans <| Set.Ioo_subset_Icc_self;
            · refine Measurable.aestronglyMeasurable ?_;
              refine Finset.measurable_sum Finset.univ fun i _ => ?_;
              unfold num_points
              measurability
            · filter_upwards [ MeasureTheory.ae_restrict_mem <| measurableSet_Ioo.diff hBad.measurableSet ] with x hx;
              rw [ Real.norm_of_nonneg ];
              · refine Finset.sum_le_sum fun i _ => ?_;
                simp +zetaDelta at *;
                exact le_trans ( Int.cast_le.mpr <| show num_points ( a i ) ( b i ) x ≤ ⌊b i - x⌋ - ⌈a i - x⌉ + 1 from le_rfl ) <| by push_cast [ num_points ] ; linarith [ Int.floor_le ( b i - x ), Int.lt_floor_add_one ( b i - x ), Int.le_ceil ( a i - x ), Int.ceil_lt_add_one ( a i - x ) ] ;
              · refine Finset.sum_nonneg fun i _ => ?_;
                unfold num_points;
                exact_mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( b i - x ), Int.lt_floor_add_one ( b i - x ), Int.le_ceil ( a i - x ), Int.ceil_lt_add_one ( a i - x ), hab i ] );
      · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.diff_subset.trans <| Set.Ioo_subset_Icc_self;
      · refine MeasureTheory.Integrable.mono'
          (g := fun x => ∑ i, ( b i - a i + 1 )) ?_ ?_ ?_;
        · norm_num +zetaDelta at *;
          exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.diff_subset.trans <| Set.Ioo_subset_Icc_self );
        · refine Measurable.aestronglyMeasurable ?_;
          refine Finset.measurable_sum Finset.univ fun i _ => ?_;
          unfold num_points
          measurability
        · filter_upwards [ MeasureTheory.ae_restrict_mem <| measurableSet_Ioo.diff <| hBad.measurableSet ] with x hx;
          rw [ Real.norm_of_nonneg ];
          · exact le_trans ( le_of_not_gt fun h => h_contra ⟨ x, hx.1.1.le, hx.1.2, hx.2, h.le ⟩ ) ( Finset.sum_le_sum fun i _ => show ( b i - a i : ℝ ) ≤ b i - a i + 1 by linarith );
          · refine Finset.sum_nonneg fun i _ => ?_;
            unfold num_points;
            exact_mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( b i - x ), Int.lt_floor_add_one ( b i - x ), Int.le_ceil ( a i - x ), Int.ceil_lt_add_one ( a i - x ), hab i ] );
    rw [ MeasureTheory.setIntegral_congr_set ] at h_integral_lt;
    any_goals exact Set.Ioo 0 1;
    · simp_all +decide;
      rw [ MeasureTheory.measureReal_def, MeasureTheory.measure_diff_null ] at h_integral_lt <;> norm_num at *;
      exact hBad.measure_zero MeasureTheory.MeasureSpace.volume;
    · rw [ MeasureTheory.ae_eq_set ] ; aesop;
      exact MeasureTheory.measure_mono_null ( fun x hx => hx.2 ) ( hBad.measure_zero MeasureTheory.MeasureSpace.volume )

/-
The total number of shifted lattice points inside the disjoint squares is at most k^2.
-/
lemma lattice_points_disjoint_sum (n : ℕ) (k : ℤ) (hk : 0 < k) (P : Packing n) (h_valid : P.is_valid)
  (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
  (h_avoid_x : ∀ i, ∀ z : ℤ, (k : ℝ) * (P i).x - x ≠ z ∧ (k : ℝ) * ((P i).x + (P i).s) - x ≠ z)
  (h_avoid_y : ∀ i, ∀ z : ℤ, (k : ℝ) * (P i).y - y ≠ z ∧ (k : ℝ) * ((P i).y + (P i).s) - y ≠ z) :
  ∑ i, num_points ((k : ℝ) * (P i).x) ((k : ℝ) * ((P i).x + (P i).s)) x * num_points ((k : ℝ) * (P i).y) ((k : ℝ) * ((P i).y + (P i).s)) y ≤ k^2 := by
    -- The sets $L \cap S_i$ are pairwise disjoint, so their union is a subset of $L \cap [0, k]^2$.
    have h_disjoint_union : ∀ i j, i ≠ j → Disjoint {p : ℤ × ℤ | ⌈k * (P i).x - x⌉ ≤ p.1 ∧ p.1 ≤ ⌊k * ((P i).x + (P i).s) - x⌋ ∧ ⌈k * (P i).y - y⌉ ≤ p.2 ∧ p.2 ≤ ⌊k * ((P i).y + (P i).s) - y⌋} {p : ℤ × ℤ | ⌈k * (P j).x - x⌉ ≤ p.1 ∧ p.1 ≤ ⌊k * ((P j).x + (P j).s) - x⌋ ∧ ⌈k * (P j).y - y⌉ ≤ p.2 ∧ p.2 ≤ ⌊k * ((P j).y + (P j).s) - y⌋} := by
      intro i j hij; rw [ Set.disjoint_left ] ; intros p hp hp'; have := h_valid i j hij; simp_all +decide [ Square.disjoint ] ;
      rcases this with ( h | h | h | h ) <;> simp_all +decide [ Int.ceil_le, Int.le_floor ];
      · exact h_avoid_x j ( p.1 : ℤ ) |>.1 ( by nlinarith [ ( by norm_cast : ( 0 :ℝ ) < k ) ] );
      · exact h_avoid_x i ( p.1 ) |>.1 ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] );
      · exact h_avoid_y j ( p.2 ) |>.1 ( by nlinarith [ ( by norm_cast : ( 0 :ℝ ) < k ) ] );
      · exact h_avoid_y j ( p.2 : ℤ ) |>.2 ( by nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ) ] );
    have h_union_subset : Finset.biUnion Finset.univ (fun i => Finset.product (Finset.Icc (⌈k * (P i).x - x⌉) (⌊k * ((P i).x + (P i).s) - x⌋)) (Finset.Icc (⌈k * (P i).y - y⌉) (⌊k * ((P i).y + (P i).s) - y⌋))) ⊆ Finset.product (Finset.Icc 0 (k - 1)) (Finset.Icc 0 (k - 1)) := by
      norm_num [ Finset.subset_iff ];
      intro a b i ha hb hc hd;
      norm_num [ Int.ceil_le, Int.le_floor ] at *;
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.le
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · apply Int.le_of_lt_add_one
        rw [← @Int.cast_lt ℝ]
        push_cast
        have hnonneg : 0 ≤ (k : ℝ) * (P i).x := mul_nonneg hk_nonneg (P i).x_nonneg
        nlinarith [ha, hx.2, hnonneg]
      · rw [← @Int.cast_lt ℝ]
        have hmul_le : (k : ℝ) * ((P i).x + (P i).s) ≤ (k : ℝ) := by
          calc
            (k : ℝ) * ((P i).x + (P i).s) ≤ (k : ℝ) * 1 := by
              exact mul_le_mul_of_nonneg_left (P i).x_plus_s_le_one hk_nonneg
            _ = (k : ℝ) := by ring
        nlinarith [hb, hx.1, hmul_le]
      · apply Int.le_of_lt_add_one
        rw [← @Int.cast_lt ℝ]
        push_cast
        have hnonneg : 0 ≤ (k : ℝ) * (P i).y := mul_nonneg hk_nonneg (P i).y_nonneg
        nlinarith [hc, hy.2, hnonneg]
      · rw [← @Int.cast_lt ℝ]
        have hmul_le : (k : ℝ) * ((P i).y + (P i).s) ≤ (k : ℝ) := by
          calc
            (k : ℝ) * ((P i).y + (P i).s) ≤ (k : ℝ) * 1 := by
              exact mul_le_mul_of_nonneg_left (P i).y_plus_s_le_one hk_nonneg
            _ = (k : ℝ) := by ring
        nlinarith [hd, hy.1, hmul_le]
    have h_card_union : Finset.card (Finset.biUnion Finset.univ (fun i => Finset.product (Finset.Icc (⌈k * (P i).x - x⌉) (⌊k * ((P i).x + (P i).s) - x⌋)) (Finset.Icc (⌈k * (P i).y - y⌉) (⌊k * ((P i).y + (P i).s) - y⌋)))) = ∑ i : Fin n, (⌊k * ((P i).x + (P i).s) - x⌋ - ⌈k * (P i).x - x⌉ + 1) * (⌊k * ((P i).y + (P i).s) - y⌋ - ⌈k * (P i).y - y⌉ + 1) := by
      rw [ Finset.card_biUnion ];
      · norm_num [ Finset.card_product ];
        refine Finset.sum_congr rfl fun i _ => ?_;
        rw [ max_eq_left, max_eq_left ];
        · ring;
        · simp +zetaDelta at *;
          exact Int.ceil_le.mpr ( by norm_num; linarith [ show ( k : ℝ ) * ( P i |> Square.s ) ≥ 0 by exact mul_nonneg ( by exact_mod_cast hk.le ) ( P i |> Square.s_nonneg ), Int.floor_le ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y ), Int.lt_floor_add_one ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y ) ] );
        · norm_num [ Int.le_floor, Int.ceil_le ];
          nlinarith [ Int.lt_floor_add_one ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) - x ), show ( k : ℝ ) ≥ 1 by exact_mod_cast hk, show ( P i |> Square.x ) ≥ 0 by exact_mod_cast ( P i |> Square.x_nonneg ), show ( P i |> Square.s ) ≥ 0 by exact_mod_cast ( P i |> Square.s_nonneg ) ];
      · intros i hi j hj hij;
        convert h_disjoint_union i j hij using 1;
        simp +decide [ Finset.disjoint_left, Set.disjoint_left ];
    have := Finset.card_mono h_union_subset; simp_all +decide [ Finset.product ] ;
    nlinarith [ Int.toNat_of_nonneg hk.le, show ∑ i : Fin n, ( ⌊ ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) - x⌋ - ⌈ ( k : ℝ ) * ( P i |> Square.x ) - x⌉ + 1 ) * ( ⌊ ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y⌋ - ⌈ ( k : ℝ ) * ( P i |> Square.y ) - y⌉ + 1 ) = ∑ i : Fin n, num_points ( ( k : ℝ ) * ( P i |> Square.x ) ) ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) ) x * num_points ( ( k : ℝ ) * ( P i |> Square.y ) ) ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ) y from Finset.sum_congr rfl fun _ _ => by unfold num_points; ring ]

/-
If the shift x avoids the fractional parts of a and b, then num_points is either floor(b-a) or ceil(b-a).
-/
lemma num_points_bounds (a b x : ℝ) (hx : 0 ≤ x ∧ x < 1)
  (ha : Int.fract a ≠ x) (hb : Int.fract b ≠ x) :
  num_points a b x = ⌊b - a⌋ ∨ num_points a b x = ⌈b - a⌉ := by
    by_contra h_contra;
    -- Since `Int.fract a ≠ x` and `Int.fract b ≠ x`, `a - x` and `b - x` are not integers. Thus, `⌈a - x⌉ = ⌊a - x⌋ + 1`.
    have h_ceil_floor : ⌈a - x⌉ = ⌊a - x⌋ + 1 := by
      rw [ Int.ceil_eq_iff ] ; aesop;
      · refine lt_of_le_of_ne ( Int.floor_le (a - x) ) ?_;
        exact fun h => ha <| by linarith [ Int.fract_add_floor a, Int.fract_add_floor ( a - x ), show ( ⌊a⌋ : ℝ ) = ⌊a - x⌋ by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith [ Int.floor_le ( a - x ), Int.lt_floor_add_one ( a - x ) ], by linarith [ Int.floor_le ( a - x ), Int.lt_floor_add_one ( a - x ) ] ⟩ ] ;
      · linarith [ Int.lt_floor_add_one ( a - x ) ];
    unfold num_points at h_contra; simp_all +decide [ Int.ceil_eq_iff ] ;
    have h_floor : ⌊b - a⌋ ≤ ⌊b - x⌋ - ⌊a - x⌋ ∧ ⌊b - x⌋ - ⌊a - x⌋ ≤ ⌈b - a⌉ := by
      exact ⟨ Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast ; linarith [ Int.floor_le ( b - a ), Int.lt_floor_add_one ( b - a ), Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ), Int.floor_le ( a - x ), Int.lt_floor_add_one ( a - x ) ], Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast ; linarith [ Int.le_ceil ( b - a ), Int.ceil_lt_add_one ( b - a ), Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ), Int.floor_le ( a - x ), Int.lt_floor_add_one ( a - x ) ] ⟩;
    cases lt_or_gt_of_ne h_contra.1 <;> cases lt_or_gt_of_ne h_contra.2 <;> linarith [ Int.le_ceil ( b - a ), Int.ceil_le_floor_add_one ( b - a ) ]

/-
There exist integer counts p_i, q_i satisfying the geometric constraints, proven by choosing appropriate shifts x_0, y_0 avoiding bad sets.
-/
lemma key_geometric_lemma (n : ℕ) (k : ℤ) (hk : 0 < k) (P : Packing n) (h_valid : P.is_valid) :
    let D := fun i => (k : ℝ) * (P i).s
    ∃ (p q : Fin n → ℤ),
      (∀ i, 0 ≤ p i ∧ 0 ≤ q i) ∧
      (∀ i, |p i - q i| ≤ 1) ∧
      (∑ i, p i ≥ ⌈∑ i, D i⌉) ∧
      (∑ i, q i ≥ ⌈∑ i, D i⌉) ∧
      (∑ i, p i * q i ≤ k^2) := by
        simp +zetaDelta at *;
        have hk_nonneg : (0 : ℝ) ≤ k := by
          exact_mod_cast hk.le
        have num_points_nonneg (a b x : ℝ) (hab : a ≤ b) : 0 ≤ num_points a b x := by
          unfold num_points
          have hceil : ⌈a - x⌉ ≤ ⌊b - x⌋ + 1 := by
            exact Int.ceil_le.mpr (by
              have hfloor : b - x < (⌊b - x⌋ : ℤ) + 1 := Int.lt_floor_add_one (b - x)
              norm_num
              linarith)
          omega

        -- Define `BadX` as the set of fractional parts of $k x_i$ and $k(x_i+s_i)$, and similarly `BadY`.
        set BadX : Set ℝ := {Int.fract ((k : ℝ) * (P i).x) | i : Fin n} ∪ {Int.fract ((k : ℝ) * ((P i).x + (P i).s)) | i : Fin n}
        set BadY : Set ℝ := {Int.fract ((k : ℝ) * (P i).y) | i : Fin n} ∪ {Int.fract ((k : ℝ) * ((P i).y + (P i).s)) | i : Fin n};
        -- By `exists_shift_sum_ge`, we find $x_0 \in [0, 1) \setminus BadX$ such that $\sum p_i(x_0) \ge \sum D_i$.
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ Set.Ioo 0 1, x₀ ∉ BadX ∧ (∑ i, (num_points ((k : ℝ) * (P i).x) ((k : ℝ) * ((P i).x + (P i).s)) x₀ : ℝ)) ≥ ∑ i, ((k : ℝ) * (P i).s) := by
          -- By `exists_shift_sum_ge`, we find $x_0 \in [0, 1) \setminus BadX$ such that $\sum p_i(x_0) \ge \sum D_i$. Use this lemma.
          have := exists_shift_sum_ge n (fun i => (k : ℝ) * (P i).x) (fun i => (k : ℝ) * ((P i).x + (P i).s)) (fun i => by
            exact mul_le_mul_of_nonneg_left ( by linarith [ ( P i ).s_nonneg ] ) ( by positivity )) (BadX ∪ {0}) (by
          exact Set.Finite.union ( Set.Finite.union ( Set.toFinite ( Set.range fun i : Fin n => Int.fract ( ( k : ℝ ) * ( P i |> Square.x ) ) ) ) ( Set.toFinite ( Set.range fun i : Fin n => Int.fract ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) ) ) ) ) ( Set.finite_singleton 0 ));
          obtain ⟨x₀, hx₀₁, hx₀₂, hx₀₃, hx₀₄⟩ := this
          use x₀
          simp_all (config := { decide := Bool.true }) [mul_add]
          · exact lt_of_le_of_ne hx₀₁ (Ne.symm hx₀₃.1)
        -- Define p_i as the number of integer points in the shifted interval [kx_i - x₀, k(x_i+s_i) - x₀].
        set p : Fin n → ℤ := fun i => num_points ((k : ℝ) * (P i).x) ((k : ℝ) * ((P i).x + (P i).s)) x₀;
        -- By `exists_shift_sum_ge`, we find $y_0 \in [0, 1) \setminus BadY$ such that $\sum q_i(y_0) \ge \sum D_i$.
        obtain ⟨y₀, hy₀⟩ : ∃ y₀ ∈ Set.Ioo 0 1, y₀ ∉ BadY ∧ (∑ i, (num_points ((k : ℝ) * (P i).y) ((k : ℝ) * ((P i).y + (P i).s)) y₀ : ℝ)) ≥ ∑ i, ((k : ℝ) * (P i).s) := by
          norm_num +zetaDelta at *;
          have := exists_shift_sum_ge n ( fun i => ( k : ℝ ) * ( P i |> Square.y ) ) ( fun i => ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ) ( fun i => mul_le_mul_of_nonneg_left ( by linarith [ ( P i |> Square.s_nonneg ) ] ) (by exact_mod_cast hk.le) ) ( BadY ∪ { 0 } ) ?_;
          · obtain ⟨ y₀, hy₀₁, hy₀₂, hy₀₃, hy₀₄ ⟩ := this; use y₀; simp_all ( config := { decide := Bool.true } ) [ mul_add ] ;
            exact ⟨ lt_of_le_of_ne hy₀₁ ( Ne.symm hy₀₃.1 ), fun i hi => hy₀₃.2 <| Or.inl ⟨ i, hi ⟩, fun i hi => hy₀₃.2 <| Or.inr ⟨ i, by simpa [ mul_add ] using hi ⟩ ⟩;
          · exact Set.Finite.union ( Set.Finite.union ( Set.toFinite ( Set.range fun i => Int.fract ( ( k : ℝ ) * ( P i |> Square.y ) ) ) ) ( Set.toFinite ( Set.range fun i => Int.fract ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ) ) ) ) ( Set.finite_singleton 0 );
        -- Define q_i as the number of integer points in the shifted interval [ky_i - y₀, k(y_i+s_i) - y₀].
        set q : Fin n → ℤ := fun i => num_points ((k : ℝ) * (P i).y) ((k : ℝ) * ((P i).y + (P i).s)) y₀;
        refine ⟨ p, q, ?_, ?_, ?_, ?_, ?_ ⟩;
        · intro i
          constructor
          · unfold p
            apply num_points_nonneg
            exact mul_le_mul_of_nonneg_left (by linarith [(P i).s_nonneg]) hk_nonneg
          · unfold q
            apply num_points_nonneg
            exact mul_le_mul_of_nonneg_left (by linarith [(P i).s_nonneg]) hk_nonneg
        · -- By `num_points_bounds`, we know that $p_i \in \{\lfloor D_i \rfloor, \lceil D_i \rceil\}$ and $q_i \in \{\lfloor D_i \rfloor, \lceil D_i \rceil\}$.
          have hpq_bounds : ∀ i, (p i = ⌊(k : ℝ) * (P i).s⌋ ∨ p i = ⌈(k : ℝ) * (P i).s⌉) ∧
              (q i = ⌊(k : ℝ) * (P i).s⌋ ∨ q i = ⌈(k : ℝ) * (P i).s⌉) := by
            intro i
            constructor
            · unfold p
              have hbounds := num_points_bounds ((k : ℝ) * (P i).x) ((k : ℝ) * ((P i).x + (P i).s)) x₀
                ⟨hx₀.1.1.le, hx₀.1.2⟩
                (by
                  intro h
                  exact hx₀.2.1 (Or.inl ⟨i, h⟩))
                (by
                  intro h
                  exact hx₀.2.1 (Or.inr ⟨i, h⟩))
              convert hbounds using 1 <;> ring_nf
            · unfold q
              have hbounds := num_points_bounds ((k : ℝ) * (P i).y) ((k : ℝ) * ((P i).y + (P i).s)) y₀
                ⟨hy₀.1.1.le, hy₀.1.2⟩
                (by
                  intro h
                  exact hy₀.2.1 (Or.inl ⟨i, h⟩))
                (by
                  intro h
                  exact hy₀.2.1 (Or.inr ⟨i, h⟩))
              convert hbounds using 1 <;> ring_nf
          intro i
          rcases hpq_bounds i with ⟨hp, hq⟩
          rcases hp with hp_floor | hp_ceil <;> rcases hq with hq_floor | hq_ceil
          · have hp' : p i = ⌊(k : ℝ) * (P i).s⌋ := by simpa [eq_comm] using hp_floor
            have hq' : q i = ⌊(k : ℝ) * (P i).s⌋ := by simpa [eq_comm] using hq_floor
            rw [hp', hq']
            simp
          · have hp' : p i = ⌊(k : ℝ) * (P i).s⌋ := by simpa [eq_comm] using hp_floor
            have hq' : q i = ⌈(k : ℝ) * (P i).s⌉ := by simpa [eq_comm] using hq_ceil
            rw [hp', hq']
            have hfc : ⌊(k : ℝ) * (P i).s⌋ ≤ ⌈(k : ℝ) * (P i).s⌉ := Int.floor_le_ceil ((k : ℝ) * (P i).s)
            have hcf : ⌈(k : ℝ) * (P i).s⌉ ≤ ⌊(k : ℝ) * (P i).s⌋ + 1 := Int.ceil_le_floor_add_one ((k : ℝ) * (P i).s)
            exact abs_sub_le_iff.mpr ⟨by omega, by omega⟩
          · have hp' : p i = ⌈(k : ℝ) * (P i).s⌉ := by simpa [eq_comm] using hp_ceil
            have hq' : q i = ⌊(k : ℝ) * (P i).s⌋ := by simpa [eq_comm] using hq_floor
            rw [hp', hq']
            have hfc : ⌊(k : ℝ) * (P i).s⌋ ≤ ⌈(k : ℝ) * (P i).s⌉ := Int.floor_le_ceil ((k : ℝ) * (P i).s)
            have hcf : ⌈(k : ℝ) * (P i).s⌉ ≤ ⌊(k : ℝ) * (P i).s⌋ + 1 := Int.ceil_le_floor_add_one ((k : ℝ) * (P i).s)
            exact abs_sub_le_iff.mpr ⟨by omega, by omega⟩
          · have hp' : p i = ⌈(k : ℝ) * (P i).s⌉ := by simpa [eq_comm] using hp_ceil
            have hq' : q i = ⌈(k : ℝ) * (P i).s⌉ := by simpa [eq_comm] using hq_ceil
            rw [hp', hq']
            simp
        · exact Int.ceil_le.mpr ( mod_cast hx₀.2.2 );
        · exact Int.ceil_le.mpr ( mod_cast hy₀.2.2 );
        · convert lattice_points_disjoint_sum n k hk P h_valid x₀ y₀ ⟨ hx₀.1.1, hx₀.1.2 ⟩ ⟨ hy₀.1.1, hy₀.1.2 ⟩ _ _;
          · intro i z; constructor <;> intro h <;> simp_all +decide ;
            · exact hx₀.2.1 <| Or.inl ⟨ i, by linarith [ Int.fract_add_floor ( ( k : ℝ ) * ( P i |> Square.x ) ), show ( Int.floor ( ( k : ℝ ) * ( P i |> Square.x ) ) : ℝ ) = z by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith, by linarith ⟩ ] ⟩;
            · exact hx₀.2.1 <| Or.inr ⟨ i, by linarith [ Int.fract_add_floor ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) ), show ( ⌊ ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) ⌋ : ℝ ) = z by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith, by linarith ⟩ ] ⟩;
          · intro i z; constructor <;> intro h <;> simp_all ( config := { decide := Bool.true } ) [ sub_eq_iff_eq_add ] ;
            · exact hy₀.2.1 <| Or.inl ⟨ i, by linarith [ Int.fract_add_floor ( ( k : ℝ ) * ( P i |> Square.y ) ), show ( ⌊ ( k : ℝ ) * ( P i |> Square.y ) ⌋ : ℝ ) = z by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith, by linarith ⟩ ] ⟩;
            · exact hy₀.2.1 <| Or.inr ⟨ i, by linarith [ Int.fract_add_floor ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ), show ( Int.floor ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ) : ℝ ) = z by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith, by linarith ⟩ ] ⟩

/- For all k > 0, and c >= -k^2, g(k^2 + 2c + 1) <= k + c/k. -/
theorem baek_koizumi_ueoro (k c : ℤ) (hk : 0 < k) (hc : -k^2 ≤ c) : g (k ^ 2 + 2 * c + 1).toNat ≤ k + c / k := by
  -- If $k^2+2c+1 \ge 0$, then $n = k^2+2c+1$.
  by_cases h_pos : 0 ≤ k^2 + 2 * c + 1;
  · have h_sup : ∀ P : Packing (Int.toNat (k^2 + 2 * c + 1)), P.is_valid → P.total_side_length ≤ k + c / k := by
      intro P hP_valid
      obtain ⟨p, q, hpq⟩ := key_geometric_lemma (Int.toNat (k^2 + 2 * c + 1)) k hk P hP_valid
      have h_sum_le : (∑ i, p i * q i : ℝ) ≤ k^2 := by
        exact_mod_cast hpq.2.2.2.2
      have h_sum_le' : (∑ i, p i : ℝ) + (∑ i, q i : ℝ) ≤ k^2 + (Int.toNat (k^2 + 2 * c + 1)) := by
        have h_sum_le' : ∀ i, p i * q i ≥ p i + q i - 1 := by
          intro i; specialize hpq; have := hpq.2.1 i; rcases abs_le.mp this with ⟨ h₁, h₂ ⟩ ; rcases lt_trichotomy ( p i ) 0 with hi | hi | hi <;> rcases lt_trichotomy ( q i ) 0 with hj | hj | hj <;> nlinarith [ hpq.1 i ] ;
        have h_sum_le' : (∑ i, p i * q i : ℝ) ≥ (∑ i, (p i + q i - 1) : ℝ) := by
          exact Finset.sum_le_sum fun i _ => mod_cast h_sum_le' i;
        norm_num [ Finset.sum_add_distrib ] at * ; linarith
      have h_sum_le'' : (∑ i, p i : ℝ) ≥ ⌈∑ i, (k : ℝ) * (P i).s⌉ := by
        exact_mod_cast hpq.2.2.1
      have h_sum_le''' : (∑ i, q i : ℝ) ≥ ⌈∑ i, (k : ℝ) * (P i).s⌉ := by
        exact_mod_cast hpq.2.2.2.1
      have h_sum_le'''' : (∑ i, (k : ℝ) * (P i).s : ℝ) ≤ k^2 + c := by
        norm_cast at *;
        rw [ Int.toNat_of_nonneg h_pos ] at *;
        exact le_trans ( Int.le_ceil _ ) ( mod_cast by linarith )
      have h_sum_le''''' : (∑ i, (P i).s : ℝ) ≤ k + c / k := by
        rw [ add_div', le_div_iff₀ ] <;> first | positivity | simp_all +decide [ ← Finset.mul_sum _ _ _ ] ; linarith;
      exact h_sum_le''''';
    exact csSup_le ⟨ _, ⟨ fun _ => ⟨ 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num ⟩, by exact fun _ _ _ => by norm_num [ Square.disjoint ], rfl ⟩ ⟩ fun L hL => by aesop;
  · unfold g; aesop;
    rw [ show ( k ^ 2 + 2 * c + 1 |> Int.toNat ) = 0 by nlinarith [ Int.toNat_of_nonpos h_pos.le ] ];
    refine csSup_le ?_ ?_ <;> norm_num;
    · exact ⟨ 0, ⟨ fun _ => ⟨ 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num ⟩, by unfold Packing.is_valid; aesop ⟩ ⟩;
    · unfold Packing.total_side_length; aesop;
      rw [ add_div', le_div_iff₀ ] <;> norm_cast
      focus nlinarith
      linarith

/-

-/

/- If `x : Fin n → ℝ` is a sequence of `n` distinct positive real numbers
with total sum `1`, where `n = k^2 + 1 + 2a` for some `a ≤ k`, then there is
a nonempty monotone (nondecreasing or nonincreasing) subsequence whose sum
is at least `k / (k^2 + a)`.

We encode the subsequence via `s : Fin (m + 1) → Fin n`, which is strictly
increasing (`StrictMono s`) so it really picks a subsequence, and
`Fin (m + 1)` guarantees that the subsequence is nonempty. -/
noncomputable section AristotleLemmas

/-
Given a sequence `x` and bounds `S` and `T` on increasing/decreasing subsequence sums, we can construct a valid packing of squares with side lengths `x i / M` where `M` is an upper bound on `S` and `T`.
-/
lemma exists_packing_from_seq {n : ℕ} (x : Fin n → ℝ) (S T : Fin n → ℝ)
  (h_pos : ∀ i, 0 < x i)
  (h_inj : Function.Injective x)
  (hS_cond : ∀ i j, i < j → x i < x j → S j ≥ S i + x j)
  (hT_cond : ∀ i j, i < j → x i > x j → T j ≥ T i + x j)
  (hS_base : ∀ i, S i ≥ x i)
  (hT_base : ∀ i, T i ≥ x i)
  (M : ℝ) (hM_S : ∀ i, S i ≤ M) (hM_T : ∀ i, T i ≤ M) :
  ∃ P : Packing n, P.is_valid ∧ ∀ i, (P i).s = x i / M := by
    by_cases hM_pos : 0 < M
    · let P : Packing n := fun i =>
        { x := (S i - x i) / M
          y := (T i - x i) / M
          s := x i / M
          s_nonneg := by
            exact div_nonneg (le_of_lt (h_pos i)) (le_of_lt hM_pos)
          x_nonneg := by
            exact div_nonneg (sub_nonneg.mpr (hS_base i)) (le_of_lt hM_pos)
          y_nonneg := by
            exact div_nonneg (sub_nonneg.mpr (hT_base i)) (le_of_lt hM_pos)
          x_plus_s_le_one := by
            rw [← add_div, div_le_iff₀ hM_pos]
            linarith [hM_S i]
          y_plus_s_le_one := by
            rw [← add_div, div_le_iff₀ hM_pos]
            linarith [hM_T i] }
      refine ⟨P, ?_, ?_⟩
      · intro i j hij
        dsimp [P, Square.disjoint]
        rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
        · rcases lt_or_gt_of_ne (h_inj.ne hij) with hx_lt | hx_gt
          · exact Or.inl (by
              rw [← add_div, div_le_div_iff_of_pos_right hM_pos]
              linarith [hS_cond i j hij_lt hx_lt])
          · exact Or.inr <| Or.inr <| Or.inl <| by
              rw [← add_div, div_le_div_iff_of_pos_right hM_pos]
              linarith [hT_cond i j hij_lt hx_gt]
        · have hji_ne : j ≠ i := Ne.symm hij
          rcases lt_or_gt_of_ne (h_inj.ne hji_ne) with hxj_lt | hxj_gt
          · exact Or.inr <| Or.inl <| by
              rw [← add_div, div_le_div_iff_of_pos_right hM_pos]
              linarith [hS_cond j i hji_lt hxj_lt]
          · exact Or.inr <| Or.inr <| Or.inr <| by
              rw [← add_div, div_le_div_iff_of_pos_right hM_pos]
              linarith [hT_cond j i hji_lt hxj_gt]
      · intro i
        rfl
    · rcases n with _ | n
      · use fun _ => ⟨0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
        simp +decide [Packing.is_valid]
      · exfalso
        linarith [h_pos 0, hS_base 0, hM_S 0]

end AristotleLemmas

theorem exists_monotone_subseq_sum_ge_general
    (k n a : ℕ)
    (hk : 0 < k)
    (ha_le : a ≤ k)
    (hn : n = k^2 + 1 + 2 * a)
    (x : Fin n → ℝ)
    (h_pos : ∀ i, 0 < x i)
    (h_inj : Function.Injective x)
    (h_sum : ∑ i, x i = (1 : ℝ)) :
    ∃ (m : ℕ) (s : Fin (m + 1) → Fin n),
      StrictMono s ∧
      (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) ∧
      (∑ i, x (s i)) ≥
        (k : ℝ) / ((k^2 + a : ℕ) : ℝ) := by
  by_contra h_contra;

  have h_all_lt_target : ∀ m : ℕ, ∀ s : Fin (m + 1) → Fin n, StrictMono s → (Monotone (x ∘ s) ∨ Antitone (x ∘ s)) → (∑ i, x (s i)) < k / (k^2 + a : ℝ) := by
    aesop;

  obtain ⟨S, hS⟩ := exists_max_increasing_subseq_sum x
  obtain ⟨T, hT⟩ := exists_max_decreasing_subseq_sum x
  set M := max (sSup (Set.range S)) (sSup (Set.range T)) with hM_def
  have hM_lt_target : M < k / (k^2 + a : ℝ) := by
    have hM_lt_target : ∀ i, S i < k / (k^2 + a : ℝ) ∧ T i < k / (k^2 + a : ℝ) := by
      intros i
      obtain ⟨m, s, hs_mono, hs_monotone, hs_last, hs_sum⟩ := hS.left i
      obtain ⟨m', s', hs'_mono, hs'_antitone, hs'_last, hs'_sum⟩ := hT.left i;
      exact ⟨ hs_sum ▸ h_all_lt_target m s hs_mono ( Or.inl hs_monotone ), hs'_sum ▸ h_all_lt_target m' s' hs'_mono ( Or.inr hs'_antitone ) ⟩;
    rcases n <;> aesop;
    ·
      have hS_finite : Set.Finite (Set.range S) := by
        exact Set.toFinite _;
      have := hS_finite.isCompact.sSup_mem;
      exact this ⟨ _, Set.mem_range_self 0 ⟩ |> fun ⟨ i, hi ⟩ => hi ▸ hM_lt_target i |>.1;
    ·
      have h_range_finite : Set.Finite (Set.range T) := by
        exact Set.toFinite _;
      have := h_range_finite.isCompact.sSup_mem;
      exact this ⟨ _, Set.mem_range_self 0 ⟩ |> fun ⟨ i, hi ⟩ => hi ▸ hM_lt_target i |>.2;

  obtain ⟨P, hP_valid, hP_side_lengths⟩ : ∃ P : Packing n, P.is_valid ∧ ∀ i, (P i).s = x i / M := by
    apply exists_packing_from_seq;
    any_goals tauto;
    · exact fun i => le_max_of_le_left <| le_csSup ( Set.finite_range S |> Set.Finite.bddAbove ) <| Set.mem_range_self i;
    · exact fun i => le_max_of_le_right <| le_csSup ( Set.finite_range T |> Set.Finite.bddAbove ) <| Set.mem_range_self i;

  have hL_le_g : (∑ i, (P i).s) ≤ g n := by
    refine le_csSup ?_ ?_;
    · refine ⟨ n, fun L hL => ?_ ⟩ ; aesop;
      exact le_trans ( Finset.sum_le_sum fun _ _ => show ( w _ |> Square.s ) ≤ 1 from by linarith [ w ‹_› |> Square.s_nonneg, w ‹_› |> Square.x_nonneg, w ‹_› |> Square.y_nonneg, w ‹_› |> Square.x_plus_s_le_one, w ‹_› |> Square.y_plus_s_le_one ] ) ( by norm_num );
    · exact ⟨ P, hP_valid, rfl ⟩
  have hg_le_k_plus_a_div_k : g n ≤ k + a / k := by
    have := baek_koizumi_ueoro k a;
    convert this ( by positivity ) ( by nlinarith ) using 1 ; norm_cast ; ring_nf;
    exact hn ▸ by ring_nf;

  have h_one_div_target : 1 / (k / (k^2 + a : ℝ)) = k + a / k := by
    field_simp;

  have h_one_div_M_gt_one_div_target : 1 / M > 1 / (k / (k^2 + a : ℝ)) := by
    gcongr;
    exact lt_max_of_lt_left ( lt_of_lt_of_le ( h_pos ⟨ 0, by nlinarith ⟩ ) ( le_csSup ( Set.finite_range S |> Set.Finite.bddAbove ) ( Set.mem_range_self _ ) |> le_trans ( hS.2.2 _ ) ) );
  have h_sum_side_lengths : (∑ i, (P i).s) = ∑ i, x i / M := by
    simp [hP_side_lengths]
  have h_one_div_M_le_g : 1 / M ≤ g n := by
    calc
      1 / M = (∑ i, x i) / M := by rw [h_sum]
      _ = ∑ i, x i / M := by rw [Finset.sum_div]
      _ = ∑ i, (P i).s := by rw [h_sum_side_lengths]
      _ ≤ g n := hL_le_g
  have h_one_div_M_le_target : 1 / M ≤ 1 / (k / (k^2 + a : ℝ)) := by
    rw [h_one_div_target]
    exact le_trans h_one_div_M_le_g hg_le_k_plus_a_div_k
  linarith

lemma sorted_sublist_of_subset_fin {n : ℕ} : ∀ {l₂ : List (Fin n)},
    List.Sorted (· < ·) l₂ → ∀ {l₁ : List (Fin n)},
    List.Sorted (· < ·) l₁ → (∀ x ∈ l₁, x ∈ l₂) → List.Sublist l₁ l₂ := by
  intro l₂
  induction l₂ with
  | nil =>
      intro h₂ l₁ h₁ hmem
      cases l₁ with
      | nil => exact List.Sublist.slnil
      | cons x xs =>
          have : x ∈ ([] : List (Fin n)) := hmem x (by simp)
          cases this
  | cons y ys ih =>
      intro h₂ l₁ h₁ hmem
      cases l₁ with
      | nil => exact List.nil_sublist (y :: ys)
      | cons x xs =>
          have hxmem : x = y ∨ x ∈ ys := by
            have := hmem x (by simp)
            simpa using this
          rcases hxmem with hxy | hxys
          · subst x
            apply List.Sublist.cons₂
            apply ih (List.Pairwise.tail h₂)
            · exact List.Pairwise.tail h₁
            · intro z hz
              have hzmem : z = y ∨ z ∈ ys := by
                have := hmem z (by simp [hz])
                simpa using this
              rcases hzmem with hzy | hzys
              · subst z
                have hylt : y < y := (List.pairwise_cons.mp h₁).1 y hz
                exact (lt_irrefl y hylt).elim
              · exact hzys
          · apply List.Sublist.cons
            apply ih (List.Pairwise.tail h₂)
            · exact h₁
            · intro z hz
              have hzmem : z = y ∨ z ∈ ys := by
                have := hmem z hz
                simpa using this
              rcases hzmem with hzy | hzys
              · rcases (show z = x ∨ z ∈ xs from by simpa using hz) with hz_eq_x | hz_in_xs
                · have hy_eq_x : y = x := hzy.symm.trans hz_eq_x
                  have hyx : y < x := (List.pairwise_cons.mp h₂).1 x hxys
                  have hxx : x < x := hy_eq_x ▸ hyx
                  exact (lt_irrefl x hxx).elim
                · have hy_in_xs : y ∈ xs := by simpa [hzy] using hz_in_xs
                  have hyx : y < x := (List.pairwise_cons.mp h₂).1 x hxys
                  have hxy : x < y := (List.pairwise_cons.mp h₁).1 y hy_in_xs
                  exact (lt_asymm hxy hyx).elim
              · exact hzys

lemma sublist_finRange_of_strictMono {n m : ℕ} (s : Fin (m + 1) → Fin n) (hs : StrictMono s) :
    List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange n) := by
  apply sorted_sublist_of_subset_fin
  · simp +decide [List.Sorted]
    rw [List.pairwise_iff_get]
    aesop
  · rw [List.Sorted]
    rw [List.pairwise_map, List.pairwise_iff_get]
    intro i j hij
    exact hs (by simpa using hij)
  · intro x hx
    simp

lemma sum_subseq_le_Mp {n : ℕ} (L : List ℝ) (hL_len : L.length = n) (hL_pairwise : L.Pairwise (· ≠ ·))
  (m : ℕ) (s : Fin (m+1) → Fin n) (hs : StrictMono s)
  (hmono : Monotone (fun i => L.get ⟨(s i : ℕ), by rw [hL_len]; exact (s i).isLt⟩) ∨ Antitone (fun i => L.get ⟨(s i : ℕ), by rw [hL_len]; exact (s i).isLt⟩)) :
  ∑ i, L.get ⟨(s i : ℕ), by rw [hL_len]; exact (s i).isLt⟩ ≤ Mp L := by
  let sL : Fin (m + 1) → Fin L.length := fun i => ⟨(s i : ℕ), by rw [hL_len]; exact (s i).isLt⟩
  let sub : List ℝ := (List.finRange (m + 1)).map (fun i => L.get (sL i))
  have hsL : StrictMono sL := by
    intro i j hij
    exact hs hij
  have h_idx_sub : List.Sublist (List.map (fun i => sL i) (List.finRange (m + 1))) (List.finRange L.length) :=
    sublist_finRange_of_strictMono sL hsL
  have h_sublist : List.Sublist sub L := by
    unfold sub
    simpa [List.map_map, sL, List.map_get_finRange L] using h_idx_sub.map (fun i => L.get i)
  have h_sum_eq : sub.sum = ∑ i, L.get (sL i) := by
    unfold sub
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have h_sorted : List.Sorted (· < ·) sub ∨ List.Sorted (· > ·) sub := by
    rcases hmono with hinc | hdec
    · left
      unfold sub
      rw [List.Sorted, List.pairwise_map]
      rw [List.pairwise_iff_get]
      intro i j hij
      have hle : L.get (sL ((List.finRange (m + 1)).get i)) ≤ L.get (sL ((List.finRange (m + 1)).get j)) := hinc (by simpa using hij.le)
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hpair := List.pairwise_iff_get.mp hL_pairwise (sL ((List.finRange (m + 1)).get i)) (sL ((List.finRange (m + 1)).get j)) (hsL (by simpa using hij))
      exact hpair heq
    · right
      unfold sub
      rw [List.Sorted, List.pairwise_map]
      rw [List.pairwise_iff_get]
      intro i j hij
      have hle : L.get (sL ((List.finRange (m + 1)).get j)) ≤ L.get (sL ((List.finRange (m + 1)).get i)) := hdec (by simpa using hij.le)
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hpair := List.pairwise_iff_get.mp hL_pairwise (sL ((List.finRange (m + 1)).get i)) (sL ((List.finRange (m + 1)).get j)) (hsL (by simpa using hij))
      exact hpair heq.symm
  have hmem : sub.sum ∈ ((L.sublists.filter (fun s => Decidable.decide (List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s))).map List.sum) := by
    refine List.mem_map.mpr ?_
    refine ⟨sub, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨by simpa [List.mem_sublists] using h_sublist, by simpa using h_sorted⟩
  have hle : sub.sum ≤ Mp L := by
    unfold Mp
    let xs : List ℝ := List.map List.sum (List.filter (fun s => decide (List.Sorted (fun x1 x2 => x1 < x2) s ∨ List.Sorted (fun x1 x2 => x2 < x1) s)) L.sublists)
    have hmem' : sub.sum ∈ xs := by simpa [xs] using hmem
    change sub.sum ≤ xs.maximum.getD 0
    cases hm : xs.maximum with
    | bot =>
        have hxempty : xs = [] := by
          simpa [List.maximum] using (List.argmax_eq_none.mp hm)
        simp [hxempty] at hmem'
    | coe mx =>
        exact List.le_maximum_of_mem hmem' hm
  rw [← h_sum_eq]
  exact hle

lemma exists_seq_of_cp_le {n : ℕ} {K : ℝ} (hn : n ≠ 0) (h : cp n ≤ K) :
  ∀ ε > 0, ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧
  (∀ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s →
    (Monotone (x ∘ s) ∨ Antitone (x ∘ s)) →
    ∑ i, x (s i) ≤ K + ε) := by
  intro ε ε_pos
  obtain ⟨L, hL_len, hL_nodup, hL_pos, hL_ratio⟩ :
      ∃ L : List ℝ, L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ Mp L / L.sum < K + ε := by
    unfold cp at h
    have hlt : sInf { r | ∃ L : List ℝ, L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ r = Mp L / L.sum } < K + ε :=
      lt_of_le_of_lt h (lt_add_of_pos_right K ε_pos)
    rcases exists_lt_of_csInf_lt (show { r : ℝ | ∃ L : List ℝ, L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ r = Mp L / L.sum }.Nonempty from by
      refine ⟨Mp (List.map (fun i : ℕ => (i : ℝ) + 1) (List.range n)) / (List.map (fun i : ℕ => (i : ℝ) + 1) (List.range n)).sum, ?_⟩
      refine ⟨List.map (fun i : ℕ => (i : ℝ) + 1) (List.range n), by simp, ?_, ?_, rfl⟩
      · exact List.Nodup.map (by
          intro a b hab
          norm_num at hab ⊢
          exact_mod_cast hab) List.nodup_range
      · intro x hx
        rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
        positivity) hlt with ⟨r, ⟨L, hL_len, hL_nodup, hL_pos, rfl⟩, hL_ratio⟩
    exact ⟨L, hL_len, hL_nodup, hL_pos, hL_ratio⟩
  subst n
  have hL_ne : L ≠ [] := by
    intro hnil
    apply hn
    simp [hnil]
  have hsum_pos : 0 < L.sum := List.sum_pos L hL_pos hL_ne
  let x : Fin L.length → ℝ := fun i => L.get i / L.sum
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact div_pos (hL_pos (L.get i) (List.get_mem _ _)) hsum_pos
  · intro i j hij
    have hget : L.get i = L.get j := (div_left_inj' (ne_of_gt hsum_pos)).mp hij
    exact List.nodup_iff_injective_get.mp hL_nodup hget
  · change (∑ i : Fin L.length, L.get i / L.sum) = 1
    rw [← Finset.sum_div]
    rw [← List.sum_ofFn]
    rw [List.ofFn_eq_map, List.map_get_finRange]
    exact div_self (ne_of_gt hsum_pos)
  · intro m s hs hmono
    have hraw_mono : Monotone (fun i => L.get (s i)) ∨ Antitone (fun i => L.get (s i)) := by
      rcases hmono with hinc | hdec
      · left
        intro i j hij
        exact (div_le_div_iff_of_pos_right hsum_pos).mp (hinc hij)
      · right
        intro i j hij
        exact (div_le_div_iff_of_pos_right hsum_pos).mp (hdec hij)
    have hraw_le : ∑ i, L.get (s i) ≤ Mp L :=
      sum_subseq_le_Mp L rfl hL_nodup m s hs hraw_mono
    change (∑ i, L.get (s i) / L.sum) ≤ K + ε
    rw [← Finset.sum_div]
    exact le_trans (div_le_div_of_nonneg_right hraw_le (le_of_lt hsum_pos)) hL_ratio.le

/-- Approximate sharpness of the bound `k / (k^2 + a)` in the case of a nonnegative
integer `a`. -/
theorem exists_seq_with_monotone_subseq_sum_le_general_nonneg
    (k n : ℕ) (a : ℤ)
    (hk : 0 < k)
    (ha_low : 0 ≤ a)
    (ha_high : a ≤ k)
    (hn : (n : ℤ) = (k : ℤ) ^ 2 + 1 + 2 * a) :
    ∀ ε > (0 : ℝ),
      ∃ (x : Fin n → ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∑ i, x i = (1 : ℝ)) ∧
        (∀ (m : ℕ) (s : Fin (m + 1) → Fin n),
          StrictMono s →
          (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
          (∑ i, x (s i)) ≤
            ε + (k : ℝ) / ((k : ℝ) ^ 2 + (a : ℝ))) := by
  intro ε hε_pos
  have hn_ne : n ≠ 0 := by
    intro hn0
    have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
    have hsq : (0 : ℤ) < (k : ℤ)^2 := sq_pos_of_ne_zero (by omega)
    have hnonneg : (0 : ℤ) ≤ 2 * a := by nlinarith
    have hpos : (0 : ℤ) < (k : ℤ)^2 + 1 + 2 * a := by nlinarith
    omega
  have hlen : k^2 + 2 * a.natAbs + 1 = n := by
    have hcast : ((k^2 + 2 * a.natAbs + 1 : ℕ) : ℤ) = (n : ℤ) := by
      norm_num [Int.natAbs_of_nonneg ha_low]
      rw [hn]
      ring
    exact_mod_cast hcast
  have ha_abs_le : a.natAbs ≤ k := by
    have hcast : (a.natAbs : ℤ) ≤ (k : ℤ) := by
      rw [Int.natAbs_of_nonneg ha_low]
      exact ha_high
    exact_mod_cast hcast
  have hcp_abs : cp n ≤ (k : ℝ) / ((k : ℝ)^2 + (a.natAbs : ℝ)) := by
    rw [← hlen]
    simpa [pow_two] using main_theorem k a.natAbs (Nat.succ_le_of_lt hk) ha_abs_le
  have hcp : cp n ≤ (k : ℝ) / ((k : ℝ)^2 + (a : ℝ)) := by
    have ha_cast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
      rw [show ((a.natAbs : ℕ) : ℝ) = (|a| : ℝ) by norm_num]
      rw [abs_of_nonneg]
      exact_mod_cast ha_low
    simpa [ha_cast] using hcp_abs
  simpa [Function.comp, add_comm, add_left_comm, add_assoc] using
    exists_seq_of_cp_le hn_ne hcp ε hε_pos

/- Approximate sharpness of the bound `k / (k^2 + a)` in the case of a negative
integer `a` with `-(k : ℤ) ≤ a < -1`.

If `(n : ℤ) = (k : ℤ)^2 + 1 + 2 * a` with `-(k : ℤ) ≤ a < -1`, then for every `ε > 0`
there exists a sequence `x : Fin n → ℝ` of `n` distinct positive real numbers with
total sum `1` such that every nonempty monotone (nondecreasing or nonincreasing)
subsequence has sum at most `ε + k / (k^2 + a)` (interpreted in `ℝ` as
`(k : ℝ) / ((k : ℝ)^2 + (a : ℝ))`).

Subsequences are encoded by strictly increasing maps `s : Fin (m + 1) → Fin n`;
`StrictMono s` ensures we have a genuine subsequence, and `Fin (m + 1)` ensures
the subsequence is nonempty. -/
noncomputable section AristotleLemmas

lemma sum_subseq_le_M_of_monotone {n : ℕ} (L : List ℝ) (hL_len : L.length = n)
  (hL_pairwise : L.Pairwise (· ≠ ·))
  (m : ℕ) (s : Fin (m + 1) → Fin n) (hs : StrictMono s)
  (h_mono : Monotone (fun i => L.get ⟨s i, by rw [hL_len]; exact (s i).isLt⟩) ∨
            Antitone (fun i => L.get ⟨s i, by rw [hL_len]; exact (s i).isLt⟩)) :
  ∑ i, L.get ⟨s i, by rw [hL_len]; exact (s i).isLt⟩ ≤ M L := by
  have hle_mp :
      ∑ i, L.get ⟨(s i : ℕ), by rw [hL_len]; exact (s i).isLt⟩ ≤ Mp L :=
    sum_subseq_le_Mp L hL_len hL_pairwise m s hs (by
      simpa only using h_mono)
  have hMp : Mp L = M L := by
    rw [M_eq_max]
    rfl
  exact le_trans (by simpa only using hle_mp) hMp.le

lemma exists_seq_of_c_le {n : ℕ} {K : ℝ} (hn : n ≠ 0) (h : c n ≤ K) :
  ∀ ε > 0, ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧
  (∀ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s →
    (Monotone (x ∘ s) ∨ Antitone (x ∘ s)) →
    ∑ i, x (s i) ≤ K + ε) := by
  intro ε ε_pos
  obtain ⟨L, hL_len, hL_pairwise, hL_pos, hL_ratio⟩ :
      ∃ L : List ℝ, L.length = n ∧ L.Pairwise (· ≠ ·) ∧
        (∀ x ∈ L, 0 < x) ∧ M L / L.sum < K + ε := by
    unfold c at h
    have hlt : sInf (c_set n) < K + ε :=
      lt_of_le_of_lt h (lt_add_of_pos_right K ε_pos)
    rcases exists_lt_of_csInf_lt (show (c_set n).Nonempty from by
      refine ⟨M (List.map (fun i : ℕ => (i : ℝ) + 1) (List.range n)) /
          (List.map (fun i : ℕ => (i : ℝ) + 1) (List.range n)).sum, ?_⟩
      refine ⟨List.map (fun i : ℕ => (i : ℝ) + 1) (List.range n), by simp, ?_, ?_, rfl⟩
      · rw [List.pairwise_map]
        refine List.Pairwise.imp ?_ List.pairwise_lt_range
        intro a b hab hne
        norm_num at hne
        exact Nat.ne_of_lt hab hne
      · intro x hx
        rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
        positivity) hlt with ⟨r, ⟨L, hL_len, hL_pairwise, hL_pos, rfl⟩, hL_ratio⟩
    exact ⟨L, hL_len, hL_pairwise, hL_pos, hL_ratio⟩
  subst n
  have hL_ne : L ≠ [] := by
    intro hnil
    apply hn
    simp [hnil]
  have hsum_pos : 0 < L.sum := List.sum_pos L hL_pos hL_ne
  let x : Fin L.length → ℝ := fun i => L.get i / L.sum
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact div_pos (hL_pos (L.get i) (List.get_mem _ _)) hsum_pos
  · intro i j hij
    have hget : L.get i = L.get j := (div_left_inj' (ne_of_gt hsum_pos)).mp hij
    by_contra hne
    have hpair_get := (List.pairwise_iff_get.mp hL_pairwise)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hpair_get i j hlt) hget
    · exact (hpair_get j i hgt) hget.symm
  · change (∑ i : Fin L.length, L.get i / L.sum) = 1
    rw [← Finset.sum_div]
    rw [← List.sum_ofFn]
    rw [List.ofFn_eq_map, List.map_get_finRange]
    exact div_self (ne_of_gt hsum_pos)
  · intro m s hs hmono
    have hraw_mono :
        Monotone (fun i => L.get (s i)) ∨
          Antitone (fun i => L.get (s i)) := by
      rcases hmono with hinc | hdec
      · left
        intro i j hij
        exact (div_le_div_iff_of_pos_right hsum_pos).mp (hinc hij)
      · right
        intro i j hij
        exact (div_le_div_iff_of_pos_right hsum_pos).mp (hdec hij)
    have hraw_le :
        ∑ i, L.get (s i) ≤ M L :=
      sum_subseq_le_M_of_monotone L rfl hL_pairwise m s hs hraw_mono
    change (∑ i, L.get (s i) / L.sum) ≤ K + ε
    rw [← Finset.sum_div]
    exact le_trans (div_le_div_of_nonneg_right hraw_le (le_of_lt hsum_pos)) hL_ratio.le

end AristotleLemmas

theorem exists_seq_with_monotone_subseq_sum_le_general_neg
    (k n : ℕ) (a : ℤ)
    (hk : 0 < k)
    (ha_low : -(k : ℤ) ≤ a)
    (ha_high : a < -1)
    (hn : (n : ℤ) = (k : ℤ) ^ 2 + 1 + 2 * a) :
    ∀ ε > (0 : ℝ),
      ∃ (x : Fin n → ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∑ i, x i = (1 : ℝ)) ∧
        (∀ (m : ℕ) (s : Fin (m + 1) → Fin n),
          StrictMono s →
          (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
          (∑ i, x (s i)) ≤
            ε + (k : ℝ) / ((k : ℝ) ^ 2 + (a : ℝ))) := by
  intro ε hε_pos;
  convert exists_seq_of_c_le _ _ ε hε_pos using 1;
  any_goals exact ( k : ℝ ) / ( k ^ 2 + a );
  · ac_rfl;
  · nlinarith;
  · convert thm_main_v2 k a _ _ _ using 1 <;> norm_cast;
    grind

noncomputable section AristotleLemmas

/-
Given sequences S and T satisfying the recurrence relations for increasing and decreasing subsequences, we can construct a valid packing of squares.
-/
lemma valid_packing_of_recurrence {n : ℕ} (x : Fin n → ℝ) (S T : Fin n → ℝ) (B : ℝ)
  (h_pos : ∀ i, 0 < x i)
  (h_inj : Function.Injective x)
  (hB_pos : 0 < B)
  (hS_rec : ∀ i j, i < j → x i < x j → S j ≥ S i + x j)
  (hT_rec : ∀ i j, i < j → x i > x j → T j ≥ T i + x j)
  (hS_base : ∀ i, S i ≥ x i)
  (hT_base : ∀ i, T i ≥ x i)
  (hS_bound : ∀ i, S i ≤ B)
  (hT_bound : ∀ i, T i ≤ B) :
  ∃ (P : Packing n), P.is_valid ∧ P.total_side_length = (∑ i, x i) / B := by
    -- Define the side length of each square in the packing.
    set s : Fin n → ℝ := fun i => x i / B;
    -- Define the bottom-left corner of each square in the packing.
    set P : Fin n → Square := fun i => ⟨(S i - x i) / B, (T i - x i) / B, s i, by
      exact div_nonneg ( le_of_lt ( h_pos i ) ) hB_pos.le, by
      exact div_nonneg ( sub_nonneg.2 ( hS_base i ) ) hB_pos.le, by
      exact div_nonneg ( sub_nonneg_of_le ( hT_base i ) ) hB_pos.le, by
      rw [ ← add_div, div_le_iff₀ ] <;> linarith [ hS_base i, hT_base i, hS_bound i, hT_bound i, h_pos i ], by
      rw [ ← add_div, div_le_iff₀ ] <;> linarith [ h_pos i, hB_pos, hT_base i, hT_bound i ]⟩
    generalize_proofs at *;
    -- Show that the packing P is valid.
    have hP_valid : ∀ i j, i ≠ j → (P i).disjoint (P j) := by
      intro i j hij; cases lt_or_gt_of_ne hij <;> cases lt_or_gt_of_ne ( h_inj.ne hij ) <;> simp +decide [ *, Square.disjoint ] ;
      · simp +zetaDelta at *;
        field_simp;
        exact Or.inl ( by linarith [ hS_rec i j ‹_› ‹_› ] );
      · aesop;
        exact Or.inr <| Or.inr <| Or.inl <| by have := hT_rec i j h h_1; ring_nf at *; nlinarith [ inv_pos.mpr hB_pos, mul_inv_cancel₀ hB_pos.ne', h_pos i, h_pos j, hS_base i, hS_base j, hT_base i, hT_base j, hS_bound i, hS_bound j, hT_bound i, hT_bound j ] ;
      · aesop;
        exact Or.inr <| Or.inr <| Or.inr <| by have := hT_rec _ _ h h_1; nlinarith [ h_pos i, h_pos j, hS_base i, hS_base j, hT_base i, hT_base j, hS_bound i, hS_bound j, hT_bound i, hT_bound j, div_mul_cancel₀ ( S j - x j ) hB_pos.ne', div_mul_cancel₀ ( T j - x j ) hB_pos.ne', div_mul_cancel₀ ( S i - x i ) hB_pos.ne', div_mul_cancel₀ ( T i - x i ) hB_pos.ne', div_mul_cancel₀ ( x j ) hB_pos.ne', div_mul_cancel₀ ( x i ) hB_pos.ne' ] ;
      · aesop;
        contrapose! hS_rec;
        exact ⟨ j, i, h, h_1, by nlinarith [ h_pos j, h_pos i, hS_base j, hS_base i, hT_base j, hT_base i, hS_bound j, hS_bound i, hT_bound j, hT_bound i, mul_div_cancel₀ ( S j - x j ) hB_pos.ne', mul_div_cancel₀ ( S i - x i ) hB_pos.ne', mul_div_cancel₀ ( x i ) hB_pos.ne', mul_div_cancel₀ ( x j ) hB_pos.ne' ] ⟩;
    exact ⟨ P, hP_valid, by rw [ Finset.sum_div _ _ _ ] ; rfl ⟩

theorem g_gt_inv_of_strict_bound
    (n : ℕ) (hn : n ≠ 0)
    (x : Fin n → ℝ)
    (h_pos : ∀ i, 0 < x i)
    (h_inj : Function.Injective x)
    (h_sum : ∑ i, x i = 1)
    (B : ℝ)
    (hB_pos : 0 < B)
    (h_strict : ∀ (m : ℕ) (s : Fin (m + 1) → Fin n),
      StrictMono s →
      (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
      (∑ i, x (s i)) < B) :
    g n > 1 / B := by
      -- Use `exists_max_increasing_subseq_sum` to get `S` and `exists_max_decreasing_subseq_sum` to get `T`.
      obtain ⟨S, hS⟩ := exists_max_increasing_subseq_sum x
      obtain ⟨T, hT⟩ := exists_max_decreasing_subseq_sum x
      have hS_lt_B : ∀ i, S i < B := by
        intro i; obtain ⟨ m, s, hs₁, hs₂, hs₃, hs₄ ⟩ := hS.1 i; specialize h_strict m s hs₁; aesop;
      have hT_lt_B : ∀ i, T i < B := by
        intro i; specialize hT; obtain ⟨ m, s, hs₁, hs₂, hs₃, hs₄ ⟩ := hT.1 i; specialize h_strict m s hs₁; aesop;
      -- Let's choose B' = max (max_i S i, max_i T i)
      obtain ⟨B', hB'_def⟩ : ∃ B' : ℝ, (∀ i, S i ≤ B') ∧ (∀ i, T i ≤ B') ∧ B' < B := by
        have h_max_exists : ∃ M, M ∈ Set.range S ∪ Set.range T ∧ ∀ y ∈ Set.range S ∪ Set.range T, y ≤ M := by
          apply_rules [ IsCompact.exists_isGreatest, CompactIccSpace.isCompact_Icc ];
          · exact Set.Finite.isCompact ( Set.toFinite _ );
          · exact ⟨ _, Set.mem_union_left _ <| Set.mem_range_self ⟨ 0, Nat.pos_of_ne_zero hn ⟩ ⟩;
        grind;
      have h_valid_packing : ∃ P : Packing n, P.is_valid ∧ P.total_side_length = 1 / B' := by
        have := valid_packing_of_recurrence x S T B' h_pos h_inj;
        simpa only [ h_sum ] using this ( lt_of_lt_of_le ( h_pos ⟨ 0, Nat.pos_of_ne_zero hn ⟩ ) ( hS.2.2 _ |> le_trans <| hB'_def.1 _ ) ) hS.2.1 hT.2.1 hS.2.2 hT.2.2 hB'_def.1 hB'_def.2.1;
      have h_g_ge_1_div_B' : ∀ P : Packing n, P.is_valid → P.total_side_length ≤ g n := by
        exact fun P hP => le_csSup ( by exact ⟨ ∑ i, ( 1 : ℝ ), by rintro x ⟨ Q, hQ, rfl ⟩ ; exact Finset.sum_le_sum fun i _ => show ( Q i |> Square.s ) ≤ 1 from by linarith [ Q i |> Square.x_nonneg, Q i |> Square.y_nonneg, Q i |> Square.x_plus_s_le_one, Q i |> Square.y_plus_s_le_one ] ⟩ ) ⟨ P, hP, rfl ⟩;
      aesop;
      exact lt_of_lt_of_le ( inv_strictAnti₀ ( show 0 < B' from lt_of_lt_of_le ( h_pos ⟨ 0, Nat.pos_of_ne_zero hn ⟩ ) ( right _ |> le_trans <| left_2 _ ) ) right_2 ) ( right_3 ▸ h_g_ge_1_div_B' _ left_6 )

end AristotleLemmas

theorem exists_monotone_subseq_sum_ge_general_range
    (k n : ℕ) (a : ℤ)
    (hk : 0 < k)
    (ha_low : -k ≤ a)
    (ha_high : a ≤ k)
    (hn : (n : ℤ) = (k : ℤ) ^ 2 + 1 + 2 * a)
    (x : Fin n → ℝ)
    (h_pos : ∀ i, 0 < x i)
    (h_inj : Function.Injective x)
    (h_sum : ∑ i, x i = (1 : ℝ)) :
    ∃ (m : ℕ) (s : Fin (m + 1) → Fin n),
      StrictMono s ∧
      (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) ∧
      (∑ i, x (s i)) ≥
        (k : ℝ) / ((k^2 + a) : ℝ) := by
  have h1 : (k : ℤ) ^ 2 + a ≥ 0 := by
    nlinarith only [ ha_low, ha_high, hk ];
  by_contra h_contra;
  have h2 : g n > 1 / ((k : ℝ) / ((k : ℝ) ^ 2 + a)) := by
    apply g_gt_inv_of_strict_bound n (by
    aesop) x h_pos h_inj h_sum ((k : ℝ) / ((k : ℝ) ^ 2 + a)) (by
    by_cases h_eq : k^2 + a = 0;
    · norm_num [ show a = -k ^ 2 by linarith ] at *;
      norm_num [ show k = 1 by nlinarith only [ hk, ha_low ] ] at *;
      aesop;
    · exact div_pos ( by positivity ) ( by norm_cast; positivity ));
    exact fun m s hs hs' => lt_of_not_ge fun h => h_contra ⟨ m, s, hs, hs', h ⟩;
  have h3 : g n ≤ (k : ℝ) + a / k := by
    convert baek_koizumi_ueoro k ( a : ℤ ) ( mod_cast hk ) ( by linarith ) using 1;
    grind;
  rw [ div_div_eq_mul_div, gt_iff_lt, div_lt_iff₀ ] at h2 <;> nlinarith [ ( by norm_cast : ( 0 :ℝ ) < k ), mul_div_cancel₀ ( a :ℝ ) ( by positivity : ( k :ℝ ) ≠ 0 ), ( by norm_cast : ( -k :ℝ ) ≤ a ), ( by norm_cast : ( a :ℝ ) ≤ k ), ( by norm_cast : ( k :ℝ ) ^ 2 + a ≥ 0 ) ]

/-- Approximate sharpness of the bound `k / (k^2 + a)` in the case of `a` in a range. -/
theorem exists_seq_with_monotone_subseq_sum_le_general_range
    (k n : ℕ) (a : ℤ)
    (hk : 0 < k)
    (ha_low : -k < a)
    (ha_high : a ≤ k)
    (hn : (n : ℤ) = (k : ℤ) ^ 2 + 1 + 2 * a) :
    ∀ ε > (0 : ℝ),
      ∃ (x : Fin n → ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∑ i, x i = (1 : ℝ)) ∧
        (∀ (m : ℕ) (s : Fin (m + 1) → Fin n),
          StrictMono s →
          (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) →
          (∑ i, x (s i)) ≤
            ε + (k : ℝ) / ((k : ℝ) ^ 2 + (a : ℝ))) := by
  by_cases ha : a = -1 ∨ -k < a ∧ a < -1 ∨ 0 ≤ a ∧ a ≤ k;
  · rcases ha with ( rfl | ⟨ ha₁, ha₂ ⟩ | ⟨ ha₁, ha₂ ⟩ );
    · intro ε hε_pos;
      simp +zetaDelta at *;
      convert exists_seq_with_monotone_subseq_sum_le_minus_one k (k ^ 2 - 1) _ _ _ _ using 1;
      any_goals trivial;
      rw [ show n = k ^ 2 - 1 by exact eq_tsub_of_add_eq <| by linarith ] ; norm_num [ Nat.cast_sub <| show 1 ≤ k ^ 2 from by nlinarith ] ;
      ring_nf;
    · apply_rules [ exists_seq_with_monotone_subseq_sum_le_general_neg ];
      linarith;
    · convert exists_seq_with_monotone_subseq_sum_le_general_nonneg k n ( Int.toNat a ) hk ( by linarith [ Int.toNat_of_nonneg ha₁ ] ) _ using 1;
      · aesop;
      · linarith [ Int.toNat_of_nonneg ha₁ ];
  · grind


/-
FINAL THEOREM STATEMENTS AND RESULTS
-/

/-- A (not-necessarily-longest) monotone subsequence of `x` is given by
strictly increasing indices `s`, and the values are either `Monotone` or `Antitone`. -/
noncomputable def IsMonotoneSubseq {n : ℕ} (x : Fin n → ℝ) (m : ℕ) (s : Fin (m + 1) → Fin n) : Prop :=
  StrictMono s ∧
    (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i)))

/-- The set of all possible sums of monotone subsequences of `x`. -/
noncomputable def monoSubseqSumSet {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  { r | ∃ (m : ℕ) (s : Fin (m + 1) → Fin n),
      IsMonotoneSubseq x m s ∧ r = ∑ i, x (s i) }

/-- The maximal (supremal) sum of a monotone subsequence of `x`. -/
noncomputable def maxMonoSubseqSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (monoSubseqSumSet x)

/-- The score of a sequence is:
(max sum of a monotone subsequence) / (sum of all entries). -/
noncomputable def score {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  maxMonoSubseqSum x / (∑ i, x i)

/-- `c(n)` is the infimum of the scores over all sequences `x : Fin n → ℝ`
with distinct positive entries (distinctness expressed as `Injective`). -/
noncomputable def c_opt (n : ℕ) : ℝ :=
  sInf { r : ℝ |
    ∃ (x : Fin n → ℝ),
      (∀ i, 0 < x i) ∧
      Function.Injective x ∧
      r = score x }

theorem c_opt_eq_k_div_sq_add_a
    (k n : ℕ) (a : ℤ)
    (hk : 1 < k)
    (ha_low : -k < a)
    (ha_high : a ≤ k)
    (hn : (n : ℤ) = k^2 + 1 + 2 * a) :
    c_opt n = (k : ℝ) / (k^2 + a) := by
      refine le_antisymm ?_ ?_;
      · -- By `exists_seq_with_monotone_subseq_sum_le_general_range`, there exists a sequence $x$ with score ≤ K + ε for any ε > 0.
        have h_exists_seq : ∀ ε > 0, ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧ score x ≤ (k : ℝ) / ((k : ℝ) ^ 2 + a) + ε := by
          intro ε hε_pos;
          have := exists_seq_with_monotone_subseq_sum_le_general_range k n a ( by linarith ) ( by linarith ) ( by linarith ) hn ε hε_pos;
          obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := this; use x; unfold score; aesop;
          refine csSup_le ?_ ?_;
          · let s0 : Fin (0 + 1) → Fin n :=
              fun _ => ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩
            refine ⟨ ∑ i, x (s0 i), ⟨ 0, s0, ?_, rfl ⟩ ⟩;
            exact ⟨ by simp +decide [ StrictMono ], Or.inl <| by simp +decide [ Monotone ] ⟩;
          · rintro _ ⟨ m, s, ⟨ hs₁, hs₂ ⟩, rfl ⟩ ; linarith [ hx₄ m s hs₁ hs₂ ] ;
        refine le_of_forall_pos_le_add ?_;
        intro ε hε; obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := h_exists_seq ε hε; exact le_trans ( csInf_le ⟨ 0, by rintro _ ⟨ y, hy₁, hy₂, rfl ⟩ ; exact div_nonneg ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ m, s, hs₁, hs₂, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => le_of_lt ( hy₁ _ ) ) ( Finset.sum_nonneg fun _ _ => le_of_lt ( hy₁ _ ) ) ⟩ ⟨ x, hx₁, hx₂, rfl ⟩ ) ( by simpa [ hx₃ ] using hx₄ ) ;
      · -- By definition of $c_{opt}$, we know that for any sequence $x$ of $n$ distinct positive real numbers, $\text{score}(x) \geq \frac{k}{k^2 + a}$.
        have h_score_ge : ∀ x : Fin n → ℝ, (∀ i, 0 < x i) → Function.Injective x → (maxMonoSubseqSum x) / (∑ i, x i) ≥ (k : ℝ) / ((k^2 + a) : ℝ) := by
          intro x hx_pos hx_inj
          set y := fun i => x i / (∑ i, x i) with hy_def
          have hy_sum : ∑ i, y i = 1 := by
            rw [ ← Finset.sum_div, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ ⟨ 0, by nlinarith ⟩, Finset.mem_univ _ ⟩ ]
          have hy_pos : ∀ i, 0 < y i := by
            exact fun i => div_pos ( hx_pos i ) ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ i, Finset.mem_univ _ ⟩ )
          have hy_inj : Function.Injective y := by
            exact fun i j hij => hx_inj <| by rw [ div_eq_div_iff ] at hij <;> nlinarith [ hx_pos i, hx_pos j, Finset.single_le_sum ( fun i _ => le_of_lt ( hx_pos i ) ) ( Finset.mem_univ i ), Finset.single_le_sum ( fun i _ => le_of_lt ( hx_pos i ) ) ( Finset.mem_univ j ) ] ;
          have h_monotone_subseq : ∃ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s ∧ (Monotone (fun i => y (s i)) ∨ Antitone (fun i => y (s i))) ∧ (∑ i, y (s i)) ≥ (k : ℝ) / ((k^2 + a) : ℝ) := by
            convert exists_monotone_subseq_sum_ge_general_range k n a ( by linarith ) ( by linarith ) ( by linarith ) hn y hy_pos hy_inj hy_sum using 1
          obtain ⟨m, s, hs_mono, hs_monotone, hs_sum⟩ := h_monotone_subseq
          have h_monotone_subseq_x : ∃ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s ∧ (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) ∧ (∑ i, x (s i)) ≥ (k : ℝ) / ((k^2 + a) : ℝ) * (∑ i, x i) := by
            use m, s;
            refine ⟨ hs_mono, ?_, ?_ ⟩;
            · exact Or.imp ( fun h => fun i j hij => by have := h hij; rw [ div_le_div_iff_of_pos_right ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ s i, Finset.mem_univ _ ⟩ ) ] at this; linarith ) ( fun h => fun i j hij => by have := h hij; rw [ div_le_div_iff_of_pos_right ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ s i, Finset.mem_univ _ ⟩ ) ] at this; linarith ) hs_monotone;
            · rw [ ← Finset.sum_div _ _ _ ] at * ; rw [ ge_iff_le, le_div_iff₀ ] at * <;> linarith [ Finset.sum_pos ( fun i _ => hx_pos i ) ⟨ ⟨ 0, Nat.pos_of_ne_zero <| by aesop_cat ⟩, Finset.mem_univ _ ⟩ ] ;
          obtain ⟨m, s, hs_mono, hs_monotone, hs_sum⟩ := h_monotone_subseq_x
          have h_max_mono_subseq_sum : maxMonoSubseqSum x ≥ (k : ℝ) / ((k^2 + a) : ℝ) * (∑ i, x i) := by
            refine le_trans hs_sum ( le_csSup ?_ ?_ );
            · refine ⟨ ∑ i, x i, ?_ ⟩;
              rintro _ ⟨ m, s, hs_mono, rfl ⟩;
              have h_sum_le : ∑ i ∈ Finset.image s Finset.univ, x i ≤ ∑ i, x i := by
                exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => le_of_lt ( hx_pos _ );
              rwa [ Finset.sum_image <| by intros i hi j hj hij; exact hs_mono.1.injective hij ] at h_sum_le;
            · exact ⟨ m, s, ⟨ hs_mono, hs_monotone ⟩, rfl ⟩
          have h_score_ge : (maxMonoSubseqSum x) / (∑ i, x i) ≥ (k : ℝ) / ((k^2 + a) : ℝ) := by
            exact le_div_iff₀ ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Finset.mem_univ _ ⟩ ) |>.2 h_max_mono_subseq_sum
          exact h_score_ge;
        refine le_csInf ?_ ?_ <;> aesop;
        let x0 : Fin n → ℝ := fun i => (i : ℝ) + 1
        refine ⟨ score x0, ⟨ x0, ?_, ?_, rfl ⟩ ⟩;
        · intro i
          simp [x0]
          positivity
        · intro i j h
          simp [x0] at h
          exact Fin.ext (by exact_mod_cast h)

#print axioms c_opt_eq_k_div_sq_add_a
-- 'Erdos1026.c_opt_eq_k_div_sq_add_a' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1026
