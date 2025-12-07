/-
This was proven by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

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
      simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
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
      refine' ⟨ S, _, _, fun i => _ ⟩;
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
            · exact False.elim <| hij.not_le <| Fin.le_last _;
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
            · refine' ⟨ ∑ i, |x i|, fun s hs => _ ⟩ ; aesop;
              have h_sum_le : ∑ j : Fin (w + 1), x (w_1 j) ≤ ∑ i ∈ Finset.image w_1 Finset.univ, |x i| := by
                rw [ Finset.sum_image <| by intros i hi j hj hij; exact left.injective hij ];
                exact Finset.sum_le_sum fun _ _ => le_abs_self _;
              exact h_sum_le.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.image_subset_iff.mpr fun i _ => Finset.mem_univ _ ) fun _ _ _ => abs_nonneg _ );
            · exact ⟨ m', s'', hs''_mono, hs''_monotone, hs''_last, rfl ⟩;
          linarith;
        -- Since $S_i$ is the supremum of the set, we have $S_i \leq S_j - x_j$.
        have h_Si_le_Sj_minus_xj : S i ≤ S j - x j := by
          refine' csSup_le _ _ <;> norm_num;
          · exact ⟨ _, ⟨ 0, fun _ => i, by simp +decide [ StrictMono ], by simp +decide [ Monotone ], by simp +decide, rfl ⟩ ⟩;
          · exact fun b m s' hs' hs'' hs''' hb => by linarith [ h_sum_ge _ ⟨ m, s', hs', hs'', hs''', hb ⟩ ] ;
        linarith;
      · refine' le_csSup _ _;
        · refine' ⟨ ∑ j : Fin n, |x j|, fun s hs => _ ⟩ ; aesop;
          refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ ( Finset.image w_1 Finset.univ ) ) fun _ _ _ => abs_nonneg _ );
          rw [ Finset.sum_image <| by intros i hi j hj hij; exact left.injective hij ] ; exact Finset.sum_le_sum fun i _ => le_abs_self _;
        · exact ⟨ 0, fun _ => i, by simp +decide [ StrictMono ], by simp +decide [ Monotone ], by simp +decide, by simp +decide ⟩

set_option maxHeartbeats 0 in
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
      refine' ⟨ T, _, _, _ ⟩ <;> aesop;
      · obtain ⟨ m, s, hs₁, hs₂, hs₃, hs₄ ⟩ := hT₁ i;
        refine' le_trans _ ( hT₂ j ( m + 1 ) ( Fin.snoc s j ) _ _ _ );
        · simp +decide [ Fin.sum_univ_castSucc, hs₄ ];
        · intro i j hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> aesop;
          · exact False.elim <| hij.not_le <| Fin.le_last _;
          · exact lt_of_le_of_lt ( hs₁.monotone ( Fin.le_last _ ) ) a;
        · intro i j hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> aesop;
          exact le_trans a_1.le ( hs₂ <| Fin.le_last _ );
        · simp +decide [ Fin.snoc ];
      · specialize hT₁ i ; aesop;
        specialize hT₂ ( w_1 ( Fin.last w ) ) 0 ( fun _ => w_1 ( Fin.last w ) ) ; aesop;
        exact hT₂ ( by simp ( config := { decide := Bool.true } ) [ StrictMono ] ) ( by simp ( config := { decide := Bool.true } ) [ Antitone ] )

set_option maxHeartbeats 0 in
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
    refine' ⟨ S_max, hS_max.1, T_max, hT_max.1, hS_max.2, hT_max.2, _ ⟩;
    rwa [ ENNReal.toReal_ofReal ( show 0 ≤ S_max by obtain ⟨ i, hi ⟩ := hS_max.2; linarith [ h_pos i, hS_base i ] ), ENNReal.toReal_ofReal ( show 0 ≤ T_max by obtain ⟨ i, hi ⟩ := hT_max.2; linarith [ h_pos i, hT_base i ] ) ] at h_total_area_le

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
    refine' ⟨ 0, fun _ => 0, by simp +decide, Or.inl <| fun _ _ _ => by simp +decide, by simp +decide [ h_sum ] ⟩;
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
      push_neg at h_contra;
      exact h_max_gt.not_le ( by convert mul_le_mul h_contra.1 h_contra.2 ( show 0 ≤ T_max by obtain ⟨ i, rfl ⟩ := hT_max_eq; exact le_trans ( le_of_lt ( h_pos i ) ) ( hT.2.2 i ) ) ( show 0 ≤ ( 1 : ℝ ) / k by positivity ) using 1 ; ring );
    rcases h_max_gt with h | h;
    · obtain ⟨ i, hi ⟩ := hS_max_eq;
      -- Since $S i = S_max$ and $S_max > 1/k$, there exists an increasing subsequence ending at $i$ with sum $S i$.
      obtain ⟨m, s, hs_mono, hs_monotone, hs_last, hs_sum⟩ := hS.left i;
      exact ⟨ m, s, hs_mono, Or.inl hs_monotone, by linarith [ hS_max i ] ⟩;
    · rcases hT_max_eq with ⟨ i, rfl ⟩;
      rcases hT.1 i with ⟨ m, s, hs₁, hs₂, hs₃, hs₄ ⟩ ; exact ⟨ m, s, hs₁, Or.inr hs₂, by linarith ⟩
