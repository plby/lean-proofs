/-

This is a Lean formalization of a solution to Erdős Problem 1026.
https://www.erdosproblems.com/1026

See the following blog post for the story behind this solution:
https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/

The original problem of Erdős was unclear.  A collaborative process of
Desmond Weisenberg, Stijn Cambie, and Wouter van Doorn clarified the
question and was accepted by Thomas Bloom on erdosproblems.com.
Later, this statement was found in a survey of J. Michael Steele.

A later collaborative process of Boris Alexeev, Aristotle (from
Harmonic), KoishiChan, Terence Tao, AlphaProof (from Google DeepMind),
and Lawrence Wu together with prior literature of Jineon Baek,
Junnosuke Koizumi, and Takahiro Ueoro (and Iwan Praton and Adam Zsolt
Wagner) solved the problem.

The problem is a generalization of the Erdős–Szekeres theorem,
especially of its proof by Abraham Seidenberg.

Aristotle from Harmonic generated all of the formal proofs.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib


set_option maxHeartbeats 0

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
      · -- Since $s$ is strictly monotone, for any $p < q$, $s p < s q$. Now, if $es\_seq k \circ s$ is monotone, then for $p < q$, $es\_seq k (s p) \leq es\_seq k (s q)$.
        have h_diff : ∀ p q : Fin (n + 1), p < q → es_seq k (s p) < es_seq k (s q) := by
          have h_diff : ∀ p q : Fin (n + 1), p < q → es_seq k (s p) ≠ es_seq k (s q) := by
            intro p q hpq; intro h; have := es_seq_injective k hk; have := this h; aesop;
            exact hpq.ne ( hs.injective this );
          -- Since es_seq k is injective, if es_seq k (s p) ≤ es_seq k (s q) and they are not equal, then it must be that es_seq k (s p) < es_seq k (s q).
          intros p q hpq
          have h_le : es_seq k (s p) ≤ es_seq k (s q) := by
            exact ‹Monotone ( es_seq k ∘ s ) › hpq.le;
          exact lt_of_le_of_ne h_le ( h_diff p q hpq );
        -- Since $(s p).val \% k$ is strictly increasing and lies within $\{0, 1, ..., k-1\}$, the number of distinct values is exactly $n + 1$.
        have h_distinct : Finset.card (Finset.image (fun p : Fin (n + 1) => (s p).val % k) Finset.univ) = n + 1 := by
          rw [ Finset.card_image_of_injective _ _, Finset.card_fin ];
          intros p q hpq;
          cases lt_trichotomy p q <;> aesop;
          · have := h_diff p q h_1; unfold es_seq at this; aesop;
            exact absurd this ( not_lt_of_ge ( Nat.sub_le_sub_left ( Nat.div_le_div_right <| le_of_lt <| hs h_1 ) _ ) );
          · have := h_diff _ _ h_3; simp_all +decide [ es_seq ] ;
            exact False.elim <| this.not_le <| Nat.sub_le_sub_left ( Nat.div_le_div_right <| le_of_lt <| hs h_3 ) _;
        exact h_distinct ▸ le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun p _ => Finset.mem_range.mpr ( Nat.mod_lt _ hk ) ) ) ( by simpa );
      · -- Let's denote the sequence $u_i = i.val / k$ and $v_i = i.val % k$.
        set u : Fin (k ^ 2) → ℕ := fun i => i.val / k
        set v : Fin (k ^ 2) → ℕ := fun i => i.val % k;
        -- Since $s$ is strictly monotone, for $p < q$, we have $u_{s_p} \le u_{s_q}$.
        have h_u_mono : ∀ p q : Fin (n + 1), p < q → u (s p) < u (s q) := by
          intros p q hpq
          have h_u_lt : u (s p) ≤ u (s q) := by
            exact Nat.div_le_div_right ( le_of_lt ( hs hpq ) );
          cases eq_or_lt_of_le h_u_lt <;> aesop;
          have := h hpq.le; unfold es_seq at this; aesop;
          have := hs hpq; ( have := Nat.mod_add_div ( s p ) k; have := Nat.mod_add_div ( s q ) k; aesop; );
          grind +ring;
        -- Since $u (s p)$ is strictly increasing and takes values in $\{0, 1, ..., k-1\}$, the number of distinct values it can take is at most $k$.
        have h_u_distinct : Finset.card (Finset.image (fun p => u (s p)) Finset.univ) ≤ k := by
          exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun p _ => Finset.mem_range.mpr <| Nat.div_lt_of_lt_mul <| by nlinarith [ Fin.is_lt ( s p ) ] ) ( by simpa );
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
          exact?;
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

set_option maxHeartbeats 0 in
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
  set δ := ε / k with hδ
  set y_fun := fun i : Fin (k^2) => 1 + δ * (es_seq k i : ℝ) with hy_fun
  set S := ∑ i : Fin (k^2), y_fun i with hS
  set x_fun := fun i : Fin (k^2) => y_fun i / S with hx_fun
  have hS_pos : 0 < S := by
    exact Finset.sum_pos ( fun _ _ => add_pos_of_pos_of_nonneg zero_lt_one <| mul_nonneg ( div_nonneg hεpos.le <| Nat.cast_nonneg _ ) <| Nat.cast_nonneg _ ) ⟨ ⟨ 0, by positivity ⟩, Finset.mem_univ _ ⟩
  use x_fun
  simp [x_fun];
  refine' ⟨ _, _, _, _ ⟩;
  · exact fun i => div_pos ( add_pos_of_pos_of_nonneg zero_lt_one ( mul_nonneg ( div_nonneg hεpos.le ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) ) hS_pos;
  · -- By definition of y_fun, if y_fun i = y_fun j, then 1 + δ * (es_seq k i) = 1 + δ * (es_seq k j).
    intro i j hij
    have h_eq : 1 + δ * (es_seq k i : ℝ) = 1 + δ * (es_seq k j : ℝ) := by
      rw [ div_eq_div_iff ] at hij <;> nlinarith [ show 0 < S from hS_pos ];
    have := es_seq_injective k hk; aesop;
  · rw [ ← Finset.sum_div, div_self hS_pos.ne' ];
  · intro n s hs h_mono
    have h_sum_bound : ∑ i : Fin (n + 1), y_fun (s i) ≤ k + δ * k * (k^2 - 1) := by
      -- Since $s$ is monotone, the length of $s$ is at most $k$.
      have h_monotone_length : (n + 1) ≤ k := by
        -- Since $s$ is a monotone subsequence of the Erdos-Szekeres sequence, its length is at most $k$.
        have h_monotone_length : ∀ n : ℕ, ∀ s : Fin (n + 1) → Fin (k^2), StrictMono s → ((Monotone (fun i => es_seq k (s i))) ∨ (Antitone (fun i => es_seq k (s i)))) → n + 1 ≤ k := by
          exact?;
        apply h_monotone_length n s hs;
        simp_all +decide [ Monotone, Antitone, div_le_div_iff_of_pos_right, hS_pos ];
      have h_sum_bound : ∀ i, y_fun (s i) ≤ 1 + δ * (k^2 - 1) := by
        -- Since $es\_seq k i \leq k^2 - 1$ for all $i$, we have $y\_fun (s i) \leq 1 + \delta * (k^2 - 1)$.
        have h_es_seq_bound : ∀ i : Fin (k^2), es_seq k i ≤ k^2 - 1 := by
          intro i; unfold es_seq; aesop;
          · exact le_tsub_of_add_le_left ( by nlinarith only [ Nat.mod_lt ( i : ℕ ) hk, Nat.sub_le ( k - 1 ) ( ( i : ℕ ) / k ), Nat.div_mul_le_self ( i : ℕ ) k, Nat.sub_add_cancel hk ] );
          · exact le_tsub_of_add_le_left ( by nlinarith only [ Nat.mod_lt ( i : ℕ ) hk, Nat.div_add_mod ( i : ℕ ) k, Nat.sub_add_cancel ( show 1 ≤ k from hk ), Nat.sub_add_cancel ( show ( i : ℕ ) / k ≤ k - 1 from Nat.le_sub_one_of_lt ( Nat.div_lt_of_lt_mul <| by nlinarith only [ Fin.is_lt i, hk ] ) ) ] );
        exact fun i => add_le_add_left ( mul_le_mul_of_nonneg_left ( le_tsub_of_add_le_right <| by norm_cast; linarith [ h_es_seq_bound ( s i ), Nat.sub_add_cancel <| show 1 ≤ k ^ 2 from pow_pos hk 2 ] ) <| by positivity ) _;
      refine le_trans ( Finset.sum_le_sum fun _ _ => h_sum_bound _ ) ?_;
      norm_num;
      nlinarith only [ show ( n : ℝ ) + 1 ≤ k by norm_cast, show ( 0 : ℝ ) ≤ δ * ( k ^ 2 - 1 ) by exact mul_nonneg ( div_nonneg hεpos.le ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( by norm_cast; nlinarith ) ) ];
    -- Since $S = k^2 + \delta \frac{k^2(k^2-1)}{2}$, we can bound the ratio.
    have h_ratio_bound : S ≥ k^2 := by
      exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => le_add_of_nonneg_right <| mul_nonneg ( div_nonneg hεpos.le <| Nat.cast_nonneg _ ) <| Nat.cast_nonneg _ );
    rw [ ← Finset.sum_div _ _ _, div_le_iff₀ ] <;> try positivity;
    field_simp;
    rw [ show δ = ε / k from rfl ] at h_sum_bound;
    norm_num [ hk.ne' ] at *;
    nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, mul_le_mul_of_nonneg_left ( show ( k : ℝ ) ≥ 1 by norm_cast ) hεpos.le ]

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
  obtain ⟨x, hx_pos, hx_inj, hx_sum, hx_bound⟩ : ∃ (x : Fin (k ^ 2) → ℝ), (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧ (∀ m : ℕ, (∀ s : Fin (m + 1) → Fin (k ^ 2), StrictMono s → (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i))) → (∑ i, x (s i)) ≤ ε / 2 + (1 : ℝ) / (k : ℝ))) := by
    apply exists_seq_with_monotone_subseq_sum_le k (by linarith) (ε / 2) (half_pos hε_pos);
  -- Let's choose the smallest element of `x` and call it `x_min`.
  obtain ⟨i_min, hi_min⟩ : ∃ i_min : Fin (k ^ 2), ∀ i : Fin (k ^ 2), x i ≥ x i_min := by
    simpa using Finset.exists_min_image Finset.univ ( fun i => x i ) ⟨ ⟨ 0, by positivity ⟩, Finset.mem_univ _ ⟩;
  -- Remove the smallest element `x_min` from `x` and scale the remaining elements to maintain the sum equal to 1.
  set x' : Fin (k ^ 2 - 1) → ℝ := fun i => x (Finset.erase Finset.univ i_min |>.orderEmbOfFin (by
  simp ( config := { decide := Bool.true } ) [ Finset.card_erase_of_mem ( Finset.mem_univ i_min ) ]) i) / (1 - x i_min) with hx'
  generalize_proofs at *;
  refine' ⟨ fun i => x' ( hn ▸ i ), _, _, _, _ ⟩;
  · exact fun i => div_pos ( hx_pos _ ) ( sub_pos.mpr ( hx_sum ▸ by rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i_min ) ] ; exact lt_add_of_pos_right _ ( Finset.sum_pos ( fun i _ => hx_pos i ) <| Finset.card_pos.mp <| by simpa [ Finset.card_sdiff, * ] using by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ k ^ 2 from by nlinarith ) ] ) ) );
  · intro i j hij; aesop
    all_goals generalize_proofs at *;
    rw [ div_eq_div_iff ] at hij <;> norm_num at *;
    · exact Classical.not_not.1 fun hi => absurd ( hij.resolve_right ( by linarith [ hx_pos i_min, hi_min i_min, show x i_min < 1 from by rw [ ← hx_sum ] ; rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i_min ) ] ; exact lt_add_of_pos_right _ <| Finset.sum_pos ( fun i hi => hx_pos i ) <| Finset.card_pos.1 <| by simpa [ Finset.card_sdiff, * ] using by nlinarith [ Nat.sub_add_cancel <| show 1 ≤ k ^ 2 from by nlinarith ] ] ) ) ( hx_inj.ne <| by aesop );
    · rw [ sub_eq_zero, eq_comm ];
      rw [ ← hx_sum, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i_min ) ];
      exact ne_of_lt ( lt_add_of_pos_right _ ( Finset.sum_pos ( fun _ _ => hx_pos _ ) <| Finset.card_pos.mp <| by simpa [ Finset.card_sdiff ] using by nlinarith [ Nat.sub_add_cancel <| show 1 ≤ k ^ 2 from by nlinarith ] ) );
    · rw [ sub_eq_zero, eq_comm ];
      rw [ ← hx_sum, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i_min ) ];
      exact ne_of_lt ( lt_add_of_pos_right _ ( Finset.sum_pos ( fun _ _ => hx_pos _ ) <| Finset.card_pos.mp <| by simpa [ Finset.card_sdiff ] using by nlinarith [ Nat.sub_add_cancel <| show 1 ≤ k ^ 2 from by nlinarith ] ) );
  · have h_sum_x'_eq_one : ∑ i : Fin (k ^ 2 - 1), x' i = (∑ i ∈ Finset.univ.erase i_min, x i) / (1 - x i_min) := by
      norm_num +zetaDelta at *;
      rw [ ← Finset.sum_div _ _ _, ← Finset.sum_erase_add _ _ ( Finset.mem_univ i_min ), add_tsub_cancel_right ];
      rw [ ← Finset.sum_image ];
      · rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.mem_coe.mpr <| Finset.orderEmbOfFin_mem _ _ _ ) <| by simp ( config := { decide := Bool.true } ) [ Finset.card_image_of_injective _ <| show Function.Injective ( fun i : Fin ( k ^ 2 - 1 ) => ( Finset.univ.erase i_min |> Finset.orderEmbOfFin <| by aesop ) i ) from fun i j hij => by simpa [ Fin.ext_iff ] using hij ] ];
      · exact fun i _ j _ hij => by simpa [ Fin.ext_iff ] using hij;
    aesop;
    exact div_self <| ne_of_gt <| sub_pos_of_lt <| hx_sum ▸ by rw [ Finset.sum_eq_add_sum_diff_singleton <| Finset.mem_univ i_min ] ; exact lt_add_of_pos_right _ <| Finset.sum_pos ( fun i hi => hx_pos i ) <| Finset.card_pos.mp <| by simpa [ Finset.card_sdiff ] using by nlinarith [ Nat.sub_add_cancel <| show 1 ≤ k ^ 2 from by nlinarith ] ;
  · intro m s hs_mono hs_monotone
    have h_sum_x' : ∑ i : Fin (m + 1), x' (hn ▸ s i) ≤ (ε / 2 + 1 / (k : ℝ)) / (1 - x i_min) := by
      simp +zetaDelta at *;
      rw [ ← Finset.sum_div _ _ _ ];
      gcongr;
      · exact sub_nonneg_of_le ( hx_sum ▸ Finset.single_le_sum ( fun i _ => le_of_lt ( hx_pos i ) ) ( Finset.mem_univ i_min ) );
      · convert hx_bound m ( fun i => ( Finset.univ.erase i_min |> Finset.orderEmbOfFin <| by aesop ) ( hn ▸ s i ) ) _ _ using 1;
        · intro i j hij; have := hs_mono hij; aesop;
        · simp_all ( config := { decide := Bool.true } ) [ Monotone, Antitone, div_eq_mul_inv ];
          exact Or.imp ( fun h => fun a b hab => by have := h hab; rw [ div_le_div_iff_of_pos_right ( sub_pos.mpr <| hx_sum ▸ by rw [ Finset.sum_eq_add_sum_diff_singleton <| Finset.mem_univ i_min ] ; exact lt_add_of_pos_right _ <| Finset.sum_pos ( fun i hi => hx_pos i ) <| Finset.card_pos.mp <| by simpa [ Finset.card_sdiff, * ] using by nlinarith ) ] at this; linarith ) ( fun h => fun a b hab => by have := h hab; rw [ div_le_div_iff_of_pos_right ( sub_pos.mpr <| hx_sum ▸ by rw [ Finset.sum_eq_add_sum_diff_singleton <| Finset.mem_univ i_min ] ; exact lt_add_of_pos_right _ <| Finset.sum_pos ( fun i hi => hx_pos i ) <| Finset.card_pos.mp <| by simpa [ Finset.card_sdiff, * ] using by nlinarith ) ] at this; linarith ) hs_monotone;
    -- Since $x_{\text{min}} \leq \frac{1}{k^2}$, we have $1 - x_{\text{min}} \geq 1 - \frac{1}{k^2} = \frac{k^2 - 1}{k^2}$.
    have h_x_min_le : x i_min ≤ 1 / (k ^ 2 : ℝ) := by
      rw [ le_div_iff₀ ( by positivity ) ];
      have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => hi_min i; simp_all ( config := { decide := Bool.true } ) [ mul_comm ] ;
    -- Substitute $1 - x_{\text{min}} \geq \frac{k^2 - 1}{k^2}$ into the inequality.
    have h_subst : (ε / 2 + 1 / (k : ℝ)) / (1 - x i_min) ≤ (ε / 2 + 1 / (k : ℝ)) * (k^2 / (k^2 - 1)) := by
      rw [ div_le_iff₀ ];
      · rw [ mul_assoc ];
        refine' le_mul_of_one_le_right ( by positivity ) _;
        rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith only [ show ( k : ℝ ) ≥ 2 by norm_cast, h_x_min_le, one_div_mul_cancel ( by positivity : ( k : ℝ ) ^ 2 ≠ 0 ) ];
      · exact sub_pos_of_lt ( lt_of_le_of_lt h_x_min_le ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ hk ] ) );
    refine' le_trans h_sum_x' ( le_trans h_subst _ );
    field_simp;
    rw [ div_le_iff₀ ] <;> norm_num [ Nat.cast_sub ( show 1 ≤ k ^ 2 from by nlinarith ) ] <;> ring_nf <;> norm_num;
    · nlinarith only [ show ( k : ℝ ) ≥ 2 by norm_cast, inv_mul_cancel₀ ( by nlinarith only [ show ( k : ℝ ) ≥ 2 by norm_cast ] : ( -1 + ( k : ℝ ) ^ 2 ) ≠ 0 ), hε_pos, sq_nonneg ( ( k : ℝ ) - 1 ) ];
    · linarith

/-
===
-/

/-
M(L) is the maximum sum of a monotone subsequence of L. M_inc(L) and M_dec(L) are the maximum sums of increasing and decreasing subsequences, respectively.
-/
noncomputable def M_inc (L : List ℝ) : ℝ :=
  (L.sublists.filter (fun S => S.Sorted (· < ·))).map List.sum |>.maximum.getD 0

noncomputable def M_dec (L : List ℝ) : ℝ :=
  (L.sublists.filter (fun S => S.Sorted (· > ·))).map List.sum |>.maximum.getD 0

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
    unfold M_inc;
    -- By definition of $M_inc$, we know that every increasing subsequence of $A ++ B$ is either entirely in $A$ or entirely in $B$.
    have h_subseq : ∀ S ∈ (A ++ B).sublists, S.Sorted (· < ·) → (∃ T ∈ A.sublists, T.Sorted (· < ·) ∧ S = T ∨ ∃ T ∈ B.sublists, T.Sorted (· < ·) ∧ S = T) ∨ (∃ T₁ ∈ A.sublists, T₁.Sorted (· < ·) ∧ ∃ T₂ ∈ B.sublists, T₂.Sorted (· < ·) ∧ S = T₁ ++ T₂) := by
      intro S hS hS';
      -- Let's split the list $S$ into two parts: elements from $A$ and elements from $B$.
      obtain ⟨T₁, T₂, hT₁, hT₂, hS_eq⟩ : ∃ T₁ T₂ : List ℝ, T₁ ∈ A.sublists ∧ T₂ ∈ B.sublists ∧ S = T₁ ++ T₂ := by
        simp_all +decide [ List.sublists_append ];
        grind;
      simp_all +decide [ List.Sorted ];
      rw [ List.pairwise_append ] at hS' ; aesop;
    -- By definition of $M_inc$, we know that every increasing subsequence of $A ++ B$ is either entirely in $A$ or entirely in $B$, or it is a concatenation of an increasing subsequence of $A$ and an increasing subsequence of $B$.
    have h_max_sum : ∀ S ∈ (A ++ B).sublists, S.Sorted (· < ·) → S.sum ≤ (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) A.sublists)).maximum.getD 0 + (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) B.sublists)).maximum.getD 0 := by
      intro S hS hS'; specialize h_subseq S hS hS'; aesop;
      · unfold Option.getD; aesop;
        · have := List.argmax_eq_some_iff.mp heq; aesop;
          exact le_add_of_le_of_nonneg ( left_2 _ _ left left_1 rfl ) ( by linarith [ show 0 ≤ x_1 by exact le_trans ( by norm_num ) ( List.le_maximum_of_mem ( List.mem_map.mpr ⟨ [ ], List.mem_filter.mpr ⟨ by aesop, by aesop ⟩, rfl ⟩ ) heq_1 ) ] );
        · rw [ List.maximum ] at heq;
          rw [ List.argmax_eq_some_iff ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
      · refine' le_add_of_nonneg_of_le _ _;
        · unfold Option.getD; aesop;
          have := List.maximum_mem heq; aesop;
          by_contra h_neg;
          have := List.argmax_eq_some_iff.mp heq; aesop;
          exact h_neg.not_le ( by have := left_2 0 [ ] ( by simp +decide ) ( by simp +decide ) rfl; linarith );
        · unfold Option.getD; aesop;
          · have := List.argmax_eq_some_iff.mp heq; aesop;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
      · refine' add_le_add _ _;
        · unfold Option.getD; aesop;
          · have := List.argmax_eq_some_iff.mp heq; aesop;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
        · unfold Option.getD; aesop;
          · rw [ List.maximum ] at heq;
            rw [ List.argmax_eq_some_iff ] at heq ; aesop;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
    -- By definition of $M_inc$, we know that there exists an increasing subsequence of $A ++ B$ whose sum is equal to the sum of the maximum sums of increasing subsequences of $A$ and $B$.
    obtain ⟨S, hS⟩ : ∃ S ∈ (A ++ B).sublists, S.Sorted (· < ·) ∧ S.sum = (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) A.sublists)).maximum.getD 0 + (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) B.sublists)).maximum.getD 0 := by
      -- Let $T₁$ be the maximum sum increasing subsequence of $A$ and $T₂$ be the maximum sum increasing subsequence of $B$.
      obtain ⟨T₁, hT₁⟩ : ∃ T₁ ∈ A.sublists, T₁.Sorted (· < ·) ∧ T₁.sum = (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) A.sublists)).maximum.getD 0 := by
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num ⟩
      obtain ⟨T₂, hT₂⟩ : ∃ T₂ ∈ B.sublists, T₂.Sorted (· < ·) ∧ T₂.sum = (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) B.sublists)).maximum.getD 0 := by
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num ⟩;
      refine' ⟨ T₁ ++ T₂, _, _, _ ⟩ <;> simp_all +decide [ List.sublists_append ];
      · exact ⟨ T₂, hT₂.1, T₁, hT₁.1, rfl ⟩;
      · simp_all +decide [ List.Sorted ];
        grind;
    refine' le_antisymm _ _;
    · unfold Option.getD; aesop;
      any_goals have := List.maximum_mem heq; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq ; aesop;
    · rw [ ← hS.2.2 ];
      unfold Option.getD; aesop;
      · rw [ List.maximum ] at heq;
        rw [ List.argmax_eq_some_iff ] at heq ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq ; aesop

/-
If every element in A is less than every element in B, then the maximum sum of a decreasing subsequence of A ++ B is the maximum of the sums of decreasing subsequences of A and B.
-/
theorem M_dec_append_of_lt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
  M_dec (A ++ B) = max (M_dec A) (M_dec B) := by
    -- Let's denote the subsequence of B in the maximum decreasing subsequence of A ++ B by .B.
    apply le_antisymm;
    · unfold M_dec; aesop;
      -- Every decreasing subsequence of $A ++ B$ is either a subsequence of $A$ or a subsequence of $B$.
      have h_subseq : ∀ S ∈ (A ++ B).sublists.filter (fun S => S.Sorted (· > ·)), S ∈ A.sublists.filter (fun S => S.Sorted (· > ·)) ∨ S ∈ B.sublists.filter (fun S => S.Sorted (· > ·)) := by
        aesop;
        -- If S is a sublist of A ++ B, then S can be split into a part from A and a part from B.
        obtain ⟨S_A, S_B, hS⟩ : ∃ S_A S_B, S = S_A ++ S_B ∧ S_A.Sublist A ∧ S_B.Sublist B := by
          exact?;
        cases S_A <;> cases S_B <;> aesop;
        have := left_1 head_1 ( Or.inr ( Or.inl rfl ) ) ; linarith [ h _ ( left_3.subset ( by aesop ) ) _ ( right_1.subset ( by aesop ) ) ] ;
      unfold Option.getD; aesop;
      · have := List.maximum_mem heq; aesop;
        cases h_subseq w left right_1 <;> [ left; right ] <;> have := List.maximum_mem heq_1 <;> have := List.maximum_mem heq_2 <;> aesop;
        · have := List.argmax_eq_some_iff.mp heq_1; aesop;
        · have := List.argmax_eq_some_iff.mp heq_2; aesop;
      · rw [ List.maximum ] at *;
        rw [ List.argmax_eq_none ] at heq_2 ; aesop;
        exact absurd ( heq_2 [ ] ( by norm_num ) ) ( by norm_num );
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq_1 ; aesop;
        specialize heq_1 [ ] ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq_1 heq_2 ; aesop;
        specialize heq_1 [ ] ; specialize heq_2 [ ] ; aesop;
      · contrapose! heq; simp_all +decide [ List.maximum ] ;
        rw [ List.argmax_eq_none ] ; aesop;
        exact ⟨ [ ], List.nil_sublist _, List.sorted_nil ⟩;
    · unfold M_dec; aesop;
      · unfold Option.getD; aesop;
        · rw [ List.maximum ] at *;
          rw [ List.argmax_eq_some_iff ] at * ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq_1 ; aesop;
          contrapose! heq_1;
          exact ⟨ [ ], List.nil_sublist _, List.sorted_nil ⟩;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          specialize heq [ ] ; aesop;
      · unfold Option.getD;
        cases h : List.maximum ( List.map List.sum ( List.filter ( fun S => Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) S ) ) ( A ++ B ).sublists ) ) <;> aesop;
        · contrapose! h;
          exact ⟨ [ ], List.nil_sublist _, List.sorted_nil ⟩;
        · replace h := List.argmax_eq_some_iff.mp h; aesop;
          have := List.maximum_mem heq; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          specialize heq [ ] ; aesop

/-
If every element in A is greater than every element in B, then the maximum sum of an increasing subsequence of A ++ B is the maximum of the sums of increasing subsequences of A and B.
-/
theorem M_inc_append_of_gt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a > b) :
  M_inc (A ++ B) = max (M_inc A) (M_inc B) := by
    -- Let $S$ be an increasing subsequence of $A ++ B$. We need to show that $S$ has a sum less than or equal to $\max(M_inc(A), M_inc(B))$.
    have h_subseq : ∀ S ∈ (A ++ B).sublists.filter (fun S => S.Sorted (· < ·)), S.sum ≤ max (M_inc A) (M_inc B) := by
      intro S hS
      have h_split : ∃ S_A S_B, S = S_A ++ S_B ∧ S_A ∈ A.sublists ∧ S_B ∈ B.sublists := by
        norm_num +zetaDelta at *;
        bound;
        exact?;
      aesop;
      by_cases hw : w = [] <;> by_cases hw' : w_1 = [] <;> simp_all +decide [ List.Sorted ];
      · unfold M_inc; aesop;
        unfold Option.getD; aesop;
        contrapose! heq; aesop;
        rw [ List.maximum ] at *;
        rw [ List.argmax_eq_some_iff ] at * ; aesop;
        exact absurd ( left_1 _ [ ] ( by norm_num ) ( by norm_num ) rfl ) ( by norm_num; linarith );
      · -- Since $w_1$ is a subsequence of $B$ and $B$ is sorted in increasing order, the sum of $w_1$ is less than or equal to the sum of the maximum increasing subsequence of $B$, which is $M_inc B$.
        have h_sum_le_M_inc_B : w_1.sum ≤ M_inc B := by
          -- Since $w_1$ is a subsequence of $B$ and $B$ is sorted in increasing order, the sum of $w_1$ is less than or equal to the sum of the maximum increasing subsequence of $B$, which is $M_inc B$. Hence, we have $w_1.sum ≤ M_inc B$.
          have h_sum_le_M_inc_B : w_1.sum ≤ (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) (List.sublists B))).maximum.getD 0 := by
            have h_sum_le_M_inc_B : w_1.sum ∈ List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) (List.sublists B)) := by
              aesop;
            have h_sum_le_M_inc_B : ∀ {l : List ℝ}, w_1.sum ∈ l → w_1.sum ≤ List.maximum l := by
              intros l hl; induction l <;> aesop;
              · simp +decide [ List.maximum_cons ];
              · simp_all +decide [ List.maximum_cons ];
            specialize h_sum_le_M_inc_B ‹_›; cases h : List.maximum ( List.map List.sum ( List.filter ( fun S => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) S ) ) B.sublists ) ) <;> aesop;
          exact h_sum_le_M_inc_B;
        exact Or.inr h_sum_le_M_inc_B;
      · have h_sum_le_max : ∀ {S : List ℝ}, S ∈ A.sublists → S.Sorted (· < ·) → S.sum ≤ (List.map List.sum (List.filter (fun S => S.Sorted (· < ·)) A.sublists)).maximum.getD 0 := by
          unfold Option.getD; aesop;
          · have := List.argmax_eq_some_iff.mp heq; aesop;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
        exact Or.inl <| h_sum_le_max ( List.mem_sublists.mpr left_2 ) right;
      · rw [ List.pairwise_append ] at right ; aesop;
        contrapose! right;
        exact ⟨ _, List.head!_mem_self hw, _, List.head!_mem_self hw', le_of_lt ( h _ ( left_2.subset ( List.head!_mem_self hw ) ) _ ( right_1.subset ( List.head!_mem_self hw' ) ) ) ⟩;
    refine' le_antisymm _ _ <;> aesop;
    · unfold M_inc at *;
      unfold Option.getD; aesop;
      · have := List.maximum_mem heq; aesop;
      · have := List.maximum_mem heq; aesop;
      · have := List.maximum_mem heq; aesop;
      · rw [ List.maximum ] at heq;
        rw [ List.argmax_eq_some_iff ] at heq ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq ; aesop;
        specialize heq [ ] ; aesop;
    · -- Any increasing subsequence of A is also an increasing subsequence of A ++ B.
      have h_inc_A : ∀ S ∈ (A.sublists.filter (fun S => S.Sorted (· < ·))), S.sum ≤ M_inc (A ++ B) := by
        unfold M_inc; aesop;
        unfold Option.getD; aesop;
        · have := List.argmax_eq_some_iff.mp heq; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
      unfold M_inc at *; aesop;
      unfold Option.getD; aesop;
      · have := List.maximum_mem heq; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_some_iff ] at heq ; aesop;
      · specialize h_inc_A [ ] ; aesop;
    · have h_subseq_B : ∀ S ∈ B.sublists.filter (fun S => S.Sorted (· < ·)), S.sum ≤ M_inc (A ++ B) := by
        aesop;
        refine' List.le_maximum_of_mem _ _;
        exact ( List.map List.sum ( List.filter ( fun S => S.Sorted ( · < · ) ) ( List.sublists ( A ++ B ) ) ) );
        · aesop;
        · unfold M_inc;
          cases h : List.maximum ( List.map List.sum ( List.filter ( fun S => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) S ) ) ( A ++ B ).sublists ) ) <;> aesop;
      unfold M_inc at *; aesop;
      unfold Option.getD; aesop;
      · have := List.maximum_mem heq; aesop;
      · have := List.maximum_mem heq; aesop;
      · contrapose! h_subseq_B;
        exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num; linarith ⟩

/-
If every element in A is greater than every element in B, then the maximum sum of a decreasing subsequence of A ++ B is the sum of the maximum sums of decreasing subsequences of A and B.
-/
theorem M_dec_append_of_gt {A B : List ℝ} (h : ∀ a ∈ A, ∀ b ∈ B, a > b) :
  M_dec (A ++ B) = M_dec A + M_dec B := by
    -- The maximum sum of a decreasing subsequence in A ++ B is the sum of the maximum sums of decreasing subsequences in A and B.
    have h_max_sum_dec : ∀ S ∈ (A ++ B).sublists, S.Sorted (· > ·) → S.sum ≤ M_dec A + M_dec B := by
      intros S hS hS_sorted
      have h_split : ∃ S_A ∈ A.sublists, ∃ S_B ∈ B.sublists, S = S_A ++ S_B := by
        simp +zetaDelta at *;
        rw [ List.sublist_append_iff ] at hS ; aesop;
      unfold M_dec; aesop;
      refine' add_le_add _ _;
      · have h_max_sum_dec_A : ∀ S ∈ A.sublists, S.Sorted (· > ·) → S.sum ≤ (List.map List.sum (List.filter (fun S => S.Sorted (· > ·)) A.sublists)).maximum.getD 0 := by
          unfold Option.getD; aesop;
          · have := List.argmax_eq_some_iff.mp heq; aesop;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
        exact h_max_sum_dec_A _ ( List.mem_sublists.mpr left ) ( hS_sorted.sublist ( List.sublist_append_left _ _ ) );
      · unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
          have h_max_sum_dec_B : ∀ S ∈ B.sublists, S.Sorted (· > ·) → S.sum ≤ w_2.sum := by
            have := List.argmax_eq_some_iff.mp heq; aesop;
          exact h_max_sum_dec_B _ ( List.mem_sublists.mpr left_1 ) ( hS_sorted.sublist ( List.sublist_append_right _ _ ) );
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          specialize heq [ ] ; aesop;
    -- To prove the equality, it suffices to show that there exists a decreasing subsequence of A ++ B whose sum is M_dec A + M_dec B.
    obtain ⟨S, hS⟩ : ∃ S ∈ (A ++ B).sublists, S.Sorted (· > ·) ∧ S.sum = M_dec A + M_dec B := by
      obtain ⟨S_A, hS_A⟩ : ∃ S_A ∈ A.sublists, S_A.Sorted (· > ·) ∧ S_A.sum = M_dec A := by
        unfold M_dec;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num ⟩
      obtain ⟨S_B, hS_B⟩ : ∃ S_B ∈ B.sublists, S_B.Sorted (· > ·) ∧ S_B.sum = M_dec B := by
        unfold M_dec;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num ⟩;
      use S_A ++ S_B; aesop;
      · exact List.Sublist.append left left_1;
      · rw [ List.Sorted ] at *;
        grind +ring;
    -- Since $S$ is a decreasing subsequence of $A ++ B$ with sum $M_dec A + M_dec B$, and $M_dec A + M_dec B$ is the maximum possible sum of such a subsequence, it follows that $M_dec A + M_dec B$ is indeed the maximum element of the list.
    have h_max_eq : List.maximum (List.map List.sum (List.filter (fun S => List.Sorted (· > ·) S) (A ++ B).sublists)) = some (M_dec A + M_dec B) := by
      have h_max_eq : ∀ x ∈ List.map List.sum (List.filter (fun S => List.Sorted (· > ·) S) (A ++ B).sublists), x ≤ M_dec A + M_dec B := by
        aesop;
      refine' List.argmax_eq_some_iff.mpr _ ; aesop;
      · aesop;
      · rw [ le_antisymm a_4 ( h_max_eq _ _ a_1 a_2 rfl ) ];
    unfold M_dec at * ; aesop

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
    -- Let's unfold the definition of $M_{\text{inc}}$.
    unfold M_inc;
    unfold Option.getD; aesop;
    · -- Since L is sorted and all elements are positive, the maximum sum of any increasing subsequence of L is just the sum of L itself.
      have h_max_sum : ∀ S ∈ List.sublists L, S.Sorted (· < ·) → S.sum ≤ L.sum := by
        aesop;
        have := List.Sublist.sum_le_sum a;
        exact this fun x hx => le_of_lt ( h_pos x hx );
      refine' le_antisymm _ _;
      · have := List.maximum_mem heq; aesop;
      · refine' List.le_maximum_of_mem _ heq;
        aesop;
    · rw [ List.maximum ] at heq;
      rw [ List.argmax_eq_none ] at heq ; aesop

/-
If L is sorted increasing and has positive elements, then M_dec(L) is the maximum element of L.
-/
theorem M_dec_sorted {L : List ℝ} (h_sorted : L.Sorted (· < ·)) (h_pos : ∀ x ∈ L, 0 < x) :
  M_dec L = L.maximum.getD 0 := by
    unfold M_dec;
    unfold Option.getD; aesop;
    · have h_max_sublist : ∀ S ∈ List.filter (fun S => S.Sorted (· > ·)) L.sublists, List.sum S ≤ x_1 := by
        intros S hS
        have h_max_sublist : S.length ≤ 1 := by
          contrapose! hS; aesop;
          have := List.pairwise_iff_get.mp a_1; aesop;
          have := List.pairwise_iff_get.mp ( h_sorted.sublist a ) ; aesop;
          exact lt_asymm ( this ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ( Nat.zero_lt_one ) ) ( this_1 ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ( Nat.zero_lt_one ) );
        cases S <;> aesop;
        · exact le_of_lt ( h_pos _ ( List.maximum_mem heq_1 ) );
        · exact?;
      have h_max_sublist : x ≤ x_1 := by
        have := List.maximum_mem heq; aesop;
      have h_max_sublist : x_1 ∈ List.map List.sum (List.filter (fun S => S.Sorted (· > ·)) L.sublists) := by
        have h_max_sublist : x_1 ∈ L := by
          exact?;
        exact List.mem_map.mpr ⟨ [ x_1 ], List.mem_filter.mpr ⟨ List.mem_sublists.mpr <| by aesop, by aesop ⟩, by aesop ⟩;
      exact le_antisymm ‹_› ( List.le_maximum_of_mem h_max_sublist <| by aesop );
    · simp_all +decide [ List.maximum ];
      rw [ List.argmax_eq_none ] at heq_1 ; aesop;
      injection heq.symm;
    · rw [ List.maximum ] at heq_1;
      rw [ List.argmax_eq_some_iff ] at heq_1 ; aesop;
      simp_all +decide [ List.maximum ];
      rw [ List.argmax_eq_none ] at heq ; aesop;
      specialize heq [ x ] ; aesop

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
    bound;
    unfold es_part_blocks at a; aesop;
    refine' List.pairwise_iff_get.mpr _;
    aesop

/-
Blocks in es_part_blocks are pairwise decreasing: every element in an earlier block is greater than every element in a later block.
-/
theorem es_part_blocks_decreasing (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) :
  ∀ i j, i < j → j < num_blocks →
    let B := es_part_blocks num_blocks block_size base_val start_idx eps
    ∀ x ∈ B[i]!, ∀ y ∈ B[j]!, x > y := by
      unfold es_part_blocks; aesop;
      rw [ List.getElem?_range ] at a_2 ; aesop;
      · norm_cast;
        nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ num_blocks ), Nat.sub_add_cancel ( by omega : j ≤ num_blocks - 1 ), Nat.sub_add_cancel ( by omega : i ≤ num_blocks - 1 ) ];
      · linarith

/-
If L is a list of lists such that blocks are pairwise decreasing, then M_inc(L.flatten) is the maximum of M_inc of the blocks.
-/
theorem M_inc_flatten_of_pairwise_decreasing (L : List (List ℝ))
  (h_dec : ∀ i j, i < j → j < L.length → ∀ x ∈ L[i]!, ∀ y ∈ L[j]!, x > y) :
  M_inc L.flatten = (L.map M_inc).maximum.getD 0 := by
    induction L <;> aesop;
    -- Apply the lemma M_inc_append_of_gt with the given h_dec.
    have h_max : M_inc (head ++ tail.flatten) = max (M_inc head) (M_inc (tail.flatten)) := by
      apply M_inc_append_of_gt;
      aesop;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 left ; specialize h_dec 0 ( i + 1 ) ; aesop;
    specialize tail_ih ( fun i j hij hj => h_dec ( i + 1 ) ( j + 1 ) ( Nat.succ_lt_succ hij ) ( by linarith ) ) ; aesop;
    unfold Option.getD; aesop;
    · rw [ List.maximum_cons ] at heq_1 ; aesop;
      erw [ WithBot.coe_eq_coe ] at heq_1 ; aesop;
    · simp_all +decide [ List.maximum ];
      rw [ List.argmax_eq_none ] at heq_1 ; aesop;
    · simp_all +decide [ List.maximum ];
      rw [ List.argmax_eq_none ] at heq ; aesop;
      injection heq_1;
    · simp_all +decide [ List.maximum ];
      rw [ List.argmax_eq_none ] at heq_1 ; aesop

/-
If L is a list of lists such that blocks are pairwise decreasing, then M_dec(L.flatten) is the sum of M_dec of the blocks.
-/
theorem M_dec_flatten_of_pairwise_decreasing (L : List (List ℝ))
  (h_dec : ∀ i j, i < j → j < L.length → ∀ x ∈ L[i]!, ∀ y ∈ L[j]!, x > y) :
  M_dec L.flatten = (L.map M_dec).sum := by
    -- We'll use induction on the length of L.
    induction' L with L ih;
    · bound;
    · have := @M_dec_append_of_gt L ( List.flatten ih ) ?_;
      · aesop;
        exact tail_ih fun i j hij hj x hx y hy => h_dec ( i + 1 ) ( j + 1 ) ( by linarith ) ( by linarith ) x ( by aesop ) y ( by aesop );
      · aesop;
        obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp left;
        specialize h_dec 0 ( k + 1 ) ; aesop

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
    exact?

/-
M_inc of es_part is the maximum of the sums of its blocks.
-/
theorem M_inc_es_part_eq_max_sum (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  M_inc (es_part num_blocks block_size base_val start_idx eps) =
  ((es_part_blocks num_blocks block_size base_val start_idx eps).map List.sum).maximum.getD 0 := by
    rw [ es_part_eq_join ];
    rw [ M_inc_flatten_of_pairwise_decreasing ];
    · rw [ List.map_congr_left ];
      exact?;
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
      exact?;
    exact?

/-
M_inc of es_part is the maximum of the sums of its blocks.
-/
theorem M_inc_es_part_eq_max_sum_v2 (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ) (h_eps : 0 < eps) (h_base : 0 < base_val) :
  M_inc (es_part num_blocks block_size base_val start_idx eps) =
  ((es_part_blocks num_blocks block_size base_val start_idx eps).map List.sum).maximum.getD 0 := by
    exact?

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
      · exact?;
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
                                    exact?

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
      exact?
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
      · exact?;
      · omega;
      · contrapose! hd; aesop;
        unfold es_part at hx hy; aesop;
      · exact hx
    have hy_range : d.red + (d.start2) * eps ≤ y ∧ y ≤ d.red + (d.start2 + d.len2 - 1) * eps := by
      apply es_part_bounds;
      · exact?;
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
      exact?;
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
      intro b hb; induction' block_size with block_size ih <;> simp_all +decide [ List.range_succ ] ; ring;
      norm_num [ List.sum_map_add, List.sum_range_succ' ] at * ; ring_nf at * ; aesop;
      linarith;
    convert Finset.sum_congr rfl fun b hb => h_block_sum b ( Finset.mem_range.mp hb ) using 1;
    · refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
      convert h_block_sum n h₁ using 3 ; rw [ Nat.cast_sub <| Nat.le_sub_one_of_lt h₁ ] ; rw [ Nat.cast_sub <| by linarith ] ; push_cast ; ring;
    · norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
      norm_num [ ← Finset.sum_mul _ _ _ ] ; ring;
      exact Nat.recOn num_blocks ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith;

/-
Formula for M_inc of an es_part.
-/
theorem M_inc_es_part_value (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ)
  (h_eps : 0 < eps) (h_base : 0 < base_val) (h_blocks : 0 < num_blocks) (h_size : 0 < block_size) :
  M_inc (es_part num_blocks block_size base_val start_idx eps) =
  (block_size : ℝ) * base_val +
  eps * (block_size * start_idx + block_size * ((num_blocks - 1) * block_size) + (block_size * (block_size - 1)) / 2) := by
    -- Let's simplify the formula for the sum of the es_part.
    have h_w_sum : ∀ (b : ℕ), b < num_blocks → List.sum (es_part_blocks num_blocks block_size base_val start_idx eps)[b]! =
      (block_size : ℝ) * base_val + eps * (block_size * start_idx + block_size * ((num_blocks - 1 - b) * block_size) + block_size * (block_size - 1) / 2) := by
        unfold es_part_blocks; aesop;
        norm_num [ Nat.cast_sub ( show b ≤ num_blocks - 1 from Nat.le_sub_one_of_lt a ), List.sum_map_mul_right ];
        rw [ show ( List.map Nat.cast ( List.range block_size ) ).sum = ( block_size : ℝ ) * ( block_size - 1 ) / 2 from Nat.recOn block_size ( by norm_num ) fun n ih => by norm_num [ List.range_succ ] at * ; linarith ] ; rw [ Nat.cast_sub <| by linarith ] ; push_cast ; ring;
    -- By definition of $M_inc$, we have $M_inc (es_part num_blocks block_size base_val start_idx eps) = \max_{0 \leq b < num_blocks} (List.sum (es_part_blocks num_blocks block_size base_val start_idx eps)[b]!)$.
    have h_max : M_inc (es_part num_blocks block_size base_val start_idx eps) = (List.map (fun b => List.sum (es_part_blocks num_blocks block_size base_val start_idx eps)[b]!) (List.range num_blocks)).maximum.getD 0 := by
      convert M_inc_es_part_eq_max_sum_v2 num_blocks block_size base_val start_idx eps h_eps h_base using 1;
      unfold es_part_blocks; aesop;
      congr! 2;
      refine' List.ext_get _ _ <;> aesop;
    -- Since the sums are strictly decreasing, the maximum is achieved at $b = 0$.
    have h_max_b0 : List.maximum (List.map (fun b => List.sum (es_part_blocks num_blocks block_size base_val start_idx eps)[b]!) (List.range num_blocks)) = some (List.sum (es_part_blocks num_blocks block_size base_val start_idx eps)[0]!) := by
      rw [ List.maximum ];
      rw [ List.argmax_eq_some_iff ];
      norm_num +zetaDelta at *;
      refine' ⟨ ⟨ 0, h_blocks, _ ⟩, _, _ ⟩ <;> aesop;
    aesop

/-
Formula for M_dec of an es_part.
-/
theorem M_dec_es_part_value (num_blocks block_size : ℕ) (base_val : ℝ) (start_idx : ℕ) (eps : ℝ)
  (h_eps : 0 < eps) (h_base : 0 < base_val) (h_blocks : 0 < num_blocks) (h_size : 0 < block_size) :
  M_dec (es_part num_blocks block_size base_val start_idx eps) =
  (num_blocks : ℝ) * base_val +
  eps * (num_blocks * start_idx + block_size * (num_blocks * (num_blocks - 1) / 2) + num_blocks * (block_size - 1)) := by
    have := @M_dec_es_part_eq_sum_max num_blocks block_size base_val start_idx eps h_eps h_base;
    -- Let's simplify the expression for the maximum of each block.
    have h_max_block : ∀ b ∈ List.range num_blocks, (es_part_blocks num_blocks block_size base_val start_idx eps)[b]!.maximum.getD 0 = base_val + (start_idx + ((num_blocks - 1 - b) * block_size + (block_size - 1))) * eps := by
      unfold es_part_blocks; aesop;
      -- The maximum element in the list is the last element, which corresponds to `i = block_size - 1`.
      have h_max_last : List.maximum (List.map (fun i : ℕ => base_val + (↑start_idx + (↑(num_blocks - 1 - b) * ↑block_size + ↑i)) * eps) (List.range block_size)) = some (base_val + (↑start_idx + (↑(num_blocks - 1 - b) * ↑block_size + ↑(block_size - 1))) * eps) := by
        have h_max_last : ∀ i ∈ List.range block_size, base_val + (↑start_idx + (↑(num_blocks - 1 - b) * ↑block_size + ↑i)) * eps ≤ base_val + (↑start_idx + (↑(num_blocks - 1 - b) * ↑block_size + ↑(block_size - 1))) * eps := by
          exact fun i hi => add_le_add_left ( mul_le_mul_of_nonneg_right ( add_le_add_left ( add_le_add_left ( Nat.cast_le.mpr ( Nat.le_sub_one_of_lt ( List.mem_range.mp hi ) ) ) _ ) _ ) h_eps.le ) _;
        rw [ List.maximum ];
        rw [ List.argmax_eq_some_iff ];
        simp +zetaDelta at *;
        exact ⟨ ⟨ block_size - 1, Nat.sub_lt h_size zero_lt_one, Or.inl rfl ⟩, h_max_last, fun a ha₁ ha₂ => by rw [ le_antisymm ( h_max_last a ha₁ ) ha₂ ] ⟩;
      cases h : List.maximum ( List.map ( fun i : ℕ => base_val + ( ↑start_idx + ( ↑ ( num_blocks - 1 - b ) * ↑block_size + ↑i ) ) * eps ) ( List.range block_size ) ) <;> aesop;
      exact Or.inl <| Or.inl <| by rw [ Nat.cast_sub <| Nat.le_sub_one_of_lt a ] ; rw [ Nat.cast_sub <| by linarith ] ; push_cast ; ring;
    -- Let's simplify the sum of the maximums of the blocks.
    have h_sum_max_blocks : (List.map (fun b => (es_part_blocks num_blocks block_size base_val start_idx eps)[b]!.maximum.getD 0) (List.range num_blocks)).sum = ∑ b ∈ Finset.range num_blocks, (base_val + (start_idx + ((num_blocks - 1 - b) * block_size + (block_size - 1))) * eps) := by
      rw [ ← Finset.sum_congr rfl h_max_block ] ; aesop;
    simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_mul, mul_sub ];
    convert h_sum_max_blocks using 1;
    · refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
      · unfold es_part_blocks; aesop;
      · grind;
    · norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_mul, mul_sub ] ; ring;
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
      exact Nat.recOn num_blocks ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith;

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
    refine' ⟨ _, _, _ ⟩;
    · norm_num +zetaDelta at *;
      rw [ max_eq_right ] <;> norm_cast;
      · rw [ Int.toNat_of_nonneg ( by linarith ) ];
      · cases abs_cases ( a + 1 ) <;> cases abs_cases a <;> nlinarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ), Nat.sub_add_cancel ( show a.natAbs ≤ k.toNat from by omega ) ];
    · cases abs_cases ( a + 1 : ℝ ) <;> cases abs_cases ( a : ℝ ) <;> simp +decide [ * ] <;> ring;
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · linarith [ ( by norm_cast : ( a : ℝ ) < -1 ) ];
      · rw [ Nat.cast_sub ] <;> norm_cast;
        · rw [ Int.subNatNat_eq_coe ] ; norm_num ; ring;
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
      simp +decide [ List.flatMap, List.map ];
      fun_prop;
    convert h_cont.tendsto 0 using 1 ; norm_num [ limit_sum ];
    rw [ seq_eps_eq_seq_of_data ] ; norm_num [ part1, part2, part3, sum_es_part_eq ] ; ring;
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
    · unfold es_part; aesop;
      induction ( List.range num_blocks ) <;> aesop;
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
                                              convert limit_M_inc_es_part _ _ _ _ _ _ using 1;
                                              congr! 1;
                                              · aesop;
                                              · cases a <;> aesop;
                                                · linarith;
                                                · cases a <;> cases n_1 <;> norm_num [ Int.negSucc_coe ] at * ; linarith

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
                                              · unfold part3 limit_part3; aesop;
                                                unfold es_part; aesop;

/-
M_inc of the sequence converges to limit_M_inc as epsilon goes to 0 from above.
-/
theorem limit_M_inc_correct_right (k : ℤ) (a : ℤ) (h_k : k ≥ 1) (h_a_le : -k ≤ a) (h_a_lt : a < -1) :
  Filter.Tendsto (fun eps => M_inc (seq_eps k a eps)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (limit_M_inc k a)) := by
    -- By the properties of limits, if the limits of the parts exist, then the limit of their combination also exists.
    have h_limit_comb : Filter.Tendsto (fun eps => max (M_inc (part1 { k := k, a := a, eps := eps }) + M_inc (part2 { k := k, a := a, eps := eps })) (M_inc (part3 { k := k, a := a, eps := eps }))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (limit_part1 k a + limit_part2 k a) (limit_part3 k a))) := by
                                                                                                                                                                      exact Filter.Tendsto.max ( Filter.Tendsto.add ( limit_M_inc_part1_correct k a h_k h_a_le h_a_lt ) ( limit_M_inc_part2_correct k a h_k h_a_le h_a_lt ) ) ( limit_M_inc_part3_correct k a h_k h_a_le h_a_lt );
    refine' Filter.Tendsto.congr' _ ( h_limit_comb.trans _ );
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
      exact?;
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
                                              · unfold part1; aesop;
                                                unfold M_dec; aesop;
                                                unfold es_part; aesop;
                                                bound;
                                                induction ( List.range a.natAbs ) <;> aesop

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
                                              · unfold es_part; aesop;

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
          refine' Filter.eventually_of_mem self_mem_nhdsWithin fun eps h_eps => _;
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
    · exact?;
    · exact?;
    · exact?

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
  ((L.sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s)).map List.sum).maximum.getD 0

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
  ((L.sublists.filter (fun s => List.Sorted (· < ·) s)).map List.sum).maximum.getD 0

noncomputable def max_dec_sum (L : List ℝ) : ℝ :=
  ((L.sublists.filter (fun s => List.Sorted (· > ·) s)).map List.sum).maximum.getD 0

lemma M_eq_max (L : List ℝ) : Mp L = max (max_inc_sum L) (max_dec_sum L) := by
  -- By definition of $M$, we can write
  unfold Mp;
  -- By definition of `List.maximum`, it returns the maximum element in the list, or `none` if the list is empty.
  have h_max_def : List.maximum (List.map List.sum (List.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s) L.sublists)) = max (List.maximum (List.map List.sum (List.filter (fun s => List.Sorted (· < ·) s) L.sublists))) (List.maximum (List.map List.sum (List.filter (fun s => List.Sorted (· > ·) s) L.sublists))) := by
    induction' L.sublists using List.reverseRecOn with s L ih <;> aesop;
    by_cases h : List.Sorted ( · < · ) L <;> by_cases h' : List.Sorted ( · > · ) L <;> simp_all +decide [ List.maximum_append ];
    · simp +decide [ max_assoc, max_comm, max_left_comm ];
    · ac_rfl;
    · rw [ max_assoc ];
  cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ) ) L.sublists ) ) <;> cases h' : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 > x2 ) s ) ) L.sublists ) ) <;> aesop;
  · specialize h_max_def [ ] ; aesop;
  · specialize h [ ] ; aesop;
  · specialize h' [ ] ; aesop;
  · unfold max_inc_sum max_dec_sum; aesop;

/-
The sum of an es_block.
-/
lemma es_block_sum (base : ℝ) (start_idx : ℕ) (size : ℕ) (eps : ℝ) :
  (es_block base start_idx size eps).sum = (size : ℝ) * base + eps * ((size : ℝ) * (start_idx : ℝ) + (size : ℝ) * ((size : ℝ) - 1) / 2) := by
    unfold es_block;
    induction size <;> simp_all +decide [ List.range_succ ] ; ring;
    simp_all +decide [ add_comm, add_left_comm, add_assoc, mul_assoc, List.sum_map_add ] ; ring_nf at * ; aesop;
    linarith

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
      induction' num_blocks with d ih;
      · aesop;
      · -- By definition of `es_partp`, we can split the sum into the sum of the first `d` blocks and the sum of the last block.
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
        rw [ List.nodup_map_iff_inj_on ] ; aesop;
        induction ( k - a ) <;> simp_all +decide [ List.range_succ ];
        rw [ List.nodup_append ] ; aesop;
      · refine' List.Pairwise.imp_of_mem _ _;
        use fun x y => x < y;
        · intros; rw [ Function.onFun, List.disjoint_iff_ne ] ; aesop;
          unfold es_block at *; aesop;
          norm_cast at h;
          rw [ Int.subNatNat_eq_coe ] at h ; push_cast at h ; nlinarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_pos ( by linarith ) ) ) ];
        · exact?
    have h_part2p_nodup : (es_partp a (a * (k - a)) (a + 1) (a + 1) eps).Nodup := by
      erw [ List.nodup_flatMap ];
      unfold es_block; aesop;
      · induction a + 1 <;> simp_all +decide [ List.range_succ ];
        rw [ List.nodup_append ] ; aesop;
      · rw [ List.pairwise_iff_get ] ; aesop;
        rw [ Function.onFun, List.disjoint_left ] ; aesop;
        nlinarith [ show ( i : ℝ ) + 1 ≤ j from mod_cast _hij, show ( x_1 : ℝ ) ≤ a by norm_cast; linarith, show ( w_1 : ℝ ) ≤ a by norm_cast; linarith ]
    have h_part3p_nodup : (es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps).Nodup := by
      refine' List.nodup_flatMap.mpr _;
      unfold es_block; aesop;
      · rw [ List.nodup_map_iff_inj_on ] ; aesop;
        rw [ List.nodup_flatMap ] ; aesop;
        norm_num [ List.pairwise_iff_get ];
        exact fun i j hij => ne_of_gt hij;
      · rw [ List.pairwise_iff_get ] ; aesop;
        rw [ Function.onFun, List.disjoint_left ] ; aesop;
        nlinarith [ show ( i : ℝ ) + 1 ≤ j from mod_cast _hij, show ( x_1 : ℝ ) < k from mod_cast a_3, show ( w_1 : ℝ ) < k from mod_cast left ]
    have h_parts_disjoint : Disjoint (es_partp (a + 1) 0 a (k - a) eps).toFinset (es_partp a (a * (k - a)) (a + 1) (a + 1) eps).toFinset ∧ Disjoint (es_partp a (a * (k - a)) (a + 1) (a + 1) eps).toFinset (es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps).toFinset ∧ Disjoint (es_partp (a + 1) (a * (k - a) + (a + 1) * (a + 1)) (k - a) k eps).toFinset (es_partp (a + 1) 0 a (k - a) eps).toFinset := by
      unfold es_partp; aesop;
      · norm_num [ List.disjoint_left, es_block ];
        aesop;
        -- Since $eps$ is positive and less than 1, the term $((a - x) * (k - a) + x_3 * (a + 1) + (a - x_5) + x_2 - k + a + 1) * eps$ must be less than 1.
        have h_coeff : ((a - x) * (k - a) + x_3 * (a + 1) + (a - x_5) + x_2 - k + a + 1) * eps < 1 := by
          refine' lt_of_le_of_lt _ h_eps_small;
          field_simp;
          nlinarith only [ show ( x : ℝ ) + 1 ≤ a by norm_cast, show ( x_2 : ℝ ) + 1 ≤ k - a by exact le_tsub_of_add_le_left ( by norm_cast; linarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) ) ) ] ), show ( x_3 : ℝ ) + 1 ≤ a + 1 by norm_cast, show ( x_5 : ℝ ) + 1 ≤ a + 1 by norm_cast ];
        rw [ Nat.cast_sub ( by linarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_pos ( by linarith ) ) ) ] ) ] at * ; nlinarith;
      · norm_num [ List.disjoint_left, es_block ];
        aesop;
        nlinarith [ show ( x : ℝ ) ≤ a by norm_cast; linarith, show ( x_2 : ℝ ) ≤ a by norm_cast; linarith, show ( x_3 : ℝ ) < k - a by exact lt_tsub_iff_left.mpr ( by norm_cast; linarith [ Nat.sub_add_cancel ( show a ≤ k from le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop_cat ) ) ) ] ), show ( x_5 : ℝ ) < k by norm_cast, mul_nonneg h_eps_pos.le ( Nat.cast_nonneg a ), mul_nonneg h_eps_pos.le ( Nat.cast_nonneg x_3 ), mul_nonneg h_eps_pos.le ( Nat.cast_nonneg x_5 ) ];
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
    unfold es_partp es_partp_max_val; aesop;
    unfold es_block at right; aesop;
    exact mul_le_mul_of_nonneg_right ( by nlinarith [ show ( w : ℝ ) + 1 ≤ num_blocks by norm_cast, show ( w_2 : ℝ ) + 1 ≤ size by norm_cast ] ) heps

/-
es_block is strictly decreasing if epsilon is positive.
-/
lemma es_block_decreasing (base : ℝ) (start_idx : ℕ) (size : ℕ) (eps : ℝ) (heps : 0 < eps) :
  List.Sorted (· > ·) (es_block base start_idx size eps) := by
    unfold es_block;
    refine' List.pairwise_iff_get.mpr _ ; aesop;
    -- The flatMap of the range size is just the list of natural numbers from 0 to size-1.
    have h_flatMap : List.flatMap (fun (a : ℕ) => [(↑a : ℝ)]) (List.range size) = List.map (fun (a : ℕ) => ↑a) (List.range size) := by
      exact?;
    aesop

/-
Any increasing subsequence of an es_partp has length at most num_blocks.
-/
lemma es_partp_inc_length_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 < eps) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· < ·) s →
  s.length ≤ num_blocks := by
    unfold es_partp;
    -- Since each element in es_block is strictly decreasing, any increasing subsequence can contain at most one element from each block.
    have h_block : ∀ b : ℕ, ∀ s : List ℝ, s.Sublist (es_block base (start_idx + b * size) size eps) → s.Sorted (· < ·) → s.length ≤ 1 := by
      aesop;
      have h_block : ∀ b : ℕ, ∀ s : List ℝ, s.Sublist (es_block base (start_idx + b * size) size eps) → s.Sorted (· < ·) → s.length ≤ 1 := by
        intros b s hs_sub hs_sorted
        have h_block_sorted : s.Sorted (· > ·) := by
          exact List.Pairwise.sublist hs_sub <| es_block_decreasing base ( start_idx + b * size ) size eps heps
        rcases s with ( _ | ⟨ x, _ | ⟨ y, s ⟩ ⟩ ) <;> aesop;
        linarith;
      exact h_block b s a a_1;
    induction' num_blocks with num_blocks ih <;> simp_all +decide [ List.range_succ ];
    intro s hs hs'; rw [ List.sublist_append_iff ] at hs; aesop;
    exact add_le_add ( ih _ left_1 ( hs'.sublist ( List.sublist_append_left _ _ ) ) ) ( h_block _ _ right ( hs'.sublist ( List.sublist_append_right _ _ ) ) )

/-
The sum of any increasing subsequence in an es_partp is bounded by num_blocks * max_val.
-/
lemma es_partp_inc_sum_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hbase : 0 ≤ base) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· < ·) s →
  List.sum s ≤ (num_blocks : ℝ) * es_partp_max_val base start_idx num_blocks size eps := by
    intros s hs_sub hs_sorted
    have hs_len : s.length ≤ num_blocks := by
      by_cases h_eps_pos : 0 < eps;
      · exact?;
      · cases eq_or_lt_of_le heps <;> aesop;
        unfold es_partp at hs_sub;
        unfold es_block at hs_sub;
        have := hs_sorted; rcases s with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> aesop;
        · nlinarith;
        · have := hs_sub.subset; aesop;
    have h_max_sum : ∀ x ∈ s, x ≤ es_partp_max_val base start_idx num_blocks size eps := by
      exact fun x hx => es_partp_bound base start_idx num_blocks size eps heps x ( hs_sub.subset hx );
    exact le_trans ( List.sum_le_card_nsmul _ _ h_max_sum ) ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hs_len ) ( show 0 ≤ es_partp_max_val base start_idx num_blocks size eps by unfold es_partp_max_val; positivity ) )

/-
Any decreasing subsequence of an es_partp has length at most size.
-/
lemma es_partp_dec_length_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 < eps) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· > ·) s →
  s.length ≤ size := by
    intros s hs_sub hs_sorted
    -- We argue that s must be a sublist of a single block.
    -- Let's show that if s has elements from different blocks, it violates sortedness.
    -- Or simpler: s cannot contain elements from block i and block j with i < j.
    -- Since s is a subsequence, elements appear in order.
    -- If x from block i and y from block j appear in s, then x comes before y in s.
    -- Since s is decreasing, x > y.
    -- But block i < block j (values), so x < y. Contradiction.
    -- Thus all elements must be from the same block.
    -- The length of a block is size.
    have h_block_decreasing : ∀ (s : List ℝ), List.Sublist s (List.flatMap (fun b => es_block base (start_idx + b * size) size eps) (List.range num_blocks)) → List.Sorted (· > ·) s → s.length ≤ size := by
      -- By induction on the number of blocks, we can show that any decreasing subsequence of the entire flattened list can't have more elements than the size of one block.
      have h_induction : ∀ (num_blocks : ℕ), ∀ (s : List ℝ), List.Sublist s (List.flatMap (fun b => es_block base (start_idx + b * size) size eps) (List.range num_blocks)) → List.Sorted (· > ·) s → s.length ≤ size := by
        intro num_blocks; induction' num_blocks with num_blocks ih <;> simp_all +decide [ List.range_succ ] ;
        intro s hs_sub hs_sorted; rw [ List.sublist_append_iff ] at hs_sub; aesop;
        simp_all +decide [ List.Sorted ];
        rw [ List.pairwise_append ] at hs_sorted ; aesop;
        contrapose! right_1;
        -- Since $w$ is a sublist of the previous blocks and $w_1$ is a sublist of the current block, and the blocks are strictly decreasing, the maximum element in $w$ is less than or equal to the minimum element in $w_1$.
        have h_max_min : ∀ x ∈ w, ∀ y ∈ w_1, x ≤ y := by
          intros x hx y hy; have := left_1.subset hx; have := right.subset hy; aesop;
          unfold es_block at *; aesop;
          nlinarith [ show ( w_2 : ℝ ) + 1 ≤ num_blocks by norm_cast, show ( w_5 : ℝ ) + 1 ≤ size by norm_cast, show ( w_6 : ℝ ) + 1 ≤ size by norm_cast ];
        rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> rcases w_1 with ( _ | ⟨ z, _ | ⟨ w, w_1 ⟩ ⟩ ) <;> aesop;
        · cases right;
        · have := List.Sublist.length_le right; simp_all +decide ;
          rw [ es_block_length ] at this ; linarith;
        · unfold es_block at right; aesop;
        · have := ih ( x :: y :: w ) left_1 ; simp_all +decide;
          linarith;
      exact h_induction num_blocks;
    exact h_block_decreasing s hs_sub hs_sorted

/-
The sum of any decreasing subsequence in an es_partp is bounded by size * max_val.
-/
lemma es_partp_dec_sum_le (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (hbase : 0 ≤ base) :
  ∀ (s : List ℝ), List.Sublist s (es_partp base start_idx num_blocks size eps) → List.Sorted (· > ·) s →
  List.sum s ≤ (size : ℝ) * es_partp_max_val base start_idx num_blocks size eps := by
    intro s hs_sub hs_sorted
    have h_length : s.length ≤ size := by
      by_cases heps_pos : 0 < eps;
      · exact?;
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
    -- Any increasing subsequence of $L1 ++ L2$ is either entirely in $L1$, or it starts in $L1$ and extends into $L2$, or it is entirely in $L2$. Since $L1 < L2$, the sum in the second case is less than or equal to the sum of the maximum increasing subsequences of $L1$ and $L2$.
    have h_increasing_subseq : ∀ s : List ℝ, s.Sublist (L1 ++ L2) → s.Sorted (· < ·) → s.sum ≤ max_inc_sum L1 + max_inc_sum L2 := by
      -- Any increasing subsequence s of L1 ++ L2 can be split into an increasing subsequence s1 of L1 and an increasing subsequence s2 of L2.
      intros s hs hs_sorted
      obtain ⟨s1, s2, hs1, hs2, hs_split⟩ : ∃ s1 s2, s1.Sublist L1 ∧ s2.Sublist L2 ∧ s = s1 ++ s2 := by
        rw [ List.sublist_append_iff ] at hs ; aesop;
      -- Since $s1$ and $s2$ are increasing subsequences of $L1$ and $L2$ respectively, their sums are less than or equal to the maximum sums of $L1$ and $L2$.
      have hs1_sum : s1.sum ≤ max_inc_sum L1 := by
        unfold max_inc_sum;
        unfold Option.getD; aesop;
        · rw [ List.maximum ] at heq;
          rw [ List.argmax_eq_some_iff ] at heq ; aesop;
          exact left _ _ hs1 ( hs_sorted.sublist ( List.sublist_append_left _ _ ) ) rfl;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          exact False.elim <| heq s1 hs1 <| hs_sorted.sublist <| List.sublist_append_left _ _
      have hs2_sum : s2.sum ≤ max_inc_sum L2 := by
        -- Since $s2$ is an increasing subsequence of $L2$, its sum is less than or equal to the maximum sum of $L2$.
        have hs2_sorted : List.Sorted (· < ·) s2 := by
          replace hs_sorted := List.pairwise_append.mp ( hs_split ▸ hs_sorted ) ; aesop;
        have hs2_max : s2.sum ≤ ((L2.sublists.filter (fun s => List.Sorted (· < ·) s)).map List.sum).maximum.getD 0 := by
          unfold Option.getD; aesop;
          · exact List.le_maximum_of_mem ( List.mem_map.mpr ⟨ s2, List.mem_filter.mpr ⟨ List.mem_sublists.mpr hs2, by aesop ⟩, rfl ⟩ ) heq;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
        exact hs2_max;
      simpa only [ hs_split, List.sum_append ] using add_le_add hs1_sum hs2_sum;
    -- By definition of max_inc_sum, we know that there exist subsequences in L1 and L2 whose sums add up to max_inc_sum L1 + max_inc_sum L2.
    have h_exists_subseq : ∃ s1 s2 : List ℝ, s1.Sublist L1 ∧ s1.Sorted (· < ·) ∧ s2.Sublist L2 ∧ s2.Sorted (· < ·) ∧ s1.sum = max_inc_sum L1 ∧ s2.sum = max_inc_sum L2 ∧ (s1 ++ s2).Sublist (L1 ++ L2) ∧ (s1 ++ s2).Sorted (· < ·) := by
      -- By definition of max_inc_sum, we know that there exist subsequences in L1 and L2 whose sums are max_inc_sum L1 and max_inc_sum L2, respectively.
      obtain ⟨s1, hs1⟩ : ∃ s1 : List ℝ, s1.Sublist L1 ∧ s1.Sorted (· < ·) ∧ s1.sum = max_inc_sum L1 := by
        unfold max_inc_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num ⟩
      obtain ⟨s2, hs2⟩ : ∃ s2 : List ℝ, s2.Sublist L2 ∧ s2.Sorted (· < ·) ∧ s2.sum = max_inc_sum L2 := by
        unfold max_inc_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], List.nil_sublist _, List.sorted_nil, by norm_num ⟩;
      refine' ⟨ s1, s2, hs1.1, hs1.2.1, hs2.1, hs2.2.1, hs1.2.2, hs2.2.2, _, _ ⟩;
      · exact List.Sublist.append hs1.1 hs2.1;
      · rw [ List.Sorted ] at *;
        rw [ List.pairwise_append ] ; aesop;
        exact h _ ( left.subset a_1 ) _ ( left_1.subset a_2 );
    refine' le_antisymm _ _;
    · have h_max_inc_sum_def : max_inc_sum (L1 ++ L2) = (List.sublists (L1 ++ L2) |>.filter (fun s => List.Sorted (· < ·) s) |>.map List.sum |>.maximum.getD 0) := by
        exact?;
      unfold Option.getD at h_max_inc_sum_def; aesop;
      · have := List.maximum_mem heq; aesop;
        linarith [ h_increasing_subseq _ left_7 right_2 ];
      · rw [ List.maximum ] at heq;
        rw [ List.argmax_eq_none ] at heq ; aesop;
    · unfold max_inc_sum at *; aesop;
      have h_subseq : (w ++ w_1).sum ∈ List.map List.sum (List.filter (fun s => Decidable.decide (List.Sorted (· < ·) s)) (L1 ++ L2).sublists) := by
        aesop;
      have h_subseq : ∀ {l : List ℝ}, (w ++ w_1).sum ∈ l → (w ++ w_1).sum ≤ List.maximum l := by
        intros l hl; induction l <;> aesop;
        · simp +decide [ List.maximum_cons ];
        · simp_all +decide [ List.maximum_cons ];
      specialize h_subseq ‹_›; aesop;
      cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ) ) ( L1 ++ L2 ).sublists ) ) <;> aesop;
      exact WithBot.coe_le_coe.mp h_subseq

/-
Every element in an es_partp corresponds to an index in the range.
-/
lemma exists_idx_of_mem_es_partp (base : ℝ) (start_idx : ℕ) (num_blocks size : ℕ) (eps : ℝ) :
  ∀ x ∈ es_partp base start_idx num_blocks size eps, ∃ i : ℕ, start_idx ≤ i ∧ i < start_idx + num_blocks * size ∧ x = base + i * eps := by
    unfold es_partp; aesop;
    unfold es_block at right; aesop;
    use start_idx + w * size + (size - 1 - w_2);
    norm_num;
    exact ⟨ by nlinarith, by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ size ), Nat.sub_add_cancel ( by omega : w_2 ≤ size - 1 ) ], Or.inl <| by rw [ Nat.cast_sub <| by omega, Nat.cast_sub <| by omega ] ; push_cast ; ring ⟩

/-
If L1 > L2, then max_inc_sum(L1 ++ L2) = max(max_inc_sum(L1), max_inc_sum(L2)).
-/
lemma max_inc_sum_append_of_gt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x > y) :
  max_inc_sum (L1 ++ L2) = max (max_inc_sum L1) (max_inc_sum L2) := by
    -- Any increasing subsequence in L1 ++ L2 must be entirely within L1 or entirely within L2.
    have h_cases : ∀ s : List ℝ, s.Sublist (L1 ++ L2) → s.Sorted (· < ·) → s.Sublist L1 ∨ s.Sublist L2 := by
      intro s hs hs'; rw [ List.sublist_append_iff ] at hs; aesop;
      rcases w with ( _ | ⟨ x, w ⟩ ) <;> rcases w_1 with ( _ | ⟨ y, w_1 ⟩ ) <;> simp_all +decide [ List.Sorted ];
      have := hs'.1 y ( by aesop ) ; have := h x ( left_1.subset ( by aesop ) ) y ( right.subset ( by aesop ) ) ; linarith;
    -- Therefore, the maximum sum of an increasing subsequence in L1 ++ L2 is the maximum of the maximum sums of L1 and L2.
    have h_max : ∀ s : List ℝ, s.Sublist (L1 ++ L2) → s.Sorted (· < ·) → s.sum ≤ max (max_inc_sum L1) (max_inc_sum L2) := by
      intro s hs hs'; specialize h_cases s hs hs'; aesop;
      · unfold max_inc_sum;
        unfold Option.getD; aesop;
        · have := List.argmax_eq_some_iff.mp heq; aesop;
        · rw [ List.maximum ] at heq;
          rw [ List.argmax_eq_some_iff ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
      · -- Since $s$ is a sublist of $L2$ and sorted, it is also a sublist of $L2$ and sorted, so its sum is less than or equal to the maximum sum of an increasing subsequence in $L2$.
        have h_max_L2 : s.sum ≤ ((L2.sublists.filter (fun s => List.Sorted (· < ·) s)).map List.sum).maximum.getD 0 := by
          unfold Option.getD; aesop;
          · have := List.argmax_eq_some_iff.mp heq; aesop;
          · simp_all +decide [ List.maximum ];
            rw [ List.argmax_eq_none ] at heq ; aesop;
        exact Or.inr h_max_L2;
    refine' le_antisymm _ _;
    · unfold max_inc_sum;
      unfold Option.getD; aesop;
      · have := List.maximum_mem heq; aesop;
        specialize h_max w left right_1 ; aesop;
        · unfold max_inc_sum at h_1; aesop;
        · unfold max_inc_sum at h_2; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq_2 ; aesop;
        specialize heq_2 [ ] ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq_1 ; aesop;
        exact False.elim <| heq_1 [ ] ( List.nil_sublist _ ) <| List.sorted_nil;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq_1 heq_2 ; aesop;
        specialize heq_1 [ ] ; specialize heq_2 [ ] ; aesop;
      · rw [ List.maximum ] at *;
        rw [ List.argmax_eq_none ] at heq ; aesop;
        contrapose! heq; aesop;
        exact ⟨ [ ], List.nil_sublist _, List.sorted_nil ⟩;
    · cases max_cases ( max_inc_sum L1 ) ( max_inc_sum L2 ) <;> aesop;
      · unfold max_inc_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; have := List.maximum_mem heq_1; aesop;
          exact List.le_maximum_of_mem ( by aesop ) heq_1;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq_1 ; aesop;
          specialize heq_1 [ ] ; aesop;
        · rw [ List.maximum ] at *;
          rw [ List.argmax_eq_none ] at heq ; aesop;
          specialize heq [ ] ; aesop;
      · unfold max_inc_sum;
        unfold Option.getD; aesop;
        · rw [ List.maximum ] at *;
          rw [ List.argmax_eq_some_iff ] at * ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq_1 ; aesop;
          contrapose! heq_1;
          exact ⟨ [ ], List.nil_sublist _, List.sorted_nil ⟩;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          exact absurd ( heq [ ] ( by norm_num ) ( by norm_num ) ) ( by norm_num )

/-
If L1 < L2, then max_dec_sum(L1 ++ L2) = max(max_dec_sum(L1), max_dec_sum(L2)).
-/
lemma max_dec_sum_append_of_lt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x < y) :
  max_dec_sum (L1 ++ L2) = max (max_dec_sum L1) (max_dec_sum L2) := by
    -- Any decreasing subsequence of $L1 ++ L2$ can be split into a decreasing subsequence of $L1$ and a decreasing subsequence of $L2$.
    have h_split : ∀ s : List ℝ, List.Sublist s (L1 ++ L2) → List.Sorted (· > ·) s → List.sum s ≤ max (max_dec_sum L1) (max_dec_sum L2) := by
      intros s hs_sub hs_sorted
      have h_split : ∃ s1 s2 : List ℝ, s1.Sublist L1 ∧ s2.Sublist L2 ∧ s = s1 ++ s2 ∧ List.Sorted (· > ·) s1 ∧ List.Sorted (· > ·) s2 := by
        have h_split : ∃ s1 s2 : List ℝ, s1.Sublist L1 ∧ s2.Sublist L2 ∧ s = s1 ++ s2 := by
          rw [ List.sublist_append_iff ] at hs_sub ; aesop;
        obtain ⟨ s1, s2, hs1, hs2, rfl ⟩ := h_split; use s1, s2; aesop;
        · exact hs_sorted.sublist ( List.sublist_append_left _ _ );
        · exact hs_sorted.sublist ( List.sublist_append_right _ _ );
      obtain ⟨ s1, s2, hs1, hs2, rfl, hs1', hs2' ⟩ := h_split; simp_all +decide [ List.sublists_append ] ;
      have h_split_sum : ∀ s : List ℝ, List.Sublist s L1 → List.Sorted (· > ·) s → List.sum s ≤ max_dec_sum L1 := by
        unfold max_dec_sum; aesop;
        unfold Option.getD; aesop;
        · rw [ List.maximum ] at heq;
          rw [ List.argmax_eq_some_iff ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop
      have h_split_sum' : ∀ s : List ℝ, List.Sublist s L2 → List.Sorted (· > ·) s → List.sum s ≤ max_dec_sum L2 := by
        unfold max_dec_sum; aesop;
        unfold Option.getD; aesop;
        · have := List.argmax_eq_some_iff.mp heq; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop
      exact Classical.or_iff_not_imp_left.2 fun h => by
        by_cases h1 : s1 = [] <;> by_cases h2 : s2 = [] <;> simp_all +decide [ List.Sorted ];
        · apply le_trans (by norm_num) (h_split_sum' [] (by simp) (by simp));
        · rw [ List.pairwise_append ] at hs_sorted ; aesop;
          exact absurd ( hs_sorted _ ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr h1 ) ) ) _ ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr h2 ) ) ) ) ( by linarith [ h_1 _ ( hs1.subset ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr h1 ) ) ) ) _ ( hs2.subset ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr h2 ) ) ) ) ] );
    refine' le_antisymm _ _;
    · unfold max_dec_sum;
      cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 > x2 ) s ) ) ( L1 ++ L2 |> List.sublists ) ) ) <;> aesop;
      · contrapose! h;
        exact ⟨ [ ], List.nil_sublist _, List.sorted_nil ⟩;
      · have := List.maximum_mem h; aesop;
    · unfold max_dec_sum at *; aesop;
      · unfold Option.getD; aesop;
        · have := List.argmax_eq_some_iff.mp heq; aesop;
          have := List.le_maximum_of_mem ( List.mem_map.mpr ⟨ w, ?_, rfl ⟩ ) heq_1; aesop;
          simp +decide [ List.mem_filter, List.mem_sublists, left_1, right_2 ];
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq_1 ; aesop;
          rw [ List.argmax_eq_some_iff ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          specialize heq [ ] ; aesop;
      · unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
          have := List.argmax_eq_some_iff.mp heq_1; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq_1 ; aesop;
          rw [ List.argmax_eq_some_iff ] at heq ; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
          specialize heq [ ] ; aesop

/-
If L1 > L2, then max_dec_sum(L1 ++ L2) = max_dec_sum(L1) + max_dec_sum(L2).
-/
lemma max_dec_sum_append_of_gt (L1 L2 : List ℝ) (h : ∀ x ∈ L1, ∀ y ∈ L2, x > y) :
  max_dec_sum (L1 ++ L2) = max_dec_sum L1 + max_dec_sum L2 := by
    apply le_antisymm;
    · have h_max_dec_sum_append : ∀ (s : List ℝ), s.Sublist (L1 ++ L2) → s.Sorted (· > ·) → s.sum ≤ max_dec_sum L1 + max_dec_sum L2 := by
        intros s hs_sub hs_sorted
        have h_split : ∃ s1 s2 : List ℝ, s = s1 ++ s2 ∧ s1.Sublist L1 ∧ s2.Sublist L2 ∧ s1.Sorted (· > ·) ∧ s2.Sorted (· > ·) := by
          have h_split : ∃ s1 s2 : List ℝ, s = s1 ++ s2 ∧ s1.Sublist L1 ∧ s2.Sublist L2 := by
            exact?;
          obtain ⟨ s1, s2, rfl, hs1, hs2 ⟩ := h_split; exact ⟨ s1, s2, rfl, hs1, hs2, hs_sorted.sublist ( List.sublist_append_left _ _ ), hs_sorted.sublist ( List.sublist_append_right _ _ ) ⟩ ;
        aesop;
        refine' add_le_add _ _;
        · refine' List.le_maximum_of_mem _ _;
          exact ( L1.sublists.filter ( fun s => List.Sorted ( · > · ) s ) |> List.map List.sum );
          · aesop;
          · unfold max_dec_sum; aesop;
            cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) s ) ) L1.sublists ) ) <;> aesop;
        · refine' List.le_maximum_of_mem _ _;
          exact ( L2.sublists.filter ( fun s => List.Sorted ( · > · ) s ) |> List.map List.sum );
          · aesop;
          · unfold max_dec_sum; aesop;
            cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) s ) ) L2.sublists ) ) <;> aesop;
      contrapose! h_max_dec_sum_append;
      have h_max_dec_sum_append : ∃ s ∈ (L1 ++ L2).sublists.filter (fun s => s.Sorted (· > ·)), s.sum = max_dec_sum (L1 ++ L2) := by
        unfold max_dec_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], by norm_num ⟩;
      aesop;
    · -- Let $s_1$ be an increasing subsequence of $L1$ with maximum sum, and $s_2$ be an increasing subsequence of $L2$ with maximum sum.
      obtain ⟨s1, hs1⟩ : ∃ s1 : List ℝ, s1 ∈ (L1.sublists.filter (fun s => List.Sorted (· > ·) s)) ∧ List.sum s1 = max_dec_sum L1 := by
        unfold max_dec_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], by norm_num ⟩
      obtain ⟨s2, hs2⟩ : ∃ s2 : List ℝ, s2 ∈ (L2.sublists.filter (fun s => List.Sorted (· > ·) s)) ∧ List.sum s2 = max_dec_sum L2 := by
        unfold max_dec_sum;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
        · exact ⟨ [ ], by aesop ⟩;
      -- Since $s1$ and $s2$ are subsequences of $L1$ and $L2$ respectively, their concatenation $s1 ++ s2$ is a subsequence of $L1 ++ L2$.
      have h_concat : s1 ++ s2 ∈ (L1 ++ L2).sublists.filter (fun s => List.Sorted (· > ·) s) := by
        aesop;
        · exact List.Sublist.append left left_1;
        · rw [ List.Sorted ] at *;
          grind +ring;
      have h_concat_sum : List.sum (s1 ++ s2) ≤ Option.getD (List.map List.sum (List.filter (fun s => List.Sorted (· > ·) s) (L1 ++ L2).sublists)).maximum 0 := by
        unfold Option.getD; aesop;
        · have := List.le_maximum_of_mem ( List.mem_map.mpr ⟨ s1 ++ s2, List.mem_filter.mpr ⟨ List.mem_sublists.mpr left_2, by aesop ⟩, rfl ⟩ ) heq; aesop;
        · simp_all ( config := { decide := Bool.true } ) [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
      aesop

/-
Elements of part1p are greater than elements of part2p.
-/
lemma part1p_gt_part2p (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  ∀ x ∈ part1p k a eps, ∀ y ∈ part2p k a eps, x > y := by
    unfold part1p part2p; aesop;
    obtain ⟨ i, hi₁, hi₂, rfl ⟩ := exists_idx_of_mem_es_partp ( a + 1 ) 0 a ( k - a ) eps _ a_1 ; obtain ⟨ j, hj₁, hj₂, rfl ⟩ := exists_idx_of_mem_es_partp a ( a * ( k - a ) ) ( a + 1 ) ( a + 1 ) eps _ a_2;
    -- Since $j < a * (k - a) + (a + 1) * (a + 1)$ and $eps * (k^2 + 2 * a + 1) < 1$, we have $j * eps < 1$.
    have h_j_eps_lt_1 : (j : ℝ) * eps < 1 := by
      refine' lt_of_le_of_lt _ heps_small;
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
    · exact?;
    · exact?

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
    refine' le_trans ( M_eq_max _ |> Eq.le ) _;
    -- Applying the lemmas for max_inc_sum and max_dec_sum constructions:
    have h_max_inc : max_inc_sum (construction k a eps) ≤ (k : ℝ) * (a + 1) + eps * (k^2 + 2*a + 1)^3 := by
      -- By Lemma 2, we know that the maximum increasing subsequence sum is bounded by the sum of the maximum increasing subsequences of each part.
      have h_part1p : max_inc_sum (part1p k a eps) ≤ (a : ℝ) * ((a + 1) + (a * (k - a)) * eps) := by
        have := es_partp_inc_sum_le ( a + 1 ) 0 a ( k - a ) eps ( by positivity ) ( by positivity );
        unfold max_inc_sum; aesop;
        unfold Option.getD; aesop;
        · have := List.maximum_mem heq; aesop;
          convert this_1 w left right_1 using 1 ; unfold es_partp_max_val ; ring;
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
          convert this using 2 ; ring;
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
            · exact?;
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
      · exact?;
      · exact?;
    aesop

/-
M(L + c) <= M(L) + length(L) * cp for cp >= 0.
-/
lemma M_shift (L : List ℝ) (cp : ℝ) (hc : 0 ≤ cp) :
  Mp (L.map (· + cp)) ≤ Mp L + L.length * cp := by
    unfold Mp;
    -- The sum of a sequence in $L + c$ is equal to the sum of the corresponding sequence in $L$ plus the sum of $c$ over the length of the sequence.
    have h_sum_eq : ∀ s ∈ (List.map (fun x => x + cp) L).sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s), ∃ s' ∈ L.sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s), s.length = s'.length ∧ s.sum = s'.sum + s.length * cp := by
      aesop;
      · -- Let $s'$ be the sublist of $L$ corresponding to $s$.
        obtain ⟨s', hs'⟩ : ∃ s' : List ℝ, s = s'.map (fun x => x + cp) := by
          have h_sublist : ∀ {s : List ℝ}, s.Sublist (List.map (fun x => x + cp) L) → ∃ s' : List ℝ, s = s'.map (fun x => x + cp) := by
            grind;
          exact h_sublist left;
        use s'; aesop;
        · rw [ List.sublist_map_iff ] at * ; aesop;
          rw [ List.map_inj_right ] at right <;> aesop;
        · simp_all +decide [ List.Sorted ];
          simp_all +decide [ List.pairwise_map ];
      · use List.map (fun x => x - cp) s;
        aesop;
        · have := left.map ( fun x => x - cp );
          convert this using 1 ; ext x ; aesop;
        · simp_all +decide [ List.Sorted ];
          simp_all +decide [ List.pairwise_map ];
        · simp ( config := { decide := Bool.true } ) [ sub_eq_add_neg, List.sum_map_add ];
    -- Using the equality of sums, we can bound the maximum sum.
    have h_max_sum_bound : ∀ s ∈ (List.map (fun x => x + cp) L).sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s), s.sum ≤ (List.map List.sum (L.sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s))).maximum.getD 0 + (L.length : ℝ) * cp := by
      intros s hs
      obtain ⟨s', hs', hs_len, hs_sum⟩ := h_sum_eq s hs
      have h_max_sum_bound : s'.sum ≤ (List.map List.sum (L.sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s))).maximum.getD 0 := by
        have h_max_sum_bound : ∀ {l : List ℝ}, s'.sum ∈ l → s'.sum ≤ List.maximum l := by
          exact?;
        convert h_max_sum_bound _;
        any_goals exact List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ∨ List.Sorted ( fun x1 x2 => x1 > x2 ) s ) ) L.sublists );
        · cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ∨ List.Sorted ( fun x1 x2 => x1 > x2 ) s ) ) L.sublists ) ) <;> aesop;
        · exact List.mem_map.mpr ⟨ s', hs', rfl ⟩;
      norm_num +zetaDelta at *;
      exact hs_sum.symm ▸ add_le_add h_max_sum_bound ( mul_le_mul_of_nonneg_right ( mod_cast hs_len.symm ▸ hs'.1.length_le ) hc );
    cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ∨ List.Sorted ( fun x1 x2 => x1 > x2 ) s ) ) ( List.map ( fun x => x + cp ) L |> List.sublists ) ) ) <;> aesop;
    · specialize h [ ] ; aesop;
    · have := List.maximum_mem h; aesop;

/-
Elements of construction are non-negative.
-/
lemma construction_nonneg (k a : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
  ∀ x ∈ construction k a eps, 0 ≤ x := by
    unfold construction; aesop;
    · obtain ⟨ i, hi ⟩ := exists_idx_of_mem_es_partp _ _ _ _ _ _ h;
      nlinarith;
    · unfold es_partp at h; aesop;
      unfold es_block at right; aesop;
      exact add_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith ) ) ) ) heps );
    · unfold es_partp at h_2; aesop;
      unfold es_block at right; aesop;
      exact add_nonneg ( by positivity ) ( mul_nonneg ( by nlinarith [ show ( w_2 : ℝ ) < k by norm_cast ] ) heps )

/-
M(construction_pos) is bounded by k(a+1) + eps * (n^3 + n).
-/
lemma M_construction_pos_le (k a : ℕ) (eps : ℝ) (hak : a ≤ k) (heps_pos : 0 < eps) (heps_small : eps * ((k^2 + 2*a + 1 : ℕ) : ℝ) < 1) :
  Mp (construction_pos k a eps) ≤ (k : ℝ) * ((a : ℝ) + 1) + eps * ((k^2 + 2*a + 1 : ℕ) : ℝ)^3 + ((k^2 + 2*a + 1 : ℕ) : ℝ) * eps := by
    unfold construction_pos;
    have h_len : (construction k a eps).length = k^2 + 2*a + 1 := construction_length k a eps hak;
    rw [ ← h_len ];
    refine' le_trans ( M_shift _ _ heps_pos.le ) _;
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
      refine' tendsto_nhdsWithin_of_tendsto_nhds _;
      convert Filter.Tendsto.div ( Continuous.tendsto _ _ ) ( Continuous.tendsto _ _ ) _ using 2 <;> norm_num;
      exacts [ by rw [ div_eq_div_iff ] <;> ring <;> positivity, by infer_instance, by infer_instance, by continuity, by continuity, ⟨ by positivity, by positivity ⟩ ];
    refine' le_of_tendsto_of_tendsto tendsto_const_nhds h_limit _;
    rw [ Filter.EventuallyLE, eventually_nhdsWithin_iff ];
    filter_upwards [ gt_mem_nhds <| show 0 < 1 / ( ( k^2 + 2*a + 1 : ℝ ) ) from by positivity ] with x hx₁ hx₂ ; aesop;
    refine' le_trans ( csInf_le _ ⟨ construction_pos k a x, _, _, _, rfl ⟩ ) _;
    · exact ⟨ 0, by rintro _ ⟨ L, hL₁, hL₂, hL₃, rfl ⟩ ; exact div_nonneg ( by
        unfold Mp;
        unfold Option.getD; aesop;
        have := List.maximum_mem heq; aesop;
        · exact List.sum_nonneg fun x hx => le_of_lt ( hL₃ x ( left.subset hx ) );
        · exact List.sum_nonneg fun x hx => le_of_lt ( hL₃ x ( left.subset hx ) ) ) ( List.sum_nonneg fun x hx => le_of_lt ( hL₃ x hx ) ) ⟩;
    · unfold construction_pos;
      rw [ List.length_map, construction_length ] ; linarith;
    · refine' List.Nodup.map _ _;
      · exact add_left_injective x;
      · refine' construction_nodup k a x hx₂ _;
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
  rw [ M_eq_max ];
  -- The maximum of two non-negative numbers is non-negative.
  apply le_max_of_le_left;
  by_contra h_neg;
  unfold max_inc_sum at h_neg;
  unfold Option.getD at h_neg ; aesop;
  rw [ List.maximum ] at heq;
  rw [ List.argmax_eq_some_iff ] at heq ; aesop;
  specialize left 0 [ ] ; aesop;
  linarith

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
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 1 + |b| + |x|;
            · exact Continuous.integrableOn_Ioc ( by continuity );
            · apply_rules [ Measurable.aestronglyMeasurable, measurable_const ];
              exact Measurable.comp ( by measurability ) ( Measurable.floor ( measurable_const.sub measurable_id' ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using abs_le.mpr ⟨ by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ], by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ] ⟩;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 1 + |b| + |x|;
            · exact Continuous.integrableOn_Ioc ( by continuity );
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( measurable_id'.const_sub _ |> Measurable.floor ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using abs_le.mpr ⟨ by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ], by cases abs_cases b <;> cases abs_cases x <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ] ⟩;
        -- In the first interval, $\lfloor b-x \rfloor = k$ and in the second interval, $\lfloor b-x \rfloor = k-1$.
        have h_floor_values : (∫ x in Set.Ioo 0 δ, (⌊b - x⌋ : ℝ)) = (∫ x in Set.Ioo 0 δ, (k : ℝ)) ∧ (∫ x in Set.Ioo δ 1, (⌊b - x⌋ : ℝ)) = (∫ x in Set.Ioo δ 1, (k - 1 : ℝ)) := by
          constructor <;> refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => _ <;> aesop;
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
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 2 + |a| + ε;
            · norm_num;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact Measurable.ceil ( by exact measurable_const.sub measurable_id' ) ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> cases abs_cases a <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ), hx.1, hx.2 ] ;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 2 + |a| + |x|;
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
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => |b - x| + 1;
        · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.Ioo_subset_Icc_self;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact measurable_id'.const_sub _ |> Measurable.floor ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using abs_le.mpr ⟨ by cases abs_cases ( b - x ) <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ], by cases abs_cases ( b - x ) <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ) ] ⟩;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => 2 + |a| + |b|;
        · norm_num;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact measurable_id'.const_sub _ |> Measurable.ceil ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using by rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [ Int.le_ceil ( a - x ), Int.ceil_lt_add_one ( a - x ), hx.1, hx.2 ] ;
      · refine' MeasureTheory.Integrable.sub _ _;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun x => 2 + |b|;
          · norm_num;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( by measurability ) ( by exact measurable_id'.const_sub _ |> Measurable.floor ) );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using abs_le.mpr ⟨ by cases abs_cases b <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ), hx.1, hx.2 ], by cases abs_cases b <;> linarith [ Int.floor_le ( b - x ), Int.lt_floor_add_one ( b - x ), hx.1, hx.2 ] ⟩;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun x => 2 + |a| + |b|;
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
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => |b i - a i| + 1;
        · norm_num;
        · -- The function num_points is a composition of measurable functions (floor and ceiling), hence it is measurable.
          have h_num_points_measurable : Measurable (fun x => num_points (a i) (b i) x) := by
            exact Measurable.add ( Measurable.sub ( Measurable.floor ( measurable_const.sub measurable_id' ) ) ( Measurable.ceil ( measurable_const.sub measurable_id' ) ) ) measurable_const;
          exact Measurable.aestronglyMeasurable ( by measurability );
        · refine' MeasureTheory.ae_of_all _ _ ; aesop;
          refine' abs_le.mpr ⟨ _, _ ⟩ <;> norm_num [ num_points ] <;> cases abs_cases ( b i - a i ) <;> linarith [ Int.floor_le ( b i - a_1 ), Int.lt_floor_add_one ( b i - a_1 ), Int.le_ceil ( a i - a_1 ), Int.ceil_lt_add_one ( a i - a_1 ) ] ;
    -- By contradiction, assume that for all $x \in [0, 1) \setminus Bad$, $\sum_{i=1}^n num\_points(a_i, b_i, x) < \sum_{i=1}^n (b_i - a_i)$.
    by_contra h_contra;
    have h_integral_lt : ∫ x in (Set.Ioo 0 1) \ Bad, (∑ i, (num_points (a i) (b i) x : ℝ)) < ∫ x in (Set.Ioo 0 1) \ Bad, (∑ i, (b i - a i) : ℝ) := by
      apply lt_of_sub_pos;
      rw [ ← MeasureTheory.integral_sub ];
      · rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
        · simp_all ( config := { decide := Bool.true } ) [ Function.support ];
          refine' ( lt_of_lt_of_le _ ( MeasureTheory.measure_mono _ ) );
          rotate_left;
          exact Set.Ioo 0 1 \ Bad;
          · exact fun x hx => ne_of_gt <| sub_pos_of_lt <| by linarith [ h_contra x hx.1.1.le hx.1.2 hx.2 ] ;
          · simp +zetaDelta at *;
            rw [ MeasureTheory.measure_diff_null ] <;> norm_num;
            exact hBad.measure_zero MeasureTheory.MeasureSpace.volume;
        · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioo.diff hBad.measurableSet ) ] with x hx using sub_nonneg_of_le <| le_of_not_ge fun hx' => h_contra ⟨ x, hx.1.1.le, hx.1.2, hx.2, hx' ⟩;
        · refine' MeasureTheory.Integrable.sub _ _;
          · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.diff_subset.trans <| Set.Ioo_subset_Icc_self;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => ∑ i, ( b i - a i + 2 );
            · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.diff_subset.trans <| Set.Ioo_subset_Icc_self;
            · refine' Measurable.aestronglyMeasurable _;
              refine' Finset.measurable_sum _ fun i _ => _;
              refine' Measurable.comp ( show Measurable fun x : ℤ => ( x : ℝ ) from by measurability ) _;
              exact Measurable.add ( Measurable.sub ( Measurable.floor ( measurable_const.sub measurable_id' ) ) ( Measurable.ceil ( measurable_const.sub measurable_id' ) ) ) measurable_const;
            · filter_upwards [ MeasureTheory.ae_restrict_mem <| measurableSet_Ioo.diff hBad.measurableSet ] with x hx;
              rw [ Real.norm_of_nonneg ];
              · refine Finset.sum_le_sum fun i _ => ?_;
                simp +zetaDelta at *;
                exact le_trans ( Int.cast_le.mpr <| show num_points ( a i ) ( b i ) x ≤ ⌊b i - x⌋ - ⌈a i - x⌉ + 1 from le_rfl ) <| by push_cast [ num_points ] ; linarith [ Int.floor_le ( b i - x ), Int.lt_floor_add_one ( b i - x ), Int.le_ceil ( a i - x ), Int.ceil_lt_add_one ( a i - x ) ] ;
              · refine' Finset.sum_nonneg fun i _ => _;
                unfold num_points;
                exact_mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( b i - x ), Int.lt_floor_add_one ( b i - x ), Int.le_ceil ( a i - x ), Int.ceil_lt_add_one ( a i - x ), hab i ] );
      · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.diff_subset.trans <| Set.Ioo_subset_Icc_self;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => ∑ i, ( b i - a i + 1 );
        · norm_num +zetaDelta at *;
          exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.diff_subset.trans <| Set.Ioo_subset_Icc_self );
        · refine' Measurable.aestronglyMeasurable _;
          refine' Finset.measurable_sum _ fun i _ => _;
          exact Measurable.comp ( by measurability ) ( show Measurable fun x => num_points ( a i ) ( b i ) x from by exact Measurable.sub ( Int.measurable_floor.comp ( measurable_const.sub measurable_id' ) ) ( Int.measurable_ceil.comp ( measurable_const.sub measurable_id' ) ) |> Measurable.add <| measurable_const );
        · filter_upwards [ MeasureTheory.ae_restrict_mem <| measurableSet_Ioo.diff <| hBad.measurableSet ] with x hx;
          rw [ Real.norm_of_nonneg ];
          · exact le_trans ( le_of_not_lt fun h => h_contra ⟨ x, hx.1.1.le, hx.1.2, hx.2, h.le ⟩ ) ( Finset.sum_le_sum fun i _ => show ( b i - a i : ℝ ) ≤ b i - a i + 1 by linarith );
          · refine' Finset.sum_nonneg fun i _ => _;
            unfold num_points;
            exact_mod_cast Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( b i - x ), Int.lt_floor_add_one ( b i - x ), Int.le_ceil ( a i - x ), Int.ceil_lt_add_one ( a i - x ), hab i ] );
    rw [ MeasureTheory.setIntegral_congr_set ] at h_integral_lt;
    any_goals exact Set.Ioo 0 1;
    · simp_all +decide [ MeasureTheory.integral_diff, hBad.measure_zero ];
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
      exact ⟨ ⟨ Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( P i |> Square.x ) ≥ 0 by exact ( P i |> Square.x_nonneg ), show ( P i |> Square.s ) ≥ 0 by exact ( P i |> Square.s_nonneg ) ] ), Int.le_sub_one_of_lt ( by rw [ ← @Int.cast_lt ℝ ] ; nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( P i |> Square.x ) + ( P i |> Square.s ) ≤ 1 by exact ( P i |> Square.x_plus_s_le_one ) ] ) ⟩, ⟨ Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( P i |> Square.y ) ≥ 0 by exact ( P i |> Square.y_nonneg ), show ( P i |> Square.s ) ≥ 0 by exact ( P i |> Square.s_nonneg ) ] ), Int.le_sub_one_of_lt ( by rw [ ← @Int.cast_lt ℝ ] ; nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( P i |> Square.y ) + ( P i |> Square.s ) ≤ 1 by exact ( P i |> Square.y_plus_s_le_one ) ] ) ⟩ ⟩;
    have h_card_union : Finset.card (Finset.biUnion Finset.univ (fun i => Finset.product (Finset.Icc (⌈k * (P i).x - x⌉) (⌊k * ((P i).x + (P i).s) - x⌋)) (Finset.Icc (⌈k * (P i).y - y⌉) (⌊k * ((P i).y + (P i).s) - y⌋)))) = ∑ i : Fin n, (⌊k * ((P i).x + (P i).s) - x⌋ - ⌈k * (P i).x - x⌉ + 1) * (⌊k * ((P i).y + (P i).s) - y⌋ - ⌈k * (P i).y - y⌉ + 1) := by
      rw [ Finset.card_biUnion ];
      · norm_num [ Finset.card_product ];
        refine' Finset.sum_congr rfl fun i _ => _;
        rw [ max_eq_left, max_eq_left ];
        · ring;
        · simp +zetaDelta at *;
          exact Int.ceil_le.mpr ( by norm_num; linarith [ show ( k : ℝ ) * ( P i |> Square.s ) ≥ 0 by exact mul_nonneg ( Int.cast_nonneg.mpr hk.le ) ( P i |> Square.s_nonneg ), Int.floor_le ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y ), Int.lt_floor_add_one ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y ) ] );
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
      · refine' lt_of_le_of_ne ( Int.floor_le _ ) _;
        exact fun h => ha <| by linarith [ Int.fract_add_floor a, Int.fract_add_floor ( a - x ), show ( ⌊a⌋ : ℝ ) = ⌊a - x⌋ by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith [ Int.floor_le ( a - x ), Int.lt_floor_add_one ( a - x ) ], by linarith [ Int.floor_le ( a - x ), Int.lt_floor_add_one ( a - x ) ] ⟩ ] ;
      · linarith [ Int.lt_floor_add_one ( a - x ) ];
    unfold num_points at h_contra; simp_all +decide [ Int.floor_eq_iff, Int.ceil_eq_iff ] ;
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
        -- Define `BadX` as the set of fractional parts of $k x_i$ and $k(x_i+s_i)$, and similarly `BadY`.
        set BadX : Set ℝ := {Int.fract ((k : ℝ) * (P i).x) | i : Fin n} ∪ {Int.fract ((k : ℝ) * ((P i).x + (P i).s)) | i : Fin n}
        set BadY : Set ℝ := {Int.fract ((k : ℝ) * (P i).y) | i : Fin n} ∪ {Int.fract ((k : ℝ) * ((P i).y + (P i).s)) | i : Fin n};
        -- By `exists_shift_sum_ge`, we find $x_0 \in [0, 1) \setminus BadX$ such that $\sum p_i(x_0) \ge \sum D_i$.
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ Set.Ioo 0 1, x₀ ∉ BadX ∧ (∑ i, (num_points ((k : ℝ) * (P i).x) ((k : ℝ) * ((P i).x + (P i).s)) x₀ : ℝ)) ≥ ∑ i, ((k : ℝ) * (P i).s) := by
          -- By `exists_shift_sum_ge`, we find $x_0 \in [0, 1) \setminus BadX$ such that $\sum p_i(x_0) \ge \sum D_i$. Use this lemma.
          have := exists_shift_sum_ge n (fun i => (k : ℝ) * (P i).x) (fun i => (k : ℝ) * ((P i).x + (P i).s)) (fun i => by
            exact mul_le_mul_of_nonneg_left ( by linarith [ ( P i ).s_nonneg ] ) ( by positivity )) (BadX ∪ {0}) (by
          exact Set.Finite.union ( Set.Finite.union ( Set.toFinite ( Set.range fun i : Fin n => Int.fract ( ( k : ℝ ) * ( P i |> Square.x ) ) ) ) ( Set.toFinite ( Set.range fun i : Fin n => Int.fract ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) ) ) ) ) ( Set.finite_singleton 0 ));
          grind;
        -- Define p_i as the number of integer points in the shifted interval [kx_i - x₀, k(x_i+s_i) - x₀].
        set p : Fin n → ℤ := fun i => num_points ((k : ℝ) * (P i).x) ((k : ℝ) * ((P i).x + (P i).s)) x₀;
        -- By `exists_shift_sum_ge`, we find $y_0 \in [0, 1) \setminus BadY$ such that $\sum q_i(y_0) \ge \sum D_i$.
        obtain ⟨y₀, hy₀⟩ : ∃ y₀ ∈ Set.Ioo 0 1, y₀ ∉ BadY ∧ (∑ i, (num_points ((k : ℝ) * (P i).y) ((k : ℝ) * ((P i).y + (P i).s)) y₀ : ℝ)) ≥ ∑ i, ((k : ℝ) * (P i).s) := by
          norm_num +zetaDelta at *;
          have := exists_shift_sum_ge n ( fun i => ( k : ℝ ) * ( P i |> Square.y ) ) ( fun i => ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ) ( fun i => mul_le_mul_of_nonneg_left ( by linarith [ ( P i |> Square.s_nonneg ) ] ) <| Int.cast_nonneg.mpr hk.le ) ( BadY ∪ { 0 } ) ?_;
          · obtain ⟨ y₀, hy₀₁, hy₀₂, hy₀₃, hy₀₄ ⟩ := this; use y₀; simp_all ( config := { decide := Bool.true } ) [ mul_add ] ;
            exact ⟨ lt_of_le_of_ne hy₀₁ ( Ne.symm hy₀₃.1 ), fun i hi => hy₀₃.2 <| Or.inl ⟨ i, hi ⟩, fun i hi => hy₀₃.2 <| Or.inr ⟨ i, by simpa [ mul_add ] using hi ⟩ ⟩;
          · exact Set.Finite.union ( Set.Finite.union ( Set.toFinite ( Set.range fun i => Int.fract ( ( k : ℝ ) * ( P i |> Square.y ) ) ) ) ( Set.toFinite ( Set.range fun i => Int.fract ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) ) ) ) ) ( Set.finite_singleton 0 );
        -- Define q_i as the number of integer points in the shifted interval [ky_i - y₀, k(y_i+s_i) - y₀].
        set q : Fin n → ℤ := fun i => num_points ((k : ℝ) * (P i).y) ((k : ℝ) * ((P i).y + (P i).s)) y₀;
        refine' ⟨ p, q, _, _, _, _, _ ⟩;
        · intro i; unfold p q; unfold num_points; aesop;
          · exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) - x₀ ), Int.lt_floor_add_one ( ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) ) - x₀ ), Int.le_ceil ( ( k : ℝ ) * ( P i |> Square.x ) - x₀ ), Int.ceil_lt_add_one ( ( k : ℝ ) * ( P i |> Square.x ) - x₀ ), show ( k : ℝ ) * ( P i |> Square.s ) ≥ 0 by exact mul_nonneg ( Int.cast_nonneg.mpr hk.le ) ( P i |> Square.s_nonneg ) ] );
          · norm_num [ sub_add ];
            exact Int.ceil_le.mpr ( by norm_num; linarith [ Int.floor_le ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y₀ ), Int.lt_floor_add_one ( ( k : ℝ ) * ( ( P i |> Square.y ) + ( P i |> Square.s ) ) - y₀ ), show ( k : ℝ ) * ( P i |> Square.s ) ≥ 0 by exact mul_nonneg ( Int.cast_nonneg.mpr hk.le ) ( P i |> Square.s_nonneg ) ] );
        · -- By `num_points_bounds`, we know that $p_i \in \{\lfloor D_i \rfloor, \lceil D_i \rceil\}$ and $q_i \in \{\lfloor D_i \rfloor, \lceil D_i \rceil\}$.
          have hpq_bounds : ∀ i, p i ∈ ({⌊(k : ℝ) * (P i).s⌋, ⌈(k : ℝ) * (P i).s⌉} : Set ℤ) ∧ q i ∈ ({⌊(k : ℝ) * (P i).s⌋, ⌈(k : ℝ) * (P i).s⌉} : Set ℤ) := by
            bound;
            · convert num_points_bounds _ _ _ ⟨ left.1.le, left.2 ⟩ _ _ using 1;
              rotate_left;
              exact ( k : ℝ ) * ( P i |> Square.x );
              exact ( k : ℝ ) * ( ( P i |> Square.x ) + ( P i |> Square.s ) );
              · exact fun h => left_2 <| Or.inl ⟨ i, h ⟩;
              · exact fun h => left_2 <| Or.inr ⟨ i, h ⟩;
              · grind;
            · simp +zetaDelta at *;
              convert num_points_bounds _ _ _ _ _ _ using 2 <;> ring;
              · constructor <;> linarith;
              · exact left_3.1 i;
              · simpa only [ mul_add ] using left_3.2 i;
          intro i; specialize hpq_bounds i; aesop;
          · exact abs_sub_le_iff.mpr ⟨ by linarith [ Int.floor_le_ceil ( ( k : ℝ ) * ( P i ).s ), Int.ceil_le_floor_add_one ( ( k : ℝ ) * ( P i ).s ) ], by linarith [ Int.floor_le_ceil ( ( k : ℝ ) * ( P i ).s ), Int.ceil_le_floor_add_one ( ( k : ℝ ) * ( P i ).s ) ] ⟩;
          · exact abs_sub_le_iff.mpr ⟨ by linarith [ Int.floor_le_ceil ( ( k : ℝ ) * ( P i |> Square.s ) ), Int.ceil_le_floor_add_one ( ( k : ℝ ) * ( P i |> Square.s ) ) ], by linarith [ Int.floor_le_ceil ( ( k : ℝ ) * ( P i |> Square.s ) ), Int.ceil_le_floor_add_one ( ( k : ℝ ) * ( P i |> Square.s ) ) ] ⟩;
        · exact Int.ceil_le.mpr ( mod_cast hx₀.2.2 );
        · exact Int.ceil_le.mpr ( mod_cast hy₀.2.2 );
        · convert lattice_points_disjoint_sum n k hk P h_valid x₀ y₀ ⟨ hx₀.1.1, hx₀.1.2 ⟩ ⟨ hy₀.1.1, hy₀.1.2 ⟩ _ _;
          · intro i z; constructor <;> intro h <;> simp_all +decide [ Int.fract_eq_iff ] ;
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
    rw [ show ( k ^ 2 + 2 * c + 1 |> Int.toNat ) = 0 by nlinarith [ Int.toNat_of_nonpos h_pos.le ] ] ; norm_num;
    refine' csSup_le _ _ <;> norm_num;
    · exact ⟨ 0, ⟨ fun _ => ⟨ 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num ⟩, by unfold Packing.is_valid; aesop ⟩ ⟩;
    · unfold Packing.total_side_length; aesop;
      rw [ add_div', le_div_iff₀ ] <;> norm_cast ; nlinarith;
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
    by_cases hM_pos : 0 < M;
    · refine' ⟨ fun i => ⟨ ( S i - x i ) / M, ( T i - x i ) / M, x i / M, _, _, _, _, _ ⟩, _, _ ⟩ <;> norm_num [ hM_pos, ne_of_gt, h_pos ];
      any_goals rw [ div_add_div_same, div_le_iff₀ ] <;> linarith [ hM_S i, hM_T i, hS_base i, hT_base i, h_pos i ];
      any_goals rw [ le_div_iff₀ ] <;> linarith [ h_pos i, hS_base i, hT_base i, hM_S i, hM_T i ];
      intro i j hij;
      cases lt_or_gt_of_ne hij <;> simp_all +decide [ Square.disjoint ];
      · cases lt_or_gt_of_ne ( h_inj.ne ‹_› ) <;> aesop;
        · exact Or.inl ( by rw [ ← add_div, div_le_div_iff_of_pos_right hM_pos ] ; linarith [ hS_cond i j h h_1 ] );
        · field_simp;
          exact Or.inr <| Or.inr <| Or.inl <| by linarith [ hT_cond i j h h_1 ] ;
      · field_simp;
        cases lt_or_gt_of_ne ( h_inj.ne ‹_› ) <;> first | exact Or.inl <| by linarith [ hS_cond _ _ ‹_› ‹_› ] | exact Or.inr <| Or.inl <| by linarith [ hS_cond _ _ ‹_› ‹_› ] | exact Or.inr <| Or.inr <| Or.inl <| by linarith [ hT_cond _ _ ‹_› ‹_› ] | exact Or.inr <| Or.inr <| Or.inr <| by linarith [ hT_cond _ _ ‹_› ‹_› ] ;
    · rcases n <;> aesop;
      · use fun _ => ⟨ 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num ⟩ ; simp +decide [ Packing.is_valid ] ;
      · linarith [ h_pos 0, hS_base 0, hM_S 0 ]

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
  -- Assume for contradiction that every monotone subsequence has sum strictly less than `target := k / (k^2 + a)`.
  have h_all_lt_target : ∀ m : ℕ, ∀ s : Fin (m + 1) → Fin n, StrictMono s → (Monotone (x ∘ s) ∨ Antitone (x ∘ s)) → (∑ i, x (s i)) < k / (k^2 + a : ℝ) := by
    aesop;
  -- Let `M = max (max_i S i) (max_i T i)`. Then `M < target`.
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
    · -- Since $S$ is a function from a finite set to $\mathbb{R}$, its range is finite.
      have hS_finite : Set.Finite (Set.range S) := by
        exact Set.toFinite _;
      have := hS_finite.isCompact.sSup_mem;
      exact this ⟨ _, Set.mem_range_self 0 ⟩ |> fun ⟨ i, hi ⟩ => hi ▸ hM_lt_target i |>.1;
    · -- Since the range of T is finite, its supremum is the maximum element in that range.
      have h_range_finite : Set.Finite (Set.range T) := by
        exact Set.toFinite _;
      have := h_range_finite.isCompact.sSup_mem;
      exact this ⟨ _, Set.mem_range_self 0 ⟩ |> fun ⟨ i, hi ⟩ => hi ▸ hM_lt_target i |>.2;
  -- Apply `exists_packing_from_seq` with this `M` to obtain a valid packing `P` of `n` squares with side lengths `s_i = x i / M`.
  obtain ⟨P, hP_valid, hP_side_lengths⟩ : ∃ P : Packing n, P.is_valid ∧ ∀ i, (P i).s = x i / M := by
    apply exists_packing_from_seq;
    any_goals tauto;
    · exact fun i => le_max_of_le_left <| le_csSup ( Set.finite_range S |> Set.Finite.bddAbove ) <| Set.mem_range_self i;
    · exact fun i => le_max_of_le_right <| le_csSup ( Set.finite_range T |> Set.Finite.bddAbove ) <| Set.mem_range_self i;
  -- By definition of `g(n)`, `L ≤ g(n)`. By `baek_koizumi_ueoro`, `g(n) ≤ k + a/k`.
  have hL_le_g : (∑ i, (P i).s) ≤ g n := by
    refine' le_csSup _ _;
    · refine' ⟨ n, fun L hL => _ ⟩ ; aesop;
      exact le_trans ( Finset.sum_le_sum fun _ _ => show ( w _ |> Square.s ) ≤ 1 from by linarith [ w ‹_› |> Square.s_nonneg, w ‹_› |> Square.x_nonneg, w ‹_› |> Square.y_nonneg, w ‹_› |> Square.x_plus_s_le_one, w ‹_› |> Square.y_plus_s_le_one ] ) ( by norm_num );
    · exact ⟨ P, hP_valid, rfl ⟩
  have hg_le_k_plus_a_div_k : g n ≤ k + a / k := by
    have := baek_koizumi_ueoro k a;
    convert this ( by positivity ) ( by nlinarith ) using 1 ; norm_cast ; ring;
    exact hn ▸ by ring;
  -- But `target = k / (k^2 + a)`, so `1/target = (k^2 + a) / k = k + a/k`.
  have h_one_div_target : 1 / (k / (k^2 + a : ℝ)) = k + a / k := by
    field_simp;
  -- Since `M < target`, `1/M > 1/target = k + a/k`.
  have h_one_div_M_gt_one_div_target : 1 / M > 1 / (k / (k^2 + a : ℝ)) := by
    gcongr;
    exact lt_max_of_lt_left ( lt_of_lt_of_le ( h_pos ⟨ 0, by nlinarith ⟩ ) ( le_csSup ( Set.finite_range S |> Set.Finite.bddAbove ) ( Set.mem_range_self _ ) |> le_trans ( hS.2.2 _ ) ) );
  norm_num [ Finset.sum_div _ _ _, hP_side_lengths ] at *;
  rw [ ← Finset.sum_div _ _ _, h_sum ] at hL_le_g ; norm_num at hL_le_g ; linarith

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
  obtain ⟨L, hL⟩ : ∃ L : List ℝ, L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ (∑ i ∈ Finset.range n, L.get! i) = 1 ∧ (Mp L / (∑ i ∈ Finset.range n, L.get! i)) < (k : ℝ) / (k^2 + a.natAbs) + ε / 2 := by
    have h_inf : ∀ ε > 0, ∃ L : List ℝ, L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ (Mp L) / L.sum < (k : ℝ) / (k^2 + a.natAbs) + ε / 2 := by
      intros ε hε_pos
      have h_inf : sInf { r : ℝ | ∃ (L : List ℝ), L.length = n ∧ L.Nodup ∧ (∀ x ∈ L, 0 < x) ∧ r = Mp L / L.sum } ≤ (k : ℝ) / (k^2 + a.natAbs) := by
        convert main_theorem k a.natAbs ( mod_cast hk ) ( mod_cast by linarith [ abs_of_nonneg ha_low ] ) using 1 ; ring;
        rw [ show 1 + k ^ 2 + a.natAbs * 2 = n by linarith [ abs_of_nonneg ha_low ] ] ; rfl;
      contrapose! h_inf;
      refine' lt_of_lt_of_le _ ( le_csInf _ _ );
      exact lt_add_of_pos_right _ ( half_pos hε_pos );
      · refine' ⟨ _, ⟨ List.map ( fun i : ℕ => ( i + 1 : ℝ ) ) ( List.range n ), _, _, _, rfl ⟩ ⟩ <;> norm_num;
        · rw [ List.nodup_map_iff_inj_on ] ; aesop;
          grind;
        · exact fun _ _ => Nat.cast_add_one_pos _;
      · aesop;
    obtain ⟨ L, hL₁, hL₂, hL₃, hL₄ ⟩ := h_inf ε hε_pos;
    refine' ⟨ L.map fun x => x / L.sum, _, _, _, _, _ ⟩ <;> simp_all +decide [ ne_of_gt ];
    · rw [ List.nodup_map_iff_inj_on ] ; aesop;
      · have h_sum_pos : 0 < L.sum := by
          have h_sum_pos : ∀ {L : List ℝ}, (∀ x ∈ L, 0 < x) → L ≠ [] → 0 < L.sum := by
            intro L hL₁ hL₂; induction L <;> aesop;
            by_cases h : tail = [] <;> aesop ; positivity;
          exact h_sum_pos hL₃ ( by aesop_cat );
        rw [ div_eq_div_iff ] at a_3 <;> nlinarith [ hL₃ x a_1, hL₃ y a_2 ];
      · assumption;
    · induction L <;> aesop;
      · exact add_pos_of_pos_of_nonneg left_1 ( List.sum_nonneg fun x hx => le_of_lt ( right_1 x hx ) );
      · exact add_pos_of_pos_of_nonneg left_1 ( List.sum_nonneg fun x hx => le_of_lt ( right_1 x hx ) );
    · have h_sum : ∑ x ∈ Finset.range n, (L[x]! : ℝ) = L.sum := by
        simp +decide [ ← hL₁, Finset.sum_range, List.sum ];
      convert congr_arg ( fun x : ℝ => x / L.sum ) h_sum using 1;
      · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; aesop;
      · rw [ div_self ] ; aesop;
        rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> norm_num at *;
        · nlinarith;
        · linarith;
        · linarith [ show 0 ≤ L.sum from List.sum_nonneg fun x hx => le_of_lt ( hL₃.2.2 x hx ) ];
    · -- By definition of $Mp$, we know that $Mp (L.map (fun x => x / L.sum)) = Mp L / L.sum$.
      have hMp_map : Mp (L.map (fun x => x / L.sum)) = Mp L / L.sum := by
        unfold Mp; simp +decide [ div_eq_inv_mul, List.sum_map_mul_right ] ;
        -- By definition of `List.map`, we can factor out the constant `L.sum⁻¹` from the sum.
        have h_map : List.map List.sum (List.filter (fun s => Decidable.decide (List.Sorted (· < ·) s) || Decidable.decide (List.Sorted (· > ·) s)) (List.map (fun x => L.sum⁻¹ * x) L).sublists) = List.map (fun s => L.sum⁻¹ * s) (List.map List.sum (List.filter (fun s => Decidable.decide (List.Sorted (· < ·) s) || Decidable.decide (List.Sorted (· > ·) s)) L.sublists)) := by
          have h_map : List.map List.sum (List.filter (fun s => Decidable.decide (List.Sorted (· < ·) s) || Decidable.decide (List.Sorted (· > ·) s)) (List.map (fun x => L.sum⁻¹ * x) L).sublists) = List.map (fun s => L.sum⁻¹ * s) (List.map List.sum (List.filter (fun s => Decidable.decide (List.Sorted (· < ·) s) || Decidable.decide (List.Sorted (· > ·) s)) L.sublists)) := by
            have h_sublists : List.sublists (List.map (fun x => L.sum⁻¹ * x) L) = List.map (fun s => List.map (fun x => L.sum⁻¹ * x) s) (List.sublists L) := by
              rw [ List.sublists_map ]
            rw [ h_sublists, List.filter_map ];
            simp +decide [ Function.comp, List.sum_map_mul_left ];
            congr! 2;
            · ext; simp +decide [ List.sum_map_mul_left ] ;
              rw [ List.sum_map_mul_left ];
              rw [ List.map_id' ];
            · ext; simp [Function.comp];
              by_cases h : L.sum = 0 <;> simp_all +decide [ List.Sorted ];
              · cases L <;> aesop;
                · nlinarith;
                · linarith [ show 0 ≤ List.sum tail from List.sum_nonneg fun x hx => le_of_lt ( right_1 x hx ) ];
              · simp +decide [ List.pairwise_map, mul_lt_mul_iff_right₀ ( inv_pos.mpr ( show 0 < L.sum from lt_of_le_of_ne ( List.sum_nonneg fun x hx => le_of_lt ( hL₃ x hx ) ) ( Ne.symm h ) ) ) ];
          exact h_map;
        have h_max_map : ∀ {l : List ℝ}, l ≠ [] → List.maximum (List.map (fun x => L.sum⁻¹ * x) l) = Option.map (fun x => L.sum⁻¹ * x) (List.maximum l) := by
          intros l hl_nonempty; induction l <;> aesop;
          by_cases h : tail = [] <;> simp_all +decide [ List.maximum_cons ];
          · rfl;
          · cases h : List.maximum tail <;> aesop;
            cases max_cases ( head : WithBot ℝ ) ( a_1 : WithBot ℝ ) <;> simp +decide [ * ];
            · erw [ WithBot.coe_eq_coe ] at * ; aesop;
              exact mul_le_mul_of_nonneg_left h_2 ( inv_nonneg.2 ( List.sum_nonneg fun x hx => le_of_lt ( hL₃ x hx ) ) );
            · exact WithBot.coe_le_coe.mpr ( mul_le_mul_of_nonneg_left ( le_of_lt ( by aesop ) ) ( inv_nonneg.mpr ( show 0 ≤ L.sum from List.sum_nonneg fun x hx => le_of_lt ( hL₃ x hx ) ) ) );
        by_cases h : List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ) || Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) s ) ) L.sublists ) = [ ] <;> aesop;
        · specialize h [ ] ; aesop;
          specialize h_map [ ] ; aesop;
        · specialize @h_max_map ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ) || Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) s ) ) L.sublists ) ) ; aesop;
          cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ) || Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) s ) ) L.sublists ) ) <;> aesop;
          specialize h_max_map w left right ; aesop;
      have h_sum_map : ∑ x ∈ Finset.range n, (Option.map (fun x => x / L.sum) L[x]?).getD Inhabited.default = L.sum / L.sum := by
        have h_sum_map : ∑ x ∈ Finset.range n, (Option.map (fun x => x / L.sum) L[x]?).getD Inhabited.default = (∑ x ∈ Finset.range n, L[x]!) / L.sum := by
          rw [ Finset.sum_div _ _ _ ];
          refine' Finset.sum_congr rfl fun i hi => _ ; aesop;
        aesop;
        norm_num [ Finset.sum_range, List.get?_eq_get ];
      by_cases h : L.sum = 0 <;> aesop;
  -- By definition of `Mp`, we know that `Mp(L)` is the maximum of the sums of monotone subsequences of `L`.
  have hMp_L : ∀ m : ℕ, ∀ s : Fin (m + 1) → Fin n, StrictMono s → (Monotone (fun i => L.get! (s i)) ∨ Antitone (fun i => L.get! (s i))) → (∑ i, L.get! (s i)) ≤ Mp L := by
    intros m s hs_mono hs_monotone
    have h_subseq : List.Sublist (List.map (fun i => L.get! (s i)) (List.finRange (m + 1))) L := by
      have h_subseq : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange n) := by
        have h_subseq : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.map (fun i => i) (List.finRange n)) := by
          have h_sorted : List.Sorted (· < ·) (List.map (fun i => s i) (List.finRange (m + 1))) := by
            simp +decide [ List.Sorted, hs_mono.lt_iff_lt ];
            rw [ List.pairwise_iff_get ];
            aesop
          have h_subseq : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange n) := by
            have h_sorted : List.Sorted (· < ·) (List.map (fun i => s i) (List.finRange (m + 1))) := h_sorted
            have h_perm : List.Perm (List.map (fun i => s i) (List.finRange (m + 1))) (List.map (fun i => i) (List.finRange n) |>.filter (fun i => i ∈ List.map (fun i => s i) (List.finRange (m + 1)))) := by
              rw [ List.perm_iff_count ];
              intro i; by_cases hi : i ∈ List.map ( fun i => s i ) ( List.finRange ( m + 1 ) ) <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
              rw [ List.count_eq_one_of_mem ];
              · exact List.Nodup.map ( fun i j hij => hs_mono.injective hij ) ( List.nodup_finRange _ );
              · aesop
            have h_subseq : List.Sublist (List.filter (fun i => i ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.map (fun i => i) (List.finRange n))) (List.finRange n) := by
              simp +zetaDelta at *;
            convert h_subseq using 1;
            exact List.eq_of_perm_of_sorted h_perm h_sorted ( by simpa using List.Sorted.filter ( fun i => Decidable.decide ( i ∈ List.map ( fun i => s i ) ( List.finRange ( m + 1 ) ) ) ) ( List.pairwise_iff_get.mpr <| by simp +decide [ List.get ] ) );
          aesop;
        aesop;
      have h_subseq : List.Sublist (List.map (fun i => L.get! i) (List.map (fun i => s i) (List.finRange (m + 1)))) (List.map (fun i => L.get! i) (List.finRange n)) := by
        convert h_subseq.map _ using 1;
        any_goals exact fun i => L.get! i;
        · induction ( List.finRange ( m + 1 ) ) <;> aesop;
        · induction ( List.finRange n ) <;> aesop;
      convert h_subseq using 1;
      · simp +decide [ Function.comp ];
      · refine' List.ext_get _ _ <;> aesop;
        · -- The flatMap of the finRange of L.length is just the list of indices of L.
          have h_flatMap : List.flatMap (fun a : Fin L.length => [(↑a : ℕ)]) (List.finRange L.length) = List.map (fun a : Fin L.length => ↑a) (List.finRange L.length) := by
            induction ( List.finRange L.length ) <;> aesop;
          aesop;
        · -- The flatMap of the finRange is just the list of indices from 0 to L.length - 1, so the nth element is n.
          have h_flatMap : List.flatMap (fun a : Fin L.length => [(↑a : ℕ)]) (List.finRange L.length) = List.map (fun a : Fin L.length => ↑a) (List.finRange L.length) := by
            induction ( List.finRange L.length ) <;> aesop;
          aesop;
    have h_subseq_max : ∀ s : List ℝ, List.Sublist s L → List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s → s.sum ≤ Mp L := by
      intros s hs_subseq hs_monotone
      have h_subseq_max : s.sum ∈ ((L.sublists.filter (fun s => List.Sorted (· < ·) s ∨ List.Sorted (· > ·) s)).map List.sum) := by
        aesop;
      apply_rules [ List.le_maximum_of_mem ];
      unfold Mp; aesop;
      all_goals cases h : List.maximum ( List.map List.sum ( List.filter ( fun s => Decidable.decide ( List.Sorted ( fun x1 x2 => x1 < x2 ) s ) || Decidable.decide ( List.Sorted ( fun x1 x2 => x2 < x1 ) s ) ) L.sublists ) ) <;> aesop;
    convert h_subseq_max _ h_subseq _ using 1;
    simp_all +decide [ List.Sorted, List.pairwise_iff_get ];
    cases hs_monotone <;> simp_all +decide [ Monotone, Antitone ];
    · left; intro i j hij; exact lt_of_le_of_ne ( by solve_by_elim [ le_of_lt hij ] ) ( by
        have := List.nodup_iff_injective_get.mp ( show List.Nodup ( List.map ( fun i : Fin ( m + 1 ) => L[( s i : ℕ )] ) ( List.finRange ( m + 1 ) ) ) from ?_ ) ; aesop;
        · have := @this ⟨ i, by simpa using i.2 ⟩ ⟨ j, by simpa using j.2 ⟩ ; aesop;
        · grind ) ;
    · right;
      aesop;
      refine' lt_of_le_of_ne ( h _hij.le ) _;
      intro H; have := List.nodup_iff_injective_get.mp left_2; have := @this ( s ⟨ j, by simpa using j.2 ⟩ ) ( s ⟨ i, by simpa using i.2 ⟩ ) ; aesop;
      exact absurd ( hs_mono.injective this ) ( ne_of_gt _hij );
  simp_all +decide [ Finset.sum_range, Fin.cast_val_eq_self ];
  use fun i => L.get! i; aesop;
  · intro i j hij; have := List.nodup_iff_injective_get.mp left_1; aesop;
  · rw [ abs_of_nonneg ( by positivity ) ] at right_1 ; linarith [ hMp_L m s a_1 ( Or.inl h ) ];
  · exact le_trans ( hMp_L m s a_1 <| Or.inr h_1 ) <| by rw [ abs_of_nonneg ( by positivity ) ] at right_1; linarith;

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
    aesop
    generalize_proofs at *;
    · refine' le_trans _ ( le_max_left _ _ );
      have h_sublist : (List.finRange (m + 1)).map (fun i => L.get ⟨s i, by solve_by_elim⟩) ∈ List.sublists L := by
        have h_sublist : List.Sublist (List.map (fun i => L.get ⟨s i, by solve_by_elim⟩) (List.finRange (m + 1))) (List.map (fun i => L.get i) (List.finRange L.length)) := by
          have h_sublist : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length) := by
            have h_sublist : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.map (fun i => i) (List.finRange L.length)) := by
              have h_sorted : List.Sorted (· < ·) (List.map (fun i => s i) (List.finRange (m + 1))) := by
                simp +decide [ List.Sorted, hs.lt_iff_lt ];
                rw [ List.pairwise_map, List.pairwise_iff_get ];
                aesop
              have h_sublist : ∀ {l1 l2 : List (Fin L.length)}, List.Sorted (· < ·) l1 → List.Sorted (· < ·) l2 → (∀ x ∈ l1, x ∈ l2) → List.Sublist l1 l2 := by
                intros l1 l2 hl1 hl2 h; induction' l1 with x l1 ih generalizing l2 <;> aesop;
                rcases List.mem_iff_get.1 left_1 with ⟨ i, hi ⟩ ; aesop
                generalize_proofs at *;
                have := List.pairwise_iff_get.mp hl2; aesop;
                have h_sublist : List.Sublist (l1) (List.drop (i + 1) l2) := by
                  apply ih;
                  · exact hl2.sublist ( List.drop_sublist _ _ );
                  · intro x hx; specialize right_1 x hx; rw [ List.mem_iff_get ] at right_1; aesop;
                    rw [ List.mem_iff_get ] ; aesop
                    generalize_proofs at *;
                    by_cases h_cases : w.val ≤ i.val;
                    · exact absurd ( left _ hx ) ( not_lt_of_ge ( le_of_lt ( this _ _ ( show w < i from lt_of_le_of_ne h_cases ( by rintro rfl; exact absurd ( left _ hx ) ( by simp ) ) ) ) ) );
                    · use ⟨ w - ( i + 1 ), by
                        grind ⟩
                      generalize_proofs at *;
                      simp +decide [ add_tsub_cancel_of_le ( by linarith : ( i : ℕ ) + 1 ≤ w ) ]
                generalize_proofs at *;
                have h_sublist : List.Sublist (l2[(i : ℕ)] :: l1) (l2.take (i + 1) ++ List.drop (i + 1) l2) := by
                  rw [ List.take_succ ] ; aesop;
                  have h_sublist : List.Sublist (l2[(i : ℕ)] :: l1) (l2.take (i + 1) ++ List.drop (i + 1) l2) := by
                    have h_sublist : List.Sublist (l2[(i : ℕ)] :: l1) (l2[(i : ℕ)] :: List.drop (i + 1) l2) := by
                      exact List.Sublist.cons₂ _ h_sublist
                    rw [ List.take_succ ] ; aesop
                    generalize_proofs at *;
                    exact h_sublist.trans ( List.drop_sublist _ _ )
                  generalize_proofs at *;
                  convert h_sublist using 1 ; rw [ List.take_append_drop ]
                generalize_proofs at *;
                convert h_sublist using 1;
                rw [ List.take_append_drop ]
              generalize_proofs at *;
              apply h_sublist h_sorted;
              · simp +decide [ List.Sorted ];
                simp +decide [ List.pairwise_iff_get ];
              · simp +zetaDelta at *
            generalize_proofs at *;
            aesop;
          convert h_sublist.map _ using 1;
          aesop;
        aesop;
      have h_sorted : List.Sorted (· < ·) (List.map (fun i => L.get ⟨s i, by solve_by_elim⟩) (List.finRange (m + 1))) := by
        refine' List.pairwise_iff_get.mpr _;
        aesop;
        exact lt_of_le_of_ne ( h ( Nat.le_of_lt ‹_› ) ) ( by have := List.pairwise_iff_get.mp hL_pairwise; aesop );
      unfold M_inc;
      unfold Option.getD; aesop;
      · rw [ List.maximum ] at heq;
        rw [ List.argmax_eq_some_iff ] at heq ; aesop;
      · simp_all +decide [ List.maximum ];
        rw [ List.argmax_eq_none ] at heq ; aesop;
    · -- If `fun i => L[s i]` is antitone, then `sub` is sorted by `>`.
      have h_sub_antitone : (List.finRange (m + 1)).map (fun i => L.get (s i)) ∈ (L.sublists.filter (fun S => S.Sorted (· > ·))) := by
        rw [ List.mem_filter ] ; aesop;
        · have h_sublist : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length) := by
            have h_sorted : List.Sorted (· < ·) (List.map (fun i => s i) (List.finRange (m + 1))) := by
              simp +decide [ List.Sorted, hs.lt_iff_lt ];
              rw [ List.pairwise_iff_get ] ; aesop
            have h_sublist : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length) := by
              have h_perm : List.Perm (List.map (fun i => s i) (List.finRange (m + 1))) (List.filter (fun x => x ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length)) := by
                rw [ List.perm_iff_count ];
                intro a; by_cases ha : a ∈ List.map ( fun i => s i ) ( List.finRange ( m + 1 ) ) <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
                rw [ List.count_eq_one_of_mem ] ; aesop;
                · exact List.Nodup.map ( fun i j hij => hs.injective hij ) ( List.nodup_finRange _ );
                · aesop
              have h_sublist : List.Sublist (List.filter (fun x => x ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length)) (List.finRange L.length) := by
                simp +zetaDelta at *;
              have h_sublist : List.Sublist (List.map (fun i => s i) (List.finRange (m + 1))) (List.filter (fun x => x ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length)) := by
                have h_perm : List.Perm (List.map (fun i => s i) (List.finRange (m + 1))) (List.filter (fun x => x ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length)) := h_perm
                have h_sorted : List.Sorted (· < ·) (List.map (fun i => s i) (List.finRange (m + 1))) := h_sorted
                have h_sorted_filter : List.Sorted (· < ·) (List.filter (fun x => x ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length)) := by
                  exact List.Pairwise.filter _ ( List.pairwise_iff_get.mpr <| by aesop )
                have h_eq : List.map (fun i => s i) (List.finRange (m + 1)) = List.filter (fun x => x ∈ List.map (fun i => s i) (List.finRange (m + 1))) (List.finRange L.length) := by
                  exact List.eq_of_perm_of_sorted h_perm h_sorted h_sorted_filter;
                grind;
              exact h_sublist.trans ‹_›;
            exact h_sublist;
          convert h_sublist.map ( fun x => L[x] ) using 1;
          · aesop;
          · norm_num +zetaDelta at *;
        · rw [ List.Sorted ];
          rw [ List.pairwise_iff_get ] ; aesop;
          refine' lt_of_le_of_ne ( h_1 _hij.le ) _;
          have := List.pairwise_iff_get.mp hL_pairwise;
          exact this _ _ ( hs _hij ) |> Ne.symm;
      -- Since `sub` is in the filter for `M_dec`, we have `sub.sum ≤ M_dec L`.
      have h_sub_dec : ((List.finRange (m + 1)).map (fun i => L.get (s i))).sum ≤ M_dec L := by
        unfold M_dec;
        unfold Option.getD; aesop;
        · have := List.argmax_eq_some_iff.mp heq; aesop;
        · simp_all +decide [ List.maximum ];
          rw [ List.argmax_eq_none ] at heq ; aesop;
      exact le_trans ( by simpa [ List.map ] using h_sub_dec ) ( le_max_right _ _ )

lemma exists_seq_of_c_le {n : ℕ} {K : ℝ} (hn : n ≠ 0) (h : c n ≤ K) :
  ∀ ε > 0, ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧
  (∀ (m : ℕ) (s : Fin (m + 1) → Fin n), StrictMono s →
    (Monotone (x ∘ s) ∨ Antitone (x ∘ s)) →
    ∑ i, x (s i) ≤ K + ε) := by
      field_simp;
      intro ε ε_pos
      obtain ⟨L, hL_len, hL_pairwise, hL_pos, hL_ratio⟩ : ∃ L : List ℝ, L.length = n ∧ L.Pairwise (· ≠ ·) ∧ (∀ x ∈ L, 0 < x) ∧ M L / L.sum < K + ε := by
        have := exists_lt_of_csInf_lt ( show { r | ∃ L : List ℝ, L.length = n ∧ L.Pairwise ( · ≠ · ) ∧ ( ∀ x ∈ L, 0 < x ) ∧ r = M L / L.sum }.Nonempty from ?_ ) ( show sInf { r | ∃ L : List ℝ, L.length = n ∧ L.Pairwise ( · ≠ · ) ∧ ( ∀ x ∈ L, 0 < x ) ∧ r = M L / L.sum } < K + ε from ?_ ) <;> aesop;
        · refine' ⟨ _, ⟨ List.map ( fun i : ℕ => ( i : ℝ ) + 1 ) ( List.range n ), _, _, _, rfl ⟩ ⟩ <;> norm_num [ List.pairwise_iff_get ];
          · exact fun i j hij => ne_of_lt hij;
          · exact fun a ha => Nat.cast_add_one_pos a;
        · exact lt_of_le_of_lt h ( lt_add_of_pos_right K ε_pos );
      -- Define `x` as the normalized version of `L`.
      obtain ⟨x, hx_def⟩ : ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧ (∀ i, x i = L.get ⟨i, by rw [hL_len]; exact i.isLt⟩ / L.sum) := by
        refine' ⟨ fun i => L.get ⟨ i, by linarith [ Fin.is_lt i ] ⟩ / L.sum, _, _, _, fun i => rfl ⟩;
        · bound;
          · exact hL_pos _ ( by simp );
          · -- Since every element in L is positive, their sum is also positive.
            apply List.sum_pos; intro x hx; exact hL_pos x hx;
            aesop;
        · intro i j hij;
          simp_all +decide [ ne_of_gt, div_eq_mul_inv ];
          rw [ List.pairwise_iff_get ] at hL_pairwise;
          cases hij <;> simp_all +decide [ ne_of_gt, List.get ];
          · exact Classical.not_not.1 fun hi => hL_pairwise ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ⟨ j, by linarith [ Fin.is_lt j ] ⟩ ( lt_of_le_of_ne ( le_of_not_gt fun hi' => hL_pairwise ⟨ j, by linarith [ Fin.is_lt j ] ⟩ ⟨ i, by linarith [ Fin.is_lt i ] ⟩ hi' <| by linarith ) ( by aesop ) ) ‹_›;
          · induction L <;> aesop;
            exact absurd h_1 ( ne_of_gt ( add_pos_of_pos_of_nonneg left ( List.sum_nonneg fun x hx => le_of_lt ( right x hx ) ) ) );
        · rw [ ← Finset.sum_div _ _ _, div_eq_iff ] <;> aesop;
          induction L <;> aesop;
          linarith [ show 0 ≤ List.sum tail from List.sum_nonneg fun x hx => le_of_lt ( right_1 x hx ) ];
      refine' ⟨ x, hx_def.1, hx_def.2.1, hx_def.2.2.1, _ ⟩;
      intro m s hs_mono hs_monotone
      have h_sum_L : ∑ i, L.get ⟨s i, by rw [hL_len]; exact (s i).isLt⟩ ≤ M L := by
        apply sum_subseq_le_M_of_monotone L hL_len hL_pairwise m s hs_mono;
        aesop;
        · simp_all ( config := { decide := Bool.true } ) [ Monotone, Antitone ];
          exact Or.inl fun a b hab => by have := h_1 hab; rw [ div_le_div_iff_of_pos_right ( left ⟨ 0, by linarith [ Fin.is_lt ( s a ), Fin.is_lt ( s b ) ] ⟩ ) ] at this; linarith;
        · right;
          intro i j hij; have := h_2 hij; aesop;
          rwa [ div_le_div_iff_of_pos_right ( left _ ) ] at this;
          exact s i;
      simp_all ( config := { decide := Bool.true } ) [ ← Finset.sum_div _ _ _, div_lt_iff₀ ];
      exact le_trans ( div_le_div_of_nonneg_right h_sum_L <| List.sum_nonneg fun x hx => le_of_lt <| hL_pos x hx ) hL_ratio.le

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
      ring;
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
      refine' le_antisymm _ _;
      · -- By `exists_seq_with_monotone_subseq_sum_le_general_range`, there exists a sequence $x$ with score ≤ K + ε for any ε > 0.
        have h_exists_seq : ∀ ε > 0, ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ Function.Injective x ∧ (∑ i, x i = 1) ∧ score x ≤ (k : ℝ) / ((k : ℝ) ^ 2 + a) + ε := by
          intro ε hε_pos;
          have := exists_seq_with_monotone_subseq_sum_le_general_range k n a ( by linarith ) ( by linarith ) ( by linarith ) hn ε hε_pos;
          obtain ⟨ x, hx₁, hx₂, hx₃, hx₄ ⟩ := this; use x; unfold score; aesop;
          refine' csSup_le _ _;
          · refine' ⟨ _, ⟨ 0, fun _ => ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, _, rfl ⟩ ⟩;
            exact ⟨ by simp +decide [ StrictMono ], Or.inl <| by simp +decide [ Monotone ] ⟩;
          · rintro _ ⟨ m, s, ⟨ hs₁, hs₂ ⟩, rfl ⟩ ; linarith [ hx₄ m s hs₁ hs₂ ] ;
        refine' le_of_forall_pos_le_add _;
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
            refine' ⟨ hs_mono, _, _ ⟩;
            · exact Or.imp ( fun h => fun i j hij => by have := h hij; rw [ div_le_div_iff_of_pos_right ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ s i, Finset.mem_univ _ ⟩ ) ] at this; linarith ) ( fun h => fun i j hij => by have := h hij; rw [ div_le_div_iff_of_pos_right ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ s i, Finset.mem_univ _ ⟩ ) ] at this; linarith ) hs_monotone;
            · rw [ ← Finset.sum_div _ _ _ ] at * ; rw [ ge_iff_le, le_div_iff₀ ] at * <;> linarith [ Finset.sum_pos ( fun i _ => hx_pos i ) ⟨ ⟨ 0, Nat.pos_of_ne_zero <| by aesop_cat ⟩, Finset.mem_univ _ ⟩ ] ;
          obtain ⟨m, s, hs_mono, hs_monotone, hs_sum⟩ := h_monotone_subseq_x
          have h_max_mono_subseq_sum : maxMonoSubseqSum x ≥ (k : ℝ) / ((k^2 + a) : ℝ) * (∑ i, x i) := by
            refine' le_trans hs_sum ( le_csSup _ _ );
            · refine' ⟨ ∑ i, x i, _ ⟩;
              rintro _ ⟨ m, s, hs_mono, rfl ⟩;
              have h_sum_le : ∑ i ∈ Finset.image s Finset.univ, x i ≤ ∑ i, x i := by
                exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => le_of_lt ( hx_pos _ );
              rwa [ Finset.sum_image <| by intros i hi j hj hij; exact hs_mono.1.injective hij ] at h_sum_le;
            · exact ⟨ m, s, ⟨ hs_mono, hs_monotone ⟩, rfl ⟩
          have h_score_ge : (maxMonoSubseqSum x) / (∑ i, x i) ≥ (k : ℝ) / ((k^2 + a) : ℝ) := by
            exact le_div_iff₀ ( Finset.sum_pos ( fun _ _ => hx_pos _ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Finset.mem_univ _ ⟩ ) |>.2 h_max_mono_subseq_sum
          exact h_score_ge;
        refine' le_csInf _ _ <;> aesop;
        refine' ⟨ _, ⟨ fun i => i + 1, _, _, rfl ⟩ ⟩ <;> norm_num [ Function.Injective ];
        · exact fun i => Nat.cast_add_one_pos _;
        · exact fun i j h => Fin.ext h
