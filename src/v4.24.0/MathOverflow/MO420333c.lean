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
Definitions for the unbounded game: Strategy, N, S, Score, W, and V_infty.
-/
open Filter Topology

/-- A (unbounded) strategy is a nondecreasing sequence of real numbers x_1 <= x_2 <= ... such that x_1 >= 1 and lim x_n = +infinity. -/
structure Strategy where
  x : ℕ → ℝ
  mono : Monotone x
  one_le_x1 : 1 ≤ x 1
  tendsto_atTop : Tendsto x atTop atTop

/-- N(y) := min {n >= 1 : x_n >= y} -/
def Strategy.N (s : Strategy) (y : ℝ) : ℕ :=
  sInf {n | 1 ≤ n ∧ y ≤ s.x n}

/-- S_n := sum_{i=1}^n x_i -/
def Strategy.S (s : Strategy) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, s.x i

/-- Score(y) := S_{N(y)} / y -/
def Strategy.Score (s : Strategy) (y : ℝ) : ℝ :=
  s.S (s.N y) / y

/-- Worst-case score W := sup_{y >= 1} Score(y) -/
def Strategy.W (s : Strategy) : ℝ :=
  sSup {s.Score y | y ≥ 1}

/-- The value of the unbounded game is V_infty := inf W -/
def V_infty : ℝ :=
  sInf {s.W | s : Strategy}

/-
Definition of a B-strategy.
-/
/-- A B-strategy is a nondecreasing finite sequence x_1 <= ... <= x_n such that x_1 >= 1 and x_n = B. -/
structure BStrategy (B : ℝ) where
  n : ℕ
  n_pos : 0 < n
  x : Fin n → ℝ
  mono : Monotone x
  one_le_x1 : 1 ≤ x ⟨0, n_pos⟩
  xn_eq_B : x ⟨n - 1, Nat.sub_lt n_pos (by simp)⟩ = B

/-
Helper function to access the k-th element of a B-strategy safely.
-/
/-- Helper to access x_k for 1 <= k <= n safely. -/
def BStrategy.x_safe {B : ℝ} (s : BStrategy B) (k : ℕ) : ℝ :=
  if h : 1 ≤ k ∧ k ≤ s.n then
    s.x ⟨k - 1, by
      omega⟩
  else
    B

/-
Definition of N(y) for a B-strategy.
-/
/-- N(y) for a B-strategy. -/
def BStrategy.N {B : ℝ} (s : BStrategy B) (y : ℝ) : ℕ :=
  sInf {k | 1 ≤ k ∧ k ≤ s.n ∧ y ≤ s.x_safe k}

/-
Definition of S_k for a B-strategy.
-/
/-- S_k := sum_{i=1}^k x_i for a B-strategy. -/
def BStrategy.S {B : ℝ} (s : BStrategy B) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, if h : i < s.n then s.x ⟨i, h⟩ else 0

/-
Definition of Score(y) for a B-strategy.
-/
/-- Score(y) for a B-strategy. -/
def BStrategy.Score {B : ℝ} (s : BStrategy B) (y : ℝ) : ℝ :=
  s.S (s.N y) / y

/-
Definition of W_B for a B-strategy.
-/
/-- Worst-case score W_B for a B-strategy. -/
def BStrategy.W {B : ℝ} (s : BStrategy B) : ℝ :=
  sSup {s.Score y | y ∈ Set.Icc 1 B}

/-
Definition of V(B) for the bounded game.
-/
/-- The value of the bounded game V(B). -/
def V (B : ℝ) : ℝ :=
  sInf {s.W | s : BStrategy B}

/-
Definition of extended strategy sequence with x_0 = 1, and proof of its monotonicity.
-/
def Strategy.x_ext (s : Strategy) (k : ℕ) : ℝ :=
  if k = 0 then 1 else s.x k

lemma Strategy.x_ext_mono (s : Strategy) : Monotone s.x_ext := by
  unfold Strategy.x_ext;
  intro m n hmn;
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all +decide;
  · exact le_trans s.one_le_x1 ( s.mono ( Nat.one_le_iff_ne_zero.mpr hn ) );
  · exact s.mono hmn

/-
Lemma: For y in (x_k, x_{k+1}], N(y) = k+1.
-/
lemma Strategy.N_eq_succ_k (s : Strategy) (k : ℕ) (y : ℝ)
    (hy_gt : s.x_ext k < y) (hy_le : y ≤ s.x_ext (k + 1)) :
    s.N y = k + 1 := by
      refine' le_antisymm _ _;
      · refine' csInf_le _ _ <;> aesop;
      · refine' le_csInf _ _;
        · use k + 1;
          unfold Strategy.x_ext at * ; aesop;
        · rcases k with ( _ | k ) <;> simp_all +decide [ Strategy.x_ext ];
          exact fun n hn hn' => Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => by linarith [ s.mono h ] )

/-
Definition of T_k and lemma that Score(y) = S_{k+1}/y for y in (x_k, x_{k+1}].
-/
def Strategy.T (s : Strategy) (k : ℕ) : ℝ :=
  s.S (k + 1) / s.x_ext k

lemma Strategy.Score_eq_of_mem_Ioc (s : Strategy) (k : ℕ) (y : ℝ)
    (hy_gt : s.x_ext k < y) (hy_le : y ≤ s.x_ext (k + 1)) :
    s.Score y = s.S (k + 1) / y := by
      unfold Strategy.Score;
      congr;
      convert Strategy.N_eq_succ_k s k y hy_gt hy_le

/-
Lemma: For y in (x_k, x_{k+1}], Score(y) <= T(k).
-/
lemma Strategy.Score_le_T_of_mem_Ioc (s : Strategy) (k : ℕ) (y : ℝ)
    (hy_gt : s.x_ext k < y) (hy_le : y ≤ s.x_ext (k + 1)) :
    s.Score y ≤ s.T k := by
      rw [ Strategy.Score_eq_of_mem_Ioc s k y hy_gt hy_le ];
      unfold Strategy.T;
      gcongr;
      · refine' Finset.sum_nonneg fun i hi => _;
        exact le_trans ( by linarith [ s.one_le_x1 ] ) ( s.mono ( show i ≥ 1 from Finset.mem_Icc.mp hi |>.1 ) );
      · unfold Strategy.x_ext;
        split_ifs <;> norm_num;
        exact lt_of_lt_of_le zero_lt_one ( s.one_le_x1.trans ( s.mono ( Nat.one_le_iff_ne_zero.mpr ‹_› ) ) )

/-
Lemma: For any y > 1, there exists k such that y is in (x_k, x_{k+1}].
-/
lemma Strategy.exists_k_mem_Ioc (s : Strategy) (y : ℝ) (hy : 1 < y) :
    ∃ k, s.x_ext k < y ∧ y ≤ s.x_ext (k + 1) := by
      -- Since $x_n \to \infty$, there exists some $N$ such that $x_N \geq y$.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, s.x_ext N ≥ y := by
        have := s.tendsto_atTop.eventually_gt_atTop y;
        norm_num +zetaDelta at *;
        exact ⟨ this.choose + 1, by rw [ Strategy.x_ext ] ; exact le_of_lt ( this.choose_spec _ ( Nat.le_succ _ ) ) ⟩;
      contrapose! hN;
      induction N <;> aesop

/-
Lemma: For any y >= 1, there exists k such that Score(y) <= T(k).
-/
lemma Strategy.exists_k_Score_le_T (s : Strategy) (y : ℝ) (hy : 1 ≤ y) :
    ∃ k, s.Score y ≤ s.T k := by
      -- If y=1, Score(1) = T(0).
      by_cases hy1 : y = 1;
      · -- If y=1, then Score(1) = T(0).
        subst hy1
        use 0
        simp [Strategy.Score, Strategy.T];
        unfold Strategy.S Strategy.x_ext
        simp [Strategy.N];
        rw [ show InfSet.sInf { n : ℕ | 1 ≤ n ∧ 1 ≤ s.x n } = 1 from le_antisymm ( Nat.sInf_le ⟨ by norm_num, by simpa using s.one_le_x1 ⟩ ) ( le_csInf ⟨ 1, by norm_num, by simpa using s.one_le_x1 ⟩ fun n hn => hn.1 ) ] ; norm_num;
      · obtain ⟨ k, hk ⟩ := Strategy.exists_k_mem_Ioc s y ( lt_of_le_of_ne hy ( Ne.symm hy1 ) );
        exact ⟨ k, Strategy.Score_le_T_of_mem_Ioc s k y hk.1 hk.2 ⟩

/-
Definition of W' as the supremum of T(k).
-/
def Strategy.W' (s : Strategy) : ℝ :=
  sSup { s.T k | k : ℕ }

/-
Lemma: If {T k} is bounded above, then W <= W'.
-/
lemma Strategy.W_le_W'_of_bddAbove (s : Strategy) (h : BddAbove {s.T k | k : ℕ}) : s.W ≤ s.W' := by
  -- By definition of $W$, we know that for any $y \geq 1$, $Score(y) \leq W$.
  have hW_le_W' : ∀ y ≥ 1, s.Score y ≤ s.W' := by
    intro y hy
    obtain ⟨k, hk⟩ := Strategy.exists_k_Score_le_T s y hy;
    exact le_trans hk ( le_csSup h ⟨ k, rfl ⟩ );
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ _, ⟨ 1, le_rfl, rfl ⟩ ⟩;
  · tauto

/-
Lemma: If x_k = x_{k+1}, then T(k+1) >= T(k) + 1.
-/
lemma Strategy.T_succ_ge_T_of_x_eq (s : Strategy) (k : ℕ) (h : s.x_ext k = s.x_ext (k + 1)) :
    s.T k + 1 ≤ s.T (k + 1) := by
      -- By definition of $T$, we know that $T(k) = S(k+1)/x_k$ and $T(k+1) = S(k+2)/x_{k+1}$.
      simp [Strategy.T, Strategy.S, Strategy.x_ext] at *;
      simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      rw [ div_add_one, div_le_div_iff_of_pos_right ];
      · exact add_le_add_left ( s.mono ( Nat.le_succ _ ) ) _;
      · split_ifs at h <;> linarith [ s.one_le_x1, s.mono ( show 1 ≤ k + 1 from Nat.succ_pos _ ) ];
      · linarith [ show 0 < s.x ( k + 1 ) from lt_of_lt_of_le zero_lt_one ( s.mono ( Nat.le_add_left _ _ ) |> le_trans ( s.one_le_x1 ) ) ]

/-
Lemma: If x is constant from k to m, then T(m) >= T(k) + (m-k).
-/
lemma Strategy.T_ge_T_add_diff (s : Strategy) (k m : ℕ) (hkm : k ≤ m)
    (h_eq : ∀ i, k ≤ i → i < m → s.x_ext i = s.x_ext (i + 1)) :
    s.T k + (m - k : ℝ) ≤ s.T m := by
      -- We proceed by induction on m - k.
      induction' hkm with m ih;
      · norm_num;
      · rename_i h;
        exact le_trans ( by push_cast; linarith [ h fun i hi₁ hi₂ => h_eq i hi₁ ( Nat.lt_succ_of_lt hi₂ ) ] ) ( Strategy.T_succ_ge_T_of_x_eq s m ( h_eq m ih ( Nat.lt_succ_self m ) ) )

/-
Lemma: For any k, there exists m >= k such that x jumps at m.
-/
lemma Strategy.exists_jump_ge (s : Strategy) (k : ℕ) :
    ∃ m ≥ k, s.x_ext m < s.x_ext (m + 1) := by
      -- Since $x$ tends to infinity, it cannot be constant forever. So there must be a jump after $k$.
      have h_nonconst : ¬ (∃ c, ∀ m ≥ k, s.x_ext m = c) := by
        intro ⟨ c, hc ⟩
        have h_const : Filter.Tendsto (fun m => s.x_ext m) Filter.atTop (nhds c) := by
          exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop k ] with m hm; rw [ hc m hm ] );
        convert not_tendsto_atTop_of_tendsto_nhds h_const _;
        exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( s.tendsto_atTop.eventually_gt_atTop x ) with ⟨ m, hm ⟩ ; exact ⟨ m + 1, fun n hn => le_of_lt <| by have := hm n ( by linarith ) ; unfold Strategy.x_ext; aesop ⟩ ;
      contrapose! h_nonconst;
      exact ⟨ s.x_ext k, fun m hm => le_antisymm ( Nat.le_induction ( by norm_num ) ( fun n hn ih => by linarith [ h_nonconst n hn ] ) m hm ) ( by exact ( show s.x_ext m ≥ s.x_ext k from Nat.le_induction ( by norm_num ) ( fun n hn ih => by linarith [ h_nonconst n hn, ih, show s.x_ext ( n + 1 ) ≥ s.x_ext n from by exact s.x_ext_mono ( by norm_num ) ] ) m hm ) ) ⟩

/-
Lemma: If x jumps at m, we can find a score arbitrarily close to T(m).
-/
lemma Strategy.exists_Score_gt_of_jump (s : Strategy) (m : ℕ) (h_jump : s.x_ext m < s.x_ext (m + 1)) (C : ℝ) (hC : C < s.T m) :
    ∃ y ≥ 1, s.Score y > C := by
      -- Since $C < T(m)$, there exists $y \in (x_m, x_{m+1}]$ such that $Score(y) > C$.
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ Set.Ioo (s.x_ext m) (s.x_ext (m + 1)), s.Score y > C := by
        have h_score_arbitrarily_close : Filter.Tendsto (fun y => s.Score y) (nhdsWithin (s.x_ext m) (Set.Ioi (s.x_ext m))) (nhds (s.T m)) := by
          -- By definition of $Score$, we know that for $y \in (x_m, x_{m+1}]$, $Score(y) = S_{m+1}/y$.
          have h_score_eq : ∀ᶠ y in nhdsWithin (s.x_ext m) (Set.Ioi (s.x_ext m)), s.Score y = s.S (m + 1) / y := by
            filter_upwards [ Ioo_mem_nhdsGT h_jump ] with y hy using by rw [ Strategy.Score_eq_of_mem_Ioc s m y hy.1 hy.2.le ] ;
          rw [ Filter.tendsto_congr' h_score_eq ];
          refine' tendsto_nhdsWithin_of_tendsto_nhds _;
          convert Filter.Tendsto.div ( tendsto_const_nhds ) ( Filter.tendsto_id ) _ using 1 <;> norm_num [ h_jump.ne, Strategy.T ];
          · infer_instance;
          · infer_instance;
          · exact ne_of_gt ( lt_of_lt_of_le zero_lt_one ( show 1 ≤ s.x_ext m from by exact Nat.recOn m ( by exact le_rfl ) fun n ihn => by exact le_trans ihn ( s.x_ext_mono ( Nat.le_succ _ ) ) ) );
        have := h_score_arbitrarily_close.eventually ( lt_mem_nhds hC ) ; have := this.and ( Ioo_mem_nhdsGT h_jump ) ; obtain ⟨ y, hy₁, hy₂ ⟩ := this.exists; exact ⟨ y, hy₂, hy₁ ⟩ ;
      refine' ⟨ y, _, hy₂ ⟩;
      exact le_trans ( show 1 ≤ s.x_ext m from by exact Nat.recOn m ( by exact le_rfl ) fun n ihn => by exact le_trans ihn ( s.x_ext_mono ( Nat.le_succ _ ) ) ) hy₁.1.le

/-
Lemma: If {T k} is unbounded, then {Score y} is unbounded.
-/
lemma Strategy.not_bddAbove_Score_of_not_bddAbove_T (s : Strategy) (h : ¬ BddAbove {s.T k | k : ℕ}) :
    ¬ BddAbove {s.Score y | y ≥ 1} := by
      -- Assume {T k} is unbounded. Let M be arbitrary.
      by_contra h_contra
      obtain ⟨M, hM⟩ : ∃ M, ∀ y ≥ 1, s.Score y ≤ M := by
        exact ⟨ h_contra.choose, fun y hy => h_contra.choose_spec ⟨ y, hy, rfl ⟩ ⟩;
      -- There exists k such that T k > M + 1.
      obtain ⟨k, hk⟩ : ∃ k, s.T k > M + 1 := by
        simpa using not_bddAbove_iff.mp h ( M + 1 );
      -- Let m >= k be the smallest index such that x jumps at m (i.e. x_m < x_{m+1}).
      obtain ⟨m, hm_ge_k, hm_jump⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext (m + 1) ∧ ∀ j, k ≤ j → j < m → s.x_ext j = s.x_ext (j + 1) := by
        -- By definition of $m$, there exists some $m \geq k$ such that $x_m < x_{m+1}$.
        obtain ⟨m, hm_ge_k, hm_jump⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext (m + 1) := by
          exact?;
        -- Let $m$ be the smallest index such that $x_m < x_{m+1}$.
        obtain ⟨m, hm_ge_k, hm_jump, hm_min⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext (m + 1) ∧ ∀ j, k ≤ j → j < m → ¬(s.x_ext j < s.x_ext (j + 1)) := by
          exact ⟨ Nat.find ( ⟨ m, hm_ge_k, hm_jump ⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext ( m + 1 ) ), Nat.find_spec ( ⟨ m, hm_ge_k, hm_jump ⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext ( m + 1 ) ) |>.1, Nat.find_spec ( ⟨ m, hm_ge_k, hm_jump ⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext ( m + 1 ) ) |>.2, by aesop ⟩;
        use m, hm_ge_k, hm_jump;
        intro j hj₁ hj₂; specialize hm_min j hj₁ hj₂; exact le_antisymm ( by exact s.x_ext_mono ( Nat.le_succ _ ) ) ( by exact le_of_not_gt hm_min ) ;
      -- By T_ge_T_add_diff, T(m) >= T(k) + (m-k) >= T(k).
      have h_T_m_ge_T_k : s.T m ≥ s.T k := by
        have h_T_m_ge_T_k : s.T m ≥ s.T k + (m - k : ℝ) := by
          apply Strategy.T_ge_T_add_diff s k m hm_ge_k hm_jump.right;
        linarith [ show ( m : ℝ ) ≥ k by norm_cast ];
      -- Since x jumps at m, by exists_Score_gt_of_jump with C = M, there exists y >= 1 such that Score(y) > M.
      obtain ⟨y, hy_ge_1, hy_score⟩ : ∃ y ≥ 1, s.Score y > M := by
        exact Strategy.exists_Score_gt_of_jump s m hm_jump.1 M ( by linarith );
      linarith [ hM y hy_ge_1 ]

/-
Proof that W <= W'.
-/
lemma Strategy.W_le_W' (s : Strategy) : s.W ≤ s.W' := by
  by_cases h : BddAbove {s.T k | k : ℕ}
  · exact Strategy.W_le_W'_of_bddAbove s h
  · have h_score : ¬ BddAbove {s.Score y | y ≥ 1} := Strategy.not_bddAbove_Score_of_not_bddAbove_T s h
    rw [Strategy.W, Real.sSup_of_not_bddAbove h_score]
    rw [Strategy.W', Real.sSup_of_not_bddAbove h]

/-
Lemma: If x jumps at k, then T(k) <= W (assuming scores are bounded).
-/
lemma Strategy.T_le_W_of_jump (s : Strategy) (k : ℕ) (h_jump : s.x_ext k < s.x_ext (k + 1))
    (h_bdd : BddAbove {s.Score y | y ≥ 1}) : s.T k ≤ s.W := by
      -- Assume for contradiction that $\lim_{y \to x_k^+} Score(y) > W$.
      by_contra h_contra;
      -- Then there exists some $C$ such that $s.T k > C > s.W$.
      obtain ⟨C, hC⟩ : ∃ C, s.T k > C ∧ C > s.W := by
        exact ⟨ ( s.T k + s.W ) / 2, by linarith, by linarith ⟩;
      -- By the lemma, there exists $y \geq 1$ such that $Score(y) > C$.
      obtain ⟨y, hy⟩ : ∃ y ≥ 1, s.Score y > C := by
        apply Strategy.exists_Score_gt_of_jump s k h_jump C hC.left;
      linarith [ show s.W ≥ s.Score y by exact le_csSup h_bdd ⟨ y, hy.1, rfl ⟩ ]

/-
Lemma: T(k) <= W for all k (assuming scores are bounded).
-/
lemma Strategy.T_le_W (s : Strategy) (k : ℕ) (h_bdd : BddAbove {s.Score y | y ≥ 1}) : s.T k ≤ s.W := by
  -- Let m be the smallest index >= k such that x jumps at m.
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext (m + 1) ∧ ∀ i, k ≤ i → i < m → s.x_ext i = s.x_ext (i + 1) := by
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext (m + 1) := by
      exact?;
    -- Let $m$ be the smallest index $\geq k$ such that $x$ jumps at $m$.
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ≥ k ∧ s.x_ext m < s.x_ext (m + 1) ∧ ∀ i, k ≤ i → i < m → ¬(s.x_ext i < s.x_ext (i + 1)) := by
      exact ⟨ Nat.find ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext ( m + 1 ) ), Nat.find_spec ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext ( m + 1 ) ) |>.1, Nat.find_spec ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m ≥ k, s.x_ext m < s.x_ext ( m + 1 ) ) |>.2, by aesop ⟩;
    use m, hm₁, hm₂.left
    intro i hi₁ hi₂
    have h_eq : s.x_ext i ≤ s.x_ext (i + 1) := by
      apply s.x_ext_mono; exact Nat.le_succ i
    have h_eq' : s.x_ext i ≥ s.x_ext (i + 1) := by
      exact le_of_not_gt fun h => hm₂.2 i hi₁ hi₂ h
    exact le_antisymm h_eq h_eq';
  -- By T_ge_T_add_diff, T(m) ≥ T(k) + (m-k) ≥ T(k).
  have h_Tm_ge_Tk : s.T m ≥ s.T k + (m - k : ℝ) := by
    have := Strategy.T_ge_T_add_diff s k m hm₁ hm₂.2; aesop;
  have := Strategy.T_le_W_of_jump s m hm₂.1 h_bdd;
  linarith [ show ( m : ℝ ) ≥ k by norm_cast ]

/-
Lemma: W = W'.
-/
lemma Strategy.W_eq_W' (s : Strategy) : s.W = s.W' := by
  by_cases h_bdd : BddAbove { s.Score y | y ≥ 1 };
  · refine' le_antisymm ( Strategy.W_le_W' s ) _;
    refine' csSup_le _ _;
    · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
    · exact fun x hx => hx.choose_spec ▸ Strategy.T_le_W s _ h_bdd;
  · unfold Strategy.W Strategy.W';
    rw [ Real.sSup_of_not_bddAbove h_bdd ];
    rw [ Real.sSup_of_not_bddAbove ];
    contrapose! h_bdd;
    exact ⟨ h_bdd.choose, by rintro x ⟨ y, hy, rfl ⟩ ; obtain ⟨ k, hk ⟩ := s.exists_k_Score_le_T y hy; exact hk.trans ( h_bdd.choose_spec ⟨ k, rfl ⟩ ) ⟩

/-
Definition of the strategy x_n = 2^{n-1}.
-/
def pow2_x (n : ℕ) : ℝ := if n = 0 then 1 else 2^(n-1)

def pow2Strategy : Strategy where
  x := pow2_x
  mono := by
    unfold pow2_x;
    intro m n hmn;
    cases m <;> cases n <;> simp_all +decide [ pow_le_pow_right₀ ];
    exact one_le_pow₀ ( by norm_num )
  one_le_x1 := by
    convert one_le_pow₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) using 1
  tendsto_atTop := by
    refine' Filter.tendsto_atTop_atTop.mpr _;
    intro b
    obtain ⟨i, hi⟩ : ∃ i : ℕ, 2^i > b := by
      exact pow_unbounded_of_one_lt b one_lt_two;
    unfold pow2_x;
    exact ⟨ i + 1, fun n hn => by rw [ if_neg ( by linarith ) ] ; exact le_trans hi.le ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_pred_of_lt hn ) ) ⟩

/-
Lemma: S_n for the doubling strategy is 2^n - 1.
-/
lemma pow2Strategy_S (n : ℕ) : pow2Strategy.S n = (2 : ℝ)^n - 1 := by
  -- We can prove this by induction on $n$.
  induction' n with n ih;
  · norm_num [ pow2Strategy ];
    exact?;
  · unfold pow2Strategy;
    unfold Strategy.S at *;
    erw [ Finset.sum_Ioc_succ_top, ih ] <;> norm_num [ pow_succ', pow2_x ];
    ring

/-
Lemma: T(k) for the doubling strategy.
-/
lemma pow2Strategy_T (k : ℕ) : pow2Strategy.T k = if k = 0 then 1 else 4 - (2 : ℝ)⁻¹ ^ (k - 1) := by
  -- By definition of $T$, we know that $T(k) = S_{k+1} / x_k$.
  have h_T_def : ∀ k, pow2Strategy.T k = (pow2Strategy.S (k + 1)) / (pow2_x k) := by
    unfold Strategy.T Strategy.x_ext;
    bound;
  -- By definition of $S$, we know that $S_{k+1} = 2^{k+1} - 1$.
  have h_S_def : ∀ k, pow2Strategy.S (k + 1) = (2 : ℝ)^(k + 1) - 1 := by
    exact?;
  rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
  · norm_num [ pow2_x ];
  · unfold pow2_x; ring;
    simpa using by ring;

/-
Lemma: The worst-case score of the doubling strategy is 4.
-/
lemma pow2Strategy_W : pow2Strategy.W = 4 := by
  rw [ Strategy.W_eq_W' ];
  refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _ <;> norm_num;
  · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
  · intro k; rw [ pow2Strategy_T ] ; split_ifs <;> norm_num;
  · intro w hw;
    -- Since $w < 4$, we can choose $a$ such that $2^{-a} < 4 - w$.
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (2 : ℝ)⁻¹ ^ a < 4 - w := by
      exact exists_pow_lt_of_lt_one ( by linarith ) ( by norm_num );
    use a + 1;
    rw [ pow2Strategy_T ] ; norm_num at * ; linarith

/-
Definitions of auxiliary sequences a_n and t_n.
-/
def Strategy.a (s : Strategy) (n : ℕ) : ℝ := s.S n / s.x n
def Strategy.t (s : Strategy) (n : ℕ) : ℝ := s.x (n + 1) / s.x n

/-
Lemma: T(n) = a(n) + t(n) for n >= 1.
-/
lemma Strategy.T_eq_a_add_t (s : Strategy) (n : ℕ) (hn : 1 ≤ n) :
  s.T n = s.a n + s.t n := by
    unfold Strategy.T Strategy.a Strategy.t;
    field_simp;
    rw [ show s.S ( n + 1 ) = s.S n + s.x ( n + 1 ) from ?_ ];
    · unfold Strategy.x_ext; aesop;
    · unfold Strategy.S; simp +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;

/-
Lemma: If Score(y) <= R for all y, then a_n + t_n <= R.
-/
def Strategy.BoundedBy (s : Strategy) (R : ℝ) : Prop :=
  ∀ y ≥ 1, s.Score y ≤ R

lemma Strategy.a_add_t_le_R (s : Strategy) (R : ℝ) (h : s.BoundedBy R) (n : ℕ) (hn : 1 ≤ n) :
  s.a n + s.t n ≤ R := by
    rw [ ← Strategy.T_eq_a_add_t ];
    · -- By definition of $W$, we know that $T(k) \leq W$ for all $k$.
      have h_T_le_W : ∀ k : ℕ, s.T k ≤ s.W := by
        -- By definition of $W$, we know that $T(k) \leq W$ for all $k$ because $W$ is the supremum of the scores.
        intros k
        apply Strategy.T_le_W;
        exact ⟨ R, by rintro x ⟨ y, hy, rfl ⟩ ; exact h y hy ⟩;
      -- Since $W \leq R$ by the definition of $BoundedBy$, we can conclude that $s.T n \leq R$.
      have h_W_le_R : s.W ≤ R := by
        apply csSup_le;
        · exact ⟨ _, ⟨ 1, by norm_num, rfl ⟩ ⟩;
        · aesop;
      exact le_trans ( h_T_le_W n ) h_W_le_R;
    · exact?

/-
Lemma: a_n + t_n <= R.
-/
lemma Strategy.a_add_t_le_R_aux (s : Strategy) (R : ℝ) (h : ∀ y ≥ 1, s.Score y ≤ R) (n : ℕ) (hn : 1 ≤ n) :
  s.a n + s.t n ≤ R := by
    rw [ ← Strategy.T_eq_a_add_t s n hn ]
    have h_bdd : BddAbove {s.Score y | y ≥ 1} := by
      use R
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    have h_T_le_W : s.T n ≤ s.W := Strategy.T_le_W s n h_bdd
    have h_W_le_R : s.W ≤ R := by
      apply csSup_le
      · exact ⟨ _, ⟨ 1, by norm_num, rfl ⟩ ⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact h y hy
    exact le_trans h_T_le_W h_W_le_R

/-
Definitions of g(a) and the sequence b_n (shifted by 1, so b_seq 0 = b_1 = 1).
-/
def g (R a : ℝ) : ℝ := R / (R - a)

def b_seq (R : ℝ) : ℕ → ℝ
| 0 => 1
| n + 1 => g R (b_seq R n)

/-
Lemma: a_n <= R - 1.
-/
lemma Strategy.a_le_R_sub_one (s : Strategy) (R : ℝ) (h : s.BoundedBy R) (n : ℕ) (hn : 1 ≤ n) :
  s.a n ≤ R - 1 := by
    -- By Lemma 2, we know that $t_n \geq 1$ for all $n \geq 1$.
    have h_t_ge_1 : ∀ n, 1 ≤ n → s.t n ≥ 1 := by
      exact fun n hn => one_le_div ( show 0 < s.x n from lt_of_lt_of_le zero_lt_one ( s.one_le_x1.trans ( s.mono hn ) ) ) |>.2 ( s.mono ( Nat.le_succ _ ) );
    linarith [ h_t_ge_1 n hn, Strategy.a_add_t_le_R_aux s R h n hn ]

/-
Lemma: a_{n+1} >= g(R, a_n).
-/
lemma Strategy.a_succ_ge (s : Strategy) (R : ℝ) (h : s.BoundedBy R) (n : ℕ) (hn : 1 ≤ n) :
  s.a (n + 1) ≥ g R (s.a n) := by
    have h_an1 : s.a (n + 1) = s.a n / s.t n + 1 := by
      -- By definition of $S$, we have $S_{n+1} = S_n + x_{n+1}$.
      have h_S_succ : s.S (n + 1) = s.S n + s.x (n + 1) := by
        exact Finset.sum_Ioc_succ_top ( by norm_num ) _;
      unfold Strategy.a Strategy.t
      field_simp [h_S_succ];
      rw [ mul_div_mul_right, div_add_one ];
      · rw [h_S_succ];
      · linarith [ s.mono ( show n + 1 ≥ 1 by linarith ), show 1 ≤ s.x 1 from s.one_le_x1 ];
      · exact ne_of_gt ( lt_of_lt_of_le zero_lt_one ( s.mono ( Nat.one_le_iff_ne_zero.mpr ( by linarith ) ) |> le_trans ( s.one_le_x1 ) ) );
    have h_t_le : s.t n ≤ R - s.a n := by
      have := Strategy.a_add_t_le_R_aux s R h n hn; linarith!;
    have h_pos : 0 < s.a n := by
      exact div_pos ( show 0 < s.S n from Finset.sum_pos ( fun i hi => by linarith [ show 1 ≤ s.x i from by exact Nat.le_induction ( by linarith [ s.one_le_x1 ] ) ( fun k hk ih => by linarith [ s.mono ( Nat.le_succ k ) ] ) i ( Finset.mem_Icc.mp hi |>.1 ) ] ) ( by norm_num; linarith ) ) ( show 0 < s.x n from by exact Nat.le_induction ( by linarith [ s.one_le_x1 ] ) ( fun k hk ih => by linarith [ s.mono ( Nat.le_succ k ) ] ) n hn );
    have h_pos_t : 0 < s.t n := by
      exact div_pos ( show 0 < s.x ( n + 1 ) from lt_of_lt_of_le ( show 0 < s.x 1 from lt_of_lt_of_le ( by norm_num ) ( s.one_le_x1 ) ) ( s.mono ( by linarith ) ) ) ( show 0 < s.x n from lt_of_lt_of_le ( show 0 < s.x 1 from lt_of_lt_of_le ( by norm_num ) ( s.one_le_x1 ) ) ( s.mono ( by linarith ) ) );
    unfold g;
    rw [ h_an1, ge_iff_le, div_add_one, div_le_div_iff₀ ] <;> nlinarith [ mul_div_cancel₀ ( s.a n ) h_pos_t.ne' ]

/-
Lemma: g(R, a) is increasing in a for a < R.
-/
lemma g_mono (R : ℝ) (hR : 0 < R) (x y : ℝ) (hx : x ≤ y) (hy : y < R) :
  g R x ≤ g R y := by
    unfold g;
    gcongr ; linarith

/-
Lemma: a_n >= b_{n-1}.
-/
lemma Strategy.a_ge_b (s : Strategy) (R : ℝ) (h : s.BoundedBy R) (hR : 0 < R) (n : ℕ) (hn : 1 ≤ n) :
  s.a n ≥ b_seq R (n - 1) := by
    -- We proceed by induction on $n$.
    induction' n, Nat.succ_le.mpr hn using Nat.le_induction with n ih;
    · -- For the base case $n = 1$, we have $a_1 = \frac{S_1}{x_1} = \frac{x_1}{x_1} = 1$.
      simp [Strategy.a, Strategy.S];
      rw [ div_self ] <;> norm_num [ b_seq ] ; linarith [ s.one_le_x1 ];
    · -- By the induction hypothesis, we have $s.a n \geq b_seq R (n - 1)$.
      have h_ind : s.a n ≥ b_seq R (n - 1) := by
        solve_by_elim;
      -- By the induction hypothesis and the definition of $b_seq$, we have $g R (s.a n) \geq b_seq R n$.
      have h_g : g R (s.a n) ≥ b_seq R n := by
        have h_g : g R (b_seq R (n - 1)) ≤ g R (s.a n) := by
          apply g_mono;
          · exact?;
          · exact h_ind;
          · exact lt_of_le_of_lt ( Strategy.a_le_R_sub_one s R h n ih ) ( by linarith );
        cases n <;> aesop;
      exact le_trans h_g ( by simpa using Strategy.a_succ_ge s R h n ih )

/-
Lemma: g(a) > a for a < R < 4.
-/
lemma g_gt_self (R a : ℝ) (hR : 0 < R) (hR4 : R < 4) (ha : a < R) :
  g R a > a := by
    unfold g;
    rw [ gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ sq_nonneg ( a - R / 2 ) ]

/-
Lemma: b_n is not bounded by R-1.
-/
lemma b_seq_not_bounded_by_R (R : ℝ) (hR0 : 0 < R) (hR4 : R < 4) :
  ¬ (∀ n, b_seq R n ≤ R - 1) := by
    by_contra! h;
    -- Since the sequence $b_n$ is strictly increasing and bounded above by $R - 1$, it must converge to some limit $L \leq R - 1$.
    have h_converge : ∃ L, Filter.Tendsto (fun n => b_seq R n) Filter.atTop (nhds L) ∧ L ≤ R - 1 := by
      have h_inc : StrictMono (fun n => b_seq R n) := by
        refine' strictMono_nat_of_lt_succ _;
        intro n;
        exact g_gt_self R ( b_seq R n ) hR0 hR4 ( by linarith [ h n ] );
      exact ⟨ _, tendsto_atTop_isLUB h_inc.monotone ( isLUB_ciSup ⟨ R - 1, Set.forall_mem_range.mpr h ⟩ ), by exact ciSup_le h ⟩;
    -- By continuity of $g$ on $(-\infty, R)$, $L = g(L)$.
    obtain ⟨L, hL_tendsto, hL_le⟩ := h_converge
    have hL_eq : L = g R L := by
      have hL_eq : Filter.Tendsto (fun n => g R (b_seq R n)) Filter.atTop (nhds (g R L)) := by
        exact Filter.Tendsto.div tendsto_const_nhds ( tendsto_const_nhds.sub hL_tendsto ) ( by linarith );
      exact tendsto_nhds_unique hL_tendsto ( by rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; simpa only [ show ( fun n => b_seq R ( n + 1 ) ) = fun n => g R ( b_seq R n ) from funext fun n => rfl ] using hL_eq );
    unfold g at hL_eq;
    rw [ eq_div_iff ] at hL_eq <;> try linarith;
    nlinarith [ sq_nonneg ( L - R / 2 ) ]

/-
Definition of the sequence x_n = (n+1)2^{n-2}.
-/
def tight_x (n : ℕ) : ℝ := (n + 1) * (2 : ℝ)^n / 4

/-
The tight unbounded strategy using the sequence x_n.
-/
def tightUnboundedStrategy : Strategy := {
  x := tight_x
  mono := by
    exact fun m n hmn => by exact div_le_div_of_nonneg_right ( by gcongr ; linarith ) zero_le_four;
  one_le_x1 := by
    unfold tight_x; norm_num
  tendsto_atTop := by
    unfold tight_x;
    refine' Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop;
    intro n; rw [ le_div_iff₀ ] <;> norm_cast ; induction' n with n ih <;> norm_num [ pow_succ' ] at * ; nlinarith [ Nat.one_le_pow n 2 zero_lt_two ] ;
}

/-
The tight unbounded strategy has worst-case score 4.
-/
theorem prop_tight_unbounded :
    (∀ n ≥ 1, tightUnboundedStrategy.S (n + 1) = 4 * tightUnboundedStrategy.x n) ∧
    tightUnboundedStrategy.W = 4 := by
      have h_sum : ∀ n ≥ 1, tightUnboundedStrategy.S (n + 1) = 4 * tightUnboundedStrategy.x n := by
        intro n hn;
        unfold tightUnboundedStrategy;
        unfold Strategy.S;
        unfold tight_x; induction hn <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc), pow_succ' ] at * ; linarith;
      have h_T : ∀ n ≥ 1, tightUnboundedStrategy.T n = 4 := by
        intros n hn
        unfold Strategy.T
        simp [h_sum n hn];
        unfold Strategy.x_ext;
        rw [ if_neg ( by linarith ), mul_div_cancel_right₀ _ ( ne_of_gt ( show 0 < tightUnboundedStrategy.x n from by exact div_pos ( mul_pos ( by linarith ) ( pow_pos ( by norm_num ) _ ) ) ( by norm_num ) ) ) ];
      have h_T_eq : tightUnboundedStrategy.T 0 = 1 := by
        unfold Strategy.T; norm_num [ Strategy.S, Strategy.x_ext ] ;
        unfold tightUnboundedStrategy; norm_num [ tight_x ] ;
      have h_W : tightUnboundedStrategy.W = sSup {tightUnboundedStrategy.T n | n : ℕ} := by
        -- By definition of $W$, we know that $W = W'$.
        apply Strategy.W_eq_W';
      rw [ h_W ];
      exact ⟨ h_sum, le_antisymm ( csSup_le ⟨ _, ⟨ 1, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ n, rfl ⟩ ; exact if hn : n ≥ 1 then h_T n hn ▸ by norm_num else by interval_cases n ; norm_num [ h_T_eq ] ) ( le_csSup ⟨ 4, by rintro x ⟨ n, rfl ⟩ ; exact if hn : n ≥ 1 then h_T n hn ▸ by norm_num else by interval_cases n ; norm_num [ h_T_eq ] ⟩ ⟨ 1, by norm_num [ h_T ] ⟩ ) ⟩

/-
A strategy is bounded if its set of scores is bounded above.
-/
def Strategy.IsBounded (s : Strategy) : Prop := BddAbove {s.Score y | y ≥ 1}

/-
The tight unbounded strategy is bounded.
-/
lemma tightUnboundedStrategy_isBounded : tightUnboundedStrategy.IsBounded := by
  unfold Strategy.IsBounded;
  -- By definition of $W$, we know that $W = 4$.
  have hW : tightUnboundedStrategy.W = 4 := by
    exact prop_tight_unbounded.2;
  contrapose! hW;
  unfold Strategy.W; aesop;

/-
The value of the unbounded game, defined as the infimum of worst-case scores over all bounded strategies.
-/
def V_infty_correct : ℝ := sInf { x | ∃ s : Strategy, s.IsBounded ∧ s.W = x }

/-
The score is bounded by the worst-case score.
-/
lemma Strategy.score_le_W (s : Strategy) (h : s.IsBounded) (y : ℝ) (hy : 1 ≤ y) : s.Score y ≤ s.W := by
  exact le_csSup h ⟨ y, hy, rfl ⟩

/-
The value of the unbounded game is 4.
-/
theorem thm_unbounded_value_correct : V_infty_correct = 4 := by
  refine' le_antisymm _ _;
  · -- The tight unbounded strategy has a worst-case score of 4 and is bounded, so 4 is in the set of worst-case scores of bounded strategies.
    have h_tight_in_set : ∃ s : Strategy, s.IsBounded ∧ s.W = 4 := by
      use tightUnboundedStrategy;
      exact ⟨ tightUnboundedStrategy_isBounded, by exact prop_tight_unbounded.2 ⟩;
    exact csInf_le ⟨ 0, by rintro x ⟨ s, hs, rfl ⟩ ; exact ( by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ y, hy, rfl ⟩ ; exact div_nonneg ( Finset.sum_nonneg fun _ _ => le_of_lt <| by linarith [ show 0 < s.x ‹_› from by linarith [ show 1 ≤ s.x ‹_› from by exact s.mono ( show 1 ≤ _ from by aesop ) |> le_trans ( show 1 ≤ s.x 1 from by linarith [ s.one_le_x1 ] ) ] ] ) <| by linarith [ show 1 ≤ y from by linarith ] ) ⟩ h_tight_in_set;
  · refine' le_csInf _ _;
    · exact ⟨ _, ⟨ tightUnboundedStrategy, tightUnboundedStrategy_isBounded, rfl ⟩ ⟩;
    · rintro _ ⟨ s, hs, rfl ⟩;
      -- By Lemma 2, if W < 4, then a_n ≤ W - 1 and a_n ≥ b_{n-1}.
      by_contra h_contra
      have h_a_le : ∀ n ≥ 1, s.a n ≤ s.W - 1 := by
        apply_rules [ Strategy.a_le_R_sub_one ];
        exact fun y hy => s.score_le_W hs y hy
      have h_a_ge : ∀ n ≥ 1, s.a n ≥ b_seq s.W (n - 1) := by
        apply Strategy.a_ge_b;
        · exact fun y hy => s.score_le_W hs y hy;
        · have := h_a_le 1 le_rfl;
          exact lt_of_lt_of_le ( show 0 < s.a 1 from div_pos ( show 0 < s.S 1 from by exact Finset.sum_pos ( fun i hi => by exact lt_of_lt_of_le zero_lt_one ( by exact s.one_le_x1.trans ( s.mono ( Nat.one_le_iff_ne_zero.mpr <| by aesop ) ) ) ) <| by norm_num ) <| by exact lt_of_lt_of_le zero_lt_one <| by exact s.one_le_x1.trans <| s.mono <| Nat.one_le_iff_ne_zero.mpr <| by aesop ) <| by linarith;
      -- But b_n is unbounded for W < 4. Contradiction.
      have h_b_unbounded : ¬ (∀ n, b_seq s.W n ≤ s.W - 1) := by
        apply b_seq_not_bounded_by_R;
        · have := h_a_ge 1 le_rfl; norm_num at this;
          unfold b_seq at this; linarith [ h_a_le 1 le_rfl ] ;
        · linarith;
      exact h_b_unbounded fun n => by simpa using h_a_ge ( n + 1 ) ( by linarith ) |> le_trans <| h_a_le ( n + 1 ) ( by linarith ) ;

/-
Helper lemma: x_k = S_k - S_{k-1}.
-/
lemma BStrategy.x_succ_eq_S_sub_S {B : ℝ} (s : BStrategy B) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ s.n) :
    s.x_safe k = s.S k - s.S (k - 1) := by
      unfold BStrategy.x_safe BStrategy.S;
      cases k <;> simp_all +decide [ Finset.sum_range_succ ];
      grind

/-
Extended strategy sequence x_0=1, x_k for k>=1, is monotone.
-/
def BStrategy.x_ext {B : ℝ} (s : BStrategy B) (k : ℕ) : ℝ :=
  if k = 0 then 1 else s.x_safe k

lemma BStrategy.x_ext_mono {B : ℝ} (s : BStrategy B) : Monotone s.x_ext := by
  -- By definition of $x_ext$, we know that $x_ext$ is monotone.
  unfold BStrategy.x_ext
  simp [Monotone];
  intro a b hab; split_ifs <;> simp_all +decide [ BStrategy.x_safe ] ;
  · split_ifs;
    · exact le_trans s.one_le_x1 ( s.mono ( Nat.zero_le _ ) );
    · linarith [ s.one_le_x1, s.xn_eq_B, s.mono ( show ⟨ 0, s.n_pos ⟩ ≤ ⟨ s.n - 1, Nat.sub_lt s.n_pos zero_lt_one ⟩ from Nat.zero_le _ ) ];
  · split_ifs <;> norm_num at *;
    · exact s.mono ( Nat.sub_le_sub_right hab 1 );
    · linarith [ ‹1 ≤ b → s.n < b› ( by linarith ), s.mono ( show ⟨ a - 1, by omega ⟩ ≤ ⟨ s.n - 1, by omega ⟩ from Nat.sub_le_sub_right ( by linarith ) _ ), s.xn_eq_B ];
    · grind

/-
If x_k = x_{k+1}, then S_{k+2}/x_{k+1} >= S_{k+1}/x_k + 1.
-/
lemma BStrategy.ratio_increasing_of_eq {B : ℝ} (s : BStrategy B) (k : ℕ) (hk : k + 1 < s.n)
    (heq : s.x_ext k = s.x_ext (k + 1)) (hx_pos : 0 < s.x_ext k) :
    s.S (k + 1) / s.x_ext k + 1 ≤ s.S (k + 2) / s.x_ext (k + 1) := by
      rw [ div_add_one, div_le_div_iff₀ ];
      · -- By definition of $S$, we have $S (k + 2) = S (k + 1) + x_{k+2}$.
        have hS_succ : s.S (k + 2) = s.S (k + 1) + s.x_safe (k + 2) := by
          unfold BStrategy.S;
          simp +decide [ Finset.sum_range_succ, BStrategy.x_safe ];
          grind;
        -- By definition of $x_{ext}$, we have $x_{ext} (k + 2) \ge x_{ext} k$.
        have hx_ext_mono : s.x_ext k ≤ s.x_ext (k + 2) := by
          exact s.x_ext_mono ( Nat.le_succ_of_le ( Nat.le_succ _ ) );
        unfold BStrategy.x_ext at * ; aesop;
      · exact?;
      · linarith;
      · positivity

/-
If x_k < x_{k+1}, then S_{k+1} <= R * x_k.
-/
lemma BStrategy.S_le_R_x_of_jump {B : ℝ} (s : BStrategy B) {R : ℝ} (hW : s.W ≤ R) (k : ℕ) (hk : k < s.n)
    (hjump : s.x_ext k < s.x_ext (k + 1)) :
    s.S (k + 1) ≤ R * s.x_ext k := by
      -- Consider any $y$ in the interval $(x_k, x_{k+1}]$. Then $N(y) = k + 1$, so $\text{Score}(y) = S_{k+1}/y$.
      have h_score_ge : ∀ y ∈ Set.Ioo (s.x_ext k) (s.x_ext (k + 1)), s.Score y = s.S (k + 1) / y := by
        intro y hy
        unfold BStrategy.Score
        have hN : s.N y = k + 1 := by
          refine' le_antisymm _ _;
          · refine' Nat.sInf_le ⟨ _, _, hy.2.le ⟩;
            · linarith;
            · linarith;
          · refine' le_csInf _ _;
            · exact ⟨ k + 1, Nat.succ_pos _, Nat.succ_le_of_lt hk, hy.2.le ⟩;
            · intro b hb;
              contrapose! hjump;
              -- Since $b < k + 1$, we have $s.x_ext b \leq s.x_ext k$ by the monotonicity of $s.x_ext$.
              have h_monotone : s.x_ext b ≤ s.x_ext k := by
                exact BStrategy.x_ext_mono _ ( by linarith );
              linarith [ hy.1, hy.2, hb.2.2, show s.x_ext b = s.x_safe b from by unfold BStrategy.x_ext; aesop ]
        rw [hN];
      -- Since $y \in (x_k, x_{k+1}]$, we have $\text{Score}(y) \le W \le R$.
      have h_score_le_R : ∀ y ∈ Set.Ioo (s.x_ext k) (s.x_ext (k + 1)), s.Score y ≤ R := by
        intros y hy
        have h_score_le_W : s.Score y ≤ s.W := by
          apply le_csSup;
          · have h_bdd_above : BddAbove (Set.image (fun y => s.Score y) (Set.Icc 1 B)) := by
              have h_bdd_above : BddAbove (Set.image (fun y => s.S (s.N y) / y) (Set.Icc 1 B)) := by
                have h_finite : Set.Finite (Set.image (fun y => s.N y) (Set.Icc 1 B)) := by
                  refine Set.Finite.subset ( Set.finite_Icc 0 s.n ) ?_;
                  rintro _ ⟨ y, hy, rfl ⟩;
                  unfold BStrategy.N;
                  field_simp;
                  by_cases h : ∃ k, 1 ≤ k ∧ k ≤ s.n ∧ y ≤ s.x_safe k;
                  · exact ⟨ Nat.zero_le _, le_trans ( csInf_le ⟨ 0, fun k hk => Nat.zero_le _ ⟩ h.choose_spec ) h.choose_spec.2.1 ⟩;
                  · rw [ show { k | 1 ≤ k ∧ k ≤ s.n ∧ y ≤ s.x_safe k } = ∅ by ext; aesop ] ; norm_num
                have h_bdd_above : BddAbove (Set.image (fun n => s.S n / 1) (Set.image (fun y => s.N y) (Set.Icc 1 B))) := by
                  exact Set.Finite.bddAbove ( h_finite.image _ );
                obtain ⟨ M, hM ⟩ := h_bdd_above;
                exact ⟨ M, Set.forall_mem_image.2 fun x hx => by have := hM ⟨ s.N x, Set.mem_image_of_mem _ hx, rfl ⟩ ; exact le_trans ( div_le_div_of_nonneg_left ( by linarith [ show 0 ≤ s.S ( s.N x ) from Finset.sum_nonneg fun _ _ => by
                                                                                                                                                                                    split_ifs <;> norm_num;
                                                                                                                                                                                    exact le_trans ( by norm_num ) ( s.one_le_x1.trans ( s.mono ( Nat.zero_le _ ) ) ) ] ) ( by linarith [ Set.mem_Icc.mp hx ] ) ( by linarith [ Set.mem_Icc.mp hx ] ) ) this ⟩;
              exact h_bdd_above;
            exact h_bdd_above;
          · -- Since $y$ is in the interval $(x_k, x_{k+1}]$, and $x_k$ and $x_{k+1}$ are part of the strategy's sequence, which is non-decreasing and starts at 1, we have $1 \leq y \leq B$.
            have hy_bounds : 1 ≤ y ∧ y ≤ B := by
              field_simp;
              constructor;
              · -- Since $s.x_ext k$ is part of the strategy's sequence, which is non-decreasing and starts at 1, we have $1 \leq s.x_ext k$.
                have h_x_ext_k_ge_1 : 1 ≤ s.x_ext k := by
                  unfold BStrategy.x_ext;
                  split_ifs <;> simp_all +decide [ BStrategy.x_safe ];
                  rw [ if_pos ⟨ Nat.pos_of_ne_zero ‹_›, hk.le ⟩ ];
                  exact le_trans ( s.one_le_x1 ) ( s.mono ( Nat.zero_le _ ) );
                linarith [ hy.1 ];
              · refine' hy.2.le.trans _;
                unfold BStrategy.x_ext;
                unfold BStrategy.x_safe;
                field_simp;
                split_ifs <;> norm_num;
                · linarith;
                · linarith;
                · contradiction;
                · exact le_trans ( s.mono ( Nat.le_sub_one_of_lt hk ) ) ( by linarith [ s.xn_eq_B ] );
            exact ⟨ y, hy_bounds, rfl ⟩;
        linarith;
      -- Taking the limit as $y \downarrow x_k$, we get $S_{k+1} \le R x_k$.
      have h_limit : Filter.Tendsto (fun y => s.S (k + 1) / y) (nhdsWithin (s.x_ext k) (Set.Ioi (s.x_ext k))) (nhds (s.S (k + 1) / s.x_ext k)) := by
        exact tendsto_const_nhds.div ( Filter.tendsto_id.mono_left inf_le_left ) ( by linarith [ show 0 < s.x_ext k from by exact lt_of_lt_of_le zero_lt_one <| by exact le_trans ( by norm_num ) <| show 1 ≤ s.x_ext k from by exact Nat.recOn k ( by exact le_rfl ) fun n ihn => by exact le_trans ihn <| s.x_ext_mono <| Nat.le_succ _ ] );
      have h_limit_le_R : s.S (k + 1) / s.x_ext k ≤ R := by
        exact le_of_tendsto h_limit ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hjump ⟩ ) fun y hy => h_score_ge y hy ▸ h_score_le_R y hy );
      rwa [ div_le_iff₀ ( show 0 < s.x_ext k from _ ) ] at h_limit_le_R;
      unfold BStrategy.x_ext;
      split_ifs <;> simp_all +decide [ BStrategy.x_safe ];
      rw [ if_pos ⟨ Nat.pos_of_ne_zero ‹_›, hk.le ⟩ ];
      exact lt_of_lt_of_le ( show 0 < s.x ⟨ 0, by linarith ⟩ from by linarith [ s.one_le_x1 ] ) ( s.mono <| Nat.zero_le _ )

/-
Existence of a maximal index m >= k such that x_m = x_k.
-/
lemma BStrategy.exists_max_eq {B : ℝ} (s : BStrategy B) (k : ℕ) (hk : k ≤ s.n) :
    ∃ m, k ≤ m ∧ m ≤ s.n ∧ s.x_ext m = s.x_ext k ∧ (m = s.n ∨ s.x_ext m < s.x_ext (m + 1)) := by
      obtain ⟨m, hm⟩ : ∃ m ∈ Finset.Icc k s.n, s.x_ext m = s.x_ext k ∧ ∀ i ∈ Finset.Icc k s.n, s.x_ext i = s.x_ext k → i ≤ m := by
        exact ⟨ Finset.max' ( Finset.filter ( fun i => s.x_ext i = s.x_ext k ) ( Finset.Icc k s.n ) ) ⟨ k, by aesop ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun i => s.x_ext i = s.x_ext k ) ( Finset.Icc k s.n ) ) ⟨ k, by aesop ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun i => s.x_ext i = s.x_ext k ) ( Finset.Icc k s.n ) ) ⟨ k, by aesop ⟩ ) |>.2, fun i hi hi' => Finset.le_max' _ _ ( by aesop ) ⟩;
      exact ⟨ m, Finset.mem_Icc.mp hm.1 |>.1, Finset.mem_Icc.mp hm.1 |>.2, hm.2.1, Classical.or_iff_not_imp_left.2 fun h => lt_of_le_of_ne ( by exact ( BStrategy.x_ext_mono s ) ( by linarith [ Finset.mem_Icc.mp hm.1 |>.1, Finset.mem_Icc.mp hm.1 |>.2 ] ) ) ( Ne.symm <| by intro H; exact h <| by have := hm.2.2 ( m + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hm.1 |>.1, Finset.mem_Icc.mp hm.1 |>.2 ], by exact Nat.le_of_not_lt fun hmn => h <| by linarith [ Finset.mem_Icc.mp hm.1 |>.1, Finset.mem_Icc.mp hm.1 |>.2 ] ⟩ ) ; aesop ) ⟩

/-
Definition of tight polynomials p_k(R).
-/
def p_poly (R : ℝ) : ℕ → ℝ
| 0 => 1
| 1 => R
| (k + 2) => R * (p_poly R (k + 1) - p_poly R k)

/-
Definition of strict B-strategy and lemma about N(y).
-/
def BStrategy.Strict {B : ℝ} (s : BStrategy B) : Prop :=
  ∀ k, k < s.n → s.x_ext k < s.x_ext (k + 1)

lemma BStrategy.N_eq_of_strict {B : ℝ} (s : BStrategy B) (h_strict : s.Strict) (k : ℕ) (hk : k < s.n)
    (y : ℝ) (hy_gt : s.x_ext k < y) (hy_le : y ≤ s.x_ext (k + 1)) :
    s.N y = k + 1 := by
      refine' le_antisymm _ _;
      · refine' csInf_le _ _ <;> aesop;
      · refine' Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => _ );
        -- Since $k \geq s.N y$, we have $y \leq s.x_ext k$.
        have hy_le_xk : y ≤ s.x_ext k := by
          have hy_le_xk : y ≤ s.x_ext (s.N y) := by
            rw [ BStrategy.N ];
            have := Nat.sInf_mem ( show { k | 1 ≤ k ∧ k ≤ s.n ∧ y ≤ s.x_safe k }.Nonempty from ?_ );
            · unfold BStrategy.x_ext; aesop;
            · use k + 1;
              aesop;
          exact hy_le_xk.trans ( s.x_ext_mono h );
        linarith

/-
For a strict B-strategy, S_{k+1}/x_k <= W.
-/
lemma BStrategy.S_succ_div_x_le_W_of_strict {B : ℝ} (s : BStrategy B) (h_strict : s.Strict) (k : ℕ) (hk : k < s.n) :
    s.S (k + 1) / s.x_ext k ≤ s.W := by
      -- By definition of strict B-strategy, if $x_k < x_{k+1}$, then $S_{k+1} \leq W(B) x_k$.
      have h_strict_le : ∀ k, k < s.n → s.x_ext k < s.x_ext (k + 1) → s.S (k + 1) ≤ s.W * s.x_ext k := by
        intros k hk h_jump
        apply BStrategy.S_le_R_x_of_jump s (by
        rfl) k hk h_jump;
      rw [ div_le_iff₀ ];
      · exact h_strict_le k hk ( h_strict k hk );
      · induction' k with k ih;
        · unfold BStrategy.x_ext; aesop;
        · exact lt_of_lt_of_le ( ih ( Nat.lt_of_succ_lt hk ) ) ( h_strict k ( Nat.lt_of_succ_lt hk ) |> le_of_lt )

/-
Sum of p_poly terms: sum_{i=1}^{k+1} p_i = R p_k.
-/
lemma p_poly_sum {R : ℝ} (k : ℕ) : ∑ i ∈ Finset.range (k + 1), p_poly R (i + 1) = R * p_poly R k := by
  induction' k with k ih;
  · -- For the base case when $k = 0$, we see that the sum is just $p_poly R 1$.
    simp [p_poly];
  · rw [ Finset.sum_range_succ ];
    rw [ show p_poly R ( k + 2 ) = R * ( p_poly R ( k + 1 ) - p_poly R k ) from rfl ] ; linear_combination ih

/-
Lemma 3: If R = 4cos^2(theta) and sin(theta) != 0, then p_k(R) = (2cos(theta))^k * sin((k+1)theta) / sin(theta).
-/
lemma p_poly_trig (θ : ℝ) (hθ : Real.sin θ ≠ 0) (k : ℕ) :
    let R := 4 * Real.cos θ ^ 2
    p_poly R k = (2 * Real.cos θ) ^ k * (Real.sin ((k + 1) * θ) / Real.sin θ) := by
      -- We'll use induction on $k$ to prove this.
      induction' k using Nat.strong_induction_on with k ih generalizing θ; rcases k with ( _ | _ | k ) <;> norm_num at * ; aesop;
      · rw [ Real.sin_two_mul ] ; ring_nf ; aesop;
      · rw [ show p_poly ( 4 * Real.cos θ ^ 2 ) ( k + 1 + 1 ) = 4 * Real.cos θ ^ 2 * ( p_poly ( 4 * Real.cos θ ^ 2 ) ( k + 1 ) - p_poly ( 4 * Real.cos θ ^ 2 ) k ) by rfl ] ; rw [ ih ( k + 1 ) ( by linarith ) θ hθ, ih k ( by linarith ) θ hθ ] ; push_cast ; ring;
        rw [ show θ * 3 = θ * 2 + θ by ring, show θ * 2 = θ + θ by ring ] ; norm_num [ Real.sin_add, Real.cos_add ] ; ring;
        rw [ show Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 by ring, Real.sin_sq ] ; ring;

/-
Lemma 8 (part 1): If R = 4cos^2(theta) with theta in (0, pi), then p_{k+1}(R) - p_k(R) = (2cos(theta))^k * sin((k+3)theta) / sin(theta).
-/
lemma p_poly_diff_trig (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi) (k : ℕ) :
    let R := 4 * Real.cos θ ^ 2
    p_poly R (k + 1) - p_poly R k = (2 * Real.cos θ) ^ k * (Real.sin ((k + 3 : ℝ) * θ) / Real.sin θ) := by
      -- Apply Lemma 7 (p_poly_trig) to rewrite p_poly R (k + 1) and p_poly R k.
      have h_p_poly_trig : ∀ k : ℕ, p_poly (4 * Real.cos θ ^ 2) k = (2 * Real.cos θ) ^ k * (Real.sin ((k + 1) * θ) / Real.sin θ) := by
        exact fun k => p_poly_trig θ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt ) ) k;
      norm_num [ add_mul, Real.sin_add, h_p_poly_trig ] ; ring;
      rw [ show θ * 3 = 3 * θ by ring, Real.sin_three_mul, Real.cos_three_mul ] ; norm_num [ Real.sin_add, Real.cos_add ] ; ring;
      rw [ show Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 by ring, Real.sin_sq ] ; ring

/-
Lemma 8 (part 2): If 0 < theta <= pi/(m+3), then p_0(R) <= p_1(R) <= ... <= p_m(R).
-/
lemma p_poly_mono_of_small_theta (m : ℕ) (θ : ℝ) (hθ_pos : 0 < θ) (hθ_le : θ ≤ Real.pi / (m + 3)) :
    let R := 4 * Real.cos θ ^ 2
    ∀ k < m, p_poly R k ≤ p_poly R (k + 1) := by
      -- By Lemma 8 (part 1), $p_{k+1}(R) - p_k(R) = (2\cos\theta)^k \sin((k+3)\theta) / \sin\theta$.
      have h_diff_pos : ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi / (m + 3) → ∀ k < m, 0 ≤ (2 * Real.cos θ) ^ k * (Real.sin ((k + 3 : ℝ) * θ) / Real.sin θ) := by
        intros θ hθ_pos hθ_le k hk; exact mul_nonneg ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by nlinarith [ Real.pi_pos, ( by norm_cast : ( k:ℝ ) + 1 ≤ m ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by linarith : ( m:ℝ ) + 3 ≠ 0 ) ] ⟩ ) ) _ ) ( div_nonneg ( Real.sin_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, ( by norm_cast : ( k:ℝ ) + 1 ≤ m ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by linarith : ( m:ℝ ) + 3 ≠ 0 ) ], by nlinarith [ Real.pi_pos, ( by norm_cast : ( k:ℝ ) + 1 ≤ m ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by linarith : ( m:ℝ ) + 3 ≠ 0 ) ] ⟩ ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by nlinarith [ Real.pi_pos, ( by norm_cast : ( k:ℝ ) + 1 ≤ m ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by linarith : ( m:ℝ ) + 3 ≠ 0 ) ] ⟩ ) ) ;
      -- By Lemma 8 (part 1), $p_{k+1}(R) - p_k(R) = (2\cos\theta)^k \sin((k+3)\theta) / \sin\theta$. Therefore, $p_{k+1}(R) \geq p_k(R)$ for $k < m$.
      intros R k hk_lt_m
      have h_diff : p_poly R (k + 1) - p_poly R k = (2 * Real.cos θ) ^ k * (Real.sin ((k + 3 : ℝ) * θ) / Real.sin θ) := by
        convert p_poly_diff_trig θ hθ_pos ( by rw [ le_div_iff₀ <| by positivity ] at hθ_le; nlinarith [ Real.pi_pos ] ) k using 1;
      linarith [ h_diff_pos θ hθ_pos hθ_le k hk_lt_m ]

/-
Definition 9: rho_n = 4cos^2(pi/(n+3)), B_n = (2cos(pi/(n+3)))^(n+1).
-/
def rho (n : ℕ) : ℝ := 4 * Real.cos (Real.pi / (n + 3)) ^ 2

def B_val (n : ℕ) : ℝ := (2 * Real.cos (Real.pi / (n + 3))) ^ (n + 1)

/-
Lemma 10: p_n(rho_{n-1}) = B_{n-1} and p_n(rho_n) = B_n.
-/
lemma p_poly_endpoints (n : ℕ) (hn : 1 ≤ n) :
    p_poly (rho (n - 1)) n = B_val (n - 1) ∧
    p_poly (rho n) n = B_val n := by
      -- Apply the lemma p_poly_trig to both parts of the conjunction.
      apply And.intro;
      · -- Apply the lemma p_poly_trig with θ = π/(n+2).
        have h_trig : p_poly (rho (n - 1)) n = (2 * Real.cos (Real.pi / (n + 2))) ^ n * (Real.sin ((n + 1) * (Real.pi / (n + 2))) / Real.sin (Real.pi / (n + 2))) := by
          convert p_poly_trig _ _ _ using 3 <;> ring;
          · rw [ Nat.cast_sub hn ] ; ring;
          · rw [ Nat.cast_sub hn ] ; ring;
          · rw [ Nat.cast_sub hn ] ; ring;
          · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( mul_lt_of_lt_one_right Real.pi_pos ( inv_lt_one_of_one_lt₀ ( by norm_cast; linarith [ Nat.sub_add_cancel hn ] ) ) ) );
        rw [ h_trig ];
        rw [ show ( n + 1 : ℝ ) * ( Real.pi / ( n + 2 ) ) = Real.pi - Real.pi / ( n + 2 ) by nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n + 2 : ℝ ) ≠ 0 ) ], Real.sin_pi_sub ] ; norm_num [ B_val ];
        rw [ div_self <| ne_of_gt <| Real.sin_pos_of_pos_of_lt_pi ( by positivity ) <| by rw [ div_lt_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ] ; rw [ Nat.sub_add_cancel hn ] ; ring;
        rw [ Nat.cast_sub ( by linarith ) ] ; ring;
      · -- Apply the lemma p_poly_trig with θ = π/(n+3).
        have h_trig : p_poly (rho n) n = (2 * Real.cos (Real.pi / (n + 3))) ^ n * (Real.sin ((n + 1) * (Real.pi / (n + 3))) / Real.sin (Real.pi / (n + 3))) := by
          convert p_poly_trig ( Real.pi / ( n + 3 ) ) _ n using 1;
          exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( div_lt_self Real.pi_pos ( by norm_cast; linarith ) ) );
        rw [ h_trig, show ( n + 1 : ℝ ) * ( Real.pi / ( n + 3 ) ) = Real.pi - 2 * ( Real.pi / ( n + 3 ) ) by linarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ) ] ] ; norm_num [ Real.sin_two_mul, mul_assoc, mul_left_comm ] ; ring;
        rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( mul_lt_of_lt_one_right Real.pi_pos ( inv_lt_one_of_one_lt₀ ( by norm_cast; linarith ) ) ) ) ) ] ; unfold B_val ; ring;

/-
Lemma 11: p_n(R) is strictly increasing on [rho_{n-1}, rho_n].
-/
lemma p_poly_strict_mono (n : ℕ) (hn : 1 ≤ n) :
    StrictMonoOn (p_poly · n) (Set.Icc (rho (n - 1)) (rho n)) := by
      -- By definition of $p_poly$, we know that $p_poly(R, n) = (2 * cos(theta))^n * sin((n + 1) * theta) / sin(theta)$ for $R = 4 * cos^2(theta)$.
      have h_p_poly_trig : ∀ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), let R := 4 * Real.cos θ ^ 2; p_poly R n = (2 * Real.cos θ) ^ n * (Real.sin ((n + 1) * θ) / Real.sin θ) := by
        intros θ hθ
        apply p_poly_trig θ;
        exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hθ.1 ) ( lt_of_le_of_lt hθ.2 ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos ] ) ) );
      -- Since $R(\theta)$ is decreasing in $\theta$, $p_n(R)$ is increasing in $R$.
      have h_p_poly_inc : ∀ θ1 θ2 : ℝ, Real.pi / (n + 3) ≤ θ1 → θ1 < θ2 → θ2 ≤ Real.pi / (n + 2) → (2 * Real.cos θ1) ^ n * (Real.sin ((n + 1) * θ1) / Real.sin θ1) > (2 * Real.cos θ2) ^ n * (Real.sin ((n + 1) * θ2) / Real.sin θ2) := by
        intros θ1 θ2 hθ1 hθ2 hθ3
        have h_cos : Real.cos θ1 > Real.cos θ2 := by
          exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by linarith [ Real.pi_pos, div_nonneg Real.pi_pos.le ( by positivity : 0 ≤ ( n : ℝ ) + 3 ) ] ) ( by linarith [ Real.pi_pos, div_le_self Real.pi_pos.le ( by linarith : ( n : ℝ ) + 2 ≥ 1 ) ] ) hθ2
        have h_sin : Real.sin ((n + 1) * θ1) > Real.sin ((n + 1) * θ2) := by
          rw [ ← Real.cos_sub_pi_div_two, ← Real.cos_sub_pi_div_two ] ; refine' Real.cos_lt_cos_of_nonneg_of_le_pi _ _ _ <;> try nlinarith [ Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ];
          rw [ div_le_iff₀ ] at hθ1 <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ]
        have h_sin_theta : Real.sin θ1 < Real.sin θ2 := by
          rw [ ← Real.cos_pi_div_two_sub, ← Real.cos_pi_div_two_sub ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] );
        gcongr;
        · exact pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show 0 ≤ θ1 by exact le_trans ( by positivity ) hθ1 ], by linarith [ Real.pi_pos, show θ2 ≤ Real.pi / 2 by exact hθ3.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ⟩ ) ) _;
        · exact div_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi ( by exact mul_nonneg ( by positivity ) ( by linarith [ Real.pi_pos, show 0 ≤ θ1 by exact le_trans ( by positivity ) hθ1 ] ) ) ( by exact le_trans ( mul_le_mul_of_nonneg_left hθ3 ( by positivity ) ) ( by rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ) ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith [ Real.pi_pos, show 0 ≤ θ1 by exact le_trans ( by positivity ) hθ1 ] ) ( by linarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_le_self Real.pi_pos.le ( by linarith : ( n : ℝ ) + 2 ≥ 1 ) ] ) );
        · exact mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, show 0 ≤ θ1 by exact le_trans ( by positivity ) hθ1 ], by linarith [ Real.pi_pos, show θ2 ≤ Real.pi / 2 by exact hθ3.trans ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] ⟩ );
        · exact Real.sin_nonneg_of_nonneg_of_le_pi ( by exact mul_nonneg ( by positivity ) ( by linarith [ Real.pi_pos, show 0 ≤ θ1 by exact le_trans ( by positivity ) hθ1 ] ) ) ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] );
        · exact Real.sin_pos_of_pos_of_lt_pi ( lt_of_lt_of_le ( by positivity ) hθ1 ) ( lt_of_lt_of_le hθ2 ( le_trans hθ3 ( div_le_self Real.pi_pos.le ( by linarith ) ) ) );
      -- By definition of $rho$, we know that $rho(n-1) = 4 * cos^2(pi/(n+2))$ and $rho(n) = 4 * cos^2(pi/(n+3))$.
      have h_rho_bounds : ∀ x ∈ Set.Icc (rho (n - 1)) (rho n), ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), x = 4 * Real.cos θ ^ 2 := by
        intro x hx
        obtain ⟨θ, hθ⟩ : ∃ θ ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)), 4 * Real.cos θ ^ 2 = x := by
          apply_rules [ intermediate_value_Icc' ];
          · bound;
          · fun_prop;
          · convert hx using 1;
            unfold rho; cases n <;> norm_num at *;
            norm_cast;
        aesop;
      intros x hx y hy hxy;
      obtain ⟨ θx, hθx₁, hθx₂ ⟩ := h_rho_bounds x hx; obtain ⟨ θy, hθy₁, hθy₂ ⟩ := h_rho_bounds y hy; simp_all +decide only [Set.mem_Icc] ;
      contrapose! hxy;
      exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ⟩ ) ( Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ( by linarith [ show θx ≤ θy from le_of_not_gt fun h => by linarith [ h_p_poly_inc _ _ hθy₁.1 h hθx₁.2 ] ] ) ) _ ) zero_le_four

/-
Lemma 12: If R is in [rho_{n-1}, rho_n], then p_{n+1}(R) <= p_n(R) and p_{n+2}(R) <= 0.
-/
lemma p_poly_step_limit (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : R ∈ Set.Icc (rho (n - 1)) (rho n)) :
    p_poly R (n + 1) ≤ p_poly R n ∧ p_poly R (n + 2) ≤ 0 := by
      have h_sin_neg : Real.sin ((n + 3 : ℝ) * (Real.arccos (Real.sqrt (R / 4)))) ≤ 0 := by
        -- Since $\theta \in [\frac{\pi}{n+3}, \frac{\pi}{n+2}]$, we have $(n+3)\theta \in [\pi, \pi + \frac{\pi}{n+2})$.
        have h_theta_range : Real.pi ≤ (n + 3) * Real.arccos (Real.sqrt (R / 4)) ∧ (n + 3) * Real.arccos (Real.sqrt (R / 4)) ≤ Real.pi + Real.pi / (n + 2) := by
          have h_theta_range : Real.arccos (Real.sqrt (R / 4)) ∈ Set.Icc (Real.pi / (n + 3)) (Real.pi / (n + 2)) := by
            -- Since $R \in [\rho_{n-1}, \rho_n]$, we have $\cos(\theta) \in [\cos(\pi/(n+2)), \cos(\pi/(n+3))]$.
            have h_cos_range : Real.cos (Real.arccos (Real.sqrt (R / 4))) ∈ Set.Icc (Real.cos (Real.pi / (n + 2))) (Real.cos (Real.pi / (n + 3))) := by
              rw [ Real.cos_arccos ] <;> norm_num [ rho ] at *;
              · field_simp;
                constructor <;> norm_num [ Nat.cast_sub hn ] at *;
                · exact Real.le_sqrt_of_sq_le ( by ring_nf at *; linarith );
                · rw [ Real.sqrt_le_left ] <;> nlinarith [ show 0 ≤ Real.cos ( Real.pi / ( n + 3 ) ) from Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ];
              · linarith [ Real.sqrt_nonneg R ];
              · exact div_le_one_of_le₀ ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ Real.cos_sq_le_one ( Real.pi / ( n + 3 ) ) ] ⟩ ) zero_le_two;
            -- Since $\cos$ is decreasing on $[0, \pi]$, if $\cos(a) \leq \cos(b)$, then $a \geq b$.
            have h_arccos_bounds : Real.arccos (Real.sqrt (R / 4)) ≥ Real.pi / (n + 3) ∧ Real.arccos (Real.sqrt (R / 4)) ≤ Real.pi / (n + 2) := by
              have h_cos_decreasing : ∀ a b : ℝ, 0 ≤ a → a ≤ Real.pi → 0 ≤ b → b ≤ Real.pi → Real.cos a ≤ Real.cos b → a ≥ b := by
                exact fun a b ha hb ha' hb' hab => le_of_not_gt fun h => hab.not_lt <| Real.cos_lt_cos_of_nonneg_of_le_pi ( by linarith ) ( by linarith ) h
              apply And.intro;
              · apply h_cos_decreasing;
                · exact Real.arccos_nonneg _;
                · linarith [ Real.arccos_le_pi ( Real.sqrt ( R / 4 ) ) ];
                · positivity;
                · exact div_le_self Real.pi_pos.le ( by linarith );
                · exact h_cos_range.2;
              · contrapose! h_cos_decreasing;
                use Real.pi / (n + 2), Real.arccos (Real.sqrt (R / 4));
                exact ⟨ by positivity, div_le_self Real.pi_pos.le ( by linarith ), Real.arccos_nonneg _, Real.arccos_le_pi _, h_cos_range.1, h_cos_decreasing ⟩;
            exact h_arccos_bounds;
          constructor <;> nlinarith [ h_theta_range.1, h_theta_range.2, Real.pi_pos, mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 3 ≠ 0 ), mul_div_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ];
        rw [ ← Real.cos_sub_pi_div_two ] ; exact Real.cos_nonpos_of_pi_div_two_le_of_le ( by linarith ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ] ) ;
      have h_p_poly_diff : p_poly R (n + 1) - p_poly R n = (2 * Real.cos (Real.arccos (Real.sqrt (R / 4)))) ^ n * (Real.sin ((n + 3 : ℝ) * Real.arccos (Real.sqrt (R / 4)))) / Real.sin (Real.arccos (Real.sqrt (R / 4))) := by
        have h_p_poly_diff : p_poly R (n + 1) - p_poly R n = (2 * Real.cos (Real.arccos (Real.sqrt (R / 4)))) ^ n * (Real.sin ((n + 3 : ℝ) * Real.arccos (Real.sqrt (R / 4)))) / Real.sin (Real.arccos (Real.sqrt (R / 4))) := by
          have hθ : R = 4 * Real.cos (Real.arccos (Real.sqrt (R / 4))) ^ 2 := by
            rw [ Real.cos_arccos ];
            · rw [ Real.sq_sqrt ] <;> linarith [ hR.1, show 0 ≤ rho ( n - 1 ) from mul_nonneg zero_le_four ( sq_nonneg _ ) ];
            · linarith [ Real.sqrt_nonneg ( R / 4 ) ];
            · exact Real.sqrt_le_iff.mpr ⟨ by norm_num, by linarith [ hR.2, show rho n ≤ 4 by exact mul_le_of_le_one_right zero_le_four <| Real.cos_sq_le_one _ ] ⟩
          have hθ_pos : 0 < Real.arccos (Real.sqrt (R / 4)) ∧ Real.arccos (Real.sqrt (R / 4)) < Real.pi := by
            refine' ⟨ Real.arccos_pos.mpr _, lt_of_le_of_ne ( Real.arccos_le_pi _ ) _ ⟩ <;> norm_num;
            · rw [ div_lt_iff₀, Real.sqrt_lt' ] <;> norm_num;
              exact hR.2.trans_lt ( show rho n < 4 by rw [ show rho n = 4 * Real.cos ( Real.pi / ( n + 3 ) ) ^ 2 by rfl ] ; nlinarith only [ Real.cos_sq' ( Real.pi / ( n + 3 ) ), Real.sin_pos_of_pos_of_lt_pi ( show 0 < Real.pi / ( n + 3 ) by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith only [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ) ] );
            · linarith [ Real.sqrt_nonneg R ];
          convert p_poly_diff_trig ( Real.arccos ( Real.sqrt ( R / 4 ) ) ) hθ_pos.1 hθ_pos.2 n using 1;
          · rw [ ← hθ ];
          · ring;
        exact h_p_poly_diff;
      -- Since $R \geq 0$, we have $(2 * \cos(\theta))^n \geq 0$ and $\sin(\theta) > 0$, thus $p_{n+1}(R) - p_n(R) \leq 0$.
      have h_p_poly_diff_nonpos : p_poly R (n + 1) - p_poly R n ≤ 0 := by
        rw [h_p_poly_diff];
        refine' div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos ( pow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ _, _ ⟩ ) ) _ ) h_sin_neg ) ( Real.sin_nonneg_of_mem_Icc ⟨ _, _ ⟩ );
        · linarith [ Real.pi_pos, Real.arccos_nonneg ( Real.sqrt ( R / 4 ) ) ];
        · rw [ Real.arccos_le_pi_div_two ] ; norm_num;
          positivity;
        · exact Real.arccos_nonneg _;
        · linarith [ Real.pi_pos, Real.arccos_le_pi ( Real.sqrt ( R / 4 ) ) ];
      have h_p_poly_succ : p_poly R (n + 2) = R * (p_poly R (n + 1) - p_poly R n) := by
        exact?;
      exact ⟨ by linarith, by nlinarith [ hR.1, show 0 ≤ R from le_trans ( by exact mul_nonneg zero_le_four <| sq_nonneg _ ) hR.1 ] ⟩

/-
Lemma 13: B_n is strictly increasing.
-/
lemma B_val_strict_mono : StrictMono B_val := by
  refine' strictMono_nat_of_lt_succ _;
  intro n;
  -- By definition of $B_val$, we have $B_val (n + 1) = (2 * Real.cos (Real.pi / (n + 4)))^(n + 2)$.
  simp [B_val];
  -- Since $2 \cos(\pi/(n+4)) > 1$, we can divide both sides of the inequality by $(2 \cos(\pi/(n+4)))^{n+1}$.
  have h_div : (2 * Real.cos (Real.pi / (n + 3))) ^ (n + 1) < (2 * Real.cos (Real.pi / (n + 4))) ^ (n + 1) * (2 * Real.cos (Real.pi / (n + 4))) := by
    -- Since $2 \cos(\pi/(n+4)) > 1$, we can divide both sides of the inequality by $(2 \cos(\pi/(n+4)))^{n+1}$ to get $1 < 2 \cos(\pi/(n+4))$.
    have h_div : 1 < 2 * Real.cos (Real.pi / (n + 4)) := by
      nlinarith [ show Real.cos ( Real.pi / ( n + 4 ) ) > 1 / 2 by rw [ ← Real.cos_pi_div_three ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 4 ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, div_mul_cancel₀ Real.pi ( by positivity : ( n : ℝ ) + 4 ≠ 0 ) ] ) ];
    exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by nlinarith [ show 0 ≤ Real.cos ( Real.pi / ( n + 3 ) ) from Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ⟩ ] ) ( show 2 * Real.cos ( Real.pi / ( n + 3 ) ) ≤ 2 * Real.cos ( Real.pi / ( n + 4 ) ) from mul_le_mul_of_nonneg_left ( Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ) <| by gcongr ; linarith ) zero_le_two ) _ ) ( lt_mul_of_one_lt_right ( by exact pow_pos ( by linarith ) _ ) h_div );
  exact h_div.trans_eq ( by ring )

/-
Lemma 14: B_n tends to infinity as n tends to infinity.
-/
lemma B_val_tendsto_atTop : Tendsto B_val atTop atTop := by
  -- We'll use that $B_n$ tends to infinity as $n$ tends to infinity. We can show this by noting that $B_n = (2 \cos(\pi / (n + 3)))^{n + 1}$ and $\cos(\pi / (n + 3))$ tends to $1$ as $n$ tends to infinity.
  have h_cos : Filter.Tendsto (fun n : ℕ => 2 * Real.cos (Real.pi / (n + 3))) Filter.atTop (nhds 2) := by
    exact le_trans ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ( by norm_num );
  -- Since $2 \cos(\pi / (n + 3))$ tends to $2$ as $n$ tends to infinity, we can use the fact that $2^{n+1}$ grows exponentially.
  have h_exp : Filter.Tendsto (fun n : ℕ => (2 * Real.cos (Real.pi / (n + 3))) ^ (n + 1)) Filter.atTop Filter.atTop := by
    -- Since $2 \cos(\pi / (n + 3))$ tends to $2$ as $n$ tends to infinity, we can use the fact that $(2 \cos(\pi / (n + 3)))^{n + 1}$ grows exponentially.
    have h_exp : Filter.Tendsto (fun n : ℕ => Real.exp ((n + 1) * Real.log (2 * Real.cos (Real.pi / (n + 3))))) Filter.atTop Filter.atTop := by
      -- Since $\log(2 \cos \frac{\pi}{n+3}) \to \log 2$ as $n \to \infty$, we can use the fact that $(n + 1) \log(2 \cos \frac{\pi}{n+3}) \to \infty$.
      have h_log : Filter.Tendsto (fun n : ℕ => (n + 1) * Real.log (2 * Real.cos (Real.pi / (n + 3)))) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_mul_pos;
        exacts [ show 0 < Real.log 2 by positivity, Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop, by simpa using Filter.Tendsto.log h_cos two_ne_zero ];
      aesop;
    refine h_exp.congr' ( by filter_upwards [ h_cos.eventually ( lt_mem_nhds one_lt_two ) ] with n hn using by rw [ mul_comm, Real.exp_mul, Real.exp_log ( by linarith ) ] ; norm_cast );
  convert h_exp using 1

/-
Definition of n(B) as the smallest n such that B <= B_n.
-/
noncomputable def n_of_B (B : ℝ) (hB : 1 < B) : ℕ :=
  Nat.find (show ∃ n, B ≤ B_val n by
              exact ( B_val_tendsto_atTop.eventually ( Filter.eventually_ge_atTop B ) ) |> fun h => h.exists)

/-
Properties of n(B): n(B) >= 1, B_{n(B)-1} < B <= B_{n(B)}.
-/
lemma n_of_B_props (B : ℝ) (hB : 1 < B) :
    1 ≤ n_of_B B hB ∧ B_val (n_of_B B hB - 1) < B ∧ B ≤ B_val (n_of_B B hB) := by
      -- Since $n_of_B B hB$ is the smallest natural number such that $B \leq B_val n$, we have $B \leq B_val (n_of_B B hB)$ by definition.
      have hB_le_B_val : B ≤ B_val (n_of_B B hB) := by
        exact Nat.find_spec ( _ : ∃ n, B ≤ B_val n );
      refine' ⟨ _, _, hB_le_B_val ⟩;
      · by_contra h_contra;
        interval_cases _ : n_of_B B hB ; norm_num at *;
        exact hB.not_le ( hB_le_B_val.trans ( by norm_num [ B_val ] ) );
      · by_cases h : n_of_B B hB = 0;
        · unfold B_val at * ; aesop;
        · exact lt_of_not_ge fun h' => Nat.find_min ( show ∃ n, B ≤ B_val n from ⟨ _, hB_le_B_val ⟩ ) ( Nat.sub_lt ( Nat.pos_of_ne_zero h ) zero_lt_one ) h'

/-
n(B) tends to infinity as B tends to infinity.
-/
noncomputable def n_of_B_total (B : ℝ) : ℕ :=
  if h : 1 < B then n_of_B B h else 1

lemma n_of_B_total_eq (B : ℝ) (h : 1 < B) : n_of_B_total B = n_of_B B h := by
  simp [n_of_B_total, h]

lemma n_of_B_total_tendsto : Filter.Tendsto n_of_B_total Filter.atTop Filter.atTop := by
  refine' Filter.tendsto_atTop_atTop.mpr fun n => _;
  -- By definition of $n_of_B_total$, we know that $n_of_B_total a$ is the smallest $n$ such that $a \leq B_val n$.
  unfold n_of_B_total;
  use B_val n + 1;
  field_simp;
  intro a ha; split_ifs <;> simp_all +decide [ n_of_B ];
  · exact fun m mn => lt_of_le_of_lt ( B_val_strict_mono.monotone mn.le ) ( by linarith );
  · linarith [ show 0 < B_val n from pow_pos ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by rw [ lt_div_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ], by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos ] ⟩ ) ) _ ]

/-
Theorem 15: lim_{B -> infinity} B^{1/n(B)} = 2.
-/
theorem thm_limit_growth_base : Filter.Tendsto (fun B => B ^ (1 / (n_of_B_total B : ℝ))) Filter.atTop (nhds 2) := by
  -- The limit of $B^{1/n(B)}$ is $2$ as $B \to \infty$.
  have h_lim : Filter.Tendsto (fun B : ℝ => B ^ (1 / (n_of_B_total B : ℝ)))
    Filter.atTop (nhds 2) := by
    have h_squeeze : ∀ᶠ B in Filter.atTop, (B_val (n_of_B_total B - 1)) ^ (1 / (n_of_B_total B : ℝ)) < B ^ (1 / (n_of_B_total B : ℝ)) ∧ B ^ (1 / (n_of_B_total B : ℝ)) ≤ (B_val (n_of_B_total B)) ^ (1 / (n_of_B_total B : ℝ)) := by
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with B hB;
      constructor;
      · have := n_of_B_props B hB;
        rw [ n_of_B_total_eq B hB ] ; exact Real.rpow_lt_rpow ( by exact le_of_lt ( show 0 < B_val ( n_of_B B hB - 1 ) from by exact pow_pos ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by rw [ lt_div_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n_of_B B hB : ℝ ) ≥ 1 by exact_mod_cast this.1 ], by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n_of_B B hB : ℝ ) ≥ 1 by exact_mod_cast this.1 ] ⟩ ) ) _ ) ) this.2.1 ( by norm_num ; linarith );
      · gcongr;
        convert n_of_B_props B hB |>.2.2 using 1;
        unfold n_of_B_total; aesop;
    have h_squeeze : Filter.Tendsto (fun B : ℝ => (B_val (n_of_B_total B - 1)) ^ (1 / (n_of_B_total B : ℝ))) Filter.atTop (nhds 2) ∧ Filter.Tendsto (fun B : ℝ => (B_val (n_of_B_total B)) ^ (1 / (n_of_B_total B : ℝ))) Filter.atTop (nhds 2) := by
      have h_squeeze : Filter.Tendsto (fun n : ℕ => (B_val (n - 1)) ^ (1 / (n : ℝ))) Filter.atTop (nhds 2) ∧ Filter.Tendsto (fun n : ℕ => (B_val n) ^ (1 / (n : ℝ))) Filter.atTop (nhds 2) := by
        have h_squeeze : Filter.Tendsto (fun n : ℕ => (2 * Real.cos (Real.pi / (n + 2))) ^ ((n : ℝ) / (n : ℝ))) Filter.atTop (nhds 2) ∧ Filter.Tendsto (fun n : ℕ => (2 * Real.cos (Real.pi / (n + 3))) ^ ((n + 1 : ℝ) / (n : ℝ))) Filter.atTop (nhds 2) := by
          constructor;
          · exact le_trans ( Filter.Tendsto.rpow ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) <| by norm_num ) <| by norm_num;
          · -- We'll use the fact that $(2 \cos(\pi/(n+3)))^{(n+1)/n}$ converges to $2$ as $n \to \infty$.
            have h_cos : Filter.Tendsto (fun n : ℕ => (2 * Real.cos (Real.pi / (n + 3))) ^ (1 + 1 / (n : ℝ))) Filter.atTop (nhds 2) := by
              convert Filter.Tendsto.rpow ( tendsto_const_nhds.mul ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ( tendsto_const_nhds.add <| tendsto_one_div_atTop_nhds_zero_nat ) _ using 2 <;> norm_num;
            refine h_cos.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ add_div, div_self ( by positivity ) ] );
        refine' ⟨ h_squeeze.1.congr' _, h_squeeze.2.congr' _ ⟩;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; rcases n with ( _ | n ) <;> norm_num [ B_val ] at *;
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ] <;> nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos ] ⟩ ) ), Nat.cast_add_one, mul_inv_cancel₀ ( by linarith ), Real.rpow_one ] ; ring;
          rw [ show ( n : ℝ ) * ( 1 + n : ℝ ) ⁻¹ + ( 1 + n : ℝ ) ⁻¹ = 1 by linarith [ mul_inv_cancel₀ ( by linarith : ( 1 + n : ℝ ) ≠ 0 ) ] ] ; norm_num;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
          unfold B_val;
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ) ] ; push_cast ; ring;
      exact ⟨ h_squeeze.1.comp <| Filter.tendsto_atTop_atTop.2 fun n => by rcases Filter.eventually_atTop.1 ( n_of_B_total_tendsto.eventually_ge_atTop n ) with ⟨ m, hm ⟩ ; exact ⟨ m, fun x hx => hm x hx ⟩, h_squeeze.2.comp <| Filter.tendsto_atTop_atTop.2 fun n => by rcases Filter.eventually_atTop.1 ( n_of_B_total_tendsto.eventually_ge_atTop n ) with ⟨ m, hm ⟩ ; exact ⟨ m, fun x hx => hm x hx ⟩ ⟩;
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_squeeze.1 h_squeeze.2 ( by filter_upwards [ ‹∀ᶠ B in Filter.atTop, B_val ( n_of_B_total B - 1 ) ^ ( 1 / ( n_of_B_total B : ℝ ) ) < B ^ ( 1 / ( n_of_B_total B : ℝ ) ) ∧ B ^ ( 1 / ( n_of_B_total B : ℝ ) ) ≤ B_val ( n_of_B_total B ) ^ ( 1 / ( n_of_B_total B : ℝ ) ) › ] with x hx using hx.1.le ) ( by filter_upwards [ ‹∀ᶠ B in Filter.atTop, B_val ( n_of_B_total B - 1 ) ^ ( 1 / ( n_of_B_total B : ℝ ) ) < B ^ ( 1 / ( n_of_B_total B : ℝ ) ) ∧ B ^ ( 1 / ( n_of_B_total B : ℝ ) ) ≤ B_val ( n_of_B_total B ) ^ ( 1 / ( n_of_B_total B : ℝ ) ) › ] with x hx using hx.2 );
  convert h_lim using 1

/-
p_n(R) is continuous in R.
-/
lemma p_poly_continuous (n : ℕ) : Continuous (fun R => p_poly R n) := by
  -- By definition of $p_poly$, we know that it is a polynomial in $R$.
  have h_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ R : ℝ, p_poly R n = p.eval R := by
    intro n
    induction' n using Nat.strong_induction_on with n ih;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ p_poly ];
    · exact ⟨ 1, fun R => by norm_num ⟩;
    · exact ⟨ Polynomial.X, fun R => by norm_num ⟩;
    · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith ) ; obtain ⟨ q, hq ⟩ := ih n ( by linarith ) ; exact ⟨ Polynomial.X * ( p - q ), fun R => by simp +decide [ hp, hq ] ⟩;
  obtain ⟨ p, hp ⟩ := h_poly n; simpa only [ hp ] using p.continuous;

/-
Theorem 13 (part 1): There exists a unique R in (rho_{n-1}, rho_n] such that p_n(R) = B.
-/
theorem exists_unique_R_of_B (B : ℝ) (hB : 1 < B) :
    let n := n_of_B_total B
    ∃! R, R ∈ Set.Ioc (rho (n - 1)) (rho n) ∧ p_poly R n = B := by
      refine' ⟨ _, _, _ ⟩;
      exact ( Classical.choose ( show ∃ R ∈ Set.Ioc ( rho ( n_of_B_total B - 1 ) ) ( rho ( n_of_B_total B ) ), p_poly R ( n_of_B_total B ) = B from by
                                  apply_rules [ intermediate_value_Ioc ];
                                  · unfold rho; gcongr <;> norm_num;
                                    · exact Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ] <;> nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ ] <;> nlinarith [ Real.pi_pos ] ⟩;
                                    · refine' Real.cos_le_cos_of_nonneg_of_le_pi _ _ _ <;> try positivity;
                                      · exact div_le_self Real.pi_pos.le ( by linarith );
                                      · gcongr ; norm_num;
                                  · exact Continuous.continuousOn ( p_poly_continuous _ );
                                  · simp +zetaDelta at *;
                                    have h_bounds : p_poly (rho (n_of_B_total B - 1)) (n_of_B_total B) < B ∧ B ≤ p_poly (rho (n_of_B_total B)) (n_of_B_total B) := by
                                      have h1 := n_of_B_props B hB
                                      have h2 := p_poly_endpoints (n_of_B_total B) (by
                                      unfold n_of_B_total; aesop;)
                                      unfold n_of_B_total at * ; aesop;
                                    exact h_bounds ) )
      all_goals generalize_proofs at *;
      · exact Classical.choose_spec ‹∃ x ∈ Set.Ioc ( rho ( n_of_B_total B - 1 ) ) ( rho ( n_of_B_total B ) ), p_poly x ( n_of_B_total B ) = B›;
      · intro y hy
        all_goals generalize_proofs at *;
        have := Classical.choose_spec ‹∃ x ∈ Set.Ioc ( rho ( n_of_B_total B - 1 ) ) ( rho ( n_of_B_total B ) ), p_poly x ( n_of_B_total B ) = B›;
        have h_unique : StrictMonoOn (fun R => p_poly R (n_of_B_total B)) (Set.Icc (rho (n_of_B_total B - 1)) (rho (n_of_B_total B))) := by
          apply p_poly_strict_mono;
          grind;
        exact StrictMonoOn.injOn h_unique ⟨ hy.1.1.le, hy.1.2 ⟩ ⟨ this.1.1.le, this.1.2 ⟩ ( by linarith )

/-
rho_n tends to 4 as n tends to infinity.
-/
lemma rho_tendsto_4 : Filter.Tendsto rho Filter.atTop (nhds 4) := by
  exact le_trans ( tendsto_const_nhds.mul ( Filter.Tendsto.pow ( Real.continuous_cos.continuousAt.tendsto.comp <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) _ ) ) ( by norm_num )

/-
Definition of x(B) and its property: x(B) is in (rho_{n-1}, rho_n] and p_n(x(B)) = B.
-/
noncomputable def x_guess (B : ℝ) : ℝ :=
  if h : 1 < B then
    Classical.choose (exists_unique_R_of_B B h)
  else
    1

lemma x_guess_spec (B : ℝ) (h : 1 < B) :
    x_guess B ∈ Set.Ioc (rho (n_of_B_total B - 1)) (rho (n_of_B_total B)) ∧
    p_poly (x_guess B) (n_of_B_total B) = B := by
      have := @exists_unique_R_of_B B h;
      obtain ⟨ R, hR₁, hR₂ ⟩ := this;
      unfold x_guess;
      have := Classical.choose_spec ( show ∃ R, R ∈ Set.Ioc ( rho ( n_of_B_total B - 1 ) ) ( rho ( n_of_B_total B ) ) ∧ p_poly R ( n_of_B_total B ) = B from ⟨ R, ⟨ hR₁.1.1, hR₁.1.2 ⟩, hR₁.2 ⟩ );
      grind

/-
Theorem 16: lim_{B -> infinity} x(B) = 4.
-/
theorem thm_limit_first_guess : Filter.Tendsto x_guess Filter.atTop (nhds 4) := by
  -- By definition of $x_guess$, we know that for any $B > 1$, $x_guess B$ is in the interval $(\rho_{n-1}, \rho_n]$ and $p_n(x_guess B) = B$.
  have h_x_guess_bounds : ∀ B > 1, x_guess B ∈ Set.Ioc (rho (n_of_B_total B - 1)) (rho (n_of_B_total B)) := by
    exact fun B hB => x_guess_spec B hB |>.1;
  -- Since $\rho_n \to 4$ as $n \to \infty$, both $\rho_{n-1}$ and $\rho_n$ tend to $4$.
  have h_rho_tendsto_4 : Filter.Tendsto (fun n => rho n) Filter.atTop (nhds 4) := by
    exact?;
  -- Since $n_of_B_total B \to \infty$ as $B \to \infty$, both $\rho_{n_of_B_total B - 1}$ and $\rho_{n_of_B_total B}$ tend to $4$.
  have h_rho_n_of_B_tendsto_4 : Filter.Tendsto (fun B => rho (n_of_B_total B - 1)) Filter.atTop (nhds 4) ∧ Filter.Tendsto (fun B => rho (n_of_B_total B)) Filter.atTop (nhds 4) := by
    exact ⟨ h_rho_tendsto_4.comp <| Filter.tendsto_atTop_atTop.mpr fun n => by rcases Filter.eventually_atTop.mp ( n_of_B_total_tendsto.eventually_ge_atTop ( n + 1 ) ) with ⟨ B, hB ⟩ ; exact ⟨ B, fun b hb => Nat.le_pred_of_lt <| hB b hb ⟩, h_rho_tendsto_4.comp <| n_of_B_total_tendsto ⟩;
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_rho_n_of_B_tendsto_4.1 h_rho_n_of_B_tendsto_4.2 ( Filter.eventually_atTop.mpr ⟨ 2, fun B hB => h_x_guess_bounds B ( by linarith ) |>.1.le ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 2, fun B hB => h_x_guess_bounds B ( by linarith ) |>.2 ⟩ )

/-
Lemma: If x_k < y <= x_{k+1}, then N(y) = k+1.
-/
lemma BStrategy.N_eq_of_jump {B : ℝ} (s : BStrategy B) (k : ℕ) (hk : k < s.n)
    (y : ℝ) (hy_gt : s.x_safe k < y) (hy_le : y ≤ s.x_safe (k + 1)) :
    s.N y = k + 1 := by
      -- By definition of $N$, we need to show that $k + 1$ is the smallest index $m$ such that $x_m \geq y$.
      have hN_def : ∀ m, 1 ≤ m → m ≤ s.n → y ≤ s.x_safe m → k + 1 ≤ m := by
        intro m hm₁ hm₂ hm₃;
        by_cases h_cases : m ≤ k;
        · -- Since $m \leq k$, we have $x_m \leq x_k$.
          have h_xm_le_xk : s.x_safe m ≤ s.x_safe k := by
            have h_xm_le_xk : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ s.n → s.x_safe i ≤ s.x_safe j := by
              intros i j hi hj hjn
              have h_monotone : s.x_ext i ≤ s.x_ext j := by
                exact s.x_ext_mono hj;
              unfold BStrategy.x_ext at h_monotone; aesop;
            exact h_xm_le_xk m k hm₁ h_cases hk.le;
          linarith;
        · linarith;
      refine' le_antisymm _ _;
      · refine' csInf_le _ _ <;> norm_num;
        exact ⟨ Nat.succ_le_of_lt hk, hy_le ⟩;
      · refine' le_csInf _ _;
        · exact ⟨ k + 1, by linarith, by linarith, hy_le ⟩;
        · aesop

/-
Lemma: c_k(R) >= 0 for k <= n, given p_k is monotone.
-/
def c_poly (R : ℝ) : ℕ → ℝ
| 0 => 0
| 1 => 1
| (k + 2) => R * (c_poly R (k + 1) - c_poly R k)

lemma c_poly_nonneg (n : ℕ) (R : ℝ) (hR : 2 ≤ R) (h_mono : ∀ k < n, p_poly R k ≤ p_poly R (k + 1)) :
    ∀ k ≤ n, 0 ≤ c_poly R k := by
      intro k hk;
      -- By definition of $c_poly$, we know that $c_poly R k = p_poly R (k - 1)$ for $k \geq 1$.
      have h_c_poly_def : ∀ k ≥ 1, c_poly R k = p_poly R (k - 1) := by
        intro k hk
        induction' k using Nat.strong_induction_on with k ih;
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ c_poly ];
        · rfl;
        · rcases k with ( _ | k ) <;> simp_all +decide [ c_poly ];
          · exact show R * 1 = R by ring;
          · exact?;
      rcases k with ( _ | k ) <;> simp_all +decide;
      · exact le_rfl;
      · induction' k using Nat.strong_induction_on with k ih;
        rcases k with ( _ | _ | k ) <;> norm_num [ h_c_poly_def ] at *;
        · exact zero_le_one;
        · exact le_trans ( by norm_num [ show p_poly R 0 = 1 from rfl ] ) ( h_mono 0 ( by linarith ) );
        · exact le_trans ( ih _ ( by linarith ) ( by linarith ) ) ( h_mono _ ( by linarith ) )

/-
Definition of c_k, d_k and proof that c_k * R = p_k.
-/
def cd_seq (R : ℝ) : ℕ → ℝ × ℝ
| 0 => (0, 0)
| 1 => (1, 0)
| k + 1 =>
  let (c, d) := cd_seq R k
  ((R - 1) * c - d, c + d)

def c_val (R : ℝ) (k : ℕ) := (cd_seq R k).1
def d_val (R : ℝ) (k : ℕ) := (cd_seq R k).2

lemma c_val_eq_p_poly_div_R (R : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    c_val R k * R = p_poly R k := by
      -- By definition of $c_val$ and $d_val$, we have $c_val R (k + 1) = (R - 1) * c_val R k - d_val R k$ and $d_val R (k + 1) = c_val R k + d_val R k$.
      have h_recurrence : ∀ k, c_val R (k + 2) = (R - 1) * c_val R (k + 1) - d_val R (k + 1) ∧ d_val R (k + 2) = c_val R (k + 1) + d_val R (k + 1) := by
        aesop;
      -- We prove the statement by induction on $k$.
      induction' k using Nat.strong_induction_on with k ih;
      rcases k with ( _ | _ | k ) <;> simp_all +decide;
      · exact show ( 1 : ℝ ) * R = R by ring;
      · have := ih ( k + 1 ) ( by linarith ) ( by linarith ) ; ( have := ih k ( by linarith ) ; ( rcases k with ( _ | k ) <;> simp_all +decide [ sub_mul, mul_assoc ] ; ) );
        · unfold p_poly d_val; ring;
          unfold p_poly; norm_num; ring;
          rw [ show cd_seq R 1 = ( 1, 0 ) from rfl ] ; ring;
        · have := ih ( k + 1 ) ( by linarith ) ( by linarith ) ; ( have := ih ( k + 2 ) ( by linarith ) ( by linarith ) ; ( norm_num [ h_recurrence, p_poly ] at * ; nlinarith; ) )

/-
Lemma: sum_{i=0}^{k+1} c_i = R c_k + 1.
-/
lemma c_poly_sum (R : ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), c_poly R i = R * c_poly R k + 1 := by
      induction k <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
      · norm_num [ add_comm, c_poly ];
      · rw [ show c_poly R ( _ + 2 ) = R * ( c_poly R ( _ + 1 ) - c_poly R _ ) by exact rfl ] ; ring

/-
Lemma: If s is strict, then S_{k+1} <= W * x_k.
-/
lemma BStrategy.S_succ_le_W_mul_x_of_strict {B : ℝ} (s : BStrategy B) (h_strict : s.Strict) (k : ℕ) (hk : k < s.n) :
    s.S (k + 1) ≤ s.W * s.x_safe k := by
      have := BStrategy.S_succ_div_x_le_W_of_strict s h_strict k hk;
      rw [ div_le_iff₀ ] at this;
      · field_simp;
        unfold BStrategy.x_ext at this;
        split_ifs at this <;> simp_all +decide [ BStrategy.x_safe ];
        -- Since $B \geq 1$, we have $s.W \leq s.W * B$.
        have hB_ge_1 : 1 ≤ B := by
          exact s.xn_eq_B ▸ s.one_le_x1.trans ( s.mono ( Nat.zero_le _ ) );
        refine' le_trans this ( le_mul_of_one_le_right _ hB_ge_1 );
        refine' le_trans _ this;
        unfold BStrategy.S; norm_num;
        split_ifs ; linarith [ s.one_le_x1 ];
      · unfold BStrategy.x_ext;
        field_simp;
        split_ifs <;> norm_num [ BStrategy.x_safe ];
        rw [ if_pos ⟨ Nat.pos_of_ne_zero ‹_›, hk.le ⟩ ];
        exact lt_of_lt_of_le ( show 0 < s.x ⟨ 0, s.n_pos ⟩ from by linarith [ s.one_le_x1 ] ) ( s.mono ( Nat.zero_le _ ) )

/-
Lemma: If x_k < x_{k+1}, then S_{k+1} <= W * x_k.
-/
lemma BStrategy.S_le_W_mul_x_of_jump {B : ℝ} (s : BStrategy B) (k : ℕ) (hk : k < s.n)
    (hjump : s.x_safe k < s.x_safe (k + 1)) :
    s.S (k + 1) ≤ s.W * s.x_safe k := by
      have := @BStrategy.S_le_R_x_of_jump B s;
      -- Apply the hypothesis `this` with R = s.W.
      specialize this (le_refl s.W) k hk;
      simp_all +decide [ BStrategy.x_ext ];
      rcases k with ( _ | k ) <;> simp_all +decide [ BStrategy.x_safe ];
      split_ifs at hjump <;> simp_all +decide [ BStrategy.x_ext ];
      exact absurd hjump ( by linarith! [ s.xn_eq_B, show s.x ⟨ s.n - 1, Nat.sub_lt hk zero_lt_one ⟩ ≥ s.x ⟨ 0, hk ⟩ from s.mono ( Nat.zero_le _ ) ] )
