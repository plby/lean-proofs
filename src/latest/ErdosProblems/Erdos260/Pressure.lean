import ErdosProblems.Erdos260.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sparse-block lower bound and bounded-excess contribution

This module corresponds to Section 4 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos260

/-- Data fixed after the denominator is chosen and before the rational
numerator or support set is allowed to vary.  In particular, the positive
pressure parameter is shared by every compatible scale family. -/
structure FixedScaleContext where
  Q : ℕ
  Q_pos : 0 < Q
  structural : StructuralParams
  entropy : EntropyParams
  entropy_structural : entropy.structural = structural
  epsilon : ℝ
  epsilon_pos : 0 < epsilon

/-- A coherent family indexed by the dyadic exponent.  The rational support,
its increasing enumeration, the structural/entropy parameters, and the
pressure offset are fixed before `L` varies. -/
structure ScaleFamily where
  rational : RationalSupport
  enumeration : SupportEnumeration rational.S
  structural : StructuralParams
  entropy : EntropyParams
  entropy_structural : entropy.structural = structural
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  system : ℕ → WindowSystem
  level_eq : ∀ L, (system L).L = L
  rational_eq : ∀ L, (system L).rational = rational
  enumeration_eq : ∀ L n, (system L).enumeration.a n = enumeration.a n
  structural_eq : ∀ L, (system L).structural = structural
  entropy_eq : ∀ L, (system L).entropy = entropy
  epsilon_eq : ∀ L, (system L).epsilon = epsilon
  offset_eq : ∀ L,
    (system L).s = Nat.floor (entropy.kappa * (L : ℝ))

/-- Length of the paper's threshold interval. -/
def thresholdLength (W : WindowSystem) : ℝ :=
  W.structural.cI * W.L

/-- Integrated window excess as the certified finite real value of the
counting × Lebesgue mass. -/
def integratedExcess (W : WindowSystem) : ℝ :=
  totalMassReal W

@[simp] theorem integratedExcess_eq_totalMassReal (W : WindowSystem) :
    integratedExcess W = totalMassReal W := rfl

@[simp] theorem ofReal_integratedExcess (W : WindowSystem) :
    ENNReal.ofReal (integratedExcess W) = mass W.pairSet W.excess := by
  exact ofReal_totalMassReal W

namespace ScaleFamily

/-- A scale family is compatible with a denominator-level context when all
data selected before the rational numerator/support agree with that context. -/
def MatchesContext (F : ScaleFamily) (context : FixedScaleContext) : Prop :=
  F.rational.eta.den = context.Q ∧
    F.structural = context.structural ∧
    F.entropy = context.entropy ∧
    F.epsilon = context.epsilon

end ScaleFamily

/-- The mass formulation of the same window-threshold quantity. -/
def totalWindowMass (W : WindowSystem) : ℝ≥0∞ :=
  mass W.pairSet W.excess

/-! ## Discrete window-counting infrastructure -/

/-- A positive strictly increasing enumeration of naturals lies strictly
above the identity. -/
theorem supportEnumeration_index_lt {S : Set ℕ}
    (e : SupportEnumeration S) (n : ℕ) : n < e.a n := by
  induction n with
  | zero => exact e.positive 0
  | succ n ih =>
      exact lt_of_le_of_lt (Nat.succ_le_iff.mpr ih)
        (e.strictMono (Nat.lt_succ_self n))

/-- First enumeration index whose support point is strictly above `x`. -/
def firstIndexAbove {S : Set ℕ} (e : SupportEnumeration S) (x : ℕ) : ℕ :=
  Nat.find (p := fun n => x < e.a n)
    ⟨x, supportEnumeration_index_lt e x⟩

theorem firstIndexAbove_spec {S : Set ℕ} (e : SupportEnumeration S) (x : ℕ) :
    x < e.a (firstIndexAbove e x) := by
  exact Nat.find_spec (p := fun n => x < e.a n)
    ⟨x, supportEnumeration_index_lt e x⟩

theorem firstIndexAbove_le {S : Set ℕ} (e : SupportEnumeration S) (x : ℕ) :
    firstIndexAbove e x ≤ x := by
  exact Nat.find_min' (p := fun n => x < e.a n)
    ⟨x, supportEnumeration_index_lt e x⟩
    (supportEnumeration_index_lt e x)

theorem firstIndexAbove_minimal {S : Set ℕ} (e : SupportEnumeration S)
    (x n : ℕ) (hn : n < firstIndexAbove e x) : e.a n ≤ x := by
  by_contra hnot
  have hx : x < e.a n := Nat.lt_of_not_ge hnot
  have hle : firstIndexAbove e x ≤ n :=
    Nat.find_min' (p := fun n => x < e.a n)
      ⟨x, supportEnumeration_index_lt e x⟩ hx
  omega

/-- Consecutive points of an increasing enumeration determine a genuine
support gap. -/
theorem supportGap_isSupportGap {S : Set ℕ} (e : SupportEnumeration S)
    (k : ℕ) : IsSupportGap S (e.a k) (supportGap e k) := by
  have hstep : e.a k < e.a (k + 1) := e.strictMono (Nat.lt_succ_self k)
  refine ⟨by simpa [supportGap] using Nat.sub_pos_of_lt hstep,
    ?_, ?_, ?_⟩
  · exact (Set.ext_iff.mp e.range_eq (e.a k)).mp ⟨k, rfl⟩
  · apply (Set.ext_iff.mp e.range_eq
      (e.a k + supportGap e k)).mp
    refine ⟨k + 1, ?_⟩
    exact (Nat.add_sub_of_le hstep.le).symm
  · intro n hkn hnk hnS
    have hnRange : n ∈ Set.range e.a :=
      (Set.ext_iff.mp e.range_eq n).mpr hnS
    rcases hnRange with ⟨j, rfl⟩
    have hkj : k < j := (e.strictMono.lt_iff_lt).mp hkn
    have hjk : j < k + 1 := by
      apply (e.strictMono.lt_iff_lt).mp
      simpa [supportGap, Nat.add_sub_of_le hstep.le] using hnk
    omega

/-- A finite consecutive sum of support gaps telescopes. -/
theorem sum_supportGap_Ico {S : Set ℕ} (e : SupportEnumeration S)
    (lo hi : ℕ) (hlo : lo ≤ hi) :
    ∑ k ∈ Finset.Ico lo hi, supportGap e k = e.a hi - e.a lo := by
  induction hi with
  | zero =>
      have : lo = 0 := by omega
      subst lo
      simp
  | succ hi ih =>
      by_cases hEq : lo = hi + 1
      · subst lo
        simp
      · have hlohi : lo ≤ hi := by omega
        rw [Finset.sum_Ico_succ_top hlohi, ih hlohi]
        have hmono : e.a lo ≤ e.a hi := e.strictMono.monotone hlohi
        have hstep : e.a hi ≤ e.a (hi + 1) :=
          (e.strictMono (Nat.lt_succ_self hi)).le
        simp only [supportGap]
        omega

/-- The raw order-`s+1` span is the corresponding endpoint difference. -/
theorem rawWindowSpan_eq_sub (W : WindowSystem) (k : ℕ) (hk : W.s ≤ k) :
    W.rawWindowSpan k = W.enumeration.a (k + 1) -
      W.enumeration.a (k - W.s) := by
  rw [WindowSystem.rawWindowSpan, dif_pos hk]
  unfold windowSpan windowGapWord GapWord.span WindowSystem.window
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have htel := sum_supportGap_Ico W.enumeration (k - W.s) (k + 1) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at htel
  simpa [show k + 1 - (k - W.s) = W.s + 1 by omega] using htel

/-- Across a run with no support digit, the carry doubles at every step. -/
theorem carryInt_zero_run (R : RationalSupport) (N r : ℕ)
    (hzero : ∀ j, 1 ≤ j → j ≤ r → N + j ∉ R.S) :
    carryInt R (N + r) = (2 : ℤ) ^ r * carryInt R N := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hzero' : ∀ j, 1 ≤ j → j ≤ r → N + j ∉ R.S := by
        intro j hj1 hjr
        exact hzero j hj1 (hjr.trans (Nat.le_succ r))
      rw [show N + (r + 1) = (N + r) + 1 by omega,
        carryInt_succ, ih hzero']
      have hnot : N + r + 1 ∉ R.S := by
        simpa [Nat.add_assoc] using hzero (r + 1) (by omega) (by omega)
      simp [digit, hnot, pow_succ]
      ring

/-- Uniformly in the numerator and support, every sufficiently large
multiplicative interval `(N,2N]` contains a support point. -/
theorem exists_support_Ioc_of_large (Q xexp : ℕ)
    (hexp : ∀ n : ℕ, xexp ≤ n → 3 * Q * n < 2 ^ (n - 1))
    (R : RationalSupport) (hden : R.eta.den = Q) (N : ℕ)
    (hN : max xexp 2 ≤ N) :
    ∃ n ∈ R.S, N < n ∧ n ≤ 2 * N := by
  by_contra hnone
  have hzero : ∀ j, 1 ≤ j → j ≤ N → N + j ∉ R.S := by
    intro j hj1 hjN hmem
    apply hnone
    exact ⟨N + j, hmem, by omega, by omega⟩
  have hrun := carryInt_zero_run R N N hzero
  have hlower : 1 ≤ carryInt R N := (prop_carry R).2.2.2 N
  have hupper : carryInt R (N + N) ≤
      (R.eta.den : ℤ) * ((N + N) + 2) := (prop_carry R).2.2.1 (N + N)
  have hpowInt : (2 : ℤ) ^ N ≤ carryInt R (N + N) := by
    rw [hrun]
    have hpnonneg : (0 : ℤ) ≤ (2 : ℤ) ^ N := by positivity
    nlinarith
  have hpow : 2 ^ N ≤ Q * (2 * N + 2) := by
    rw [hden] at hupper
    have := hpowInt.trans hupper
    have hnat : 2 ^ N ≤ Q * (N + N + 2) := by
      exact_mod_cast this
    simpa [two_mul] using hnat
  have hlinear : Q * (2 * N + 2) ≤ 3 * Q * N := by
    have hbase : 2 * N + 2 ≤ 3 * N := by
      have : 2 ≤ N := (le_max_right xexp 2).trans hN
      omega
    have := Nat.mul_le_mul_left Q hbase
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hstrict := hexp N ((le_max_left xexp 2).trans hN)
  have hpred_le : 2 ^ (N - 1) ≤ 2 ^ N :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le N 1)
  omega

/-- Every fixed quadratic polynomial is eventually dominated by `2^L`. -/
theorem eventually_quadratic_lt_two_pow (A : ℕ) :
    ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → A * L ^ 2 < 2 ^ L := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 2
    (show (1 : ℝ) < 2 by norm_num)).const_mul (A : ℝ)
  have ht0 : Tendsto
      (fun L : ℕ => (A : ℝ) * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L))
      atTop (nhds 0) := by
    simpa using ht
  have hevent : ∀ᶠ L : ℕ in atTop,
      (A : ℝ) * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L) < 1 :=
    (tendsto_order.1 ht0).2 1 (by norm_num)
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hevent
  refine ⟨L0, ?_⟩
  intro L hL
  have h := hL0 L hL
  have hpow : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hreal : (A : ℝ) * (L : ℝ) ^ 2 < (2 : ℝ) ^ L := by
    apply (div_lt_one hpow).mp
    simpa [mul_div_assoc] using h
  exact_mod_cast hreal

/-- The anchors are exactly the interval between the first support index
above `X` and the first support index above `2X`. -/
theorem anchors_eq_Ico_firstIndices (W : WindowSystem) :
    W.anchors = Finset.Ico (firstIndexAbove W.enumeration W.X)
      (firstIndexAbove W.enumeration (2 * W.X)) := by
  classical
  let i := firstIndexAbove W.enumeration W.X
  let j := firstIndexAbove W.enumeration (2 * W.X)
  have hi : W.X < W.enumeration.a i := firstIndexAbove_spec _ _
  have hj : 2 * W.X < W.enumeration.a j := firstIndexAbove_spec _ _
  have hjle : j ≤ 2 * W.X := firstIndexAbove_le _ _
  ext k
  simp only [WindowSystem.anchors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ico]
  constructor
  · rintro ⟨_, hkX, hk2X⟩
    have hik : i ≤ k := by
      by_contra hnot
      have hle := firstIndexAbove_minimal W.enumeration W.X k
        (Nat.lt_of_not_ge hnot)
      omega
    have hkj : k < j := by
      by_contra hnot
      have hjk : j ≤ k := Nat.le_of_not_gt hnot
      have := W.enumeration.strictMono.monotone hjk
      omega
    exact ⟨hik, hkj⟩
  · rintro ⟨hik, hkj⟩
    have hkX : W.X < W.enumeration.a k :=
      hi.trans_le (W.enumeration.strictMono.monotone hik)
    have hk2X : W.enumeration.a k ≤ 2 * W.X :=
      firstIndexAbove_minimal W.enumeration (2 * W.X) k hkj
    exact ⟨by omega, hkX, hk2X⟩

theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

theorem rawWindowSpan_eq_sum_range (W : WindowSystem) (k : ℕ)
    (hk : W.s ≤ k) :
    W.rawWindowSpan k =
      ∑ r ∈ Finset.range W.m,
        supportGap W.enumeration (k - W.s + r) := by
  rw [WindowSystem.rawWindowSpan, dif_pos hk]
  unfold windowSpan windowGapWord GapWord.span WindowSystem.window
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

/-- Every gap in the central index interval is counted by all `m=s+1`
overlapping anchored windows. -/
theorem central_gap_multiplicity (W : WindowSystem) (i j : ℕ)
    (hanchors : W.anchors = Finset.Ico i j)
    (hsi : W.s ≤ i) (hij0 : i ≤ j) (hwidth : W.s ≤ j - i) :
    W.m * (W.enumeration.a (j - W.s) - W.enumeration.a i) ≤
      ∑ k ∈ W.anchors, W.rawWindowSpan k := by
  have hij : i ≤ j - W.s := by omega
  have hcentral := sum_supportGap_Ico W.enumeration i (j - W.s) hij
  rw [hanchors]
  calc
    W.m * (W.enumeration.a (j - W.s) - W.enumeration.a i) =
        ∑ r ∈ Finset.range W.m,
          ∑ t ∈ Finset.Ico i (j - W.s), supportGap W.enumeration t := by
      rw [← hcentral]
      simp [WindowSystem.m, mul_comm]
    _ ≤ ∑ r ∈ Finset.range W.m,
          ∑ k ∈ Finset.Ico i j,
            supportGap W.enumeration (k - W.s + r) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrs : r ≤ W.s := by
        simpa [WindowSystem.m] using (Finset.mem_range.mp hr)
      have hshift :
          (∑ k ∈ Finset.Ico i j,
              supportGap W.enumeration (k - W.s + r)) =
            ∑ t ∈ Finset.Ico (i - W.s + r) (j - W.s + r),
              supportGap W.enumeration t := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        have hlen :
            (j - W.s + r) - (i - W.s + r) = j - i := by omega
        rw [hlen]
        apply Finset.sum_congr rfl
        intro q hq
        have harg : i + q - W.s + r = i - W.s + r + q := by omega
        rw [harg]
      rw [hshift]
      apply Finset.sum_le_sum_of_subset
      exact Finset.Ico_subset_Ico (by omega) (by omega)
    _ = ∑ k ∈ Finset.Ico i j, W.rawWindowSpan k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [rawWindowSpan_eq_sum_range W k]
      exact hsi.trans (Finset.mem_Ico.mp hk).1

theorem sum_supportGap_le_mul {S : Set ℕ} (e : SupportEnumeration S)
    (lo hi G : ℕ) (hlo : lo ≤ hi)
    (hgap : ∀ k ∈ Finset.Ico lo hi, supportGap e k ≤ G) :
    e.a hi - e.a lo ≤ (hi - lo) * G := by
  rw [← sum_supportGap_Ico e lo hi hlo]
  calc
    (∑ k ∈ Finset.Ico lo hi, supportGap e k) ≤
        ∑ _k ∈ Finset.Ico lo hi, G := Finset.sum_le_sum hgap
    _ = (hi - lo) * G := by simp

/-- Paper label: `lem:window-count` (Section 4). -/
theorem lem_window_count (Q : ℕ) (hQ : 0 < Q)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ L0 : ℕ, ∀ W : WindowSystem,
      W.rational.eta.den = Q → L0 ≤ W.L →
      (W.s : ℝ) ≤ C * W.L →
       ((W.m * W.X : ℕ) : ℝ) ≤
         (∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) +
           K * (W.s + 1) * (W.L : ℝ) ^ 2 := by
  obtain ⟨Cgap, x0, hgap⟩ := lem_gap Q hQ
  obtain ⟨xexp, hexp⟩ := eventually_linear_lt_two_pow_pred Q
  let cN := Nat.ceil C
  let K0 := (cN + 1) * (Cgap + 2)
  obtain ⟨Lquad, hquad⟩ := eventually_quadratic_lt_two_pow (4 * K0)
  let L0 := max Lquad (max (max xexp x0 + 2) 4)
  refine ⟨(K0 : ℝ), by positivity, L0, ?_⟩
  intro W hden hL hs
  have hL' : max Lquad (max (max xexp x0 + 2) 4) ≤ W.L := by
    simpa [L0] using hL
  have hLquad : Lquad ≤ W.L := (le_max_left _ _).trans hL'
  have hLbase : max xexp x0 + 2 ≤ W.L :=
    (le_max_left _ 4).trans ((le_max_right Lquad _).trans hL')
  have hL4 : 4 ≤ W.L :=
    (le_max_right (max xexp x0 + 2) 4).trans
      ((le_max_right Lquad _).trans hL')
  let H := 2 ^ (W.L - 2)
  have hHpos : 0 < H := by positivity
  have hxexpH : max xexp 2 ≤ H := by
    have hself := self_le_two_pow (W.L - 2)
    dsimp [H]
    omega
  have hx0H : x0 ≤ H := by
    have hself := self_le_two_pow (W.L - 2)
    dsimp [H]
    omega
  have hX : W.X = 4 * H := by
    unfold WindowSystem.X dyadicScale
    dsimp [H]
    calc
      2 ^ W.L = 2 ^ ((W.L - 2) + 2) := by
        congr 1
        omega
      _ = 2 ^ (W.L - 2) * 2 ^ 2 := pow_add _ _ _
      _ = 4 * 2 ^ (W.L - 2) := by ring
  obtain ⟨nv, hnvS, hnvLower, hnvUpper⟩ :=
    exists_support_Ioc_of_large Q xexp hexp W.rational hden H hxexpH
  have hnvRange : nv ∈ Set.range W.enumeration.a :=
    (Set.ext_iff.mp W.enumeration.range_eq nv).mpr hnvS
  rcases hnvRange with ⟨v, hv⟩
  have hvLower : H < W.enumeration.a v := by simpa [hv] using hnvLower
  have hvUpper : W.enumeration.a v ≤ 2 * H := by simpa [hv] using hnvUpper
  have hxexp2H : max xexp 2 ≤ 2 * H := hxexpH.trans (by omega)
  obtain ⟨nu, hnuS, hnuLower, hnuUpper⟩ :=
    exists_support_Ioc_of_large Q xexp hexp W.rational hden (2 * H) hxexp2H
  have hnuRange : nu ∈ Set.range W.enumeration.a :=
    (Set.ext_iff.mp W.enumeration.range_eq nu).mpr hnuS
  rcases hnuRange with ⟨u, hu⟩
  have huLower : 2 * H < W.enumeration.a u := by simpa [hu] using hnuLower
  have huUpper : W.enumeration.a u ≤ 4 * H := by
    calc
      W.enumeration.a u = nu := hu
      _ ≤ 2 * (2 * H) := hnuUpper
      _ = 4 * H := by ring
  let i := firstIndexAbove W.enumeration W.X
  let j := firstIndexAbove W.enumeration (2 * W.X)
  have hi : W.X < W.enumeration.a i := firstIndexAbove_spec _ _
  have hj : 2 * W.X < W.enumeration.a j := firstIndexAbove_spec _ _
  have hv_i : v < i := by
    by_contra hnot
    have hiv : i ≤ v := Nat.le_of_not_gt hnot
    have hmono := W.enumeration.strictMono.monotone hiv
    omega
  have hu_i : u < i := by
    by_contra hnot
    have hiu : i ≤ u := Nat.le_of_not_gt hnot
    have hmono := W.enumeration.strictMono.monotone hiu
    omega
  have hiPos : 0 < i := by omega
  have hprevX : W.enumeration.a (i - 1) ≤ W.X :=
    firstIndexAbove_minimal W.enumeration W.X (i - 1) (by omega)
  have huPrev : u ≤ i - 1 := by omega
  have hprevLower : 2 * H < W.enumeration.a (i - 1) :=
    huLower.trans_le (W.enumeration.strictMono.monotone huPrev)
  have hprevGap0 := hgap W.rational hden (W.enumeration.a (i - 1))
    (by omega) (supportGap W.enumeration (i - 1))
    (supportGap_isSupportGap W.enumeration (i - 1))
  have hlogPrev : Nat.log 2 (W.enumeration.a (i - 1)) ≤ W.L := by
    calc
      Nat.log 2 (W.enumeration.a (i - 1)) ≤ Nat.log 2 W.X :=
        Nat.log_mono_right hprevX
      _ = W.L := by
        simp [WindowSystem.X, dyadicScale, Nat.log_pow]
  let G := W.L + 1 + Cgap
  have hprevGap : supportGap W.enumeration (i - 1) ≤ G := by
    dsimp [G]
    omega
  have hprevStep : W.enumeration.a (i - 1) < W.enumeration.a i := by
    apply W.enumeration.strictMono
    omega
  have haiSplit :
      W.enumeration.a i = W.enumeration.a (i - 1) +
        supportGap W.enumeration (i - 1) := by
    rw [supportGap, show i - 1 + 1 = i by omega,
      Nat.add_sub_of_le hprevStep.le]
  have haiUpper : W.enumeration.a i ≤ W.X + G := by omega
  have hGapIJ : ∀ t ∈ Finset.Ico i j, supportGap W.enumeration t ≤ G := by
    intro t ht
    have hit : i ≤ t := (Finset.mem_Ico.mp ht).1
    have htj : t < j := (Finset.mem_Ico.mp ht).2
    have hatLower : W.X < W.enumeration.a t :=
      hi.trans_le (W.enumeration.strictMono.monotone hit)
    have hatUpper : W.enumeration.a t ≤ 2 * W.X :=
      firstIndexAbove_minimal W.enumeration (2 * W.X) t htj
    have hgb := hgap W.rational hden (W.enumeration.a t) (by omega)
      (supportGap W.enumeration t) (supportGap_isSupportGap W.enumeration t)
    have hlog : Nat.log 2 (W.enumeration.a t) ≤ W.L + 1 := by
      calc
        Nat.log 2 (W.enumeration.a t) ≤ Nat.log 2 (2 * W.X) :=
          Nat.log_mono_right hatUpper
        _ = W.L + 1 := by
          rw [show 2 * W.X = 2 ^ (W.L + 1) by
            simp [WindowSystem.X, dyadicScale, pow_succ, mul_comm],
            Nat.log_pow (by omega)]
    dsimp [G]
    omega
  have hCceil : C ≤ (cN : ℝ) := by
    simpa [cN] using (Nat.le_ceil C)
  have hsNat : W.s ≤ cN * W.L := by
    have hsReal : (W.s : ℝ) ≤ ((cN * W.L : ℕ) : ℝ) := by
      calc
        (W.s : ℝ) ≤ C * (W.L : ℝ) := hs
        _ ≤ (cN : ℝ) * (W.L : ℝ) :=
          mul_le_mul_of_nonneg_right hCceil (Nat.cast_nonneg _)
        _ = ((cN * W.L : ℕ) : ℝ) := by norm_num
    exact_mod_cast hsReal
  have hmLe : W.m ≤ (cN + 1) * W.L := by
    dsimp [WindowSystem.m]
    nlinarith
  have hGLe : G ≤ (Cgap + 2) * W.L := by
    have hL1 : 1 ≤ W.L := by omega
    have hCmul : Cgap ≤ Cgap * W.L := by
      calc
        Cgap = Cgap * 1 := by simp
        _ ≤ Cgap * W.L := Nat.mul_le_mul_left Cgap hL1
    calc
      G = W.L + 1 + Cgap := rfl
      _ ≤ W.L + W.L + Cgap * W.L := by omega
      _ = (Cgap + 2) * W.L := by ring
  have hmG : W.m * G ≤ K0 * W.L ^ 2 := by
    calc
      W.m * G ≤ ((cN + 1) * W.L) * ((Cgap + 2) * W.L) :=
        Nat.mul_le_mul hmLe hGLe
      _ = K0 * W.L ^ 2 := by simp [K0]; ring
  have hpoly : 4 * K0 * W.L ^ 2 < W.X := by
    simpa [WindowSystem.X, dyadicScale] using hquad W.L hLquad
  have hfourSmall : 4 * (K0 * W.L ^ 2) < 4 * H := by
    calc
      4 * (K0 * W.L ^ 2) = 4 * K0 * W.L ^ 2 := by ring
      _ < W.X := hpoly
      _ = 4 * H := hX
  have hKsmall : K0 * W.L ^ 2 < H := by omega
  have hmGsmall : W.m * G < H := hmG.trans_lt hKsmall
  have hsGsmall : W.s * G < H := by
    have hsm : W.s ≤ W.m := by simp [WindowSystem.m]
    exact (Nat.mul_le_mul_right G hsm).trans_lt hmGsmall
  have hGapVI : ∀ t ∈ Finset.Ico v i, supportGap W.enumeration t ≤ G := by
    intro t ht
    have hvt : v ≤ t := (Finset.mem_Ico.mp ht).1
    have hti : t < i := (Finset.mem_Ico.mp ht).2
    have hatLower : H < W.enumeration.a t :=
      hvLower.trans_le (W.enumeration.strictMono.monotone hvt)
    have hatUpper : W.enumeration.a t ≤ W.X :=
      firstIndexAbove_minimal W.enumeration W.X t hti
    have hgb := hgap W.rational hden (W.enumeration.a t) (by omega)
      (supportGap W.enumeration t) (supportGap_isSupportGap W.enumeration t)
    have hlog : Nat.log 2 (W.enumeration.a t) ≤ W.L := by
      calc
        Nat.log 2 (W.enumeration.a t) ≤ Nat.log 2 W.X :=
          Nat.log_mono_right hatUpper
        _ = W.L := by
          simp [WindowSystem.X, dyadicScale, Nat.log_pow]
    dsimp [G]
    omega
  have hi_s : W.s < i := by
    by_contra hnot
    have his : i ≤ W.s := Nat.le_of_not_gt hnot
    have hsum := sum_supportGap_le_mul W.enumeration v i G hv_i.le hGapVI
    have hmul : (i - v) * G ≤ W.s * G :=
      Nat.mul_le_mul_right G (by omega)
    have hdifflower : 2 * H < W.enumeration.a i - W.enumeration.a v := by
      rw [hX] at hi
      omega
    omega
  have hGsmall : G < H := by
    have hGm : G ≤ W.m * G := by
      have hmpos : 1 ≤ W.m := by simp [WindowSystem.m]
      simpa using Nat.mul_le_mul_right G hmpos
    exact hGm.trans_lt hmGsmall
  have hai2X : W.enumeration.a i ≤ 2 * W.X := by
    rw [hX] at haiUpper ⊢
    omega
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := Nat.le_of_not_gt hnot
    have hmono := W.enumeration.strictMono.monotone hji
    omega
  have hwidth : W.s < j - i := by
    by_contra hnot
    have hjiS : j - i ≤ W.s := Nat.le_of_not_gt hnot
    have hsum := sum_supportGap_le_mul W.enumeration i j G hij.le hGapIJ
    have hmul : (j - i) * G ≤ W.s * G :=
      Nat.mul_le_mul_right G hjiS
    have hdifflower : H < W.enumeration.a j - W.enumeration.a i := by
      rw [hX] at hj haiUpper
      omega
    omega
  have hanchors : W.anchors = Finset.Ico i j :=
    anchors_eq_Ico_firstIndices W
  have hcentral := central_gap_multiplicity W i j hanchors hi_s.le hij.le
    (Nat.le_of_lt hwidth)
  have hi_jsub : i ≤ j - W.s := by omega
  have htailGap : ∀ t ∈ Finset.Ico (j - W.s) j,
      supportGap W.enumeration t ≤ G := by
    intro t ht
    apply hGapIJ t
    exact Finset.mem_Ico.mpr
      ⟨hi_jsub.trans (Finset.mem_Ico.mp ht).1,
        (Finset.mem_Ico.mp ht).2⟩
  have htail := sum_supportGap_le_mul W.enumeration (j - W.s) j G
    (by omega) htailGap
  have htailMul : (j - (j - W.s)) * G ≤ W.s * G := by
    apply Nat.mul_le_mul_right
    omega
  have hajSplit : W.enumeration.a j = W.enumeration.a (j - W.s) +
      (W.enumeration.a j - W.enumeration.a (j - W.s)) := by
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono.monotone (by omega))).symm
  have hacenterSplit : W.enumeration.a (j - W.s) = W.enumeration.a i +
      (W.enumeration.a (j - W.s) - W.enumeration.a i) := by
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono.monotone hi_jsub)).symm
  have hmG_eq : W.m * G = W.s * G + G := by
    simp [WindowSystem.m]
    ring
  have hcoordinate : W.X ≤
      (W.enumeration.a (j - W.s) - W.enumeration.a i) + W.m * G := by
    omega
  have hmulCoordinate := Nat.mul_le_mul_left W.m hcoordinate
  have hboundary : W.m * (W.m * G) ≤ W.m * (K0 * W.L ^ 2) :=
    Nat.mul_le_mul_left W.m hmG
  have hnat : W.m * W.X ≤
      (∑ k ∈ W.anchors, W.rawWindowSpan k) +
        K0 * W.m * W.L ^ 2 := by
    calc
      W.m * W.X ≤ W.m *
          ((W.enumeration.a (j - W.s) - W.enumeration.a i) + W.m * G) :=
        hmulCoordinate
      _ = W.m * (W.enumeration.a (j - W.s) - W.enumeration.a i) +
          W.m * (W.m * G) := by ring
      _ ≤ (∑ k ∈ W.anchors, W.rawWindowSpan k) +
          W.m * (K0 * W.L ^ 2) := Nat.add_le_add hcentral hboundary
      _ = (∑ k ∈ W.anchors, W.rawWindowSpan k) +
          K0 * W.m * W.L ^ 2 := by ring
  exact_mod_cast hnat

/-- Tonelli identity for the finite anchor set: each threshold weight is
integrated exactly once after summing all spatial anchors. -/
theorem mass_pairSet_eq_threshold_lintegral (W : WindowSystem) :
    mass W.pairSet W.excess =
      ∫⁻ T in W.thresholds,
        ∑ k ∈ W.anchors, ENNReal.ofReal (W.excess (k, T)) ∂volume := by
  unfold mass windowThresholdMeasure
  rw [WindowSystem.pairSet_eq_prod]
  change (∫⁻ e : WindowThreshold,
      ENNReal.ofReal (W.excess e) ∂
        (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds)) = _
  have hmeasure :
      (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        (Measure.count.restrict (W.anchors : Set ℕ)).prod
          (volume.restrict W.thresholds) :=
    (Measure.prod_restrict (μ := Measure.count) (ν := volume)
      (W.anchors : Set ℕ) W.thresholds).symm
  rw [hmeasure]
  rw [MeasureTheory.lintegral_prod_symm]
  · apply lintegral_congr
    intro T
    rw [MeasureTheory.lintegral_finset]
    simp
  · exact (W.measurable_excess.ennreal_ofReal.aemeasurable)

/-- A uniform lower bound for the sum of excesses at every threshold gives
the corresponding lower bound for the certified real mass. -/
theorem integratedExcess_lower_of_threshold_sum (W : WindowSystem) (A : ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ T ∈ W.thresholds,
      A ≤ ∑ k ∈ W.anchors, W.excess (k, T)) :
    A * thresholdLength W ≤ integratedExcess W := by
  have hlength : 0 ≤ thresholdLength W :=
    mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hmass : ENNReal.ofReal (A * thresholdLength W) ≤
      mass W.pairSet W.excess := by
    rw [mass_pairSet_eq_threshold_lintegral]
    rw [ENNReal.ofReal_mul hA]
    calc
      ENNReal.ofReal A * ENNReal.ofReal (thresholdLength W) =
          ∫⁻ _T in W.thresholds, ENNReal.ofReal A ∂volume := by
        rw [MeasureTheory.setLIntegral_const]
        congr 1
        simp [WindowSystem.thresholds, thresholdInterval, Real.volume_Icc,
          thresholdLength]
      _ ≤ ∫⁻ T in W.thresholds,
          ∑ k ∈ W.anchors, ENNReal.ofReal (W.excess (k, T)) ∂volume := by
        apply setLIntegral_mono'
          (by simp [WindowSystem.thresholds, thresholdInterval])
        intro T hT
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · exact ENNReal.ofReal_le_ofReal (hlower T hT)
        · intro k hk
          exact le_max_right _ _
  have hleftTop : ENNReal.ofReal (A * thresholdLength W) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hrightTop : mass W.pairSet W.excess ≠ ⊤ :=
    totalMass_finite W
  have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  rw [ENNReal.toReal_ofReal (mul_nonneg hA hlength)] at hreal
  simpa [integratedExcess, totalMassReal, FiniteMass.toReal] using hreal

/-- Anchor indices inject into the support points in the same dyadic block. -/
theorem anchors_card_le_dyadicBlockCount (W : WindowSystem) :
    W.anchors.card ≤ dyadicBlockCount W.rational.S W.X := by
  classical
  let a : ℕ → ℕ := W.enumeration.a
  have ha_strict : StrictMono a := W.enumeration.strictMono
  have ha_range : Set.range a = W.rational.S := W.enumeration.range_eq
  have hsubset : W.anchors.image a ⊆
      (Finset.Ioc W.X (2 * W.X)).filter (fun n => n ∈ W.rational.S) := by
    rw [Finset.image_subset_iff]
    intro k hk
    simp only [WindowSystem.anchors, Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by simpa [a] using hk.2.1, by simpa [a] using hk.2.2⟩, ?_⟩
    have hmem : a k ∈ Set.range a := ⟨k, rfl⟩
    rw [ha_range] at hmem
    exact hmem
  calc
    W.anchors.card = (W.anchors.image a).card :=
      (Finset.card_image_of_injective W.anchors ha_strict.injective).symm
    _ ≤ ((Finset.Ioc W.X (2 * W.X)).filter
        (fun n => n ∈ W.rational.S)).card := Finset.card_le_card hsubset
    _ = dyadicBlockCount W.rational.S W.X := by rfl

theorem eventually_real_quadratic_lt_eighth_two_pow (K : ℝ) :
    ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      K * (L : ℝ) ^ 2 < (1 / 8 : ℝ) * (2 : ℝ) ^ L := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 2
    (show (1 : ℝ) < 2 by norm_num)).const_mul K
  have ht0 : Tendsto
      (fun L : ℕ => K * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L))
      atTop (nhds 0) := by
    simpa using ht
  have hevent : ∀ᶠ L : ℕ in atTop,
      K * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L) < (1 / 8 : ℝ) :=
    (tendsto_order.1 ht0).2 (1 / 8) (by norm_num)
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hevent
  refine ⟨L0, ?_⟩
  intro L hL
  have h := hL0 L hL
  have hpow : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  apply (div_lt_iff₀ hpow).mp
  simpa [mul_div_assoc] using h

/-- Paper label: `prop:pressure` (Section 4). -/
theorem prop_pressure (Q : ℕ) (hQ : 0 < Q)
    (p : StructuralParams) (entropy : EntropyParams)
    (_hstructural : entropy.structural = p) :
    ∃ ε cLower deltaLower : ℝ,
      0 < ε ∧ 0 < cLower ∧ 0 < deltaLower ∧
      ∃ L0 : ℕ, ∀ W : WindowSystem, ∀ δ : ℝ,
        W.rational.eta.den = Q → W.structural = p →
        W.entropy = entropy → W.epsilon = ε →
        W.s = Nat.floor (entropy.kappa * (W.L : ℝ)) →
        L0 ≤ W.L → 0 < δ → δ ≤ deltaLower →
        (dyadicBlockCount W.rational.S W.X : ℝ) ≤ δ * W.X →
        cLower * W.m * W.X * thresholdLength W ≤ integratedExcess W := by
  let C := entropy.kappa + 1
  have hC : 0 < C := by dsimp [C]; linarith [entropy.kappa_pos]
  obtain ⟨K, hK, Lwindow, hwindow⟩ := lem_window_count Q hQ C hC
  obtain ⟨Lasym, hasym⟩ := eventually_real_quadratic_lt_eighth_two_pow K
  let D : ℝ := 3 + p.cI + p.C0
  have hD : 0 < D := by
    dsimp [D]
    linarith [p.cI_pos]
  let deltaLower := entropy.kappa / (8 * D)
  have hdeltaLower : 0 < deltaLower := by
    dsimp [deltaLower]
    exact div_pos entropy.kappa_pos (mul_pos (by norm_num) hD)
  let L0 := max Lwindow (max Lasym 1)
  refine ⟨1, 1 / 2, deltaLower, by norm_num, by norm_num,
    hdeltaLower, L0, ?_⟩
  intro W δ hden hWp hWentropy hWepsilon hsEq hL hδ hδupper hsparse
  have hL' : max Lwindow (max Lasym 1) ≤ W.L := by
    simpa [L0] using hL
  have hLwindow : Lwindow ≤ W.L := (le_max_left _ _).trans hL'
  have hLasym : Lasym ≤ W.L :=
    (le_max_left _ 1).trans ((le_max_right Lwindow _).trans hL')
  have hL1 : 1 ≤ W.L :=
    (le_max_right Lasym 1).trans ((le_max_right Lwindow _).trans hL')
  have hkLnonneg : 0 ≤ entropy.kappa * (W.L : ℝ) :=
    mul_nonneg entropy.kappa_pos.le (Nat.cast_nonneg _)
  have hsC : (W.s : ℝ) ≤ C * (W.L : ℝ) := by
    rw [hsEq]
    calc
      ((Nat.floor (entropy.kappa * (W.L : ℝ)) : ℕ) : ℝ) ≤
          entropy.kappa * (W.L : ℝ) := Nat.floor_le hkLnonneg
      _ ≤ C * (W.L : ℝ) := by
        dsimp [C]
        calc
          entropy.kappa * (W.L : ℝ) ≤
              entropy.kappa * W.L + 1 * W.L :=
            le_add_of_nonneg_right (by positivity)
          _ = (entropy.kappa + 1) * W.L := by ring
  have hcount := hwindow W hden hLwindow hsC
  have hboundary : K * (W.L : ℝ) ^ 2 ≤ (1 / 8 : ℝ) * W.X := by
    have h := (hasym W.L hLasym).le
    simpa [WindowSystem.X, dyadicScale] using h
  have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
  have hspanLower :
      (7 / 8 : ℝ) * W.m * W.X ≤
        (∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) := by
    have hboundaryMul :
        K * (W.s + 1 : ℕ) * (W.L : ℝ) ^ 2 ≤
          (1 / 8 : ℝ) * W.m * W.X := by
      have := mul_le_mul_of_nonneg_left hboundary hmnonneg
      calc
        K * (W.s + 1 : ℕ) * (W.L : ℝ) ^ 2 =
            (W.m : ℝ) * (K * (W.L : ℝ) ^ 2) := by
          simp [WindowSystem.m]
          ring
        _ ≤ (W.m : ℝ) * ((1 / 8 : ℝ) * W.X) := this
        _ = (1 / 8 : ℝ) * W.m * W.X := by ring
    have hmXnonneg : (0 : ℝ) ≤ W.m * W.X := by positivity
    simp only [Nat.cast_add, Nat.cast_one] at hboundaryMul
    push_cast at hcount
    calc
      (7 / 8 : ℝ) * W.m * W.X =
          (W.m : ℝ) * W.X - (1 / 8 : ℝ) * W.m * W.X := by ring
      _ ≤ (W.m : ℝ) * W.X -
          K * ((W.s : ℝ) + 1) * (W.L : ℝ) ^ 2 :=
        sub_le_sub_left hboundaryMul _
      _ ≤ ∑ k ∈ W.anchors, (W.rawWindowSpan k : ℝ) := by
        exact (sub_le_iff_le_add).2 hcount
      _ = ((∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) : ℝ) := by
        push_cast
        rfl
  have hfloorLower : entropy.kappa * (W.L : ℝ) < (W.m : ℝ) := by
    have h := Nat.lt_floor_add_one (entropy.kappa * (W.L : ℝ))
    rw [← hsEq] at h
    simpa [WindowSystem.m] using h
  have hanchor : (W.anchors.card : ℝ) ≤ δ * W.X := by
    calc
      (W.anchors.card : ℝ) ≤ dyadicBlockCount W.rational.S W.X := by
        exact_mod_cast anchors_card_le_dyadicBlockCount W
      _ ≤ δ * W.X := hsparse
  have hdeltaD : δ * D ≤ entropy.kappa / 8 := by
    calc
      δ * D ≤ deltaLower * D :=
        mul_le_mul_of_nonneg_right hδupper hD.le
      _ = entropy.kappa / 8 := by
        dsimp [deltaLower]
        field_simp
  have hpointwise : ∀ T ∈ W.thresholds,
      (1 / 2 : ℝ) * W.m * W.X ≤
        ∑ k ∈ W.anchors, W.excess (k, T) := by
    intro T hT
    have hTupper :
        T ≤ 2 * (W.L : ℝ) + p.C0 + p.cI * W.L := by
      exact hT.2.trans_eq (by rw [hWp])
    have hC0mul : (p.C0 : ℝ) ≤ p.C0 * (W.L : ℝ) := by
      have hnat : p.C0 ≤ p.C0 * W.L := by
        calc
          p.C0 = p.C0 * 1 := by simp
          _ ≤ p.C0 * W.L := Nat.mul_le_mul_left p.C0 hL1
      exact_mod_cast hnat
    have hTU : T + W.epsilon * W.L ≤ D * W.L := by
      rw [hWepsilon]
      dsimp [D]
      nlinarith
    have hTnonneg : 0 ≤ T := by
      have hTlower := hT.1
      have hbase : (0 : ℝ) ≤
          2 * W.L + W.structural.C0 := by positivity
      exact hbase.trans hTlower
    have hTU_nonneg : 0 ≤ T + W.epsilon * W.L := by
      rw [hWepsilon]
      positivity
    have hDWLnonneg : 0 ≤ D * (W.L : ℝ) :=
      mul_nonneg hD.le (Nat.cast_nonneg _)
    have hloss : (W.anchors.card : ℝ) *
        (T + W.epsilon * W.L) ≤ (1 / 8 : ℝ) * W.m * W.X := by
      calc
        (W.anchors.card : ℝ) * (T + W.epsilon * W.L) ≤
            (δ * W.X) * (D * W.L) :=
          mul_le_mul hanchor hTU hTU_nonneg
            (mul_nonneg hδ.le (Nat.cast_nonneg _))
        _ = (δ * D) * W.X * W.L := by ring
        _ ≤ (entropy.kappa / 8) * W.X * W.L := by
          gcongr
        _ ≤ (1 / 8 : ℝ) * W.m * W.X := by
          have hfloorLe : entropy.kappa * (W.L : ℝ) ≤ W.m :=
            hfloorLower.le
          calc
            (entropy.kappa / 8) * W.X * W.L =
                ((1 / 8 : ℝ) * W.X) * (entropy.kappa * W.L) := by ring
            _ ≤ ((1 / 8 : ℝ) * W.X) * W.m :=
              mul_le_mul_of_nonneg_left hfloorLe (by positivity)
            _ = (1 / 8 : ℝ) * W.m * W.X := by ring
    have hterm : ∀ k ∈ W.anchors,
        ((W.rawWindowSpan k : ℕ) : ℝ) - T - W.epsilon * W.L ≤
          W.excess (k, T) := by
      intro k hk
      unfold WindowSystem.excess
      exact le_max_left _ _
    have hsumTerm := Finset.sum_le_sum hterm
    have hsumExpand :
        (∑ k ∈ W.anchors,
            (((W.rawWindowSpan k : ℕ) : ℝ) - T - W.epsilon * W.L)) =
          ((∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) : ℝ) -
            (W.anchors.card : ℝ) * (T + W.epsilon * W.L) := by
      push_cast
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsumExpand] at hsumTerm
    linarith
  have hA : 0 ≤ (1 / 2 : ℝ) * W.m * W.X := by positivity
  have hmass := integratedExcess_lower_of_threshold_sum W
    ((1 / 2 : ℝ) * W.m * W.X) hA hpointwise
  simpa using hmass

theorem boundedPairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    W.boundedPairs Z0 ⊆ W.pairSet := by
  exact inter_subset_left

/-- Certified real mass of the bounded-excess parent family. -/
def boundedPairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (W.boundedPairs Z0) (boundedPairs_subset_pairSet W Z0)

/-- Exact measure of the full window–threshold rectangle. -/
theorem windowThresholdMeasure_pairSet (W : WindowSystem) :
    windowThresholdMeasure W.pairSet =
      (W.anchors.card : ℝ≥0∞) * ENNReal.ofReal (thresholdLength W) := by
  rw [WindowSystem.pairSet_eq_prod, windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        Measure.count (W.anchors : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc, thresholdLength]
  congr 2
  ring

/-- Paper label: `prop:moderate` (Section 4). -/
theorem prop_moderate (W : WindowSystem) (Z0 : ℕ) (cstar : ℝ)
    (hcstar : 0 ≤ cstar)
    (hsparse : (dyadicBlockCount W.rational.S W.X : ℝ) ≤ cstar * W.X) :
    boundedPairsMass W Z0 ≤
      Z0 * cstar * W.m * W.X * thresholdLength W := by
  have _hcstar : 0 ≤ cstar := hcstar
  have hc : (0 : ℝ) ≤ ((W.m * Z0 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlength : 0 ≤ thresholdLength W := by
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hmass :
      mass (W.boundedPairs Z0) W.excess ≤
        ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ)) *
          windowThresholdMeasure W.pairSet := by
    unfold mass
    calc
      (∫⁻ e in W.boundedPairs Z0, ENNReal.ofReal (W.excess e)
          ∂windowThresholdMeasure) ≤
          ∫⁻ _e in W.boundedPairs Z0,
            ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ))
              ∂windowThresholdMeasure := by
        apply setLIntegral_mono measurable_const
        intro e he
        apply ENNReal.ofReal_le_ofReal
        exact_mod_cast he.2
      _ ≤ ∫⁻ _e in W.pairSet,
            ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ))
              ∂windowThresholdMeasure :=
        lintegral_mono_set (boundedPairs_subset_pairSet W Z0)
      _ = ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ)) *
            windowThresholdMeasure W.pairSet :=
        setLIntegral_const _ _
  have hleft_top : mass (W.boundedPairs Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (W.boundedPairs Z0)
      (boundedPairs_subset_pairSet W Z0)).ne_top
  have hright_top :
      ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ)) *
          windowThresholdMeasure W.pairSet ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (windowThresholdMeasure_pairSet_ne_top W)
  have hto := (ENNReal.toReal_le_toReal hleft_top hright_top).2 hmass
  have hreal : boundedPairsMass W Z0 ≤
      (((W.m * Z0 : ℕ) : ℝ)) * W.anchors.card * thresholdLength W := by
    change (mass (W.boundedPairs Z0) W.excess).toReal ≤ _
    rw [windowThresholdMeasure_pairSet] at hto
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlength, mul_assoc] using hto
  have hanchors : (W.anchors.card : ℝ) ≤ cstar * W.X := by
    calc
      (W.anchors.card : ℝ) ≤ dyadicBlockCount W.rational.S W.X := by
        exact_mod_cast anchors_card_le_dyadicBlockCount W
      _ ≤ cstar * W.X := hsparse
  calc
    boundedPairsMass W Z0 ≤
        (((W.m * Z0 : ℕ) : ℝ)) * W.anchors.card * thresholdLength W := hreal
    _ ≤ (((W.m * Z0 : ℕ) : ℝ)) *
        (cstar * W.X) * thresholdLength W := by
      gcongr
    _ = Z0 * cstar * W.m * W.X * thresholdLength W := by
      push_cast
      ring

end Erdos260
