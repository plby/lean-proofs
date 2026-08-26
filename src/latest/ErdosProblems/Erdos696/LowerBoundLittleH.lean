/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.UpperBoundLittleH

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

variable [sw : SiegelWalfisz]
include sw

-- === Inlined from Erdos696/LowerBoundLittleH.lean ===
/-
# Lower bound for `h(n)`

Mirrors §5 of `erdos_696_paper.tex`.

**Theorem.** For all but `o(x)` integers `n ≤ x`,
`h(n) ≥ (1/2 - o(1)) log_* x`.

**Proof structure (paper §5).**
1. *Prime-successor mass lemma* (Lemma 5.1):
   `∑_{exp(exp y) < q ≤ exp(exp(η y)), q ≡ 1 mod p, q prime} 1/q
       = (η-1) y / φ(p) + O(1) ≥ c₁(η-1) y / p`.
   Uses Siegel–Walfisz.
2. *Tower scale* (equation (5.4)): set `B := L^2`, `m_j := m_0 + 2(j-1)`
   with `m_0 = ⌊L^{1/2}⌋`, `R := (L - m_0 - 2)/2`.  Then `R = (1/2 - o(1)) L`.
3. *Greedy chain construction* (Lemma 5.2): in the product model,
   `P(no chain p₁ < ⋯ < p_R exists) ≤ o(1) + L · exp(-c₁ L^2 / 2) = o(1)`.
4. *CRT transfer* (Lemma 2.7): density of "good" `n` is
   `P_prod(C_h) + O(M/x) = 1 - o(1)`.  Uses Chebyshev to bound `M`.
-/



open Real

lemma integral_one_div_mul_log_of_one_lt {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t)) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  have hgt1 : ∀ x ∈ Set.uIcc a b, 1 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    linarith [hgt1 x hx]
  have hlogpos : ∀ x ∈ Set.uIcc a b, 0 < Real.log x := by
    intro x hx
    exact Real.log_pos (hgt1 x hx)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Real.log (Real.log t)) (1 / (x * Real.log x)) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (hpos x hx)
    have hlogne : Real.log x ≠ 0 := ne_of_gt (hlogpos x hx)
    have h := (Real.hasDerivAt_log hlogne).comp x (Real.hasDerivAt_log hxne)
    simpa [Function.comp_def, one_div, mul_comm, mul_left_comm, mul_assoc] using h
  have hcont_log : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc a b) := by
    exact continuousOn_id.log (fun t ht => (hpos t ht).ne')
  have hcont_prod : ContinuousOn (fun t : ℝ => t * Real.log t) (Set.uIcc a b) := by
    exact continuousOn_id.mul hcont_log
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.uIcc a b) := by
    exact continuousOn_const.div hcont_prod
      (fun t ht => mul_ne_zero (hpos t ht).ne' (ne_of_gt (hlogpos t ht)))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

private lemma integral_exp_exp_one_div_mul_log {y η : ℝ} (hy : 0 ≤ y) (hη : 1 ≤ η) :
    (∫ t in Real.exp (Real.exp y)..Real.exp (Real.exp (η * y)),
        1 / (t * Real.log t)) =
      (η - 1) * y := by
  have ha : 1 < Real.exp (Real.exp y) := Real.one_lt_exp_iff.mpr (Real.exp_pos y)
  have hy_le : y ≤ η * y := by nlinarith [hy, hη]
  have hab : Real.exp (Real.exp y) ≤ Real.exp (Real.exp (η * y)) := by
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hy_le)
  rw [integral_one_div_mul_log_of_one_lt ha hab]
  simp [sub_mul]

private lemma exp_decay_eventually_small {C c₀ : ℝ} (hC : 0 < C) (hc₀ : 0 < c₀) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      C * Real.exp (-c₀ * Real.sqrt (Real.exp y)) ≤ (1 / 2 : ℝ) := by
  have htend :
      Filter.Tendsto (fun y : ℝ => C * Real.exp (-c₀ * Real.sqrt (Real.exp y)))
        Filter.atTop (nhds 0) := by
    have hsqrt :
        Filter.Tendsto (fun y : ℝ => Real.sqrt (Real.exp y)) Filter.atTop
          Filter.atTop := by
      exact Real.tendsto_sqrt_atTop.comp Real.tendsto_exp_atTop
    have hneg :
        Filter.Tendsto (fun y : ℝ => -c₀ * Real.sqrt (Real.exp y)) Filter.atTop
          Filter.atBot := by
      exact hsqrt.const_mul_atTop_of_neg (by linarith)
    have hexp :
        Filter.Tendsto (fun y : ℝ => Real.exp (-c₀ * Real.sqrt (Real.exp y)))
          Filter.atTop (nhds 0) := by
      exact Real.tendsto_exp_atBot.comp hneg
    simpa using hexp.const_mul C
  rw [Metric.tendsto_atTop] at htend
  rcases htend (1 / 2) (by norm_num) with ⟨Y, hY⟩
  refine ⟨Y, fun y hy => ?_⟩
  have hdist := hY y hy
  have hlt : C * Real.exp (-c₀ * Real.sqrt (Real.exp y)) < 1 / 2 := by
    simpa [Real.dist_eq, abs_mul, abs_of_pos hC, abs_of_pos (Real.exp_pos _)] using
      hdist
  exact le_of_lt hlt

/-- **Lemma 5.1 (prime-successor mass) — explicit `c₁ = 1/2`.**

For every `B ≥ 2`, for all sufficiently large `y`, every prime `p ≤ y`, and
every `η ≥ B`,
`∑_{exp(exp y) < q ≤ exp(exp(η y)), q ≡ 1 mod p, q prime} 1/q
   ≥ (1/2)(η - 1) y / p`.

Paper §5.2 line 1147-1152: paper applies this with `c₁ = 1/2` (constant from
`sw_reciprocal_AP`). The constant `1/2` is exposed in the type to enable
downstream paper-faithful derivations of the `B/8` bound. -/
lemma prime_successor_mass :
    ∀ B : ℝ, 2 ≤ B →
      ∃ y₀ : ℝ, 0 < y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y →
            ∀ η : ℝ, B ≤ η →
              (∑ q ∈ Finset.filter
                  (fun q => q.Prime ∧ q % p = 1 ∧
                    Real.exp (Real.exp y) < (q : ℝ) ∧
                    (q : ℝ) ≤ Real.exp (Real.exp (η * y)))
                  (Finset.Iic ⌊Real.exp (Real.exp (η * y))⌋₊),
                (1 : ℝ) / (q : ℝ)) ≥ (1/2 : ℝ) * (η - 1) * y / (p : ℝ) := by
  intro B hB
  rcases sw_reciprocal_AP 1 (by norm_num : (0 : ℝ) < 1) with
    ⟨c₀, hc₀, C, hC, hSW⟩
  rcases exp_decay_eventually_small hC hc₀ with ⟨Yerr, hYerr⟩
  refine ⟨max 1 Yerr, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 Yerr)
  intro y hy p hp hp_le_y η hη
  let X : ℝ := Real.exp (Real.exp y)
  let Y : ℝ := Real.exp (Real.exp (η * y))
  let S : ℝ :=
    ∑ q ∈ Finset.filter
      (fun q => q.Prime ∧ q % p = 1 ∧ X < (q : ℝ) ∧ (q : ℝ) ≤ Y)
      (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (q : ℝ)
  let M : ℝ := (1 / (p.totient : ℝ)) * ∫ t in X..Y, 1 / (t * Real.log t)
  let E : ℝ := C * Real.exp (-c₀ * Real.sqrt (Real.log X))
  have hy_ge_one : 1 ≤ y := le_trans (le_max_left 1 Yerr) hy
  have hy_nonneg : 0 ≤ y := by linarith
  have hη_ge_two : 2 ≤ η := le_trans hB hη
  have hη_ge_one : 1 ≤ η := by linarith
  have hX_ge_three : 3 ≤ X := by
    have htwo_le_expy : (2 : ℝ) ≤ Real.exp y := by
      exact le_trans (le_of_lt Real.exp_one_gt_two) (Real.exp_le_exp.mpr hy_ge_one)
    have hthree_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
      nlinarith [Real.add_one_le_exp (2 : ℝ)]
    exact le_trans hthree_le_exp_two (Real.exp_le_exp.mpr htwo_le_expy)
  have hy_le_eta_y : y ≤ η * y := by nlinarith [hy_nonneg, hη_ge_one]
  have hX_le_Y : X ≤ Y := by
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hy_le_eta_y)
  have hp_one : 1 ≤ p := hp.one_le
  have hp_one_lt : 1 < p := hp.one_lt
  have hp_pos_real : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_mod_bound : (p : ℝ) ≤ (Real.log X) ^ (1 : ℝ) := by
    have hy_le_expy : y ≤ Real.exp y := by
      have := Real.add_one_le_exp y
      linarith
    calc
      (p : ℝ) ≤ y := hp_le_y
      _ ≤ Real.exp y := hy_le_expy
      _ = (Real.log X) ^ (1 : ℝ) := by simp [X]
  have hsw := hSW X Y hX_ge_three hX_le_Y p hp_one hp_mod_bound 1 (by simp)
  have hsw' : |S - M| ≤ E := by
    simpa [S, M, E, X, Y, Nat.mod_eq_of_lt hp_one_lt] using hsw
  have hS_lower : M - E ≤ S := by
    have hle := (abs_le.1 hsw').1
    linarith
  have hsmall : E ≤ (1 / 2 : ℝ) := by
    have hy_Yerr : Yerr ≤ y := le_trans (le_max_right 1 Yerr) hy
    simpa [E, X] using hYerr y hy_Yerr
  have hI : (∫ t in X..Y, 1 / (t * Real.log t)) = (η - 1) * y := by
    simpa [X, Y] using integral_exp_exp_one_div_mul_log hy_nonneg hη_ge_one
  have hA_nonneg : 0 ≤ (η - 1) * y := by nlinarith [hη_ge_one, hy_nonneg]
  have hp_sub_pos_real : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp_one_lt
  have hp_sub_le_real : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.sub_le p 1
  have hM_ge : (η - 1) * y / (p : ℝ) ≤ M := by
    calc
      (η - 1) * y / (p : ℝ) ≤ (η - 1) * y / ((p - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hA_nonneg hp_sub_pos_real hp_sub_le_real
      _ = (1 / (p.totient : ℝ)) * ∫ t in X..Y, 1 / (t * Real.log t) := by
        rw [hI, Nat.totient_prime hp]
        ring
      _ = M := rfl
  have hR_ge_one : 1 ≤ (η - 1) * y / (p : ℝ) := by
    have hηm1 : 1 ≤ η - 1 := by linarith
    have hydiv : 1 ≤ y / (p : ℝ) := (one_le_div₀ hp_pos_real).2 hp_le_y
    have hηm1_nonneg : 0 ≤ η - 1 := by linarith
    have hmul : (1 : ℝ) * 1 ≤ (η - 1) * (y / (p : ℝ)) :=
      mul_le_mul hηm1 hydiv (by norm_num) hηm1_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have htarget_le : (1 / 2 : ℝ) * ((η - 1) * y / (p : ℝ)) ≤ M - E := by
    have htmp : (1 / 2 : ℝ) * ((η - 1) * y / (p : ℝ)) ≤
        (η - 1) * y / (p : ℝ) - 1 / 2 := by
      nlinarith [hR_ge_one]
    nlinarith [hM_ge, hsmall]
  have hfinal : (1 / 2 : ℝ) * ((η - 1) * y / (p : ℝ)) ≤ S :=
    le_trans htarget_le hS_lower
  simpa [S, X, Y, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfinal

lemma almostAll_of_forall {P : ℕ → Prop} (h : ∀ n, P n) : almostAll P := by
  unfold almostAll
  have hzero : (fun x : ℝ =>
      ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x) = fun _ => 0 := by
    funext x
    have hempty : {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} = (∅ : Set ℕ) := by
      ext n
      simp [h n]
    simp [hempty]
  rw [hzero]
  exact tendsto_const_nhds

private lemma greedy_h_chain_large_epsilon :
    ∀ ε : ℝ, (1 / 2 : ℝ) ≤ ε →
      almostAll (fun n => (hChain n : ℝ) ≥ (1 / 2 - ε) * (logStar n : ℝ)) := by
  intro ε hε
  apply almostAll_of_forall
  intro n
  have hh : (0 : ℝ) ≤ (hChain n : ℝ) := by positivity
  have hlog : (0 : ℝ) ≤ (logStar n : ℝ) := by positivity
  have hcoef : (1 / 2 - ε : ℝ) ≤ 0 := by linarith
  have hrhs : (1 / 2 - ε) * (logStar n : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoef hlog
  exact le_trans hrhs hh

/-- Auxiliary deterministic condition: `n` contains a prime chain of length at least `R`. -/
private def HasPrimeChainLengthAtLeast (R n : ℕ) : Prop :=
  ∃ ps : List ℕ, IsPrimeChain n ps ∧ R ≤ ps.length

private lemma IsPrimeChain.length_le_self {n : ℕ} (hn : n ≠ 0) {ps : List ℕ}
    (hps : IsPrimeChain n ps) : ps.length ≤ n := by
  rcases hps with ⟨hprime, hpair, _hmod⟩
  have hnodup : ps.Nodup := hpair.nodup
  rw [← List.toFinset_card_of_nodup hnodup]
  have hsub : ps.toFinset ⊆ Finset.Icc 1 n := by
    intro p hp
    rw [List.mem_toFinset] at hp
    simpa [Finset.mem_Icc] using
      (show 1 ≤ p ∧ p ≤ n from
        ⟨(hprime p hp).1.one_le, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hprime p hp).2⟩)
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma hChain_ge_of_hasPrimeChainLengthAtLeast {R n : ℕ} (hn : n ≠ 0)
    (hR : HasPrimeChainLengthAtLeast R n) : R ≤ hChain n := by
  rcases hR with ⟨ps, hps, hRle⟩
  have hbound : BddAbove {ℓ : ℕ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ} := by
    refine ⟨n, ?_⟩
    intro ℓ hℓ
    rcases hℓ with ⟨qs, hqs, rfl⟩
    exact hqs.length_le_self hn
  have hmem : ps.length ∈ {ℓ : ℕ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ} :=
    ⟨ps, hps, rfl⟩
  have hle : ps.length ≤ hChain n := by
    dsimp [hChain]
    exact le_csSup hbound hmem
  exact hRle.trans hle

/-- A pointwise lower-bound witness for the backwards construction. -/
private def GoodLowerPrimeChain (ε : ℝ) (n : ℕ) : Prop :=
  ∃ R : ℕ, n ≠ 0 ∧ HasPrimeChainLengthAtLeast R n ∧
    (1 / 2 - ε) * (logStar (n : ℝ) : ℝ) ≤ (R : ℝ)

private lemma lower_bound_of_good_prime_chain {ε : ℝ} {n : ℕ}
    (hgood : GoodLowerPrimeChain ε n) :
    (hChain n : ℝ) ≥ (1 / 2 - ε) * (logStar (n : ℝ) : ℝ) := by
  rcases hgood with ⟨R, hn, hchain, hR⟩
  have hnat : R ≤ hChain n := hChain_ge_of_hasPrimeChainLengthAtLeast hn hchain
  have hreal : (R : ℝ) ≤ (hChain n : ℝ) := by exact_mod_cast hnat
  exact hR.trans hreal

private lemma lower_bound_from_good_prime_chains {ε : ℝ}
    (hgood : almostAll (GoodLowerPrimeChain ε)) :
    almostAll (fun n => (hChain n : ℝ) ≥ (1 / 2 - ε) * (logStar n : ℝ)) :=
  almostAll_mono hgood (fun _ hn => lower_bound_of_good_prime_chain hn)

/-- The paper §5.2 window parameter `B = L^2`, where `L = log_* x`. -/
private noncomputable def lowerHWindowB (L : ℕ) : ℝ :=
  (L : ℝ) ^ 2

/-- The initial tower index `m₀ = ⌊sqrt L⌋` used in the lower-bound construction. -/
private noncomputable def lowerHWindowM0 (L : ℕ) : ℕ :=
  ⌊Real.sqrt (L : ℝ)⌋₊

/-- The zero-indexed tower index `m_j = m₀ + 2j` for the `h` lower-bound stages. -/
private noncomputable def lowerHWindowM (L j : ℕ) : ℕ :=
  lowerHWindowM0 L + 2 * j

/-- The tower scale `y_j = T_{m_j} / B` from paper §5.2. -/
private noncomputable def lowerHWindowY (L j : ℕ) : ℝ :=
  tower (lowerHWindowM L j) / lowerHWindowB L

/-- The number of greedy prime-successor stages available at scale `L`. -/
private noncomputable def lowerHChainLength (L : ℕ) : ℕ :=
  (L - lowerHWindowM0 L - 2) / 2

private lemma lowerHChainLength_le (L : ℕ) : lowerHChainLength L ≤ L := by
  dsimp [lowerHChainLength]
  omega

private lemma lowerHWindowM_add_four_le_of_mem_range {L j : ℕ}
    (hj : j ∈ Finset.range (lowerHChainLength L)) :
    lowerHWindowM L j + 4 ≤ L := by
  dsimp [lowerHChainLength, lowerHWindowM] at hj ⊢
  rw [Finset.mem_range] at hj
  omega

private lemma exp_nat_le_tower (m : ℕ) : Real.exp (m : ℝ) ≤ tower m := by
  induction m with
  | zero =>
      norm_num [tower]
  | succ m _ =>
      change Real.exp ((m + 1 : ℕ) : ℝ) ≤ Real.exp (tower m)
      apply Real.exp_le_exp.mpr
      simpa [Nat.cast_add, Nat.cast_one] using tower_ge m

private lemma lowerHWindowY_zero_tendsto_atTop :
    Filter.Tendsto (fun L : ℕ => lowerHWindowY L 0) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro A
  have hsqrt : Filter.Tendsto (fun L : ℕ => Real.sqrt (L : ℝ)) Filter.atTop
      Filter.atTop := by
    exact Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbase : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ 4) Filter.atTop
      Filter.atTop :=
    Real.tendsto_exp_div_pow_atTop 4
  have hcomp : Filter.Tendsto (fun L : ℕ => Real.exp (Real.sqrt (L : ℝ)) /
      (Real.sqrt (L : ℝ)) ^ 4) Filter.atTop Filter.atTop := by
    simpa [Function.comp_def] using hbase.comp hsqrt
  have hscaled : Filter.Tendsto (fun L : ℕ => Real.exp (-1) *
      (Real.exp (Real.sqrt (L : ℝ)) / (Real.sqrt (L : ℝ)) ^ 4))
      Filter.atTop Filter.atTop := by
    exact hcomp.const_mul_atTop (Real.exp_pos (-1))
  filter_upwards [hscaled.eventually_ge_atTop A] with L hA
  let s : ℝ := Real.sqrt (L : ℝ)
  let k : ℕ := ⌊s⌋₊
  have hfloor : s - 1 ≤ (k : ℝ) := le_of_lt (Nat.sub_one_lt_floor s)
  have hnum : Real.exp (-1) * Real.exp s ≤ tower k := by
    calc
      Real.exp (-1) * Real.exp s = Real.exp (s - 1) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr hfloor
      _ ≤ tower k := exp_nat_le_tower k
  have hdeneq : s ^ 4 = (L : ℝ) ^ 2 := by
    have hs : s ^ 2 = (L : ℝ) := by
      dsimp [s]
      exact Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (s ^ 2)]
  have hle :
      Real.exp (-1) *
          (Real.exp (Real.sqrt (L : ℝ)) / (Real.sqrt (L : ℝ)) ^ 4) ≤
        lowerHWindowY L 0 := by
    calc
      Real.exp (-1) *
          (Real.exp (Real.sqrt (L : ℝ)) / (Real.sqrt (L : ℝ)) ^ 4)
          = (Real.exp (-1) * Real.exp s) / s ^ 4 := by
            dsimp [s]
            ring
      _ ≤ tower k / s ^ 4 := div_le_div_of_nonneg_right hnum (by positivity)
      _ = lowerHWindowY L 0 := by
            simp [lowerHWindowY, lowerHWindowM, lowerHWindowM0, lowerHWindowB, s, k,
              hdeneq]
  exact hA.trans hle

/-- Candidate prime successors in the paper's set `Q_j(p_j)`.

This is the finite interval
`exp(exp y_j) < q ≤ exp(exp((B/2)y_j))`, restricted to primes `q ≡ 1 mod p`.
-/
private noncomputable def lowerHSuccessorCandidates (L j p : ℕ) : Finset ℕ := by
  classical
  exact
    Finset.filter
      (fun q : ℕ =>
        q.Prime ∧ q % p = 1 ∧
          Real.exp (Real.exp (lowerHWindowY L j)) < (q : ℝ) ∧
          (q : ℝ) ≤
            Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j)))
      (Finset.Iic
        ⌊Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j))⌋₊)

/-- The least element of a finite set of natural numbers, if it is nonempty. -/
private noncomputable def finsetLeastNat? (s : Finset ℕ) : Option ℕ := by
  classical
  exact if h : s.Nonempty then some (s.min' h) else none

/-- Selected primes below the first tower scale. -/
private noncomputable def lowerHInitialSelectedPrimes (L n : ℕ) : Finset ℕ := by
  classical
  exact
    Finset.filter
      (fun p : ℕ => p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ lowerHWindowY L 0)
      (Finset.Iic ⌊lowerHWindowY L 0⌋₊)

/-- Selected candidate successors from the stage window `Q_j(p)`. -/
private noncomputable def lowerHSelectedSuccessors (L j p n : ℕ) : Finset ℕ := by
  classical
  exact Finset.filter (fun q : ℕ => q ∣ n) (lowerHSuccessorCandidates L j p)

/-- The deterministic least-prime greedy construction from paper §5.2. -/
private noncomputable def lowerHGreedyPrime? (L n : ℕ) : ℕ → Option ℕ
  | 0 => finsetLeastNat? (lowerHInitialSelectedPrimes L n)
  | j + 1 =>
      match lowerHGreedyPrime? L n j with
      | none => none
      | some p => finsetLeastNat? (lowerHSelectedSuccessors L j p n)

/-- Initial failure for the paper §5.2 greedy construction: no selected prime appears
below the first tower scale. -/
private noncomputable def LowerHInitialFailure (L n : ℕ) : Prop :=
  lowerHGreedyPrime? L n 0 = none

/-- Stage failure for the paper §5.2 greedy construction: the deterministic current
prime `p_j` exists, but no selected prime in `Q_j(p_j)` is available as a successor. -/
private noncomputable def LowerHStageFailure (L j n : ℕ) : Prop :=
  ∃ p : ℕ,
    lowerHGreedyPrime? L n j = some p ∧
      finsetLeastNat? (lowerHSelectedSuccessors L j p n) = none

private lemma finsetLeastNat?_mem {s : Finset ℕ} {p : ℕ}
    (hp : finsetLeastNat? s = some p) : p ∈ s := by
  classical
  by_cases hne : s.Nonempty
  · simp [finsetLeastNat?, hne] at hp
    subst p
    exact Finset.min'_mem s hne
  · simp [finsetLeastNat?, hne] at hp

private lemma lowerHGreedyPrime?_prime_dvd {L n j p : ℕ}
    (hp : lowerHGreedyPrime? L n j = some p) : p.Prime ∧ p ∣ n := by
  induction j generalizing p with
  | zero =>
      have hmem : p ∈ lowerHInitialSelectedPrimes L n := finsetLeastNat?_mem hp
      simp [lowerHInitialSelectedPrimes] at hmem
      exact ⟨hmem.2.1, hmem.2.2.1⟩
  | succ j ih =>
      cases hp₀ : lowerHGreedyPrime? L n j with
      | none =>
          simp [lowerHGreedyPrime?, hp₀] at hp
      | some p₀ =>
          have hmem : p ∈ lowerHSelectedSuccessors L j p₀ n := by
            exact finsetLeastNat?_mem (by simpa [lowerHGreedyPrime?, hp₀] using hp)
          simp [lowerHSelectedSuccessors, lowerHSuccessorCandidates] at hmem
          exact ⟨hmem.1.2.1, hmem.2⟩

private lemma lowerHGreedyPrime?_succ_mem {L n j p q : ℕ}
    (hp : lowerHGreedyPrime? L n j = some p)
    (hq : lowerHGreedyPrime? L n (j + 1) = some q) :
    q ∈ lowerHSelectedSuccessors L j p n := by
  unfold lowerHGreedyPrime? at hq
  rw [hp] at hq
  exact finsetLeastNat?_mem hq

private lemma prime_lt_of_mod_eq_one {p q : ℕ} (_hp : p.Prime) (hq : q.Prime)
    (hmod : q % p = 1) : p < q := by
  by_contra hnot
  have hqle : q ≤ p := le_of_not_gt hnot
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst q
    simp at hmod
  have hq_lt_p : q < p := lt_of_le_of_ne hqle hq_ne_p
  have hmod' : q % p = q := Nat.mod_eq_of_lt hq_lt_p
  have hq_one : q = 1 := by
    rw [hmod'] at hmod
    omega
  exact hq.ne_one hq_one

private lemma lowerHGreedyPrime?_succ_lt {L n j p q : ℕ}
    (hp : lowerHGreedyPrime? L n j = some p)
    (hq : lowerHGreedyPrime? L n (j + 1) = some q) : p < q := by
  have hpprime : p.Prime := (lowerHGreedyPrime?_prime_dvd hp).1
  have hqprime : q.Prime := (lowerHGreedyPrime?_prime_dvd hq).1
  have hmem := lowerHGreedyPrime?_succ_mem hp hq
  have hmod : q % p = 1 := by
    simp [lowerHSelectedSuccessors, lowerHSuccessorCandidates] at hmem
    exact hmem.1.2.2.1
  exact prime_lt_of_mod_eq_one hpprime hqprime hmod

private lemma lowerHGreedyPrime?_succ_mod {L n j p q : ℕ}
    (hp : lowerHGreedyPrime? L n j = some p)
    (hq : lowerHGreedyPrime? L n (j + 1) = some q) : q % p = 1 := by
  have hmem := lowerHGreedyPrime?_succ_mem hp hq
  simp [lowerHSelectedSuccessors, lowerHSuccessorCandidates] at hmem
  exact hmem.1.2.2.1

private lemma lowerHGreedyPrime?_exists_succ_of_not_stage_failure {L n j p : ℕ}
    (hp : lowerHGreedyPrime? L n j = some p) (hnot : ¬ LowerHStageFailure L j n) :
    ∃ q : ℕ, lowerHGreedyPrime? L n (j + 1) = some q := by
  classical
  have hleast_ne :
      finsetLeastNat? (lowerHSelectedSuccessors L j p n) ≠ none := by
    intro hnone
    exact hnot ⟨p, hp, hnone⟩
  unfold lowerHGreedyPrime?
  rw [hp]
  cases hleast : finsetLeastNat? (lowerHSelectedSuccessors L j p n) with
  | none => exact (hleast_ne hleast).elim
  | some q =>
      refine ⟨q, ?_⟩
      simpa [lowerHGreedyPrime?, hp] using hleast

private lemma hasPrimeChainLengthAtLeast_of_greedy_successes {L n R : ℕ}
    (hinit : ¬ LowerHInitialFailure L n)
    (hstages : ∀ j ∈ Finset.range R, ¬ LowerHStageFailure L j n) :
    HasPrimeChainLengthAtLeast R n := by
  classical
  have hsome_le : ∀ j : ℕ, j ≤ R → ∃ p : ℕ, lowerHGreedyPrime? L n j = some p := by
    intro j hj
    induction j with
    | zero =>
        have hne : lowerHGreedyPrime? L n 0 ≠ none := by
          simpa [LowerHInitialFailure] using hinit
        cases h0 : lowerHGreedyPrime? L n 0 with
        | none => exact (hne h0).elim
        | some p => exact ⟨p, rfl⟩
    | succ j ih =>
        have hjR : j < R := Nat.lt_of_succ_le hj
        rcases ih (Nat.le_of_lt hjR) with ⟨p, hp⟩
        exact lowerHGreedyPrime?_exists_succ_of_not_stage_failure hp
          (hstages j (Finset.mem_range.mpr hjR))
  let pval : ℕ → ℕ := fun j =>
    if hj : j < R then Classical.choose (hsome_le j hj.le) else 0
  have hpval : ∀ {j : ℕ}, j < R → lowerHGreedyPrime? L n j = some (pval j) := by
    intro j hj
    dsimp [pval]
    rw [dif_pos hj]
    exact Classical.choose_spec (hsome_le j hj.le)
  have hpval_lt_succ : ∀ j : ℕ, j + 1 < R → pval j < pval (j + 1) := by
    intro j hj
    have hj0 : j < R := Nat.lt_trans (Nat.lt_succ_self j) hj
    exact lowerHGreedyPrime?_succ_lt (hpval hj0) (hpval hj)
  have hpval_lt_of_lt : ∀ {i j : ℕ}, i < j → j < R → pval i < pval j := by
    intro i j hij hjR
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases h : i = j
        · subst i
          exact hpval_lt_succ j hjR
        · have hij' : i < j := by omega
          have hj_lt_R : j < R := Nat.lt_trans (Nat.lt_succ_self j) hjR
          exact lt_trans (ih hij' hj_lt_R) (hpval_lt_succ j hjR)
  let ps : List ℕ := List.ofFn (fun i : Fin R => pval i)
  refine ⟨ps, ?_, by simp [ps]⟩
  constructor
  · intro p hp
    simp [ps, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact lowerHGreedyPrime?_prime_dvd (hpval i.isLt)
  constructor
  · simp [ps, List.pairwise_ofFn]
    intro i j hij
    exact hpval_lt_of_lt hij j.isLt
  · intro i hi
    have hiR : i.val < R := by
      simpa [ps] using i.isLt
    have hi1R : i.val + 1 < R := by
      simpa [ps] using hi
    have hcur := hpval hiR
    have hnext := hpval hi1R
    have hmod := lowerHGreedyPrime?_succ_mod hcur hnext
    simpa [ps] using hmod

private lemma nat_cast_div_two_sub_one_le (a : ℕ) :
    (a : ℝ) / 2 - 1 ≤ ((a / 2 : ℕ) : ℝ) := by
  have h : a ≤ 2 * (a / 2) + 1 := by omega
  have hr : (a : ℝ) ≤ 2 * ((a / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
  linarith

private lemma sqrt_le_mul_self_of_inv_sq_le {δ L : ℝ} (hδ : 0 < δ) (hLnonneg : 0 ≤ L)
    (hL : (1 / δ) ^ 2 ≤ L) : Real.sqrt L ≤ δ * L := by
  rw [Real.sqrt_le_left]
  · have hmul := mul_le_mul_of_nonneg_left hL (sq_nonneg δ)
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hone : 1 ≤ δ ^ 2 * L := by
      field_simp [hδne] at hmul
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
    nlinarith [hone, hLnonneg]
  · positivity

private lemma exists_iteratedLog_le_exp_one_of_le_tower_le (K : ℕ) {x : ℝ}
    (hx : x ≤ tower K) : ∃ k : ℕ, k ≤ K ∧ iteratedLog k x ≤ Real.exp 1 := by
  induction K generalizing x with
  | zero =>
      exact ⟨0, le_rfl, by simpa only [iteratedLog, tower] using hx⟩
  | succ K ih =>
      by_cases hx0 : x ≤ Real.exp 1
      · exact ⟨0, Nat.zero_le _, by simpa [iteratedLog] using hx0⟩
      · have hxpos : 0 < x := lt_trans (Real.exp_pos 1) (lt_of_not_ge hx0)
        have hlog_le : Real.log x ≤ tower K := by
          have hx_le_exp : x ≤ Real.exp (tower K) := by simpa [tower] using hx
          exact (Real.log_le_iff_le_exp hxpos).2 hx_le_exp
        rcases ih hlog_le with ⟨k, hk_le, hk⟩
        exact ⟨k + 1, Nat.succ_le_succ hk_le, by simpa [iteratedLog_log] using hk⟩

theorem logStar_le_of_le_tower (K : ℕ) {x : ℝ} (hx : x ≤ tower K) :
    logStar x ≤ K := by
  classical
  unfold logStar
  let h : ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 := exists_iteratedLog_le_exp_one x
  rw [dif_pos h]
  rcases exists_iteratedLog_le_exp_one_of_le_tower_le K hx with ⟨k, hk_le, hk⟩
  exact (Nat.find_min' h hk).trans hk_le

theorem logStar_nat_le_logStar_of_le_floor {x : ℝ} {n : ℕ} (hx_nonneg : 0 ≤ x)
    (hnx : n ≤ ⌊x⌋₊) : logStar (n : ℝ) ≤ logStar x := by
  have hn_floor : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnx
  have hn_le_x : (n : ℝ) ≤ x := hn_floor.trans (Nat.floor_le hx_nonneg)
  exact logStar_le_of_le_tower (logStar x) (hn_le_x.trans (self_le_tower_logStar x))

private lemma lowerHChainLength_eventually_ge (ε : ℝ) (hε : 0 < ε)
    (hε_lt : ε < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      (1 / 2 - ε) * (L : ℝ) ≤ (lowerHChainLength L : ℝ) := by
  classical
  let L₀ : ℕ := max 16 (max ⌈(1 / (ε / 2)) ^ 2⌉₊ ⌈4 / ε⌉₊)
  refine ⟨L₀, ?_⟩
  intro L hL
  let m₀ : ℕ := lowerHWindowM0 L
  have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
  have hceil_sq : ⌈(1 / (ε / 2)) ^ 2⌉₊ ≤ L := by
    exact (le_max_left _ _).trans (le_max_right _ _ |>.trans hL)
  have hceil_four : ⌈4 / ε⌉₊ ≤ L := by
    exact (le_max_right _ _).trans (le_max_right _ _ |>.trans hL)
  have hL_ge_sq : (1 / (ε / 2)) ^ 2 ≤ (L : ℝ) := (Nat.ceil_le).1 hceil_sq
  have hL_ge_four : 4 / ε ≤ (L : ℝ) := (Nat.ceil_le).1 hceil_four
  have hδ : 0 < ε / 2 := by positivity
  have hm₀_le_sqrt : (m₀ : ℝ) ≤ Real.sqrt (L : ℝ) := by
    dsimp [m₀, lowerHWindowM0]
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrt_le : Real.sqrt (L : ℝ) ≤ (ε / 2) * (L : ℝ) :=
    sqrt_le_mul_self_of_inv_sq_le hδ hL_nonneg hL_ge_sq
  have hm₀_le : (m₀ : ℝ) ≤ (ε / 2) * (L : ℝ) := hm₀_le_sqrt.trans hsqrt_le
  have htwo_le : (2 : ℝ) ≤ (ε / 2) * (L : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hL_ge_four (by positivity : 0 ≤ ε / 2)
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp [hεne] at hmul
    linarith
  have hm₀_add_two_real : ((m₀ + 2 : ℕ) : ℝ) ≤ (L : ℝ) := by
    have hε_le_one : ε ≤ 1 := by linarith
    norm_num
    nlinarith [hm₀_le, htwo_le, hε_le_one, hL_nonneg]
  have hm₀_add_two : m₀ + 2 ≤ L := by exact_mod_cast hm₀_add_two_real
  have hm₀_le_L : m₀ ≤ L := by omega
  have htwo_le_sub : 2 ≤ L - m₀ := by omega
  have hcast :
      (((L - m₀ - 2 : ℕ) : ℝ)) = (L : ℝ) - (m₀ : ℝ) - 2 := by
    rw [show L - m₀ - 2 = L - (m₀ + 2) by omega]
    rw [Nat.cast_sub hm₀_add_two]
    push_cast
    ring
  have hdiv :
      ((L - m₀ - 2 : ℕ) : ℝ) / 2 - 1 ≤
        (((L - m₀ - 2) / 2 : ℕ) : ℝ) :=
    nat_cast_div_two_sub_one_le (L - m₀ - 2)
  have hmain :
      (1 / 2 - ε) * (L : ℝ) ≤ ((L - m₀ - 2 : ℕ) : ℝ) / 2 - 1 := by
    rw [hcast]
    nlinarith [hm₀_le, htwo_le]
  exact hmain.trans (by simpa [lowerHChainLength, m₀] using hdiv)

private lemma card_bad_le_one_add_failure_sum {N R : ℕ} {P I : ℕ → Prop}
    {S : ℕ → ℕ → Prop}
    (hsub : ∀ n : ℕ, n ≤ N → ¬ P n →
      n = 0 ∨ I n ∨ ∃ j : ℕ, j ∈ Finset.range R ∧ S j n) :
    Nat.card {n : ℕ | n ≤ N ∧ ¬ P n} ≤
      1 + Nat.card {n : ℕ | n ≤ N ∧ I n} +
        ∑ j ∈ Finset.range R, Nat.card {n : ℕ | n ≤ N ∧ S j n} := by
  classical
  let badF : Finset ℕ := Finset.filter (fun n => ¬ P n) (Finset.Iic N)
  let zeroF : Finset ℕ := {0}
  let initF : Finset ℕ := Finset.filter I (Finset.Iic N)
  let stageF : ℕ → Finset ℕ := fun j => Finset.filter (S j) (Finset.Iic N)
  let stageU : Finset ℕ := (Finset.range R).biUnion stageF
  let U : Finset ℕ := zeroF ∪ initF ∪ stageU
  have hbad_subset : badF ⊆ U := by
    intro n hn
    simp [badF] at hn
    rcases hsub n hn.1 hn.2 with hzero | hinit | hstage
    · simp [U, zeroF, hzero]
    · simp [U, initF, hn.1, hinit]
    · rcases hstage with ⟨j, hj, hSj⟩
      simp [U, stageU, stageF]
      right
      right
      exact ⟨j, Finset.mem_range.mp hj, hn.1, hSj⟩
  have hcard_fin :
      badF.card ≤ 1 + initF.card + ∑ j ∈ Finset.range R, (stageF j).card := by
    calc
      badF.card ≤ U.card := Finset.card_le_card hbad_subset
      _ ≤ (zeroF ∪ initF).card + stageU.card := by
        simpa [U, Nat.add_assoc] using Finset.card_union_le (zeroF ∪ initF) stageU
      _ ≤ (zeroF.card + initF.card) + stageU.card := by
        have h := Nat.add_le_add_right (Finset.card_union_le zeroF initF) stageU.card
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      _ ≤ (1 + initF.card) + ∑ j ∈ Finset.range R, (stageF j).card := by
        have hstageU : stageU.card ≤ ∑ j ∈ Finset.range R, (stageF j).card := by
          simpa [stageU] using (Finset.card_biUnion_le : stageU.card ≤
            ∑ j ∈ Finset.range R, (stageF j).card)
        have h := Nat.add_le_add_left hstageU (zeroF.card + initF.card)
        simpa [zeroF, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      _ = 1 + initF.card + ∑ j ∈ Finset.range R, (stageF j).card := by
        simp [Nat.add_assoc]
  have hbad_card :
      Nat.card {n : ℕ | n ≤ N ∧ ¬ P n} = badF.card :=
    Nat.subtype_card badF (by intro n; simp [badF])
  have hinit_card :
      Nat.card {n : ℕ | n ≤ N ∧ I n} = initF.card :=
    Nat.subtype_card initF (by intro n; simp [initF, and_comm])
  have hstage_card : ∀ j : ℕ,
      Nat.card {n : ℕ | n ≤ N ∧ S j n} = (stageF j).card := by
    intro j
    exact Nat.subtype_card (stageF j)
      (by intro n; simp [stageF, and_comm])
  rw [hbad_card, hinit_card]
  have hsum_eq :
      (∑ j ∈ Finset.range R, (stageF j).card) =
        ∑ j ∈ Finset.range R, Nat.card {n : ℕ | n ≤ N ∧ S j n} := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact (hstage_card j).symm
  calc
    badF.card ≤ 1 + initF.card + ∑ j ∈ Finset.range R, (stageF j).card := hcard_fin
    _ = 1 + initF.card + ∑ j ∈ Finset.range R, Nat.card {n : ℕ | n ≤ N ∧ S j n} := by
      rw [hsum_eq]

/-- Prime cutoff for the stage-`j` CRT window in the `h` lower-bound construction. -/
private noncomputable def lowerHStageCutoff (L j : ℕ) : ℕ :=
  ⌊Real.exp
    (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j))⌋₊

/-- Finite residue/product-model failure probability for one `h`-stage.

This packages the independent divisibility model over one complete CRT period
`primorial (lowerHStageCutoff L j)`.  Bounding this quantity is the paper §5.2
product-model step; `stage_h_crt_transfer` below then turns it into integer density. -/
private noncomputable def lowerHStageFailureResidueProb (L j : ℕ) : ℝ :=
  (Nat.card
      {r : Fin (primorial (lowerHStageCutoff L j)) //
        LowerHStageFailure L j r.val} : ℝ) /
    (primorial (lowerHStageCutoff L j) : ℝ)

lemma primorial_pos (P : ℕ) : 0 < primorial P := by
  unfold primorial
  exact Finset.prod_pos (by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.pos)

lemma prime_dvd_primorial_of_le {p P : ℕ} (hp : p.Prime) (hle : p ≤ P) :
    p ∣ primorial P := by
  unfold primorial
  exact Finset.dvd_prod_of_mem _ (by simp [hp, hle])

private lemma dvd_iff_of_mod_primorial_eq {P q n n' : ℕ} (hqprime : q.Prime)
    (hqle : q ≤ P) (hmod : n % primorial P = n' % primorial P) :
    q ∣ n ↔ q ∣ n' := by
  have hmodeq : n ≡ n' [MOD primorial P] := by
    simpa [Nat.ModEq] using hmod
  exact hmodeq.dvd_iff (prime_dvd_primorial_of_le hqprime hqle)

private lemma self_le_exp_exp_half (t : ℝ) : t ≤ Real.exp (Real.exp (t / 2)) := by
  have h1 : t ≤ Real.exp (t / 2) := by
    have h := (Real.two_mul_le_exp (x := t / 2))
    nlinarith
  have h2 : Real.exp (t / 2) ≤ Real.exp (Real.exp (t / 2)) := by
    apply Real.exp_le_exp.mpr
    have h := Real.add_one_le_exp (t / 2)
    linarith
  exact h1.trans h2

private lemma lowerHStageExponent_eq {L j : ℕ} (hBne : lowerHWindowB L ≠ 0) :
    (lowerHWindowB L / 2) * lowerHWindowY L j = tower (lowerHWindowM L j) / 2 := by
  unfold lowerHWindowY
  field_simp [hBne]

private lemma lowerHStageCutoff_mono_right {L k j : ℕ}
    (hB : 2 ≤ lowerHWindowB L) (hkj : k ≤ j) :
    lowerHStageCutoff L k ≤ lowerHStageCutoff L j := by
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  apply Real.exp_le_exp.mpr
  have hBne : lowerHWindowB L ≠ 0 := by linarith
  rw [lowerHStageExponent_eq (L := L) (j := k) hBne,
    lowerHStageExponent_eq (L := L) (j := j) hBne]
  have hm : lowerHWindowM L k ≤ lowerHWindowM L j := by
    simp [lowerHWindowM]
    omega
  have htower : tower (lowerHWindowM L k) ≤ tower (lowerHWindowM L j) :=
    (strictMono_nat_of_lt_succ tower_lt_succ).monotone hm
  linarith

private lemma lowerHInitialSelectedPrime_le_cutoff {L j n q : ℕ}
    (hB : 2 ≤ lowerHWindowB L) (hq : q ∈ lowerHInitialSelectedPrimes L n) :
    q ≤ lowerHStageCutoff L j := by
  rw [lowerHInitialSelectedPrimes] at hq
  simp only [Finset.mem_filter, Finset.mem_Iic] at hq
  rcases hq with ⟨_hqfloor, _hqprime, _hqdiv, hqY⟩
  have hBne : lowerHWindowB L ≠ 0 := by linarith
  have hBge1 : (1 : ℝ) ≤ lowerHWindowB L := by linarith
  have hm : lowerHWindowM L 0 ≤ lowerHWindowM L j := by
    simp [lowerHWindowM]
  have htower_mono : tower (lowerHWindowM L 0) ≤ tower (lowerHWindowM L j) :=
    (strictMono_nat_of_lt_succ tower_lt_succ).monotone hm
  have hy0_le_tower : lowerHWindowY L 0 ≤ tower (lowerHWindowM L j) := by
    unfold lowerHWindowY
    exact (div_le_self (tower_pos _).le hBge1).trans htower_mono
  have hend : tower (lowerHWindowM L j) ≤
      Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j)) := by
    rw [lowerHStageExponent_eq (L := L) (j := j) hBne]
    exact self_le_exp_exp_half _
  exact Nat.le_floor (hqY.trans (hy0_le_tower.trans hend))

private lemma lowerHSuccessorCandidate_le_cutoff {L k j p q : ℕ}
    (hB : 2 ≤ lowerHWindowB L) (hkj : k ≤ j)
    (hq : q ∈ lowerHSuccessorCandidates L k p) :
    q ≤ lowerHStageCutoff L j := by
  rw [lowerHSuccessorCandidates] at hq
  simp only [Finset.mem_filter, Finset.mem_Iic] at hq
  have hqk : q ≤ lowerHStageCutoff L k := by
    simpa [lowerHStageCutoff] using hq.1
  exact hqk.trans (lowerHStageCutoff_mono_right hB hkj)

private lemma lowerHInitialSelectedPrimes_eq_of_mod {L j n n' : ℕ}
    (hB : 2 ≤ lowerHWindowB L)
    (hmod : n % primorial (lowerHStageCutoff L j) =
      n' % primorial (lowerHStageCutoff L j)) :
    lowerHInitialSelectedPrimes L n = lowerHInitialSelectedPrimes L n' := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    rw [lowerHInitialSelectedPrimes] at hq ⊢
    simp only [Finset.mem_filter, Finset.mem_Iic] at hq ⊢
    rcases hq with ⟨hqfloor, hqprime, hqdiv, hqY⟩
    have hqmem : q ∈ lowerHInitialSelectedPrimes L n := by
      rw [lowerHInitialSelectedPrimes]
      simp [hqfloor, hqprime, hqdiv, hqY]
    have hqle := lowerHInitialSelectedPrime_le_cutoff (L := L) (j := j) hB hqmem
    exact ⟨hqfloor, hqprime, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mp hqdiv, hqY⟩
  · intro hq
    rw [lowerHInitialSelectedPrimes] at hq ⊢
    simp only [Finset.mem_filter, Finset.mem_Iic] at hq ⊢
    rcases hq with ⟨hqfloor, hqprime, hqdiv, hqY⟩
    have hqmem : q ∈ lowerHInitialSelectedPrimes L n' := by
      rw [lowerHInitialSelectedPrimes]
      simp [hqfloor, hqprime, hqdiv, hqY]
    have hqle := lowerHInitialSelectedPrime_le_cutoff (L := L) (j := j) hB hqmem
    exact ⟨hqfloor, hqprime, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mpr hqdiv, hqY⟩

private lemma lowerHSelectedSuccessors_eq_of_mod {L k j p n n' : ℕ}
    (hB : 2 ≤ lowerHWindowB L) (hkj : k ≤ j)
    (hmod : n % primorial (lowerHStageCutoff L j) =
      n' % primorial (lowerHStageCutoff L j)) :
    lowerHSelectedSuccessors L k p n = lowerHSelectedSuccessors L k p n' := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    rw [lowerHSelectedSuccessors] at hq ⊢
    simp only [Finset.mem_filter] at hq ⊢
    rcases hq with ⟨hqcand, hqdiv⟩
    have hqcand' := hqcand
    rw [lowerHSuccessorCandidates] at hqcand'
    simp only [Finset.mem_filter, Finset.mem_Iic] at hqcand'
    have hqprime : q.Prime := hqcand'.2.1
    have hqle := lowerHSuccessorCandidate_le_cutoff (L := L) (k := k) (j := j)
      (p := p) hB hkj hqcand
    exact ⟨hqcand, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mp hqdiv⟩
  · intro hq
    rw [lowerHSelectedSuccessors] at hq ⊢
    simp only [Finset.mem_filter] at hq ⊢
    rcases hq with ⟨hqcand, hqdiv⟩
    have hqcand' := hqcand
    rw [lowerHSuccessorCandidates] at hqcand'
    simp only [Finset.mem_filter, Finset.mem_Iic] at hqcand'
    have hqprime : q.Prime := hqcand'.2.1
    have hqle := lowerHSuccessorCandidate_le_cutoff (L := L) (k := k) (j := j)
      (p := p) hB hkj hqcand
    exact ⟨hqcand, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mpr hqdiv⟩

lemma lowerHGreedyPrime?_eq_of_mod {L j k n n' : ℕ}
    (hB : 2 ≤ lowerHWindowB L) (hkj : k ≤ j)
    (hmod : n % primorial (lowerHStageCutoff L j) =
      n' % primorial (lowerHStageCutoff L j)) :
    lowerHGreedyPrime? L n k = lowerHGreedyPrime? L n' k := by
  induction k with
  | zero =>
      simp [lowerHGreedyPrime?, lowerHInitialSelectedPrimes_eq_of_mod hB hmod]
  | succ k ih =>
      have hk_le_j : k ≤ j := Nat.le_of_succ_le hkj
      have ih' := ih hk_le_j
      rw [lowerHGreedyPrime?, lowerHGreedyPrime?, ih']
      cases hgp : lowerHGreedyPrime? L n' k with
      | none => rfl
      | some p =>
          simp [lowerHSelectedSuccessors_eq_of_mod (L := L) (k := k) (j := j)
            (p := p) hB hk_le_j hmod]

private lemma LowerHStageFailure_iff_of_mod {L j n n' : ℕ}
    (hB : 2 ≤ lowerHWindowB L)
    (hmod : n % primorial (lowerHStageCutoff L j) =
      n' % primorial (lowerHStageCutoff L j)) :
    LowerHStageFailure L j n ↔ LowerHStageFailure L j n' := by
  constructor
  · rintro ⟨p, hgp, hnone⟩
    have hgp_eq := lowerHGreedyPrime?_eq_of_mod (L := L) (j := j) (k := j)
      (n := n) (n' := n') hB le_rfl hmod
    have hsucc_eq := lowerHSelectedSuccessors_eq_of_mod (L := L) (k := j) (j := j)
      (p := p) (n := n) (n' := n') hB le_rfl hmod
    exact ⟨p, by simpa [hgp_eq] using hgp, by simpa [hsucc_eq] using hnone⟩
  · rintro ⟨p, hgp, hnone⟩
    have hgp_eq := lowerHGreedyPrime?_eq_of_mod (L := L) (j := j) (k := j)
      (n := n) (n' := n') hB le_rfl hmod
    have hsucc_eq := lowerHSelectedSuccessors_eq_of_mod (L := L) (k := j) (j := j)
      (p := p) (n := n) (n' := n') hB le_rfl hmod
    exact ⟨p, by simpa [hgp_eq] using hgp, by simpa [hsucc_eq] using hnone⟩

private lemma lowerHInitialFailure_not_dvd {L n p : ℕ}
    (hp : p.Prime) (hpY : (p : ℝ) ≤ lowerHWindowY L 0)
    (hfail : LowerHInitialFailure L n) :
    ¬ p ∣ n := by
  intro hdiv
  have hp_floor : p ≤ ⌊lowerHWindowY L 0⌋₊ := Nat.le_floor hpY
  have hmem : p ∈ lowerHInitialSelectedPrimes L n := by
    rw [lowerHInitialSelectedPrimes]
    simp [hp_floor, hp, hdiv, hpY]
  have hne : (lowerHInitialSelectedPrimes L n).Nonempty := ⟨p, hmem⟩
  unfold LowerHInitialFailure at hfail
  simp [lowerHGreedyPrime?, finsetLeastNat?, hne] at hfail

private lemma card_bounded_periodic {P : ℕ → Prop} [DecidablePred P] {M N : ℕ}
    (hM : 0 < M) (hperiod : ∀ n, P n ↔ P (n % M)) :
    Nat.card {n : ℕ | n ≤ N ∧ P n} ≤
      Nat.card {r : Fin M // P r.val} * (N / M + 1) := by
  classical
  let f : {n : ℕ // n ≤ N ∧ P n} ↪ {r : Fin M // P r.val} × Fin (N / M + 1) :=
  { toFun := fun n =>
      (⟨⟨n.1 % M, Nat.mod_lt _ hM⟩, (hperiod n.1).mp n.2.2⟩,
       ⟨n.1 / M, Nat.lt_succ_of_le (Nat.div_le_div_right n.2.1)⟩)
    inj' := by
      intro a b hab
      have hmod : a.1 % M = b.1 % M := congrArg (fun z => (z.1.1 : ℕ)) hab
      have hdiv : a.1 / M = b.1 / M :=
        congrArg (fun z => (z.2 : Fin (N / M + 1)).val) hab
      apply Subtype.ext
      calc
        a.1 = M * (a.1 / M) + a.1 % M := (Nat.div_add_mod a.1 M).symm
        _ = M * (b.1 / M) + b.1 % M := by rw [hdiv, hmod]
        _ = b.1 := Nat.div_add_mod b.1 M }
  have hle := Finite.card_le_of_embedding f
  change Nat.card {n : ℕ // n ≤ N ∧ P n} ≤ _
  simpa only [Nat.card_prod, Nat.card_fin] using hle

lemma periodic_count_le {P : ℕ → Prop} [DecidablePred P] {M N : ℕ}
    (hM : 0 < M) (hperiod : ∀ n, P n ↔ P (n % M)) :
    (Nat.card {n : ℕ | n ≤ N ∧ P n} : ℝ) ≤
      ((Nat.card {r : Fin M // P r.val} : ℝ) / (M : ℝ)) * (N : ℝ) + (M : ℝ) := by
  classical
  let C := Nat.card {r : Fin M // P r.val}
  have hper := card_bounded_periodic (P := P) (M := M) (N := N) hM hperiod
  have hperR : (Nat.card {n : ℕ | n ≤ N ∧ P n} : ℝ) ≤
      (Nat.card {r : Fin M // P r.val} * (N / M + 1) : ℕ) := by
    exact_mod_cast hper
  have hC_le_M_nat : C ≤ M := by
    dsimp [C]
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_le (fun r : Fin M => P r.val))
  have hC_le_M : (C : ℝ) ≤ (M : ℝ) := by exact_mod_cast hC_le_M_nat
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  calc
    (Nat.card {n : ℕ | n ≤ N ∧ P n} : ℝ)
        ≤ (C : ℝ) * ((N / M + 1 : ℕ) : ℝ) := by
          simpa [C, Nat.cast_mul] using hperR
    _ ≤ (C : ℝ) * ((N : ℝ) / (M : ℝ) + 1) := by
      have hdiv : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / (M : ℝ) := Nat.cast_div_le
      have hCnonneg : (0 : ℝ) ≤ C := by positivity
      norm_num
      nlinarith
    _ = ((C : ℝ) / (M : ℝ)) * (N : ℝ) + (C : ℝ) := by
      field_simp [hMne]
    _ ≤ ((C : ℝ) / (M : ℝ)) * (N : ℝ) + (M : ℝ) := by
      linarith

private lemma coprime_to_primorial_count_le_sieve_product (P N : ℕ) :
    let M := primorial P
    let T := Finset.filter Nat.Prime (Finset.Iic P)
    (Nat.card {n : ℕ | n ≤ N ∧ M.Coprime n} : ℝ) ≤
      (∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ))) * (N : ℝ) + (M : ℝ) := by
  classical
  let M := primorial P
  let T := Finset.filter Nat.Prime (Finset.Iic P)
  have hMpos : 0 < M := primorial_pos P
  have hperiod : ∀ n : ℕ, M.Coprime n ↔ M.Coprime (n % M) := by
    intro n
    have hmod : n % M = (n % M) % M := by
      rw [Nat.mod_eq_of_lt (Nat.mod_lt n hMpos)]
    have hmodeq : n ≡ n % M [MOD M] := by
      simpa [Nat.ModEq] using hmod
    have hg : n.gcd M = (n % M).gcd M := hmodeq.gcd_eq
    rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
    rw [Nat.gcd_comm M n, Nat.gcd_comm M (n % M)]
    exact ⟨fun h => by simpa [hg] using h, fun h => by simpa [hg] using h⟩
  have hcount := periodic_count_le (P := fun n : ℕ => M.Coprime n) (M := M) (N := N)
    hMpos hperiod
  let C := Nat.card {r : Fin M // M.Coprime r.val}
  have hC_le_tot_nat : C ≤ M.totient := by
    let f : {r : Fin M // M.Coprime r.val} ↪ {m : ℕ | m < M ∧ M.Coprime m} :=
      { toFun := fun r => ⟨r.1.val, r.1.isLt, r.2⟩
        inj' := by
          intro a b hab
          apply Subtype.ext
          apply Fin.ext
          exact congrArg Subtype.val hab }
    have htarget_finite : Set.Finite {m : ℕ | m < M ∧ M.Coprime m} :=
      (Set.finite_Iio M).subset (by
        intro m hm
        exact hm.1)
    haveI : Finite {m : ℕ | m < M ∧ M.Coprime m} := htarget_finite.to_subtype
    have hle := Finite.card_le_of_embedding f
    have htot := Nat.totient_eq_card_lt_and_coprime M
    simpa [C, htot] using hle
  have hC_le_tot : (C : ℝ) ≤ (M.totient : ℝ) := by exact_mod_cast hC_le_tot_nat
  have hpf : M.primeFactors = T := by
    dsimp [M, T, primorial]
    exact Nat.primeFactors_prod (by
      intro p hp
      exact (Finset.mem_filter.mp hp).2)
  have htot :
      (M.totient : ℝ) = (M : ℝ) * ∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hq := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    simpa [hpf, one_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_sub, Rat.cast_inv,
      map_prod] using hq
  have hratio : (C : ℝ) / (M : ℝ) ≤ ∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ)) := by
    rw [div_le_iff₀ (by exact_mod_cast hMpos)]
    simpa [htot, mul_comm] using hC_le_tot
  calc
    (Nat.card {n : ℕ | n ≤ N ∧ M.Coprime n} : ℝ)
        ≤ ((C : ℝ) / (M : ℝ)) * (N : ℝ) + (M : ℝ) := by
          simpa [C] using hcount
    _ ≤ (∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ))) * (N : ℝ) + (M : ℝ) := by
          gcongr

/-! ### Paper §5.2 lines 1156-1170 — exact CRT residue counts (paper-faithful)

The lemmas below formalise paper §5.2's "independent Bernoulli with probabilities `1/q`"
claim (line 1158) and the conditional probability `∏(1−1/q)` (line 1162) **exactly**,
with no slack. They count residues in `[0, M)` avoiding all primes in a finset `Q`,
where `∏Q ∣ M` (true when `M = primorial(P)` and `Q ⊆ {primes ≤ P}`).

Proof structure:
- `pmodel_count_multiples_of_p_in_range` — multiples of `p` in `[0, M)` are exactly `M/p`.
- `pmodel_count_avoid_one_prime` — paper line 1162 marginal: count of `r ∈ [0, M)`
   with `p ∤ r` is `(M/p) · (p − 1)`, equivalent to `M · (1 − 1/p)`.
- `pmodel_totient_prod_distinct_primes` — paper line 1158 iterated: `totient(∏Q) = ∏(q−1)`.
- `pmodel_count_coprime_in_block` — periodicity per length-`N` block: each block contributes
   exactly `totient(N)` residues coprime to `N` (wraps Mathlib `filter_coprime_Ico_eq_totient`).
- `pmodel_count_avoid_primes_eq` — paper line 1162 EXACT (no slack):
   when `∏Q ∣ M`, count `{r ∈ [0,M) : ∀q ∈ Q, q ∤ r} = M · ∏(1−1/q)`.

These compose with `prod_one_sub_inv_le_exp_neg_sum` (1−x ≤ e^{−x}) and
`prime_successor_mass` (∑1/q ≥ B/8) to bound `lowerHStageFailureResidueProb` by
`exp(−B/8)`, matching paper line 1170 exactly. -/
/-- **Paper §5.2 line 1158 ("independent Bernoulli with probabilities `1/q`")** —
formalised as `totient(∏Q) = ∏(q − 1)` for distinct primes. Iterated `Nat.totient_mul`. -/
private lemma pmodel_totient_prod_distinct_primes :
    ∀ {Q : Finset ℕ}, (∀ q ∈ Q, q.Prime) →
      Nat.totient (∏ q ∈ Q, q) = ∏ q ∈ Q, (q - 1) := by
  classical
  intro Q
  induction Q using Finset.induction_on with
  | empty => intro _; simp
  | insert p P hpP ih =>
    intro hQ_prime
    have hp_prime : p.Prime := hQ_prime p (Finset.mem_insert_self p P)
    have hP_prime : ∀ q ∈ P, q.Prime := fun q hq =>
      hQ_prime q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpP, Finset.prod_insert hpP]
    have hp_cop : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hqP
      have hq_prime : q.Prime := hP_prime q hqP
      have hpq : p ≠ q := fun heq => hpP (heq ▸ hqP)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hpq
    rw [Nat.totient_mul hp_cop, Nat.totient_prime hp_prime, ih hP_prime]

/-- Per-block coprime count: in any interval `[i·N, (i+1)·N)` of length `N`,
the count of residues coprime to `N` is exactly `totient(N)`. Wraps Mathlib's
`Nat.filter_coprime_Ico_eq_totient`. -/
private lemma pmodel_count_coprime_in_block (N i : ℕ) :
    ((Finset.Ico (i * N) ((i + 1) * N)).filter (fun r => N.Coprime r)).card = N.totient := by
  have h_eq : (i + 1) * N = i * N + N := by ring
  rw [h_eq]
  exact Nat.filter_coprime_Ico_eq_totient N (i * N)

/-- **Paper §5.2 line 1158 — abstract CRT factored count.**

For coprime `a, b` and predicates `Pa, Pb : ℕ → Prop` periodic mod `a, b` resp.,
counts in `[0, a·b)` factor as a product:

  `card{r ∈ [0,a·b) : Pa(r) ∧ Pb(r)} = card{r ∈ [0,a) : Pa(r)} · card{r ∈ [0,b) : Pb(r)}`.

This is the formal Chinese Remainder Theorem applied to indicator functions —
paper §5.2 line 1158's "independent Bernoulli events" claim. Uses
`Nat.chineseRemainder` for the bijection between `Finset.range (a·b)` and
`Finset.range a × Finset.range b` via `r ↦ (r % a, r % b)`. -/
private lemma pmodel_crt_factored_count {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (Pa : ℕ → Prop) [DecidablePred Pa]
    (Pb : ℕ → Prop) [DecidablePred Pb]
    (hPa : ∀ r r', r % a = r' % a → (Pa r ↔ Pa r'))
    (hPb : ∀ r r', r % b = r' % b → (Pb r ↔ Pb r')) :
    ((Finset.range (a * b)).filter (fun r => Pa r ∧ Pb r)).card =
      ((Finset.range a).filter Pa).card * ((Finset.range b).filter Pb).card := by
  classical
  have hab_pos : 0 < a * b := Nat.mul_pos ha hb
  rw [← Finset.card_product]
  refine Finset.card_bij (fun r _ => (r % a, r % b)) ?_ ?_ ?_
  · -- maps to target
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hr ⊢
    obtain ⟨hrlt, hPar, hPbr⟩ := hr
    refine ⟨⟨Nat.mod_lt _ ha, ?_⟩, ⟨Nat.mod_lt _ hb, ?_⟩⟩
    · exact (hPa r (r % a) (Nat.mod_mod r a).symm).mp hPar
    · exact (hPb r (r % b) (Nat.mod_mod r b).symm).mp hPbr
  · -- injective
    intro r hr r' hr' heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr hr'
    have h1 : r % a = r' % a := (Prod.mk.inj heq).1
    have h2 : r % b = r' % b := (Prod.mk.inj heq).2
    have hra : r ≡ r' [MOD a] := h1
    have hrb : r ≡ r' [MOD b] := h2
    -- Combine hra, hrb via coprime to get r ≡ r' [MOD a*b]
    have hrab : r ≡ r' [MOD a * b] := by
      have h1' : r ≡ r' [MOD a] := hra
      have h2' : r ≡ r' [MOD b] := hrb
      exact (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨h1', h2'⟩
    -- r, r' < a*b and r ≡ r' [MOD a*b] ⟹ r = r'
    have hmodr : r % (a * b) = r := Nat.mod_eq_of_lt hr.1
    have hmodr' : r' % (a * b) = r' := Nat.mod_eq_of_lt hr'.1
    have := hrab
    rw [Nat.ModEq] at this
    omega
  · -- surjective
    intro st hst
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hst
    obtain ⟨⟨hslt, hPas⟩, ⟨htlt, hPbt⟩⟩ := hst
    -- Use Nat.chineseRemainder to find z ≡ st.1 [MOD a] ∧ z ≡ st.2 [MOD b]
    obtain ⟨z, hza, hzb⟩ := Nat.chineseRemainder hab st.1 st.2
    refine ⟨z % (a * b), ?_, ?_⟩
    · -- z % (a*b) ∈ filtered set
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hab_pos, ?_, ?_⟩
      · -- Pa (z % (a*b))
        have hmod_a : (z % (a * b)) % a = z % a := by
          rw [Nat.mod_mul_right_mod]
        have hz_eq : z % a = st.1 := by
          have := hza
          rw [Nat.ModEq] at this
          rw [this, Nat.mod_eq_of_lt hslt]
        have h1 : (z % (a * b)) % a = st.1 := by rw [hmod_a, hz_eq]
        have h2 : st.1 % a = st.1 := Nat.mod_eq_of_lt hslt
        exact (hPa (z % (a*b)) st.1 (by rw [h1, h2])).mpr hPas
      · -- Pb (z % (a*b))
        have hmod_b : (z % (a * b)) % b = z % b := by
          have : a * b = b * a := by ring
          rw [this, Nat.mod_mul_right_mod]
        have hz_eq : z % b = st.2 := by
          have := hzb
          rw [Nat.ModEq] at this
          rw [this, Nat.mod_eq_of_lt htlt]
        have h1 : (z % (a * b)) % b = st.2 := by rw [hmod_b, hz_eq]
        have h2 : st.2 % b = st.2 := Nat.mod_eq_of_lt htlt
        exact (hPb (z % (a*b)) st.2 (by rw [h1, h2])).mpr hPbt
    · -- (z % (a*b)) % a = st.1 and (z % (a*b)) % b = st.2
      have hmod_a : (z % (a * b)) % a = z % a := by
        rw [Nat.mod_mul_right_mod]
      have hmod_b : (z % (a * b)) % b = z % b := by
        have : a * b = b * a := by ring
        rw [this, Nat.mod_mul_right_mod]
      have hz_eq_a : z % a = st.1 := by
        have := hza
        rw [Nat.ModEq] at this
        rw [this, Nat.mod_eq_of_lt hslt]
      have hz_eq_b : z % b = st.2 := by
        have := hzb
        rw [Nat.ModEq] at this
        rw [this, Nat.mod_eq_of_lt htlt]
      ext
      · simp [hmod_a, hz_eq_a]
      · simp [hmod_b, hz_eq_b]

/-- **Block-count lemma** (paper-faithful CRT lift):
For `P` periodic mod `N`, count on `[0, N·k)` equals `k · count on [0, N)`.

Used to lift residue-count results from one period to multiple periods. -/
lemma pmodel_block_count_periodic
    {P : ℕ → Prop} [DecidablePred P] {N k : ℕ}
    (hP : ∀ r r', r % N = r' % N → (P r ↔ P r')) :
    ((Finset.range (N * k)).filter P).card = k * ((Finset.range N).filter P).card := by
  classical
  induction k with
  | zero => simp
  | succ j ih =>
    have hsplit : Finset.range (N * (j + 1)) =
                  Finset.range (N * j) ∪ Finset.Ico (N * j) (N * (j + 1)) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      constructor
      · intro hx
        rcases Nat.lt_or_ge x (N * j) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hx⟩
      · rintro (h | ⟨_, h⟩)
        · have : N * j ≤ N * (j + 1) := Nat.mul_le_mul_left N (Nat.le_succ j)
          linarith
        · exact h
    rw [hsplit]
    have hdisj : Disjoint (Finset.range (N * j)) (Finset.Ico (N * j) (N * (j + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Ico] at hx'
      omega
    rw [Finset.filter_union]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    rw [ih]
    have hsucc_split : N * (j + 1) = N * j + N := by ring
    have hblock_bij : ((Finset.Ico (N * j) (N * (j + 1))).filter P).card =
                      ((Finset.range N).filter P).card := by
      apply Finset.card_bij (fun r _ => r - N * j)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_Ico] at hr
        simp only [Finset.mem_filter, Finset.mem_range]
        have hr_lt : r < N * j + N := by rw [← hsucc_split]; exact hr.1.2
        refine ⟨by omega, ?_⟩
        have hmod_eq : (r - N * j) % N = r % N := by
          conv_rhs => rw [show r = (r - N * j) + N * j from by omega]
          rw [Nat.add_mul_mod_self_left]
        exact (hP r (r - N * j) hmod_eq.symm).mp hr.2
      · intro r1 hr1 r2 hr2 h
        simp only [Finset.mem_filter, Finset.mem_Ico] at hr1 hr2
        omega
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_range] at hv
        refine ⟨v + N * j, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, ?_⟩, ?_⟩
        · rw [hsucc_split]; omega
        · have hmod_eq : (v + N * j) % N = v % N := Nat.add_mul_mod_self_left v N j
          exact (hP v (v + N * j) hmod_eq.symm).mp hv.2
    rw [hblock_bij]
    ring

/-- **Lifted CRT factored count** (paper §5.2 line 1158, applied to `[0, M)`):
when `a·b ∣ M` with `a, b` coprime and `Pa, Pb` periodic, the joint count factors.

`card{r ∈ [0,M) : Pa(r) ∧ Pb(r)} = (M/(a·b)) · card{Pa in [0,a)} · card{Pb in [0,b)}`. -/
lemma pmodel_crt_factored_count_lifted {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hab_dvd : a * b ∣ M)
    (Pa : ℕ → Prop) [DecidablePred Pa]
    (Pb : ℕ → Prop) [DecidablePred Pb]
    (hPa : ∀ r r', r % a = r' % a → (Pa r ↔ Pa r'))
    (hPb : ∀ r r', r % b = r' % b → (Pb r ↔ Pb r')) :
    ((Finset.range M).filter (fun r => Pa r ∧ Pb r)).card =
      (M / (a * b)) *
        (((Finset.range a).filter Pa).card * ((Finset.range b).filter Pb).card) := by
  classical
  -- The conjunction Pa ∧ Pb is periodic mod (a*b)
  have hPaPb : ∀ r r', r % (a * b) = r' % (a * b) → ((Pa r ∧ Pb r) ↔ (Pa r' ∧ Pb r')) := by
    intro r r' h
    have hra : r % a = r' % a := by
      have h1 : r % (a * b) % a = r' % (a * b) % a := by rw [h]
      rwa [Nat.mod_mul_right_mod, Nat.mod_mul_right_mod] at h1
    have hrb : r % b = r' % b := by
      have h1 : r % (a * b) % b = r' % (a * b) % b := by rw [h]
      rw [show a * b = b * a from Nat.mul_comm a b] at h1
      rwa [Nat.mod_mul_right_mod, Nat.mod_mul_right_mod] at h1
    exact ⟨fun ⟨hpa, hpb⟩ => ⟨(hPa r r' hra).mp hpa, (hPb r r' hrb).mp hpb⟩,
           fun ⟨hpa, hpb⟩ => ⟨(hPa r r' hra).mpr hpa, (hPb r r' hrb).mpr hpb⟩⟩
  obtain ⟨k, hk⟩ := hab_dvd
  -- count on [0, M) = k · count on [0, a*b)
  have hblock : ((Finset.range M).filter (fun r => Pa r ∧ Pb r)).card =
      k * ((Finset.range (a * b)).filter (fun r => Pa r ∧ Pb r)).card := by
    rw [hk]
    exact pmodel_block_count_periodic hPaPb
  -- count on [0, a*b) factors via CRT
  have hcrt := pmodel_crt_factored_count ha hb hab Pa Pb hPa hPb
  rw [hblock, hcrt]
  -- M/(a*b) = k since M = (a*b)*k
  have hk_eq : M / (a * b) = k := by
    rw [hk]; exact Nat.mul_div_cancel_left k (Nat.mul_pos ha hb)
  rw [hk_eq]

/-- **Paper §5.2 lines 1162-1170 — exact (no slack).**

For a Finset `Q` of distinct primes whose product divides `M` (e.g. `M = primorial(P)`,
`Q ⊆ {primes ≤ P}`), the count of residues in `[0, M)` avoiding *all* `q ∈ Q` is
**exactly** `M · ∏_{q ∈ Q} (1 − 1/q)`.

This is paper line 1162's `P(stage j fails | past) = ∏(1−1/q)` formalised exactly:
when conditioned on past structure (mod the relevant primorial), the residue count
equals `M · ∏(1−1/q)` with no remainder slack.

Proof: split `[0, M) = ⊔_{i < M/N} [i·N, (i+1)·N)` (where `N = ∏Q`); each block has
`totient(N)` coprime residues; sum gives `(M/N) · totient(N) = (M/N) · ∏(q−1) =
M · ∏(1 − 1/q)`. -/
lemma pmodel_count_avoid_primes_eq
    {Q : Finset ℕ} (hQ_prime : ∀ q ∈ Q, q.Prime)
    {M : ℕ} (hMpos : 0 < M)
    (hprodQ_dvd : (∏ q ∈ Q, q) ∣ M) :
    (((Finset.range M).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r)).card : ℝ) =
      (M : ℝ) * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by
  classical
  set N : ℕ := ∏ q ∈ Q, q with hN_def
  have hN_pos : 0 < N := Finset.prod_pos (fun q hq => (hQ_prime q hq).pos)
  have hN_ne : N ≠ 0 := hN_pos.ne'
  have hequiv : ∀ r, (∀ q ∈ Q, ¬ q ∣ r) ↔ Nat.Coprime N r := by
    intro r
    refine ⟨fun h => ?_, fun h q hq h_div => ?_⟩
    · rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      have hgcd_pos : 1 < Nat.gcd N r := by
        have : 0 < Nat.gcd N r := Nat.gcd_pos_of_pos_left _ hN_pos
        omega
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hgcd_pos)
      have hp_N : p ∣ N := hp_dvd.trans (Nat.gcd_dvd_left _ _)
      have hp_r : p ∣ r := hp_dvd.trans (Nat.gcd_dvd_right _ _)
      rcases (Prime.dvd_finset_prod_iff hp_prime.prime _).mp hp_N with ⟨q, hq, hpq⟩
      have hq_prime : q.Prime := hQ_prime q hq
      have hpq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hpq
      exact h q hq (hpq_eq ▸ hp_r)
    · have hqN : q ∣ N := by rw [hN_def]; exact Finset.dvd_prod_of_mem _ hq
      have hq_gcd : q ∣ Nat.gcd N r := Nat.dvd_gcd hqN h_div
      have hq_one : q ∣ 1 := h ▸ hq_gcd
      have := (hQ_prime q hq).one_lt
      exact absurd hq_one (by intro habs; have := Nat.le_of_dvd (by norm_num) habs; omega)
  have hfilter_eq : (Finset.range M).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r) =
                    (Finset.range M).filter (fun r => Nat.Coprime N r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, hequiv r]
  rw [hfilter_eq]
  obtain ⟨k, hk⟩ := hprodQ_dvd
  have hk_pos : 0 < k := by
    by_contra hk_zero
    push_neg at hk_zero
    interval_cases k
    rw [hk] at hMpos
    simp at hMpos
  have hblock_count :
      ∀ kk : ℕ, ((Finset.range (N * kk)).filter (fun r => N.Coprime r)).card =
                kk * N.totient := by
    intro kk
    induction kk with
    | zero => simp
    | succ j ih =>
      have hsplit : Finset.range (N * (j + 1)) =
                    Finset.range (N * j) ∪ Finset.Ico (N * j) (N * (j + 1)) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        constructor
        · intro hx
          rcases Nat.lt_or_ge x (N * j) with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h⟩)
          · have : N * j ≤ N * (j + 1) := Nat.mul_le_mul_left N (Nat.le_succ j)
            linarith
          · exact h
      rw [hsplit]
      have hdisj : Disjoint (Finset.range (N * j)) (Finset.Ico (N * j) (N * (j + 1))) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_range] at hx
        simp only [Finset.mem_Ico] at hx'
        omega
      rw [Finset.filter_union]
      rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
      rw [ih]
      have hblock : (Finset.Ico (N * j) (N * (j + 1))).filter (fun r => N.Coprime r) =
                    (Finset.Ico (j * N) ((j + 1) * N)).filter (fun r => N.Coprime r) := by
        rw [show N * j = j * N from Nat.mul_comm N j,
            show N * (j + 1) = (j + 1) * N from Nat.mul_comm N (j + 1)]
      rw [hblock, pmodel_count_coprime_in_block]
      ring
  have hcount_nat :
      ((Finset.range M).filter (fun r => Nat.Coprime N r)).card = k * N.totient := by
    rw [hk]
    exact hblock_count k
  have hcount_real : (((Finset.range M).filter (fun r => Nat.Coprime N r)).card : ℝ) =
                     (k : ℝ) * (N.totient : ℝ) := by
    rw [show (k : ℝ) * (N.totient : ℝ) = ((k * N.totient : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast hcount_nat
  rw [hcount_real]
  rw [show N.totient = ∏ q ∈ Q, (q - 1) from pmodel_totient_prod_distinct_primes hQ_prime]
  rw [show ((∏ q ∈ Q, (q - 1) : ℕ) : ℝ) = ∏ q ∈ Q, ((q : ℝ) - 1) from by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq_prime := hQ_prime q hq
    rw [Nat.cast_sub (hq_prime.pos : 1 ≤ q)]
    push_cast; ring]
  rw [show (∏ q ∈ Q, ((q : ℝ) - 1)) = (N : ℝ) * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) from by
    rw [hN_def, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq_prime := hQ_prime q hq
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
    field_simp]
  rw [hk]
  push_cast
  ring

private lemma prod_one_sub_inv_le_exp_neg_sum (T : Finset ℕ) (hpos : ∀ q ∈ T, 0 < q) :
    (∏ q ∈ T, (1 - (1 : ℝ) / (q : ℝ))) ≤
      Real.exp (-(∑ q ∈ T, (1 : ℝ) / (q : ℝ))) := by
  classical
  calc
    (∏ q ∈ T, (1 - (1 : ℝ) / (q : ℝ)))
        ≤ ∏ q ∈ T, Real.exp (-(1 : ℝ) / (q : ℝ)) := by
          apply Finset.prod_le_prod
          · intro q hq
            have hle : (1 : ℝ) / (q : ℝ) ≤ 1 := by
              have hq_one : (1 : ℝ) ≤ q := by
                exact_mod_cast Nat.succ_le_of_lt (hpos q hq)
              simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq_one
            linarith
          · intro q _hq
            simpa [sub_eq_add_neg, neg_div] using Real.one_sub_le_exp_neg ((1 : ℝ) / (q : ℝ))
    _ = Real.exp (∑ q ∈ T, (-(1 : ℝ) / (q : ℝ))) := by
          rw [Real.exp_sum]
    _ = Real.exp (-(∑ q ∈ T, (1 : ℝ) / (q : ℝ))) := by
          congr 1
          have hterm : (∑ q ∈ T, (-(1 : ℝ) / (q : ℝ))) =
              ∑ q ∈ T, -((1 : ℝ) / (q : ℝ)) := by
            apply Finset.sum_congr rfl
            intro q _hq
            ring
          rw [hterm, Finset.sum_neg_distrib]

private lemma prime_reciprocal_sum_eventually_ge (A : ℝ) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧
      ∀ y : ℝ, Y₀ ≤ y →
        A ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊y⌋₊), (1 : ℝ) / (p : ℝ) := by
  classical
  rcases mertens with ⟨M, C, hC, hmertens⟩
  let Z : ℝ := A + |M| + C + 1
  let Y₀ : ℝ := max (Real.exp 1) (Real.exp (Real.exp Z))
  refine ⟨Y₀, ?_, ?_⟩
  · have htwo_exp : (2 : ℝ) ≤ Real.exp 1 := by
      simpa using Real.two_mul_le_exp (x := 1)
    exact htwo_exp.trans (le_max_left _ _)
  intro y hy
  let S : ℝ := ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊y⌋₊), (1 : ℝ) / (p : ℝ)
  have hy_exp1 : Real.exp 1 ≤ y := (le_max_left _ _).trans hy
  have hy_expZ : Real.exp (Real.exp Z) ≤ y := (le_max_right _ _).trans hy
  have hy_two : (2 : ℝ) ≤ y := by
    have htwo_exp : (2 : ℝ) ≤ Real.exp 1 := by
      simpa using Real.two_mul_le_exp (x := 1)
    exact htwo_exp.trans hy_exp1
  have hy_pos : 0 < y := by linarith
  have hlog_ge_one : (1 : ℝ) ≤ Real.log y :=
    (Real.le_log_iff_exp_le hy_pos).2 hy_exp1
  have hlog_pos : 0 < Real.log y := by linarith
  have hlog_ge_expZ : Real.exp Z ≤ Real.log y :=
    (Real.le_log_iff_exp_le hy_pos).2 hy_expZ
  have hloglog_ge : Z ≤ Real.log (Real.log y) :=
    (Real.le_log_iff_exp_le hlog_pos).2 hlog_ge_expZ
  have hm := hmertens y hy_two
  have hm_lower : Real.log (Real.log y) + M - C / Real.log y ≤ S := by
    have h := (abs_le.mp hm).1
    linarith
  have hCdiv : C / Real.log y ≤ C := by
    rw [div_le_iff₀ hlog_pos]
    nlinarith
  have hmain : A ≤ Real.log (Real.log y) + M - C / Real.log y := by
    dsimp [Z] at hloglog_ge
    nlinarith [hloglog_ge, neg_abs_le M, hCdiv]
  exact hmain.trans hm_lower

private lemma chebyshev_stage_exponent_eventually (Cθ : ℝ) (hCθ : 0 < Cθ) :
    ∀ᶠ m : ℕ in Filter.atTop,
      Cθ * Real.exp (Real.exp (tower m / 2)) ≤ (1 / 2 : ℝ) * tower (m + 2) := by
  have hhalf : Filter.Tendsto (fun m : ℕ => tower m / 2) Filter.atTop Filter.atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tower_tendsto_atTop.const_mul_atTop
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹))
  have hehalf : Filter.Tendsto (fun m : ℕ => Real.exp (tower m / 2)) Filter.atTop
      Filter.atTop := by
    exact Real.tendsto_exp_atTop.comp hhalf
  filter_upwards [hehalf.eventually_ge_atTop (max 2 (Real.log (2 * Cθ)))] with m hm
  let E : ℝ := Real.exp (tower m / 2)
  have hE2 : (2 : ℝ) ≤ E := (le_max_left _ _).trans hm
  have hlog_le : Real.log (2 * Cθ) ≤ E := (le_max_right _ _).trans hm
  have hlog_add : Real.log (2 * Cθ) + E ≤ E ^ 2 := by
    nlinarith [hE2, hlog_le]
  have hmain : 2 * Cθ * Real.exp E ≤ Real.exp (E ^ 2) := by
    calc
      2 * Cθ * Real.exp E = Real.exp (Real.log (2 * Cθ) + E) := by
        rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * Cθ)]
      _ ≤ Real.exp (E ^ 2) := Real.exp_le_exp.mpr hlog_add
  have hEtower : E ^ 2 = tower (m + 1) := by
    dsimp [E]
    rw [sq]
    rw [← Real.exp_add]
    ring_nf
    rw [show 1 + m = m + 1 by omega]
    rfl
  calc
    Cθ * Real.exp (Real.exp (tower m / 2)) = Cθ * Real.exp E := rfl
    _ ≤ (1 / 2 : ℝ) * Real.exp (E ^ 2) := by nlinarith
    _ = (1 / 2 : ℝ) * tower (m + 2) := by
      rw [hEtower]
      rfl

private lemma linear_le_delta_exp_half_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) + 2 ≤ δ * Real.exp ((n : ℝ) / 2) := by
  have hnat_half : Filter.Tendsto (fun n : ℕ => (n : ℝ) / 2) Filter.atTop
      Filter.atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹))
  have hbase : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ 1) Filter.atTop
      Filter.atTop :=
    Real.tendsto_exp_div_pow_atTop 1
  have hcomp : Filter.Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) / 2) / (((n : ℝ) / 2) ^ 1)) Filter.atTop
      Filter.atTop := by
    simpa [Function.comp_def] using hbase.comp hnat_half
  filter_upwards [hcomp.eventually_ge_atTop (4 / δ), Filter.eventually_ge_atTop 4] with
    n hn hn4
  have hnpos : 0 < ((n : ℝ) / 2) := by positivity
  have hge : 4 / δ ≤ Real.exp ((n : ℝ) / 2) / ((n : ℝ) / 2) := by
    simpa using hn
  rw [le_div_iff₀ hnpos] at hge
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have h2n : 2 * (n : ℝ) ≤ δ * Real.exp ((n : ℝ) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hge hδ.le
    field_simp [hδ.ne'] at hmul
    nlinarith
  have hn2 : (n : ℝ) + 2 ≤ 2 * (n : ℝ) := by nlinarith
  exact hn2.trans h2n

private lemma primorial_le_exp_chebyshev {Cθ : ℝ}
    (htheta : ∀ t : ℝ, 2 ≤ t →
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), Real.log (p : ℝ)) ≤
        Cθ * t)
    {P : ℕ} (hP : (2 : ℝ) ≤ P) :
    (primorial P : ℝ) ≤ Real.exp (Cθ * (P : ℝ)) := by
  classical
  let T := Finset.filter Nat.Prime (Finset.Iic P)
  have hMpos : 0 < (primorial P : ℝ) := by exact_mod_cast primorial_pos P
  have hlog : Real.log (primorial P : ℝ) = ∑ p ∈ T, Real.log (p : ℝ) := by
    unfold primorial
    rw [Nat.cast_prod]
    rw [Real.log_prod]
    · intro p hp
      have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
      exact_mod_cast hpprime.ne_zero
  have hthetaP : (∑ p ∈ T, Real.log (p : ℝ)) ≤ Cθ * (P : ℝ) := by
    simpa [T] using htheta (P : ℝ) hP
  calc
    (primorial P : ℝ) = Real.exp (Real.log (primorial P : ℝ)) := by
      rw [Real.exp_log hMpos]
    _ ≤ Real.exp (Cθ * (P : ℝ)) := by
      rw [hlog]
      exact Real.exp_le_exp.mpr hthetaP

private lemma lowerHStageCutoff_le_exp_exp_tower {L j : ℕ}
    (hj : j ∈ Finset.range (lowerHChainLength L)) :
    (lowerHStageCutoff L j : ℝ) ≤ Real.exp (Real.exp (tower (L - 4) / 2)) := by
  have hm4 : lowerHWindowM L j + 4 ≤ L := lowerHWindowM_add_four_le_of_mem_range hj
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 4 ≤ L := by omega
    exact_mod_cast (Nat.lt_of_lt_of_le (by omega : 0 < 4) this)
  have hBne : lowerHWindowB L ≠ 0 := by
    dsimp [lowerHWindowB]
    positivity
  have hexp :
      (lowerHWindowB L / 2) * lowerHWindowY L j = tower (lowerHWindowM L j) / 2 :=
    lowerHStageExponent_eq hBne
  have hm_le : lowerHWindowM L j ≤ L - 4 := by omega
  have htower_le : tower (lowerHWindowM L j) ≤ tower (L - 4) :=
    (strictMono_nat_of_lt_succ tower_lt_succ).monotone hm_le
  have harg_le :
      (lowerHWindowB L / 2) * lowerHWindowY L j ≤ tower (L - 4) / 2 := by
    rw [hexp]
    linarith
  calc
    (lowerHStageCutoff L j : ℝ)
        ≤ Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j)) := by
          exact Nat.floor_le (by positivity)
    _ ≤ Real.exp (Real.exp (tower (L - 4) / 2)) := by
          gcongr

/-- Bridge: `Nat.card {r : Fin M // P r.val} = ((Finset.range M).filter P).card`.
This connects the `Fin M`-subtype counting form (used in
`lowerHStageFailureResidueProb`) with the `Finset.range M`-filter form (used in
`pmodel_count_avoid_primes_eq` and `pmodel_crt_factored_count`). -/
lemma fin_card_subtype_eq_range_filter_card {M : ℕ} (P : ℕ → Prop)
    [DecidablePred P] :
    Nat.card {r : Fin M // P r.val} =
      ((Finset.range M).filter P).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.subtype_card]
  apply Finset.card_bij (fun (r : Fin M) (_ : r ∈ (Finset.univ : Finset (Fin M)).filter
        (fun r : Fin M => P r.val)) => r.val)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨r.isLt, hr⟩
  · intro r hr r' hr' h
    exact Fin.ext h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    refine ⟨⟨v, hv.1⟩, ?_, rfl⟩
    simp [Finset.mem_filter, hv.2]

/-- Helper: if `lowerHSelectedSuccessors L j p r` is empty (no chosen successor),
then no `q ∈ Q_j(p)` divides `r`. -/
private lemma no_q_dvd_of_no_selected (L j p r : ℕ)
    (hsucc : finsetLeastNat? (lowerHSelectedSuccessors L j p r) = none) :
    ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r := by
  classical
  intro q hq hdvd
  have hmem : q ∈ lowerHSelectedSuccessors L j p r := by
    simp [lowerHSelectedSuccessors, hq, hdvd]
  unfold finsetLeastNat? at hsucc
  by_cases hne : (lowerHSelectedSuccessors L j p r).Nonempty
  · simp [hne] at hsucc
  · exact hne ⟨q, hmem⟩

/-- Helper: if no `q ∈ Q_j(p)` divides `r`, then no chosen successor exists. -/
private lemma no_selected_of_no_q_dvd (L j p r : ℕ)
    (hsucc : ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r) :
    finsetLeastNat? (lowerHSelectedSuccessors L j p r) = none := by
  classical
  unfold finsetLeastNat?
  have hempty : ¬ (lowerHSelectedSuccessors L j p r).Nonempty := by
    rintro ⟨q, hq⟩
    simp [lowerHSelectedSuccessors, Finset.mem_filter] at hq
    exact hsucc q hq.1 hq.2
  simp [hempty]

/-- The bad set decomposes as a disjoint union over prime values `p`, indexed
by an arbitrary Finset `S` of primes containing all possible `p_j(r)` values.
The hypothesis `hS` ensures the index is large enough; in the application
`S := {primes ≤ stage_cut}` is sufficient since `p_j ≤ y_j ≤ stage_cut`
(paper §5.2 line 1142). -/
private lemma lowerHStageFailure_finset_card_eq_sum_by_prime (L j M : ℕ)
    (S : Finset ℕ)
    (hS : ∀ r p, r ∈ Finset.range M → lowerHGreedyPrime? L r j = some p → p ∈ S) :
    letI : DecidablePred (fun r => LowerHStageFailure L j r) := Classical.decPred _
    ((Finset.range M).filter (fun r => LowerHStageFailure L j r)).card =
      ∑ p ∈ S,
        ((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p ∧
          ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r)).card := by
  classical
  have hset_eq : ((Finset.range M).filter (fun r => LowerHStageFailure L j r)) =
      S.biUnion (fun p =>
        (Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p ∧
          ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨hrM, ⟨p, hgp, hsucc⟩⟩
      exact ⟨p, hS r p (Finset.mem_range.mpr hrM) hgp, hrM, hgp,
        no_q_dvd_of_no_selected L j p r hsucc⟩
    · rintro ⟨p, _, hrM, hgp, hsucc⟩
      exact ⟨hrM, ⟨p, hgp, no_selected_of_no_q_dvd L j p r hsucc⟩⟩
  rw [hset_eq]
  rw [Finset.card_biUnion]
  intro p _ p' _ hpp'
  simp only [Function.onFun]
  rw [Finset.disjoint_filter]
  intro r _ ⟨hgp, _⟩ ⟨hgp', _⟩
  exact hpp' (Option.some_inj.mp (hgp.symm.trans hgp'))

/-- For `x ≥ 1`, `log x ≤ x - 1`. Direct from `Real.log_le_sub_one_of_pos`. -/
private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 :=
  Real.log_le_sub_one_of_pos (by linarith)

/-- For `x ≥ 1`, `2 * log x ≤ x`. Standard: log grows slower than identity.
Proof via case analysis on x ≤ 4 (using log x ≤ x-1 and 2(x-1) ≤ x for x ≥ 2; numerical for x ≤ 2)
and x ≥ 4 (using monotonicity). -/
private lemma two_log_le_self {x : ℝ} (hx : 1 ≤ x) : 2 * Real.log x ≤ x := by
  -- Use log x = 2 log √x ≤ 2(√x - 1).
  -- 2 log x ≤ 4(√x - 1) ≤ x iff x ≥ 4(√x - 1) iff x + 4 ≥ 4√x iff (√x - 2)² ≥ 0 ✓.
  have hx_pos : (0 : ℝ) < x := by linarith
  have hsqrt_x_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  -- log x = 2 log(√x)
  have h_log_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have h_sqrt_sq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    have : Real.log x = Real.log (Real.sqrt x * Real.sqrt x) := by rw [h_sqrt_sq]
    rw [this, Real.log_mul hsqrt_x_pos.ne' hsqrt_x_pos.ne']
    ring
  rw [h_log_eq]
  -- Want: 2 * (2 log √x) ≤ x, i.e., 4 log √x ≤ x.
  -- Use log √x ≤ √x - 1.
  have h_log_sqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := log_le_sub_one hsqrt_ge_one
  -- Want: 4(√x - 1) ≤ x, i.e., x - 4√x + 4 ≥ 0, i.e., (√x - 2)² ≥ 0. ✓
  have h_quadratic : x - 4 * Real.sqrt x + 4 ≥ 0 := by
    have h := sq_nonneg (Real.sqrt x - 2)
    have : (Real.sqrt x - 2)^2 = x - 4 * Real.sqrt x + 4 := by
      rw [sub_sq]
      have : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
      nlinarith [this]
    linarith
  nlinarith [h_log_sqrt]

/-- For `x ≥ 1`, `log x ≤ √x`. Apply `two_log_le_self` at `√x`:
`2 log √x ≤ √x`, and `log x = 2 log √x`, so `log x ≤ √x`. -/
private lemma log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hsqrt_x_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  -- 2 log √x ≤ √x (from two_log_le_self).
  have h := two_log_le_self hsqrt_ge_one
  -- log x = 2 log √x.
  have h_log_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have h_sqrt_sq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    have : Real.log x = Real.log (Real.sqrt x * Real.sqrt x) := by rw [h_sqrt_sq]
    rw [this, Real.log_mul hsqrt_x_pos.ne' hsqrt_x_pos.ne']
    ring
  linarith

/-- `exp 2 > 7`. Numerical bound from `Real.exp_one_gt_d9`. -/
private lemma exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
  rw [h_exp2]
  nlinarith [Real.exp_pos 1]

/-- `tower 1 = exp(exp 1) > 7`. -/
private lemma tower_one_gt_seven : (7 : ℝ) < tower 1 := by
  show (7 : ℝ) < Real.exp (tower 0)
  show (7 : ℝ) < Real.exp (Real.exp 1)
  -- exp(exp 1) > exp 2 > 7 (via exp 1 > 2 and exp monotone).
  have h_e_gt_two : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have h_exp_e_gt_exp_two : Real.exp 2 < Real.exp (Real.exp 1) :=
    Real.exp_lt_exp.mpr h_e_gt_two
  linarith [exp_two_gt_seven]

/-- For `L ∈ {1, 2, 3}`, `4 log L ≤ tower 1`. Uses `log 3 < 2 log 2 < 1.4`. -/
private lemma four_log_le_tower_one_of_le_three {L : ℝ}
    (hL_one_le : 1 ≤ L) (hL_le_three : L ≤ 3) :
    4 * Real.log L ≤ tower 1 := by
  -- log L ≤ log 3 < 2 log 2 < 2 · 0.7 = 1.4. So 4 log L < 5.6 < 7 < tower 1.
  have h_log_le : Real.log L ≤ Real.log 3 :=
    Real.log_le_log (by linarith) hL_le_three
  have h_log3_lt : Real.log 3 < 2 * Real.log 2 := by
    have h : Real.log 3 < Real.log 4 :=
      Real.log_lt_log (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) < 4)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  have h_log2_lt : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9; linarith
  -- 4 log L ≤ 4 log 3 < 8 log 2 < 5.6 < 7 < tower 1
  have h1 : 4 * Real.log L < 8 * Real.log 2 := by linarith
  have h2 : 8 * Real.log 2 < 5.6 := by linarith
  linarith [tower_one_gt_seven]

/-- For `L ≥ 16`, `4 log L ≤ exp(√L)`. Chain `4 log L ≤ 4 √L ≤ L ≤ exp(√L)`. -/
private lemma four_log_le_exp_sqrt_of_ge_16 {L : ℝ} (hL : 16 ≤ L) :
    4 * Real.log L ≤ Real.exp (Real.sqrt L) := by
  have hL_ge_one : (1 : ℝ) ≤ L := by linarith
  have hL_pos : (0 : ℝ) < L := by linarith
  -- Step 1: 4 log L ≤ 4 √L
  have h1 : 4 * Real.log L ≤ 4 * Real.sqrt L := by
    have := log_le_sqrt hL_ge_one; linarith
  -- Step 2: 4 √L ≤ L. Use √L ≥ 4 (since L ≥ 16).
  have hsqrt_ge_4 : 4 ≤ Real.sqrt L := by
    have h16 : Real.sqrt 16 ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    have : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
    linarith
  have hsqrt_sq : Real.sqrt L * Real.sqrt L = L :=
    Real.mul_self_sqrt (by linarith)
  have h2 : 4 * Real.sqrt L ≤ L := by nlinarith [hsqrt_sq]
  -- Step 3: L ≤ exp(√L) (since log L ≤ √L).
  have h3 : L ≤ Real.exp (Real.sqrt L) := by
    have h_log_sqrt : Real.log L ≤ Real.sqrt L := log_le_sqrt hL_ge_one
    calc L = Real.exp (Real.log L) := (Real.exp_log hL_pos).symm
      _ ≤ Real.exp (Real.sqrt L) := Real.exp_le_exp.mpr h_log_sqrt
  linarith

/-- `tower 2 > 100`. Big bound for analytic uses.
`tower 2 = exp(tower 1) > exp(7) > 100` (since exp 7 ≈ 1097). -/
private lemma tower_two_gt_hundred : (100 : ℝ) < tower 2 := by
  show (100 : ℝ) < Real.exp (tower 1)
  have h_t1_gt7 : (7 : ℝ) < tower 1 := tower_one_gt_seven
  have h_exp_t1 : Real.exp 7 < Real.exp (tower 1) := Real.exp_lt_exp.mpr h_t1_gt7
  -- exp(7) > 100. Use exp(7) = exp(2) * exp(2) * exp(2) * exp(1) and bounds.
  have h_exp7 : Real.exp 7 = Real.exp 2 * Real.exp 2 * Real.exp 2 * Real.exp 1 := by
    rw [show (7 : ℝ) = 2 + 2 + 2 + 1 by norm_num,
        Real.exp_add, Real.exp_add, Real.exp_add]
  have h_exp2_gt : (7 : ℝ) < Real.exp 2 := exp_two_gt_seven
  have h_exp1_gt : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have h_exp7_gt : (100 : ℝ) < Real.exp 7 := by
    -- exp 7 > 7 * 7 * 7 * 2 = 686 > 100. Build via successive products.
    have hpos1 : 0 < Real.exp 1 := Real.exp_pos 1
    have hpos2 : 0 < Real.exp 2 := Real.exp_pos 2
    have h_sq : (49 : ℝ) < Real.exp 2 * Real.exp 2 := by nlinarith
    have h_cube : (343 : ℝ) < Real.exp 2 * Real.exp 2 * Real.exp 2 := by nlinarith
    have h_final : (686 : ℝ) < Real.exp 2 * Real.exp 2 * Real.exp 2 * Real.exp 1 := by
      nlinarith
    rw [h_exp7]; linarith
  linarith

/-- For `4 ≤ L ≤ 15`, `4 log L ≤ tower 2`. -/
private lemma four_log_le_tower_two_of_le_fifteen {L : ℝ}
    (hL_ge : 4 ≤ L) (hL_le : L ≤ 15) :
    4 * Real.log L ≤ tower 2 := by
  -- 4 log L ≤ 4 log 15. log 15 < 3 (since exp 3 > 15).
  have hL_pos : (0 : ℝ) < L := by linarith
  have h_log_le : Real.log L ≤ Real.log 15 :=
    Real.log_le_log hL_pos hL_le
  -- log 15 < log(exp 3) = 3 (since exp 3 > 15).
  have h_log15_lt : Real.log 15 < 3 := by
    have h_exp3_gt_15 : (15 : ℝ) < Real.exp 3 := by
      -- exp(3) > exp(2) · exp(1) > 7 · 2 = 14? Need >15.
      -- Use exp(3) = exp(2) · exp(1) and exp(2) > 7, exp(1) > 2.7.
      have h_e1 : (2.7 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      have h_e2 : (7 : ℝ) < Real.exp 2 := exp_two_gt_seven
      have h_exp3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by
        rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.exp_add]
      rw [h_exp3]; nlinarith [Real.exp_pos 1, Real.exp_pos 2]
    have h : Real.log 15 < Real.log (Real.exp 3) :=
      Real.log_lt_log (by norm_num : (0:ℝ) < 15) h_exp3_gt_15
    rwa [Real.log_exp] at h
  -- 4 log L < 4 · 3 = 12 ≤ tower 2 (since tower 2 > 100)
  linarith [tower_two_gt_hundred]

/-- Tower lower bound: `T_m ≥ exp(m+1)` for `m ≥ 0`.
By induction, using `tower 0 = exp 1` and `Real.add_one_le_exp`. -/
private lemma tower_ge_exp_succ (m : ℕ) :
    Real.exp ((m : ℝ) + 1) ≤ tower m := by
  induction m with
  | zero =>
      simp only [Nat.cast_zero, zero_add]
      show Real.exp 1 ≤ Real.exp 1
      exact le_refl _
  | succ k ih =>
      show Real.exp (((k + 1 : ℕ) : ℝ) + 1) ≤ Real.exp (tower k)
      apply Real.exp_le_exp.mpr
      push_cast
      have h := Real.add_one_le_exp ((k : ℝ) + 1)
      linarith

/-! ### Phase 1: Tighter periodicity (paper line 1156)

Paper §5.2 line 1156: "The construction up to stage j depends only on selected
primes lying below the present search interval."

Formalised here as: `lowerHGreedyPrime? L · j` is periodic mod `primorial(⌊y_j⌋₊)`. -/

/-- **Analytic bound (paper line 1133-1141):** `exp(exp((B/2)*y_k)) ≤ y_{k+1}`.

Paper: `exp(exp((B/2)y_j)) ≪ exp(exp(B y_j))/B = y_{j+1}` (eq 1136-1141).
The `≪` is asymptotic; for the formal version we need this for all `L ≥ 2`,
i.e., `B ≥ 4`.

Proof: `y_{k+1} = T_{m_{k+1}}/B = exp(exp(T_{m_k}))/B = exp(exp(B*y_k))/B`.
So want `B · exp(exp((B/2)y_k)) ≤ exp(exp(B y_k))`, i.e.,
`log B + exp((B/2)y_k) ≤ exp(B y_k)`. For `(B/2) y_k ≥ 1`, this is
`log B ≤ exp((B/2)y_k) (exp((B/2)y_k) - 1)`, easily satisfied. -/
private lemma exp_exp_half_le_y_succ {L k : ℕ} (hB : 2 ≤ lowerHWindowB L) :
    Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L k)) ≤
      lowerHWindowY L (k + 1) := by
  -- Step 1: Express y_{k+1} via tower successor: y_{k+1} = exp(exp(B*y_k))/B.
  have hB_pos : 0 < lowerHWindowB L := by linarith
  have hB_ne : lowerHWindowB L ≠ 0 := hB_pos.ne'
  have hm_succ : lowerHWindowM L (k + 1) = lowerHWindowM L k + 1 + 1 := by
    unfold lowerHWindowM; ring
  have hy_succ_eq : lowerHWindowY L (k + 1) =
      Real.exp (Real.exp (lowerHWindowB L * lowerHWindowY L k)) / lowerHWindowB L := by
    unfold lowerHWindowY
    rw [hm_succ]
    -- tower(m+1+1) = exp(tower(m+1)) = exp(exp(tower m))
    show Real.exp (tower (lowerHWindowM L k + 1)) / lowerHWindowB L = _
    have htower_unfold : tower (lowerHWindowM L k + 1) =
        Real.exp (tower (lowerHWindowM L k)) := rfl
    rw [htower_unfold]
    -- B * (tower m_k / B) = tower m_k
    have hBy : lowerHWindowB L * (tower (lowerHWindowM L k) / lowerHWindowB L) =
        tower (lowerHWindowM L k) := by field_simp
    rw [show lowerHWindowB L * (tower (lowerHWindowM L k) / lowerHWindowB L) =
        tower (lowerHWindowM L k) from hBy]
  rw [hy_succ_eq]
  rw [le_div_iff₀ hB_pos]
  -- Goal: exp(exp((B/2)*y_k)) * B ≤ exp(exp(B*y_k))
  set yk := lowerHWindowY L k
  set BL := lowerHWindowB L
  have hBy_eq : BL * yk = tower (lowerHWindowM L k) := by
    show lowerHWindowB L * lowerHWindowY L k = tower (lowerHWindowM L k)
    unfold lowerHWindowY
    rw [mul_div_cancel₀ _ hB_ne]
  have hBhalf_yk : (BL / 2) * yk = tower (lowerHWindowM L k) / 2 := by
    have : (BL / 2) * yk = (BL * yk) / 2 := by ring
    rw [this, hBy_eq]
  rw [hBhalf_yk, hBy_eq]
  -- Goal: exp(exp(T_{m_k}/2)) * B ≤ exp(exp(T_{m_k}))
  set t := tower (lowerHWindowM L k) with ht_def
  -- Step 2: t ≥ T_0 = exp(1).
  have ht_ge_e : Real.exp 1 ≤ t := by
    show tower 0 ≤ tower (lowerHWindowM L k)
    exact (strictMono_nat_of_lt_succ tower_lt_succ).monotone (Nat.zero_le _)
  -- Step 3: t/2 ≥ exp(1)/2 ≈ 1.36 ≥ log 2 ≈ 0.69.
  have ht_half_ge : Real.exp 1 / 2 ≤ t / 2 := by linarith
  have hlog2_le_e_half : Real.log 2 ≤ Real.exp 1 / 2 := by
    have h1 : Real.log 2 < 0.7 := Real.log_two_lt_d9.trans (by norm_num)
    have h2 : Real.exp 1 / 2 ≥ 1 := by
      have := Real.exp_one_gt_d9; linarith
    linarith
  have hlog2_le : Real.log 2 ≤ t / 2 := hlog2_le_e_half.trans ht_half_ge
  -- Step 4: exp(t) ≥ 2 * exp(t/2). Since t = (t/2) + (t/2) and exp((t/2) + log 2) ≤ exp(t).
  have hdouble : 2 * Real.exp (t / 2) ≤ Real.exp t := by
    have hsum : Real.log 2 + t / 2 ≤ t := by
      have : t = t / 2 + t / 2 := by ring
      linarith
    calc 2 * Real.exp (t / 2)
        = Real.exp (Real.log 2) * Real.exp (t / 2) := by
          rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ = Real.exp (Real.log 2 + t / 2) := by rw [Real.exp_add]
      _ ≤ Real.exp t := Real.exp_le_exp.mpr hsum
  -- Step 5: Use this to show exp(t) - exp(t/2) ≥ exp(t/2).
  have hdiff_ge : Real.exp (t / 2) ≤ Real.exp t - Real.exp (t / 2) := by linarith
  -- Step 6: log B ≤ exp(t/2). Since t/2 ≥ T_0/2 and exp(T_0/2) is large.
  -- t = T_{m_k} ≥ T_{m_0+1} = exp(T_{m_0}) ≥ exp(m_0 + 1) ≥ exp(⌊√L⌋ + 1) ≥ exp(√L).
  -- For all L ≥ 1: 2 log L ≤ exp(√L) (standard). This gives log B = 2 log L ≤ exp(√L) ≤ exp(t/2).
  --
  -- The cleanest path: t ≥ T_{m_k+1}_bound... actually we only need t/2 ≥ 2 log L.
  -- t/2 = T_{m_k}/2. T_{m_k} ≥ T_{m_0} ≥ exp(m_0). m_0 = ⌊√L⌋.
  -- Want: T_{m_k}/2 ≥ 2 log L, i.e., T_{m_k} ≥ 4 log L.
  -- T_{m_k} ≥ exp(m_k + 1). m_k + 1 ≥ m_0 + 1 ≥ √L (since ⌊√L⌋ + 1 ≥ √L).
  -- So T_{m_k} ≥ exp(√L). Need exp(√L) ≥ 4 log L.
  --
  -- Key inequality: For L ≥ 1, exp(√L) ≥ 4 log L. (Holds: at L=1, 0 ≤ exp(1) = e ≥ 0;
  -- at L=4, 4 log 4 ≈ 5.55 ≤ exp(2) ≈ 7.39; at L=100, 4 log 100 ≈ 18.4 ≤ exp(10) ≈ 22026.)
  --
  -- We further reduce to: (a) log L ≤ √L (log grows slower than sqrt), (b) 4 ≤ exp(√L)/√L for √L ≥ 1.
  --
  -- Standard chain: log L ≤ L - 1 ≤ L ≤ √L · √L. For √L ≥ 4, log L ≤ √L · √L ≤ √L · exp(√L)/4
  --   (using exp(x) ≥ 4 for x ≥ log 4 ≈ 1.39). So 4 log L ≤ exp(√L).
  --
  -- Let me prove this step by step.
  have hL_ge_one : (1 : ℝ) ≤ L := by
    -- B = L^2 ≥ 2, so L^2 ≥ 2, hence L ≥ √2 > 1
    have : 2 ≤ (L : ℝ)^2 := by
      have := hB
      show 2 ≤ lowerHWindowB L
      exact this
    have hL_sq_ge : (L : ℝ)^2 ≥ 2 := this
    have : (L : ℝ) ≥ 0 := Nat.cast_nonneg L
    nlinarith [hL_sq_ge]
  have hlogB_le_exp : Real.log BL ≤ Real.exp (t / 2) := by
    -- Chain: log B ≤ t/2 ≤ exp(t/2). (b) standard, (a) via tower bound + case split.
    have ht_half_le_exp : t / 2 ≤ Real.exp (t / 2) := by
      have := Real.add_one_le_exp (t / 2); linarith
    apply le_trans _ ht_half_le_exp
    have hBL_eq : BL = (L : ℝ)^2 := by show lowerHWindowB L = (L : ℝ)^2; rfl
    rw [hBL_eq]
    rw [Real.log_pow]
    push_cast
    -- Goal: 2 * Real.log ↑L ≤ t / 2. Suffices: 4 * log L ≤ t.
    suffices h : 4 * Real.log (L : ℝ) ≤ t by linarith
    -- Three cases on L: ≤ 3, [4, 15], ≥ 16.
    by_cases hL_le_3 : L ≤ 3
    · -- L ≤ 3: 4 log L ≤ tower 1 ≤ t (via m_k ≥ 1)
      have hL_real_le_3 : (L : ℝ) ≤ 3 := by exact_mod_cast hL_le_3
      have h1 := four_log_le_tower_one_of_le_three hL_ge_one hL_real_le_3
      have hmk_ge_one : 1 ≤ lowerHWindowM L k := by
        unfold lowerHWindowM lowerHWindowM0
        have h1' : 1 ≤ ⌊Real.sqrt L⌋₊ := by
          apply Nat.le_floor; push_cast
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_le_sqrt hL_ge_one
        omega
      have h_t1_le_t : tower 1 ≤ t :=
        (strictMono_nat_of_lt_succ tower_lt_succ).monotone hmk_ge_one
      linarith
    · push_neg at hL_le_3
      by_cases hL_le_15 : L ≤ 15
      · -- 4 ≤ L ≤ 15: 4 log L ≤ tower 2 ≤ t (via m_k ≥ 2)
        have hL_real_ge_4 : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_le_3
        have hL_real_le_15 : (L : ℝ) ≤ 15 := by exact_mod_cast hL_le_15
        have h1 := four_log_le_tower_two_of_le_fifteen hL_real_ge_4 hL_real_le_15
        have hmk_ge_two : 2 ≤ lowerHWindowM L k := by
          unfold lowerHWindowM lowerHWindowM0
          have h1' : 2 ≤ ⌊Real.sqrt L⌋₊ := by
            apply Nat.le_floor; push_cast
            rw [show (2 : ℝ) = Real.sqrt 4 by
              rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
            exact Real.sqrt_le_sqrt hL_real_ge_4
          omega
        have h_t2_le_t : tower 2 ≤ t :=
          (strictMono_nat_of_lt_succ tower_lt_succ).monotone hmk_ge_two
        linarith
      · -- L ≥ 16: 4 log L ≤ exp(√L) ≤ exp(m_k + 1) ≤ tower m_k = t
        push_neg at hL_le_15
        have hL_real_ge_16 : (16 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_le_15
        have h1 := four_log_le_exp_sqrt_of_ge_16 hL_real_ge_16
        have h_floor_lt : Real.sqrt L < (⌊Real.sqrt L⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have hmk_ge_m0 : lowerHWindowM L k ≥ lowerHWindowM0 L := by
          unfold lowerHWindowM; omega
        have hm0_eq : lowerHWindowM0 L = ⌊Real.sqrt L⌋₊ := rfl
        have h_sqrt_le : Real.sqrt L ≤ (lowerHWindowM L k : ℝ) + 1 := by
          have : (lowerHWindowM0 L : ℝ) ≤ (lowerHWindowM L k : ℝ) := by
            exact_mod_cast hmk_ge_m0
          rw [hm0_eq] at this
          linarith
        have h_exp_le : Real.exp (Real.sqrt L) ≤ Real.exp ((lowerHWindowM L k : ℝ) + 1) :=
          Real.exp_le_exp.mpr h_sqrt_le
        have h_tower_ge : Real.exp ((lowerHWindowM L k : ℝ) + 1) ≤ t :=
          tower_ge_exp_succ _
        linarith
  -- Step 7: combine. log B ≤ exp(t/2) ≤ exp(t) - exp(t/2). Hence log B + exp(t/2) ≤ exp(t).
  -- This means B ≤ exp(exp(t) - exp(t/2)), i.e., B * exp(exp(t/2)) ≤ exp(exp(t)). Good.
  have hsum_ineq : Real.log BL + Real.exp (t/2) ≤ Real.exp t := by linarith
  -- Convert to multiplicative form: B * exp(exp(t/2)) ≤ exp(exp(t)).
  rw [show Real.exp (Real.exp (t / 2)) * BL = BL * Real.exp (Real.exp (t / 2)) from by ring]
  rw [← Real.exp_log hB_pos]
  rw [show Real.exp (Real.log BL) * Real.exp (Real.exp (t / 2)) =
      Real.exp (Real.log BL + Real.exp (t / 2)) from by rw [← Real.exp_add]]
  exact Real.exp_le_exp.mpr hsum_ineq

/-- **Successor candidate bound (paper line 1133):** `q ∈ Q_k(p) → q ≤ ⌊y_{k+1}⌋₊`. -/
private lemma lowerHSuccessorCandidate_le_y_succ_floor
    {L k p q : ℕ} (hB : 2 ≤ lowerHWindowB L)
    (hq : q ∈ lowerHSuccessorCandidates L k p) :
    q ≤ ⌊lowerHWindowY L (k + 1)⌋₊ := by
  rw [lowerHSuccessorCandidates] at hq
  simp only [Finset.mem_filter, Finset.mem_Iic] at hq
  -- q ≤ ⌊exp(exp((B/2)*y_k))⌋₊
  have hq_le_cand : q ≤ ⌊Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L k))⌋₊ :=
    hq.1
  -- ⌊exp(exp((B/2)*y_k))⌋₊ ≤ ⌊y_{k+1}⌋₊ via the analytic bound
  exact hq_le_cand.trans (Nat.floor_le_floor (exp_exp_half_le_y_succ hB))

/-- y_k is monotone in k (since m_k = m_0 + 2k is monotone and tower is monotone). -/
private lemma lowerHWindowY_mono_k {L : ℕ} (hB : 2 ≤ lowerHWindowB L)
    {k k' : ℕ} (hkk' : k ≤ k') :
    lowerHWindowY L k ≤ lowerHWindowY L k' := by
  unfold lowerHWindowY
  have hB_pos : 0 < lowerHWindowB L := by linarith
  have hm_le : lowerHWindowM L k ≤ lowerHWindowM L k' := by
    unfold lowerHWindowM; omega
  have htower_le : tower (lowerHWindowM L k) ≤ tower (lowerHWindowM L k') :=
    (strictMono_nat_of_lt_succ tower_lt_succ).monotone hm_le
  exact div_le_div_of_nonneg_right htower_le hB_pos.le

/-- ⌊y_k⌋₊ is monotone in k. -/
private lemma lowerHWindowY_floor_mono_k {L : ℕ} (hB : 2 ≤ lowerHWindowB L)
    {k k' : ℕ} (hkk' : k ≤ k') :
    ⌊lowerHWindowY L k⌋₊ ≤ ⌊lowerHWindowY L k'⌋₊ :=
  Nat.floor_le_floor (lowerHWindowY_mono_k hB hkk')

/-- **Successor candidate bounded by `⌊y_j⌋₊`** when `k+1 ≤ j` (paper line 1124-1128). -/
private lemma lowerHSuccessorCandidate_le_y_j_floor
    {L k j p q : ℕ} (hB : 2 ≤ lowerHWindowB L) (hkj : k + 1 ≤ j)
    (hq : q ∈ lowerHSuccessorCandidates L k p) :
    q ≤ ⌊lowerHWindowY L j⌋₊ :=
  (lowerHSuccessorCandidate_le_y_succ_floor hB hq).trans
    (lowerHWindowY_floor_mono_k hB hkj)

/-- **Initial selected prime bounded by `⌊y_j⌋₊`** (paper line 1124-1125). -/
private lemma lowerHInitialSelectedPrime_le_y_j_floor
    {L j n q : ℕ} (hB : 2 ≤ lowerHWindowB L)
    (hq : q ∈ lowerHInitialSelectedPrimes L n) :
    q ≤ ⌊lowerHWindowY L j⌋₊ := by
  rw [lowerHInitialSelectedPrimes] at hq
  simp only [Finset.mem_filter, Finset.mem_Iic] at hq
  exact hq.1.trans (lowerHWindowY_floor_mono_k hB (Nat.zero_le j))

/-- **Tighter periodicity for initial primes** (using `⌊y_j⌋₊` modulus). -/
private lemma lowerHInitialSelectedPrimes_eq_of_mod_y_j_floor
    {L j n n' : ℕ} (hB : 2 ≤ lowerHWindowB L)
    (hmod : n % primorial ⌊lowerHWindowY L j⌋₊ =
      n' % primorial ⌊lowerHWindowY L j⌋₊) :
    lowerHInitialSelectedPrimes L n = lowerHInitialSelectedPrimes L n' := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    rw [lowerHInitialSelectedPrimes] at hq ⊢
    simp only [Finset.mem_filter, Finset.mem_Iic] at hq ⊢
    rcases hq with ⟨hqfloor, hqprime, hqdiv, hqY⟩
    have hqmem : q ∈ lowerHInitialSelectedPrimes L n := by
      rw [lowerHInitialSelectedPrimes]
      simp [hqfloor, hqprime, hqdiv, hqY]
    have hqle := lowerHInitialSelectedPrime_le_y_j_floor (j := j) hB hqmem
    exact ⟨hqfloor, hqprime, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mp hqdiv, hqY⟩
  · intro hq
    rw [lowerHInitialSelectedPrimes] at hq ⊢
    simp only [Finset.mem_filter, Finset.mem_Iic] at hq ⊢
    rcases hq with ⟨hqfloor, hqprime, hqdiv, hqY⟩
    have hqmem : q ∈ lowerHInitialSelectedPrimes L n' := by
      rw [lowerHInitialSelectedPrimes]
      simp [hqfloor, hqprime, hqdiv, hqY]
    have hqle := lowerHInitialSelectedPrime_le_y_j_floor (j := j) hB hqmem
    exact ⟨hqfloor, hqprime, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mpr hqdiv, hqY⟩

/-- **Tighter periodicity for selected successors** (using `⌊y_j⌋₊` modulus). -/
private lemma lowerHSelectedSuccessors_eq_of_mod_y_j_floor
    {L k j p n n' : ℕ} (hB : 2 ≤ lowerHWindowB L) (hkj : k + 1 ≤ j)
    (hmod : n % primorial ⌊lowerHWindowY L j⌋₊ =
      n' % primorial ⌊lowerHWindowY L j⌋₊) :
    lowerHSelectedSuccessors L k p n = lowerHSelectedSuccessors L k p n' := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    rw [lowerHSelectedSuccessors] at hq ⊢
    simp only [Finset.mem_filter] at hq ⊢
    rcases hq with ⟨hqcand, hqdiv⟩
    have hqcand' := hqcand
    rw [lowerHSuccessorCandidates] at hqcand'
    simp only [Finset.mem_filter, Finset.mem_Iic] at hqcand'
    have hqprime : q.Prime := hqcand'.2.1
    have hqle := lowerHSuccessorCandidate_le_y_j_floor (L := L) (k := k) (j := j)
      (p := p) hB hkj hqcand
    exact ⟨hqcand, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mp hqdiv⟩
  · intro hq
    rw [lowerHSelectedSuccessors] at hq ⊢
    simp only [Finset.mem_filter] at hq ⊢
    rcases hq with ⟨hqcand, hqdiv⟩
    have hqcand' := hqcand
    rw [lowerHSuccessorCandidates] at hqcand'
    simp only [Finset.mem_filter, Finset.mem_Iic] at hqcand'
    have hqprime : q.Prime := hqcand'.2.1
    have hqle := lowerHSuccessorCandidate_le_y_j_floor (L := L) (k := k) (j := j)
      (p := p) hB hkj hqcand
    exact ⟨hqcand, (dvd_iff_of_mod_primorial_eq hqprime hqle hmod).mpr hqdiv⟩

/-- **Paper §5.2 line 1142:** every chain prime `p_j` (returned by
`lowerHGreedyPrime?`) is bounded by `⌊y_j⌋₊`.

For `j = 0`: `p_0` comes from `lowerHInitialSelectedPrimes ⊆ Iic ⌊y_0⌋₊`.
For `j ≥ 1`: `p_j` comes from `lowerHSuccessorCandidates L (j-1) p_prev` ⊆
  `Iic ⌊y_j⌋₊` (via `lowerHSuccessorCandidate_le_y_succ_floor`). -/
private lemma lowerHGreedyPrime?_le_y_j_floor
    {L j r p : ℕ} (hB : 2 ≤ lowerHWindowB L)
    (hp : lowerHGreedyPrime? L r j = some p) :
    p ≤ ⌊lowerHWindowY L j⌋₊ := by
  cases j with
  | zero =>
    unfold lowerHGreedyPrime? at hp
    have hp_mem := finsetLeastNat?_mem hp
    rw [lowerHInitialSelectedPrimes] at hp_mem
    simp only [Finset.mem_filter, Finset.mem_Iic] at hp_mem
    exact hp_mem.1
  | succ k =>
    unfold lowerHGreedyPrime? at hp
    cases hp_prev : lowerHGreedyPrime? L r k with
    | none => simp [hp_prev] at hp
    | some p_prev =>
      have hp_mem : p ∈ lowerHSelectedSuccessors L k p_prev r :=
        finsetLeastNat?_mem (by simpa [hp_prev] using hp)
      rw [lowerHSelectedSuccessors] at hp_mem
      simp only [Finset.mem_filter] at hp_mem
      have hp_in_cand : p ∈ lowerHSuccessorCandidates L k p_prev := hp_mem.1
      exact lowerHSuccessorCandidate_le_y_succ_floor hB hp_in_cand

/-- **Phase 1D — paper line 1156:** `lowerHGreedyPrime? L · k` for `k ≤ j` is
periodic modulo `primorial(⌊y_j⌋₊)`. -/
private lemma lowerHGreedyPrime?_eq_of_mod_y_j_floor {L j k n n' : ℕ}
    (hB : 2 ≤ lowerHWindowB L) (hkj : k ≤ j)
    (hmod : n % primorial ⌊lowerHWindowY L j⌋₊ =
      n' % primorial ⌊lowerHWindowY L j⌋₊) :
    lowerHGreedyPrime? L n k = lowerHGreedyPrime? L n' k := by
  induction k with
  | zero =>
      simp [lowerHGreedyPrime?, lowerHInitialSelectedPrimes_eq_of_mod_y_j_floor hB hmod]
  | succ k ih =>
      have hk_le_j : k ≤ j := Nat.le_of_succ_le hkj
      have ih' := ih hk_le_j
      rw [lowerHGreedyPrime?, lowerHGreedyPrime?, ih']
      cases hgp : lowerHGreedyPrime? L n' k with
      | none => rfl
      | some p =>
          simp [lowerHSelectedSuccessors_eq_of_mod_y_j_floor (L := L) (k := k) (j := j)
            (p := p) hB hkj hmod]

/-- **Paper §5.2 line 1146 ("for L large"):** `lowerHWindowY L j → ∞` as `L → ∞`.

Proof chain:
- `tower(m) ≥ exp(m+1)` (`tower_ge_exp_succ`).
- `m_j(L) = ⌊√L⌋ + 2j ≥ √L + 2j - 1` (floor lower bound).
- So `tower(m_j(L)) ≥ exp(√L + 2j) = exp(2j) · exp(√L)`.
- `lowerHWindowY L j = tower(m_j(L)) / L² ≥ exp(2j) · exp(√L) / L²`.
- `exp(√L)/L² = exp(√L)/(√L)^4 → ∞` via `Real.tendsto_exp_div_pow_atTop 4` at `x = √L`.
- Multiply by positive constant `exp(2j)` to conclude. -/
private lemma lowerHWindowY_tendsto_atTop (j : ℕ) :
    Filter.Tendsto (fun L : ℕ => lowerHWindowY L j) Filter.atTop Filter.atTop := by
  -- Step 1: `(L : ℝ) → ∞` as `L : ℕ → ∞`.
  have hLreal : Filter.Tendsto (fun L : ℕ => (L : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  -- Step 2: `Real.sqrt L → ∞` as `L → ∞`.
  have hsqrt : Filter.Tendsto (fun L : ℕ => Real.sqrt L) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hLreal
  -- Step 3: `exp(√L) / (√L)^4 → ∞`. (Note (√L)^4 = L² for L ≥ 0.)
  have hexp_pow : Filter.Tendsto
      (fun L : ℕ => Real.exp (Real.sqrt L) / (Real.sqrt L)^4)
      Filter.atTop Filter.atTop :=
    (Real.tendsto_exp_div_pow_atTop 4).comp hsqrt
  -- Step 4: `(√L)^4 = L²` (for L : ℕ ≥ 0).
  have hpow4_eq : ∀ L : ℕ, (Real.sqrt L)^4 = (L : ℝ)^2 := by
    intro L
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL
    calc (Real.sqrt L)^4 = (Real.sqrt L ^ 2)^2 := by ring
      _ = (L : ℝ)^2 := by rw [hsq]
  -- Step 5: Hence `exp(√L) / L² → ∞`.
  have hexp_L2 : Filter.Tendsto
      (fun L : ℕ => Real.exp (Real.sqrt L) / (L : ℝ)^2)
      Filter.atTop Filter.atTop := by
    have heq : (fun L : ℕ => Real.exp (Real.sqrt L) / (Real.sqrt L)^4) =
               (fun L : ℕ => Real.exp (Real.sqrt L) / (L : ℝ)^2) := by
      funext L; rw [hpow4_eq]
    rw [heq] at hexp_pow
    exact hexp_pow
  -- Step 6: Multiply by `exp(2j) > 0` to get `exp(2j) · exp(√L)/L² → ∞`.
  have hconst_pos : (0 : ℝ) < Real.exp (2 * j) := Real.exp_pos _
  have hexp_2j_L2 : Filter.Tendsto
      (fun L : ℕ => Real.exp (2 * j) * (Real.exp (Real.sqrt L) / (L : ℝ)^2))
      Filter.atTop Filter.atTop :=
    hexp_L2.const_mul_atTop hconst_pos
  -- Step 7: Show `lowerHWindowY L j ≥ exp(2j) · exp(√L) / L²` eventually.
  -- y_j(L) = tower(⌊√L⌋+2j)/L² ≥ exp(⌊√L⌋+2j+1)/L² ≥ exp(√L+2j)/L² = exp(2j)·exp(√L)/L².
  have hbound : ∀ L : ℕ, 1 ≤ L →
      Real.exp (2 * j) * (Real.exp (Real.sqrt L) / (L : ℝ)^2) ≤ lowerHWindowY L j := by
    intro L hL
    have hL_pos : (0 : ℝ) < L := by exact_mod_cast hL
    have hL_pos_sq : (0 : ℝ) < (L : ℝ)^2 := by positivity
    -- tower(m_j) ≥ exp(m_j + 1)
    have htower_ge : Real.exp ((lowerHWindowM L j : ℝ) + 1) ≤
        tower (lowerHWindowM L j) := tower_ge_exp_succ _
    -- m_j + 1 ≥ √L + 2j (via ⌊√L⌋ + 1 ≥ √L).
    have hmj_ge : Real.sqrt L + 2 * j ≤ (lowerHWindowM L j : ℝ) + 1 := by
      unfold lowerHWindowM lowerHWindowM0
      have hfloor_lt : Real.sqrt L < (⌊Real.sqrt L⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      push_cast
      linarith
    -- So tower(m_j) ≥ exp(√L + 2j) = exp(2j) · exp(√L).
    have htower_ge' : Real.exp (Real.sqrt L + 2 * j) ≤ tower (lowerHWindowM L j) :=
      (Real.exp_le_exp.mpr hmj_ge).trans htower_ge
    have hexp_split : Real.exp (Real.sqrt L + 2 * j) =
        Real.exp (2 * j) * Real.exp (Real.sqrt L) := by
      rw [Real.exp_add]; ring
    rw [hexp_split] at htower_ge'
    -- Now: lowerHWindowY = tower / lowerHWindowB = tower / L²
    show Real.exp (2 * j) * (Real.exp (Real.sqrt L) / (L : ℝ)^2) ≤
         tower (lowerHWindowM L j) / lowerHWindowB L
    have hB_eq : lowerHWindowB L = (L : ℝ)^2 := rfl
    rw [hB_eq]
    rw [show Real.exp (2 * j) * (Real.exp (Real.sqrt L) / (L : ℝ)^2) =
        (Real.exp (2 * j) * Real.exp (Real.sqrt L)) / (L : ℝ)^2 from by ring]
    exact div_le_div_of_nonneg_right htower_ge' hL_pos_sq.le
  -- Step 8: Squeeze: f ≤ y_j eventually, f → ∞ ⟹ y_j → ∞.
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hexp_2j_L2
  exact Filter.eventually_atTop.mpr ⟨1, hbound⟩

/-- For any threshold `y₀`, eventually `y_j ≥ y₀` as `L → ∞`. Direct application of
`lowerHWindowY_tendsto_atTop`. -/
private lemma lowerHWindowY_eventually_ge (j : ℕ) (y₀ : ℝ) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L → y₀ ≤ lowerHWindowY L j := by
  have h : ∀ᶠ L : ℕ in Filter.atTop, y₀ ≤ lowerHWindowY L j :=
    (lowerHWindowY_tendsto_atTop j).eventually_ge_atTop y₀
  rcases h.exists with ⟨N, hN⟩
  -- `h.exists` gives some N satisfying property, but we want ∀ L ≥ N.
  -- Use the eventually structure directly.
  rw [Filter.eventually_atTop] at h
  exact h

/-- Product-model stage-failure estimate (paper §5.2 lines 1162-1170).

`hyj_thresh` encodes paper line 1146's "for L large" condition. -/
private lemma stage_h_pmodel_failure_prob (j L : ℕ)
    (hB : 2 ≤ lowerHWindowB L)
    (hyj_thresh : Classical.choose (prime_successor_mass 2 (by norm_num : (2:ℝ) ≤ 2))
                  ≤ lowerHWindowY L j) :
    lowerHStageFailureResidueProb L j ≤ Real.exp (-(lowerHWindowB L) / 8) := by
  classical
  -- Setup
  set B := lowerHWindowB L with hB_def
  set yj := lowerHWindowY L j with hyj_def
  set stage_cut : ℕ := lowerHStageCutoff L j with hsc_def
  set M : ℕ := primorial stage_cut with hM_def
  have hMpos : 0 < M := primorial_pos _
  have hMreal_pos : (0 : ℝ) < M := by exact_mod_cast hMpos
  -- Goal: card{r : Fin M | LBSF L j r.val} / M ≤ exp(-B/8)
  unfold lowerHStageFailureResidueProb
  rw [div_le_iff₀ hMreal_pos]
  -- Goal: card{r : Fin M | LBSF L j r.val} ≤ exp(-B/8) * M
  --
  -- Bridge to Finset.range form
  rw [fin_card_subtype_eq_range_filter_card]
  -- Index the decomposition by primes ≤ ⌊y_j⌋₊ (paper §5.2 line 1142: p_j ≤ y_j).
  set yj_floor_for_S : ℕ := ⌊yj⌋₊ with hyj_floor_for_S_def
  set S : Finset ℕ := (Finset.Iic yj_floor_for_S).filter Nat.Prime with hS_def
  -- Bound: every p_j(r) is ≤ ⌊y_j⌋₊ by paper §5.2 line 1142.
  have hS_bound : ∀ r p, r ∈ Finset.range M →
      lowerHGreedyPrime? L r j = some p → p ∈ S := by
    intro r p _ hgp
    have hp_prime := (lowerHGreedyPrime?_prime_dvd hgp).1
    have hp_le_yj_floor : p ≤ yj_floor_for_S := lowerHGreedyPrime?_le_y_j_floor hB hgp
    simp [hS_def, hp_prime, hp_le_yj_floor]
  -- Decompose the bad set as a disjoint union over p:
  rw [lowerHStageFailure_finset_card_eq_sum_by_prime L j M S hS_bound]
  -- Goal: ↑(∑ p ∈ S, card{Pa(p) ∧ Pb(p)}) ≤ exp(-B/8) * M
  --
  -- Phase 2 assembly: paper §5.2 lines 1158-1170.
  set yj_floor : ℕ := ⌊yj⌋₊ with hyj_floor_def
  set a : ℕ := primorial yj_floor with ha_def
  have ha_pos : 0 < a := primorial_pos _
  -- ⌊y_j⌋₊ ≤ stage_cut (already proven inline below)
  have hyj_floor_le_cut : yj_floor ≤ stage_cut := by
    show ⌊yj⌋₊ ≤ lowerHStageCutoff L j
    unfold lowerHStageCutoff
    apply Nat.floor_le_floor
    unfold lowerHWindowY
    have hB_pos : 0 < lowerHWindowB L := by linarith
    have hyj_nn : 0 ≤ lowerHWindowY L j := by
      unfold lowerHWindowY
      exact div_nonneg (tower_pos _).le hB_pos.le
    calc lowerHWindowY L j
        ≤ Real.exp (lowerHWindowY L j) := by
          have := Real.add_one_le_exp (lowerHWindowY L j); linarith
      _ ≤ Real.exp (Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j)) := by
          apply Real.exp_le_exp.mpr
          calc lowerHWindowY L j
              ≤ Real.exp (lowerHWindowY L j) := by
                have := Real.add_one_le_exp (lowerHWindowY L j); linarith
            _ ≤ Real.exp ((lowerHWindowB L / 2) * lowerHWindowY L j) := by
                apply Real.exp_le_exp.mpr
                have hB_half : 1 ≤ lowerHWindowB L / 2 := by linarith
                nlinarith [hyj_nn, hB_half]
  have ha_dvd_M : a ∣ M := by
    show primorial yj_floor ∣ primorial stage_cut
    -- primorial(a) | primorial(b) when a ≤ b
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Iic] at hp ⊢
    exact ⟨hp.1.trans hyj_floor_le_cut, hp.2⟩
  -- Per-branch identity: card{Pa ∧ Pb}(p) = card{Pa}(p) · ∏(1-1/q) for each p ∈ S
  -- Then sum and use mass bound + disjointness.
  --
  -- First, push_cast the sum to reals
  push_cast
  rw [show (∑ p ∈ S, ((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p ∧
        ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r)).card : ℝ) =
      ∑ p ∈ S, (((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p ∧
        ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r)).card : ℝ) from by rfl]
  -- **Phase 2 — Paper §5.2 lines 1158-1170 assembly.**
  -- Strategy: per-branch CRT factorization + mass bound + sum disjointness.
  --
  -- Sub-claim (i): Per-branch CRT identity (paper line 1158):
  -- For each p ∈ S, card{r ∈ [0,M) : Pa ∧ Pb} = card{r ∈ [0,M) : Pa} · ∏(1-1/q).
  have hper_branch : ∀ p ∈ S,
      (((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p ∧
          ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r)).card : ℝ) =
      (((Finset.range M).filter
          (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ) *
      (∏ q ∈ lowerHSuccessorCandidates L j p, (1 - 1 / (q : ℝ))) := by
    intro p hp
    -- **Paper §5.2 line 1158 CRT independence.**
    -- Setup: a := primorial(yj_floor), b := ∏ Q_j(p).
    -- Pa = "p_j(r) = p" periodic mod a (proven via lowerHGreedyPrime?_eq_of_mod_y_j_floor).
    -- Pb = "no q ∈ Q_j(p) divides r" periodic mod b (direct).
    -- a, b coprime (Q_j(p) primes > yj > yj_floor); a·b ∣ M.
    -- Apply pmodel_crt_factored_count_lifted, then simplify via Pa block count + Pb avoid count.
    classical
    set Q := lowerHSuccessorCandidates L j p with hQ_def
    set a : ℕ := primorial yj_floor_for_S with ha_def
    set b : ℕ := ∏ q ∈ Q, q with hb_def
    -- Q-primes are prime
    have hQ_prime : ∀ q ∈ Q, q.Prime := by
      intro q hq
      rw [hQ_def, lowerHSuccessorCandidates] at hq
      simp only [Finset.mem_filter, Finset.mem_Iic] at hq
      exact hq.2.1
    -- Q-primes are > yj_floor (paper line 1158: q > exp(exp y_j) > y_j ≥ ⌊y_j⌋₊)
    have hQ_gt_yj : ∀ q ∈ Q, (yj_floor_for_S : ℝ) < q := by
      intro q hq
      rw [hQ_def, lowerHSuccessorCandidates] at hq
      simp only [Finset.mem_filter, Finset.mem_Iic] at hq
      -- yj_floor = ⌊yj⌋₊ ≤ yj < exp(yj) ≤ exp(exp yj) < q
      have hq_gt_exp_exp : Real.exp (Real.exp (lowerHWindowY L j)) < (q : ℝ) :=
        hq.2.2.2.1
      have hyj_nn : 0 ≤ lowerHWindowY L j := by
        unfold lowerHWindowY; have hB_pos : 0 < lowerHWindowB L := by linarith
        exact div_nonneg (tower_pos _).le hB_pos.le
      have hyj_le_exp : lowerHWindowY L j ≤ Real.exp (lowerHWindowY L j) := by
        have := Real.add_one_le_exp (lowerHWindowY L j); linarith
      have hyj_le_exp_exp : lowerHWindowY L j ≤ Real.exp (Real.exp (lowerHWindowY L j)) :=
        hyj_le_exp.trans (by
          have := Real.add_one_le_exp (Real.exp (lowerHWindowY L j))
          linarith)
      have hfloor_le : (yj_floor_for_S : ℝ) ≤ lowerHWindowY L j := by
        show (⌊lowerHWindowY L j⌋₊ : ℝ) ≤ lowerHWindowY L j
        exact Nat.floor_le hyj_nn
      linarith
    -- Q-primes are > yj_floor (Nat version)
    have hQ_gt_yj_nat : ∀ q ∈ Q, yj_floor_for_S < q := by
      intro q hq
      have h := hQ_gt_yj q hq
      exact_mod_cast h
    -- a, b > 0
    have ha_pos : 0 < a := primorial_pos _
    have hb_pos : 0 < b := by
      rw [hb_def]; exact Finset.prod_pos (fun q hq => (hQ_prime q hq).pos)
    -- Coprime a b: every q ∈ Q is > yj_floor, so q ∉ {primes ≤ yj_floor}, so coprime to a.
    have hcop : Nat.Coprime a b := by
      rw [ha_def, hb_def]
      apply Nat.Coprime.prod_right
      intro q hq
      -- primorial yj_floor coprime to q (which is > yj_floor)
      apply Nat.Coprime.prod_left
      intro p' hp'
      simp only [Finset.mem_filter, Finset.mem_Iic] at hp'
      have hp'_prime : p'.Prime := hp'.2
      have hq_prime : q.Prime := hQ_prime q hq
      have hp'_le : p' ≤ yj_floor_for_S := hp'.1
      have hq_gt : yj_floor_for_S < q := hQ_gt_yj_nat q hq
      have hp'_ne_q : p' ≠ q := fun heq => by omega
      exact (Nat.coprime_primes hp'_prime hq_prime).mpr hp'_ne_q
    -- a · b ∣ M: a ∣ M (proven), b ∣ M (Q ⊆ primes ≤ stage_cut), coprime ⟹ product ∣ M.
    have hb_dvd_M : b ∣ M := by
      rw [hb_def]
      show (∏ q ∈ Q, q) ∣ primorial stage_cut
      unfold primorial
      apply Finset.prod_dvd_prod_of_subset
      intro q hq
      rw [hQ_def, lowerHSuccessorCandidates] at hq
      simp only [Finset.mem_filter, Finset.mem_Iic] at hq
      simp only [Finset.mem_filter, Finset.mem_Iic]
      refine ⟨?_, hq.2.1⟩
      -- q ≤ stage_cut: q ≤ ⌊exp(exp((B/2)*y_j))⌋₊ = stage_cut
      show q ≤ lowerHStageCutoff L j
      unfold lowerHStageCutoff
      exact hq.1
    have hab_dvd : a * b ∣ M := (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ha_dvd_M hb_dvd_M)
    -- Pa periodic mod a
    have hPa_periodic : ∀ r r', r % a = r' % a →
        ((lowerHGreedyPrime? L r j = some p) ↔ (lowerHGreedyPrime? L r' j = some p)) := by
      intro r r' hmod
      have h_eq := lowerHGreedyPrime?_eq_of_mod_y_j_floor (k := j) (j := j) (n := r) (n' := r')
        hB (le_refl j) hmod
      rw [h_eq]
    -- Pb periodic mod b: divisibility by q ∈ Q periodic mod b (since q ∣ b).
    have hPb_periodic : ∀ r r', r % b = r' % b →
        ((∀ q ∈ Q, ¬ q ∣ r) ↔ (∀ q ∈ Q, ¬ q ∣ r')) := by
      intro r r' hmod
      have hdvd_iff : ∀ q ∈ Q, (q ∣ r ↔ q ∣ r') := by
        intro q hq
        have hq_dvd_b : q ∣ b := by rw [hb_def]; exact Finset.dvd_prod_of_mem _ hq
        have hr_modEq : r ≡ r' [MOD b] := hmod
        exact hr_modEq.dvd_iff hq_dvd_b
      constructor
      · intro h q hq hq_dvd_r'
        exact h q hq ((hdvd_iff q hq).mpr hq_dvd_r')
      · intro h q hq hq_dvd_r
        exact h q hq ((hdvd_iff q hq).mp hq_dvd_r)
    -- Apply pmodel_crt_factored_count_lifted
    have hcrt :
        ((Finset.range M).filter (fun r => (lowerHGreedyPrime? L r j = some p) ∧
            (∀ q ∈ Q, ¬ q ∣ r))).card =
        (M / (a * b)) *
          (((Finset.range a).filter (fun r => lowerHGreedyPrime? L r j = some p)).card *
           ((Finset.range b).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r)).card) :=
      pmodel_crt_factored_count_lifted ha_pos hb_pos hcop hab_dvd
        (fun r => lowerHGreedyPrime? L r j = some p)
        (fun r => ∀ q ∈ Q, ¬ q ∣ r)
        hPa_periodic hPb_periodic
    -- card{Pb in [0, b)} = b · ∏(1-1/q) via pmodel_count_avoid_primes_eq
    have hPb_count : (((Finset.range b).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r)).card : ℝ) =
        (b : ℝ) * ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by
      apply pmodel_count_avoid_primes_eq hQ_prime hb_pos
      rw [hb_def]
    -- card{Pa in [0, M)} = (M/a) · card{Pa in [0, a)} via pmodel_block_count_periodic
    -- M = a · (M/a) for a ∣ M
    obtain ⟨k, hk_def⟩ := ha_dvd_M
    have hk_eq : M / a = k := by
      rw [hk_def]; exact Nat.mul_div_cancel_left k ha_pos
    have hPa_block :
        ((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p)).card =
        k * ((Finset.range a).filter (fun r => lowerHGreedyPrime? L r j = some p)).card := by
      rw [hk_def]
      exact pmodel_block_count_periodic hPa_periodic
    -- M = a · b · (M/(a·b)) for a·b ∣ M
    obtain ⟨k', hk'_def⟩ := hab_dvd
    have hk'_eq : M / (a * b) = k' := by
      rw [hk'_def]
      exact Nat.mul_div_cancel_left k' (Nat.mul_pos ha_pos hb_pos)
    -- Combine: card{Pa ∧ Pb in [0, M)} = (M/(a·b)) · card{Pa in a} · card{Pb in b}.
    -- Show: (M/(a·b)) · card{Pa in a} = card{Pa in [0, M)} / b.
    -- (M/(a·b)) · card{Pa in a} = (M/(a·b)) · ((M/a)/(M/a)) ·  card{Pa in a} = ((M/a)/b) · ((M/a) · card{Pa in a}/M) · (M)
    --
    -- Cleaner: card{Pa ∧ Pb in [0, M)} = (M/(a·b)) · card{Pa in a} · b · ∏(1-1/q)
    --                                  = (M·b/(a·b)) · card{Pa in a} · ∏(1-1/q)
    --                                  = (M/a) · card{Pa in a} · ∏(1-1/q)
    --                                  = card{Pa in [0,M)} · ∏(1-1/q)
    rw [show ((((Finset.range M).filter (fun r => (lowerHGreedyPrime? L r j = some p) ∧
                  ∀ q ∈ Q, ¬ q ∣ r)).card : ℕ) : ℝ) =
        ((M / (a * b) *
          (((Finset.range a).filter (fun r => lowerHGreedyPrime? L r j = some p)).card *
            ((Finset.range b).filter (fun r => ∀ q ∈ Q, ¬ q ∣ r)).card) : ℕ) : ℝ) from by
      exact_mod_cast hcrt]
    push_cast
    rw [hPb_count]
    rw [show (((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ) =
        ((k * ((Finset.range a).filter (fun r => lowerHGreedyPrime? L r j = some p)).card : ℕ) : ℝ) from by
      exact_mod_cast hPa_block]
    push_cast
    -- Goal: (M/(a·b)) · card{Pa in a} · (b · ∏(1-1/q)) = (k · card{Pa in a}) · ∏(1-1/q)
    -- Use M = a·b·k', a·k = M, so b·k = a·b·k'/a = b·k', hence k = b·k'/b = k'...
    -- Actually: M = a·k (from hk_def) and M = a·b·k' (from hk'_def). So a·k = a·b·k', k = b·k'.
    have hk_bk' : k = b * k' := by
      have : a * k = a * (b * k') := by
        rw [← mul_assoc]; rw [← hk'_def]; rw [hk_def]
      exact Nat.eq_of_mul_eq_mul_left ha_pos this
    rw [hk_bk', hk'_eq]
    push_cast
    ring
  -- Sub-claim (ii): Per-branch mass bound (paper line 1166-1170):
  -- For each p ∈ S with p ≤ y_j, ∏(1-1/q) ≤ exp(-B/8).
  have hmass_bound : ∀ p ∈ S,
      (∏ q ∈ lowerHSuccessorCandidates L j p, (1 - 1 / (q : ℝ))) ≤
      Real.exp (-(lowerHWindowB L) / 8) := by
    intro p hp
    -- Extract: p prime, p ≤ ⌊y_j⌋₊
    have hp_prime : p.Prime := by
      simp only [hS_def, Finset.mem_filter, Finset.mem_Iic] at hp
      exact hp.2
    have hp_le_yj_floor_nat : p ≤ yj_floor_for_S := by
      simp only [hS_def, Finset.mem_filter, Finset.mem_Iic] at hp
      exact hp.1
    -- Real version: p ≤ y_j
    have hyj_nn : 0 ≤ yj := by
      show 0 ≤ lowerHWindowY L j
      unfold lowerHWindowY
      have hB_pos : 0 < lowerHWindowB L := by linarith
      exact div_nonneg (tower_pos _).le hB_pos.le
    have hp_le_yj_real : (p : ℝ) ≤ yj := by
      have h1 : (p : ℝ) ≤ (yj_floor_for_S : ℝ) := by exact_mod_cast hp_le_yj_floor_nat
      have h2 : (yj_floor_for_S : ℝ) ≤ yj := by
        show (⌊yj⌋₊ : ℝ) ≤ yj
        exact Nat.floor_le hyj_nn
      linarith
    -- B ≥ 4 (since B = L² ≥ 2 with L Nat ⟹ L ≥ 2 ⟹ B ≥ 4)
    have hB_ge_4 : (4 : ℝ) ≤ lowerHWindowB L := by
      have h_sq : (2 : ℝ) ≤ (L : ℝ)^2 := by
        have := hB; show (2 : ℝ) ≤ (L : ℝ)^2; exact this
      have hL_nat : 2 ≤ L := by
        by_contra hLlt
        push_neg at hLlt
        interval_cases L
        · norm_num at h_sq
        · norm_num at h_sq
      have hL_real : (2 : ℝ) ≤ L := by exact_mod_cast hL_nat
      show (4 : ℝ) ≤ (L : ℝ)^2
      nlinarith
    -- Apply prime_successor_mass with B' = 2.
    -- Use `Classical.choose_spec` to extract the y₀ matching `hyj_thresh`.
    set pm := prime_successor_mass 2 (by norm_num : (2:ℝ) ≤ 2) with hpm_def
    set y₀ := Classical.choose pm with hy₀_def
    have hy₀_spec := Classical.choose_spec pm
    obtain ⟨hy₀_pos, hmass⟩ := hy₀_spec
    -- y_j ≥ y₀ from lemma hypothesis (paper line 1146 "for L large").
    have hyj_ge_y0 : y₀ ≤ yj := hyj_thresh
    -- η = B/2 ≥ 2 (since B ≥ 4)
    have hη_ge_two : (2 : ℝ) ≤ lowerHWindowB L / 2 := by linarith
    have hsum_lower := hmass yj hyj_ge_y0 p hp_prime hp_le_yj_real
      (lowerHWindowB L / 2) hη_ge_two
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hyj_pos : 0 < yj := by
      -- y_j > 0 since p ≤ y_j and p ≥ 2 > 0
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      linarith
    have hsum_ge_B8 : (lowerHWindowB L) / 8 ≤
        ∑ q ∈ Finset.filter
          (fun q => q.Prime ∧ q % p = 1 ∧
            Real.exp (Real.exp yj) < (q : ℝ) ∧
            (q : ℝ) ≤ Real.exp (Real.exp ((lowerHWindowB L / 2) * yj)))
          (Finset.Iic ⌊Real.exp (Real.exp ((lowerHWindowB L / 2) * yj))⌋₊),
        (1 : ℝ) / (q : ℝ) := by
      have h1 : (1 / 2 : ℝ) * (lowerHWindowB L / 2 - 1) * yj / p ≥ lowerHWindowB L / 8 := by
        have hyj_div_p : 1 ≤ yj / p := by
          rw [le_div_iff₀ hp_pos]; linarith
        have hB_half_minus_one : lowerHWindowB L / 4 ≤ lowerHWindowB L / 2 - 1 := by linarith
        have : (1 / 2 : ℝ) * (lowerHWindowB L / 2 - 1) * yj / p =
            (1 / 2 : ℝ) * (lowerHWindowB L / 2 - 1) * (yj / p) := by ring
        rw [this]
        have h_factor_pos : 0 < (1 / 2 : ℝ) * (lowerHWindowB L / 4) := by linarith
        nlinarith [hyj_div_p, hB_half_minus_one, sq_nonneg (lowerHWindowB L)]
      linarith [hsum_lower]
    -- Match the filter in lowerHSuccessorCandidates with the one above.
    have hcand_eq : lowerHSuccessorCandidates L j p =
        Finset.filter (fun q : ℕ => q.Prime ∧ q % p = 1 ∧
          Real.exp (Real.exp yj) < (q : ℝ) ∧
          (q : ℝ) ≤ Real.exp (Real.exp ((lowerHWindowB L / 2) * yj)))
          (Finset.Iic ⌊Real.exp (Real.exp ((lowerHWindowB L / 2) * yj))⌋₊) := by
      rw [lowerHSuccessorCandidates]
    -- Apply prod_one_sub_inv_le_exp_neg_sum + bound exp on monotone exp.
    have hQ_pos : ∀ q ∈ lowerHSuccessorCandidates L j p, 0 < q := by
      intro q hq
      rw [lowerHSuccessorCandidates] at hq
      simp only [Finset.mem_filter, Finset.mem_Iic] at hq
      exact hq.2.1.pos
    calc (∏ q ∈ lowerHSuccessorCandidates L j p, (1 - 1 / (q : ℝ)))
        ≤ Real.exp (-(∑ q ∈ lowerHSuccessorCandidates L j p, (1 : ℝ) / (q : ℝ))) :=
          prod_one_sub_inv_le_exp_neg_sum _ hQ_pos
      _ ≤ Real.exp (-(lowerHWindowB L / 8)) := by
          apply Real.exp_le_exp.mpr
          rw [hcand_eq] at *
          linarith [hsum_ge_B8]
      _ = Real.exp (-(lowerHWindowB L) / 8) := by ring_nf
  -- Sub-claim (iii): Sum-disjointness bound (paper line 1158):
  -- ∑_{p ∈ S} card{r : p_j(r) = p} ≤ M.
  have hsum_disjoint :
      (∑ p ∈ S, (((Finset.range M).filter
          (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ)) ≤ (M : ℝ) := by
    -- {r : p_j(r) = p} are disjoint subsets of [0, M).
    have h_eq : (∑ p ∈ S, ((Finset.range M).filter
          (fun r => lowerHGreedyPrime? L r j = some p)).card) =
        ((S.biUnion (fun p => (Finset.range M).filter
            (fun r => lowerHGreedyPrime? L r j = some p))).card) := by
      rw [Finset.card_biUnion]
      intro p _ p' _ hpp'
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro r _ hgp hgp'
      exact hpp' (Option.some_inj.mp (hgp.symm.trans hgp'))
    have h_sub : (S.biUnion (fun p => (Finset.range M).filter
        (fun r => lowerHGreedyPrime? L r j = some p))) ⊆ Finset.range M := by
      intro r hr
      simp only [Finset.mem_biUnion, Finset.mem_filter] at hr
      obtain ⟨p, _, hrM, _⟩ := hr
      exact hrM
    have h_card_le : (S.biUnion (fun p => (Finset.range M).filter
        (fun r => lowerHGreedyPrime? L r j = some p))).card ≤ M := by
      have := Finset.card_le_card h_sub
      rwa [Finset.card_range] at this
    have : (∑ p ∈ S, ((Finset.range M).filter
          (fun r => lowerHGreedyPrime? L r j = some p)).card) ≤ M := by
      rw [h_eq]; exact h_card_le
    exact_mod_cast this
  -- Helper: each card is nonneg as a real
  have h_card_nn : ∀ p ∈ S,
      (0 : ℝ) ≤ (((Finset.range M).filter
          (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ) := by
    intro p _; positivity
  -- Combine via calc.
  calc (∑ p ∈ S, (((Finset.range M).filter (fun r => lowerHGreedyPrime? L r j = some p ∧
        ∀ q ∈ lowerHSuccessorCandidates L j p, ¬ q ∣ r)).card : ℝ))
    = ∑ p ∈ S, ((((Finset.range M).filter
          (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ) *
        (∏ q ∈ lowerHSuccessorCandidates L j p, (1 - 1 / (q : ℝ)))) :=
      Finset.sum_congr rfl (fun p hp => hper_branch p hp)
    _ ≤ ∑ p ∈ S, ((((Finset.range M).filter
            (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ) *
          Real.exp (-(lowerHWindowB L) / 8)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (hmass_bound p hp) (h_card_nn p hp)
    _ = Real.exp (-(lowerHWindowB L) / 8) *
        ∑ p ∈ S, (((Finset.range M).filter
            (fun r => lowerHGreedyPrime? L r j = some p)).card : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ Real.exp (-(lowerHWindowB L) / 8) * (M : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_disjoint (Real.exp_pos _).le

/-- Uniform version of `stage_h_crt_transfer` for summing over the stages present at
one scale `x`.

The proof is intentionally the same CRT-period argument as `stage_h_crt_transfer`,
but with `j` quantified after the lower cutoff for `x`.  This exposes the fact that
the only eventual lower bound needed here is `logStar x ≥ 2`, independent of `j`. -/
private lemma stage_failure_density_h_uniform :
    ∃ x₀ : ℝ, 0 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ j : ℕ, ∀ ηerr : ℝ, 0 ≤ ηerr →
          let L := logStar x
          let B := lowerHWindowB L
          let yj := lowerHWindowY L j
          let Mj := primorial ⌊Real.exp (Real.exp ((B / 2) * yj))⌋₊
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
            Real.exp (-B / 8) * x + (Mj : ℝ) + ηerr * x := by
  classical
  rcases eventually_logStar_ge 2 with ⟨N₁, hN₁⟩
  -- Paper line 1146 "for L large": uniform threshold via y_0 (since y_j ≥ y_0).
  set y₀ := Classical.choose (prime_successor_mass 2 (by norm_num : (2:ℝ) ≤ 2)) with hy₀_def
  rcases lowerHWindowY_eventually_ge 0 y₀ with ⟨N_y, hN_y⟩
  rcases eventually_logStar_ge N_y with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  refine ⟨((N : ℝ) + 1), by positivity, ?_⟩
  intro x hx j ηerr hηerr
  let L := logStar x
  let B := lowerHWindowB L
  let yj := lowerHWindowY L j
  let P := lowerHStageCutoff L j
  let M := primorial P
  have hx_nonneg : 0 ≤ x := by
    have hx0 : (0 : ℝ) < N + 1 := by positivity
    linarith
  have hfloor_ge : N ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
    linarith
  have hN₁_le_floor : N₁ ≤ ⌊x⌋₊ := le_trans (Nat.le_max_left _ _) hfloor_ge
  have hN₂_le_floor : N₂ ≤ ⌊x⌋₊ := le_trans (Nat.le_max_right _ _) hfloor_ge
  have hL_ge : 2 ≤ L := by
    have hfloor_log : 2 ≤ logStar ((⌊x⌋₊ : ℕ) : ℝ) := hN₁ ⌊x⌋₊ hN₁_le_floor
    exact hfloor_log.trans
      (logStar_nat_le_logStar_of_le_floor hx_nonneg (Nat.le_refl ⌊x⌋₊))
  have hL_ge_Ny : N_y ≤ L := by
    have hfloor_log : N_y ≤ logStar ((⌊x⌋₊ : ℕ) : ℝ) := hN₂ ⌊x⌋₊ hN₂_le_floor
    exact hfloor_log.trans
      (logStar_nat_le_logStar_of_le_floor hx_nonneg (Nat.le_refl ⌊x⌋₊))
  have hB : 2 ≤ B := by
    have hLreal : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge
    dsimp [B, lowerHWindowB]
    nlinarith [sq_nonneg ((L : ℝ) - 2)]
  have hMpos : 0 < M := by
    exact primorial_pos P
  have hperiod : ∀ n : ℕ, LowerHStageFailure L j n ↔ LowerHStageFailure L j (n % M) := by
    intro n
    apply LowerHStageFailure_iff_of_mod hB
    have hmod : n % M = (n % M) % M := by
      rw [Nat.mod_eq_of_lt (Nat.mod_lt n hMpos)]
    exact hmod
  have hcount := periodic_count_le
    (P := fun n : ℕ => LowerHStageFailure L j n) (M := M) (N := ⌊x⌋₊) hMpos hperiod
  have hcount' :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
        lowerHStageFailureResidueProb L j * (⌊x⌋₊ : ℝ) + (M : ℝ) := by
    simpa [lowerHStageFailureResidueProb, P, M, mul_comm, mul_left_comm, mul_assoc]
      using hcount
  have hfloor_le_x : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hprob_nonneg : 0 ≤ lowerHStageFailureResidueProb L j := by
    unfold lowerHStageFailureResidueProb
    exact div_nonneg (by positivity) (by exact_mod_cast (primorial_pos (lowerHStageCutoff L j)).le)
  have hcount_x :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
        lowerHStageFailureResidueProb L j * x + (M : ℝ) := by
    calc
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)
          ≤ lowerHStageFailureResidueProb L j * (⌊x⌋₊ : ℝ) + (M : ℝ) := hcount'
      _ ≤ lowerHStageFailureResidueProb L j * x + (M : ℝ) := by
        gcongr
  -- Paper §5.2 line 1146 "for L large": y_j ≥ y_0 ≥ y₀ via enlarged x₀.
  have hyj_thresh : y₀ ≤ lowerHWindowY L j := by
    have h1 : y₀ ≤ lowerHWindowY L 0 := hN_y L hL_ge_Ny
    have h2 : lowerHWindowY L 0 ≤ lowerHWindowY L j :=
      lowerHWindowY_mono_k hB (Nat.zero_le j)
    linarith
  have hprob := stage_h_pmodel_failure_prob j L hB hyj_thresh
  have hmain :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
        Real.exp (-B / 8) * x + (M : ℝ) := by
    calc
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)
          ≤ lowerHStageFailureResidueProb L j * x + (M : ℝ) := hcount_x
      _ ≤ Real.exp (-B / 8) * x + (M : ℝ) := by
        gcongr
  have heta_nonneg : 0 ≤ ηerr * x := mul_nonneg hηerr hx_nonneg
  change
    (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
      Real.exp (-B / 8) * x + (M : ℝ) + ηerr * x
  linarith

private lemma stage_failure_sum_from_uniform_bound {x ηstep : ℝ}
    (hbound : ∀ j : ℕ,
      let L := logStar x
      let B := lowerHWindowB L
      let yj := lowerHWindowY L j
      let Mj := primorial ⌊Real.exp (Real.exp ((B / 2) * yj))⌋₊
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
        Real.exp (-B / 8) * x + (Mj : ℝ) + ηstep * x) :
    let L := logStar x
    let R := lowerHChainLength L
    let B := lowerHWindowB L
    (∑ j ∈ Finset.range R,
        (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)) ≤
      (R : ℝ) * (Real.exp (-B / 8) * x + ηstep * x) +
        ∑ j ∈ Finset.range R,
          (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) := by
  classical
  let L := logStar x
  let R := lowerHChainLength L
  let B := lowerHWindowB L
  have hsum := Finset.sum_le_sum (s := Finset.range R) (f := fun j =>
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)) (g := fun j =>
      Real.exp (-B / 8) * x +
        (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) +
          ηstep * x) (by
        intro j _hj
        simpa [L, B] using hbound j)
  calc
    (∑ j ∈ Finset.range R,
        (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ))
        ≤ ∑ j ∈ Finset.range R,
            (Real.exp (-B / 8) * x +
              (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) +
                ηstep * x) := hsum
    _ = (R : ℝ) * (Real.exp (-B / 8) * x + ηstep * x) +
          ∑ j ∈ Finset.range R,
            (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) := by
        simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring

private lemma stage_failure_exp_sum_small :
    ∀ η : ℝ, 0 < η →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          let R := lowerHChainLength L
          let B := lowerHWindowB L
          (R : ℝ) * (Real.exp (-B / 8) * x) ≤ η / 3 * x := by
  intro η hη
  have hcoeff :
      ∃ K : ℕ, ∀ L : ℕ, K ≤ L →
        (L : ℝ) * Real.exp (-((L : ℝ) ^ 2) / 8) ≤ η / 3 := by
    have ht : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y)) Filter.atTop (nhds 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    rw [Metric.tendsto_atTop] at ht
    rcases ht (η / 3) (by positivity) with ⟨Y, hY⟩
    let K : ℕ := max 8 ⌈Y⌉₊
    refine ⟨K, ?_⟩
    intro L hKL
    have hL_ge_8_nat : 8 ≤ L := (le_max_left 8 ⌈Y⌉₊).trans hKL
    have hL_ge_Y : Y ≤ (L : ℝ) := by
      have hceil : Y ≤ (⌈Y⌉₊ : ℕ) := Nat.le_ceil Y
      have hceil_le : ⌈Y⌉₊ ≤ L := (le_max_right 8 ⌈Y⌉₊).trans hKL
      exact hceil.trans (by exact_mod_cast hceil_le)
    have hsmall_lt := hY (L : ℝ) hL_ge_Y
    have hsmall : (L : ℝ) * Real.exp (-(L : ℝ)) ≤ η / 3 := by
      have hnonneg : 0 ≤ (L : ℝ) * Real.exp (-(L : ℝ)) := by positivity
      have habs0 : |(L : ℝ) * Real.exp (-(L : ℝ)) - 0| < η / 3 := by
        simpa [Real.dist_eq] using hsmall_lt
      have habs : (L : ℝ) * Real.exp (-(L : ℝ)) < η / 3 := by
        simpa [abs_of_nonneg hnonneg] using habs0
      exact le_of_lt habs
    have hexp_le : Real.exp (-((L : ℝ) ^ 2) / 8) ≤ Real.exp (-(L : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hL8 : (8 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_8_nat
      nlinarith
    calc
      (L : ℝ) * Real.exp (-((L : ℝ) ^ 2) / 8)
          ≤ (L : ℝ) * Real.exp (-(L : ℝ)) := by gcongr
      _ ≤ η / 3 := hsmall
  rcases hcoeff with ⟨K, hK⟩
  rcases eventually_logStar_ge K with ⟨N, hN⟩
  refine ⟨(N + 1 : ℝ), by positivity, ?_⟩
  intro x hx
  let L := logStar x
  let R := lowerHChainLength L
  let B := lowerHWindowB L
  have hx_pos : 0 < x := by
    have hx0 : (0 : ℝ) < N + 1 := by positivity
    linarith
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hfloor_ge : N ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
    linarith
  have hL_ge : K ≤ L := by
    have hfloor_log : K ≤ logStar ((⌊x⌋₊ : ℕ) : ℝ) := hN ⌊x⌋₊ hfloor_ge
    exact hfloor_log.trans
      (logStar_nat_le_logStar_of_le_floor hx_nonneg (Nat.le_refl ⌊x⌋₊))
  have hR_le_L : (R : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast lowerHChainLength_le L
  have hcoeffL : (L : ℝ) * Real.exp (-((L : ℝ) ^ 2) / 8) ≤ η / 3 := hK L hL_ge
  have hcoeffR : (R : ℝ) * Real.exp (-B / 8) ≤ η / 3 := by
    calc
      (R : ℝ) * Real.exp (-B / 8) ≤ (L : ℝ) * Real.exp (-B / 8) := by
        gcongr
      _ = (L : ℝ) * Real.exp (-((L : ℝ) ^ 2) / 8) := by simp [B, lowerHWindowB]
      _ ≤ η / 3 := hcoeffL
  calc
    (R : ℝ) * (Real.exp (-B / 8) * x) = ((R : ℝ) * Real.exp (-B / 8)) * x := by
      ring
    _ ≤ (η / 3) * x := by gcongr

private lemma stage_failure_eta_sum_small {x η : ℝ} (hη : 0 < η) (hx_nonneg : 0 ≤ x) :
    let L := logStar x
    let R := lowerHChainLength L
    (R : ℝ) * ((η / (3 * (max 1 R : ℕ) : ℝ)) * x) ≤ η / 3 * x := by
  let L := logStar x
  let R := lowerHChainLength L
  have hden_pos : 0 < (3 * (max 1 R : ℕ) : ℝ) := by positivity
  have hR_le_den : (R : ℝ) ≤ (max 1 R : ℕ) := by
    exact_mod_cast (le_max_right 1 R)
  have hratio_le : (R : ℝ) / (max 1 R : ℕ) ≤ 1 := by
    have hden' : 0 < ((max 1 R : ℕ) : ℝ) := by positivity
    exact (div_le_one hden').2 hR_le_den
  calc
    (R : ℝ) * ((η / (3 * (max 1 R : ℕ) : ℝ)) * x)
        = (η / 3 * ((R : ℝ) / (max 1 R : ℕ))) * x := by
          field_simp [hden_pos.ne']
    _ ≤ (η / 3 * 1) * x := by
      gcongr
    _ = η / 3 * x := by ring

private lemma lemma_initial_failure_decay :
    ∀ δ : ℝ, 0 < δ →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) ≤ δ * x := by
  classical
  intro δ hδ
  let A : ℝ := -Real.log (δ / 2)
  rcases prime_reciprocal_sum_eventually_ge A with ⟨Y₀, hY₀_two, hYsum⟩
  let P₀ : ℕ := ⌊Y₀⌋₊
  let M₀ : ℕ := primorial P₀
  let T₀ : Finset ℕ := Finset.filter Nat.Prime (Finset.Iic P₀)
  have hY₀_pos : 0 < Y₀ := by linarith
  have hprod_nonneg : 0 ≤ ∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpge1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hpprime.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hinv_le : (1 : ℝ) / (p : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hppos]
      simpa using hpge1
    linarith
  have hprod_small : (∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ))) ≤ δ / 2 := by
    have hposT : ∀ q ∈ T₀, 0 < q := by
      intro q hq
      exact (Finset.mem_filter.mp hq).2.pos
    have hprod_exp := prod_one_sub_inv_le_exp_neg_sum T₀ hposT
    have hsum := hYsum Y₀ le_rfl
    have hexp_le : Real.exp (-(∑ q ∈ T₀, (1 : ℝ) / (q : ℝ))) ≤ δ / 2 := by
      have hle_log : -(∑ q ∈ T₀, (1 : ℝ) / (q : ℝ)) ≤ Real.log (δ / 2) := by
        dsimp [A, T₀, P₀] at hsum
        linarith
      calc
        Real.exp (-(∑ q ∈ T₀, (1 : ℝ) / (q : ℝ)))
            ≤ Real.exp (Real.log (δ / 2)) := Real.exp_le_exp.mpr hle_log
        _ = δ / 2 := Real.exp_log (by positivity)
    exact hprod_exp.trans hexp_le
  obtain ⟨K, hK⟩ :=
    Filter.eventually_atTop.mp (lowerHWindowY_zero_tendsto_atTop.eventually_ge_atTop Y₀)
  rcases eventually_logStar_ge K with ⟨N, hN⟩
  let x₀ : ℝ := max (N + 1 : ℝ) (max (2 * (M₀ : ℝ) / δ) 1)
  refine ⟨x₀, ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  intro x hx
  let L := logStar x
  have hxN1 : (N + 1 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hxM0 : 2 * (M₀ : ℝ) / δ ≤ x :=
    (le_max_left _ _).trans ((le_max_right (N + 1 : ℝ) _).trans hx)
  have hxone : (1 : ℝ) ≤ x :=
    (le_max_right _ _).trans ((le_max_right (N + 1 : ℝ) _).trans hx)
  have hx_nonneg : 0 ≤ x := by linarith
  have hfloor_ge : N ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
    linarith
  have hL_ge_K : K ≤ L := by
    have hfloor_log : K ≤ logStar ((⌊x⌋₊ : ℕ) : ℝ) := hN ⌊x⌋₊ hfloor_ge
    exact hfloor_log.trans
      (logStar_nat_le_logStar_of_le_floor hx_nonneg (Nat.le_refl ⌊x⌋₊))
  have hY_L : Y₀ ≤ lowerHWindowY L 0 := hK L hL_ge_K
  have hsubset :
      {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} ⊆
        {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} := by
    intro n hn
    rcases hn with ⟨hnx, hfail⟩
    refine ⟨hnx, ?_⟩
    by_contra hcop
    rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with ⟨p, hp, hpM, hpn⟩
    have hp_mem : p ∈ T₀ := by
      dsimp [M₀, primorial] at hpM
      rcases (Prime.dvd_finset_prod_iff hp.prime (fun q : ℕ => q)).mp hpM with
        ⟨q, hq, hpq⟩
      have hqprime : q.Prime := (Finset.mem_filter.mp hq).2
      have hpq_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
      simpa [T₀, hpq_eq] using hq
    have hp_floor : p ≤ P₀ := Finset.mem_Iic.mp (Finset.mem_filter.mp hp_mem).1
    have hpY₀ : (p : ℝ) ≤ Y₀ := by
      have hp_le_floor : (p : ℝ) ≤ (P₀ : ℕ) := by exact_mod_cast hp_floor
      exact hp_le_floor.trans (by simpa [P₀] using Nat.floor_le (by linarith))
    have hpYL : (p : ℝ) ≤ lowerHWindowY L 0 := hpY₀.trans hY_L
    exact lowerHInitialFailure_not_dvd hp hpYL hfail hpn
  have htarget_finite : Set.Finite {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} :=
    (Set.finite_Iic ⌊x⌋₊).subset (by
      intro n hn
      exact hn.1)
  have hcard_nat :
      Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} ≤
        Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} :=
    Nat.card_mono htarget_finite hsubset
  have hcard_real :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) ≤
        (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} : ℝ) := by
    exact_mod_cast hcard_nat
  have hcop_count := coprime_to_primorial_count_le_sieve_product P₀ ⌊x⌋₊
  have hfloor_le_x : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hcop_bound :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} : ℝ) ≤
        (∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ))) * x + (M₀ : ℝ) := by
    calc
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} : ℝ)
          ≤ (∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ))) * (⌊x⌋₊ : ℝ) +
              (M₀ : ℝ) := by
            simpa [M₀, T₀] using hcop_count
      _ ≤ (∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ))) * x + (M₀ : ℝ) := by
            gcongr
  have hM_term : (M₀ : ℝ) ≤ δ / 2 * x := by
    rw [div_le_iff₀ hδ] at hxM0
    nlinarith
  have hprod_term : (∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ))) * x ≤ δ / 2 * x := by
    exact mul_le_mul_of_nonneg_right hprod_small hx_nonneg
  calc
    (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ)
        ≤ (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ M₀.Coprime n} : ℝ) := hcard_real
    _ ≤ (∏ p ∈ T₀, (1 - (1 : ℝ) / (p : ℝ))) * x + (M₀ : ℝ) := hcop_bound
    _ ≤ δ * x := by
      nlinarith

private lemma lemma_primorial_sum_small :
    ∀ δ : ℝ, 0 < δ →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          let R := lowerHChainLength L
          let B := lowerHWindowB L
          (∑ j ∈ Finset.range R,
            (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ)) ≤
              δ * x := by
  classical
  intro δ hδ
  rcases chebyshev_theta with ⟨Cθ, hCθ_pos, htheta⟩
  obtain ⟨K₁, hK₁⟩ :=
    Filter.eventually_atTop.mp (chebyshev_stage_exponent_eventually Cθ hCθ_pos)
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.mp (linear_le_delta_exp_half_eventually δ hδ)
  let K : ℕ := max 6 (max (K₁ + 4) (K₂ + 2))
  rcases eventually_logStar_ge K with ⟨N, hN⟩
  refine ⟨(N + 1 : ℝ), by positivity, ?_⟩
  intro x hx
  let L := logStar x
  let R := lowerHChainLength L
  let B := lowerHWindowB L
  have hx_pos : 0 < x := by
    have hx0 : (0 : ℝ) < N + 1 := by positivity
    linarith
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hfloor_ge : N ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
    linarith
  have hL_ge_K : K ≤ L := by
    have hfloor_log : K ≤ logStar ((⌊x⌋₊ : ℕ) : ℝ) := hN ⌊x⌋₊ hfloor_ge
    exact hfloor_log.trans
      (logStar_nat_le_logStar_of_le_floor hx_nonneg (Nat.le_refl ⌊x⌋₊))
  have hL_ge6 : 6 ≤ L := (le_max_left 6 (max (K₁ + 4) (K₂ + 2))).trans hL_ge_K
  have hL_ge_K₁4 : K₁ + 4 ≤ L :=
    (le_max_left (K₁ + 4) (K₂ + 2)).trans
      ((le_max_right 6 (max (K₁ + 4) (K₂ + 2))).trans hL_ge_K)
  have hL_ge_K₂2 : K₂ + 2 ≤ L :=
    (le_max_right (K₁ + 4) (K₂ + 2)).trans
      ((le_max_right 6 (max (K₁ + 4) (K₂ + 2))).trans hL_ge_K)
  have hstage_period_bound : ∀ j ∈ Finset.range R,
      (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) ≤
        Real.exp (tower (L - 2) / 2) := by
    intro j hj
    let Pj : ℕ := ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊
    have hPj_eq : Pj = lowerHStageCutoff L j := by
      simp [Pj, lowerHStageCutoff, B, lowerHWindowB, div_eq_mul_inv, mul_assoc]
    have hm_ge_K₁ : K₁ ≤ L - 4 := by omega
    have hcheb_event := hK₁ (L - 4) hm_ge_K₁
    have hPj_le :
        (Pj : ℝ) ≤ Real.exp (Real.exp (tower (L - 4) / 2)) := by
      rw [hPj_eq]
      exact lowerHStageCutoff_le_exp_exp_tower (L := L) (j := j) hj
    have hCθP :
        Cθ * (Pj : ℝ) ≤ (1 / 2 : ℝ) * tower (L - 2) := by
      calc
        Cθ * (Pj : ℝ) ≤ Cθ * Real.exp (Real.exp (tower (L - 4) / 2)) := by
          gcongr
        _ ≤ (1 / 2 : ℝ) * tower ((L - 4) + 2) := hcheb_event
        _ = (1 / 2 : ℝ) * tower (L - 2) := by
          rw [show (L - 4) + 2 = L - 2 by omega]
    have harg_pos : 0 < (B / 2) * lowerHWindowY L j := by
      have hBne : lowerHWindowB L ≠ 0 := by
        dsimp [lowerHWindowB]
        positivity
      rw [show B = lowerHWindowB L by rfl, lowerHStageExponent_eq (L := L) (j := j) hBne]
      exact div_pos (tower_pos _) (by norm_num)
    have hPj_two : (2 : ℝ) ≤ (Pj : ℝ) := by
      have hval_two : (2 : ℝ) ≤ Real.exp (Real.exp ((B / 2) * lowerHWindowY L j)) := by
        have hone_le : (1 : ℝ) ≤ Real.exp ((B / 2) * lowerHWindowY L j) := by
          calc
            (1 : ℝ) = Real.exp 0 := by simp
            _ ≤ Real.exp ((B / 2) * lowerHWindowY L j) :=
              Real.exp_le_exp.mpr harg_pos.le
        have htwo_exp : (2 : ℝ) ≤ Real.exp 1 := by
          simpa using Real.two_mul_le_exp (x := 1)
        exact htwo_exp.trans (Real.exp_le_exp.mpr hone_le)
      exact_mod_cast (Nat.le_floor hval_two : 2 ≤ Pj)
    have hprim := primorial_le_exp_chebyshev (Cθ := Cθ) htheta hPj_two
    calc
      (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ)
          = (primorial Pj : ℝ) := by rfl
      _ ≤ Real.exp (Cθ * (Pj : ℝ)) := hprim
      _ ≤ Real.exp ((1 / 2 : ℝ) * tower (L - 2)) := Real.exp_le_exp.mpr hCθP
      _ = Real.exp (tower (L - 2) / 2) := by ring_nf
  have hsum_bound :
      (∑ j ∈ Finset.range R,
        (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ)) ≤
        (R : ℝ) * Real.exp (tower (L - 2) / 2) := by
    calc
      (∑ j ∈ Finset.range R,
        (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ))
          ≤ ∑ _j ∈ Finset.range R, Real.exp (tower (L - 2) / 2) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hstage_period_bound j hj
      _ = (R : ℝ) * Real.exp (tower (L - 2) / 2) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hR_le_L : (R : ℝ) ≤ (L : ℝ) := by exact_mod_cast lowerHChainLength_le L
  have hlinear_event := hK₂ (L - 2) (by omega : K₂ ≤ L - 2)
  have hL_linear : (L : ℝ) ≤ δ * Real.exp (tower (L - 2) / 2) := by
    have hcast : (((L - 2 : ℕ) : ℝ) + 2) = (L : ℝ) := by
      have : 2 ≤ L := by omega
      rw [Nat.cast_sub this]
      ring
    have htower_exp :
        Real.exp (((L - 2 : ℕ) : ℝ) / 2) ≤ Real.exp (tower (L - 2) / 2) := by
      apply Real.exp_le_exp.mpr
      have htower_ge : ((L - 2 : ℕ) : ℝ) ≤ tower (L - 2) := by
        have h := tower_ge (L - 2)
        linarith
      linarith
    calc
      (L : ℝ) = ((L - 2 : ℕ) : ℝ) + 2 := hcast.symm
      _ ≤ δ * Real.exp (((L - 2 : ℕ) : ℝ) / 2) := hlinear_event
      _ ≤ δ * Real.exp (tower (L - 2) / 2) := by
        gcongr
  have htower_pred_lt_x : tower (L - 1) < x := by
    by_contra hnot
    have hxle : x ≤ tower (L - 1) := le_of_not_gt hnot
    have hle := logStar_le_of_le_tower (L - 1) hxle
    dsimp [L] at hle
    omega
  have hmain_tower :
      (R : ℝ) * Real.exp (tower (L - 2) / 2) ≤ δ * tower (L - 1) := by
    have hLmul :
        (L : ℝ) * Real.exp (tower (L - 2) / 2) ≤ δ * tower (L - 1) := by
      calc
        (L : ℝ) * Real.exp (tower (L - 2) / 2)
            ≤ (δ * Real.exp (tower (L - 2) / 2)) *
                Real.exp (tower (L - 2) / 2) := by
              gcongr
        _ = δ * Real.exp (tower (L - 2)) := by
              rw [mul_assoc, ← Real.exp_add]
              ring_nf
        _ = δ * tower (L - 1) := by
              rw [show L - 1 = (L - 2) + 1 by omega]
              rfl
    calc
      (R : ℝ) * Real.exp (tower (L - 2) / 2)
          ≤ (L : ℝ) * Real.exp (tower (L - 2) / 2) := by
            gcongr
      _ ≤ δ * tower (L - 1) := hLmul
  calc
    (∑ j ∈ Finset.range R,
      (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ))
        ≤ (R : ℝ) * Real.exp (tower (L - 2) / 2) := hsum_bound
    _ ≤ δ * tower (L - 1) := hmain_tower
    _ ≤ δ * x := by
      gcongr

private lemma stage_failure_sum_h_of_bookkeeping
    (hinit : ∀ δ : ℝ, 0 < δ →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) ≤ δ * x)
    (hprim : ∀ δ : ℝ, 0 < δ →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          let R := lowerHChainLength L
          let B := lowerHWindowB L
          (∑ j ∈ Finset.range R,
            (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ)) ≤
              δ * x) :
    ∀ η : ℝ, 0 < η →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          let R := lowerHChainLength L
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) +
              (∑ j ∈ Finset.range R,
                (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)) ≤
            η * x := by
  classical
  intro η hη
  let δ : ℝ := η / 4
  let ηstage : ℝ := 3 * η / 4
  have hδ : 0 < δ := by positivity
  have hηstage : 0 < ηstage := by positivity
  rcases stage_failure_density_h_uniform with ⟨xstage, hxstage_pos, hstage⟩
  rcases hinit δ hδ with ⟨xinit, hxinit_pos, hinit_bound⟩
  rcases hprim δ hδ with ⟨xprim, hxprim_pos, hprim_bound⟩
  rcases stage_failure_exp_sum_small ηstage hηstage with ⟨xexp, hxexp_pos, hexp_bound⟩
  let x₀ : ℝ := max xstage (max xinit (max xprim (max xexp 1)))
  refine ⟨x₀, ?_, ?_⟩
  · exact lt_of_lt_of_le hxstage_pos (le_max_left _ _)
  intro x hx
  let L := logStar x
  let R := lowerHChainLength L
  let B := lowerHWindowB L
  let ηstep : ℝ := ηstage / (3 * (max 1 R : ℕ) : ℝ)
  have hxstage : xstage ≤ x := (le_max_left _ _).trans hx
  have hxinit : xinit ≤ x :=
    (le_max_left xinit _).trans ((le_max_right xstage _).trans hx)
  have hxprim : xprim ≤ x :=
    (le_max_left xprim _).trans
      ((le_max_right xinit _).trans ((le_max_right xstage _).trans hx))
  have hxexp : xexp ≤ x :=
    (le_max_left xexp 1).trans
      ((le_max_right xprim _).trans
        ((le_max_right xinit _).trans ((le_max_right xstage _).trans hx)))
  have hxone : (1 : ℝ) ≤ x :=
    (le_max_right xexp 1).trans
      ((le_max_right xprim _).trans
        ((le_max_right xinit _).trans ((le_max_right xstage _).trans hx)))
  have hx_nonneg : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hxone
  have hηstep_nonneg : 0 ≤ ηstep := by positivity
  have hstage_point : ∀ j : ℕ,
      let L := logStar x
      let B := lowerHWindowB L
      let yj := lowerHWindowY L j
      let Mj := primorial ⌊Real.exp (Real.exp ((B / 2) * yj))⌋₊
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) ≤
        Real.exp (-B / 8) * x + (Mj : ℝ) + ηstep * x := by
    intro j
    simpa [L, B, ηstep] using hstage x hxstage j ηstep hηstep_nonneg
  have hstage_sum := stage_failure_sum_from_uniform_bound (x := x) (ηstep := ηstep)
    hstage_point
  have hstage_sum' :
      (∑ j ∈ Finset.range R,
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)) ≤
        (R : ℝ) * (Real.exp (-B / 8) * x) +
          (R : ℝ) * (ηstep * x) +
            ∑ j ∈ Finset.range R,
              (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) := by
    calc
      (∑ j ∈ Finset.range R,
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ))
          ≤ (R : ℝ) * (Real.exp (-B / 8) * x + ηstep * x) +
              ∑ j ∈ Finset.range R,
                (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) := by
            simpa [L, R, B] using hstage_sum
      _ = (R : ℝ) * (Real.exp (-B / 8) * x) +
            (R : ℝ) * (ηstep * x) +
              ∑ j ∈ Finset.range R,
                (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ) := by
            ring
  have hinit_x :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) ≤ δ * x := by
    simpa [L] using hinit_bound x hxinit
  have hprim_x :
      (∑ j ∈ Finset.range R,
        (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ)) ≤
          δ * x := by
    simpa [L, R, B] using hprim_bound x hxprim
  have hexp_x : (R : ℝ) * (Real.exp (-B / 8) * x) ≤ ηstage / 3 * x := by
    simpa [L, R, B] using hexp_bound x hxexp
  have heta_x : (R : ℝ) * (ηstep * x) ≤ ηstage / 3 * x := by
    simpa [L, R, ηstep] using stage_failure_eta_sum_small (x := x) (η := ηstage)
      hηstage hx_nonneg
  have hδ_eq : δ = η / 4 := rfl
  have hηstage_div : ηstage / 3 = η / 4 := by ring
  have hinit_q :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) ≤
        η / 4 * x := by
    simpa [hδ_eq] using hinit_x
  have hprim_q :
      (∑ j ∈ Finset.range R,
        (primorial ⌊Real.exp (Real.exp ((B / 2) * lowerHWindowY L j))⌋₊ : ℝ)) ≤
          η / 4 * x := by
    simpa [hδ_eq] using hprim_x
  have hexp_q : (R : ℝ) * (Real.exp (-B / 8) * x) ≤ η / 4 * x := by
    simpa [hηstage_div] using hexp_x
  have heta_q : (R : ℝ) * (ηstep * x) ≤ η / 4 * x := by
    simpa [hηstage_div] using heta_x
  have htotal :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) +
          (∑ j ∈ Finset.range R,
            (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)) ≤
        η * x := by
    linarith
  simpa [L, R] using htotal

/-- Paper §5.2 union bound over all greedy stages.

The initial failure is `o(x)`, and the sum over `j < R` of the one-stage bounds
from `stage_failure_density_h` is also `o(x)` because
`R ≤ L` while `L * exp(-L^2/8) → 0`; Chebyshev bounds the combined CRT-period
errors by `o(x)`. -/
private lemma stage_failure_sum_h :
    ∀ η : ℝ, 0 < η →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := logStar x
          let R := lowerHChainLength L
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) +
              (∑ j ∈ Finset.range R,
                (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ)) ≤
            η * x := by
  classical
  intro η hη
  exact stage_failure_sum_h_of_bookkeeping lemma_initial_failure_decay
    lemma_primorial_sum_small η hη

/-- Paper §5.2--§5.3 bridge from summed stage failures to a density-one set of
integers carrying a long lower prime chain.

Outside the exceptional set bounded by `stage_failure_sum_h`, the deterministic
least-prime greedy construction produces primes `p₁ < ⋯ < p_R`, all dividing
`n`, with `p_{j+1} ≡ 1 mod p_j`.  The tower arithmetic gives
`R ≥ (1/2 - ε) log_* n`, so the chain packages as `GoodLowerPrimeChain ε n`. -/
private lemma good_lower_prime_chains_from_stage_sums :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → almostAll (GoodLowerPrimeChain ε) := by
  classical
  intro ε hε hε_lt
  rcases lowerHChainLength_eventually_ge ε hε hε_lt with ⟨L₀, hL₀⟩
  unfold almostAll
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro δ hδ
  have hη : 0 < δ / 3 := by positivity
  rcases stage_failure_sum_h (δ / 3) hη with ⟨xsum, hxsum_pos, hsum⟩
  let x₁ : ℝ := max xsum (max (tower L₀) (max (3 / δ) 1))
  filter_upwards [Filter.eventually_ge_atTop x₁] with x hx
  have hxsum : xsum ≤ x := (le_max_left _ _).trans hx
  have hxtower : tower L₀ ≤ x := by
    exact (le_max_left _ _).trans ((le_max_right xsum _).trans hx)
  have hxthree : 3 / δ ≤ x := by
    exact (le_max_left _ _).trans ((le_max_right (tower L₀) _).trans
      ((le_max_right xsum _).trans hx))
  have hxone : (1 : ℝ) ≤ x := by
    exact (le_max_right _ _).trans ((le_max_right (tower L₀) _).trans
      ((le_max_right xsum _).trans hx))
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxone
  have hxnonneg : 0 ≤ x := hxpos.le
  let L : ℕ := logStar x
  let R : ℕ := lowerHChainLength L
  have hL_ge : L₀ ≤ L := by
    by_contra hnot
    have hlt : L < L₀ := Nat.lt_of_not_ge hnot
    have htower_lt : tower L < tower L₀ :=
      strictMono_nat_of_lt_succ tower_lt_succ hlt
    have hx_le : x ≤ tower L := by simpa [L] using self_le_tower_logStar x
    linarith
  have hsub : ∀ n : ℕ, n ≤ ⌊x⌋₊ → ¬ GoodLowerPrimeChain ε n →
      n = 0 ∨ LowerHInitialFailure L n ∨
        ∃ j : ℕ, j ∈ Finset.range R ∧ LowerHStageFailure L j n := by
    intro n hn hbad
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · right
      by_cases hinit : LowerHInitialFailure L n
      · exact Or.inl hinit
      · right
        by_contra hno_stage
        have hstages : ∀ j ∈ Finset.range R, ¬ LowerHStageFailure L j n := by
          intro j hj hfail
          exact hno_stage ⟨j, hj, hfail⟩
        have hchain : HasPrimeChainLengthAtLeast R n :=
          hasPrimeChainLengthAtLeast_of_greedy_successes hinit hstages
        have hlog_le : logStar (n : ℝ) ≤ L :=
          logStar_nat_le_logStar_of_le_floor hxnonneg hn
        have hlog_real : (logStar (n : ℝ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlog_le
        have hcoef_nonneg : 0 ≤ (1 / 2 - ε : ℝ) := by linarith
        have hscale : (1 / 2 - ε) * (L : ℝ) ≤ (R : ℝ) := by
          simpa [L, R] using hL₀ L hL_ge
        have hineq : (1 / 2 - ε) * (logStar (n : ℝ) : ℝ) ≤ (R : ℝ) :=
          (mul_le_mul_of_nonneg_left hlog_real hcoef_nonneg).trans hscale
        exact hbad ⟨R, hn0, hchain, hineq⟩
  have hcard_nat :=
    card_bad_le_one_add_failure_sum (N := ⌊x⌋₊) (R := R)
      (P := GoodLowerPrimeChain ε) (I := LowerHInitialFailure L)
      (S := fun j n => LowerHStageFailure L j n) hsub
  have hfail := hsum x hxsum
  have hcard_real :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerPrimeChain ε n} : ℝ) ≤
        1 + (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHInitialFailure L n} : ℝ) +
          ∑ j ∈ Finset.range R,
            (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ LowerHStageFailure L j n} : ℝ) := by
    exact_mod_cast hcard_nat
  have hbad_bound :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerPrimeChain ε n} : ℝ) ≤
        1 + (δ / 3) * x := by
    nlinarith [hcard_real, hfail]
  have hone_div : 1 / x ≤ δ / 3 := by
    have hδx' : 3 ≤ x * δ := by
      rwa [div_le_iff₀ hδ] at hxthree
    have hδx : 3 ≤ δ * x := by nlinarith
    field_simp [hxpos.ne', (ne_of_gt hδ)]
    nlinarith
  have hratio :
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerPrimeChain ε n} : ℝ) / x < δ := by
    have htmp := div_le_div_of_nonneg_right hbad_bound hxpos.le
    calc
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerPrimeChain ε n} : ℝ) / x
          ≤ (1 + (δ / 3) * x) / x := htmp
      _ = 1 / x + δ / 3 := by
        field_simp [hxpos.ne']
      _ ≤ δ / 3 + δ / 3 := by linarith
      _ < δ := by linarith
  have hnonneg :
      0 ≤ (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerPrimeChain ε n} : ℝ) / x := by
    positivity
  rwa [Real.norm_of_nonneg hnonneg]

/-- **Lemma 5.2 (greedy `h`-chain in the product model).**

In the independent prime model on primes up to `y_R`, the probability
that there is no prime chain `p₁ < ⋯ < p_R` of the prescribed form is
`o(1)` as `R = (1/2 - o(1)) log_* x → ∞`.

Uses `prime_successor_mass` and a union bound over the `R` greedy
steps, then `crt_transfer` to lift product-model density to integer
density.

Refactored 2026-04-28 to carry actual density content (was `True` stub).
The statement now directly asserts the integer density result needed
by `lower_bound_h`. -/
lemma greedy_h_chain :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n => (hChain n : ℝ) ≥ (1/2 - ε) * (logStar n : ℝ)) := by
  intro ε _hε
  by_cases hlarge : (1 / 2 : ℝ) ≤ ε
  · simpa using greedy_h_chain_large_epsilon ε hlarge
  · exact lower_bound_from_good_prime_chains
      (good_lower_prime_chains_from_stage_sums ε _hε (lt_of_not_ge hlarge))

/-- **Theorem 5.0 (lower bound for `h`).**

For all but `o(x)` integers `n ≤ x`, `h(n) ≥ (1/2 - o(1)) log_* x`.

Encoded ε-style.  Direct corollary of `greedy_h_chain`. -/
theorem lower_bound_h :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n => (hChain n : ℝ) ≥ (1/2 - ε) * (logStar n : ℝ)) :=
  greedy_h_chain

end Erdos696
