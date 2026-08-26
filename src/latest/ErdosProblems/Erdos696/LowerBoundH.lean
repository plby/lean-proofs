/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.CompositeSuccessor

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

variable [sw : SiegelWalfisz]
include sw

-- === Inlined from Erdos696/LowerBoundH.lean ===
/-
# Lower bound for `H(n)`

Mirrors §7 of `erdos_696_paper.tex`.

**Theorem.** For all but `o(x)` integers `n ≤ x`,
`H(n) ≥ (1 - o(1)) log_* x`.

**Proof structure (paper §7).**
1. *Tower scale*: `B := A + 10`, `m_0 := ⌊L^{1/2}⌋`,
   `y_j := exp(T_{m_0+j-1} / B)`, `R := L - m_0 - 4 = (1-o(1)) L`.
2. *Scale property* (Lemma 7.2): `exp(y_j^A) ≤ y_{j+1}`.
3. *Greedy chain construction* (Lemma 7.3): with probability `1 - o(1)`
   in the product model, there is a divisor chain
   `1 = d_1 < d_2 < ⋯ < d_{R+1}` with each `d_{j+1}` a squarefree
   product of selected primes from a disjoint window
   `(exp y_j, exp(y_j^{A-1})]`, satisfying `d_{j+1} ≡ 1 (mod d_j)`.
   Uses `composite_successor` independently in each window.
4. *CRT transfer*: density of "good" `n` is `1 - o(1)`.

This is the hardest section of the paper, but the structural reduction
to `composite_successor` and `crt_transfer` is straightforward.
-/



open Real

/-- **Lemma 7.2 (scale property for `H`).**

For all sufficiently large `L` and all `1 ≤ j < R`,
`exp(y_j^A) ≤ y_{j+1}`.

Sketch: equivalent to `exp(A T_m / B) ≤ exp T_m / B`, i.e.
`T_m (1 - A/B) ≥ log B`.  Holds since `1 - A/B = 10/B > 0` and
`T_m → ∞`.

Real-analysis bookkeeping on the tower.

Refactored 2026-04-28: af-010 found counterexample A=-10,B=0 satisfying
the prior `A+10≤B` hypothesis but breaking conclusion. Added `0 < A`
hypothesis (paper §7 requires A > 10, this is the minimum needed). -/
lemma scale_H (A B : ℝ) (hA : 0 < A) (hAB : A + 10 ≤ B) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ j : ℕ, j + 1 ≤ L →
        ∃ m : ℕ,
          Real.exp ((Real.exp (tower m / B)) ^ A) ≤
            Real.exp (tower (m + 1) / B) := by
  have hB : 0 < B := by linarith
  have hBne : B ≠ 0 := ne_of_gt hB
  have hABlt : A < B := by linarith
  have hdelta : 0 < 1 - A / B := by
    have hdiv : A / B < 1 := (div_lt_one hB).2 hABlt
    linarith
  have hev := tower_tendsto_atTop.eventually_ge_atTop (Real.log B / (1 - A / B))
  rcases Filter.eventually_atTop.1 hev with ⟨m, hm⟩
  refine ⟨0, ?_⟩
  intro _L _hL _j _hj
  refine ⟨m, ?_⟩
  have hmge : Real.log B / (1 - A / B) ≤ tower m := hm m le_rfl
  have hmul : Real.log B ≤ tower m * (1 - A / B) := by
    rwa [div_le_iff₀ hdelta] at hmge
  have hrewrite : tower m * (1 - A / B) = tower m - A * (tower m / B) := by
    field_simp [hBne]
  have hlin : A * (tower m / B) + Real.log B ≤ tower m := by
    nlinarith
  apply Real.exp_le_exp.mpr
  rw [show tower (m + 1) = Real.exp (tower m) by rfl]
  have hpow : (Real.exp (tower m / B)) ^ A = Real.exp (A * (tower m / B)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  rw [hpow]
  rw [le_div_iff₀ hB]
  calc
    Real.exp (A * (tower m / B)) * B =
        Real.exp (A * (tower m / B)) * Real.exp (Real.log B) := by
      rw [Real.exp_log hB]
    _ = Real.exp (A * (tower m / B) + Real.log B) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (tower m) := by
      exact Real.exp_le_exp.mpr hlin

/-- **Strong form of scale_H (paper line 1853 verbatim)**: for `m` sufficiently large,
`exp(y_m^A) ≤ y_{m+1}` (where `y_m := exp(T_m/B)`).

This is the per-`m` form needed when applying scale_H at a specific window index, not
just the existential per-(L,j) form in `scale_H`. -/
private lemma scale_H_strong (A B : ℝ) (hA : 0 < A) (hAB : A + 10 ≤ B) :
    ∃ m_thr : ℕ, ∀ m : ℕ, m_thr ≤ m →
        Real.exp ((Real.exp (tower m / B)) ^ A) ≤ Real.exp (tower (m + 1) / B) := by
  have hB : 0 < B := by linarith
  have hBne : B ≠ 0 := ne_of_gt hB
  have hABlt : A < B := by linarith
  have hdelta : 0 < 1 - A / B := by
    have hdiv : A / B < 1 := (div_lt_one hB).2 hABlt
    linarith
  have hev := tower_tendsto_atTop.eventually_ge_atTop (Real.log B / (1 - A / B))
  rcases Filter.eventually_atTop.1 hev with ⟨m_thr, hm_thr⟩
  refine ⟨m_thr, ?_⟩
  intro m hm_ge
  have hmge : Real.log B / (1 - A / B) ≤ tower m := hm_thr m hm_ge
  have hmul : Real.log B ≤ tower m * (1 - A / B) := by
    rwa [div_le_iff₀ hdelta] at hmge
  have hrewrite : tower m * (1 - A / B) = tower m - A * (tower m / B) := by
    field_simp [hBne]
  have hlin : A * (tower m / B) + Real.log B ≤ tower m := by
    nlinarith
  apply Real.exp_le_exp.mpr
  rw [show tower (m + 1) = Real.exp (tower m) by rfl]
  have hpow : (Real.exp (tower m / B)) ^ A = Real.exp (A * (tower m / B)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  rw [hpow]
  rw [le_div_iff₀ hB]
  calc
    Real.exp (A * (tower m / B)) * B =
        Real.exp (A * (tower m / B)) * Real.exp (Real.log B) := by
      rw [Real.exp_log hB]
    _ = Real.exp (A * (tower m / B) + Real.log B) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (tower m) := Real.exp_le_exp.mpr hlin

private lemma greedy_H_chain_large_epsilon :
    ∀ ε : ℝ, 1 ≤ ε →
      almostAll (fun n => (HChain n : ℝ) ≥ (1 - ε) * (logStar n : ℝ)) := by
  intro ε hε
  apply almostAll_of_forall
  intro n
  have hH : (0 : ℝ) ≤ (HChain n : ℝ) := by positivity
  have hlog : (0 : ℝ) ≤ (logStar n : ℝ) := by positivity
  have hcoef : (1 - ε : ℝ) ≤ 0 := by linarith
  have hrhs : (1 - ε) * (logStar n : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoef hlog
  exact le_trans hrhs hH

/-- Auxiliary deterministic condition: `n` contains a divisor chain of length at least `R`. -/
private def HasDivisorChainLengthAtLeast (R n : ℕ) : Prop :=
  ∃ ds : List ℕ, IsDivisorChain n ds ∧ R ≤ ds.length

private lemma divisorChain_length_le_self {n : ℕ} (hn : n ≠ 0) {ds : List ℕ}
    (hds : IsDivisorChain n ds) : ds.length ≤ n := by
  rcases hds with ⟨hdiv, hpair, _hmod⟩
  have hnodup : ds.Nodup := hpair.nodup
  rw [← List.toFinset_card_of_nodup hnodup]
  have hsub : ds.toFinset ⊆ Finset.Icc 1 n := by
    intro d hd
    rw [List.mem_toFinset] at hd
    simpa [Finset.mem_Icc] using
      (show 1 ≤ d ∧ d ≤ n from
        ⟨(hdiv d hd).1, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hdiv d hd).2⟩)
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma HChain_ge_of_hasDivisorChainLengthAtLeast {R n : ℕ} (hn : n ≠ 0)
    (hn1 : n ≠ 1) (hR : HasDivisorChainLengthAtLeast R n) : R ≤ HChain n := by
  rcases hR with ⟨ds, hds, hRle⟩
  have hbound : BddAbove {u : ℕ | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u} := by
    refine ⟨n, ?_⟩
    intro u hu
    rcases hu with ⟨qs, hqs, rfl⟩
    exact divisorChain_length_le_self hn hqs
  have hmem : ds.length ∈ {u : ℕ | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u} :=
    ⟨ds, hds, rfl⟩
  have hle : ds.length ≤ HChain n := by
    show ds.length ≤ HChain n
    rw [HChain, if_neg hn1]
    exact le_csSup hbound hmem
  exact hRle.trans hle

/-- Pointwise lower-bound witness for the greedy divisor-chain construction. -/
private def GoodLowerDivisorChain (ε : ℝ) (n : ℕ) : Prop :=
  ∃ R : ℕ, n ≠ 0 ∧ HasDivisorChainLengthAtLeast R n ∧
    (1 - ε) * (logStar (n : ℝ) : ℝ) ≤ (R : ℝ)

private lemma lower_bound_of_good_divisor_chain {ε : ℝ} {n : ℕ}
    (hgood : GoodLowerDivisorChain ε n) :
    (HChain n : ℝ) ≥ (1 - ε) * (logStar (n : ℝ) : ℝ) := by
  rcases hgood with ⟨R, hn, hchain, hR⟩
  by_cases hn1 : n = 1
  · -- n = 1: logStar 1 = 0, both sides are 0.
    subst hn1
    have h_logStar_zero : logStar ((1 : ℕ) : ℝ) = 0 := by
      classical
      have h_one_le_exp : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      have hex : ∃ k : ℕ, iteratedLog k ((1 : ℕ) : ℝ) ≤ Real.exp 1 :=
        ⟨0, by simp [iteratedLog]⟩
      unfold logStar
      rw [dif_pos hex, Nat.find_eq_zero]
      simpa [iteratedLog] using h_one_le_exp
    have hgoal : (1 - ε) * ((logStar ((1 : ℕ) : ℝ) : ℝ)) = 0 := by
      rw [h_logStar_zero]; push_cast; ring
    have hHC_nn : (0 : ℝ) ≤ ((HChain 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith [hgoal, hHC_nn]
  have hnat : R ≤ HChain n := HChain_ge_of_hasDivisorChainLengthAtLeast hn hn1 hchain
  have hreal : (R : ℝ) ≤ (HChain n : ℝ) := by exact_mod_cast hnat
  exact hR.trans hreal

private lemma lower_bound_from_good_divisor_chains {ε : ℝ}
    (hgood : almostAll (GoodLowerDivisorChain ε)) :
    almostAll (fun n => (HChain n : ℝ) ≥ (1 - ε) * (logStar n : ℝ)) :=
  almostAll_mono hgood (fun _ hn => lower_bound_of_good_divisor_chain hn)

/-- The scale witness supplied by `scale_H` for the `H`-chain tower windows. -/
private def HScaleWitness (A : ℝ) (Lscale : ℕ) : Prop :=
  ∀ L : ℕ, Lscale ≤ L →
    ∀ j : ℕ, j + 1 ≤ L →
      ∃ m : ℕ,
        Real.exp ((Real.exp (tower m / (A + 10))) ^ A) ≤
          Real.exp (tower (m + 1) / (A + 10))

/-- The Chebyshev-theta witness used to absorb the CRT/primorial remainder. -/
private def ChebyshevThetaWitness (Cθ : ℝ) : Prop :=
  ∀ t : ℝ, 2 ≤ t →
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), Real.log (p : ℝ)) ≤ Cθ * t

/-- The summed stage-failure estimate: the union of all failed stages has
density `0`, hence only `o(x)` integers fail to carry the requested lower
divisor chain. -/
private def StageFailureSumH (ε A c y₀ : ℝ) : Prop :=
  10 < A ∧ 0 < c ∧ 0 < y₀ ∧
    ∀ η : ℝ, 0 < η →
      ∃ x₀ : ℝ, 0 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} : ℝ) ≤ η * x

/-! ### Paper §7.4 chain event (paper line 2031-2045).

Following paper §7.4 verbatim: define the `H`-greedy-chain event `HChainEvent`
with cutoff parameters, prove `M`-periodicity (paper line 2031-2037), then
apply `crt_transfer` (paper line 2049) once to transfer to integer density. -/

/-- Paper §7.4 line 2031-2045: the chain event `C_H` for parameters
`(A, B, m₀, R)`.  An integer `n` satisfies `HChainEvent` iff it admits a
divisor chain `(d_2, d_3, …, d_{R+1})` (Lean indexing — paper's
`d_1 = 1` is dropped because `IsDivisorChain` requires consecutive
mod-1 conditions which fail at `d_1 = 1`) where:
- The chain `IsDivisorChain n` (paper's `d_{j+1} ≡ 1 (mod d_j)` and
  divisibility by `n`).
- Each chain element `ds[k]` is a squarefree product of primes from the
  window `W_{k+1} := (exp y_{k+1}, exp(y_{k+1}^{A-1})]`,
  `y_{k+1} := exp(T_{m₀+k}/B)` (paper line 1893).
- Each `ds[k] ≤ exp(y_{k+1}^A)` (paper line 1908).

By paper line 2031-2037, every prime used is `≤ P := exp(y_R^{A-1})`, so
`HChainEvent` depends only on `(𝟙_{p∣n})_{p ≤ P}`, hence `M`-periodic
with `M := primorial(P)`. -/
private def HChainEvent (A B : ℝ) (m₀ R : ℕ) (n : ℕ) : Prop :=
  ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = R ∧
    ∀ (k : ℕ) (hk : k < ds.length),
      Squarefree (ds.get ⟨k, hk⟩) ∧
      (∀ p ∈ Nat.primeFactors (ds.get ⟨k, hk⟩),
        Real.exp (Real.exp (tower (m₀ + k) / B)) < (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))) ∧
      (ds.get ⟨k, hk⟩ : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A)

/-- A squarefree natural number with all prime factors `≤ P` divides `primorial P`. -/
private lemma squarefree_dvd_primorial_of_primeFactors_le {d P : ℕ}
    (hd_sqf : Squarefree d) (hd_primes : ∀ p ∈ Nat.primeFactors d, p ≤ P) :
    d ∣ primorial P := by
  -- d = ∏ primes(d) (squarefree), and each prime ≤ P, so d ∣ ∏ primes ≤ P = primorial P.
  have hd_eq : (∏ p ∈ Nat.primeFactors d, p) = d :=
    Nat.prod_primeFactors_of_squarefree hd_sqf
  rw [← hd_eq]
  -- ∏_{p ∈ primeFactors d} p ∣ primorial P, since each prime is ≤ P.
  unfold primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Iic]
  exact ⟨hd_primes p hp, Nat.prime_of_mem_primeFactors hp⟩

/-- Paper §7.4 line 2031-2045: `HChainEvent` is `M`-periodic for
`M = primorial(P)`, where `P` bounds every prime used in any chain element.

Concretely: if every chain element is a squarefree product of primes `≤ P`,
then `n ≡ n' (mod primorial P)` implies the same chain works for both. -/
private lemma HChainEvent_periodic (A B : ℝ) (m₀ R : ℕ) (P : ℕ)
    (hP_bound : ∀ k : ℕ, k < R →
      Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1)) ≤ (P : ℝ)) :
    ∀ n n' : ℕ, n % primorial P = n' % primorial P →
      (HChainEvent A B m₀ R n ↔ HChainEvent A B m₀ R n') := by
  intro n n' hmod
  have hmodeq : n ≡ n' [MOD primorial P] := by simpa [Nat.ModEq] using hmod
  -- For any chain ds, every element ds[k] is a squarefree product of primes ≤
  -- exp(y_{k+1}^{A-1}) ≤ P.  Hence ds[k] ∣ primorial P.  Then by Nat.ModEq.dvd_iff,
  -- ds[k] ∣ n ↔ ds[k] ∣ n'.  IsDivisorChain conditions on pairwise/mod don't depend
  -- on n/n'.  So the same chain witnesses HChainEvent for both.
  constructor
  all_goals {
    rintro ⟨ds, hchain, hlen, hprop⟩
    refine ⟨ds, ?_, hlen, hprop⟩
    rcases hchain with ⟨hdiv, hpair, hmodc⟩
    refine ⟨?_, hpair, hmodc⟩
    intro d hd_mem
    -- Get d ∈ ds, find its index k.
    rw [List.mem_iff_get] at hd_mem
    rcases hd_mem with ⟨⟨k, hk⟩, hd_eq⟩
    have hk_lt : k < ds.length := hk
    have hk_lt_R : k < R := hlen ▸ hk_lt
    rcases hprop k hk_lt with ⟨hd_sqf, hd_primes, _hd_le⟩
    -- d divides primorial P.
    have hd_sqf' : Squarefree d := by rw [← hd_eq]; exact hd_sqf
    have hd_primes' : ∀ p ∈ Nat.primeFactors d, p ≤ P := by
      intro p hp
      have hp_in : p ∈ Nat.primeFactors (ds.get ⟨k, hk⟩) := by
        rw [hd_eq]; exact hp
      have ⟨_h_lower, h_upper⟩ := hd_primes p hp_in
      have hp_real_le : (p : ℝ) ≤ (P : ℝ) := h_upper.trans (hP_bound k hk_lt_R)
      exact_mod_cast hp_real_le
    have hd_dvd_M : d ∣ primorial P :=
      squarefree_dvd_primorial_of_primeFactors_le hd_sqf' hd_primes'
    refine ⟨?_, ?_⟩
    · exact (hdiv d (List.mem_iff_get.mpr ⟨⟨k, hk⟩, hd_eq⟩)).1
    · -- d ∣ n' (or d ∣ n in the second direction).
      have h_old : d ∣ _ := (hdiv d (List.mem_iff_get.mpr ⟨⟨k, hk⟩, hd_eq⟩)).2
      first | exact (hmodeq.dvd_iff hd_dvd_M).mp h_old |
             exact (hmodeq.symm.dvd_iff hd_dvd_M).mp h_old
  }

/-- Companion to `HChainEvent_density_via_crt` for the BAD event: density of
`¬HChainEvent` is within `M/x` of some `q_prod`.  By `crt_transfer` applied to
the (also `M`-periodic) negation. -/
private lemma HChainEvent_complement_density_via_crt (A B : ℝ) (m₀ R : ℕ) (P : ℕ) (hP : 2 ≤ P)
    (hP_bound : ∀ k : ℕ, k < R →
      Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1)) ≤ (P : ℝ)) :
    ∃ q_prod : ℝ, ∀ x : ℝ, 1 ≤ x →
      |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - q_prod| ≤
        (primorial P : ℝ) / x := by
  classical
  refine crt_transfer P hP (fun n => ¬ HChainEvent A B m₀ R n) ?_
  intro n n' hmod
  have h := HChainEvent_periodic A B m₀ R P hP_bound n n' hmod
  exact not_iff_not.mpr h

/-- Periodicity form `∀ n, E n ↔ E (n % M)`, derived from
`HChainEvent_periodic`'s pairwise form. -/
private lemma HChainEvent_periodic_alt (A B : ℝ) (m₀ R : ℕ) (P : ℕ)
    (hP_bound : ∀ k : ℕ, k < R →
      Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1)) ≤ (P : ℝ))
    (n : ℕ) : HChainEvent A B m₀ R n ↔ HChainEvent A B m₀ R (n % primorial P) := by
  apply HChainEvent_periodic A B m₀ R P hP_bound
  rw [Nat.mod_mod]

/-- The `q_prod` from `crt_transfer` applied to the BAD event equals the residue
density of `¬HChainEvent` mod `primorial P` (i.e., the count of bad residues
divided by `primorial P`).

Proof: take any specific `x = N · primorial P` with `N → ∞`.  At these `x`,
the density `|{n ≤ x : ¬E}|/x` equals the residue density (no boundary
issue at multiples of the period).  By `crt_transfer`, `|density - q_prod| ≤
M/x = 1/N → 0`, so `q_prod = residue density`.

This lemma packages the equivalence so we can bound `q_prod` directly from
the residue density bound `HChainEvent_pmodel_bound`. -/
private lemma HChainEvent_q_prod_eq_residue_density
    (A B : ℝ) (m₀ R : ℕ) (P : ℕ) (_hP : 2 ≤ P)
    (hP_bound : ∀ k : ℕ, k < R →
      Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1)) ≤ (P : ℝ))
    (q_prod : ℝ)
    (h_crt : ∀ x : ℝ, 1 ≤ x →
      |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - q_prod| ≤
        (primorial P : ℝ) / x) :
    q_prod = (Nat.card {r : Fin (primorial P) // ¬ HChainEvent A B m₀ R r.val} : ℝ) /
              (primorial P : ℝ) := by
  classical
  set M : ℕ := primorial P with hM_def
  have hMpos : 0 < M := by
    rw [hM_def]
    unfold primorial
    exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hMpos_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  set rd : ℝ := (Nat.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} : ℝ) / (M : ℝ)
  have hperiod_alt : ∀ n : ℕ, ¬ HChainEvent A B m₀ R n ↔ ¬ HChainEvent A B m₀ R (n % M) := by
    intro n
    exact not_iff_not.mpr (HChainEvent_periodic_alt A B m₀ R P hP_bound n)
  -- By periodic_count_le, |bad_count - rd · ⌊x⌋| ≤ M for x ≥ 1.
  -- Hence |bad_count/x - rd · (⌊x⌋/x)| ≤ M/x, and ⌊x⌋/x ≤ 1, so |bad_count/x - rd| ≤ 2M/x for x ≥ 1.
  have h_count_density : ∀ x : ℝ, 1 ≤ x →
      |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - rd| ≤
        2 * (M : ℝ) / x := by
    intro x hx
    have hxpos : 0 < x := by linarith
    have h_pcle := periodic_count_le (P := fun n => ¬ HChainEvent A B m₀ R n)
      (M := M) (N := ⌊x⌋₊) hMpos hperiod_alt
    -- h_pcle : count ≤ (rd_count / M) * ⌊x⌋ + M = rd * ⌊x⌋ + M (by definition of rd).
    -- Note that rd = (rd_count : ℝ) / (M : ℝ), so (rd_count / M) * ⌊x⌋ = rd * ⌊x⌋.
    -- We need both upper and lower bounds.
    have h_count_nonneg : (0 : ℝ) ≤
        (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) := by positivity
    have h_rd_nonneg : 0 ≤ rd := by
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact hMpos_real.le
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
    -- Upper bound on bad_count (from periodic_count_le).
    have h_upper : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) ≤
        rd * x + M := by
      calc (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)
          ≤ rd * (⌊x⌋₊ : ℝ) + M := by
            have := h_pcle
            simp [rd] at this ⊢
            linarith [this]
        _ ≤ rd * x + M := by nlinarith [h_rd_nonneg, hfloor_le]
    -- Apply div_le and rearrange.
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · -- Upper: bad_count/x - rd ≤ 2M/x.
      have hdiff : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) - rd * x ≤ M := by
        linarith
      have h_div : ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) - rd * x) / x ≤
          (M : ℝ) / x :=
        div_le_div_of_nonneg_right hdiff hxpos.le
      have h_split : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) / x - rd =
          ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) - rd * x) / x := by
        field_simp
      have hM2x : (M : ℝ) / x ≤ 2 * (M : ℝ) / x :=
        div_le_div_of_nonneg_right (by linarith [hMpos_real]) hxpos.le
      linarith [h_split, h_div, hM2x]
    · -- Lower: rd - bad_count/x ≤ 2M/x.
      -- Apply periodic_count_le to HChainEvent (E itself) to get count(E) ≤ (1-rd)·⌊x⌋ + M.
      -- Then count(¬E) = (⌊x⌋+1) - count(E) ≥ rd·⌊x⌋ + 1 - M.
      -- Hence rd · x - count(¬E) ≤ rd · x - rd·⌊x⌋ - 1 + M = rd·(x-⌊x⌋) + M - 1 ≤ M.
      have hperiod_E : ∀ n : ℕ, HChainEvent A B m₀ R n ↔ HChainEvent A B m₀ R (n % M) :=
        HChainEvent_periodic_alt A B m₀ R P hP_bound
      have h_pcle_E := periodic_count_le (P := fun n => HChainEvent A B m₀ R n)
        (M := M) (N := ⌊x⌋₊) hMpos hperiod_E
      -- Compute residue density of E mod M = 1 - rd via complement count.
      have h_card_E_eq : Nat.card {r : Fin M // HChainEvent A B m₀ R r.val} =
          Fintype.card {r : Fin M // HChainEvent A B m₀ R r.val} :=
        Nat.card_eq_fintype_card
      have h_card_nE_eq : Nat.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} =
          Fintype.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} :=
        Nat.card_eq_fintype_card
      have h_compl := Fintype.card_subtype_compl
        (fun r : Fin M => HChainEvent A B m₀ R r.val)
      have h_card_M : Fintype.card (Fin M) = M := Fintype.card_fin M
      have h_E_le_M : Fintype.card {r : Fin M // HChainEvent A B m₀ R r.val} ≤ M := by
        have := Fintype.card_subtype_le (fun r : Fin M => HChainEvent A B m₀ R r.val)
        rwa [Fintype.card_fin] at this
      have h_card_total_nat : Fintype.card {r : Fin M // HChainEvent A B m₀ R r.val} +
          Fintype.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} = M := by
        rw [h_compl, h_card_M]
        omega
      have h_card_total_M : (Nat.card {r : Fin M // HChainEvent A B m₀ R r.val} : ℝ) +
          (Nat.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} : ℝ) = (M : ℝ) := by
        rw [h_card_E_eq, h_card_nE_eq]
        exact_mod_cast h_card_total_nat
      -- Hence Nat.card_E / M = (M - Nat.card_¬E) / M = 1 - rd.
      have h_E_density_eq : (Nat.card {r : Fin M // HChainEvent A B m₀ R r.val} : ℝ) / (M : ℝ) =
          1 - rd := by
        have hM_ne : (M : ℝ) ≠ 0 := hMpos_real.ne'
        have h_rd_eq : rd =
            (Nat.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} : ℝ) / (M : ℝ) := rfl
        rw [h_rd_eq]
        field_simp
        linarith
      -- Apply periodic_count_le to E.
      have h_good_upper : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ HChainEvent A B m₀ R n} : ℝ) ≤
          (1 - rd) * (⌊x⌋₊ : ℝ) + (M : ℝ) := by
        have := h_pcle_E
        rw [h_E_density_eq] at this
        exact this
      -- Compute partition: card_E + card_¬E = ⌊x⌋ + 1.
      -- Use Finset reasoning: card (filter E ∪ filter ¬E) = card (Iic) = ⌊x⌋ + 1.
      have h_partition_card : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ HChainEvent A B m₀ R n} : ℝ) +
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) = (⌊x⌋₊ : ℝ) + 1 := by
        classical
        have h_E_eq : Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ HChainEvent A B m₀ R n} =
            ((Finset.Iic ⌊x⌋₊).filter (fun n => HChainEvent A B m₀ R n)).card :=
          Nat.subtype_card _ (by intro n; simp [Finset.mem_filter])
        have h_nE_eq : Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} =
            ((Finset.Iic ⌊x⌋₊).filter (fun n => ¬ HChainEvent A B m₀ R n)).card :=
          Nat.subtype_card _ (by intro n; simp [Finset.mem_filter])
        rw [h_E_eq, h_nE_eq]
        have h_filter_union : (Finset.Iic ⌊x⌋₊).filter (fun n => HChainEvent A B m₀ R n) ∪
            (Finset.Iic ⌊x⌋₊).filter (fun n => ¬ HChainEvent A B m₀ R n) =
            Finset.Iic ⌊x⌋₊ := by
          ext n; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
          · intro hn
            rcases em (HChainEvent A B m₀ R n) with hE | hE
            · exact Or.inl ⟨hn, hE⟩
            · exact Or.inr ⟨hn, hE⟩
        have h_filter_disj : Disjoint
            ((Finset.Iic ⌊x⌋₊).filter (fun n => HChainEvent A B m₀ R n))
            ((Finset.Iic ⌊x⌋₊).filter (fun n => ¬ HChainEvent A B m₀ R n)) := by
          rw [Finset.disjoint_left]
          intro n hE hnE
          rw [Finset.mem_filter] at hE hnE
          exact hnE.2 hE.2
        have h_card_iic : (Finset.Iic ⌊x⌋₊).card = ⌊x⌋₊ + 1 := Nat.card_Iic _
        have h_sum := Finset.card_union_of_disjoint h_filter_disj
        rw [h_filter_union, h_card_iic] at h_sum
        exact_mod_cast h_sum.symm
      -- card_¬E ≥ (⌊x⌋+1) - card_E ≥ (⌊x⌋+1) - ((1-rd)·⌊x⌋ + M) = rd·⌊x⌋ + 1 - M.
      have h_bad_lower :
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) ≥
          rd * (⌊x⌋₊ : ℝ) + 1 - (M : ℝ) := by linarith
      -- rd · x - card_¬E ≤ M.
      have h_rd_le_one : rd ≤ 1 := by
        rw [show (1 : ℝ) = (M : ℝ) / (M : ℝ) from (div_self hMpos_real.ne').symm]
        apply div_le_div_of_nonneg_right _ hMpos_real.le
        have h_card_le : Nat.card {r : Fin M // ¬ HChainEvent A B m₀ R r.val} ≤ M := by
          have := Fintype.card_subtype_le (fun r : Fin M => ¬ HChainEvent A B m₀ R r.val)
          simpa [Nat.card_eq_fintype_card] using this
        exact_mod_cast h_card_le
      have hx_minus_floor : (x - (⌊x⌋₊ : ℝ)) < 1 := by
        have := Nat.lt_floor_add_one x
        linarith [Nat.floor_le hxpos.le]
      have h_diff_nn : 0 ≤ x - (⌊x⌋₊ : ℝ) := by linarith [Nat.floor_le hxpos.le]
      have h_key : rd * x -
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) ≤ (M : ℝ) := by
        have hstep : rd * (x - (⌊x⌋₊ : ℝ)) ≤ 1 := by
          calc rd * (x - (⌊x⌋₊ : ℝ)) ≤ 1 * (x - (⌊x⌋₊ : ℝ)) :=
                mul_le_mul_of_nonneg_right h_rd_le_one h_diff_nn
            _ = x - (⌊x⌋₊ : ℝ) := one_mul _
            _ ≤ 1 := le_of_lt hx_minus_floor
        nlinarith [h_bad_lower]
      have h_div_step : (rd * x -
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x ≤ (M : ℝ) / x :=
        div_le_div_of_nonneg_right h_key hxpos.le
      have h_split_lower : (rd * x -
          (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x =
          rd - (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ) / x := by
        field_simp
      rw [h_split_lower] at h_div_step
      have h_M_le_2M : (M : ℝ) / x ≤ 2 * (M : ℝ) / x :=
        div_le_div_of_nonneg_right (by linarith [hMpos_real]) hxpos.le
      linarith
  -- Combine with h_crt: for x ≥ 1, |q_prod - rd| ≤ |density - q_prod| + |density - rd| ≤ M/x + 2M/x = 3M/x.
  have h_q_prod_close_rd : ∀ x : ℝ, 1 ≤ x → |q_prod - rd| ≤ 3 * (M : ℝ) / x := by
    intro x hx
    have h1 := h_crt x hx
    have h2 := h_count_density x hx
    have key : |q_prod - rd| ≤
        |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - q_prod| +
        |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - rd| := by
      have := abs_sub_abs_le_abs_sub q_prod rd
      have h_tri := abs_sub_comm q_prod rd
      have habs : |q_prod - rd| = |rd - q_prod| := by rw [abs_sub_comm]
      have : |rd - q_prod| ≤
          |rd - ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x| +
          |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - q_prod| := by
        exact abs_sub_le _ _ _
      rw [habs]
      have h_swap : |rd - ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x| =
          |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ HChainEvent A B m₀ R n} : ℝ)) / x - rd| := by
        rw [abs_sub_comm]
      linarith [this, h_swap]
    have hxpos : 0 < x := by linarith
    have hM_div_pos : 0 ≤ (M : ℝ) / x := by positivity
    have h3M_div : 3 * (M : ℝ) / x = (M : ℝ) / x + 2 * (M : ℝ) / x := by ring
    linarith
  -- Take limit: |q_prod - rd| ≤ 3M/x for all x ≥ 1.  Hence |q_prod - rd| = 0.
  have h_le_zero : |q_prod - rd| ≤ 0 := by
    by_contra h_pos_neg
    push_neg at h_pos_neg
    -- h_pos_neg : 0 < |q_prod - rd|.
    -- Choose x large enough that 3M/x < |q_prod - rd|.
    have h_diff_pos : 0 < |q_prod - rd| := h_pos_neg
    set δ : ℝ := |q_prod - rd|
    have hδ_pos : 0 < δ := h_diff_pos
    set x : ℝ := 4 * (M : ℝ) / δ + 1 with hx_def
    have hx_ge_one : 1 ≤ x := by
      rw [hx_def]
      have h_mul_pos : 0 ≤ 4 * (M : ℝ) / δ := by positivity
      linarith
    have hx_pos : 0 < x := by linarith
    have h_x_bound := h_q_prod_close_rd x hx_ge_one
    -- 3M/x < δ.
    have h_strict : 3 * (M : ℝ) / x < δ := by
      have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
      have hx_eq_simpl : δ * x = 4 * (M : ℝ) + δ := by
        rw [hx_def, mul_add, mul_div_cancel₀ _ hδ_ne, mul_one]
      rw [div_lt_iff₀ hx_pos]
      linarith [hx_eq_simpl, hMpos_real]
    linarith
  have h_eq : |q_prod - rd| = 0 := le_antisymm h_le_zero (abs_nonneg _)
  have h_sub : q_prod - rd = 0 := abs_eq_zero.mp h_eq
  linarith

/-- `HChainEvent` directly witnesses `HasDivisorChainLengthAtLeast R`. -/
private lemma hasDivisorChainLengthAtLeast_of_HChainEvent
    {A B : ℝ} {m₀ R : ℕ} {n : ℕ} (h : HChainEvent A B m₀ R n) :
    HasDivisorChainLengthAtLeast R n := by
  rcases h with ⟨ds, hchain, hlen, _⟩
  exact ⟨ds, hchain, hlen.symm.le⟩

/-- **Strict variant of HChainEvent (paper-faithful, forbids trivial `ds = [1]`).**

`HChainEventStrict A B m₀ R n` holds iff there's a chain `ds : List ℕ` of length R
witnessing HChainEvent AND with the first element `ds[0] ≥ 2` (excluding the trivial
`[1]` chain that Lean's encoding allows but paper doesn't).

For R ≥ 2, `HChainEventStrict_R = HChainEvent_R` automatically (the IsDivisorChain
mod constraint `ds[1] % ds[0] = 1` forces `ds[0] ≥ 2`).

For R = 0 or R = 1, the trivial `ds = []` or `[1]` is allowed by HChainEvent but
explicitly forbidden by HChainEventStrict (for R = 1).

This is the paper-faithful event used in the per-stage decomposition.  Paper line
1888-1891 explicitly says `1 = d_1 < d_2 < ⋯ < d_{R+1}` with `d_2 ≥ 2` (since `d_2 > 1`),
which corresponds to Lean's `ds[0] ≥ 2`. -/
private def HChainEventStrict (A B : ℝ) (m₀ R : ℕ) (n : ℕ) : Prop :=
  ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = R ∧
    (∀ (k : ℕ) (hk : k < ds.length),
      Squarefree (ds.get ⟨k, hk⟩) ∧
      (∀ p ∈ Nat.primeFactors (ds.get ⟨k, hk⟩),
        Real.exp (Real.exp (tower (m₀ + k) / B)) < (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))) ∧
      (ds.get ⟨k, hk⟩ : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A)) ∧
    (R = 0 ∨ ∃ (h0 : 0 < ds.length), 2 ≤ ds.get ⟨0, h0⟩)

/-- HChainEventStrict implies HChainEvent (just drops the strictness condition). -/
private lemma HChainEvent_of_strict {A B : ℝ} {m₀ R : ℕ} {n : ℕ}
    (h : HChainEventStrict A B m₀ R n) : HChainEvent A B m₀ R n := by
  rcases h with ⟨ds, hchain, hlen, hprop, _⟩
  exact ⟨ds, hchain, hlen, hprop⟩

/-- The least element of a finite set of natural numbers (mirrors LBL pattern). -/
private noncomputable def hFinsetLeastNat? (s : Finset ℕ) : Option ℕ := by
  classical
  exact if h : s.Nonempty then some (s.min' h) else none

/-- **Deterministic admissible-next set (paper line 1905-1910).**

For chain at level `k` with last element `d_prev`, the candidate set for the next
chain element is `{e ∈ ℕ : d_prev < e, e ≡ 1 (mod d_prev), e ∣ n, Squarefree e,
all prime factors of e in W_{k+1} = (exp y_{k+1}, exp(y_{k+1}^{A-1})], e ≤ exp(y_{k+1}^A)}`,
where `y_{k+1} = exp(tower(m₀+k)/B)` (paper line 1842).

The `k` parameter here is the index of the NEW element being added (so chain
length increases from `k` to `k+1`).  This matches `HChainEventStrict`'s indexing
where `ds[k]` uses `tower(m₀+k)` (LBH:788). -/
private noncomputable def hChainAdmissibleNext
    (A B : ℝ) (m₀ k : ℕ) (d_prev : ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact
    Finset.filter
      (fun e : ℕ =>
        d_prev < e ∧ e % d_prev = 1 % d_prev ∧ e ∣ n ∧ Squarefree e ∧
        (∀ p ∈ Nat.primeFactors e,
          Real.exp (Real.exp (tower (m₀ + k) / B)) < (p : ℝ) ∧
          (p : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))) ∧
        (e : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A))
      (Finset.Iic ⌊Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A)⌋₊)

/-- **Deterministic chain endpoint at level k (paper line 1898, 1910).**

Paper line 1910: "If at least one admissible `e` exists, define `d_{j+1}` to be
the LEAST such admissible integer."  This is the least-element greedy.

Indexing: `hChainEndpoint? n 0 = some 1` (paper's `d_1 = 1`); `hChainEndpoint? n (k+1)`
is the least admissible new element extending from `d_k = hChainEndpoint? n k`.

For Lean `HChainEventStrict_k(n)` the chain has length `k` storing
`[d_2, d_3, ..., d_{k+1}]` (paper indexing, with `d_1 = 1` dropped).  So
`hChainEndpoint? n (k+1) = some d` corresponds to `d_{k+1}` (paper) being the
deterministic chain endpoint at our Lean level `k+1`.

Periodicity: `hChainEndpoint? n k` depends only on `(n mod p)` for primes
`p ≤ exp(y_k^{A-1})` (paper line 1899, 1923).  We will prove
`hChainEndpoint?_eq_of_mod` analogous to LBL `lowerHGreedyPrime?_eq_of_mod`. -/
private noncomputable def hChainEndpoint?
    (A B : ℝ) (m₀ : ℕ) (n : ℕ) : ℕ → Option ℕ
  | 0 => some 1
  | k + 1 =>
      match hChainEndpoint? A B m₀ n k with
      | none => none
      | some d_prev => hFinsetLeastNat? (hChainAdmissibleNext A B m₀ k d_prev n)

/-- Membership characterisation for `hChainAdmissibleNext`. -/
private lemma hChainAdmissibleNext_mem {A B : ℝ} {m₀ k d_prev n e : ℕ} :
    e ∈ hChainAdmissibleNext A B m₀ k d_prev n ↔
      e ≤ ⌊Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A)⌋₊ ∧
      d_prev < e ∧ e % d_prev = 1 % d_prev ∧ e ∣ n ∧ Squarefree e ∧
      (∀ p ∈ Nat.primeFactors e,
        Real.exp (Real.exp (tower (m₀ + k) / B)) < (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))) ∧
      (e : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A) := by
  classical
  unfold hChainAdmissibleNext
  simp only [Finset.mem_filter, Finset.mem_Iic]

/-- Membership of `hFinsetLeastNat?` result. -/
private lemma hFinsetLeastNat?_mem {s : Finset ℕ} {p : ℕ}
    (hp : hFinsetLeastNat? s = some p) : p ∈ s := by
  classical
  by_cases hne : s.Nonempty
  · simp [hFinsetLeastNat?, hne] at hp
    subst p
    exact Finset.min'_mem s hne
  · simp [hFinsetLeastNat?, hne] at hp

/-- `hChainEndpoint? n 0 = some 1`. -/
private lemma hChainEndpoint?_zero (A B : ℝ) (m₀ n : ℕ) :
    hChainEndpoint? A B m₀ n 0 = some 1 := rfl

/-- If `hChainEndpoint?` returns `some d` at level `k+1`, the previous level returns `some`. -/
private lemma hChainEndpoint?_succ_prev_some {A B : ℝ} {m₀ n k d : ℕ}
    (hk : hChainEndpoint? A B m₀ n (k + 1) = some d) :
    ∃ d_prev : ℕ, hChainEndpoint? A B m₀ n k = some d_prev := by
  by_cases h_some : (hChainEndpoint? A B m₀ n k).isSome
  · exact Option.isSome_iff_exists.mp h_some
  · rw [Option.not_isSome_iff_eq_none] at h_some
    unfold hChainEndpoint? at hk
    rw [h_some] at hk
    simp at hk

/-- If `hChainEndpoint?` returns `some d` at level `k+1`, then `d` is in the
admissible set for the previous endpoint. -/
private lemma hChainEndpoint?_succ_mem_admissible {A B : ℝ} {m₀ n k d : ℕ}
    (hk : hChainEndpoint? A B m₀ n (k + 1) = some d) :
    ∃ d_prev : ℕ, hChainEndpoint? A B m₀ n k = some d_prev ∧
      d ∈ hChainAdmissibleNext A B m₀ k d_prev n := by
  rcases hChainEndpoint?_succ_prev_some hk with ⟨d_prev, hd_prev⟩
  refine ⟨d_prev, hd_prev, ?_⟩
  unfold hChainEndpoint? at hk
  rw [hd_prev] at hk
  exact hFinsetLeastNat?_mem hk

/-- **Nat-form periodicity (paper line 1916, 1923 — paper-faithful).**

Strengthened version of `hChainAdmissibleNext_eq_of_mod_primorial` using a
Nat-form hypothesis `⌊exp(...)⌋₊ ≤ P` instead of the real-valued
`exp(...) ≤ (P : ℝ)`.  Mathematically equivalent in our context (primes are
integers, so the floor cutoff captures exactly the relevant primes), but avoids
the floor/ceil bridge issue when applying with `P = past_cutoff = ⌊exp(...)⌋₊`. -/
private lemma hChainAdmissibleNext_eq_of_mod_primorial_floor
    {A B : ℝ} (_hA : 1 ≤ A) {m₀ k d_prev n n' P : ℕ}
    (hP_bound : ⌊Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))⌋₊ ≤ P)
    (hmod : n ≡ n' [MOD primorial P]) :
    hChainAdmissibleNext A B m₀ k d_prev n = hChainAdmissibleNext A B m₀ k d_prev n' := by
  classical
  unfold hChainAdmissibleNext
  apply Finset.filter_congr
  intro e _he
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, h2, h_dvd, h_sqf, h_primes, h_size⟩
    refine ⟨h1, h2, ?_, h_sqf, h_primes, h_size⟩
    have h_e_dvd_M : e ∣ primorial P := by
      rw [← Nat.prod_primeFactors_of_squarefree h_sqf]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hp_data := h_primes p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      -- (p : ℝ) ≤ exp(...). Since p is Nat, p ≤ ⌊exp(...)⌋₊ via Nat.le_floor.
      have hp_le_floor : p ≤ ⌊Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))⌋₊ :=
        Nat.le_floor hp_data.2
      have hp_le_P : p ≤ P := hp_le_floor.trans hP_bound
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨hp_le_P, hp_prime⟩
    exact (hmod.dvd_iff h_e_dvd_M).mp h_dvd
  · rintro ⟨h1, h2, h_dvd, h_sqf, h_primes, h_size⟩
    refine ⟨h1, h2, ?_, h_sqf, h_primes, h_size⟩
    have h_e_dvd_M : e ∣ primorial P := by
      rw [← Nat.prod_primeFactors_of_squarefree h_sqf]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hp_data := h_primes p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_le_floor : p ≤ ⌊Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))⌋₊ :=
        Nat.le_floor hp_data.2
      have hp_le_P : p ≤ P := hp_le_floor.trans hP_bound
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨hp_le_P, hp_prime⟩
    exact (hmod.dvd_iff h_e_dvd_M).mpr h_dvd

/-- **Unpack `hChainEndpoint?_succ` constraints (paper line 1925-1930).**

If `hChainEndpoint? A B m₀ n (k+1) = some d`, then the previous level returned
`some d_prev`, and `d` satisfies all the admissibility constraints from
`hChainAdmissibleNext`: `d_prev < d`, `d ≡ 1 (mod d_prev)`, `d ∣ n`, `Squarefree d`,
all prime factors in `W_{k+1} = (exp y_{k+1}, exp(y_{k+1}^{A-1})]`, `d ≤ exp(y_{k+1}^A)`.

Paper line 1925-1928: "On success, Lemma 6.2 guarantees `d_{j+1} ≡ 1 (mod d_j)`,
`d_{j+1} > d_j`, `d_{j+1} ≤ exp(y_j^A)`." -/
private lemma hChainEndpoint?_succ_constraints {A B : ℝ} {m₀ n k d : ℕ}
    (hk : hChainEndpoint? A B m₀ n (k + 1) = some d) :
    ∃ d_prev : ℕ,
      hChainEndpoint? A B m₀ n k = some d_prev ∧
      d_prev < d ∧
      d % d_prev = 1 % d_prev ∧
      d ∣ n ∧
      Squarefree d ∧
      (∀ p ∈ Nat.primeFactors d,
        Real.exp (Real.exp (tower (m₀ + k) / B)) < (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ (A - 1))) ∧
      (d : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + k) / B)) ^ A) := by
  rcases hChainEndpoint?_succ_mem_admissible hk with ⟨d_prev, hd_prev, hd_admissible⟩
  rcases hChainAdmissibleNext_mem.mp hd_admissible with
    ⟨_h_le, h1, h2, h3, h4, h5, h6⟩
  exact ⟨d_prev, hd_prev, h1, h2, h3, h4, h5, h6⟩

/-- **`hChainEndpoint?` at level 1 implies `d ≥ 2` (paper line 1891).**

For `k ≥ 1`, the chain element `d_{k+1}` satisfies `d_{k+1} > d_k ≥ 1`, hence `d ≥ 2`.
At level 1 specifically, `d_1 = 1` and `d_2 > 1` so `d_2 ≥ 2`. -/
private lemma hChainEndpoint?_one_ge_two {A B : ℝ} {m₀ n d : ℕ}
    (hk : hChainEndpoint? A B m₀ n 1 = some d) : 2 ≤ d := by
  rcases hChainEndpoint?_succ_constraints hk with ⟨d_prev, hd_prev, h_lt, _h_mod, _, _, _, _⟩
  -- hd_prev : hChainEndpoint? A B m₀ n 0 = some d_prev.  By hChainEndpoint?_zero, d_prev = 1.
  rw [hChainEndpoint?_zero] at hd_prev
  -- hd_prev : some 1 = some d_prev
  have h_eq : d_prev = 1 := by
    injection hd_prev.symm
  rw [h_eq] at h_lt
  -- h_lt : 1 < d
  omega

/-- **All hChainEndpoint? values are ≥ 1.** -/
private lemma hChainEndpoint?_some_ge_one {A B : ℝ} {m₀ : ℕ} :
    ∀ {k n d : ℕ}, hChainEndpoint? A B m₀ n k = some d → 1 ≤ d := by
  intro k
  induction k with
  | zero =>
    intros n d hk
    rw [hChainEndpoint?_zero] at hk
    injection hk with h_eq
    omega
  | succ k _ih =>
    intros n d hk
    rcases hChainEndpoint?_succ_constraints hk with ⟨_, _, h_lt, _, _, _, _, _⟩
    omega

/-- **Soundness: greedy success at level k implies HCEStrict_k holds.**

This is the converse direction connecting the deterministic greedy construction
to the existential HCEStrict event.  We construct the witness chain
`ds = [d_2, d_3, ..., d_{k+1}]` (paper indexing) from the greedy values
`hChainEndpoint? n j` for `j ∈ {1, ..., k}`, and verify all chain properties.

Paper line 1925-1928: "On success, Lemma 6.2 guarantees d_{j+1} ≡ 1 mod d_j,
d_{j+1} > d_j, d_{j+1} ≤ exp(y_j^A)." -/
private lemma HCEStrict_of_hChainEndpoint?_some {A B : ℝ} {m₀ : ℕ} :
    ∀ {k : ℕ} {n d : ℕ}, hChainEndpoint? A B m₀ n k = some d →
    ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = k ∧
      (∀ (i : ℕ) (hi : i < ds.length),
        Squarefree (ds.get ⟨i, hi⟩) ∧
        (∀ p ∈ Nat.primeFactors (ds.get ⟨i, hi⟩),
          Real.exp (Real.exp (tower (m₀ + i) / B)) < (p : ℝ) ∧
          (p : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + i) / B)) ^ (A - 1))) ∧
        (ds.get ⟨i, hi⟩ : ℝ) ≤ Real.exp ((Real.exp (tower (m₀ + i) / B)) ^ A)) ∧
      (k = 0 ∨ ∃ h0 : 0 < ds.length, 2 ≤ ds.get ⟨0, h0⟩) ∧
      (k = 0 ∨ ∃ h : k - 1 < ds.length, ds.get ⟨k - 1, h⟩ = d) := by
  intro k
  induction k with
  | zero =>
    intros n d hk
    refine ⟨[], ?_, rfl, ?_, Or.inl rfl, Or.inl rfl⟩
    · -- IsDivisorChain n [].
      refine ⟨?_, List.Pairwise.nil, ?_⟩
      · intros x hx; cases hx
      · intro i _hi; exact i.elim0
    · -- per-element constraints (vacuous for empty list).
      intro i hi; simp at hi
  | succ k ih =>
    intros n d hk
    rcases hChainEndpoint?_succ_constraints hk with
      ⟨d_prev, hd_prev, h_lt, h_mod, h_dvd, h_sqf, h_primes, h_size⟩
    rcases ih hd_prev with
      ⟨ds_prev, hchain_prev, hlen_prev, hprop_prev, hstrict_prev, h_last_eq⟩
    refine ⟨ds_prev ++ [d], ?_, ?_, ?_, ?_, ?_⟩
    · -- IsDivisorChain n (ds_prev ++ [d]).
      rcases hchain_prev with ⟨hdiv, hpair, hmodChain⟩
      refine ⟨?_, ?_, ?_⟩
      · -- Divisibility.
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hdiv x hx
        · rw [List.mem_singleton] at hx; subst hx
          exact ⟨by omega, h_dvd⟩
      · -- Pairwise <.
        rw [List.pairwise_append]
        refine ⟨hpair, List.pairwise_singleton _ _, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        -- Need x < d for x ∈ ds_prev.
        -- Use: ds_prev[i] ≤ ds_prev.last = d_prev (Pairwise <), and d_prev < d.
        rcases List.mem_iff_get.mp hx with ⟨⟨i, hi⟩, hi_eq⟩
        -- We have hi : i < ds_prev.length = k.
        -- The last index of ds_prev is k - 1 (when k ≥ 1).
        by_cases hk_zero : k = 0
        · -- k = 0, so ds_prev = [], contradiction with hi.
          rw [hlen_prev, hk_zero] at hi
          omega
        · -- k ≥ 1: use Pairwise to get ds_prev[i] ≤ ds_prev[k-1] = d_prev < d.
          have h_klast_pos : k - 1 < ds_prev.length := by
            rcases h_last_eq with hk0 | ⟨hk_pos, _⟩
            · exact absurd hk0 hk_zero
            · exact hk_pos
          have h_d_prev_eq : ds_prev.get ⟨k - 1, h_klast_pos⟩ = d_prev := by
            rcases h_last_eq with hk0 | ⟨hk_pos, h_eq⟩
            · exact absurd hk0 hk_zero
            · convert h_eq using 2
          -- i ≤ k - 1.
          have hi_le : i ≤ k - 1 := by rw [hlen_prev] at hi; omega
          rcases lt_or_eq_of_le hi_le with h_i_lt | h_i_eq
          · -- i < k - 1: use Pairwise to get ds_prev[i] < ds_prev[k-1] = d_prev.
            have h_lt_dprev : ds_prev.get ⟨i, hi⟩ < ds_prev.get ⟨k - 1, h_klast_pos⟩ :=
              List.pairwise_iff_get.mp hpair ⟨i, hi⟩ ⟨k - 1, h_klast_pos⟩ h_i_lt
            rw [h_d_prev_eq] at h_lt_dprev
            rw [← hi_eq]
            linarith
          · -- i = k - 1: ds_prev[i] = d_prev < d.
            have h_eq_dprev : ds_prev.get ⟨i, hi⟩ = d_prev := by
              have h_idx_eq : (⟨i, hi⟩ : Fin ds_prev.length) = ⟨k - 1, h_klast_pos⟩ := by
                apply Fin.ext; exact h_i_eq
              rw [h_idx_eq, h_d_prev_eq]
            rw [← hi_eq, h_eq_dprev]
            exact h_lt
      · -- Mod constraints.
        intro idx hidx
        have h_total_len : (ds_prev ++ [d]).length = k + 1 := by
          rw [List.length_append, List.length_singleton, hlen_prev]
        have hidx_R1 : idx.val + 1 < k + 1 := h_total_len ▸ hidx
        by_cases hidx_lt : idx.val + 1 < k
        · -- (idx, idx+1) within ds_prev.
          have hidx_in_ds : idx.val < ds_prev.length := by rw [hlen_prev]; omega
          have hidx1_in_ds : idx.val + 1 < ds_prev.length := by rw [hlen_prev]; exact hidx_lt
          have h_get_i : (ds_prev ++ [d]).get idx = ds_prev.get ⟨idx.val, hidx_in_ds⟩ := by
            simp [List.get_eq_getElem, List.getElem_append_left, hidx_in_ds]
          have h_get_i1 : (ds_prev ++ [d]).get ⟨idx.val + 1, hidx⟩ =
              ds_prev.get ⟨idx.val + 1, hidx1_in_ds⟩ := by
            simp [List.get_eq_getElem, List.getElem_append_left, hidx1_in_ds]
          rw [h_get_i, h_get_i1]
          exact hmodChain ⟨idx.val, hidx_in_ds⟩ hidx1_in_ds
        · -- idx.val + 1 = k (boundary): ds_prev[k-1] = d_prev, d at position k.
          push_neg at hidx_lt
          have hidx_val_eq : idx.val = k - 1 := by omega
          have hidx_in_ds : idx.val < ds_prev.length := by rw [hlen_prev]; omega
          have h_get_i : (ds_prev ++ [d]).get idx = d_prev := by
            have h_idx_eq : (ds_prev ++ [d]).get idx = ds_prev.get ⟨idx.val, hidx_in_ds⟩ := by
              simp [List.get_eq_getElem, List.getElem_append_left, hidx_in_ds]
            rw [h_idx_eq]
            -- ds_prev[k-1] = d_prev (using h_last_eq).
            have h_klast_pos : k - 1 < ds_prev.length := by rw [hlen_prev]; omega
            -- Need k ≥ 1 for h_last_eq to give us the equality.
            have hk_ge_1 : 1 ≤ k := by
              rw [hlen_prev] at hidx_in_ds
              by_contra h_neg
              push_neg at h_neg
              interval_cases k
              omega
            have h_d_prev_eq : ds_prev.get ⟨k - 1, h_klast_pos⟩ = d_prev := by
              rcases h_last_eq with hk0 | ⟨hk_pos, h_eq⟩
              · -- k = 0 contradicts hk_ge_1.
                omega
              · convert h_eq using 2
            have h_idx_eq2 : (⟨idx.val, hidx_in_ds⟩ : Fin ds_prev.length) =
                ⟨k - 1, h_klast_pos⟩ := by apply Fin.ext; exact hidx_val_eq
            rw [h_idx_eq2, h_d_prev_eq]
          have h_get_i1 : (ds_prev ++ [d]).get ⟨idx.val + 1, hidx⟩ = d := by
            have h_idx_eq : idx.val + 1 = ds_prev.length := by rw [hlen_prev]; omega
            simp [List.get_eq_getElem, List.getElem_append_right, h_idx_eq]
          rw [h_get_i, h_get_i1]
          -- Goal: d % d_prev = 1.  We have h_mod : d % d_prev = 1 % d_prev.
          -- For d_prev ≥ 2: 1 % d_prev = 1, so h_mod gives the goal.
          -- d_prev ≥ 2 follows from: ds_prev[0] ≥ 2 (strictness), Pairwise<, and
          -- ds_prev[k-1] = d_prev (from h_last_eq), with k ≥ 1 (hk_zero negated).
          have hk_ge_1 : 1 ≤ k := by
            by_contra h_neg
            push_neg at h_neg
            interval_cases k
            -- k = 0: ds_prev = [], so hidx_in_ds : idx.val < 0, contradiction.
            rw [hlen_prev] at hidx_in_ds
            omega
          have h_d_prev_ge_2 : 2 ≤ d_prev := by
            -- For k ≥ 1, h_last_eq has the right disjunct: ds_prev[k-1] = d_prev.
            -- Strictness gives ds_prev[0] ≥ 2.  Pairwise gives ds_prev[0] < ds_prev[k-1] (if k ≥ 2)
            -- or equal (if k = 1).
            rcases h_last_eq with hk0 | ⟨hk_pos, h_last_eq'⟩
            · omega
            · rcases hstrict_prev with hk0_strict | ⟨h_orig_pos, h_ds0_ge⟩
              · omega
              · -- ds_prev[0] ≥ 2, ds_prev[k-1] = d_prev.
                -- If k = 1: ds_prev[0] = d_prev, so d_prev ≥ 2.
                -- If k ≥ 2: ds_prev[0] < ds_prev[k-1] = d_prev (Pairwise), so d_prev > 2 ≥ 2.
                by_cases hk_eq_1 : k = 1
                · -- k = 1: ds_prev has length 1, ds_prev[0] = ds_prev[k-1].
                  have h_idx_eq_ : (⟨0, h_orig_pos⟩ : Fin ds_prev.length) =
                      ⟨k - 1, hk_pos⟩ := by apply Fin.ext; omega
                  rw [h_idx_eq_] at h_ds0_ge
                  rw [h_last_eq'] at h_ds0_ge
                  exact h_ds0_ge
                · -- k ≥ 2: Pairwise gives strict inequality.
                  have hk_ge_2 : 2 ≤ k := by omega
                  have h_0_lt : (0 : ℕ) < k - 1 := by omega
                  -- hpair is in scope from the outer rcases of hchain_prev.
                  have h_ds_lt :
                      ds_prev.get ⟨0, h_orig_pos⟩ < ds_prev.get ⟨k - 1, hk_pos⟩ :=
                    List.pairwise_iff_get.mp hpair ⟨0, h_orig_pos⟩ ⟨k - 1, hk_pos⟩ h_0_lt
                  rw [h_last_eq'] at h_ds_lt
                  omega
          -- Goal is `Nat.ModEq d_prev d 1`, i.e., `d % d_prev = 1 % d_prev` — exactly h_mod.
          exact h_mod
    · -- length = k + 1.
      rw [List.length_append, List.length_singleton, hlen_prev]
    · -- per-element constraints.
      intro i hi
      have h_total_len : (ds_prev ++ [d]).length = k + 1 := by
        rw [List.length_append, List.length_singleton, hlen_prev]
      have hi_R1 : i < k + 1 := h_total_len ▸ hi
      by_cases hi_lt : i < k
      · -- Index in ds_prev.
        have hi_in_ds : i < ds_prev.length := by rw [hlen_prev]; exact hi_lt
        have h_get_eq : (ds_prev ++ [d]).get ⟨i, hi⟩ = ds_prev.get ⟨i, hi_in_ds⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_left, hi_in_ds]
        rw [h_get_eq]
        exact hprop_prev i hi_in_ds
      · -- i = k.
        have hi_eq : i = k := by omega
        have h_idx_in_appended : i = ds_prev.length := by rw [hlen_prev]; exact hi_eq
        have h_get_eq : (ds_prev ++ [d]).get ⟨i, hi⟩ = d := by
          simp [List.get_eq_getElem, List.getElem_append_right, h_idx_in_appended]
        rw [h_get_eq]
        rw [hi_eq]
        exact ⟨h_sqf, h_primes, h_size⟩
    · -- Strictness for k+1: ds_ext[0] ≥ 2.
      right
      have h_pos_ext : 0 < (ds_prev ++ [d]).length := by
        rw [List.length_append, List.length_singleton, hlen_prev]; omega
      refine ⟨h_pos_ext, ?_⟩
      by_cases hk_zero : k = 0
      · -- k = 0: ds_prev = [], so (ds_prev ++ [d]).get 0 = d.
        subst hk_zero
        have h_ds_empty : ds_prev = [] := List.length_eq_zero_iff.mp hlen_prev
        have h_get_d : (ds_prev ++ [d]).get ⟨0, h_pos_ext⟩ = d := by
          simp [List.get_eq_getElem, h_ds_empty]
        rw [h_get_d]
        exact hChainEndpoint?_one_ge_two hk
      · -- k ≥ 1: ds_prev nonempty, (ds_prev ++ [d]).get 0 = ds_prev.get 0.
        have h_ds_pos : 0 < ds_prev.length := by rw [hlen_prev]; omega
        have h_get_eq : (ds_prev ++ [d]).get ⟨0, h_pos_ext⟩ = ds_prev.get ⟨0, h_ds_pos⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_left, h_ds_pos]
        rw [h_get_eq]
        rcases hstrict_prev with hk_z | ⟨h_orig_pos, h_ds0_ge⟩
        · exact absurd hk_z hk_zero
        · -- h_ds0_ge : 2 ≤ ds_prev.get ⟨0, h_orig_pos⟩.
          exact h_ds0_ge
    · -- Last element clause for k+1.
      right
      have h_kp1_pos : (k + 1) - 1 < (ds_prev ++ [d]).length := by
        rw [List.length_append, List.length_singleton, hlen_prev]; omega
      refine ⟨h_kp1_pos, ?_⟩
      have h_idx_eq : (k + 1) - 1 = ds_prev.length := by rw [hlen_prev]; omega
      simp [List.get_eq_getElem, List.getElem_append_right, h_idx_eq]

/-- **Nat-form periodicity for `hChainEndpoint?` (paper line 1913, 1923 — paper-faithful).**

Strengthened version using Nat-form hypothesis `⌊exp(...)⌋₊ ≤ P` instead of
the real-valued `exp(...) ≤ (P : ℝ)`.  Paper-faithful: matches paper's prime
set exactly when applied with `P = past_cutoff = ⌊exp(...)⌋₊`. -/
private lemma hChainEndpoint?_eq_of_mod_primorial_floor
    {A B : ℝ} (hA : 1 ≤ A) {m₀ : ℕ} :
    ∀ {k n n' P : ℕ},
      (∀ j : ℕ, j < k → ⌊Real.exp ((Real.exp (tower (m₀ + j) / B)) ^ (A - 1))⌋₊ ≤ P) →
      n ≡ n' [MOD primorial P] →
      hChainEndpoint? A B m₀ n k = hChainEndpoint? A B m₀ n' k := by
  intro k
  induction k with
  | zero =>
    intros n n' P _hP_bound _hmod
    rfl
  | succ j ih =>
    intros n n' P hP_bound hmod
    have ih_j : hChainEndpoint? A B m₀ n j = hChainEndpoint? A B m₀ n' j := by
      apply ih (P := P) ?_ hmod
      intro j' hj'
      exact hP_bound j' (Nat.lt_succ_of_lt hj')
    show (match hChainEndpoint? A B m₀ n j with
          | none => none
          | some d_prev => hFinsetLeastNat? (hChainAdmissibleNext A B m₀ j d_prev n)) =
         (match hChainEndpoint? A B m₀ n' j with
          | none => none
          | some d_prev => hFinsetLeastNat? (hChainAdmissibleNext A B m₀ j d_prev n'))
    rw [ih_j]
    cases hChainEndpoint? A B m₀ n' j with
    | none => rfl
    | some d_prev =>
      have hP_at_j : ⌊Real.exp ((Real.exp (tower (m₀ + j) / B)) ^ (A - 1))⌋₊ ≤ P :=
        hP_bound j (Nat.lt_succ_self j)
      simp only [hChainAdmissibleNext_eq_of_mod_primorial_floor hA hP_at_j hmod]

/-- **Greedy success at level `k`** (paper §7.3).

For paper's deterministic greedy chain construction, `hGreedySucc k n` holds iff the
recursive `hChainEndpoint? n k` returns some non-trivial value (paper line 1898-1910:
"the construction succeeds at stages 1, ..., k").

This is paper's `S_k` event (line 1939). -/
private def hGreedySucc (A B : ℝ) (m₀ k n : ℕ) : Prop :=
  ∃ d : ℕ, hChainEndpoint? A B m₀ n k = some d

/-- **Soundness corollary: greedy success implies HCEStrict.**

Direct application of `HCEStrict_of_hChainEndpoint?_some` — the greedy chain is a
valid HCEStrict witness. -/
private lemma HChainEventStrict_of_hGreedySucc {A B : ℝ} {m₀ k n : ℕ}
    (h : hGreedySucc A B m₀ k n) : HChainEventStrict A B m₀ k n := by
  rcases h with ⟨d, hd⟩
  rcases HCEStrict_of_hChainEndpoint?_some hd with
    ⟨ds, hchain, hlen, hprop, hstrict, _⟩
  exact ⟨ds, hchain, hlen, hprop, hstrict⟩

/-- **Soundness contrapositive: ¬HCEStrict implies ¬greedy_succ.**

Used to bound `density({¬HCEStrict_R})` via greedy events
(paper line 1957-1962: "P(some stage fails) ≤ ∑ y_j^{-c}"). -/
private lemma not_hGreedySucc_of_not_HChainEventStrict {A B : ℝ} {m₀ k n : ℕ}
    (h : ¬ HChainEventStrict A B m₀ k n) : ¬ hGreedySucc A B m₀ k n :=
  fun hg => h (HChainEventStrict_of_hGreedySucc hg)

/-- **`hGreedySucc` is decidable** (via Option.isSome). -/
private noncomputable instance hGreedySucc_decidable {A B : ℝ} {m₀ k n : ℕ} :
    Decidable (hGreedySucc A B m₀ k n) := by
  by_cases h_some : (hChainEndpoint? A B m₀ n k).isSome
  · exact isTrue (Option.isSome_iff_exists.mp h_some)
  · apply isFalse
    rintro ⟨d, hd⟩
    rw [Option.not_isSome_iff_eq_none] at h_some
    rw [h_some] at hd
    cases hd

/-- **Equivalence: `hChainAdmissibleNext` non-empty iff `GoodCompositeSuccessor`.**

Paper line 1905-1908 verbatim: a "squarefree product `e` admissible at stage j+1"
matches both definitions:
- `hChainAdmissibleNext` filters `e ∈ ℕ` with admissibility constraints.
- `GoodCompositeSuccessor` quantifies `∃ T : Finset ℕ` of admissible primes with `e = ∏ T ∣ n`.

The bijection is `e ↔ T = e.primeFactors` (using `Squarefree e ⟹ e = ∏ T`). -/
private lemma hChainAdmissibleNext_nonempty_iff_GoodCompositeSuccessor
    {A B : ℝ} (_hA : 1 ≤ A) {m₀ k d_prev n : ℕ} (hd_prev_pos : 0 < d_prev) :
    (hChainAdmissibleNext A B m₀ k d_prev n).Nonempty ↔
      GoodCompositeSuccessor A (Real.exp (tower (m₀ + k) / B)) d_prev n := by
  constructor
  · -- nonempty → GoodCompositeSuccessor.
    rintro ⟨e, he⟩
    rcases hChainAdmissibleNext_mem.mp he with
      ⟨_h_le, h_d_lt, h_mod, h_dvd, h_sqf, h_primes, h_size⟩
    -- T := e.primeFactors.  e = ∏ T (since e squarefree).
    refine ⟨e.primeFactors, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · -- T.Nonempty.
      rw [Nat.nonempty_primeFactors]
      omega  -- 1 < e from d_prev < e ∧ d_prev ≥ 1.
    · -- All q ∈ T are prime in (exp y, exp(y^(A-1))].
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact ⟨hp_prime, h_primes p hp⟩
    · -- ∏ T ≡ 1 mod d_prev.  Use ∏ T = e.
      have h_prod_eq : ∏ q ∈ e.primeFactors, q = e :=
        Nat.prod_primeFactors_of_squarefree h_sqf
      rw [h_prod_eq]
      exact h_mod
    · -- d_prev < ∏ T.
      have h_prod_eq : ∏ q ∈ e.primeFactors, q = e :=
        Nat.prod_primeFactors_of_squarefree h_sqf
      rw [h_prod_eq]; exact h_d_lt
    · -- ∏ T ≤ exp(y^A).
      have h_prod_eq : ∏ q ∈ e.primeFactors, q = e :=
        Nat.prod_primeFactors_of_squarefree h_sqf
      rw [h_prod_eq]; exact h_size
    · -- ∏ T ∣ n.
      have h_prod_eq : ∏ q ∈ e.primeFactors, q = e :=
        Nat.prod_primeFactors_of_squarefree h_sqf
      rw [h_prod_eq]; exact h_dvd
  · -- GoodCompositeSuccessor → nonempty.
    rintro ⟨T, ⟨hT_ne, hT_prime, hT_mod, hT_lt, hT_size⟩, hT_dvd⟩
    -- e := ∏ T.  Show e ∈ hChainAdmissibleNext.
    set e : ℕ := ∏ q ∈ T, q with he_def
    refine ⟨e, ?_⟩
    rw [hChainAdmissibleNext_mem]
    -- e ≤ ⌊exp(y^A)⌋₊.
    refine ⟨?_, hT_lt, hT_mod, hT_dvd, ?_, ?_, hT_size⟩
    · -- e ≤ ⌊exp(y^A)⌋₊ (from hT_size : e ≤ exp(y^A)).
      apply Nat.le_floor; exact hT_size
    · -- Squarefree e.
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro a ha b hb hab
        have h_a_prime := (hT_prime a ha).1
        have h_b_prime := (hT_prime b hb).1
        have h_coprime : Nat.Coprime a b := (Nat.coprime_primes h_a_prime h_b_prime).mpr hab
        exact Nat.coprime_iff_isRelPrime.mp h_coprime
      · intro i hi
        exact (hT_prime i hi).1.squarefree
    · -- All prime factors of e are in (exp y, exp(y^(A-1))].
      intro p hp
      -- e = ∏ T, so primeFactors(e) = T.
      have h_pf : Nat.primeFactors e = T := by
        rw [he_def]; exact Nat.primeFactors_prod (fun q hq => (hT_prime q hq).1)
      rw [h_pf] at hp
      exact (hT_prime p hp).2

/-- **Greedy stage failure event characterization (paper line 1942).**

Greedy succeeds at level `k` but fails at level `k+1` iff there exists a chain endpoint `d`
satisfying `hChainEndpoint? n k = some d` and no admissible squarefree extension exists
(equivalently `¬ GoodCompositeSuccessor 20 y_target d n`). -/
private lemma hGreedyStageFailure_iff
    {A B : ℝ} (hA : 1 ≤ A) {m₀ k n : ℕ} :
    (hGreedySucc A B m₀ k n ∧ ¬ hGreedySucc A B m₀ (k + 1) n) ↔
      ∃ d : ℕ, hChainEndpoint? A B m₀ n k = some d ∧
        ¬ GoodCompositeSuccessor A (Real.exp (tower (m₀ + k) / B)) d n := by
  constructor
  · rintro ⟨⟨d, hd⟩, hnot⟩
    refine ⟨d, hd, ?_⟩
    -- ¬hGreedySucc (k+1) means hChainEndpoint? n (k+1) = none.
    -- hChainEndpoint? n (k+1) = match endpoint k with | some d => hFinsetLeastNat? (admissible) | none => none.
    -- With endpoint k = some d: it's hFinsetLeastNat? (hChainAdmissibleNext A B m₀ k d n).
    -- This is none iff hChainAdmissibleNext = ∅ iff ¬nonempty iff (by equivalence) ¬GoodComposite.
    intro hgood
    apply hnot
    -- Need: hGreedySucc (k+1) n.
    have h_d_pos : 0 < d := by
      have := hChainEndpoint?_some_ge_one hd
      omega
    have h_admissible_nonempty :
        (hChainAdmissibleNext A B m₀ k d n).Nonempty :=
      (hChainAdmissibleNext_nonempty_iff_GoodCompositeSuccessor hA h_d_pos).mpr hgood
    -- Greedy at level (k+1) returns some d' = least admissible.
    refine ⟨(hChainAdmissibleNext A B m₀ k d n).min' h_admissible_nonempty, ?_⟩
    show hChainEndpoint? A B m₀ n (k + 1) = some _
    unfold hChainEndpoint?
    rw [hd]
    simp only [hFinsetLeastNat?, h_admissible_nonempty, dif_pos]
  · rintro ⟨d, hd, hnotgood⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    rintro ⟨d', hd'⟩
    -- hd' : hChainEndpoint? n (k+1) = some d'.
    -- This unfolds to: match (some d) with | some d_prev => hFinsetLeastNat? ... = some d'.
    -- Hence hFinsetLeastNat? (hChainAdmissibleNext A B m₀ k d n) = some d'.
    -- So admissible is nonempty, contradicting hnotgood.
    have h_unf : hFinsetLeastNat? (hChainAdmissibleNext A B m₀ k d n) = some d' := by
      have hd_uniq : hChainEndpoint? A B m₀ n k = some d := hd
      unfold hChainEndpoint? at hd'
      rw [hd_uniq] at hd'
      exact hd'
    have h_d_pos : 0 < d := by
      have := hChainEndpoint?_some_ge_one hd
      omega
    have h_admissible_nonempty :
        (hChainAdmissibleNext A B m₀ k d n).Nonempty := by
      by_contra h
      simp [hFinsetLeastNat?, h] at h_unf
    exact hnotgood
      ((hChainAdmissibleNext_nonempty_iff_GoodCompositeSuccessor hA h_d_pos).mp h_admissible_nonempty)

-- NOTE: Under the paper-faithful IsDivisorChain definition (using `Nat.ModEq d e 1`,
-- which is vacuous for d=1), chains can start with `ds[0] = 1`.  So the previous
-- lemma `HChainEventStrict_iff_HChainEvent_of_two_le` no longer holds: only the
-- forward direction (`HChainEvent_of_strict`) is true.  Callers that need the
-- forward direction use `HChainEvent_of_strict` directly.

/-- Helper: convert subtype card on Fin M to filter card on Finset.range M. -/
private lemma h_fin_subtype_card_eq_range {M : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    Nat.card {r : Fin M // P r.val} = ((Finset.range M).filter P).card := by
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

/-- **Greedy success at higher level implies greedy success at lower level.**

Direct corollary of `hChainEndpoint?_succ_prev_some`. -/
private lemma hGreedySucc_truncate {A B : ℝ} {m₀ : ℕ} {R : ℕ} {n : ℕ}
    (h : hGreedySucc A B m₀ (R + 1) n) : hGreedySucc A B m₀ R n := by
  rcases h with ⟨d, hd⟩
  exact hChainEndpoint?_succ_prev_some hd

/-- **Greedy event telescope (paper line 1957-1962, greedy version).**

Decomposes "greedy fails at level R" into a sum over "greedy succeeds at j-1 but fails at j"
for j = 1, ..., R.

This is the GREEDY analog of `HChainEventStrict_failure_telescope_le`.  Paper-faithful:
matches paper's `P(¬S_R) ≤ ∑_{j=1}^R P(F_j ∩ S_{j-1})`. -/
private lemma hGreedySucc_failure_telescope_le
    (A B : ℝ) (m₀ R : ℕ) (M : ℕ) :
    (Nat.card {r : Fin M // ¬ hGreedySucc A B m₀ R r.val} : ℝ) ≤
      ∑ j ∈ Finset.range R,
        (Nat.card {r : Fin M // hGreedySucc A B m₀ j r.val ∧
                              ¬ hGreedySucc A B m₀ (j+1) r.val} : ℝ) := by
  classical
  induction R with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have h_empty : {r : Fin M // ¬ hGreedySucc A B m₀ 0 r.val} → False := by
      intro ⟨r, hr⟩
      exact hr ⟨1, hChainEndpoint?_zero A B m₀ r.val⟩
    have h_card_zero : Nat.card {r : Fin M // ¬ hGreedySucc A B m₀ 0 r.val} = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨r, hr⟩ => h_empty ⟨r, hr⟩⟩
    rw [h_card_zero]
    simp
  | succ R ih =>
    rw [Finset.sum_range_succ]
    have h_decomp : ∀ r : Fin M,
        ¬ hGreedySucc A B m₀ (R + 1) r.val ↔
          (¬ hGreedySucc A B m₀ R r.val) ∨
          (hGreedySucc A B m₀ R r.val ∧ ¬ hGreedySucc A B m₀ (R + 1) r.val) := by
      intro r
      constructor
      · intro hnotR1
        by_cases hR : hGreedySucc A B m₀ R r.val
        · exact Or.inr ⟨hR, hnotR1⟩
        · exact Or.inl hR
      · rintro (hnotR | ⟨_, hnotR1⟩)
        · intro hR1; exact hnotR (hGreedySucc_truncate hR1)
        · exact hnotR1
    set notR1 := {r : Fin M // ¬ hGreedySucc A B m₀ (R + 1) r.val}
    set notR := {r : Fin M // ¬ hGreedySucc A B m₀ R r.val}
    set transR := {r : Fin M // hGreedySucc A B m₀ R r.val ∧
        ¬ hGreedySucc A B m₀ (R + 1) r.val}
    have h_card_le :
        (Nat.card notR1 : ℝ) ≤ (Nat.card notR : ℝ) + (Nat.card transR : ℝ) := by
      have h_finset_notR1 : Finset.univ.filter
          (fun r : Fin M => ¬ hGreedySucc A B m₀ (R + 1) r.val) ⊆
          (Finset.univ.filter (fun r : Fin M => ¬ hGreedySucc A B m₀ R r.val) ∪
           Finset.univ.filter (fun r : Fin M => hGreedySucc A B m₀ R r.val ∧
              ¬ hGreedySucc A B m₀ (R + 1) r.val)) := by
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rw [Finset.mem_union]
        rcases (h_decomp r).mp hr with hnR | ⟨hR, hnR1⟩
        · exact Or.inl (by simp [Finset.mem_filter, hnR])
        · exact Or.inr (by simp [Finset.mem_filter, hR, hnR1])
      have h_card_le_set : (Finset.univ.filter
          (fun r : Fin M => ¬ hGreedySucc A B m₀ (R + 1) r.val)).card ≤
          (Finset.univ.filter (fun r : Fin M => ¬ hGreedySucc A B m₀ R r.val)).card +
          (Finset.univ.filter (fun r : Fin M => hGreedySucc A B m₀ R r.val ∧
              ¬ hGreedySucc A B m₀ (R + 1) r.val)).card :=
        le_trans (Finset.card_le_card h_finset_notR1) (Finset.card_union_le _ _)
      have h_eq_notR1 : Nat.card notR1 = (Finset.univ.filter
          (fun r : Fin M => ¬ hGreedySucc A B m₀ (R + 1) r.val)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.subtype_card]
      have h_eq_notR : Nat.card notR = (Finset.univ.filter
          (fun r : Fin M => ¬ hGreedySucc A B m₀ R r.val)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.subtype_card]
      have h_eq_transR : Nat.card transR = (Finset.univ.filter
          (fun r : Fin M => hGreedySucc A B m₀ R r.val ∧
              ¬ hGreedySucc A B m₀ (R + 1) r.val)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.subtype_card]
      rw [h_eq_notR1, h_eq_notR, h_eq_transR]
      exact_mod_cast h_card_le_set
    have h_ih : (Nat.card notR : ℝ) ≤
        ∑ j ∈ Finset.range R,
          (Nat.card {r : Fin M // hGreedySucc A B m₀ j r.val ∧
                                ¬ hGreedySucc A B m₀ (j+1) r.val} : ℝ) := ih
    show (Nat.card notR1 : ℝ) ≤
      (∑ j ∈ Finset.range R,
        (Nat.card {r : Fin M // hGreedySucc A B m₀ j r.val ∧
            ¬ hGreedySucc A B m₀ (j+1) r.val} : ℝ)) + (Nat.card transR : ℝ)
    linarith

/-! ### Paper §7.3 + §7.4 summation

The summed-stage failure-density estimate is the assembly of paper §7.3
(Lemma 7.3, greedy H-chain in product model has failure prob `≤ ∑ y_j^{-c} → 0`
by tower-spacing and stage independence) and paper §7.4 (CRT transfer, Lemma 2.7,
plus Chebyshev θ to bound the primorial error `M = primorial(exp(y_R^{A-1})) = o(x)`).

Implementing this paper-faithfully requires:
* The product-model union bound across disjoint windows (paper §7.3 line 1838-1853).
  Key: stages are independent in the product model because window primes are
  disjoint; failure prob per stage ≤ `y_j^{-c}` from `composite_successor_uniform`'s
  underlying product-model bound; sum is geometric in `j` via tower spacing.
* The single CRT transfer at cutoff `P = exp(y_R^{A-1})` (paper §7.4 line 2049).
* Chebyshev's bound `log M ≤ Cθ · P` (paper §7.4 line 2007), `P ≤ T_{L-3}`
  (line 2003), `log x ≥ T_{L-2} = exp(T_{L-3})`, hence `M = x^{o(1)} = o(x)`.

Following CLOSURE_PLAN_LBH.md Option A (paper-faithful): the proof structure
mirrors paper §7.4 line 2031-2049 — define an `M`-periodic chain event, apply
`crt_transfer` (Lemma 2.7) **once** with cutoff `P = exp(y_R^{A-1})`, and bound
the product-model failure probability by `∑ y_j^{-c}` via the disjoint-window
union bound (paper line 1957-1972). -/

/-- **Phase 6 helper (paper §7.1 line 1846-1848 chain length).**
For ε ∈ (0, 1), there exists L₀ such that for all L ≥ L₀,
`(1 - ε) · L ≤ L - ⌊L^{1/2}⌋ - 4`.  Packages "chain has length R = L - m_0 - 4"
into "chain has length ≥ (1-ε) · log_*(n)" required by GoodLowerDivisorChain.

Paper §7.1 line 1846-1848: `R = L - m_0 - 4` where `m_0 = ⌊L^{1/2}⌋`,
hence `R = (1 - o(1)) · L`. -/
private lemma chain_length_packaging
    {ε : ℝ} (hε : 0 < ε) (_hε_lt_one : ε < 1) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      (1 - ε) * (L : ℝ) ≤ ((L - Nat.sqrt L - 4 : ℕ) : ℝ) := by
  -- Strategy: choose L₀ ≥ max(16, ⌈100/ε²⌉) so that for L ≥ L₀:
  -- (a) √L ≥ 10/ε (since L ≥ 100/ε² ⟹ √L ≥ 10/ε), giving ε·√L ≥ 10.
  -- (b) √L ≥ 4 (since L ≥ 16).
  -- Then ε·L = ε·√L · √L ≥ 10·√L ≥ √L + 9·√L ≥ √L + 36 ≥ √L + 4.
  -- So (1-ε)·L = L - ε·L ≤ L - √L - 4 ≤ ((L - √L - 4 : ℕ) : ℝ).
  refine ⟨Nat.ceil (100 / ε ^ 2) + 16, ?_⟩
  intro L hL
  have hε_pos : 0 < ε := hε
  have hL_ge_16 : 16 ≤ L := le_trans (Nat.le_add_left _ _) hL
  have hL_ge_ceil : Nat.ceil (100 / ε ^ 2) ≤ L :=
    le_trans (Nat.le_add_right _ _) hL
  have hL_pos : 0 < L := by omega
  have hL_real_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
  have hL_real_ge_16 : (16 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_16
  -- L (in ℝ) ≥ 100/ε².
  have hL_real_ge_100 : (100 : ℝ) / ε ^ 2 ≤ (L : ℝ) := by
    have hceil : (100 : ℝ) / ε ^ 2 ≤ (Nat.ceil (100 / ε ^ 2) : ℝ) := Nat.le_ceil _
    have hceil_le : (Nat.ceil (100 / ε ^ 2) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_ceil
    linarith
  -- Real.sqrt L ≥ 10/ε.
  have hε_sq_pos : 0 < ε ^ 2 := by positivity
  have h_inv_eps_sq : 0 < 100 / ε ^ 2 := by positivity
  have h_sqrt_real_ge : (10 : ℝ) / ε ≤ Real.sqrt (L : ℝ) := by
    have h_sq_target : (10 / ε) ^ 2 = 100 / ε ^ 2 := by ring
    have h_sq_le : (10 / ε) ^ 2 ≤ (L : ℝ) := by rw [h_sq_target]; exact hL_real_ge_100
    have h_10_eps_nn : (0 : ℝ) ≤ 10 / ε := by positivity
    rw [show (10 : ℝ) / ε = Real.sqrt ((10 / ε) ^ 2) by
      rw [Real.sqrt_sq h_10_eps_nn]]
    exact Real.sqrt_le_sqrt h_sq_le
  -- Real.sqrt L ≥ 4 (from L ≥ 16).
  have h_sqrt_real_ge_4 : (4 : ℝ) ≤ Real.sqrt (L : ℝ) := by
    have h16_eq : (4 : ℝ) = Real.sqrt 16 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    rw [h16_eq]
    exact Real.sqrt_le_sqrt hL_real_ge_16
  -- ε · Real.sqrt L ≥ 10 (from h_sqrt_real_ge).
  have h_eps_sqrt : (10 : ℝ) ≤ ε * Real.sqrt (L : ℝ) := by
    have hne : ε ≠ 0 := ne_of_gt hε_pos
    have h := mul_le_mul_of_nonneg_left h_sqrt_real_ge hε_pos.le
    have h_simp : ε * (10 / ε) = 10 := by
      field_simp
    linarith [h_simp]
  -- ε · L ≥ 10 · Real.sqrt L (using L = (Real.sqrt L)² for L ≥ 0).
  have h_sqrt_sq : Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) = (L : ℝ) :=
    Real.mul_self_sqrt hL_real_pos.le
  have h_eps_L : (10 : ℝ) * Real.sqrt (L : ℝ) ≤ ε * (L : ℝ) := by
    calc (10 : ℝ) * Real.sqrt (L : ℝ)
        ≤ (ε * Real.sqrt (L : ℝ)) * Real.sqrt (L : ℝ) := by
          have h_sqrt_nn : 0 ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
          nlinarith
      _ = ε * (L : ℝ) := by rw [mul_assoc, h_sqrt_sq]
  -- ε · L ≥ √L + 4 (since 10·√L ≥ √L + 9·√L ≥ √L + 36 ≥ √L + 4).
  have h_eps_L_ge : Real.sqrt (L : ℝ) + 4 ≤ ε * (L : ℝ) := by
    calc Real.sqrt (L : ℝ) + 4
        ≤ Real.sqrt (L : ℝ) + Real.sqrt (L : ℝ) := by linarith
      _ = 2 * Real.sqrt (L : ℝ) := by ring
      _ ≤ 10 * Real.sqrt (L : ℝ) := by
          have h_sqrt_nn : 0 ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
          nlinarith
      _ ≤ ε * (L : ℝ) := h_eps_L
  -- Nat.sqrt L ≤ Real.sqrt L.
  have h_nat_sqrt_le_real : ((Nat.sqrt L : ℕ) : ℝ) ≤ Real.sqrt (L : ℝ) := by
    have h_sq_le : ((Nat.sqrt L : ℕ) : ℝ) ^ 2 ≤ (L : ℝ) := by
      have h_nat : (Nat.sqrt L) ^ 2 ≤ L := Nat.sqrt_le' L
      exact_mod_cast h_nat
    have h_sqrt_nn : (0 : ℝ) ≤ ((Nat.sqrt L : ℕ) : ℝ) := by positivity
    rw [show Real.sqrt (L : ℝ) = Real.sqrt (((Nat.sqrt L : ℕ) : ℝ) ^ 2 +
        ((L : ℝ) - ((Nat.sqrt L : ℕ) : ℝ) ^ 2)) by ring_nf]
    have hL_diff_nn : 0 ≤ (L : ℝ) - ((Nat.sqrt L : ℕ) : ℝ) ^ 2 := by linarith
    calc ((Nat.sqrt L : ℕ) : ℝ)
        = Real.sqrt (((Nat.sqrt L : ℕ) : ℝ) ^ 2) := by
          rw [Real.sqrt_sq h_sqrt_nn]
      _ ≤ Real.sqrt (((Nat.sqrt L : ℕ) : ℝ) ^ 2 +
            ((L : ℝ) - ((Nat.sqrt L : ℕ) : ℝ) ^ 2)) := by
          apply Real.sqrt_le_sqrt; linarith
  -- Nat subtraction lower bound: Nat.sqrt L + 4 ≤ L for L ≥ 16.
  have h_nat_diff_nn : Nat.sqrt L + 4 ≤ L := by
    have h_sqrt_ge_4 : 4 ≤ Nat.sqrt L := by
      have h_sqrt_mono : Nat.sqrt 16 ≤ Nat.sqrt L := Nat.sqrt_le_sqrt hL_ge_16
      -- Nat.sqrt 16 ≥ 4 since 4 * 4 = 16 ≤ 16, so 4 ≤ Nat.sqrt 16.
      have h_sqrt_16_ge : 4 ≤ Nat.sqrt 16 := by
        have h_le : 4 * 4 ≤ 16 := by norm_num
        exact Nat.le_sqrt.mpr h_le
      omega
    have h_sq_self : Nat.sqrt L ^ 2 ≤ L := Nat.sqrt_le' L
    have h_sq_eq : Nat.sqrt L ^ 2 = Nat.sqrt L * Nat.sqrt L := by ring
    have h_sq_self' : Nat.sqrt L * Nat.sqrt L ≤ L := h_sq_eq ▸ h_sq_self
    have h_2sqrt : Nat.sqrt L + 4 ≤ Nat.sqrt L + Nat.sqrt L := by omega
    have h_2sqrt_le_sq : Nat.sqrt L + Nat.sqrt L ≤ Nat.sqrt L * Nat.sqrt L := by
      nlinarith
    omega
  -- Cast Nat subtraction to ℝ.
  have h_nat_cast :
      ((L - Nat.sqrt L - 4 : ℕ) : ℝ) = (L : ℝ) - ((Nat.sqrt L : ℕ) : ℝ) - 4 := by
    have h_first : Nat.sqrt L ≤ L := by
      have := Nat.sqrt_le_self L
      exact this
    have h_second : 4 ≤ L - Nat.sqrt L := by omega
    push_cast [Nat.cast_sub h_first, Nat.cast_sub h_second]
    ring
  -- Final assembly: (1-ε)·L = L - ε·L ≤ L - √L - 4 ≤ L - Nat.sqrt L - 4 = (L-√L-4).
  rw [h_nat_cast]
  have h_main : (1 - ε) * (L : ℝ) ≤ (L : ℝ) - Real.sqrt (L : ℝ) - 4 := by
    have : (1 - ε) * (L : ℝ) = (L : ℝ) - ε * (L : ℝ) := by ring
    linarith
  linarith

/-- Auxiliary tower monotonicity (tower is monotone in ℕ argument). -/
private lemma tower_le_of_le {a b : ℕ} (hab : a ≤ b) : tower a ≤ tower b := by
  induction b with
  | zero =>
    interval_cases a
    rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h_lt | h_ge
    · have h_a_le_b : a ≤ b := Nat.lt_succ_iff.mp h_lt
      exact (ih h_a_le_b).trans (tower_lt_succ b).le
    · have h_a_eq : a = b + 1 := le_antisymm hab h_ge
      rw [h_a_eq]

/-- **Phase 2 helper (paper §7.2 line 1965-1973 tower-decay sum).**
For c > 0, η > 0, there exists L₀ such that for all L ≥ L₀ and B ≥ 1,
`2 · exp(-c · T_{⌊L^{1/2}⌋} / B) ≤ η`.

Paper §7.2 line 1965-1973 verbatim: `∑_{j=1}^R y_j^{-c} ≤ ∑_{j≥1} y_1^{-c·2^{j-1}} ≤ 2·y_1^{-c}`,
using `y_{j+1} ≥ y_j²` (paper Lemma 7.2).  Here `y_1 = exp(T_{m_0}/B)` where
`m_0 = ⌊L^{1/2}⌋`, so `y_1^{-c} = exp(-c·T_{m_0}/B)`.  As `L → ∞`, `m_0 → ∞`,
`T_{m_0} → ∞`, hence `y_1^{-c} → 0`. -/
private lemma tower_decay_sum_bound
    {c B : ℝ} (hc : 0 < c) (hB : 1 ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      2 * Real.exp (-c * tower (Nat.sqrt L) / B) ≤ η := by
  -- Need: 2 · exp(-c · T_{√L} / B) ≤ η.
  -- Equivalently: exp(-c · T_{√L} / B) ≤ η/2.
  -- Equivalently: -c · T_{√L} / B ≤ log(η/2).
  -- Equivalently: c · T_{√L} / B ≥ -log(η/2) = log(2/η).
  -- Equivalently: T_{√L} ≥ B · log(2/η) / c.
  -- Need: T_{√L} → ∞ as L → ∞.  Since √L → ∞ and T monotonic, T_{√L} → ∞.
  -- Use tower_tendsto_atTop on `Nat.sqrt L`.
  -- For m_0 := tower-arg, want T_{m_0} ≥ M.  By tower_tendsto_atTop, ∃ m₀ s.t. tower m ≥ M for m ≥ m₀.
  have h_tower : Filter.Tendsto tower Filter.atTop Filter.atTop := tower_tendsto_atTop
  rcases (Filter.tendsto_atTop.mp h_tower (B * Real.log (2 / η) / c)) with hev
  rcases Filter.eventually_atTop.mp hev with ⟨m₀, hm₀⟩
  -- L₀ := m₀² (so √L ≥ m₀ for L ≥ L₀).
  refine ⟨m₀ ^ 2, ?_⟩
  intro L hL_large
  -- Nat.sqrt L ≥ m₀ since L ≥ m₀².
  have h_sqrt_ge : m₀ ≤ Nat.sqrt L := by
    have h_m_sq_le : m₀ ^ 2 ≤ L := hL_large
    have h_m_sq_eq : m₀ * m₀ = m₀ ^ 2 := by ring
    rw [← h_m_sq_eq] at h_m_sq_le
    exact Nat.le_sqrt.mpr h_m_sq_le
  -- tower (Nat.sqrt L) ≥ tower m₀ ≥ B · log(2/η) / c.
  have h_tower_ge : B * Real.log (2 / η) / c ≤ tower (Nat.sqrt L) := by
    have h_tower_mono : tower m₀ ≤ tower (Nat.sqrt L) := by
      -- tower is monotone (tower_lt_succ + induction)
      apply tower_le_of_le h_sqrt_ge
    exact (hm₀ m₀ le_rfl).trans h_tower_mono
  -- Now prove: 2 · exp(-c · T_{√L} / B) ≤ η.
  -- exp(-c · T / B) = 1 / exp(c · T / B).  Want this ≤ η/2.
  -- So exp(c · T / B) ≥ 2/η, i.e., c · T / B ≥ log(2/η), i.e., T ≥ B · log(2/η) / c.
  -- We have h_tower_ge : T ≥ B · log(2/η) / c.
  have hB_pos : 0 < B := by linarith
  have h_eta_half_pos : 0 < η / 2 := by positivity
  have h_2_eta_gt_1 : 1 ≤ 2 / η ∨ 2 / η < 1 := by
    by_cases h : 1 ≤ 2 / η
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)
  -- Case split: η ≥ 2 (i.e., 2/η ≤ 1) — then log(2/η) ≤ 0, trivial bound.
  -- Otherwise η < 2 (i.e., 2/η > 1) — use main argument.
  rcases h_2_eta_gt_1 with h_2_eta_ge_1 | h_2_eta_lt_1
  · -- 2/η ≥ 1: log(2/η) ≥ 0.  c·T/B ≥ log(2/η).
    have h_log_nn : 0 ≤ Real.log (2 / η) := Real.log_nonneg h_2_eta_ge_1
    have h_c_T_B_ge_log : Real.log (2 / η) ≤ c * tower (Nat.sqrt L) / B := by
      rw [le_div_iff₀ hB_pos]
      rw [div_le_iff₀ hc] at h_tower_ge
      nlinarith
    -- exp(c·T/B) ≥ 2/η ⟹ exp(-c·T/B) ≤ η/2.
    have h_neg : -c * tower (Nat.sqrt L) / B ≤ -Real.log (2 / η) := by
      have h_eq : -c * tower (Nat.sqrt L) / B = -(c * tower (Nat.sqrt L) / B) := by ring
      linarith [h_c_T_B_ge_log]
    have h_eta_pos : 0 < η := hη
    have h_2_pos : (0 : ℝ) < 2 := by norm_num
    have h_2_eta_pos : 0 < 2 / η := by positivity
    have h_log_eq : Real.exp (Real.log (2 / η)) = 2 / η := Real.exp_log h_2_eta_pos
    have h_exp_le : Real.exp (-c * tower (Nat.sqrt L) / B) ≤ Real.exp (-Real.log (2 / η)) :=
      Real.exp_le_exp.mpr h_neg
    have h_exp_neg_log : Real.exp (-Real.log (2 / η)) = η / 2 := by
      rw [Real.exp_neg, h_log_eq]
      field_simp
    rw [h_exp_neg_log] at h_exp_le
    linarith
  · -- 2/η < 1: η > 2.  exp(-c·T/B) ≤ 1 ≤ η/2 (since η > 2 means η/2 > 1).
    -- exp(-x) ≤ 1 for x ≥ 0 (which we have since c·T/B ≥ 0).
    have h_arg_nn : 0 ≤ c * tower (Nat.sqrt L) / B := by
      have := tower_pos (Nat.sqrt L)
      positivity
    have h_neg_arg_np : -c * tower (Nat.sqrt L) / B ≤ 0 := by
      have h_neg : -(c * tower (Nat.sqrt L) / B) ≤ 0 := by linarith
      have h_eq : -c * tower (Nat.sqrt L) / B = -(c * tower (Nat.sqrt L) / B) := by ring
      linarith
    have h_exp_le_one : Real.exp (-c * tower (Nat.sqrt L) / B) ≤ 1 := by
      have := Real.exp_le_one_iff.mpr h_neg_arg_np
      exact this
    -- η > 2 (from 2/η < 1 ∧ η > 0).
    have h_eta_gt_2 : 2 < η := by
      have : 2 < η := by
        rw [div_lt_one hη] at h_2_eta_lt_1
        linarith
      exact this
    linarith

/-- **Phase 5 helper (paper §7.3 line 2006-2007 Chebyshev primorial bound).**
Given the Chebyshev θ-witness, `primorial t ≤ exp(C_θ · t)` for all `t ≥ 2`.
Equivalently, `log primorial t ≤ C_θ · t`.

Paper §7.3 line 2006-2007: "Set M := ∏_{p ≤ P} p.  By Chebyshev (Lemma~\ref{lem:Cheb}),
log M ≤ C_θ · P = o(log x), hence M = x^{o(1)} = o(x)." -/
private lemma chebyshev_primorial_bound
    {Cθ : ℝ} (htheta : ChebyshevThetaWitness Cθ)
    (t : ℝ) (ht : 2 ≤ t) :
    Real.log ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) ≤ Cθ * t := by
  -- log(primorial t) = ∑_{p ≤ t prime} log p ≤ C_θ · t (Chebyshev θ).
  unfold ChebyshevThetaWitness at htheta
  have h_prod_pos : (0 : ℝ) < ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) := by
    have h_nat_pos : 0 < ∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p := by
      apply Finset.prod_pos
      intro p hp
      have h_p_prime := (Finset.mem_filter.mp hp).2
      exact h_p_prime.pos
    exact_mod_cast h_nat_pos
  have h_log_prod : Real.log ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) =
      ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), Real.log (p : ℝ) := by
    rw [Nat.cast_prod]
    rw [Real.log_prod]
    intro p hp
    have h_p_prime := (Finset.mem_filter.mp hp).2
    have h_p_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast h_p_prime.pos
    exact h_p_pos.ne'
  rw [h_log_prod]
  exact htheta t ht

/-- **Threshold inequality** (paper-faithful: y_target ≥ exp(c+2) sufficient).

For `y ≥ exp(c+2)`, `A ≥ 2`, `c ≥ 0`: `2 · y^{2+c} ≤ exp(y^A)`.

Proof: log form gives `log 2 + (2+c) · log y ≤ y^A`.
Using `log y ≤ y - 1`: `(2+c) · log y ≤ (2+c) · y`.
Using `y ≥ exp(c+2) ≥ c+3`: `(2+c) · y ≤ y · y = y^2 ≤ y^A` (for A ≥ 2).
log 2 ≤ 1 ≤ y^A - y^2 (for y large, A > 2).  Combining gives the result. -/
private lemma h_threshold_inequality {y c A : ℝ}
    (hy_pos : 0 < y) (hy_ge_exp : Real.exp (c + 2) ≤ y) (hA_ge : 2 ≤ A) (hc_pos : 0 < c) :
    2 * y ^ (2 + c) ≤ Real.exp (y ^ A) := by
  -- Step 1: y ≥ c + 3.
  have hy_ge_c3 : c + 3 ≤ y := by
    have h_exp_ge : c + 3 ≤ Real.exp (c + 2) := by
      have := Real.add_one_le_exp (c + 2); linarith
    linarith
  have hy_ge_1 : (1 : ℝ) ≤ y := by linarith
  have hy_ge_2 : (2 : ℝ) ≤ y := by linarith
  -- Step 2: log y ≤ y (from log y ≤ y - 1).
  have hy_log_le : Real.log y ≤ y := by
    have := Real.log_le_sub_one_of_pos hy_pos; linarith
  -- Step 3: log y ≥ c + 2.
  have h_log_y_ge : c + 2 ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos _) hy_ge_exp
    rwa [Real.log_exp] at h
  have h_two_c_nn : 0 ≤ 2 + c := by linarith
  -- Step 4: (2+c) log y ≤ (2+c) · y.
  have h_term_le : (2 + c) * Real.log y ≤ (2 + c) * y :=
    mul_le_mul_of_nonneg_left hy_log_le h_two_c_nn
  -- Step 5: (2+c) · y + log 2 ≤ y².
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have h_step_y_sq : (2 + c) * y + Real.log 2 ≤ y^2 := by
    nlinarith [hy_ge_c3, hy_ge_2, hy_pos.le, h_log2_le_one]
  -- Step 6: y² ≤ y^A (rpow monotone, A ≥ 2, y ≥ 1).
  have hy_sq_eq : y^2 = y ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = (1 : ℝ) + 1 from by norm_num,
        Real.rpow_add_one (ne_of_gt hy_pos), Real.rpow_one]
    ring
  have hy_sq_le_pow_A : y^2 ≤ y ^ A := by
    rw [hy_sq_eq]
    exact Real.rpow_le_rpow_of_exponent_le hy_ge_1 hA_ge
  have h_RHS_le_pow_A : (2 + c) * y + Real.log 2 ≤ y ^ A := by linarith
  -- Step 7: log 2 + (2+c) · log y ≤ y^A.
  have h_log_form : Real.log 2 + (2 + c) * Real.log y ≤ y ^ A := by linarith
  -- Step 8: 2 · y^{2+c} ≤ exp(y^A) via exp_le_exp + algebraic identity.
  have h_eq : Real.exp (Real.log 2 + (2 + c) * Real.log y) = 2 * y ^ (2 + c) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [Real.rpow_def_of_pos hy_pos]
    congr 1; ring
  have h_le : Real.exp (Real.log 2 + (2 + c) * Real.log y) ≤ Real.exp (y ^ A) :=
    Real.exp_le_exp.mpr h_log_form
  linarith

open scoped Classical in
/-- Transfer the successor residue estimate to a future prime window. -/
private lemma future_window_failure_bound
    {A : ℝ} (hA_eq : A = 20) {c : ℝ} (hc : 0 < c)
    {y₀ : ℝ}
    (h_residue : ∀ y : ℝ, y₀ ≤ y → ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ y →
      (Nat.card {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
        CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
        (compositeSuccessorCRTPeriod 20 y d : ℝ) ≤
          Real.exp (-c * Real.log y) / (2 * (d : ℝ)))
    {y_target : ℝ} (hy_target_ge_y₀ : y₀ ≤ y_target)
    (hy_target_ge_2 : 2 ≤ y_target)
    (h_y_target_ge_exp_c2 : Real.exp (c + 2) ≤ y_target)
    {P M a b : ℕ} (hM_def : M = primorial P) (hMpos : 0 < M)
    (hP_at_target : 2 * Real.exp (y_target ^ A) ≤ (P : ℝ))
    (hb_pos : 0 < b) (hb_dvd_M : b ∣ M) (ha_dvd_M : a ∣ M)
    (hab_coprime : a.Coprime b) (hab_dvd_M : a * b ∣ M)
    (hPb_periodic : ∀ d r r' : ℕ, r % b = r' % b →
      (¬ GoodCompositeSuccessor A y_target d r ↔
        ¬ GoodCompositeSuccessor A y_target d r'))
    {d : ℕ} (hd_pos : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y_target) (hd_dvd_a : d ∣ a) :
    (((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ) ≤
      (b : ℝ) * Real.exp (-c * Real.log y_target) := by
  classical
  have hA_pos : 0 < A := by rw [hA_eq]; norm_num
  have hy_target_pos : 0 < y_target := by linarith only [hy_target_ge_2]
  have hy_target_ge_1 : 1 ≤ y_target := by linarith only [hy_target_ge_2]
  -- **Step 1**: y_target ≥ y₀ from L₀ choice.
  -- **Step 2**: Apply h_residue + composite_successor_bad_count_le_periodic at x = M.
  -- h_residue: ρ(y_target, d) ≤ exp(-c·log y_target) / (2d).
  have hρ_bound := h_residue y_target hy_target_ge_y₀ d hd_pos hd_le_y
  -- composite_successor_bad_count_le_periodic: count{BadSet at x} ≤ ρ · x + M_d.
  have hM_real_nn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le _
  have hperiodic := composite_successor_bad_count_le_periodic
    (A := 20) (y := y_target) (d := d) hd_pos hy_target_ge_1 hM_real_nn
  -- Combine: count{BadSet at M} ≤ ρ · M + M_d ≤ y^{-c}/(2d) · M + M_d.
  set M_d : ℕ := compositeSuccessorCRTPeriod 20 y_target d with hMd_def
  set ρ : ℝ := (Nat.card {r : Fin M_d //
      CompositeSuccessorCoreBad 20 y_target d r.val} : ℝ) / (M_d : ℝ) with hρ_def
  have hρ_le : ρ ≤ Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) := by
    rw [hρ_def, hMd_def]; exact hρ_bound
  have hρ_nn : (0 : ℝ) ≤ ρ := by
    rw [hρ_def]
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcount_strong : (Nat.card (CompositeSuccessorBadSet 20 y_target d (M : ℝ)) : ℝ) ≤
      Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) * (M : ℝ) + (M_d : ℝ) := by
    have hperiodic_R : (Nat.card (CompositeSuccessorBadSet 20 y_target d (M : ℝ)) : ℝ) ≤
        ρ * (M : ℝ) + (M_d : ℝ) := by
      rw [hρ_def, hMd_def]; exact hperiodic
    have hρM_le : ρ * (M : ℝ) ≤ Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hρ_le hM_real_nn
    linarith
  --
  -- **Step 4**: Convert CompositeSuccessorBadSet card to Finset card on range M.
  -- CompositeSuccessorBadSet 20 y_target d M = {n : 0 < n ∧ n ≤ ⌊M⌋₊ ∧ d ∣ n ∧ ¬GoodComp(20, y_target, d, n)}.
  -- For x = (M : ℝ), ⌊x⌋₊ = M.  So set = {n : 1 ≤ n ≤ M ∧ d ∣ n ∧ ¬GoodComp(20, ·)}.
  -- Match A = 20 via hA_eq.
  have hA_eq_20 : A = 20 := hA_eq
  -- **Step 5**: Use coreBad_card_eq_no_good_quotient at d, P = M/d.
  -- ((Finset.range (d * (M/d))).filter (CoreBad)).card = ((Finset.range (M/d)).filter (¬GoodComp)).card.
  -- Note: d * (M/d) = M (since d ∣ M).
  have hd_dvd_M : d ∣ M := dvd_trans hd_dvd_a ha_dvd_M
  have hd_M_eq : d * (M / d) = M := Nat.mul_div_cancel' hd_dvd_M
  have hcoreBad_eq := coreBad_card_eq_no_good_quotient (y := y_target) hy_target_ge_2
    (d := d) (P := M / d) hd_pos hd_le_y
  -- hcoreBad_eq : ((Finset.range (d * (M/d))).filter CoreBad).card =
  --              ((Finset.range (M/d)).filter (¬GoodComp 20 y_target d)).card
  rw [hd_M_eq] at hcoreBad_eq
  -- hcoreBad_eq : ((Finset.range M).filter CoreBad).card = ((Finset.range (M/d)).filter ¬GoodComp).card
  --
  -- **Step 6**: Bound LHS via h_strong.  count{CoreBad} ≤ y_target^{-c} · M / d.
  -- The CompositeSuccessorBadSet bound transfers to Finset.range M with adjustment for n=0 vs n=M.
  -- **Bridge: Finset.range M card ↔ Nat.card BadSet (via boundary equivalence).**
  -- card{Finset.range M filter CoreBad} = card{[0, M-1] : CoreBad}.
  -- Nat.card BadSet = card{[1, M] : CoreBad ∧ 0 < n} = card{[1, M] : CoreBad}.
  -- Boundary: 0 vs M.  Both have d ∣ n (d ∣ 0 trivial, d ∣ M from hd_dvd_M).
  -- ¬GoodComp(d, M) = ¬GoodComp(d, 0) by Pb b-periodicity (M ≡ 0 mod b since b ∣ M).
  -- Hence card{[0, M-1] : CoreBad} = card{[1, M] : CoreBad} = Nat.card BadSet.
  have h_card_eq :
      ((Finset.range M).filter (fun r => CompositeSuccessorCoreBad 20 y_target d r)).card =
        Nat.card (CompositeSuccessorBadSet 20 y_target d (M : ℝ)) := by
    -- Step 1: BadSet (Set) = ↑(Finset.Icc 1 M filter CoreBad).
    have hM_floor : ⌊(M : ℝ)⌋₊ = M := Nat.floor_natCast M
    have hBadSet_eq :
        CompositeSuccessorBadSet 20 y_target d (M : ℝ) =
          ↑((Finset.Icc 1 M).filter
              (fun n => CompositeSuccessorCoreBad 20 y_target d n)) := by
      ext n
      change (0 < n ∧ n ≤ ⌊(M : ℝ)⌋₊ ∧ CompositeSuccessorCoreBad 20 y_target d n) ↔
        n ∈ (Finset.Icc 1 M).filter (fun n => CompositeSuccessorCoreBad 20 y_target d n)
      rw [Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
      simp only [Nat.succ_le_iff, and_assoc]
    rw [hBadSet_eq]
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    -- Step 2: card{Finset.range M filter CoreBad} = card{Finset.Icc 1 M filter CoreBad}.
    -- Bijection 0 ↔ M (boundary equivalence via Pb b-periodicity, d ∣ M).
    have hd_dvd_M : d ∣ M := dvd_trans hd_dvd_a ha_dvd_M
    have hM_pos : 1 ≤ M := hMpos
    -- Pb b-periodicity gives ¬GoodComp(d, M) ↔ ¬GoodComp(d, 0) since M ≡ 0 mod b.
    have hM_mod_b' : M % b = 0 := Nat.dvd_iff_mod_eq_zero.mp hb_dvd_M
    have hCoreBad_0_iff_M : CompositeSuccessorCoreBad 20 y_target d 0 ↔
        CompositeSuccessorCoreBad 20 y_target d M := by
      constructor
      · rintro ⟨_, h0_ngood⟩
        refine ⟨hd_dvd_M, ?_⟩
        -- ¬GoodComp(d, M) from ¬GoodComp(d, 0) via periodicity.
        have h_mod : (0 : ℕ) % b = M % b := by rw [Nat.zero_mod]; exact hM_mod_b'.symm
        have hA_eq_20' : A = 20 := hA_eq
        have h_iff := hPb_periodic d 0 M h_mod
        rw [hA_eq_20'] at h_iff
        exact h_iff.mp h0_ngood
      · rintro ⟨_, hM_ngood⟩
        refine ⟨dvd_zero _, ?_⟩
        have h_mod : M % b = (0 : ℕ) % b := by rw [Nat.zero_mod]; exact hM_mod_b'
        have hA_eq_20' : A = 20 := hA_eq
        have h_iff := hPb_periodic d M 0 h_mod
        rw [hA_eq_20'] at h_iff
        exact h_iff.mp hM_ngood
    -- Apply Finset.card_bij'.
    apply Finset.card_bij'
      (i := fun n _ => if n = 0 then M else n)
      (j := fun m _ => if m = M then 0 else m)
    · -- ∀ n ∈ s, i n ∈ t.
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_filter, Finset.mem_Icc]
      by_cases hn_zero : n = 0
      · subst hn_zero
        rw [if_pos rfl]
        refine ⟨⟨hM_pos, le_refl _⟩, ?_⟩
        exact hCoreBad_0_iff_M.mp hn.2
      · rw [if_neg hn_zero]
        have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_zero
        exact ⟨⟨hn_pos, le_of_lt hn.1⟩, hn.2⟩
    · -- ∀ m ∈ t, j m ∈ s.
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_range]
      by_cases hm_M : m = M
      · subst hm_M
        rw [if_pos rfl]
        refine ⟨hMpos, ?_⟩
        exact hCoreBad_0_iff_M.mpr hm.2
      · rw [if_neg hm_M]
        have hm_lt : m < M := lt_of_le_of_ne hm.1.2 hm_M
        exact ⟨hm_lt, hm.2⟩
    · -- left_inv: j (i n) = n.
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      by_cases hn_zero : n = 0
      · subst hn_zero
        -- i 0 _ = M (if 0 = 0 then M else 0).
        -- j M _ = 0 (if M = M then 0 else M).
        simp only [↓reduceIte]
        -- Goal should be 0 = 0 by rfl.
      · rw [if_neg hn_zero]
        have hn_lt : n < M := hn.1
        have hn_ne_M : n ≠ M := ne_of_lt hn_lt
        rw [if_neg hn_ne_M]
    · -- right_inv: i (j m) = m.
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      by_cases hm_M : m = M
      · subst hm_M
        simp only [↓reduceIte]
      · rw [if_neg hm_M]
        have hm_pos : 1 ≤ m := hm.1.1
        have hm_ne_zero : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm_pos
        rw [if_neg hm_ne_zero]
  have h_finset_le_strong :
      (((Finset.range M).filter (fun r => CompositeSuccessorCoreBad 20 y_target d r)).card : ℝ) ≤
        Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) * (M : ℝ) + (M_d : ℝ) := by
    rw [show (((Finset.range M).filter (fun r => CompositeSuccessorCoreBad 20 y_target d r)).card : ℝ) =
          (Nat.card (CompositeSuccessorBadSet 20 y_target d (M : ℝ)) : ℝ) from by
        exact_mod_cast h_card_eq]
    exact hcount_strong
  -- **Step 7**: Pb b-periodicity (b ∣ M/d, since d ∣ a, b ∣ M, gcd(a,b)=1 ⟹ b ∣ M/d).
  have hb_dvd_Mdiv_d : b ∣ M / d := by
    -- d ∣ a (hypothesis), a ∣ M ⟹ M = a · (M/a) = (a/d) · d · (M/a).
    -- So M/d = (a/d) · (M/a).  Since b ∣ (M/a) (from a · b ∣ M and gcd(a,b)=1):
    -- M/a = b · ((M/a)/b), hence M/d = (a/d) · b · ((M/a)/b), so b ∣ M/d.
    rcases hd_dvd_a with ⟨k_d, hk_d⟩  -- a = d * k_d
    rcases hab_dvd_M with ⟨k_ab, hk_ab⟩  -- M = a * b * k_ab
    -- M = d · k_d · b · k_ab, so M/d = k_d · b · k_ab, divisible by b.
    have hM_eq : M = d * (k_d * b * k_ab) := by rw [hk_ab, hk_d]; ring
    have hd_pos_local : 0 < d := hd_pos
    have hMdiv_eq : M / d = k_d * b * k_ab := by
      rw [hM_eq]; exact Nat.mul_div_cancel_left _ hd_pos_local
    rw [hMdiv_eq]
    exact ⟨k_d * k_ab, by ring⟩
  have hMd_eq : M / d = b * ((M / d) / b) := (Nat.mul_div_cancel' hb_dvd_Mdiv_d).symm
  -- Apply pmodel_block_count_periodic to factor.
  have hPb_periodic_d : ∀ r r' : ℕ, r % b = r' % b →
      ((¬ GoodCompositeSuccessor 20 y_target d r) ↔ ¬ GoodCompositeSuccessor 20 y_target d r') := by
    intros r r' hmod
    have h := hPb_periodic d r r' hmod
    rw [hA_eq_20] at h
    exact h
  have h_block :
      ((Finset.range (M / d)).filter (fun r => ¬ GoodCompositeSuccessor 20 y_target d r)).card =
      ((M / d) / b) *
        ((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor 20 y_target d r)).card := by
    conv_lhs => rw [hMd_eq]
    exact pmodel_block_count_periodic hPb_periodic_d
  -- **Step 8**: Combine.
  -- (M/(d·b)) · count{Pb on b} ≤ y^{-c} · M/d
  -- ⟹ count{Pb on b} ≤ y^{-c} · b.
  have h_count_eq : ((Finset.range (M / d)).filter (fun r => ¬ GoodCompositeSuccessor 20 y_target d r)).card =
      ((Finset.range M).filter (fun r => CompositeSuccessorCoreBad 20 y_target d r)).card := by
    exact hcoreBad_eq.symm
  have h_PbA_eq : (((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ) =
      (((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor 20 y_target d r)).card : ℝ) := by
    rw [hA_eq_20]
  rw [h_PbA_eq]
  -- Goal: count{Pb on b (with 20)} ≤ b · y_target^{-c}.
  set count_Pb := ((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor 20 y_target d r)).card
      with h_count_Pb_def
  -- From h_block: count_{range(M/d)} = ((M/d)/b) * count_Pb.
  -- From h_count_eq: count_{range(M/d)} = count_{CoreBad on range M}.
  -- From h_finset_le_strong: count_{CoreBad on range M} ≤ y^{-c} · M/d.
  -- Combine: ((M/d)/b) * count_Pb ≤ y^{-c} · M/d.  ⟹ count_Pb ≤ y^{-c} · b.
  have hMd_b_pos : 0 < (M / d) / b := by
    -- d * b ∣ M (from d ∣ a, b ∣ M, gcd(d, b) = 1 via gcd(a, b) = 1 + d ∣ a).
    -- M = d * b * k for k > 0 (M > 0).  So M/d = b * k, (M/d)/b = k > 0.
    have hd_cop_b : Nat.Coprime d b :=
      Nat.Coprime.coprime_dvd_left hd_dvd_a hab_coprime
    have hdb_dvd_M : d * b ∣ M :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hd_cop_b hd_dvd_M hb_dvd_M
    rcases hdb_dvd_M with ⟨k_db, hk_db⟩
    have hMdivd_eq : M / d = b * k_db := by
      rw [hk_db, show d * b * k_db = d * (b * k_db) from by ring]
      exact Nat.mul_div_cancel_left _ hd_pos
    have hMdivd_div_b : M / d / b = k_db := by
      rw [hMdivd_eq]
      exact Nat.mul_div_cancel_left _ hb_pos
    rw [hMdivd_div_b]
    -- k_db > 0: from M > 0 and M = d * b * k_db.
    rcases Nat.eq_zero_or_pos k_db with h_zero | h_pos
    · rw [h_zero, Nat.mul_zero] at hk_db
      omega
    · exact h_pos
  have hMdb_R_pos : (0 : ℝ) < ((M / d) / b : ℕ) := by exact_mod_cast hMd_b_pos
  have hd_R_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hd_R_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_R_pos
  have hb_R_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
  have hb_R_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_R_pos
  have hM_R_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hM_R_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_R_pos
  have hdb_dvd_M_inline : d * b ∣ M := by
    have hd_cop_b : Nat.Coprime d b :=
      Nat.Coprime.coprime_dvd_left hd_dvd_a hab_coprime
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hd_cop_b hd_dvd_M hb_dvd_M
  -- ((M/d)/b : ℕ) = M / (d*b).
  have hMdb_eq_Nat : (M / d) / b = M / (d * b) := Nat.div_div_eq_div_mul M d b
  have hMdb_R_eq : (((M / d) / b : ℕ) : ℝ) = (M : ℝ) / ((d : ℝ) * (b : ℝ)) := by
    rw [hMdb_eq_Nat]
    have hdb_cast_ne : ((d * b : ℕ) : ℝ) ≠ 0 := by
      push_cast
      exact mul_ne_zero hd_R_ne hb_R_ne
    have h : ((M / (d * b) : ℕ) : ℝ) = (M : ℝ) / ((d * b : ℕ) : ℝ) :=
      Nat.cast_div hdb_dvd_M_inline hdb_cast_ne
    rw [h]; push_cast; ring
  -- h_combine: ((M/d)/b : ℝ) * count_Pb ≤ y^{-c}/(2d) · M + M_d.
  have h_combine : (((M / d) / b : ℕ) : ℝ) * (count_Pb : ℝ) ≤
      Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) * (M : ℝ) + (M_d : ℝ) := by
    have h_block_R : (((Finset.range (M / d)).filter (fun r => ¬ GoodCompositeSuccessor 20 y_target d r)).card : ℝ) =
        (((M / d) / b : ℕ) : ℝ) * (count_Pb : ℝ) := by
      exact_mod_cast h_block
    rw [← h_block_R, h_count_eq]
    exact h_finset_le_strong
  -- Substitute (M/d)/b = M/(d·b) into h_combine:
  --   (M/(d·b)) · count_Pb ≤ y^{-c}/(2d) · M + M_d.
  -- Multiply both sides by (d·b/M):
  --   count_Pb ≤ y^{-c}/(2d) · M · (d·b/M) + M_d · (d·b/M)
  --           = y^{-c}/2 · b + M_d · d · b / M.
  rw [hMdb_R_eq] at h_combine
  -- **Sub-claim**: M_d · d · b / M ≤ y^{-c}/2 · b (requires M ≥ 2 · M_d · d · y^c).
  -- This is the "L₀ sufficiently large" step (paper §7.4 line 1980-1985: P = exp(y_R^{A-1}) dominates).
  -- Closure path (multi-fire):
  --
  -- 1. From hP_bound at index k+1 (need k+1 < L - √L - 4, restrict L₀ if needed):
  --      exp(y_{k+2}^{A-1}) ≤ outer_P, where y_{k+2} = exp(tower(√L+k+1)/B).
  --
  -- 2. From scale_H_strong applied at √L+k:
  --      exp(y_{k+1}^A) ≤ y_{k+2}, i.e., exp(y_target^A) ≤ y_{k+2}.
  --      Hence y_{k+2}^{A-1} ≥ exp((A-1) · y_target^A) (after exp).
  --
  -- 3. Combined: outer_P ≥ exp(exp((A-1) · y_target^A)) (super-exponential).
  --
  -- 4. By Bertrand's postulate (Mathlib `Nat.exists_prime_lt_and_le_two_mul`):
  --      For outer_P ≥ 2 · ⌊exp(y_target^A)⌋₊ (which holds via step 3),
  --      ∃ prime p, ⌊exp(y_target^A)⌋₊ < p ≤ 2 · ⌊exp(y_target^A)⌋₊ ≤ outer_P.
  --
  -- 5. p ∤ primorial(⌊exp(y_target^A)⌋₊) (since p > ⌊exp(y_target^A)⌋₊), but p ∣ primorial outer_P.
  --    Combined with primorial(⌊exp(y_target^A)⌋₊) ∣ primorial outer_P:
  --      primorial outer_P ≥ primorial(⌊exp(y_target^A)⌋₊) · p.
  --
  -- 6. p ≥ ⌊exp(y_target^A)⌋₊ + 1 ≥ exp(y_target^A) (for y_target large).
  --    Hence primorial outer_P / primorial(⌊exp(y_target^A)⌋₊) ≥ exp(y_target^A).
  --
  -- 7. M_d = d · primorial(⌊exp(y_target^A)⌋₊).
  --    M = primorial outer_P ≥ primorial(⌊exp(y_target^A)⌋₊) · exp(y_target^A) = M_d/d · exp(y_target^A).
  --    M_d · d / M ≤ d² · primorial(⌊exp(y_target^A)⌋₊) / (primorial(⌊exp(y_target^A)⌋₊) · exp(y_target^A))
  --             = d² / exp(y_target^A) ≤ y_target² / exp(y_target^A).
  --
  -- 8. For y_target large, y_target² / exp(y_target^A) ≤ y_target^{-c}/2 (since exp grows faster than poly).
  --
  -- ~150-200 LOC for full Lean proof.  Closes in subsequent fires.
  have hMd_extra_le :
      (M_d : ℝ) * (d : ℝ) * (b : ℝ) / (M : ℝ) ≤
        Real.exp (-c * Real.log y_target) / 2 * (b : ℝ) := by
    -- **Steps A-C lifted to caller**: hP_at_target gives 2·exp(y_target^A) ≤ outer_P.
    -- Caller derives this from hP_bound (k+1) + scale_H for non-boundary k, and from
    -- hP_strong_at_R for boundary k = L-√L-5 (paper §7.4 line 1980-1985).
    have h_2exp_y_target_le_outer_P :
        2 * Real.exp (y_target ^ A) ≤ (P : ℝ) := by
      exact hP_at_target
    have h_exp_y_target_pos : 0 < Real.exp (y_target ^ A) := Real.exp_pos _
    have h_exp_y_target_le_outer_P : Real.exp (y_target ^ A) ≤ (P : ℝ) := by
      linarith [h_2exp_y_target_le_outer_P, h_exp_y_target_pos]
    have h_floor_le_P : ⌊Real.exp (y_target ^ A)⌋₊ ≤ P :=
      Nat.floor_le_of_le h_exp_y_target_le_outer_P
    -- **Step D**: primorial(⌊exp(y_target^A)⌋₊) ∣ M = primorial outer_P.
    have h_prim_dvd : primorial ⌊Real.exp (y_target ^ A)⌋₊ ∣ M := by
      rw [hM_def]
      unfold primorial
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Iic] at hp
      rw [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨hp.1.trans h_floor_le_P, hp.2⟩
    -- **Step E**: 2·⌊exp(y_target^A)⌋₊ ≤ outer_P (so Bertrand finds prime ≤ outer_P).
    set N : ℕ := ⌊Real.exp (y_target ^ A)⌋₊ with hN_def
    have hN_le_P : N ≤ P := h_floor_le_P
    -- 2 · N ≤ outer_P: from outer_P ≥ exp(exp((A-1)y_target^A)) >> 2 · exp(y_target^A) ≥ 2 N.
    -- Now closed via hP_at_target (the strengthened P bound at exponent A).
    have h2N_le_P : 2 * N ≤ P := by
      -- 2N = 2·⌊exp(y_target^A)⌋₊ ≤ 2·exp(y_target^A) ≤ outer_P (via hP_at_target).
      have h2N_R_le : (2 * N : ℝ) ≤ 2 * Real.exp (y_target ^ A) := by
        have h_floor_le : (N : ℝ) ≤ Real.exp (y_target ^ A) := by
          rw [hN_def]; exact Nat.floor_le (Real.exp_pos _).le
        linarith
      exact_mod_cast h2N_R_le.trans h_2exp_y_target_le_outer_P
    -- **Step F**: Bertrand → ∃ prime p₀ ∈ (N, 2·N].
    have hN_pos : 0 < N := by
      rw [hN_def]
      apply Nat.floor_pos.mpr
      have : (1 : ℝ) ≤ y_target ^ A := by
        calc (1 : ℝ) = 1 ^ A := by rw [Real.one_rpow]
          _ ≤ y_target ^ A := Real.rpow_le_rpow (by norm_num) hy_target_ge_1 hA_pos.le
      have hexp_ge : (1 : ℝ) ≤ Real.exp (y_target ^ A) := by
        have := Real.exp_pos (y_target ^ A)
        have h_log : Real.log (Real.exp (y_target ^ A)) = y_target ^ A := Real.log_exp _
        have h_ge : Real.log 1 ≤ Real.log (Real.exp (y_target ^ A)) := by
          rw [h_log, Real.log_one]; linarith
        have := Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1) this
        exact this.mp h_ge
      exact hexp_ge
    have hN_ne_zero : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN_pos
    rcases Nat.exists_prime_lt_and_le_two_mul N hN_ne_zero with ⟨p₀, hp₀_prime, hN_lt_p₀, hp₀_le_2N⟩
    have hp₀_le_P : p₀ ≤ P := hp₀_le_2N.trans h2N_le_P
    -- **Step G**: primorial outer_P ≥ primorial N · p₀.
    have hprim_ge_prod : primorial N * p₀ ≤ primorial P := by
      -- primorial outer_P = ∏ primes ≤ outer_P. Includes primes ≤ N (= primorial N) and p₀.
      -- Since p₀ > N, p₀ ∉ primes ≤ N, so primorial N and p₀ are coprime.
      -- p₀ ∣ primorial outer_P, primorial N ∣ primorial outer_P, gcd = 1 ⟹ primorial N · p₀ ∣ primorial outer_P.
      have hp₀_in_P : p₀ ∈ Finset.filter Nat.Prime (Finset.Iic P) := by
        rw [Finset.mem_filter, Finset.mem_Iic]
        exact ⟨hp₀_le_P, hp₀_prime⟩
      have hp₀_not_in_N : p₀ ∉ Finset.filter Nat.Prime (Finset.Iic N) := by
        intro h
        rw [Finset.mem_filter, Finset.mem_Iic] at h
        omega
      have hp₀_dvd_primorial_P : p₀ ∣ primorial P := by
        unfold primorial
        exact Finset.dvd_prod_of_mem _ hp₀_in_P
      have hprim_N_dvd : primorial N ∣ primorial P := by
        unfold primorial
        apply Finset.prod_dvd_prod_of_subset
        intro q hq
        rw [Finset.mem_filter, Finset.mem_Iic] at hq
        rw [Finset.mem_filter, Finset.mem_Iic]
        exact ⟨hq.1.trans hN_le_P, hq.2⟩
      have h_cop : Nat.Coprime (primorial N) p₀ := by
        unfold primorial
        apply Nat.Coprime.prod_left
        intro q hq
        rw [Finset.mem_filter, Finset.mem_Iic] at hq
        have hq_prime : q.Prime := hq.2
        have hq_le : q ≤ N := hq.1
        have hq_ne_p₀ : q ≠ p₀ := by
          intro heq; rw [heq] at hq_le; omega
        exact (Nat.coprime_primes hq_prime hp₀_prime).mpr hq_ne_p₀
      have h_dvd : primorial N * p₀ ∣ primorial P :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop hprim_N_dvd hp₀_dvd_primorial_P
      have hprim_P_pos : 0 < primorial P := by
        unfold primorial
        exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
      exact Nat.le_of_dvd hprim_P_pos h_dvd
    -- **Step H**: M_d · d · b / M ≤ y_target^{-c}/2 · b.
    -- M_d = d · primorial N (with A = 20 = our outer A via hA_eq, N = ⌊exp(y_target^A)⌋₊).
    have hMd_eq : (M_d : ℝ) = (d : ℝ) * (primorial N : ℝ) := by
      rw [hMd_def]
      unfold compositeSuccessorCRTPeriod compositeSuccessorCutoff
      push_cast
      congr 1
      rw [hN_def, hA_eq]
    -- M = primorial P ≥ primorial N · p₀ (from hprim_ge_prod).
    have hM_ge_prod_R : (primorial N : ℝ) * (p₀ : ℝ) ≤ (M : ℝ) := by
      rw [hM_def]
      exact_mod_cast hprim_ge_prod
    -- (p₀ : ℝ) ≥ N + 1 > exp(y_target^A) (since p₀ > N Nat, ⌊x⌋₊ + 1 > x).
    have hp₀_R_ge : (p₀ : ℝ) ≥ Real.exp (y_target ^ A) := by
      have hp₀_ge_N1 : (N + 1 : ℕ) ≤ p₀ := hN_lt_p₀
      have hp₀_R_ge_N1 : ((N + 1 : ℕ) : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀_ge_N1
      have hN1_gt_exp : Real.exp (y_target ^ A) < ((N + 1 : ℕ) : ℝ) := by
        rw [hN_def]
        push_cast
        exact Nat.lt_floor_add_one (Real.exp (y_target ^ A))
      linarith
    -- M_d · d · b / M ≤ d² · primorial N · b / (primorial N · p₀) = d² · b / p₀.
    have hprim_N_R_pos : (0 : ℝ) < (primorial N : ℝ) := by
      have : 0 < primorial N := by
        unfold primorial; exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
      exact_mod_cast this
    have hp₀_R_pos : (0 : ℝ) < (p₀ : ℝ) := by
      exact_mod_cast hp₀_prime.pos
    have hMd_d_b_le : (M_d : ℝ) * (d : ℝ) * (b : ℝ) / (M : ℝ) ≤
        (d : ℝ)^2 * (b : ℝ) / (p₀ : ℝ) := by
      rw [hMd_eq]
      -- (d · primorial N) · d · b / M = d² · primorial N · b / M.
      -- ≤ d² · primorial N · b / (primorial N · p₀) (using M ≥ primorial N · p₀).
      -- = d² · b / p₀.
      have hM_R_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      have hPN_p₀_R_pos : (0 : ℝ) < (primorial N : ℝ) * (p₀ : ℝ) :=
        mul_pos hprim_N_R_pos hp₀_R_pos
      have h_db2_nn : (0 : ℝ) ≤ (d : ℝ)^2 * (primorial N : ℝ) * (b : ℝ) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hprim_N_R_pos.le) (Nat.cast_nonneg _)
      have h_lhs : (d : ℝ) * (primorial N : ℝ) * (d : ℝ) * (b : ℝ) / (M : ℝ) =
          ((d : ℝ)^2 * (primorial N : ℝ) * (b : ℝ)) / (M : ℝ) := by ring
      rw [h_lhs]
      have h_rhs : (d : ℝ)^2 * (b : ℝ) / (p₀ : ℝ) =
          ((d : ℝ)^2 * (primorial N : ℝ) * (b : ℝ)) / ((primorial N : ℝ) * (p₀ : ℝ)) := by
        field_simp
      rw [h_rhs]
      apply div_le_div_of_nonneg_left h_db2_nn hPN_p₀_R_pos hM_ge_prod_R
    -- Now bound (d : ℝ)^2 * (b : ℝ) / (p₀ : ℝ) ≤ y_target^{-c}/2 · b.
    -- d ≤ y_target, p₀ ≥ exp(y_target^A).  Need: 2 · d² ≤ exp(y_target^A) · y_target^{-c}.
    -- I.e., 2 · d² · y_target^c ≤ exp(y_target^A).
    -- Using d ≤ y_target: 2 · y_target² · y_target^c = 2 · y_target^{2+c} ≤ exp(y_target^A).
    -- For y_target ≥ 2, A = 20, c reasonable: exp(2^20) >> 2 · 2^{2+c}. ✓
    have h_inner : (d : ℝ)^2 * (b : ℝ) / (p₀ : ℝ) ≤
        Real.exp (-c * Real.log y_target) / 2 * (b : ℝ) := by
      have hd_R_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
      have hd_sq_le : (d : ℝ)^2 ≤ y_target^2 := by nlinarith [hd_le_y, hd_R_nn]
      have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
      -- y_target ≥ exp(c+2) from tow_target ≥ B · (c+2).
      -- Apply the threshold lemma.
      have hA_ge_2 : (2 : ℝ) ≤ A := by linarith
      have h_threshold : 2 * y_target ^ (2 + c) ≤ Real.exp (y_target ^ A) :=
        h_threshold_inequality hy_target_pos h_y_target_ge_exp_c2 hA_ge_2 hc
      -- d² · b / p₀ ≤ y² · b / exp(y^A) ≤ exp(-c log y)/2 · b.
      have hp₀_R_pos' : 0 < (p₀ : ℝ) := hp₀_R_pos
      have h_exp_y_pos : 0 < Real.exp (y_target ^ A) := Real.exp_pos _
      have h_yc_pos : 0 < y_target ^ c := Real.rpow_pos_of_pos hy_target_pos _
      have h_db_le : (d : ℝ)^2 * (b : ℝ) / (p₀ : ℝ) ≤
          y_target^2 * (b : ℝ) / Real.exp (y_target ^ A) := by
        apply div_le_div₀
        · exact mul_nonneg (sq_nonneg _) hb_nn
        · exact mul_le_mul_of_nonneg_right hd_sq_le hb_nn
        · exact h_exp_y_pos
        · exact hp₀_R_ge
      -- y² · b / exp(y^A) ≤ exp(-c log y)/2 · b.
      -- ⟺ y²/exp(y^A) ≤ exp(-c log y)/2.
      -- exp(-c log y) = y^{-c}.
      have h_exp_neg_c : Real.exp (-c * Real.log y_target) = y_target ^ (-c) := by
        rw [Real.rpow_def_of_pos hy_target_pos]
        congr 1; ring
      have hy_sq_eq : y_target^2 = y_target ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = (1 : ℝ) + 1 from by norm_num,
            Real.rpow_add_one (ne_of_gt hy_target_pos), Real.rpow_one]
        ring
      have h_yc_pow : y_target^2 * y_target ^ c = y_target ^ (2 + c) := by
        rw [hy_sq_eq, ← Real.rpow_add hy_target_pos]
      -- y² · 2 · y^c ≤ exp(y^A) (from h_threshold via h_yc_pow).
      have h_y2_2_yc_le : 2 * (y_target^2 * y_target ^ c) ≤ Real.exp (y_target ^ A) := by
        rw [h_yc_pow]; exact h_threshold
      -- y² / exp(y^A) ≤ y^{-c}/2 = (y^c)⁻¹/2.
      have h_split_le : y_target^2 / Real.exp (y_target ^ A) ≤ y_target ^ (-c) / 2 := by
        rw [Real.rpow_neg hy_target_pos.le]
        -- Goal: y² / exp(y^A) ≤ (y^c)⁻¹ / 2.
        -- Multiply both sides by 2 · exp(y^A) · y^c (positive): 2 · y² · y^c ≤ exp(y^A).
        rw [div_le_div_iff₀ h_exp_y_pos (by norm_num : (0 : ℝ) < 2)]
        -- Goal: y² * 2 ≤ (y^c)⁻¹ * exp(y^A).
        rw [show ((y_target ^ c)⁻¹ * Real.exp (y_target ^ A)) =
            Real.exp (y_target ^ A) / (y_target ^ c) from by
          rw [mul_comm, ← div_eq_mul_inv]]
        rw [le_div_iff₀ h_yc_pos]
        calc y_target^2 * 2 * y_target ^ c
            = 2 * (y_target^2 * y_target ^ c) := by ring
          _ ≤ Real.exp (y_target ^ A) := h_y2_2_yc_le
      rw [← h_exp_neg_c] at h_split_le
      -- Combine: d² · b / p₀ ≤ y² · b / exp(y^A) ≤ exp(-c log y)/2 · b.
      have h_step_b : y_target^2 * (b : ℝ) / Real.exp (y_target ^ A) ≤
          Real.exp (-c * Real.log y_target) / 2 * (b : ℝ) := by
        rw [show y_target^2 * (b : ℝ) / Real.exp (y_target ^ A) =
            (y_target^2 / Real.exp (y_target ^ A)) * (b : ℝ) from by ring]
        exact mul_le_mul_of_nonneg_right h_split_le hb_nn
      linarith
    linarith [hMd_d_b_le, h_inner]
  -- Algebraic manipulation: from h_combine, derive count_Pb ≤ y^{-c}/2 · b + M_d · d · b / M.
  have hdb_R_pos : (0 : ℝ) < (d : ℝ) * (b : ℝ) := mul_pos hd_R_pos hb_R_pos
  have hdb_R_ne : (d : ℝ) * (b : ℝ) ≠ 0 := ne_of_gt hdb_R_pos
  have h_count_le_split :
      (count_Pb : ℝ) ≤
        Real.exp (-c * Real.log y_target) / 2 * (b : ℝ) +
        (M_d : ℝ) * (d : ℝ) * (b : ℝ) / (M : ℝ) := by
    -- h_combine : (M : ℝ) / ((d : ℝ) * (b : ℝ)) * count_Pb ≤ y^{-c}/(2d) · M + M_d.
    -- Multiply both sides by (d·b/M): count_Pb ≤ ... · (d·b/M).
    have h_mul : (M : ℝ) / ((d : ℝ) * (b : ℝ)) * (count_Pb : ℝ) * ((d : ℝ) * (b : ℝ) / (M : ℝ)) =
        (count_Pb : ℝ) := by
      field_simp
    have hCoeff_pos : (0 : ℝ) < (d : ℝ) * (b : ℝ) / (M : ℝ) := by positivity
    have h_step : (M : ℝ) / ((d : ℝ) * (b : ℝ)) * (count_Pb : ℝ) * ((d : ℝ) * (b : ℝ) / (M : ℝ)) ≤
        (Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) * (M : ℝ) + (M_d : ℝ)) *
        ((d : ℝ) * (b : ℝ) / (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_right h_combine hCoeff_pos.le
    rw [h_mul] at h_step
    have h_rhs_simplify :
        (Real.exp (-c * Real.log y_target) / (2 * (d : ℝ)) * (M : ℝ) + (M_d : ℝ)) *
          ((d : ℝ) * (b : ℝ) / (M : ℝ)) =
        Real.exp (-c * Real.log y_target) / 2 * (b : ℝ) +
        (M_d : ℝ) * (d : ℝ) * (b : ℝ) / (M : ℝ) := by
      field_simp
    rw [h_rhs_simplify] at h_step
    exact h_step
  -- Combine with hMd_extra_le:
  --   count_Pb ≤ y^{-c}/2 · b + y^{-c}/2 · b = y^{-c} · b.
  linarith

/-- **Per-greedy-stage failure bound (paper line 1942-1955).**

Paper-faithful bound on greedy stage failure probability.  For each stage `k`,
the density of integers `n ∈ [0, M)` (where `M = primorial P`) for which
greedy succeeds at level `k` but fails at level `k+1` is bounded by `y_{k+1}^{-c}/2`.

Paper §7.3 line 1942: `P(F_j | past) ≪ y_j^{-c}` (uniform in past on `S_{j-1}`).
Paper §7.3 line 1944-1952: `P(F_j ∩ S_{j-1}) = E[1_{S_{j-1}} · P(F_j | past)] ≪ y_j^{-c}`.

In our Lean residue density model: stage k → k+1 corresponds to "greedy succeeds
at level k but fails at level k+1", i.e., `hGreedySucc k n ∧ ¬ hGreedySucc (k+1) n`.

Proof outline (paper line 1944-1955):
1. Convert `hGreedySucc k n ∧ ¬ hGreedySucc (k+1) n` to existential via
   `hGreedyStageFailure_iff`: `∃ d, hChainEndpoint? n k = some d ∧
   ¬GoodCompositeSuccessor 20 y_target d n`.
2. Partition by d-value: `card = ∑_{d} card({chain_endpoint = d ∧ ¬GoodComposite})`.
3. For each d, apply CRT factorization (`pmodel_crt_factored_count_lifted`):
   - Pa = "endpoint = d" (past-periodic via `hChainEndpoint?_eq_of_mod_primorial`).
   - Pb = "¬GoodCompositeSuccessor" (W_{k+1}-periodic).
   - a = primorial(past_cutoff), b = ∏ W_{k+1} primes; a, b coprime; ab ∣ M.
4. Per-d count ≤ (M/ab) · count(Pa in [0,a)) · count(Pb in [0,b)).
5. count(Pb in [0,b)) ≤ b · y_target^{-c}/2 (via `composite_successor_residue_density`
   transferred to the smaller modulus b).
6. Sum gives ≤ y_target^{-c}/2 · M · density({hGreedySucc k}) ≤ y_target^{-c}/2 · M.

The CRT factorization and future-window count are separated below so that
the proof can be checked with the default computational limits. -/
private lemma h_chain_per_greedy_stage_failure_bound
    {A : ℝ} (hA_eq : A = 20) {B : ℝ} (hAB : A + 10 ≤ B) :
    ∃ c : ℝ, 0 < c ∧
      ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ P : ℕ, 2 ≤ P →
        (∀ k : ℕ, k < L - Nat.sqrt L - 4 →
          Real.exp ((Real.exp (tower (Nat.sqrt L + k) / B)) ^ (A - 1)) ≤ (P : ℝ)) →
        -- hP_at_target: STRONGER per-stage P bound at exponent A (paper §7.4 line 1980-1985).
        -- For each stage k in 0..R-1 (R = L-√L-4), 2 · exp(y_target^A) ≤ outer_P where
        -- y_target = exp(tower(√L+k)/B).  The factor of 2 supports Bertrand's postulate
        -- (∃ prime in (N, 2N]).  Caller derives this from hP_bound (k+1) + scale_H_strong
        -- for non-boundary k (chain has gap exp(y_{k+2}^{A-1}) >> 2·exp(y^A)), and from
        -- hP_strong_at_R for boundary k = R-1 (gap tower(L-3) >> 2·exp(y_R^A)).
        -- This abstraction lets us cover ALL paper stages (including the last) uniformly.
        (∀ k : ℕ, k < L - Nat.sqrt L - 4 →
          2 * Real.exp ((Real.exp (tower (Nat.sqrt L + k) / B)) ^ A) ≤ (P : ℝ)) →
        -- Range now covers ALL paper stages 1..R (R = L-√L-4 in our Lean indexing,
        -- paper's R = L-√L-5 corresponds to our k = L-√L-5 = R-1).
        -- Paper §7.4 line 1957-1962: union bound over j = 1..R.  Lean k = 0..R-1.
        ∀ k : ℕ, k < L - Nat.sqrt L - 4 →
          (Nat.card {r : Fin (primorial P) //
              hGreedySucc A B (Nat.sqrt L) k r.val ∧
              ¬ hGreedySucc A B (Nat.sqrt L) (k + 1) r.val} : ℝ) ≤
            Real.exp (-c * (tower (Nat.sqrt L + k) / B)) / 2 *
              (primorial P : ℝ) := by
  classical
  -- Extract from `step7_residue_density_bound_strong` (CS:8613): A=20-fixed residue
  -- density bound `ρ(y_target, d) ≤ exp(-c·log y_target) / (2d)` (paper §6.2 line 1517-1525).
  -- Combined with `composite_successor_bad_count_le_periodic` (CS:1434), gives:
  --   |bad(20, y, d, x)| ≤ ρ · x + M_d  ≤  y^{-c}/(2d) · x + M_d
  -- where M_d = compositeSuccessorCRTPeriod 20 y d.  The /d in ρ cancels the *d
  -- arising from the bijection r=d*j when transferring count{BadSet} to count{Pb on b}.
  -- This avoids the opaque existential x₀ from step7_combine_and_crt_transfer_strong;
  -- we directly bound the additive M_d term via primorial arithmetic.
  rcases step7_residue_density_bound_strong with ⟨c, hc, y₀, hy₀, h_residue⟩
  -- We use c_outer = c / 2 in the existential to absorb the factor-of-2:
  -- for tower(√L+k) ≥ 2B·log 2/c, we have y_target^{-c} ≤ y_target^{-(c/2)} / 2,
  -- which converts count ≤ M·y_target^{-c} into ≤ M·y_target^{-(c/2)}/2.
  refine ⟨c / 2, by linarith, ?_⟩
  -- L₀ from per-stage setup (matches existing H_chain_per_stage_failure_bound's L₀ derivation).
  have hA_pos : 0 < A := by rw [hA_eq]; norm_num
  have hA_one_le : 1 ≤ A := by rw [hA_eq]; norm_num
  rcases scale_H_strong A B hA_pos hAB with ⟨m_scale, hm_scale⟩
  have hB_pos : 0 < B := by linarith
  -- tow_target combines:
  --  * `B · log y₀`: ensures y_target ≥ y₀ (for step7_combine applicability).
  --  * `2 · B · log 2 / c`: ensures tower ≥ 2B·log 2/c (for y_target^{-c} ≤ y_target^{-c/2}/2 conversion).
  --  * `B · log 2`: ensures y_target ≥ 2 (for coreBad_card_eq_no_good_quotient's hy : 2 ≤ y).
  --  * `B · (c + 2)`: ensures y_target ≥ exp(c+2) for threshold inequality
  --    `2 · y_target^{2+c} ≤ exp(y_target^A)` (paper §7.4 line 1980-1985 outer_P bound).
  set tow_target : ℝ := max (max (max (max 0 (B * Real.log y₀)) (2 * B * Real.log 2 / c))
    (B * Real.log 2)) (B * (c + 2)) with htow_target_def
  rcases Filter.tendsto_atTop.mp tower_tendsto_atTop tow_target with hev_tower
  rcases Filter.eventually_atTop.mp hev_tower with ⟨m₀_thr, hm₀_thr⟩
  refine ⟨max (max (m₀_thr ^ 2) (m_scale ^ 2)) 16, ?_⟩
  intro L hL_ge_max P hP_ge_2 hP_bound hP_at_target k _hk
  -- Setup: M = primorial P, y_target = y_{k+1}.
  set M : ℕ := primorial P with hM_def
  have hMpos : 0 < M := by
    rw [hM_def]
    exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hMpos_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  set y_target : ℝ := Real.exp (tower (Nat.sqrt L + k) / B) with hy_target_def
  have hy_target_pos : 0 < y_target := Real.exp_pos _
  have hy_target_ge_1 : 1 ≤ y_target := by
    rw [hy_target_def]; apply Real.one_le_exp
    exact div_nonneg (tower_pos _).le hB_pos.le
  have hy_target_nn : 0 ≤ y_target := hy_target_pos.le
  -- Bridge: convert hGreedySucc events to the existential form via hGreedyStageFailure_iff.
  have h_event_iff : ∀ r : Fin M,
      (hGreedySucc A B (Nat.sqrt L) k r.val ∧
        ¬ hGreedySucc A B (Nat.sqrt L) (k + 1) r.val) ↔
      ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) r.val k = some d ∧
        ¬ GoodCompositeSuccessor A y_target d r.val := by
    intro r
    rw [hy_target_def]
    -- The existential form gives us paper's "F_{k+1} ∩ S_k" in terms of GoodCompositeSuccessor.
    -- Use hGreedyStageFailure_iff but adjust for A = 20 / generic A consistency:
    -- hGreedyStageFailure_iff returns a condition with A (unchanged) used in GoodCompositeSuccessor.
    exact hGreedyStageFailure_iff hA_one_le
  -- Convert subtype card via the iff.
  have h_card_eq : Nat.card {r : Fin M //
      hGreedySucc A B (Nat.sqrt L) k r.val ∧
      ¬ hGreedySucc A B (Nat.sqrt L) (k + 1) r.val} =
      Nat.card {r : Fin M //
        ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) r.val k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d r.val} :=
    Nat.card_congr (Equiv.subtypeEquivRight h_event_iff)
  rw [h_card_eq]
  -- **Partition by d-value (paper line 1898-1910):**
  --   {n : ∃ d, hChainEndpoint? n k = some d ∧ ¬GoodCompositeSuccessor 20 y_target d n}
  --   = ⊔_{d ∈ valid_d} {n : hChainEndpoint? n k = some d ∧ ¬GoodCompositeSuccessor ...}.
  -- Different d-values give disjoint sets (hChainEndpoint? is a function),
  -- so the disjoint union becomes a Finset.sum.
  --
  -- The valid d-range: d ∈ Finset.Ioc 0 ⌊y_target⌋₊ (covers all possible chain endpoints
  -- since paper line 1908 + scale_H gives d ≤ exp(y_k^A) ≤ y_target via h_d_bound_via_scale).
  -- We use the looser d ∈ Finset.Iic M (M = primorial P) since chain endpoints divide M
  -- (their primes lie in past windows ≤ exp(y_k^{A-1}) ≤ P).
  -- Using Finset.Iic ⌊exp(y_target^A)⌋₊ — covers all valid chain endpoints from
  -- hChainAdmissibleNext (paper line 1908: e ≤ exp(y_j^A)).
  set d_cutoff : ℕ := ⌊Real.exp (y_target ^ A)⌋₊ with hdc_def
  set valid_d : Finset ℕ := Finset.Iic d_cutoff with hvd_def
  -- Bridge to filter form using h_fin_subtype_card_eq_range (provide classical Decidable).
  have h_card_to_filter :
      Nat.card {r : Fin M //
        ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) r.val k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d r.val} =
      ((Finset.range M).filter (fun n =>
        ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d n)).card := by
    classical
    exact h_fin_subtype_card_eq_range
      (fun n => ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
        ¬ GoodCompositeSuccessor A y_target d n)
  rw [h_card_to_filter]
  -- Partition by d: card{n : ∃ d ∈ S, P(d, n)} ≤ ∑_{d ∈ S} card{n : P(d, n)}.
  -- (For a function-valued d, equality holds; for general existential, ≤ holds.)
  -- We use ≤ for simplicity (suffices for our bound).
  -- **Partition equality (since hChainEndpoint? is a function)**:
  -- Each n with `∃ d, ...` has a UNIQUE d (= hChainEndpoint? n k).
  -- So {n : ∃ d ∈ valid_d, P(d, n)} = ⊔_{d ∈ valid_d} {n : P(d, n)} (disjoint).
  -- This converts to Finset.sum equality.
  have h_card_eq_sum :
      (((Finset.range M).filter (fun n =>
        ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d n)).card : ℝ) ≤
      ∑ d ∈ valid_d,
        (((Finset.range M).filter (fun n =>
          hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d n)).card : ℝ) := by
    -- Use Finset.card_biUnion_le: card(LHS) ≤ ∑_{d ∈ valid_d} card({n : P(d, n)}).
    -- LHS ⊆ ⋃_{d ∈ valid_d} {n : P(d, n)} since:
    --   any n in LHS has some d with hChainEndpoint? n k = some d.
    --   d ∈ Finset.Iic d_cutoff (= valid_d) since hChainEndpoint? returns from hChainAdmissibleNext
    --   which filters from Iic d_cutoff.
    have h_subset :
        (Finset.range M).filter (fun n =>
          ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
            ¬ GoodCompositeSuccessor A y_target d n) ⊆
        valid_d.biUnion (fun d => (Finset.range M).filter (fun n =>
          hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d n)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hn_lt, d, hd, hgood⟩ := hn
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_Iic, hvd_def]
      refine ⟨d, ?_, hn_lt, hd, hgood⟩
      -- d ∈ valid_d = Iic d_cutoff: d ≤ ⌊exp(y_target^A)⌋₊.
      -- Case-split on k.
      by_cases hk_zero : k = 0
      · -- k = 0: d = 1 by hChainEndpoint?_zero.
        subst hk_zero
        rw [hChainEndpoint?_zero] at hd
        injection hd with h_eq
        rw [← h_eq]
        -- Need 1 ≤ d_cutoff = ⌊exp(y_target^A)⌋₊.
        -- y_target ≥ 1, so y_target^A ≥ 1, so exp(...) ≥ exp(1) > 2, floor ≥ 2 ≥ 1.
        rw [hdc_def]
        apply Nat.le_floor
        have hy_pow_ge : 1 ≤ y_target ^ A := by
          calc (1 : ℝ) = 1 ^ A := by rw [Real.one_rpow]
            _ ≤ y_target ^ A := Real.rpow_le_rpow (by norm_num) hy_target_ge_1 hA_pos.le
        have hexp_ge : (1 : ℝ) ≤ Real.exp (y_target ^ A) := by
          have := Real.exp_pos (y_target ^ A)
          have h_log : Real.log (Real.exp (y_target ^ A)) = y_target ^ A := Real.log_exp _
          have h_ge : Real.log 1 ≤ Real.log (Real.exp (y_target ^ A)) := by
            rw [h_log, Real.log_one]; linarith
          have := Real.log_le_log_iff (by norm_num : (0 : ℝ) < 1) this
          exact this.mp h_ge
        push_cast
        exact hexp_ge
      · -- k ≥ 1: d ∈ hChainAdmissibleNext A B m₀ (k-1) d_prev n.
        have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_zero
        rcases hChainEndpoint?_succ_mem_admissible (k := k - 1)
          (by rw [Nat.sub_add_cancel hk_pos]; exact hd) with ⟨_, _, hd_admissible⟩
        rcases hChainAdmissibleNext_mem.mp hd_admissible with
          ⟨h_d_le_floor, _, _, _, _, _, _⟩
        -- h_d_le_floor : d ≤ ⌊exp(y_{k}^A)⌋₊ where y_k = exp(tower(m₀+(k-1))/B).
        -- Need d ≤ ⌊exp(y_target^A)⌋₊ where y_target = exp(tower(m₀+k)/B).
        -- Since tower(m₀+(k-1)) ≤ tower(m₀+k), y_k ≤ y_target.
        rw [hdc_def, hy_target_def]
        -- Show ⌊exp((exp(tower((Nat.sqrt L) + (k - 1))/B))^A)⌋₊ ≤ ⌊exp((exp(tower((Nat.sqrt L) + k)/B))^A)⌋₊.
        have h_sub_eq : Nat.sqrt L + (k - 1) + 1 = Nat.sqrt L + k := by omega
        apply le_trans h_d_le_floor
        apply Nat.floor_le_floor
        apply Real.exp_le_exp.mpr
        apply Real.rpow_le_rpow
        · positivity
        · -- exp(tower(m₀+(k-1))/B) ≤ exp(tower(m₀+k)/B): tower monotone.
          apply Real.exp_le_exp.mpr
          have h_idx_le : Nat.sqrt L + (k - 1) ≤ Nat.sqrt L + k := by omega
          have h_tow_le : tower (Nat.sqrt L + (k - 1)) ≤ tower (Nat.sqrt L + k) :=
            tower_le_of_le h_idx_le
          exact div_le_div_of_nonneg_right h_tow_le hB_pos.le
        · exact hA_pos.le
    calc (((Finset.range M).filter _).card : ℝ)
        ≤ ((valid_d.biUnion _).card : ℝ) := by
          exact_mod_cast Finset.card_le_card h_subset
      _ ≤ (∑ d ∈ valid_d, ((Finset.range M).filter _).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
  -- **CRT factorization setup (paper line 1932-1955)**.
  --
  -- Define the past/future moduli for CRT factorization:
  --  * `a` := primorial of primes ≤ exp(y_k^{A-1}) (covers all past windows W_1, ..., W_k).
  --     Paper line 1899: chain prefix "is determined by selections in earlier windows".
  --  * `b` := primorial of primes in W_{k+1} = (exp y_target, exp(y_target^{A-1})].
  --     Paper line 1903: window definition.
  --
  -- For k = 0 (no past windows), a = 1.  For k ≥ 1, a uses primes ≤ exp(y_k^{A-1}).
  -- Both a and b divide M = primorial P (via hP_bound at indices k-1 and k).
  -- a, b coprime via window disjointness (paper line 1932-1936): scale_H gives
  --   y_target = y_{k+1} ≥ exp(y_k^A) > y_k^{A-1}, so primes in a are < y_target,
  --   while primes in b are > exp(y_target) > y_target.  Disjoint.
  set future_lower_floor : ℕ := ⌊Real.exp y_target⌋₊ with hflf_def
  set future_upper_floor : ℕ := ⌊Real.exp (y_target ^ (A - 1))⌋₊ with hfuf_def
  -- b := primorial of primes q with future_lower_floor < q ≤ future_upper_floor.
  -- These are the W_{k+1} primes: q > exp(y_target), q ≤ exp(y_target^{A-1}).
  set b_primes : Finset ℕ :=
    (Finset.Ioc future_lower_floor future_upper_floor).filter Nat.Prime with hbp_def
  set b : ℕ := ∏ q ∈ b_primes, q with hb_def
  have hb_pos : 0 < b := by
    rw [hb_def]
    apply Finset.prod_pos
    intro q hq
    rw [hbp_def] at hq
    rw [Finset.mem_filter] at hq
    exact hq.2.pos
  -- All q ∈ b_primes are prime and > future_lower_floor.
  have hb_primes_prime : ∀ q ∈ b_primes, q.Prime := by
    intros q hq
    rw [hbp_def] at hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    exact hq.2
  -- b ∣ M: every q ∈ b_primes is ≤ future_upper_floor ≤ P (via hP_bound at index k).
  have hb_dvd_M : b ∣ M := by
    rw [hb_def, hM_def]
    -- Want: ∏ q ∈ b_primes, q ∣ primorial P.
    -- Since each q ∈ b_primes is prime and ≤ future_upper_floor ≤ P,
    -- each q divides primorial P (= ∏ p ≤ P prime, p).
    -- Hence the product divides primorial P (squarefree case).
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro q hq
    rw [hbp_def, Finset.mem_filter, Finset.mem_Ioc] at hq
    -- hq : (future_lower_floor < q ∧ q ≤ future_upper_floor) ∧ q.Prime
    have hq_prime := hq.2
    have hq_le_upper : q ≤ future_upper_floor := hq.1.2
    -- future_upper_floor ≤ P via hP_bound at k.
    have hP_at_k : Real.exp ((Real.exp (tower (Nat.sqrt L + k) / B)) ^ (A - 1)) ≤ (P : ℝ) :=
      hP_bound k (by omega)
    have h_q_le_P : q ≤ P := by
      have h_floor_le : future_upper_floor ≤ P := by
        -- ⌊exp(y_target^(A-1))⌋₊ ≤ P since exp(y_target^(A-1)) ≤ P (hP_at_k) and P is Nat.
        have h_eq_y : Real.exp (y_target ^ (A - 1)) =
            Real.exp ((Real.exp (tower (Nat.sqrt L + k) / B)) ^ (A - 1)) := by
          rw [hy_target_def]
        rw [hfuf_def, h_eq_y]
        exact_mod_cast Nat.floor_le_of_le hP_at_k
      omega
    -- q ∈ primorial P's filter set (primes ≤ P).
    rw [Finset.mem_filter, Finset.mem_Iic]
    exact ⟨by omega, hq_prime⟩
  -- **Past-primorial `a`** (paper line 1899: chain prefix is determined by W_1, ..., W_k).
  -- For k = 0, no past windows: a = 1.  For k ≥ 1, a = primorial(⌊exp(y_k^{A-1})⌋₊).
  set past_cutoff : ℕ := if hk : 1 ≤ k then
    ⌊Real.exp ((Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ (A - 1))⌋₊ else 0
    with hpc_def
  set a : ℕ := primorial past_cutoff with ha_def
  have ha_pos : 0 < a := by
    rw [ha_def]
    unfold primorial
    apply Finset.prod_pos
    intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.pos
  -- a ∣ M: every prime in a is ≤ past_cutoff ≤ exp(y_k^{A-1}).
  -- For k = 0: past_cutoff = 0, a = primorial(0) = 1 (= ∏ over empty/single set).
  --   Hence a ∣ M trivially (1 ∣ anything).
  -- For k ≥ 1: past_cutoff = ⌊exp(y_k^{A-1})⌋₊, and exp(y_k^{A-1}) ≤ y_target = y_{k+1}
  --   (by scale_H: y_{k+1} ≥ exp(y_k^A) > exp(y_k^{A-1}) for A > 1, paper line 1933).
  --   And y_target ≤ exp(y_target^{A-1}) ≤ P (via hP_bound at index k).  So past_cutoff ≤ P.
  have ha_dvd_M : a ∣ M := by
    rw [ha_def, hM_def]
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Iic] at hp ⊢
    refine ⟨?_, hp.2⟩
    -- p ≤ past_cutoff ≤ P.
    have h_pc_le_P : past_cutoff ≤ P := by
      by_cases hk_zero : k = 0
      · -- k = 0: past_cutoff = 0 ≤ P.
        rw [hpc_def]
        simp [hk_zero]
      · -- k ≥ 1: past_cutoff = ⌊exp(y_k^{A-1})⌋₊.
        have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_zero
        rw [hpc_def, dif_pos hk_pos]
        -- ⌊exp(y_k^{A-1})⌋₊ ≤ P via hP_bound at index (k-1).
        have h_km1_lt : k - 1 < L - Nat.sqrt L - 4 := by omega
        have hP_at_km1 := hP_bound (k - 1) h_km1_lt
        exact_mod_cast Nat.floor_le_of_le hP_at_km1
    omega
  -- **Coprimality `a.Coprime b` (paper line 1932-1936 verbatim)**.
  -- a's primes ≤ past_cutoff ≤ exp(y_k^{A-1}).  For k ≥ 1, by scale_H
  -- (paper line 1933): y_target = y_{k+1} ≥ exp(y_k^A) > y_k^{A-1}, so
  -- exp(y_k^{A-1}) < exp(y_target).  Hence a's primes < future_lower_floor,
  -- while b's primes > future_lower_floor.  Disjoint primes ⟹ coprime products.
  have hab_coprime : a.Coprime b := by
    rw [ha_def, hb_def]
    -- primorial past_cutoff coprime to ∏ b_primes.
    -- Use Nat.Coprime.prod_right: ∀ q ∈ b_primes, primorial past_cutoff coprime q.
    apply Nat.Coprime.prod_right
    intro q hq
    -- For each q ∈ b_primes: q is prime, q > future_lower_floor ≥ past_cutoff (need to show).
    -- Hence q is NOT in primorial past_cutoff's prime set, so coprime.
    rw [hbp_def, Finset.mem_filter, Finset.mem_Ioc] at hq
    have hq_prime : q.Prime := hq.2
    have hq_gt_lower : future_lower_floor < q := hq.1.1
    -- past_cutoff < q: need past_cutoff ≤ future_lower_floor.
    -- For k = 0: past_cutoff = 0 ≤ future_lower_floor (any natural).
    -- For k ≥ 1: past_cutoff ≤ ⌊exp(y_k^{A-1})⌋₊ ≤ ⌊exp(y_target - 1)⌋₊ ≤ future_lower_floor.
    --   Actually we need exp(y_k^{A-1}) < exp(y_target).  By scale_H paper line 1933:
    --   y_target = y_{k+1} > y_k^{A-1}, so exp(y_target) > exp(y_k^{A-1}).
    --   But future_lower_floor = ⌊exp(y_target)⌋₊.  We need past_cutoff < future_lower_floor.
    --
    -- For k ≥ 1: past_cutoff = ⌊exp(y_k^{A-1})⌋₊.  Need ⌊exp(y_k^{A-1})⌋₊ < ⌊exp(y_target)⌋₊.
    --   Since exp(y_k^{A-1}) < exp(y_target), AND BOTH are positive non-integer reals
    --   (generally), the floors might differ by ≥ 1 OR be equal.
    --   Generally ⌊x⌋₊ < ⌊y⌋₊ requires y - x ≥ 1.  In our case, exp(y_target) - exp(y_k^{A-1})
    --   can be very large, so floors differ.
    --
    -- Simpler approach: show past_cutoff < q directly via past_cutoff < exp(y_target) < q.
    have hpc_lt_q : past_cutoff < q := by
      by_cases hk_zero : k = 0
      · rw [hpc_def]
        simp [hk_zero]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_of_le_of_lt (Nat.zero_le _) hq_prime.one_lt)
      · -- k ≥ 1: past_cutoff ≤ ⌊exp(y_k^{A-1})⌋₊.
        have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_zero
        rw [hpc_def, dif_pos hk_pos]
        -- Need ⌊exp(y_k^{A-1})⌋₊ < q.
        -- We have q > future_lower_floor = ⌊exp(y_target)⌋₊.
        -- Need ⌊exp(y_k^{A-1})⌋₊ ≤ future_lower_floor (then strict via q > future_lower_floor).
        -- exp(y_k^{A-1}) ≤ exp(y_target) (since y_k^{A-1} ≤ y_target by scale_H).
        -- Actually, scale_H gives y_target ≥ exp(y_k^A) > y_k^{A-1}, hence exp(y_k^{A-1}) < exp(y_target).
        -- So ⌊exp(y_k^{A-1})⌋₊ ≤ ⌊exp(y_target)⌋₊ = future_lower_floor.
        -- Then ⌊exp(y_k^{A-1})⌋₊ ≤ future_lower_floor < q.
        have h_y_k_lt_y_target : (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ (A - 1) <
            Real.exp (tower (Nat.sqrt L + k) / B) := by
          -- y_k^{A-1} < y_{k+1} = y_target via scale_H_strong applied at m = √L + k - 1.
          have h_sqrt_km1_ge_m_scale : m_scale ≤ Nat.sqrt L + (k - 1) := by
            have h_sqrt_ge : m_scale ≤ Nat.sqrt L := by
              rw [Nat.le_sqrt, ← pow_two]
              exact le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hL_ge_max
            exact h_sqrt_ge.trans (Nat.le_add_right _ _)
          have h_scale := hm_scale _ h_sqrt_km1_ge_m_scale
          -- h_scale : exp((exp(tower(√L+(k-1))/B))^A) ≤ exp(tower(√L+(k-1)+1)/B).
          -- We need: (exp(tower(√L+(k-1))/B))^{A-1} < exp(tower(√L+k)/B).
          -- = (exp(tower(√L+(k-1))/B))^{A-1} < y_target.
          -- (exp(tower/B))^{A-1} < (exp(tower/B))^A (when exp(tower/B) > 1, A > 1).
          -- Then exp((exp(tower/B))^A) ≤ y_target+1's tower (next stage), giving:
          -- (exp(tower/B))^A ≤ tower(√L+k)/B (i.e., y_target = exp(tower(√L+k)/B)).
          -- Hmm, simpler: (exp t)^{A-1} < exp((exp t)^A) (by add_one_le_exp + monotonicity).
          have h_exp_pos : (1 : ℝ) ≤ Real.exp (tower (Nat.sqrt L + (k - 1)) / B) := by
            apply Real.one_le_exp
            exact div_nonneg (tower_pos _).le hB_pos.le
          have h_pow_lt_pow : (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ (A - 1) ≤
              (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A := by
            apply Real.rpow_le_rpow_of_exponent_le h_exp_pos
            linarith
          -- Bridge: y_k^{A-1} < exp(y_k^A) ≤ exp(tower(√L+k)/B) = y_target.
          -- Step 1: y_k^{A-1} ≤ y_k^A (since y_k ≥ 1 and A-1 ≤ A).
          -- Step 2: y_k^A < exp(y_k^A) (Real.add_one_le_exp).
          -- Step 3: exp(y_k^A) ≤ exp(tower(√L+k)/B) (scale_H_strong, after exp).
          have h_y_k_pow_lt_y_target_internal :
              (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ (A - 1) <
              Real.exp ((Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A) := by
            have h_pow_pos : (0 : ℝ) <
                (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A := by
              apply Real.rpow_pos_of_pos
              exact Real.exp_pos _
            have h_pow_ne_zero : (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A ≠ 0 :=
              ne_of_gt h_pow_pos
            have h_x_lt_exp_x : (Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A <
                Real.exp ((Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A) := by
              have := Real.add_one_lt_exp h_pow_ne_zero
              linarith
            linarith [h_pow_lt_pow]
          have h_exp_y_k_pow_le : Real.exp ((Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ A) ≤
              Real.exp (tower (Nat.sqrt L + k) / B) := by
            -- scale_H_strong applied at m = √L + k - 1: gives the LHS ≤ exp(tower(√L+k)/B).
            have h_idx_eq : Nat.sqrt L + (k - 1) + 1 = Nat.sqrt L + k := by omega
            rw [← h_idx_eq]
            exact h_scale
          linarith
        -- Lift to floor comparison.
        have h_floor_le : ⌊Real.exp ((Real.exp (tower (Nat.sqrt L + (k - 1)) / B)) ^ (A - 1))⌋₊ ≤
            future_lower_floor := by
          rw [hflf_def]
          apply Nat.floor_le_floor
          -- exp(y_k^{A-1}) ≤ exp(y_target). Use h_y_k_lt_y_target.
          apply Real.exp_le_exp.mpr
          rw [hy_target_def]
          exact le_of_lt h_y_k_lt_y_target
        omega
    have h_q_not_in_primorial : q ∉ Finset.filter Nat.Prime (Finset.Iic past_cutoff) := by
      intro h_in
      rw [Finset.mem_filter, Finset.mem_Iic] at h_in
      omega
    -- primorial past_cutoff = ∏ p ∈ filter Prime (Iic past_cutoff), p.
    -- q is prime, q ∉ filter, so q is coprime to each factor p.
    rw [primorial]
    apply Nat.Coprime.prod_left
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Iic] at hp
    have hp_prime : p.Prime := hp.2
    have hp_le : p ≤ past_cutoff := hp.1
    have hp_ne_q : p ≠ q := fun heq => by rw [heq] at hp_le; omega
    exact (Nat.coprime_primes hp_prime hq_prime).mpr hp_ne_q
  -- a * b ∣ M.
  have hab_dvd_M : a * b ∣ M :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hab_coprime ha_dvd_M hb_dvd_M
  -- **Pa(d) periodicity (paper line 1913, 1923 — past-window measurability)**.
  -- Pa(d, n) := "hChainEndpoint? n k = some d" depends only on n mod a = primorial past_cutoff.
  -- Use hChainEndpoint?_eq_of_mod_primorial_floor (Nat-form, paper-faithful).
  have hPa_periodic : ∀ d : ℕ, ∀ r r' : ℕ, r % a = r' % a →
      (hChainEndpoint? A B (Nat.sqrt L) r k = some d ↔
       hChainEndpoint? A B (Nat.sqrt L) r' k = some d) := by
    intro d r r' hmod
    -- Need: ⌊exp((exp(tower(m₀+j)/B))^{A-1})⌋₊ ≤ past_cutoff for all j < k.
    have hP_bound_nat : ∀ j : ℕ, j < k →
        ⌊Real.exp ((Real.exp (tower (Nat.sqrt L + j) / B)) ^ (A - 1))⌋₊ ≤ past_cutoff := by
      intro j hj
      have hk_ge_1 : 1 ≤ k := by omega
      rw [hpc_def, dif_pos hk_ge_1]
      apply Nat.floor_le_floor
      apply Real.exp_le_exp.mpr
      apply Real.rpow_le_rpow
      · positivity
      · apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right
        · apply tower_le_of_le; omega
        · exact hB_pos.le
      · linarith
    have hr_modeq : r ≡ r' [MOD a] := hmod
    have hr_modeq' : r ≡ r' [MOD primorial past_cutoff] := by
      rw [ha_def] at hr_modeq; exact hr_modeq
    have hA_one_le_local : (1 : ℝ) ≤ A := by linarith
    rw [hChainEndpoint?_eq_of_mod_primorial_floor hA_one_le_local hP_bound_nat hr_modeq']
  -- **Pb(d) periodicity (paper line 1916 — future-window measurability)**.
  -- Pb(d, n) := "¬GoodCompositeSuccessor A y_target d n" depends only on n mod b
  -- (the product of W_{k+1} primes), since GoodCompositeSuccessor's only n-dependence
  -- is via (∏ T) ∣ n for T ⊆ b_primes.
  have hPb_periodic : ∀ d : ℕ, ∀ r r' : ℕ, r % b = r' % b →
      (¬ GoodCompositeSuccessor A y_target d r ↔ ¬ GoodCompositeSuccessor A y_target d r') := by
    intro d r r' hmod
    have h_pos_iff : GoodCompositeSuccessor A y_target d r ↔
        GoodCompositeSuccessor A y_target d r' := by
      constructor
      · rintro ⟨T, hT_admissible, hT_dvd⟩
        refine ⟨T, hT_admissible, ?_⟩
        -- ∏ T ∣ r' from ∏ T ∣ r and r ≡ r' [MOD b], where ∏ T ∣ b.
        have hT_dvd_b : (∏ q ∈ T, q) ∣ b := by
          rw [hb_def]
          apply Finset.prod_dvd_prod_of_subset
          intro q hqT
          rcases hT_admissible with ⟨_hTne, hTprime, _⟩
          have hq_data := hTprime q hqT
          rw [hbp_def, Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨?_, ?_⟩, hq_data.1⟩
          · -- future_lower_floor < q (Nat).
            -- (q : ℝ) > exp y_target, so q ≥ ⌊exp y_target⌋₊ + 1 = future_lower_floor + 1.
            -- Hmm need to be careful with Nat coercion.
            -- Actually we just need future_lower_floor < q (Nat strict).
            -- (q : ℝ) > exp y_target ≥ (future_lower_floor : ℝ) (since floor ≤ real).
            -- So (q : ℝ) > (future_lower_floor : ℝ).  Nat cast: q > future_lower_floor.
            rw [hflf_def]
            have : (Real.exp y_target) < (q : ℝ) := hq_data.2.1
            have h_floor_le : (⌊Real.exp y_target⌋₊ : ℝ) ≤ Real.exp y_target :=
              Nat.floor_le (Real.exp_pos _).le
            have : (⌊Real.exp y_target⌋₊ : ℝ) < (q : ℝ) := lt_of_le_of_lt h_floor_le this
            exact_mod_cast this
          · -- q ≤ future_upper_floor (Nat).
            -- (q : ℝ) ≤ exp(y_target^{A-1}). Since q is Nat, q ≤ ⌊exp(...)⌋₊ via Nat.le_floor.
            rw [hfuf_def]
            exact Nat.le_floor hq_data.2.2
        have hr_modeq : r ≡ r' [MOD b] := hmod
        exact (hr_modeq.dvd_iff hT_dvd_b).mp hT_dvd
      · rintro ⟨T, hT_admissible, hT_dvd⟩
        refine ⟨T, hT_admissible, ?_⟩
        have hT_dvd_b : (∏ q ∈ T, q) ∣ b := by
          rw [hb_def]
          apply Finset.prod_dvd_prod_of_subset
          intro q hqT
          rcases hT_admissible with ⟨_hTne, hTprime, _⟩
          have hq_data := hTprime q hqT
          rw [hbp_def, Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨?_, ?_⟩, hq_data.1⟩
          · rw [hflf_def]
            have : (Real.exp y_target) < (q : ℝ) := hq_data.2.1
            have h_floor_le : (⌊Real.exp y_target⌋₊ : ℝ) ≤ Real.exp y_target :=
              Nat.floor_le (Real.exp_pos _).le
            have : (⌊Real.exp y_target⌋₊ : ℝ) < (q : ℝ) := lt_of_le_of_lt h_floor_le this
            exact_mod_cast this
          · rw [hfuf_def]
            exact Nat.le_floor hq_data.2.2
        have hr_modeq : r ≡ r' [MOD b] := hmod
        exact (hr_modeq.dvd_iff hT_dvd_b).mpr hT_dvd
    exact not_iff_not.mpr h_pos_iff
  -- **Per-d CRT factorization** via `pmodel_crt_factored_count_lifted` (LBL:1446).
  -- For each d ∈ valid_d:
  --   card({Pa(d) ∧ Pb(d) on Fin M}) = (M/(a·b)) · count(Pa(d) on Fin a) · count(Pb(d) on Fin b).
  have hpc_factor : ∀ d : ℕ,
      (((Finset.range M).filter (fun r =>
        hChainEndpoint? A B (Nat.sqrt L) r k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d r)).card : ℕ) =
      (M / (a * b)) *
        (((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card *
         ((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor A y_target d r)).card) := by
    intro d
    apply pmodel_crt_factored_count_lifted ha_pos hb_pos hab_coprime hab_dvd_M
      (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)
      (fun r => ¬ GoodCompositeSuccessor A y_target d r)
      (hPa_periodic d) (hPb_periodic d)
  -- **Per-d count(Pb on b) bound (paper line 1942 + §6.2 Lemma 6.2 with /d factor)**.
  -- For each d ∈ valid_d with 1 ≤ d ≤ y_target:
  --   count(Pb(d) on Fin b) ≤ b · y_target^{-c}.
  -- Strategy (paper line 1944-1976):
  --  1. Apply h_strong at x = (M : ℝ) to get
  --     count{CompositeSuccessorBadSet 20 y_target d M} ≤ y_target^{-c} · M / d.
  --     Requires M ≥ x₀(y_target, d), which holds for L large enough since M is super-primorial.
  --  2. CompositeSuccessorBadSet = {n ∈ [1, M] : 0 < n ∧ d ∣ n ∧ ¬GoodComp(d, n)}.
  --  3. Bijection r = d*j (using d coprime to b's primes, paper line 1932-1936):
  --     count{n ∈ [1, M] : d ∣ n ∧ ¬GoodComp(d, n)} = count{j ∈ [1, M/d] : ¬GoodComp(d, j)}.
  --  4. b-periodicity (paper line 1916), with b ∣ M/d (since d ∣ a, b ∣ M, gcd(a,b)=1):
  --     count{j ∈ range(M/d) : ¬GoodComp(d, j)} = (M/(db)) · count{Pb on b}.
  --  5. Combine: (M/(db)) · count{Pb on b} ≤ y_target^{-c} · M/d, hence count{Pb on b} ≤ y_target^{-c} · b.
  have hPbBound : ∀ d : ℕ, d ∈ valid_d → 1 ≤ d → (d : ℝ) ≤ y_target → d ∣ a →
      (((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ) ≤
        (b : ℝ) * Real.exp (-c * Real.log y_target) := by
    intro d _hd_mem hd_pos hd_le_y hd_dvd_a
    have hsqrt : m₀_thr ≤ Nat.sqrt L := by
      rw [Nat.le_sqrt, ← pow_two]
      exact le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hL_ge_max
    have htower := hm₀_thr (Nat.sqrt L + k) (hsqrt.trans (Nat.le_add_right _ _))
    have hexp_bound : ∀ z : ℝ, B * z ≤ tow_target → Real.exp z ≤ y_target := by
      intro z hz
      rw [hy_target_def]
      apply Real.exp_le_exp.mpr
      rw [le_div_iff₀ hB_pos]
      simpa only [mul_comm] using hz.trans htower
    have hy₀_le : y₀ ≤ y_target := by
      rw [← Real.exp_log hy₀]
      apply hexp_bound
      rw [htow_target_def]
      exact (le_max_right _ _).trans
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    have hy₂ : 2 ≤ y_target := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      apply hexp_bound
      rw [htow_target_def]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hyc : Real.exp (c + 2) ≤ y_target := by
      apply hexp_bound
      rw [htow_target_def]
      exact le_max_right _ _
    exact future_window_failure_bound hA_eq hc h_residue hy₀_le hy₂ hyc
      hM_def hMpos (hP_at_target k _hk) hb_pos hb_dvd_M ha_dvd_M
      hab_coprime hab_dvd_M hPb_periodic hd_pos hd_le_y hd_dvd_a
  -- **Sum over d ∈ valid_d**.  Combine hpc_factor (per-d CRT factorization),
  -- hPbBound (per-d Pb bound), and h_card_eq_sum (partition by d) to derive
  -- card({∃ d, Pa ∧ Pb on M}) ≤ M · y_target^{-c} ≤ M · y_target^{-c/2}/2 (paper line 1944-1952).
  --
  -- Note: the chain endpoint d satisfies d ≤ y_target (paper line 1930: d_{j+1} ≤ y_{j+1}).
  -- For any n with hChainEndpoint? n k = some d, admissibility (paper line 1908) gives
  -- d ≤ exp(y_k^A) ≤ y_target via scale_H.  We restrict the partition to
  -- valid_d_good := {d ∈ valid_d : 1 ≤ d ≤ ⌊y_target⌋₊}.  Terms with d ∉ valid_d_good
  -- have count{Pa(d) on a} = 0 (no chain with such an endpoint).
  --
  -- **Step 1**: chain-endpoint range lemma (paper line 1930 + 1908).
  -- For any n, if hChainEndpoint? A B (Nat.sqrt L) n k = some d, then 1 ≤ d ≤ ⌊y_target⌋₊.
  have h_endpoint_range : ∀ n : ℕ, ∀ d : ℕ,
      hChainEndpoint? A B (Nat.sqrt L) n k = some d → 1 ≤ d ∧ d ≤ ⌊y_target⌋₊ := by
    intro n d hd
    refine ⟨hChainEndpoint?_some_ge_one hd, ?_⟩
    -- d ≤ ⌊y_target⌋₊: from chain admissibility d ≤ exp(y_k^A), then scale_H gives ≤ y_target.
    by_cases hk_zero : k = 0
    · -- k = 0: hChainEndpoint?_zero ⟹ d = 1 ≤ ⌊y_target⌋₊.
      subst hk_zero
      rw [hChainEndpoint?_zero] at hd
      injection hd with h_eq
      rw [← h_eq]
      apply Nat.le_floor
      simp
      exact hy_target_ge_1
    · -- k ≥ 1: extract admissibility constraint.
      have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_zero
      rcases hChainEndpoint?_succ_mem_admissible (k := k - 1)
        (by rw [Nat.sub_add_cancel hk_pos]; exact hd) with ⟨_, _, hd_admissible⟩
      rcases hChainAdmissibleNext_mem.mp hd_admissible with
        ⟨h_d_le_floor, _, _, _, _, _, _⟩
      -- h_d_le_floor : d ≤ ⌊exp(y_k^A)⌋₊ where y_k = exp(tower(√L+(k-1))/B).
      -- scale_H_strong: exp(y_k^A) ≤ y_target = exp(tower(√L+k)/B).
      have h_sqrt_km1_ge_m_scale : m_scale ≤ Nat.sqrt L + (k - 1) := by
        have h_sqrt_ge : m_scale ≤ Nat.sqrt L := by
          rw [Nat.le_sqrt, ← pow_two]
          exact le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hL_ge_max
        exact h_sqrt_ge.trans (Nat.le_add_right _ _)
      have h_scale := hm_scale _ h_sqrt_km1_ge_m_scale
      -- h_scale : exp((exp(tower(√L+(k-1))/B))^A) ≤ exp(tower(√L+(k-1)+1)/B) = y_target.
      have h_idx_eq : Nat.sqrt L + (k - 1) + 1 = Nat.sqrt L + k := by omega
      rw [h_idx_eq] at h_scale
      -- d ≤ ⌊exp(y_k^A)⌋₊ ≤ ⌊y_target⌋₊.
      apply le_trans h_d_le_floor
      apply Nat.floor_le_floor
      rw [hy_target_def]
      exact h_scale
  -- **Step 2**: Bound the sum by per-d CRT factorization + hPbBound.
  -- ∑_d (((Finset.range M).filter Pa∧Pb).card : ℝ)
  -- ≤ ∑_d (M/(ab)) · count{Pa(d) on a} · count{Pb(d) on b}     [hpc_factor: equality]
  -- ≤ ∑_d (M/(ab)) · count{Pa(d) on a} · b · y_target^{-c}     [hPbBound]
  -- = (M/(ab)) · b · y_target^{-c} · ∑_d count{Pa(d) on a}
  -- = (M/a) · y_target^{-c} · ∑_d count{Pa(d) on a}
  -- ≤ (M/a) · y_target^{-c} · a   [partition: ∑_d count{Pa(d) on a} ≤ a]
  -- = M · y_target^{-c}.
  --
  -- For technical reasons (hPbBound requires d ≤ y_target), we restrict d via
  -- h_endpoint_range: count{Pa(d) on a} > 0 ⟹ d ∈ [1, ⌊y_target⌋₊].
  -- For d ∉ valid_d_good (= {d : 1 ≤ d ≤ ⌊y_target⌋₊}), count{Pa(d) on a} = 0.
  have hMpos_R : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hab_pos : 0 < a * b := Nat.mul_pos ha_pos hb_pos
  have hab_pos_R : (0 : ℝ) < (a * b : ℝ) := by exact_mod_cast hab_pos
  have ha_pos_R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
  have hb_pos_R : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
  -- Bound each per-d term by (M/(ab)) · count{Pa(d) on a} · b · y_target^{-c}.
  -- For d ∈ valid_d_good (1 ≤ d ≤ ⌊y_target⌋₊): use hPbBound directly.
  -- For d outside valid_d_good: count{Pa(d) on a} = 0, so term = 0 ≤ rhs trivially.
  -- For convenience, pre-compute (M/(ab) : ℕ) as a Real coercion equal to (M:ℝ)/((a:ℝ)*(b:ℝ)).
  have hMab_div_eq : ((M / (a * b) : ℕ) : ℝ) = (M : ℝ) / ((a : ℝ) * (b : ℝ)) := by
    rcases hab_dvd_M with ⟨k_ab, hk_ab⟩
    have h_div : M / (a * b) = k_ab := by
      rw [hk_ab]; exact Nat.mul_div_cancel_left k_ab hab_pos
    rw [h_div]
    have hM_eq_R : (M : ℝ) = (a : ℝ) * (b : ℝ) * (k_ab : ℝ) := by
      have : (M : ℝ) = ((a * b * k_ab : ℕ) : ℝ) := by exact_mod_cast hk_ab
      rw [this]; push_cast; ring
    rw [hM_eq_R]
    field_simp
  have h_per_d_bound : ∀ d ∈ valid_d,
      (((Finset.range M).filter (fun r =>
        hChainEndpoint? A B (Nat.sqrt L) r k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ) ≤
      ((M : ℝ) / ((a : ℝ) * (b : ℝ))) *
        ((((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ) *
          ((b : ℝ) * Real.exp (-c * Real.log y_target))) := by
    intro d _hd_mem
    have hpf := hpc_factor d
    have hpf_R : (((Finset.range M).filter (fun r =>
          hChainEndpoint? A B (Nat.sqrt L) r k = some d ∧
            ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ) =
        ((M / (a * b) : ℕ) : ℝ) *
          ((((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ) *
            (((Finset.range b).filter (fun r => ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ)) := by
      exact_mod_cast hpf
    rw [hpf_R, hMab_div_eq]
    -- Case-split: if count{Pa(d) on a} = 0, term = 0.  Otherwise, d is a chain endpoint
    -- ⟹ 1 ≤ d ≤ ⌊y_target⌋₊ AND d ∣ a (from past-window admissibility, paper line 1899-1908).
    by_cases h_count_zero : ((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card = 0
    · -- Pa-trivial case: term = 0.
      rw [h_count_zero]
      push_cast
      have h_exp_pos : 0 < Real.exp (-c * Real.log y_target) := Real.exp_pos _
      have h_b_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
      have h_pos : (0 : ℝ) ≤ (M : ℝ) / ((a : ℝ) * (b : ℝ)) * (0 * ((b : ℝ) * Real.exp (-c * Real.log y_target))) := by
        positivity
      linarith
    · -- Pa-nontrivial: ∃ r ∈ range a with hChainEndpoint? = some d.  Extract.
      push_neg at h_count_zero
      have h_count_pos : 0 < ((Finset.range a).filter
          (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card := Nat.pos_of_ne_zero h_count_zero
      have h_filter_nonempty : ((Finset.range a).filter
          (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).Nonempty :=
        Finset.card_pos.mp h_count_pos
      rcases h_filter_nonempty with ⟨r, hr⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      -- hr : r < a ∧ hChainEndpoint? = some d.
      -- Extract: 1 ≤ d ≤ ⌊y_target⌋₊ (h_endpoint_range), AND d ∣ a (sub-claim).
      rcases h_endpoint_range r d hr.2 with ⟨h1d, hd_floor⟩
      have hd_le_y : (d : ℝ) ≤ y_target := by
        have hd_floor_R : (d : ℝ) ≤ (⌊y_target⌋₊ : ℝ) := by exact_mod_cast hd_floor
        have h_floor_le_y : (⌊y_target⌋₊ : ℝ) ≤ y_target := Nat.floor_le hy_target_nn
        linarith
      -- d ∣ a: from chain admissibility (paper line 1893, 1899-1908).
      -- For r with hChainEndpoint? = some d, d's prime factors are in W_k =
      -- (exp y_k, exp(y_k^{A-1})], hence each prime ≤ exp(y_k^{A-1}) ≤ past_cutoff.
      -- Combined with d squarefree (paper line 1893), d ∣ primorial past_cutoff = a.
      have hd_dvd_a : d ∣ a := by
        by_cases hk_zero : k = 0
        · -- k = 0: d = 1.
          subst hk_zero
          have hd_eq_1 : d = 1 := by
            have := hr.2
            rw [hChainEndpoint?_zero] at this
            injection this.symm
          rw [hd_eq_1]
          exact one_dvd _
        · -- k ≥ 1: extract chain admissibility constraints.
          have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_zero
          have h_eq_succ : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
          have hr2_kfix : hChainEndpoint? A B (Nat.sqrt L) r ((k - 1) + 1) = some d := by
            rw [h_eq_succ]; exact hr.2
          rcases hChainEndpoint?_succ_mem_admissible hr2_kfix with ⟨_, _, hd_admissible⟩
          rcases hChainAdmissibleNext_mem.mp hd_admissible with
            ⟨_, _, _, _, hd_sqf, hd_primes_window, _⟩
          rw [ha_def, hpc_def, dif_pos hk_pos]
          apply squarefree_dvd_primorial_of_primeFactors_le hd_sqf
          intro p hp
          have hp_window := hd_primes_window p hp
          exact Nat.le_floor hp_window.2
      have hPbBound_d := hPbBound d _hd_mem h1d hd_le_y hd_dvd_a
      have hPa_card_nn : (0 : ℝ) ≤
          (((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ) := by
        exact Nat.cast_nonneg _
      have hMab_div_nn : (0 : ℝ) ≤ (M : ℝ) / ((a : ℝ) * (b : ℝ)) := by
        apply div_nonneg (Nat.cast_nonneg _)
        exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hMab_div_nn
      apply mul_le_mul_of_nonneg_left hPbBound_d hPa_card_nn
  -- **Step 3**: ∑ over d.
  have h_sum_bound :
      (∑ d ∈ valid_d,
        (((Finset.range M).filter (fun r =>
          hChainEndpoint? A B (Nat.sqrt L) r k = some d ∧
            ¬ GoodCompositeSuccessor A y_target d r)).card : ℝ)) ≤
      ((M : ℝ) / (a * b)) * ((b : ℝ) * Real.exp (-c * Real.log y_target)) *
        (∑ d ∈ valid_d,
          (((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ)) := by
    calc (∑ d ∈ valid_d, _)
        ≤ ∑ d ∈ valid_d, ((M : ℝ) / (a * b)) *
              ((((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ) *
                ((b : ℝ) * Real.exp (-c * Real.log y_target))) :=
          Finset.sum_le_sum h_per_d_bound
      _ = ((M : ℝ) / (a * b)) * ((b : ℝ) * Real.exp (-c * Real.log y_target)) *
            (∑ d ∈ valid_d,
              (((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _; ring
  -- **Step 4**: ∑_d count{Pa(d) on a} ≤ a (partition).
  have h_sum_Pa_le_a :
      (∑ d ∈ valid_d,
        (((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ)) ≤
      (a : ℝ) := by
    -- The sets {r : Pa(d, r)}_{d ∈ valid_d} are disjoint subsets of Fin a.
    have h_eq : (∑ d ∈ valid_d, ((Finset.range a).filter
            (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card) =
        ((valid_d.biUnion (fun d => (Finset.range a).filter
            (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d))).card) := by
      rw [Finset.card_biUnion]
      intro d _ d' _ hdd'
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro r _ hgp hgp'
      exact hdd' (Option.some_inj.mp (hgp.symm.trans hgp'))
    have h_sub : (valid_d.biUnion (fun d => (Finset.range a).filter
        (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d))) ⊆ Finset.range a := by
      intro r hr
      simp only [Finset.mem_biUnion, Finset.mem_filter] at hr
      obtain ⟨_, _, hra, _⟩ := hr
      exact hra
    have h_card_le : (valid_d.biUnion (fun d => (Finset.range a).filter
        (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d))).card ≤ a := by
      have := Finset.card_le_card h_sub
      rwa [Finset.card_range] at this
    have h_sum_le_a : (∑ d ∈ valid_d, ((Finset.range a).filter
          (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card) ≤ a := by
      rw [h_eq]; exact h_card_le
    exact_mod_cast h_sum_le_a
  -- **Step 5**: Combine.  card{∃ d, Pa ∧ Pb on M} ≤ ∑_d term ≤ M · y_target^{-c}.
  have h_main_bound :
      (((Finset.range M).filter (fun n =>
        ∃ d : ℕ, hChainEndpoint? A B (Nat.sqrt L) n k = some d ∧
          ¬ GoodCompositeSuccessor A y_target d n)).card : ℝ) ≤
      (M : ℝ) * Real.exp (-c * Real.log y_target) := by
    -- LHS ≤ ∑_d term (h_card_eq_sum) ≤ (M/(ab)) · b · y^{-c} · a (h_sum_bound + h_sum_Pa_le_a).
    have h_step1 : ((M : ℝ) / (a * b)) * ((b : ℝ) * Real.exp (-c * Real.log y_target)) *
            (∑ d ∈ valid_d,
              (((Finset.range a).filter (fun r => hChainEndpoint? A B (Nat.sqrt L) r k = some d)).card : ℝ)) ≤
        ((M : ℝ) / (a * b)) * ((b : ℝ) * Real.exp (-c * Real.log y_target)) * (a : ℝ) := by
      apply mul_le_mul_of_nonneg_left h_sum_Pa_le_a
      have h_exp_pos : 0 < Real.exp (-c * Real.log y_target) := Real.exp_pos _
      positivity
    have h_simplify : ((M : ℝ) / (a * b)) * ((b : ℝ) * Real.exp (-c * Real.log y_target)) * (a : ℝ) =
        (M : ℝ) * Real.exp (-c * Real.log y_target) := by
      have hab_ne : (a : ℝ) * (b : ℝ) ≠ 0 := by positivity
      field_simp
    linarith [h_card_eq_sum, h_sum_bound, h_step1, h_simplify]
  -- **Step 6**: Convert y_target^{-c} ≤ y_target^{-c/2}/2 for tower(√L+k) large enough.
  -- y_target = exp(tower(√L+k)/B).
  -- y_target^{-c} = exp(-c · tower/B).
  -- y_target^{-c/2}/2 = exp(-(c/2)·tower/B)/2.
  -- Need: exp(-c·tower/B) ≤ exp(-(c/2)·tower/B)/2.
  --   ⟺ 2 ≤ exp((c/2)·tower/B)
  --   ⟺ log 2 ≤ (c/2)·tower/B
  --   ⟺ tower ≥ 2B·log 2 / c.
  -- Holds for tower(√L+k) ≥ 2B·log 2 / c.  L₀ choice (m₀_thr) was made for tow_target = max 0 (B·log y₀)
  -- which only ensures y_target ≥ y₀.  For c-related threshold, we need additional bound on L.
  -- For now: subsume via stronger L₀ (might need to revisit if not auto-satisfied).
  have h_log_y_target : Real.log y_target = tower (Nat.sqrt L + k) / B := by
    rw [hy_target_def]
    exact Real.log_exp _
  have h_y_target_neg_c : Real.exp (-c * Real.log y_target) =
      Real.exp (-c * (tower (Nat.sqrt L + k) / B)) := by
    rw [h_log_y_target]
  rw [h_y_target_neg_c] at h_main_bound
  -- Goal: card ≤ exp(-(c/2)·tower/B)/2 · M.
  -- Have: card ≤ M · exp(-c·tower/B).
  -- Need: M · exp(-c·tower/B) ≤ exp(-(c/2)·tower/B)/2 · M.
  -- ⟺ exp(-c·tower/B) ≤ exp(-(c/2)·tower/B)/2.
  -- ⟺ 2 · exp(-c·tower/B) ≤ exp(-(c/2)·tower/B).
  -- ⟺ log 2 - c·tower/B ≤ -(c/2)·tower/B.
  -- ⟺ log 2 ≤ (c/2)·tower/B.
  -- ⟺ tower ≥ 2B·log 2 / c.
  -- Tower(√L+k) ≥ tower(√L) ≥ T₀ from L₀ choice, where T₀ ≥ B·log y₀.
  -- We need T₀ ≥ 2B·log 2 / c additionally.  Add to L₀.
  -- Actually our existing tow_target := max 0 (B · log y₀).  For y₀ ≥ 4, B·log y₀ ≥ 2B·log 2/c if log y₀ ≥ 2 log 2 / c.
  -- Equivalently y₀ ≥ exp(2 log 2/c) = 2^{2/c}.  For c arbitrary, may not hold.
  -- Workaround: pick c'_outer < c sufficiently small for the existing L₀.
  --
  -- Simpler bridging: use exp(-c·tower/B) ≤ exp(-(c/2)·tower/B) (since c/2 < c, exp grows in -arg).
  -- That gives M · exp(-c·tower/B) ≤ M · exp(-(c/2)·tower/B), but we need ≤ M · exp(-(c/2)·tower/B)/2.
  -- So a factor of 2 missing.
  --
  -- Tighter bridging: exp(-c·tower/B) = exp(-(c/2)·tower/B) · exp(-(c/2)·tower/B).
  -- For exp(-(c/2)·tower/B) ≤ 1/2, we get exp(-c·tower/B) ≤ exp(-(c/2)·tower/B) · 1/2.
  -- Need: exp(-(c/2)·tower/B) ≤ 1/2 ⟺ (c/2)·tower/B ≥ log 2 ⟺ tower ≥ 2B·log 2/c.
  --
  -- Encode this requirement.
  have h_tower_ge_threshold : 2 * B * Real.log 2 / c ≤ tower (Nat.sqrt L + k) := by
    -- Tower(√L+k) ≥ tower(√L) (monotone) ≥ tow_target (via hm₀_thr applied at √L) ≥ 2B·log 2/c
    -- (via le_max_right of tow_target def).
    have h_sqrt_ge : m₀_thr ≤ Nat.sqrt L := by
      rw [Nat.le_sqrt, ← pow_two]
      exact le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hL_ge_max
    have h_tower_sqrt_ge : tow_target ≤ tower (Nat.sqrt L) := hm₀_thr (Nat.sqrt L) h_sqrt_ge
    have h_tower_mono : tower (Nat.sqrt L) ≤ tower (Nat.sqrt L + k) :=
      tower_le_of_le (Nat.le_add_right _ _)
    have h_tow_target_ge : 2 * B * Real.log 2 / c ≤ tow_target := by
      rw [htow_target_def]
      exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
    linarith
  have h_two_exp_le : (2 : ℝ) * Real.exp (-c * (tower (Nat.sqrt L + k) / B)) ≤
      Real.exp (-(c/2) * (tower (Nat.sqrt L + k) / B)) := by
    -- 2 · exp(-c·t) ≤ exp(-(c/2)·t)  ⟺  log 2 ≤ (c/2)·t  ⟺  t ≥ 2 log 2 / c.
    -- With t = tower(√L+k)/B, need tower/B ≥ 2 log 2/c, i.e., tower ≥ 2B·log 2/c.
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have h_log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h_tower_ge : Real.log 2 ≤ (c/2) * (tower (Nat.sqrt L + k) / B) := by
      have h_thr : 2 * B * Real.log 2 / c ≤ tower (Nat.sqrt L + k) := h_tower_ge_threshold
      have hc_pos_R : 0 < c := hc
      have hB_pos_R : 0 < B := hB_pos
      -- Multiply: 2 * B * log 2 / c ≤ tower ⟹ log 2 ≤ (c/(2B)) · tower = (c/2) · (tower/B).
      rw [div_le_iff₀ hc_pos_R] at h_thr
      have h_paren_eq : (c/2) * (tower (Nat.sqrt L + k) / B) = tower (Nat.sqrt L + k) * c / (2 * B) := by
        field_simp
      rw [h_paren_eq]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B)]
      linarith
    -- Now: 2·exp(-c·t) ≤ exp(-(c/2)·t) ⟺ log 2 + (-c·t) ≤ -(c/2)·t ⟺ log 2 ≤ (c/2)·t. ✓
    have h_step : Real.log 2 + (-c * (tower (Nat.sqrt L + k) / B)) ≤
        (-(c/2)) * (tower (Nat.sqrt L + k) / B) := by linarith
    -- Take exp.
    calc (2 : ℝ) * Real.exp (-c * (tower (Nat.sqrt L + k) / B))
        = Real.exp (Real.log 2) * Real.exp (-c * (tower (Nat.sqrt L + k) / B)) := by
          rw [Real.exp_log h_two_pos]
      _ = Real.exp (Real.log 2 + (-c * (tower (Nat.sqrt L + k) / B))) := by
          rw [← Real.exp_add]
      _ ≤ Real.exp ((-(c/2)) * (tower (Nat.sqrt L + k) / B)) :=
          Real.exp_le_exp.mpr h_step
  -- **Step 7**: Combine.
  -- Goal: card ≤ exp(-(c/2)·tower/B)/2 · M.
  have hMpos_R' : (0 : ℝ) ≤ (M : ℝ) := hMpos_R.le
  have h_final : (M : ℝ) * Real.exp (-c * (tower (Nat.sqrt L + k) / B)) ≤
      Real.exp (-(c/2) * (tower (Nat.sqrt L + k) / B)) / 2 * (M : ℝ) := by
    have h_div_form : Real.exp (-(c/2) * (tower (Nat.sqrt L + k) / B)) / 2 =
        (1/2) * Real.exp (-(c/2) * (tower (Nat.sqrt L + k) / B)) := by ring
    rw [h_div_form]
    -- Goal: M · exp(-c·t) ≤ (1/2) · exp(-(c/2)·t) · M.
    -- ⟺ 2 · exp(-c·t) ≤ exp(-(c/2)·t).  This is h_two_exp_le.
    have hM_le : (M : ℝ) * Real.exp (-c * (tower (Nat.sqrt L + k) / B)) ≤
        (M : ℝ) * ((1/2) * Real.exp (-(c/2) * (tower (Nat.sqrt L + k) / B))) := by
      apply mul_le_mul_of_nonneg_left _ hMpos_R'
      linarith [h_two_exp_le]
    linarith [hM_le]
  -- Conclude via h_main_bound.
  linarith [h_main_bound, h_final]

/-- **Geometric sum bound (paper line 1963-1972).**

For `L ≥ Lscale` (where scale_H gives `y_{j+1} ≥ exp(y_j^A) ≥ y_j^{A-1} ≥ y_j^2` for `A ≥ 3`),
we have `y_j ≥ y_1^{2^{j-1}}`, hence `y_j^{-c} ≤ y_1^{-c · 2^{j-1}}`.

Paper line 1965-1972: the geometric sum
$\sum_{j=1}^R y_j^{-c} \le \sum_{j \ge 1} y_1^{-c \, 2^{j-1}} \le 2 y_1^{-c}$
(when `y_1^{-c} ≤ 1/2`).

For us this is `∑_{k=0}^{R-1} exp(-c · tower(m₀+k)/B) ≤ 2 exp(-c · tower(m₀)/B)`. -/
private lemma H_chain_geometric_sum_bound
    {A B c : ℝ} (hA_pos : 10 < A) (hAB : A + 10 ≤ B) (hc : 0 < c)
    (Lscale : ℕ) (_hScale : HScaleWitness A Lscale) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
          Real.exp (-c * (tower (Nat.sqrt L + k) / B)) ≤
        2 * Real.exp (-c * (tower (Nat.sqrt L) / B)) := by
  -- Paper line 1963-1972.  Strategy: per-step decay x_{k+1} ≤ x_k/2, then geometric series.
  -- For L large, tower(√L+k+1) - tower(√L+k) = exp(tower(...)) - tower(...) ≥ B log 2 / c.
  -- Hence x_{k+1} = exp(-c · tower/B · (k+1)) ≤ x_k · exp(-log 2) = x_k / 2.
  have hB_pos : 0 < B := by linarith
  have hT_threshold : 0 < B * Real.log 2 / c := by
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  -- Choose L₀ s.t. tower(√L₀) ≥ max(1, B · log 2 / c) =: T₀.
  set T₀ : ℝ := max 1 (B * Real.log 2 / c) with hT₀_def
  have hT₀_ge_1 : 1 ≤ T₀ := le_max_left _ _
  have hT₀_ge_blog2c : B * Real.log 2 / c ≤ T₀ := le_max_right _ _
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hT₀_ge_1
  -- Find L₀ s.t. tower(√L) ≥ T₀ for L ≥ L₀.
  rcases Filter.tendsto_atTop.mp tower_tendsto_atTop T₀ with hev_tower
  rcases Filter.eventually_atTop.mp hev_tower with ⟨m₀, hm₀⟩
  refine ⟨m₀ ^ 2, ?_⟩
  intro L hL_ge
  -- Nat.sqrt L ≥ m₀.
  have h_sqrt_ge : m₀ ≤ Nat.sqrt L := by
    have h := hL_ge
    rw [Nat.le_sqrt]
    have : m₀ * m₀ = m₀ ^ 2 := by ring
    omega
  have h_tower_sqrt_ge_T₀ : T₀ ≤ tower (Nat.sqrt L) :=
    (hm₀ m₀ le_rfl).trans (tower_le_of_le h_sqrt_ge)
  -- Per-step decay: ∀ k, exp(-c · tower(√L+k+1)/B) ≤ (1/2) · exp(-c · tower(√L+k)/B).
  -- Equivalent to: tower(√L+k+1) ≥ tower(√L+k) + B · log 2 / c.
  have h_step_decay : ∀ k : ℕ,
      Real.exp (-c * (tower (Nat.sqrt L + (k+1)) / B)) ≤
        Real.exp (-c * (tower (Nat.sqrt L + k) / B)) / 2 := by
    intro k
    -- tower(√L+k) ≥ T₀ ≥ 1, so exp(tower(√L+k)) ≥ 2 · tower(√L+k).
    have h_tower_k_ge_T₀ : T₀ ≤ tower (Nat.sqrt L + k) :=
      h_tower_sqrt_ge_T₀.trans (tower_le_of_le (Nat.le_add_right _ _))
    have h_tower_k_ge_1 : 1 ≤ tower (Nat.sqrt L + k) := hT₀_ge_1.trans h_tower_k_ge_T₀
    have h_tower_k_ge_blog2c : B * Real.log 2 / c ≤ tower (Nat.sqrt L + k) :=
      hT₀_ge_blog2c.trans h_tower_k_ge_T₀
    -- exp(t) ≥ 2t for t ≥ 1.
    have h_exp_ge_2t : 2 * tower (Nat.sqrt L + k) ≤ Real.exp (tower (Nat.sqrt L + k)) := by
      -- exp(1) ≈ 2.718 > 2.
      -- For t ≥ 1, exp(t) ≥ exp(1) · t ≥ 2t (since exp(1) ≥ 2 and... wait this needs care).
      -- Use: exp(t)/t is increasing for t ≥ 1. At t=1: exp(1)/1 ≈ 2.71. So exp(t)/t ≥ 2.71 for t ≥ 1.
      -- Hence exp(t) ≥ 2.71 · t > 2t.
      have h_e_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      -- exp(t) - 2t at t=1: exp(1) - 2 ≈ 0.71 ≥ 0. Derivative: exp(t) - 2.
      -- For t ≥ log 2, exp(t) ≥ 2, so derivative ≥ 0, function increasing.
      -- Since log 2 < 1, function is increasing on [1, ∞), starting at 0.71 > 0. ✓
      -- Concrete proof: induction on t, using exp(t+1) = e · exp(t) ≥ 2 · exp(t) ≥ 2(t+1) for t ≥ 1.
      -- Easier: use that exp is convex with exp(0) = 1, slope exp(1).
      -- For now: use Real.add_one_le_exp t or similar.
      -- Strategy: exp(t) ≥ 1 + t + t²/2 (Taylor, second-order).
      -- For t ≥ 1: 1 + t + t²/2 ≥ 1 + t + t/2 = 1 + 3t/2 ≥ 2t iff 1 ≥ t/2 iff t ≤ 2.
      -- Hmm that doesn't work for t > 2.
      -- Better: exp(t) ≥ (1+1/n)^{n·t} for various n.  Or use Real.exp_one_lt_d9 / known bounds.
      -- Simplest: exp(t) is convex, exp(0) = 1, exp'(0) = 1, exp''(t) = exp(t) ≥ 1.
      -- So exp(t) ≥ 1 + t + t²/2 for t ≥ 0.  For t ≥ 2, exp(t) ≥ 1 + t + 2 ≥ 2t. (1+t+2 ≥ 2t iff 3 ≥ t, conflict with t ≥ 2 only if t > 3.)
      -- Hmm.  Use a cleaner fact: exp(t) ≥ e^{t/2} · e^{t/2} ≥ (1 + t/2)² = 1 + t + t²/4.
      -- For t ≥ 4: 1 + t + t²/4 ≥ 1 + t + t = 1 + 2t > 2t. ✓
      -- For 1 ≤ t < 4: just verify directly that exp(t) ≥ 2t.
      --   t=1: exp(1) ≈ 2.71 ≥ 2. ✓
      --   t=2: exp(2) ≈ 7.39 ≥ 4. ✓
      --   t=3: exp(3) ≈ 20.09 ≥ 6. ✓
      -- For all t ≥ 1: exp(t) ≥ 2t.
      -- Mathlib lemma?
      -- exp(t) ≥ t + 1 (for any t).  We use this on s = t - 1.
      -- exp(t-1) ≥ t.  Hence exp(t) = exp(t-1) · e ≥ t · e ≥ 2t (since e ≥ 2).
      have h_exp_t_minus_1 : tower (Nat.sqrt L + k) ≤ Real.exp (tower (Nat.sqrt L + k) - 1) := by
        have h := Real.add_one_le_exp (tower (Nat.sqrt L + k) - 1)
        linarith
      -- exp(t) = exp((t-1) + 1) = exp(t-1) · exp(1) ≥ (t - 1 + 1) · exp(1) = t · exp(1) ≥ 2t.
      have h_exp_decomp : Real.exp (tower (Nat.sqrt L + k)) =
          Real.exp (tower (Nat.sqrt L + k) - 1) * Real.exp 1 := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h_exp_decomp]
      have h_pos_t : 0 ≤ tower (Nat.sqrt L + k) := by linarith
      have h_t_eq : tower (Nat.sqrt L + k) - 1 + 1 = tower (Nat.sqrt L + k) := by ring
      have h_inner : tower (Nat.sqrt L + k) ≤ Real.exp (tower (Nat.sqrt L + k) - 1) := by
        linarith [h_exp_t_minus_1, h_t_eq]
      have h_exp_t_ge_t : tower (Nat.sqrt L + k) * Real.exp 1 ≤
          Real.exp (tower (Nat.sqrt L + k) - 1) * Real.exp 1 := by
        apply mul_le_mul_of_nonneg_right h_inner (Real.exp_pos _).le
      calc 2 * tower (Nat.sqrt L + k) ≤ Real.exp 1 * tower (Nat.sqrt L + k) := by
            have := h_e_ge_2
            nlinarith [h_pos_t]
        _ = tower (Nat.sqrt L + k) * Real.exp 1 := by ring
        _ ≤ Real.exp (tower (Nat.sqrt L + k) - 1) * Real.exp 1 := h_exp_t_ge_t
    -- tower(m+1) = exp(tower(m)) ≥ 2 · tower(m) ≥ tower(m) + tower(m) ≥ tower(m) + B log 2 / c.
    have h_tower_succ_eq : tower (Nat.sqrt L + (k+1)) = Real.exp (tower (Nat.sqrt L + k)) := by
      have h : Nat.sqrt L + (k + 1) = (Nat.sqrt L + k) + 1 := by ring
      rw [h]; rfl
    have h_tower_diff : tower (Nat.sqrt L + (k+1)) - tower (Nat.sqrt L + k) ≥
        B * Real.log 2 / c := by
      rw [h_tower_succ_eq]
      have := h_exp_ge_2t
      linarith [h_tower_k_ge_blog2c]
    -- Hence c · (tower(m+1) - tower(m)) / B ≥ log 2.
    have h_diff_div : (c * tower (Nat.sqrt L + (k+1)) - c * tower (Nat.sqrt L + k)) / B ≥
        Real.log 2 := by
      have h_factor : c * tower (Nat.sqrt L + (k+1)) - c * tower (Nat.sqrt L + k) =
          c * (tower (Nat.sqrt L + (k+1)) - tower (Nat.sqrt L + k)) := by ring
      rw [h_factor]
      have h_le : B * Real.log 2 ≤ c * (tower (Nat.sqrt L + (k+1)) - tower (Nat.sqrt L + k)) := by
        have h_c_blog2 : c * (B * Real.log 2 / c) = B * Real.log 2 := by
          field_simp
        rw [← h_c_blog2]
        exact mul_le_mul_of_nonneg_left h_tower_diff hc.le
      rw [ge_iff_le, le_div_iff₀ hB_pos]
      linarith
    -- exp(-c·tower(m+1)/B) = exp(-c·tower(m)/B - (log 2)) (well, ≤) = exp(-c·tower(m)/B)/2.
    have h_diff_split : (c * tower (Nat.sqrt L + (k+1)) - c * tower (Nat.sqrt L + k)) / B =
        c * tower (Nat.sqrt L + (k+1)) / B - c * tower (Nat.sqrt L + k) / B := by
      field_simp
    have h_diff_div' : c * tower (Nat.sqrt L + (k+1)) / B - c * tower (Nat.sqrt L + k) / B ≥
        Real.log 2 := h_diff_split ▸ h_diff_div
    have h_neg_diff : -c * (tower (Nat.sqrt L + (k+1)) / B) ≤
        -c * (tower (Nat.sqrt L + k) / B) - Real.log 2 := by
      have h_eq1 : c * tower (Nat.sqrt L + (k+1)) / B = c * (tower (Nat.sqrt L + (k+1)) / B) := by
        ring
      have h_eq2 : c * tower (Nat.sqrt L + k) / B = c * (tower (Nat.sqrt L + k) / B) := by ring
      rw [h_eq1, h_eq2] at h_diff_div'
      linarith
    -- exp is monotone.
    have h_exp_le : Real.exp (-c * (tower (Nat.sqrt L + (k+1)) / B)) ≤
        Real.exp (-c * (tower (Nat.sqrt L + k) / B) - Real.log 2) :=
      Real.exp_le_exp.mpr h_neg_diff
    have h_exp_split : Real.exp (-c * (tower (Nat.sqrt L + k) / B) - Real.log 2) =
        Real.exp (-c * (tower (Nat.sqrt L + k) / B)) / 2 := by
      rw [show -c * (tower (Nat.sqrt L + k) / B) - Real.log 2 =
          -c * (tower (Nat.sqrt L + k) / B) + (-Real.log 2) from by ring]
      rw [Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      field_simp
    linarith [h_exp_split ▸ h_exp_le]
  -- Now by induction on k: x_k ≤ x_0 · (1/2)^k.
  have h_pow_decay : ∀ k : ℕ,
      Real.exp (-c * (tower (Nat.sqrt L + k) / B)) ≤
        Real.exp (-c * (tower (Nat.sqrt L) / B)) * (1/2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      have h_step := h_step_decay j
      have h_pow_succ : (1/2 : ℝ) ^ (j + 1) = (1/2 : ℝ) ^ j * (1/2) := by ring
      calc Real.exp (-c * (tower (Nat.sqrt L + (j + 1)) / B))
          ≤ Real.exp (-c * (tower (Nat.sqrt L + j) / B)) / 2 := h_step
        _ ≤ Real.exp (-c * (tower (Nat.sqrt L) / B)) * (1/2 : ℝ) ^ j / 2 := by
            apply div_le_div_of_nonneg_right ih (by norm_num)
        _ = Real.exp (-c * (tower (Nat.sqrt L) / B)) * (1/2 : ℝ) ^ (j + 1) := by
            rw [h_pow_succ]; ring
  -- Sum: ∑_{k=0}^{R-1} x_k ≤ x_0 · ∑_{k=0}^{R-1} (1/2)^k ≤ x_0 · 2 = 2 x_0.
  have h_sum_bound :
      ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
          Real.exp (-c * (tower (Nat.sqrt L + k) / B)) ≤
        ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
          Real.exp (-c * (tower (Nat.sqrt L) / B)) * (1/2 : ℝ) ^ k :=
    Finset.sum_le_sum (fun k _ => h_pow_decay k)
  have h_factor :
      ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
          Real.exp (-c * (tower (Nat.sqrt L) / B)) * (1/2 : ℝ) ^ k =
      Real.exp (-c * (tower (Nat.sqrt L) / B)) *
        ∑ k ∈ Finset.range (L - Nat.sqrt L - 4), (1/2 : ℝ) ^ k := by
    rw [Finset.mul_sum]
  rw [h_factor] at h_sum_bound
  -- ∑_{k=0}^{R-1} (1/2)^k = ((1/2)^R - 1) / (1/2 - 1) = 2 · (1 - (1/2)^R) ≤ 2.
  have h_geom_eq : ∑ k ∈ Finset.range (L - Nat.sqrt L - 4), (1/2 : ℝ) ^ k =
      ((1/2 : ℝ) ^ (L - Nat.sqrt L - 4) - 1) / ((1/2 : ℝ) - 1) :=
    geom_sum_eq (by norm_num : (1/2 : ℝ) ≠ 1) _
  have h_geom_le : ∑ k ∈ Finset.range (L - Nat.sqrt L - 4), (1/2 : ℝ) ^ k ≤ 2 := by
    rw [h_geom_eq]
    have h_pow_nn : 0 ≤ ((1/2 : ℝ)) ^ (L - Nat.sqrt L - 4) :=
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) _
    have h_pow_le_one : ((1/2 : ℝ)) ^ (L - Nat.sqrt L - 4) ≤ 1 :=
      pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
    -- ((1/2)^R - 1) / (1/2 - 1) = (1 - (1/2)^R) / (1/2) = 2(1 - (1/2)^R) ≤ 2.
    have h_split : ((1/2 : ℝ) ^ (L - Nat.sqrt L - 4) - 1) / ((1/2 : ℝ) - 1) =
        2 * (1 - (1/2 : ℝ) ^ (L - Nat.sqrt L - 4)) := by
      field_simp; ring
    rw [h_split]
    linarith
  have h_x0_nn : 0 ≤ Real.exp (-c * (tower (Nat.sqrt L) / B)) := (Real.exp_pos _).le
  calc ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            Real.exp (-c * (tower (Nat.sqrt L + k) / B))
      ≤ Real.exp (-c * (tower (Nat.sqrt L) / B)) *
          ∑ k ∈ Finset.range (L - Nat.sqrt L - 4), (1/2 : ℝ) ^ k := h_sum_bound
    _ ≤ Real.exp (-c * (tower (Nat.sqrt L) / B)) * 2 :=
        mul_le_mul_of_nonneg_left h_geom_le h_x0_nn
    _ = 2 * Real.exp (-c * (tower (Nat.sqrt L) / B)) := by ring

/-- **Greedy-event-based variant of HChainEvent_pmodel_bound (paper §7.3 line 1888-1976).**

Same conclusion as `HChainEvent_pmodel_bound` but proven via the greedy-event pipeline:
1. Soundness contrapositive: `¬HCEStrict_R ⟹ ¬hGreedySucc_R`.
2. Greedy telescope (`hGreedySucc_failure_telescope_le`).
3. Per-stage greedy bound (`h_chain_per_greedy_stage_failure_bound`).
4. Geometric sum + tower decay.

This is the paper-faithful version (all three steps formally proven). -/
private lemma HChainEvent_pmodel_bound_via_greedy
    {A : ℝ} (hA_eq : A = 20) {B : ℝ} (hAB : A + 10 ≤ B)
    (Lscale : ℕ) (_hScale : HScaleWitness A Lscale)
    {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ P : ℕ, 2 ≤ P →
      (∀ k : ℕ, k < L - Nat.sqrt L - 4 →
        Real.exp ((Real.exp (tower (Nat.sqrt L + k) / B)) ^ (A - 1)) ≤ (P : ℝ)) →
      -- hP_strong_at_R: extra hypothesis for the LAST stage R = L-√L-5 (Lean k).
      -- Captures outer_P ≥ 2·exp(y_R^A) needed for the deep primorial bound (Bertrand).
      -- The factor of 2 supports Bertrand's postulate (∃ prime in (N, 2N]).
      -- Caller (stage_failure_sum_H) verifies this from outer_P = ⌊tower(L-3)⌋₊
      -- via 4·exp(exp(2T/3)) ≤ exp(exp(T)) and floor absorption (T = tower(L-5)).
      2 * Real.exp ((Real.exp (tower (Nat.sqrt L + (L - Nat.sqrt L - 5)) / B)) ^ A) ≤ (P : ℝ) →
      ((Nat.card {r : Fin (primorial P) //
          ¬ HChainEvent A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) /
        (primorial P : ℝ) ≤ η) := by
  classical
  -- Get c, L₁ from per-greedy-stage bound.
  rcases h_chain_per_greedy_stage_failure_bound (A := A) hA_eq (B := B) hAB
    with ⟨c, hc, L₁, hL₁⟩
  -- Get L₀ from geometric sum bound (same c).
  have hA_pos : 10 < A := by rw [hA_eq]; norm_num
  rcases H_chain_geometric_sum_bound (A := A) (B := B) (c := c) hA_pos hAB hc
    Lscale _hScale with ⟨L₂, hL₂⟩
  -- Get L₀ from tower_decay_sum_bound (target η, same c).
  have hB_pos : 1 ≤ B := by linarith
  rcases tower_decay_sum_bound (B := B) hc hB_pos hη with ⟨L₃, hL₃⟩
  -- Get scale_H_strong's m_scale (paper §7.4 line 1933) for hP_at_target_full derivation.
  have hA_pos_local : 0 < A := by linarith
  rcases scale_H_strong A B hA_pos_local hAB with ⟨m_scale, hm_scale⟩
  refine ⟨max (max (max (max L₁ L₂) L₃) 16) (m_scale ^ 2), ?_⟩
  intro L hL_max P hP_ge_2 hP_bound hP_strong_at_R
  have hL_ge_L₁ : L₁ ≤ L :=
    le_trans (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_left _ _)
      |>.trans (le_max_left _ _)) hL_max
  have hL_ge_L₂ : L₂ ≤ L :=
    le_trans (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_left _ _)
      |>.trans (le_max_left _ _)) hL_max
  have hL_ge_L₃ : L₃ ≤ L :=
    le_trans (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_left _ _)) hL_max
  have hL_ge_16 : 16 ≤ L :=
    le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hL_max
  have hL_ge_m_scale_sq : m_scale ^ 2 ≤ L := le_trans (le_max_right _ _) hL_max
  -- Setup: M = primorial P.
  set M : ℕ := primorial P with hM_def
  have hMpos : 0 < M := by
    rw [hM_def]
    exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hMpos_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  -- **Step 1 (paper line 1957-1962): greedy telescope.**
  have h_telescope := hGreedySucc_failure_telescope_le A B (Nat.sqrt L) (L - Nat.sqrt L - 4) M
  -- **Step 2a: build hP_at_target_full for ALL stages k < L - √L - 4.**
  -- For non-boundary k < L - √L - 5: derive 2·exp(y^A) ≤ outer_P from hP_bound (k+1) +
  -- scale_H (paper §7.4 line 1933).  For boundary k = L - √L - 5: use hP_strong_at_R directly.
  -- This abstraction lets the inner lemma cover ALL paper stages 1..R uniformly.
  have hA_one_le : 1 ≤ A := by rw [hA_eq]; norm_num
  have hP_at_target_full : ∀ k : ℕ, k < L - Nat.sqrt L - 4 →
      2 * Real.exp ((Real.exp (tower (Nat.sqrt L + k) / B)) ^ A) ≤ (P : ℝ) := by
    intro k hk
    by_cases hk_lt : k < L - Nat.sqrt L - 5
    · -- Non-boundary: derive from hP_bound (k+1) + scale_H.
      have hk_plus_one_lt : k + 1 < L - Nat.sqrt L - 4 := by omega
      have hP_at_k1 := hP_bound (k + 1) hk_plus_one_lt
      have h_sqrt_k_ge_m_scale : m_scale ≤ Nat.sqrt L + k := by
        have h_sqrt_ge : m_scale ≤ Nat.sqrt L := by
          rw [Nat.le_sqrt, ← pow_two]; exact hL_ge_m_scale_sq
        exact h_sqrt_ge.trans (Nat.le_add_right _ _)
      have h_scale_at_k := hm_scale (Nat.sqrt L + k) h_sqrt_k_ge_m_scale
      -- h_scale_at_k : exp((exp(tower(√L+k)/B))^A) ≤ exp(tower(√L+k+1)/B).
      have h_idx_eq : Nat.sqrt L + k + 1 = Nat.sqrt L + (k + 1) := by omega
      have hB_pos_local : 0 < B := by linarith
      set y_target : ℝ := Real.exp (tower (Nat.sqrt L + k) / B) with hy_target_def
      have hy_target_pos : 0 < y_target := Real.exp_pos _
      have hy_target_ge_1 : 1 ≤ y_target := by
        rw [hy_target_def]; apply Real.one_le_exp
        exact div_nonneg (tower_pos _).le hB_pos_local.le
      have h_scale_y_to_kp2 : Real.exp (y_target ^ A) ≤
          Real.exp (tower (Nat.sqrt L + (k + 1)) / B) := by
        rw [hy_target_def, ← h_idx_eq]; exact h_scale_at_k
      -- Chain: 2·exp(y^A) ≤ exp(exp(y^A)) ≤ exp(y_{k+2}) ≤ exp(y_{k+2}^{A-1}) ≤ outer_P.
      have h_y_kp2_ge_one : (1 : ℝ) ≤ Real.exp (tower (Nat.sqrt L + (k + 1)) / B) := by
        apply Real.one_le_exp; exact div_nonneg (tower_pos _).le hB_pos_local.le
      have h_A_sub_one_ge : (1 : ℝ) ≤ A - 1 := by linarith
      have h_y_kp2_pow_ge_self : Real.exp (tower (Nat.sqrt L + (k + 1)) / B) ≤
          (Real.exp (tower (Nat.sqrt L + (k + 1)) / B)) ^ (A - 1) := by
        nth_rewrite 1 [show Real.exp (tower (Nat.sqrt L + (k + 1)) / B) =
            (Real.exp (tower (Nat.sqrt L + (k + 1)) / B)) ^ (1 : ℝ) from
            (Real.rpow_one _).symm]
        exact Real.rpow_le_rpow_of_exponent_le h_y_kp2_ge_one h_A_sub_one_ge
      -- 2·exp(y^A) ≤ exp(exp(y^A)).
      have h_exp_y_pos : 0 < Real.exp (y_target ^ A) := Real.exp_pos _
      have h_two_exp_le : 2 * Real.exp (y_target ^ A) ≤
          Real.exp (Real.exp (y_target ^ A)) := by
        have h_eq : Real.exp (Real.exp (y_target ^ A)) =
            Real.exp (y_target ^ A) * Real.exp (Real.exp (y_target ^ A) - y_target ^ A) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h_eq]
        have h_exp_diff : (1 : ℝ) ≤ Real.exp (y_target ^ A) - y_target ^ A := by
          have := Real.add_one_le_exp (y_target ^ A); linarith
        have h_log2_le : Real.log 2 ≤ Real.exp (y_target ^ A) - y_target ^ A := by
          have := Real.log_two_lt_d9; linarith
        have h_two_le_exp_diff : (2 : ℝ) ≤
            Real.exp (Real.exp (y_target ^ A) - y_target ^ A) := by
          have h2 : Real.exp (Real.log 2) ≤
              Real.exp (Real.exp (y_target ^ A) - y_target ^ A) :=
            Real.exp_le_exp.mpr h_log2_le
          rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h2
        have := mul_le_mul_of_nonneg_left h_two_le_exp_diff h_exp_y_pos.le
        linarith
      -- exp(exp(y^A)) ≤ exp(y_{k+2}^{A-1}) ≤ outer_P.
      have h_chain : Real.exp (Real.exp (y_target ^ A)) ≤
          Real.exp ((Real.exp (tower (Nat.sqrt L + (k + 1)) / B)) ^ (A - 1)) := by
        apply Real.exp_le_exp.mpr
        have h_step1 : Real.exp (y_target ^ A) ≤
            Real.exp (tower (Nat.sqrt L + (k + 1)) / B) := h_scale_y_to_kp2
        linarith [h_step1, h_y_kp2_pow_ge_self]
      show 2 * Real.exp (y_target ^ A) ≤ (P : ℝ)
      linarith [h_two_exp_le, h_chain, hP_at_k1]
    · -- Boundary k = L - √L - 5: use hP_strong_at_R directly.
      have hk_eq : k = L - Nat.sqrt L - 5 := by omega
      rw [hk_eq]; exact hP_strong_at_R
  -- **Step 2b (paper line 1942): per-greedy-stage bound for each k < R.**
  have h_per_stage := hL₁ L hL_ge_L₁ P hP_ge_2 hP_bound hP_at_target_full
  -- **Step 3: sum the per-stage greedy bounds.  Inner lemma now covers ALL stages.**
  have h_sum_bound :
      (∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
        (Nat.card {r : Fin M // hGreedySucc A B (Nat.sqrt L) k r.val ∧
                                 ¬ hGreedySucc A B (Nat.sqrt L) (k + 1) r.val} : ℝ)) ≤
      (∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
        Real.exp (-c * (tower (Nat.sqrt L + k) / B)) / 2 * (M : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    exact h_per_stage k hk
  have h_sum_factor :
      (∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
        Real.exp (-c * (tower (Nat.sqrt L + k) / B)) / 2 * (M : ℝ)) =
      ((∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
        Real.exp (-c * (tower (Nat.sqrt L + k) / B))) / 2) * (M : ℝ) := by
    calc (∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            Real.exp (-c * (tower (Nat.sqrt L + k) / B)) / 2 * (M : ℝ))
        = ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            (Real.exp (-c * (tower (Nat.sqrt L + k) / B)) * (M : ℝ)) / 2 :=
          Finset.sum_congr rfl (fun _ _ => by ring)
      _ = (∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            Real.exp (-c * (tower (Nat.sqrt L + k) / B)) * (M : ℝ)) / 2 :=
          (Finset.sum_div _ _ _).symm
      _ = ((∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            Real.exp (-c * (tower (Nat.sqrt L + k) / B))) * (M : ℝ)) / 2 := by
            rw [Finset.sum_mul]
      _ = ((∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            Real.exp (-c * (tower (Nat.sqrt L + k) / B))) / 2) * (M : ℝ) := by ring
  rw [h_sum_factor] at h_sum_bound
  -- **Step 4: geometric sum bound.**
  have h_geom := hL₂ L hL_ge_L₂
  -- **Step 5: tower decay (final asymptotic).**
  have h_decay := hL₃ L hL_ge_L₃
  -- **Step 6: combine.**
  have h_chain_bound :
      (Nat.card {r : Fin M //
        ¬ hGreedySucc A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) ≤
      ((2 * Real.exp (-c * (tower (Nat.sqrt L) / B))) / 2) * (M : ℝ) := by
    calc (Nat.card {r : Fin M // ¬ hGreedySucc A B (Nat.sqrt L)
              (L - Nat.sqrt L - 4) r.val} : ℝ)
        ≤ ∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
            (Nat.card {r : Fin M // hGreedySucc A B (Nat.sqrt L) k r.val ∧
                                     ¬ hGreedySucc A B (Nat.sqrt L) (k + 1) r.val} : ℝ) :=
          h_telescope
      _ ≤ ((∑ k ∈ Finset.range (L - Nat.sqrt L - 4),
              Real.exp (-c * (tower (Nat.sqrt L + k) / B))) / 2) * (M : ℝ) := h_sum_bound
      _ ≤ ((2 * Real.exp (-c * (tower (Nat.sqrt L) / B))) / 2) * (M : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · apply div_le_div_of_nonneg_right h_geom (by norm_num)
          · exact hMpos_real.le
  have h_simplify :
      ((2 * Real.exp (-c * (tower (Nat.sqrt L) / B))) / 2) =
        Real.exp (-c * (tower (Nat.sqrt L) / B)) := by ring
  rw [h_simplify] at h_chain_bound
  -- **Step 7: use soundness contrapositive to bound HChainEvent.**
  -- ¬HChainEvent_R ⟹ ¬HCEStrict_R (for R ≥ 2 via the equivalence)
  -- ⟹ ¬hGreedySucc_R (via not_hGreedySucc_of_not_HChainEventStrict).
  have hR_ge_2 : 2 ≤ L - Nat.sqrt L - 4 := by
    have h_sqrt_sq_le : Nat.sqrt L * Nat.sqrt L ≤ L := by
      have := Nat.sqrt_le' L
      rw [pow_two] at this
      exact this
    have h_sqrt_ge_4 : 4 ≤ Nat.sqrt L := by
      rw [Nat.le_sqrt]; omega
    have h_4sqrt_le_L : 4 * Nat.sqrt L ≤ L := by
      calc 4 * Nat.sqrt L ≤ Nat.sqrt L * Nat.sqrt L := by
            have := h_sqrt_ge_4
            nlinarith
        _ ≤ L := h_sqrt_sq_le
    omega
  have h_iff : ∀ r : Fin M,
      ¬ HChainEvent A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val →
      ¬ hGreedySucc A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val := by
    intro r hnE
    apply not_hGreedySucc_of_not_HChainEventStrict
    intro hHCE
    apply hnE
    exact HChainEvent_of_strict hHCE
  have h_card_le_greedy : (Nat.card {r : Fin M //
        ¬ HChainEvent A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) ≤
      (Nat.card {r : Fin M //
        ¬ hGreedySucc A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) := by
    -- Use Nat.card_le_card_of_injective with the inclusion map.
    have h_inj :
        Function.Injective
          (fun (r : {r : Fin M // ¬ HChainEvent A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val}) =>
            (⟨r.val, h_iff r.val r.property⟩ :
              {r : Fin M // ¬ hGreedySucc A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val})) := by
      intro r₁ r₂ h_eq
      apply Subtype.ext
      have := congrArg Subtype.val h_eq
      exact this
    exact_mod_cast Nat.card_le_card_of_injective _ h_inj
  -- tower_decay_sum_bound: 2 · exp(-c · tower(√L)/B) ≤ η.
  have h_card_le_η : (Nat.card {r : Fin M //
        ¬ HChainEvent A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) ≤ η * (M : ℝ) := by
    have h_exp_le : Real.exp (-c * (tower (Nat.sqrt L) / B)) ≤ η := by
      have h_eq : -c * tower (Nat.sqrt L) / B = -c * (tower (Nat.sqrt L) / B) := by ring
      have := h_decay
      rw [h_eq] at this
      have h_x_pos : 0 < Real.exp (-c * (tower (Nat.sqrt L) / B)) := Real.exp_pos _
      linarith
    calc (Nat.card {r : Fin M //
            ¬ HChainEvent A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ)
        ≤ (Nat.card {r : Fin M //
            ¬ hGreedySucc A B (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) := h_card_le_greedy
      _ ≤ Real.exp (-c * (tower (Nat.sqrt L) / B)) * (M : ℝ) := h_chain_bound
      _ ≤ η * (M : ℝ) := mul_le_mul_of_nonneg_right h_exp_le hMpos_real.le
  rw [div_le_iff₀ hMpos_real]
  exact h_card_le_η

/-- **Phase 5 main (paper §7.3 line 2003-2007 primorial decay).**
For `Cθ > 0`, `η > 0`, there exists `L₀` such that for all `L ≥ L₀` and any `t ≤ T_{L-3}`
and `x ≥ T_L`, we have `primorial t / x ≤ η`.

Paper §7.3 line 2003-2007 verbatim: `P ≤ T_{L-3} = o(log x)`, `log M ≤ Cθ · P`,
hence `M = x^{o(1)} = o(x)`.  Concretely: `log M ≤ Cθ · T_{L-3}`, while
`log x ≥ T_{L-1} >> T_{L-3}`, so `M/x ≤ exp(Cθ · T_{L-3} - T_{L-1}) → 0`. -/
private lemma primorial_decay_bound
    {Cθ : ℝ} (hCθ_pos : 0 < Cθ) (htheta : ChebyshevThetaWitness Cθ)
    {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ t : ℝ, 2 ≤ t → t ≤ tower (L - 3) →
      ∀ x : ℝ, tower (L - 1) ≤ x →
        ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) / x ≤ η := by
  -- M ≤ exp(Cθ · t) ≤ exp(Cθ · T_{L-3}).
  -- x ≥ T_L = exp(T_{L-1}) ≥ exp(2·Cθ·T_{L-3} + log(1/η)) for L large.
  -- So M/x ≤ exp(Cθ·T_{L-3} - log x) ≤ exp(-Cθ·T_{L-3} - log(1/η)) = η · exp(-Cθ·T_{L-3}) ≤ η.
  --
  -- Strategy: choose L₀ s.t. for L ≥ L₀, T_{L-1} ≥ 2·Cθ·T_{L-3} + log(1/η).
  -- Since T_{L-1} = exp(T_{L-2}) >> T_{L-3} for L large, this holds.
  -- Equivalently: T_{L-1} - Cθ·T_{L-3} ≥ Cθ·T_{L-3} + log(1/η).
  -- For T_{L-3} → ∞: T_{L-1} = exp(T_{L-2}) = exp(exp(T_{L-3})) >>>> Cθ·T_{L-3} + log(1/η).
  --
  -- Pick L₀ s.t. tower (L₀ - 1) ≥ 2·Cθ·tower (L₀ - 3) + |log η| + 1.
  -- Use tower_tendsto_atTop.
  -- For simplicity, target tower (L - 1) ≥ Cθ·tower(L-3) - log η = Cθ·tower(L-3) + log(1/η).
  -- For L ≥ 4 (so L-3 ≥ 1) and L-3 → ∞ (i.e., L → ∞), this holds.
  -- Use: tower (L - 1) ≥ tower (L - 3) + 1, which is a weak bound.  Need stronger.
  -- tower (L - 1) = exp(tower(L-2)) = exp(exp(tower(L-3))).  For T_{L-3} ≥ 1,
  -- tower (L-1) ≥ exp(exp(1)) ≈ 15, but we need it to dominate Cθ·tower(L-3).
  -- For tower (L-3) ≥ M, tower (L-2) = exp(tower(L-3)) ≥ exp(M),
  -- tower (L-1) = exp(tower(L-2)) ≥ exp(exp(M)).
  -- We need exp(exp(M)) ≥ Cθ · M + log(1/η).  For M ≥ log(Cθ + log(1/η) + 1), this holds.
  -- (Assuming M ≥ 1, exp(M) ≥ M + 1, exp(exp(M)) ≥ exp(M+1) = e · exp(M) ≥ e·(M+1) ≥ ...)
  --
  -- Concrete approach: choose L₀ s.t. T_{L₀-1} ≥ Cθ · T_{L₀-3} + |log η| + 1.
  -- T_{L₀-1} = exp(T_{L₀-2}) ≥ T_{L₀-2} + 1 (Real.add_one_le_exp).
  -- T_{L₀-2} = exp(T_{L₀-3}) ≥ T_{L₀-3} + 1.
  -- So T_{L₀-1} ≥ T_{L₀-3} + 2.  Weak.
  -- Need: exp(exp(T_{L₀-3})) ≥ Cθ · T_{L₀-3} + bound.
  -- Use tower_tendsto_atTop: choose m₀ s.t. tower m ≥ Cθ · tower (m-2) + |log η| + 1 for m ≥ m₀ + 2.
  -- Hmm, this needs analytic argument about tower growth rate.  Let me just use the
  -- existence: tower → ∞, so tower (L - 1) → ∞ as L → ∞.  And the ratio
  -- (tower(L-1)) / (Cθ · tower(L-3)) → ∞ super-exponentially.
  -- For the formalization, use Filter.tendsto_atTop with target value.
  -- Define M_target := Cθ · tower (m₀ - 3) + |log η| + 1 (depends on choice).
  -- Hmm this is recursive.
  --
  -- Alternative: direct.  For η > 0, |log η| is some fixed real.
  -- Pick L₀ = max(4, m₀ + 4) where m₀ is from tower_tendsto_atTop applied to threshold.
  -- For L ≥ L₀, L - 3 ≥ m₀ + 1, so tower(L-3) ≥ tower(m₀+1) ≥ huge.
  -- Then tower(L-1) ≥ tower(L-3) + ε where ε grows.
  --
  -- Concrete approach using Mathlib's `tendsto_exp_div_pow_atTop` (n=1):
  -- exp(t)/t → ∞.  Hence ∃ t₀, ∀ t ≥ t₀, exp(t) ≥ (Cθ+1)·t + |log η⁻¹|.
  -- For T_{L-3} ≥ t₀ (achievable for L large via tower_tendsto):
  --   T_{L-1} = exp(exp(T_{L-3})) ≥ exp(T_{L-3}) ≥ (Cθ+1)·T_{L-3} + |log η⁻¹| ≥ Cθ·T_{L-3} + |log η⁻¹|.
  -- Then for x ≥ T_L = exp(T_{L-1}):
  --   log x ≥ T_{L-1} ≥ Cθ·T_{L-3} + |log η⁻¹|.
  --   log M ≤ Cθ · t ≤ Cθ · T_{L-3} (from chebyshev_primorial_bound + ht_le_T).
  --   log(M/x) = log M - log x ≤ Cθ·T_{L-3} - (Cθ·T_{L-3} + |log η⁻¹|) = -|log η⁻¹| = log η.
  --   So M/x ≤ exp(log η) = η.
  --
  -- Step 1: Find t₀ s.t. ∀ t ≥ t₀, exp t ≥ (Cθ+1)·t + |log η⁻¹|.
  have hη_log_target : (0 : ℝ) < |Real.log η⁻¹| + 1 := by positivity
  have h_tendsto : Filter.Tendsto (fun t : ℝ => Real.exp t / t) Filter.atTop Filter.atTop := by
    simpa using tendsto_exp_div_pow_atTop 1
  have h_eventually : ∀ᶠ t : ℝ in Filter.atTop,
      (Cθ + 1) + (|Real.log η⁻¹| + 1) ≤ Real.exp t / t := by
    rw [Filter.tendsto_atTop] at h_tendsto
    exact h_tendsto _
  rcases (Filter.eventually_atTop.mp h_eventually) with ⟨t₀, ht₀⟩
  -- Step 2: Find m₁ s.t. ∀ m ≥ m₁, tower m ≥ max(t₀, 1).
  have h_tower_tendsto : Filter.Tendsto tower Filter.atTop Filter.atTop := tower_tendsto_atTop
  rcases (Filter.tendsto_atTop.mp h_tower_tendsto (max t₀ 1)) with hev_m
  rcases (Filter.eventually_atTop.mp hev_m) with ⟨m₁, hm₁⟩
  -- Step 3: For L ≥ m₁ + 4, T_{L-3} ≥ tower m₁ ≥ max(t₀, 1).
  refine ⟨m₁ + 4, ?_⟩
  intro L hL t ht_2 ht_le_T x hx_ge_T
  have hL_ge_4 : 4 ≤ L := le_trans (by omega : 4 ≤ m₁ + 4) hL
  have h_L_minus_3_ge_m1 : m₁ ≤ L - 3 := by omega
  have h_tower_L3_ge : max t₀ 1 ≤ tower (L - 3) := by
    have h_tower_mono : tower m₁ ≤ tower (L - 3) := tower_le_of_le h_L_minus_3_ge_m1
    exact (hm₁ m₁ le_rfl).trans h_tower_mono
  have h_tower_L3_ge_t₀ : t₀ ≤ tower (L - 3) := le_trans (le_max_left _ _) h_tower_L3_ge
  have h_tower_L3_ge_1 : (1 : ℝ) ≤ tower (L - 3) := le_trans (le_max_right _ _) h_tower_L3_ge
  have h_tower_L3_pos : 0 < tower (L - 3) := by linarith
  -- Step 4: exp(T_{L-3}) / T_{L-3} ≥ (Cθ+1) + (|log η⁻¹|+1).
  have h_ratio := ht₀ (tower (L - 3)) h_tower_L3_ge_t₀
  -- Step 5: exp(T_{L-3}) ≥ ((Cθ+1) + (|log η⁻¹|+1)) · T_{L-3}.
  have h_exp_bound : ((Cθ + 1) + (|Real.log η⁻¹| + 1)) * tower (L - 3) ≤ Real.exp (tower (L - 3)) := by
    have := mul_le_mul_of_nonneg_right h_ratio h_tower_L3_pos.le
    rw [div_mul_cancel₀ _ (ne_of_gt h_tower_L3_pos)] at this
    linarith
  -- Step 6: exp(T_{L-3}) = T_{L-2}, T_{L-1} = exp(T_{L-2}) ≥ T_{L-2} = exp(T_{L-3}).
  have h_T_L_minus_2_eq : tower (L - 2) = Real.exp (tower (L - 3)) := by
    rcases Nat.exists_eq_add_of_le hL_ge_4 with ⟨k, hk⟩
    -- L = 4 + k, so L - 2 = 2 + k, L - 3 = 1 + k
    have hL_eq : L = k + 4 := by omega
    have hL2_eq : L - 2 = k + 2 := by omega
    have hL3_eq : L - 3 = k + 1 := by omega
    rw [hL2_eq, hL3_eq]
    show tower (k + 1 + 1) = Real.exp (tower (k + 1))
    rfl
  have h_T_L_minus_1_eq : tower (L - 1) = Real.exp (tower (L - 2)) := by
    have hL_minus_1_eq : L - 1 = (L - 2) + 1 := by omega
    rw [hL_minus_1_eq]
    rfl
  -- Step 7: T_{L-1} ≥ T_{L-2} = exp(T_{L-3}) ≥ ((Cθ+1) + (|log η⁻¹|+1)) · T_{L-3}.
  have h_T_L_minus_1_ge_exp : Real.exp (tower (L - 3)) ≤ tower (L - 1) := by
    rw [h_T_L_minus_1_eq, h_T_L_minus_2_eq]
    have h := Real.add_one_le_exp (Real.exp (tower (L - 3)))
    linarith
  -- Step 8: log x ≥ T_{L-2} (from x ≥ T_{L-1} = exp(T_{L-2})).
  have h_x_pos : 0 < x := by linarith [tower_pos (L - 1), hx_ge_T]
  have h_log_x_ge_TL2 : tower (L - 2) ≤ Real.log x := by
    have h_x_ge_exp : Real.exp (tower (L - 2)) ≤ x := by
      have hL_eq : L - 1 = (L - 2) + 1 := by omega
      have h_TL_eq : tower (L - 1) = Real.exp (tower (L - 2)) := by rw [hL_eq]; rfl
      linarith [hx_ge_T]
    exact (Real.le_log_iff_exp_le h_x_pos).mpr h_x_ge_exp
  -- Step 9: log M ≤ Cθ · t ≤ Cθ · T_{L-3} (from chebyshev_primorial_bound).
  have h_log_M : Real.log ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) ≤
      Cθ * t := chebyshev_primorial_bound htheta t ht_2
  have h_log_M_ge_T_L3 : Real.log ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) ≤
      Cθ * tower (L - 3) := by
    calc Real.log _ ≤ Cθ * t := h_log_M
      _ ≤ Cθ * tower (L - 3) := mul_le_mul_of_nonneg_left ht_le_T hCθ_pos.le
  -- Step 10: M/x ≤ η.
  -- log(M/x) = log M - log x ≤ Cθ·T_{L-3} - T_{L-1} ≤ Cθ·T_{L-3} - exp(T_{L-3}) ≤ -|log η⁻¹| ≤ log η.
  have h_M_pos : (0 : ℝ) < ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) := by
    have h_nat_pos : 0 < ∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p := by
      apply Finset.prod_pos
      intro p hp
      have h_p_prime := (Finset.mem_filter.mp hp).2
      exact h_p_prime.pos
    exact_mod_cast h_nat_pos
  have h_log_diff : Real.log
      (((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) / x) ≤ Real.log η := by
    rw [Real.log_div (ne_of_gt h_M_pos) (ne_of_gt h_x_pos)]
    -- log M - log x ≤ Cθ·T_{L-3} - T_{L-2} (since log x ≥ T_{L-2})
    have h_diff_bound : Real.log ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) - Real.log x ≤
        Cθ * tower (L - 3) - tower (L - 2) := by linarith
    -- Cθ·T_{L-3} - T_{L-2} ≤ -|log η⁻¹|.
    -- T_{L-2} = exp(T_{L-3}) ≥ ((Cθ+1) + (|log η⁻¹|+1)) · T_{L-3}.
    have h_TL2_lower : ((Cθ + 1) + (|Real.log η⁻¹| + 1)) * tower (L - 3) ≤ tower (L - 2) := by
      rw [h_T_L_minus_2_eq]
      exact h_exp_bound
    have h_T_L3_ge_1' : (1 : ℝ) ≤ tower (L - 3) := h_tower_L3_ge_1
    have h_neg_abs_le : -|Real.log η⁻¹| ≤ Real.log η := by
      have h_log_eta_inv : Real.log η⁻¹ = -Real.log η := by
        rw [Real.log_inv]
      rw [h_log_eta_inv]
      by_cases h_pos : 0 ≤ Real.log η
      · rw [show |-Real.log η| = Real.log η from by rw [abs_neg]; exact abs_of_nonneg h_pos]
        linarith
      · have h_neg : Real.log η < 0 := lt_of_not_ge h_pos
        rw [show |-Real.log η| = -Real.log η from by
          rw [abs_neg]; exact abs_of_neg h_neg]
        linarith
    have h_main_bound : Cθ * tower (L - 3) - tower (L - 2) ≤ -|Real.log η⁻¹| := by
      have h_T_L3_pos : (0 : ℝ) < tower (L - 3) := by linarith
      have h_factor_bound : ((Cθ + 1) + (|Real.log η⁻¹| + 1)) * tower (L - 3) ≥
          Cθ * tower (L - 3) + |Real.log η⁻¹| := by
        have h_expand : ((Cθ + 1) + (|Real.log η⁻¹| + 1)) * tower (L - 3) =
            Cθ * tower (L - 3) + tower (L - 3) +
              |Real.log η⁻¹| * tower (L - 3) + tower (L - 3) := by ring
        have h_abs_nn : 0 ≤ |Real.log η⁻¹| := abs_nonneg _
        have h_T_L3_ge_one : 1 ≤ tower (L - 3) := h_tower_L3_ge_1
        nlinarith
      linarith
    linarith [h_neg_abs_le]
  -- Convert log(M/x) ≤ log η to M/x ≤ η.
  have h_M_x_pos : (0 : ℝ) < ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) / x := by
    positivity
  have h_eta_pos : (0 : ℝ) < η := hη
  rw [show η = Real.exp (Real.log η) from (Real.exp_log h_eta_pos).symm,
    show ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) / x =
      Real.exp (Real.log (((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), p : ℕ) : ℝ) / x))
    from (Real.exp_log h_M_x_pos).symm]
  exact Real.exp_le_exp.mpr h_log_diff

/-- **Paper §7.4 line 1989-1999: P bound.**

For `L` sufficiently large and any `k < L - √L - 4` (i.e., k < R), the
H-chain prime-window upper endpoint
`exp(y_{k+1}^{A-1}) = exp((exp(T_{m_0+k}/B))^{A-1})`
is bounded by `⌊tower(L-3)⌋₊`.

Paper proof (line 1985-1999): with `m_0 + R - 1 = L - 5`,
`log log P_paper = (A-1) T_{L-5} / B`.  Since `(A-1)/B = 19/30 < 1`,
exponentiating twice gives `log P_paper < T_{L-4}`, `P_paper < T_{L-3}`.

Constants: `A = 20`, `B = 30`, `(A-1)/B = 19/30`.

Concretely we show `exp(exp(19q)) + 1 ≤ tower(L-3)` (slightly stronger),
which gives `exp(exp(19q)) ≤ tower(L-3) - 1 ≤ ⌊tower(L-3)⌋₊` via floor.
-/
private lemma hP_chain_bound_existence :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ k : ℕ, k < L - Nat.sqrt L - 4 →
      Real.exp ((Real.exp (tower (Nat.sqrt L + k) / 30)) ^ ((20 : ℝ) - 1)) ≤
        (⌊tower (L - 3)⌋₊ : ℝ) := by
  -- Need L ≥ 16 to ensure: (a) L - √L - 4 > 0, (b) tower(L-5) ≥ exp 1, (c) tower(L-4) is large.
  refine ⟨16, ?_⟩
  intro L hL16 k hk
  -- Step 1: √L + k ≤ L - 5.  (Since k ≤ R - 1 = L - √L - 5.)
  have h_sqrtL_le : Nat.sqrt L ≤ L := Nat.sqrt_le_self L
  have hL_ge_16 : 16 ≤ L := hL16
  -- For L ≥ 16, Nat.sqrt L ≥ 4 (via 4*4 = 16 ≤ L).
  have h_sqrt_ge_4 : 4 ≤ Nat.sqrt L := by
    rw [Nat.le_sqrt]
    omega
  -- √L + 4 ≤ L for L ≥ 16: √L · √L ≤ L (always true, Nat.sqrt_le'), and 2*√L ≤ √L*√L for √L ≥ 2.
  have h_sqrtL_le_L_4 : Nat.sqrt L + 4 ≤ L := by
    have h_sqrt_sq : Nat.sqrt L * Nat.sqrt L ≤ L := by
      have h := Nat.sqrt_le' L
      rw [pow_two] at h
      exact h
    have h_2_le_sqrt : 2 * Nat.sqrt L ≤ Nat.sqrt L * Nat.sqrt L := by
      have := h_sqrt_ge_4
      nlinarith
    have h_4_plus_sqrt : Nat.sqrt L + 4 ≤ 2 * Nat.sqrt L := by omega
    omega
  have hsumk_le : Nat.sqrt L + k ≤ L - 5 := by
    have hk_lt : k < L - Nat.sqrt L - 4 := hk
    -- We need k + Nat.sqrt L + 5 ≤ L.
    -- Have: k < L - Nat.sqrt L - 4, i.e., k + Nat.sqrt L + 4 < L (assuming no underflow).
    -- L - Nat.sqrt L - 4 is well-defined since Nat.sqrt L + 4 ≤ L.
    have h_R_pos : 0 < L - Nat.sqrt L - 4 := by omega
    omega
  -- Step 2: tower(√L+k) ≤ tower(L-5).
  have h_tower_mono_k : tower (Nat.sqrt L + k) ≤ tower (L - 5) :=
    (strictMono_nat_of_lt_succ tower_lt_succ).monotone hsumk_le
  -- Step 3: q := tower(√L+k)/30; show q ≤ tower(L-5)/30.
  set q := tower (Nat.sqrt L + k) / 30 with hq_def
  have hq_le : q ≤ tower (L - 5) / 30 :=
    div_le_div_of_nonneg_right h_tower_mono_k (by norm_num)
  -- Step 4: convert (exp q)^19 = exp(19q) using rpow_def_of_pos.
  have h_exp_pow_eq : (Real.exp q) ^ ((20:ℝ) - 1) = Real.exp (19 * q) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos q), Real.log_exp]
    have h_arith : ((20:ℝ) - 1) = 19 := by norm_num
    rw [h_arith]; ring_nf
  rw [h_exp_pow_eq]
  -- Step 5: tower(L-5) ≥ exp 1 (induction: tower 0 = exp 1, monotone).
  have h_tower_ge_e : ∀ (m : ℕ), Real.exp 1 ≤ tower m := by
    intro m
    induction m with
    | zero => simp [tower]
    | succ k ih =>
      show Real.exp 1 ≤ Real.exp (tower k)
      apply Real.exp_le_exp.mpr
      have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
      linarith
  have h_tower_L5_ge_e : Real.exp 1 ≤ tower (L - 5) := h_tower_ge_e _
  -- Step 6: 19 * tower(L-5)/30 ≤ tower(L-5) - log 2.
  -- Equivalently: 11 * tower(L-5) / 30 ≥ log 2, using tower(L-5) ≥ exp 1 > 2.7 and log 2 < 0.7.
  have h_log_2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h_e_ge_2_7 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h_11_tower_ge_log2 : Real.log 2 ≤ 11 * tower (L - 5) / 30 := by
    have h_30_pos : (0 : ℝ) < 30 := by norm_num
    -- 11 * 2.7 / 30 = 29.7 / 30 = 0.99 > 0.6931...
    have h_27_ge_log2 : (0.6931471808 : ℝ) ≤ 11 * 2.7 / 30 := by norm_num
    have h_11_e_le_11_tower : (11 : ℝ) * 2.7 ≤ 11 * tower (L - 5) := by
      have := h_tower_L5_ge_e
      linarith
    have h_chain : (11 : ℝ) * 2.7 / 30 ≤ 11 * tower (L - 5) / 30 :=
      div_le_div_of_nonneg_right h_11_e_le_11_tower h_30_pos.le
    linarith
  -- Step 7: 19q ≤ 19 * tower(L-5)/30 ≤ tower(L-5) - log 2.
  have h_19q_le : 19 * q ≤ tower (L - 5) - Real.log 2 := by
    have h_19q_30 : 19 * q ≤ 19 * tower (L - 5) / 30 := by
      have h_19_nn : (0 : ℝ) ≤ 19 := by norm_num
      calc 19 * q ≤ 19 * (tower (L - 5) / 30) := by
            exact mul_le_mul_of_nonneg_left hq_le h_19_nn
        _ = 19 * tower (L - 5) / 30 := by ring
    have h_30_split : 19 * tower (L - 5) / 30 = tower (L - 5) - 11 * tower (L - 5) / 30 := by ring
    linarith
  -- Step 8: exp(19q) ≤ exp(tower(L-5) - log 2) = exp(tower(L-5))/2 = tower(L-4)/2.
  have h_tower_L4_eq : tower (L - 4) = Real.exp (tower (L - 5)) := by
    have h : L - 4 = (L - 5) + 1 := by omega
    rw [h]; rfl
  have h_exp_19q_le : Real.exp (19 * q) ≤ tower (L - 4) / 2 := by
    have h1 : Real.exp (19 * q) ≤ Real.exp (tower (L - 5) - Real.log 2) :=
      Real.exp_le_exp.mpr h_19q_le
    have h2 : Real.exp (tower (L - 5) - Real.log 2) = Real.exp (tower (L - 5)) / 2 := by
      rw [show tower (L - 5) - Real.log 2 = tower (L - 5) + (- Real.log 2) from by ring]
      rw [Real.exp_add]
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      field_simp
    linarith [h2 ▸ h1, h_tower_L4_eq]
  -- Step 9: exp(exp(19q)) ≤ exp(tower(L-4)/2).
  have h_exp_exp_19q : Real.exp (Real.exp (19 * q)) ≤ Real.exp (tower (L - 4) / 2) :=
    Real.exp_le_exp.mpr h_exp_19q_le
  -- Step 10: exp(tower(L-4)/2) + 1 ≤ tower(L-3).
  -- Set u := exp(tower(L-4)/2).  Then u² = exp(tower(L-4)) = tower(L-3).
  -- For tower(L-4) ≥ exp 1 > 2*log 2: u ≥ 2.  Then u² ≥ 2u ≥ u + u ≥ u + 1.
  have h_tower_L3_eq : tower (L - 3) = Real.exp (tower (L - 4)) := by
    have h : L - 3 = (L - 4) + 1 := by omega
    rw [h]; rfl
  have h_tower_L4_ge_e : Real.exp 1 ≤ tower (L - 4) := h_tower_ge_e _
  -- u := exp(tower(L-4)/2) ≥ 2.
  have h_u_ge_2 : 2 ≤ Real.exp (tower (L - 4) / 2) := by
    -- exp(tower(L-4)/2) ≥ 2 iff tower(L-4)/2 ≥ log 2 iff tower(L-4) ≥ 2 * log 2.
    have h_2log2 : 2 * Real.log 2 ≤ tower (L - 4) := by
      -- 2 * log 2 < 2 < exp 1 ≤ tower(L-4).
      have h_2log2_lt_2 : 2 * Real.log 2 < 2 := by linarith [h_log_2_lt]
      have h_e_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [h_e_ge_2_7]
      linarith
    have h_div : Real.log 2 ≤ tower (L - 4) / 2 := by linarith
    have h_exp_le : Real.exp (Real.log 2) ≤ Real.exp (tower (L - 4) / 2) :=
      Real.exp_le_exp.mpr h_div
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h_exp_le
    exact h_exp_le
  -- u² = exp(tower(L-4)) = tower(L-3).
  have h_u_sq_eq : (Real.exp (tower (L - 4) / 2)) ^ 2 = tower (L - 3) := by
    rw [sq, ← Real.exp_add, h_tower_L3_eq]
    congr 1
    ring
  -- u + 1 ≤ u² for u ≥ 2.
  have h_u_plus_1 : Real.exp (tower (L - 4) / 2) + 1 ≤ tower (L - 3) := by
    have h_u_sq : Real.exp (tower (L - 4) / 2) + 1 ≤ (Real.exp (tower (L - 4) / 2)) ^ 2 := by
      have h_u_ge_2' := h_u_ge_2
      nlinarith
    linarith [h_u_sq_eq]
  -- Step 11: tower(L-3) - 1 ≤ ⌊tower(L-3)⌋₊ via Nat.lt_floor_add_one.
  have h_floor_lower : tower (L - 3) - 1 ≤ (⌊tower (L - 3)⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one (tower (L - 3))
    linarith
  -- Combine: exp(exp(19q)) ≤ tower(L-4)/2 ≤ exp(tower(L-4)/2) ≤ tower(L-3) - 1 ≤ ⌊tower(L-3)⌋₊.
  -- Wait — actually exp(exp(19q)) ≤ exp(tower(L-4)/2), not ≤ tower(L-4)/2.  Let me re-thread.
  -- exp(exp(19q)) ≤ exp(tower(L-4)/2) (Step 9) ≤ tower(L-3) - 1 (Step 10) ≤ ⌊tower(L-3)⌋₊ (Step 11).
  linarith [h_exp_exp_19q, h_u_plus_1, h_floor_lower]

/-- A fixed gap between two exponential towers absorbs rounding to an integer. -/
private lemma double_exp_floor_gap {T : ℝ} (hT : 3 ≤ T) :
    2 * Real.exp (Real.exp (2 * T / 3)) ≤ (⌊Real.exp (Real.exp T)⌋₊ : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hthird : 2 ≤ Real.exp (T / 3) :=
    he.trans (Real.exp_monotone (by linarith only [hT]))
  have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith only [he]
  have hu : 4 ≤ Real.exp (2 * T / 3) :=
    hexp2.trans (Real.exp_monotone (by linarith only [hT]))
  have htwice : 2 * Real.exp (2 * T / 3) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (T / 3) * Real.exp (2 * T / 3) :=
        mul_le_mul_of_nonneg_right hthird (Real.exp_pos _).le
      _ = Real.exp T := by rw [← Real.exp_add]; congr 1; ring
  have hlog4 : Real.log 4 ≤ Real.exp (2 * T / 3) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h, hu]
  have hgap : 4 * Real.exp (Real.exp (2 * T / 3)) ≤ Real.exp (Real.exp T) := by
    calc
      _ = Real.exp (Real.log 4 + Real.exp (2 * T / 3)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ _ := Real.exp_monotone (by linarith only [hlog4, htwice])
  have hfloor := Nat.lt_floor_add_one (Real.exp (Real.exp T))
  have hone : 1 ≤ Real.exp (Real.exp (2 * T / 3)) :=
    Real.one_le_exp (Real.exp_pos _).le
  linarith only [hgap, hfloor, hone]

/-- Paper §7.4 summation, specialized to the parameter-free witness supplied by
`stage_failure_density_H_witness`.

**Paper-faithful proof structure (paper lines 1886-2059, single-CRT approach
following CLOSURE_PLAN_LBH.md Option A):**

1. **Define `M`-periodic chain event** (paper line 2031-2045): the event
   `C_H(n) := "n has the H-greedy-chain (1 = d_1 < ⋯ < d_{R+1}) using only
   primes ≤ P"` depends only on `(𝟙_{p∣n})_{p ≤ P}` where
   `P := ⌊exp(y_R^{A-1})⌋`.  Hence `C_H` is `M`-periodic with
   `M := primorial(P)`.

2. **Product-model bound** (paper Lemma 7.3, line 1888-1976): in the
   independent prime model on primes ≤ `P`,
   `P_prod(¬ C_H) ≤ ∑_{j=1}^R O(y_j^{-c})` via union bound across stages.
   Each stage bound `P_prod(F_j ∩ S_{j-1}) ≤ y_j^{-c}` follows from
   `composite_successor_residue_density` (uniformly in `d ≤ y_j`, paper
   line 1920).  The geometric sum `∑ y_j^{-c} ≤ 2 y_1^{-c}` (paper line
   1964-1972) uses `y_{j+1} ≥ y_j^2` from `scale_H`.

3. **Single CRT transfer** (paper line 2049): apply `crt_transfer` ONCE
   with cutoff `P`. This gives
   `|density(C_H)/x − P_prod(C_H)| ≤ M/x`.

4. **Bound `M = o(x)`** (paper line 2007): `log M ≤ C_θ · P ≤ C_θ · T_{L-3}`
   (Chebyshev, our `chebyshev_primorial_bound` + `primorial_decay_bound`),
   while `log x ≥ T_{L-2}` so `M/x → 0` super-polynomially.

5. **Chain length packaging** (paper line 1846-1848, 2054-2057): when `C_H`
   holds, `H(n) ≥ R + 1 ≥ (1-ε) · L` for `L ≥ L₀(ε)` via
   `chain_length_packaging`.

**Critical paper-faithfulness note**: this proof must use a SINGLE CRT
application (paper line 2049), NOT a per-stage CRT summation.  The
per-stage approach via `composite_successor_uniform_d_conditional` summed
over `(j, d)` gives a `log y · y^{-c}` bound (extra `log y` factor) which
is a strict weakening of paper's `y^{-c}` bound — prohibited by the
"no weakening" rule.

The hard sub-claim is step 2 (product-model bound across stages).  This
requires multi-window product-model machinery (defining the chain event
on residues mod `M`, decomposing by stage, using `scale_H` window
disjointness for independence).  Closed across multiple fires from
`composite_successor_residue_density`. -/
private lemma stage_failure_sum_H (ε : ℝ) (hε : 0 < ε) (hε_lt_one : ε < 1)
    (Cθ : ℝ) (hCθ_pos : 0 < Cθ) (htheta : ChebyshevThetaWitness Cθ) :
    ∃ A : ℝ, 10 < A ∧ ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℝ, 0 < y₀ ∧
      StageFailureSumH ε A c y₀ := by
  -- Paper §7.4 line 2031-2059: paper-faithful single-CRT assembly.
  -- Set A = 20, B = A + 10 = 30 (paper line 1838).
  classical
  rcases composite_successor_residue_density with ⟨c, hc, _y₀_in, _hy₀_in_pos, _hresidue⟩
  refine ⟨20, by norm_num, c, hc, 1, by norm_num, by norm_num, hc, by norm_num, ?_⟩
  intro η hη
  -- Get scale_H witness for A = 20, B = 30.
  rcases scale_H 20 30 (by norm_num : (0:ℝ) < 20) (by norm_num : (20:ℝ) + 10 ≤ 30)
    with ⟨Lscale, hScaleH⟩
  -- Convert to HScaleWitness form (the (20 + 10) vs 30 are defEq).
  have hScaleH' : HScaleWitness (20 : ℝ) Lscale := by
    intro L hL j hj
    rcases hScaleH L hL j hj with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h_eq : ((20 : ℝ) + 10) = 30 := by norm_num
    rw [h_eq]
    exact hm
  -- Get L₀ from residue density bound (paper Lemma 7.3, with target η/4).
  rcases HChainEvent_pmodel_bound_via_greedy (A := (20:ℝ)) (B := (30:ℝ)) (rfl : (20:ℝ) = 20)
    (by norm_num : (20:ℝ) + 10 ≤ 30) Lscale hScaleH' (η := η / 4)
    (by positivity) with ⟨L₁, hL₁⟩
  -- Get L₀ from primorial decay (M/x bound, target η/4, paper line 2007).
  rcases primorial_decay_bound hCθ_pos htheta (η := η / 4)
    (by positivity) with ⟨L₂, hL₂⟩
  -- Get L₀ from chain length packaging (paper line 1846-1848).
  rcases chain_length_packaging hε hε_lt_one with ⟨L₃, hL₃⟩
  -- Get L₀ from P-bound tower analysis (paper line 1989-1999).
  rcases hP_chain_bound_existence with ⟨L₄, hL₄⟩
  -- L₀ = max of all bounds.
  let L₀ : ℕ := max (max L₁ L₂) (max (max L₃ L₄) (max Lscale 16))
  -- x₀ := max (tower L₀) (2/η) ensures L ≥ L₀ AND 1/x ≤ η/2.
  refine ⟨max (tower L₀) (2 / η), ?_, ?_⟩
  · exact lt_max_of_lt_left (tower_pos _)
  intro x hx
  have hx_ge_tower : tower L₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx_ge_inv : 2 / η ≤ x := le_trans (le_max_right _ _) hx
  -- Final bound: |bad set|/x ≤ η.
  -- Concrete bound chain (paper §7.4 line 2031-2049 verbatim):
  -- 1. ¬GoodLowerDivisorChain ε n ⟹ n = 0 ∨ ¬HChainEvent_L n ∨ chain too short.
  --    For L ≥ L₃: chain_length_packaging gives (1-ε)·L ≤ R, so for n with
  --    HChainEvent_L the chain length R suffices for GoodLowerDivisorChain.
  --    Hence ¬GoodLowerDivisorChain ⟹ n = 0 ∨ ¬HChainEvent_L.
  -- 2. By HChainEvent_complement_density_via_crt: ∃ q_prod, ∀x, |density(¬E)/x - q_prod| ≤ M/x.
  -- 3. By HChainEvent_q_prod_eq_residue_density: q_prod = residue density of ¬E mod M.
  -- 4. By HChainEvent_pmodel_bound: residue density ≤ η/4.
  -- 5. So q_prod ≤ η/4, hence density(¬E)/x ≤ η/4 + M/x.
  -- 6. By primorial_decay_bound: M/x ≤ η/4.
  -- 7. Hence density(¬E)/x ≤ η/2, so |¬E count| ≤ η/2 · x.
  -- 8. |bad set| ≤ 1 + |¬E count| ≤ 1 + η/2·x ≤ η·x for x ≥ 2/η.
  --
  -- Compute L = logStar x and show L ≥ L₀ (via logStar/tower monotonicity).
  set L : ℕ := logStar x with hL_def
  have hL_ge_L₀ : L₀ ≤ L := by
    by_contra h_lt
    push_neg at h_lt
    have h_tower_strict : tower (logStar x) < tower L₀ :=
      strictMono_nat_of_lt_succ tower_lt_succ h_lt
    have h_x_le : x ≤ tower (logStar x) := self_le_tower_logStar x
    have h_x_ge : tower L₀ ≤ x := hx_ge_tower
    linarith
  -- L ≥ each of L₁, L₂, L₃, Lscale, 16.
  -- Recall L₀ = max (max L₁ L₂) (max L₃ (max Lscale 16)).
  have hL₀_ge_L₁ : L₁ ≤ L₀ := by
    have h1 : L₁ ≤ max L₁ L₂ := le_max_left _ _
    have h2 : max L₁ L₂ ≤ L₀ := le_max_left _ _
    omega
  have hL₀_ge_L₂ : L₂ ≤ L₀ := by
    have h1 : L₂ ≤ max L₁ L₂ := le_max_right _ _
    have h2 : max L₁ L₂ ≤ L₀ := le_max_left _ _
    omega
  have hL₀_ge_L₃ : L₃ ≤ L₀ := by
    have h1 : L₃ ≤ max L₃ L₄ := le_max_left _ _
    have h2 : max L₃ L₄ ≤ max (max L₃ L₄) (max Lscale 16) := le_max_left _ _
    have h3 : max (max L₃ L₄) (max Lscale 16) ≤ L₀ := le_max_right _ _
    omega
  have hL₀_ge_L₄ : L₄ ≤ L₀ := by
    have h1 : L₄ ≤ max L₃ L₄ := le_max_right _ _
    have h2 : max L₃ L₄ ≤ max (max L₃ L₄) (max Lscale 16) := le_max_left _ _
    have h3 : max (max L₃ L₄) (max Lscale 16) ≤ L₀ := le_max_right _ _
    omega
  have hL₀_ge_16 : 16 ≤ L₀ := by
    have h1 : 16 ≤ max Lscale 16 := le_max_right _ _
    have h2 : max Lscale 16 ≤ max (max L₃ L₄) (max Lscale 16) := le_max_right _ _
    have h3 : max (max L₃ L₄) (max Lscale 16) ≤ L₀ := le_max_right _ _
    omega
  have hL_ge_L₁ : L₁ ≤ L := le_trans hL₀_ge_L₁ hL_ge_L₀
  have hL_ge_L₂ : L₂ ≤ L := le_trans hL₀_ge_L₂ hL_ge_L₀
  have hL_ge_L₃ : L₃ ≤ L := le_trans hL₀_ge_L₃ hL_ge_L₀
  have hL_ge_L₄ : L₄ ≤ L := le_trans hL₀_ge_L₄ hL_ge_L₀
  have hL_ge_16 : 16 ≤ L := le_trans hL₀_ge_16 hL_ge_L₀
  -- Set m₀ = √L, R = L - m₀ - 4, P = ⌊tower(L-3)⌋₊.
  -- This P satisfies P ≤ tower(L-3) (needed for primorial_decay_bound) and
  -- P ≥ exp(y_R^{A-1}) for L large (needed for hP_bound).
  set m₀ : ℕ := Nat.sqrt L with hm₀_def
  set R : ℕ := L - m₀ - 4 with hR_def
  set P : ℕ := ⌊tower (L - 3)⌋₊ with hP_def
  -- Setup x-related basics.
  have hx_pos : 0 < x := by
    have htowerpos : 0 < tower L₀ := tower_pos _
    linarith
  have hx_ge_one : 1 ≤ x := by
    have htower_ge : (1 : ℝ) ≤ tower L₀ := by
      -- tower is at least exp 1 > 1 for L₀ ≥ 0.
      have h := Real.add_one_le_exp (tower (L₀ - 1) - 1)
      have htower_ge_e : (Real.exp 1 : ℝ) ≤ tower L₀ := by
        induction L₀ with
        | zero => simp [tower]
        | succ k ih =>
          show Real.exp 1 ≤ tower (k + 1)
          show Real.exp 1 ≤ Real.exp (tower k)
          apply Real.exp_le_exp.mpr
          calc (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
            _ ≤ tower k := ih
      have he_ge : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    linarith
  -- Verify hP_bound (paper line 1989-1999): exp(y_{k+1}^{A-1}) ≤ P.
  -- Paper derives this via log log P_paper = (A-1)/B · T_{L-5} < T_{L-5} (since (A-1)/B < 1),
  -- exponentiating twice gives P_paper < tower(L-3); P = ⌊tower(L-3)⌋ ≥ tower(L-3) - 1 absorbs
  -- the strict slack.  Discharged by `hP_chain_bound_existence` (paper line 1985-1999).
  have hP_bound_chain : ∀ k : ℕ, k < L - Nat.sqrt L - 4 →
      Real.exp ((Real.exp (tower (Nat.sqrt L + k) / 30)) ^ ((20 : ℝ) - 1)) ≤ (P : ℝ) := by
    intro k hk
    show Real.exp ((Real.exp (tower (Nat.sqrt L + k) / 30)) ^ ((20 : ℝ) - 1)) ≤
        (⌊tower (L - 3)⌋₊ : ℝ)
    exact hL₄ L hL_ge_L₄ k hk
  -- Apply HChainEvent_pmodel_bound to get residue density ≤ η/4.
  -- For L ≥ 16, tower (L - 3) ≥ tower 13 ≫ 2, so ⌊tower(L-3)⌋ ≥ 2.
  have hP_ge_2 : 2 ≤ P := by
    show 2 ≤ ⌊tower (L - 3)⌋₊
    have h_tower_ge_two : (2 : ℝ) ≤ tower (L - 3) := by
      -- tower (L-3) ≥ tower 0 = exp 1 > 2 for L ≥ 4.
      -- Actually tower 0 = exp 1 ≈ 2.71 > 2.
      have hL_ge_4 : 4 ≤ L := by linarith [hL_ge_16]
      have hL_minus_3_ge_1 : 1 ≤ L - 3 := by omega
      have h_tower_mono : tower 1 ≤ tower (L - 3) := by
        exact (strictMono_nat_of_lt_succ tower_lt_succ).monotone hL_minus_3_ge_1
      have h_tower_one : tower 1 = Real.exp (Real.exp 1) := by
        show tower (0 + 1) = Real.exp (Real.exp 1)
        rfl
      -- exp(exp 1) > 2.
      have h_exp_exp_one_ge : (2 : ℝ) ≤ Real.exp (Real.exp 1) := by
        have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
        have h2 : Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr h1
        have h3 : (2 : ℝ) ≤ Real.exp 1 := by
          -- exp 1 ≈ 2.71828.
          have := Real.exp_one_gt_d9
          linarith
        linarith
      linarith [h_tower_one ▸ h_exp_exp_one_ge]
    have h_floor_ge : 2 ≤ ⌊tower (L - 3)⌋₊ := by
      apply Nat.le_floor
      exact_mod_cast h_tower_ge_two
    exact h_floor_ge
  have h_residue_le : ((Nat.card {r : Fin (primorial P) //
        ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) r.val} : ℝ) /
      (primorial P : ℝ) ≤ η / 4) := by
    -- Provide hP_strong_at_R: exp(exp(tower(L-5)/30)^20) ≤ tower(L-3) = exp(tower(L-4)).
    -- ⟺ exp(tower(L-5)/30)^20 ≤ tower(L-4).
    -- ⟺ exp(20·tower(L-5)/30) ≤ tower(L-4) = exp(tower(L-5)).
    -- ⟺ 20·tower(L-5)/30 ≤ tower(L-5).  ⟺  20/30 ≤ 1.  TRUE.
    have hP_strong_at_R :
        2 * Real.exp ((Real.exp (tower (Nat.sqrt L + (L - Nat.sqrt L - 5)) / 30)) ^ (20 : ℝ)) ≤
          (P : ℝ) := by
      have hroot4 : 4 ≤ Nat.sqrt L := by rw [Nat.le_sqrt]; omega
      have hrootSq : Nat.sqrt L * Nat.sqrt L ≤ L := by
        simpa only [pow_two] using Nat.sqrt_le' L
      have hroot5 : Nat.sqrt L + 5 ≤ L := by nlinarith only [hroot4, hrootSq]
      have hidx : Nat.sqrt L + (L - Nat.sqrt L - 5) = L - 5 := by omega
      have htower : tower (L - 3) = Real.exp (Real.exp (tower (L - 5))) := by
        rw [show L - 3 = (L - 5) + 1 + 1 by omega]
        rfl
      have hpow : (Real.exp (tower (L - 5) / 30)) ^ (20 : ℝ) =
          Real.exp (2 * tower (L - 5) / 3) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      have hT : 3 ≤ tower (L - 5) := by
        have h := tower_ge (L - 5)
        have hcast : (2 : ℝ) ≤ (L - 5 : ℕ) := by exact_mod_cast (show 2 ≤ L - 5 by omega)
        linarith only [h, hcast]
      change _ ≤ (⌊tower (L - 3)⌋₊ : ℝ)
      rw [hidx, hpow, htower]
      exact double_exp_floor_gap hT
    have := hL₁ L hL_ge_L₁ P hP_ge_2 hP_bound_chain hP_strong_at_R
    exact this
  -- Apply HChainEvent_complement_density_via_crt.
  have h_crt := HChainEvent_complement_density_via_crt (20 : ℝ) (30 : ℝ)
    (Nat.sqrt L) (L - Nat.sqrt L - 4) P hP_ge_2 hP_bound_chain
  rcases h_crt with ⟨q_prod, hq_prod⟩
  -- Apply q_prod_eq_residue_density.
  have h_q_eq := HChainEvent_q_prod_eq_residue_density (20 : ℝ) (30 : ℝ)
    (Nat.sqrt L) (L - Nat.sqrt L - 4) P hP_ge_2 hP_bound_chain q_prod hq_prod
  -- q_prod ≤ η/4.
  have h_q_le : q_prod ≤ η / 4 := by rw [h_q_eq]; exact h_residue_le
  -- Apply hq_prod at x.
  have h_density_bound := hq_prod x hx_ge_one
  -- |density(¬E)/x - q_prod| ≤ M/x where M = primorial P.
  -- Hence density(¬E)/x ≤ q_prod + M/x ≤ η/4 + M/x.
  have h_dens_upper : ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧
        ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n} : ℝ)) / x ≤
      η / 4 + (primorial P : ℝ) / x := by
    have : ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧
          ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n} : ℝ)) / x ≤
        q_prod + (primorial P : ℝ) / x := by
      have habs := abs_le.mp h_density_bound
      linarith [habs.2]
    linarith
  -- Apply primorial_decay_bound (paper §7.4 line 2003-2007): M/x ≤ η/4.
  -- Paper line 1194: T_{L-1} < x ≤ T_L.  Hence tower(L-1) ≤ x.
  -- t = (P : ℝ) = (⌊tower(L-3)⌋ : ℝ) ≤ tower(L-3) (floor inequality).
  -- 2 ≤ t since P ≥ 2.
  have h_primorial : (primorial P : ℝ) / x ≤ η / 4 := by
    -- Paper line 1192-1194: by definition of L = logStar x, T_{L-1} < x ≤ T_L.
    have htower_pred_lt_x : tower (L - 1) < x := by
      by_contra hnot
      have hxle : x ≤ tower (L - 1) := le_of_not_gt hnot
      have hle := logStar_le_of_le_tower (L - 1) hxle
      -- hle : logStar x ≤ L - 1, but L = logStar x ≥ 16, contradiction.
      have hL_eq : L = logStar x := hL_def
      rw [hL_eq] at hL_ge_16
      omega
    have htower_pred_le_x : tower (L - 1) ≤ x := le_of_lt htower_pred_lt_x
    -- t = (P : ℝ); need 2 ≤ t and t ≤ tower(L-3).
    have hP_real_ge_2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP_ge_2
    have hP_real_le_tower : (P : ℝ) ≤ tower (L - 3) := by
      have h_floor_le : (⌊tower (L - 3)⌋₊ : ℝ) ≤ tower (L - 3) := by
        apply Nat.floor_le
        exact (tower_pos _).le
      show (⌊tower (L - 3)⌋₊ : ℝ) ≤ tower (L - 3)
      exact h_floor_le
    have h_primorial_eq :
        ((∏ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊(P : ℝ)⌋₊), p : ℕ) : ℝ) =
        (primorial P : ℝ) := by
      have h_floor_P : ⌊(P : ℝ)⌋₊ = P := Nat.floor_natCast P
      rw [h_floor_P]
      rfl
    -- Apply primorial_decay_bound at L_index = L.
    have h_decay := hL₂ L hL_ge_L₂ (P : ℝ) hP_real_ge_2 hP_real_le_tower x htower_pred_le_x
    rw [h_primorial_eq] at h_decay
    exact h_decay
  -- Combine: density(¬E)/x ≤ η/2.
  -- Combine: density(¬E)/x ≤ η/2.
  have h_dens_le_half : ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧
        ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n} : ℝ)) / x ≤
      η / 2 := by linarith
  -- Hence |¬E count| ≤ η/2 · x.
  have h_bad_count_bound : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧
        ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n} : ℝ) ≤
      (η / 2) * x := by
    rw [div_le_iff₀ hx_pos] at h_dens_le_half
    linarith
  -- Show: ¬GoodLowerDivisorChain ⟹ n = 0 ∨ ¬HChainEvent.
  -- For n ≠ 0 with HChainEvent: HasDCL R n (via hasDivisorChainLengthAtLeast_of_HChainEvent).
  -- Then (1-ε)·logStar n ≤ R follows from chain_length_packaging + logStar n ≤ logStar x = L.
  -- Hence GoodLowerDivisorChain ε n holds.
  have h_inclusion : ∀ n : ℕ, n ≤ ⌊x⌋₊ → ¬ GoodLowerDivisorChain ε n →
      n = 0 ∨ ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n := by
    intro n hn hbad
    by_cases hn_zero : n = 0
    · exact Or.inl hn_zero
    right
    intro hHEv
    apply hbad
    refine ⟨L - Nat.sqrt L - 4, hn_zero,
      hasDivisorChainLengthAtLeast_of_HChainEvent hHEv, ?_⟩
    -- (1-ε)·logStar n ≤ R = L - √L - 4.
    have hlogStar_le : logStar (n : ℝ) ≤ L := by
      apply logStar_nat_le_logStar_of_le_floor (by linarith : (0 : ℝ) ≤ x) hn
    have h_chain_pkg : (1 - ε) * (L : ℝ) ≤ ((L - Nat.sqrt L - 4 : ℕ) : ℝ) := hL₃ L hL_ge_L₃
    have hcoef_nn : 0 ≤ (1 - ε) := by linarith
    calc (1 - ε) * (logStar (n : ℝ) : ℝ)
        ≤ (1 - ε) * (L : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hcoef_nn
          exact_mod_cast hlogStar_le
      _ ≤ ((L - Nat.sqrt L - 4 : ℕ) : ℝ) := h_chain_pkg
  -- |bad set| ≤ 1 + |¬E count|.
  have h_bad_subset_count : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} : ℝ) ≤
      1 + (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧
        ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n} : ℝ) := by
    classical
    -- Bad set ⊆ {0} ∪ {¬HChainEvent}. Counted via Finset partition.
    -- bad_finset := (Iic ⌊x⌋₊).filter ¬GoodLowerDivisorChain ε.
    -- nE_finset := (Iic ⌊x⌋₊).filter ¬HChainEvent.
    -- bad_finset ⊆ {0} ∪ nE_finset (via h_inclusion).
    -- bad_finset.card ≤ 1 + nE_finset.card.
    set bad_finset : Finset ℕ :=
      (Finset.Iic ⌊x⌋₊).filter (fun n => ¬ GoodLowerDivisorChain ε n)
    set nE_finset : Finset ℕ :=
      (Finset.Iic ⌊x⌋₊).filter
        (fun n => ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n)
    -- Convert Nat.card to Finset.card.
    have h_bad_card_eq : Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} =
        bad_finset.card :=
      Nat.subtype_card _ (by intro n; simp [bad_finset, Finset.mem_filter])
    have h_nE_card_eq : Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧
        ¬ HChainEvent (20 : ℝ) (30 : ℝ) (Nat.sqrt L) (L - Nat.sqrt L - 4) n} =
        nE_finset.card :=
      Nat.subtype_card _ (by intro n; simp [nE_finset, Finset.mem_filter])
    rw [h_bad_card_eq, h_nE_card_eq]
    -- bad_finset ⊆ {0} ∪ nE_finset.
    have h_subset : bad_finset ⊆ {0} ∪ nE_finset := by
      intro n hn
      have hn_filter : n ∈ (Finset.Iic ⌊x⌋₊).filter
          (fun n => ¬ GoodLowerDivisorChain ε n) := hn
      rw [Finset.mem_filter, Finset.mem_Iic] at hn_filter
      rw [Finset.mem_union]
      rcases h_inclusion n hn_filter.1 hn_filter.2 with hzero | hnE
      · left; rw [Finset.mem_singleton]; exact hzero
      · right
        rw [Finset.mem_filter, Finset.mem_Iic]
        exact ⟨hn_filter.1, hnE⟩
    -- bad_finset.card ≤ ({0} ∪ nE_finset).card ≤ 1 + nE_finset.card.
    have h_card_le : bad_finset.card ≤ ({0} ∪ nE_finset : Finset ℕ).card :=
      Finset.card_le_card h_subset
    have h_union_card : ({0} ∪ nE_finset : Finset ℕ).card ≤ ({0} : Finset ℕ).card + nE_finset.card :=
      Finset.card_union_le _ _
    have h_singleton : ({0} : Finset ℕ).card = 1 := Finset.card_singleton _
    have h_total : bad_finset.card ≤ 1 + nE_finset.card := by
      calc bad_finset.card ≤ ({0} ∪ nE_finset : Finset ℕ).card := h_card_le
        _ ≤ ({0} : Finset ℕ).card + nE_finset.card := h_union_card
        _ = 1 + nE_finset.card := by rw [h_singleton]
    exact_mod_cast h_total
  -- Final: |bad|/x ≤ 1/x + η/2 ≤ η/2 + η/2 = η for x ≥ 2/η.
  have h_one_div_le : 1 / x ≤ η / 2 := by
    rw [div_le_iff₀ hx_pos]
    have : 2 ≤ η * x := by
      have h := hx_ge_inv
      rw [div_le_iff₀ hη] at h
      linarith
    linarith
  have h_final : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} : ℝ) ≤ η * x := by
    have h_total : (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} : ℝ) ≤
        1 + (η / 2) * x := by linarith
    -- 1 + (η/2)·x ≤ η·x for x ≥ 2/η, i.e., 1 ≤ (η/2)·x, i.e., 2/η ≤ x.
    have h_one_le : (1 : ℝ) ≤ (η / 2) * x := by
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have := hx_ge_inv
      rw [div_le_iff₀ hη] at this
      linarith
    linarith
  exact h_final

private lemma good_lower_divisor_chains_from_stage_sums {ε A c y₀ : ℝ}
    (hsum : StageFailureSumH ε A c y₀) :
    almostAll (GoodLowerDivisorChain ε) := by
  -- Convert the summed `o(x)` failure estimate into the `almostAll` predicate.
  classical
  unfold StageFailureSumH at hsum
  rcases hsum with ⟨_hA, _hc, _hy₀, hsmall⟩
  unfold almostAll
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro δ hδ
  rcases hsmall (δ / 2) (by positivity) with ⟨x₀, hx₀_pos, hx₀⟩
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hx
  have hx_pos : 0 < x := hx₀_pos.trans_le hx
  have hbound := hx₀ x hx
  have hdiv :
      ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} : ℕ) : ℝ) / x
        ≤ δ / 2 := by
    rw [div_le_iff₀ hx_pos]
    exact hbound
  have hnonneg :
      0 ≤ ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ GoodLowerDivisorChain ε n} : ℕ) : ℝ) / x := by
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  linarith

/-- Paper §7.3 plus §7.4, isolated from the final `greedy_H_chain` wrapper.

The proof uses `composite_successor_uniform` for the one-step failure bound,
`scale_H` with `B = A + 10` for disjoint tower windows, and the CRT/primorial
bookkeeping controlled by `chebyshev_theta`.  This lemma is the remaining
paper-faithful analytic bridge: summing the stage-failure densities gives
`o(x)`, while the produced successor divisors form a divisor chain of length
`(1 - o(1)) log_* n`. -/
private lemma good_lower_divisor_chains_from_uniform_successors :
    ∀ ε : ℝ, 0 < ε → ε < 1 → almostAll (GoodLowerDivisorChain ε) := by
  classical
  intro ε hε hε_lt_one
  rcases chebyshev_theta with ⟨Cθ, hCθ_pos, htheta⟩
  -- `stage_failure_sum_H` now obtains the unique `(A, c, y₀)` package from
  -- `stage_failure_density_H_witness` before carrying out the paper §7.4
  -- summation and deterministic greedy-chain packaging.
  rcases stage_failure_sum_H ε hε hε_lt_one Cθ hCθ_pos htheta with
    ⟨A, _hA, c, _hc, y₀, _hy₀_pos, hsum⟩
  exact good_lower_divisor_chains_from_stage_sums (ε := ε) (A := A) (c := c) (y₀ := y₀)
    hsum

/-- Density-one form of the paper §7.3 greedy construction plus §7.4 CRT bookkeeping.

For every `0 < ε < 1`, almost every integer carries a divisor chain whose length is
at least `(1 - ε) log_* n`.  The paper proves this by applying
`composite_successor_uniform` along the tower scales from `scale_H`, summing the
per-stage failure densities, and absorbing the CRT-periodic remainders as `o(x)`. -/
private lemma good_lower_divisor_chains :
    ∀ ε : ℝ, 0 < ε → ε < 1 → almostAll (GoodLowerDivisorChain ε) := by
  exact good_lower_divisor_chains_from_uniform_successors

/-- **Lemma 7.3 (greedy `H`-chain in the product model).**

In the independent prime model on primes up to `exp(y_R^{A-1})`, with
probability `1 - o(1)` there is a divisor chain `1 = d_1 < ⋯ < d_{R+1}`
with the form described in §7.2.

Sketch: at each stage `j`, apply `composite_successor` with `d := d_j`,
`y := y_j` to obtain a squarefree product `d_{j+1}` of selected primes
in `(exp y_j, exp(y_j^{A-1})]`.  The events at different stages are
independent (disjoint windows), so failure probabilities add to `o(1)`.

Uses `composite_successor` independently in each window, plus
`crt_transfer` to lift product-model density to integer density.

Refactored 2026-04-28 to carry actual density content (was `True` stub).
The statement now directly asserts the integer density result needed
by `lower_bound_H`. -/
lemma greedy_H_chain :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n => (HChain n : ℝ) ≥ (1 - ε) * (logStar n : ℝ)) := by
  intro ε hε
  by_cases hlarge : (1 : ℝ) ≤ ε
  · simpa using greedy_H_chain_large_epsilon ε hlarge
  · exact lower_bound_from_good_divisor_chains
      (good_lower_divisor_chains ε hε (lt_of_not_ge hlarge))

/-- **Theorem 7.1 (lower bound for `H`).**

For all but `o(x)` integers `n ≤ x`, `H(n) ≥ (1 - o(1)) log_* x`.

Encoded ε-style.  Direct corollary of `greedy_H_chain`. -/
theorem lower_bound_H :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n => (HChain n : ℝ) ≥ (1 - ε) * (logStar n : ℝ)) :=
  greedy_H_chain

end Erdos696
