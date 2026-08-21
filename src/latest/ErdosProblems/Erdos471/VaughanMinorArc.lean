/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Obligation P3 (Phase 1) of
`problems/ternary-goldbach/plans/bridge_targets_redesign.md`: proven
skeleton layers for the corrected item-9 bridge target
`hardCutoffVaughanTypeIIHighDenominatorCenterQSensitiveTargetParam`
(the `q`-dependent classical Vinogradov envelope
`K·(n/√q + n^{4/5} + √(q·n))·(log n)⁴` for the `Λ − log` Type-II sum at
the hypothesized Dirichlet witness denominator).

Phase-1 layers PROVED here (complete proofs, no proof holes):

* `dyadicBoxCount_le_three_log` — the dyadic box count
  `Nat.log 2 n + 1 ≤ 3·log n` (one of the four budgeted log factors);
* `Ioc_zero_eq_dyadic_biUnion` / `norm_sum_Ioc_zero_le_dyadic` — exact
  dyadic partition of `(0, N]` into `{1}` plus the truncated blocks
  `(2^j, min (2^{j+1}) N]` and the triangle-inequality decomposition of
  any exponential sum along it;
* `sum_Icc_inv_le_one_add_log` / `sum_Icc_ite_dvd_inv_le` — harmonic-sum
  bookkeeping;
* `sum_Ioc_card_divisors_sq_le` — the honest divisor second moment
  `Σ_{m≤N} τ(m)² ≤ N·(1 + log N)³` (double counting against
  `N/lcm(d₁,d₂) ≤ N·gcd/(d₁d₂)` plus three harmonic sums), the source of
  the coefficient-ℓ² log factors;
* `dyadicL2Sq_vaughanTypeII_outer_le` / `dyadicL2Sq_vaughanTypeII_inner_le`
  — ℓ² bounds for the actual Vaughan Type-II coefficient sequences
  `Λ_{>V}` (outer) and `μ_{>U} * ζ` (inner, divisor-bounded) on dyadic
  boxes;
* `vaughanTypeII_single_box_bound` — single-box application of the
  proof-complete `AnalyticNT.Bilinear.TypeII.typeII_bound_uniform` to the
  Vaughan coefficient pair, with the concrete envelope
  `C·√(1+log(q+1))·√(DM/q+D+M+q)·√(D·log²(2D+1))·√(2M(1+log 2M)³)`;
* `center_round_separation` / `norm_log_expSum_le_of_center` — the
  `log`-part absorption: a reduced witness center with `q ≥ 2` forces
  `‖α‖ ≥ 1/(2q)`, whence `‖Σ log·e‖ ≤ 2q·log n` (consumes the proven
  P2 distance-sensitive kernel);
* `norm_lambdaLow_expSum_le` / `norm_lambda_sub_log_expSum_le_trivial` —
  the small Vaughan `Λ_{≤V}` piece and the trivial `2n log n` bound
  (used for the `q = 1` witness branch where `‖α‖ ≥ 1/(2q)` fails);
* `hardCutoffVaughanTypeIIQSensitiveTarget_of_pieces` — ASSEMBLY: the
  corrected item-9 target (for EVERY cutoff `U`) follows from the two
  remaining named obligations below via Vaughan's identity
  (`vaughan_to_typeI_typeII_bilinear_full`, `U = V = ⌊n^{2/5}⌋`),
  with the `q = 1` branch closed by the trivial bound and the
  `Λ_{≤V}`/`log` pieces absorbed into the `n^{4/5}`/`√(qn)` envelope
  terms.

Phase-2 obligations — BOTH DISCHARGED (2026-06-11, complete proofs):

* `vaughanTypeIPieceQSensitiveEnvelopeBound_proved` — Type-I piece via
  the hyperbola swap (`sum_Ioc_divisors_swap`), the fixed-outer form,
  Abel summation against the geometric kernel
  (`norm_logInner_le_kernel`), and the classical
  `Σ_{r≤R} min(n/r, 1/‖rα‖)`-type harmonic-block bound in dichotomy
  form (`typeIKernelBound`: resonant moduli `q ∣ r` take the hyperbola
  cap summed over `r = qh`; non-resonant moduli take the Davenport
  symmetric-residue bound `q/j_r` from `nonres_dist_int_lb`, grouped by
  residue blocks against `symmetric_harmonic_sum_bound`); `K = 2000`;
* `vaughanTypeIIPieceQSensitiveEnvelopeBound_proved` — Type-II piece via
  dyadic outer blocks + the Layer-10 truncated per-block Schur bound +
  the effectiveness dichotomy (a non-vanishing block term forces
  `V < d₀ ≤ 2D` and `(V+1)d₀ ≤ n`, pinning the effective window
  `D ≤ n^{3/5}`, `K ≤ 2n^{3/5}` that yields the `n^{8/5}` middle term)
  + `effective_block_envelope_bound` numerics; `K = 300`;
* `hardCutoffVaughanTypeIIQSensitiveTarget_proved` /
  `helfgottMinorArcTypeIIHDCQSensitiveBridgeProposal_proved` — the
  corrected item-9 target (for EVERY cutoff) and its bridge proposal,
  now theorems.

`(log n)⁴` budget audit for Phase 2 (recorded per the plan): box count
contributes `(3 log n)²` across the two dyadic variables, the per-box
envelope `√(1+log(q+1)) ≤ √(1+log(n+1))` one more after squaring into
the count, and the coefficient ℓ² norms contribute
`√(log²(2D+1))·√((1+log 2M)³)` ≈ `log^{5/2}` on the √-scale — total
`log^{1+1+1/2+5/4}` ≲ `log⁴` only after the standard refinement that the
box-count square multiplies the SUP of box bounds, not their product;
the assembly must use `Σ_j √(x_j) ≤ √(J·Σ x_j)` (Cauchy–Schwarz on the
box index).  This is Phase-2 content; nothing in this file claims it.
-/

import ErdosProblems.Erdos471.External.MathExtras.NumberTheory.Vinogradov.HardCutoffTypeIDistanceSensitive
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Chebyshev
import ErdosProblems.Erdos471.External.AnalyticNT.Bilinear.TypeI
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

namespace MathExtras
namespace Helfgott

open Finset

/-! ## Layer 4: the dyadic box-count log factor -/

/-- **Box-count log factor.**  The number of dyadic blocks needed to cover
`(0, n]` is `Nat.log 2 n + 1 ≤ 3·log n` for `n ≥ 2`
(constant `2/log 2 + ε ≤ 3`). -/
theorem dyadicBoxCount_le_three_log (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowR : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hcpos : (0 : ℝ) < Real.log 2 := by linarith
  have hlogpow : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_pow] at h
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hX_pos : (0 : ℝ) < Real.log n := lt_of_lt_of_le hcpos hlogn
  have key : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log n := by
    have : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 =
        (Nat.log 2 n : ℝ) * Real.log 2 + Real.log 2 := by ring
    rw [this]
    linarith
  have key2 : 2 * Real.log n ≤ 3 * Real.log n * Real.log 2 := by nlinarith
  have h1 : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
      3 * Real.log n * Real.log 2 := key.trans key2
  have h2 : ((Nat.log 2 n : ℝ) + 1) ≤ 3 * Real.log n :=
    le_of_mul_le_mul_right h1 hcpos
  push_cast
  exact h2

/-! ## Layer 1: dyadic partition of `(0, N]` -/

/-- **Dyadic partition.**  `(0, N] = {1} ∪ ⋃_{j ≤ log₂ N} (2^j, min(2^{j+1}, N)]`
(for `N ≥ 1`); each block is of the exact `Ioc K (2K)`-after-truncation
shape consumed by `AnalyticNT.Bilinear.TypeII.typeIISum`. -/
theorem Ioc_zero_eq_dyadic_biUnion (N : ℕ) (hN : 1 ≤ N) :
    Finset.Ioc 0 N =
      insert 1 ((Finset.range (Nat.log 2 N + 1)).biUnion
        (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N))) := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range,
    le_min_iff]
  constructor
  · rintro ⟨hm0, hmN⟩
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    · refine Or.inr ⟨Nat.log 2 (m - 1), ?_, ?_, ?_, hmN⟩
      · have hle : m - 1 ≤ N := by omega
        exact Nat.lt_succ_of_le (Nat.log_mono_right hle)
      · have h := Nat.pow_log_le_self 2 (x := m - 1) (by omega)
        omega
      · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (m - 1)
        omega
  · rintro (rfl | ⟨j, _, hjm, hm2, hmN⟩)
    · exact ⟨one_pos, hN⟩
    · exact ⟨lt_of_le_of_lt (Nat.zero_le _) hjm, hmN⟩

/-- Pairwise disjointness of the dyadic blocks. -/
theorem dyadic_blocks_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint ↑(Finset.range (Nat.log 2 N + 1))
      (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
  have key : ∀ i j : ℕ, i < j →
      Disjoint (Finset.Ioc (2 ^ i) (min (2 ^ (i + 1)) N))
        (Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
    intro i j hij
    refine Finset.disjoint_left.mpr ?_
    intro m hm hm'
    obtain ⟨_, hm2⟩ := Finset.mem_Ioc.mp hm
    obtain ⟨hm3, _⟩ := Finset.mem_Ioc.mp hm'
    have hpow : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij
    have := le_min_iff.mp hm2
    omega
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- **Dyadic decomposition of an exponential sum** (triangle inequality
along the dyadic partition): the full sum over `(0, N]` is bounded by the
`m = 1` term plus the sum of the block norms. -/
theorem norm_sum_Ioc_zero_le_dyadic (f : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ m ∈ Finset.Ioc 0 N, f m‖ ≤
      ‖f 1‖ + ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        ‖∑ m ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f m‖ := by
  classical
  have hnotmem : (1 : ℕ) ∉ (Finset.range (Nat.log 2 N + 1)).biUnion
      (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)) := by
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ioc, not_exists]
    intro j hcon
    obtain ⟨_, h2, _⟩ := hcon
    have h1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  rw [Ioc_zero_eq_dyadic_biUnion N hN, Finset.sum_insert hnotmem]
  refine (norm_add_le _ _).trans ?_
  have hblocks :
      ‖∑ m ∈ (Finset.range (Nat.log 2 N + 1)).biUnion
          (fun j => Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N)), f m‖ ≤
        ∑ j ∈ Finset.range (Nat.log 2 N + 1),
          ‖∑ m ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f m‖ := by
    rw [Finset.sum_biUnion (dyadic_blocks_pairwiseDisjoint N)]
    exact norm_sum_le _ _
  linarith

/-! ## Layer 2a: harmonic-sum bookkeeping -/

/-- Harmonic-sum bound `Σ_{d=1}^N 1/d ≤ 1 + log N` (Mathlib's
`harmonic_le_one_add_log`, recast over `ℝ` on `Icc 1 N`). -/
theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ((d : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have heq : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, ((d : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  linarith [heq ▸ h]

/-- The reciprocal sum over multiples of `g` in `[1, N]` is at most
`(1/g)·H(N)`. -/
theorem sum_Icc_ite_dvd_inv_le (N g : ℕ) (hg : 1 ≤ g) :
    ∑ d ∈ Finset.Icc 1 N, (if g ∣ d then ((d : ℝ))⁻¹ else 0) ≤
      ((g : ℝ))⁻¹ * ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hsub : {d ∈ Finset.Icc 1 N | g ∣ d} ⊆
      (Finset.Icc 1 N).image (fun e => g * e) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hgd⟩ := hd
    refine Finset.mem_image.mpr ⟨d / g, ?_, Nat.mul_div_cancel' hgd⟩
    rw [Finset.mem_Icc]
    refine ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hgd),
      (Nat.div_le_self d g).trans hdN⟩
  calc ∑ d ∈ {d ∈ Finset.Icc 1 N | g ∣ d}, ((d : ℝ))⁻¹
      ≤ ∑ d ∈ (Finset.Icc 1 N).image (fun e => g * e), ((d : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ = ∑ e ∈ Finset.Icc 1 N, (((g * e : ℕ) : ℝ))⁻¹ :=
        Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)
    _ = ((g : ℝ))⁻¹ * ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        push_cast
        rw [mul_inv]

/-! ## Layer 2b: the divisor second moment -/

/-- **Divisor-count second moment** (crude but honest):
`Σ_{m=1}^N τ(m)² ≤ N·(1 + log N)³`.

Double counting: `τ(m)² = Σ_{d₁,d₂ ∣ m} 1`, the inner count of
`m ∈ (0,N]` divisible by both is `⌊N/lcm⌋ ≤ N·gcd/(d₁d₂)`, the gcd is
bounded by the sum of common divisors `g`, and the three resulting
reciprocal sums are each one harmonic factor `H(N) ≤ 1 + log N`. -/
theorem sum_Ioc_card_divisors_sq_le (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2 ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  classical
  set H : ℝ := ∑ e ∈ Finset.Icc 1 N, ((e : ℝ))⁻¹ with hH
  have hH_nonneg : 0 ≤ H := Finset.sum_nonneg fun e _ => by positivity
  have hH_le : H ≤ 1 + Real.log N := sum_Icc_inv_le_one_add_log N
  -- the indicator reciprocal sum
  set A : ℕ → ℝ := fun g => ∑ d ∈ Finset.Icc 1 N,
    (if g ∣ d then ((d : ℝ))⁻¹ else 0) with hA
  have hA_nonneg : ∀ g, 0 ≤ A g := fun g =>
    Finset.sum_nonneg fun d _ => by by_cases h : g ∣ d <;> simp [h]
  have hA_le : ∀ g, 1 ≤ g → A g ≤ ((g : ℝ))⁻¹ * H := fun g hg =>
    sum_Icc_ite_dvd_inv_le N g hg
  -- Step 1: pointwise divisor-count expansion
  have hcard : ∀ m ∈ Finset.Ioc 0 N,
      ((m.divisors.card : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then (1 : ℝ) else 0) := by
    intro m hm
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hm
    have hset : m.divisors = {d ∈ Finset.Icc 1 N | d ∣ m} := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, _⟩
        have hd0 : d ≠ 0 := by
          rintro rfl
          exact absurd (zero_dvd_iff.mp hdvd) (by omega)
        exact ⟨⟨by omega, (Nat.le_of_dvd hm0 hdvd).trans hmN⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hset, Finset.sum_boole]
  -- Step 2+3: expand the square, swap, evaluate the inner sum to ⌊N/lcm⌋
  have hmain : ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
        ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
    calc ∑ m ∈ Finset.Ioc 0 N, ((m.divisors.card : ℕ) : ℝ) ^ 2
        = ∑ m ∈ Finset.Ioc 0 N, ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hcard m hm, sq, Finset.sum_mul_sum]
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc 0 N,
            (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
          have hpt : ∀ m : ℕ,
              (if d₁ ∣ m then (1 : ℝ) else 0) * (if d₂ ∣ m then (1 : ℝ) else 0) =
                (if Nat.lcm d₁ d₂ ∣ m then (1 : ℝ) else 0) := by
            intro m
            by_cases h1 : d₁ ∣ m <;> by_cases h2 : d₂ ∣ m
            · simp [h1, h2, Nat.lcm_dvd h1 h2]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h2 ((Nat.dvd_lcm_right d₁ d₂).trans h)
              simp [h1, h2, this]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
              simp [h1, h2, this]
            · have : ¬ Nat.lcm d₁ d₂ ∣ m := fun h =>
                h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
              simp [h1, h2, this]
          simp_rw [hpt]
          rw [Finset.sum_boole]
          norm_cast
          exact Nat.Ioc_filter_dvd_card_eq_div N (Nat.lcm d₁ d₂)
  rw [hmain]
  -- Step 4: ⌊N/lcm⌋ ≤ N·gcd/(d₁·d₂)
  have hstep4 : ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
      ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤
        ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
          (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
    refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
    obtain ⟨h11, _⟩ := Finset.mem_Icc.mp hd₁
    obtain ⟨h21, _⟩ := Finset.mem_Icc.mp hd₂
    have hlcm0 : 0 < Nat.lcm d₁ d₂ :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    have h1 : ((N / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤ (N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) :=
      Nat.cast_div_le
    refine h1.trans (le_of_eq ?_)
    have hgl : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ) =
        (d₁ : ℝ) * (d₂ : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
    have hgpos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ (by omega)
    have hgcd0 : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← hgl, mul_comm (N : ℝ) ((Nat.gcd d₁ d₂ : ℕ) : ℝ),
      mul_div_mul_left _ _ hgcd0]
  refine hstep4.trans ?_
  -- Step 5: gcd ≤ Σ_g common-divisor indicator
  have hgcd_le : ∀ d₁ ∈ Finset.Icc 1 N, ∀ d₂ ∈ Finset.Icc 1 N,
      ((Nat.gcd d₁ d₂ : ℕ) : ℝ) ≤
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) := by
    intro d₁ hd₁ d₂ hd₂
    obtain ⟨h11, h1N⟩ := Finset.mem_Icc.mp hd₁
    have hgpos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ (by omega)
    have hgle : Nat.gcd d₁ d₂ ≤ d₁ := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left d₁ d₂)
    have hgmem : Nat.gcd d₁ d₂ ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hsingle := Finset.single_le_sum
      (f := fun g => if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0)
      (fun g _ => by by_cases h : g ∣ d₁ ∧ g ∣ d₂ <;> simp [h]) hgmem
    simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using hsingle
  -- Step 6: rearrange to N · Σ_g g · A(g)²
  have hstep6 : ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
      (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤
        (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) := by
    have hpoint : ∀ d₁ ∈ Finset.Icc 1 N, ∀ d₂ ∈ Finset.Icc 1 N,
        (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) ≤
          ∑ g ∈ Finset.Icc 1 N, (N : ℝ) *
            ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) := by
      intro d₁ hd₁ d₂ hd₂
      obtain ⟨h11, _⟩ := Finset.mem_Icc.mp hd₁
      obtain ⟨h21, _⟩ := Finset.mem_Icc.mp hd₂
      have hfact : ∀ g : ℕ,
          (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
            (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) =
          (N : ℝ) * (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) /
            ((d₁ : ℝ) * (d₂ : ℝ)) := by
        intro g
        by_cases h1 : g ∣ d₁
        · by_cases h2 : g ∣ d₂
          · simp only [h1, h2, and_self, if_true, div_eq_mul_inv, mul_inv]
            ring
          · simp [h1, h2]
        · simp [h1]
      simp_rw [hfact]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgcd_le d₁ hd₁ d₂ hd₂) (Nat.cast_nonneg N))
        (by positivity)
    calc ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
          (N : ℝ) * (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ))
        ≤ ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            ∑ g ∈ Finset.Icc 1 N, (N : ℝ) *
              ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ =>
            hpoint d₁ hd₁ d₂ hd₂
      _ = ∑ d₁ ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ g ∈ Finset.Icc 1 N, ∑ d₁ ∈ Finset.Icc 1 N, ∑ d₂ ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
              (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) :=
          Finset.sum_comm
      _ = (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [hA]
          have hterm : ∀ d₁ d₂ : ℕ,
              (N : ℝ) * ((if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) * (g : ℝ)) =
              ((N : ℝ) * (g : ℝ) * (if g ∣ d₁ then ((d₁ : ℝ))⁻¹ else 0)) *
                (if g ∣ d₂ then ((d₂ : ℝ))⁻¹ else 0) := fun _ _ => by ring
          simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
          rw [← Finset.mul_sum]
          ring
  refine hstep6.trans ?_
  -- Step 7: A(g) ≤ H/g, sum the harmonic factors
  have hstep7 : ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g) ≤ H * H * H := by
    have hterm : ∀ g ∈ Finset.Icc 1 N,
        (g : ℝ) * (A g * A g) ≤ ((g : ℝ))⁻¹ * (H * H) := by
      intro g hg
      obtain ⟨hg1, _⟩ := Finset.mem_Icc.mp hg
      have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hg1
      have hAg := hA_le g hg1
      have hAg0 := hA_nonneg g
      have hinvH : 0 ≤ ((g : ℝ))⁻¹ * H := mul_nonneg (by positivity) hH_nonneg
      calc (g : ℝ) * (A g * A g)
          ≤ (g : ℝ) * ((((g : ℝ))⁻¹ * H) * (((g : ℝ))⁻¹ * H)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hgpos)
            exact mul_le_mul hAg hAg hAg0 hinvH
        _ = ((g : ℝ))⁻¹ * (H * H) := by
            field_simp
    calc ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g)
        ≤ ∑ g ∈ Finset.Icc 1 N, ((g : ℝ))⁻¹ * (H * H) := Finset.sum_le_sum hterm
      _ = H * (H * H) := by rw [← Finset.sum_mul, ← hH]
      _ = H * H * H := by ring
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (N : ℝ) * ∑ g ∈ Finset.Icc 1 N, (g : ℝ) * (A g * A g)
      ≤ (N : ℝ) * (H * H * H) := mul_le_mul_of_nonneg_left hstep7 hN0
    _ ≤ (N : ℝ) * ((1 + Real.log N) * (1 + Real.log N) * (1 + Real.log N)) := by
        have h1 : H * H * H ≤ (1 + Real.log N) * (1 + Real.log N) * (1 + Real.log N) := by
          have hl0 : (0 : ℝ) ≤ 1 + Real.log N := hH_nonneg.trans hH_le
          exact mul_le_mul (mul_le_mul hH_le hH_le hH_nonneg hl0) hH_le hH_nonneg
            (mul_nonneg hl0 hl0)
        exact mul_le_mul_of_nonneg_left h1 hN0
    _ = (N : ℝ) * (1 + Real.log N) ^ 3 := by ring

/-! ## Layer 2c: ℓ² bounds for the actual Vaughan Type-II coefficients -/

/-- The inner Vaughan Type-II coefficient `(μ_{>U} * ζ)(m)` is
divisor-bounded: `‖·‖ ≤ τ(m)`.  (Public replica of the private
`vaughanMuHigh_mul_zeta_abs_le_card_divisors` in `MinorArcVaughan`.) -/
theorem norm_vaughanTypeIIBilinearInnerCoeff_le_card_divisors (U m : ℕ) :
    ‖Vinogradov.vaughanTypeIIBilinearInnerCoeff U m‖ ≤
      ((m.divisors.card : ℕ) : ℝ) := by
  unfold Vinogradov.vaughanTypeIIBilinearInnerCoeff
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold Vinogradov.vaughanTypeIIInnerArithmetic
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  calc |∑ d ∈ m.divisors, Vinogradov.vaughanMuHigh U d|
      ≤ ∑ d ∈ m.divisors, |Vinogradov.vaughanMuHigh U d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ m.divisors, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        unfold Vinogradov.vaughanMuHigh
        by_cases h : U < d
        · simp only [ArithmeticFunction.coe_mk, h, if_true]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        · simp [h]
    _ = ((m.divisors.card : ℕ) : ℝ) := by simp

/-- The outer Vaughan Type-II coefficient `Λ_{>V}(d)` is `log`-bounded on
the dyadic box `(D, 2D]`. -/
theorem norm_vaughanTypeIIBilinearCoeff_le_log (V D d : ℕ)
    (hd : d ∈ Finset.Ioc D (2 * D)) :
    ‖Vinogradov.vaughanTypeIIBilinearCoeff V d‖ ≤
      Real.log (2 * (D : ℝ) + 1) := by
  obtain ⟨hd1, hd2⟩ := Finset.mem_Ioc.mp hd
  have hlog0 : 0 ≤ Real.log (2 * (D : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) D])
  unfold Vinogradov.vaughanTypeIIBilinearCoeff
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold Vinogradov.vaughanLambdaHigh
  by_cases h : V < d
  · simp only [ArithmeticFunction.coe_mk, h, if_true]
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have hd0 : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le D) hd1
    refine Real.log_le_log (by exact_mod_cast hd0) ?_
    exact_mod_cast (by omega : d ≤ 2 * D + 1)
  · simp [h, hlog0]

/-- ℓ²-bound for the outer (von-Mangoldt) coefficient on a dyadic box:
`Σ_{d ∈ (D,2D]} ‖Λ_{>V}(d)‖² ≤ D·log²(2D+1)`. -/
theorem dyadicL2Sq_vaughanTypeII_outer_le (V D : ℕ) :
    AnalyticNT.Bilinear.TypeII.dyadicL2Sq
        (Vinogradov.vaughanTypeIIBilinearCoeff V) D ≤
      (D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2 := by
  unfold AnalyticNT.Bilinear.TypeII.dyadicL2Sq
  calc ∑ d ∈ Finset.Ioc D (2 * D),
        ‖Vinogradov.vaughanTypeIIBilinearCoeff V d‖ ^ 2
      ≤ ∑ _d ∈ Finset.Ioc D (2 * D), Real.log (2 * (D : ℝ) + 1) ^ 2 := by
        refine Finset.sum_le_sum fun d hd => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_vaughanTypeIIBilinearCoeff_le_log V D d hd) 2
    _ = (D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Ioc]
        have h2D : 2 * D - D = D := by omega
        rw [h2D, nsmul_eq_mul]

/-- ℓ²-bound for the inner (divisor-bounded) coefficient on a dyadic box:
`Σ_{m ∈ (M,2M]} ‖(μ_{>U}*ζ)(m)‖² ≤ 2M·(1 + log 2M)³` via the divisor
second moment. -/
theorem dyadicL2Sq_vaughanTypeII_inner_le (U M : ℕ) :
    AnalyticNT.Bilinear.TypeII.dyadicL2Sq
        (Vinogradov.vaughanTypeIIBilinearInnerCoeff U) M ≤
      2 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
  unfold AnalyticNT.Bilinear.TypeII.dyadicL2Sq
  calc ∑ m ∈ Finset.Ioc M (2 * M),
        ‖Vinogradov.vaughanTypeIIBilinearInnerCoeff U m‖ ^ 2
      ≤ ∑ m ∈ Finset.Ioc M (2 * M), ((m.divisors.card : ℕ) : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun m _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_vaughanTypeIIBilinearInnerCoeff_le_card_divisors U m) 2
    _ ≤ ∑ m ∈ Finset.Ioc 0 (2 * M), ((m.divisors.card : ℕ) : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc (Nat.zero_le M) le_rfl)
          (fun _ _ _ => sq_nonneg _)
    _ ≤ ((2 * M : ℕ) : ℝ) * (1 + Real.log ((2 * M : ℕ) : ℝ)) ^ 3 :=
        sum_Ioc_card_divisors_sq_le (2 * M)
    _ = 2 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
        push_cast
        ring

/-- `dyadicL2` (square-root) form of the outer bound. -/
theorem dyadicL2_vaughanTypeII_outer_le (V D : ℕ) :
    AnalyticNT.Bilinear.TypeII.dyadicL2
        (Vinogradov.vaughanTypeIIBilinearCoeff V) D ≤
      Real.sqrt ((D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2) := by
  unfold AnalyticNT.Bilinear.TypeII.dyadicL2
  exact Real.sqrt_le_sqrt (dyadicL2Sq_vaughanTypeII_outer_le V D)

/-- `dyadicL2` (square-root) form of the inner bound. -/
theorem dyadicL2_vaughanTypeII_inner_le (U M : ℕ) :
    AnalyticNT.Bilinear.TypeII.dyadicL2
        (Vinogradov.vaughanTypeIIBilinearInnerCoeff U) M ≤
      Real.sqrt (2 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 3) := by
  unfold AnalyticNT.Bilinear.TypeII.dyadicL2
  exact Real.sqrt_le_sqrt (dyadicL2Sq_vaughanTypeII_inner_le U M)

/-! ## Layer 3: single-box application of `typeII_bound_uniform` -/

/-- **Single-box Type-II bound** for the actual Vaughan coefficient pair
`(Λ_{>V}, μ_{>U}*ζ)` on the dyadic box `(D, 2D] × (M, 2M]`: combining the
proof-complete `AnalyticNT.Bilinear.TypeII.typeII_bound_uniform`
(IK Lemma 13.8 / Helfgott §5.1 (5.54)) with the concrete coefficient
ℓ²-bounds above.  The hypotheses `q ≤ Q ≤ qDM + 1`, `2M ≤ Q`,
`|α − a/q| ≤ 1/(qQ)`, reduced `a/q`, and per-box non-resonance are
exactly `typeII_bound_uniform`'s; their discharge from the item-9
center data (with `Q := n`) is Phase-2 plumbing. -/
theorem vaughanTypeII_single_box_bound
    (U V a q D M Q : ℕ) (α : ℝ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hQ_le : (Q : ℝ) ≤ (q : ℝ) * D * M + 1)
    (hM_Q : 2 * M ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q)
    (h_nonres : ∀ k ∈ Finset.Ico 1 (M + 1),
      AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k) ≠ 0) :
    ‖AnalyticNT.Bilinear.TypeII.typeIISum
        (Vinogradov.vaughanTypeIIBilinearCoeff V)
        (Vinogradov.vaughanTypeIIBilinearInnerCoeff U) D M α‖ ≤
      AnalyticNT.Bilinear.TypeII.C_typeII *
        Real.sqrt (1 + Real.log ((q : ℝ) + 1)) *
        Real.sqrt ((D : ℝ) * M / q + D + M + q) *
        Real.sqrt ((D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2) *
        Real.sqrt (2 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 3) := by
  refine (AnalyticNT.Bilinear.TypeII.typeII_bound_uniform a q α D M Q hq hQ hQ_le
    hM_Q hα hcop _ _ h_nonres).trans ?_
  have hpre : 0 ≤ AnalyticNT.Bilinear.TypeII.C_typeII *
      Real.sqrt (1 + Real.log ((q : ℝ) + 1)) *
      Real.sqrt ((D : ℝ) * M / q + D + M + q) :=
    mul_nonneg (mul_nonneg (le_of_lt AnalyticNT.Bilinear.TypeII.C_typeII_pos)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hL2b_nonneg : 0 ≤ AnalyticNT.Bilinear.TypeII.dyadicL2
      (Vinogradov.vaughanTypeIIBilinearInnerCoeff U) M := by
    unfold AnalyticNT.Bilinear.TypeII.dyadicL2
    exact Real.sqrt_nonneg _
  refine mul_le_mul ?_ (dyadicL2_vaughanTypeII_inner_le U M) hL2b_nonneg
    (mul_nonneg hpre (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left (dyadicL2_vaughanTypeII_outer_le V D) hpre

/-! ## Layer 5: `log`-part absorption at the witness center -/

/-- A reduced witness center `a/q` with `q ≥ 2` and window `1/(qn)`
(`n ≥ 2`) keeps `α` at distance `≥ 1/(2q)` from EVERY integer: the
center is `≥ 1/q` from each integer (reduced, non-integer), and the
window eats at most half of that. -/
theorem center_round_separation (n a q : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (hn2 : 2 ≤ n) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * n)) :
    ∀ k : ℤ, 1 / (2 * (q : ℝ)) ≤ |α - (k : ℝ)| := by
  intro k
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  -- the numerator `a − kq` is a nonzero integer
  have hint : (a : ℤ) - k * q ≠ 0 := by
    intro hzero
    have hdvd : (q : ℤ) ∣ (a : ℤ) := ⟨k, by linarith⟩
    have hdvdN : q ∣ a := by exact_mod_cast hdvd
    have hg : Nat.gcd a q = 1 := hcop
    have hq1 : q ∣ 1 := by
      have h := Nat.dvd_gcd hdvdN (dvd_refl q)
      rwa [hg] at h
    have := Nat.le_of_dvd one_pos hq1
    omega
  have habs : (1 : ℝ) ≤ |(a : ℝ) - (k : ℝ) * q| := by
    have h1 : (1 : ℤ) ≤ |(a : ℤ) - k * q| := Int.one_le_abs hint
    exact_mod_cast h1
  -- the center is ≥ 1/q from k
  have h1q : 1 / (q : ℝ) ≤ |(a : ℝ) / q - (k : ℝ)| := by
    have hak : (a : ℝ) / q - (k : ℝ) = ((a : ℝ) - (k : ℝ) * q) / q := by
      field_simp
    rw [hak, abs_div, abs_of_pos hqR]
    exact div_le_div_of_nonneg_right habs hqR.le
  -- triangle: |α − k| ≥ |a/q − k| − |a/q − α|
  have htri : |(a : ℝ) / q - (k : ℝ)| - |α - (a : ℝ) / q| ≤ |α - (k : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub ((a : ℝ) / q - (k : ℝ)) ((a : ℝ) / q - α)
    have hxy : ((a : ℝ) / q - (k : ℝ)) - ((a : ℝ) / q - α) = α - (k : ℝ) := by ring
    rw [hxy] at h
    rwa [abs_sub_comm ((a : ℝ) / q) α] at h
  -- window ≤ half the center separation
  have hqn : 1 / ((q : ℝ) * n) ≤ 1 / (2 * q) := by
    have h2q : (0 : ℝ) < 2 * q := by linarith
    have hle : 2 * (q : ℝ) ≤ (q : ℝ) * n := by nlinarith
    exact one_div_le_one_div_of_le h2q hle
  have h12 : 1 / (q : ℝ) - 1 / (2 * q) = 1 / (2 * q) := by
    field_simp
    ring
  have hd := hdist.le.trans hqn
  linarith

/-- **`log`-part absorption.**  Under the item-9 witness-center geometry
(`q ≥ 2` reduced, window `1/(qn)`), the pure-`log` exponential sum obeys
`‖Σ_{m≤n} log m·e(mα)‖ ≤ 2q·log n` — consuming the proven P2
distance-sensitive kernel at separation `δ = 1/(2q)`. -/
theorem norm_log_expSum_le_of_center (n a q : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (hn2 : 2 ≤ n) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * n)) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      2 * (q : ℝ) * Real.log n := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2
  have hsep := center_round_separation n a q α hq2 hn2 hcop hdist
  have hδ : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
  have h := hardCutoffVaughanTypeILogDistanceSensitiveBound_separation
    (K := 1) (n := n) (α := α) (δ := 1 / (2 * (q : ℝ))) zero_le_one hδ hsep
    (hardCutoffVaughanTypeILogDistanceSensitiveBound_holds n α)
  refine h.trans (le_of_eq ?_)
  rw [one_mul, one_div, div_eq_mul_inv, inv_inv]
  ring

/-! ## Layer 5b: the small pieces (`Λ_{≤V}` and the trivial `Λ − log` bound) -/

/-- The low Vaughan piece is tiny: `‖Σ_{m≤N} Λ_{≤V}(m)e(mα)‖ ≤ V·log V`. -/
theorem norm_lambdaLow_expSum_le (V N : ℕ) (α : ℝ) (hV : 1 ≤ V) :
    ‖Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) N α‖ ≤
      (V : ℝ) * Real.log V := by
  have hlogV : 0 ≤ Real.log (V : ℝ) := Real.log_nonneg (by exact_mod_cast hV)
  rw [arithmeticExpSum_eq_sum_Ioc]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Finset.Ioc 0 N,
        ‖((Vinogradov.vaughanLambdaLow V m : ℝ) : ℂ) * Vinogradov.addChar α m‖
      ≤ ∑ m ∈ Finset.Ioc 0 N, (if m ≤ V then Real.log (V : ℝ) else 0) := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨hm0, _⟩ := Finset.mem_Ioc.mp hm
        rw [norm_mul, Vinogradov.norm_addChar, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        unfold Vinogradov.vaughanLambdaLow
        by_cases h : m ≤ V
        · simp only [ArithmeticFunction.coe_mk, h, if_true]
          rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
          exact Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast h)
        · simp [h]
    _ ≤ (V : ℝ) * Real.log V := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ hlogV
        have hsub : {m ∈ Finset.Ioc 0 N | m ≤ V} ⊆ Finset.Ioc 0 V := by
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
          exact ⟨hm.1.1, hm.2⟩
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Ioc] at hcard
        exact_mod_cast hcard.trans (by omega)

/-- Pointwise subtraction for arithmetic functions (no `sub_apply` in
Mathlib's `ArithmeticFunction` API). -/
theorem arithmeticFunction_sub_apply (f g : ArithmeticFunction ℝ) (m : ℕ) :
    (f - g) m = f m - g m := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    ← sub_eq_add_neg]

/-- Trivial bound `‖Σ_{m≤n}(Λ−log)(m)e(mα)‖ ≤ 2n·log n` (used on the
`q = 1` witness branch, where the envelope is `≥ n·(log n)⁴`). -/
theorem norm_lambda_sub_log_expSum_le_trivial (n : ℕ) (α : ℝ) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α‖ ≤
      2 * (n : ℝ) * Real.log n := by
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  rw [arithmeticExpSum_eq_sum_Ioc]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Finset.Ioc 0 n,
        ‖(((ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) m : ℝ) : ℂ) *
          Vinogradov.addChar α m‖
      ≤ ∑ _m ∈ Finset.Ioc 0 n, 2 * Real.log (n : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨hm0, hmn⟩ := Finset.mem_Ioc.mp hm
        rw [norm_mul, Vinogradov.norm_addChar, mul_one, Complex.norm_real,
          Real.norm_eq_abs, arithmeticFunction_sub_apply]
        have hlm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast hmn)
        calc |ArithmeticFunction.vonMangoldt m - ArithmeticFunction.log m|
            ≤ |ArithmeticFunction.vonMangoldt m| + |ArithmeticFunction.log m| :=
              abs_sub _ _
          _ = ArithmeticFunction.vonMangoldt m + Real.log (m : ℝ) := by
              rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
                ArithmeticFunction.log_apply,
                abs_of_nonneg (Real.log_natCast_nonneg m)]
          _ ≤ 2 * Real.log (n : ℝ) := by
              have h1 := ArithmeticFunction.vonMangoldt_le_log (n := m)
              linarith
    _ = 2 * (n : ℝ) * Real.log n := by
        rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        ring

/-! ## Phase-2 obligations and the assembly -/

/-- Vaughan bilinear cutoff `U = V = ⌊n^{2/5}⌋` — the classical choice
producing the `n^{4/5}` envelope term (IK Lemma 13.6 / Vaughan). -/
def vaughanCutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((2 : ℝ) / 5)⌋₊

theorem one_le_vaughanCutoff (n : ℕ) (hn : 1 ≤ n) : 1 ≤ vaughanCutoff n := by
  unfold vaughanCutoff
  rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  push_cast
  exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)

theorem vaughanCutoff_le_rpow (n : ℕ) :
    ((vaughanCutoff n : ℕ) : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **Phase-2 obligation (Type-I piece).**  The Vaughan Type-I bilinear
sum at cutoff `⌊n^{2/5}⌋` obeys the classical envelope under the witness
center geometry.  Attack route: fixed-outer form
(`vaughanTypeIBilinearSum_eq_fixed_outer`-style), per-`d` geometric
kernel from `HardCutoffTypeIDistanceSensitive`, and the standard
`Σ_{d≤D} min(N/d, 1/‖dα‖) ≪ (N/q + D + q)(1+log q)`-type harmonic sum
(cf. `AnalyticNT.Bilinear.TypeI`). -/
def vaughanTypeIPieceQSensitiveEnvelopeBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n a q : ℕ, ∀ α : ℝ,
    3 ≤ n → 2 ≤ q → q ≤ n → a < q → Nat.Coprime a q →
    |α - (a : ℝ) / q| < 1 / ((q : ℝ) * n) →
      ‖Vinogradov.vaughanTypeIBilinearSum
          (vaughanCutoff n) (vaughanCutoff n) n α‖ ≤
        K * hardCutoffVaughanTypeIIVinogradovEnvelope n q

/-- **Phase-2 obligation (Type-II piece).**  The Vaughan Type-II bilinear
sum at cutoff `⌊n^{2/5}⌋` obeys the classical envelope under the witness
center geometry.  Attack route: dyadic boxes via
`norm_sum_Ioc_zero_le_dyadic`, hyperbola truncation, per-box
`vaughanTypeII_single_box_bound`, box count via
`dyadicBoxCount_le_three_log`, ℓ² bookkeeping via
`dyadicL2Sq_vaughanTypeII_outer_le`/`…_inner_le`, plus non-resonance
handling for the finitely many `k` with `αk ∈ ℤ` (Phase-2 design:
either `q > 2M` on the relevant boxes or a separate rational-α branch). -/
def vaughanTypeIIPieceQSensitiveEnvelopeBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n a q : ℕ, ∀ α : ℝ,
    3 ≤ n → 2 ≤ q → q ≤ n → a < q → Nat.Coprime a q →
    |α - (a : ℝ) / q| < 1 / ((q : ℝ) * n) →
      ‖Vinogradov.vaughanTypeIIBilinearSum
          (vaughanCutoff n) (vaughanCutoff n) n α‖ ≤
        K * hardCutoffVaughanTypeIIVinogradovEnvelope n q

theorem envelope_nonneg (n q : ℕ) :
    0 ≤ hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
  unfold hardCutoffVaughanTypeIIVinogradovEnvelope
  positivity

theorem one_le_log_of_three_le (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  rw [Real.le_log_iff_exp_le hn0]
  calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    _ ≤ 3 := by norm_num
    _ ≤ (n : ℝ) := by exact_mod_cast hn

theorem cast_le_sqrt_mul (q n : ℕ) (hqn : q ≤ n) :
    (q : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hle : (q : ℝ) * q ≤ (q : ℝ) * n := by
    have hq : ((q : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
    nlinarith
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_mul_self hq0] at h

/-- **P3 Phase-1 assembly.**  The corrected item-9 target
`hardCutoffVaughanTypeIIHighDenominatorCenterQSensitiveTargetParam U`
holds for EVERY cutoff `U` once the two Phase-2 piece obligations are
discharged: Vaughan's identity at `U = V = ⌊n^{2/5}⌋`
(`vaughan_to_typeI_typeII_bilinear_full`, proven) splits `Λ − log` into
`Λ_{≤V}`-piece + Type-I + Type-II − `log`-piece; the `Λ_{≤V}` piece is
`≤ V·log V ≤ n^{4/5}(log n)⁴`-absorbed, the `log` piece is
`≤ 2q·log n ≤ 2√(qn)(log n)⁴`-absorbed for `q ≥ 2`
(`norm_log_expSum_le_of_center`), and the `q = 1` witness branch is
closed outright by the trivial bound against the `n·(log n)⁴` envelope
floor.  Constants: `Npow = 3`, `Kpow = KI + KII + 4`. -/
theorem hardCutoffVaughanTypeIIQSensitiveTarget_of_pieces
    (hI : vaughanTypeIPieceQSensitiveEnvelopeBound)
    (hII : vaughanTypeIIPieceQSensitiveEnvelopeBound) :
    ∀ U : ℕ → ℕ,
      hardCutoffVaughanTypeIIHighDenominatorCenterQSensitiveTargetParam U := by
  obtain ⟨KI, hKI, hIb⟩ := hI
  obtain ⟨KII, hKII, hIIb⟩ := hII
  intro U
  refine ⟨3, KI + KII + 4, by linarith, ?_⟩
  intro n hn3 _hn2 α _hα _hwin a q hcen hdist _hUq
  obtain ⟨hqn, hq0, haq, hcop⟩ := hcen
  unfold hardCutoffVaughanTypeIILambdaSubLogQSensitiveBound
  set E := hardCutoffVaughanTypeIIVinogradovEnvelope n q with hE
  have hE0 : 0 ≤ E := envelope_nonneg n q
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hlog4 : Real.log n ≤ (Real.log n) ^ 4 := by
    calc Real.log (n : ℝ) = Real.log n * 1 := (mul_one _).symm
      _ ≤ Real.log n * (Real.log n) ^ 3 := by
          refine mul_le_mul_of_nonneg_left ?_ hlog0
          calc (1 : ℝ) = 1 ^ 3 := by norm_num
            _ ≤ (Real.log n) ^ 3 := pow_le_pow_left₀ zero_le_one hlog1 3
      _ = (Real.log n) ^ 4 := by ring
  have hEsqrt : Real.sqrt ((q : ℝ) * n) * (Real.log n) ^ 4 ≤ E := by
    rw [hE]
    unfold hardCutoffVaughanTypeIIVinogradovEnvelope
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog0 4)
    have h1 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    linarith
  have hE45 : (n : ℝ) ^ ((4 : ℝ) / 5) * (Real.log n) ^ 4 ≤ E := by
    rw [hE]
    unfold hardCutoffVaughanTypeIIVinogradovEnvelope
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog0 4)
    have h1 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q := by positivity
    have h3 : (0 : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := Real.sqrt_nonneg _
    linarith
  by_cases hq1 : q = 1
  · -- q = 1 witness branch: trivial bound against the n·log⁴n floor
    subst hq1
    have hEn : (n : ℝ) * Real.log n ≤ E := by
      rw [hE]
      unfold hardCutoffVaughanTypeIIVinogradovEnvelope
      push_cast [Real.sqrt_one, one_mul]
      rw [div_one]
      refine le_trans (mul_le_mul_of_nonneg_left hlog4 (le_of_lt hnR)) ?_
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog0 4)
      have h2 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have h3 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      linarith
    have htriv := norm_lambda_sub_log_expSum_le_trivial n α
    calc ‖Vinogradov.arithmeticExpSum
          (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α‖
        ≤ 2 * (n : ℝ) * Real.log n := htriv
      _ ≤ 2 * E := by linarith
      _ ≤ (KI + KII + 4) * E := by nlinarith
  · -- q ≥ 2 branch: Vaughan decomposition + piece obligations
    have hq2 : 2 ≤ q := by omega
    have hn2' : 2 ≤ n := by omega
    set V := vaughanCutoff n with hV
    have hV1 : 1 ≤ V := one_le_vaughanCutoff n (by omega)
    have hdecomp := Vinogradov.vaughan_to_typeI_typeII_bilinear_full
      V V n hV1 hV1 α
    have hsub : Vinogradov.arithmeticExpSum
        (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α =
        Vinogradov.vonMangoldtExpSum α n -
          Vinogradov.arithmeticExpSum
            (ArithmeticFunction.log : ArithmeticFunction ℝ) n α := by
      unfold Vinogradov.arithmeticExpSum Vinogradov.vonMangoldtExpSum
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [arithmeticFunction_sub_apply]
      push_cast
      ring
    rw [hsub, hdecomp]
    have hnorm : ‖(Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α +
          Vinogradov.vaughanTypeIBilinearSum V V n α +
          Vinogradov.vaughanTypeIIBilinearSum V V n α) -
          Vinogradov.arithmeticExpSum
            (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
        ‖Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α‖ +
          ‖Vinogradov.vaughanTypeIBilinearSum V V n α‖ +
          ‖Vinogradov.vaughanTypeIIBilinearSum V V n α‖ +
          ‖Vinogradov.arithmeticExpSum
            (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ := by
      refine (norm_sub_le _ _).trans ?_
      have h1 := norm_add_le
        (Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α +
          Vinogradov.vaughanTypeIBilinearSum V V n α)
        (Vinogradov.vaughanTypeIIBilinearSum V V n α)
      have h2 := norm_add_le
        (Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α)
        (Vinogradov.vaughanTypeIBilinearSum V V n α)
      linarith
    refine hnorm.trans ?_
    -- the four pieces
    have hlow : ‖Vinogradov.arithmeticExpSum
        (Vinogradov.vaughanLambdaLow V) n α‖ ≤ E := by
      refine (norm_lambdaLow_expSum_le V n α hV1).trans ?_
      have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
      have hVle : (V : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
        refine (vaughanCutoff_le_rpow n).trans ?_
        exact Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
      have hVn : (V : ℝ) ≤ (n : ℝ) := by
        refine (vaughanCutoff_le_rpow n).trans ?_
        calc (n : ℝ) ^ ((2 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
          _ = (n : ℝ) := Real.rpow_one _
      have hVpos : (0 : ℝ) < V := by exact_mod_cast hV1
      have hlogV : Real.log (V : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hVpos hVn
      calc (V : ℝ) * Real.log V
          ≤ (n : ℝ) ^ ((4 : ℝ) / 5) * (Real.log n) ^ 4 :=
            mul_le_mul hVle (hlogV.trans hlog4)
              (Real.log_nonneg (by exact_mod_cast hV1))
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ ≤ E := hE45
    have hTI : ‖Vinogradov.vaughanTypeIBilinearSum V V n α‖ ≤ KI * E := by
      have h := hIb n a q α hn3 hq2 hqn haq hcop hdist
      rwa [← hV, ← hE] at h
    have hTII : ‖Vinogradov.vaughanTypeIIBilinearSum V V n α‖ ≤ KII * E := by
      have h := hIIb n a q α hn3 hq2 hqn haq hcop hdist
      rwa [← hV, ← hE] at h
    have hlogpart : ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤ 2 * E := by
      refine (norm_log_expSum_le_of_center n a q α hq2 hn2' hcop hdist).trans ?_
      have hq_sqrt : (q : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := cast_le_sqrt_mul q n hqn
      have h1 : (q : ℝ) * Real.log n ≤ Real.sqrt ((q : ℝ) * n) * (Real.log n) ^ 4 :=
        mul_le_mul hq_sqrt hlog4 hlog0 (Real.sqrt_nonneg _)
      linarith
    calc ‖Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α‖ +
          ‖Vinogradov.vaughanTypeIBilinearSum V V n α‖ +
          ‖Vinogradov.vaughanTypeIIBilinearSum V V n α‖ +
          ‖Vinogradov.arithmeticExpSum
            (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖
        ≤ E + KI * E + KII * E + 2 * E := by linarith
      _ = (KI + KII + 3) * E := by ring
      _ ≤ (KI + KII + 4) * E := by nlinarith

/-! ## Phase 2 (Type-II piece), Layer 6: coefficient-vanishing and
nearest-integer-distance helpers -/

/-- The inner Vaughan Type-II coefficient `(μ_{>U}*ζ)(m)` vanishes for
`m ≤ U` (every divisor of `m` is `≤ U`, killing each `μ_{>U}` factor). -/
theorem vaughanTypeIIBilinearInnerCoeff_eq_zero_of_le (U m : ℕ) (h : m ≤ U) :
    Vinogradov.vaughanTypeIIBilinearInnerCoeff U m = 0 := by
  have hz : Vinogradov.vaughanTypeIIInnerArithmetic U m = 0 := by
    unfold Vinogradov.vaughanTypeIIInnerArithmetic
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    refine Finset.sum_eq_zero fun d hd => ?_
    have hdm : d ≤ m := Nat.divisor_le hd
    unfold Vinogradov.vaughanMuHigh
    simp only [ArithmeticFunction.coe_mk]
    rw [if_neg (by omega)]
  unfold Vinogradov.vaughanTypeIIBilinearInnerCoeff
  rw [hz]
  norm_num

/-- The outer Vaughan Type-II coefficient `Λ_{>V}(d)` vanishes for `d ≤ V`. -/
theorem vaughanTypeIIBilinearCoeff_eq_zero_of_le (V d : ℕ) (h : d ≤ V) :
    Vinogradov.vaughanTypeIIBilinearCoeff V d = 0 := by
  unfold Vinogradov.vaughanTypeIIBilinearCoeff Vinogradov.vaughanLambdaHigh
  simp only [ArithmeticFunction.coe_mk]
  rw [if_neg (by omega)]
  norm_num

/-- `TypeII.nearestIntDist` is the distance to the nearest integer. -/
theorem typeII_nearestIntDist_eq_abs_sub_round (x : ℝ) :
    AnalyticNT.Bilinear.TypeII.nearestIntDist x = |x - (round x : ℝ)| := by
  unfold AnalyticNT.Bilinear.TypeII.nearestIntDist
  exact (abs_sub_round_eq_min x).symm

/-- The nearest-integer distance is even. -/
theorem typeII_nearestIntDist_neg (x : ℝ) :
    AnalyticNT.Bilinear.TypeII.nearestIntDist (-x) =
      AnalyticNT.Bilinear.TypeII.nearestIntDist x := by
  unfold AnalyticNT.Bilinear.TypeII.nearestIntDist
  by_cases hx : Int.fract x = 0
  · rw [Int.fract_neg_eq_zero.mpr hx, hx]
  · rw [Int.fract_neg hx, sub_sub_cancel]
    exact min_comm _ _

/-- Vanishing of the nearest-integer distance characterizes integers
(in `round` form). -/
theorem typeII_nearestIntDist_eq_zero_iff (x : ℝ) :
    AnalyticNT.Bilinear.TypeII.nearestIntDist x = 0 ↔ (round x : ℝ) = x := by
  rw [typeII_nearestIntDist_eq_abs_sub_round, abs_eq_zero, sub_eq_zero]
  exact eq_comm

/-- **Geometric kernel over an arbitrary block.**  For non-integer
frequency `β`, every block sum of the additive character obeys
`‖Σ_{d∈(A,B]} e(dβ)‖ ≤ 1/(2‖β‖)` (closed geometric series + Jordan). -/
theorem norm_addChar_sum_Ioc_le_round_block (β : ℝ)
    (h : (round β : ℝ) ≠ β) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ioc A B, Vinogradov.addChar β d‖ ≤
      1 / (2 * |β - (round β : ℝ)|) := by
  have hd_pos : 0 < |β - (round β : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
  rcases Nat.lt_or_ge B A with hBA | hAB
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity
  · have hnotint : ¬ ∃ j : ℤ, (j : ℝ) = β := by
      rintro ⟨j, rfl⟩
      exact h (by rw [round_intCast])
    have hζ : Vinogradov.addChar β 1 ≠ 1 := by
      intro hc
      exact hnotint ((Vinogradov.addChar_one_eq_one_iff β).mp hc)
    have hIoc : Finset.Ioc A B = Finset.Ico (A + 1) (B + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hsum : (∑ d ∈ Finset.Ico (A + 1) (B + 1), Vinogradov.addChar β d)
        = ((Vinogradov.addChar β 1) ^ (B + 1) -
            (Vinogradov.addChar β 1) ^ (A + 1)) /
          (Vinogradov.addChar β 1 - 1) := by
      rw [show (∑ d ∈ Finset.Ico (A + 1) (B + 1), Vinogradov.addChar β d)
          = ∑ d ∈ Finset.Ico (A + 1) (B + 1), (Vinogradov.addChar β 1) ^ d from
        Finset.sum_congr rfl fun d _ => Vinogradov.addChar_eq_addChar_one_pow β d]
      exact geom_sum_Ico hζ (by omega)
    rw [hIoc, hsum, norm_div]
    have hnum : ‖(Vinogradov.addChar β 1) ^ (B + 1) -
        (Vinogradov.addChar β 1) ^ (A + 1)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, norm_pow, Vinogradov.norm_addChar]
      norm_num
    have hden : 2 * (2 * |β - (round β : ℝ)|) ≤ ‖Vinogradov.addChar β 1 - 1‖ := by
      rw [Vinogradov.norm_addChar_one_sub_one_eq_two_abs_sin]
      have hj := Vinogradov.sin_pi_lower_bound_dist_int β
      linarith
    have h4d : 0 < 2 * (2 * |β - (round β : ℝ)|) := by linarith
    calc ‖(Vinogradov.addChar β 1) ^ (B + 1) -
          (Vinogradov.addChar β 1) ^ (A + 1)‖ / ‖Vinogradov.addChar β 1 - 1‖
        ≤ 2 / (2 * (2 * |β - (round β : ℝ)|)) :=
          div_le_div₀ (by norm_num) hnum h4d hden
      _ = 1 / (2 * |β - (round β : ℝ)|) := by
          have hd_ne : |β - (round β : ℝ)| ≠ 0 := ne_of_gt hd_pos
          field_simp

/-- **Resonance dichotomy.**  Under the witness-center window
`|α − a/q| < 1/(qn)` (reduced `a/q`), a frequency `α·Δ` with
`|Δ| ≤ n` can only be an integer when `q ∣ Δ`: the integer
`(round(αΔ))·q − a·Δ = Δ·q·(α − a/q)` has absolute value `< 1`,
hence vanishes, forcing `q ∣ aΔ` and (coprimality) `q ∣ Δ`. -/
theorem typeII_nearestIntDist_ne_zero_of_not_dvd
    (n a q : ℕ) (α : ℝ) (hq : 1 ≤ q) (hn : 1 ≤ n) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * n))
    (Δ : ℤ) (hΔn : |Δ| ≤ (n : ℤ)) (hndvd : ¬ ((q : ℤ) ∣ Δ)) :
    AnalyticNT.Bilinear.TypeII.nearestIntDist (α * (Δ : ℝ)) ≠ 0 := by
  intro hres
  have hround : (round (α * (Δ : ℝ)) : ℝ) = α * (Δ : ℝ) :=
    (typeII_nearestIntDist_eq_zero_iff _).mp hres
  set j : ℤ := round (α * (Δ : ℝ)) with hj
  have hΔ0 : Δ ≠ 0 := by
    rintro rfl
    exact hndvd (dvd_zero _)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ((j * q - a * Δ : ℤ) : ℝ) =
      (Δ : ℝ) * q * (α - (a : ℝ) / q) := by
    push_cast
    rw [hround]
    field_simp
  have hΔR_pos : (0 : ℝ) < |(Δ : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hΔ0
  have hΔR_le : |(Δ : ℝ)| ≤ (n : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hΔn
  have habs : |((j * q - a * Δ : ℤ) : ℝ)| < 1 := by
    rw [hcast, abs_mul, abs_mul, abs_of_pos hqR]
    calc |(Δ : ℝ)| * q * |α - (a : ℝ) / q|
        < |(Δ : ℝ)| * q * (1 / ((q : ℝ) * n)) := by
          refine mul_lt_mul_of_pos_left hdist ?_
          positivity
      _ = |(Δ : ℝ)| / n := by field_simp
      _ ≤ 1 := by
          rw [div_le_one hnR]
          exact hΔR_le
  have hN0 : j * q - a * Δ = 0 := by
    have h1 : |j * q - a * Δ| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp h1
  have hdvd : (q : ℤ) ∣ (a : ℤ) * Δ := ⟨j, by linear_combination (-1 : ℤ) * hN0⟩
  have hcop' : IsCoprime (q : ℤ) (a : ℤ) :=
    Nat.Coprime.isCoprime (Nat.Coprime.symm hcop)
  exact hndvd (hcop'.dvd_of_dvd_mul_left hdvd)

/-- Residue classes inside `(0, K]` have at most `K/q + 1` elements. -/
theorem card_residue_class_Ioc_le (K q r : ℕ) :
    ((Finset.Ioc 0 K).filter (fun m => m % q = r)).card ≤ K / q + 1 := by
  classical
  have hmaps : ∀ m ∈ (Finset.Ioc 0 K).filter (fun m => m % q = r),
      m / q ∈ Finset.range (K / q + 1) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.2))
  have hinj : ∀ x ∈ (Finset.Ioc 0 K).filter (fun m => m % q = r),
      ∀ y ∈ (Finset.Ioc 0 K).filter (fun m => m % q = r),
        x / q = y / q → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hy
    calc x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
      _ = q * (y / q) + y % q := by rw [hxy, hx.2, hy.2]
      _ = y := Nat.div_add_mod y q
  calc ((Finset.Ioc 0 K).filter (fun m => m % q = r)).card
      ≤ (Finset.range (K / q + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = K / q + 1 := Finset.card_range _

/-! ## Layer 7: hyperbola truncation onto a common inner range -/

theorem range_succ_eq_insert_Ioc (X : ℕ) :
    Finset.range (X + 1) = insert 0 (Finset.Ioc 0 X) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
  omega

/-- **Hyperbola truncation.**  The per-`d` inner Vaughan Type-II sum over
`m ≤ n/d` equals the sum over the common dyadic range `(0, K]`
(`n/d ≤ K`) gated by the hyperbola condition `d·m ≤ n`. -/
theorem inner_sum_eq_truncated (U n d K : ℕ) (α : ℝ) (hd : 0 < d)
    (hK : n / d ≤ K) :
    ∑ m ∈ Finset.range (n / d + 1),
        Vinogradov.vaughanTypeIIBilinearInnerCoeff U m *
          Vinogradov.addChar α (d * m) =
      ∑ m ∈ Finset.Ioc 0 K,
        if d * m ≤ n then
          Vinogradov.vaughanTypeIIBilinearInnerCoeff U m *
            Vinogradov.addChar α (d * m)
        else 0 := by
  rw [range_succ_eq_insert_Ioc, Finset.sum_insert (by simp),
    vaughanTypeIIBilinearInnerCoeff_eq_zero_of_le U 0 (Nat.zero_le U),
    zero_mul, zero_add, ← Finset.sum_filter]
  refine (Finset.sum_congr ?_ fun m _ => rfl)
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_filter]
  constructor
  · rintro ⟨h0, hle⟩
    have h1 : m * d ≤ n := (Nat.le_div_iff_mul_le hd).mp hle
    exact ⟨⟨h0, hle.trans hK⟩, by rwa [Nat.mul_comm] at h1⟩
  · rintro ⟨⟨h0, _⟩, hdm⟩
    exact ⟨h0, (Nat.le_div_iff_mul_le hd).mpr (by rwa [Nat.mul_comm] at hdm)⟩

/-- Conjugate-product of additive characters at a common outer `d`:
`e(d m₁ α)·conj(e(d m₂ α)) = e(d·(α m₁ − α m₂))`. -/
theorem addChar_mul_conj_addChar (α : ℝ) (d m₁ m₂ : ℕ) :
    Vinogradov.addChar α (d * m₁) *
        (starRingEnd ℂ) (Vinogradov.addChar α (d * m₂)) =
      Vinogradov.addChar (α * m₁ - α * m₂) d := by
  unfold Vinogradov.addChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
    map_ofNat]
  push_cast
  ring

/-- The surviving outer `d`-set of a hyperbola-truncated pair is an
interval. -/
theorem pair_d_filter_eq_Ioc (n D D₂ m₁ m₂ : ℕ) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    (Finset.Ioc D D₂).filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n) =
      Finset.Ioc D (min D₂ (min (n / m₁) (n / m₂))) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
  constructor
  · rintro ⟨⟨hD, hD₂⟩, h1, h2⟩
    exact ⟨hD, hD₂, (Nat.le_div_iff_mul_le hm₁).mpr h1,
      (Nat.le_div_iff_mul_le hm₂).mpr h2⟩
  · rintro ⟨hD, hD₂, h1, h2⟩
    exact ⟨⟨hD, hD₂⟩, (Nat.le_div_iff_mul_le hm₁).mp h1,
      (Nat.le_div_iff_mul_le hm₂).mp h2⟩

/-! ## Layer 8: block `ℓ²`-mass expansion into pair kernels -/

private lemma truncated_pair_term_eq (i : ℕ → ℂ) (n : ℕ) (α : ℝ)
    (d m₁ m₂ : ℕ) :
    (if d * m₁ ≤ n then i m₁ * Vinogradov.addChar α (d * m₁) else 0) *
      (starRingEnd ℂ)
        (if d * m₂ ≤ n then i m₂ * Vinogradov.addChar α (d * m₂) else 0) =
      if d * m₁ ≤ n ∧ d * m₂ ≤ n then
        (i m₁ * (starRingEnd ℂ) (i m₂)) *
          Vinogradov.addChar (α * m₁ - α * m₂) d
      else 0 := by
  by_cases h1 : d * m₁ ≤ n
  · by_cases h2 : d * m₂ ≤ n
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, map_mul, mul_mul_mul_comm,
        addChar_mul_conj_addChar]
    · rw [if_pos h1, if_neg h2, map_zero, mul_zero,
        if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, zero_mul, if_neg (fun h => h1 h.1)]

/-- **Block `ℓ²`-mass expansion.**  The outer-block sum of squared inner
norms is bounded by the bilinear pair sum against the truncated
`d`-geometric kernels (Schur shape). -/
theorem block_l2_mass_le_pair_sum
    (i : ℕ → ℂ) (B X : Finset ℕ) (n : ℕ) (α : ℝ) :
    ∑ d ∈ B,
        ‖∑ m ∈ X,
          if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ ^ 2 ≤
      ∑ m₁ ∈ X, ∑ m₂ ∈ X, ‖i m₁‖ * ‖i m₂‖ *
        ‖∑ d ∈ B.filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
            Vinogradov.addChar (α * m₁ - α * m₂) d‖ := by
  classical
  have h1 : ∑ d ∈ B,
      ‖∑ m ∈ X,
        if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ ^ 2 =
      (∑ m₁ ∈ X, ∑ m₂ ∈ X, (i m₁ * (starRingEnd ℂ) (i m₂)) *
        ∑ d ∈ B.filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
          Vinogradov.addChar (α * m₁ - α * m₂) d).re := by
    have hWd : ∀ d : ℕ,
        ‖∑ m ∈ X,
          if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ ^ 2 =
        (∑ m₁ ∈ X, ∑ m₂ ∈ X,
          if d * m₁ ≤ n ∧ d * m₂ ≤ n then
            (i m₁ * (starRingEnd ℂ) (i m₂)) *
              Vinogradov.addChar (α * m₁ - α * m₂) d
          else 0).re := by
      intro d
      set W : ℂ := ∑ m ∈ X,
        if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0 with hWdef
      have hsq : ‖W‖ ^ 2 = (W * (starRingEnd ℂ) W).re := by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [hsq]
      congr 1
      rw [hWdef, map_sum, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun m₁ _ =>
        Finset.sum_congr rfl fun m₂ _ => truncated_pair_term_eq i n α d m₁ m₂
    calc ∑ d ∈ B,
        ‖∑ m ∈ X,
          if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ ^ 2
        = ∑ d ∈ B, (∑ m₁ ∈ X, ∑ m₂ ∈ X,
            if d * m₁ ≤ n ∧ d * m₂ ≤ n then
              (i m₁ * (starRingEnd ℂ) (i m₂)) *
                Vinogradov.addChar (α * m₁ - α * m₂) d
            else 0).re := Finset.sum_congr rfl fun d _ => hWd d
      _ = (∑ d ∈ B, ∑ m₁ ∈ X, ∑ m₂ ∈ X,
            if d * m₁ ≤ n ∧ d * m₂ ≤ n then
              (i m₁ * (starRingEnd ℂ) (i m₂)) *
                Vinogradov.addChar (α * m₁ - α * m₂) d
            else 0).re := by rw [Complex.re_sum]
      _ = (∑ m₁ ∈ X, ∑ m₂ ∈ X, ∑ d ∈ B,
            if d * m₁ ≤ n ∧ d * m₂ ≤ n then
              (i m₁ * (starRingEnd ℂ) (i m₂)) *
                Vinogradov.addChar (α * m₁ - α * m₂) d
            else 0).re := by
          rw [Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
      _ = (∑ m₁ ∈ X, ∑ m₂ ∈ X, (i m₁ * (starRingEnd ℂ) (i m₂)) *
            ∑ d ∈ B.filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
              Vinogradov.addChar (α * m₁ - α * m₂) d).re := by
          congr 1
          refine Finset.sum_congr rfl fun m₁ _ =>
            Finset.sum_congr rfl fun m₂ _ => ?_
          rw [Finset.mul_sum, Finset.sum_filter]
  rw [h1]
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun m₁ _ => ?_
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun m₂ _ => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj]

/-! ## Layer 9: Schur pair-sum machinery -/

/-- Nonnegativity of the large-sieve summand. -/
theorem lsds_summand_nonneg (D : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ min ((D : ℝ) + 1) (1 / (2 * x)) := by
  refine le_min ?_ ?_
  · have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    linarith
  · positivity

/-- **Off-diagonal row bound.**  For any subset `s ⊆ (0, K]` avoiding the
base point `m₀ ≤ K`, the row of difference kernels is at most twice the
one-sided large-sieve sum. -/
theorem noncong_row_sum_le (K D m₀ : ℕ) (α : ℝ) (hm₀K : m₀ ≤ K)
    (s : Finset ℕ) (hs : s ⊆ Finset.Ioc 0 K) (hm₀s : m₀ ∉ s) :
    ∑ m ∈ s,
        min ((D : ℝ) + 1)
          (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
            (α * (m₀ : ℝ) - α * (m : ℝ)))) ≤
      2 * ∑ k ∈ Finset.Ico 1 (K + 1),
        min ((D : ℝ) + 1)
          (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) := by
  classical
  set g : ℕ → ℝ := fun k =>
    min ((D : ℝ) + 1)
      (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    lsds_summand_nonneg D _ (AnalyticNT.Bilinear.TypeII.nearestIntDist_nonneg _)
  have hLS0 : 0 ≤ ∑ k ∈ Finset.Ico 1 (K + 1), g k :=
    Finset.sum_nonneg fun k _ => hg0 k
  -- split by position relative to `m₀`
  rw [← Finset.sum_filter_add_sum_filter_not s (fun m => m < m₀)]
  have hbelow : ∑ m ∈ s.filter (fun m => m < m₀),
      min ((D : ℝ) + 1)
        (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
          (α * (m₀ : ℝ) - α * (m : ℝ)))) ≤
      ∑ k ∈ Finset.Ico 1 (K + 1), g k := by
    have hcongr : ∀ m ∈ s.filter (fun m => m < m₀),
        min ((D : ℝ) + 1)
          (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
            (α * (m₀ : ℝ) - α * (m : ℝ)))) = g (m₀ - m) := by
      intro m hm
      obtain ⟨_, hlt⟩ := Finset.mem_filter.mp hm
      have hcast : ((m₀ - m : ℕ) : ℝ) = (m₀ : ℝ) - (m : ℝ) :=
        Nat.cast_sub hlt.le
      have harg : α * (m₀ : ℝ) - α * (m : ℝ) = α * ((m₀ - m : ℕ) : ℝ) := by
        rw [hcast]
        ring
      rw [harg]
    rw [Finset.sum_congr rfl hcongr]
    have himg : ∑ m ∈ s.filter (fun m => m < m₀), g (m₀ - m) =
        ∑ k ∈ (s.filter (fun m => m < m₀)).image (fun m => m₀ - m), g k :=
      (Finset.sum_image (by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
        omega)).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hg0 k
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hms, hlt⟩ := Finset.mem_filter.mp hm
    have hm' := hs hms
    simp only [Finset.mem_Ioc] at hm'
    simp only [Finset.mem_Ico]
    omega
  have habove : ∑ m ∈ s.filter (fun m => ¬ m < m₀),
      min ((D : ℝ) + 1)
        (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
          (α * (m₀ : ℝ) - α * (m : ℝ)))) ≤
      ∑ k ∈ Finset.Ico 1 (K + 1), g k := by
    have hcongr : ∀ m ∈ s.filter (fun m => ¬ m < m₀),
        min ((D : ℝ) + 1)
          (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
            (α * (m₀ : ℝ) - α * (m : ℝ)))) = g (m - m₀) := by
      intro m hm
      obtain ⟨hms, hge⟩ := Finset.mem_filter.mp hm
      have hne : m ≠ m₀ := fun h => hm₀s (h ▸ hms)
      have hgt : m₀ < m := by omega
      have hcast : ((m - m₀ : ℕ) : ℝ) = (m : ℝ) - (m₀ : ℝ) :=
        Nat.cast_sub hgt.le
      rw [hg]
      have harg : α * (m₀ : ℝ) - α * (m : ℝ) = -(α * ((m - m₀ : ℕ) : ℝ)) := by
        rw [hcast]
        ring
      rw [harg, typeII_nearestIntDist_neg]
    rw [Finset.sum_congr rfl hcongr]
    have himg : ∑ m ∈ s.filter (fun m => ¬ m < m₀), g (m - m₀) =
        ∑ k ∈ (s.filter (fun m => ¬ m < m₀)).image (fun m => m - m₀), g k :=
      (Finset.sum_image (by
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
        (try dsimp only at hxy)
        omega)).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hg0 k
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hms, hge⟩ := Finset.mem_filter.mp hm
    have hne : m ≠ m₀ := fun h => hm₀s (h ▸ hms)
    have hm' := hs hms
    simp only [Finset.mem_Ioc] at hm'
    simp only [Finset.mem_Ico]
    omega
  linarith

/-- **Congruent-pair Cauchy–Schwarz.**  Pairs in `(0,K]²` with congruent
coordinates mod `q` contribute at most `(K/q + 1)·Σ f²` to the product
sum (per-residue-class Cauchy–Schwarz against the class size). -/
theorem cong_pair_sum_le (q K : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ)
    (_hf : ∀ m, 0 ≤ f m) :
    ∑ p ∈ ((Finset.Ioc 0 K) ×ˢ (Finset.Ioc 0 K)).filter
        (fun p => p.1 % q = p.2 % q), f p.1 * f p.2 ≤
      ((K : ℝ) / q + 1) * ∑ m ∈ Finset.Ioc 0 K, f m ^ 2 := by
  classical
  set X := Finset.Ioc 0 K with hX
  set S := (X ×ˢ X).filter (fun p => p.1 % q = p.2 % q) with hS
  have hmaps : ∀ p ∈ S, p.1 % q ∈ Finset.range q := fun p _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => f p.1 * f p.2)]
  have hfiber : ∀ r, S.filter (fun p => p.1 % q = r) =
      (X.filter (fun m => m % q = r)) ×ˢ (X.filter (fun m => m % q = r)) := by
    intro r
    ext p
    simp only [hS, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hcong⟩, hr⟩
      exact ⟨⟨h1, hr⟩, h2, by rw [← hcong]; exact hr⟩
    · rintro ⟨⟨h1, hr1⟩, h2, hr2⟩
      exact ⟨⟨⟨h1, h2⟩, by rw [hr1, hr2]⟩, hr1⟩
  have hclass_bound : ∀ r ∈ Finset.range q,
      ∑ p ∈ S.filter (fun p => p.1 % q = r), f p.1 * f p.2 ≤
        ((K : ℝ) / q + 1) * ∑ m ∈ X.filter (fun m => m % q = r), f m ^ 2 := by
    intro r _
    rw [hfiber r]
    rw [Finset.sum_product]
    have hsum_eq : ∑ m₁ ∈ X.filter (fun m => m % q = r),
        ∑ m₂ ∈ X.filter (fun m => m % q = r), f m₁ * f m₂ =
        (∑ m ∈ X.filter (fun m => m % q = r), f m) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    rw [hsum_eq]
    have hCS := sq_sum_le_card_mul_sum_sq
      (s := X.filter (fun m => m % q = r)) (f := f)
    refine hCS.trans ?_
    have hcard : ((X.filter (fun m => m % q = r)).card : ℝ) ≤ (K : ℝ) / q + 1 := by
      have h1 : (X.filter (fun m => m % q = r)).card ≤ K / q + 1 :=
        card_residue_class_Ioc_le K q r
      have h2 : ((K / q + 1 : ℕ) : ℝ) ≤ (K : ℝ) / q + 1 := by
        push_cast
        have := Nat.cast_div_le (m := K) (n := q) (α := ℝ)
        linarith
      calc ((X.filter (fun m => m % q = r)).card : ℝ)
          ≤ ((K / q + 1 : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ (K : ℝ) / q + 1 := h2
    exact mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg fun m _ => sq_nonneg _)
  refine (Finset.sum_le_sum hclass_bound).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · have hmaps' : ∀ m ∈ X, m % q ∈ Finset.range q := fun m _ =>
      Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
    rw [Finset.sum_fiberwise_of_maps_to hmaps' (fun m => f m ^ 2)]
  · have h0 : (0 : ℝ) ≤ (K : ℝ) / q := by positivity
    linarith

/-- **Non-congruent pair sum** via AM–GM symmetrization and the row
bound: at most `2·LS·Σf²`. -/
private lemma noncong_pair_kernel_sum_le (q K D : ℕ) (α : ℝ) (f : ℕ → ℝ)
    (_hf : ∀ m, 0 ≤ f m) :
    ∑ p ∈ ((Finset.Ioc 0 K) ×ˢ (Finset.Ioc 0 K)).filter
        (fun p => ¬ p.1 % q = p.2 % q),
      f p.1 * f p.2 *
        min ((D : ℝ) + 1)
          (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
            (α * (p.1 : ℝ) - α * (p.2 : ℝ)))) ≤
      2 * (∑ k ∈ Finset.Ico 1 (K + 1),
          min ((D : ℝ) + 1)
            (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k)))) *
        ∑ m ∈ Finset.Ioc 0 K, f m ^ 2 := by
  classical
  set X := Finset.Ioc 0 K with hX
  set κ : ℕ × ℕ → ℝ := fun p =>
    min ((D : ℝ) + 1)
      (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
        (α * (p.1 : ℝ) - α * (p.2 : ℝ)))) with hκdef
  set LS : ℝ := ∑ k ∈ Finset.Ico 1 (K + 1),
    min ((D : ℝ) + 1)
      (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) with hLSdef
  set S := (X ×ˢ X).filter (fun p => ¬ p.1 % q = p.2 % q) with hSdef
  have hκ0 : ∀ p : ℕ × ℕ, 0 ≤ κ p := fun p =>
    lsds_summand_nonneg D _ (AnalyticNT.Bilinear.TypeII.nearestIntDist_nonneg _)
  have hLS0 : 0 ≤ LS := Finset.sum_nonneg fun k _ =>
    lsds_summand_nonneg D _ (AnalyticNT.Bilinear.TypeII.nearestIntDist_nonneg _)
  have hSumf0 : 0 ≤ ∑ m ∈ X, f m ^ 2 := Finset.sum_nonneg fun m _ => sq_nonneg _
  have hAM : ∀ p ∈ S, f p.1 * f p.2 * κ p ≤
      (f p.1 ^ 2 * κ p + f p.2 ^ 2 * κ p) / 2 := by
    intro p _
    have h1 : f p.1 * f p.2 ≤ (f p.1 ^ 2 + f p.2 ^ 2) / 2 := by
      nlinarith [sq_nonneg (f p.1 - f p.2)]
    calc f p.1 * f p.2 * κ p
        ≤ (f p.1 ^ 2 + f p.2 ^ 2) / 2 * κ p :=
          mul_le_mul_of_nonneg_right h1 (hκ0 p)
      _ = (f p.1 ^ 2 * κ p + f p.2 ^ 2 * κ p) / 2 := by ring
  refine (Finset.sum_le_sum hAM).trans ?_
  have hsplit : ∑ p ∈ S, (f p.1 ^ 2 * κ p + f p.2 ^ 2 * κ p) / 2 =
      (∑ p ∈ S, f p.1 ^ 2 * κ p) / 2 + (∑ p ∈ S, f p.2 ^ 2 * κ p) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, add_div]
  rw [hsplit]
  have hfirst : ∑ p ∈ S, f p.1 ^ 2 * κ p ≤ 2 * LS * ∑ m ∈ X, f m ^ 2 := by
    have h1 : ∑ p ∈ S, f p.1 ^ 2 * κ p =
        ∑ m₁ ∈ X, ∑ m₂ ∈ X.filter (fun m₂ => ¬ m₁ % q = m₂ % q),
          f m₁ ^ 2 * κ (m₁, m₂) := by
      rw [hSdef, Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_congr rfl fun m₁ _ => (Finset.sum_filter _ _).symm
    rw [h1]
    have h2 : ∀ m₁ ∈ X, ∑ m₂ ∈ X.filter (fun m₂ => ¬ m₁ % q = m₂ % q),
        f m₁ ^ 2 * κ (m₁, m₂) ≤ f m₁ ^ 2 * (2 * LS) := by
      intro m₁ hm₁
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hm₁K : m₁ ≤ K := (Finset.mem_Ioc.mp (hX ▸ hm₁)).2
      exact noncong_row_sum_le K D m₁ α hm₁K
        (X.filter (fun m₂ => ¬ m₁ % q = m₂ % q))
        ((Finset.filter_subset _ _).trans (by rw [hX]))
        (by simp)
    calc ∑ m₁ ∈ X, ∑ m₂ ∈ X.filter (fun m₂ => ¬ m₁ % q = m₂ % q),
          f m₁ ^ 2 * κ (m₁, m₂)
        ≤ ∑ m₁ ∈ X, f m₁ ^ 2 * (2 * LS) := Finset.sum_le_sum h2
      _ = 2 * LS * ∑ m ∈ X, f m ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  have hsecond : ∑ p ∈ S, f p.2 ^ 2 * κ p ≤ 2 * LS * ∑ m ∈ X, f m ^ 2 := by
    have h1 : ∑ p ∈ S, f p.2 ^ 2 * κ p =
        ∑ m₂ ∈ X, ∑ m₁ ∈ X.filter (fun m₁ => ¬ m₁ % q = m₂ % q),
          f m₂ ^ 2 * κ (m₁, m₂) := by
      rw [hSdef, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
      exact Finset.sum_congr rfl fun m₂ _ => (Finset.sum_filter _ _).symm
    rw [h1]
    have h2 : ∀ m₂ ∈ X, ∑ m₁ ∈ X.filter (fun m₁ => ¬ m₁ % q = m₂ % q),
        f m₂ ^ 2 * κ (m₁, m₂) ≤ f m₂ ^ 2 * (2 * LS) := by
      intro m₂ hm₂
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hrw : ∀ m₁ ∈ X.filter (fun m₁ => ¬ m₁ % q = m₂ % q),
          κ (m₁, m₂) = min ((D : ℝ) + 1)
            (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
              (α * (m₂ : ℝ) - α * (m₁ : ℝ)))) := by
        intro m₁ _
        rw [hκdef]
        dsimp only
        have harg : α * (m₁ : ℝ) - α * (m₂ : ℝ) =
            -(α * (m₂ : ℝ) - α * (m₁ : ℝ)) := by ring
        rw [harg, typeII_nearestIntDist_neg]
      rw [Finset.sum_congr rfl hrw]
      have hm₂K : m₂ ≤ K := (Finset.mem_Ioc.mp (hX ▸ hm₂)).2
      exact noncong_row_sum_le K D m₂ α hm₂K
        (X.filter (fun m₁ => ¬ m₁ % q = m₂ % q))
        ((Finset.filter_subset _ _).trans (by rw [hX]))
        (by simp)
    calc ∑ m₂ ∈ X, ∑ m₁ ∈ X.filter (fun m₁ => ¬ m₁ % q = m₂ % q),
          f m₂ ^ 2 * κ (m₁, m₂)
        ≤ ∑ m₂ ∈ X, f m₂ ^ 2 * (2 * LS) := Finset.sum_le_sum h2
      _ = 2 * LS * ∑ m ∈ X, f m ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  linarith

/-- **Schur pair-sum bound.**  The full hyperbola-truncated pair sum is
controlled by the diagonal/congruent Cauchy–Schwarz term plus twice the
large-sieve sum, times the inner `ℓ²` mass. -/
theorem pair_sum_le_schur
    (n a q D D₂ K Q : ℕ) (α : ℝ) (i : ℕ → ℂ)
    (hq2 : 2 ≤ q) (_hn : 1 ≤ n) (hQ1 : 1 ≤ Q) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (hD₂ : D₂ ≤ 2 * D) (hKQ : K ≤ Q) :
    ∑ m₁ ∈ Finset.Ioc 0 K, ∑ m₂ ∈ Finset.Ioc 0 K, ‖i m₁‖ * ‖i m₂‖ *
        ‖∑ d ∈ (Finset.Ioc D D₂).filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
            Vinogradov.addChar (α * m₁ - α * m₂) d‖ ≤
      (((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
          2 * ∑ k ∈ Finset.Ico 1 (K + 1),
            min ((D : ℝ) + 1)
              (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k)))) *
        ∑ m ∈ Finset.Ioc 0 K, ‖i m‖ ^ 2 := by
  classical
  set X := Finset.Ioc 0 K with hX
  set f : ℕ → ℝ := fun m => ‖i m‖ with hfdef
  set LS : ℝ := ∑ k ∈ Finset.Ico 1 (K + 1),
    min ((D : ℝ) + 1)
      (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) with hLSdef
  have hSumf0 : 0 ≤ ∑ m ∈ X, f m ^ 2 := Finset.sum_nonneg fun m _ => sq_nonneg _
  have hLS0 : 0 ≤ LS := Finset.sum_nonneg fun k _ =>
    lsds_summand_nonneg D _ (AnalyticNT.Bilinear.TypeII.nearestIntDist_nonneg _)
  -- trivial cardinality bound on the truncated geometric kernel
  have hJcard : ∀ m₁ m₂ : ℕ,
      ‖∑ d ∈ (Finset.Ioc D D₂).filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
          Vinogradov.addChar (α * m₁ - α * m₂) d‖ ≤ (D : ℝ) + 1 := by
    intro m₁ m₂
    refine (norm_sum_le _ _).trans ?_
    have hsum1 : ∑ d ∈ (Finset.Ioc D D₂).filter
          (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
        ‖Vinogradov.addChar (α * m₁ - α * m₂) d‖ =
        (((Finset.Ioc D D₂).filter
          (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n)).card : ℝ) := by
      rw [Finset.sum_congr rfl fun d _ => Vinogradov.norm_addChar _ _,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum1]
    have hcard : ((Finset.Ioc D D₂).filter
        (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n)).card ≤ D + 1 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Nat.card_Ioc]
      omega
    calc (((Finset.Ioc D D₂).filter
          (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n)).card : ℝ)
        ≤ ((D + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (D : ℝ) + 1 := by push_cast; ring
  -- kernel bound for non-congruent pairs
  have hJker : ∀ m₁ ∈ X, ∀ m₂ ∈ X, ¬ m₁ % q = m₂ % q →
      ‖∑ d ∈ (Finset.Ioc D D₂).filter (fun d => d * m₁ ≤ n ∧ d * m₂ ≤ n),
          Vinogradov.addChar (α * m₁ - α * m₂) d‖ ≤
        1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
          (α * (m₁ : ℝ) - α * (m₂ : ℝ))) := by
    intro m₁ hm₁ m₂ hm₂ hne
    rw [hX] at hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    have hΔdvd : ¬ ((q : ℤ) ∣ ((m₁ : ℤ) - (m₂ : ℤ))) := by
      intro hdvd
      apply hne
      have hmodeq : m₂ ≡ m₁ [MOD q] := (Nat.modEq_iff_dvd).mpr hdvd
      exact hmodeq.symm
    have hΔn : |(m₁ : ℤ) - (m₂ : ℤ)| ≤ (Q : ℤ) := by
      rw [abs_le]
      constructor <;> [nlinarith [hm₁.1, hm₂.2, hKQ]; nlinarith [hm₁.2, hm₂.1, hKQ]]
    have hres := typeII_nearestIntDist_ne_zero_of_not_dvd Q a q α
      (by omega) hQ1 hcop hdist _ hΔn hΔdvd
    have harg : α * (m₁ : ℝ) - α * (m₂ : ℝ) =
        α * (((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) := by
      push_cast
      ring
    have hround : (round (α * (m₁ : ℝ) - α * (m₂ : ℝ)) : ℝ) ≠
        (α * (m₁ : ℝ) - α * (m₂ : ℝ)) := by
      rw [harg]
      intro hc
      exact hres ((typeII_nearestIntDist_eq_zero_iff _).mpr hc)
    rw [pair_d_filter_eq_Ioc n D D₂ m₁ m₂ hm₁.1 hm₂.1]
    refine (norm_addChar_sum_Ioc_le_round_block _ hround _ _).trans ?_
    rw [typeII_nearestIntDist_eq_abs_sub_round]
  -- split into congruent and non-congruent pairs
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter_add_sum_filter_not (X ×ˢ X)
    (fun p => p.1 % q = p.2 % q)]
  have hcong : ∑ p ∈ (X ×ˢ X).filter (fun p => p.1 % q = p.2 % q),
      f p.1 * f p.2 *
        ‖∑ d ∈ (Finset.Ioc D D₂).filter
            (fun d => d * p.1 ≤ n ∧ d * p.2 ≤ n),
          Vinogradov.addChar (α * p.1 - α * p.2) d‖ ≤
      ((D : ℝ) + 1) * (((K : ℝ) / q + 1) * ∑ m ∈ X, f m ^ 2) := by
    have h1 : ∀ p ∈ (X ×ˢ X).filter (fun p => p.1 % q = p.2 % q),
        f p.1 * f p.2 *
          ‖∑ d ∈ (Finset.Ioc D D₂).filter
              (fun d => d * p.1 ≤ n ∧ d * p.2 ≤ n),
            Vinogradov.addChar (α * p.1 - α * p.2) d‖ ≤
          f p.1 * f p.2 * ((D : ℝ) + 1) := by
      intro p _
      exact mul_le_mul_of_nonneg_left (hJcard p.1 p.2)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_mul, mul_comm _ ((D : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left
      (cong_pair_sum_le q K (by omega) f (fun m => norm_nonneg _))
      (by positivity)
  have hnoncong : ∑ p ∈ (X ×ˢ X).filter (fun p => ¬ p.1 % q = p.2 % q),
      f p.1 * f p.2 *
        ‖∑ d ∈ (Finset.Ioc D D₂).filter
            (fun d => d * p.1 ≤ n ∧ d * p.2 ≤ n),
          Vinogradov.addChar (α * p.1 - α * p.2) d‖ ≤
      2 * LS * ∑ m ∈ X, f m ^ 2 := by
    have h1 : ∀ p ∈ (X ×ˢ X).filter (fun p => ¬ p.1 % q = p.2 % q),
        f p.1 * f p.2 *
          ‖∑ d ∈ (Finset.Ioc D D₂).filter
              (fun d => d * p.1 ≤ n ∧ d * p.2 ≤ n),
            Vinogradov.addChar (α * p.1 - α * p.2) d‖ ≤
          f p.1 * f p.2 *
            min ((D : ℝ) + 1)
              (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist
                (α * (p.1 : ℝ) - α * (p.2 : ℝ)))) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      refine le_min (hJcard p.1 p.2) ?_
      exact hJker p.1 (hX ▸ hp.1.1) p.2 (hX ▸ hp.1.2) hp.2
    refine (Finset.sum_le_sum h1).trans ?_
    exact noncong_pair_kernel_sum_le q K D α f (fun m => norm_nonneg _)
  calc ∑ p ∈ (X ×ˢ X).filter (fun p => p.1 % q = p.2 % q),
        f p.1 * f p.2 *
          ‖∑ d ∈ (Finset.Ioc D D₂).filter
              (fun d => d * p.1 ≤ n ∧ d * p.2 ≤ n),
            Vinogradov.addChar (α * p.1 - α * p.2) d‖ +
      ∑ p ∈ (X ×ˢ X).filter (fun p => ¬ p.1 % q = p.2 % q),
        f p.1 * f p.2 *
          ‖∑ d ∈ (Finset.Ioc D D₂).filter
              (fun d => d * p.1 ≤ n ∧ d * p.2 ≤ n),
            Vinogradov.addChar (α * p.1 - α * p.2) d‖
      ≤ ((D : ℝ) + 1) * (((K : ℝ) / q + 1) * ∑ m ∈ X, f m ^ 2) +
          2 * LS * ∑ m ∈ X, f m ^ 2 := add_le_add hcong hnoncong
    _ = (((D : ℝ) + 1) * ((K : ℝ) / q + 1) + 2 * LS) * ∑ m ∈ X, f m ^ 2 := by
        ring

/-! ## Layer 10: the truncated per-block Type-II bound -/

/-- **Truncated per-block Type-II bound** (the Phase-2 core).  For a
dyadic outer block `(D, D₂] ⊆ (D, 2D]` with hyperbola-truncated inner
sums (`m ≤ n/d` per `d`), the block of the Vaughan Type-II bilinear sum
obeys the `q`-uniform large-sieve envelope at the common inner range
`K = n/D`: Cauchy–Schwarz on `d`, the Schur pair expansion, the
congruent-pair Cauchy–Schwarz, and `large_sieve_diagonal_split`. -/
theorem vaughanTypeII_truncated_block_bound
    (n a q U V D D₂ Q : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (hqQ : q ≤ Q) (hQn : Q ≤ n) (_haq : a < q)
    (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (hD : 1 ≤ D) (hD₂ : D₂ ≤ 2 * D) (h2D : 2 * D ≤ n)
    (h2K : 2 * (n / D) ≤ Q) :
    ‖∑ d ∈ Finset.Ioc D D₂,
        Vinogradov.vaughanTypeIIBilinearCoeff V d *
          ∑ m ∈ Finset.range (n / d + 1),
            Vinogradov.vaughanTypeIIBilinearInnerCoeff U m *
              Vinogradov.addChar α (d * m)‖ ≤
      Real.sqrt ((D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2) *
        (Real.sqrt (((n / D : ℕ) : ℝ) *
            (1 + Real.log ((n / D : ℕ) : ℝ)) ^ 3) *
          Real.sqrt (11 * (1 + Real.log ((q : ℝ) + 1)) *
            ((D : ℝ) * ((n / D : ℕ) : ℝ) / (q : ℝ) + (D : ℝ) +
              ((n / D : ℕ) : ℝ) + (q : ℝ)))) := by
  classical
  set K := n / D with hKdef
  set i : ℕ → ℂ := Vinogradov.vaughanTypeIIBilinearInnerCoeff U with hidef
  set c : ℕ → ℂ := Vinogradov.vaughanTypeIIBilinearCoeff V with hcdef
  have hKn : K ≤ n := Nat.div_le_self n D
  have hK1 : 1 ≤ K := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hq1 : 1 ≤ q := by omega
  have hn1 : 1 ≤ n := by omega
  -- Step 1: common inner range
  have hrw : ∀ d ∈ Finset.Ioc D D₂,
      c d * ∑ m ∈ Finset.range (n / d + 1),
          i m * Vinogradov.addChar α (d * m) =
      c d * ∑ m ∈ Finset.Ioc 0 K,
        if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0 := by
    intro d hd
    obtain ⟨hdD, _⟩ := Finset.mem_Ioc.mp hd
    congr 1
    exact inner_sum_eq_truncated U n d K α (by omega)
      (Nat.div_le_div_left (by omega) (by omega))
  rw [Finset.sum_congr rfl hrw]
  -- Step 2: Cauchy–Schwarz on the outer block
  have hCS : ‖∑ d ∈ Finset.Ioc D D₂, c d *
      ∑ m ∈ Finset.Ioc 0 K,
        if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ ≤
      Real.sqrt (∑ d ∈ Finset.Ioc D D₂, ‖c d‖ ^ 2) *
        Real.sqrt (∑ d ∈ Finset.Ioc D D₂,
          ‖∑ m ∈ Finset.Ioc 0 K,
            if d * m ≤ n then i m * Vinogradov.addChar α (d * m)
            else 0‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∑ d ∈ Finset.Ioc D D₂, ‖c d *
        ∑ m ∈ Finset.Ioc 0 K,
          if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ =
        ∑ d ∈ Finset.Ioc D D₂, ‖c d‖ *
          ‖∑ m ∈ Finset.Ioc 0 K,
            if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ :=
      Finset.sum_congr rfl fun d _ => norm_mul _ _
    rw [h1]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ioc D D₂)
      (fun d => ‖c d‖)
      (fun d => ‖∑ m ∈ Finset.Ioc 0 K,
        if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖)
    have h3 : 0 ≤ ∑ d ∈ Finset.Ioc D D₂, ‖c d‖ *
        ‖∑ m ∈ Finset.Ioc 0 K,
          if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ :=
      Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h4 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq h3,
      Real.sqrt_mul (Finset.sum_nonneg fun d _ => sq_nonneg _)] at h4
    exact h4
  refine hCS.trans ?_
  -- Step 3: outer ℓ² mass on the (possibly truncated) block
  have houter : ∑ d ∈ Finset.Ioc D D₂, ‖c d‖ ^ 2 ≤
      (D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2 := by
    refine le_trans ?_ (dyadicL2Sq_vaughanTypeII_outer_le V D)
    unfold AnalyticNT.Bilinear.TypeII.dyadicL2Sq
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => sq_nonneg _
    exact Finset.Ioc_subset_Ioc le_rfl hD₂
  -- Step 4: inner ℓ² mass via pair expansion + Schur + large sieve
  have hinner : ∑ d ∈ Finset.Ioc D D₂,
      ‖∑ m ∈ Finset.Ioc 0 K,
        if d * m ≤ n then i m * Vinogradov.addChar α (d * m) else 0‖ ^ 2 ≤
      ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) *
        (11 * (1 + Real.log ((q : ℝ) + 1)) *
          ((D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ))) := by
    refine le_trans
      (block_l2_mass_le_pair_sum i (Finset.Ioc D D₂) (Finset.Ioc 0 K) n α) ?_
    refine le_trans
      (pair_sum_le_schur n a q D D₂ K Q α i hq2 hn1 (by omega) hcop hdist hD₂
        (by omega)) ?_
    set ℓ : ℝ := 1 + Real.log ((q : ℝ) + 1) with hldef
    have hl1 : 1 ≤ ℓ := by
      rw [hldef]
      have h0 : 0 ≤ Real.log ((q : ℝ) + 1) := by
        refine Real.log_nonneg ?_
        have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        linarith
      linarith
    have hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ :=
      ⟨α - (a : ℝ) / q, le_of_lt hdist, by ring⟩
    have hQ_le : (Q : ℝ) ≤ (q : ℝ) * D * K + 1 := by
      have e := Nat.div_add_mod n D
      rw [← hKdef] at e
      have hmod : n % D < D := Nat.mod_lt n (by omega)
      have hqDK : n ≤ q * (D * K) + 1 := by
        have h2P : 2 * (D * K) ≤ q * (D * K) := Nat.mul_le_mul_right _ hq2
        omega
      have hQle' : Q ≤ q * (D * K) + 1 := le_trans hQn hqDK
      calc (Q : ℝ) ≤ ((q * (D * K) + 1 : ℕ) : ℝ) := by exact_mod_cast hQle'
        _ = (q : ℝ) * D * K + 1 := by push_cast; ring
    have hlsds := AnalyticNT.Bilinear.TypeII.large_sieve_diagonal_split
      a q α D K Q hq1 hqQ hQ_le h2K hα hcop
    rw [← hldef] at hlsds
    have hLS0 : 0 ≤ ∑ k ∈ Finset.Ico 1 (K + 1),
        min ((D : ℝ) + 1)
          (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) :=
      Finset.sum_nonneg fun k _ => lsds_summand_nonneg D _
        (AnalyticNT.Bilinear.TypeII.nearestIntDist_nonneg _)
    have hl2i : ∑ m ∈ Finset.Ioc 0 K, ‖i m‖ ^ 2 ≤
        (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 := by
      calc ∑ m ∈ Finset.Ioc 0 K, ‖i m‖ ^ 2
          ≤ ∑ m ∈ Finset.Ioc 0 K, ((m.divisors.card : ℕ) : ℝ) ^ 2 := by
            refine Finset.sum_le_sum fun m _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _)
              (norm_vaughanTypeIIBilinearInnerCoeff_le_card_divisors U m) 2
        _ ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 :=
            sum_Ioc_card_divisors_sq_le K
    have hl2i0 : 0 ≤ ∑ m ∈ Finset.Ioc 0 K, ‖i m‖ ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hDKq0 : 0 ≤ (D : ℝ) * K / q := by positivity
    have hKq : (K : ℝ) / q ≤ K := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hΦ : ((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
        2 * (((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
          4 * ((K : ℝ) + q) * ℓ) ≤
        11 * ℓ * ((D : ℝ) * K / q + D + K + q) := by
      have t1 : 3 * ((D : ℝ) * K / q) ≤ 11 * ℓ * ((D : ℝ) * K / q) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hl1) hDKq0]
      have t2 : 3 * (D : ℝ) ≤ 11 * ℓ * D := by nlinarith
      have t3 : 3 * ((K : ℝ) / q) + 8 * K * ℓ ≤ 11 * ℓ * K := by
        nlinarith [hKq, mul_nonneg (sub_nonneg.mpr hl1)
          (le_of_lt (lt_of_lt_of_le zero_lt_one hK1R))]
      have t4 : 3 + 8 * (q : ℝ) * ℓ ≤ 11 * ℓ * q := by nlinarith
      have expand : ((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
          2 * (((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
            4 * ((K : ℝ) + q) * ℓ) =
          3 * ((D : ℝ) * K / q) + 3 * (D : ℝ) + (3 * ((K : ℝ) / q) +
            8 * (K : ℝ) * ℓ) + (3 + 8 * (q : ℝ) * ℓ) := by
        field_simp
        ring
      rw [expand]
      have expand2 : 11 * ℓ * ((D : ℝ) * K / q + D + K + q) =
          11 * ℓ * ((D : ℝ) * K / q) + 11 * ℓ * (D : ℝ) +
            11 * ℓ * (K : ℝ) + 11 * ℓ * (q : ℝ) := by ring
      rw [expand2]
      linarith [t1, t2, t3, t4]
    have hfactor : ((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
        2 * ∑ k ∈ Finset.Ico 1 (K + 1),
          min ((D : ℝ) + 1)
            (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) ≤
        11 * ℓ * ((D : ℝ) * K / q + D + K + q) := by
      refine le_trans ?_ hΦ
      have := mul_le_mul_of_nonneg_left hlsds (by norm_num : (0:ℝ) ≤ 2)
      linarith
    have hfactor0 : 0 ≤ ((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
        2 * ∑ k ∈ Finset.Ico 1 (K + 1),
          min ((D : ℝ) + 1)
            (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k))) := by
      have h1 : 0 ≤ ((D : ℝ) + 1) * ((K : ℝ) / q + 1) := by positivity
      linarith
    calc (((D : ℝ) + 1) * ((K : ℝ) / q + 1) +
          2 * ∑ k ∈ Finset.Ico 1 (K + 1),
            min ((D : ℝ) + 1)
              (1 / (2 * AnalyticNT.Bilinear.TypeII.nearestIntDist (α * k)))) *
          ∑ m ∈ Finset.Ioc 0 K, ‖i m‖ ^ 2
        ≤ (11 * ℓ * ((D : ℝ) * K / q + D + K + q)) *
            ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) := by
          refine mul_le_mul hfactor hl2i hl2i0 ?_
          have h11 : (0 : ℝ) ≤ 11 * ℓ := by linarith
          have hsum0 : 0 ≤ (D : ℝ) * K / q + D + K + q := by positivity
          positivity
      _ = ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) *
            (11 * ℓ * ((D : ℝ) * K / q + D + K + q)) := by ring
  -- Step 5: assemble the square roots
  have houter0 : 0 ≤ (D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2 := by positivity
  have hinner0 : 0 ≤ ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) *
      (11 * (1 + Real.log ((q : ℝ) + 1)) *
        ((D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ))) := by
    have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1R
    have hl0 : 0 ≤ 1 + Real.log ((q : ℝ) + 1) := by
      have : 0 ≤ Real.log ((q : ℝ) + 1) :=
        Real.log_nonneg (by
          have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          linarith)
      linarith
    have h1 : 0 ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 := by positivity
    have h2 : 0 ≤ (D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ) := by
      positivity
    positivity
  have hKinner0 : 0 ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 := by
    have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1R
    positivity
  calc Real.sqrt (∑ d ∈ Finset.Ioc D D₂, ‖c d‖ ^ 2) *
        Real.sqrt (∑ d ∈ Finset.Ioc D D₂,
          ‖∑ m ∈ Finset.Ioc 0 K,
            if d * m ≤ n then i m * Vinogradov.addChar α (d * m)
            else 0‖ ^ 2)
      ≤ Real.sqrt ((D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2) *
          Real.sqrt (((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) *
            (11 * (1 + Real.log ((q : ℝ) + 1)) *
              ((D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ)))) := by
        refine mul_le_mul (Real.sqrt_le_sqrt houter) (Real.sqrt_le_sqrt hinner)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2) *
          (Real.sqrt ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) *
            Real.sqrt (11 * (1 + Real.log ((q : ℝ) + 1)) *
              ((D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ)))) := by
        rw [Real.sqrt_mul hKinner0]

/-! ## Phase 2, Layer 11a: shared numeric helpers -/

/-- `2 ≤ n^{1/5}` for `n ≥ 32`. -/
theorem two_le_rpow_fifth {n : ℕ} (hn : 32 ≤ n) :
    (2 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 5) := by
  have h32 : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have e2 : (2 : ℝ) = ((2 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast (2 : ℝ) 5, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [e2]
  refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
  norm_num
  linarith

/-- `2·n^{4/5} ≤ n` for `n ≥ 32`. -/
theorem two_mul_rpow45_le {n : ℕ} (hn : 32 ≤ n) :
    2 * (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h15 := two_le_rpow_fifth hn
  have hsplit : (n : ℝ) ^ ((1 : ℝ) / 5) * (n : ℝ) ^ ((4 : ℝ) / 5) = (n : ℝ) := by
    rw [← Real.rpow_add hnR, show (1:ℝ)/5 + 4/5 = 1 by norm_num, Real.rpow_one]
  calc 2 * (n : ℝ) ^ ((4 : ℝ) / 5)
      ≤ (n : ℝ) ^ ((1 : ℝ) / 5) * (n : ℝ) ^ ((4 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right h15 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) := hsplit

/-- `2 ≤ n^{2/5}` for `n ≥ 6`. -/
theorem two_le_rpow_two_fifths {n : ℕ} (hn : 6 ≤ n) :
    (2 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) := by
  have h6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have e1 : (n : ℝ) ^ ((2 : ℝ) / 5) = ((n : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have e2 : (2 : ℝ) = ((2 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast (2 : ℝ) 5, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [e1, e2]
  refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
  norm_num
  nlinarith

/-- The vaughan cutoff is at least `2` for `n ≥ 6`. -/
theorem two_le_vaughanCutoff {n : ℕ} (hn : 6 ≤ n) : 2 ≤ vaughanCutoff n := by
  have h := two_le_rpow_two_fifths hn
  exact Nat.le_floor (by exact_mod_cast h)

/-- `U·V ≤ n^{4/5}` for the Vaughan cutoffs. -/
theorem vaughanCutoff_sq_le_rpow45 (n : ℕ) :
    (vaughanCutoff n : ℝ) * (vaughanCutoff n : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
  have h := vaughanCutoff_le_rpow n
  have h0 : (0 : ℝ) ≤ (vaughanCutoff n : ℝ) := Nat.cast_nonneg _
  calc (vaughanCutoff n : ℝ) * (vaughanCutoff n : ℝ)
      ≤ (n : ℝ) ^ ((2 : ℝ) / 5) * (n : ℝ) ^ ((2 : ℝ) / 5) :=
        mul_le_mul h h h0 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ ((4 : ℝ) / 5) := by
        rw [← Real.rpow_add' (Nat.cast_nonneg n) (by norm_num)]
        norm_num

/-- Envelope floor `2·(log n)⁴ ≤ E` (used by the small-`n` crude branches). -/
theorem envelope_ge_two_log_pow_four (n q : ℕ) (hn3 : 3 ≤ n) (hq2 : 2 ≤ q) :
    2 * (Real.log n) ^ 4 ≤ hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
  unfold hardCutoffVaughanTypeIIVinogradovEnvelope
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hL0 : 0 ≤ Real.log n := by linarith
  have hsqrt : (2 : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := by
    have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have h4 : (4 : ℝ) ≤ (q : ℝ) * n := by nlinarith
    calc (2 : ℝ) = Real.sqrt 4 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ Real.sqrt ((q : ℝ) * n) := Real.sqrt_le_sqrt h4
  have h1 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q := by positivity
  have h2 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsum : (2 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
      Real.sqrt ((q : ℝ) * n) := by linarith
  exact mul_le_mul_of_nonneg_right hsum (pow_nonneg hL0 4)

/-- `log n ≤ (log n)⁴` for `n ≥ 3`. -/
theorem log_le_log_pow_four (n : ℕ) (hn : 3 ≤ n) :
    Real.log n ≤ (Real.log n) ^ 4 := by
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn
  have h3 : (1 : ℝ) ≤ (Real.log n) ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (Real.log n) ^ 3 := pow_le_pow_left₀ zero_le_one hL1 3
  calc Real.log n = Real.log n * 1 := (mul_one _).symm
    _ ≤ Real.log n * (Real.log n) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = (Real.log n) ^ 4 := by ring

/-- Subadditivity of `√` over three summands. -/
theorem sqrt_add_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have ea := Real.sq_sqrt ha
  have eb := Real.sq_sqrt hb
  have ec := Real.sq_sqrt hc
  have na := Real.sqrt_nonneg a
  have nb := Real.sqrt_nonneg b
  have nc := Real.sqrt_nonneg c
  have h1 : a + b + c ≤ (Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2 := by
    nlinarith [mul_nonneg na nb, mul_nonneg nb nc, mul_nonneg na nc]
  calc Real.sqrt (a + b + c)
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt a + Real.sqrt b + Real.sqrt c := Real.sqrt_sq (by positivity)

/-- `log(2D+1) ≤ 3·log n` for `D ≤ n`, `n ≥ 3`. -/
theorem log_two_mul_add_one_le_three_log (n D : ℕ) (hn : 3 ≤ n) (hD : D ≤ n) :
    Real.log (2 * (D : ℝ) + 1) ≤ 3 * Real.log n := by
  have hDn : (D : ℝ) ≤ (n : ℝ) := by exact_mod_cast hD
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h9 : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h1 : 2 * (D : ℝ) + 1 ≤ (n : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left h9 (by linarith : (0:ℝ) ≤ (n : ℝ))]
  calc Real.log (2 * (D : ℝ) + 1)
      ≤ Real.log ((n : ℝ) ^ 3) := Real.log_le_log (by positivity) h1
    _ = 3 * Real.log n := by rw [Real.log_pow]; push_cast; ring

/-- `1 + log(q+1) ≤ 3·log n` for `q ≤ n`, `n ≥ 3`. -/
theorem one_add_log_succ_le_three_log (n q : ℕ) (hn : 3 ≤ n) (hq : q ≤ n) :
    1 + Real.log ((q : ℝ) + 1) ≤ 3 * Real.log n := by
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn
  have hq' : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq
  have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (q : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h2 : Real.log ((q : ℝ) + 1) ≤ 2 * Real.log n := by
    calc Real.log ((q : ℝ) + 1)
        ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
  linarith

/-! ## Phase 2, Layer 11b: per-block envelope numerics (Type-II) -/

private theorem sqrt_effective_block_scale_bound (n q : ℕ)
    (hn3 : 3 ≤ n) (hq2 : 2 ≤ q) :
    Real.sqrt (2401 * Real.log n ^ 6 *
        ((n : ℝ) ^ 2 / q + 3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n)) ≤
      98 * Real.log n ^ 3 *
        ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((q : ℝ) * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 ≤ Real.log n := by
    linarith [one_le_log_of_three_le n hn3]
  have hL3 : (0 : ℝ) ≤ Real.log n ^ 3 := pow_nonneg hL0 3
  rw [show (2401 : ℝ) * Real.log n ^ 6 =
      (49 * Real.log n ^ 3) ^ 2 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hA0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / q := by positivity
  have hB0 : (0 : ℝ) ≤ 3 * (n : ℝ) ^ ((8 : ℝ) / 5) := by positivity
  have hC0 : (0 : ℝ) ≤ (q : ℝ) * n := by positivity
  have h3 := sqrt_add_three_le hA0 hB0 hC0
  have hs1 : Real.sqrt ((n : ℝ) ^ 2 / q) =
      (n : ℝ) / Real.sqrt q := by
    rw [Real.sqrt_div (sq_nonneg (n : ℝ)) q, Real.sqrt_sq hnR.le]
  have hs2 : Real.sqrt (3 * (n : ℝ) ^ ((8 : ℝ) / 5)) ≤
      2 * (n : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have h45 : Real.sqrt ((n : ℝ) ^ ((8 : ℝ) / 5)) =
        (n : ℝ) ^ ((4 : ℝ) / 5) := by
      have e : (n : ℝ) ^ ((8 : ℝ) / 5) =
          ((n : ℝ) ^ ((4 : ℝ) / 5)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ ((4 : ℝ) / 5)) 2,
          ← Real.rpow_mul hnR.le]
        norm_num
      rw [e, Real.sqrt_sq (Real.rpow_nonneg hnR.le _)]
    rw [h45]
    have h32 : Real.sqrt 3 ≤ 2 := by
      calc
        Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hnR.le _)
  have hsqrt : Real.sqrt ((n : ℝ) ^ 2 / q +
      3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n) ≤
      (n : ℝ) / Real.sqrt q + 2 * (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((q : ℝ) * n) := by
    calc
      Real.sqrt ((n : ℝ) ^ 2 / q +
          3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n) ≤
        Real.sqrt ((n : ℝ) ^ 2 / q) +
          Real.sqrt (3 * (n : ℝ) ^ ((8 : ℝ) / 5)) +
            Real.sqrt ((q : ℝ) * n) := h3
      _ ≤ (n : ℝ) / Real.sqrt q + 2 * (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((q : ℝ) * n) := by rw [hs1]; linarith
  have henv1 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q := by positivity
  have henv2 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by positivity
  have henv3 : (0 : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := Real.sqrt_nonneg _
  calc
    49 * Real.log n ^ 3 * Real.sqrt ((n : ℝ) ^ 2 / q +
        3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n) ≤
      49 * Real.log n ^ 3 * ((n : ℝ) / Real.sqrt q +
        2 * (n : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt ((q : ℝ) * n)) := by
          exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ 98 * Real.log n ^ 3 * ((n : ℝ) / Real.sqrt q +
        (n : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt ((q : ℝ) * n)) := by
      nlinarith [mul_nonneg hL3 henv1, mul_nonneg hL3 henv2,
        mul_nonneg hL3 henv3]

/-- **Effective-block envelope numerics.**  For an effective dyadic block
(`D ≤ n^{3/5}`, `K ≤ 2n^{3/5}`, `DK ≤ n`), the per-block Schur envelope
of `vaughanTypeII_truncated_block_bound` is at most
`98·(log n)³·(n/√q + n^{4/5} + √(qn))`. -/
theorem effective_block_envelope_bound (n q D K : ℕ)
    (hn3 : 3 ≤ n) (hq2 : 2 ≤ q) (hqn : q ≤ n)
    (hD1 : 1 ≤ D) (hK1 : 1 ≤ K) (hDK : D * K ≤ n)
    (hDle : (D : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5))
    (hKle : (K : ℝ) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 5)) :
    Real.sqrt ((D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2) *
      (Real.sqrt ((K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3) *
        Real.sqrt (11 * (1 + Real.log ((q : ℝ) + 1)) *
          ((D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ)))) ≤
      98 * Real.log n ^ 3 *
        ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((q : ℝ) * n)) := by
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hL0 : 0 ≤ Real.log n := by linarith
  set L := Real.log n with hLdef
  have hL3 : (0 : ℝ) ≤ L ^ 3 := pow_nonneg hL0 3
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hDn : D ≤ n := le_trans (Nat.le_mul_of_pos_right D (by omega)) hDK
  have hKn : K ≤ n := le_trans (Nat.le_mul_of_pos_left K (by omega)) hDK
  have hKR1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hlogK0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR1
  have hlogq0 : 0 ≤ Real.log ((q : ℝ) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  set X := (D : ℝ) * Real.log (2 * (D : ℝ) + 1) ^ 2 with hXdef
  set Y := (K : ℝ) * (1 + Real.log (K : ℝ)) ^ 3 with hYdef
  set Z := 11 * (1 + Real.log ((q : ℝ) + 1)) *
    ((D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ)) with hZdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    have : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
    positivity
  have hW0 : (0 : ℝ) ≤ (D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ) := by
    positivity
  have hZ0 : 0 ≤ Z := by
    rw [hZdef]
    have h11 : (0 : ℝ) ≤ 11 * (1 + Real.log ((q : ℝ) + 1)) := by linarith
    exact mul_nonneg h11 hW0
  -- factor bounds
  have hX' : X ≤ (D : ℝ) * (9 * L ^ 2) := by
    rw [hXdef]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg D)
    have h3 := log_two_mul_add_one_le_three_log n D hn3 hDn
    have h0 : 0 ≤ Real.log (2 * (D : ℝ) + 1) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
      linarith
    calc Real.log (2 * (D : ℝ) + 1) ^ 2 ≤ (3 * L) ^ 2 := by
          exact pow_le_pow_left₀ h0 h3 2
      _ = 9 * L ^ 2 := by ring
  have hY' : Y ≤ (K : ℝ) * (8 * L ^ 3) := by
    rw [hYdef]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K)
    have hlogK : Real.log (K : ℝ) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log (by linarith) (by exact_mod_cast hKn)
    have h1K : (0 : ℝ) ≤ 1 + Real.log (K : ℝ) := by linarith
    calc (1 + Real.log (K : ℝ)) ^ 3 ≤ (2 * L) ^ 3 := by
          exact pow_le_pow_left₀ h1K (by linarith) 3
      _ = 8 * L ^ 3 := by ring
  have hsplit : (n : ℝ) ^ ((2 : ℝ) / 5) * (n : ℝ) ^ ((3 : ℝ) / 5) = (n : ℝ) := by
    rw [← Real.rpow_add hnR, show (2:ℝ)/5 + 3/5 = 1 by norm_num, Real.rpow_one]
  have hZ' : Z ≤ 33 * L * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q) := by
    rw [hZdef]
    have hZ1 : 11 * (1 + Real.log ((q : ℝ) + 1)) ≤ 33 * L := by
      have := one_add_log_succ_le_three_log n q hn3 hqn
      rw [hLdef]
      linarith
    have hZ2 : (D : ℝ) * (K : ℝ) / (q : ℝ) + (D : ℝ) + (K : ℝ) + (q : ℝ) ≤
        (n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q := by
      have hDKn : (D : ℝ) * K ≤ (n : ℝ) := by exact_mod_cast hDK
      have h1 : (D : ℝ) * (K : ℝ) / (q : ℝ) ≤ (n : ℝ) / q := by gcongr
      linarith
    exact mul_le_mul hZ1 hZ2 hW0 (by positivity)
  -- collapse the three square roots
  have hcollapse : Real.sqrt X * (Real.sqrt Y * Real.sqrt Z) =
      Real.sqrt (X * (Y * Z)) := by
    rw [← Real.sqrt_mul hY0, ← Real.sqrt_mul hX0]
  rw [hcollapse]
  -- bound the product under the root
  have h85 : (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 5) = (n : ℝ) ^ ((8 : ℝ) / 5) := by
    rw [show ((8:ℝ)/5) = 1 + (3:ℝ)/5 by norm_num, Real.rpow_add hnR, Real.rpow_one]
  set S := (n : ℝ) ^ 2 / q + 3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n with hSdef
  clear_value S
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  have hprod : X * (Y * Z) ≤ 2401 * L ^ 6 * S := by
    have hYZ0 : 0 ≤ Y * Z := mul_nonneg hY0 hZ0
    have hstep : X * (Y * Z) ≤
        ((D : ℝ) * (9 * L ^ 2)) * (((K : ℝ) * (8 * L ^ 3)) *
          (33 * L * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q))) := by
      refine mul_le_mul hX' ?_ hYZ0 (by positivity)
      refine mul_le_mul hY' hZ' hZ0 ?_
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith [mul_nonneg hK0 hL3]
    refine hstep.trans ?_
    have hDKn : (D : ℝ) * K ≤ (n : ℝ) := by exact_mod_cast hDK
    have hbound : ((D : ℝ) * K) * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q) ≤ S := by
      rw [hSdef]
      have hA0 : (0 : ℝ) ≤ (n : ℝ) / q := by positivity
      have hB0 : (0 : ℝ) ≤ 3 * (n : ℝ) ^ ((3 : ℝ) / 5) := by positivity
      have hC0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      have hDK0 : (0 : ℝ) ≤ (D : ℝ) * K := by positivity
      have hexp : (n : ℝ) * ((n : ℝ) / q) + (n : ℝ) * (3 * (n : ℝ) ^ ((3 : ℝ) / 5)) +
          (n : ℝ) * q = (n : ℝ) ^ 2 / q + 3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n := by
        rw [← h85]; ring
      calc ((D : ℝ) * K) * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q)
          = ((D : ℝ) * K) * ((n : ℝ) / q) + ((D : ℝ) * K) * (3 * (n : ℝ) ^ ((3 : ℝ) / 5)) +
            ((D : ℝ) * K) * q := by ring
        _ ≤ (n : ℝ) * ((n : ℝ) / q) + (n : ℝ) * (3 * (n : ℝ) ^ ((3 : ℝ) / 5)) +
            (n : ℝ) * q := by
            refine add_le_add (add_le_add ?_ ?_) ?_
            · exact mul_le_mul_of_nonneg_right hDKn hA0
            · exact mul_le_mul_of_nonneg_right hDKn hB0
            · exact mul_le_mul_of_nonneg_right hDKn hC0
        _ = (n : ℝ) ^ 2 / q + 3 * (n : ℝ) ^ ((8 : ℝ) / 5) + q * n := hexp
    have hrw : ((D : ℝ) * (9 * L ^ 2)) * (((K : ℝ) * (8 * L ^ 3)) *
        (33 * L * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q))) =
        2376 * (((D : ℝ) * K) * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q)) * L ^ 6 := by
      ring
    rw [hrw]
    have hL6 : (0 : ℝ) ≤ L ^ 6 := by positivity
    have h2376 : 2376 * (((D : ℝ) * K) * ((n : ℝ) / q + 3 * (n : ℝ) ^ ((3 : ℝ) / 5) + q)) *
        L ^ 6 ≤ 2376 * S * L ^ 6 := by
      refine mul_le_mul_of_nonneg_right ?_ hL6
      refine mul_le_mul_of_nonneg_left hbound (by norm_num)
    refine h2376.trans ?_
    linarith only [mul_nonneg hS0 hL6]
  refine (Real.sqrt_le_sqrt hprod).trans ?_
  simpa [hLdef, hSdef] using sqrt_effective_block_scale_bound n q hn3 hq2
/-! ## Phase 2, Layer 11c: crude small-`n` bound (Type-II) -/

/-- `τ(m) ≤ m`. -/
theorem card_divisors_le_self (m : ℕ) : m.divisors.card ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hsub : m.divisors ⊆ Finset.Icc 1 m := by
      intro d hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    have hcard := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at hcard

/-- Crude trivial bound for the Vaughan Type-II bilinear sum
(used only for `n ≤ 5`). -/
theorem norm_vaughanTypeIIBilinearSum_le_crude (U V n : ℕ) (α : ℝ) (hn : 1 ≤ n) :
    ‖Vinogradov.vaughanTypeIIBilinearSum U V n α‖ ≤
      2 * (n : ℝ) ^ 3 * Real.log n := by
  have hL0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Vinogradov.vaughanTypeIIBilinearSum_eq_fixed_outer]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ Finset.Ioc V n,
      ‖Vinogradov.vaughanTypeIIBilinearCoeff V d *
        ∑ m ∈ Finset.range (n / d + 1),
          Vinogradov.vaughanTypeIIBilinearInnerCoeff U m *
            Vinogradov.addChar α (d * m)‖ ≤ Real.log n * (2 * (n : ℝ) ^ 2) := by
    intro d hd
    obtain ⟨hVd, hdn⟩ := Finset.mem_Ioc.mp hd
    rw [norm_mul]
    have hc : ‖Vinogradov.vaughanTypeIIBilinearCoeff V d‖ ≤ Real.log n := by
      unfold Vinogradov.vaughanTypeIIBilinearCoeff Vinogradov.vaughanLambdaHigh
      simp only [ArithmeticFunction.coe_mk]
      rw [Complex.norm_real, Real.norm_eq_abs, if_pos hVd,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      refine (ArithmeticFunction.vonMangoldt_le_log (n := d)).trans ?_
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < d))
        (by exact_mod_cast hdn)
    have hin : ‖∑ m ∈ Finset.range (n / d + 1),
        Vinogradov.vaughanTypeIIBilinearInnerCoeff U m *
          Vinogradov.addChar α (d * m)‖ ≤ 2 * (n : ℝ) ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      have hms : ∀ m ∈ Finset.range (n / d + 1),
          ‖Vinogradov.vaughanTypeIIBilinearInnerCoeff U m *
            Vinogradov.addChar α (d * m)‖ ≤ (n : ℝ) := by
        intro m hm
        have hmn : m ≤ n := by
          have := Finset.mem_range.mp hm
          have := Nat.div_le_self n d
          omega
        rw [norm_mul, Vinogradov.norm_addChar, mul_one]
        refine (norm_vaughanTypeIIBilinearInnerCoeff_le_card_divisors U m).trans ?_
        exact_mod_cast (card_divisors_le_self m).trans hmn
      refine (Finset.sum_le_sum hms).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h1 : ((n / d + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
        have hdiv : n / d + 1 ≤ n + 1 := by
          have := Nat.div_le_self n d
          omega
        exact_mod_cast hdiv
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    exact mul_le_mul hc hin (norm_nonneg _) hL0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Ioc V n).card : ℝ) ≤ (n : ℝ) := by
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.sub_le n V
  have h0 : (0 : ℝ) ≤ Real.log n * (2 * (n : ℝ) ^ 2) := by positivity
  calc ((Finset.Ioc V n).card : ℝ) * (Real.log n * (2 * (n : ℝ) ^ 2))
      ≤ (n : ℝ) * (Real.log n * (2 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard h0
    _ = 2 * (n : ℝ) ^ 3 * Real.log n := by ring

/-! ## Phase 2, Layer 11d: the Type-II piece -/

/-- **Phase-2 obligation (Type-II piece) DISCHARGED.**  Dyadic outer
blocks + hyperbola truncation + per-block Schur bound + effectiveness
dichotomy (`q`-resonance handled inside the proven block bound), with
constant `K = 300`. -/
theorem vaughanTypeIIPieceQSensitiveEnvelopeBound_proved :
    vaughanTypeIIPieceQSensitiveEnvelopeBound := by
  refine ⟨300, by norm_num, ?_⟩
  intro n a q α hn3 hq2 hqn haq hcop hdist
  have hE0 : 0 ≤ hardCutoffVaughanTypeIIVinogradovEnvelope n q := envelope_nonneg n q
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hL0 : 0 ≤ Real.log n := by linarith
  by_cases hn6 : n < 6
  · -- crude branch (`n ∈ {3, 4, 5}`): trivial bound against the envelope floor
    have hcrude := norm_vaughanTypeIIBilinearSum_le_crude
      (vaughanCutoff n) (vaughanCutoff n) n α (by omega)
    have hE2 := envelope_ge_two_log_pow_four n q hn3 hq2
    have hL4 := log_le_log_pow_four n hn3
    have hn5 : (n : ℝ) ≤ 5 := by exact_mod_cast (by omega : n ≤ 5)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcube : (n : ℝ) ^ 3 ≤ 125 := by
      have h := pow_le_pow_left₀ hn0 hn5 3
      norm_num at h
      exact h
    calc ‖Vinogradov.vaughanTypeIIBilinearSum
          (vaughanCutoff n) (vaughanCutoff n) n α‖
        ≤ 2 * (n : ℝ) ^ 3 * Real.log n := hcrude
      _ ≤ 250 * Real.log n := by nlinarith
      _ ≤ 250 * (Real.log n) ^ 4 := by
          linarith [mul_le_mul_of_nonneg_left hL4 (by norm_num : (0:ℝ) ≤ 250)]
      _ = 125 * (2 * (Real.log n) ^ 4) := by ring
      _ ≤ 125 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
          linarith [mul_le_mul_of_nonneg_left hE2 (by norm_num : (0:ℝ) ≤ 125)]
      _ ≤ 300 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by linarith
  · -- main branch: `n ≥ 6`
    push Not at hn6
    set V := vaughanCutoff n with hVdef
    have hV2 : 2 ≤ V := by rw [hVdef]; exact two_le_vaughanCutoff hn6
    have hV1 : 1 ≤ V := by omega
    have hn1 : 1 ≤ n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    -- fixed-outer form + zero-extension to `Ioc 0 n`
    rw [Vinogradov.vaughanTypeIIBilinearSum_eq_fixed_outer]
    have hext : ∑ d ∈ Finset.Ioc V n,
        Vinogradov.vaughanTypeIIBilinearCoeff V d *
          ∑ m ∈ Finset.range (n / d + 1),
            Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
              Vinogradov.addChar α (d * m) =
        ∑ d ∈ Finset.Ioc 0 n,
          Vinogradov.vaughanTypeIIBilinearCoeff V d *
            ∑ m ∈ Finset.range (n / d + 1),
              Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                Vinogradov.addChar α (d * m) := by
      refine Finset.sum_subset (Finset.Ioc_subset_Ioc (Nat.zero_le V) le_rfl) ?_
      intro x hx hnx
      have hx' := Finset.mem_Ioc.mp hx
      have hxV : x ≤ V := by
        by_contra hcon
        push Not at hcon
        exact hnx (Finset.mem_Ioc.mpr ⟨hcon, hx'.2⟩)
      rw [vaughanTypeIIBilinearCoeff_eq_zero_of_le V x hxV, zero_mul]
    rw [hext]
    -- dyadic decomposition of the outer sum
    refine le_trans (norm_sum_Ioc_zero_le_dyadic
      (fun d => Vinogradov.vaughanTypeIIBilinearCoeff V d *
        ∑ m ∈ Finset.range (n / d + 1),
          Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
            Vinogradov.addChar α (d * m)) n hn1) ?_
    -- per-block bound
    have hblock : ∀ j ∈ Finset.range (Nat.log 2 n + 1),
        ‖∑ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
            Vinogradov.vaughanTypeIIBilinearCoeff V d *
              ∑ m ∈ Finset.range (n / d + 1),
                Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                  Vinogradov.addChar α (d * m)‖ ≤
          98 * Real.log n ^ 3 *
            ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n)) := by
      intro j _
      have henv0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((q : ℝ) * n) := by positivity
      have hL30 : (0 : ℝ) ≤ Real.log n ^ 3 := pow_nonneg hL0 3
      by_cases hz : ∀ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
          Vinogradov.vaughanTypeIIBilinearCoeff V d *
            ∑ m ∈ Finset.range (n / d + 1),
              Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                Vinogradov.addChar α (d * m) = 0
      · rw [Finset.sum_eq_zero hz, norm_zero]
        have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 98) hL30) henv0
        linarith
      · -- effective block: extract a witness and discharge the hypotheses
        push Not at hz
        obtain ⟨d₀, hd₀mem, hd₀ne⟩ := hz
        obtain ⟨hDd₀, hd₀le⟩ := Finset.mem_Ioc.mp hd₀mem
        have hpow : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
        have hd₀2D : d₀ ≤ 2 * 2 ^ j := by
          have := min_le_left ((2 : ℕ) ^ (j + 1)) n
          omega
        have hd₀n : d₀ ≤ n := le_trans hd₀le (min_le_right _ _)
        have hD1 : 1 ≤ (2 : ℕ) ^ j := Nat.one_le_two_pow
        have hd₀pos : 0 < d₀ := by omega
        have hcne : Vinogradov.vaughanTypeIIBilinearCoeff V d₀ ≠ 0 :=
          left_ne_zero_of_mul hd₀ne
        have hVd₀ : V < d₀ := by
          by_contra hcon
          push Not at hcon
          exact hcne (vaughanTypeIIBilinearCoeff_eq_zero_of_le V d₀ hcon)
        have hinne : (∑ m ∈ Finset.range (n / d₀ + 1),
            Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
              Vinogradov.addChar α (d₀ * m)) ≠ 0 := right_ne_zero_of_mul hd₀ne
        obtain ⟨m₀, hm₀mem, hm₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinne
        have him : Vinogradov.vaughanTypeIIBilinearInnerCoeff V m₀ ≠ 0 :=
          left_ne_zero_of_mul hm₀ne
        have hVm₀ : V < m₀ := by
          by_contra hcon
          push Not at hcon
          exact him (vaughanTypeIIBilinearInnerCoeff_eq_zero_of_le V m₀ hcon)
        have hm₀le : m₀ ≤ n / d₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₀mem)
        have hVd₀n : (V + 1) * d₀ ≤ n := by
          have h1 : V + 1 ≤ n / d₀ := by omega
          exact (Nat.le_div_iff_mul_le hd₀pos).mp h1
        -- ℕ-side block hypotheses
        have h2D : 2 * 2 ^ j ≤ n := by
          have h3 : 3 * (2 ^ j + 1) ≤ (V + 1) * d₀ :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
        have hD2 : 2 ≤ (2 : ℕ) ^ j := by omega
        have h2K : 2 * (n / 2 ^ j) ≤ n := by
          have h1 : n / 2 ^ j ≤ n / 2 := Nat.div_le_div_left hD2 (by norm_num)
          omega
        have hK1 : 1 ≤ n / 2 ^ j := (Nat.one_le_div_iff (by omega)).mpr (by omega)
        have hDK : 2 ^ j * (n / 2 ^ j) ≤ n := by
          calc 2 ^ j * (n / 2 ^ j) = n / 2 ^ j * 2 ^ j := Nat.mul_comm _ _
            _ ≤ n := Nat.div_mul_le_self n (2 ^ j)
        -- ℝ-side effective-window bounds
        have hsplit : (n : ℝ) ^ ((2 : ℝ) / 5) * (n : ℝ) ^ ((3 : ℝ) / 5) = (n : ℝ) := by
          rw [← Real.rpow_add hnR, show (2:ℝ)/5 + 3/5 = 1 by norm_num, Real.rpow_one]
        have hU1 : (n : ℝ) ^ ((2 : ℝ) / 5) < (V : ℝ) + 1 := by
          rw [hVdef]
          unfold vaughanCutoff
          exact Nat.lt_floor_add_one _
        have hDpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < (2 : ℕ) ^ j)
        have hDleN : (2 ^ j + 1) * (V + 1) ≤ n := by
          calc (2 ^ j + 1) * (V + 1) ≤ d₀ * (V + 1) :=
                Nat.mul_le_mul (by omega) (le_refl (V + 1))
            _ = (V + 1) * d₀ := Nat.mul_comm _ _
            _ ≤ n := hVd₀n
        have hDle : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by
          have hcc : (((2 ^ j + 1) * (V + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hDleN
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one] at hcc
          have hc1 : ((2 ^ j : ℕ) : ℝ) * ((V : ℝ) + 1) ≤ (n : ℝ) := by
            have hV0 : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
            nlinarith [hDpos.le]
          have hcast : ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5)) ≤ (n : ℝ) := by
            calc ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5))
                ≤ ((2 ^ j : ℕ) : ℝ) * ((V : ℝ) + 1) :=
                  mul_le_mul_of_nonneg_left hU1.le hDpos.le
              _ ≤ (n : ℝ) := hc1
          have hpos25 : (0 : ℝ) < (n : ℝ) ^ ((2 : ℝ) / 5) :=
            Real.rpow_pos_of_pos hnR _
          have h2 : ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5)) ≤
              (n : ℝ) ^ ((3 : ℝ) / 5) * ((n : ℝ) ^ ((2 : ℝ) / 5)) := by
            calc ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5)) ≤ (n : ℝ) := hcast
              _ = (n : ℝ) ^ ((3 : ℝ) / 5) * ((n : ℝ) ^ ((2 : ℝ) / 5)) := by
                  rw [mul_comm]
                  exact hsplit.symm
          exact le_of_mul_le_mul_right h2 hpos25
        have hKle : ((n / 2 ^ j : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) := by
          have h1 : ((n / 2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
            Nat.cast_div_le
          have hVd2 : (V : ℝ) + 1 ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
            have hN : V + 1 ≤ 2 * 2 ^ j := by omega
            exact_mod_cast hN
          have h2 : (n : ℝ) ^ ((2 : ℝ) / 5) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
            linarith [hU1]
          have h3 : (n : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) := by
            rw [div_le_iff₀ hDpos]
            calc (n : ℝ) = (n : ℝ) ^ ((2 : ℝ) / 5) * (n : ℝ) ^ ((3 : ℝ) / 5) :=
                  hsplit.symm
              _ ≤ (2 * ((2 ^ j : ℕ) : ℝ)) * ((n : ℝ) ^ ((3 : ℝ) / 5)) :=
                  mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hnR.le _)
              _ = 2 * (n : ℝ) ^ ((3 : ℝ) / 5) * ((2 ^ j : ℕ) : ℝ) := by ring
          linarith
        refine (vaughanTypeII_truncated_block_bound n a q V V (2 ^ j)
          (min (2 ^ (j + 1)) n) n α hq2 hqn le_rfl haq hcop hdist hD1 ?_
          h2D h2K).trans ?_
        · exact le_trans (min_le_left _ _) (le_of_eq hpow)
        · exact effective_block_envelope_bound n q (2 ^ j) (n / 2 ^ j) hn3 hq2 hqn
            hD1 hK1 hDK hDle hKle
    -- assemble: the `d = 1` term vanishes, box count ≤ 3·log n
    have hf1 : Vinogradov.vaughanTypeIIBilinearCoeff V 1 = 0 :=
      vaughanTypeIIBilinearCoeff_eq_zero_of_le V 1 hV1
    have hcount := dyadicBoxCount_le_three_log n (by omega)
    have henv0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((q : ℝ) * n) := by positivity
    have hblk0 : (0 : ℝ) ≤ 98 * Real.log n ^ 3 *
        ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((q : ℝ) * n)) := by
      have hL30 : (0 : ℝ) ≤ Real.log n ^ 3 := pow_nonneg hL0 3
      have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 98) hL30) henv0
      linarith
    calc ‖Vinogradov.vaughanTypeIIBilinearCoeff V 1 *
          ∑ m ∈ Finset.range (n / 1 + 1),
            Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
              Vinogradov.addChar α (1 * m)‖ +
          ∑ j ∈ Finset.range (Nat.log 2 n + 1),
            ‖∑ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
              Vinogradov.vaughanTypeIIBilinearCoeff V d *
                ∑ m ∈ Finset.range (n / d + 1),
                  Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                    Vinogradov.addChar α (d * m)‖
        = ∑ j ∈ Finset.range (Nat.log 2 n + 1),
            ‖∑ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
              Vinogradov.vaughanTypeIIBilinearCoeff V d *
                ∑ m ∈ Finset.range (n / d + 1),
                  Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                    Vinogradov.addChar α (d * m)‖ := by
          rw [hf1, zero_mul, norm_zero, zero_add]
      _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 n + 1),
            (98 * Real.log n ^ 3 *
              ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
                Real.sqrt ((q : ℝ) * n))) := Finset.sum_le_sum hblock
      _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) *
            (98 * Real.log n ^ 3 *
              ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
                Real.sqrt ((q : ℝ) * n))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 3 * Real.log n *
            (98 * Real.log n ^ 3 *
              ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
                Real.sqrt ((q : ℝ) * n))) :=
          mul_le_mul_of_nonneg_right hcount hblk0
      _ ≤ 300 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
          unfold hardCutoffVaughanTypeIIVinogradovEnvelope
          have hfin : (0 : ℝ) ≤ ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n)) * (Real.log n) ^ 4 :=
            mul_nonneg henv0 (pow_nonneg hL0 4)
          linarith only [hfin]

/-! ## Phase 2, Layer 12a: Type-I infrastructure -/

/-- Frequency-shift for the additive character: `e(α·(r·f)) = e((α·r)·f)`. -/
theorem addChar_freq_shift (α : ℝ) (r f : ℕ) :
    Vinogradov.addChar α (r * f) = Vinogradov.addChar (α * r) f := by
  unfold Vinogradov.addChar
  congr 1
  push_cast
  ring

/-- **Hyperbola swap.**  `Σ_{m ≤ M} Σ_{e ∣ m} F(e, m) = Σ_{e ≤ M} Σ_{f ≤ M/e} F(e, ef)`. -/
theorem sum_Ioc_divisors_swap (M : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ m ∈ Finset.Ioc 0 M, ∑ e ∈ m.divisors, F e m =
      ∑ e ∈ Finset.Ioc 0 M, ∑ f ∈ Finset.Ioc 0 (M / e), F e (e * f) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.2, p.1 / p.2⟩)
    (j := fun p => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hm0, hmM⟩, hdvd, hne⟩ := hp
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hdvd hm0
    refine ⟨⟨he0, le_trans (Nat.le_of_dvd hm0 hdvd) hmM⟩, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hm0 hdvd) he0
    · exact Nat.div_le_div_right hmM
  · rintro ⟨e, f⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨he0, heM⟩, hf0, hfM⟩ := hp
    have hefM : e * f ≤ M := by
      have hfe := (Nat.le_div_iff_mul_le he0).mp hfM
      calc e * f = f * e := Nat.mul_comm e f
        _ ≤ M := hfe
    exact ⟨⟨by positivity, hefM⟩, Dvd.intro f rfl, by positivity⟩
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp
    obtain ⟨_, hdvd, _⟩ := hp
    simp [Nat.mul_div_cancel' hdvd]
  · rintro ⟨e, f⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc] at hp
    obtain ⟨⟨he0, _⟩, _, _⟩ := hp
    simp [Nat.mul_div_cancel_left f he0]
  · rintro ⟨m, e⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisors] at hp
    obtain ⟨_, hdvd, _⟩ := hp
    simp [Nat.mul_div_cancel' hdvd]

/-- Fixed-outer-divisor form of the divisor-pair Vaughan Type-I sum
(companion of `vaughanTypeIIBilinearSum_eq_fixed_outer`, via the
hyperbola swap; the outer coefficient is NOT restricted, so the outer
range is all of `(0, N]`). -/
theorem vaughanTypeIBilinearSum_eq_fixed_outer (U V N : ℕ) (α : ℝ) :
    Vinogradov.vaughanTypeIBilinearSum U V N α =
      ∑ d ∈ Finset.Ioc 0 N,
        Vinogradov.vaughanTypeIBilinearCoeff U V d *
          ∑ f ∈ Finset.Ioc 0 (N / d),
            Vinogradov.vaughanTypeIBilinearInnerCoeff V f *
              Vinogradov.addChar α (d * f) := by
  unfold Vinogradov.vaughanTypeIBilinearSum
  rw [range_succ_eq_insert_Ioc, Finset.sum_insert (by simp)]
  rw [show (Nat.divisorsAntidiagonal 0) = ∅ from rfl, Finset.sum_empty, zero_add]
  have h1 : ∀ m ∈ Finset.Ioc 0 N,
      (∑ dm ∈ m.divisorsAntidiagonal,
        Vinogradov.vaughanTypeIBilinearCoeff U V dm.1 *
          Vinogradov.vaughanTypeIBilinearInnerCoeff V dm.2 *
          Vinogradov.addChar α (dm.1 * dm.2)) =
      ∑ e ∈ m.divisors,
        Vinogradov.vaughanTypeIBilinearCoeff U V e *
          Vinogradov.vaughanTypeIBilinearInnerCoeff V (m / e) *
          Vinogradov.addChar α (e * (m / e)) := by
    intro m _
    exact Nat.sum_divisorsAntidiagonal (fun i j =>
      Vinogradov.vaughanTypeIBilinearCoeff U V i *
        Vinogradov.vaughanTypeIBilinearInnerCoeff V j *
        Vinogradov.addChar α (i * j))
  rw [Finset.sum_congr rfl h1,
    sum_Ioc_divisors_swap N (fun e m =>
      Vinogradov.vaughanTypeIBilinearCoeff U V e *
        Vinogradov.vaughanTypeIBilinearInnerCoeff V (m / e) *
        Vinogradov.addChar α (e * (m / e)))]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨he0, _⟩ := Finset.mem_Ioc.mp he
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Nat.mul_div_cancel_left f he0]
  ring

/-- The Type-I outer coefficient vanishes above the cutoff. -/
theorem vaughanTypeIBilinearCoeff_eq_zero_of_gt (U V d : ℕ) (h : U < d) :
    Vinogradov.vaughanTypeIBilinearCoeff U V d = 0 := by
  unfold Vinogradov.vaughanTypeIBilinearCoeff Vinogradov.vaughanMuLow
  simp only [ArithmeticFunction.coe_mk]
  rw [if_neg (by omega)]
  norm_num

/-- The Type-I outer coefficient is bounded by `1`. -/
theorem norm_vaughanTypeIBilinearCoeff_le_one (U V d : ℕ) :
    ‖Vinogradov.vaughanTypeIBilinearCoeff U V d‖ ≤ 1 := by
  unfold Vinogradov.vaughanTypeIBilinearCoeff Vinogradov.vaughanMuLow
  simp only [ArithmeticFunction.coe_mk]
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast h
  · norm_num

/-- The convolution `(ζ * Λ_{≤V})(f)` is sandwiched in `[0, log f]`. -/
theorem zeta_mul_lambdaLow_mem (V f : ℕ) :
    0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        Vinogradov.vaughanLambdaLow V) f ∧
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        Vinogradov.vaughanLambdaLow V) f ≤ Real.log f := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  constructor
  · refine Finset.sum_nonneg fun e _ => ?_
    unfold Vinogradov.vaughanLambdaLow
    simp only [ArithmeticFunction.coe_mk]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_refl 0
  · calc ∑ e ∈ f.divisors, Vinogradov.vaughanLambdaLow V e
        ≤ ∑ e ∈ f.divisors, ArithmeticFunction.vonMangoldt e := by
          refine Finset.sum_le_sum fun e _ => ?_
          unfold Vinogradov.vaughanLambdaLow
          simp only [ArithmeticFunction.coe_mk]
          split_ifs
          · exact le_refl _
          · exact ArithmeticFunction.vonMangoldt_nonneg
      _ = Real.log f := ArithmeticFunction.vonMangoldt_sum

/-- The Type-I inner coefficient is bounded by `2·log n` on `[0, n]`. -/
theorem norm_vaughanTypeIBilinearInnerCoeff_le (V n f : ℕ) (hf : f ≤ n) :
    ‖Vinogradov.vaughanTypeIBilinearInnerCoeff V f‖ ≤ 2 * Real.log n := by
  have hLn0 : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogf : Real.log (f : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simpa using hLn0
    · exact Real.log_le_log (by exact_mod_cast hf0) (by exact_mod_cast hf)
  have hlogf0 : (0 : ℝ) ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  obtain ⟨hz0, hzle⟩ := zeta_mul_lambdaLow_mem V f
  unfold Vinogradov.vaughanTypeIBilinearInnerCoeff Vinogradov.vaughanTypeIInnerArithmetic
  rw [Complex.norm_real, Real.norm_eq_abs, arithmeticFunction_sub_apply,
    ArithmeticFunction.log_apply]
  rw [abs_sub_comm, abs_le]
  constructor <;> nlinarith

/-! ## Phase 2, Layer 12b: the Type-I kernel dichotomy -/

/-- Per-modulus Type-I kernel bound: resonant moduli (`q ∣ r`) take the
hyperbola cap `n/r + 1`; non-resonant moduli take the Davenport
symmetric-residue bound `q / min(ar mod q, q − ar mod q)`. -/
noncomputable def typeIKernelBound (n a q r : ℕ) : ℝ :=
  if q ∣ r then ((n / r : ℕ) : ℝ) + 1
  else (q : ℝ) / ((min (a * r % q) (q - a * r % q) : ℕ) : ℝ)

theorem typeIKernelBound_nonneg (n a q r : ℕ) : 0 ≤ typeIKernelBound n a q r := by
  unfold typeIKernelBound
  split_ifs
  · positivity
  · positivity

/-- For `q ∤ r` (with `a ⊥ q`) the symmetric residue distance is `≥ 1`. -/
theorem nonres_symdist_pos (a q r : ℕ) (hq1 : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hndvd : ¬ q ∣ r) : 1 ≤ min (a * r % q) (q - a * r % q) := by
  have hs0 : a * r % q ≠ 0 := by
    intro hc
    exact hndvd (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcop)
      (Nat.dvd_of_mod_eq_zero hc))
  have hsq : a * r % q < q := Nat.mod_lt _ (by omega)
  omega

/-- **Non-resonance separation.**  Under the witness window, for `q ∤ r`,
`1 ≤ r ≤ R`, `2R ≤ n`, every integer is at distance `≥ j_r/(2q)` from
`α·r`, where `j_r = min(ar mod q, q − ar mod q)`. -/
theorem nonres_dist_int_lb (n a q R r : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (hn1 : 1 ≤ n) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * n))
    (h2R : 2 * R ≤ n) (_hr1 : 1 ≤ r) (hrR : r ≤ R) (hndvd : ¬ q ∣ r) :
    ∀ k : ℤ, ((min (a * r % q) (q - a * r % q) : ℕ) : ℝ) / (2 * q) ≤
      |α * r - (k : ℝ)| := by
  intro k
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hrRR : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
  have hs0 : a * r % q ≠ 0 := by
    intro hc
    exact hndvd (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcop)
      (Nat.dvd_of_mod_eq_zero hc))
  have hsq : a * r % q < q := Nat.mod_lt _ (by omega)
  have hj1 : 1 ≤ min (a * r % q) (q - a * r % q) :=
    nonres_symdist_pos a q r (by omega) hcop hndvd
  set s := a * r % q with hsdef
  set j := min s (q - s) with hjdef
  -- Step 1: integer separation `|ar − kq| ≥ j`
  have habs : (j : ℤ) ≤ |((a * r : ℕ) : ℤ) - k * q| := by
    have hdm := Nat.div_add_mod (a * r) q
    set c : ℤ := ((a * r / q : ℕ) : ℤ) - k with hcdef
    have hare : ((a * r : ℕ) : ℤ) - k * q = q * c + s := by
      rw [hcdef]
      have : ((a * r : ℕ) : ℤ) = (q : ℤ) * ((a * r / q : ℕ) : ℤ) + (s : ℤ) := by
        exact_mod_cast hdm.symm
      rw [this]
      ring
    rw [hare]
    have hjs : (j : ℤ) ≤ s := by exact_mod_cast min_le_left s (q - s)
    have hjqs : (j : ℤ) ≤ (q : ℤ) - s := by
      have h1 : j ≤ q - s := min_le_right s (q - s)
      have h2 : ((q - s : ℕ) : ℤ) = (q : ℤ) - s := by
        have : s ≤ q := le_of_lt hsq
        omega
      calc (j : ℤ) ≤ ((q - s : ℕ) : ℤ) := by exact_mod_cast h1
        _ = (q : ℤ) - s := h2
    rcases (by omega : 0 ≤ c ∨ c ≤ -1) with hc0 | hc0
    · have h1 : (0 : ℤ) ≤ (q : ℤ) * c := mul_nonneg (by positivity) hc0
      rw [abs_of_nonneg (by omega)]
      omega
    · have h1 : (q : ℤ) * c ≤ -q := by nlinarith
      rw [abs_of_nonpos (by omega)]
      omega
  -- Step 2: real form of step 1
  have habsR : (j : ℝ) ≤ |(a : ℝ) * r - (k : ℝ) * q| := by
    have h2 : ((j : ℤ) : ℝ) ≤ ((|((a * r : ℕ) : ℤ) - k * q| : ℤ) : ℝ) := by
      exact_mod_cast habs
    rw [Int.cast_abs] at h2
    push_cast at h2
    exact h2
  -- Step 3: the rational point is `j/q`-separated, the window is `≤ 1/(2q)`
  have hq_div : (j : ℝ) / q ≤ |(a : ℝ) * r / q - (k : ℝ)| := by
    have he : (a : ℝ) * r / q - (k : ℝ) = ((a : ℝ) * r - (k : ℝ) * q) / q := by
      field_simp
    rw [he, abs_div, abs_of_pos hqR]
    gcongr
  have h1 : |(a : ℝ) * r / q - (k : ℝ)| - |(α - (a : ℝ) / q) * r| ≤
      |α * r - (k : ℝ)| := by
    have he : (a : ℝ) * r / q - (k : ℝ) =
        (α * r - (k : ℝ)) - (α - (a : ℝ) / q) * r := by ring
    have h2 : |(a : ℝ) * r / q - (k : ℝ)| ≤
        |α * r - (k : ℝ)| + |(α - (a : ℝ) / q) * r| := by
      rw [he]
      exact abs_sub _ _
    linarith
  have hsmall : |(α - (a : ℝ) / q) * r| ≤ 1 / (2 * q) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ (r : ℝ))]
    have hm1 : |α - (a : ℝ) / q| * r ≤ (1 / ((q : ℝ) * n)) * r :=
      mul_le_mul_of_nonneg_right hdist.le (Nat.cast_nonneg r)
    have hm2 : (1 / ((q : ℝ) * n)) * (r : ℝ) ≤ 1 / (2 * q) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have h2r : 2 * (r : ℝ) ≤ (n : ℝ) := by
        have hN : 2 * r ≤ n := by omega
        exact_mod_cast hN
      nlinarith
    linarith
  have hjq : (j : ℝ) / (2 * q) + 1 / (2 * q) ≤ (j : ℝ) / q := by
    rw [← add_div, div_le_div_iff₀ (by positivity) hqR]
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    nlinarith
  linarith

/-- **Partial-sum kernel bound.**  Every prefix of the inner geometric sum
at frequency `α·d` obeys the Type-I kernel dichotomy bound. -/
theorem norm_addChar_partial_le_kernel (n a q R d k Q : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (_hn1 : 1 ≤ n) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (h2R : 2 * R ≤ Q) (hd1 : 1 ≤ d) (hdR : d ≤ R) (hk : k ≤ n / d) :
    ‖∑ f ∈ Finset.Ioc 0 k, Vinogradov.addChar (α * d) f‖ ≤
      typeIKernelBound n a q d := by
  unfold typeIKernelBound
  split_ifs with hdvd
  · -- resonant modulus: trivial cardinality cap
    refine (norm_sum_le _ _).trans ?_
    have hsum : ∑ f ∈ Finset.Ioc 0 k, ‖Vinogradov.addChar (α * d) f‖ = (k : ℝ) := by
      rw [Finset.sum_congr rfl fun f _ => Vinogradov.norm_addChar _ _,
        Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one]
    rw [hsum]
    have hkd : (k : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  · -- non-resonant modulus: geometric kernel + separation
    have hsep := nonres_dist_int_lb Q a q R d α hq2 (by omega) hcop hdist h2R
      hd1 hdR hdvd
    have hj1 : 1 ≤ min (a * d % q) (q - a * d % q) :=
      nonres_symdist_pos a q d (by omega) hcop hdvd
    have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hjR : (0 : ℝ) < ((min (a * d % q) (q - a * d % q) : ℕ) : ℝ) := by
      exact_mod_cast hj1
    have hjq2 : (0 : ℝ) < ((min (a * d % q) (q - a * d % q) : ℕ) : ℝ) / (2 * q) :=
      div_pos hjR (by positivity)
    have hround : (round (α * d) : ℝ) ≠ α * d := by
      intro hc
      have h0 := hsep (round (α * d))
      rw [hc, sub_self, abs_zero] at h0
      linarith
    refine (norm_addChar_sum_Ioc_le_round (α * d) hround k).trans ?_
    have hd0 := hsep (round (α * d))
    have habs0 : (0 : ℝ) < |α * d - (round (α * d) : ℝ)| := lt_of_lt_of_le hjq2 hd0
    rw [div_le_div_iff₀ (by linarith) hjR]
    have hkey : 2 * (q : ℝ) * (((min (a * d % q) (q - a * d % q) : ℕ) : ℝ) / (2 * q)) =
        ((min (a * d % q) (q - a * d % q) : ℕ) : ℝ) := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hd0 (by positivity : (0:ℝ) ≤ 2 * (q : ℝ))]

/-! ## Phase 2, Layer 12c: the classical harmonic-block kernel sum -/

/-- **Resonant kernel sum**: `Σ_{r ≤ R, q ∣ r} (n/r + 1) ≤ (n/q)(1+log n) + R`. -/
theorem sum_typeIKernel_resonant_le (n q R : ℕ) (hq1 : 1 ≤ q) (hRn : R ≤ n)
    (hn1 : 1 ≤ n) :
    ∑ r ∈ (Finset.Icc 1 R).filter (fun r => q ∣ r), (((n / r : ℕ) : ℝ) + 1) ≤
      (n : ℝ) / q * (1 + Real.log n) + (R : ℝ) := by
  classical
  have hterm0 : ∀ r : ℕ, (0:ℝ) ≤ ((n / r : ℕ) : ℝ) + 1 := fun r => by positivity
  have hsub : (Finset.Icc 1 R).filter (fun r => q ∣ r) ⊆
      (Finset.Icc 1 (R / q)).image (fun h => q * h) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hr1, hrR⟩, hdvd⟩ := hr
    refine Finset.mem_image.mpr ⟨r / q, ?_, Nat.mul_div_cancel' hdvd⟩
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right hrR⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun i _ _ => hterm0 i) ?_
  rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h :
    Set.InjOn (fun h => q * h) ↑(Finset.Icc 1 (R / q)))]
  have hbound : ∀ h ∈ Finset.Icc 1 (R / q),
      ((n / (q * h) : ℕ) : ℝ) + 1 ≤ (n : ℝ) / q * ((h : ℝ))⁻¹ + 1 := by
    intro h hh
    obtain ⟨hh1, _⟩ := Finset.mem_Icc.mp hh
    have h1 : ((n / (q * h) : ℕ) : ℝ) ≤ (n : ℝ) / ((q * h : ℕ) : ℝ) :=
      Nat.cast_div_le
    have heq : (n : ℝ) / ((q * h : ℕ) : ℝ) = (n : ℝ) / q * ((h : ℝ))⁻¹ := by
      rw [Nat.cast_mul, div_mul_eq_div_div, div_eq_mul_inv ((n : ℝ) / q)]
    linarith [heq ▸ h1]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, mul_one]
  have hH := sum_Icc_inv_le_one_add_log (R / q)
  have hlogRq : Real.log ((R / q : ℕ) : ℝ) ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos (R / q) with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hpos)
        (by exact_mod_cast le_trans (Nat.div_le_self R q) hRn)
  have hnq0 : (0 : ℝ) ≤ (n : ℝ) / q := by positivity
  have hcard : ((R / q + 1 - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    have : R / q + 1 - 1 ≤ R := by
      have := Nat.div_le_self R q
      omega
    exact_mod_cast this
  have hsum_inv : (n : ℝ) / q * (∑ d ∈ Finset.Icc 1 (R / q), ((d : ℝ))⁻¹) ≤
      (n : ℝ) / q * (1 + Real.log n) := by
    refine mul_le_mul_of_nonneg_left ?_ hnq0
    linarith
  linarith

/-- **Non-resonant kernel sum** (Davenport residue blocks):
`Σ_{r ≤ R, q ∤ r} q/j_r ≤ 4(R + q)(1 + log q)`. -/
theorem sum_typeIKernel_nonres_le (a q R : ℕ) (hq2 : 2 ≤ q)
    (hcop : Nat.Coprime a q) :
    ∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬ q ∣ r),
        (q : ℝ) / ((min (a * r % q) (q - a * r % q) : ℕ) : ℝ) ≤
      4 * ((R : ℝ) + q) * (1 + Real.log q) := by
  classical
  have hq0 : 0 < q := by omega
  have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by
    have : (0:ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
    linarith
  have hmaps : ∀ r ∈ (Finset.Icc 1 R).filter (fun r => ¬ q ∣ r),
      r / q ∈ Finset.range (R / q + 1) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hr.1.2))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun r => (q : ℝ) / ((min (a * r % q) (q - a * r % q) : ℕ) : ℝ))]
  have hfiber : ∀ h ∈ Finset.range (R / q + 1),
      ∑ r ∈ ((Finset.Icc 1 R).filter (fun r => ¬ q ∣ r)).filter
          (fun r => r / q = h),
        (q : ℝ) / ((min (a * r % q) (q - a * r % q) : ℕ) : ℝ) ≤
      (q : ℝ) * (4 * (1 + Real.log q)) := by
    intro h _
    set s := ((Finset.Icc 1 R).filter (fun r => ¬ q ∣ r)).filter
      (fun r => r / q = h) with hsdef
    have hinj : ∀ x ∈ s, ∀ y ∈ s, a * x % q = a * y % q → x = y := by
      intro x hx y hy hxy
      simp only [hsdef, Finset.mem_filter, Finset.mem_Icc] at hx hy
      have hmod : x % q = y % q :=
        Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcop) hxy
      have hxq : x / q = h := hx.2
      have hyq : y / q = h := hy.2
      calc x = q * h + x % q := by rw [← hxq]; exact (Nat.div_add_mod x q).symm
        _ = q * h + y % q := by rw [hmod]
        _ = y := by rw [← hyq]; exact Nat.div_add_mod y q
    have hinjOn : Set.InjOn (fun r => a * r % q) ↑s := by
      intro x hx y hy hxy
      exact hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy
    refine le_trans (le_of_eq (Finset.sum_image
      (f := fun t => (q : ℝ) / ((min t (q - t) : ℕ) : ℝ)) hinjOn).symm) ?_
    have hsub : s.image (fun r => a * r % q) ⊆ Finset.Ico 1 q := by
      intro t ht
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
      simp only [hsdef, Finset.mem_filter, Finset.mem_Icc] at hr
      have hndvd := hr.1.2
      have hs0 : a * r % q ≠ 0 := by
        intro hc
        exact hndvd (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcop)
          (Nat.dvd_of_mod_eq_zero hc))
      exact Finset.mem_Ico.mpr ⟨by omega, Nat.mod_lt _ hq0⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => by positivity)) ?_
    have hfact : ∑ t ∈ Finset.Ico 1 q, (q : ℝ) / ((min t (q - t) : ℕ) : ℝ) =
        (q : ℝ) * ∑ t ∈ Finset.Ico 1 q, (1 : ℝ) / ((min t (q - t) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [mul_one_div]
    rw [hfact]
    have hsym := AnalyticNT.Bilinear.TypeI.symmetric_harmonic_sum_bound q hq2
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact_mod_cast hsym
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcount : ((R / q + 1 : ℕ) : ℝ) * (q : ℝ) ≤ (R : ℝ) + q := by
    have hN : (R / q + 1) * q ≤ R + q := by
      have h1 := Nat.div_mul_le_self R q
      rw [Nat.add_mul, one_mul]
      omega
    exact_mod_cast hN
  calc ((R / q + 1 : ℕ) : ℝ) * ((q : ℝ) * (4 * (1 + Real.log q)))
      = (((R / q + 1 : ℕ) : ℝ) * (q : ℝ)) * (4 * (1 + Real.log q)) := by ring
    _ ≤ ((R : ℝ) + q) * (4 * (1 + Real.log q)) :=
        mul_le_mul_of_nonneg_right hcount (by linarith)
    _ = 4 * ((R : ℝ) + q) * (1 + Real.log q) := by ring

/-- **Master Type-I kernel sum** (the classical
`Σ_{r ≤ R} min(n/r, 1/‖rα‖) ≪ (n/q + R + q)·log` bound, in dichotomy
form). -/
theorem sum_typeIKernel_le (n a q R : ℕ) (hq2 : 2 ≤ q) (hRn : R ≤ n)
    (hn1 : 1 ≤ n) (hcop : Nat.Coprime a q) :
    ∑ r ∈ Finset.Icc 1 R, typeIKernelBound n a q r ≤
      (n : ℝ) / q * (1 + Real.log n) + (R : ℝ) +
        4 * ((R : ℝ) + q) * (1 + Real.log q) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 R) (fun r => q ∣ r)]
  have h1 : ∑ r ∈ (Finset.Icc 1 R).filter (fun r => q ∣ r),
      typeIKernelBound n a q r =
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r => q ∣ r), (((n / r : ℕ) : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hr
    unfold typeIKernelBound
    rw [if_pos hdvd]
  have h2 : ∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬ q ∣ r),
      typeIKernelBound n a q r =
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬ q ∣ r),
        (q : ℝ) / ((min (a * r % q) (q - a * r % q) : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hr
    unfold typeIKernelBound
    rw [if_neg hdvd]
  rw [h1, h2]
  have hres := sum_typeIKernel_resonant_le n q R (by omega) hRn hn1
  have hnonres := sum_typeIKernel_nonres_le a q R hq2 hcop
  linarith

/-! ## Phase 2, Layer 12d: the log-weighted inner sum (Abel) -/

/-- **Log-weighted inner sum** at modulus `d`:
`‖Σ_{f ≤ n/d} log f · e(αdf)‖ ≤ 2·log n·B(d)` via Abel summation against
the partial-sum kernel. -/
theorem norm_logInner_le_kernel (n a q R d Q : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (hn1 : 1 ≤ n) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (h2R : 2 * R ≤ Q) (hd1 : 1 ≤ d) (hdR : d ≤ R) :
    ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
        Vinogradov.addChar α (d * f)‖ ≤
      2 * Real.log n * typeIKernelBound n a q d := by
  have hB0 := typeIKernelBound_nonneg n a q d
  have hL0 : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hrw : ∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
      Vinogradov.addChar α (d * f) =
      ∑ f ∈ Finset.Ioc 0 (n / d),
        Vinogradov.addChar (α * d) f * ((Real.log f : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [addChar_freq_shift α d f, mul_comm]
  rw [hrw]
  refine le_trans (abel_norm_bound_monotone_increasing
    (fun f => Vinogradov.addChar (α * d) f) (fun f => Real.log f) 0 (n / d)
    (Nat.zero_le _) (typeIKernelBound n a q d) hB0 ?_ ?_ ?_) ?_
  · intro k hk
    obtain ⟨-, hk2⟩ := Finset.mem_Ioc.mp hk
    exact norm_addChar_partial_le_kernel n a q R d k Q α hq2 hn1 hcop hdist
      h2R hd1 hdR hk2
  · intro k
    exact Real.log_natCast_nonneg k
  · intro k _ _
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · exact Real.log_le_log (by exact_mod_cast hkpos)
        (by exact_mod_cast Nat.le_succ k)
  · have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
      · rw [h0]
        simpa using hL0
      · exact Real.log_le_log (by exact_mod_cast hpos)
          (by exact_mod_cast Nat.div_le_self n d)
    have hmul := mul_le_mul_of_nonneg_left hlog
      (by linarith : (0:ℝ) ≤ 2 * typeIKernelBound n a q d)
    nlinarith

/-! ## Phase 2, Layer 12e: crude small-`n` Type-I bound -/

/-- Crude trivial bound for the Vaughan Type-I bilinear sum
(used only for `n ≤ 31`). -/
theorem norm_vaughanTypeIBilinearSum_le_crude (U V n : ℕ) (α : ℝ) (hn : 1 ≤ n) :
    ‖Vinogradov.vaughanTypeIBilinearSum U V n α‖ ≤
      2 * (n : ℝ) ^ 2 * Real.log n := by
  have hL0 : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  rw [vaughanTypeIBilinearSum_eq_fixed_outer]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ Finset.Ioc 0 n,
      ‖Vinogradov.vaughanTypeIBilinearCoeff U V d *
        ∑ f ∈ Finset.Ioc 0 (n / d),
          Vinogradov.vaughanTypeIBilinearInnerCoeff V f *
            Vinogradov.addChar α (d * f)‖ ≤ (n : ℝ) * (2 * Real.log n) := by
    intro d hd
    rw [norm_mul]
    have hc := norm_vaughanTypeIBilinearCoeff_le_one U V d
    have hin : ‖∑ f ∈ Finset.Ioc 0 (n / d),
        Vinogradov.vaughanTypeIBilinearInnerCoeff V f *
          Vinogradov.addChar α (d * f)‖ ≤ (n : ℝ) * (2 * Real.log n) := by
      refine (norm_sum_le _ _).trans ?_
      have hms : ∀ f ∈ Finset.Ioc 0 (n / d),
          ‖Vinogradov.vaughanTypeIBilinearInnerCoeff V f *
            Vinogradov.addChar α (d * f)‖ ≤ 2 * Real.log n := by
        intro f hf
        obtain ⟨-, hf2⟩ := Finset.mem_Ioc.mp hf
        rw [norm_mul, Vinogradov.norm_addChar, mul_one]
        exact norm_vaughanTypeIBilinearInnerCoeff_le V n f
          (le_trans hf2 (Nat.div_le_self n d))
      refine (Finset.sum_le_sum hms).trans ?_
      rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      have h1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.div_le_self n d
      have h2 : (0:ℝ) ≤ 2 * Real.log n := by linarith
      exact mul_le_mul_of_nonneg_right h1 h2
    calc ‖Vinogradov.vaughanTypeIBilinearCoeff U V d‖ *
          ‖∑ f ∈ Finset.Ioc 0 (n / d),
            Vinogradov.vaughanTypeIBilinearInnerCoeff V f *
              Vinogradov.addChar α (d * f)‖
        ≤ 1 * ((n : ℝ) * (2 * Real.log n)) :=
          mul_le_mul hc hin (norm_nonneg _) (by norm_num)
      _ = (n : ℝ) * (2 * Real.log n) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have h0 : (0 : ℝ) ≤ (n : ℝ) * (2 * Real.log n) := by positivity
  calc (n : ℝ) * ((n : ℝ) * (2 * Real.log n))
      = 2 * (n : ℝ) ^ 2 * Real.log n := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * Real.log n := le_refl _

/-! ## Phase 2, Layer 12f: the `ζ * Λ_{≤U}` inner piece -/

/-- **Convolution expansion of the `ζ * Λ_{≤U}` inner sum**: hyperbola swap
onto moduli `e ≤ U`, leaving pure geometric sums at moduli `d·e`. -/
theorem norm_zetaLambdaInner_le_sum (U n d : ℕ) (α : ℝ) :
    ‖∑ f ∈ Finset.Ioc 0 (n / d),
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)‖ ≤
      ∑ e ∈ Finset.Icc 1 U, ArithmeticFunction.vonMangoldt e *
        ‖∑ g ∈ Finset.Ioc 0 (n / (d * e)),
          Vinogradov.addChar (α * ((d * e : ℕ) : ℝ)) g‖ := by
  classical
  -- Step 1: expand the convolution and swap the hyperbola sum
  have hstep1 : ∑ f ∈ Finset.Ioc 0 (n / d),
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
        Vinogradov.addChar α (d * f) =
      ∑ e ∈ Finset.Ioc 0 (n / d),
        ((Vinogradov.vaughanLambdaLow U e : ℝ) : ℂ) *
          ∑ g ∈ Finset.Ioc 0 (n / d / e),
            Vinogradov.addChar α (d * (e * g)) := by
    have h1 : ∀ f ∈ Finset.Ioc 0 (n / d),
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f) =
        ∑ e ∈ f.divisors, ((Vinogradov.vaughanLambdaLow U e : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f) := by
      intro f _
      rw [ArithmeticFunction.coe_zeta_mul_apply, Complex.ofReal_sum,
        Finset.sum_mul]
    rw [Finset.sum_congr rfl h1,
      sum_Ioc_divisors_swap (n / d) (fun e m =>
        ((Vinogradov.vaughanLambdaLow U e : ℝ) : ℂ) *
          Vinogradov.addChar α (d * m))]
    exact Finset.sum_congr rfl fun e _ => (Finset.mul_sum _ _ _).symm
  rw [hstep1]
  refine (norm_sum_le _ _).trans ?_
  -- Step 2: restrict to `e ≤ U` (the truncated Λ vanishes above the cutoff)
  have hres := Finset.sum_filter_of_ne
    (s := Finset.Ioc 0 (n / d)) (p := fun e => e ≤ U)
    (f := fun e => ‖((Vinogradov.vaughanLambdaLow U e : ℝ) : ℂ) *
      ∑ g ∈ Finset.Ioc 0 (n / d / e),
        Vinogradov.addChar α (d * (e * g))‖)
    (by
      intro e _ hne
      by_contra hcon
      push Not at hcon
      apply hne
      have hz : Vinogradov.vaughanLambdaLow U e = 0 := by
        unfold Vinogradov.vaughanLambdaLow
        simp only [ArithmeticFunction.coe_mk]
        rw [if_neg (by omega)]
      simp [hz])
  rw [← hres]
  have hsubset : (Finset.Ioc 0 (n / d)).filter (fun e => e ≤ U) ⊆
      Finset.Icc 1 U := by
    intro e he
    obtain ⟨hmem, hle⟩ := Finset.mem_filter.mp he
    obtain ⟨he0, _⟩ := Finset.mem_Ioc.mp hmem
    exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun e _ _ => norm_nonneg _)) ?_
  · refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hlam : |Vinogradov.vaughanLambdaLow U e| ≤
        ArithmeticFunction.vonMangoldt e := by
      unfold Vinogradov.vaughanLambdaLow
      simp only [ArithmeticFunction.coe_mk]
      rcases Nat.lt_or_ge U e with hcase | hcase
      · rw [if_neg (by omega), abs_zero]
        exact ArithmeticFunction.vonMangoldt_nonneg
      · rw [if_pos hcase, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hsum_eq : ∑ g ∈ Finset.Ioc 0 (n / d / e),
        Vinogradov.addChar α (d * (e * g)) =
        ∑ g ∈ Finset.Ioc 0 (n / (d * e)),
          Vinogradov.addChar (α * ((d * e : ℕ) : ℝ)) g := by
      rw [Nat.div_div_eq_div_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← mul_assoc d e g, addChar_freq_shift α (d * e) g]
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_right hlam (norm_nonneg _)

/-! ## Phase 2, Layer 12g: the Type-I piece -/

/-- **Phase-2 obligation (Type-I piece) DISCHARGED.**  Fixed-outer form +
log/convolution split + Abel summation against the geometric kernel +
the classical `Σ_{r ≤ R} min(n/r, 1/‖rα‖)`-type harmonic-block bound
(`typeIKernelBound` dichotomy), with constant `K = 2000`. -/
theorem vaughanTypeIPieceQSensitiveEnvelopeBound_proved :
    vaughanTypeIPieceQSensitiveEnvelopeBound := by
  classical
  refine ⟨2000, by norm_num, ?_⟩
  intro n a q α hn3 hq2 hqn haq hcop hdist
  have hE0 := envelope_nonneg n q
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hL0 : 0 ≤ Real.log n := by linarith
  by_cases hn32 : n < 32
  · -- crude branch (`n ≤ 31`): trivial bound against the envelope floor
    have hcrude := norm_vaughanTypeIBilinearSum_le_crude
      (vaughanCutoff n) (vaughanCutoff n) n α (by omega)
    have hE2 := envelope_ge_two_log_pow_four n q hn3 hq2
    have hL4 := log_le_log_pow_four n hn3
    have hn31 : (n : ℝ) ≤ 31 := by exact_mod_cast (by omega : n ≤ 31)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq : (n : ℝ) ^ 2 ≤ 961 := by
      have h := pow_le_pow_left₀ hn0 hn31 2
      norm_num at h
      exact h
    calc ‖Vinogradov.vaughanTypeIBilinearSum
          (vaughanCutoff n) (vaughanCutoff n) n α‖
        ≤ 2 * (n : ℝ) ^ 2 * Real.log n := hcrude
      _ ≤ 1922 * Real.log n := by nlinarith
      _ ≤ 1922 * (Real.log n) ^ 4 := by
          linarith [mul_le_mul_of_nonneg_left hL4 (by norm_num : (0:ℝ) ≤ 1922)]
      _ = 961 * (2 * (Real.log n) ^ 4) := by ring
      _ ≤ 961 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
          linarith [mul_le_mul_of_nonneg_left hE2 (by norm_num : (0:ℝ) ≤ 961)]
      _ ≤ 2000 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by linarith
  · -- main branch: `n ≥ 32`
    push Not at hn32
    set U := vaughanCutoff n with hUdef
    have hU1 : 1 ≤ U := by rw [hUdef]; exact one_le_vaughanCutoff n (by omega)
    have hUn45 : (U : ℝ) * U ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
      rw [hUdef]; exact vaughanCutoff_sq_le_rpow45 n
    have h2UV : 2 * (U * U) ≤ n := by
      have hreal : 2 * ((U : ℝ) * U) ≤ (n : ℝ) := by
        have h1 : 2 * ((U : ℝ) * U) ≤ 2 * (n : ℝ) ^ ((4 : ℝ) / 5) := by linarith
        linarith [two_mul_rpow45_le hn32]
      exact_mod_cast hreal
    have hUVn : U * U ≤ n := by omega
    have hUUU : U ≤ U * U := Nat.le_mul_of_pos_right U (by omega)
    have hUn : U ≤ n := le_trans hUUU hUVn
    have h2U : 2 * U ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    -- fixed-outer form
    rw [vaughanTypeIBilinearSum_eq_fixed_outer]
    refine le_trans (norm_sum_le _ _) ?_
    -- restrict the outer sum to `d ≤ U`
    have hres := Finset.sum_filter_of_ne
      (s := Finset.Ioc 0 n) (p := fun d => d ≤ U)
      (f := fun d => ‖Vinogradov.vaughanTypeIBilinearCoeff U U d *
        ∑ f ∈ Finset.Ioc 0 (n / d),
          Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
            Vinogradov.addChar α (d * f)‖)
      (by
        intro d _ hne
        by_contra hcon
        push Not at hcon
        apply hne
        simp [vaughanTypeIBilinearCoeff_eq_zero_of_gt U U d hcon])
    rw [← hres]
    have hsubset : (Finset.Ioc 0 n).filter (fun d => d ≤ U) ⊆
        Finset.Icc 1 U := by
      intro d hd
      obtain ⟨hmem, hle⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd0, _⟩ := Finset.mem_Ioc.mp hmem
      exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun d _ _ => norm_nonneg _)) ?_
    -- split each summand into `log` and `ζ * Λ_{≤U}` pieces
    have hWsplit : ∀ d ∈ Finset.Icc 1 U,
        ‖Vinogradov.vaughanTypeIBilinearCoeff U U d *
          ∑ f ∈ Finset.Ioc 0 (n / d),
            Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
              Vinogradov.addChar α (d * f)‖ ≤
        ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)‖ +
          ‖∑ f ∈ Finset.Ioc 0 (n / d),
            ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
              Vinogradov.addChar α (d * f)‖ := by
      intro d _
      rw [norm_mul]
      have hsub : ∑ f ∈ Finset.Ioc 0 (n / d),
          Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
            Vinogradov.addChar α (d * f) =
          (∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)) -
          ∑ f ∈ Finset.Ioc 0 (n / d),
            ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
              Vinogradov.addChar α (d * f) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun f _ => ?_
        unfold Vinogradov.vaughanTypeIBilinearInnerCoeff
          Vinogradov.vaughanTypeIInnerArithmetic
        rw [arithmeticFunction_sub_apply, ArithmeticFunction.log_apply,
          Complex.ofReal_sub, sub_mul]
      calc ‖Vinogradov.vaughanTypeIBilinearCoeff U U d‖ *
            ‖∑ f ∈ Finset.Ioc 0 (n / d),
              Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
                Vinogradov.addChar α (d * f)‖
          ≤ 1 * ‖∑ f ∈ Finset.Ioc 0 (n / d),
              Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
                Vinogradov.addChar α (d * f)‖ :=
            mul_le_mul_of_nonneg_right
              (norm_vaughanTypeIBilinearCoeff_le_one U U d) (norm_nonneg _)
        _ = ‖∑ f ∈ Finset.Ioc 0 (n / d),
              Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
                Vinogradov.addChar α (d * f)‖ := one_mul _
        _ ≤ _ := by
            rw [hsub]
            exact norm_sub_le _ _
    refine le_trans (Finset.sum_le_sum hWsplit) ?_
    rw [Finset.sum_add_distrib]
    -- the `log` piece via Abel + the kernel master sum
    have hLpart : ∑ d ∈ Finset.Icc 1 U,
        ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)‖ ≤
        2 * Real.log n * ((n : ℝ) / q * (1 + Real.log n) + ((U * U : ℕ) : ℝ) +
          4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q)) := by
      have hper : ∀ d ∈ Finset.Icc 1 U,
          ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)‖ ≤
          2 * Real.log n * typeIKernelBound n a q d := by
        intro d hd
        obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
        exact norm_logInner_le_kernel n a q U d n α hq2 (by omega) hcop hdist
          h2U hd1 hdU
      refine le_trans (Finset.sum_le_sum hper) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      have hmaster := sum_typeIKernel_le n a q U hq2 hUn (by omega) hcop
      have hUcast : (U : ℝ) ≤ ((U * U : ℕ) : ℝ) := by exact_mod_cast hUUU
      have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by
        have : (0:ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
        linarith
      nlinarith
    -- the `ζ * Λ_{≤U}` piece via the hyperbola swap + the kernel master sum
    have hZpart : ∑ d ∈ Finset.Icc 1 U,
        ‖∑ f ∈ Finset.Ioc 0 (n / d),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)‖ ≤
        Real.log n * ((n : ℝ) / q * (1 + Real.log n) + ((U * U : ℕ) : ℝ) +
          4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q)) := by
      refine le_trans (Finset.sum_le_sum fun d _ =>
        norm_zetaLambdaInner_le_sum U n d α) ?_
      rw [← Finset.sum_product']
      have hmaps : ∀ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U,
          p.1 * p.2 ∈ Finset.Icc 1 (U * U) := by
        rintro ⟨d, e⟩ hp
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
        rw [Finset.mem_Icc]
        constructor
        · have := Nat.mul_le_mul hp.1.1 hp.2.1
          omega
        · exact Nat.mul_le_mul hp.1.2 hp.2.2
      rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun p => ArithmeticFunction.vonMangoldt p.2 *
          ‖∑ g ∈ Finset.Ioc 0 (n / (p.1 * p.2)),
            Vinogradov.addChar (α * ((p.1 * p.2 : ℕ) : ℝ)) g‖)]
      have hper_r : ∀ r ∈ Finset.Icc 1 (U * U),
          ∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
              (fun p => p.1 * p.2 = r),
            ArithmeticFunction.vonMangoldt p.2 *
              ‖∑ g ∈ Finset.Ioc 0 (n / (p.1 * p.2)),
                Vinogradov.addChar (α * ((p.1 * p.2 : ℕ) : ℝ)) g‖ ≤
          Real.log n * typeIKernelBound n a q r := by
        intro r hr
        obtain ⟨hr1, hrUV⟩ := Finset.mem_Icc.mp hr
        have hcongr : ∀ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
            (fun p => p.1 * p.2 = r),
            ArithmeticFunction.vonMangoldt p.2 *
              ‖∑ g ∈ Finset.Ioc 0 (n / (p.1 * p.2)),
                Vinogradov.addChar (α * ((p.1 * p.2 : ℕ) : ℝ)) g‖ =
            ArithmeticFunction.vonMangoldt p.2 *
              ‖∑ g ∈ Finset.Ioc 0 (n / r), Vinogradov.addChar (α * r) g‖ := by
          intro p hp
          obtain ⟨-, hpr⟩ := Finset.mem_filter.mp hp
          rw [hpr]
        rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
        have hG0 : (0 : ℝ) ≤ ‖∑ g ∈ Finset.Ioc 0 (n / r),
            Vinogradov.addChar (α * r) g‖ := norm_nonneg _
        have hGr : ‖∑ g ∈ Finset.Ioc 0 (n / r),
            Vinogradov.addChar (α * r) g‖ ≤ typeIKernelBound n a q r :=
          norm_addChar_partial_le_kernel n a q (U * U) r (n / r) n α hq2
            (by omega) hcop hdist h2UV hr1 hrUV (le_refl _)
        have hw : ∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
            (fun p => p.1 * p.2 = r), ArithmeticFunction.vonMangoldt p.2 ≤
            Real.log n := by
          set S := (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
            (fun p => p.1 * p.2 = r) with hSdef
          have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) ↑S := by
            intro p₁ hp₁ p₂ hp₂ hcoord
            simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq,
              Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
            simp only at hcoord
            have he1 : 1 ≤ p₁.2 := hp₁.1.2.1
            have hmul : p₁.1 * p₁.2 = p₂.1 * p₂.2 := by rw [hp₁.2, hp₂.2]
            have h1 : p₁.1 = p₂.1 := by
              refine Nat.eq_of_mul_eq_mul_right (by omega : 0 < p₁.2) ?_
              rw [hmul, hcoord]
            exact Prod.ext h1 hcoord
          have himg := Finset.sum_image
            (f := fun e => ArithmeticFunction.vonMangoldt e) hinj
          refine le_trans (le_of_eq himg.symm) ?_
          have hsub : S.image (fun p : ℕ × ℕ => p.2) ⊆ r.divisors := by
            intro e he
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
            obtain ⟨-, hpr⟩ := Finset.mem_filter.mp hp
            exact Nat.mem_divisors.mpr ⟨Dvd.intro_left p.1 hpr, by omega⟩
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)) ?_
          rw [ArithmeticFunction.vonMangoldt_sum]
          have hrn : r ≤ n := le_trans hrUV hUVn
          exact Real.log_le_log (by exact_mod_cast hr1)
            (by exact_mod_cast hrn)
        exact mul_le_mul hw hGr hG0 hL0
      refine le_trans (Finset.sum_le_sum hper_r) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hL0
      exact sum_typeIKernel_le n a q (U * U) hq2 hUVn (by omega) hcop
    -- final numeric assembly
    set M2 := (n : ℝ) / q * (1 + Real.log n) + ((U * U : ℕ) : ℝ) +
      4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q) with hM2def
    have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by
      have : (0:ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
      linarith
    have hM2bound : M2 ≤ 10 * Real.log n *
        ((n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q) := by
      rw [hM2def]
      have hUU45 : ((U * U : ℕ) : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
        rw [Nat.cast_mul]
        exact hUn45
      have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hlogq : 1 + Real.log q ≤ 2 * Real.log n := by
        have h1 : Real.log q ≤ Real.log n :=
          Real.log_le_log hq0R (by exact_mod_cast hqn)
        linarith
      have hnq0 : (0 : ℝ) ≤ (n : ℝ) / q := by positivity
      have hr450 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have h1 : (n : ℝ) / q * (1 + Real.log n) ≤
          (n : ℝ) / q * (2 * Real.log n) :=
        mul_le_mul_of_nonneg_left (by linarith) hnq0
      have h2 : ((U * U : ℕ) : ℝ) ≤ 2 * Real.log n * (n : ℝ) ^ ((4 : ℝ) / 5) := by
        calc ((U * U : ℕ) : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := hUU45
          _ = 1 * (n : ℝ) ^ ((4 : ℝ) / 5) := (one_mul _).symm
          _ ≤ 2 * Real.log n * (n : ℝ) ^ ((4 : ℝ) / 5) :=
              mul_le_mul_of_nonneg_right (by linarith) hr450
      have h3 : 4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q) ≤
          8 * Real.log n * ((n : ℝ) ^ ((4 : ℝ) / 5) + q) := by
        have ha : ((U * U : ℕ) : ℝ) + q ≤ (n : ℝ) ^ ((4 : ℝ) / 5) + q := by
          linarith
        calc 4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q)
            ≤ 4 * (((U * U : ℕ) : ℝ) + q) * (2 * Real.log n) :=
              mul_le_mul_of_nonneg_left hlogq (by positivity)
          _ ≤ 4 * ((n : ℝ) ^ ((4 : ℝ) / 5) + q) * (2 * Real.log n) := by
              have hc := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ) ≤ 4))
                (by linarith : (0:ℝ) ≤ 2 * Real.log n)
              linarith
          _ = 8 * Real.log n * ((n : ℝ) ^ ((4 : ℝ) / 5) + q) := by ring
      have hq0' : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      nlinarith [mul_nonneg hL0 hnq0, mul_nonneg hL0 hr450,
        mul_nonneg hL0 hq0']
    -- envelope comparison
    have hsqpos : (0 : ℝ) < Real.sqrt q := by
      refine Real.sqrt_pos.mpr ?_
      exact_mod_cast (by omega : 0 < q)
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    have hsqle : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
      have h1 : (q : ℝ) ≤ ((q : ℝ)) ^ 2 := by nlinarith
      calc Real.sqrt (q : ℝ) ≤ Real.sqrt (((q : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (q : ℝ) := Real.sqrt_sq (by positivity)
    have hdivle : (n : ℝ) / q ≤ (n : ℝ) / Real.sqrt q := by
      gcongr
    have hqsq : (q : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := cast_le_sqrt_mul q n hqn
    have hlog24 : (Real.log n) ^ 2 ≤ (Real.log n) ^ 4 :=
      pow_le_pow_right₀ hL1 (by norm_num)
    have henvX : (n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q ≤
        (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((q : ℝ) * n) := by linarith
    have henvX0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((q : ℝ) * n) := by positivity
    calc ∑ d ∈ Finset.Icc 1 U,
          ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)‖ +
        ∑ d ∈ Finset.Icc 1 U,
          ‖∑ f ∈ Finset.Ioc 0 (n / d),
            ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
              Vinogradov.addChar α (d * f)‖
        ≤ 2 * Real.log n * M2 + Real.log n * M2 := by
          rw [hM2def]
          exact add_le_add hLpart hZpart
      _ = 3 * Real.log n * M2 := by ring
      _ ≤ 3 * Real.log n * (10 * Real.log n *
            ((n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q)) :=
          mul_le_mul_of_nonneg_left hM2bound (by linarith)
      _ = 30 * (Real.log n) ^ 2 *
            ((n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q) := by ring
      _ ≤ 30 * (Real.log n) ^ 2 *
            ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n)) :=
          mul_le_mul_of_nonneg_left henvX (by positivity)
      _ ≤ 30 * (Real.log n) ^ 4 *
            ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n)) := by
          refine mul_le_mul_of_nonneg_right ?_ henvX0
          nlinarith
      _ ≤ 2000 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
          unfold hardCutoffVaughanTypeIIVinogradovEnvelope
          nlinarith [mul_nonneg henvX0 (pow_nonneg hL0 4)]


/-! ## Phase 2 COMPLETE: the corrected item-9 target and bridge proposal -/

/-- **Corrected item-9 target PROVED** (for every cutoff `U`): both Phase-2
piece obligations are discharged above, so the Phase-1 assembly yields the
`q`-sensitive classical Vinogradov envelope for the `Λ − log` Type-II sum at
every hypothesized Dirichlet witness denominator. -/
theorem hardCutoffVaughanTypeIIQSensitiveTarget_proved :
    ∀ U : ℕ → ℕ,
      hardCutoffVaughanTypeIIHighDenominatorCenterQSensitiveTargetParam U :=
  hardCutoffVaughanTypeIIQSensitiveTarget_of_pieces
    vaughanTypeIPieceQSensitiveEnvelopeBound_proved
    vaughanTypeIIPieceQSensitiveEnvelopeBound_proved


/-! ## P4 prerequisites: `Q`-window piece theorems -/

/-- **`Q`-window Type-II piece** (P4 generalization of
`vaughanTypeIIPieceQSensitiveEnvelopeBound_proved`): the Vaughan Type-II
bilinear sum at cutoff `⌊n^{2/5}⌋` obeys the classical envelope under a
reduced witness `a/q` with the WIDER Dirichlet window `1/(qQ)` at any
intermediate scale `4n^{3/5} ≤ Q ≤ n`.  The `2·(inner range) ≤ Q` side
condition of the per-block Schur machinery is discharged from the
effectiveness window `K ≤ 2n^{3/5}` and the `Q`-floor hypothesis. -/
theorem vaughanTypeIIPiece_envelope_at (n a q Q : ℕ) (α : ℝ)
    (hn6 : 6 ≤ n) (hq2 : 2 ≤ q) (hqQ : q ≤ Q) (hQn : Q ≤ n)
    (haq : a < q) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (hQ35 : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (Q : ℝ)) :
    ‖Vinogradov.vaughanTypeIIBilinearSum
        (vaughanCutoff n) (vaughanCutoff n) n α‖ ≤
      300 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hqn : q ≤ n := le_trans hqQ hQn
  have hE0 : 0 ≤ hardCutoffVaughanTypeIIVinogradovEnvelope n q := envelope_nonneg n q
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hL0 : 0 ≤ Real.log n := by linarith
  set V := vaughanCutoff n with hVdef
  have hV2 : 2 ≤ V := by rw [hVdef]; exact two_le_vaughanCutoff hn6
  have hV1 : 1 ≤ V := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- fixed-outer form + zero-extension to `Ioc 0 n`
  rw [Vinogradov.vaughanTypeIIBilinearSum_eq_fixed_outer]
  have hext : ∑ d ∈ Finset.Ioc V n,
      Vinogradov.vaughanTypeIIBilinearCoeff V d *
        ∑ m ∈ Finset.range (n / d + 1),
          Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
            Vinogradov.addChar α (d * m) =
      ∑ d ∈ Finset.Ioc 0 n,
        Vinogradov.vaughanTypeIIBilinearCoeff V d *
          ∑ m ∈ Finset.range (n / d + 1),
            Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
              Vinogradov.addChar α (d * m) := by
    refine Finset.sum_subset (Finset.Ioc_subset_Ioc (Nat.zero_le V) le_rfl) ?_
    intro x hx hnx
    have hx' := Finset.mem_Ioc.mp hx
    have hxV : x ≤ V := by
      by_contra hcon
      push Not at hcon
      exact hnx (Finset.mem_Ioc.mpr ⟨hcon, hx'.2⟩)
    rw [vaughanTypeIIBilinearCoeff_eq_zero_of_le V x hxV, zero_mul]
  rw [hext]
  -- dyadic decomposition of the outer sum
  refine le_trans (norm_sum_Ioc_zero_le_dyadic
    (fun d => Vinogradov.vaughanTypeIIBilinearCoeff V d *
      ∑ m ∈ Finset.range (n / d + 1),
        Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
          Vinogradov.addChar α (d * m)) n hn1) ?_
  -- per-block bound
  have hblock : ∀ j ∈ Finset.range (Nat.log 2 n + 1),
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
          Vinogradov.vaughanTypeIIBilinearCoeff V d *
            ∑ m ∈ Finset.range (n / d + 1),
              Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                Vinogradov.addChar α (d * m)‖ ≤
        98 * Real.log n ^ 3 *
          ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
            Real.sqrt ((q : ℝ) * n)) := by
    intro j _
    have henv0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((q : ℝ) * n) := by positivity
    have hL30 : (0 : ℝ) ≤ Real.log n ^ 3 := pow_nonneg hL0 3
    by_cases hz : ∀ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
        Vinogradov.vaughanTypeIIBilinearCoeff V d *
          ∑ m ∈ Finset.range (n / d + 1),
            Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
              Vinogradov.addChar α (d * m) = 0
    · rw [Finset.sum_eq_zero hz, norm_zero]
      have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 98) hL30) henv0
      linarith
    · -- effective block: extract a witness and discharge the hypotheses
      push Not at hz
      obtain ⟨d₀, hd₀mem, hd₀ne⟩ := hz
      obtain ⟨hDd₀, hd₀le⟩ := Finset.mem_Ioc.mp hd₀mem
      have hpow : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      have hd₀2D : d₀ ≤ 2 * 2 ^ j := by
        have := min_le_left ((2 : ℕ) ^ (j + 1)) n
        omega
      have hd₀n : d₀ ≤ n := le_trans hd₀le (min_le_right _ _)
      have hD1 : 1 ≤ (2 : ℕ) ^ j := Nat.one_le_two_pow
      have hd₀pos : 0 < d₀ := by omega
      have hcne : Vinogradov.vaughanTypeIIBilinearCoeff V d₀ ≠ 0 :=
        left_ne_zero_of_mul hd₀ne
      have hVd₀ : V < d₀ := by
        by_contra hcon
        push Not at hcon
        exact hcne (vaughanTypeIIBilinearCoeff_eq_zero_of_le V d₀ hcon)
      have hinne : (∑ m ∈ Finset.range (n / d₀ + 1),
          Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
            Vinogradov.addChar α (d₀ * m)) ≠ 0 := right_ne_zero_of_mul hd₀ne
      obtain ⟨m₀, hm₀mem, hm₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinne
      have him : Vinogradov.vaughanTypeIIBilinearInnerCoeff V m₀ ≠ 0 :=
        left_ne_zero_of_mul hm₀ne
      have hVm₀ : V < m₀ := by
        by_contra hcon
        push Not at hcon
        exact him (vaughanTypeIIBilinearInnerCoeff_eq_zero_of_le V m₀ hcon)
      have hm₀le : m₀ ≤ n / d₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₀mem)
      have hVd₀n : (V + 1) * d₀ ≤ n := by
        have h1 : V + 1 ≤ n / d₀ := by omega
        exact (Nat.le_div_iff_mul_le hd₀pos).mp h1
      -- ℕ-side block hypotheses
      have h2D : 2 * 2 ^ j ≤ n := by
        have h3 : 3 * (2 ^ j + 1) ≤ (V + 1) * d₀ :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      have hD2 : 2 ≤ (2 : ℕ) ^ j := by omega
      have hK1 : 1 ≤ n / 2 ^ j := (Nat.one_le_div_iff (by omega)).mpr (by omega)
      have hDK : 2 ^ j * (n / 2 ^ j) ≤ n := by
        calc 2 ^ j * (n / 2 ^ j) = n / 2 ^ j * 2 ^ j := Nat.mul_comm _ _
          _ ≤ n := Nat.div_mul_le_self n (2 ^ j)
      -- ℝ-side effective-window bounds
      have hsplit : (n : ℝ) ^ ((2 : ℝ) / 5) * (n : ℝ) ^ ((3 : ℝ) / 5) = (n : ℝ) := by
        rw [← Real.rpow_add hnR, show (2:ℝ)/5 + 3/5 = 1 by norm_num, Real.rpow_one]
      have hU1 : (n : ℝ) ^ ((2 : ℝ) / 5) < (V : ℝ) + 1 := by
        rw [hVdef]
        unfold vaughanCutoff
        exact Nat.lt_floor_add_one _
      have hDpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < (2 : ℕ) ^ j)
      have hDleN : (2 ^ j + 1) * (V + 1) ≤ n := by
        calc (2 ^ j + 1) * (V + 1) ≤ d₀ * (V + 1) :=
              Nat.mul_le_mul (by omega) (le_refl (V + 1))
          _ = (V + 1) * d₀ := Nat.mul_comm _ _
          _ ≤ n := hVd₀n
      have hDle : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by
        have hcc : (((2 ^ j + 1) * (V + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hDleN
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one] at hcc
        have hc1 : ((2 ^ j : ℕ) : ℝ) * ((V : ℝ) + 1) ≤ (n : ℝ) := by
          have hV0 : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
          nlinarith [hDpos.le]
        have hcast : ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5)) ≤ (n : ℝ) := by
          calc ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5))
              ≤ ((2 ^ j : ℕ) : ℝ) * ((V : ℝ) + 1) :=
                mul_le_mul_of_nonneg_left hU1.le hDpos.le
            _ ≤ (n : ℝ) := hc1
        have hpos25 : (0 : ℝ) < (n : ℝ) ^ ((2 : ℝ) / 5) :=
          Real.rpow_pos_of_pos hnR _
        have h2 : ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5)) ≤
            (n : ℝ) ^ ((3 : ℝ) / 5) * ((n : ℝ) ^ ((2 : ℝ) / 5)) := by
          calc ((2 ^ j : ℕ) : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 5)) ≤ (n : ℝ) := hcast
            _ = (n : ℝ) ^ ((3 : ℝ) / 5) * ((n : ℝ) ^ ((2 : ℝ) / 5)) := by
                rw [mul_comm]
                exact hsplit.symm
        exact le_of_mul_le_mul_right h2 hpos25
      have hKle : ((n / 2 ^ j : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) := by
        have h1 : ((n / 2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ j : ℕ) : ℝ) :=
          Nat.cast_div_le
        have hVd2 : (V : ℝ) + 1 ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
          have hN : V + 1 ≤ 2 * 2 ^ j := by omega
          exact_mod_cast hN
        have h2 : (n : ℝ) ^ ((2 : ℝ) / 5) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
          linarith [hU1]
        have h3 : (n : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) := by
          rw [div_le_iff₀ hDpos]
          calc (n : ℝ) = (n : ℝ) ^ ((2 : ℝ) / 5) * (n : ℝ) ^ ((3 : ℝ) / 5) :=
                hsplit.symm
            _ ≤ (2 * ((2 ^ j : ℕ) : ℝ)) * ((n : ℝ) ^ ((3 : ℝ) / 5)) :=
                mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hnR.le _)
            _ = 2 * (n : ℝ) ^ ((3 : ℝ) / 5) * ((2 ^ j : ℕ) : ℝ) := by ring
        linarith
      have h2KQ : 2 * (n / 2 ^ j) ≤ Q := by
        have hcast : ((2 * (n / 2 ^ j) : ℕ) : ℝ) ≤ (Q : ℝ) := by
          push_cast
          calc 2 * ((n / 2 ^ j : ℕ) : ℝ)
              ≤ 2 * (2 * (n : ℝ) ^ ((3 : ℝ) / 5)) := by linarith [hKle]
            _ = 4 * (n : ℝ) ^ ((3 : ℝ) / 5) := by ring
            _ ≤ (Q : ℝ) := hQ35
        exact_mod_cast hcast
      refine (vaughanTypeII_truncated_block_bound n a q V V (2 ^ j)
        (min (2 ^ (j + 1)) n) Q α hq2 hqQ hQn haq hcop hdist hD1 ?_
        h2D h2KQ).trans ?_
      · exact le_trans (min_le_left _ _) (le_of_eq hpow)
      · exact effective_block_envelope_bound n q (2 ^ j) (n / 2 ^ j) hn3 hq2 hqn
          hD1 hK1 hDK hDle hKle
  -- assemble: the `d = 1` term vanishes, box count ≤ 3·log n
  have hf1 : Vinogradov.vaughanTypeIIBilinearCoeff V 1 = 0 :=
    vaughanTypeIIBilinearCoeff_eq_zero_of_le V 1 hV1
  have hcount := dyadicBoxCount_le_three_log n (by omega)
  have henv0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
      Real.sqrt ((q : ℝ) * n) := by positivity
  have hblk0 : (0 : ℝ) ≤ 98 * Real.log n ^ 3 *
      ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((q : ℝ) * n)) := by
    have hL30 : (0 : ℝ) ≤ Real.log n ^ 3 := pow_nonneg hL0 3
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 98) hL30) henv0
    linarith
  calc ‖Vinogradov.vaughanTypeIIBilinearCoeff V 1 *
        ∑ m ∈ Finset.range (n / 1 + 1),
          Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
            Vinogradov.addChar α (1 * m)‖ +
        ∑ j ∈ Finset.range (Nat.log 2 n + 1),
          ‖∑ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
            Vinogradov.vaughanTypeIIBilinearCoeff V d *
              ∑ m ∈ Finset.range (n / d + 1),
                Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                  Vinogradov.addChar α (d * m)‖
      = ∑ j ∈ Finset.range (Nat.log 2 n + 1),
          ‖∑ d ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) n),
            Vinogradov.vaughanTypeIIBilinearCoeff V d *
              ∑ m ∈ Finset.range (n / d + 1),
                Vinogradov.vaughanTypeIIBilinearInnerCoeff V m *
                  Vinogradov.addChar α (d * m)‖ := by
        rw [hf1, zero_mul, norm_zero, zero_add]
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 n + 1),
          (98 * Real.log n ^ 3 *
            ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n))) := Finset.sum_le_sum hblock
    _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) *
          (98 * Real.log n ^ 3 *
            ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 3 * Real.log n *
          (98 * Real.log n ^ 3 *
            ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n))) :=
        mul_le_mul_of_nonneg_right hcount hblk0
    _ ≤ 300 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
        unfold hardCutoffVaughanTypeIIVinogradovEnvelope
        have hfin : (0 : ℝ) ≤ ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
            Real.sqrt ((q : ℝ) * n)) * (Real.log n) ^ 4 :=
          mul_nonneg henv0 (pow_nonneg hL0 4)
        linarith only [hfin]

/-- **`Q`-window Type-I piece** (P4 generalization of
`vaughanTypeIPieceQSensitiveEnvelopeBound_proved`): the Vaughan Type-I
bilinear sum at cutoff `⌊n^{2/5}⌋` obeys the classical envelope under a
reduced witness `a/q` with the WIDER Dirichlet window `1/(qQ)` at any
intermediate scale `2⌊n^{2/5}⌋² ≤ Q ≤ n` (the non-resonance separation
`nonres_dist_int_lb` needs only `2R ≤ Q` at `R = ⌊n^{2/5}⌋²`). -/
theorem vaughanTypeIPiece_envelope_at (n a q Q : ℕ) (α : ℝ)
    (hn32 : 32 ≤ n) (hq2 : 2 ≤ q) (hqQ : q ≤ Q) (hQn : Q ≤ n)
    (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (h2UVQ : 2 * (vaughanCutoff n * vaughanCutoff n) ≤ Q) :
    ‖Vinogradov.vaughanTypeIBilinearSum
        (vaughanCutoff n) (vaughanCutoff n) n α‖ ≤
      2000 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hqn : q ≤ n := le_trans hqQ hQn
  have hE0 := envelope_nonneg n q
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hL0 : 0 ≤ Real.log n := by linarith
  set U := vaughanCutoff n with hUdef
  have hU1 : 1 ≤ U := by rw [hUdef]; exact one_le_vaughanCutoff n (by omega)
  have hUn45 : (U : ℝ) * U ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [hUdef]; exact vaughanCutoff_sq_le_rpow45 n
  have h2UV : 2 * (U * U) ≤ n := by
    have hreal : 2 * ((U : ℝ) * U) ≤ (n : ℝ) := by
      have h1 : 2 * ((U : ℝ) * U) ≤ 2 * (n : ℝ) ^ ((4 : ℝ) / 5) := by linarith
      linarith [two_mul_rpow45_le hn32]
    exact_mod_cast hreal
  have hUVn : U * U ≤ n := by omega
  have hUUU : U ≤ U * U := Nat.le_mul_of_pos_right U (by omega)
  have hUn : U ≤ n := le_trans hUUU hUVn
  have h2U : 2 * U ≤ n := by omega
  have h2UQ : 2 * U ≤ Q := by omega
  have hn1 : 1 ≤ n := by omega
  -- fixed-outer form
  rw [vaughanTypeIBilinearSum_eq_fixed_outer]
  refine le_trans (norm_sum_le _ _) ?_
  -- restrict the outer sum to `d ≤ U`
  have hres := Finset.sum_filter_of_ne
    (s := Finset.Ioc 0 n) (p := fun d => d ≤ U)
    (f := fun d => ‖Vinogradov.vaughanTypeIBilinearCoeff U U d *
      ∑ f ∈ Finset.Ioc 0 (n / d),
        Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
          Vinogradov.addChar α (d * f)‖)
    (by
      intro d _ hne
      by_contra hcon
      push Not at hcon
      apply hne
      simp [vaughanTypeIBilinearCoeff_eq_zero_of_gt U U d hcon])
  rw [← hres]
  have hsubset : (Finset.Ioc 0 n).filter (fun d => d ≤ U) ⊆
      Finset.Icc 1 U := by
    intro d hd
    obtain ⟨hmem, hle⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd0, _⟩ := Finset.mem_Ioc.mp hmem
    exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun d _ _ => norm_nonneg _)) ?_
  -- split each summand into `log` and `ζ * Λ_{≤U}` pieces
  have hWsplit : ∀ d ∈ Finset.Icc 1 U,
      ‖Vinogradov.vaughanTypeIBilinearCoeff U U d *
        ∑ f ∈ Finset.Ioc 0 (n / d),
          Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
            Vinogradov.addChar α (d * f)‖ ≤
      ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)‖ +
        ‖∑ f ∈ Finset.Ioc 0 (n / d),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)‖ := by
    intro d _
    rw [norm_mul]
    have hsub : ∑ f ∈ Finset.Ioc 0 (n / d),
        Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
          Vinogradov.addChar α (d * f) =
        (∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)) -
        ∑ f ∈ Finset.Ioc 0 (n / d),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      unfold Vinogradov.vaughanTypeIBilinearInnerCoeff
        Vinogradov.vaughanTypeIInnerArithmetic
      rw [arithmeticFunction_sub_apply, ArithmeticFunction.log_apply,
        Complex.ofReal_sub, sub_mul]
    calc ‖Vinogradov.vaughanTypeIBilinearCoeff U U d‖ *
          ‖∑ f ∈ Finset.Ioc 0 (n / d),
            Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
              Vinogradov.addChar α (d * f)‖
        ≤ 1 * ‖∑ f ∈ Finset.Ioc 0 (n / d),
            Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
              Vinogradov.addChar α (d * f)‖ :=
          mul_le_mul_of_nonneg_right
            (norm_vaughanTypeIBilinearCoeff_le_one U U d) (norm_nonneg _)
      _ = ‖∑ f ∈ Finset.Ioc 0 (n / d),
            Vinogradov.vaughanTypeIBilinearInnerCoeff U f *
              Vinogradov.addChar α (d * f)‖ := one_mul _
      _ ≤ _ := by
          rw [hsub]
          exact norm_sub_le _ _
  refine le_trans (Finset.sum_le_sum hWsplit) ?_
  rw [Finset.sum_add_distrib]
  -- the `log` piece via Abel + the kernel master sum
  have hLpart : ∑ d ∈ Finset.Icc 1 U,
      ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
        Vinogradov.addChar α (d * f)‖ ≤
      2 * Real.log n * ((n : ℝ) / q * (1 + Real.log n) + ((U * U : ℕ) : ℝ) +
        4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q)) := by
    have hper : ∀ d ∈ Finset.Icc 1 U,
        ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)‖ ≤
        2 * Real.log n * typeIKernelBound n a q d := by
      intro d hd
      obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
      exact norm_logInner_le_kernel n a q U d Q α hq2 (by omega) hcop hdist
        h2UQ hd1 hdU
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hmaster := sum_typeIKernel_le n a q U hq2 hUn (by omega) hcop
    have hUcast : (U : ℝ) ≤ ((U * U : ℕ) : ℝ) := by exact_mod_cast hUUU
    have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by
      have : (0:ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
      linarith
    nlinarith
  -- the `ζ * Λ_{≤U}` piece via the hyperbola swap + the kernel master sum
  have hZpart : ∑ d ∈ Finset.Icc 1 U,
      ‖∑ f ∈ Finset.Ioc 0 (n / d),
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)‖ ≤
      Real.log n * ((n : ℝ) / q * (1 + Real.log n) + ((U * U : ℕ) : ℝ) +
        4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q)) := by
    refine le_trans (Finset.sum_le_sum fun d _ =>
      norm_zetaLambdaInner_le_sum U n d α) ?_
    rw [← Finset.sum_product']
    have hmaps : ∀ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U,
        p.1 * p.2 ∈ Finset.Icc 1 (U * U) := by
      rintro ⟨d, e⟩ hp
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      constructor
      · have := Nat.mul_le_mul hp.1.1 hp.2.1
        omega
      · exact Nat.mul_le_mul hp.1.2 hp.2.2
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => ArithmeticFunction.vonMangoldt p.2 *
        ‖∑ g ∈ Finset.Ioc 0 (n / (p.1 * p.2)),
          Vinogradov.addChar (α * ((p.1 * p.2 : ℕ) : ℝ)) g‖)]
    have hper_r : ∀ r ∈ Finset.Icc 1 (U * U),
        ∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
            (fun p => p.1 * p.2 = r),
          ArithmeticFunction.vonMangoldt p.2 *
            ‖∑ g ∈ Finset.Ioc 0 (n / (p.1 * p.2)),
              Vinogradov.addChar (α * ((p.1 * p.2 : ℕ) : ℝ)) g‖ ≤
        Real.log n * typeIKernelBound n a q r := by
      intro r hr
      obtain ⟨hr1, hrUV⟩ := Finset.mem_Icc.mp hr
      have hcongr : ∀ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
          (fun p => p.1 * p.2 = r),
          ArithmeticFunction.vonMangoldt p.2 *
            ‖∑ g ∈ Finset.Ioc 0 (n / (p.1 * p.2)),
              Vinogradov.addChar (α * ((p.1 * p.2 : ℕ) : ℝ)) g‖ =
          ArithmeticFunction.vonMangoldt p.2 *
            ‖∑ g ∈ Finset.Ioc 0 (n / r), Vinogradov.addChar (α * r) g‖ := by
        intro p hp
        obtain ⟨-, hpr⟩ := Finset.mem_filter.mp hp
        rw [hpr]
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
      have hG0 : (0 : ℝ) ≤ ‖∑ g ∈ Finset.Ioc 0 (n / r),
          Vinogradov.addChar (α * r) g‖ := norm_nonneg _
      have hGr : ‖∑ g ∈ Finset.Ioc 0 (n / r),
          Vinogradov.addChar (α * r) g‖ ≤ typeIKernelBound n a q r :=
        norm_addChar_partial_le_kernel n a q (U * U) r (n / r) Q α hq2
          (by omega) hcop hdist h2UVQ hr1 hrUV (le_refl _)
      have hw : ∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
          (fun p => p.1 * p.2 = r), ArithmeticFunction.vonMangoldt p.2 ≤
          Real.log n := by
        set S := (Finset.Icc 1 U ×ˢ Finset.Icc 1 U).filter
          (fun p => p.1 * p.2 = r) with hSdef
        have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) ↑S := by
          intro p₁ hp₁ p₂ hp₂ hcoord
          simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq,
            Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
          simp only at hcoord
          have he1 : 1 ≤ p₁.2 := hp₁.1.2.1
          have hmul : p₁.1 * p₁.2 = p₂.1 * p₂.2 := by rw [hp₁.2, hp₂.2]
          have h1 : p₁.1 = p₂.1 := by
            refine Nat.eq_of_mul_eq_mul_right (by omega : 0 < p₁.2) ?_
            rw [hmul, hcoord]
          exact Prod.ext h1 hcoord
        have himg := Finset.sum_image
          (f := fun e => ArithmeticFunction.vonMangoldt e) hinj
        refine le_trans (le_of_eq himg.symm) ?_
        have hsub : S.image (fun p : ℕ × ℕ => p.2) ⊆ r.divisors := by
          intro e he
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨-, hpr⟩ := Finset.mem_filter.mp hp
          exact Nat.mem_divisors.mpr ⟨Dvd.intro_left p.1 hpr, by omega⟩
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)) ?_
        rw [ArithmeticFunction.vonMangoldt_sum]
        have hrn : r ≤ n := le_trans hrUV hUVn
        exact Real.log_le_log (by exact_mod_cast hr1)
          (by exact_mod_cast hrn)
      exact mul_le_mul hw hGr hG0 hL0
    refine le_trans (Finset.sum_le_sum hper_r) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    exact sum_typeIKernel_le n a q (U * U) hq2 hUVn (by omega) hcop
  -- final numeric assembly
  set M2 := (n : ℝ) / q * (1 + Real.log n) + ((U * U : ℕ) : ℝ) +
    4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q) with hM2def
  have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by
    have : (0:ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
    linarith
  have hM2bound : M2 ≤ 10 * Real.log n *
      ((n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q) := by
    rw [hM2def]
    have hUU45 : ((U * U : ℕ) : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
      rw [Nat.cast_mul]
      exact hUn45
    have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hlogq : 1 + Real.log q ≤ 2 * Real.log n := by
      have h1 : Real.log q ≤ Real.log n :=
        Real.log_le_log hq0R (by exact_mod_cast hqn)
      linarith
    have hnq0 : (0 : ℝ) ≤ (n : ℝ) / q := by positivity
    have hr450 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h1 : (n : ℝ) / q * (1 + Real.log n) ≤
        (n : ℝ) / q * (2 * Real.log n) :=
      mul_le_mul_of_nonneg_left (by linarith) hnq0
    have h2 : ((U * U : ℕ) : ℝ) ≤ 2 * Real.log n * (n : ℝ) ^ ((4 : ℝ) / 5) := by
      calc ((U * U : ℕ) : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := hUU45
        _ = 1 * (n : ℝ) ^ ((4 : ℝ) / 5) := (one_mul _).symm
        _ ≤ 2 * Real.log n * (n : ℝ) ^ ((4 : ℝ) / 5) :=
            mul_le_mul_of_nonneg_right (by linarith) hr450
    have h3 : 4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q) ≤
        8 * Real.log n * ((n : ℝ) ^ ((4 : ℝ) / 5) + q) := by
      have ha : ((U * U : ℕ) : ℝ) + q ≤ (n : ℝ) ^ ((4 : ℝ) / 5) + q := by
        linarith
      calc 4 * (((U * U : ℕ) : ℝ) + q) * (1 + Real.log q)
          ≤ 4 * (((U * U : ℕ) : ℝ) + q) * (2 * Real.log n) :=
            mul_le_mul_of_nonneg_left hlogq (by positivity)
        _ ≤ 4 * ((n : ℝ) ^ ((4 : ℝ) / 5) + q) * (2 * Real.log n) := by
            have hc := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ) ≤ 4))
              (by linarith : (0:ℝ) ≤ 2 * Real.log n)
            linarith
        _ = 8 * Real.log n * ((n : ℝ) ^ ((4 : ℝ) / 5) + q) := by ring
    have hq0' : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith [mul_nonneg hL0 hnq0, mul_nonneg hL0 hr450,
      mul_nonneg hL0 hq0']
  -- envelope comparison
  have hsqpos : (0 : ℝ) < Real.sqrt q := by
    refine Real.sqrt_pos.mpr ?_
    exact_mod_cast (by omega : 0 < q)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hsqle : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
    have h1 : (q : ℝ) ≤ ((q : ℝ)) ^ 2 := by nlinarith
    calc Real.sqrt (q : ℝ) ≤ Real.sqrt (((q : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (q : ℝ) := Real.sqrt_sq (by positivity)
  have hdivle : (n : ℝ) / q ≤ (n : ℝ) / Real.sqrt q := by
    gcongr
  have hqsq : (q : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := cast_le_sqrt_mul q n hqn
  have hlog24 : (Real.log n) ^ 2 ≤ (Real.log n) ^ 4 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have henvX : (n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q ≤
      (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt ((q : ℝ) * n) := by linarith
  have henvX0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
      Real.sqrt ((q : ℝ) * n) := by positivity
  calc ∑ d ∈ Finset.Icc 1 U,
        ‖∑ f ∈ Finset.Ioc 0 (n / d), ((Real.log f : ℝ) : ℂ) *
          Vinogradov.addChar α (d * f)‖ +
      ∑ d ∈ Finset.Icc 1 U,
        ‖∑ f ∈ Finset.Ioc 0 (n / d),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              Vinogradov.vaughanLambdaLow U) f : ℝ) : ℂ) *
            Vinogradov.addChar α (d * f)‖
      ≤ 2 * Real.log n * M2 + Real.log n * M2 := by
        rw [hM2def]
        exact add_le_add hLpart hZpart
    _ = 3 * Real.log n * M2 := by ring
    _ ≤ 3 * Real.log n * (10 * Real.log n *
          ((n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q)) :=
        mul_le_mul_of_nonneg_left hM2bound (by linarith)
    _ = 30 * (Real.log n) ^ 2 *
          ((n : ℝ) / q + (n : ℝ) ^ ((4 : ℝ) / 5) + q) := by ring
    _ ≤ 30 * (Real.log n) ^ 2 *
          ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
            Real.sqrt ((q : ℝ) * n)) :=
        mul_le_mul_of_nonneg_left henvX (by positivity)
    _ ≤ 30 * (Real.log n) ^ 4 *
          ((n : ℝ) / Real.sqrt q + (n : ℝ) ^ ((4 : ℝ) / 5) +
            Real.sqrt ((q : ℝ) * n)) := by
        refine mul_le_mul_of_nonneg_right ?_ henvX0
        nlinarith
    _ ≤ 2000 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
        unfold hardCutoffVaughanTypeIIVinogradovEnvelope
        nlinarith [mul_nonneg henvX0 (pow_nonneg hL0 4)]

/-!
## P4 (corrected item-10): the annulus Schur target

`hardCutoffSchurPhaseCancellationAnnulusTargetParam U` asks for the
arbitrary-constant sharp-scale bound `‖Σ(Λ−log)e(mα)‖ ≤ KII·n/(log n)²`
on the two-sided Dirichlet annulus
`(log n)³/n < |q₀α − a₀| ≤ (U n)(log n)³/n` (reduced, `q₀ ≤ U n`).

**Dichotomy** (this section): take the Dirichlet approximant `x/y` of
`α` at level `Qlev := ⌊n/(log n)¹³⌋` (`Real.exists_rat_abs_sub_le_and_den_le`).

* If `x/y ≠ a₀/q₀`, the `1/(q₀y)` gap between distinct fractions plus the
  annulus *upper* edge force `y ≥ n/(2(U n)(log n)³) ≥ (log n)¹³`
  (using the cutoff growth bound `2(U n)(log n)¹⁶ ≤ n`), so `y` sits in
  the sweet range `(log n)¹³ ≤ y ≤ n/(log n)¹³` and the `Q`-window
  envelope theorems beat the sharp scale (`annulus_witness_margin`).
* If `x/y = a₀/q₀` and `q₀ ≥ (log n)¹³`, the envelope applies at the
  annulus center itself, with the level-`Qlev` window.
* If `x/y = a₀/q₀` and `q₀ < (log n)¹³`, then
  `|q₀α − a₀| ≤ 1/(Qlev+1) ≤ (log n)¹³/n`: `α` is in the genuine
  Siegel–Walfisz zone — polylog modulus, window shrunk past every
  fixed power of `log` over `n`.  This branch is the named obligation
  `hardCutoffSchurAnnulusSiegelWalfiszObligation` below; everything
  else is PROVED here.
-/

/-- `Q`-window variant of `norm_log_expSum_le_of_center`: a reduced witness
center `a/q` (`q ≥ 2`) with window `1/(qQ)` at ANY scale `Q ≥ 2` keeps `α`
at distance `≥ 1/(2q)` from every integer, so the pure-`log` sum obeys
`‖Σ_{m≤n} log m·e(mα)‖ ≤ 2q·log n`. -/
theorem norm_log_expSum_le_of_center_at (n a q Q : ℕ) (α : ℝ)
    (hq2 : 2 ≤ q) (hQ2 : 2 ≤ Q) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q)) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      2 * (q : ℝ) * Real.log n := by
  have hsep := center_round_separation Q a q α hq2 hQ2 hcop hdist
  have hδ : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
  have h := hardCutoffVaughanTypeILogDistanceSensitiveBound_separation
    (K := 1) (n := n) (α := α) (δ := 1 / (2 * (q : ℝ))) zero_le_one hδ hsep
    (hardCutoffVaughanTypeILogDistanceSensitiveBound_holds n α)
  refine h.trans (le_of_eq ?_)
  rw [one_mul, one_div, div_eq_mul_inv, inv_inv]
  ring

/-- **`Q`-window `Λ − log` envelope** (P4 master step): under a reduced
witness `a/q` (`2 ≤ q ≤ Q`) with window `1/(qQ)` at any intermediate scale
`max(4n^{3/5}, 2⌊n^{2/5}⌋²) ≤ Q ≤ n`, the full `Λ − log` exponential sum
obeys the classical envelope at `q`, with constant
`2304 = 2000 (Type I) + 300 (Type II) + 4 (Λ_{≤V} and log pieces)`. -/
theorem lambdaSubLog_envelope_at (n a q Q : ℕ) (α : ℝ)
    (hn32 : 32 ≤ n) (hq2 : 2 ≤ q) (hqQ : q ≤ Q) (hQn : Q ≤ n)
    (haq : a < q) (hcop : Nat.Coprime a q)
    (hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q))
    (hQ35 : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (Q : ℝ))
    (h2UVQ : 2 * (vaughanCutoff n * vaughanCutoff n) ≤ Q) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α‖ ≤
      2304 * hardCutoffVaughanTypeIIVinogradovEnvelope n q := by
  have hn3 : 3 ≤ n := by omega
  have hqn : q ≤ n := le_trans hqQ hQn
  set E := hardCutoffVaughanTypeIIVinogradovEnvelope n q with hE
  have hE0 : 0 ≤ E := envelope_nonneg n q
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog1 : 1 ≤ Real.log n := one_le_log_of_three_le n hn3
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hlog4 : Real.log n ≤ (Real.log n) ^ 4 := by
    calc Real.log (n : ℝ) = Real.log n * 1 := (mul_one _).symm
      _ ≤ Real.log n * (Real.log n) ^ 3 := by
          refine mul_le_mul_of_nonneg_left ?_ hlog0
          calc (1 : ℝ) = 1 ^ 3 := by norm_num
            _ ≤ (Real.log n) ^ 3 := pow_le_pow_left₀ zero_le_one hlog1 3
      _ = (Real.log n) ^ 4 := by ring
  have hEsqrt : Real.sqrt ((q : ℝ) * n) * (Real.log n) ^ 4 ≤ E := by
    rw [hE]
    unfold hardCutoffVaughanTypeIIVinogradovEnvelope
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog0 4)
    have h1 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    linarith
  have hE45 : (n : ℝ) ^ ((4 : ℝ) / 5) * (Real.log n) ^ 4 ≤ E := by
    rw [hE]
    unfold hardCutoffVaughanTypeIIVinogradovEnvelope
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog0 4)
    have h1 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt q := by positivity
    have h3 : (0 : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := Real.sqrt_nonneg _
    linarith
  set V := vaughanCutoff n with hV
  have hV1 : 1 ≤ V := one_le_vaughanCutoff n (by omega)
  have hdecomp := Vinogradov.vaughan_to_typeI_typeII_bilinear_full
    V V n hV1 hV1 α
  have hsub : Vinogradov.arithmeticExpSum
      (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α =
      Vinogradov.vonMangoldtExpSum α n -
        Vinogradov.arithmeticExpSum
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n α := by
    unfold Vinogradov.arithmeticExpSum Vinogradov.vonMangoldtExpSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [arithmeticFunction_sub_apply]
    push_cast
    ring
  rw [hsub, hdecomp]
  have hnorm : ‖(Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α +
        Vinogradov.vaughanTypeIBilinearSum V V n α +
        Vinogradov.vaughanTypeIIBilinearSum V V n α) -
        Vinogradov.arithmeticExpSum
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      ‖Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α‖ +
        ‖Vinogradov.vaughanTypeIBilinearSum V V n α‖ +
        ‖Vinogradov.vaughanTypeIIBilinearSum V V n α‖ +
        ‖Vinogradov.arithmeticExpSum
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_add_le
      (Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α +
        Vinogradov.vaughanTypeIBilinearSum V V n α)
      (Vinogradov.vaughanTypeIIBilinearSum V V n α)
    have h2 := norm_add_le
      (Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α)
      (Vinogradov.vaughanTypeIBilinearSum V V n α)
    linarith
  refine hnorm.trans ?_
  have hlow : ‖Vinogradov.arithmeticExpSum
      (Vinogradov.vaughanLambdaLow V) n α‖ ≤ E := by
    refine (norm_lambdaLow_expSum_le V n α hV1).trans ?_
    have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    have hVle : (V : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 5) := by
      refine (vaughanCutoff_le_rpow n).trans ?_
      exact Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    have hVn : (V : ℝ) ≤ (n : ℝ) := by
      refine (vaughanCutoff_le_rpow n).trans ?_
      calc (n : ℝ) ^ ((2 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have hVpos : (0 : ℝ) < V := by exact_mod_cast hV1
    have hlogV : Real.log (V : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hVpos hVn
    calc (V : ℝ) * Real.log V
        ≤ (n : ℝ) ^ ((4 : ℝ) / 5) * (Real.log n) ^ 4 :=
          mul_le_mul hVle (hlogV.trans hlog4)
            (Real.log_nonneg (by exact_mod_cast hV1))
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ E := hE45
  have hTI : ‖Vinogradov.vaughanTypeIBilinearSum V V n α‖ ≤ 2000 * E := by
    have h := vaughanTypeIPiece_envelope_at n a q Q α hn32 hq2 hqQ hQn hcop
      hdist h2UVQ
    rwa [← hV, ← hE] at h
  have hTII : ‖Vinogradov.vaughanTypeIIBilinearSum V V n α‖ ≤ 300 * E := by
    have h := vaughanTypeIIPiece_envelope_at n a q Q α (by omega) hq2 hqQ hQn
      haq hcop hdist hQ35
    rwa [← hV, ← hE] at h
  have hlogpart : ‖Vinogradov.arithmeticExpSum
      (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤ 2 * E := by
    refine (norm_log_expSum_le_of_center_at n a q Q α hq2 (by omega) hcop
      hdist).trans ?_
    have hq_sqrt : (q : ℝ) ≤ Real.sqrt ((q : ℝ) * n) := cast_le_sqrt_mul q n hqn
    have h1 : (q : ℝ) * Real.log n ≤ Real.sqrt ((q : ℝ) * n) * (Real.log n) ^ 4 :=
      mul_le_mul hq_sqrt hlog4 hlog0 (Real.sqrt_nonneg _)
    linarith
  calc ‖Vinogradov.arithmeticExpSum (Vinogradov.vaughanLambdaLow V) n α‖ +
        ‖Vinogradov.vaughanTypeIBilinearSum V V n α‖ +
        ‖Vinogradov.vaughanTypeIIBilinearSum V V n α‖ +
        ‖Vinogradov.arithmeticExpSum
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖
      ≤ E + 2000 * E + 300 * E + 2 * E := by linarith
    _ = 2303 * E := by ring
    _ ≤ 2304 * E := by linarith

end Helfgott
end MathExtras
