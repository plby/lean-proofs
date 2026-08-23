/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities

/-!
# Sharp rational Liouville and terminal-contour parameter budgets

The radical degree is `13^(oldRank+1)`, not an arbitrary square-root-sized
quantity.  The source seed `q <= k^epsilon` and
`epsilon = 1/(6(rank+1))` give the sharper bound `degree <= k^(1/6)`.
The same seed leaves enough separation between `k^(1/6)` and `sqrt k` for
the literal terminal Lemma-5 nodal count to absorb the rational Liouville
coefficient.
-/

noncomputable section

namespace Erdos240.VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-- The source seed leaves a factor `128` between the one-sixth and
one-half powers of `k`. -/
theorem oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half :
    (128 : ℝ) * P.k ^ (1 / 6 : ℝ) ≤ P.k ^ (1 / 2 : ℝ) := by
  have hseed : (128 : ℝ) ≤ P.k ^ P.epsilon := by
    have hkSeed : P.kSeedBase ≤ P.k ^ P.epsilon := by
      have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
        P.epsilon_pos.le
      rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
    calc
      (128 : ℝ) ≤ P.kSeedBase := by
        unfold kSeedBase
        have hrank : (2 : ℝ) ≤ P.rank + 1 := by
          exact_mod_cast Nat.succ_le_succ P.one_le_rank
        nlinarith
      _ ≤ P.k ^ P.epsilon := hkSeed
  have hepsilon : P.epsilon + 1 / 6 ≤ (1 / 2 : ℝ) := by
    have hepsilon' : P.epsilon ≤ (1 / 3 : ℝ) := by
      rw [P.epsilon_eq]
      have hrank : (1 : ℝ) ≤ P.rank + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
      apply (div_le_iff₀
        (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
      nlinarith
    nlinarith
  calc
    (128 : ℝ) * P.k ^ (1 / 6 : ℝ) ≤
        P.k ^ P.epsilon * P.k ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right hseed
        (Real.rpow_nonneg P.k_pos.le _)
    _ = P.k ^ (P.epsilon + 1 / 6) := by
      rw [Real.rpow_add P.k_pos]
    _ ≤ P.k ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsilon

/-- The exact radical-field degree is bounded by the one-sixth source
power, retaining the full rank dependence in `epsilon`. -/
theorem sourceRadicalDegree_le_k_rpow_one_sixth {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (13 ^ (oldRank + 1) : ℝ) ≤ P.k ^ (1 / 6 : ℝ) := by
  have hbase := P.q_le_k_rpow_epsilon
  have hpow : (P.q : ℝ) ^ P.rank ≤
      (P.k ^ P.epsilon) ^ P.rank :=
    pow_le_pow_left₀ (by positivity) hbase P.rank
  calc
    (13 ^ (oldRank + 1) : ℝ) = (P.q : ℝ) ^ P.rank := by
      norm_num [P.q_eq, VDPLParameters.rank]
    _ ≤ (P.k ^ P.epsilon) ^ P.rank := hpow
    _ = P.k ^ (P.epsilon * P.rank) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul P.k_pos.le]
    _ ≤ P.k ^ (1 / 6 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le P.one_le_k
      rw [P.epsilon_eq]
      have hr : (0 : ℝ) < P.rank + 1 := by positivity
      field_simp
      nlinarith

/-- Floor-sharp lower bound for the terminal Lemma-5 node count before
taking the logarithm of the inverse-two nodal factor. -/
theorem fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    (15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) := by
  let x : ℝ := P.levelScale J
  let A : ℝ := ((P.q ^ J : ℕ) : ℝ) * P.h
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let R : ℕ := P.lemmaFiveLocalRadius J
  let T : ℕ := P.lemmaFiveLocalMultiplicity J
  let S : ℕ := ⌊P.levelScale J / 6⌋₊
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hx : (512 : ℝ) < x := by
    simpa only [x] using P.fiveHundredTwelve_lt_levelScale_of_LevelOK hJ
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos
      (by exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) J)
      (by exact_mod_cast P.h_pos)
  have hu : (64 : ℝ) ≤ u := by
    simpa only [u] using P.sixtyFour_le_k_rpow_half
  have hSfloor : x / 6 - 1 < (S : ℝ) := by
    dsimp only [x, S]
    linarith [Nat.lt_floor_add_one (P.levelScale J / 6)]
  have hdivNat : S < 3 * (S / 3 + 1) := by omega
  have hdiv : (S : ℝ) / 3 < (T : ℝ) := by
    have hdivCast : (S : ℝ) < 3 * ((S / 3 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdivNat
    dsimp only [T, lemmaFiveLocalMultiplicity, S]
    push_cast at hdivCast ⊢
    linarith
  have hT : x / 19 < (T : ℝ) := by
    have hpre : (x / 6 - 1) / 3 < (T : ℝ) := by linarith
    nlinarith
  have hRfloor : 16 * A * u < (R : ℝ) + 1 := by
    dsimp only [R, lemmaFiveLocalRadius, A, u]
    simpa only [mul_assoc] using
      Nat.lt_floor_add_one
        (16 * ((P.q ^ J : ℕ) : ℝ) * P.h *
          P.k ^ (1 / 2 : ℝ))
  have hAu : 1 < A * u := by
    have hAone : (1 : ℝ) ≤ A := by
      dsimp only [A]
      exact one_le_mul_of_one_le_of_one_le
        (by exact_mod_cast one_le_pow₀ (show 1 ≤ P.q from P.one_lt_q.le))
        (by exact_mod_cast P.h_pos)
    have h64 : (64 : ℝ) ≤ A * u := by
      have := mul_le_mul hAone hu (by norm_num : (0 : ℝ) ≤ 64)
        (by positivity : (0 : ℝ) ≤ A)
      norm_num at this ⊢
      exact this
    nlinarith
  have hR : 15 * A * u < (R : ℝ) := by nlinarith
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < (T : ℝ) := (div_pos hxpos (by norm_num)).trans hT
  have hRpos : 0 < (R : ℝ) := by nlinarith
  have hprod : (15 * A * u) * (x / 19) < (R : ℝ) * T := by
    calc
      (15 * A * u) * (x / 19) < (R : ℝ) * (x / 19) :=
        mul_lt_mul_of_pos_right hR (div_pos hxpos (by norm_num))
      _ < (R : ℝ) * T := mul_lt_mul_of_pos_left hT hRpos
  have hsource : A * x = H := by
    calc
      A * x = P.levelScale J * ((P.q ^ J : ℕ) : ℝ) * P.h := by
        dsimp only [A, x]
        ring
      _ = H := by rw [P.levelScale_mul_qpow_mul_h J]
  change (15 / 19 : ℝ) * u * H < ((R * T : ℕ) : ℝ)
  rw [Nat.cast_mul, ← hsource]
  nlinarith

/-- The literal terminal nodal count dominates the sharp rational
Liouville coefficient `34*k^(1/6)` with eight further height units. -/
theorem eight_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    (8 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let n : ℕ := P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J
  have hv : (1 : ℝ) ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow P.one_le_k (by norm_num)
  have huv : 128 * v ≤ u := by
    simpa only [u, v] using
      P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
  have hcoeff : 8 + 34 * v < (15 / 19 : ℝ) * u * Real.log 2 := by
    have hbase : (42 : ℝ) < (15 / 19 : ℝ) * 128 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hfortyTwo : 8 + 34 * v ≤ 42 * v := by nlinarith
    have hvscaled : 42 * v <
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v :=
      mul_lt_mul_of_pos_right hbase (lt_of_lt_of_le (by norm_num) hv)
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have huScaled :
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v ≤
          (15 / 19 : ℝ) * u * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left huv hlog0]
    exact hfortyTwo.trans_lt (hvscaled.trans_le huScaled)
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hcount :=
    P.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count hJ
  have hfirst := mul_lt_mul_of_pos_right hcoeff hHpos
  dsimp only [u, v, H, n] at hcount hfirst ⊢
  calc
    (8 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        Real.log 2) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := hfirst
    _ = ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) *
          Real.log 2 := by ring
    _ < ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 :=
      mul_lt_mul_of_pos_right hcount (Real.log_pos (by norm_num))

/-- A slightly stronger reserve than the preceding public endpoint.  The
extra two height units are what let the final rational contour be strictly
smaller than the Liouville threshold, rather than merely smaller than its
non-strict upper exponent. -/
theorem ten_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    (10 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hv : (1 : ℝ) ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow P.one_le_k (by norm_num)
  have huv : 128 * v ≤ u := by
    simpa only [u, v] using
      P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
  have hcoeff : 10 + 34 * v < (15 / 19 : ℝ) * u * Real.log 2 := by
    have hbase : (44 : ℝ) < (15 / 19 : ℝ) * 128 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hfortyFour : 10 + 34 * v ≤ 44 * v := by nlinarith
    have hvscaled : 44 * v <
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v :=
      mul_lt_mul_of_pos_right hbase (lt_of_lt_of_le (by norm_num) hv)
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have huScaled :
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v ≤
          (15 / 19 : ℝ) * u * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left huv hlog0]
    exact hfortyFour.trans_lt (hvscaled.trans_le huScaled)
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hcount :=
    P.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count hJ
  have hfirst := mul_lt_mul_of_pos_right hcoeff hHpos
  dsimp only [u, v, H] at hcount hfirst ⊢
  calc
    (10 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) * Real.log 2) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := hfirst
    _ = ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) *
          Real.log 2 := by ring
    _ < ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 :=
      mul_lt_mul_of_pos_right hcount (Real.log_pos (by norm_num))

/-- Degree-indexed form of the floor-sharp terminal count.  This is the
literal numerical inequality consumed by the rational Liouville closure. -/
theorem nine_add_thirtyFour_mul_sourceRadicalDegree_mul_sourceHeight_lt_count_log_two
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J) :
    (9 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let d : ℝ := (13 ^ (oldRank + 1) : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hdv : d ≤ v := by
    simpa only [d, v] using P.sourceRadicalDegree_le_k_rpow_one_sixth
  have hcoef : 9 + 34 * d < 10 + 34 * v := by nlinarith
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hscaled := mul_lt_mul_of_pos_right hcoef hHpos
  have hcount :=
    P.ten_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two hJ
  simpa only [d, v, H] using hscaled.trans hcount

/-- The exact outer estimate against the sharp degree-dependent rational
Liouville exponent. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    {outer : ℝ} (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((34 * (13 ^ (oldRank + 1) : ℝ) + 6) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  have hcount :=
    P.nine_add_thirtyFour_mul_sourceRadicalDegree_mul_sourceHeight_lt_count_log_two hJ
  have hH := P.one_le_sourceHeightUnit
  nlinarith

/-- Ready-to-use terminal outer-contour estimate on the sharp rational
Liouville scale. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sharpRationalScale
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) {outer : ℝ}
    (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((5 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  have hcount :=
    P.eight_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two hJ
  have hH := P.one_le_sourceHeightUnit
  have hv : (1 : ℝ) ≤ P.k ^ (1 / 6 : ℝ) :=
    Real.one_le_rpow P.one_le_k (by norm_num)
  nlinarith

/-- Two-unit-slack version of the sharp rational outer estimate.  The
extra reserve is what permits the local and outer terms to be added before
comparison with the exact rational Liouville threshold. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sharpRationalScale_add_two
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) {outer : ℝ}
    (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((7 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  have hcount :=
    P.ten_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two hJ
  have hH := P.one_le_sourceHeightUnit
  nlinarith

/-- `k^(1/6)`-indexed count reserve for the source-faithful `18 H`
terminal-circle growth. -/
theorem twentyFive_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    (25 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hv : (1 : ℝ) ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow P.one_le_k (by norm_num)
  have huv : 128 * v ≤ u := by
    simpa only [u, v] using
      P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
  have hcoeff : 25 + 34 * v < (15 / 19 : ℝ) * u * Real.log 2 := by
    have hbase : (59 : ℝ) < (15 / 19 : ℝ) * 128 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hle : 25 + 34 * v ≤ 59 * v := by nlinarith
    have hvscaled : 59 * v <
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v :=
      mul_lt_mul_of_pos_right hbase (lt_of_lt_of_le (by norm_num) hv)
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have huScaled :
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v ≤
          (15 / 19 : ℝ) * u * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left huv hlog0]
    exact hle.trans_lt (hvscaled.trans_le huScaled)
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hcount :=
    P.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count hJ
  have hfirst := mul_lt_mul_of_pos_right hcoeff hHpos
  dsimp only [u, v, H] at hcount hfirst ⊢
  calc
    (25 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) * Real.log 2) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := hfirst
    _ = ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) *
          Real.log 2 := by ring
    _ < ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 :=
      mul_lt_mul_of_pos_right hcount (Real.log_pos (by norm_num))

/-- Source-faithful `k^(1/6)`-indexed terminal outer estimate. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sharpRationalScale_of_growth_eighteen
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) {outer : ℝ}
    (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (18 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((6 + 34 * P.k ^ (1 / 6 : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  have hcount :=
    P.twentyFive_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two hJ
  have hH := P.one_le_sourceHeightUnit
  nlinarith

/-- The literal terminal node count has enough room to pay both the exact
radical degree in the rational Liouville bound and the source-faithful
`18 H` outer-circle growth. -/
theorem twentyFive_add_thirtyFour_mul_sourceRadicalDegree_mul_sourceHeight_lt_count_log_two
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J) :
    (25 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let d : ℝ := (13 ^ (oldRank + 1) : ℝ)
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hdv : d ≤ v := by
    simpa only [d, v] using P.sourceRadicalDegree_le_k_rpow_one_sixth
  have hv : (1 : ℝ) ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow P.one_le_k (by norm_num)
  have huv : 128 * v ≤ u := by
    simpa only [u, v] using
      P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
  have hcoeff : 25 + 34 * d < (15 / 19 : ℝ) * u * Real.log 2 := by
    have hbase : (59 : ℝ) < (15 / 19 : ℝ) * 128 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hle : 25 + 34 * d ≤ 59 * v := by nlinarith
    have hvscaled : 59 * v <
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v :=
      mul_lt_mul_of_pos_right hbase (lt_of_lt_of_le (by norm_num) hv)
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have huScaled :
        ((15 / 19 : ℝ) * 128 * Real.log 2) * v ≤
          (15 / 19 : ℝ) * u * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left huv hlog0]
    exact hle.trans_lt (hvscaled.trans_le huScaled)
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hcount :=
    P.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count hJ
  have hfirst := mul_lt_mul_of_pos_right hcoeff hHpos
  dsimp only [d, u, v, H] at hcount hfirst ⊢
  calc
    (25 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) * Real.log 2) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := hfirst
    _ = ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) *
          Real.log 2 := by ring
    _ < ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 :=
      mul_lt_mul_of_pos_right hcount (Real.log_pos (by norm_num))

/-- Source-faithful terminal outer-contour estimate.  It absorbs the actual
`18 H` boundary growth and retains one full height unit beyond the exact
rational Liouville exponent `(5 + 34 d) H`. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_growth_eighteen
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    {outer : ℝ} (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (18 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  have hcount :=
    P.twentyFive_add_thirtyFour_mul_sourceRadicalDegree_mul_sourceHeight_lt_count_log_two hJ
  have hH := P.one_le_sourceHeightUnit
  nlinarith

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
#print axioms Erdos240.VDPLParameters.sourceRadicalDegree_le_k_rpow_one_sixth
#print axioms Erdos240.VDPLParameters.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count
#print axioms Erdos240.VDPLParameters.eight_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sharpRationalScale
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sharpRationalScale_add_two
#print axioms Erdos240.VDPLParameters.twentyFive_add_thirtyFour_mul_k_rpow_one_sixth_mul_sourceHeight_lt_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sharpRationalScale_of_growth_eighteen
#print axioms Erdos240.VDPLParameters.nine_add_thirtyFour_mul_sourceRadicalDegree_mul_sourceHeight_lt_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale
#print axioms Erdos240.VDPLParameters.twentyFive_add_thirtyFour_mul_sourceRadicalDegree_mul_sourceHeight_lt_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_growth_eighteen
