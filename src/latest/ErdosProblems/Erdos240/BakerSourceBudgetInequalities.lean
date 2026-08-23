/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerAdmissibleParameters
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Positivity

/-!
# Numerical budget inequalities for the source extrapolation steps

This file collects the floor arithmetic and elementary exponential
comparisons used by source Lemmas 4--6.  In particular, the strict slack in
the second interpolation on p. 52 is proved from the actual parameter ledger:
with `q = 13`, the next full budget occupies strictly less than three quarters
of the preceding `/9` budget.

No analytic or vanishing assertion occurs in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-! ## Floor losses in the derivative budgets -/

/-- The baseline admissibility ledger gives a scale larger than `512` at
every admissible level, even in the smallest possible rank. -/
theorem fiveHundredTwelve_lt_levelScale_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    (512 : ℝ) < P.levelScale J := by
  have hlarge := P.fiveHundredTwelve_mul_rank_add_one_lt_levelScale hJ
  have hrankNat : 1 ≤ P.rank + 1 := Nat.succ_le_succ (Nat.zero_le P.rank)
  have hrank : (1 : ℝ) ≤ P.rank + 1 := by exact_mod_cast hrankNat
  nlinarith

/-- Every admissible level has scale strictly larger than `117`.  This is
the exact threshold needed to absorb the two floor losses in the comparison
`4 floor(x/13) < 3 floor(x/9)`. -/
theorem oneHundredSeventeen_lt_levelScale_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    (117 : ℝ) < P.levelScale J := by
  exact (by norm_num : (117 : ℝ) < 512).trans
    (P.fiveHundredTwelve_lt_levelScale_of_LevelOK hJ)

/-- The literal strict three-quarter slack used on p. 52.  The left side is
the successor full derivative budget; the right side is the current `/9`
budget produced by Lemma 5. -/
theorem four_mul_Slevel_succ_lt_three_mul_Sstep_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    4 * P.Slevel (J + 1) < 3 * P.Sstep J := by
  have hscale : (117 : ℝ) < P.levelScale J :=
    P.oneHundredSeventeen_lt_levelScale_of_LevelOK hJ
  have hnext : (P.Slevel (J + 1) : ℝ) ≤ P.levelScale J / 13 := by
    calc
      (P.Slevel (J + 1) : ℝ) ≤ P.levelScale (J + 1) :=
        P.Slevel_cast_le (J + 1)
      _ = P.levelScale J / 13 := by simp [P.levelScale_succ, q]
  have hstep : P.levelScale J / 9 < (P.Sstep J : ℝ) + 1 :=
    P.levelScale_div_nine_lt_Sstep_add_one J
  have hreal : (4 : ℝ) * P.Slevel (J + 1) < 3 * P.Sstep J := by
    nlinarith
  exact_mod_cast hreal

/-- A successor-admissible version, convenient in the induction where the
new state is already indexed by `J+1`. -/
theorem four_mul_Slevel_succ_lt_three_mul_Sstep_of_LevelOK_succ [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK (J + 1)) :
    4 * P.Slevel (J + 1) < 3 * P.Sstep J := by
  exact P.four_mul_Slevel_succ_lt_three_mul_Sstep_of_LevelOK
    (VDPLParameters.LevelOK.mono P hJ (Nat.le_succ J))

/-- The successor budget therefore fits in the integral part of `3S/4`. -/
theorem Slevel_succ_le_three_mul_Sstep_div_four_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    P.Slevel (J + 1) ≤ 3 * P.Sstep J / 4 := by
  have h := P.four_mul_Slevel_succ_lt_three_mul_Sstep_of_LevelOK hJ
  omega

/-- Splitting an integral budget into the source's `3/4` base part and
`1/4` extra-derivative part never exceeds the original budget. -/
theorem three_mul_div_four_add_div_four_le (S : ℕ) :
    3 * S / 4 + S / 4 ≤ S := by
  omega

/-- Exact additive budget needed by the coprime-node Hermite repair: a base
multi-index of successor size plus an extra derivative of order at most
`floor(S/4)` still lies in the available `S = Sstep J` box. -/
theorem Slevel_succ_add_Sstep_div_four_le_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    P.Slevel (J + 1) + P.Sstep J / 4 ≤ P.Sstep J := by
  exact (Nat.add_le_add_right
      (P.Slevel_succ_le_three_mul_Sstep_div_four_of_LevelOK hJ)
      (P.Sstep J / 4)).trans
    (three_mul_div_four_add_div_four_le (P.Sstep J))

/-- The same p. 52 additive slack from admissibility of the successor. -/
theorem Slevel_succ_add_Sstep_div_four_le_of_LevelOK_succ [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK (J + 1)) :
    P.Slevel (J + 1) + P.Sstep J / 4 ≤ P.Sstep J := by
  exact P.Slevel_succ_add_Sstep_div_four_le_of_LevelOK
    (VDPLParameters.LevelOK.mono P hJ (Nat.le_succ J))

/-- Admissibility leaves a nontrivial `/9` budget.  The stronger lower bound
is useful for all endpoint `Fin` types occurring in the p. 52 repair. -/
theorem thirteen_le_Sstep_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) : 13 ≤ P.Sstep J := by
  unfold Sstep
  apply Nat.le_floor
  have hscale := P.oneHundredSeventeen_lt_levelScale_of_LevelOK hJ
  nlinarith

theorem Sstep_div_four_pos_of_LevelOK [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) : 0 < P.Sstep J / 4 := by
  have := P.thirteen_le_Sstep_of_LevelOK hJ
  omega

/-- The direct Lemma-4 jet multiplicity is nonzero. -/
theorem Slevel_sub_Sstep_add_one_pos [Nonempty ι] (J : ℕ) :
    0 < P.Slevel J - P.Sstep J + 1 := by omega

/-- A base derivative in the `/9` box and an extra head derivative below
`Slevel-Sstep+1` still fit in the original full derivative box.  This is the
floor-exact bookkeeping behind equations (7)--(8). -/
theorem add_lt_Slevel_sub_Sstep_add_one_le_Slevel [Nonempty ι]
    {J base extra : ℕ} (hbase : base ≤ P.Sstep J)
    (hextra : extra < P.Slevel J - P.Sstep J + 1) :
    base + extra ≤ P.Slevel J := by
  have hstep := P.Sstep_le_Slevel J
  omega

/-- Quantitative lower bound after the `/9` floor loss. -/
theorem eight_mul_levelScale_sub_nine_lt_nine_mul_Slevel_sub_Sstep
    [Nonempty ι] (J : ℕ) :
    8 * P.levelScale J - 9 <
      9 * ((P.Slevel J - P.Sstep J : ℕ) : ℝ) := by
  have hfull : P.levelScale J < P.Slevel J + 1 :=
    P.levelScale_lt_Slevel_add_one J
  have hstep : (P.Sstep J : ℝ) ≤ P.levelScale J / 9 :=
    P.Sstep_cast_le J
  have hle := P.Sstep_le_Slevel J
  rw [Nat.cast_sub hle]
  nlinarith

/-! ## The exact one-third split in source Lemma 5 -/

/-- Pure floor arithmetic for Lemma 5.  If `A=floor x`, then the source
budgets are `A/6` and `A/9`; the extra derivative allowance `(A/6)/3`
fits alongside the base `A/9` budget without any asymptotic error. -/
theorem floor_div_nine_add_floor_div_six_div_three_le_floor_div_six
    {x : ℝ} :
    ⌊x / 9⌋₊ + ⌊x / 6⌋₊ / 3 ≤ ⌊x / 6⌋₊ := by
  rw [Nat.floor_div_ofNat, Nat.floor_div_ofNat]
  omega

/-- Parameter-shaped form of the Lemma-5 derivative split. -/
theorem Sstep_add_levelScale_div_six_floor_div_three_le [Nonempty ι]
    (J : ℕ) :
    P.Sstep J + ⌊P.levelScale J / 6⌋₊ / 3 ≤
      ⌊P.levelScale J / 6⌋₊ := by
  unfold Sstep
  exact floor_div_nine_add_floor_div_six_div_three_le_floor_div_six

/-- Consequently, every extra derivative order represented by
`Fin (floor(floor(levelScale/6)/3)+1)` fits together with a `/9`-budget
base multi-index in the terminal Lemma-4 `/6` box. -/
theorem add_lt_levelScale_div_six_floor_div_three_add_one_le
    [Nonempty ι] {J base extra : ℕ}
    (hbase : base ≤ P.Sstep J)
    (hextra : extra < ⌊P.levelScale J / 6⌋₊ / 3 + 1) :
    base + extra ≤ ⌊P.levelScale J / 6⌋₊ := by
  have hsplit := P.Sstep_add_levelScale_div_six_floor_div_three_le J
  omega

/-! ## Remaining displayed source parameter inequalities -/

/-- The lower half of the Lemma-5 auxiliary-prime requirement. -/
theorem seven_le_q : 7 ≤ P.q := by simp [q]

/-- The upper half of the Lemma-5 auxiliary-prime requirement
`q ≤ k^(mu/(2(rank+1)))` follows from the stronger baseline constraint
`q ≤ k^epsilon`. -/
theorem q_le_k_rpow_mu_div_two_rank_add_one :
    (P.q : ℝ) ≤ P.k ^ (P.mu / (2 * (P.rank + 1 : ℝ))) := by
  have hexponent : P.epsilon ≤
      P.mu / (2 * (P.rank + 1 : ℝ)) := by
    rw [P.epsilon_eq, P.mu_eq]
    have hrank : (0 : ℝ) < P.rank + 1 := by positivity
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  exact P.q_le_k_rpow_epsilon.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_le_k hexponent)

/-- The baseline seed makes the square-root scale very large.  This is the
numerical reserve used to absorb all local-circle powers in source Lemma 5. -/
theorem sixtyFour_le_k_rpow_half :
    (64 : ℝ) ≤ P.k ^ (1 / 2 : ℝ) := by
  have hseed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have hepsilon : P.epsilon ≤ (1 / 2 : ℝ) := by
    rw [P.epsilon_eq]
    have hrank : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    apply (div_le_div_iff₀ (by positivity)
      (by positivity : (0 : ℝ) < 2)).2
    nlinarith
  have hhalf : P.k ^ P.epsilon ≤ P.k ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsilon
  calc
    (64 : ℝ) ≤ P.kSeedBase := by
      unfold kSeedBase
      have hrank : (1 : ℝ) ≤ P.rank + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
      nlinarith
    _ ≤ P.k ^ P.epsilon := hseed
    _ ≤ P.k ^ (1 / 2 : ℝ) := hhalf

/-- Since the source rank is nonzero, the preceding square-root reserve is
in fact at least `128`.  This sharper integer is used by the explicit
Hermite-basis version of the Lemma-5 local factor. -/
theorem oneTwentyEight_le_k_rpow_half :
    (128 : ℝ) ≤ P.k ^ (1 / 2 : ℝ) := by
  have hseed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have hepsilon : P.epsilon ≤ (1 / 2 : ℝ) := by
    rw [P.epsilon_eq]
    have hrank : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    apply (div_le_div_iff₀ (by positivity)
      (by positivity : (0 : ℝ) < 2)).2
    nlinarith
  have hhalf : P.k ^ P.epsilon ≤ P.k ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsilon
  calc
    (128 : ℝ) ≤ P.kSeedBase := by
      unfold kSeedBase
      have hrank : (2 : ℝ) ≤ P.rank + 1 := by
        exact_mod_cast Nat.succ_le_succ P.one_le_rank
      nlinarith
    _ ≤ P.k ^ P.epsilon := hseed
    _ ≤ P.k ^ (1 / 2 : ℝ) := hhalf

/-- The baseline seed already implies the local-circle requirement
`(16/3)(1+mu)(rank+1) < k` recorded in source Lemma 4. -/
theorem sixteen_div_three_mul_one_add_mu_mul_rank_add_one_lt_k :
    (16 / 3 : ℝ) * (1 + P.mu) * (P.rank + 1) < P.k := by
  have hbaseSeed : P.kSeedBase ≤ P.kSeed := by
    unfold kSeed
    exact le_self_pow₀ P.one_le_kSeedBase P.kExponent_pos.ne'
  have hrank : (0 : ℝ) < P.rank + 1 := by positivity
  calc
    (16 / 3 : ℝ) * (1 + P.mu) * (P.rank + 1) <
        64 * (P.rank + 1) := by rw [P.mu_eq]; nlinarith
    _ = P.kSeedBase := rfl
    _ ≤ P.kSeed := hbaseSeed
    _ < P.k := P.kSeed_lt_k

/-- The second additional p. 39 inequality is already stronger at the
baseline: `6 < q = 13 ≤ k^epsilon`. -/
theorem six_lt_k_rpow_epsilon : (6 : ℝ) < P.k ^ P.epsilon := by
  calc
    (6 : ℝ) < P.q := by norm_num [q]
    _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon

/-- Extract the root form of the first p. 39 ledger requirement. -/
theorem eightyOne_lt_k_rpow_inv_rank_add_one
    (hreq : P.sourceDimensionThreshold ∈ P.kRequirements) :
    (81 : ℝ) < P.k ^ (1 / (P.rank + 1 : ℝ)) := by
  let e : ℝ := P.rank + 1
  have he : 0 < e := by dsimp [e]; positivity
  have hbase : 0 < (81 : ℝ) := by norm_num
  have hraw : P.sourceDimensionThreshold < P.k := P.requirement_lt_k hreq
  have hrpow := Real.rpow_lt_rpow
    (Real.rpow_nonneg hbase.le e) hraw (one_div_pos.mpr he)
  have hroot : ((81 : ℝ) ^ e) ^ (1 / e) = 81 := by
    rw [← Real.rpow_mul hbase.le]
    rw [mul_one_div_cancel he.ne', Real.rpow_one]
  unfold sourceDimensionThreshold at hraw
  change ((81 : ℝ) ^ e) < P.k at hraw
  rw [hroot] at hrpow
  simpa only [e] using hrpow

/-- Canonical admissibility supplies the first root inequality without an
endpoint membership hypothesis. -/
theorem withSourceRequirements_eightyOne_lt_k_rpow
    (extra : Finset ℝ) :
    (81 : ℝ) < (P.withSourceRequirements extra).k ^
      (1 / ((P.withSourceRequirements extra).rank + 1 : ℝ)) := by
  exact eightyOne_lt_k_rpow_inv_rank_add_one
    (P := P.withSourceRequirements extra)
    (P.sourceDimensionThreshold_mem_withSourceRequirements extra)

/-- Extract the root form of the third p. 39 ledger requirement. -/
theorem ten_div_epsilon_lt_k_rpow_inv_source_exponent
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    10 / P.epsilon <
      P.k ^ (1 / ((1 + P.mu) * (P.rank + 1 : ℝ))) := by
  let e : ℝ := (1 + P.mu) * (P.rank + 1 : ℝ)
  have he : 0 < e := by dsimp [e]; positivity
  have hbase : 0 < (10 : ℝ) / P.epsilon :=
    div_pos (by norm_num) P.epsilon_pos
  have hraw : P.sourceTenThreshold < P.k := P.requirement_lt_k hreq
  have hrpow := Real.rpow_lt_rpow
    (Real.rpow_nonneg hbase.le e) hraw (one_div_pos.mpr he)
  have hroot :
      ((10 / P.epsilon : ℝ) ^ e) ^ (1 / e) = 10 / P.epsilon := by
    rw [← Real.rpow_mul hbase.le]
    have he0 : e ≠ 0 := he.ne'
    rw [mul_one_div_cancel he0, Real.rpow_one]
  unfold sourceTenThreshold at hraw
  change ((10 / P.epsilon : ℝ) ^ e) < P.k at hraw
  rw [hroot] at hrpow
  simpa only [e] using hrpow

/-- For a parameter obtained from the canonical admissibility constructor,
the preceding root inequality is unconditional. -/
theorem withSourceRequirements_ten_div_epsilon_lt_k_rpow
    (extra : Finset ℝ) :
    10 / (P.withSourceRequirements extra).epsilon <
      (P.withSourceRequirements extra).k ^
        (1 / ((1 + (P.withSourceRequirements extra).mu) *
          ((P.withSourceRequirements extra).rank + 1 : ℝ))) := by
  exact ten_div_epsilon_lt_k_rpow_inv_source_exponent
    (P := P.withSourceRequirements extra)
    (P.sourceTenThreshold_mem_withSourceRequirements extra)

/-! ## Source radii and complete residue blocks -/

/-- Literal terminal integral radius used by source Lemma 5.  This duplicate
parameter-level name avoids an import cycle with the concrete interpolation
module, whose `sourceRationalNodeRadius` is proved equal to it. -/
def lemmaFiveLocalRadius (J : ℕ) : ℕ :=
  ⌊16 * ((P.q ^ J : ℕ) : ℝ) * P.h * P.k ^ (1 / 2 : ℝ)⌋₊

/-- Literal repeated-node multiplicity `floor(floor(levelScale/6)/3)+1`
from source Lemma 5. -/
def lemmaFiveLocalMultiplicity (J : ℕ) : ℕ :=
  ⌊P.levelScale J / 6⌋₊ / 3 + 1

/-- Every successor source radius is a union of complete `q`-residue
blocks.  This is the divisibility input in the exact coprime-node count. -/
theorem q_dvd_R_succ (J : ℕ) : P.q ∣ P.R (J + 1) := by
  rw [P.R_succ]
  exact dvd_mul_right _ _

/-- Cancelling the inverse `q^J` in the level scale recovers the common
source exponent without any floor loss. -/
theorem levelScale_mul_qpow_mul_h [Nonempty ι] (J : ℕ) :
    P.levelScale J * ((P.q ^ J : ℕ) : ℝ) * P.h =
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
  have hqpow : (((P.q ^ J : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero J (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)))
  unfold levelScale qInvPow
  field_simp

/-- The nested source floor is exactly a single `/36` floor. -/
theorem Sstep_div_four_eq_floor_levelScale_div_thirtySix (J : ℕ) :
    P.Sstep J / 4 = ⌊P.levelScale J / 36⌋₊ := by
  unfold Sstep
  rw [Nat.floor_div_ofNat, Nat.floor_div_ofNat,
    Nat.div_div_eq_div_mul]

/-- Exact number of coprime nodes in the successor radius for `q=13`. -/
theorem successor_coprime_node_count_eq (J : ℕ) :
    P.R (J + 1) * (P.q - 1) / P.q = 192 * P.q ^ J * P.h := by
  simp only [R, q, pow_succ]
  rw [show 16 * (13 ^ J * 13) * P.h * (13 - 1) =
      13 * (192 * 13 ^ J * P.h) by norm_num; ring]
  rw [Nat.mul_comm 13 (192 * 13 ^ J * P.h)]
  exact Nat.mul_div_left _ (by decide)

/-- The literal p. 52 coprime nodal factor supplies more than three complete
source exponents.  Floors are absorbed using the already proved admissible
scale bound `117 < levelScale J`; no new lower bound on `k` is required. -/
theorem three_mul_sourceExponent_lt_coprime_decayExponent [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    3 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4) : ℕ) *
        Real.log 3 := by
  let x : ℝ := P.levelScale J
  let A : ℝ := ((P.q ^ J : ℕ) : ℝ) * P.h
  let T : ℝ := ((P.Sstep J / 4 : ℕ) : ℝ)
  have hx : (117 : ℝ) < x := by
    exact P.oneHundredSeventeen_lt_levelScale_of_LevelOK hJ
  have hA : 0 < A := by
    dsimp only [A]
    have hqpow : 0 < P.q ^ J := pow_pos (by simp [q]) J
    exact mul_pos (by exact_mod_cast hqpow) (by exact_mod_cast P.h_pos)
  have hTfloor : x / 36 < T + 1 := by
    dsimp only [x, T]
    rw [P.Sstep_div_four_eq_floor_levelScale_div_thirtySix]
    exact Nat.lt_floor_add_one _
  have hsource :
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld = A * x := by
    dsimp only [A, x]
    rw [← P.levelScale_mul_qpow_mul_h J]
    ring_nf
  have hlargeA : 117 * A < A * x := by
    nlinarith [mul_lt_mul_of_pos_left hx hA]
  have hdecay : 3 * (A * x) < (192 * A) * T := by
    have hTmul : (192 * A) * (x / 36 - 1) < (192 * A) * T := by
      apply mul_lt_mul_of_pos_left
      · linarith
      · positivity
    nlinarith
  have hcount :
      (((P.R (J + 1) * (P.q - 1) / P.q) *
          (P.Sstep J / 4) : ℕ) : ℝ) = (192 * A) * T := by
    rw [P.successor_coprime_node_count_eq J]
    dsimp only [A, T]
    push_cast
    ring
  have hlog : (1 : ℝ) < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  rw [hsource, hcount]
  exact hdecay.trans_le (by
    have hnonneg : 0 ≤ (192 * A) * T := by positivity
    nlinarith)

/-- A sharper form of the p. 52 comparison.  The full baseline scale
`512 < levelScale J`, together with the certified decimal lower bound for
`log 3`, leaves five complete source exponents after the `/36` floor loss.
This is the useful form when two growth exponents must be paid before the
final `exp (-3E)` conclusion. -/
theorem five_mul_sourceExponent_lt_coprime_decayExponent [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4) : ℕ) *
        Real.log 3 := by
  let x : ℝ := P.levelScale J
  let A : ℝ := ((P.q ^ J : ℕ) : ℝ) * P.h
  let T : ℝ := ((P.Sstep J / 4 : ℕ) : ℝ)
  have hx : (512 : ℝ) < x := by
    exact P.fiveHundredTwelve_lt_levelScale_of_LevelOK hJ
  have hA : 0 < A := by
    dsimp only [A]
    have hqpow : 0 < P.q ^ J := pow_pos (by simp [q]) J
    exact mul_pos (by exact_mod_cast hqpow) (by exact_mod_cast P.h_pos)
  have hTfloor : x / 36 - 1 < T := by
    dsimp only [x, T]
    rw [P.Sstep_div_four_eq_floor_levelScale_div_thirtySix]
    linarith [Nat.lt_floor_add_one (P.levelScale J / 36)]
  have hTpos : 0 < T := by
    have : (0 : ℝ) < x / 36 - 1 := by linarith
    linarith
  have hsource :
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld = A * x := by
    dsimp only [A, x]
    rw [← P.levelScale_mul_qpow_mul_h J]
    ring_nf
  have hbase :
      5 * (A * x) <
        (1.0986122885 : ℝ) * ((192 * A) * (x / 36 - 1)) := by
    nlinarith [mul_lt_mul_of_pos_left hx hA]
  have hfloor :
      (1.0986122885 : ℝ) * ((192 * A) * (x / 36 - 1)) <
        (1.0986122885 : ℝ) * ((192 * A) * T) := by
    exact mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left hTfloor (by positivity)) (by norm_num)
  have hlog : (1.0986122885 : ℝ) < Real.log 3 :=
    Real.log_three_gt_d9
  have hlogStep :
      (1.0986122885 : ℝ) * ((192 * A) * T) <
        ((192 * A) * T) * Real.log 3 := by
    have hZ : 0 < (192 * A) * T := mul_pos (by positivity) hTpos
    nlinarith [mul_lt_mul_of_pos_left hlog hZ]
  have hcount :
      (((P.R (J + 1) * (P.q - 1) / P.q) *
          (P.Sstep J / 4) : ℕ) : ℝ) = (192 * A) * T := by
    rw [P.successor_coprime_node_count_eq J]
    dsimp only [A, T]
    push_cast
    ring
  rw [hsource, hcount]
  exact hbase.trans (hfloor.trans hlogStep)

/-- The outer circle `|z| = 3R` stays at distance at least `2R` from every
target integer `l ≤ R`. -/
theorem two_mul_R_le_three_mul_R_sub_target {J l : ℕ}
    (hl : l ≤ P.R J) :
    (2 : ℝ) * P.R J ≤ 3 * P.R J - l := by
  have hl' : (l : ℝ) ≤ P.R J := by exact_mod_cast hl
  linarith

/-- In particular, the source contour denominator is positive. -/
theorem three_mul_R_sub_target_pos {J l : ℕ}
    (hl : l ≤ P.R J) :
    0 < (3 : ℝ) * P.R J - l := by
  have hR : (0 : ℝ) < P.R J := by exact_mod_cast P.R_pos J
  have h := P.two_mul_R_le_three_mul_R_sub_target hl
  exact (mul_pos (by norm_num) hR).trans_le h

/-! ## Elementary exponential absorption -/

/-- Convert a natural power into the exponential budget used throughout
the source. -/
theorem pow_le_exp_of_mul_log_le {a A : ℝ} {n : ℕ}
    (ha : 0 < a) (h : (n : ℝ) * Real.log a ≤ A) :
    a ^ n ≤ Real.exp A := by
  calc
    a ^ n = Real.exp (Real.log a) ^ n := by rw [Real.exp_log ha]
    _ = Real.exp ((n : ℝ) * Real.log a) :=
      (Real.exp_nat_mul (Real.log a) n).symm
    _ ≤ Real.exp A := Real.exp_le_exp.mpr h

/-- Strict version of `pow_le_exp_of_mul_log_le`. -/
theorem pow_lt_exp_of_mul_log_lt {a A : ℝ} {n : ℕ}
    (ha : 0 < a) (h : (n : ℝ) * Real.log a < A) :
    a ^ n < Real.exp A := by
  calc
    a ^ n = Real.exp (Real.log a) ^ n := by rw [Real.exp_log ha]
    _ = Real.exp ((n : ℝ) * Real.log a) :=
      (Real.exp_nat_mul (Real.log a) n).symm
    _ < Real.exp A := Real.exp_lt_exp.mpr h

/-- The complete explicit-Hermite-basis loss in source Lemma 5 fits in one
twelfth of the normalized source exponent.  Here `R` and `T` are the literal
terminal radius and repeated-node multiplicity, so this theorem includes
both floor losses and the extra `+1` in `T`.

The factor on the left is the exact `q^T * 2^((4R+3)T)` supplied by the
factorial-cancelled explicit basis estimate. -/
theorem lemmaFive_explicitHermiteFactor_le_exp_twelfth [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    (P.q : ℝ) ^ P.lemmaFiveLocalMultiplicity J *
        (2 : ℝ) ^ ((4 * P.lemmaFiveLocalRadius J + 3) *
          P.lemmaFiveLocalMultiplicity J) ≤
      Real.exp ((P.C * P.Omega * Real.log P.OmegaOld *
        Real.log (P.Bsrc : ℝ)) / 12) := by
  let R : ℕ := P.lemmaFiveLocalRadius J
  let T : ℕ := P.lemmaFiveLocalMultiplicity J
  let x : ℝ := P.levelScale J
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  have hxpos : 0 < x := by exact P.levelScale_pos J
  have hxlarge : (512 : ℝ) < x := by
    exact P.fiveHundredTwelve_lt_levelScale_of_LevelOK hJ
  have hu : (128 : ℝ) ≤ u := by
    exact P.oneTwentyEight_le_k_rpow_half
  have hupos : 0 < u := by dsimp only [u]; positivity
  have hWpos : 0 < W := by
    dsimp only [W]
    exact mul_pos P.Omega_pos P.log_OmegaOld_pos
  have hR : (R : ℝ) ≤
      16 * ((P.q ^ J : ℕ) : ℝ) * P.h * u := by
    dsimp only [R, lemmaFiveLocalRadius, u]
    exact Nat.floor_le (by positivity)
  have hT : (T : ℝ) ≤ x / 16 := by
    dsimp only [T, lemmaFiveLocalMultiplicity]
    calc
      ((⌊P.levelScale J / 6⌋₊ / 3 + 1 : ℕ) : ℝ) =
          ((⌊P.levelScale J / 6⌋₊ / 3 : ℕ) : ℝ) + 1 := by
            push_cast
            rfl
      _ ≤ (⌊P.levelScale J / 6⌋₊ : ℝ) / 3 + 1 := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ (P.levelScale J / 6) / 3 + 1 := by
        gcongr
        exact Nat.floor_le (by positivity)
      _ ≤ x / 16 := by
        dsimp only [x]
        nlinarith
  have hRT : (R : ℝ) * T ≤ (P.h : ℝ) * P.k * u * W := by
    calc
      (R : ℝ) * T ≤
          (16 * ((P.q ^ J : ℕ) : ℝ) * P.h * u) * (x / 16) :=
        mul_le_mul hR hT (by positivity) (by positivity)
      _ = (P.h : ℝ) * P.k * u * W := by
        dsimp only [x, W]
        rw [show
          (16 * ((P.q ^ J : ℕ) : ℝ) * (P.h : ℝ) * u) *
              (P.levelScale J / 16) =
            (P.levelScale J * ((P.q ^ J : ℕ) : ℝ) * P.h) * u by ring]
        rw [P.levelScale_mul_qpow_mul_h J]
        ring
  have hqInv : P.qInvPow J ≤ 1 := by
    have hmono := P.qInvPow_antitone (Nat.zero_le J)
    simpa [qInvPow] using hmono
  have hxUpper : x ≤ P.k * W := by
    dsimp only [x, W]
    unfold levelScale
    have hkW : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
      mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
        P.log_OmegaOld_pos.le
    calc
      P.qInvPow J * P.k * P.Omega * Real.log P.OmegaOld =
          P.qInvPow J * (P.k * P.Omega * Real.log P.OmegaOld) := by ring
      _ ≤ 1 * (P.k * P.Omega * Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_right hqInv hkW
      _ = P.k * (P.Omega * Real.log P.OmegaOld) := by ring
  have hOneH : (1 : ℝ) ≤ P.h := by exact_mod_cast P.h_pos
  have hOneU : (1 : ℝ) ≤ u := (by norm_num : (1 : ℝ) ≤ 128).trans hu
  have hkW_le : P.k * W ≤ (P.h : ℝ) * P.k * u * W := by
    have hkWnonneg : 0 ≤ P.k * W := mul_nonneg P.k_pos.le hWpos.le
    have hh : P.k * W ≤ (P.h : ℝ) * (P.k * W) :=
      le_mul_of_one_le_left hkWnonneg hOneH
    have hhu : (P.h : ℝ) * (P.k * W) ≤
        ((P.h : ℝ) * (P.k * W)) * u :=
      le_mul_of_one_le_right (mul_nonneg (by positivity) hkWnonneg) hOneU
    calc
      P.k * W ≤ (P.h : ℝ) * (P.k * W) := hh
      _ ≤ ((P.h : ℝ) * (P.k * W)) * u := hhu
      _ = (P.h : ℝ) * P.k * u * W := by ring
  have hTloss : 4 * (T : ℝ) ≤ (P.h : ℝ) * P.k * u * W := by
    have h4T : 4 * (T : ℝ) ≤ x / 4 := by nlinarith
    exact h4T.trans (by
      have hxQuarter : x / 4 ≤ x := by nlinarith
      exact hxQuarter.trans (hxUpper.trans hkW_le))
  have hIndex :
      (((4 * R * T + 7 * T : ℕ) : ℝ)) ≤
        6 * ((P.h : ℝ) * P.k * u * W) := by
    push_cast
    nlinarith
  have huSquare : u * u = P.k := by
    dsimp only [u]
    rw [← Real.rpow_add P.k_pos]
    norm_num
  have hSeventyTwoU : (72 : ℝ) * u ≤ P.k := by
    calc
      (72 : ℝ) * u ≤ u * u :=
        mul_le_mul_of_nonneg_right
          ((by norm_num : (72 : ℝ) ≤ 128).trans hu) hupos.le
      _ = P.k := huSquare
  have hCoeff :
      (72 : ℝ) * P.h * P.k * u ≤
        Real.log (P.Bsrc : ℝ) * P.k * P.k := by
    calc
      (72 : ℝ) * P.h * P.k * u =
          (P.h : ℝ) * P.k * (72 * u) := by ring
      _ ≤ (P.h : ℝ) * P.k * P.k :=
        mul_le_mul_of_nonneg_left hSeventyTwoU
          (mul_nonneg (by positivity) P.k_pos.le)
      _ ≤ Real.log (P.Bsrc : ℝ) * P.k * P.k := by
        have hkk : 0 ≤ P.k * P.k := mul_nonneg P.k_pos.le P.k_pos.le
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right P.h_cast_le_log_Bsrc hkk
  have hCoeffW := mul_le_mul_of_nonneg_right hCoeff hWpos.le
  have hCore :
      6 * ((P.h : ℝ) * P.k * u * W) ≤
        (P.C * P.Omega * Real.log P.OmegaOld *
          Real.log (P.Bsrc : ℝ)) / 12 := by
    rw [C, P.mu_eq]
    norm_num [Real.rpow_two]
    dsimp only [W] at hCoeffW ⊢
    nlinarith
  have hLoss :
      (P.q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) ≤
        (2 : ℝ) ^ (4 * R * T + 7 * T) := by
    calc
      (P.q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) ≤
          ((2 : ℝ) ^ 4) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) := by
        gcongr
        norm_num [q]
      _ = (2 : ℝ) ^ (4 * R * T + 7 * T) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  change (P.q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) ≤ _
  refine hLoss.trans (pow_le_exp_of_mul_log_le (by norm_num) ?_)
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hIndexNonneg : (0 : ℝ) ≤ ((4 * R * T + 7 * T : ℕ) : ℝ) := by
    positivity
  calc
    ((4 * R * T + 7 * T : ℕ) : ℝ) * Real.log 2 ≤
        ((4 * R * T + 7 * T : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlogTwo hIndexNonneg
    _ ≤ 6 * ((P.h : ℝ) * P.k * u * W) := by simpa using hIndex
    _ ≤ (P.C * P.Omega * Real.log P.OmegaOld *
        Real.log (P.Bsrc : ℝ)) / 12 := hCore

/-- The earlier local-circle kernel factor is a subfactor of the explicit
Hermite-basis loss, and hence satisfies the same one-twelfth budget. -/
theorem lemmaFive_localCircleFactor_le_exp_twelfth [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    (2 : ℝ) ^ (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) *
        ((P.q : ℝ) *
          (2 : ℝ) ^ (3 * P.lemmaFiveLocalRadius J)) ^
            P.lemmaFiveLocalMultiplicity J ≤
      Real.exp ((P.C * P.Omega * Real.log P.OmegaOld *
        Real.log (P.Bsrc : ℝ)) / 12) := by
  let R : ℕ := P.lemmaFiveLocalRadius J
  let T : ℕ := P.lemmaFiveLocalMultiplicity J
  apply le_trans (b :=
    (P.q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T))
  · rw [mul_pow]
    calc
      (2 : ℝ) ^ (R * T) *
          ((P.q : ℝ) ^ T * ((2 : ℝ) ^ (3 * R)) ^ T) =
          (P.q : ℝ) ^ T * (2 : ℝ) ^ (4 * R * T) := by
            rw [← pow_mul]
            calc
              (2 : ℝ) ^ (R * T) *
                  ((P.q : ℝ) ^ T * (2 : ℝ) ^ (3 * R * T)) =
                  (P.q : ℝ) ^ T *
                    ((2 : ℝ) ^ (R * T) * (2 : ℝ) ^ (3 * R * T)) := by ring
              _ = (P.q : ℝ) ^ T *
                  (2 : ℝ) ^ (R * T + 3 * R * T) := by rw [pow_add]
              _ = (P.q : ℝ) ^ T * (2 : ℝ) ^ (4 * R * T) := by
                congr 2
                ring
      _ ≤ (P.q : ℝ) ^ T * (2 : ℝ) ^ ((4 * R + 3) * T) := by
        apply mul_le_mul_of_nonneg_left
        · have hbase : 4 * R ≤ 4 * R + 3 := by omega
          have hexp : 4 * R * T ≤ (4 * R + 3) * T :=
            Nat.mul_le_mul_right T hbase
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
        · positivity
  · simpa only [R, T] using
      P.lemmaFive_explicitHermiteFactor_le_exp_twelfth hJ

/-- Exponential form of the exact p. 52 coprime-node decay.  This packages
the preceding strict exponent comparison as the inverse-cube power bound
consumed by the interpolation argument. -/
theorem coprime_decay_pow_lt_exp_neg_three_sourceExponent [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    ((3 : ℝ)⁻¹) ^
        ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4)) <
      Real.exp (-(3 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  apply pow_lt_exp_of_mul_log_lt (by positivity)
  rw [Real.log_inv]
  have h := P.three_mul_sourceExponent_lt_coprime_decayExponent hJ
  push_cast at h ⊢
  linarith

/-- Sharper inverse-power form, retaining all five source exponents supplied
by the baseline admissibility ledger. -/
theorem coprime_decay_pow_lt_exp_neg_five_sourceExponent [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) :
    ((3 : ℝ)⁻¹) ^
        ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4)) <
      Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  apply pow_lt_exp_of_mul_log_lt (by positivity)
  rw [Real.log_inv]
  have h := P.five_mul_sourceExponent_lt_coprime_decayExponent hJ
  push_cast at h ⊢
  linarith

/-- The source prints the coprime decay as a power of a powered base.  This
is definitionally the flattened natural exponent used in the budget lemmas. -/
theorem coprime_decay_source_power_eq (J : ℕ) :
    (((3 : ℝ)⁻¹) ^ (P.R (J + 1) * (P.q - 1) / P.q)) ^
        (P.Sstep J / 4) =
      ((3 : ℝ)⁻¹) ^
        ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4)) := by
  rw [pow_mul]

/-- Literal nested-power transcription of the p. 52 five-exponent bound. -/
theorem coprime_decay_source_power_lt_exp_neg_five_sourceExponent
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    (((3 : ℝ)⁻¹) ^ (P.R (J + 1) * (P.q - 1) / P.q)) ^
        (P.Sstep J / 4) <
      Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  rw [P.coprime_decay_source_power_eq J]
  exact P.coprime_decay_pow_lt_exp_neg_five_sourceExponent hJ

/-- Paying a two-source-exponent growth loss against the exact p. 52 nodal
factor still leaves the source's strict `exp (-3E)` target. -/
theorem mul_coprime_decay_lt_exp_neg_three_sourceExponent [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) {growth : ℝ}
    (hgrowth : growth ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    growth * ((3 : ℝ)⁻¹) ^
        ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4)) <
      Real.exp (-(3 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  let E : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let decay : ℝ := ((3 : ℝ)⁻¹) ^
    ((P.R (J + 1) * (P.q - 1) / P.q) * (P.Sstep J / 4))
  have hdecay : decay < Real.exp (-(5 * E)) := by
    exact P.coprime_decay_pow_lt_exp_neg_five_sourceExponent hJ
  calc
    growth * decay ≤ Real.exp (2 * E) * decay :=
      mul_le_mul_of_nonneg_right (by simpa only [E] using hgrowth) (by positivity)
    _ < Real.exp (2 * E) * Real.exp (-(5 * E)) :=
      mul_lt_mul_of_pos_left hdecay (Real.exp_pos _)
    _ = Real.exp (-(3 * E)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(3 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := rfl

/-! ## Exact per-stage source Lemma 4 contour budget -/

/-- The derivative budget in source Lemma 4 decreases at every inner stage.
This is the parameter-only version of the bookkeeping fact, kept here so
that numerical estimates do not need to import the analytic induction. -/
theorem lemmaFourBudget_succ_le_current (N t : ℕ) :
    P.lemmaFourBudget N (t + 1) ≤ P.lemmaFourBudget N t := by
  cases t with
  | zero =>
      simp only [Nat.zero_add, P.lemmaFourBudget_zero,
        P.lemmaFourBudget_one]
      have hfloor :
          ((⌊(P.Slevel N : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤
            (P.Slevel N : ℝ) / 2 :=
        Nat.floor_le (by positivity)
      have hhalf : (P.Slevel N : ℝ) / 2 ≤ P.Slevel N := by
        have hnonneg : (0 : ℝ) ≤ P.Slevel N := by positivity
        linarith
      exact_mod_cast hfloor.trans hhalf
  | succ t =>
      have htpos : 1 ≤ t + 1 := by omega
      have hepslt : P.epsilon < 1 := by
        rw [P.epsilon_eq]
        have hrank : (0 : ℝ) < P.rank + 1 := by positivity
        apply (div_lt_one (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
        nlinarith
      have harg :
          0 ≤ (1 - P.epsilon) *
            (P.lemmaFourBudget N (t + 1) : ℝ) := by
        positivity
      have hfloor :
          ((⌊(1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ)⌋₊ : ℕ) : ℝ) ≤
            (1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ) :=
        Nat.floor_le harg
      have hmul :
          (1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ) ≤
            P.lemmaFourBudget N (t + 1) := by
        have hbudget :
            (0 : ℝ) ≤ P.lemmaFourBudget N (t + 1) := by positivity
        nlinarith [P.epsilon_pos]
      rw [show t + 1 + 1 = t + 2 by omega,
        P.lemmaFourBudget_succ_succ,
        P.lemmaFourEpsilon_eq_epsilon htpos]
      exact_mod_cast hfloor.trans hmul

/-- Every inner derivative budget is bounded by the initial level budget. -/
theorem lemmaFourBudget_le_Slevel (N t : ℕ) :
    P.lemmaFourBudget N t ≤ P.Slevel N := by
  induction t with
  | zero => simp
  | succ t ih =>
      exact (P.lemmaFourBudget_succ_le_current N t).trans ih

/-- A fixed-family constant large enough to pay the complete local-circle
kernel and number-of-terms loss at every genuine source Lemma 4 stage.  The
constant depends on `k` (hence on the fixed old family/rank), but not on the
outer level or the varying final prime. -/
def lemmaFourContourAbsorptionConstant : ℝ :=
  960 * P.k ^ 2

/-- The literal equation-(9) double-sum factor at an arbitrary genuine
source Lemma 4 stage fits in one sixth of the fixed-family exponent.

Here the repeated-node multiplicity is exactly
`S_t - S_(t+1) + 1`; both radius floors and the final `+1` are included.
The proof only uses the actual stage bound `t < 3(rank+1)` and admissibility
of the outer level. -/
theorem lemmaFour_localCircleFactor_le_exp_sixth [Nonempty ι]
    {N t l : ℕ} (hN : P.LevelOK N)
    (ht : t < 3 * (P.rank + 1))
    (hl : l ≤ P.lemmaFourRadius N (t + 1)) :
    (2 : ℝ) ^
        (((3 * P.lemmaFourRadius N t + l) *
              (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)) +
          P.lemmaFourRadius N t *
              (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)) ≤
      Real.exp ((P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
        P.Omega * Real.log P.OmegaOld) / 6) := by
  let T : ℕ :=
    P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1
  let M : ℝ :=
    16 * ((P.q ^ N : ℕ) : ℝ) * P.h * P.k
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  have hxlarge : (512 : ℝ) < P.levelScale N :=
    P.fiveHundredTwelve_lt_levelScale_of_LevelOK hN
  have heps : P.epsilon * ((t + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [P.epsilon_eq]
    have ht' : ((t + 1 : ℕ) : ℝ) ≤ 3 * (P.rank + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr ht)
    have hden : (0 : ℝ) < 6 * (P.rank + 1) := by positivity
    calc
      (1 / (6 * (P.rank + 1 : ℝ))) * ((t + 1 : ℕ) : ℝ) =
          ((t + 1 : ℕ) : ℝ) / (6 * (P.rank + 1 : ℝ)) := by ring
      _ ≤ 1 := (div_le_one hden).2 (by nlinarith)
  have hkpow :
      P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ)) ≤ P.k := by
    simpa using Real.rpow_le_rpow_of_exponent_le P.one_le_k heps
  have hRnext : (P.lemmaFourRadius N (t + 1) : ℝ) ≤ M := by
    calc
      (P.lemmaFourRadius N (t + 1) : ℝ) ≤
          P.lemmaFourRadiusScale N (t + 1) :=
        Nat.floor_le (P.lemmaFourRadiusScale_pos N (t + 1)).le
      _ ≤ M := by
        dsimp only [VDPLParameters.lemmaFourRadiusScale, M]
        gcongr
  have hepsMono : P.epsilon * (t : ℝ) ≤
      P.epsilon * ((t + 1 : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ P.epsilon_pos.le
    exact_mod_cast Nat.le_succ t
  have hkpowOld : P.k ^ (P.epsilon * (t : ℝ)) ≤ P.k :=
    (Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsMono).trans hkpow
  have hRold : (P.lemmaFourRadius N t : ℝ) ≤ M := by
    calc
      (P.lemmaFourRadius N t : ℝ) ≤
          P.lemmaFourRadiusScale N t :=
        Nat.floor_le (P.lemmaFourRadiusScale_pos N t).le
      _ ≤ M := by
        dsimp only [VDPLParameters.lemmaFourRadiusScale, M]
        gcongr
  have hlM : (l : ℝ) ≤ M := by
    exact (by exact_mod_cast hl : (l : ℝ) ≤
      P.lemmaFourRadius N (t + 1)).trans hRnext
  have hTnat : T ≤ P.Slevel N + 1 := by
    dsimp only [T]
    have hbudget := P.lemmaFourBudget_le_Slevel N t
    omega
  have hT : (T : ℝ) ≤ 2 * P.levelScale N := by
    have hS := P.Slevel_cast_le N
    have hone : (1 : ℝ) ≤ P.levelScale N := by linarith
    have hTcast : (T : ℝ) ≤ (P.Slevel N + 1 : ℕ) := by
      exact_mod_cast hTnat
    push_cast at hTcast
    linarith
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (by positivity))
        (by positivity))
      P.k_pos.le
  have hMT : M * (T : ℝ) ≤
      32 * (P.h : ℝ) * P.k ^ 2 * W := by
    calc
      M * (T : ℝ) ≤ M * (2 * P.levelScale N) :=
        mul_le_mul_of_nonneg_left hT hM0
      _ = 32 * P.k *
          (P.levelScale N * ((P.q ^ N : ℕ) : ℝ) * P.h) := by
        dsimp only [M]
        ring
      _ = 32 * (P.h : ℝ) * P.k ^ 2 * W := by
        rw [P.levelScale_mul_qpow_mul_h N]
        dsimp only [W]
        ring
  have hexponent :
      (((((3 * P.lemmaFourRadius N t + l) * T) +
          P.lemmaFourRadius N t * T : ℕ) : ℝ)) ≤
        160 * (P.h : ℝ) * P.k ^ 2 * W := by
    push_cast
    calc
      ((3 * (P.lemmaFourRadius N t : ℝ) + l) * T +
          (P.lemmaFourRadius N t : ℝ) * T) =
          (4 * (P.lemmaFourRadius N t : ℝ) + l) * T := by ring
      _ ≤ (5 * M) * T := by
        gcongr
        linarith
      _ = 5 * (M * T) := by ring
      _ ≤ 5 * (32 * (P.h : ℝ) * P.k ^ 2 * W) := by gcongr
      _ = 160 * (P.h : ℝ) * P.k ^ 2 * W := by ring
  apply pow_le_exp_of_mul_log_le (by norm_num : (0 : ℝ) < 2)
  calc
    (((((3 * P.lemmaFourRadius N t + l) * T) +
        P.lemmaFourRadius N t * T : ℕ) : ℝ)) * Real.log 2 ≤
        (((((3 * P.lemmaFourRadius N t + l) * T) +
          P.lemmaFourRadius N t * T : ℕ) : ℝ)) := by
      apply mul_le_of_le_one_right (by positivity)
      nlinarith [Real.log_two_lt_d9]
    _ ≤ 160 * (P.h : ℝ) * P.k ^ 2 * W := hexponent
    _ = (P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
        P.Omega * Real.log P.OmegaOld) / 6 := by
      unfold lemmaFourContourAbsorptionConstant
      dsimp only [W]
      ring

/-- Generic outer-contour absorption for the exact integral nodal quotient.
It is stated in logarithmic form so the source's separate `t = 0` and
`t > 0` count estimates can use the same endpoint. -/
theorem mul_two_inv_pow_lt_exp_neg_of_add_lt_count_log
    {growth G D : ℝ} {n : ℕ}
    (hgrowth : growth ≤ Real.exp G)
    (hcount : D + G < (n : ℝ) * Real.log 2) :
    growth * (1 / 2 : ℝ) ^ n < Real.exp (-D) := by
  have hpow : (1 / 2 : ℝ) ^ n =
      Real.exp (-((n : ℝ) * Real.log 2)) := by
    calc
      (1 / 2 : ℝ) ^ n = Real.exp (Real.log (1 / 2 : ℝ)) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
      _ = Real.exp ((n : ℝ) * Real.log (1 / 2 : ℝ)) :=
        (Real.exp_nat_mul (Real.log (1 / 2 : ℝ)) n).symm
      _ = Real.exp (-((n : ℝ) * Real.log 2)) := by
        rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
          rw [one_div, Real.log_inv]]
        congr 1
        ring
  rw [hpow]
  calc
    growth * Real.exp (-((n : ℝ) * Real.log 2)) ≤
        Real.exp G * Real.exp (-((n : ℝ) * Real.log 2)) :=
      mul_le_mul_of_nonneg_right hgrowth (Real.exp_pos _).le
    _ = Real.exp (G - (n : ℝ) * Real.log 2) := by
      rw [sub_eq_add_neg, Real.exp_add]
    _ < Real.exp (-D) := by
      apply Real.exp_lt_exp.mpr
      linarith

/-- The `3^(-n)` analogue of `mul_two_inv_pow_lt_exp_neg_of_add_lt_count_log`.
This is the form used at every positive source Lemma-4 stage, where a genuinely
new integral target gives one factor `1/3` for each old nodal factor. -/
theorem mul_three_inv_pow_lt_exp_neg_of_add_lt_count_log
    {growth G D : ℝ} {n : ℕ}
    (hgrowth : growth ≤ Real.exp G)
    (hcount : D + G < (n : ℝ) * Real.log 3) :
    growth * (1 / 3 : ℝ) ^ n < Real.exp (-D) := by
  have hpow : (1 / 3 : ℝ) ^ n =
      Real.exp (-((n : ℝ) * Real.log 3)) := by
    calc
      (1 / 3 : ℝ) ^ n = Real.exp (Real.log (1 / 3 : ℝ)) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 3)]
      _ = Real.exp ((n : ℝ) * Real.log (1 / 3 : ℝ)) :=
        (Real.exp_nat_mul (Real.log (1 / 3 : ℝ)) n).symm
      _ = Real.exp (-((n : ℝ) * Real.log 3)) := by
        rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
          rw [one_div, Real.log_inv]]
        congr 1
        ring
  rw [hpow]
  calc
    growth * Real.exp (-((n : ℝ) * Real.log 3)) ≤
        Real.exp G * Real.exp (-((n : ℝ) * Real.log 3)) :=
      mul_le_mul_of_nonneg_right hgrowth (Real.exp_pos _).le
    _ = Real.exp (G - (n : ℝ) * Real.log 3) := by
      rw [sub_eq_add_neg, Real.exp_add]
    _ < Real.exp (-D) := by
      apply Real.exp_lt_exp.mpr
      linarith

/-- Absorb both the exact positive-stage nodal decay `3^(-n)` and the
`3/2` radius-over-gap loss from the outer Cauchy integral.  One extra unit in
the logarithmic count is sufficient because `3/2 < exp 1`. -/
theorem three_halves_mul_three_inv_pow_mul_lt_exp_neg_of_count
    {growth G D : ℝ} {n : ℕ}
    (hgrowth0 : 0 ≤ growth)
    (hgrowth : growth ≤ Real.exp G)
    (hcount : D + 1 + G < (n : ℝ) * Real.log 3) :
    (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^ n * growth) < Real.exp (-D) := by
  have hdecay : growth * (1 / 3 : ℝ) ^ n < Real.exp (-(D + 1)) := by
    apply mul_three_inv_pow_lt_exp_neg_of_add_lt_count_log hgrowth
    linarith
  have hfactor : (3 / 2 : ℝ) < Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  calc
    (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^ n * growth) =
        (3 / 2 : ℝ) * (growth * (1 / 3 : ℝ) ^ n) := by ring
    _ < Real.exp 1 * Real.exp (-(D + 1)) :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hfactor.le
          (mul_nonneg hgrowth0 (pow_nonneg (by norm_num) n)))
        (mul_lt_mul_of_pos_left hdecay (Real.exp_pos 1))
    _ = Real.exp (-D) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The corresponding `3/2` Cauchy-loss absorption for the uniform
`2^(-n)` nodal estimate used in source Lemma 5. -/
theorem three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count
    {growth G D : ℝ} {n : ℕ}
    (hgrowth0 : 0 ≤ growth)
    (hgrowth : growth ≤ Real.exp G)
    (hcount : D + 1 + G < (n : ℝ) * Real.log 2) :
    (3 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * growth) < Real.exp (-D) := by
  have hdecay : growth * (1 / 2 : ℝ) ^ n < Real.exp (-(D + 1)) := by
    apply mul_two_inv_pow_lt_exp_neg_of_add_lt_count_log hgrowth
    linarith
  have hfactor : (3 / 2 : ℝ) < Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  calc
    (3 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * growth) =
        (3 / 2 : ℝ) * (growth * (1 / 2 : ℝ) ^ n) := by ring
    _ < Real.exp 1 * Real.exp (-(D + 1)) :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hfactor.le
          (mul_nonneg hgrowth0 (pow_nonneg (by norm_num) n)))
        (mul_lt_mul_of_pos_left hdecay (Real.exp_pos 1))
    _ = Real.exp (-D) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-! ## The exact source Lemma 5 outer count -/

/-- The common source height unit is at least one.  Keeping this elementary
fact explicit lets the contour estimates pay a fixed factor such as `3/2`
with one additional exponential unit. -/
theorem one_le_sourceHeightUnit [Nonempty ι] :
    (1 : ℝ) ≤ (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  have hk : (1 : ℝ) ≤ P.k := P.one_le_k
  have hOmega : (1 : ℝ) ≤ P.Omega := P.one_le_Omega
  have hlog : (1 / 2 : ℝ) ≤ Real.log P.OmegaOld := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ Real.log P.OmegaOld := P.log_two_le_log_OmegaOld
  have hhk : (2 : ℝ) ≤ (P.h : ℝ) * P.k := by
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ (P.h : ℝ) * P.k :=
        mul_le_mul hh hk (by norm_num) (by positivity)
  have hOlog : (1 / 2 : ℝ) ≤ P.Omega * Real.log P.OmegaOld := by
    calc
      (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
      _ ≤ P.Omega * Real.log P.OmegaOld :=
        mul_le_mul hOmega hlog (by norm_num) (by positivity)
  calc
    (1 : ℝ) = 2 * (1 / 2) := by ring
    _ ≤ ((P.h : ℝ) * P.k) *
        (P.Omega * Real.log P.OmegaOld) :=
      mul_le_mul hhk hOlog (by norm_num)
        (mul_nonneg (by positivity) P.k_pos.le)
    _ = (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by ring

/-- The literal floored Lemma-5 radius and multiplicity provide more than
thirty source height units of logarithmic decay.  This is substantially
stronger than the `2^(-R*T)` estimate needed by the outer contour, and it
retains both floor losses and the terminal `+1` in the multiplicity. -/
theorem thirty_mul_sourceHeightUnit_lt_lemmaFive_count_log_two
    [Nonempty ι] {J : ℕ} (hJ : P.LevelOK J) :
    30 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
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
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu
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
  have hRT : (15 / 19 : ℝ) * u * H < (R : ℝ) * T := by
    have hxdiv : 0 < x / 19 := div_pos hxpos (by norm_num)
    have hprod : (15 * A * u) * (x / 19) < (R : ℝ) * T := by
      calc
        (15 * A * u) * (x / 19) < (R : ℝ) * (x / 19) :=
          mul_lt_mul_of_pos_right hR hxdiv
        _ < (R : ℝ) * T := mul_lt_mul_of_pos_left hT hRpos
    have hsource : A * x = H := by
      calc
        A * x = P.levelScale J * ((P.q ^ J : ℕ) : ℝ) * P.h := by
          dsimp only [A, x]
          ring
        _ = H := by
          rw [P.levelScale_mul_qpow_mul_h J]
    calc
      (15 / 19 : ℝ) * u * H = (15 * A * u) * (x / 19) := by
        rw [← hsource]
        ring
      _ < (R : ℝ) * T := hprod
  have hcoeff : (30 : ℝ) < (15 / 19 : ℝ) * u * Real.log 2 := by
    have hbase : (30 : ℝ) < (15 / 19 : ℝ) * 64 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans_le (by
      have hlog0 : 0 ≤ Real.log 2 := Real.log_pos (by norm_num) |>.le
      gcongr)
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hfirst : 30 * H < ((15 / 19 : ℝ) * u * H) * Real.log 2 := by
    calc
      30 * H < ((15 / 19 : ℝ) * u * Real.log 2) * H :=
        mul_lt_mul_of_pos_right hcoeff hHpos
      _ = ((15 / 19 : ℝ) * u * H) * Real.log 2 := by ring
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change 30 * H < ((R * T : ℕ) : ℝ) * Real.log 2
  rw [Nat.cast_mul]
  exact hfirst.trans
    (mul_lt_mul_of_pos_right hRT hlogpos)

/-- After paying a two-height-unit outer-growth bound and the exact `3/2`
Cauchy radius/gap factor, the Lemma-5 nodal quotient still leaves twenty
seven full source height units of decay.  The normalized oversized constant
does not occur here: the outer count is intrinsically tied to the original
source height scale. -/
theorem lemmaFive_outerFactor_lt_exp_neg_twentySeven [Nonempty ι]
    {J : ℕ} (hJ : P.LevelOK J) {outer : ℝ}
    (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-(27 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  have hcount := P.thirty_mul_sourceHeightUnit_lt_lemmaFive_count_log_two hJ
  have hH := P.one_le_sourceHeightUnit
  linarith

/-- At the exceptional first source Lemma 4 stage, the exact floored node
count still supplies more than five units of logarithmic decay.  This is the
honest strength available with the current source specialization `D = 1`;
it is deliberately recorded independently of any subsequently chosen
logarithmic-form constant. -/
theorem five_mul_initialOuterExponent_lt_count_mul_log_two [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) :
    5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFourRadius N 0 *
        (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1) : ℕ) : ℝ) *
          Real.log 2 := by
  let x : ℝ := P.levelScale N
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let T : ℕ := P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1
  have hxlarge : (512 : ℝ) < x := by
    exact P.fiveHundredTwelve_lt_levelScale_of_LevelOK hN
  have hbudget : P.lemmaFourBudget N 1 ≤ P.lemmaFourBudget N 0 :=
    P.lemmaFourBudget_succ_le_current N 0
  have hfloor : (P.lemmaFourBudget N 1 : ℝ) ≤
      (P.Slevel N : ℝ) / 2 := by
    rw [P.lemmaFourBudget_one]
    exact Nat.floor_le (by positivity)
  have hT : (P.Slevel N : ℝ) / 2 ≤ T := by
    dsimp only [T]
    rw [P.lemmaFourBudget_zero]
    have hbudgetS : P.lemmaFourBudget N 1 ≤ P.Slevel N := by
      simpa only [P.lemmaFourBudget_zero] using hbudget
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hbudgetS]
    linarith
  have hS : x - 1 < (P.Slevel N : ℝ) := by
    have h : x < (P.Slevel N : ℝ) + 1 := by
      simpa only [x, VDPLParameters.Slevel] using
        Nat.lt_floor_add_one (P.levelScale N)
    linarith
  have hTstrong : (x - 1) / 2 < (T : ℝ) := by linarith
  have hR : P.lemmaFourRadius N 0 = 16 * P.q ^ N * P.h := by
    rw [P.lemmaFourRadius_zero]
    rfl
  have hRpos : (0 : ℝ) < P.lemmaFourRadius N 0 := by
    exact_mod_cast (by simpa only [P.lemmaFourRadius_zero] using P.R_pos N)
  have hcount :
      (511 / 64 : ℝ) * H <
        (P.lemmaFourRadius N 0 : ℝ) * T := by
    have hTx : (511 / 1024 : ℝ) * x < T := by
      have hx : (511 / 512 : ℝ) * x < x - 1 := by
        nlinarith
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hTx hRpos
    have hcancel := P.levelScale_mul_qpow_mul_h N
    calc
      (511 / 64 : ℝ) * H =
          (P.lemmaFourRadius N 0 : ℝ) *
            ((511 / 1024 : ℝ) * x) := by
        rw [hR]
        push_cast
        dsimp only [x, H]
        rw [show (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld =
          P.levelScale N * ((P.q ^ N : ℕ) : ℝ) * P.h by
            exact hcancel.symm]
        simp only [Nat.cast_pow]
        ring
      _ < (P.lemmaFourRadius N 0 : ℝ) * T := hmul
  have hlog : (5 : ℝ) < (511 / 64 : ℝ) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hHpos : 0 < H := by
    dsimp only [H]
    exact mul_pos
      (mul_pos
        (mul_pos (by exact_mod_cast P.h_pos) P.k_pos)
        P.Omega_pos)
      P.log_OmegaOld_pos
  have hfirst : 5 * H <
      ((511 / 64 : ℝ) * H) * Real.log 2 := by
    calc
      5 * H < ((511 / 64 : ℝ) * Real.log 2) * H :=
        mul_lt_mul_of_pos_right hlog hHpos
      _ = ((511 / 64 : ℝ) * H) * Real.log 2 := by ring
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Nat.cast_mul]
  change 5 * H <
    (P.lemmaFourRadius N 0 : ℝ) * (T : ℝ) * Real.log 2
  exact hfirst.trans
    (mul_lt_mul_of_pos_right hcount hlogpos)

/-- Paying a two-exponent source growth bound against the exact initial
outer nodal quotient leaves a strict three-exponent decay. -/
theorem mul_initialOuterFactor_lt_exp_neg_three [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) {growth : ℝ}
    (hgrowth : growth ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    growth * (1 / 2 : ℝ) ^
        (P.lemmaFourRadius N 0 *
          (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)) <
      Real.exp (-(3 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  apply mul_two_inv_pow_lt_exp_neg_of_add_lt_count_log hgrowth
  have hcount := P.five_mul_initialOuterExponent_lt_count_mul_log_two hN
  linarith

/-- The radius/gap factor in the integral outer-contour remainder costs at
most `3/2`.  This is the literal expression produced by the Cauchy kernel at
radius `3R`, after the numerator and boundary nodal products are bounded by
`R^n` and `(2R)^n`. -/
theorem integralOuter_geometricFactor_le_three_halves
    {R l n : ℕ} (hR : 0 < R) (hl : l ≤ R)
    {outer : ℝ} (houter : 0 ≤ outer) :
    (3 * (R : ℝ)) *
        (((((R : ℝ) / (2 * R)) ^ n) * outer) /
          (3 * (R : ℝ) - l)) ≤
      (3 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * outer) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hlreal : (l : ℝ) ≤ R := by exact_mod_cast hl
  have hgap : 2 * (R : ℝ) ≤ 3 * R - l := by linarith
  have hgapPos : 0 < 3 * (R : ℝ) - l :=
    (mul_pos (by norm_num) hRreal).trans_le hgap
  have hbase : (R : ℝ) / (2 * R) = 1 / 2 := by
    field_simp
  rw [hbase]
  let X : ℝ := (1 / 2 : ℝ) ^ n * outer
  have hX : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hdiv : X / (3 * (R : ℝ) - l) ≤ X / (2 * R) := by
    exact div_le_div₀ hX le_rfl (mul_pos (by norm_num) hRreal) hgap
  calc
    (3 * (R : ℝ)) * (X / (3 * (R : ℝ) - l)) ≤
        (3 * R) * (X / (2 * R)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = (3 / 2 : ℝ) * X := by field_simp

/-- Complete honest initial-stage outer-remainder estimate.  A source
growth loss of `exp(2H)`, the exact floored nodal quotient, and the geometric
`3/2` factor leave the strict bound `exp(-2H)`. -/
theorem initialOuterRemainder_lt_exp_neg_two [Nonempty ι]
    {N l : ℕ} (hN : P.LevelOK N)
    (hl : l ≤ P.lemmaFourRadius N 1) {outer : ℝ}
    (houter : 0 ≤ outer)
    (hgrowth : outer ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 * (P.lemmaFourRadius N 1 : ℝ)) *
        (((((P.lemmaFourRadius N 1 : ℝ) /
          (2 * P.lemmaFourRadius N 1)) ^
            (P.lemmaFourRadius N 0 *
              (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1))) *
          outer) / (3 * (P.lemmaFourRadius N 1 : ℝ) - l)) <
      Real.exp (-(2 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let n : ℕ := P.lemmaFourRadius N 0 *
    (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)
  have hR : 0 < P.lemmaFourRadius N 1 := by
    exact (P.R_pos (N + 1)).trans_le
      (P.R_succ_le_lemmaFourRadius_one N)
  have hgeom := integralOuter_geometricFactor_le_three_halves hR hl houter
    (n := n)
  have hdecay : outer * (1 / 2 : ℝ) ^ n < Real.exp (-(3 * H)) := by
    simpa only [H, n, mul_comm] using
      P.mul_initialOuterFactor_lt_exp_neg_three hN hgrowth
  have hOmegaOld : (2 : ℝ) ≤ P.OmegaOld := by
    exact (show (2 : ℝ) ≤ P.rank by
      exact_mod_cast P.two_le_rank).trans P.rank_le_OmegaOld
  have hOmega : (2 : ℝ) ≤ P.Omega := by
    unfold VDPLParameters.Omega
    nlinarith [P.one_le_log_newHeight, P.log_newHeight_pos]
  have hlog : (1 / 2 : ℝ) ≤ Real.log P.OmegaOld :=
    (by nlinarith [Real.log_two_gt_d9] :
      (1 / 2 : ℝ) ≤ Real.log 2).trans P.log_two_le_log_OmegaOld
  have hH : (1 : ℝ) ≤ H := by
    dsimp only [H]
    have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.h_pos
    have hk : (1 : ℝ) ≤ P.k := P.one_le_k
    have hhk : (1 : ℝ) ≤ (P.h : ℝ) * P.k := by
      nlinarith [mul_le_mul hh hk (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ P.h)]
    have hOlog : (1 : ℝ) ≤ P.Omega * Real.log P.OmegaOld := by
      nlinarith [mul_le_mul hOmega hlog
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by positivity : (0 : ℝ) ≤ P.Omega)]
    nlinarith [mul_le_mul hhk hOlog (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ P.h) P.k_pos.le)]
  have hthreeHalves : (3 / 2 : ℝ) < Real.exp H := by
    calc
      (3 / 2 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      _ ≤ Real.exp H := Real.exp_le_exp.mpr hH
  calc
    (3 * (P.lemmaFourRadius N 1 : ℝ)) *
        (((((P.lemmaFourRadius N 1 : ℝ) /
          (2 * P.lemmaFourRadius N 1)) ^ n) * outer) /
            (3 * (P.lemmaFourRadius N 1 : ℝ) - l)) ≤
        (3 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * outer) := hgeom
    _ < (3 / 2 : ℝ) * Real.exp (-(3 * H)) := by
      have hdecay' : (1 / 2 : ℝ) ^ n * outer < Real.exp (-(3 * H)) := by
        simpa only [mul_comm] using hdecay
      exact mul_lt_mul_of_pos_left hdecay' (by norm_num)
    _ < Real.exp H * Real.exp (-(3 * H)) :=
      mul_lt_mul_of_pos_right hthreeHalves (Real.exp_pos _)
    _ = Real.exp (-(2 * H)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Two errors with a common exponential exponent can be absorbed into a
weaker exponent once the gap exceeds `log 2`. -/
theorem add_lt_exp_neg_of_le_exp_neg
    {x y strong weak : ℝ}
    (hx : x ≤ Real.exp (-strong)) (hy : y ≤ Real.exp (-strong))
    (hgap : Real.log 2 < strong - weak) :
    x + y < Real.exp (-weak) := by
  have htwo : x + y ≤ 2 * Real.exp (-strong) := by linarith
  have hlog : Real.log 2 - strong < -weak := by linarith
  have hexp : Real.exp (Real.log 2 - strong) < Real.exp (-weak) :=
    Real.exp_lt_exp.mpr hlog
  calc
    x + y ≤ 2 * Real.exp (-strong) := htwo
    _ = Real.exp (Real.log 2 - strong) := by
      rw [sub_eq_add_neg, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < Real.exp (-weak) := hexp

/-- A multiplicative power loss can be absorbed into an exponential gap.
This is the form used for the nodal-product factors in Lemmas 4, 5, and the
p. 52 coprime completion. -/
theorem mul_pow_exp_neg_le_exp_neg
    {a strong weak : ℝ} {n : ℕ}
    (ha : 0 < a)
    (hgap : (n : ℝ) * Real.log a - strong ≤ -weak) :
    a ^ n * Real.exp (-strong) ≤ Real.exp (-weak) := by
  calc
    a ^ n * Real.exp (-strong) =
        Real.exp (Real.log a) ^ n * Real.exp (-strong) := by
      rw [Real.exp_log ha]
    _ = Real.exp ((n : ℝ) * Real.log a) * Real.exp (-strong) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp ((n : ℝ) * Real.log a - strong) := by
      rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ Real.exp (-weak) := Real.exp_le_exp.mpr hgap

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.four_mul_Slevel_succ_lt_three_mul_Sstep_of_LevelOK
#print axioms Erdos240.VDPLParameters.Slevel_succ_add_Sstep_div_four_le_of_LevelOK
#print axioms Erdos240.VDPLParameters.withSourceRequirements_eightyOne_lt_k_rpow
#print axioms Erdos240.VDPLParameters.withSourceRequirements_ten_div_epsilon_lt_k_rpow
#print axioms Erdos240.VDPLParameters.q_dvd_R_succ
#print axioms Erdos240.VDPLParameters.three_mul_sourceExponent_lt_coprime_decayExponent
#print axioms Erdos240.VDPLParameters.five_mul_sourceExponent_lt_coprime_decayExponent
#print axioms Erdos240.VDPLParameters.coprime_decay_pow_lt_exp_neg_three_sourceExponent
#print axioms Erdos240.VDPLParameters.coprime_decay_pow_lt_exp_neg_five_sourceExponent
#print axioms Erdos240.VDPLParameters.mul_coprime_decay_lt_exp_neg_three_sourceExponent
#print axioms Erdos240.VDPLParameters.oneTwentyEight_le_k_rpow_half
#print axioms Erdos240.VDPLParameters.lemmaFive_explicitHermiteFactor_le_exp_twelfth
#print axioms Erdos240.VDPLParameters.lemmaFive_localCircleFactor_le_exp_twelfth
#print axioms Erdos240.VDPLParameters.lemmaFour_localCircleFactor_le_exp_sixth
#print axioms Erdos240.VDPLParameters.thirty_mul_sourceHeightUnit_lt_lemmaFive_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_twentySeven
#print axioms Erdos240.VDPLParameters.five_mul_initialOuterExponent_lt_count_mul_log_two
#print axioms Erdos240.VDPLParameters.mul_initialOuterFactor_lt_exp_neg_three
#print axioms Erdos240.VDPLParameters.initialOuterRemainder_lt_exp_neg_two
#print axioms Erdos240.VDPLParameters.add_lt_exp_neg_of_le_exp_neg
