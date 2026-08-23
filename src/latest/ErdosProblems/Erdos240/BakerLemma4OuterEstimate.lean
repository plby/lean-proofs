/- leanprover/lean4:v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.InterpolationProducts
import ErdosProblems.Erdos240.BakerAdmissibleParameters

/-!
# The sharp outer nodal quotient in source Lemma 4

On the outer circle of radius `3 * Rnext`, a new integral target
`Rold < l <= Rnext` gives the pointwise factor `1 / 3` at every old node.
This is sharper than the uniform `1 / 2` estimate valid on the whole interval:
the strict separation `r < l` retains the same node `r` in the numerator and
denominator.  The resulting power `3 ^ (-(Rold * S))` is the factor printed
in van der Poorten--Loxton's proof of Lemma 4.
-/

open scoped BigOperators

open Complex Finset

noncomputable section

namespace Erdos240.InterpolationProducts

/-- At a new integral target, the distance to an old node is at most one
third of the distance from the outer circle to that same node. -/
theorem three_mul_norm_target_sub_node_le_outer
    {Rold Rnext l r : ℕ} {z : ℂ}
    (hr : r ≤ Rold) (hRold : Rold < l) (hl : l ≤ Rnext)
    (hz : ‖z‖ = 3 * Rnext) :
    3 * ‖(l : ℂ) - (r : ℂ)‖ ≤ ‖z - (r : ℂ)‖ := by
  have hrl : r ≤ l := hr.trans hRold.le
  have hnum : ‖(l : ℂ) - (r : ℂ)‖ = (l : ℝ) - r := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hrl)
  have hrnext : (r : ℝ) ≤ Rnext := by
    exact_mod_cast hr.trans (hRold.le.trans hl)
  have hden : 3 * (Rnext : ℝ) - r ≤ ‖z - (r : ℂ)‖ := by
    calc
      3 * (Rnext : ℝ) - r = ‖z‖ - ‖(r : ℂ)‖ := by
        simp only [hz, Complex.norm_natCast]
      _ ≤ ‖z - (r : ℂ)‖ := norm_sub_norm_le _ _
  rw [hnum]
  have hnumden : 3 * ((l : ℝ) - r) ≤ 3 * Rnext - r := by
    have hl' : (l : ℝ) ≤ Rnext := by exact_mod_cast hl
    linarith
  exact hnumden.trans hden

/-- The literal `3^(-Rold*S)` outer quotient from source equation (9).
The target must be genuinely new; old targets are already covered by the
induction hypothesis and do not need interpolation. -/
theorem norm_integralNodalProduct_newTarget_div_outerCircle_le
    {Rold Rnext S l : ℕ} {z : ℂ}
    (hRold : Rold < l) (hl : l ≤ Rnext)
    (hz : ‖z‖ = 3 * Rnext) :
    ‖integralNodalProduct Rold S (l : ℂ) /
        integralNodalProduct Rold S z‖ ≤
      (1 / 3 : ℝ) ^ (Rold * S) := by
  rw [integralNodalProduct, integralNodalProduct,
    ← Finset.prod_div_distrib, norm_prod]
  calc
    ∏ i ∈ range Rold,
        ‖((l : ℂ) - (i + 1 : ℕ)) ^ S /
          (z - (i + 1 : ℕ)) ^ S‖ ≤
        ∏ _i ∈ range Rold, (1 / 3 : ℝ) ^ S := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hir : i + 1 ≤ Rold := Nat.succ_le_iff.mpr (mem_range.mp hi)
        have hdist := three_mul_norm_target_sub_node_le_outer
          hir hRold hl hz
        have hden : 0 < ‖z - ((i + 1 : ℕ) : ℂ)‖ := by
          have hnode : ((i + 1 : ℕ) : ℝ) < 3 * Rnext := by
            have hiRnext : i + 1 ≤ Rnext :=
              hir.trans (hRold.le.trans hl)
            have hRnext : 0 < Rnext := lt_of_lt_of_le (by omega) hl
            exact_mod_cast (show i + 1 < 3 * Rnext by omega)
          rw [norm_pos_iff, sub_ne_zero]
          intro h
          have := congrArg norm h
          simp only [hz, Complex.norm_natCast] at this
          linarith
        have hbase :
            ‖((l : ℂ) - (i + 1 : ℕ)) /
                (z - (i + 1 : ℕ))‖ ≤ (1 / 3 : ℝ) := by
          rw [norm_div, div_le_iff₀ hden]
          nlinarith
        rw [← div_pow, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hbase S
    _ = (1 / 3 : ℝ) ^ (Rold * S) := by
      rw [Finset.prod_const, card_range, mul_comm Rold S, pow_mul]

end Erdos240.InterpolationProducts

namespace Erdos240.VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-! ## The genuine-stage node count -/

/-- The Lemma-4 derivative budget is nonincreasing.  This local copy keeps
the sharp outer estimate independent of the larger numerical-assembly
module. -/
theorem outer_lemmaFourBudget_succ_le_current (N t : ℕ) :
    P.lemmaFourBudget N (t + 1) ≤ P.lemmaFourBudget N t := by
  cases t with
  | zero =>
      simp only [Nat.zero_add, P.lemmaFourBudget_zero,
        P.lemmaFourBudget_one]
      have hfloor :
          ((⌊(P.Slevel N : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤
            (P.Slevel N : ℝ) / 2 := Nat.floor_le (by positivity)
      have hhalf : (P.Slevel N : ℝ) / 2 ≤ P.Slevel N := by
        have hnonneg : (0 : ℝ) ≤ P.Slevel N := by positivity
        linarith
      exact_mod_cast hfloor.trans hhalf
  | succ t =>
      have htpos : 1 ≤ t + 1 := by omega
      have hepslt : P.epsilon < 1 := by
        rw [P.epsilon_eq]
        have hm : (1 : ℝ) ≤ P.rank + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
        apply (div_lt_one (by positivity :
          (0 : ℝ) < 6 * (P.rank + 1))).2
        nlinarith
      have harg : 0 ≤ (1 - P.epsilon) *
          (P.lemmaFourBudget N (t + 1) : ℝ) := by positivity
      have hfloor :
          ((⌊(1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ)⌋₊ : ℕ) : ℝ) ≤
            (1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ) := Nat.floor_le harg
      have hmul : (1 - P.epsilon) *
          (P.lemmaFourBudget N (t + 1) : ℝ) ≤
          P.lemmaFourBudget N (t + 1) := by
        have hbudget : (0 : ℝ) ≤ P.lemmaFourBudget N (t + 1) := by positivity
        nlinarith [P.epsilon_pos]
      rw [show t + 1 + 1 = t + 2 by omega,
        P.lemmaFourBudget_succ_succ,
        P.lemmaFourEpsilon_eq_epsilon htpos]
      exact_mod_cast hfloor.trans hmul

/-- A floor-robust lower bound for every positive Lemma-4 budget before the
terminal stage.  The numerical constant `31/128` deliberately retains the
floor losses: the source's linear recursion gives essentially one quarter
of `levelScale`, while admissibility makes the total accumulated loss less
than `levelScale / 128`. -/
theorem thirtyOne_div_oneTwentyEight_mul_levelScale_lt_lemmaFourBudget
    [Nonempty ι] {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1)) :
    (31 / 128 : ℝ) * P.levelScale N < P.lemmaFourBudget N t := by
  let x : ℝ := P.levelScale N
  let m : ℝ := P.rank + 1
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
  have hx : 512 * m < x := by
    simpa only [x, m] using
      P.fiveHundredTwelve_mul_rank_add_one_lt_levelScale hN
  have hS : 2 ≤ P.Slevel N := by
    unfold Slevel
    apply Nat.le_floor
    have : (2 : ℝ) ≤ 512 * m := by nlinarith
    exact this.trans hx.le
  have htcast : (t : ℝ) ≤ 3 * m := by
    have ht' : t ≤ 3 * (P.rank + 1) := Nat.le_of_lt ht
    dsimp only [m]
    exact_mod_cast ht'
  have hteps : (t : ℝ) * P.epsilon ≤ 1 / 2 := by
    rw [P.epsilon_eq]
    calc
      (t : ℝ) * (1 / (6 * (P.rank + 1 : ℝ))) =
          (t : ℝ) / (6 * m) := by dsimp only [m]; ring
      _ ≤ (3 * m) / (6 * m) :=
        div_le_div_of_nonneg_right htcast (by positivity)
      _ = 1 / 2 := by field_simp <;> norm_num
  have hlower := P.lemmaFourBudget_lower_linear N t hS htpos hteps
  have hcoeff : (1 / 2 : ℝ) ≤
      1 - ((t : ℝ) - 1) * P.epsilon := by
    nlinarith [P.epsilon_pos]
  have hA : 0 ≤ (P.Slevel N : ℝ) / 2 - 1 := by
    have hSreal : (2 : ℝ) ≤ P.Slevel N := by exact_mod_cast hS
    linarith
  have hfloor : x - 1 < (P.Slevel N : ℝ) := by
    dsimp only [x]
    linarith [P.levelScale_lt_Slevel_add_one N]
  have htbound : (t : ℝ) < 3 * m := by
    dsimp only [m]
    exact_mod_cast ht
  have hcoarse :
      (1 / 2 : ℝ) * ((P.Slevel N : ℝ) / 2 - 1) -
          ((t : ℝ) - 1) < P.lemmaFourBudget N t := by
    exact (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hcoeff hA) _).trans_lt hlower
  dsimp only [x, m] at hx htbound ⊢
  dsimp only [x] at hfloor
  push_cast at hcoarse
  nlinarith

/-- At every positive stage the source recursion is multiplication by
`1-epsilon` followed by a floor.  Consequently the exact Hermite
multiplicity `S_t-S_(t+1)+1` is strictly larger than `epsilon*S_t`; the
strictness absorbs the floor without any auxiliary error term. -/
theorem epsilon_mul_lemmaFourBudget_lt_stageMultiplicity
    [Nonempty ι] {N t : ℕ} (htpos : 1 ≤ t) :
    P.epsilon * P.lemmaFourBudget N t <
      (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1 : ℕ) := by
  cases t with
  | zero => omega
  | succ u =>
      have heq := P.lemmaFourEpsilon_eq_epsilon (J := u + 1) (by omega)
      have hepslt : P.epsilon < 1 := by
        rw [P.epsilon_eq]
        have hm : (1 : ℝ) ≤ P.rank + 1 := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
        apply (div_lt_one (by positivity :
          (0 : ℝ) < 6 * (P.rank + 1))).2
        nlinarith
      have harg : 0 ≤
          (1 - P.epsilon) * (P.lemmaFourBudget N (u + 1) : ℝ) := by
        positivity
      have hnext :
          (P.lemmaFourBudget N (u + 2) : ℝ) ≤
            (1 - P.epsilon) * (P.lemmaFourBudget N (u + 1) : ℝ) := by
        rw [P.lemmaFourBudget_succ_succ, heq]
        exact Nat.floor_le harg
      have hmono := P.outer_lemmaFourBudget_succ_le_current N (u + 1)
      rw [show u + 1 + 1 = u + 2 by omega]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hmono]
      nlinarith

/-- The floor in the source radius loses less than one unit.  Since the
remaining factors are all at least one, `floor(16*A)` is still strictly
larger than `15*A`. -/
theorem fifteen_mul_radiusCore_lt_lemmaFourRadius [Nonempty ι]
    (N t : ℕ) :
    15 * (((P.q ^ N : ℕ) : ℝ) * P.h *
        P.k ^ (P.epsilon * (t : ℝ))) < P.lemmaFourRadius N t := by
  let A : ℝ := ((P.q ^ N : ℕ) : ℝ) * P.h *
    P.k ^ (P.epsilon * (t : ℝ))
  have hq : (1 : ℝ) ≤ (P.q ^ N : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero N (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)))
  have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.h_pos
  have hkpow : (1 : ℝ) ≤ P.k ^ (P.epsilon * (t : ℝ)) := by
    exact Real.one_le_rpow P.one_le_k
      (mul_nonneg P.epsilon_pos.le (Nat.cast_nonneg t))
  have hA : 1 ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ ((P.q ^ N : ℕ) : ℝ) * P.h *
          P.k ^ (P.epsilon * (t : ℝ)) := by gcongr
  have hfloor := Nat.lt_floor_add_one (P.lemmaFourRadiusScale N t)
  have hscale : P.lemmaFourRadiusScale N t = 16 * A := by
    unfold lemmaFourRadiusScale
    dsimp only [A]
    ring
  unfold lemmaFourRadius
  rw [hscale] at hfloor
  rw [hscale]
  dsimp only [A] at hA ⊢
  push_cast at hfloor
  nlinarith

/-- In the specialization `mu=1`, the exponent in the source's third
parameter requirement is exactly `3*epsilon`. -/
theorem ten_div_epsilon_lt_k_rpow_three_mul_epsilon
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    10 / P.epsilon < P.k ^ (3 * P.epsilon) := by
  let e : ℝ := (1 + P.mu) * (P.rank + 1 : ℝ)
  have he : 0 < e := by
    dsimp only [e]
    rw [P.mu_eq]
    positivity
  have hbase : 0 < (10 : ℝ) / P.epsilon :=
    div_pos (by norm_num) P.epsilon_pos
  have hraw : P.sourceTenThreshold < P.k := P.requirement_lt_k hreq
  have hrpow := Real.rpow_lt_rpow
    (Real.rpow_nonneg hbase.le e) hraw (one_div_pos.mpr he)
  have hroot :
      ((10 / P.epsilon : ℝ) ^ e) ^ (1 / e) = 10 / P.epsilon := by
    rw [← Real.rpow_mul hbase.le]
    rw [mul_one_div_cancel he.ne', Real.rpow_one]
  unfold sourceTenThreshold at hraw
  change ((10 / P.epsilon : ℝ) ^ e) < P.k at hraw
  rw [hroot] at hrpow
  have h : 10 / P.epsilon < P.k ^ (1 / e) := hrpow
  have hexponent :
      3 * P.epsilon =
        1 / ((1 + P.mu) * (P.rank + 1 : ℝ)) := by
    rw [P.mu_eq, P.epsilon_eq]
    have hm : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    ring
  rw [hexponent]
  simpa only [e] using h

/-- Combining the budget lower bound with the exact floor loss in the
successor recursion gives the source multiplicity at its natural scale. -/
theorem thirtyOne_div_oneTwentyEight_mul_epsilon_mul_levelScale_lt_stageMultiplicity
    [Nonempty ι] {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1)) :
    (31 / 128 : ℝ) * P.epsilon * P.levelScale N <
      (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1 : ℕ) := by
  have hbudget :=
    P.thirtyOne_div_oneTwentyEight_mul_levelScale_lt_lemmaFourBudget
      hN htpos ht
  have hscaled := mul_lt_mul_of_pos_left hbudget P.epsilon_pos
  have hmult := P.epsilon_mul_lemmaFourBudget_lt_stageMultiplicity
    (N := N) htpos
  calc
    (31 / 128 : ℝ) * P.epsilon * P.levelScale N =
        P.epsilon * ((31 / 128 : ℝ) * P.levelScale N) := by ring
    _ < P.epsilon * P.lemmaFourBudget N t := hscaled
    _ < (P.lemmaFourBudget N t -
        P.lemmaFourBudget N (t + 1) + 1 : ℕ) := hmult

/-- Source positive-stage node count before taking the logarithm.  This is
the exact product of the floored radius and the Hermite multiplicity; the
constant `465/128 = 15*(31/128)` retains every floor loss. -/
theorem positiveStage_rawExponent_lt_nodeCount [Nonempty ι]
    {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1)) :
    (465 / 128 : ℝ) * P.epsilon * (P.h : ℝ) *
        P.k ^ (1 + P.epsilon * (t : ℝ)) *
        (P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFourRadius N t *
        (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1) : ℕ) : ℝ) := by
  let Q : ℝ := ((P.q ^ N : ℕ) : ℝ)
  let Kt : ℝ := P.k ^ (P.epsilon * (t : ℝ))
  let T : ℕ := P.lemmaFourBudget N t -
    P.lemmaFourBudget N (t + 1) + 1
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) N
  have hKt : 0 < Kt := by
    exact Real.rpow_pos_of_pos P.k_pos _
  have hR : 15 * (Q * P.h * Kt) < P.lemmaFourRadius N t := by
    simpa only [Q, Kt] using P.fifteen_mul_radiusCore_lt_lemmaFourRadius N t
  have hT : (31 / 128 : ℝ) * P.epsilon * P.levelScale N < T := by
    simpa only [T] using
      P.thirtyOne_div_oneTwentyEight_mul_epsilon_mul_levelScale_lt_stageMultiplicity
        hN htpos ht
  have hTpos : 0 < (31 / 128 : ℝ) * P.epsilon * P.levelScale N := by
    exact mul_pos
      (mul_pos (by norm_num) P.epsilon_pos) (P.levelScale_pos N)
  have hRpos : 0 < (P.lemmaFourRadius N t : ℝ) :=
    (mul_pos (by positivity) (mul_pos (mul_pos hQ (by exact_mod_cast P.h_pos)) hKt)).trans hR
  have hproduct :
      (15 * (Q * P.h * Kt)) *
          ((31 / 128 : ℝ) * P.epsilon * P.levelScale N) <
        (P.lemmaFourRadius N t : ℝ) * T := by
    calc
      (15 * (Q * P.h * Kt)) *
          ((31 / 128 : ℝ) * P.epsilon * P.levelScale N) <
          (P.lemmaFourRadius N t : ℝ) *
            ((31 / 128 : ℝ) * P.epsilon * P.levelScale N) :=
        mul_lt_mul_of_pos_right hR hTpos
      _ < (P.lemmaFourRadius N t : ℝ) * T :=
        mul_lt_mul_of_pos_left hT hRpos
  have hK : Kt * P.k = P.k ^ (1 + P.epsilon * (t : ℝ)) := by
    dsimp only [Kt]
    calc
      P.k ^ (P.epsilon * (t : ℝ)) * P.k =
          P.k ^ (P.epsilon * (t : ℝ)) * P.k ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = P.k ^ (P.epsilon * (t : ℝ) + 1) := by
            rw [Real.rpow_add P.k_pos]
      _ = P.k ^ (1 + P.epsilon * (t : ℝ)) := by ring_nf
  have hidentity :
      (15 * (Q * P.h * Kt)) *
          ((31 / 128 : ℝ) * P.epsilon * P.levelScale N) =
        (465 / 128 : ℝ) * P.epsilon * (P.h : ℝ) *
          P.k ^ (1 + P.epsilon * (t : ℝ)) *
          (P.Omega * Real.log P.OmegaOld) := by
    unfold levelScale qInvPow
    dsimp only [Q] at hQ
    dsimp only [Q]
    rw [show (((P.q ^ N : ℕ) : ℝ))⁻¹ =
      1 / ((P.q ^ N : ℕ) : ℝ) by rw [one_div]]
    field_simp [hQ.ne']
    dsimp only [Kt] at hK ⊢
    rw [← hK]
    ring
  rw [hidentity] at hproduct
  simpa only [T, Nat.cast_mul] using hproduct

/-- The baseline seed pays the fixed `4k` part of the positive-stage outer
growth.  This is the first of the two source allocations below the exact
`465/128` node-count coefficient. -/
theorem four_mul_k_le_three_eighth_mul_epsilon_mul_stagePower
    [Nonempty ι] {t : ℕ} (htpos : 1 ≤ t) :
    4 * P.k ≤ (3 / 8 : ℝ) * P.epsilon *
      P.k ^ (1 + P.epsilon * (t : ℝ)) := by
  have hseed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have htcast : (1 : ℝ) ≤ t := by exact_mod_cast htpos
  have hexp : P.epsilon ≤ P.epsilon * (t : ℝ) := by
    nlinarith [P.epsilon_pos]
  have hmono : P.k ^ P.epsilon ≤
      P.k ^ (P.epsilon * (t : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hexp
  have hepsSeed : (32 / 3 : ℝ) ≤ P.epsilon * P.kSeedBase := by
    rw [P.epsilon_eq]
    unfold kSeedBase
    have hm : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp <;> norm_num
  have hepsStage : (32 / 3 : ℝ) ≤
      P.epsilon * P.k ^ (P.epsilon * (t : ℝ)) :=
    hepsSeed.trans <| mul_le_mul_of_nonneg_left
      (hseed.trans hmono) P.epsilon_pos.le
  have hmul := mul_le_mul_of_nonneg_left hepsStage P.k_pos.le
  have hpower : P.k * P.k ^ (P.epsilon * (t : ℝ)) =
      P.k ^ (1 + P.epsilon * (t : ℝ)) := by
    calc
      P.k * P.k ^ (P.epsilon * (t : ℝ)) =
          P.k ^ (1 : ℝ) * P.k ^ (P.epsilon * (t : ℝ)) := by
            rw [Real.rpow_one]
      _ = P.k ^ (1 + P.epsilon * (t : ℝ)) := by
            rw [Real.rpow_add P.k_pos]
  rw [← hpower]
  nlinarith

/-- The third printed p.39 requirement pays the varying-stage term.  The
identity behind the proof is
`1+epsilon*t = (1-sigma+epsilon*(t+1)) + 3*epsilon`. -/
theorem thirtyTwo_mul_nextStagePower_lt_sixteen_fifths_mul_epsilon_mul_stagePower
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) (t : ℕ) :
    32 * P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) <
      (16 / 5 : ℝ) * P.epsilon *
        P.k ^ (1 + P.epsilon * (t : ℝ)) := by
  let Knext : ℝ :=
    P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))
  have hthird := P.ten_div_epsilon_lt_k_rpow_three_mul_epsilon hreq
  have hfactor : 32 < (16 / 5 : ℝ) * P.epsilon *
      P.k ^ (3 * P.epsilon) := by
    have hm := mul_lt_mul_of_pos_left hthird
      (mul_pos (by norm_num : (0 : ℝ) < 16 / 5) P.epsilon_pos)
    have hepsne : P.epsilon ≠ 0 := P.epsilon_pos.ne'
    calc
      (32 : ℝ) = (16 / 5 : ℝ) * P.epsilon *
          (10 / P.epsilon) := by field_simp [hepsne]; ring
      _ < (16 / 5 : ℝ) * P.epsilon *
          P.k ^ (3 * P.epsilon) := hm
  have hsplit : Knext * P.k ^ (3 * P.epsilon) =
      P.k ^ (1 + P.epsilon * (t : ℝ)) := by
    dsimp only [Knext]
    rw [← Real.rpow_add P.k_pos]
    congr 1
    rw [P.sigma_eq, P.epsilon_eq]
    push_cast
    have hm : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    ring
  have hKnext : 0 < Knext := Real.rpow_pos_of_pos P.k_pos _
  have hmul := mul_lt_mul_of_pos_left hfactor hKnext
  dsimp only [Knext] at hmul ⊢
  rw [← hsplit]
  nlinarith

/-- The natural positive-stage exponent is already much larger than one.
This explicit lower bound pays the `3/2` geometric factor in the normalized
outer integral without consuming any asymptotic slack. -/
theorem ninety_lt_positiveStageExponent [Nonempty ι]
    {t : ℕ} (htpos : 1 ≤ t) :
    (90 : ℝ) < P.epsilon * (P.h : ℝ) *
      P.k ^ (1 + P.epsilon * (t : ℝ)) *
      (P.Omega * Real.log P.OmegaOld) := by
  have hseed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have htcast : (1 : ℝ) ≤ t := by exact_mod_cast htpos
  have hexp : P.epsilon ≤ P.epsilon * (t : ℝ) := by
    nlinarith [P.epsilon_pos]
  have hmono : P.k ^ P.epsilon ≤
      P.k ^ (P.epsilon * (t : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hexp
  have hepsSeed : (32 / 3 : ℝ) ≤ P.epsilon * P.kSeedBase := by
    rw [P.epsilon_eq]
    unfold kSeedBase
    have hm : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp <;> norm_num
  have hepsStage : (32 / 3 : ℝ) ≤
      P.epsilon * P.k ^ (P.epsilon * (t : ℝ)) :=
    hepsSeed.trans <| mul_le_mul_of_nonneg_left
      (hseed.trans hmono) P.epsilon_pos.le
  have hepsOne : P.epsilon ≤ 1 := by
    rw [P.epsilon_eq]
    have hm : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    apply (div_le_one (by positivity :
      (0 : ℝ) < 6 * (P.rank + 1))).2
    nlinarith
  have hkEps : P.k ^ P.epsilon ≤ P.k := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsOne
  have hk13 : (13 : ℝ) ≤ P.k := by
    calc
      (13 : ℝ) = P.q := by norm_num [q]
      _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
      _ ≤ P.k := hkEps
  have hlog : (2 / 3 : ℝ) ≤ Real.log P.OmegaOld := by
    exact (by nlinarith [Real.log_two_gt_d9] :
      (2 / 3 : ℝ) ≤ Real.log 2).trans P.log_two_le_log_OmegaOld
  have hW : (2 / 3 : ℝ) ≤ P.Omega * Real.log P.OmegaOld := by
    calc
      (2 / 3 : ℝ) = 1 * (2 / 3 : ℝ) := by ring
      _ ≤ P.Omega * Real.log P.OmegaOld :=
        mul_le_mul P.one_le_Omega hlog (by norm_num) P.Omega_pos.le
  have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.h_pos
  have hlarge :
      (13 : ℝ) * (32 / 3) * 1 * (2 / 3) ≤
        P.k * (P.epsilon * P.k ^ (P.epsilon * (t : ℝ))) *
          P.h * (P.Omega * Real.log P.OmegaOld) := by
    gcongr
  have hpower : P.k * P.k ^ (P.epsilon * (t : ℝ)) =
      P.k ^ (1 + P.epsilon * (t : ℝ)) := by
    calc
      P.k * P.k ^ (P.epsilon * (t : ℝ)) =
          P.k ^ (1 : ℝ) * P.k ^ (P.epsilon * (t : ℝ)) := by
            rw [Real.rpow_one]
      _ = P.k ^ (1 + P.epsilon * (t : ℝ)) := by
            rw [Real.rpow_add P.k_pos]
  calc
    (90 : ℝ) < 13 * (32 / 3 : ℝ) * 1 * (2 / 3) := by norm_num
    _ ≤ P.k * (P.epsilon * P.k ^ (P.epsilon * (t : ℝ))) *
        P.h * (P.Omega * Real.log P.OmegaOld) := hlarge
    _ = P.epsilon * (P.h : ℝ) *
        P.k ^ (1 + P.epsilon * (t : ℝ)) *
        (P.Omega * Real.log P.OmegaOld) := by rw [← hpower]; ring

/-- Complete logarithmic node-count inequality for every genuine positive
stage of source Lemma 4.  Its left side is exactly the target exponent, the
outer growth exponent, and the one extra unit which absorbs the normalized
Cauchy factor `3/2`; its right side is the exact floored node count times
`log 3`. -/
theorem positiveStage_outerExponent_add_growth_add_one_lt_count_mul_log_three
    [Nonempty ι] {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1))
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    ((4 * (P.h : ℝ) * P.k +
        32 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld)) + 1 <
      ((P.lemmaFourRadius N t *
        (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1) : ℕ) : ℝ) *
        Real.log 3 := by
  let Kfull : ℝ := P.k ^ (1 + P.epsilon * (t : ℝ))
  let Knext : ℝ :=
    P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  let E : ℝ := P.epsilon * (P.h : ℝ) * Kfull * W
  let count : ℕ := P.lemmaFourRadius N t *
    (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)
  have hW : 0 < W := by
    exact mul_pos P.Omega_pos P.log_OmegaOld_pos
  have hhW : 0 < (P.h : ℝ) * W :=
    mul_pos (by exact_mod_cast P.h_pos) hW
  have h4 := P.four_mul_k_le_three_eighth_mul_epsilon_mul_stagePower htpos
  have h32 :=
    P.thirtyTwo_mul_nextStagePower_lt_sixteen_fifths_mul_epsilon_mul_stagePower
      hreq t
  have hallocation : 4 * P.k + 32 * Knext <
      (143 / 40 : ℝ) * P.epsilon * Kfull := by
    dsimp only [Kfull, Knext]
    nlinarith
  have hallocationScaled := mul_lt_mul_of_pos_right hallocation hhW
  have hElarge : (90 : ℝ) < E := by
    dsimp only [E, Kfull, W]
    exact P.ninety_lt_positiveStageExponent htpos
  have hslack : (143 / 40 : ℝ) * E + 1 < (465 / 128 : ℝ) * E := by
    nlinarith
  have hleft :
      ((4 * (P.h : ℝ) * P.k + 32 * (P.h : ℝ) * Knext) * W) + 1 <
        (465 / 128 : ℝ) * E := by
    have hscaled :
        (4 * (P.h : ℝ) * P.k + 32 * (P.h : ℝ) * Knext) * W <
          (143 / 40 : ℝ) * E := by
      dsimp only [E]
      calc
        (4 * (P.h : ℝ) * P.k + 32 * (P.h : ℝ) * Knext) * W =
            (4 * P.k + 32 * Knext) * ((P.h : ℝ) * W) := by ring
        _ < ((143 / 40 : ℝ) * P.epsilon * Kfull) *
            ((P.h : ℝ) * W) := hallocationScaled
        _ = (143 / 40 : ℝ) *
            (P.epsilon * (P.h : ℝ) * Kfull * W) := by ring
    linarith
  have hraw : (465 / 128 : ℝ) * E < count := by
    dsimp only [E, Kfull, W, count]
    convert P.positiveStage_rawExponent_lt_nodeCount hN htpos ht using 1 <;>
      ring
  have hcountpos : (0 : ℝ) < count := by
    have hEpos : 0 < E := lt_trans (by norm_num) hElarge
    have hcoef : 0 < (465 / 128 : ℝ) * E := by positivity
    exact hcoef.trans hraw
  have hlog : (1 : ℝ) < Real.log 3 := by
    nlinarith [Real.log_three_gt_d9]
  have hcountlog : (count : ℝ) < count * Real.log 3 := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hlog hcountpos
  dsimp only [Knext, W, count] at hleft hraw hcountlog ⊢
  exact hleft.trans (hraw.trans hcountlog)

/-- A fixed-height form of the positive-stage count.  The source growth
exponent, five source-height units of desired decay, and the normalized
`3/2` loss still fit below the exact `3^(-R*T)` node count.  This is the
form used when the Liouville threshold is uniformly bounded below by
`exp (-4 * sourceHeight)`, independently of the inner stage. -/
theorem positiveStage_fiveHeight_add_growth_add_one_lt_count_mul_log_three
    [Nonempty ι] {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1))
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) + 1 +
        ((2 * (P.h : ℝ) * P.k +
          24 * (P.h : ℝ) *
            P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
          (P.Omega * Real.log P.OmegaOld)) <
      ((P.lemmaFourRadius N t *
        (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1) : ℕ) : ℝ) *
        Real.log 3 := by
  let Kfull : ℝ := P.k ^ (1 + P.epsilon * (t : ℝ))
  let Knext : ℝ :=
    P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  let E : ℝ := P.epsilon * (P.h : ℝ) * Kfull * W
  let count : ℕ := P.lemmaFourRadius N t *
    (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)
  have hW : 0 < W := mul_pos P.Omega_pos P.log_OmegaOld_pos
  have hhW : 0 < (P.h : ℝ) * W :=
    mul_pos (by exact_mod_cast P.h_pos) hW
  have h4 := P.four_mul_k_le_three_eighth_mul_epsilon_mul_stagePower htpos
  have h32 :=
    P.thirtyTwo_mul_nextStagePower_lt_sixteen_fifths_mul_epsilon_mul_stagePower
      hreq t
  have hallocation : 7 * P.k + 24 * Knext <
      (489 / 160 : ℝ) * P.epsilon * Kfull := by
    dsimp only [Kfull, Knext]
    nlinarith
  have hallocationScaled := mul_lt_mul_of_pos_right hallocation hhW
  have hElarge : (90 : ℝ) < E := by
    dsimp only [E, Kfull, W]
    exact P.ninety_lt_positiveStageExponent htpos
  have hslack : (489 / 160 : ℝ) * E + 1 <
      (465 / 128 : ℝ) * E := by
    nlinarith
  have hleft :
      ((7 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) * Knext) * W) + 1 <
        (465 / 128 : ℝ) * E := by
    have hscaled :
        (7 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) * Knext) * W <
          (489 / 160 : ℝ) * E := by
      dsimp only [E]
      calc
        (7 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) * Knext) * W =
            (7 * P.k + 24 * Knext) * ((P.h : ℝ) * W) := by ring
        _ < ((489 / 160 : ℝ) * P.epsilon * Kfull) *
            ((P.h : ℝ) * W) := hallocationScaled
        _ = (489 / 160 : ℝ) *
            (P.epsilon * (P.h : ℝ) * Kfull * W) := by ring
    linarith
  have hraw : (465 / 128 : ℝ) * E < count := by
    dsimp only [E, Kfull, W, count]
    convert P.positiveStage_rawExponent_lt_nodeCount hN htpos ht using 1 <;>
      ring
  have hcountpos : (0 : ℝ) < count := by
    have hEpos : 0 < E := lt_trans (by norm_num) hElarge
    have hcoef : 0 < (465 / 128 : ℝ) * E := by positivity
    exact hcoef.trans hraw
  have hlog : (1 : ℝ) < Real.log 3 := by
    nlinarith [Real.log_three_gt_d9]
  have hcountlog : (count : ℝ) < count * Real.log 3 := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hlog hcountpos
  dsimp only [Knext, W, count] at hleft hraw hcountlog ⊢
  have hshape :
      5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) + 1 +
          ((2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
            P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
            (P.Omega * Real.log P.OmegaOld)) =
        ((7 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
          (P.Omega * Real.log P.OmegaOld)) + 1 := by ring
  rw [hshape]
  exact hleft.trans (hraw.trans hcountlog)

/-- Ready-to-use positive-stage outer-contour decay.  Once the concrete
source majorant supplies the printed growth exponent, the sharp nodal
quotient and the normalized `3/2` Cauchy loss leave the target exponent
needed by the Liouville alternative. -/
theorem positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_target
    [Nonempty ι] {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1))
    (hreq : P.sourceTenThreshold ∈ P.kRequirements)
    {growth : ℝ} (hgrowth0 : 0 ≤ growth)
    (hgrowth : growth ≤ Real.exp
      ((2 * (P.h : ℝ) * P.k +
        24 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 3 : ℝ) ^
          (P.lemmaFourRadius N t *
            (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)) *
          growth) <
      Real.exp (-((2 * (P.h : ℝ) * P.k +
        8 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld))) := by
  let K : ℝ :=
    P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  let D : ℝ := (2 * (P.h : ℝ) * P.k + 8 * (P.h : ℝ) * K) * W
  let G : ℝ := (2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) * K) * W
  let count : ℕ := P.lemmaFourRadius N t *
    (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)
  have hcountSource :=
    P.positiveStage_outerExponent_add_growth_add_one_lt_count_mul_log_three
      hN htpos ht hreq
  have hcount : D + 1 + G < (count : ℝ) * Real.log 3 := by
    dsimp only [D, G, K, W, count]
    convert hcountSource using 1 <;> ring
  have hpow : (1 / 3 : ℝ) ^ count =
      Real.exp (-((count : ℝ) * Real.log 3)) := by
    calc
      (1 / 3 : ℝ) ^ count =
          Real.exp (Real.log (1 / 3 : ℝ)) ^ count := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 3)]
      _ = Real.exp ((count : ℝ) * Real.log (1 / 3 : ℝ)) :=
        (Real.exp_nat_mul (Real.log (1 / 3 : ℝ)) count).symm
      _ = Real.exp (-((count : ℝ) * Real.log 3)) := by
        rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
          rw [one_div, Real.log_inv]]
        congr 1
        ring
  have hgrowth' : growth ≤ Real.exp G := by
    dsimp only [G, K, W]
    exact hgrowth
  have hdecay : growth * (1 / 3 : ℝ) ^ count <
      Real.exp (-(D + 1)) := by
    rw [hpow]
    calc
      growth * Real.exp (-((count : ℝ) * Real.log 3)) ≤
          Real.exp G * Real.exp (-((count : ℝ) * Real.log 3)) :=
        mul_le_mul_of_nonneg_right hgrowth (Real.exp_pos _).le
      _ = Real.exp (G - (count : ℝ) * Real.log 3) := by
        rw [sub_eq_add_neg, Real.exp_add]
      _ < Real.exp (-(D + 1)) := by
        apply Real.exp_lt_exp.mpr
        linarith
  have hfactor : (3 / 2 : ℝ) < Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  dsimp only [D, G, K, W, count] at hdecay ⊢
  calc
    (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^
        (P.lemmaFourRadius N t *
          (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)) *
        growth) =
        (3 / 2 : ℝ) * (growth * (1 / 3 : ℝ) ^
          (P.lemmaFourRadius N t *
            (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1))) := by
      ring
    _ < Real.exp 1 * Real.exp (-(((2 * (P.h : ℝ) * P.k +
        8 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld)) + 1)) :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hfactor.le
          (mul_nonneg hgrowth0 (pow_nonneg (by norm_num) _)))
        (mul_lt_mul_of_pos_left hdecay (Real.exp_pos 1))
    _ = Real.exp (-((2 * (P.h : ℝ) * P.k +
        8 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Ready-to-use fixed-height positive-stage outer-contour decay.  The
printed source growth bound and sharp `3^(-R*T)` quotient leave five full
source-height units, uniformly at every genuine positive inner stage. -/
theorem positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_five
    [Nonempty ι] {N t : ℕ} (hN : P.LevelOK N) (htpos : 1 ≤ t)
    (ht : t < 3 * (P.rank + 1))
    (hreq : P.sourceTenThreshold ∈ P.kRequirements)
    {growth : ℝ} (hgrowth0 : 0 ≤ growth)
    (hgrowth : growth ≤ Real.exp
      ((2 * (P.h : ℝ) * P.k +
        24 * (P.h : ℝ) *
          P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 3 : ℝ) ^
          (P.lemmaFourRadius N t *
            (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)) *
          growth) <
      Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let G : ℝ := (2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
    P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ))) *
    (P.Omega * Real.log P.OmegaOld)
  let count : ℕ := P.lemmaFourRadius N t *
    (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)
  have hcountSource :=
    P.positiveStage_fiveHeight_add_growth_add_one_lt_count_mul_log_three
      hN htpos ht hreq
  have hcount : 5 * H + 1 + G < (count : ℝ) * Real.log 3 := by
    dsimp only [H, G, count]
    exact hcountSource
  have hpow : (1 / 3 : ℝ) ^ count =
      Real.exp (-((count : ℝ) * Real.log 3)) := by
    calc
      (1 / 3 : ℝ) ^ count =
          Real.exp (Real.log (1 / 3 : ℝ)) ^ count := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 3)]
      _ = Real.exp ((count : ℝ) * Real.log (1 / 3 : ℝ)) :=
        (Real.exp_nat_mul (Real.log (1 / 3 : ℝ)) count).symm
      _ = Real.exp (-((count : ℝ) * Real.log 3)) := by
        rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
          rw [one_div, Real.log_inv]]
        congr 1
        ring
  have hgrowth' : growth ≤ Real.exp G := by
    dsimp only [G]
    exact hgrowth
  have hdecay : growth * (1 / 3 : ℝ) ^ count <
      Real.exp (-(5 * H + 1)) := by
    rw [hpow]
    calc
      growth * Real.exp (-((count : ℝ) * Real.log 3)) ≤
          Real.exp G * Real.exp (-((count : ℝ) * Real.log 3)) :=
        mul_le_mul_of_nonneg_right hgrowth' (Real.exp_pos _).le
      _ = Real.exp (G - (count : ℝ) * Real.log 3) := by
        rw [sub_eq_add_neg, Real.exp_add]
      _ < Real.exp (-(5 * H + 1)) := by
        apply Real.exp_lt_exp.mpr
        linarith
  have hfactor : (3 / 2 : ℝ) < Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  dsimp only [H, G, count] at hdecay ⊢
  calc
    (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^
        (P.lemmaFourRadius N t *
          (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1)) *
        growth) =
        (3 / 2 : ℝ) * (growth * (1 / 3 : ℝ) ^
          (P.lemmaFourRadius N t *
            (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1))) := by
      ring
    _ < Real.exp 1 * Real.exp (-(5 *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) + 1)) :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hfactor.le
          (mul_nonneg hgrowth0 (pow_nonneg (by norm_num) _)))
        (mul_lt_mul_of_pos_left hdecay (Real.exp_pos 1))
    _ = Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-! ## The exceptional initial stage -/

/-- The exact initial floored node count supplies five full source-height
units.  This is the `t=0` companion to the positive-stage count above. -/
theorem initial_five_mul_sourceHeight_lt_count_mul_log_two [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) :
    5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) <
      ((P.lemmaFourRadius N 0 *
        (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1) : ℕ) : ℝ) *
        Real.log 2 := by
  let x : ℝ := P.levelScale N
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let T : ℕ := P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1
  have hxlarge : (512 : ℝ) < x := by
    have h := P.fiveHundredTwelve_mul_rank_add_one_lt_levelScale hN
    have hm : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    dsimp only [x]
    nlinarith
  have hbudget : P.lemmaFourBudget N 1 ≤ P.lemmaFourBudget N 0 :=
    P.outer_lemmaFourBudget_succ_le_current N 0
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
      simpa only [x, Slevel] using Nat.lt_floor_add_one (P.levelScale N)
    linarith
  have hTstrong : (x - 1) / 2 < (T : ℝ) := by linarith
  have hR : P.lemmaFourRadius N 0 = 16 * P.q ^ N * P.h := by
    rw [P.lemmaFourRadius_zero]
    rfl
  have hRpos : (0 : ℝ) < P.lemmaFourRadius N 0 := by
    exact_mod_cast (by simpa only [P.lemmaFourRadius_zero] using P.R_pos N)
  have hcount : (511 / 64 : ℝ) * H <
      (P.lemmaFourRadius N 0 : ℝ) * T := by
    have hTx : (511 / 1024 : ℝ) * x < T := by
      have hx : (511 / 512 : ℝ) * x < x - 1 := by nlinarith
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hTx hRpos
    have hcancel :
        P.levelScale N * ((P.q ^ N : ℕ) : ℝ) * P.h =
          (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
      have hqpow : (((P.q ^ N : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (pow_ne_zero N
          (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)))
      unfold levelScale qInvPow
      field_simp
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
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  have hfirst : 5 * H < ((511 / 64 : ℝ) * H) * Real.log 2 := by
    calc
      5 * H < ((511 / 64 : ℝ) * Real.log 2) * H :=
        mul_lt_mul_of_pos_right hlog hHpos
      _ = ((511 / 64 : ℝ) * H) * Real.log 2 := by ring
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Nat.cast_mul]
  change 5 * H <
    (P.lemmaFourRadius N 0 : ℝ) * (T : ℝ) * Real.log 2
  exact hfirst.trans (mul_lt_mul_of_pos_right hcount hlogpos)

/-- With the sharp new-target quotient, the same initial node count pays
seven source-height units and the extra normalized Cauchy unit. -/
theorem initial_seven_mul_sourceHeight_add_one_lt_count_mul_log_three
    [Nonempty ι] {N : ℕ} (hN : P.LevelOK N) :
    7 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) + 1 <
      ((P.lemmaFourRadius N 0 *
        (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1) : ℕ) : ℝ) *
        Real.log 3 := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let count : ℕ := P.lemmaFourRadius N 0 *
    (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)
  have hepsOne : P.epsilon ≤ 1 := by
    rw [P.epsilon_eq]
    have hm : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    apply (div_le_one (by positivity :
      (0 : ℝ) < 6 * (P.rank + 1))).2
    nlinarith
  have hkEps : P.k ^ P.epsilon ≤ P.k := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsOne
  have hk13 : (13 : ℝ) ≤ P.k := by
    calc
      (13 : ℝ) = P.q := by norm_num [q]
      _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
      _ ≤ P.k := hkEps
  have hlog : (2 / 3 : ℝ) ≤ Real.log P.OmegaOld := by
    exact (by nlinarith [Real.log_two_gt_d9] :
      (2 / 3 : ℝ) ≤ Real.log 2).trans P.log_two_le_log_OmegaOld
  have hW : (2 / 3 : ℝ) ≤ P.Omega * Real.log P.OmegaOld := by
    calc
      (2 / 3 : ℝ) = 1 * (2 / 3 : ℝ) := by ring
      _ ≤ P.Omega * Real.log P.OmegaOld :=
        mul_le_mul P.one_le_Omega hlog (by norm_num) P.Omega_pos.le
  have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.h_pos
  have hHlarge : (2 : ℝ) < H := by
    dsimp only [H]
    have hmul : (13 : ℝ) * (2 / 3) ≤
        (P.h : ℝ) * P.k * (P.Omega * Real.log P.OmegaOld) := by
      calc
        (13 : ℝ) * (2 / 3) = 1 * 13 * (2 / 3) := by ring
        _ ≤ (P.h : ℝ) * P.k *
            (P.Omega * Real.log P.OmegaOld) := by gcongr
    nlinarith
  have hfive := P.initial_five_mul_sourceHeight_lt_count_mul_log_two hN
  change 5 * H < (count : ℝ) * Real.log 2 at hfive
  have hHpos : 0 < H := (by norm_num : (0 : ℝ) < 2).trans hHlarge
  have hcountpos : (0 : ℝ) < count := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_contra h
    have hle : (count : ℝ) ≤ 0 := le_of_not_gt h
    have hnonneg : (0 : ℝ) ≤ count := Nat.cast_nonneg count
    have : (count : ℝ) = 0 := le_antisymm hle hnonneg
    rw [this, zero_mul] at hfive
    nlinarith
  have hlogs : (3 / 2 : ℝ) * Real.log 2 < Real.log 3 := by
    nlinarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have hcountLogs :
      (3 / 2 : ℝ) * ((count : ℝ) * Real.log 2) <
        (count : ℝ) * Real.log 3 := by
    have hmul := mul_lt_mul_of_pos_left hlogs hcountpos
    nlinarith
  have hseven : 7 * H + 1 < (3 / 2 : ℝ) * (5 * H) := by
    nlinarith
  calc
    7 * H + 1 < (3 / 2 : ℝ) * (5 * H) := hseven
    _ < (3 / 2 : ℝ) * ((count : ℝ) * Real.log 2) :=
      mul_lt_mul_of_pos_left hfive (by norm_num)
    _ < (count : ℝ) * Real.log 3 := hcountLogs

/-- Exact sharp `t=0` outer-contour estimate from the primary-source
`3^(-R₀T₀)` factor.  A two-height-unit growth loss and the normalized
`3/2` Cauchy factor leave five full source-height units of decay. -/
theorem initial_threeHalves_mul_outerFactor_lt_exp_neg_five [Nonempty ι]
    {N : ℕ} (hN : P.LevelOK N) {growth : ℝ}
    (hgrowth0 : 0 ≤ growth)
    (hgrowth : growth ≤ Real.exp
      (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 3 : ℝ) ^
          (P.lemmaFourRadius N 0 *
            (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)) *
          growth) <
      Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let count : ℕ := P.lemmaFourRadius N 0 *
    (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)
  have hcountSource :=
    P.initial_seven_mul_sourceHeight_add_one_lt_count_mul_log_three hN
  have hcount : 5 * H + 1 + 2 * H <
      (count : ℝ) * Real.log 3 := by
    dsimp only [H, count]
    convert hcountSource using 1 <;> ring
  have hpow : (1 / 3 : ℝ) ^ count =
      Real.exp (-((count : ℝ) * Real.log 3)) := by
    calc
      (1 / 3 : ℝ) ^ count =
          Real.exp (Real.log (1 / 3 : ℝ)) ^ count := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 3)]
      _ = Real.exp ((count : ℝ) * Real.log (1 / 3 : ℝ)) :=
        (Real.exp_nat_mul (Real.log (1 / 3 : ℝ)) count).symm
      _ = Real.exp (-((count : ℝ) * Real.log 3)) := by
        rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
          rw [one_div, Real.log_inv]]
        congr 1
        ring
  have hgrowth' : growth ≤ Real.exp (2 * H) := by
    dsimp only [H]
    exact hgrowth
  have hdecay : growth * (1 / 3 : ℝ) ^ count <
      Real.exp (-(5 * H + 1)) := by
    rw [hpow]
    calc
      growth * Real.exp (-((count : ℝ) * Real.log 3)) ≤
          Real.exp (2 * H) * Real.exp (-((count : ℝ) * Real.log 3)) :=
        mul_le_mul_of_nonneg_right hgrowth' (Real.exp_pos _).le
      _ = Real.exp (2 * H - (count : ℝ) * Real.log 3) := by
        rw [sub_eq_add_neg, Real.exp_add]
      _ < Real.exp (-(5 * H + 1)) := by
        apply Real.exp_lt_exp.mpr
        linarith
  have hfactor : (3 / 2 : ℝ) < Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  dsimp only [H, count] at hdecay ⊢
  calc
    (3 / 2 : ℝ) * ((1 / 3 : ℝ) ^
        (P.lemmaFourRadius N 0 *
          (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)) *
        growth) =
        (3 / 2 : ℝ) * (growth * (1 / 3 : ℝ) ^
          (P.lemmaFourRadius N 0 *
            (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1))) := by
      ring
    _ < Real.exp 1 * Real.exp (-(5 *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) + 1)) :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hfactor.le
          (mul_nonneg hgrowth0 (pow_nonneg (by norm_num) _)))
        (mul_lt_mul_of_pos_left hdecay (Real.exp_pos 1))
    _ = Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Erdos240.VDPLParameters

#print axioms Erdos240.InterpolationProducts.three_mul_norm_target_sub_node_le_outer
#print axioms Erdos240.InterpolationProducts.norm_integralNodalProduct_newTarget_div_outerCircle_le
#print axioms Erdos240.VDPLParameters.thirtyOne_div_oneTwentyEight_mul_levelScale_lt_lemmaFourBudget
#print axioms Erdos240.VDPLParameters.epsilon_mul_lemmaFourBudget_lt_stageMultiplicity
#print axioms Erdos240.VDPLParameters.fifteen_mul_radiusCore_lt_lemmaFourRadius
#print axioms Erdos240.VDPLParameters.ten_div_epsilon_lt_k_rpow_three_mul_epsilon
#print axioms Erdos240.VDPLParameters.positiveStage_rawExponent_lt_nodeCount
#print axioms Erdos240.VDPLParameters.four_mul_k_le_three_eighth_mul_epsilon_mul_stagePower
#print axioms Erdos240.VDPLParameters.thirtyTwo_mul_nextStagePower_lt_sixteen_fifths_mul_epsilon_mul_stagePower
#print axioms Erdos240.VDPLParameters.ninety_lt_positiveStageExponent
#print axioms Erdos240.VDPLParameters.positiveStage_outerExponent_add_growth_add_one_lt_count_mul_log_three
#print axioms Erdos240.VDPLParameters.positiveStage_fiveHeight_add_growth_add_one_lt_count_mul_log_three
#print axioms Erdos240.VDPLParameters.positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_target
#print axioms Erdos240.VDPLParameters.positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_five
#print axioms Erdos240.VDPLParameters.initial_five_mul_sourceHeight_lt_count_mul_log_two
#print axioms Erdos240.VDPLParameters.initial_seven_mul_sourceHeight_add_one_lt_count_mul_log_three
#print axioms Erdos240.VDPLParameters.initial_threeHalves_mul_outerFactor_lt_exp_neg_five
