/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.AuxConcentration
import ErdosProblems.Erdos136.TrackedTests
import ErdosProblems.Erdos136.UpperReduction

/-!
# Erdős 136: assembly interface for the upper construction

This file joins the finite conflict-free matching conclusion to the exact
triangle-block and leave-completion developments.  The remaining probabilistic
work is isolated in `HasEventualJMCInstances`: it asks for the literal retained
host, conflict, and role-refined test hypotheses, with the degree cutoff chosen
after the conflict-free theorem supplies it.
-/

namespace Erdos136

open Filter
open scoped Topology

noncomputable section

/-- A concrete conflict-degree budget.  The value is exactly
`512 * (5 + 0 + 1)^3`, where `5 n^(2-δ)` is the sharp same-colour
paint-fibre scale and the extra one absorbs the natural ceiling. -/
def jmConflictBudget : ℕ := 110592

theorem four_le_jmConflictBudget : 4 ≤ jmConflictBudget := by
  norm_num [jmConflictBudget]

theorem jmConflictBudget_absorbs_paintFiber :
    512 * ((5 : ℝ) + 0 + 1) ^ 3 ≤ (jmConflictBudget : ℝ) := by
  norm_num [jmConflictBudget]

/-- The corrected role-refined family still has only quadratically many
tests.  This is the literal entropy estimate used to place its finite index
type below the exponential capacity in `IsSpecializedCFMInstance`. -/
theorem card_jmcTrackedIndex_le (n : ℕ) :
    Fintype.card (JMCTrackedIndex n) ≤ 19 * n ^ 2 := by
  let f : JMCTrackedIndex n →
      (Fin n) ⊕ ((Fin n × Fin n) × (JMCPaintRole × JMCPaintRole)) ⊕
        ((Fin n × Fin n) × (JMCPaintRole × JMCPaintRole))
    | .leave x => Sum.inl x
    | .pairRole a =>
        Sum.inr (Sum.inl ((a.x, a.y), (a.leftRole, a.rightRole)))
    | .tripleRole a =>
        Sum.inr (Sum.inr ((a.x, a.y), (a.leftRole, a.rightRole)))
  have hrole : Function.Injective
      (fun a : JMCRolePairIndex n ↦
        ((a.x, a.y), (a.leftRole, a.rightRole))) := by
    intro a b h
    rcases a with ⟨⟨ax, ay, ha⟩, ar, as⟩
    rcases b with ⟨⟨bx, bz, hb⟩, br, bs⟩
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
    rfl
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp only [JMCTrackedIndex.leave.injEq, JMCTrackedIndex.pairRole.injEq,
    JMCTrackedIndex.tripleRole.injEq] at h ⊢
    · exact h
    · apply hrole
      simp only [Prod.mk.injEq]
      exact h
    · apply hrole
      simp only [Prod.mk.injEq]
      exact h
  have hcard : Fintype.card (JMCTrackedIndex n) ≤ n + 18 * n ^ 2 := by
    apply (Fintype.card_le_of_injective f hf).trans_eq
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      show Fintype.card JMCPaintRole = 3 by decide]
    ring
  calc
    Fintype.card (JMCTrackedIndex n) ≤ n + 18 * n ^ 2 := hcard
    _ ≤ 19 * n ^ 2 := by
      by_cases hn : n = 0
      · subst n
        simp
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      nlinarith

/-- Consequently the entire role-refined test index fits the exponential
entropy allowance of the conflict-free matching theorem. -/
theorem eventually_jmcTrackedIndex_le_auxDegree_exponential
    {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (JMCTrackedIndex n) : ℝ) ≤
        Real.exp ((jmAuxDegreeReal (jmDelta eta0) n) ^
          ((jmEta eta0) ^ 3)) := by
  apply eventually_natPolynomial_le_auxDegree_exponential
    (fun n ↦ Fintype.card (JMCTrackedIndex n)) heta0
      (C := 19) (a := 2) (by norm_num)
  filter_upwards with n
  have h := card_jmcTrackedIndex_le n
  norm_num only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow]
  exact_mod_cast h

/-- A role-independent lower bound for the nine Joos--Mubayi pair-test
centres.  The constant is deliberately coarse: each role coefficient is at
least `1/2`, present labels have probability at least `1/2`, absent labels
have probability at least `rho/2`, and the rounded old palette is at least
`5n/6`. -/
theorem pairRoleTarget_jm_lower {eta0 : ℝ} (_heta0 : 0 < eta0)
    {n : ℕ} (hn : 0 < n) (hrho : jmRho (jmDelta eta0) n ≤ 1)
    (a : AuxConcentration.PairRoleIndex n) :
    (1 / 40000 : ℝ) * (n : ℝ) ^ (7 - 2 * jmDelta eta0) ≤
      AuxConcentration.pairRoleTarget (jmOldColors (jmDelta eta0) n)
        (jmDeletion (jmDelta eta0) n) a := by
  let delta := jmDelta eta0
  let rho := jmRho delta n
  let q := jmDeletion delta n
  let p := jmRetention delta n
  let k := jmOldColors delta n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrho0 : 0 ≤ rho := by
    dsimp [rho]
    exact Real.rpow_nonneg hnR.le _
  have hqhalf : (1 / 2 : ℝ) ≤ q := by
    dsimp [q, jmDeletion, rho]
    rw [le_div_iff₀ (by positivity : 0 < 1 + jmRho delta n)]
    linarith
  have hp : rho / 2 ≤ p := by
    dsimp [p, jmRetention, rho]
    rw [div_le_div_iff_of_pos_left (jmRho_pos hn)
      (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < 1 + jmRho delta n)]
    linarith
  have hk : (5 / 6 : ℝ) * n ≤ (k : ℝ) := by
    have hceil := jmOldPaletteReal_le_colors delta n
    dsimp [k]
    apply le_trans _ hceil
    unfold jmOldPaletteReal
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6 * n) hrho0]
  have hleft :=
    (AuxConcentration.roleLeadingCoefficient_mem_Icc a.leftRole).1
  have hright :=
    (AuxConcentration.roleLeadingCoefficient_mem_Icc a.rightRole).1
  have hpowId : (n : ℝ) ^ 7 * rho ^ 2 =
      (n : ℝ) ^ (7 - 2 * delta) := by
    have hrhoEq : rho ^ 2 = (n : ℝ) ^ (-(2 * delta)) := by
      dsimp [rho]
      exact jmRho_sq_eq_base_rpow hn
    rw [hrhoEq, ← Real.rpow_natCast]
    rw [← Real.rpow_add hnR]
    congr 1
  rw [AuxConcentration.pairRoleTarget,
    AuxConcentration.leftCoefficient_eq_roleLeadingCoefficient,
    AuxConcentration.rightCoefficient_eq_roleLeadingCoefficient]
  have hret : 1 - jmDeletion (jmDelta eta0) n =
      jmRetention (jmDelta eta0) n := by
    linarith [jmRetention_add_deletion (delta := jmDelta eta0) hn]
  rw [hret, ← hpowId]
  dsimp only [delta, rho, q, p, k]
  calc
    (1 / 40000 : ℝ) *
        ((n : ℝ) ^ 7 * (jmRho (jmDelta eta0) n) ^ 2) ≤
        (1 / 2 : ℝ) * (1 / 2 : ℝ) *
          ((jmRho (jmDelta eta0) n / 2) ^ 2) * (1 / 2 : ℝ) ^ 10 *
          (((5 / 6 : ℝ) * n) ^ 3) * (n : ℝ) ^ 4 := by
      ring_nf
      exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    _ ≤ AuxConcentration.roleLeadingCoefficient a.leftRole *
        AuxConcentration.roleLeadingCoefficient a.rightRole *
        (jmRetention (jmDelta eta0) n) ^ 2 *
        (jmDeletion (jmDelta eta0) n) ^ 10 *
        (jmOldColors (jmDelta eta0) n : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
      gcongr

/-- The lower endpoint of one of the nine concentrated role-pair windows. -/
def jmPairRoleLower (eta0 : ℝ) (n : ℕ)
    (a : JMCRolePairIndex n) : ℝ :=
  let b := (auxPairRoleIndexEquiv n).symm a
  AuxConcentration.pairRoleTarget (jmOldColors (jmDelta eta0) n)
      (jmDeletion (jmDelta eta0) n) b -
    (AuxConcentration.universalPairRoleDeviation n b +
      AuxConcentration.universalPairRoleMeanError n b) -
    9 * (n : ℝ) ^ 6

/-- Uniformly over all nine role pairs, the concentrated window retains
half of its leading polynomial centre for all sufficiently large `n`. -/
theorem eventually_jmPairRoleLower_ge {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop, ∀ a : JMCRolePairIndex n,
      (1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * jmDelta eta0) ≤
        jmPairRoleLower eta0 n a := by
  have hgap : (20 / 3 : ℝ) < 7 - 2 * jmDelta eta0 := by
    have hd := jmDelta_le_one_ten_thousandth eta0
    nlinarith
  have hgrowth := eventually_const_mul_rpow_le_rpow
    (C := (6000000 : ℝ)) (a := (20 / 3 : ℝ))
      (b := 7 - 2 * jmDelta eta0) (by norm_num) hgap
  have hrho : ∀ᶠ n : ℕ in atTop, jmRho (jmDelta eta0) n ≤ 1 :=
    (jmRho_tendsto_zero (jmDelta_pos heta0)).eventually_le_const (by norm_num)
  filter_upwards [hgrowth, hrho, eventually_ge_atTop (1 : ℕ)]
      with n hgrowth hrho hn
  intro a
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hpow : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
  let b := (auxPairRoleIndexEquiv n).symm a
  have htarget := pairRoleTarget_jm_lower heta0 hn0 hrho b
  have hloss :
      AuxConcentration.universalPairRoleDeviation n b +
          AuxConcentration.universalPairRoleMeanError n b +
          9 * (n : ℝ) ^ 6 ≤
        75 * (n : ℝ) ^ (20 / 3 : ℝ) := by
    simp only [AuxConcentration.universalPairRoleDeviation,
      AuxConcentration.universalPairRoleMeanError]
    nlinarith
  have hsmall : 75 * (n : ℝ) ^ (20 / 3 : ℝ) ≤
      (1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * jmDelta eta0) := by
    nlinarith
  dsimp [jmPairRoleLower, b]
  linarith

/-- The matching role centres also have the source-scale upper bound.  This
keeps the `rho^2` factor which is essential in the terminal cross-residual. -/
theorem pairRoleTarget_jm_upper {delta : ℝ} {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n) (a : AuxConcentration.PairRoleIndex n) :
    AuxConcentration.pairRoleTarget k (jmDeletion delta n) a ≤
      (n : ℝ) ^ (7 - 2 * delta) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 ≤ jmDeletion delta n := (jmDeletion_pos hn).le
  have hq1 : jmDeletion delta n ≤ 1 := (jmDeletion_lt_one hn).le
  have hp0 : 0 ≤ jmRetention delta n := (jmRetention_pos hn).le
  have hp : jmRetention delta n ≤ jmRho delta n := by
    have hrho0 : 0 ≤ jmRho delta n := by
      unfold jmRho
      exact Real.rpow_nonneg hnR.le _
    unfold jmRetention
    exact div_le_self hrho0 (by linarith)
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hleft := (AuxConcentration.roleLeadingCoefficient_mem_Icc
    a.leftRole).2
  have hright := (AuxConcentration.roleLeadingCoefficient_mem_Icc
    a.rightRole).2
  have hleft0 := (AuxConcentration.roleLeadingCoefficient_mem_Icc
    a.leftRole).1
  have hright0 := (AuxConcentration.roleLeadingCoefficient_mem_Icc
    a.rightRole).1
  have hq10 : jmDeletion delta n ^ 10 ≤ 1 := pow_le_one₀ hq0 hq1
  have hret : 1 - jmDeletion delta n = jmRetention delta n := by
    linarith [jmRetention_add_deletion (delta := delta) hn]
  have hpow : (n : ℝ) ^ 7 * (jmRho delta n) ^ 2 =
      (n : ℝ) ^ (7 - 2 * delta) := by
    rw [jmRho_sq_eq_base_rpow hn, ← Real.rpow_natCast,
      ← Real.rpow_add hnR]
    congr 1
  rw [AuxConcentration.pairRoleTarget,
    AuxConcentration.leftCoefficient_eq_roleLeadingCoefficient,
    AuxConcentration.rightCoefficient_eq_roleLeadingCoefficient, hret]
  calc
    AuxConcentration.roleLeadingCoefficient a.leftRole *
          AuxConcentration.roleLeadingCoefficient a.rightRole *
          jmRetention delta n ^ 2 * jmDeletion delta n ^ 10 *
          (k : ℝ) ^ 3 * (n : ℝ) ^ 4 ≤
        1 * 1 * (jmRho delta n) ^ 2 * 1 *
          (n : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
      gcongr
    _ = (n : ℝ) ^ 7 * (jmRho delta n) ^ 2 := by ring
    _ = (n : ℝ) ^ (7 - 2 * delta) := hpow

/-- A deliberately coarse upper envelope for the analytic auxiliary degree.
It is used only to dominate the finitely many W1/W2 numerators. -/
theorem jmAuxDegreeReal_le_three_mul_cube {delta : ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hn : 0 < n) :
    jmAuxDegreeReal delta n ≤ 3 * (n : ℝ) ^ 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hscale : jmDegreeScale delta n ≤ (n : ℝ) ^ 3 := by
    unfold jmDegreeScale
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (sub_le_self 3 hdelta)
  have hq0 : 0 ≤ jmDeletion delta n := (jmDeletion_pos hn).le
  have hq1 : jmDeletion delta n ≤ 1 := (jmDeletion_lt_one hn).le
  have hq4 : jmDeletion delta n ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
  rw [jmAuxDegreeReal_eq hn]
  calc
    (25 / 12 : ℝ) * jmDegreeScale delta n * jmDeletion delta n ^ 4 ≤
        (25 / 12 : ℝ) * (n : ℝ) ^ 3 * 1 := by gcongr
    _ ≤ 3 * (n : ℝ) ^ 3 := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right (by norm_num : (25 / 12 : ℝ) ≤ 3)
        (by positivity : 0 ≤ (n : ℝ) ^ 3)

/-- The exact common degree selected for the retained host. -/
def jmSelectedHostDegree (eta0 : ℝ) (n : ℕ) : ℝ :=
  AuxConcentration.universalHostDegree n
    (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n)

/-- A fresh-key cover multiplicity with three host-error scales of slack. -/
def jmCoverMultiplicity (eta0 : ℝ) (n : ℕ) : ℕ :=
  ⌊jmSelectedHostDegree eta0 n -
      3 * Real.rpow (jmSelectedHostDegree eta0 n) (1 - jmEta eta0)⌋₊

/-- Finite arithmetic for the floor-defined cover multiplicity. -/
theorem jmCoverMultiplicity_bounds {eta0 : ℝ} {n : ℕ}
    (heta0 : 0 < eta0)
    (hsmall : 8 * Real.rpow (jmSelectedHostDegree eta0 n)
        (1 - jmEta eta0) + 2 ≤ jmSelectedHostDegree eta0 n)
    (hambient : ((16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
      Real.rpow (jmSelectedHostDegree eta0 n) (1 - jmEta eta0))
    (herror : AuxConcentration.universalHostDegreeError n
        (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) ≤
      Real.rpow (jmSelectedHostDegree eta0 n) (1 - jmEta eta0)) :
    let d := jmSelectedHostDegree eta0 n
    let m := jmCoverMultiplicity eta0 n
    (d / 2 ≤ (m : ℝ)) ∧
      ((m : ℝ) ≤ d) ∧
      (((m + 16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
        d - AuxConcentration.universalHostDegreeError n
          (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n)) ∧
      AuxConcentration.universalHostDegreeError n
          (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) < d := by
  dsimp only
  let d := jmSelectedHostDegree eta0 n
  let e := Real.rpow d (1 - jmEta eta0)
  let x := d - 3 * e
  have he0 : 0 ≤ e := Real.rpow_nonneg (by linarith [hsmall]) _
  have hd0 : 0 ≤ d := by linarith
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hfloorLower : x < ((Nat.floor x : ℕ) : ℝ) + 1 := by
    simpa using Nat.lt_floor_add_one x
  have hhalf : d / 2 ≤ ((Nat.floor x : ℕ) : ℝ) := by
    dsimp [x] at hfloorLower ⊢
    linarith
  have hupper : ((Nat.floor x : ℕ) : ℝ) ≤ d := by
    exact hfloor.trans (by dsimp [x]; linarith)
  have hcover : (((Nat.floor x + 16 * (6 * n ^ 2) : ℕ) : ℝ)) ≤
      d - AuxConcentration.universalHostDegreeError n
        (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) := by
    norm_num only [Nat.cast_add]
    calc
      ((Nat.floor x : ℕ) : ℝ) + ((16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
          x + e := add_le_add hfloor hambient
      _ ≤ d - AuxConcentration.universalHostDegreeError n
          (jmOldColors (jmDelta eta0) n)
            (jmDeletion (jmDelta eta0) n) := by
        dsimp [x]
        linarith
  have hgap : AuxConcentration.universalHostDegreeError n
      (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) < d := by
    dsimp [e] at herror hsmall
    linarith
  simpa [jmCoverMultiplicity, d, e, x] using
    And.intro hhalf (And.intro hupper (And.intro hcover hgap))

/-- The two numerical inputs for `jmCoverMultiplicity_bounds` hold
simultaneously for the exact retained-host degree. -/
theorem eventually_jmCoverMultiplicity_numerics {eta0 : ℝ}
    (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      8 * Real.rpow (jmSelectedHostDegree eta0 n) (1 - jmEta eta0) + 2 ≤
          jmSelectedHostDegree eta0 n ∧
        ((16 * (6 * n ^ 2) : ℕ) : ℝ) ≤
          Real.rpow (jmSelectedHostDegree eta0 n) (1 - jmEta eta0) := by
  have heta : 0 < jmEta eta0 := jmEta_pos heta0
  have heta1 : jmEta eta0 < 1 := jmEta_lt_one heta0
  have hpower := eventually_const_mul_rpow_le_auxDegree_rpow heta0
    (C := (16 : ℝ)) (a := 0) (b := jmEta eta0)
    (by norm_num) heta (by
      have hd3 : jmDelta eta0 < 3 :=
        (jmDelta_lt_one heta0).trans (by norm_num)
      positivity)
  have hambient :=
    eventually_nat_const_mul_sq_le_auxDegree_one_sub_eta 96 heta0
  filter_upwards [hpower, hambient,
    AuxConcentration.eventually_jmAuxDegreeReal_le_universalHostDegree
      (jmDelta_pos heta0),
    AuxConcentration.eventually_universalHostDegree_ge
      (d₀ := (4 : ℝ)) (jmDelta_pos heta0)
        ((jmDelta_lt_one heta0).trans (by norm_num)),
    eventually_ge_atTop (1 : ℕ)] with n hpower hambient haux hd4 hn
  let a := jmAuxDegreeReal (jmDelta eta0) n
  let d := jmSelectedHostDegree eta0 n
  have hd4' : (4 : ℝ) ≤ d := by
    simpa [d, jmSelectedHostDegree] using hd4
  have hd0 : 0 ≤ d := by linarith
  have hdpos : 0 < d := by linarith
  have ha0 : 0 ≤ a := jmAuxDegreeReal_nonneg _ _
  have had : a ≤ d := by simpa [a, d, jmSelectedHostDegree] using haux
  have hpow16 : 16 ≤ Real.rpow a (jmEta eta0) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
    simpa [a] using hpower
  have hpow16d : 16 ≤ Real.rpow d (jmEta eta0) :=
    hpow16.trans (Real.rpow_le_rpow ha0 had heta.le)
  have he0 : 0 ≤ Real.rpow d (1 - jmEta eta0) :=
    Real.rpow_nonneg hd0 _
  have hmul : Real.rpow d (jmEta eta0) *
      Real.rpow d (1 - jmEta eta0) = d := by
    change d ^ (jmEta eta0) * d ^ (1 - jmEta eta0) = d
    rw [← Real.rpow_add hdpos]
    norm_num
  have h16e : 16 * Real.rpow d (1 - jmEta eta0) ≤ d := by
    calc
      16 * Real.rpow d (1 - jmEta eta0) ≤
          Real.rpow d (jmEta eta0) *
            Real.rpow d (1 - jmEta eta0) :=
        mul_le_mul_of_nonneg_right hpow16d he0
      _ = d := hmul
  have hsmall : 8 * Real.rpow d (1 - jmEta eta0) + 2 ≤ d := by
    nlinarith
  have hambient' : ((96 * n ^ 2 : ℕ) : ℝ) ≤
      Real.rpow d (1 - jmEta eta0) := by
    exact hambient.trans
      (Real.rpow_le_rpow ha0 had (sub_nonneg.mpr heta1.le))
  constructor
  · simpa [d]
  · norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hambient' ⊢
    convert hambient' using 1 <;> ring

/-- A common coarse power envelope for every exponent used by the role
tests.  Keeping the real exponent visible avoids hiding any ceiling loss. -/
theorem selectedHostDegree_rpow_le_1296_mul {eta0 b : ℝ} {n : ℕ}
    (hn : 0 < n) (hd0 : 0 ≤ jmSelectedHostDegree eta0 n)
    (hd : jmSelectedHostDegree eta0 n ≤ 6 * (n : ℝ) ^ 3)
    (hb0 : 0 ≤ b) (hb4 : b ≤ 4) :
    (jmSelectedHostDegree eta0 n) ^ b ≤
      1296 * (n : ℝ) ^ (3 * b) := by
  let d := jmSelectedHostDegree eta0 n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0' : 0 ≤ d := by simpa [d] using hd0
  have hsix0 : 0 ≤ (6 : ℝ) := by norm_num
  have hcube0 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  calc
    d ^ b ≤ (6 * (n : ℝ) ^ 3) ^ b :=
      Real.rpow_le_rpow hd0' hd hb0
    _ = (6 : ℝ) ^ b * ((n : ℝ) ^ 3) ^ b := by
      rw [Real.mul_rpow hsix0 hcube0]
    _ = (6 : ℝ) ^ b * (n : ℝ) ^ (3 * b) := by
      have hbase : ((n : ℝ) ^ 3) = (n : ℝ) ^ (3 : ℝ) := by
        exact (Real.rpow_natCast (n : ℝ) 3).symm
      rw [hbase]
      exact congrArg (fun z : ℝ ↦ (6 : ℝ) ^ b * z)
        (Real.rpow_mul hnR.le 3 b).symm
    _ ≤ 1296 * (n : ℝ) ^ (3 * b) := by
      have h6 : (6 : ℝ) ^ b ≤ (6 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 6) hb4
      have h64 : (6 : ℝ) ^ (4 : ℝ) = 1296 := by
        calc
          (6 : ℝ) ^ (4 : ℝ) = (6 : ℝ) ^ (4 : ℕ) :=
            Real.rpow_natCast (6 : ℝ) 4
          _ = 1296 := by norm_num
      rw [h64] at h6
      exact mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hnR.le _)

/-- One oversized fixed coefficient absorbs every finite W1/W2 numerator. -/
def jmRoleNumeratorBudget : ℝ := 1000000000000

/-- The two exponent gaps behind all role-test lower and extension bounds. -/
theorem eventually_jmRoleGrowthWindows {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      jmRoleNumeratorBudget * (n : ℝ) ^ (6 + 3 * jmEta eta0) ≤
          (1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * jmDelta eta0) ∧
        jmRoleNumeratorBudget * (n : ℝ) ^ (9 + 3 * jmEta eta0) ≤
          (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * jmDelta eta0) := by
  have he : jmEta eta0 ≤ (1 / 100 : ℝ) := min_le_right _ _
  have hd : jmDelta eta0 ≤ (1 / 10000 : ℝ) :=
    jmDelta_le_one_ten_thousandth eta0
  have hgap1 : 6 + 3 * jmEta eta0 < 7 - 2 * jmDelta eta0 := by
    linarith
  have hgap2 : 9 + 3 * jmEta eta0 < 10 - 3 * jmDelta eta0 := by
    linarith
  have h1 := eventually_const_mul_rpow_le_rpow
    (C := (80000 : ℝ) * jmRoleNumeratorBudget)
    (a := 6 + 3 * jmEta eta0) (b := 7 - 2 * jmDelta eta0)
    (by norm_num [jmRoleNumeratorBudget]) hgap1
  have h2 := eventually_const_mul_rpow_le_rpow
    (C := (160000 : ℝ) * jmRoleNumeratorBudget)
    (a := 9 + 3 * jmEta eta0) (b := 10 - 3 * jmDelta eta0)
    (by norm_num [jmRoleNumeratorBudget]) hgap2
  filter_upwards [h1, h2] with n h1 h2
  constructor <;> dsimp [jmRoleNumeratorBudget] at h1 h2 ⊢ <;> nlinarith

/-- The exact scalar premises consumed by the repaired role-test adapter. -/
structure JMCTrackedTestNumerics (eta0 : ℝ) (n : ℕ) : Prop where
  pairW1 : ∀ a : JMCRolePairIndex n,
    (jmSelectedHostDegree eta0 n) ^ (2 + jmEta eta0) ≤
      jmPairRoleLower eta0 n a
  tripleW1 : ∀ a : JMCRolePairIndex n,
    (jmSelectedHostDegree eta0 n) ^ (3 + jmEta eta0) ≤
      (jmCoverMultiplicity eta0 n : ℝ) * jmPairRoleLower eta0 n a
  pairExtension : ∀ a : JMCRolePairIndex n,
    ((16 * jmcHostDegreeCeil n (jmOldColors (jmDelta eta0) n)
      (jmDeletion (jmDelta eta0) n) : ℕ) : ℝ) ≤
      jmPairRoleLower eta0 n a /
        (jmSelectedHostDegree eta0 n) ^ (1 + jmEta eta0)
  tripleExtensionOne : ∀ a : JMCRolePairIndex n,
    ((16 * (jmcHostDegreeCeil n (jmOldColors (jmDelta eta0) n)
          (jmDeletion (jmDelta eta0) n)) ^ 2 +
        256 * jmOldColors (jmDelta eta0) n * (6 * n ^ 2) ^ 2 : ℕ) : ℝ) ≤
      ((jmCoverMultiplicity eta0 n : ℝ) * jmPairRoleLower eta0 n a) /
        (jmSelectedHostDegree eta0 n) ^ (1 + jmEta eta0)
  tripleExtensionTwo : ∀ a : JMCRolePairIndex n,
    ((48 * jmcHostDegreeCeil n (jmOldColors (jmDelta eta0) n)
      (jmDeletion (jmDelta eta0) n) : ℕ) : ℝ) ≤
      ((jmCoverMultiplicity eta0 n : ℝ) * jmPairRoleLower eta0 n a) /
        (jmSelectedHostDegree eta0 n) ^ (2 + jmEta eta0)

/-- All repaired role-test W1 and extension comparisons hold for the exact
common retained-host degree. -/
theorem eventually_jmcTrackedTestNumerics {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop, JMCTrackedTestNumerics eta0 n := by
  filter_upwards [eventually_jmRoleGrowthWindows heta0,
    eventually_jmPairRoleLower_ge heta0,
    AuxConcentration.eventually_universalHostDegree_le_two_jmAuxDegreeReal
      heta0,
    AuxConcentration.eventually_jmAuxDegreeReal_le_universalHostDegree
      (jmDelta_pos heta0),
    eventually_jmDegreeScale_le_auxDegree (jmDelta_pos heta0),
    eventually_jmCoverMultiplicity_numerics heta0,
    AuxConcentration.eventually_universalHostDegreeError_le_rpow heta0,
    eventually_jmOldColors_le (jmDelta_pos heta0),
    eventually_ge_atTop (1 : ℕ)] with
      n hgrowth hlower hdupper hauxd hscale hcoverNum herror hk hn
  let delta := jmDelta eta0
  let eta := jmEta eta0
  let k := jmOldColors delta n
  let d := jmSelectedHostDegree eta0 n
  let m := jmCoverMultiplicity eta0 n
  let D := jmcHostDegreeCeil n k (jmDeletion delta n)
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have heta0' : 0 < eta := by simpa [eta] using jmEta_pos heta0
  have heta1 : eta < 1 := by simpa [eta] using jmEta_lt_one heta0
  have hdelt0 : 0 ≤ delta := by simpa [delta] using (jmDelta_pos heta0).le
  have haux0 : 0 ≤ jmAuxDegreeReal delta n := jmAuxDegreeReal_nonneg _ _
  have hscalePos : 0 < jmDegreeScale delta n := by
    unfold jmDegreeScale
    exact Real.rpow_pos_of_pos hnR _
  have hscale' : jmDegreeScale delta n ≤ jmAuxDegreeReal delta n := by
    simpa [delta] using hscale
  have had : jmAuxDegreeReal delta n ≤ d := by
    simpa [delta, d, jmSelectedHostDegree] using hauxd
  have hdpos : 0 < d := hscalePos.trans_le (hscale'.trans had)
  have hd0 : 0 ≤ d := hdpos.le
  have hauxUpper : jmAuxDegreeReal delta n ≤ 3 * (n : ℝ) ^ 3 :=
    jmAuxDegreeReal_le_three_mul_cube hdelt0 hn0
  have hdSix : d ≤ 6 * (n : ℝ) ^ 3 := by
    have hd2 : d ≤ 2 * jmAuxDegreeReal delta n := by
      simpa [delta, d, jmSelectedHostDegree] using hdupper
    linarith
  have hDlt : (D : ℝ) < d + 1 := by
    dsimp [D, k, delta, d, jmSelectedHostDegree, jmcHostDegreeCeil]
    exact Nat.ceil_lt_add_one hd0
  have hD : (D : ℝ) ≤ 7 * (n : ℝ) ^ 3 := by
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn1 3
    linarith
  have hcover := jmCoverMultiplicity_bounds heta0 hcoverNum.1 hcoverNum.2
    (by simpa [d, delta, jmSelectedHostDegree] using herror)
  have hmhalf : d / 2 ≤ (m : ℝ) := by
    simpa [d, m] using hcover.1
  have hscaleD : jmDegreeScale delta n ≤ d := by
    exact hscale'.trans had
  have hmScale : (1 / 2 : ℝ) * (n : ℝ) ^ (3 - delta) ≤ (m : ℝ) := by
    have hs : jmDegreeScale delta n = (n : ℝ) ^ (3 - delta) := rfl
    rw [← hs]
    linarith
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hkR : (k : ℝ) ≤ n := by
    have hk' : k ≤ n := by simpa [k, delta] using hk
    exact_mod_cast hk'
  have hweak := hgrowth.1
  have hstrong := hgrowth.2
  have hpowadd (u v : ℝ) :
      (n : ℝ) ^ u * (n : ℝ) ^ v = (n : ℝ) ^ (u + v) := by
    exact (Real.rpow_add hnR u v).symm
  have hpow3 (u : ℝ) :
      (n : ℝ) ^ 3 * (n : ℝ) ^ u = (n : ℝ) ^ (3 + u) := by
    rw [show (n : ℝ) ^ 3 = (n : ℝ) ^ (3 : ℝ) by
      exact (Real.rpow_natCast (n : ℝ) 3).symm]
    exact hpowadd 3 u
  have hpow6 (u : ℝ) :
      (n : ℝ) ^ 6 * (n : ℝ) ^ u = (n : ℝ) ^ (6 + u) := by
    rw [show (n : ℝ) ^ 6 = (n : ℝ) ^ (6 : ℝ) by
      exact (Real.rpow_natCast (n : ℝ) 6).symm]
    exact hpowadd 6 u
  have hnumOne :
      (((16 * D ^ 2 + 256 * k * (6 * n ^ 2) ^ 2 : ℕ) : ℝ)) ≤
        10000 * (n : ℝ) ^ 6 := by
    have hDsq : (D : ℝ) ^ 2 ≤ (7 * (n : ℝ) ^ 3) ^ 2 :=
      pow_le_pow_left₀ hD0 hD 2
    have hkn : (k : ℝ) * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
      calc
        (k : ℝ) * (n : ℝ) ^ 4 ≤ (n : ℝ) * (n : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hkR (by positivity)
        _ = (n : ℝ) ^ 5 := by ring
    have hfiveSix : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 6 := by
      calc
        (n : ℝ) ^ 5 = (n : ℝ) ^ 5 * 1 := by ring
        _ ≤ (n : ℝ) ^ 5 * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hn1 (by positivity)
        _ = (n : ℝ) ^ 6 := by ring
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat] at ⊢
    nlinarith
  have htripleBase (a : JMCRolePairIndex n) :
      (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * delta) ≤
        (m : ℝ) * jmPairRoleLower eta0 n a := by
    have hP := hlower a
    have hmul := mul_le_mul hmScale hP
      (by positivity : 0 ≤ (1 / 80000 : ℝ) *
        (n : ℝ) ^ (7 - 2 * delta)) (Nat.cast_nonneg m)
    calc
      (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * delta) =
          ((1 / 2 : ℝ) * (n : ℝ) ^ (3 - delta)) *
            ((1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * delta)) := by
        calc
          (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * delta) =
              (1 / 160000 : ℝ) *
                ((n : ℝ) ^ (3 - delta) * (n : ℝ) ^ (7 - 2 * delta)) := by
            rw [hpowadd]
            congr 1
            ring_nf
          _ = ((1 / 2 : ℝ) * (n : ℝ) ^ (3 - delta)) *
                ((1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * delta)) := by ring
      _ ≤ (m : ℝ) * jmPairRoleLower eta0 n a := hmul
  have hpowPair : d ^ (2 + eta) ≤
      1296 * (n : ℝ) ^ (6 + 3 * eta) := by
    have h := selectedHostDegree_rpow_le_1296_mul
      (eta0 := eta0) (b := 2 + eta) hn0 (by simpa [d] using hd0)
        (by simpa [d] using hdSix) (by linarith) (by linarith)
    convert h using 1 <;> simp [d, eta] <;> ring_nf
  have hpowOne : d ^ (1 + eta) ≤
      1296 * (n : ℝ) ^ (3 + 3 * eta) := by
    have h := selectedHostDegree_rpow_le_1296_mul
      (eta0 := eta0) (b := 1 + eta) hn0 (by simpa [d] using hd0)
        (by simpa [d] using hdSix) (by linarith) (by linarith)
    convert h using 1 <;> simp [d, eta] <;> ring_nf
  have hpowTwo : d ^ (2 + eta) ≤
      1296 * (n : ℝ) ^ (6 + 3 * eta) := hpowPair
  have hpowThree : d ^ (3 + eta) ≤
      1296 * (n : ℝ) ^ (9 + 3 * eta) := by
    have h := selectedHostDegree_rpow_le_1296_mul
      (eta0 := eta0) (b := 3 + eta) hn0 (by simpa [d] using hd0)
        (by simpa [d] using hdSix) (by linarith) (by linarith)
    convert h using 1 <;> simp [d, eta] <;> ring_nf
  have hbudget0 : (0 : ℝ) ≤ jmRoleNumeratorBudget := by
    norm_num [jmRoleNumeratorBudget]
  have h1296 : (1296 : ℝ) ≤ jmRoleNumeratorBudget := by
    norm_num [jmRoleNumeratorBudget]
  have h145152 : (145152 : ℝ) ≤ jmRoleNumeratorBudget := by
    norm_num [jmRoleNumeratorBudget]
  have h12960000 : (12960000 : ℝ) ≤ jmRoleNumeratorBudget := by
    norm_num [jmRoleNumeratorBudget]
  have h435456 : (435456 : ℝ) ≤ jmRoleNumeratorBudget := by
    norm_num [jmRoleNumeratorBudget]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    calc
      d ^ (2 + eta) ≤ 1296 * (n : ℝ) ^ (6 + 3 * eta) := hpowPair
      _ ≤ jmRoleNumeratorBudget * (n : ℝ) ^ (6 + 3 * eta) :=
        mul_le_mul_of_nonneg_right h1296 (Real.rpow_nonneg hnR.le _)
      _ ≤ (1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * delta) := by
        simpa [eta, delta] using hweak
      _ ≤ jmPairRoleLower eta0 n a := hlower a
  · intro a
    calc
      d ^ (3 + eta) ≤ 1296 * (n : ℝ) ^ (9 + 3 * eta) := hpowThree
      _ ≤ jmRoleNumeratorBudget * (n : ℝ) ^ (9 + 3 * eta) :=
        mul_le_mul_of_nonneg_right h1296 (Real.rpow_nonneg hnR.le _)
      _ ≤ (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * delta) := by
        simpa [eta, delta] using hstrong
      _ ≤ (m : ℝ) * jmPairRoleLower eta0 n a := htripleBase a
  · intro a
    change (((16 * D : ℕ) : ℝ)) ≤
      jmPairRoleLower eta0 n a / d ^ (1 + eta)
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hdpos (1 + eta))).2
    calc
      (((16 * D : ℕ) : ℝ)) * d ^ (1 + eta) ≤
          (16 * (7 * (n : ℝ) ^ 3)) *
            (1296 * (n : ℝ) ^ (3 + 3 * eta)) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        gcongr
      _ = 145152 * (n : ℝ) ^ (6 + 3 * eta) := by
        calc
          16 * (7 * (n : ℝ) ^ 3) *
              (1296 * (n : ℝ) ^ (3 + 3 * eta)) =
              145152 * ((n : ℝ) ^ 3 * (n : ℝ) ^ (3 + 3 * eta)) := by ring
          _ = 145152 * (n : ℝ) ^ (6 + 3 * eta) := by
            rw [hpow3]
            congr 2
            ring
      _ ≤ jmRoleNumeratorBudget * (n : ℝ) ^ (6 + 3 * eta) :=
        mul_le_mul_of_nonneg_right h145152 (Real.rpow_nonneg hnR.le _)
      _ ≤ (1 / 80000 : ℝ) * (n : ℝ) ^ (7 - 2 * delta) := by
        simpa [eta, delta] using hweak
      _ ≤ jmPairRoleLower eta0 n a := hlower a
  · intro a
    change (((16 * D ^ 2 + 256 * k * (6 * n ^ 2) ^ 2 : ℕ) : ℝ)) ≤
      ((m : ℝ) * jmPairRoleLower eta0 n a) / d ^ (1 + eta)
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hdpos (1 + eta))).2
    calc
      (((16 * D ^ 2 + 256 * k * (6 * n ^ 2) ^ 2 : ℕ) : ℝ)) *
            d ^ (1 + eta) ≤
          (10000 * (n : ℝ) ^ 6) *
            (1296 * (n : ℝ) ^ (3 + 3 * eta)) := by
        gcongr
      _ = 12960000 * (n : ℝ) ^ (9 + 3 * eta) := by
        calc
          (10000 * (n : ℝ) ^ 6) *
              (1296 * (n : ℝ) ^ (3 + 3 * eta)) =
              12960000 * ((n : ℝ) ^ 6 * (n : ℝ) ^ (3 + 3 * eta)) := by ring
          _ = 12960000 * (n : ℝ) ^ (9 + 3 * eta) := by
            rw [hpow6]
            congr 2
            ring
      _ ≤ jmRoleNumeratorBudget * (n : ℝ) ^ (9 + 3 * eta) :=
        mul_le_mul_of_nonneg_right h12960000 (Real.rpow_nonneg hnR.le _)
      _ ≤ (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * delta) := by
        simpa [eta, delta] using hstrong
      _ ≤ (m : ℝ) * jmPairRoleLower eta0 n a := htripleBase a
  · intro a
    change (((48 * D : ℕ) : ℝ)) ≤
      ((m : ℝ) * jmPairRoleLower eta0 n a) / d ^ (2 + eta)
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hdpos (2 + eta))).2
    calc
      (((48 * D : ℕ) : ℝ)) * d ^ (2 + eta) ≤
          (48 * (7 * (n : ℝ) ^ 3)) *
            (1296 * (n : ℝ) ^ (6 + 3 * eta)) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        gcongr
      _ = 435456 * (n : ℝ) ^ (9 + 3 * eta) := by
        calc
          48 * (7 * (n : ℝ) ^ 3) *
              (1296 * (n : ℝ) ^ (6 + 3 * eta)) =
              435456 * ((n : ℝ) ^ 3 * (n : ℝ) ^ (6 + 3 * eta)) := by ring
          _ = 435456 * (n : ℝ) ^ (9 + 3 * eta) := by
            rw [hpow3]
            congr 2
            ring
      _ ≤ jmRoleNumeratorBudget * (n : ℝ) ^ (9 + 3 * eta) :=
        mul_le_mul_of_nonneg_right h435456 (Real.rpow_nonneg hnR.le _)
      _ ≤ (1 / 160000 : ℝ) * (n : ℝ) ^ (10 - 3 * delta) := by
        simpa [eta, delta] using hstrong
      _ ≤ (m : ℝ) * jmPairRoleLower eta0 n a := htripleBase a

/-- The one-uniform leave test has enough total mass.  This is the scalar
part; the retained-host degree sum supplies the actual test total. -/
theorem eventually_jmLeaveW1Scalar {eta0 : ℝ} (heta0 : 0 < eta0) :
    ∀ᶠ n : ℕ in atTop,
      (jmSelectedHostDegree eta0 n) ^ (1 + jmEta eta0) ≤
        ((n - 1 : ℕ) : ℝ) *
          (jmSelectedHostDegree eta0 n -
            AuxConcentration.universalHostDegreeError n
              (jmOldColors (jmDelta eta0) n)
              (jmDeletion (jmDelta eta0) n)) := by
  have heta : 0 < jmEta eta0 := jmEta_pos heta0
  have heta1 : jmEta eta0 < 1 := jmEta_lt_one heta0
  have hgap : 3 * jmEta eta0 < 1 := by
    have he : jmEta eta0 ≤ (1 / 100 : ℝ) := min_le_right _ _
    linarith
  have hgrowth := eventually_const_mul_rpow_le_rpow
    (C := (5184 : ℝ)) (a := 3 * jmEta eta0) (b := 1)
      (by norm_num) hgap
  filter_upwards [hgrowth,
    AuxConcentration.eventually_universalHostDegree_le_two_jmAuxDegreeReal
      heta0,
    AuxConcentration.eventually_jmAuxDegreeReal_le_universalHostDegree
      (jmDelta_pos heta0),
    AuxConcentration.eventually_universalHostDegreeError_le_rpow heta0,
    eventually_jmCoverMultiplicity_numerics heta0,
    eventually_ge_atTop (2 : ℕ)] with n hgrowth hdupper hauxd herror hcover hn
  let d := jmSelectedHostDegree eta0 n
  let eta := jmEta eta0
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnCast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have haux0 : 0 ≤ jmAuxDegreeReal (jmDelta eta0) n :=
    jmAuxDegreeReal_nonneg _ _
  have hd0 : 0 ≤ d := by
    exact haux0.trans (by simpa [d, jmSelectedHostDegree] using hauxd)
  have hdSix : d ≤ 6 * (n : ℝ) ^ 3 := by
    have hauxUpper := jmAuxDegreeReal_le_three_mul_cube
      (delta := jmDelta eta0) (jmDelta_pos heta0).le hn0
    have hd2 : d ≤ 2 * jmAuxDegreeReal (jmDelta eta0) n := by
      simpa [d, jmSelectedHostDegree] using hdupper
    linarith
  have hdeta := selectedHostDegree_rpow_le_1296_mul
    (eta0 := eta0) (b := eta) hn0 (by simpa [d] using hd0)
      (by simpa [d] using hdSix) heta.le (by linarith)
  have hfour : 4 * (d ^ eta) ≤ (n : ℝ) := by
    calc
      4 * (d ^ eta) ≤ 5184 * (n : ℝ) ^ (3 * eta) := by
        have hmul : 4 * ((jmSelectedHostDegree eta0 n) ^ eta) ≤
            4 * (1296 * ((n : ℝ) ^ (3 * eta))) :=
          mul_le_mul_of_nonneg_left hdeta (by norm_num)
        exact hmul.trans_eq (by ring)
      _ ≤ (n : ℝ) ^ (1 : ℝ) := by simpa [eta] using hgrowth
      _ = (n : ℝ) := Real.rpow_one _
  have herror' : AuxConcentration.universalHostDegreeError n
      (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) ≤
        d ^ (1 - eta) := by simpa [d, eta, jmSelectedHostDegree] using herror
  have heSmall : 8 * d ^ (1 - eta) + 2 ≤ d := by
    simpa [d, eta] using hcover.1
  have hhalf : d / 2 ≤ d -
      AuxConcentration.universalHostDegreeError n
        (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) := by
    linarith [Real.rpow_nonneg hd0 (1 - eta)]
  have htwo : 2 * (d ^ eta) ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hnCast]
    have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    let x := d ^ eta
    change 4 * x ≤ (n : ℝ) at hfour
    change 2 * x ≤ (n : ℝ) - 1
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact Real.rpow_nonneg hd0 _
    have hxHalf : 2 * x ≤ (n : ℝ) / 2 := by
      calc
        2 * x = (1 / 2 : ℝ) * (4 * x) := by ring
        _ ≤ (1 / 2 : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hfour (by norm_num)
        _ = (n : ℝ) / 2 := by ring
    have hnHalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    exact hxHalf.trans hnHalf
  have hfactor : d ^ (1 + eta) = d * (d ^ eta) := by
    rw [Real.rpow_add (by linarith [heSmall] : 0 < d), Real.rpow_one]
  rw [hfactor]
  nlinarith [mul_le_mul_of_nonneg_left htwo hd0,
    mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ ((n - 1 : ℕ) : ℝ))]

/-- The one-uniform leave total is the degree sum over all off-diagonal
graph vertices rooted at `x`. -/
theorem testTotal_leaveDegreeWeight_eq_sum_degree
    {n k : ℕ} (H : Hypergraph (AuxVertex n k)) (x : Fin n) :
    testTotal (leaveDegreeWeight H x) H 1 =
      ∑ y ∈ Finset.univ.filter (fun y : Fin n ↦ y ≠ x),
        (degree H (Sum.inl s(x, y)) : ℝ) := by
  rw [testTotal_leaveDegreeWeight H H (fun _ h ↦ h)]
  simp only [graphIncidence, degree, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyx : y ≠ x
  · simp [hyx]
  · simp [hyx]

/-- The common retained-host degree window gives the exact leave-test lower
bound needed for its W1 condition. -/
theorem leaveTotal_lower_of_universalHost
    {n k : ℕ} {qprob : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates qprob R)
    (x : Fin n) :
    ((n - 1 : ℕ) : ℝ) *
        (AuxConcentration.universalHostDegree n k qprob -
          AuxConcentration.universalHostDegreeError n k qprob) ≤
      testTotal
        (leaveDegreeWeight
          (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) x)
        (auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R) 1 := by
  rw [testTotal_leaveDegreeWeight_eq_sum_degree]
  have hcard : (Finset.univ.filter (fun y : Fin n ↦ y ≠ x)).card = n - 1 := by
    rw [show Finset.univ.filter (fun y : Fin n ↦ y ≠ x) =
        Finset.univ.erase x by ext y; simp]
    simp
  rw [← hcard]
  calc
    ((Finset.univ.filter (fun y : Fin n ↦ y ≠ x)).card : ℝ) *
        (AuxConcentration.universalHostDegree n k qprob -
          AuxConcentration.universalHostDegreeError n k qprob) =
        ∑ _y ∈ Finset.univ.filter (fun y : Fin n ↦ y ≠ x),
          (AuxConcentration.universalHostDegree n k qprob -
            AuxConcentration.universalHostDegreeError n k qprob) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y hy
      have hyx : y ≠ x := (Finset.mem_filter.mp hy).2
      have hxy : x ≠ y := Ne.symm hyx
      have hactive : AuxConcentration.ActiveAuxVertex R (Sum.inl s(x, y)) := by
        simp [AuxConcentration.ActiveAuxVertex, Sym2.IsDiag, hxy]
      have hnear := hhost.1 (Sum.inl s(x, y)) hactive
      have htarget : AuxConcentration.universalDegreeTarget n k qprob
          (Sum.inl s(x, y)) =
          AuxConcentration.universalGraphDegreeTarget n k qprob := by
        simp [AuxConcentration.universalDegreeTarget, Sym2.IsDiag, hxy]
      rw [abs_lt] at hnear
      simp only [AuxConcentration.universalDegreeDeviation] at hnear
      have hmin : min
          (AuxConcentration.universalGraphDegreeTarget n k qprob)
          (AuxConcentration.universalLabelDegreeTarget n k qprob) ≤
            AuxConcentration.universalGraphDegreeTarget n k qprob := min_le_left _ _
      simp only [AuxConcentration.universalHostDegree,
        AuxConcentration.universalHostDegreeError]
      rw [htarget] at hnear
      linarith

/-- Algebraic terminal leave residual.  Both the CFM error and the relative
degree-window loss are absorbed by the source `rho^2` scale. -/
theorem leaveResidual_le_two_rpow {eta0 : ℝ} {n : ℕ} {T : ℝ}
    (heta0 : 0 < eta0) (hn : 0 < n)
    (hd1 : 1 ≤ jmSelectedHostDegree eta0 n)
    (herror : AuxConcentration.universalHostDegreeError n
        (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) ≤
      (jmSelectedHostDegree eta0 n) ^ (1 - jmEta eta0))
    (herrRho : (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3) ≤
      (jmRho (jmDelta eta0) n) ^ 2)
    (htotal : ((n - 1 : ℕ) : ℝ) *
        (jmSelectedHostDegree eta0 n -
          AuxConcentration.universalHostDegreeError n
            (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n)) ≤ T) :
    ((n - 1 : ℕ) : ℝ) -
        (1 - (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3)) *
          (jmSelectedHostDegree eta0 n) ^ (-1 : ℝ) * T ≤
      2 * (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by
  let d := jmSelectedHostDegree eta0 n
  let eta := jmEta eta0
  let E := AuxConcentration.universalHostDegreeError n
    (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n)
  let err := d ^ (-(eta ^ 3))
  let N := ((n - 1 : ℕ) : ℝ)
  have hdpos : 0 < d := by simpa [d] using lt_of_lt_of_le zero_lt_one hd1
  have hd0 : 0 ≤ d := hdpos.le
  have heta0' : 0 < eta := by simpa [eta] using jmEta_pos heta0
  have heta1 : eta < 1 := by simpa [eta] using jmEta_lt_one heta0
  have hetaCube : eta ^ 3 ≤ eta := by
    have hsquare : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
    calc
      eta ^ 3 = eta * eta ^ 2 := by ring
      _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hsquare heta0'.le
      _ = eta := by ring
  have hE0 : 0 ≤ E := by
    dsimp [E, AuxConcentration.universalHostDegreeError]
    have hminmax : min
        (AuxConcentration.universalGraphDegreeTarget n
          (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n))
        (AuxConcentration.universalLabelDegreeTarget n
          (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n)) ≤
      max
        (AuxConcentration.universalGraphDegreeTarget n
          (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n))
        (AuxConcentration.universalLabelDegreeTarget n
          (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n)) :=
      min_le_max
    have hpow0 : 0 ≤ (n : ℝ) ^ (8 / 3 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith
  have herr0 : 0 ≤ err := Real.rpow_nonneg hd0 _
  have herr1 : err ≤ 1 := by
    dsimp [err]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1
      (neg_nonpos.mpr (pow_nonneg heta0'.le 3))
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNn : N ≤ (n : ℝ) := by
    dsimp [N]
    exact_mod_cast Nat.sub_le n 1
  have hInvMul : d ^ (-1 : ℝ) * d = 1 := by
    rw [Real.rpow_neg hd0, Real.rpow_one]
    exact inv_mul_cancel₀ hdpos.ne'
  have hInvErrorPower : d ^ (-1 : ℝ) * d ^ (1 - eta) = d ^ (-eta) := by
    rw [← Real.rpow_add hdpos]
    congr 1
    ring
  have hEtaErr : d ^ (-eta) ≤ err := by
    dsimp [err]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  let u := d ^ (-1 : ℝ) * E
  have hu0 : 0 ≤ u := mul_nonneg (Real.rpow_nonneg hd0 _) hE0
  have huErr : u ≤ err := by
    calc
      u ≤ d ^ (-1 : ℝ) * d ^ (1 - eta) :=
        mul_le_mul_of_nonneg_left (by simpa [E, d, eta] using herror)
          (Real.rpow_nonneg hd0 _)
      _ = d ^ (-eta) := hInvErrorPower
      _ ≤ err := hEtaErr
  let c := (1 - err) * d ^ (-1 : ℝ)
  have hc0 : 0 ≤ c := mul_nonneg (sub_nonneg.mpr herr1)
    (Real.rpow_nonneg hd0 _)
  have hmono : c * (N * (d - E)) ≤ c * T :=
    mul_le_mul_of_nonneg_left (by simpa [N, d, E] using htotal) hc0
  have hres : N - c * T ≤ 2 * N * err := by
    have hunit : d ^ (-1 : ℝ) * (d - E) = 1 - u := by
      dsimp [u]
      rw [mul_sub, hInvMul]
    calc
      N - c * T ≤ N - c * (N * (d - E)) := sub_le_sub_left hmono _
      _ = N * (1 - (1 - err) * (1 - u)) := by
        dsimp [c]
        calc
          N - (1 - err) * d ^ (-1 : ℝ) * (N * (d - E)) =
              N - N * (1 - err) * (d ^ (-1 : ℝ) * (d - E)) := by ring
          _ = N * (1 - (1 - err) * (1 - u)) := by rw [hunit]; ring
      _ ≤ 2 * N * err := by
        have heu0 : 0 ≤ err * u := mul_nonneg herr0 hu0
        nlinarith [mul_le_mul_of_nonneg_left huErr hN0,
          mul_nonneg hN0 heu0]
  have hscale : (n : ℝ) * (jmRho (jmDelta eta0) n) ^ 2 =
      (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by
    rw [jmRho_sq_eq_base_rpow hn]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      (n : ℝ) * (n : ℝ) ^ (-(2 * jmDelta eta0)) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(2 * jmDelta eta0)) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -(2 * jmDelta eta0)) :=
        (Real.rpow_add hnR 1 (-(2 * jmDelta eta0))).symm
      _ = (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by congr 1
  calc
    N - c * T ≤ 2 * N * err := hres
    _ ≤ 2 * (n : ℝ) * (jmRho (jmDelta eta0) n) ^ 2 := by
      gcongr
    _ = 2 * (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by
      calc
        2 * (n : ℝ) * (jmRho (jmDelta eta0) n) ^ 2 =
            2 * ((n : ℝ) * (jmRho (jmDelta eta0) n) ^ 2) := by ring
        _ = 2 * (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by rw [hscale]

/-- The floor-defined cover leaves only one relative-error scale in the
coefficient of every role-pair residual. -/
theorem jmRoleCrossCoefficient_bounds {eta0 : ℝ} {n : ℕ}
    (heta0 : 0 < eta0)
    (hd1 : 1 ≤ jmSelectedHostDegree eta0 n)
    (hsmall : 8 * (jmSelectedHostDegree eta0 n) ^ (1 - jmEta eta0) + 2 ≤
      jmSelectedHostDegree eta0 n) :
    let d := jmSelectedHostDegree eta0 n
    let eta := jmEta eta0
    let err := d ^ (-(eta ^ 3))
    let m := jmCoverMultiplicity eta0 n
    0 ≤ (1 + err) * d ^ (-2 : ℝ) -
          (1 - err) * d ^ (-3 : ℝ) * (m : ℝ) ∧
      (1 + err) * d ^ (-2 : ℝ) -
          (1 - err) * d ^ (-3 : ℝ) * (m : ℝ) ≤
        6 * err * d ^ (-2 : ℝ) := by
  dsimp only
  let d := jmSelectedHostDegree eta0 n
  let eta := jmEta eta0
  let err := d ^ (-(eta ^ 3))
  let m := jmCoverMultiplicity eta0 n
  let e := d ^ (1 - eta)
  have hdpos : 0 < d := by simpa [d] using lt_of_lt_of_le zero_lt_one hd1
  have hd0 : 0 ≤ d := hdpos.le
  have heta0' : 0 < eta := by simpa [eta] using jmEta_pos heta0
  have heta1 : eta < 1 := by simpa [eta] using jmEta_lt_one heta0
  have hetaCube : eta ^ 3 ≤ eta := by
    have hsquare : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
    calc
      eta ^ 3 = eta * eta ^ 2 := by ring
      _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hsquare heta0'.le
      _ = eta := by ring
  have he0 : 0 ≤ e := Real.rpow_nonneg hd0 _
  have he1 : 1 ≤ e := by
    dsimp [e]
    exact Real.one_le_rpow hd1 (sub_nonneg.mpr heta1.le)
  have hx0 : 0 ≤ d - 3 * e := by
    have hs : 8 * e + 2 ≤ d := by simpa [d, eta, e] using hsmall
    linarith
  have hmUpper : (m : ℝ) ≤ d := by
    have hf : ((Nat.floor (d - 3 * e) : ℕ) : ℝ) ≤ d - 3 * e :=
      Nat.floor_le hx0
    have hm : m = Nat.floor (d - 3 * e) := by
      simp [m, jmCoverMultiplicity, d, eta, e]
    rw [hm]
    linarith
  have hdm : d - (m : ℝ) ≤ 4 * e := by
    have hf : d - 3 * e <
        ((Nat.floor (d - 3 * e) : ℕ) : ℝ) + 1 := by
      simpa using Nat.lt_floor_add_one (d - 3 * e)
    have hm : m = Nat.floor (d - 3 * e) := by
      simp [m, jmCoverMultiplicity, d, eta, e]
    rw [← hm] at hf
    linarith
  have herr0 : 0 ≤ err := by
    dsimp [err]
    exact Real.rpow_nonneg hd0 _
  have herr1 : err ≤ 1 := by
    dsimp [err]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1
      (neg_nonpos.mpr (pow_nonneg heta0'.le 3))
  have hetaErr : d ^ (-eta) ≤ err := by
    dsimp [err]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hp2 : d ^ (-2 : ℝ) = d * d ^ (-3 : ℝ) := by
    calc
      d ^ (-2 : ℝ) = d ^ ((1 : ℝ) + (-3 : ℝ)) := by norm_num
      _ = d ^ (1 : ℝ) * d ^ (-3 : ℝ) :=
        Real.rpow_add hdpos 1 (-3)
      _ = d * d ^ (-3 : ℝ) := by rw [Real.rpow_one]
  have he3 : e * d ^ (-3 : ℝ) = d ^ (-2 - eta) := by
    dsimp [e]
    rw [← Real.rpow_add hdpos]
    congr 1
    ring
  have heta2 : d ^ (-eta) * d ^ (-2 : ℝ) = d ^ (-2 - eta) := by
    rw [← Real.rpow_add hdpos]
    congr 1
    ring
  let K := (1 + err) * d ^ (-2 : ℝ) -
    (1 - err) * d ^ (-3 : ℝ) * (m : ℝ)
  have hKform : K = d ^ (-3 : ℝ) *
      (d - (m : ℝ) + err * (d + (m : ℝ))) := by
    dsimp [K]
    rw [hp2]
    ring
  have hK0 : 0 ≤ K := by
    rw [hKform]
    exact mul_nonneg (Real.rpow_nonneg hd0 _)
      (add_nonneg (sub_nonneg.mpr hmUpper)
        (mul_nonneg herr0 (add_nonneg hd0 (Nat.cast_nonneg m))))
  have hbracket : d - (m : ℝ) + err * (d + (m : ℝ)) ≤
      4 * e + 2 * err * d := by
    have hsum : d + (m : ℝ) ≤ 2 * d := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hsum herr0]
  have hKUpper : K ≤ 6 * err * d ^ (-2 : ℝ) := by
    calc
      K = d ^ (-3 : ℝ) *
          (d - (m : ℝ) + err * (d + (m : ℝ))) := hKform
      _ ≤ d ^ (-3 : ℝ) * (4 * e + 2 * err * d) :=
        mul_le_mul_of_nonneg_left hbracket (Real.rpow_nonneg hd0 _)
      _ = 4 * d ^ (-2 - eta) + 2 * err * d ^ (-2 : ℝ) := by
        rw [← he3, hp2]
        ring
      _ ≤ 4 * (err * d ^ (-2 : ℝ)) + 2 * err * d ^ (-2 : ℝ) := by
        rw [← heta2]
        gcongr
      _ = 6 * err * d ^ (-2 : ℝ) := by ring
  simpa [K, d, eta, err, m] using And.intro hK0 hKUpper

/-- Summing the nine role-pair residual envelopes still fits one fixed
multiple of the natural `n^(1-2δ)` leave scale. -/
theorem jmRoleCrossSum_le_40000_rpow {eta0 : ℝ} {n : ℕ}
    (heta0 : 0 < eta0) (hn : 0 < n)
    (hk : jmOldColors (jmDelta eta0) n ≤ n)
    (hd1 : 1 ≤ jmSelectedHostDegree eta0 n)
    (hsmall : 8 * (jmSelectedHostDegree eta0 n) ^ (1 - jmEta eta0) + 2 ≤
      jmSelectedHostDegree eta0 n)
    (hscale : jmDegreeScale (jmDelta eta0) n ≤
      jmSelectedHostDegree eta0 n)
    (herrRho : (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3) ≤
      (jmRho (jmDelta eta0) n) ^ 2)
    (a : JMCDistinctRootPair n) :
    (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
      let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
      (((1 + (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3)) *
              (jmSelectedHostDegree eta0 n) ^ (-2 : ℝ) -
            (1 - (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3)) *
              (jmSelectedHostDegree eta0 n) ^ (-3 : ℝ) *
                (jmCoverMultiplicity eta0 n : ℝ)) *
        (8 * (AuxConcentration.pairRoleTarget
            (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) b +
          (AuxConcentration.universalPairRoleDeviation n b +
            AuxConcentration.universalPairRoleMeanError n b))))) ≤
      40000 * (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by
  let delta := jmDelta eta0
  let eta := jmEta eta0
  let d := jmSelectedHostDegree eta0 n
  let err := d ^ (-(eta ^ 3))
  let m := jmCoverMultiplicity eta0 n
  let rho := jmRho delta n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hdpos : 0 < d := by simpa [d] using lt_of_lt_of_le zero_lt_one hd1
  have hd0 : 0 ≤ d := hdpos.le
  have hspos : 0 < jmDegreeScale delta n := by
    unfold jmDegreeScale
    exact Real.rpow_pos_of_pos hnR _
  have hscale' : jmDegreeScale delta n ≤ d := by
    simpa [delta, d] using hscale
  have hsquare : (jmDegreeScale delta n) ^ (2 : ℝ) ≤ d ^ (2 : ℝ) :=
    Real.rpow_le_rpow hspos.le hscale' (by norm_num)
  have hinv : d ^ (-2 : ℝ) ≤ (n : ℝ) ^ (-6 + 2 * delta) := by
    have hi : d ^ (-2 : ℝ) ≤ (jmDegreeScale delta n) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hd0, Real.rpow_neg hspos.le]
      simpa [one_div] using one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos hspos (2 : ℝ)) hsquare
    calc
      d ^ (-2 : ℝ) ≤ (jmDegreeScale delta n) ^ (-2 : ℝ) := hi
      _ = ((n : ℝ) ^ (3 - delta)) ^ (-2 : ℝ) := rfl
      _ = (n : ℝ) ^ ((3 - delta) * (-2 : ℝ)) :=
        (Real.rpow_mul hnR.le (3 - delta) (-2)).symm
      _ = (n : ℝ) ^ (-6 + 2 * delta) := by congr 1; ring
  have hcoeff := jmRoleCrossCoefficient_bounds heta0 hd1 hsmall
  have hcoeff0 : 0 ≤ (1 + err) * d ^ (-2 : ℝ) -
      (1 - err) * d ^ (-3 : ℝ) * (m : ℝ) := by
    simpa [d, eta, err, m] using hcoeff.1
  have hcoeffUpper : (1 + err) * d ^ (-2 : ℝ) -
      (1 - err) * d ^ (-3 : ℝ) * (m : ℝ) ≤
        6 * rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta) := by
    calc
      (1 + err) * d ^ (-2 : ℝ) -
            (1 - err) * d ^ (-3 : ℝ) * (m : ℝ) ≤
          6 * err * d ^ (-2 : ℝ) := by
            simpa [d, eta, err, m] using hcoeff.2
      _ ≤ 6 * rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta) := by
        have he : err ≤ rho ^ 2 := by
          simpa [err, d, eta, rho, delta] using herrRho
        gcongr
  have hrhoPow : rho ^ 2 = (n : ℝ) ^ (-(2 * delta)) := by
    simpa [rho] using jmRho_sq_eq_base_rpow (delta := delta) hn
  have hleading :
      (rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta)) *
          (n : ℝ) ^ (7 - 2 * delta) =
        (n : ℝ) ^ (1 - 2 * delta) := by
    rw [hrhoPow, ← Real.rpow_add hnR, ← Real.rpow_add hnR]
    congr 1
    ring
  have hdevScale :
      (rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta)) *
          (n : ℝ) ^ (20 / 3 : ℝ) ≤
        (n : ℝ) ^ (1 - 2 * delta) := by
    rw [hrhoPow, ← Real.rpow_add hnR, ← Real.rpow_add hnR]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hd := jmDelta_le_one_ten_thousandth eta0
    linarith
  have honeScale : 0 ≤ (n : ℝ) ^ (1 - 2 * delta) :=
    Real.rpow_nonneg hnR.le _
  have hterm (rx ry : JMCPaintRole) :
      let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
      (((1 + err) * d ^ (-2 : ℝ) -
            (1 - err) * d ^ (-3 : ℝ) * (m : ℝ)) *
        (8 * (AuxConcentration.pairRoleTarget
            (jmOldColors delta n) (jmDeletion delta n) b +
          (AuxConcentration.universalPairRoleDeviation n b +
            AuxConcentration.universalPairRoleMeanError n b)))) ≤
        3216 * (n : ℝ) ^ (1 - 2 * delta) := by
    dsimp only
    let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
    have htarget := pairRoleTarget_jm_upper (delta := delta) hn
      (by simpa [delta] using hk) b
    have hpow6 : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 / 3 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have hloss : AuxConcentration.universalPairRoleDeviation n b +
        AuxConcentration.universalPairRoleMeanError n b ≤
          66 * (n : ℝ) ^ (20 / 3 : ℝ) := by
      simp only [AuxConcentration.universalPairRoleDeviation,
        AuxConcentration.universalPairRoleMeanError]
      nlinarith
    have hU0 : 0 ≤ 8 * (AuxConcentration.pairRoleTarget
        (jmOldColors delta n) (jmDeletion delta n) b +
          (AuxConcentration.universalPairRoleDeviation n b +
            AuxConcentration.universalPairRoleMeanError n b)) := by
      have hq0 : 0 ≤ jmDeletion delta n := (jmDeletion_pos hn).le
      have hq1 : jmDeletion delta n ≤ 1 := (jmDeletion_lt_one hn).le
      have hp0 : 0 ≤ 1 - jmDeletion delta n := sub_nonneg.mpr hq1
      have hleft0 : 0 ≤ AuxConcentration.roleLeadingCoefficient b.leftRole :=
        (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
          (AuxConcentration.roleLeadingCoefficient_mem_Icc b.leftRole).1
      have hright0 : 0 ≤ AuxConcentration.roleLeadingCoefficient b.rightRole :=
        (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
          (AuxConcentration.roleLeadingCoefficient_mem_Icc b.rightRole).1
      have ht0 : 0 ≤ AuxConcentration.pairRoleTarget
          (jmOldColors delta n) (jmDeletion delta n) b := by
        rw [AuxConcentration.pairRoleTarget,
          AuxConcentration.leftCoefficient_eq_roleLeadingCoefficient,
          AuxConcentration.rightCoefficient_eq_roleLeadingCoefficient]
        positivity
      have hl0 : 0 ≤ AuxConcentration.universalPairRoleDeviation n b +
          AuxConcentration.universalPairRoleMeanError n b := by
        simp only [AuxConcentration.universalPairRoleDeviation,
          AuxConcentration.universalPairRoleMeanError]
        positivity
      exact mul_nonneg (by norm_num) (add_nonneg ht0 hl0)
    calc
      ((1 + err) * d ^ (-2 : ℝ) -
            (1 - err) * d ^ (-3 : ℝ) * (m : ℝ)) *
          (8 * (AuxConcentration.pairRoleTarget
              (jmOldColors delta n) (jmDeletion delta n) b +
            (AuxConcentration.universalPairRoleDeviation n b +
              AuxConcentration.universalPairRoleMeanError n b))) ≤
          (6 * rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta)) *
            (8 * ((n : ℝ) ^ (7 - 2 * delta) +
              66 * (n : ℝ) ^ (20 / 3 : ℝ))) := by
        gcongr
      _ = 48 * ((rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta)) *
          (n : ℝ) ^ (7 - 2 * delta)) +
        (48 * 66) * ((rho ^ 2 * (n : ℝ) ^ (-6 + 2 * delta)) *
          (n : ℝ) ^ (20 / 3 : ℝ)) := by ring
      _ ≤ 48 * (n : ℝ) ^ (1 - 2 * delta) +
          (48 * 66) * (n : ℝ) ^ (1 - 2 * delta) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hleading.le (by norm_num))
          (mul_le_mul_of_nonneg_left hdevScale (by norm_num))
      _ = 3216 * (n : ℝ) ^ (1 - 2 * delta) := by ring
  calc
    (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
      let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
      (((1 + (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3)) *
              (jmSelectedHostDegree eta0 n) ^ (-2 : ℝ) -
            (1 - (jmSelectedHostDegree eta0 n) ^ (-(jmEta eta0) ^ 3)) *
              (jmSelectedHostDegree eta0 n) ^ (-3 : ℝ) *
                (jmCoverMultiplicity eta0 n : ℝ)) *
        (8 * (AuxConcentration.pairRoleTarget
            (jmOldColors (jmDelta eta0) n) (jmDeletion (jmDelta eta0) n) b +
          (AuxConcentration.universalPairRoleDeviation n b +
            AuxConcentration.universalPairRoleMeanError n b))))) ≤
        ∑ _rx : JMCPaintRole, ∑ _ry : JMCPaintRole,
          3216 * (n : ℝ) ^ (1 - 2 * delta) := by
      apply Finset.sum_le_sum
      intro rx _
      apply Finset.sum_le_sum
      intro ry _
      simpa [delta, eta, d, err, m] using hterm rx ry
    _ = 28944 * (n : ℝ) ^ (1 - 2 * delta) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show Fintype.card JMCPaintRole = 3 by decide]
      ring
    _ ≤ 40000 * (n : ℝ) ^ (1 - 2 * jmDelta eta0) := by
      simpa [delta] using
        mul_le_mul_of_nonneg_right (by norm_num : (28944 : ℝ) ≤ 40000)
          honeScale

/-- The sharp same-colour half of the retained-host codegree package bounds
every paint fibre; diagonal oriented pairs have empty fibre. -/
theorem paintFiber_card_le_of_retainedHostCodegreeBounds
    {n : ℕ} {delta : ℝ}
    {R : RetainedLabels n (jmOldColors delta n)}
    (hcodeg : AuxConcentration.UniversalRetainedHostCodegreeBounds delta R)
    (p : OrientedPaint n (jmOldColors delta n)) :
    (paintFiber
      (auxiliaryHypergraph
        (AuxConcentration.allTriangleBlocks n (jmOldColors delta n)) R) p).card ≤
      jmPairCodegreeCeil 5 0 delta n := by
  classical
  let H := auxiliaryHypergraph
    (AuxConcentration.allTriangleBlocks n (jmOldColors delta n)) R
  by_cases hxy : p.left = p.right
  · have hempty : paintFiber H p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have he' := Finset.mem_filter.mp he
      have hv : p.auxTriple.1 ∈ vertexFinset H :=
        mem_vertexFinset.mpr ⟨e, he'.1, he'.2.1⟩
      have ha := AuxConcentration.active_of_mem_vertexFinset_auxiliaryHypergraph hv
      simp [AuxConcentration.ActiveAuxVertex, OrientedPaint.auxTriple, hxy] at ha
    rw [hempty]
    simp
  · let a : AuxConcentration.SameColorIndex n (jmOldColors delta n) :=
      ⟨p.color, p.left, p.right⟩
    by_cases hempty : paintFiber H p = ∅
    · rw [hempty]
      simp
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have he' := Finset.mem_filter.mp he
      have hleftVertex : p.auxTriple.2.1 ∈ vertexFinset H :=
        mem_vertexFinset.mpr ⟨e, he'.1, he'.2.2.1⟩
      have hrightVertex : p.auxTriple.2.2 ∈ vertexFinset H :=
        mem_vertexFinset.mpr ⟨e, he'.1, he'.2.2.2⟩
      have hleft :=
        AuxConcentration.active_of_mem_vertexFinset_auxiliaryHypergraph hleftVertex
      have hright :=
        AuxConcentration.active_of_mem_vertexFinset_auxiliaryHypergraph hrightVertex
      have hsharp := hcodeg.2 a hxy (by
        simpa [a, AuxConcentration.ActiveAuxVertex,
          OrientedPaint.auxTriple] using hleft) (by
        simpa [a, AuxConcentration.ActiveAuxVertex,
          OrientedPaint.auxTriple] using hright)
      calc
        (paintFiber H p).card ≤
            codegree H {p.auxTriple.2.1, p.auxTriple.2.2} :=
          paintFiber_card_le_sameColorCodegree H p
        _ ≤ jmPairCodegreeCeil 5 0 delta n := by
          simpa [H, a, OrientedPaint.auxTriple] using hsharp

/-- The exact eventual input produced by retained-label concentration and the
finite host/count estimates.  Quantifying over the conflict-free theorem's
thresholds permits the exponent hierarchy to be selected only after its
existential small parameter has been opened. -/
def HasEventualJMCInstances (ell : ℕ) (C C0 : ℝ) : Prop :=
  ∀ eta0 : ℝ, 0 < eta0 → ∀ d0 : ℝ,
    ∀ᶠ n : ℕ in atTop,
      ∃ d : ℝ,
      ∃ R : RetainedLabels n (jmOldColors (jmDelta eta0) n),
        d0 ≤ d ∧
        IsSpecializedCFMInstance
          (auxiliaryHypergraph
            (AuxConcentration.allTriangleBlocks n
              (jmOldColors (jmDelta eta0) n)) R)
          (alternatingCycleConflicts
            (AuxConcentration.allTriangleBlocks n
              (jmOldColors (jmDelta eta0) n)) R)
          d (jmEta eta0) ell jmcTestUniformity
          (jmcTestWeight
            (AuxConcentration.allTriangleBlocks n
              (jmOldColors (jmDelta eta0) n)) R) ∧
        RoleTrackedHostBounds
          (jmCeilLeaveBound C C0 (jmDelta eta0) n)
          (AuxConcentration.allTriangleBlocks n
            (jmOldColors (jmDelta eta0) n)) R d
          (Real.rpow d (-((jmEta eta0) ^ 3)))

/-- Unconditional retained hosts, sharp conflict counts, and all corrected
role tests furnish the exact eventual instances used by the upper bound. -/
theorem exists_nonnegative_hasEventualJMCInstances :
    ∃ C C0 : ℝ, 0 ≤ C ∧ 0 ≤ C0 ∧
      HasEventualJMCInstances jmConflictBudget C C0 := by
  refine ⟨40000, 0, by norm_num, by norm_num, ?_⟩
  intro eta0 heta0 d0
  filter_upwards [
    AuxConcentration.eventually_exists_joosMubayi_retained_host_for_cfm
      heta0 (max d0 4),
    eventually_jmCoverMultiplicity_numerics heta0,
    eventually_jmcTrackedTestNumerics heta0,
    eventually_jmLeaveW1Scalar heta0,
    eventually_jmOldColors_le (jmDelta_pos heta0),
    eventually_ge_atTop (1 : ℕ),
    eventually_jm_commonLink_n8_le_auxDegree heta0,
    eventually_jmActiveVertexPolynomial_le_auxDegree_exponential heta0,
    eventually_jmcTrackedIndex_le_auxDegree_exponential heta0,
    eventually_jmCeilConflictCount_comparisons jmConflictBudget heta0
      (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 0)
      jmConflictBudget_absorbs_paintFiber,
    eventually_auxDegree_cfmError_le_rho_sq heta0,
    eventually_jmDegreeScale_le_auxDegree (jmDelta_pos heta0),
    eventually_nat_const_mul_sq_le_auxDegree_one_sub_eta 6 heta0]
      with n hexists hcoverNum htestNum hleaveScalar hk hn hW3Aux
        hvertexAux hindexAux hconflict herrorAux hscaleAux hcodegAux
  obtain ⟨R, hhost, hcodeg, harith⟩ := hexists
  let delta := jmDelta eta0
  let eta := jmEta eta0
  let k := jmOldColors delta n
  let d := jmSelectedHostDegree eta0 n
  let m := jmCoverMultiplicity eta0 n
  let L := jmPairCodegreeCeil 5 0 delta n
  let B := jmCeilLeaveBound 40000 0 delta n
  let H := auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R
  let C := alternatingCycleConflicts (AuxConcentration.allTriangleBlocks n k) R
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have heta0' : 0 < eta := by simpa [eta] using jmEta_pos heta0
  have heta1 : eta < 1 := by simpa [eta] using jmEta_lt_one heta0
  have hdelta0 : 0 < delta := by simpa [delta] using jmDelta_pos heta0
  have hk' : k ≤ n := by simpa [k, delta] using hk
  change (max d0 4 ≤ d ∧ jmAuxDegreeReal delta n ≤ d ∧
      d ≤ 2 * jmAuxDegreeReal delta n ∧
      AuxConcentration.universalHostDegreeError n k (jmDeletion delta n) ≤
        d ^ (1 - eta)) at harith
  have hd0cut : d0 ≤ d := le_trans (le_max_left _ _) harith.1
  have hd4 : (4 : ℝ) ≤ d := le_trans (le_max_right _ _) harith.1
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hdpos : 0 < d := by linarith
  have hd0 : 0 ≤ d := hdpos.le
  have haux0 : 0 ≤ jmAuxDegreeReal delta n := jmAuxDegreeReal_nonneg _ _
  have hauxd : jmAuxDegreeReal delta n ≤ d := harith.2.1
  have hscale0 : jmDegreeScale delta n ≤ jmAuxDegreeReal delta n := by
    simpa [delta] using hscaleAux
  have hscale : jmDegreeScale delta n ≤ d := hscale0.trans hauxd
  have hcover := jmCoverMultiplicity_bounds heta0
    (by simpa [d, eta] using hcoverNum.1)
    (by simpa [d, eta] using hcoverNum.2)
    (by simpa [d, eta, delta, k, jmSelectedHostDegree] using harith.2.2.2)
  have hgap : AuxConcentration.universalHostDegreeError n k
      (jmDeletion delta n) < d := by
    simpa [d, eta, delta, k] using hcover.2.2.2
  have hcoverScale : (((m + 16 * (6 * n ^ 2) : ℕ) : ℝ)) ≤
      d - AuxConcentration.universalHostDegreeError n k
        (jmDeletion delta n) := by
    simpa [d, eta, delta, k, m] using hcover.2.2.1
  have herrD : d ^ (-(eta ^ 3)) ≤
      (jmAuxDegreeReal delta n) ^ (-(eta ^ 3)) := by
    have hauxpos : 0 < jmAuxDegreeReal delta n := by
      have hspos : 0 < jmDegreeScale delta n := by
        unfold jmDegreeScale
        exact Real.rpow_pos_of_pos hnR _
      exact hspos.trans_le (by simpa [delta] using hscaleAux)
    rw [Real.rpow_neg hd0, Real.rpow_neg hauxpos.le]
    simpa [one_div] using one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hauxpos (eta ^ 3))
      (Real.rpow_le_rpow hauxpos.le hauxd (pow_nonneg heta0'.le 3))
  have herrRhoAux : (jmAuxDegreeReal delta n) ^ (-(eta ^ 3)) ≤
      (jmRho delta n) ^ 2 := by
    simpa [delta, eta] using herrorAux
  have herrRho : d ^ (-(eta ^ 3)) ≤ (jmRho delta n) ^ 2 :=
    herrD.trans herrRhoAux
  have herrOne : d ^ (-(eta ^ 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hd1
      (neg_nonpos.mpr (pow_nonneg heta0'.le 3))
  have hW3Base : ((566231040 * n ^ 8 : ℕ) : ℝ) ≤
      (jmAuxDegreeReal delta n) ^ (3 - eta) := by
    simpa [delta, eta] using hW3Aux
  have hW3 : ((566231040 * n ^ 8 : ℕ) : ℝ) ≤ d ^ (3 - eta) :=
    hW3Base.trans (Real.rpow_le_rpow haux0 hauxd (by linarith))
  have hcodegreeBase : ((6 * n ^ 2 : ℕ) : ℝ) ≤
      (jmAuxDegreeReal delta n) ^ (1 - eta) := by
    simpa [delta, eta] using hcodegAux
  have hcodegreeScale : ((6 * n ^ 2 : ℕ) : ℝ) ≤ d ^ (1 - eta) :=
    hcodegreeBase.trans (Real.rpow_le_rpow haux0 hauxd (by linarith))
  have hvertex : ((vertexFinset H).card : ℝ) ≤
      Real.exp (d ^ (eta ^ 3)) := by
    calc
      ((vertexFinset H).card : ℝ) ≤
          (((n + 1).choose 2 + n * k : ℕ) : ℝ) := by
        exact_mod_cast hhost.2.2.2.2
      _ ≤ Real.exp ((jmAuxDegreeReal delta n) ^ (eta ^ 3)) := by
        simpa [delta, eta, k] using hvertexAux
      _ ≤ Real.exp (d ^ (eta ^ 3)) := by
        exact Real.exp_le_exp.mpr
          (Real.rpow_le_rpow haux0 hauxd (pow_nonneg heta0'.le 3))
  have hindex : ((Fintype.card (JMCTrackedIndex n) : ℕ) : ℝ) ≤
      Real.exp (d ^ (eta ^ 3)) := by
    have hbase : ((Fintype.card (JMCTrackedIndex n) : ℕ) : ℝ) ≤
        Real.exp ((jmAuxDegreeReal delta n) ^ (eta ^ 3)) := by
      simpa [delta, eta] using hindexAux
    exact hbase.trans (Real.exp_le_exp.mpr
      (Real.rpow_le_rpow haux0 hauxd (pow_nonneg heta0'.le 3)))
  have hpaint : ∀ p : OrientedPaint n k,
      (paintFiber H p).card ≤ L := by
    intro p
    simpa [H, L, k, delta] using
      paintFiber_card_le_of_retainedHostCodegreeBounds hcodeg p
  have hbounded : IsBounded C d jmConflictBudget eta := by
    apply alternatingCycleConflicts_isBounded_of_paintFiber
      (AuxConcentration.allTriangleBlocks n k) R d eta jmConflictBudget L hd0
        four_le_jmConflictBudget hpaint
    · exact hconflict.1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow haux0 hauxd (by norm_num))
        (Nat.cast_nonneg jmConflictBudget))
    · exact hconflict.2.1.trans
        (Real.rpow_le_rpow haux0 hauxd (by linarith))
    · exact hconflict.2.2.trans
        (Real.rpow_le_rpow haux0 hauxd (by linarith))
  have hleaveTotal (x : Fin n) : d ^ (1 + eta) ≤
      testTotal (leaveDegreeWeight H x) H 1 := by
    have hscalar : d ^ (1 + eta) ≤ ((n - 1 : ℕ) : ℝ) *
        (d - AuxConcentration.universalHostDegreeError n k
          (jmDeletion delta n)) := by
      simpa [d, eta, delta, k] using hleaveScalar
    have htotal : ((n - 1 : ℕ) : ℝ) *
        (d - AuxConcentration.universalHostDegreeError n k
          (jmDeletion delta n)) ≤ testTotal (leaveDegreeWeight H x) H 1 := by
      simpa [H, d, delta, k, jmSelectedHostDegree] using
        leaveTotal_lower_of_universalHost hhost x
    exact hscalar.trans htotal
  have htrackable : ∀ i : JMCTrackedIndex n,
      IsTrackable H C (jmcTestUniformity i) jmConflictBudget d eta
        (jmcTestWeight (AuxConcentration.allTriangleBlocks n k) R i) := by
    apply all_jmcTestWeight_isTrackable_of_host hhost hk' hd0
      (by norm_num [jmConflictBudget]) hgap hcoverScale hW3 hleaveTotal
    · intro a
      simpa [jmPairRoleLower, d, eta, delta, k] using htestNum.pairW1 a
    · intro a
      simpa [jmPairRoleLower, d, eta, delta, k, m] using htestNum.tripleW1 a
    · intro a
      simpa [jmPairRoleLower, d, eta, delta, k] using htestNum.pairExtension a
    · intro a
      simpa [jmPairRoleLower, d, eta, delta, k, m] using
        htestNum.tripleExtensionOne a
    · intro a
      simpa [jmPairRoleLower, d, eta, delta, k, m] using
        htestNum.tripleExtensionTwo a
  have hinstance : IsSpecializedCFMInstance H C d eta jmConflictBudget
      jmcTestUniformity
      (jmcTestWeight (AuxConcentration.allTriangleBlocks n k) R) := by
    refine ⟨(by intro e he; exact auxiliaryHypergraph_uniform _ R he),
      alternatingCycleConflicts_isConflictSystem _ R,
      four_le_jmConflictBudget,
      (fun c hc ↦ alternatingCycleConflicts_uniform _ R hc),
      heta0', heta1, hd1, hvertex, ?_, ?_, hbounded, hindex, ?_⟩
    · intro v hv
      have hw := hhost.2.2.2.1 v (by simpa [H] using hv)
      have hpow : d ^ (1 - eta) = d ^ (-eta) * d := by
        calc
          d ^ (1 - eta) = d ^ (-eta + 1) := by congr 1; ring
          _ = d ^ (-eta) * d ^ (1 : ℝ) := Real.rpow_add hdpos (-eta) 1
          _ = d ^ (-eta) * d := by rw [Real.rpow_one]
      have hw' : d - AuxConcentration.universalHostDegreeError n k
            (jmDeletion delta n) < (degree H v : ℝ) ∧
          (degree H v : ℝ) ≤ d := by
        simpa [H, d, delta, k, jmSelectedHostDegree] using hw
      constructor
      · calc
          (1 - d ^ (-eta)) * d = d - d ^ (1 - eta) := by
            rw [hpow]
            ring
          _ ≤ (degree H v : ℝ) := by
            linarith [harith.2.2.2, hw'.1]
      · exact hw'.2
    · intro s hs
      exact (show (codegree H s : ℝ) ≤ ((6 * n ^ 2 : ℕ) : ℝ) by
        exact_mod_cast hcodeg.1 s hs).trans hcodegreeScale
    · intro i
      refine ⟨?_, ?_, htrackable i⟩
      · cases i <;> simp
      · cases i <;> simp
  have hleaveBound (x : Fin n) :
      (n - 1 : ℕ) - (1 - d ^ (-(eta ^ 3))) * d ^ (-1 : ℝ) *
          testTotal (leaveDegreeWeight H x) H 1 ≤ B := by
    have hres := leaveResidual_le_two_rpow heta0 hn0 hd1
      (by simpa [d, eta, delta, k] using harith.2.2.2)
      (by simpa [d, eta, delta] using herrRho)
      (by simpa [H, d, delta, k, jmSelectedHostDegree] using
        leaveTotal_lower_of_universalHost hhost x)
    have hceil : 2 * (n : ℝ) ^ (1 - 2 * delta) ≤ (B : ℝ) := by
      apply le_trans (mul_le_mul_of_nonneg_right
        (by norm_num : (2 : ℝ) ≤ 40000) (Real.rpow_nonneg hnR.le _))
      simpa [B, jmCeilLeaveBound] using
        Nat.le_ceil (40000 * (n : ℝ) ^ (1 - 2 * delta))
    have hres' : (n - 1 : ℕ) - (1 - d ^ (-(eta ^ 3))) * d ^ (-1 : ℝ) *
        testTotal (leaveDegreeWeight H x) H 1 ≤
          2 * (n : ℝ) ^ (1 - 2 * delta) := by
      simpa [H, d, eta, delta] using hres
    exact hres'.trans hceil
  have hcoeff (a : JMCDistinctRootPair n) (rx ry : JMCPaintRole) :
      0 ≤ (1 + d ^ (-(eta ^ 3))) * d ^ (-2 : ℝ) -
        (1 - d ^ (-(eta ^ 3))) * d ^ (-3 : ℝ) * (m : ℝ) := by
    simpa [d, eta, m] using
      (jmRoleCrossCoefficient_bounds heta0 hd1
        (by simpa [d, eta] using hcoverNum.1)).1
  have hcrossBound (a : JMCDistinctRootPair n) :
      (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
        let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
        (((1 + d ^ (-(eta ^ 3))) * d ^ (-2 : ℝ) -
              (1 - d ^ (-(eta ^ 3))) * d ^ (-3 : ℝ) * (m : ℝ)) *
          (8 * (AuxConcentration.pairRoleTarget k (jmDeletion delta n) b +
            (AuxConcentration.universalPairRoleDeviation n b +
              AuxConcentration.universalPairRoleMeanError n b))))) ≤ B := by
    have hsum := jmRoleCrossSum_le_40000_rpow heta0 hn0 hk hd1
      (by simpa [d, eta] using hcoverNum.1)
      (by simpa [d, delta] using hscale)
      (by simpa [d, eta, delta] using herrRho) a
    have hceil : 40000 * (n : ℝ) ^ (1 - 2 * delta) ≤ (B : ℝ) := by
      simpa [B, jmCeilLeaveBound] using
        Nat.le_ceil (40000 * (n : ℝ) ^ (1 - 2 * delta))
    have hsum' :
        (∑ rx : JMCPaintRole, ∑ ry : JMCPaintRole,
          let b := (auxPairRoleIndexEquiv n).symm (a.withRoles rx ry)
          (((1 + d ^ (-(eta ^ 3))) * d ^ (-2 : ℝ) -
                (1 - d ^ (-(eta ^ 3))) * d ^ (-3 : ℝ) * (m : ℝ)) *
            (8 * (AuxConcentration.pairRoleTarget k (jmDeletion delta n) b +
              (AuxConcentration.universalPairRoleDeviation n b +
                AuxConcentration.universalPairRoleMeanError n b))))) ≤
            40000 * (n : ℝ) ^ (1 - 2 * delta) := by
      simpa [d, eta, delta, k, m] using hsum
    exact hsum'.trans hceil
  have hbounds : RoleTrackedHostBounds B
      (AuxConcentration.allTriangleBlocks n k) R d (d ^ (-(eta ^ 3))) := by
    apply roleTrackedHostBounds_of_universalHost hhost hk' hd0 herrOne hgap
      hcoverScale hleaveBound hcoeff hcrossBound
  exact ⟨d, R, hd0cut, by simpa [H, C, d, eta, delta, k] using hinstance,
    by simpa [B, d, eta, delta, k] using hbounds⟩

/-- The closed conflict-free matching theorem and the exact eventual host/test
instances yield the sparse partial colourings required by `UpperReduction`. -/
theorem exists_exponent_eventually_partialGood
    {ell : ℕ} {C C0 : ℝ}
    (hCFM : SpecializedCFMTheorem ell)
    (hinstances : HasEventualJMCInstances ell C C0) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ᶠ n : ℕ in atTop,
        Nonempty
          (PartialGood n (jmOldColors (jmDelta eta0) n)
            (jmCeilLeaveBound C C0 (jmDelta eta0) n)) := by
  rcases hCFM with ⟨eta0, heta0, hCFM⟩
  have heta : 0 < jmEta eta0 := jmEta_pos heta0
  have heta0' : jmEta eta0 < eta0 := jmEta_lt_threshold heta0
  obtain ⟨d0, hd0⟩ := hCFM (jmEta eta0) heta heta0'
  refine ⟨eta0, heta0, ?_⟩
  filter_upwards [hinstances eta0 heta0 d0] with n hn
  obtain ⟨d, R, hd, hinst, hbounds⟩ := hn
  let k := jmOldColors (jmDelta eta0) n
  let candidates := AuxConcentration.allTriangleBlocks n k
  have hconclusion :
      SpecializedCFMConclusion (auxiliaryHypergraph candidates R)
        (alternatingCycleConflicts candidates R) d (jmEta eta0)
        jmcTestUniformity (jmcTestWeight candidates R) :=
    hd0 d hd (AuxVertex n k) (JMCTrackedIndex n)
      (auxiliaryHypergraph candidates R)
      (alternatingCycleConflicts candidates R) jmcTestUniformity
      (jmcTestWeight candidates R) (by simpa [k, candidates] using hinst)
  have htests :
      TestsControlLeave (jmCeilLeaveBound C C0 (jmDelta eta0) n)
        candidates R d (jmEta eta0) jmcTestUniformity
        (jmcTestWeight candidates R) :=
    jmcRoleTestsControlLeave_of_trackedBounds candidates R d (jmEta eta0)
      (by simpa [k, candidates] using hbounds)
  simpa [k, candidates] using
    partialGood_of_specializedCFMConclusion n k
      (jmCeilLeaveBound C C0 (jmDelta eta0) n) candidates R d
      (jmEta eta0) jmcTestUniformity (jmcTestWeight candidates R)
      hconclusion htests

/-- Ratio-limit resolution once both unconditional probabilistic ingredients
have been supplied. -/
theorem erdos136Fun_tendsto_of_CFM_and_instances
    {ell : ℕ} {C C0 : ℝ}
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hCFM : SpecializedCFMTheorem ell)
    (hinstances : HasEventualJMCInstances ell C C0) :
    Tendsto (fun n : ℕ ↦ (erdos136Fun n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  obtain ⟨eta0, heta0, hpartial⟩ :=
    exists_exponent_eventually_partialGood hCFM hinstances
  have hdelta0 : 0 < jmDelta eta0 := jmDelta_pos heta0
  have hdeltaHalf : jmDelta eta0 < 1 / 2 :=
    (jmDelta_le_one_ten_thousandth eta0).trans_lt (by norm_num)
  exact erdos136Fun_tendsto_of_eventually_partialGood
    hdelta0 hdeltaHalf hC hC0 hpartial

/-- Asymptotic-equivalence resolution under the same two exact inputs.  The
public theorem later instantiates both hypotheses with their proved finite
developments. -/
theorem erdos136Fun_isEquivalent_of_CFM_and_instances
    {ell : ℕ} {C C0 : ℝ}
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hCFM : SpecializedCFMTheorem ell)
    (hinstances : HasEventualJMCInstances ell C C0) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ ↦ (erdos136Fun n : ℝ))
      (fun n : ℕ ↦ (5 / 6 : ℝ) * (n : ℝ)) := by
  apply isEquivalent_of_tendsto_normalized _ _ (by norm_num)
  exact erdos136Fun_tendsto_of_CFM_and_instances
    hC hC0 hCFM hinstances

end

end Erdos136
