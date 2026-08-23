/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1147.
https://www.erdosproblems.com/forum/thread/1147

Informal authors:
- Jakub Konieczny

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1147.md
-/
/-
This file formalizes the negative resolution of Erdős Problem 1147 by the
explicit counterexample `α = √2`.

Mathematical proof and Leanization notes: ../../../tex/1147.tex
Primary source: J. Konieczny, "Sets of recurrence as bases for the positive
integers", Acta Arith. 174 (2016), no. 4, 309–338, Lemma 1.2 and
Proposition 1.3.
-/

import ErdosProblems.Erdos868
import Mathlib

open Filter Set
open scoped Pointwise Topology

namespace Erdos1147

/-- Distance to the nearest integer, realized as the norm on `ℝ / ℤ`. -/
noncomputable def circleDist (x : ℝ) : ℝ :=
  ‖(x : AddCircle (1 : ℝ))‖

lemma circleDist_eq_round (x : ℝ) :
    circleDist x = |x - (round x : ℝ)| := by
  simp [circleDist, AddCircle.norm_eq]

lemma circleDist_nonneg (x : ℝ) : 0 ≤ circleDist x := norm_nonneg _

lemma circleDist_le_abs (x : ℝ) : circleDist x ≤ |x| := by
  change ‖(x : AddCircle (1 : ℝ))‖ ≤ |x|
  simpa [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x))

lemma circleDist_add_le (x y : ℝ) :
    circleDist (x + y) ≤ circleDist x + circleDist y := by
  change ‖((x + y : ℝ) : AddCircle (1 : ℝ))‖ ≤ _
  rw [QuotientAddGroup.mk_add]
  exact norm_add_le _ _

lemma circleDist_sub_le (x y : ℝ) :
    circleDist (x - y) ≤ circleDist x + circleDist y := by
  change ‖((x - y : ℝ) : AddCircle (1 : ℝ))‖ ≤ _
  rw [QuotientAddGroup.mk_sub]
  exact norm_sub_le _ _

/-- Reverse triangle inequality with an elementary real perturbation. -/
lemma circleDist_sub_abs_sub_le (x y : ℝ) :
    circleDist y - |x - y| ≤ circleDist x := by
  have htri : circleDist y ≤ circleDist x + circleDist (y - x) := by
    convert circleDist_add_le x (y - x) using 1
    ring_nf
  have hpert : circleDist (y - x) ≤ |x - y| := by
    simpa [abs_sub_comm] using circleDist_le_abs (y - x)
  linarith

lemma circleDist_add_int (x : ℝ) (z : ℤ) :
    circleDist (x + z) = circleDist x := by
  rw [circleDist_eq_round, circleDist_eq_round, round_add_intCast]
  push_cast
  congr 1
  ring

lemma circleDist_half : circleDist (1 / 2 : ℝ) = 1 / 2 := by
  norm_num [circleDist_eq_round, round]

lemma continuous_circleDist : Continuous circleDist := by
  exact continuous_norm.comp (AddCircle.continuous_mk' (1 : ℝ))

/-- The exact set occurring in the problem, for a general decay function. -/
def recurrenceSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ circleDist (α * (n : ℝ) ^ 2) < ε n}

/-- An asymptotic additive basis of order two. -/
abbrev IsBasis2 (A : Set ℕ) : Prop := A.IsAsymptoticAddBasisOfOrder 2

/-! ## An odd Pell sequence for `√2` -/

/-- Starting with `(3,1)`, multiplication by `17 + 6√8` preserves
`P² - 8N² = 1` and keeps both coordinates odd. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | j + 1 =>
      let u := pellPair j
      (17 * u.1 + 48 * u.2, 6 * u.1 + 17 * u.2)

def pellP (j : ℕ) : ℕ := (pellPair j).1

def pellN (j : ℕ) : ℕ := (pellPair j).2

@[simp] lemma pellP_zero : pellP 0 = 3 := rfl
@[simp] lemma pellN_zero : pellN 0 = 1 := rfl

lemma pellP_succ (j : ℕ) :
    pellP (j + 1) = 17 * pellP j + 48 * pellN j := by
  simp [pellP, pellN, pellPair]

lemma pellN_succ (j : ℕ) :
    pellN (j + 1) = 6 * pellP j + 17 * pellN j := by
  simp [pellP, pellN, pellPair]

lemma pell_identity (j : ℕ) :
    (pellP j : ℤ) ^ 2 - 8 * (pellN j : ℤ) ^ 2 = 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pellP_succ, pellN_succ]
      push_cast
      nlinarith

lemma pellP_odd (j : ℕ) : Odd (pellP j) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rcases ih with ⟨k, hk⟩
      refine ⟨17 * k + 8 + 24 * pellN j, ?_⟩
      rw [pellP_succ, hk]
      omega

lemma pellN_odd (j : ℕ) : Odd (pellN j) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rcases ih with ⟨k, hk⟩
      refine ⟨3 * pellP j + 17 * k + 8, ?_⟩
      rw [pellN_succ, hk]
      omega

lemma pellP_pos (j : ℕ) : 0 < pellP j := (pellP_odd j).pos

lemma pellN_pos (j : ℕ) : 0 < pellN j := (pellN_odd j).pos

lemma pellN_ge (j : ℕ) : j + 1 ≤ pellN j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pellN_succ]
      have hp := pellP_pos j
      omega

lemma pellN_tendsto : Tendsto (fun j ↦ (pellN j : ℝ)) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨⌈b⌉₊, fun j hj ↦ ?_⟩
  calc
    b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ (j : ℝ) := by exact_mod_cast hj
    _ ≤ (j : ℝ) + 1 := by linarith
    _ ≤ (pellN j : ℝ) := by exact_mod_cast pellN_ge j

lemma pellN_tendsto_nat : Tendsto pellN atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, fun j hj ↦ ?_⟩
  have hge := pellN_ge j
  omega

lemma pell_identity_real (j : ℕ) :
    (pellP j : ℝ) ^ 2 - 8 * (pellN j : ℝ) ^ 2 = 1 := by
  exact_mod_cast pell_identity j

/-- The signed Pell approximation error. -/
noncomputable def pellError (j : ℕ) : ℝ :=
  Real.sqrt 2 * pellN j - pellP j / 2

lemma pellError_eq (j : ℕ) :
    pellError j = -1 / (2 * (pellP j + 2 * Real.sqrt 2 * pellN j)) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : (0 : ℝ) < pellP j := by exact_mod_cast pellP_pos j
  have hs : 0 ≤ Real.sqrt 2 * pellN j := by positivity
  have hden : (2 : ℝ) * ((pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j) ≠ 0 := by
    positivity
  change pellError j = (-1 : ℝ) /
    (2 * ((pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j))
  rw [pellError]
  field_simp [hden]
  nlinarith [pell_identity_real j]

lemma pellP_div_pellN_tendsto :
    Tendsto (fun j ↦ (pellP j : ℝ) / pellN j) atTop (𝓝 (2 * Real.sqrt 2)) := by
  have hden : Tendsto
      (fun j ↦ (pellN j : ℝ) *
        ((pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j)) atTop atTop := by
    have hsum : Tendsto
        (fun j ↦ (pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j) atTop atTop := by
      exact tendsto_atTop_mono' atTop (Filter.Eventually.of_forall fun j ↦ by
        have hp : 0 ≤ (pellP j : ℝ) := by positivity
        have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hs : 1 ≤ 2 * Real.sqrt 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [show (0 : ℝ) ≤ pellN j by positivity]) pellN_tendsto
    exact pellN_tendsto.atTop_mul_atTop₀ hsum
  have hinv : Tendsto
      (fun j ↦ 1 / ((pellN j : ℝ) *
        ((pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hdiff : ∀ j,
      (pellP j : ℝ) / pellN j - 2 * Real.sqrt 2 =
        1 / ((pellN j : ℝ) *
          ((pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j)) := by
    intro j
    have hn : (pellN j : ℝ) ≠ 0 := by exact_mod_cast (pellN_pos j).ne'
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : (0 : ℝ) < pellP j := by exact_mod_cast pellP_pos j
    have hden' : (pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j ≠ 0 := by positivity
    field_simp
    nlinarith [pell_identity_real j]
  have := hinv.congr' (Filter.Eventually.of_forall fun j ↦ (hdiff j).symm)
  have hadd := this.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ 2 * Real.sqrt 2) atTop (𝓝 (2 * Real.sqrt 2)))
  convert hadd using 1 <;> ring_nf

lemma pellError_tendsto : Tendsto pellError atTop (𝓝 0) := by
  have hden : Tendsto
      (fun j ↦ 2 * ((pellP j : ℝ) + 2 * Real.sqrt 2 * pellN j)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact tendsto_atTop_mono' atTop (Filter.Eventually.of_forall fun j ↦ by
      have hp : 0 ≤ (pellP j : ℝ) := by positivity
      have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hs : 1 ≤ 2 * Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [show (0 : ℝ) ≤ pellN j by positivity]) pellN_tendsto
  apply (tendsto_const_nhds.div_atTop hden).congr'
  · filter_upwards with j
    rw [pellError_eq]

lemma pellError_mul_tendsto :
    Tendsto (fun j ↦ pellError j * pellN j) atTop
      (𝓝 (-Real.sqrt 2 / 16)) := by
  have hratio := pellP_div_pellN_tendsto
  have hform : ∀ j,
      pellError j * pellN j =
        -1 / (2 * ((pellP j : ℝ) / pellN j + 2 * Real.sqrt 2)) := by
    intro j
    rw [pellError_eq]
    have hn : (pellN j : ℝ) ≠ 0 := by exact_mod_cast (pellN_pos j).ne'
    field_simp
  have hlim : Tendsto
      (fun j ↦ -1 / (2 * ((pellP j : ℝ) / pellN j + 2 * Real.sqrt 2)))
      atTop (𝓝 (-1 / (8 * Real.sqrt 2))) := by
    have hnum : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 (-1)) :=
      tendsto_const_nhds
    have hden : Tendsto
        (fun j ↦ 2 * ((pellP j : ℝ) / pellN j + 2 * Real.sqrt 2)) atTop
        (𝓝 (2 * (2 * Real.sqrt 2 + 2 * Real.sqrt 2))) :=
      tendsto_const_nhds.mul (hratio.add tendsto_const_nhds)
    have hne : (2 : ℝ) * (2 * Real.sqrt 2 + 2 * Real.sqrt 2) ≠ 0 := by positivity
    have hq := hnum.div hden hne
    have heval : (2 : ℝ) * (2 * Real.sqrt 2 + 2 * Real.sqrt 2) =
        8 * Real.sqrt 2 := by ring
    rw [heval] at hq
    apply hq.congr'
    filter_upwards with j
    simp [div_eq_mul_inv]
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have heq : -1 / (8 * Real.sqrt 2) = -Real.sqrt 2 / 16 := by
    field_simp [hsqrt_pos.ne']
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← heq]
  exact hlim.congr' (Filter.Eventually.of_forall fun j ↦ (hform j).symm)

/-! ## Half-integer separation and the moving endpoint -/

lemma circleDist_odd_int_div_two {r : ℤ} (hr : Odd r) :
    circleDist ((r : ℝ) / 2) = 1 / 2 := by
  rcases hr with ⟨z, hz⟩
  calc
    circleDist ((r : ℝ) / 2) = circleDist ((1 / 2 : ℝ) + z) := by
      congr 1
      rw [hz]
      push_cast
      ring
    _ = circleDist (1 / 2 : ℝ) := circleDist_add_int _ z
    _ = 1 / 2 := circleDist_half

lemma odd_int_sub_of_sum_eq {a b N : ℕ} (hN : Odd N) (hab : a + b = N) :
    Odd ((a : ℤ) - (b : ℤ)) := by
  rcases hN with ⟨k, hk⟩
  refine ⟨(k : ℤ) - b, ?_⟩
  omega

lemma pell_separation {j a b : ℕ} (hab : a + b = pellN j)
    (herr : |pellError j * pellN j| < 1 / 8) :
    3 / 8 < circleDist
      (Real.sqrt 2 * (a : ℝ) ^ 2 - Real.sqrt 2 * (b : ℝ) ^ 2) := by
  have hdodd : Odd ((a : ℤ) - (b : ℤ)) :=
    odd_int_sub_of_sum_eq (pellN_odd j) hab
  have hpodd : Odd (pellP j : ℤ) := by
    rcases pellP_odd j with ⟨k, hk⟩
    exact ⟨k, by exact_mod_cast hk⟩
  have hprododd : Odd (((a : ℤ) - (b : ℤ)) * pellP j) := hdodd.mul hpodd
  let base : ℝ := (((a : ℤ) - (b : ℤ)) * pellP j : ℤ) / 2
  let perturb : ℝ := ((a : ℝ) - b) * pellError j
  have hbase : circleDist base = 1 / 2 :=
    circleDist_odd_int_div_two hprododd
  have habR : (a : ℝ) + b = pellN j := by exact_mod_cast hab
  have hphase :
      Real.sqrt 2 * (a : ℝ) ^ 2 - Real.sqrt 2 * (b : ℝ) ^ 2 =
        base + perturb := by
    have happ : Real.sqrt 2 * pellN j = pellP j / 2 + pellError j := by
      rw [pellError]
      ring
    dsimp [base, perturb]
    push_cast
    calc
      Real.sqrt 2 * (a : ℝ) ^ 2 - Real.sqrt 2 * (b : ℝ) ^ 2 =
          ((a : ℝ) - b) * (Real.sqrt 2 * pellN j) := by
            rw [← habR]
            ring
      _ = ((a : ℝ) - b) * (pellP j / 2 + pellError j) := by rw [happ]
      _ = (((a : ℝ) - b) * pellP j) / 2 +
          ((a : ℝ) - b) * pellError j := by ring
  have habs_sub : |(a : ℝ) - b| ≤ (pellN j : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [show (0 : ℝ) ≤ a by positivity,
      show (0 : ℝ) ≤ b by positivity]
  have hperturb : |perturb| < 1 / 8 := by
    have hmul : |perturb| ≤ |pellError j * pellN j| := by
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ pellN j by positivity)]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right habs_sub (abs_nonneg (pellError j)))
    exact hmul.trans_lt herr
  have hrev := circleDist_sub_abs_sub_le
    (Real.sqrt 2 * (a : ℝ) ^ 2 - Real.sqrt 2 * (b : ℝ) ^ 2) base
  rw [hphase, hbase] at hrev
  have : |base + perturb - base| = |perturb| := by ring_nf
  rw [this] at hrev
  rw [hphase]
  linarith

/-- The phase at a fixed endpoint, after removing its integer part. -/
noncomputable def endpointPhase (j n : ℕ) : ℝ :=
  1 / 2 + pellError j * pellN j - 2 * pellError j * n +
    Real.sqrt 2 * (n : ℝ) ^ 2

noncomputable def endpointLimit (n : ℕ) : ℝ :=
  1 / 2 - Real.sqrt 2 / 16 + Real.sqrt 2 * (n : ℝ) ^ 2

lemma endpoint_phase_circle (j n : ℕ) (hn : n ≤ pellN j) :
    circleDist (Real.sqrt 2 * ((pellN j - n : ℕ) : ℝ) ^ 2) =
      circleDist (endpointPhase j n) := by
  have happ : Real.sqrt 2 * pellN j = pellP j / 2 + pellError j := by
    rw [pellError]
    ring
  rcases (pellP_odd j).mul (pellN_odd j) with ⟨k, hk⟩
  let z : ℤ := (k : ℤ) - (pellP j * n : ℕ)
  have hkr : (pellP j : ℝ) * pellN j = 2 * (k : ℝ) + 1 := by
    exact_mod_cast hk
  have halg : Real.sqrt 2 * ((pellN j - n : ℕ) : ℝ) ^ 2 =
      endpointPhase j n + (z : ℝ) := by
    rw [Nat.cast_sub hn]
    calc
      Real.sqrt 2 * ((pellN j : ℝ) - n) ^ 2 =
          (Real.sqrt 2 * pellN j) * pellN j -
            2 * (Real.sqrt 2 * pellN j) * n +
              Real.sqrt 2 * (n : ℝ) ^ 2 := by ring
      _ = (pellP j / 2 + pellError j) * pellN j -
            2 * (pellP j / 2 + pellError j) * n +
              Real.sqrt 2 * (n : ℝ) ^ 2 := by rw [happ]
      _ = endpointPhase j n + (z : ℝ) := by
        dsimp [endpointPhase, z]
        push_cast
        nlinarith
  rw [halg, circleDist_add_int]

lemma endpointPhase_tendsto (n : ℕ) :
    Tendsto (fun j ↦ endpointPhase j n) atTop (𝓝 (endpointLimit n)) := by
  have hsmall : Tendsto (fun j ↦ 2 * pellError j * (n : ℝ)) atTop (𝓝 0) := by
    convert (pellError_tendsto.const_mul 2).mul_const (n : ℝ) using 1
    ring_nf
  have hhalf : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have h := (hhalf.add pellError_mul_tendsto).sub hsmall |>.add
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ Real.sqrt 2 * (n : ℝ) ^ 2) atTop
      (𝓝 (Real.sqrt 2 * (n : ℝ) ^ 2)))
  convert h using 1
  all_goals simp [endpointPhase, endpointLimit]
  all_goals ring

lemma endpointLimit_circleDist_pos (n : ℕ) : 0 < circleDist (endpointLimit n) := by
  apply lt_of_le_of_ne (circleDist_nonneg _) ?_
  intro hzero
  have habs : |endpointLimit n - (round (endpointLimit n) : ℝ)| = 0 := by
    rw [← circleDist_eq_round]
    exact hzero.symm
  have hc : endpointLimit n = (round (endpointLimit n) : ℝ) :=
    sub_eq_zero.mp (abs_eq_zero.mp habs)
  let A : ℤ := 16 * (n : ℤ) ^ 2 - 1
  let B : ℤ := 16 * round (endpointLimit n) - 8
  have hA : A ≠ 0 := by
    dsimp [A]
    omega
  have hsqrt_eq : Real.sqrt 2 = (B : ℝ) / (A : ℝ) := by
    have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    field_simp [hAR]
    dsimp [A, B, endpointLimit] at hc ⊢
    push_cast at hc ⊢
    nlinarith
  exact irrational_sqrt_two.ne_rational B A hsqrt_eq

lemma pellN_sub_tendsto (n : ℕ) :
    Tendsto (fun j ↦ pellN j - n) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b + n, fun j hj ↦ ?_⟩
  have hge := pellN_ge j
  omega

lemma fixed_endpoint_eventually_not_mem {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, pellN j - n ∉ recurrenceSet (Real.sqrt 2) ε := by
  have hphase := endpointPhase_tendsto n
  have hdist : Tendsto (fun j ↦ circleDist (endpointPhase j n)) atTop
      (𝓝 (circleDist (endpointLimit n))) :=
    (continuous_circleDist.tendsto (endpointLimit n)).comp hphase
  have hdpos := endpointLimit_circleDist_pos n
  have hdist_large : ∀ᶠ j : ℕ in atTop,
      circleDist (endpointPhase j n) > circleDist (endpointLimit n) / 2 :=
    hdist.eventually (eventually_gt_nhds (half_lt_self hdpos))
  have heps := hε.comp (pellN_sub_tendsto n)
  have heps_small : ∀ᶠ j : ℕ in atTop,
      ε (pellN j - n) < circleDist (endpointLimit n) / 2 :=
    heps.eventually (eventually_lt_nhds (half_pos hdpos))
  filter_upwards [hdist_large, heps_small, eventually_ge_atTop n] with j hjdist hjeps hj
  have hn : n ≤ pellN j := by
    have hge := pellN_ge j
    omega
  intro hmem
  have hm := hmem.2
  rw [endpoint_phase_circle j n hn] at hm
  linarith

/-! ## The explicit negative resolution -/

lemma pellError_mul_eventually_small :
    ∀ᶠ j : ℕ in atTop, |pellError j * pellN j| < 1 / 8 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hslt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hlim : |-Real.sqrt 2 / 16| < (1 / 8 : ℝ) := by
    have hnonpos : -Real.sqrt 2 / 16 ≤ (0 : ℝ) := by nlinarith
    rw [abs_of_nonpos hnonpos]
    nlinarith
  exact pellError_mul_tendsto.abs.eventually (eventually_lt_nhds hlim)

/-- Konieczny's explicit result: for every decay function tending to zero,
the quadratic recurrence set for `√2` misses infinitely many Pell numbers,
and in particular is not an asymptotic basis of order two. -/
theorem sqrtTwo_not_basis_of_tendsto_zero (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ IsBasis2 (recurrenceSet (Real.sqrt 2) ε) := by
  intro hbasis
  change (recurrenceSet (Real.sqrt 2) ε).IsAsymptoticAddBasisOfOrder 2 at hbasis
  rw [Set.isAsymptoticAddBasisOfOrder_iff_atTop] at hbasis
  have hbasisPell : ∀ᶠ j : ℕ in atTop,
      pellN j ∈ 2 • recurrenceSet (Real.sqrt 2) ε :=
    pellN_tendsto_nat.eventually hbasis
  have heps : ∀ᶠ n : ℕ in atTop, ε n < (3 / 16 : ℝ) :=
    hε.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨K, hK⟩ := eventually_atTop.1 heps
  have hendpoints : ∀ᶠ j : ℕ in atTop,
      ∀ n ∈ Finset.range K,
        pellN j - n ∉ recurrenceSet (Real.sqrt 2) ε :=
    (Finset.eventually_all (Finset.range K)).2 fun n _ ↦
      fixed_endpoint_eventually_not_mem hε n
  obtain ⟨j, hjbasis, hjerror, hjend⟩ :=
    (hbasisPell.and (pellError_mul_eventually_small.and hendpoints)).exists
  have hjbasis' : pellN j ∈
      recurrenceSet (Real.sqrt 2) ε + recurrenceSet (Real.sqrt 2) ε := by
    simpa [two_nsmul] using hjbasis
  rcases hjbasis' with ⟨a, ha, b, hb, hab⟩
  have hsmall : a < K ∨ b < K := by
    by_contra hnot
    push Not at hnot
    have hea := hK a hnot.1
    have heb := hK b hnot.2
    have hupper := circleDist_sub_le
      (Real.sqrt 2 * (a : ℝ) ^ 2) (Real.sqrt 2 * (b : ℝ) ^ 2)
    have hsep := pell_separation hab hjerror
    have ha' := ha.2
    have hb' := hb.2
    linarith
  rcases hsmall with haK | hbK
  · have hnotmem := hjend a (Finset.mem_range.2 haK)
    have heq : pellN j - a = b :=
      (Nat.eq_sub_of_add_eq (by simpa [add_comm] using hab)).symm
    exact hnotmem (heq ▸ hb)
  · have hnotmem := hjend b (Finset.mem_range.2 hbK)
    have heq : pellN j - b = a := (Nat.eq_sub_of_add_eq hab).symm
    exact hnotmem (heq ▸ ha)

/-- The decay function in the original statement of Problem 1147. -/
noncomputable def logarithmicDecay (n : ℕ) : ℝ :=
  1 / Real.log n

lemma logarithmicDecay_tendsto :
    Tendsto logarithmicDecay atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  unfold logarithmicDecay
  simp only [one_div]
  exact hlog.inv_tendsto_atTop

/-- The set displayed in Erdős Problem 1147. -/
noncomputable def problemSet (α : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ circleDist (α * (n : ℝ) ^ 2) < 1 / Real.log n}

lemma problemSet_eq (α : ℝ) :
    problemSet α = recurrenceSet α logarithmicDecay := by
  ext n
  rfl

/-- `√2` is an explicit counterexample to the proposed assertion. -/
theorem sqrtTwo_not_basis : ¬ IsBasis2 (problemSet (Real.sqrt 2)) := by
  rw [problemSet_eq]
  exact sqrtTwo_not_basis_of_tendsto_zero logarithmicDecay logarithmicDecay_tendsto

/-- Erdős Problem 1147 has a negative answer: it is false that every
positive irrational parameter gives an asymptotic additive basis of order
two. -/
theorem erdos_1147 :
    ¬ ∀ α : ℝ, 0 < α → Irrational α → IsBasis2 (problemSet α) := by
  intro h
  exact sqrtTwo_not_basis
    (h (Real.sqrt 2) (Real.sqrt_pos.2 (by norm_num)) irrational_sqrt_two)

end Erdos1147

#print axioms Erdos1147.erdos_1147
