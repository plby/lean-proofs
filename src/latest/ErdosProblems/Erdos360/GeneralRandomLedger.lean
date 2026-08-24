/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.RandomDiversity

/-!
# Uniform random-ledger estimates for `h = 8 * ell`

The random extraction used in the lower bound keeps `ell` cells out of an
ambient `8 * ell` cells.  This file supplies source-level estimates which are
uniform in the fixed positive integer `ell`.

The integer recurrence loses at most `k / (3 * ell) + 2` at each of its first
`ell` steps.  Thus the explicit hypothesis `12 * ell ^ 2 ≤ k` leaves at least
half of the original diversity.  The complement-tail exponent also admits a
closed form.  These two facts give a single exponential majorant for every
entry of the exact-split probability ledger.
-/

namespace Erdos360

open scoped BigOperators

private lemma randomResidual_step_lower {q m D : ℕ}
    (hm : 0 < m) (h2 : 2 ≤ m) (hceil : 2 * q ≤ D * m) :
    q - D ≤ q * (m - 2) / m := by
  apply (Nat.le_div_iff_mul_le hm).2
  rw [Nat.sub_mul]
  have hqm : 2 * q ≤ q * m := by nlinarith
  rw [Nat.mul_sub_left_distrib]
  omega

private lemma randomResidual_step_upper {q m : ℕ} (_hm : 0 < m) :
    q * (m - 2) / m ≤ q := by
  apply Nat.div_le_of_le_mul
  calc
    q * (m - 2) ≤ q * m := Nat.mul_le_mul_left q (Nat.sub_le m 2)
    _ = m * q := Nat.mul_comm _ _

/-- Linear loss ledger for the first `ell` steps of the `8 * ell`-cell
recurrence.  The second conjunct records the upper bound needed to pay for
the next step's loss. -/
lemma residualDiversity_eight_mul_bounds
    {ell k i : ℕ} (hell : 0 < ell) (hi : i ≤ ell) :
    let D := k / (3 * ell) + 2
    k - i * D ≤ RandomDiversity.residualDiversity k (8 * ell) i ∧
      RandomDiversity.residualDiversity k (8 * ell) i ≤ k := by
  intro D
  induction i with
  | zero => simp [RandomDiversity.residualDiversity]
  | succ i ih =>
      have hi' : i ≤ ell := by omega
      obtain ⟨ihlo, ihup⟩ := ih hi'
      let q := RandomDiversity.residualDiversity k (8 * ell) i
      let m := 8 * ell - i
      have hm7 : 7 * ell ≤ m := by
        dsimp [m]
        omega
      have hm : 0 < m := by omega
      have hm2 : 2 ≤ m := by omega
      have hklt : k < (k / (3 * ell) + 1) * (3 * ell) := by
        calc
          k < k / (3 * ell) * (3 * ell) + 3 * ell :=
            Nat.lt_div_mul_add (a := k) (b := 3 * ell) (by omega)
          _ = (k / (3 * ell) + 1) * (3 * ell) := by ring
      have hceil : 2 * q ≤ D * m := by
        have hqk : q ≤ k := ihup
        dsimp [D]
        nlinarith
      have hstepLo : q - D ≤ q * (m - 2) / m :=
        randomResidual_step_lower hm hm2 hceil
      have hstepUp : q * (m - 2) / m ≤ q :=
        randomResidual_step_upper hm
      change k - (i + 1) * D ≤
          RandomDiversity.residualDiversity k (8 * ell) i *
              (8 * ell - i - 2) / (8 * ell - i) ∧
        RandomDiversity.residualDiversity k (8 * ell) i *
              (8 * ell - i - 2) / (8 * ell - i) ≤ k
      change k - (i + 1) * D ≤ q * (m - 2) / m ∧
        q * (m - 2) / m ≤ k
      constructor
      · have hsub : k - (i + 1) * D ≤ q - D := by
          rw [show (i + 1) * D = i * D + D by ring]
          omega
        exact hsub.trans hstepLo
      · exact hstepUp.trans ihup

/-- At least half of the original diversity survives each of the first
`ell` splits of an `8 * ell`-cell extraction. -/
lemma residualDiversity_eight_mul_half
    {ell k i : ℕ} (hell : 0 < ell) (hi : i < ell)
    (hk : 12 * ell ^ 2 ≤ k) :
    k / 2 ≤ RandomDiversity.residualDiversity k (8 * ell) i := by
  have hb := residualDiversity_eight_mul_bounds (k := k) hell hi.le
  dsimp only at hb
  have hklt : k < (k / (3 * ell) + 1) * (3 * ell) := by
    calc
      k < k / (3 * ell) * (3 * ell) + 3 * ell :=
        Nat.lt_div_mul_add (a := k) (b := 3 * ell) (by omega)
      _ = (k / (3 * ell) + 1) * (3 * ell) := by ring
  have hdiv : (k / (3 * ell)) * (3 * ell) ≤ k :=
    Nat.div_mul_le_self k (3 * ell)
  have hbudget : i * (k / (3 * ell) + 2) ≤ k / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    have ha4 : 4 ≤ k / (3 * ell) := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 3 * ell)).2
      nlinarith
    have hia := Nat.mul_le_mul_right (k / (3 * ell) + 2) hi.le
    have haell := Nat.mul_le_mul_left ell ha4
    calc
      i * (k / (3 * ell) + 2) * 2 ≤
          ell * (k / (3 * ell) + 2) * 2 := Nat.mul_le_mul_right 2 hia
      _ = 2 * ell * (k / (3 * ell)) + 4 * ell := by ring
      _ ≤ 3 * ell * (k / (3 * ell)) := by nlinarith
      _ = (k / (3 * ell)) * (3 * ell) := by ring
      _ ≤ k := hdiv
  omega

/-- Closed form of the complement-diversity tail exponent. -/
lemma complementDiversityTailBound_eq_exp
    {h k : ℕ} (hh : 3 ≤ h) :
    RandomDiversity.complementDiversityTailBound h k =
      Real.exp (- (k : ℝ) /
        (2 * (h : ℝ) * (2 * (h : ℝ) - 3))) := by
  let H : ℝ := h
  let r : ℝ := (H - 2) / (H - 1)
  have hH : (3 : ℝ) ≤ H := by
    dsimp [H]
    exact_mod_cast hh
  have hH0 : H ≠ 0 := by nlinarith
  have hH1 : H - 1 ≠ 0 := by nlinarith
  have hH2 : H - 2 ≠ 0 := by nlinarith
  have h2H2 : 2 * (H - 2) ≠ 0 := mul_ne_zero (by norm_num) hH2
  have h2H3 : 2 * H - 3 ≠ 0 := by nlinarith
  have h1r : 1 - r = 1 / (H - 1) := by
    dsimp [r]
    field_simp
    ring
  have hdelta : (1 - r) / (2 * r) = 1 / (2 * (H - 2)) := by
    rw [h1r]
    dsimp [r]
    field_simp
  have hrdelta : r * (1 / (2 * (H - 2))) = 1 / (2 * (H - 1)) := by
    dsimp [r]
    field_simp
  have hplus : 1 + 1 / (2 * (H - 2)) =
      (2 * H - 3) / (2 * (H - 2)) := by
    field_simp
    ring
  have hinv : 1 / (1 + 1 / (2 * (H - 2))) - 1 =
      -1 / (2 * H - 3) := by
    rw [hplus]
    field_simp
    ring
  have hsum : r * ((1 - r) / (2 * r)) +
      (1 / (1 + ((1 - r) / (2 * r))) - 1) =
        -1 / (2 * (H - 1) * (2 * H - 3)) := by
    rw [hdelta, hrdelta, hinv]
    field_simp
    ring
  unfold RandomDiversity.complementDiversityTailBound
  dsimp only
  change Real.exp ((r * ((1 - r) / (2 * r)) +
      (1 / (1 + ((1 - r) / (2 * r))) - 1)) *
        ((k : ℝ) * (H - 1) / H)) =
    Real.exp (- (k : ℝ) / (2 * H * (2 * H - 3)))
  rw [hsum]
  congr 1
  field_simp

/-- Uniform complement-tail estimate at any of the first `ell` stages. -/
lemma complementDiversityTailBound_eight_mul
    {ell h k q : ℕ} (hell : 0 < ell) (hh : 3 ≤ h)
    (hhup : h ≤ 8 * ell) (hk : 12 * ell ^ 2 ≤ k)
    (hq : k / 2 ≤ q) :
    RandomDiversity.complementDiversityTailBound h q ≤
      Real.exp (- (k : ℝ) / (1024 * (ell : ℝ) ^ 2)) := by
  rw [complementDiversityTailBound_eq_exp hh]
  apply Real.exp_le_exp.mpr
  have hk12 : 12 ≤ k := by nlinarith
  have hqNat : k ≤ 4 * q := by omega
  have hqCast : (k : ℝ) ≤ 4 * q := by exact_mod_cast hqNat
  have hqR : (k : ℝ) / 4 ≤ q := by linarith
  have hhR : (h : ℝ) ≤ 8 * ell := by exact_mod_cast hhup
  have hhLow : (3 : ℝ) ≤ h := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < 2 * h * (2 * h - 3) :=
    mul_pos (by positivity) (by linarith)
  have hellpos : (0 : ℝ) < 1024 * (ell : ℝ) ^ 2 := by positivity
  have hratio : (k : ℝ) / (1024 * (ell : ℝ) ^ 2) ≤
      (q : ℝ) / (2 * h * (2 * h - 3)) := by
    rw [div_le_div_iff₀ hellpos hhpos]
    have hprod : 0 ≤ (8 * (ell : ℝ) - h) * (8 * ell + h) :=
      mul_nonneg (by linarith) (by positivity)
    have hden : 2 * (h : ℝ) * (2 * h - 3) ≤
        256 * (ell : ℝ) ^ 2 := by
      nlinarith
    calc
      (k : ℝ) * (2 * h * (2 * h - 3)) ≤
          k * (256 * (ell : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ ≤ (4 * q) * (256 * (ell : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hqCast (by positivity)
      _ = (q : ℝ) * (1024 * (ell : ℝ) ^ 2) := by ring
  simpa only [neg_div] using neg_le_neg hratio

/-- A single exponential majorant for every exact-split failure mass in the
first `ell` stages of an `8 * ell`-cell extraction. -/
lemma exactSplitFailureMass_eight_mul_bound
    {N s ell k i : ℕ} (hell : 0 < ell) (hi : i < ell)
    (hk : 12 * ell ^ 2 ≤ k) :
    RandomDiversity.exactSplitFailureMass N s (8 * ell - i)
        (RandomDiversity.residualDiversity k (8 * ell) i) ≤
      (4 : ℝ) * (8 * ell * s + 1) * (N + 1) *
        Real.exp (- (k : ℝ) / (1024 * (ell : ℝ) ^ 2)) := by
  let q := RandomDiversity.residualDiversity k (8 * ell) i
  let h := 8 * ell - i
  have hq : k / 2 ≤ q := residualDiversity_eight_mul_half hell hi hk
  have hh : 3 ≤ h := by
    dsimp [h]
    omega
  have hhup : h ≤ 8 * ell := by
    dsimp [h]
    omega
  have hk12 : 12 ≤ k := by nlinarith
  have hqNat : k ≤ 4 * q := by omega
  have hqCast : (k : ℝ) ≤ 4 * q := by exact_mod_cast hqNat
  have hqR : (k : ℝ) / 4 ≤ q := by linarith
  have hsample : Real.exp (-(q : ℝ) / (12 * h)) ≤
      Real.exp (- (k : ℝ) / (1024 * (ell : ℝ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hhpos : (0 : ℝ) < 12 * h := by positivity
    have hellpos : (0 : ℝ) < 1024 * (ell : ℝ) ^ 2 := by positivity
    have hhR : (h : ℝ) ≤ 8 * ell := by exact_mod_cast hhup
    have hratio : (k : ℝ) / (1024 * (ell : ℝ) ^ 2) ≤
        (q : ℝ) / (12 * h) := by
      rw [div_le_div_iff₀ hellpos hhpos]
      have hden : 12 * (h : ℝ) ≤ 96 * ell := by
        calc
          12 * (h : ℝ) ≤ 12 * (8 * (ell : ℝ)) :=
            mul_le_mul_of_nonneg_left hhR (by norm_num)
          _ = 96 * ell := by ring
      calc
        (k : ℝ) * (12 * h) ≤ k * (96 * ell) := by
          exact mul_le_mul_of_nonneg_left hden (by positivity)
        _ ≤ (4 * q) * (96 * ell) :=
          mul_le_mul_of_nonneg_right hqCast (by positivity)
        _ ≤ (q : ℝ) * (1024 * ell ^ 2) := by
          have hq0 : (0 : ℝ) ≤ q := by positivity
          have hellNat : 1 ≤ ell := hell
          have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hellNat
          have hsquare : (ell : ℝ) ≤ ell ^ 2 := by
            nlinarith [mul_nonneg (show (0 : ℝ) ≤ ell by positivity)
              (by linarith : 0 ≤ (ell : ℝ) - 1)]
          have hcoeff : (4 : ℝ) * (96 * ell) ≤ 1024 * ell ^ 2 := by
            nlinarith
          calc
            (4 * (q : ℝ)) * (96 * ell) = q * (4 * (96 * ell)) := by ring
            _ ≤ q * (1024 * ell ^ 2) :=
              mul_le_mul_of_nonneg_left hcoeff hq0
    simpa only [neg_div] using neg_le_neg hratio
  have hcomp : RandomDiversity.complementDiversityTailBound h q ≤
      Real.exp (- (k : ℝ) / (1024 * (ell : ℝ) ^ 2)) :=
    complementDiversityTailBound_eight_mul hell hh hhup hk hq
  unfold RandomDiversity.exactSplitFailureMass
  have hfactor : (((h * s + 1 : ℕ) : ℝ)) ≤ 8 * ell * s + 1 := by
    exact_mod_cast (show h * s + 1 ≤ 8 * ell * s + 1 by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right s hhup) 1)
  have hnonneg : 0 ≤ Real.exp (-(q : ℝ) / (12 * h)) +
      RandomDiversity.complementDiversityTailBound h q := by
    exact add_nonneg (Real.exp_pos _).le (by
      unfold RandomDiversity.complementDiversityTailBound
      exact (Real.exp_pos _).le)
  change (((h * s + 1 : ℕ) : ℝ)) * (2 * (N + 1)) *
      (Real.exp (-(q : ℝ) / (12 * h)) +
        RandomDiversity.complementDiversityTailBound h q) ≤ _
  calc
    (((h * s + 1 : ℕ) : ℝ)) * (2 * (N + 1)) *
          (Real.exp (-(q : ℝ) / (12 * h)) +
            RandomDiversity.complementDiversityTailBound h q) ≤
        (8 * ell * s + 1 : ℕ) * (2 * (N + 1)) *
          (Real.exp (-(q : ℝ) / (12 * h)) +
            RandomDiversity.complementDiversityTailBound h q) := by
      gcongr
    _ ≤ (8 * ell * s + 1 : ℕ) * (2 * (N + 1)) *
          (2 * Real.exp (- (k : ℝ) /
            (1024 * (ell : ℝ) ^ 2))) := by
      gcongr
      nlinarith
    _ = (4 : ℝ) * (8 * ell * s + 1) * (N + 1) *
          Real.exp (- (k : ℝ) / (1024 * (ell : ℝ) ^ 2)) := by
      push_cast
      ring

/-- The uniform majorant discharges the whole finite probability ledger as
soon as its single explicit right-hand side is less than one. -/
lemma exactSplitFailureMass_eight_mul_ledger
    {N s ell k : ℕ} (hell : 0 < ell) (hk : 12 * ell ^ 2 ≤ k)
    (hsmall : (4 : ℝ) * (8 * ell * s + 1) * (N + 1) *
      Real.exp (- (k : ℝ) / (1024 * (ell : ℝ) ^ 2)) < 1) :
    ∀ i < ell,
      RandomDiversity.exactSplitFailureMass N s (8 * ell - i)
        (RandomDiversity.residualDiversity k (8 * ell) i) < 1 := by
  intro i hi
  exact (exactSplitFailureMass_eight_mul_bound hell hi hk).trans_lt hsmall

end Erdos360
