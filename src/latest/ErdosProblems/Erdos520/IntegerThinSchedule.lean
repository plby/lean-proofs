import ErdosProblems.Erdos520.ConcreteThinBlock
import ErdosProblems.Erdos520.NormalizedEnergy
import ErdosProblems.Erdos520.ThinScheduleChebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset

namespace Erdos
namespace Problem520

/-!
# An exact integer thin-block schedule

The paper writes the endpoints using nested real exponentials.  Rounding
those expressions creates irrelevant bookkeeping.  The schedule below has
the same geometry but is integral by construction.  If `L = ell + 1` and
`J = L^K`, its logarithmic exponents are

`B * L^(J-j) * (L+1)^j`, `0 <= j <= J`.

Consequently consecutive logarithms have the exact ratio `(L+1)/L`, so the
`log log` width is at most `1/L`, while the number of blocks is polynomial.
-/

/-- Number of blocks in the exact integer schedule. -/
def integerThinBlockCount (K ell : ℕ) : ℕ := (ell + 1) ^ K

/-- The clamped block index. -/
def integerThinIndex (K ell j : ℕ) : ℕ :=
  min j (integerThinBlockCount K ell)

/-- Exponent of `2` at a scheduled endpoint. -/
def integerThinExponent (B K ell j : ℕ) : ℕ :=
  let L := ell + 1
  let J := integerThinBlockCount K ell
  let m := integerThinIndex K ell j
  B * L ^ (J - m) * (L + 1) ^ m

/-- Exact natural endpoints for the thin-prime blocks. -/
def integerThinEndpoint (B K ell j : ℕ) : ℕ :=
  2 ^ integerThinExponent B K ell j

theorem integerThinIndex_le_count (K ell j : ℕ) :
    integerThinIndex K ell j ≤ integerThinBlockCount K ell := by
  exact min_le_right _ _

theorem integerThinIndex_mono (K ell : ℕ) :
    Monotone (integerThinIndex K ell) := by
  intro i j hij
  exact min_le_min_right _ hij

private theorem integerThinCore_succ {L J m : ℕ} (hm : m < J) :
    L ^ (J - m) * (L + 1) ^ m ≤
      L ^ (J - (m + 1)) * (L + 1) ^ (m + 1) := by
  have hsub : J - m = (J - (m + 1)) + 1 := by omega
  rw [hsub, pow_succ, pow_succ]
  nlinarith [Nat.zero_le (L ^ (J - (m + 1)) * (L + 1) ^ m)]

private theorem integerThinCore_mono_of_le {L J m n : ℕ}
    (hmn : m ≤ n) (hnJ : n ≤ J) :
    L ^ (J - m) * (L + 1) ^ m ≤
      L ^ (J - n) * (L + 1) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | @succ n hmn ih =>
      exact ih (Nat.le_trans (Nat.le_succ n) hnJ) |>.trans
        (integerThinCore_succ (lt_of_lt_of_le (Nat.lt_succ_self n) hnJ))

theorem integerThinExponent_mono (B K ell : ℕ) :
    Monotone (integerThinExponent B K ell) := by
  intro i j hij
  let J := integerThinBlockCount K ell
  have hm : integerThinIndex K ell i ≤ integerThinIndex K ell j :=
    integerThinIndex_mono K ell hij
  have hcore := integerThinCore_mono_of_le (L := ell + 1) hm
    (integerThinIndex_le_count K ell j)
  dsimp [integerThinExponent]
  simpa [J, mul_assoc] using! Nat.mul_le_mul_left B hcore

theorem integerThinEndpoint_mono (B K ell : ℕ) :
    Monotone (integerThinEndpoint B K ell) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (integerThinExponent_mono B K ell hij)

theorem integerThinIndex_eq_self {K ell j : ℕ}
    (hj : j ≤ integerThinBlockCount K ell) :
    integerThinIndex K ell j = j := by
  exact min_eq_left hj

theorem integerThinExponent_eq_of_le {B K ell j : ℕ}
    (hj : j ≤ integerThinBlockCount K ell) :
    integerThinExponent B K ell j =
      B * (ell + 1) ^ (integerThinBlockCount K ell - j) *
        (ell + 2) ^ j := by
  simp [integerThinExponent, integerThinIndex_eq_self hj]

theorem integerThinExponent_step {B K ell j : ℕ}
    (hj : 1 ≤ j) (hjJ : j ≤ integerThinBlockCount K ell) :
    (ell + 1) * integerThinExponent B K ell j =
      (ell + 2) * integerThinExponent B K ell (j - 1) := by
  rw [integerThinExponent_eq_of_le hjJ,
    integerThinExponent_eq_of_le ((Nat.sub_le j 1).trans hjJ)]
  have hsub : integerThinBlockCount K ell - (j - 1) =
      (integerThinBlockCount K ell - j) + 1 := by omega
  have hjstep : j = (j - 1) + 1 := by omega
  have hpowL : (ell + 1) ^
        (integerThinBlockCount K ell - (j - 1)) =
      (ell + 1) ^ (integerThinBlockCount K ell - j) * (ell + 1) := by
    rw [hsub, pow_succ]
  have hpowR : (ell + 2) ^ j = (ell + 2) ^ (j - 1) * (ell + 2) := by
    let n := j - 1
    have hjn : j = n + 1 := by dsimp [n]; omega
    calc
      (ell + 2) ^ j = (ell + 2) ^ (n + 1) := by rw [hjn]
      _ = (ell + 2) ^ n * (ell + 2) := pow_succ _ _
      _ = (ell + 2) ^ (j - 1) * (ell + 2) := by rfl
  rw [hpowL, hpowR]
  ring

theorem log_integerThinEndpoint (B K ell j : ℕ) :
    Real.log (integerThinEndpoint B K ell j : ℝ) =
      (integerThinExponent B K ell j : ℝ) * Real.log 2 := by
  unfold integerThinEndpoint
  rw [show ((2 ^ integerThinExponent B K ell j : ℕ) : ℝ) =
      (2 : ℝ) ^ integerThinExponent B K ell j by norm_cast]
  rw [Real.log_pow]

theorem integerThinExponent_pos {B K ell j : ℕ} (hB : 1 ≤ B) :
    0 < integerThinExponent B K ell j := by
  unfold integerThinExponent
  have hBpos : 0 < B := Nat.zero_lt_of_lt hB
  have hL : 0 < ell + 1 := by omega
  have hR : 0 < ell + 1 + 1 := by omega
  positivity

theorem log_integerThinEndpoint_pos {B K ell j : ℕ} (hB : 1 ≤ B) :
    0 < Real.log (integerThinEndpoint B K ell j : ℝ) := by
  rw [log_integerThinEndpoint]
  have hexp : (0 : ℝ) < integerThinExponent B K ell j := by
    exact_mod_cast (integerThinExponent_pos (K := K) (ell := ell)
      (j := j) hB)
  exact mul_pos hexp (Real.log_pos (by norm_num))

theorem log_integerThinEndpoint_ratio {B K ell j : ℕ}
    (hB : 1 ≤ B) (hj : 1 ≤ j)
    (hjJ : j ≤ integerThinBlockCount K ell) :
    Real.log (integerThinEndpoint B K ell j : ℝ) /
        Real.log (integerThinEndpoint B K ell (j - 1) : ℝ) =
      (ell + 2 : ℝ) / (ell + 1 : ℝ) := by
  rw [log_integerThinEndpoint, log_integerThinEndpoint]
  have hstep := integerThinExponent_step (B := B) (K := K)
    (ell := ell) (j := j) hj hjJ
  have hstepR : (ell + 1 : ℝ) * integerThinExponent B K ell j =
      (ell + 2 : ℝ) * integerThinExponent B K ell (j - 1) := by
    exact_mod_cast hstep
  have hprev : (0 : ℝ) < integerThinExponent B K ell (j - 1) := by
    exact_mod_cast integerThinExponent_pos (K := K) (ell := ell)
      (j := j - 1) hB
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  field_simp
  nlinarith

/-- Consecutive valid blocks have `log log` width at most `1 / (ell+1)`,
and hence at most the `1 / ell` width needed by equation (23). -/
theorem integerThinEndpoint_logLog_width {B K ell j : ℕ}
    (hB : 1 ≤ B) (hj : 1 ≤ j)
    (hjJ : j ≤ integerThinBlockCount K ell) :
    logLogNat (integerThinEndpoint B K ell j) -
        logLogNat (integerThinEndpoint B K ell (j - 1)) ≤
      1 / (ell + 1 : ℝ) := by
  let a := integerThinEndpoint B K ell (j - 1)
  let b := integerThinEndpoint B K ell j
  have hloga : Real.log (a : ℝ) ≠ 0 :=
    (log_integerThinEndpoint_pos (K := K) (ell := ell)
      (j := j - 1) hB).ne'
  have hlogb : Real.log (b : ℝ) ≠ 0 :=
    (log_integerThinEndpoint_pos (K := K) (ell := ell)
      (j := j) hB).ne'
  have hratio : Real.log (b : ℝ) / Real.log (a : ℝ) =
      (ell + 2 : ℝ) / (ell + 1 : ℝ) :=
    log_integerThinEndpoint_ratio hB hj hjJ
  rw [logLogNat, logLogNat, ← Real.log_div hlogb hloga, hratio]
  have hratioPos : (0 : ℝ) < (ell + 2 : ℝ) / (ell + 1 : ℝ) := by positivity
  calc
    Real.log ((ell + 2 : ℝ) / (ell + 1 : ℝ))
        ≤ (ell + 2 : ℝ) / (ell + 1 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hratioPos
    _ = 1 / (ell + 1 : ℝ) := by field_simp; ring

theorem base_le_integerThinExponent (B K ell j : ℕ) :
    B ≤ integerThinExponent B K ell j := by
  unfold integerThinExponent
  have hpowL : 1 ≤ (ell + 1) ^
      (integerThinBlockCount K ell - integerThinIndex K ell j) :=
    one_le_pow₀ (by omega)
  have hpowR : 1 ≤ (ell + 1 + 1) ^ integerThinIndex K ell j :=
    one_le_pow₀ (by omega)
  calc
    B = B * 1 * 1 := by simp
    _ ≤ B * (ell + 1) ^
          (integerThinBlockCount K ell - integerThinIndex K ell j) *
        (ell + 1 + 1) ^ integerThinIndex K ell j := by gcongr

theorem base_le_integerThinEndpoint (B K ell j : ℕ) :
    B ≤ integerThinEndpoint B K ell j := by
  calc
    B ≤ 2 ^ B := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ integerThinExponent B K ell j :=
      Nat.pow_le_pow_right (by norm_num) (base_le_integerThinExponent B K ell j)
    _ = integerThinEndpoint B K ell j := rfl

/-- Choosing a base at least `2` makes every lower endpoint large enough for
the Chebyshev error term, uniformly in the block index. -/
theorem scale_le_log_integerThinEndpoint {B K ell j : ℕ} (hB : 2 ≤ B) :
    (ell : ℝ) ≤ Real.log (integerThinEndpoint B K ell j : ℝ) := by
  rw [log_integerThinEndpoint]
  have hJpos : 0 < integerThinBlockCount K ell := by
    unfold integerThinBlockCount
    positivity
  have hcore : ell + 1 ≤
      (ell + 1) ^ (integerThinBlockCount K ell) := by
    exact le_self_pow₀ (by omega) hJpos.ne'
  have hzeroIndex : integerThinIndex K ell 0 = 0 := by
    simp [integerThinIndex]
  have hbaseExponent : 2 * (ell + 1) ≤ integerThinExponent B K ell 0 := by
    rw [integerThinExponent_eq_of_le (Nat.zero_le _)]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    exact Nat.mul_le_mul hB hcore
  have hmono : integerThinExponent B K ell 0 ≤
      integerThinExponent B K ell j :=
    integerThinExponent_mono B K ell (Nat.zero_le j)
  have hexp : (2 : ℝ) * (ell + 1 : ℝ) ≤
      integerThinExponent B K ell j := by
    exact_mod_cast hbaseExponent.trans hmono
  have hlog : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  calc
    (ell : ℝ) ≤ (ell + 1 : ℝ) := by norm_num
    _ = (2 * (ell + 1 : ℝ)) * (1 / 2 : ℝ) := by ring
    _ ≤ (integerThinExponent B K ell j : ℝ) * (1 / 2 : ℝ) := by gcongr
    _ ≤ (integerThinExponent B K ell j : ℝ) * Real.log 2 := by
      gcongr

theorem two_le_integerThinEndpoint {B K ell j : ℕ} (hB : 1 ≤ B) :
    2 ≤ integerThinEndpoint B K ell j := by
  have hexp : 1 ≤ integerThinExponent B K ell j := by
    unfold integerThinExponent
    change 1 ≤ B * (ell + 1) ^
      (integerThinBlockCount K ell - integerThinIndex K ell j) *
        (ell + 1 + 1) ^ integerThinIndex K ell j
    have hL : 1 ≤ ell + 1 := Nat.succ_le_succ (Nat.zero_le ell)
    have hpowL : 1 ≤ (ell + 1) ^
        (integerThinBlockCount K ell - integerThinIndex K ell j) :=
      one_le_pow₀ hL
    have hpowR : 1 ≤ (ell + 1 + 1) ^ integerThinIndex K ell j :=
      one_le_pow₀ (by omega)
    exact one_le_mul (one_le_mul hB hpowL) hpowR
  change 2 ^ 1 ≤ 2 ^ integerThinExponent B K ell j
  exact Nat.pow_le_pow_right (by norm_num) hexp

/-- The logarithmic endpoint ratio from the base of a scale has a closed
form.  This is the exact damping geometry needed for Caich's normalized
energy. -/
theorem log_integerThinEndpoint_div_zero {B K ell j : ℕ}
    (hB : 1 ≤ B) (hj : j ≤ integerThinBlockCount K ell) :
    Real.log (integerThinEndpoint B K ell j : ℝ) /
        Real.log (integerThinEndpoint B K ell 0 : ℝ) =
      ((ell + 2 : ℕ) : ℝ) ^ j / ((ell + 1 : ℕ) : ℝ) ^ j := by
  rw [log_integerThinEndpoint, log_integerThinEndpoint,
    integerThinExponent_eq_of_le hj,
    integerThinExponent_eq_of_le (Nat.zero_le _)]
  simp only [Nat.sub_zero, pow_zero, mul_one, Nat.cast_mul, Nat.cast_pow]
  have hBne : (B : ℝ) ≠ 0 := by positivity
  have hLne : ((ell + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simpa [add_comm] using!
    (pow_sub_mul_pow (((ell + 1 : ℕ) : ℝ)) hj)

/-- Along the whole integer schedule, recovery of Caich's damping costs less
than the absolute factor `2 * π`.  The normalized exponent is at most one:
there are `(ell+1)^K` steps and each step has logarithmic ratio at most `e`.
-/
theorem integerThinEndpoint_caichDamping_le_two_pi
    {B K ell j : ℕ} (hB : 1 ≤ B)
    (hj : j ≤ integerThinBlockCount K ell) :
    Real.exp
        (Real.log
            (Real.log (integerThinEndpoint B K ell j : ℝ) /
              Real.log (integerThinEndpoint B K ell 0 : ℝ)) /
          (((ell + 1 : ℕ) : ℝ) ^ K)) ≤
      2 * Real.pi := by
  rw [log_integerThinEndpoint_div_zero hB hj, ← div_pow]
  let q : ℝ := ((ell + 2 : ℕ) : ℝ) / ((ell + 1 : ℕ) : ℝ)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqlog : Real.log q ≤ 1 := by
    calc
      Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hqpos
      _ = 1 / (((ell + 1 : ℕ) : ℝ)) := by
        dsimp [q]
        field_simp
        norm_num [Nat.cast_add]
      _ ≤ 1 := by
        apply (div_le_one (by positivity)).2
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le ell)
  have hlog : Real.log (q ^ j) ≤ (integerThinBlockCount K ell : ℝ) := by
    rw [Real.log_pow]
    calc
      (j : ℝ) * Real.log q ≤ (j : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hqlog (by positivity)
      _ = (j : ℝ) := by ring
      _ ≤ (integerThinBlockCount K ell : ℝ) := by exact_mod_cast hj
  have hdenom : (0 : ℝ) < (((ell + 1 : ℕ) : ℝ) ^ K) := by positivity
  have hexponent :
      Real.log (q ^ j) / (((ell + 1 : ℕ) : ℝ) ^ K) ≤ 1 := by
    apply (div_le_one hdenom).2
    simpa [integerThinBlockCount] using! hlog
  calc
    Real.exp
          (Real.log (q ^ j) / (((ell + 1 : ℕ) : ℝ) ^ K)) ≤
        Real.exp 1 := Real.exp_le_exp.mpr hexponent
    _ ≤ 3 := Real.exp_one_lt_three.le
    _ ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]

/-- Chebyshev's theorem supplies one absolute reciprocal-prime constant for
all blocks of the exact integer schedule. -/
theorem exists_integerThinSchedule_reciprocalBound (K : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ ell j : ℕ, 1 ≤ ell → 1 ≤ j →
        j ≤ integerThinBlockCount K ell →
          freshReciprocalSum
              (integerThinEndpoint B K ell (j - 1))
              (integerThinEndpoint B K ell j) ≤ A / (ell : ℝ) := by
  obtain ⟨A, hA, N, hN, hrecip⟩ :=
    exists_unconditional_thinBlockReciprocalBound
  refine ⟨N, hN, A, hA, ?_⟩
  intro ell j hell hj hjJ
  let a := integerThinEndpoint N K ell (j - 1)
  let b := integerThinEndpoint N K ell j
  have hNa : N ≤ a := base_le_integerThinEndpoint N K ell (j - 1)
  have ha : 2 ≤ a := hN.trans hNa
  have hab : a ≤ b := integerThinEndpoint_mono N K ell (Nat.sub_le j 1)
  have hellpos : 0 < ell := Nat.zero_lt_of_lt hell
  have hwidth₀ : logLogNat b - logLogNat a ≤ 1 / (ell + 1 : ℝ) :=
    integerThinEndpoint_logLog_width (by omega) hj hjJ
  have hdenom : (ell : ℝ) ≤ (ell + 1 : ℝ) := by norm_num
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hellpos
  have hwidth : logLogNat b - logLogNat a ≤ 1 / (ell : ℝ) :=
    hwidth₀.trans (div_le_div_of_nonneg_left (by norm_num) hellR hdenom)
  have hlarge : (ell : ℝ) ≤ Real.log (a : ℝ) :=
    scale_le_log_integerThinEndpoint hN
  exact hrecip hNa ha hab hellpos hwidth hlarge

/-- The exact integer endpoints, Caich's normalized energy, and the
unconditional Chebyshev reciprocal bound form an actual concrete thin-block
schedule.  Both analytic constants are uniform in the scale and block. -/
theorem exists_integerConcreteThinBlockSchedule (K : ℕ) :
    ∃ s : ConcreteThinBlockSchedule, ∃ B : ℕ, 2 ≤ B ∧
      s.J = integerThinBlockCount K ∧
      s.y = integerThinEndpoint B K ∧
      s.I = fun ell j ↦
        caichNormalizedEnergy (ell + 1) K
          (integerThinEndpoint B K ell 0)
          (integerThinEndpoint B K ell j) := by
  obtain ⟨B, hB, A, hA, hrecip⟩ :=
    exists_integerThinSchedule_reciprocalBound K
  let s : ConcreteThinBlockSchedule :=
    { J := integerThinBlockCount K
      y := integerThinEndpoint B K
      y_monotone := fun ell ↦ integerThinEndpoint_mono B K ell
      two_le_y := fun _ell _j ↦ two_le_integerThinEndpoint (hB.trans' (by norm_num))
      I := fun ell j ↦
        caichNormalizedEnergy (ell + 1) K
          (integerThinEndpoint B K ell 0)
          (integerThinEndpoint B K ell j)
      I_nonneg := by
        intro ell j old
        apply caichNormalizedEnergy_nonneg
        exact lt_of_lt_of_le Nat.one_lt_two
          (two_le_integerThinEndpoint (hB.trans' (by norm_num)))
      Cparseval := 1
      Cparseval_nonneg := by norm_num
      Crecip := A
      Crecip_nonneg := hA.le
      parseval_le := by
        intro ell _hell j _hj hjJ old
        let a := integerThinEndpoint B K ell (j - 1)
        let b := integerThinEndpoint B K ell j
        have ha : 1 < a := by
          exact lt_of_lt_of_le Nat.one_lt_two
            (two_le_integerThinEndpoint (hB.trans' (by norm_num)))
        have hab : a ≤ b :=
          integerThinEndpoint_mono B K ell (Nat.sub_le j 1)
        have hjprev : j - 1 ≤ integerThinBlockCount K ell :=
          (Nat.sub_le j 1).trans hjJ
        have hdamp :
            Real.exp
                (Real.log
                    (Real.log (a : ℝ) /
                      Real.log (integerThinEndpoint B K ell 0 : ℝ)) /
                  (((ell + 1 : ℕ) : ℝ) ^ K)) ≤
              (2 * Real.pi) * (1 : ℝ) := by
          simpa [a] using!
            (integerThinEndpoint_caichDamping_le_two_pi
              (K := K) (hB.trans' (by norm_num)) hjprev)
        change smoothEnergy old a / Real.log (b : ℝ) ≤
          (1 : ℝ) *
            caichNormalizedEnergy (ell + 1) K
              (integerThinEndpoint B K ell 0) a old
        exact smoothEnergy_div_log_le_caichNormalizedEnergy
          ha hab hdamp old
      reciprocal_le := by
        intro ell hell j hj hjJ
        exact hrecip ell j hell hj hjJ }
  exact ⟨s, B, hB, rfl, rfl, rfl⟩

/-- In particular, the integer schedule supplies the concrete moment bound
needed by the repaired equation-(16) argument, with no schedule hypotheses. -/
theorem exists_integerThinPrimeBlockMomentBound (K : ℕ) :
    ∃ s : ConcreteThinBlockSchedule,
      s.J = integerThinBlockCount K ∧
        ThinPrimeBlockMomentBound μ s.toThinBlockData := by
  obtain ⟨s, B, hB, hJ, _hy, _hI⟩ :=
    exists_integerConcreteThinBlockSchedule K
  exact ⟨s, hJ, s.thinPrimeBlockMomentBound⟩

end Problem520
end Erdos
