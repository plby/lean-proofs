import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Erdos1211Dynamics

/-- The sharp constant in the Conlon--Fox--Pham interval process. -/
noncomputable def sharpConstant : ℝ := (2 + Real.sqrt 3) / 4

/-- A linear Lyapunov function for the two-coordinate recurrence. -/
noncomputable def potential (a b : ℝ) : ℝ := a + (5 / 2) * b

/-- The polynomial whose larger root is `sharpConstant`. -/
noncomputable def discriminantGap (M : ℝ) : ℝ := 16 * M * (1 - M) - 1

/-- The uniform increment furnished by the two ranges `z ≤ 2/5` and `2/5 ≤ z`. -/
noncomputable def increment (M : ℝ) : ℝ :=
  min (5 * discriminantGap M / (16 * M)) (15 / 4 - 4 * M)

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  norm_num

lemma sqrt_three_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _

lemma sharpConstant_lt_one : sharpConstant < 1 := by
  dsimp [sharpConstant]
  nlinarith [sqrt_three_sq, sqrt_three_nonneg]

lemma sharpConstant_lt_fifteen_sixteen : sharpConstant < 15 / 16 := by
  dsimp [sharpConstant]
  nlinarith [sqrt_three_sq, sqrt_three_nonneg]

lemma discriminantGap_pos {M : ℝ} (hMlow : 3 / 4 ≤ M)
    (hMhigh : M < sharpConstant) : 0 < discriminantGap M := by
  have hsmallRoot : (2 - Real.sqrt 3) / 4 < M := by
    nlinarith [sqrt_three_nonneg]
  have hfactor :
      discriminantGap M =
        16 * (sharpConstant - M) * (M - (2 - Real.sqrt 3) / 4) := by
    dsimp [discriminantGap, sharpConstant]
    nlinarith [sqrt_three_sq]
  rw [hfactor]
  positivity

lemma increment_pos {M : ℝ} (hMlow : 3 / 4 ≤ M)
    (hMhigh : M < sharpConstant) : 0 < increment M := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMlow
  have hgap : 0 < discriminantGap M := discriminantGap_pos hMlow hMhigh
  have hfirst : 0 < 5 * discriminantGap M / (16 * M) := by positivity
  have hsecond : 0 < 15 / 4 - 4 * M := by
    have := sharpConstant_lt_fifteen_sixteen
    nlinarith
  exact lt_min hfirst hsecond

/-- One controlled recurrence step remaining in `[0,M]²` raises `potential`
by the explicit positive amount `increment M`. -/
lemma potential_step_ge_increment {M a b A B z : ℝ}
    (hMlow : 3 / 4 ≤ M) (hMhigh : M < sharpConstant)
    (ha0 : 0 ≤ a) (haM : a ≤ M) (hAM : A ≤ M)
    (hz0 : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hA : A = b * z + 1 - z / 2) (hB : B = a * z) :
    increment M ≤ potential A B - potential a b := by
  have hMone : M < 1 := lt_trans hMhigh sharpConstant_lt_one
  have hzpos : 0 < z := by
    rcases hz0.eq_or_lt with rfl | hz
    · norm_num at hA
      nlinarith
    · exact hz
  have hconstraint : 0 ≤ z * (1 / 2 - b) - (1 - M) := by
    nlinarith [hAM]
  have hdelta :
      potential A B - potential a b =
        1 - z / 2 + ((5 / 2) * z - 1) * a + (z - 5 / 2) * b := by
    rw [hA, hB]
    simp only [potential]
    ring
  have hgap : 0 < discriminantGap M := discriminantGap_pos hMlow hMhigh
  by_cases hz : z ≤ 2 / 5
  · have hfac0 : 0 ≤ 5 / 2 - z := by nlinarith
    have hacoef0 : 0 ≤ 1 - (5 / 2) * z := by nlinarith
    have hMa0 : 0 ≤ M - a := sub_nonneg.mpr haM
    have hprod1 : 0 ≤ (5 / 2 - z) * (z * (1 / 2 - b) - (1 - M)) :=
      mul_nonneg hfac0 hconstraint
    have hprod2 : 0 ≤ z * (M - a) * (1 - (5 / 2) * z) :=
      mul_nonneg (mul_nonneg hz0 hMa0) hacoef0
    have hlower :
        (5 / 2) * (M * z ^ 2 + 1 - M - z / 2) ≤
          z * (potential A B - potential a b) := by
      rw [hdelta]
      nlinarith [hprod1, hprod2]
    have hsquare : 0 ≤ (4 * M * z - 1) ^ 2 := sq_nonneg _
    have hquadratic :
        discriminantGap M ≤ 16 * M * (M * z ^ 2 + 1 - M - z / 2) := by
      dsimp [discriminantGap]
      nlinarith
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMlow
    have hdenpos : 0 < 16 * M := mul_pos (by norm_num) hMpos
    have hq : discriminantGap M / (16 * M) ≤
        M * z ^ 2 + 1 - M - z / 2 := by
      exact (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hquadratic)
    have hhalfGap :
        z * (5 * discriminantGap M / (16 * M)) ≤
          (5 / 2) * (discriminantGap M / (16 * M)) := by
      have hfirstNonneg : 0 ≤ 5 * discriminantGap M / (16 * M) := by positivity
      have hid :
          (5 / 2) * (discriminantGap M / (16 * M)) =
            (1 / 2) * (5 * discriminantGap M / (16 * M)) := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right hzhalf hfirstNonneg
    have hqmul :
        (5 / 2) * (discriminantGap M / (16 * M)) ≤
          (5 / 2) * (M * z ^ 2 + 1 - M - z / 2) := by
      nlinarith
    have hmul :
        z * (5 * discriminantGap M / (16 * M)) ≤
          z * (potential A B - potential a b) :=
      hhalfGap.trans (hqmul.trans hlower)
    have hfirst :
        5 * discriminantGap M / (16 * M) ≤
          potential A B - potential a b :=
      le_of_mul_le_mul_left hmul hzpos
    exact (min_le_left _ _).trans hfirst
  · have hz' : 2 / 5 ≤ z := le_of_not_ge hz
    have hfac0 : 0 ≤ 5 / 2 - z := by nlinarith
    have hacoef0 : 0 ≤ (5 / 2) * z - 1 := by nlinarith
    have hMnonneg : 0 ≤ 1 - M := by linarith
    have hzone : 0 ≤ 1 - 2 * z := by linarith
    have hprod1 : 0 ≤ (5 / 2 - z) * (z * (1 / 2 - b) - (1 - M)) :=
      mul_nonneg hfac0 hconstraint
    have hprod2 : 0 ≤ z * ((5 / 2) * z - 1) * a :=
      mul_nonneg (mul_nonneg hz0 hacoef0) ha0
    have hprod3 : 0 ≤ (5 / 2) * (1 - M) * (1 - 2 * z) :=
      mul_nonneg (mul_nonneg (by norm_num) hMnonneg) hzone
    have hsecond :
        15 / 4 - 4 * M ≤ potential A B - potential a b := by
      have hmul :
          z * (15 / 4 - 4 * M) ≤ z * (potential A B - potential a b) := by
        rw [hdelta]
        nlinarith [hprod1, hprod2, hprod3]
      exact le_of_mul_le_mul_left hmul hzpos
    exact (min_le_right _ _).trans hsecond

/-- No infinite controlled orbit of the CFP recurrence can remain in the square
`[0,M]²` when `M` is strictly below the sharp constant. -/
theorem no_infinite_orbit_below_sharp {M : ℝ} (hM : M < sharpConstant)
    (a b z : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ M)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ M)
    (hz : ∀ n, 0 ≤ z n ∧ z n ≤ 1 / 2)
    (hrecA : ∀ n, a (n + 1) = b n * z n + 1 - z n / 2)
    (hrecB : ∀ n, b (n + 1) = a n * z n) : False := by
  by_cases hMlow : 3 / 4 ≤ M
  · have hincpos : 0 < increment M := increment_pos hMlow hM
    have hstep : ∀ n,
        increment M ≤ potential (a (n + 1)) (b (n + 1)) - potential (a n) (b n) := by
      intro n
      exact potential_step_ge_increment hMlow hM
        (ha n).1 (ha n).2 (ha (n + 1)).2
        (hz n).1 (hz n).2 (hrecA n) (hrecB n)
    have hiterate : ∀ n : ℕ,
        potential (a 0) (b 0) + (n : ℝ) * increment M ≤ potential (a n) (b n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          have hs := hstep n
          push_cast
          nlinarith
    have hupper : ∀ n, potential (a n) (b n) ≤ (7 / 2) * M := by
      intro n
      dsimp [potential]
      nlinarith [(ha n).2, (hb n).2]
    obtain ⟨n, hn⟩ := exists_nat_gt
      (((7 / 2) * M - potential (a 0) (b 0)) / increment M)
    have hnmul := mul_lt_mul_of_pos_right hn hincpos
    have hlarge :
        (7 / 2) * M < potential (a 0) (b 0) + (n : ℝ) * increment M := by
      rw [div_mul_cancel₀ _ hincpos.ne'] at hnmul
      linarith
    exact (not_lt_of_ge ((hiterate n).trans (hupper n))) hlarge
  · have hMsmall : M < 3 / 4 := lt_of_not_ge hMlow
    have hnonneg : 0 ≤ b 0 * z 0 := mul_nonneg (hb 0).1 (hz 0).1
    have hrec0 : a 1 = b 0 * z 0 + 1 - z 0 / 2 := by
      simpa using hrecA 0
    have hlower : 3 / 4 ≤ a 1 := by
      rw [hrec0]
      nlinarith [(hz 0).2]
    nlinarith [(ha 1).2]

/-- Tail form used by the interval-process argument: a controlled orbit cannot
have both coordinates eventually bounded by one `M < sharpConstant`. -/
theorem no_eventually_bounded_orbit_below_sharp {M : ℝ} (hM : M < sharpConstant)
    (a b z : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (hz : ∀ n, 0 ≤ z n ∧ z n ≤ 1 / 2)
    (hrecA : ∀ n, a (n + 1) = b n * z n + 1 - z n / 2)
    (hrecB : ∀ n, b (n + 1) = a n * z n)
    (hbound : ∃ N, ∀ n, N ≤ n → a n ≤ M ∧ b n ≤ M) : False := by
  obtain ⟨N, hN⟩ := hbound
  let a' : ℕ → ℝ := fun n => a (N + n)
  let b' : ℕ → ℝ := fun n => b (N + n)
  let z' : ℕ → ℝ := fun n => z (N + n)
  apply no_infinite_orbit_below_sharp hM a' b' z'
  · intro n
    exact ⟨ha0 _, (hN _ (Nat.le_add_right N n)).1⟩
  · intro n
    exact ⟨hb0 _, (hN _ (Nat.le_add_right N n)).2⟩
  · intro n
    exact hz _
  · intro n
    simpa only [a', b', z', Nat.add_assoc] using hrecA (N + n)
  · intro n
    simpa only [a', b', z', Nat.add_assoc] using hrecB (N + n)

end Erdos1211Dynamics
