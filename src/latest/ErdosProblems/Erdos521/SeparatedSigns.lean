/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Separation of geometric sign sums for the root-repulsion estimates.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signWordValue (q : ℝ) : List Bool → ℝ
  | [] => 0
  | b :: w => signValue b + q * signWordValue q w

theorem abs_signValue (b : Bool) : |signValue b| = 1 := by
  cases b <;> norm_num [signValue]

theorem signWordValue_abs_le_two {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) (w : List Bool) :
    |signWordValue q w| ≤ 2 := by
  induction w with
  | nil => norm_num [signWordValue]
  | cons b w ih =>
    calc
      |signWordValue q (b :: w)| ≤ |signValue b| + |q * signWordValue q w| := by
        simpa only [Real.norm_eq_abs, signWordValue] using norm_add_le (signValue b) (q * signWordValue q w)
      _ = 1 + q * |signWordValue q w| := by rw [abs_signValue, abs_mul, abs_of_nonneg hq₀]
      _ ≤ 1 + q * 2 := add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hq₀)
      _ ≤ 2 := by linarith

theorem signWordValue_separated {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 2 / 5)
    (w v : List Bool) (hlen : w.length = v.length) (hneq : w ≠ v) :
    q ^ w.length ≤ |signWordValue q w - signWordValue q v| := by
  induction w generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    exact (hneq hv.symm).elim
  | cons b w ih =>
    cases v with
    | nil => simp at hlen
    | cons c v =>
      have hlen' : w.length = v.length := by simpa using hlen
      by_cases hbc : b = c
      · subst c
        have hwv : w ≠ v := by intro h; exact hneq (congrArg (List.cons b) h)
        have htail := ih v hlen' hwv
        have heq : signWordValue q (b :: w) - signWordValue q (b :: v) =
            q * (signWordValue q w - signWordValue q v) := by simp only [signWordValue]; ring
        rw [heq, abs_mul, abs_of_nonneg hq₀, List.length_cons, pow_succ]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left htail hq₀
      · have hhead : |signValue b - signValue c| = 2 := by
          cases b <;> cases c <;> norm_num [signValue] at *
        have hw := signWordValue_abs_le_two hq₀ (by linarith) w
        have hv := signWordValue_abs_le_two hq₀ (by linarith) v
        have htail : |signWordValue q w - signWordValue q v| ≤ 4 := by
          have h := norm_sub_le (signWordValue q w) (signWordValue q v)
          simp only [Real.norm_eq_abs] at h
          linarith
        have heq : signValue b - signValue c =
            (signWordValue q (b :: w) - signWordValue q (c :: v)) -
              q * (signWordValue q w - signWordValue q v) := by
          simp only [signWordValue]
          ring
        have htriangle := norm_sub_le (signWordValue q (b :: w) - signWordValue q (c :: v))
          (q * (signWordValue q w - signWordValue q v))
        simp only [Real.norm_eq_abs] at htriangle
        rw [← heq, hhead, abs_mul, abs_of_nonneg hq₀] at htriangle
        have hmul := mul_le_mul_of_nonneg_left htail hq₀
        have hsep : q ≤ |signWordValue q (b :: w) - signWordValue q (c :: v)| := by
          linarith
        apply le_trans _ hsep
        rw [List.length_cons, pow_succ]
        exact mul_le_of_le_one_left hq₀ (pow_le_one₀ hq₀ (by linarith))

theorem signWordValue_injective_on_length {q : ℝ} (hq₀ : 0 < q) (hq₁ : q ≤ 2 / 5)
    {w v : List Bool} (hlen : w.length = v.length)
    (hvalue : signWordValue q w = signWordValue q v) : w = v := by
  by_contra hneq
  have h := signWordValue_separated hq₀.le hq₁ w v hlen hneq
  rw [hvalue, sub_self, abs_zero] at h
  exact (pow_pos hq₀ _).not_ge h

theorem signWordValue_unique_in_small_interval {q z δ : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 2 / 5)
    {w v : List Bool} (hlen : w.length = v.length) (hδ : 2 * δ < q ^ w.length)
    (hw : |signWordValue q w - z| ≤ δ) (hv : |signWordValue q v - z| ≤ δ) : w = v := by
  by_contra hneq
  have hsep := signWordValue_separated hq₀ hq₁ w v hlen hneq
  have htri := norm_sub_le (signWordValue q w - z) (signWordValue q v - z)
  simp only [Real.norm_eq_abs] at htri
  rw [show (signWordValue q w - z) - (signWordValue q v - z) =
    signWordValue q w - signWordValue q v by ring] at htri
  linarith

def finiteSignValue {k : ℕ} (q : ℝ) (w : Fin k → Bool) : ℝ := signWordValue q (List.ofFn w)

theorem finiteSignValue_small_interval_card {q z δ : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 2 / 5)
    (k : ℕ) (hδ : 2 * δ < q ^ k) :
    (Finset.univ.filter (fun w : Fin k → Bool ↦ |finiteSignValue q w - z| ≤ δ)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro w hw v hv
  apply List.ofFn_injective
  exact signWordValue_unique_in_small_interval hq₀ hq₁ (by simp)
    (by simpa only [List.length_ofFn] using hδ) (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hv).2

theorem finiteSignValue_small_interval_probability {q z δ : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 2 / 5)
    (k : ℕ) (hδ : 2 * δ < q ^ k) :
    (PMF.uniformOfFintype (Fin k → Bool)).toMeasure.real
      {w | |finiteSignValue q w - z| ≤ δ} ≤ 1 / (2 : ℝ) ^ k := by
  classical
  have hcard := finiteSignValue_small_interval_card (z := z) hq₀ hq₁ k hδ
  have hcard' : Fintype.card {w : Fin k → Bool // |finiteSignValue q w - z| ≤ δ} ≤ 1 := by
    simpa only [Fintype.card_subtype] using hcard
  rw [MeasureTheory.measureReal_def, PMF.toMeasure_uniformOfFintype_apply
    (α := Fin k → Bool) (s := {w | |finiteSignValue q w - z| ≤ δ}) (Set.toFinite _).measurableSet,
    ENNReal.toReal_div]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ENNReal.toReal_natCast, Nat.cast_pow,
    Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard') (by positivity)

end Erdos521
