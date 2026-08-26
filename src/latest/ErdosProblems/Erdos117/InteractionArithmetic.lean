import ErdosProblems.Erdos117.ScalarCliques

/-!
# Expensive stages have small interaction

This is the integer arithmetic behind Corollary 5.8. The constants are
absolute; no asymptotic estimate is used as an assumption.
-/

namespace Erdos117

theorem scalarCreditRate_pos {p : ℕ} [Fact p.Prime] : 0 < scalarCreditRate p := by
  by_cases hp : p = 3
  · simp [scalarCreditRate, hp]
  · simpa [scalarCreditRate, hp] using (Fact.out : p.Prime).pos

theorem scalarDefect_le_quarter_credit (p : ℕ) {m : ℕ} (hm : 0 < m) :
    4 * scalarDefect p ≤ scalarCreditRate p * m + 4 := by
  by_cases hp : p = 3
  · simp only [scalarCreditRate, scalarDefect, if_pos hp]
    omega
  · simp [scalarCreditRate, scalarDefect, hp]

theorem three_quarters_scalar_credit (p : ℕ) {m n : ℕ} (hm : 0 < m)
    (hcredit : scalarCreditRate p * m ≤ n - 1 + scalarDefect p) :
    3 * (scalarCreditRate p * m) ≤ 4 * n := by
  by_cases hp : p = 3
  · simp only [scalarCreditRate, scalarDefect, if_pos hp] at hcredit ⊢
    omega
  · simp only [scalarCreditRate, scalarDefect, if_neg hp, Nat.add_zero] at hcredit ⊢
    omega

/-- An explicit version of the large-interaction contradiction. The product
inequality alone forces `t*w*m ≤ 4*n` once `w*m² ≥ 128*n*ell`. -/
theorem interaction_small_of_expensive {w m n ell delta t : ℕ}
    (hw : 0 < w) (hm : 0 < m) (hscalar : 3 * (w * m) ≤ 4 * n)
    (hdelta : 4 * delta ≤ w * m + 4)
    (hexpensive : 128 * n * ell ≤ w * m * m)
    (hproduct : ∀ d ≤ t, ∃ c : ℕ,
      w * m ≤ c + delta + w * ((d + 1) * ell) ∧ (d + 1) * (c + 1) ≤ n) :
    t * (w * m) ≤ 4 * n := by
  let s := w * m
  have hs : 0 < s := Nat.mul_pos hw hm
  change t * s ≤ 4 * n
  by_contra hbad
  have hbad' : 4 * n < t * s := Nat.lt_of_not_ge hbad
  let d := 4 * n / s + 1
  let q := d + 1
  have hdt : d ≤ t := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hs).mpr hbad')
  obtain ⟨c, hcredit, hcard⟩ := hproduct d hdt
  have hm96 : 96 * ell ≤ m := by
    refine Nat.le_of_mul_le_mul_left ?_ hs
    calc
      s * (96 * ell) = 32 * ell * (3 * (w * m)) := by dsimp [s]; ring
      _ ≤ 32 * ell * (4 * n) := Nat.mul_le_mul_left _ hscalar
      _ = 128 * n * ell := by ring
      _ ≤ s * m := hexpensive
  have hm16 : 16 * ell ≤ m := by omega
  have hn32 : 32 * n * ell ≤ s * m := by
    calc
      32 * n * ell ≤ 128 * n * ell :=
        Nat.mul_le_mul_right ell (Nat.mul_le_mul_right n (by decide))
      _ ≤ s * m := hexpensive
  have hq : s * q ≤ 4 * n + 2 * s := by
    have hdiv := Nat.div_mul_le_self (4 * n) s
    dsimp [q, d]
    nlinarith
  have hrhs : 4 * w * ell * (4 * n + 2 * s) ≤ s * s := by
    refine Nat.le_of_mul_le_mul_left ?_ (show (0 : ℕ) < 2 by decide)
    calc
      2 * (4 * w * ell * (4 * n + 2 * s)) =
          w * (32 * n * ell) + (w * s) * (16 * ell) := by ring
      _ ≤ w * (s * m) + (w * s) * m :=
        Nat.add_le_add (Nat.mul_le_mul_left w hn32) (Nat.mul_le_mul_left (w * s) hm16)
      _ = 2 * (s * s) := by dsimp [s]; ring
  have hdebt : 4 * (w * (q * ell)) ≤ s := by
    refine Nat.le_of_mul_le_mul_left ?_ hs
    calc
      s * (4 * (w * (q * ell))) = (4 * w * ell) * (s * q) := by ring
      _ ≤ (4 * w * ell) * (4 * n + 2 * s) := Nat.mul_le_mul_left _ hq
      _ ≤ s * s := hrhs
  have hhalf : s ≤ 2 * (c + 1) := by
    change s ≤ c + delta + w * (q * ell) at hcredit
    change 4 * delta ≤ s + 4 at hdelta
    omega
  have hupper : q * s ≤ 2 * n := by
    calc
      q * s ≤ q * (2 * (c + 1)) := Nat.mul_le_mul_left q hhalf
      _ = 2 * (q * (c + 1)) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hcard
  have hlower : 4 * n < q * s := by
    calc
      4 * n < s * d := Nat.lt_mul_div_succ _ hs
      _ ≤ s * q := Nat.mul_le_mul_left s (Nat.le_succ d)
      _ = q * s := Nat.mul_comm _ _
  omega

end Erdos117
