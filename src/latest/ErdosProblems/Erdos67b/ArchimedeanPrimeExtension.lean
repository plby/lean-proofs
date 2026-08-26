import ErdosProblems.Erdos67b.Section4Assembly

/-!
# Prime extension of the Archimedean twist

The prime-coordinate assignment `p ↦ p^(it)` extends to the expected
completely multiplicative function `n ↦ n^(it)` on positive naturals.
-/

namespace Erdos67b

noncomputable section

theorem archimedeanTwist_mul {m n : ℕ} (t : ℝ)
    (_hm : 0 < m) (_hn : 0 < n) :
    archimedeanTwist t (m * n) =
      archimedeanTwist t m * archimedeanTwist t n := by
  unfold archimedeanTwist
  rw [Nat.cast_mul]
  simpa only [Complex.ofReal_natCast, Complex.ofReal_mul] using
    (Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg m) (Nat.cast_nonneg n) (Complex.I * (t : ℂ)))

theorem primeExtension_archimedeanPrimeAssignment
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    (primeExtension (archimedeanPrimeAssignment t) n : ℂ) =
      archimedeanTwist t n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · subst n
        simp [archimedeanTwist, primeExtension_one]
      · have hn2 : 2 ≤ n := by omega
        let p : PrimeNat := ⟨n.minFac, Nat.minFac_prime (by omega)⟩
        have hpdiv : (p : ℕ) ∣ n := Nat.minFac_dvd n
        have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
        have hquotpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpdiv) p.2.pos
        have hquotlt : n / p < n := Nat.div_lt_self hn (by exact p.2.one_lt)
        calc
          (primeExtension (archimedeanPrimeAssignment t) n : ℂ) =
              (primeExtension (archimedeanPrimeAssignment t) p : ℂ) *
                (primeExtension (archimedeanPrimeAssignment t) (n / p) : ℂ) := by
            rw [← Circle.coe_mul, ← primeExtension_mul _ hp0 hquotpos.ne',
              Nat.mul_div_cancel' hpdiv]
          _ = archimedeanTwist t p * archimedeanTwist t (n / p) := by
            rw [primeExtension_prime, archimedeanPrimeAssignment_coe,
              ih (n / p) hquotlt hquotpos]
          _ = archimedeanTwist t n := by
            rw [← archimedeanTwist_mul t p.2.pos hquotpos,
              Nat.mul_div_cancel' hpdiv]

theorem norm_primeExtension_archimedeanPrimeAssignment
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖(primeExtension (archimedeanPrimeAssignment t) n : ℂ)‖ = 1 := by
  rw [primeExtension_archimedeanPrimeAssignment t hn,
    norm_archimedeanTwist hn]

theorem norm_primeExtension_archimedean_sub_le
    (t : ℝ) {n h : ℕ} (hn : 0 < n) :
    ‖(primeExtension (archimedeanPrimeAssignment t) (n + h) : ℂ) -
        (primeExtension (archimedeanPrimeAssignment t) n : ℂ)‖ ≤
      |t| * (h : ℝ) / n := by
  rw [primeExtension_archimedeanPrimeAssignment t (Nat.add_pos_left hn h),
    primeExtension_archimedeanPrimeAssignment t hn]
  have hratio := norm_localArchimedeanRatio_sub_one_le t (h := h) hn
  rw [localArchimedeanRatio_eq_twist_div t hn] at hratio
  have hnunit := norm_archimedeanTwist hn t
  have heq :
      archimedeanTwist t (n + h) - archimedeanTwist t n =
        archimedeanTwist t n *
          (archimedeanTwist t (n + h) / archimedeanTwist t n - 1) := by
    have hne : archimedeanTwist t n ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hnunit
      norm_num at hnunit
    field_simp
  rw [heq, norm_mul, hnunit, one_mul]
  exact hratio

end

end Erdos67b
