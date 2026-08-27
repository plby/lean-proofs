import ErdosProblems.Erdos4.FGKMTRationalMoments

/-! Divisibility bounds for the actual finite rational-profile square mass. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem logarithmicReciprocal_antitone {b : ℝ} (hb : 0 ≤ b) :
    AntitoneOn (logarithmicReciprocal b) (Set.Ici 1) := by
  intro x hx y hy hxy
  unfold logarithmicReciprocal
  apply (inv_le_inv₀ (logarithmicReciprocal_base_pos hb hy)
    (logarithmicReciprocal_base_pos hb hx)).mpr
  have hlog := Real.log_le_log (zero_lt_one.trans_le hx) hxy
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hb)

theorem squarefreeHarmonicWeight_divisor {W n d : ℕ} (hdn : d ∣ n)
    (hn : Squarefree n) (hW : n.Coprime W) :
    squarefreeHarmonicWeight W n = squarefreeHarmonicWeight W (n / d) / (d.totient : ℝ) := by
  have hprod : d * (n / d) = n := Nat.mul_div_cancel' hdn
  have hcop : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hn)
  have hquot : Squarefree (n / d) := hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hdn)
  have hquotW : (n / d).Coprime W := hW.of_dvd_left (Nat.div_dvd_of_dvd hdn)
  have hphi : (n.totient : ℝ) = (d.totient : ℝ) * ((n / d).totient : ℝ) := by
    calc
      _ = ((d * (n / d)).totient : ℝ) := by rw [hprod]
      _ = _ := by rw [Nat.totient_mul hcop, Nat.cast_mul]
  rw [squarefreeHarmonicWeight, if_pos ⟨hn, hW⟩,
    squarefreeHarmonicWeight, if_pos ⟨hquot, hquotW⟩, hphi]
  ring

theorem rationalSquare_divisor_pointwise (W : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdn : d ∣ n) :
    logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n ≤
      (logarithmicReciprocal b ((n / d : ℕ) : ℝ) ^ 2 * squarefreeHarmonicWeight W (n / d)) / (d.totient : ℝ) := by
  by_cases hqual : Squarefree n ∧ n.Coprime W
  · have hquot : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hq1 : (1 : ℝ) ≤ (n / d : ℕ) := by exact_mod_cast hquot
    have hrecip : logarithmicReciprocal b n ≤ logarithmicReciprocal b ((n / d : ℕ) : ℝ) :=
      logarithmicReciprocal_antitone hb hq1 hn1 (by exact_mod_cast Nat.div_le_self n d)
    have hsq := pow_le_pow_left₀ (logarithmicReciprocal_nonneg hb hn1) hrecip 2
    have hh := mul_le_mul_of_nonneg_right hsq
      (div_nonneg (squarefreeHarmonicWeight_nonneg W (n / d)) (Nat.cast_nonneg d.totient))
    rw [squarefreeHarmonicWeight_divisor hdn hqual.1 hqual.2]
    exact hh.trans_eq (by ring)
  · have hzero : squarefreeHarmonicWeight W n = 0 := by
      rw [squarefreeHarmonicWeight, if_neg hqual]
    rw [hzero, mul_zero]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (squarefreeHarmonicWeight_nonneg W (n / d)))
      (Nat.cast_nonneg _)

theorem divisor_quotient_injective_on (d R : ℕ) :
    Set.InjOn (fun n => n / d) ((Finset.Icc 1 R).filter (fun n => d ∣ n)) := by
    intro n hn m hm heq
    have hnd := (Finset.mem_filter.mp hn).2
    have hmd := (Finset.mem_filter.mp hm).2
    change n / d = m / d at heq
    calc
      n = (n / d) * d := (Nat.div_mul_cancel hnd).symm
      _ = (m / d) * d := by rw [heq]
      _ = m := Nat.div_mul_cancel hmd
theorem divisor_quotient_image_subset {d : ℕ} (hd : 0 < d) (R : ℕ) :
    ((Finset.Icc 1 R).filter (fun n => d ∣ n)).image (fun n => n / d) ⊆ Finset.Icc 1 R := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hnS := Finset.mem_filter.mp hn
    have hnb := Finset.mem_Icc.mp hnS.1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnb.1 hnS.2) hd,
      (Nat.div_le_self n d).trans hnb.2⟩

theorem rationalSquare_divisor_mass_le (W R : ℕ) {b : ℝ} (hb : 0 ≤ b)
    {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 R).filter (fun n => d ∣ n),
      logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) ≤
      rationalSquareMass W b R / (d.totient : ℝ) := by
  let S := (Finset.Icc 1 R).filter (fun n => d ∣ n)
  let f : ℕ → ℝ := fun n => logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n
  have hinj := divisor_quotient_injective_on d R
  have hsub := divisor_quotient_image_subset hd R
  change (∑ n ∈ S, f n) ≤ (∑ n ∈ Finset.Icc 1 R, f n) / (d.totient : ℝ)
  calc
    _ ≤ ∑ n ∈ S, f (n / d) / (d.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS := Finset.mem_filter.mp hn
      exact rationalSquare_divisor_pointwise W hb (Finset.mem_Icc.mp hnS.1).1 hd hnS.2
    _ = (∑ n ∈ S.image (fun n => n / d), f n) / (d.totient : ℝ) := by
      rw [Finset.sum_image hinj, Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
        mul_nonneg (sq_nonneg _) (squarefreeHarmonicWeight_nonneg W n))

end Erdos4.FGKMT
