import ErdosProblems.Erdos321.ModularFiber

namespace Erdos321

/-- After clearing denominators by `t!`, this is the integer numerator of a
signed reciprocal difference. -/
def factorialNumerator (t : ℕ) (U V : Finset ℕ) : ℤ :=
  (∑ b ∈ U, (t.factorial / b : ℕ)) - ∑ b ∈ V, (t.factorial / b : ℕ)

private lemma inv_eq_weight_div_factorial {t b : ℕ} (hbpos : 0 < b) (hbt : b ≤ t) :
    ((b : ℚ)⁻¹) = ((t.factorial / b : ℕ) : ℚ) / (t.factorial : ℚ) := by
  have hdvd : b ∣ t.factorial := Nat.dvd_factorial hbpos hbt
  rw [Nat.cast_div hdvd (by exact_mod_cast (ne_of_gt hbpos) : (b : ℚ) ≠ 0)]
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hbpos)
  have hfacq : (t.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- Exact denominator-clearing identity for two reciprocal subset sums. -/
theorem reciprocalSubsetSum_sub_eq_factorialNumerator_div
    {t : ℕ} {U V : Finset ℕ}
    (hU : ∀ b ∈ U, 0 < b ∧ b ≤ t) (hV : ∀ b ∈ V, 0 < b ∧ b ≤ t) :
    reciprocalSubsetSum U - reciprocalSubsetSum V =
      (factorialNumerator t U V : ℚ) / (t.factorial : ℚ) := by
  have hSU : reciprocalSubsetSum U =
      ((∑ b ∈ U, (t.factorial / b : ℕ)) : ℚ) / (t.factorial : ℚ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b hb
    exact inv_eq_weight_div_factorial (hU b hb).1 (hU b hb).2
  have hSV : reciprocalSubsetSum V =
      ((∑ b ∈ V, (t.factorial / b : ℕ)) : ℚ) / (t.factorial : ℚ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b hb
    exact inv_eq_weight_div_factorial (hV b hb).1 (hV b hb).2
  rw [hSU, hSV, factorialNumerator, Int.cast_sub, Int.cast_natCast,
    Int.cast_natCast]
  push_cast
  ring

/-- Distinct subsets of a valid set in `{1,…,t}` have a nonzero cleared
integer numerator. -/
theorem factorialNumerator_ne_zero_of_valid
    {t : ℕ} {B U V : Finset ℕ} (hBsub : B ⊆ Finset.Icc 1 t)
    (hB : Valid B) (hU : U ∈ B.powerset) (hV : V ∈ B.powerset)
    (hUV : U ≠ V) : factorialNumerator t U V ≠ 0 := by
  have hUrange : ∀ b ∈ U, 0 < b ∧ b ≤ t := by
    intro b hb
    exact Finset.mem_Icc.mp (hBsub (Finset.mem_powerset.mp hU hb))
  have hVrange : ∀ b ∈ V, 0 < b ∧ b ≤ t := by
    intro b hb
    exact Finset.mem_Icc.mp (hBsub (Finset.mem_powerset.mp hV hb))
  have hClear := reciprocalSubsetSum_sub_eq_factorialNumerator_div hUrange hVrange
  intro hZero
  rw [hZero] at hClear
  norm_num at hClear
  exact hUV (hB U hU V hV (sub_eq_zero.mp hClear))

/-- Cancelling a common support leaves the cleared signed numerator unchanged. -/
theorem factorialNumerator_sdiff (t : ℕ) (U V : Finset ℕ) :
    factorialNumerator t (U \ V) (V \ U) = factorialNumerator t U V := by
  have hU := Finset.sum_sdiff (f := fun b : ℕ => (t.factorial / b : ℕ))
    (Finset.inter_subset_left : U ∩ V ⊆ U)
  have hV := Finset.sum_sdiff (f := fun b : ℕ => (t.factorial / b : ℕ))
    (Finset.inter_subset_left : V ∩ U ⊆ V)
  simp only [Finset.sdiff_inter_self_left] at hU hV
  rw [Finset.inter_comm V U] at hV
  simp only [factorialNumerator]
  omega

/-- A disjoint signed numerator supported on `B` has absolute value at most
`|B| * t!`. -/
theorem factorialNumerator_natAbs_le
    {t : ℕ} {B U V : Finset ℕ} (hU : U ⊆ B) (hV : V ⊆ B)
    (hdisjoint : Disjoint U V) :
    (factorialNumerator t U V).natAbs ≤ B.card * t.factorial := by
  let w := fun b : ℕ => t.factorial / b
  have hSumU : (∑ b ∈ U, w b) ≤ U.card * t.factorial := by
    simpa [w, nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul U w t.factorial
        (fun b hb => Nat.div_le_self _ _))
  have hSumV : (∑ b ∈ V, w b) ≤ V.card * t.factorial := by
    simpa [w, nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul V w t.factorial
        (fun b hb => Nat.div_le_self _ _))
  have hCard : U.card + V.card ≤ B.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint]
    exact Finset.card_le_card (Finset.union_subset hU hV)
  have habs := Int.natAbs_sub_le
    (↑(∑ b ∈ U, w b) : ℤ) (↑(∑ b ∈ V, w b) : ℤ)
  simp only [Int.natAbs_natCast] at habs
  change (factorialNumerator t U V).natAbs ≤ _
  simp only [factorialNumerator]
  dsimp [w] at hSumU hSumV habs ⊢
  nlinarith [Nat.mul_le_mul_right t.factorial hCard]

/-- Every prime `p>t` which destroys modular separation of a rationally valid
cofactor set divides the nonzero cleared numerator of some signed relation. -/
theorem bad_prime_dvd_some_factorialNumerator
    {t p : ℕ} {B : Finset ℕ} (hp : p.Prime) (htp : t < p)
    (hBsub : B ⊆ Finset.Icc 1 t) (hB : Valid B)
    (hBad : ¬ ModularlySeparated p B) :
    ∃ U ∈ B.powerset, ∃ V ∈ B.powerset,
      U ≠ V ∧ factorialNumerator t U V ≠ 0 ∧
        (p : ℤ) ∣ factorialNumerator t U V := by
  classical
  simp only [ModularlySeparated] at hBad
  push Not at hBad
  obtain ⟨U, hU, V, hV, hUV, hNormNe⟩ := hBad
  refine ⟨U, hU, V, hV, hUV,
    factorialNumerator_ne_zero_of_valid hBsub hB hU hV hUV, ?_⟩
  have hUrange : ∀ b ∈ U, 0 < b ∧ b ≤ t := by
    intro b hb
    exact Finset.mem_Icc.mp (hBsub (Finset.mem_powerset.mp hU hb))
  have hVrange : ∀ b ∈ V, 0 < b ∧ b ≤ t := by
    intro b hb
    exact Finset.mem_Icc.mp (hBsub (Finset.mem_powerset.mp hV hb))
  have hClear := reciprocalSubsetSum_sub_eq_factorialNumerator_div hUrange hVrange
  letI : Fact p.Prime := ⟨hp⟩
  have hpNotDvdFac : ¬ p ∣ t.factorial := by
    rw [hp.dvd_factorial]
    exact not_le_of_gt htp
  have hNormFac : padicNorm p (t.factorial : ℚ) = 1 :=
    (padicNorm.nat_eq_one_iff t.factorial).mpr hpNotDvdFac
  by_contra hpNotDvdNum
  have hNormNum : padicNorm p (factorialNumerator t U V : ℚ) = 1 :=
    (padicNorm.int_eq_one_iff (factorialNumerator t U V)).mpr hpNotDvdNum
  rw [hClear, padicNorm.div, hNormNum, hNormFac] at hNormNe
  norm_num at hNormNe

end Erdos321
