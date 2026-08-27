import ErdosProblems.Erdos587.HooleyResidueProgression

/-! # The unique linear residue and its exact gcd factor -/

open scoped BigOperators

namespace Erdos587

lemma delta_gcd_linear_residue {a t : ℤ} {q c : ℕ} (hcop : IsCoprime a (q : ℤ))
    (hres : (q : ℤ) ∣ a * c - t) : Nat.gcd c q = Nat.gcd q t.natAbs := by
  apply Nat.dvd_antisymm
  · have hdq : ((Nat.gcd c q : ℕ) : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.gcd_dvd_right c q
    have hdc : ((Nat.gcd c q : ℕ) : ℤ) ∣ (c : ℤ) := by exact_mod_cast Nat.gcd_dvd_left c q
    have hdt : ((Nat.gcd c q : ℕ) : ℤ) ∣ t := by
      have h := dvd_sub (dvd_mul_of_dvd_right hdc a) (hdq.trans hres)
      simpa only [sub_sub_cancel] using h
    exact Nat.dvd_gcd (Nat.gcd_dvd_right c q) (Int.natCast_dvd.mp hdt)
  · let d := Nat.gcd q t.natAbs
    have hdq : (d : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.gcd_dvd_left q t.natAbs
    have hdt : (d : ℤ) ∣ t := Int.natCast_dvd.mpr (Nat.gcd_dvd_right q t.natAbs)
    have hdac : (d : ℤ) ∣ a * c := by
      have h := dvd_add (hdq.trans hres) hdt
      simpa only [sub_add_cancel] using h
    have hcopd : IsCoprime (d : ℤ) a := hcop.symm.of_isCoprime_of_dvd_left hdq
    have hdc : d ∣ c := by exact_mod_cast hcopd.dvd_of_dvd_mul_left hdac
    exact Nat.dvd_gcd hdc (Nat.gcd_dvd_left q t.natAbs)

theorem exists_delta_linear_residue {a t : ℤ} {q : ℕ} (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ)) :
    ∃ c : ℕ, c < q ∧ (∀ n : ℕ, (q : ℤ) ∣ a * n - t ↔ n % q = c) ∧
      Nat.gcd c q = Nat.gcd q t.natAbs := by
  let : NeZero q := ⟨hq.ne'⟩
  have ha : IsUnit (a : ZMod q) := by
    have h := hcop.map (Int.castRingHom (ZMod q))
    apply isCoprime_zero_right.mp
    simpa using h
  obtain ⟨u, hu⟩ := ha
  let v : ZMod q := (u⁻¹ : (ZMod q)ˣ) * (t : ZMod q)
  let c : ℕ := v.val
  have hc : c < q := ZMod.val_lt v
  have hcCast : (c : ZMod q) = v := ZMod.natCast_zmod_val v
  have hequiv (n : ℕ) : (q : ℤ) ∣ a * n - t ↔ n % q = c := by
    have hcast : (q : ℤ) ∣ a * n - t ↔ (a : ZMod q) * (n : ZMod q) = (t : ZMod q) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_eq_zero]
    rw [hcast, ← hu]
    have hunit : (u : ZMod q) * (n : ZMod q) = (t : ZMod q) ↔ (n : ZMod q) = v := by
      constructor
      · intro h
        dsimp only [v]
        rw [← h]
        simp only [← mul_assoc, Units.inv_mul, one_mul]
      · intro h
        rw [h]
        dsimp only [v]
        simp only [← mul_assoc, Units.mul_inv, one_mul]
    rw [hunit]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast] using hv
    · intro h
      have hval : (n : ZMod q).val = (c : ZMod q).val := by
        rw [ZMod.val_natCast, ZMod.val_natCast_of_lt hc, h]
      exact (ZMod.val_injective q hval).trans hcCast
  refine ⟨c, hc, hequiv, ?_⟩
  exact delta_gcd_linear_residue hcop ((hequiv c).mpr (Nat.mod_eq_of_lt hc))

open Classical in
theorem exists_delta_linear_residue_mean_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, 0 < q → 16 ≤ X / q → X ≤ (X / q) ^ r →
      ∀ a t : ℤ, IsCoprime a (q : ℤ) →
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
        (hooleyDelta n : ℝ)) ≤
          C * (Nat.gcd q t.natAbs).divisors.card * ((X : ℝ) / q) *
            (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_residue_mean_bound r hr
  refine ⟨C, hC, ?_⟩
  intro X q hq hlength hsize a t hcop
  obtain ⟨c, hc, hequiv, hgcd⟩ := exists_delta_linear_residue (t := t) hq hcop
  have h := hmean X q c hq hc hlength hsize
  simp_rw [hequiv]
  rwa [hgcd] at h

end Erdos587
