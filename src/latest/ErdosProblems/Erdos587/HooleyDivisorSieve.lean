import ErdosProblems.Erdos587.HooleyRoughSieve

/-!
# Sifting a fixed-divisor fiber

For primitive affine coefficients, the indices at which a fixed positive
integer divides the affine value lie in one residue class. Dividing out
that integer leaves the original slope. Consequently the sieve loss is
the totient ratio of the original slope, not of the chosen divisor.
-/

namespace Erdos587

lemma delta_affine_divisor_coprime {A B : ℤ} (hAB : IsCoprime A B)
    {d n : ℕ} (hd : (d : ℤ) ∣ A + B * n) : IsCoprime (d : ℤ) B := by
  apply IsCoprime.of_isCoprime_of_dvd_left _ hd
  simpa only [mul_comm] using hAB.add_mul_left_left (n : ℤ)

theorem delta_affine_divisor_fiber_card_le {A B : ℤ} (hB : B ≠ 0)
    (hAB : IsCoprime A B) {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (S : Finset ℕ) (Y : ℕ) (hS : S ⊆ Finset.Icc 1 Y)
    (hdiv : ∀ n ∈ S, (d : ℤ) ∣ A + B * n)
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ Q →
      ¬ (p : ℤ) ∣ (A + B * n) / d) :
    (S.card : ℝ) ≤ (B.natAbs : ℝ) / B.natAbs.totient *
      ((Y / d + 1 : ℕ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) := by
  classical
  have hlog : 0 < Real.log (Q + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q + 1 by omega))
  by_cases hne : S.Nonempty
  · let t₀ : ℕ := S.min' hne
    have ht₀ : t₀ ∈ S := Finset.min'_mem S hne
    have hcop : IsCoprime (d : ℤ) B := delta_affine_divisor_coprime hAB (hdiv t₀ ht₀)
    let i : ℕ → ℕ := fun n => (n - t₀) / d + 1
    let K : Finset ℕ := S.image i
    let C : ℤ := (A + B * t₀) / d - B
    have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    have ht₀le (n : ℕ) (hn : n ∈ S) : t₀ ≤ n := Finset.min'_le S n hn
    have hdsub (n : ℕ) (hn : n ∈ S) : d ∣ n - t₀ := by
      have hexp : B * ((n - t₀ : ℕ) : ℤ) = (A + B * n) - (A + B * t₀) := by
        rw [Nat.cast_sub (ht₀le n hn)]
        ring
      apply Int.natCast_dvd_natCast.mp
      apply hcop.dvd_of_dvd_mul_left
      rw [hexp]
      exact dvd_sub (hdiv n hn) (hdiv t₀ ht₀)
    have hrecover (n : ℕ) (hn : n ∈ S) : t₀ + d * ((n - t₀) / d) = n := by
      rw [Nat.mul_div_cancel' (hdsub n hn)]
      have := ht₀le n hn
      omega
    have hinj : Set.InjOn i (S : Set ℕ) := by
      intro n hn m hm heq
      have hquot : (n - t₀) / d = (m - t₀) / d := by
        dsimp only [i] at heq
        omega
      rw [← hrecover n hn, ← hrecover m hm, hquot]
    have hK : K ⊆ Finset.Ioc 0 (0 + (Y / d + 1)) := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      have hle : (n - t₀) / d ≤ Y / d := Nat.div_le_div_right
        ((Nat.sub_le _ _).trans (Finset.mem_Icc.mp (hS hn)).2)
      exact Finset.mem_Ioc.mpr ⟨Nat.succ_pos _, by
        simpa only [zero_add] using Nat.succ_le_succ hle⟩
    have hquotient (n : ℕ) (hn : n ∈ S) : (A + B * n) / d = C + B * i n := by
      have hr : (t₀ : ℤ) + (d : ℤ) * (((n - t₀) / d : ℕ) : ℤ) = n := by
        exact_mod_cast hrecover n hn
      have hbase := Int.mul_ediv_cancel_of_dvd (hdiv t₀ ht₀)
      apply Int.ediv_eq_of_eq_mul_right hdZ
      dsimp only [C, i]
      simp only [Nat.cast_add, Nat.cast_one]
      linear_combination -B * hr - hbase
    have hroughK : ∀ k ∈ K, ∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ C + B * k := by
      intro k hk p hp hpQ
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      rw [← hquotient n hn]
      exact hrough n hn p hp hpQ
    have hbound := delta_rough_affine_card_le hB hQ K 0 (Y / d + 1) C hK hroughK
    rwa [Finset.card_image_of_injOn hinj] at hbound
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The exact fiber length and the sieve error are both absorbed when
`d * Q² ≤ Y`, uniformly over the chosen divisor. -/
theorem delta_affine_divisor_fiber_card_le_three {A B : ℤ} (hB : B ≠ 0)
    (hAB : IsCoprime A B) {d Q Y : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hcut : d * Q ^ 2 ≤ Y) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Y)
    (hdiv : ∀ n ∈ S, (d : ℤ) ∣ A + B * n)
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ Q →
      ¬ (p : ℤ) ∣ (A + B * n) / d) :
    (S.card : ℝ) ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) *
      (Y : ℝ) / d / Real.log (Q + 1 : ℕ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hQsq : 1 ≤ Q ^ 2 := Nat.one_le_pow 2 Q hQ
  have hdY : d ≤ Y := by nlinarith
  have hfloor : ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self Y d
  have hratio : (1 : ℝ) ≤ (Y : ℝ) / d :=
    (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using (show (d : ℝ) ≤ Y by exact_mod_cast hdY))
  have hcutR : (Q : ℝ) ^ 2 ≤ (Y : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast (show Q ^ 2 * d ≤ Y by nlinarith)
  calc
    _ ≤ (B.natAbs : ℝ) / B.natAbs.totient *
        ((Y / d + 1 : ℕ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) :=
      delta_affine_divisor_fiber_card_le hB hAB hd hQ S Y hS hdiv hrough
    _ ≤ (B.natAbs : ℝ) / B.natAbs.totient * (3 * ((Y : ℝ) / d)) /
        Real.log (Q + 1 : ℕ) := by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        push_cast
        linarith
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q + 1 by omega))
    _ = _ := by ring

end Erdos587
