import ErdosProblems.Erdos336.DensePowerSaturation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma exactPowerFinset_add_wide (D : Set G) (k l : ℕ) :
    exactPowerFinset D k + exactPowerFinset D l =
      exactPowerFinset D (k + l) := by
  classical
  apply Finset.coe_injective
  rw [Finset.coe_add]
  simp only [coe_exactPowerFinset]
  exact exactPower_add D k l

private lemma three_pow_mul_le_two_pow_of_growth_wide
    (f : ℕ → ℕ) (m : ℕ)
    (hgrowth : ∀ i : ℕ, i < m → 3 * f i ≤ 2 * f (i + 1)) :
    3 ^ m * f 0 ≤ 2 ^ m * f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ih' : 3 ^ m * f 0 ≤ 2 ^ m * f m :=
        ih (fun i hi => hgrowth i (by omega))
      have hm := hgrowth m (by omega)
      calc
        3 ^ (m + 1) * f 0 = 3 * (3 ^ m * f 0) := by ring
        _ ≤ 3 * (2 ^ m * f m) := Nat.mul_le_mul_left 3 ih'
        _ ≤ 2 ^ m * (2 * f (m + 1)) := by
          nlinarith [Nat.zero_le (2 ^ m)]
        _ = 2 ^ (m + 1) * f (m + 1) := by ring

set_option exponentiation.threshold 300 in
lemma wide_dense_saturation_numerical :
    2 ^ 280 * (30000000 * Nat.factorial 36) < 3 ^ 280 := by
  norm_num [Nat.factorial]

/-- A primitive exact power of density greater than the fixed wide-density threshold saturates after
at most `2^280` copies.  This is the uniform endgame for the dense alternative
in the cyclic small-doubling trichotomy. -/
theorem wide_dense_highPower_saturates
    {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    {t : ℕ} (ht : 0 < t)
    (hdense : Fintype.card G < (30000000 * Nat.factorial 36) * (ExactPower D t).ncard) :
    ∃ u : ℕ, 0 < u ∧ u ≤ 2 ^ 280 ∧
      ExactPower D (u * t) = Set.univ := by
  let f : ℕ → ℕ := fun i => (ExactPower D (2 ^ i * t)).ncard
  have htop : ∀ i, f i ≤ Fintype.card G := by
    intro i
    dsimp [f]
    calc
      (ExactPower D (2 ^ i * t)).ncard ≤ (Set.univ : Set G).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
      _ = Fintype.card G := by simp
  have fpos : 0 < f 0 := by
    rw [Set.ncard_pos]
    refine ⟨0, ?_⟩
    apply exactPower_mono_of_zero hzero (show 0 ≤ 2 ^ 0 * t by omega)
    exact ⟨[], rfl, by simp, by simp⟩
  by_contra hnot
  push_neg at hnot
  have hnolow : ∀ i : ℕ, i < 280 →
      3 * f i ≤ 2 * f (i + 1) := by
    intro i hi
    by_contra hbad
    push_neg at hbad
    let A : Finset G := exactPowerFinset D (2 ^ i * t)
    have hAadd : A + A =
        exactPowerFinset D (2 ^ (i + 1) * t) := by
      dsimp [A]
      rw [exactPowerFinset_add_wide]
      congr 2
      ring
    have hzeroA : 0 ∈ A := by
      dsimp [A]
      rw [mem_exactPowerFinset]
      apply exactPower_mono_of_zero hzero (show 0 ≤ 2 ^ i * t by omega)
      exact ⟨[], rfl, by simp, by simp⟩
    have hgenA : AddSubgroup.closure (A : Set G) = ⊤ := by
      dsimp [A]
      rw [coe_exactPowerFinset]
      exact closure_exactPower_eq_top hzero hexact (by positivity)
    have hdblA : 2 * (A + A).card < 3 * A.card := by
      rw [hAadd]
      dsimp [A]
      simp only [card_exactPowerFinset]
      simpa [f] using hbad
    have hfullA := add_self_eq_univ_of_three_mul_lt_two_mul
      A hzeroA hgenA hdblA
    have hfull : ExactPower D (2 ^ (i + 1) * t) = Set.univ := by
      rw [hAadd] at hfullA
      ext x
      have hx := Finset.ext_iff.mp hfullA x
      simpa using hx
    have hu : 2 ^ (i + 1) ≤ 2 ^ 280 :=
      pow_le_pow_right₀ (by omega) (by omega)
    exact hnot (2 ^ (i + 1)) (by positivity) hu hfull
  have hgrow := three_pow_mul_le_two_pow_of_growth_wide f 280 hnolow
  have hden : Fintype.card G < (30000000 * Nat.factorial 36) * f 0 := by simpa [f] using hdense
  have hbad : 3 ^ 280 * f 0 < 2 ^ 280 * (30000000 * Nat.factorial 36) * f 0 := by
    calc
      3 ^ 280 * f 0 ≤ 2 ^ 280 * f 280 := hgrow
      _ ≤ 2 ^ 280 * Fintype.card G := Nat.mul_le_mul_left _ (htop 280)
      _ < 2 ^ 280 * ((30000000 * Nat.factorial 36) * f 0) :=
        (Nat.mul_lt_mul_left (by positivity)).2 hden
      _ = 2 ^ 280 * (30000000 * Nat.factorial 36) * f 0 := by ring
  have hnum := wide_dense_saturation_numerical
  have hnumMul := Nat.mul_lt_mul_of_pos_right hnum fpos
  have hreverse : 2 ^ 280 * (30000000 * Nat.factorial 36) * f 0 <
      3 ^ 280 * f 0 := by
    simpa [mul_assoc] using hnumMul
  exact (Nat.lt_asymm hbad hreverse)


end Erdos336
