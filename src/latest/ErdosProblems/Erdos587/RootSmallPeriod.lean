import ErdosProblems.Erdos587.RootCounts
import ErdosProblems.Erdos587.CenteredQuadratic

/-!
# The small-radical density case

One unit square in each complete radical period gives a uniform lower
bound for the finitely many small radicals excluded by the analytic threshold.
-/

open scoped BigOperators

namespace Erdos587

lemma unitSquareExpansionValue_nonneg (q n : ℕ) : 0 ≤ unitSquareExpansionValue q n := by
  classical
  unfold unitSquareExpansionValue
  split_ifs <;> positivity

lemma unitSquareExpansionValue_eq_of_modEq {q m n : ℕ} (h : m ≡ n [MOD q]) :
    unitSquareExpansionValue q m = unitSquareExpansionValue q n := by
  classical
  have hcop : m.Coprime q ↔ n.Coprime q := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, h.gcd_eq]
  have hcast := (ZMod.natCast_eq_natCast_iff m n q).mpr h
  simp only [unitSquareExpansionValue, hcop, hcast]

lemma one_le_unitSquareExpansionValue_one (q : ℕ) : 1 ≤ unitSquareExpansionValue q 1 := by
  classical
  have hcop : (1 : ℕ).Coprime q := by simp
  have hsq : IsSquare ((1 : ℕ) : ZMod q) := ⟨1, by simp⟩
  rw [unitSquareExpansionValue, if_pos ⟨hcop, hsq⟩]
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

lemma unitSquareExpansionValue_affine_periodic (q D R : ℕ) :
    ∀ i, unitSquareExpansionValue q (D + R * (i + q)) =
      unitSquareExpansionValue q (D + R * i) := by
  intro i
  apply unitSquareExpansionValue_eq_of_modEq
  change (D + R * (i + q)) % q = (D + R * i) % q
  simp only [Nat.mul_add, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod,
    Nat.add_zero, Nat.mod_mod]

lemma exists_affine_unit_one_residue {q D R : ℕ} (hq : 0 < q) (hR : R.Coprime q) :
    ∃ i < q, D + R * i ≡ 1 [MOD q] := by
  let : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime R hR
  let z : ZMod q := (u⁻¹ : (ZMod q)ˣ) * (1 - (D : ZMod q))
  have hRcast : (R : ZMod q) = (u : ZMod q) := (ZMod.coe_unitOfCoprime R hR).symm
  have hz : (D : ZMod q) + (R : ZMod q) * z = 1 := by
    dsimp only [z]
    rw [hRcast, ← mul_assoc, ← Units.val_mul]
    simp
  have hcast : ((D + R * z.val : ℕ) : ZMod q) = (1 : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz
  exact ⟨z.val, ZMod.val_lt z, (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (by simpa only [Nat.cast_one] using hcast)⟩

lemma one_le_unitSquareExpansion_affine_period_sum {q D R : ℕ}
    (hq : 0 < q) (hR : R.Coprime q) :
    1 ≤ ∑ i ∈ Finset.range q, unitSquareExpansionValue q (D + R * i) := by
  obtain ⟨i, hi, hmod⟩ := exists_affine_unit_one_residue (D := D) hq hR
  calc
    1 ≤ unitSquareExpansionValue q 1 := one_le_unitSquareExpansionValue_one q
    _ = unitSquareExpansionValue q (D + R * i) :=
      (unitSquareExpansionValue_eq_of_modEq hmod).symm
    _ ≤ _ := Finset.single_le_sum (s := Finset.range q)
      (f := fun j => unitSquareExpansionValue q (D + R * j))
      (fun j hj => unitSquareExpansionValue_nonneg q _) (Finset.mem_range.mpr hi)

lemma periodic_real_sum_lower (f : ℕ → ℝ) (q H : ℕ) (hq : 0 < q) (hH : 2 * q ≤ H)
    (hf : ∀ i, 0 ≤ f i) (hper : ∀ i, f (i + q) = f i)
    (hmain : 1 ≤ ∑ i ∈ Finset.range q, f i) :
    (H : ℝ) / (2 * q) ≤ ∑ i ∈ Finset.range H, f i := by
  have hperC : ∀ i, (f (i + q) : ℂ) = (f i : ℂ) := fun i => congrArg Complex.ofReal (hper i)
  have hC := sum_range_periodic_decomposition (fun i => (f i : ℂ)) q H hperC
  have hdec : (∑ i ∈ Finset.range H, f i) =
      ((H / q : ℕ) : ℝ) * (∑ i ∈ Finset.range q, f i) +
        ∑ i ∈ Finset.range (H % q), f i := by exact_mod_cast hC
  have hdiv : 0 < H / q := Nat.div_pos (by omega) hq
  have hrem := Nat.mod_lt H hq
  have hdecomp := Nat.mod_add_div H q
  have hqdiv : q ≤ q * (H / q) := by
    calc
      q = q * 1 := (mul_one q).symm
      _ ≤ q * (H / q) := Nat.mul_le_mul_left q hdiv
  have hhalf : H ≤ 2 * q * (H / q) := by nlinarith
  have hhalfR : (H : ℝ) / (2 * q) ≤ ((H / q : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (H : ℝ) ≤ 2 * q * ((H / q : ℕ) : ℝ) := by exact_mod_cast hhalf
    nlinarith
  calc
    _ ≤ ((H / q : ℕ) : ℝ) := hhalfR
    _ ≤ ((H / q : ℕ) : ℝ) * (∑ i ∈ Finset.range q, f i) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hmain
    _ ≤ ((H / q : ℕ) : ℝ) * (∑ i ∈ Finset.range q, f i) +
        ∑ i ∈ Finset.range (H % q), f i :=
      le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi => hf i))
    _ = _ := hdec.symm

lemma unitSquareExpansion_affine_sum_lower_of_two_periods {q D R H : ℕ}
    (hq : 0 < q) (hR : R.Coprime q) (hH : 2 * q ≤ H) :
    (H : ℝ) / (2 * q) ≤
      ∑ i ∈ Finset.range H, unitSquareExpansionValue q (D + R * i) := by
  exact periodic_real_sum_lower _ q H hq hH
    (fun i => unitSquareExpansionValue_nonneg q _)
    (unitSquareExpansionValue_affine_periodic q D R)
    (one_le_unitSquareExpansion_affine_period_sum hq hR)

lemma odd_root_sum_lower_of_two_radical_periods {q D R H : ℕ} (hq : 0 < q)
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2)
    (hR : R.Coprime (primeSetModulus q.primeFactors))
    (hH : 2 * primeSetModulus q.primeFactors ≤ H) :
    (H : ℝ) / (2 * primeSetModulus q.primeFactors) ≤
      ∑ i ∈ Finset.range H, (squareRootCount q (D + R * i) : ℝ) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hrad : 0 < primeSetModulus q.primeFactors :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  apply (unitSquareExpansion_affine_sum_lower_of_two_periods (D := D) hrad hR hH).trans
  exact Finset.sum_le_sum (fun i hi => unitSquareExpansionValue_le_squareRootCount_odd hodd _)

end Erdos587
