import ErdosProblems.Erdos587.OddRootDensity

/-!
# The even-modulus density transfer

A single affine class modulo eight admits roots in the full two-primary
factor. Keeping `floor(H/16)` terms in that class costs only a fixed factor.
-/

open scoped BigOperators

namespace Erdos587

lemma half_div_le_nat_div (d H : ℕ) (hd : 0 < d) (hH : d ≤ H) :
    (H : ℝ) / (2 * d) ≤ ((H / d : ℕ) : ℝ) := by
  have hdiv : 0 < H / d := Nat.div_pos hH hd
  have hrem := Nat.mod_lt H hd
  have hdecomp := Nat.mod_add_div H d
  have hddiv : d ≤ d * (H / d) := by
    calc
      d = d * 1 := (mul_one d).symm
      _ ≤ d * (H / d) := Nat.mul_le_mul_left d hdiv
  have hhalf : H ≤ 2 * d * (H / d) := by nlinarith
  apply (div_le_iff₀ (by positivity)).mpr
  have hh : (H : ℝ) ≤ 2 * d * ((H / d : ℕ) : ℝ) := by exact_mod_cast hhalf
  nlinarith

lemma affine_eight_slice_sum_le (f : ℕ → ℝ) (H i₀ : ℕ) (hi₀ : i₀ < 8)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ j ∈ Finset.range (H / 16), f (i₀ + 8 * j)) ≤ ∑ i ∈ Finset.range H, f i := by
  let g : ℕ → ℕ := fun j => i₀ + 8 * j
  have hmap : (Finset.range (H / 16)).image g ⊆ Finset.range H := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hj' := Finset.mem_range.mp hj
    have hmul := Nat.div_mul_le_self H 16
    apply Finset.mem_range.mpr
    dsimp only [g]
    omega
  have hinj : Set.InjOn g (Finset.range (H / 16) : Set ℕ) := by
    intro i hi j hj hij
    dsimp only [g] at hij
    omega
  calc
    _ = ∑ i ∈ (Finset.range (H / 16)).image g, f i := (Finset.sum_image (f := f) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun i hi hnot => hf i)

lemma affine_eight_slice_modEq_one {D R i₀ : ℕ} (h : D + R * i₀ ≡ 1 [MOD 8]) (j : ℕ) :
    D + R * i₀ + (8 * R) * j ≡ 1 [MOD 8] := by
  have hzero : (8 * R) * j ≡ 0 [MOD 8] := by
    change ((8 * R) * j) % 8 = 0 % 8
    simp only [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
  simpa only [Nat.add_zero] using h.add hzero

theorem exists_even_root_density :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (e Q D R H : ℕ), 0 < Q → (∀ p ∈ Q.primeFactors, p ≠ 2) →
        (2 : ℕ).Coprime Q → R.Coprime 8 → R.Coprime (primeSetModulus Q.primeFactors) →
        16 ≤ H → 2 * K ≤ H / 16 →
        (primeSetModulus Q.primeFactors : ℝ) ≤ ((H / 16 : ℕ) : ℝ) ^ 2 →
        (H : ℝ) / (C * (1 + Real.log (primeSetModulus Q.primeFactors)) ^ O) ≤
          ∑ i ∈ Finset.range H, (squareRootCount (2 ^ e * Q) (D + R * i) : ℝ) := by
  obtain ⟨K, hK, C, hC, O, hO, hmean⟩ := exists_uniform_unitSquareExpansion_density
  refine ⟨K, hK, 32 * C, by positivity, O, hO, ?_⟩
  intro e Q D R H hQ hodd h2 hR8 hR hH hL hroot
  obtain ⟨i₀, hi₀, hmod⟩ := exists_affine_unit_one_residue (D := D) (by norm_num : 0 < 8) hR8
  have hradDvd : primeSetModulus Q.primeFactors ∣ Q := Nat.prod_primeFactors_dvd Q
  have h8rad : (8 : ℕ).Coprime (primeSetModulus Q.primeFactors) := by
    have hh := (h2.of_dvd_right hradDvd).pow_left 3
    norm_num at hh
    exact hh
  have hR' : (8 * R).Coprime (primeSetModulus Q.primeFactors) := h8rad.mul_left hR
  have hraw := hmean Q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    hodd (D + R * i₀) (8 * R) (H / 16) hR' hL hroot
  have hcount :
      (∑ j ∈ Finset.range (H / 16),
        unitSquareExpansionValue (primeSetModulus Q.primeFactors) (D + R * i₀ + (8 * R) * j)) ≤
      ∑ i ∈ Finset.range H, (squareRootCount (2 ^ e * Q) (D + R * i) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (H / 16),
          (squareRootCount (2 ^ e * Q) (D + R * i₀ + (8 * R) * j) : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact unitSquareExpansionValue_le_squareRootCount_two_mul_odd e Q _ hQ hodd h2
          (affine_eight_slice_modEq_one hmod j)
      _ = ∑ j ∈ Finset.range (H / 16),
          (squareRootCount (2 ^ e * Q) (D + R * (i₀ + 8 * j)) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun n : ℕ => (squareRootCount (2 ^ e * Q) n : ℝ)) (by ring)
      _ ≤ _ := affine_eight_slice_sum_le
        (fun i : ℕ => (squareRootCount (2 ^ e * Q) (D + R * i) : ℝ))
        H i₀ hi₀ (fun _ => Nat.cast_nonneg _)
  have hradPos : 0 < primeSetModulus Q.primeFactors :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hlog : 0 ≤ Real.log (primeSetModulus Q.primeFactors) :=
    Real.log_nonneg (by exact_mod_cast hradPos)
  have hdenom : 0 < C * (1 + Real.log (primeSetModulus Q.primeFactors)) ^ O := by positivity
  have hhalf : (H : ℝ) / 32 ≤ ((H / 16 : ℕ) : ℝ) := by
    have hh := half_div_le_nat_div 16 H (by norm_num) hH
    norm_num at hh
    exact hh
  calc
    _ = ((H : ℝ) / 32) / (C * (1 + Real.log (primeSetModulus Q.primeFactors)) ^ O) := by ring
    _ ≤ ((H / 16 : ℕ) : ℝ) / (C * (1 + Real.log (primeSetModulus Q.primeFactors)) ^ O) :=
      div_le_div_of_nonneg_right hhalf hdenom.le
    _ ≤ _ := hraw.trans hcount

end Erdos587
