import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentBoxes

open scoped BigOperators

noncomputable section

namespace Erdos1058.BugeaudLaurent

theorem large_interpolation_determinant_of_nonsingular
    {K L R S p q a b c t T : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hR : 0 < R) (hS : 0 < S)
    (hp : 1 < p) (hq : 0 < q)
    (hpodd : Odd p) (hqodd : Odd q)
    (f₀ : Fin K × Fin L → Fin R × Fin S)
    (hf₀ : Function.Injective f₀)
    (hdet₀ : (Matrix.of (fun row col =>
      ((b * (f₀ col).1.val + a * (f₀ col).2.val : ℕ).choose row.1.val : ℚ) *
        (((p : ℚ) ^ (2 * (f₀ col).1.val) /
          (q : ℚ) ^ (2 * (f₀ col).2.val)) ^ row.2.val))).det ≠ 0)
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    ∃ f : Fin (K * L) → Fin R × Fin S,
      Function.Injective f ∧
      (clearedInterpolationMatrix p q a b f).det ≠ 0 ∧
      (2 : ℤ) ^
          (3 * ((∑ i : Fin (K * L), i.val) -
            L * ∑ k : Fin K, k.val)) ∣
        (clearedInterpolationMatrix p q a b f).det := by
  classical
  let e : Fin K × Fin L ≃ Fin (K * L) := finProdFinEquiv
  let f : Fin (K * L) → Fin R × Fin S := fun j => f₀ (e.symm j)
  have hf : Function.Injective f := hf₀.comp e.symm.injective
  let A := clearedInterpolationMatrix p q a b f
  let B := modelInterpolationMatrix p q a b c f
  have hmod : A.map (Int.castRingHom (ZMod (2 ^ T))) =
      B.map (Int.castRingHom (ZMod (2 ^ T))) := by
    ext i j
    have hfactor := zmod_cleared_exponential_entry hpodd hqodd hbc hrel
      (r := (f₀ (finProdFinEquiv.symm j)).1.val)
      (s := (f₀ (finProdFinEquiv.symm j)).2.val)
      (l := (finProdFinEquiv.symm i).2.val) (S := S)
      (f₀ (finProdFinEquiv.symm j)).2.isLt
    dsimp only [A, B, clearedInterpolationMatrix, modelInterpolationMatrix,
      Matrix.map_apply, e, f]
    simp only [binomialExponential]
    simp only [map_mul, map_pow, map_natCast] at ⊢
    push_cast at hfactor
    let coefficient : ZMod (2 ^ T) :=
      ((b * (f₀ (finProdFinEquiv.symm j)).1.val +
        a * (f₀ (finProdFinEquiv.symm j)).2.val).choose
          (finProdFinEquiv.symm i).1.val : ℕ)
    let actual : ZMod (2 ^ T) :=
      (p : ZMod (2 ^ T)) ^
          (2 * (f₀ (finProdFinEquiv.symm j)).1.val *
            (finProdFinEquiv.symm i).2.val) *
        (q : ZMod (2 ^ T)) ^
          (2 * (S - (f₀ (finProdFinEquiv.symm j)).2.val) *
            (finProdFinEquiv.symm i).2.val)
    let model : ZMod (2 ^ T) :=
      (q : ZMod (2 ^ T)) ^ (2 * S * (finProdFinEquiv.symm i).2.val) *
        ((p : ZMod (2 ^ T)) ^ (2 * c * (finProdFinEquiv.symm i).2.val)) ^
          (b * (f₀ (finProdFinEquiv.symm j)).1.val +
            a * (f₀ (finProdFinEquiv.symm j)).2.val)
    change actual = model at hfactor
    conv_lhs => rw [mul_assoc]
    change coefficient * actual = _
    rw [hfactor]
    dsimp only [coefficient, model]
    ring
  obtain ⟨H, hAB⟩ := exists_integer_perturbation_of_zmod_eq A B hmod
  let rowDegree : Fin (K * L) → ℕ := fun i => (e.symm i).1.val
  let d : Fin (K * L) → ℤ := fun i =>
    (p : ℤ) ^ (2 * c * (e.symm i).2.val)
  let scale : Fin (K * L) → ℤ := fun i =>
    (q : ℤ) ^ (2 * S * (e.symm i).2.val)
  let M := b * R + a * S + 1
  let x : Fin (K * L) → Fin M := fun j =>
    ⟨b * (f j).1.val + a * (f j).2.val, by
      have hr := (f j).1.isLt
      have hs := (f j).2.isLt
      have hr' := Nat.mul_le_mul_left b hr.le
      have hs' := Nat.mul_le_mul_left a hs.le
      dsimp only [M]
      omega⟩
  have hdegree : (∑ i : Fin (K * L), rowDegree i) =
      L * ∑ k : Fin K, k.val := by
    calc
      (∑ i : Fin (K * L), rowDegree i) =
          ∑ row : Fin K × Fin L, row.1.val := by
            simpa only [rowDegree, e] using
              e.symm.sum_comp (fun row : Fin K × Fin L => row.1.val)
      _ = L * ∑ k : Fin K, k.val := by
        rw [Fintype.sum_prod_type]
        simp [Finset.mul_sum]
  have hd : ∀ i, (2 : ℤ) ^ 3 ∣ d i - 1 := by
    intro i
    have hi := eight_dvd_odd_even_power_sub_one
      (e := c * (e.symm i).2.val) hpodd
    norm_num only [pow_succ, pow_zero, mul_one] at hi ⊢
    simpa only [d, show 2 * c * (e.symm i).2.val =
        2 * (c * (e.symm i).2.val) by ring, Nat.cast_pow] using hi
  have hbudget := interpolation_budget hL hT rowDegree hdegree
  have hB : B = Matrix.of (fun r j =>
      scale r * binomialExponential (d r) (rowDegree r) (x j)) := by
    ext i j
    rfl
  have hdiv : (2 : ℤ) ^
        (3 * ((∑ i : Fin (K * L), i.val) -
          L * ∑ k : Fin K, k.val)) ∣ A.det := by
    have hpert := two_pow_dvd_det_perturbed_mixed_scaled
      rowDegree d scale hd x H hbudget
    rw [hdegree] at hpert
    rw [hAB, hB]
    exact hpert
  have hAmap : A.map (Int.castRingHom ℚ) = Matrix.of (fun i j =>
      (q : ℚ) ^ (2 * S * (e.symm i).2.val) *
        (Matrix.of (fun row col =>
          ((b * (f₀ col).1.val + a * (f₀ col).2.val : ℕ).choose row.1.val : ℚ) *
            (((p : ℚ) ^ (2 * (f₀ col).1.val) /
              (q : ℚ) ^ (2 * (f₀ col).2.val)) ^ row.2.val))).submatrix
                e.symm e.symm i j) := by
    ext i j
    have hclear := cleared_interpolation_entry
      (p := p) (q := q) (r := (f₀ (finProdFinEquiv.symm j)).1.val)
      (s := (f₀ (finProdFinEquiv.symm j)).2.val)
      (l := (finProdFinEquiv.symm i).2.val) (S := S) hq
      (f₀ (finProdFinEquiv.symm j)).2.isLt
    dsimp only [A, clearedInterpolationMatrix, Matrix.map_apply,
      Matrix.of_apply, Matrix.submatrix_apply, e, f]
    simp only [map_mul, map_pow, map_natCast] at ⊢
    push_cast at hclear
    let coefficient : ℚ :=
      ((b * (f₀ (finProdFinEquiv.symm j)).1.val +
        a * (f₀ (finProdFinEquiv.symm j)).2.val).choose
          (finProdFinEquiv.symm i).1.val : ℕ)
    let actual : ℚ :=
      (p : ℚ) ^ (2 * (f₀ (finProdFinEquiv.symm j)).1.val *
          (finProdFinEquiv.symm i).2.val) *
        (q : ℚ) ^ (2 * (S - (f₀ (finProdFinEquiv.symm j)).2.val) *
          (finProdFinEquiv.symm i).2.val)
    let model : ℚ :=
      (q : ℚ) ^ (2 * S * (finProdFinEquiv.symm i).2.val) *
        (((p : ℚ) ^ (2 * (f₀ (finProdFinEquiv.symm j)).1.val) /
          (q : ℚ) ^ (2 * (f₀ (finProdFinEquiv.symm j)).2.val)) ^
            (finProdFinEquiv.symm i).2.val)
    change model = actual at hclear
    conv_lhs => rw [mul_assoc]
    change coefficient * actual = _
    rw [← hclear]
    dsimp only [coefficient, model]
    ring
  have hdetReindexed :
      ((Matrix.of (fun row col =>
        ((b * (f₀ col).1.val + a * (f₀ col).2.val : ℕ).choose row.1.val : ℚ) *
          (((p : ℚ) ^ (2 * (f₀ col).1.val) /
            (q : ℚ) ^ (2 * (f₀ col).2.val)) ^ row.2.val))).submatrix
              e.symm e.symm).det ≠ 0 := by
    simpa only [Matrix.det_submatrix_equiv_self] using hdet₀
  have hdetMap : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [hAmap, Matrix.det_mul_column]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ =>
      pow_ne_zero _ (by exact_mod_cast (show q ≠ 0 by omega)))) hdetReindexed
  have hAne : A.det ≠ 0 := by
    intro hzero
    apply hdetMap
    have hm := RingHom.map_det (Int.castRingHom ℚ) A
    rw [hzero, map_zero] at hm
    exact hm.symm
  exact ⟨f, hf, hAne, hdiv⟩

theorem exists_large_interpolation_determinant_boxes
    {K L R₁ R₂ S₁ S₂ p q a b c t T : ℕ}
    (hK : 0 < K) (hL : 0 < L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    ∃ f : Fin (K * L) → Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1),
      Function.Injective f ∧
      (clearedInterpolationMatrix p q a b f).det ≠ 0 ∧
      (2 : ℤ) ^ (3 * ((∑ i : Fin (K * L), i.val) -
        L * ∑ k : Fin K, k.val)) ∣
          (clearedInterpolationMatrix p q a b f).det := by
  obtain ⟨f₀, hf₀, hdet₀⟩ := exists_nonsingular_interpolation_boxes
    hK hL hR₁ hR₂ hS₁ hS₂ hp hq hpq hb hsize₁ hsize₂ hinj
  exact large_interpolation_determinant_of_nonsingular hK hL
    (by omega : 0 < R₁ + R₂ - 1) (by omega : 0 < S₁ + S₂ - 1)
    hp.one_lt hq.pos hpodd hqodd
    f₀ hf₀ hdet₀ hT hbc hrel

end Erdos1058.BugeaudLaurent
