import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentRectangle

open scoped BigOperators

noncomputable section

namespace Erdos1058.BugeaudLaurent

theorem eight_dvd_odd_square_sub_one {z : ℕ} (hz : Odd z) :
    (8 : ℤ) ∣ (z : ℤ) ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hz
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, rfl⟩ := hk
    refine ⟨(2 * j + 1) * j, ?_⟩
    push_cast
    ring
  · obtain ⟨j, hj⟩ := hk
    have hk : k = 2 * j + 1 := by omega
    subst k
    refine ⟨(2 * j + 1) * (j + 1), ?_⟩
    push_cast
    ring

theorem eight_dvd_odd_even_power_sub_one {z e : ℕ} (hz : Odd z) :
    (8 : ℤ) ∣ (z : ℤ) ^ (2 * e) - 1 := by
  have h := eight_dvd_odd_square_sub_one (z := z ^ e) hz.pow
  simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm] using h

lemma cleared_interpolation_entry {p q r s l S : ℕ}
    (hq : 0 < q) (hs : s < S) :
    (q : ℚ) ^ (2 * S * l) *
        (((p : ℚ) ^ (2 * r) / (q : ℚ) ^ (2 * s)) ^ l) =
      ((p ^ (2 * r * l) * q ^ (2 * (S - s) * l) : ℕ) : ℚ) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hS : S = (S - s) + s := by omega
  have hexp : 2 * S * l = 2 * (S - s) * l + 2 * s * l := by
    calc
      2 * S * l = 2 * ((S - s) + s) * l :=
        congrArg (fun z : ℕ => 2 * z * l) hS
      _ = 2 * (S - s) * l + 2 * s * l := by ring
  rw [hexp, pow_add, div_pow]
  rw [show ((p : ℚ) ^ (2 * r)) ^ l = (p : ℚ) ^ (2 * r * l) by
    rw [← pow_mul]]
  rw [show ((q : ℚ) ^ (2 * s)) ^ l = (q : ℚ) ^ (2 * s * l) by
    rw [← pow_mul]]
  push_cast
  field_simp

lemma zmod_cleared_exponential_entry
    {p q a b c t T r s l S : ℕ}
    (hp : Odd p) (hq : Odd q)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T])
    (hs : s < S) :
    (p ^ (2 * r * l) * q ^ (2 * (S - s) * l) : ZMod (2 ^ T)) =
      (q ^ (2 * S * l) *
        (p ^ (2 * c * l)) ^ (b * r + a * s) : ℕ) := by
  have h := zmod_interpolation_identity hp hq hbc hrel
    (r := r * l) (s := s * l) (v := (S - s) * l)
  have hS : S = (S - s) + s := by omega
  have hqexp : 2 * ((S - s) * l + s * l) = 2 * S * l := by
    calc
      2 * ((S - s) * l + s * l) = 2 * (((S - s) + s) * l) := by ring
      _ = 2 * S * l := by
        have hz := congrArg (fun z : ℕ => 2 * z * l) hS.symm
        simpa only [Nat.mul_assoc] using hz
  have hpexp :
      (p ^ (2 * c)) ^ (b * (r * l) + a * (s * l)) =
        (p ^ (2 * c * l)) ^ (b * r + a * s) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  simpa only [show 2 * (r * l) = 2 * r * l by ring,
    show 2 * ((S - s) * l) = 2 * (S - s) * l by ring, hqexp, hpexp]
    using h

lemma exists_integer_perturbation_of_zmod_eq {N T : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℤ)
    (hmod : A.map (Int.castRingHom (ZMod (2 ^ T))) =
      B.map (Int.castRingHom (ZMod (2 ^ T)))) :
    ∃ H : Matrix (Fin N) (Fin N) ℤ,
      A = B + (2 : ℤ) ^ T • H := by
  have hdvd (i j : Fin N) : (2 : ℤ) ^ T ∣ A i j - B i j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (A i j - B i j) (2 ^ T)).mp
    change (Int.castRingHom (ZMod (2 ^ T))) (A i j - B i j) = 0
    rw [map_sub]
    have hij := congrArg (fun M => M i j) hmod
    simpa only [Matrix.map_apply] using sub_eq_zero.mpr hij
  choose H hH using hdvd
  refine ⟨H, ?_⟩
  ext i j
  change A i j = B i j + (2 : ℤ) ^ T * H i j
  have hij := hH i j
  omega

lemma interpolation_budget {K L T : ℕ} (hL : 0 < L) (hT : 3 * (K * L) ≤ T)
    (rowDegree : Fin (K * L) → ℕ)
    (hdegree : ∑ r, rowDegree r = L * ∑ k : Fin K, k.val) :
    ∀ structured : Finset (Fin (K * L)),
      3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) ≤
          T * (K * L - structured.card) ∨
        3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) -
              T * (K * L - structured.card) + 3 * (∑ r, rowDegree r) ≤
            3 * (∑ t : Fin structured.card, t.val) := by
  intro structured
  have hc : structured.card ≤ K * L := by
    simpa using Finset.card_le_univ structured
  have htri (n : ℕ) : 2 * (∑ i : Fin n, i.val) = n * (n - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
    simpa [mul_comm] using Finset.sum_range_id_mul_two n
  have htriMono : (∑ i : Fin structured.card, i.val) ≤
      ∑ i : Fin (K * L), i.val := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) structured.card,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) (K * L)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hc)
    intro i _ _
    omega

  have hdiff0 :
      (∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val ≤
        (K * L) * (K * L - structured.card) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) (K * L),
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) structured.card]
    have hdecomp :=
      Finset.sum_range_add_sum_Ico (fun i : ℕ => i) hc
    have hsubeq :
        (∑ i ∈ Finset.range (K * L), i) -
            ∑ i ∈ Finset.range structured.card, i =
          ∑ i ∈ Finset.Ico structured.card (K * L), i := by
      omega
    rw [hsubeq]
    calc
      ∑ i ∈ Finset.Ico structured.card (K * L), i ≤
          ∑ _i ∈ Finset.Ico structured.card (K * L), K * L := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_Ico.mp hi).2.le
      _ = (K * L - structured.card) * (K * L) := by simp
      _ = (K * L) * (K * L - structured.card) := by ring
  have hdiff :
      3 * ((∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val) ≤
        3 * (K * L) * (K * L - structured.card) := by
    calc
      _ ≤ 3 * ((K * L) * (K * L - structured.card)) :=
        Nat.mul_le_mul_left 3 hdiff0
      _ = _ := by ring
  have hpay :
      3 * ((∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val) ≤
        T * (K * L - structured.card) := by
    calc
      _ ≤ 3 * (K * L) * (K * L - structured.card) := hdiff
      _ ≤ T * (K * L - structured.card) :=
        Nat.mul_le_mul_right _ hT
  have hdegreeBound : (∑ r, rowDegree r) ≤
      ∑ i : Fin (K * L), i.val := by
    have hKle : K ≤ K * L := by
      calc
        K = K * 1 := by simp
        _ ≤ K * L := Nat.mul_le_mul_left K hL
    have hsub : K - 1 ≤ K * L - 1 := Nat.sub_le_sub_right hKle 1
    have hdouble :
        2 * (L * ∑ k : Fin K, k.val) ≤
          2 * (∑ i : Fin (K * L), i.val) := by
      calc
        2 * (L * ∑ k : Fin K, k.val) =
            L * (2 * ∑ k : Fin K, k.val) := by ring
        _ = L * (K * (K - 1)) := by rw [htri K]
        _ = (K * L) * (K - 1) := by ring
        _ ≤ (K * L) * (K * L - 1) := Nat.mul_le_mul_left _ hsub
        _ = 2 * (∑ i : Fin (K * L), i.val) := (htri (K * L)).symm
    rw [hdegree]
    omega
  have hEadd :
      3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) +
          3 * (∑ r, rowDegree r) =
        3 * (∑ i : Fin (K * L), i.val) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hdegreeBound]
  have htriDecomp :
      3 * (∑ i : Fin (K * L), i.val) =
        3 * ((∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val) +
          3 * (∑ i : Fin structured.card, i.val) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel htriMono]
  by_cases hcoeff :
      3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) ≤
        T * (K * L - structured.card)
  · exact Or.inl hcoeff
  · right
    have hmaster :
        3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) +
            3 * (∑ r, rowDegree r) ≤
          T * (K * L - structured.card) +
            3 * (∑ i : Fin structured.card, i.val) := by
      calc
        _ = 3 * (∑ i : Fin (K * L), i.val) := hEadd
        _ = 3 * ((∑ i : Fin (K * L), i.val) -
              ∑ i : Fin structured.card, i.val) +
              3 * (∑ i : Fin structured.card, i.val) := htriDecomp
        _ ≤ T * (K * L - structured.card) +
              3 * (∑ i : Fin structured.card, i.val) :=
          Nat.add_le_add_right hpay _
    omega

def clearedInterpolationMatrix {K L R S : ℕ}
    (p q a b : ℕ) (f : Fin (K * L) → Fin R × Fin S) :
    Matrix (Fin (K * L)) (Fin (K * L)) ℤ := fun i j =>
  let row := finProdFinEquiv.symm i
  let col := f j
  ((b * col.1.val + a * col.2.val).choose row.1.val : ℤ) *
    (p : ℤ) ^ (2 * col.1.val * row.2.val) *
      (q : ℤ) ^ (2 * (S - col.2.val) * row.2.val)

def modelInterpolationMatrix {K L R S : ℕ}
    (p q a b c : ℕ) (f : Fin (K * L) → Fin R × Fin S) :
    Matrix (Fin (K * L)) (Fin (K * L)) ℤ := fun i j =>
  let row := finProdFinEquiv.symm i
  let col := f j
  (q : ℤ) ^ (2 * S * row.2.val) *
    binomialExponential ((p : ℤ) ^ (2 * c * row.2.val)) row.1.val
      (b * col.1.val + a * col.2.val)

theorem exists_large_interpolation_determinant
    {K L R₂ S₂ p q a b c t T : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hR₂ : 0 < R₂) (hS₂ : 0 < S₂)
    (hp : 1 < p) (hq : 0 < q) (hb : 0 < b)
    (hpodd : Odd p) (hqodd : Odd q) (hbodd : Odd b)
    (hsize : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    ∃ f : Fin (K * L) → Fin (R₂ + L - 1) × Fin S₂,
      Function.Injective f ∧
      (clearedInterpolationMatrix p q a b f).det ≠ 0 ∧
      (2 : ℤ) ^
          (3 * ((∑ i : Fin (K * L), i.val) -
            L * ∑ k : Fin K, k.val)) ∣
        (clearedInterpolationMatrix p q a b f).det := by
  classical
  obtain ⟨f₀, hf₀, hdet₀⟩ := exists_nonsingular_interpolation_rectangle
    hK hL hR₂ hS₂ hp hq hb hsize hinj
  let e : Fin K × Fin L ≃ Fin (K * L) := finProdFinEquiv
  let f : Fin (K * L) → Fin (R₂ + L - 1) × Fin S₂ := fun j => f₀ (e.symm j)
  have hf : Function.Injective f := hf₀.comp e.symm.injective
  let A := clearedInterpolationMatrix p q a b f
  let B := modelInterpolationMatrix p q a b c f
  have hmod : A.map (Int.castRingHom (ZMod (2 ^ T))) =
      B.map (Int.castRingHom (ZMod (2 ^ T))) := by
    ext i j
    have hfactor := zmod_cleared_exponential_entry hpodd hqodd hbc hrel
      (r := (f₀ (finProdFinEquiv.symm j)).1.val)
      (s := (f₀ (finProdFinEquiv.symm j)).2.val)
      (l := (finProdFinEquiv.symm i).2.val) (S := S₂)
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
          (2 * (S₂ - (f₀ (finProdFinEquiv.symm j)).2.val) *
            (finProdFinEquiv.symm i).2.val)
    let model : ZMod (2 ^ T) :=
      (q : ZMod (2 ^ T)) ^ (2 * S₂ * (finProdFinEquiv.symm i).2.val) *
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
    (q : ℤ) ^ (2 * S₂ * (e.symm i).2.val)
  let M := b * (R₂ + L - 1) + a * S₂ + 1
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
      (q : ℚ) ^ (2 * S₂ * (e.symm i).2.val) *
        (Matrix.of (fun row col =>
          ((b * (f₀ col).1.val + a * (f₀ col).2.val : ℕ).choose row.1.val : ℚ) *
            (((p : ℚ) ^ (2 * (f₀ col).1.val) /
              (q : ℚ) ^ (2 * (f₀ col).2.val)) ^ row.2.val))).submatrix
                e.symm e.symm i j) := by
    ext i j
    have hclear := cleared_interpolation_entry
      (p := p) (q := q) (r := (f₀ (finProdFinEquiv.symm j)).1.val)
      (s := (f₀ (finProdFinEquiv.symm j)).2.val)
      (l := (finProdFinEquiv.symm i).2.val) (S := S₂) hq
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
        (q : ℚ) ^ (2 * (S₂ - (f₀ (finProdFinEquiv.symm j)).2.val) *
          (finProdFinEquiv.symm i).2.val)
    let model : ℚ :=
      (q : ℚ) ^ (2 * S₂ * (finProdFinEquiv.symm i).2.val) *
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

theorem natAbs_det_le_factorial_mul_pow {N B : ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hentry : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ N.factorial * B ^ N := by
  have hx : ∀ i j, AbsoluteValue.abs (A i j) ≤ (B : ℤ) := by
    intro i j
    have hij := hentry i j
    rw [show AbsoluteValue.abs (A i j) = (A i j).natAbs by
      exact (Int.natCast_natAbs (A i j)).symm]
    exact_mod_cast hij
  have hdet := Matrix.det_le (A := A) (abv := AbsoluteValue.abs)
    (x := (B : ℤ)) hx
  rw [show AbsoluteValue.abs A.det = (A.det.natAbs : ℤ) by
    exact (Int.natCast_natAbs A.det).symm] at hdet
  simp only [Fintype.card_fin, nsmul_eq_mul] at hdet
  exact_mod_cast hdet

theorem clearedInterpolationMatrix_entry_bound
    {K L R S p q a b : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hR : 0 < R) (hS : 0 < S)
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b)
    (f : Fin (K * L) → Fin R × Fin S) (i j : Fin (K * L)) :
    (clearedInterpolationMatrix p q a b f i j).natAbs ≤
      (b * R + a * S) ^ K * p ^ (2 * R * L) * q ^ (2 * S * L) := by
  let row := finProdFinEquiv.symm i
  let col := f j
  let x := b * col.1.val + a * col.2.val
  let X := b * R + a * S
  have hx : x ≤ X := by
    dsimp only [x, X]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left b col.1.isLt.le)
      (Nat.mul_le_mul_left a col.2.isLt.le)
  have hX : 0 < X := by
    dsimp only [X]
    have := Nat.mul_pos hb hR
    omega
  have hchoose : x.choose row.1.val ≤ X ^ K := by
    calc
      x.choose row.1.val ≤ x ^ row.1.val := Nat.choose_le_pow _ _
      _ ≤ X ^ row.1.val := Nat.pow_le_pow_left hx _
      _ ≤ X ^ K := Nat.pow_le_pow_right hX row.1.isLt.le
  have hpexp : 2 * col.1.val * row.2.val ≤ 2 * R * L := by
    nlinarith [col.1.isLt, row.2.isLt]
  have hqexp : 2 * (S - col.2.val) * row.2.val ≤ 2 * S * L := by
    have hs : S - col.2.val ≤ S := Nat.sub_le _ _
    nlinarith [row.2.isLt]
  have hpbound : p ^ (2 * col.1.val * row.2.val) ≤ p ^ (2 * R * L) :=
    Nat.pow_le_pow_right hp hpexp
  have hqbound : q ^ (2 * (S - col.2.val) * row.2.val) ≤ q ^ (2 * S * L) :=
    Nat.pow_le_pow_right hq hqexp
  dsimp only [clearedInterpolationMatrix, row, col, x, X]
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
  exact Nat.mul_le_mul (Nat.mul_le_mul hchoose hpbound) hqbound

theorem interpolation_master_inequality
    {K L R₂ S₂ p q a b c t T : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hR₂ : 0 < R₂) (hS₂ : 0 < S₂)
    (hp : 1 < p) (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hpodd : Odd p) (hqodd : Odd q) (hbodd : Odd b)
    (hsize : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    2 ^ (3 * ((∑ i : Fin (K * L), i.val) -
          L * ∑ k : Fin K, k.val)) ≤
      (K * L).factorial *
        ((b * (R₂ + L - 1) + a * S₂) ^ K *
          p ^ (2 * (R₂ + L - 1) * L) * q ^ (2 * S₂ * L)) ^ (K * L) := by
  obtain ⟨f, _hf, hne, hdiv⟩ := exists_large_interpolation_determinant
    hK hL hR₂ hS₂ hp hq hb hpodd hqodd hbodd hsize hinj hT hbc hrel
  have hlower := two_pow_le_natAbs_of_dvd hne hdiv
  have hupper := natAbs_det_le_factorial_mul_pow
    (clearedInterpolationMatrix p q a b f)
    (fun i j => clearedInterpolationMatrix_entry_bound hK hL
      (by omega : 0 < R₂ + L - 1) hS₂ (by omega) hq hb f i j)
  exact hlower.trans hupper

/- The interpolation-budget proof was moved above the determinant definitions. -/
/-
  have hdiff0 :
      (∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val ≤
        (K * L) * (K * L - structured.card) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) (K * L),
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) structured.card]
    have hdecomp :=
      Finset.sum_range_add_sum_Ico (fun i : ℕ => i) hc
    have hsubeq :
        (∑ i ∈ Finset.range (K * L), i) -
            ∑ i ∈ Finset.range structured.card, i =
          ∑ i ∈ Finset.Ico structured.card (K * L), i := by
      omega
    rw [hsubeq]
    calc
      ∑ i ∈ Finset.Ico structured.card (K * L), i ≤
          ∑ _i ∈ Finset.Ico structured.card (K * L), K * L := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_Ico.mp hi).2.le
      _ = (K * L - structured.card) * (K * L) := by simp
      _ = (K * L) * (K * L - structured.card) := by ring
  have hdiff :
      3 * ((∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val) ≤
        3 * (K * L) * (K * L - structured.card) := by
    calc
      _ ≤ 3 * ((K * L) * (K * L - structured.card)) :=
        Nat.mul_le_mul_left 3 hdiff0
      _ = _ := by ring
  have hpay :
      3 * ((∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val) ≤
        T * (K * L - structured.card) := by
    calc
      _ ≤ 3 * (K * L) * (K * L - structured.card) := hdiff
      _ ≤ T * (K * L - structured.card) :=
        Nat.mul_le_mul_right _ hT
  have hdegreeBound : (∑ r, rowDegree r) ≤
      ∑ i : Fin (K * L), i.val := by
    have hKle : K ≤ K * L := by
      calc
        K = K * 1 := by simp
        _ ≤ K * L := Nat.mul_le_mul_left K hL
    have hsub : K - 1 ≤ K * L - 1 := Nat.sub_le_sub_right hKle 1
    have hdouble :
        2 * (L * ∑ k : Fin K, k.val) ≤
          2 * (∑ i : Fin (K * L), i.val) := by
      calc
        2 * (L * ∑ k : Fin K, k.val) =
            L * (2 * ∑ k : Fin K, k.val) := by ring
        _ = L * (K * (K - 1)) := by rw [htri K]
        _ = (K * L) * (K - 1) := by ring
        _ ≤ (K * L) * (K * L - 1) := Nat.mul_le_mul_left _ hsub
        _ = 2 * (∑ i : Fin (K * L), i.val) := (htri (K * L)).symm
    rw [hdegree]
    omega
  have hEadd :
      3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) +
          3 * (∑ r, rowDegree r) =
        3 * (∑ i : Fin (K * L), i.val) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hdegreeBound]
  have htriDecomp :
      3 * (∑ i : Fin (K * L), i.val) =
        3 * ((∑ i : Fin (K * L), i.val) -
          ∑ i : Fin structured.card, i.val) +
          3 * (∑ i : Fin structured.card, i.val) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel htriMono]
  by_cases hcoeff :
      3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) ≤
        T * (K * L - structured.card)
  · exact Or.inl hcoeff
  · right
    have hmaster :
        3 * ((∑ i : Fin (K * L), i.val) - ∑ r, rowDegree r) +
            3 * (∑ r, rowDegree r) ≤
          T * (K * L - structured.card) +
            3 * (∑ i : Fin structured.card, i.val) := by
      calc
        _ = 3 * (∑ i : Fin (K * L), i.val) := hEadd
        _ = 3 * ((∑ i : Fin (K * L), i.val) -
              ∑ i : Fin structured.card, i.val) +
              3 * (∑ i : Fin structured.card, i.val) := htriDecomp
        _ ≤ T * (K * L - structured.card) +
              3 * (∑ i : Fin structured.card, i.val) :=
          Nat.add_le_add_right hpay _
    omega
-/

end Erdos1058.BugeaudLaurent
