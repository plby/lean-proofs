import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentBalancedDeterminant

open scoped BigOperators

noncomputable section

namespace Erdos1058.BugeaudLaurent

theorem abs_det_le_factorial_mul_prod_row {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℚ) (B : Fin N → ℚ)
    (hB : ∀ i, 0 < B i) (hentry : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ N.factorial * ∏ i, B i := by
  let D : Matrix (Fin N) (Fin N) ℚ := fun i j => A i j / B i
  have hD : ∀ i j, |D i j| ≤ (1 : ℚ) := by
    intro i j
    rw [abs_div]
    rw [div_le_iff₀ (abs_pos.mpr (hB i).ne')]
    simpa [abs_of_pos (hB i)] using hentry i j
  have hdetD := Matrix.det_le (A := D) (abv := AbsoluteValue.abs)
    (x := (1 : ℚ)) hD
  simp only [Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one] at hdetD
  have hdetD' : |D.det| ≤ (N.factorial : ℚ) := by
    exact hdetD
  have hmatrix : A = Matrix.of fun i j => B i * D i j := by
    ext i j
    simp only [D, Matrix.of_apply]
    field_simp [(hB i).ne']
  rw [hmatrix, Matrix.det_mul_column, abs_mul]
  have hprodpos : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  rw [abs_of_pos hprodpos]
  have hprodnonneg : 0 ≤ ∏ i, B i := hprodpos.le
  calc
    (∏ i, B i) * |D.det| ≤ (∏ i, B i) * N.factorial :=
      mul_le_mul_of_nonneg_left hdetD' hprodnonneg
    _ = N.factorial * ∏ i, B i := by
      ring

def interpolationRowBound {K L R S p q a b : ℕ}
    (i : Fin (K * L)) : ℚ :=
  let row := finProdFinEquiv.symm i
  ((b * R + a * S : ℕ) : ℚ) ^ row.1.val / row.1.val.factorial *
    (p : ℚ) ^ (2 * (R - 1) * row.2.val) *
      (q : ℚ) ^ (2 * S * row.2.val)

theorem clearedInterpolationMatrix_cast_entry_le_rowBound
    {K L R S p q a b : ℕ}
    (hR : 0 < R) (hp : 0 < p) (hq : 0 < q)
    (f : Fin (K * L) → Fin R × Fin S) (i j : Fin (K * L)) :
    |(clearedInterpolationMatrix p q a b f i j : ℚ)| ≤
      interpolationRowBound (K := K) (L := L) (R := R) (S := S)
        (p := p) (q := q) (a := a) (b := b) i := by
  let row := finProdFinEquiv.symm i
  let col := f j
  let x := b * col.1.val + a * col.2.val
  let X := b * R + a * S
  have hx : x ≤ X := by
    dsimp only [x, X]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left b col.1.isLt.le)
      (Nat.mul_le_mul_left a col.2.isLt.le)
  have hpExp : 2 * col.1.val * row.2.val ≤
      2 * (R - 1) * row.2.val := by
    have hcol : col.1.val ≤ R - 1 := by omega
    exact Nat.mul_le_mul_right row.2.val (Nat.mul_le_mul_left 2 hcol)
  have hqExp : 2 * (S - col.2.val) * row.2.val ≤
      2 * S * row.2.val := by
    exact Nat.mul_le_mul_right row.2.val
      (Nat.mul_le_mul_left 2 (Nat.sub_le S col.2.val))
  have hchoose : (x.choose row.1.val : ℚ) ≤
      (X : ℚ) ^ row.1.val / row.1.val.factorial := by
    calc
      (x.choose row.1.val : ℚ) ≤
          (x : ℚ) ^ row.1.val / row.1.val.factorial :=
        Nat.choose_le_pow_div row.1.val x
      _ ≤ (X : ℚ) ^ row.1.val / row.1.val.factorial := by
        gcongr
  have hpPow : (p : ℚ) ^ (2 * col.1.val * row.2.val) ≤
      (p : ℚ) ^ (2 * (R - 1) * row.2.val) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hp) hpExp
  have hqPow : (q : ℚ) ^ (2 * (S - col.2.val) * row.2.val) ≤
      (q : ℚ) ^ (2 * S * row.2.val) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hq) hqExp
  dsimp only [x, X, row, col] at hchoose hpPow hqPow
  push_cast at hchoose
  dsimp only [clearedInterpolationMatrix, interpolationRowBound,
    row, col, x, X]
  push_cast
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul (mul_le_mul hchoose hpPow (by positivity) (by positivity))
    hqPow (by positivity) (by positivity)

theorem interpolationRowBound_pos
    {K L R S p q a b : ℕ}
    (hX : 0 < b * R + a * S) (hp : 0 < p) (hq : 0 < q)
    (i : Fin (K * L)) :
    0 < interpolationRowBound (K := K) (L := L) (R := R) (S := S)
      (p := p) (q := q) (a := a) (b := b) i := by
  dsimp only [interpolationRowBound]
  positivity

theorem interpolation_product_inequality_boxes
    {K L R₁ R₂ S₁ S₂ p q a b c t T : ℕ}
    (hK : 0 < K) (hL : 0 < L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (ha : 0 < a) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    (2 : ℚ) ^ (3 * ((∑ i : Fin (K * L), i.val) -
        L * ∑ k : Fin K, k.val)) ≤
      (K * L).factorial *
        ∏ i : Fin (K * L),
          interpolationRowBound (K := K) (L := L)
            (R := R₁ + R₂ - 1) (S := S₁ + S₂ - 1)
            (p := p) (q := q) (a := a) (b := b) i := by
  obtain ⟨f, _hf, hne, hdiv⟩ := exists_large_interpolation_determinant_boxes
    hK hL hR₁ hR₂ hS₁ hS₂ hp hq hpq hpodd hqodd hb
    hsize₁ hsize₂ hinj hT hbc hrel
  let A : Matrix (Fin (K * L)) (Fin (K * L)) ℚ :=
    (clearedInterpolationMatrix p q a b f).map (Int.castRingHom ℚ)
  let B : Fin (K * L) → ℚ := fun i =>
    interpolationRowBound (K := K) (L := L)
      (R := R₁ + R₂ - 1) (S := S₁ + S₂ - 1)
      (p := p) (q := q) (a := a) (b := b) i
  have hR : 0 < R₁ + R₂ - 1 := by omega
  have hS : 0 < S₁ + S₂ - 1 := by omega
  have hX : 0 < b * (R₁ + R₂ - 1) + a * (S₁ + S₂ - 1) := by
    have := Nat.mul_pos hb hR
    omega
  have hB : ∀ i, 0 < B i := fun i =>
    interpolationRowBound_pos hX hp.pos hq.pos i
  have hentry : ∀ i j, |A i j| ≤ B i := by
    intro i j
    change |(clearedInterpolationMatrix p q a b f i j : ℚ)| ≤ B i
    exact clearedInterpolationMatrix_cast_entry_le_rowBound hR hp.pos hq.pos f i j
  have hupper := abs_det_le_factorial_mul_prod_row A B hB hentry
  have hmapdet : A.det =
      ((clearedInterpolationMatrix p q a b f).det : ℚ) := by
    change (((Int.castRingHom ℚ).mapMatrix
      (clearedInterpolationMatrix p q a b f)).det) = _
    exact (RingHom.map_det (Int.castRingHom ℚ)
      (clearedInterpolationMatrix p q a b f)).symm
  have hlowerNat := two_pow_le_natAbs_of_dvd hne hdiv
  have hlower : (2 : ℚ) ^ (3 * ((∑ i : Fin (K * L), i.val) -
        L * ∑ k : Fin K, k.val)) ≤ |A.det| := by
    rw [hmapdet]
    rw [show |((clearedInterpolationMatrix p q a b f).det : ℚ)| =
        ((clearedInterpolationMatrix p q a b f).det.natAbs : ℚ) by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num]
    exact_mod_cast hlowerNat
  exact hlower.trans (by simpa only [B] using hupper)

lemma mul_log_sub_self_le_log_factorial {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * Real.log k - k ≤ Real.log k.factorial := by
  have hs := Stirling.le_log_factorial_stirling hk.ne'
  have hlogk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hlogtwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  nlinarith

lemma weighted_log_lower {K k : ℕ} (hK : 0 < K) (hk : 0 < k) :
    (k : ℝ) * Real.log K - K + k ≤ (k : ℝ) * Real.log k := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog := Real.log_le_sub_one_of_pos (div_pos hKreal hkreal)
  rw [Real.log_div hKreal.ne' hkreal.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hkreal.le
  have hcancel : (k : ℝ) * ((K : ℝ) / k - 1) = K - k := by
    field_simp
  rw [hcancel] at hmul
  linarith

theorem sum_log_factorial_lower {K : ℕ} (hK : 3 ≤ K) :
    ((∑ k : Fin K, k.val : ℕ) : ℝ) * (Real.log K - 3) ≤
      ∑ k : Fin K, Real.log k.val.factorial := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Real.log k.factorial) K]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k) K]
  have hpoint : ∀ k ∈ Finset.range K,
      (k : ℝ) * Real.log K - K ≤ Real.log k.factorial := by
    intro k hkRange
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hfac := mul_log_sub_self_le_log_factorial hkpos
      have hw := weighted_log_lower (K := K) (k := k) (by omega) hkpos
      linarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  have htri : (∑ k ∈ Finset.range K, k) * 2 = K * (K - 1) :=
    Finset.sum_range_id_mul_two K
  have htriReal : (((∑ k ∈ Finset.range K, k : ℕ) : ℝ) * 2) =
      (((K * (K - 1) : ℕ) : ℝ)) := by exact_mod_cast htri
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)] at htriReal
  have hKreal : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hdist : (∑ k ∈ Finset.range K, (k : ℝ)) * Real.log K =
      ∑ k ∈ Finset.range K, (k : ℝ) * Real.log K := by
    rw [Finset.sum_mul]
  push_cast
  nlinarith [hdist]

theorem sum_log_factorial_lower_sharp {K : ℕ} (hK : 2 ≤ K) :
    ((∑ k : Fin K, k.val : ℕ) : ℝ) * (Real.log K - 2) ≤
      ∑ k : Fin K, Real.log k.val.factorial := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Real.log k.factorial) K]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k) K]
  have hpoint : ∀ k ∈ Finset.Ico 1 K,
      (k : ℝ) * Real.log K - K ≤ Real.log k.factorial := by
    intro k hkRange
    have hkpos : 0 < k := (Finset.mem_Ico.mp hkRange).1
    have hfac := mul_log_sub_self_le_log_factorial hkpos
    have hw := weighted_log_lower (K := K) (k := k) (by omega) hkpos
    linarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [← Finset.sum_mul] at hsum
  have hle : 1 ≤ K := by omega
  rw [Finset.sum_Ico_eq_sub (fun k : ℕ => (k : ℝ)) hle,
    Finset.sum_Ico_eq_sub (fun k : ℕ => Real.log k.factorial) hle] at hsum
  simp only [Finset.sum_range_one, Nat.cast_zero, Real.log_zero, zero_sub,
    sub_zero] at hsum
  have hcard : (Finset.Ico 1 K).card = K - 1 := by simp
  rw [hcard] at hsum
  norm_num at hsum
  push_cast [Nat.cast_sub hle] at hsum
  have htri : (∑ k ∈ Finset.range K, k) * 2 = K * (K - 1) :=
    Finset.sum_range_id_mul_two K
  have htriReal : (((∑ k ∈ Finset.range K, k : ℕ) : ℝ) * 2) =
      (((K * (K - 1) : ℕ) : ℝ)) := by exact_mod_cast htri
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)] at htriReal
  push_cast
  have hdist : (∑ k ∈ Finset.range K, (k : ℝ)) * Real.log K =
      ∑ k ∈ Finset.range K, (k : ℝ) * Real.log K := by
    rw [Finset.sum_mul]
  nlinarith [hdist]

def interpolationRowBoundReal {K L R S p q a b : ℕ}
    (i : Fin (K * L)) : ℝ :=
  let row := finProdFinEquiv.symm i
  ((b * R + a * S : ℕ) : ℝ) ^ row.1.val / row.1.val.factorial *
    (p : ℝ) ^ (2 * (R - 1) * row.2.val) *
      (q : ℝ) ^ (2 * S * row.2.val)

lemma interpolationRowBound_cast {K L R S p q a b : ℕ}
    (i : Fin (K * L)) :
    ((interpolationRowBound (K := K) (L := L) (R := R) (S := S)
      (p := p) (q := q) (a := a) (b := b) i : ℚ) : ℝ) =
      interpolationRowBoundReal (K := K) (L := L) (R := R) (S := S)
        (p := p) (q := q) (a := a) (b := b) i := by
  simp only [interpolationRowBound, interpolationRowBoundReal]
  push_cast
  rfl

lemma interpolationRowBoundReal_pos {K L R S p q a b : ℕ}
    (hX : 0 < b * R + a * S) (hp : 0 < p) (hq : 0 < q)
    (i : Fin (K * L)) :
    0 < interpolationRowBoundReal (K := K) (L := L) (R := R) (S := S)
      (p := p) (q := q) (a := a) (b := b) i := by
  dsimp only [interpolationRowBoundReal]
  positivity

lemma log_interpolationRowBoundReal {K L R S p q a b : ℕ}
    (hX : 0 < b * R + a * S) (hp : 0 < p) (hq : 0 < q)
    (i : Fin (K * L)) :
    Real.log (interpolationRowBoundReal (K := K) (L := L) (R := R) (S := S)
      (p := p) (q := q) (a := a) (b := b) i) =
      ((finProdFinEquiv.symm i).1.val : ℝ) * Real.log (b * R + a * S) -
        Real.log (finProdFinEquiv.symm i).1.val.factorial +
      (2 * (R - 1) * (finProdFinEquiv.symm i).2.val : ℕ) * Real.log p +
      (2 * S * (finProdFinEquiv.symm i).2.val : ℕ) * Real.log q := by
  dsimp only [interpolationRowBoundReal]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem sum_log_interpolationRowBoundReal {K L R S p q a b : ℕ}
    (hX : 0 < b * R + a * S) (hp : 0 < p) (hq : 0 < q) :
    (∑ i : Fin (K * L), Real.log
      (interpolationRowBoundReal (K := K) (L := L) (R := R) (S := S)
        (p := p) (q := q) (a := a) (b := b) i)) =
      (L : ℝ) * (∑ k : Fin K, (k.val : ℝ)) * Real.log (b * R + a * S) -
        (L : ℝ) * ∑ k : Fin K, Real.log k.val.factorial +
      (K : ℝ) * (∑ l : Fin L, (l.val : ℝ)) *
        ((2 * (R - 1) : ℕ) * Real.log p + (2 * S : ℕ) * Real.log q) := by
  let e : Fin K × Fin L ≃ Fin (K * L) := finProdFinEquiv
  calc
    (∑ i : Fin (K * L), Real.log
      (interpolationRowBoundReal (K := K) (L := L) (R := R) (S := S)
        (p := p) (q := q) (a := a) (b := b) i)) =
        ∑ row : Fin K × Fin L, Real.log
          (interpolationRowBoundReal (K := K) (L := L) (R := R) (S := S)
            (p := p) (q := q) (a := a) (b := b) (e row)) := by
              exact (e.sum_comp _).symm
    _ = _ := by
      simp_rw [log_interpolationRowBoundReal hX hp hq]
      rw [Fintype.sum_prod_type]
      simp only [e, Equiv.symm_apply_apply]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
        ← Finset.sum_mul, ← Finset.mul_sum]
      push_cast
      rw [show (∑ l : Fin L, (2 : ℝ) * (R - 1 : ℕ) * l.val) =
          (2 : ℝ) * (R - 1 : ℕ) * ∑ l : Fin L, (l.val : ℝ) by
        rw [Finset.mul_sum]]
      rw [show (∑ l : Fin L, (2 : ℝ) * S * l.val) =
          (2 : ℝ) * S * ∑ l : Fin L, (l.val : ℝ) by
        rw [Finset.mul_sum]]
      ring

theorem interpolation_log_inequality_boxes_raw
    {K L R₁ R₂ S₁ S₂ p q a b c t T : ℕ}
    (hK : 0 < K) (hL : 0 < L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (ha : 0 < a) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    ((3 * ((∑ i : Fin (K * L), i.val) -
        L * ∑ k : Fin K, k.val) : ℕ) : ℝ) * Real.log 2 ≤
      Real.log (K * L).factorial +
        ∑ i : Fin (K * L), Real.log
          (interpolationRowBoundReal (K := K) (L := L)
            (R := R₁ + R₂ - 1) (S := S₁ + S₂ - 1)
            (p := p) (q := q) (a := a) (b := b) i) := by
  have hprod := interpolation_product_inequality_boxes hK hL hR₁ hR₂ hS₁ hS₂
    hp hq hpq hpodd hqodd ha hb hsize₁ hsize₂ hinj hT hbc hrel
  have hreal :
      (((2 : ℚ) ^ (3 * ((∑ i : Fin (K * L), i.val) -
          L * ∑ k : Fin K, k.val)) : ℚ) : ℝ) ≤
        ((((K * L).factorial : ℚ) *
          ∏ i : Fin (K * L),
            interpolationRowBound (K := K) (L := L)
              (R := R₁ + R₂ - 1) (S := S₁ + S₂ - 1)
              (p := p) (q := q) (a := a) (b := b) i : ℚ) : ℝ) := by
    exact_mod_cast hprod
  push_cast at hreal
  simp_rw [interpolationRowBound_cast] at hreal
  have hlog := Real.log_le_log (by positivity) hreal
  have hR : 0 < R₁ + R₂ - 1 := by omega
  have hX : 0 < b * (R₁ + R₂ - 1) + a * (S₁ + S₂ - 1) :=
    Nat.add_pos_left (Nat.mul_pos hb hR) _
  have hrowpos : ∀ i : Fin (K * L), 0 <
      interpolationRowBoundReal (K := K) (L := L)
        (R := R₁ + R₂ - 1) (S := S₁ + S₂ - 1)
        (p := p) (q := q) (a := a) (b := b) i := fun i =>
    interpolationRowBoundReal_pos hX hp.pos hq.pos i
  rw [Real.log_pow,
    Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr
      (fun i _ => (hrowpos i).ne')),
    Real.log_prod (fun i _ => (hrowpos i).ne')] at hlog
  simpa only [Nat.cast_ofNat] using hlog

lemma log_factorial_le_self_mul_log {N : ℕ} (hN : 0 < N) :
    Real.log N.factorial ≤ (N : ℝ) * Real.log N := by
  have hcast : ((N.factorial : ℕ) : ℝ) ≤ ((N ^ N : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le_pow N
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < N.factorial) hcast
  push_cast at hlog
  rw [Real.log_pow] at hlog
  exact hlog

theorem interpolation_explicit_log_inequality_boxes
    {K L R₁ R₂ S₁ S₂ p q a b c t T : ℕ}
    (hK : 3 ≤ K) (hL : 0 < L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (ha : 0 < a) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    ((3 * ((∑ i : Fin (K * L), i.val) -
        L * ∑ k : Fin K, k.val) : ℕ) : ℝ) * Real.log 2 ≤
      (K * L : ℕ) * Real.log (K * L) +
      (L : ℝ) * (∑ k : Fin K, (k.val : ℝ)) *
        (Real.log (b * (R₁ + R₂ - 1) + a * (S₁ + S₂ - 1)) -
          Real.log K + 2) +
      (K : ℝ) * (∑ l : Fin L, (l.val : ℝ)) *
        ((2 * (R₁ + R₂ - 1 - 1) : ℕ) * Real.log p +
          (2 * (S₁ + S₂ - 1) : ℕ) * Real.log q) := by
  have hraw := interpolation_log_inequality_boxes_raw (by omega : 0 < K) hL
    hR₁ hR₂ hS₁ hS₂ hp hq hpq hpodd hqodd ha hb hsize₁ hsize₂ hinj
    hT hbc hrel
  have hR : 0 < R₁ + R₂ - 1 := by omega
  have hX : 0 < b * (R₁ + R₂ - 1) + a * (S₁ + S₂ - 1) :=
    Nat.add_pos_left (Nat.mul_pos hb hR) _
  rw [sum_log_interpolationRowBoundReal hX hp.pos hq.pos] at hraw
  have hfac := log_factorial_le_self_mul_log
    (Nat.mul_pos (by omega : 0 < K) hL)
  have hden := sum_log_factorial_lower_sharp (by omega : 2 ≤ K)
  have hdenL := mul_le_mul_of_nonneg_left hden
    (by positivity : (0 : ℝ) ≤ L)
  push_cast at hfac
  push_cast at hdenL
  push_cast [Nat.cast_sub (by omega : 1 ≤ R₁ + R₂),
    Nat.cast_sub (by omega : 1 ≤ S₁ + S₂)] at hraw ⊢
  ring_nf at hdenL hfac hraw ⊢
  linarith

theorem interpolation_criterion_boxes
    {K L R₁ R₂ S₁ S₂ p q a b c t T : ℕ}
    (hK : 3 ≤ K) (hL : 0 < L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (ha : 0 < a) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T])
    (hcriterion :
      (K * L : ℕ) * Real.log (K * L) +
        (L : ℝ) * (∑ k : Fin K, (k.val : ℝ)) *
          (Real.log (b * (R₁ + R₂ - 1) + a * (S₁ + S₂ - 1)) -
            Real.log K + 2) +
        (K : ℝ) * (∑ l : Fin L, (l.val : ℝ)) *
          ((2 * (R₁ + R₂ - 1 - 1) : ℕ) * Real.log p +
            (2 * (S₁ + S₂ - 1) : ℕ) * Real.log q) <
      ((3 * ((∑ i : Fin (K * L), i.val) -
          L * ∑ k : Fin K, k.val) : ℕ) : ℝ) * Real.log 2) : False := by
  have hbound := interpolation_explicit_log_inequality_boxes hK hL
    hR₁ hR₂ hS₁ hS₂ hp hq hpq hpodd hqodd ha hb hsize₁ hsize₂ hinj
    hT hbc hrel
  linarith

lemma two_mul_sum_fin_val (K : ℕ) :
    2 * (∑ k : Fin K, (k.val : ℝ)) = (K : ℝ) * (K - 1) := by
  by_cases hK0 : K = 0
  · subst K
    simp
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (k : ℝ)) K]
  have htri : (∑ k ∈ Finset.range K, k) * 2 = K * (K - 1) :=
    Finset.sum_range_id_mul_two K
  have hreal : (((∑ k ∈ Finset.range K, k : ℕ) : ℝ) * 2) =
      (((K * (K - 1) : ℕ) : ℝ)) := by exact_mod_cast htri
  have hKone : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK0
  push_cast at hreal ⊢
  push_cast [Nat.cast_sub hKone] at hreal
  linarith

theorem interpolation_simple_criterion_boxes
    {K L R₁ R₂ S₁ S₂ p q a b c t T : ℕ}
    (hK : 3 ≤ K) (hL : 2 ≤ L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (ha : 0 < a) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val))
    (hT : 3 * (K * L) ≤ T)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T])
    (hcriterion :
      2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log (b * (R₁ + R₂ - 1) + a * (S₁ + S₂ - 1)) -
            Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((R₁ + R₂ - 1 - 1 : ℕ) * Real.log p +
            (S₁ + S₂ - 1 : ℕ) * Real.log q) <
      3 * K * (L - 1 : ℕ) * Real.log 2) : False := by
  apply interpolation_criterion_boxes hK (by omega : 0 < L)
    hR₁ hR₂ hS₁ hS₂ hp hq hpq hpodd hqodd ha hb hsize₁ hsize₂ hinj
    hT hbc hrel
  have hsumK := two_mul_sum_fin_val K
  have hsumL := two_mul_sum_fin_val L
  have hsumN := two_mul_sum_fin_val (K * L)
  have hKreal : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hKLnatpos : 0 < K * L := Nat.mul_pos (by omega) (by omega)
  have hdiffNonnegReal :
      (L : ℝ) * (∑ k : Fin K, (k.val : ℝ)) ≤
        ∑ i : Fin (K * L), (i.val : ℝ) := by
    have hLm1 : (0 : ℝ) ≤ L - 1 := by linarith
    have hprod : (0 : ℝ) ≤ (K : ℝ) ^ 2 * L * (L - 1) := by positivity
    push_cast at hsumN
    ring_nf at hsumK hsumN
    nlinarith [hprod]
  have hdiffNonneg :
      L * ∑ k : Fin K, k.val ≤ ∑ i : Fin (K * L), i.val := by
    exact_mod_cast hdiffNonnegReal
  have hdiff :
      (2 : ℝ) * (((∑ i : Fin (K * L), i.val) -
        L * ∑ k : Fin K, k.val : ℕ) : ℝ) =
          (K : ℝ) ^ 2 * L * (L - 1) := by
    push_cast [Nat.cast_sub hdiffNonneg,
      Nat.cast_sub (by omega : 1 ≤ K),
      Nat.cast_sub (by omega : 1 ≤ L),
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hKLnatpos.ne')] at hsumK hsumN ⊢
    ring_nf at hsumK hsumN ⊢
    nlinarith
  have hKLpos : (0 : ℝ) < K * L := by positivity
  have hscalePos : (0 : ℝ) < (K : ℝ) * L / 2 := by positivity
  have hscaled := mul_lt_mul_of_pos_left hcriterion hscalePos
  push_cast [Nat.cast_sub (by omega : 1 ≤ K),
    Nat.cast_sub (by omega : 1 ≤ L),
    Nat.cast_sub (by omega : 1 ≤ R₁ + R₂),
    Nat.cast_sub (by omega : 1 ≤ S₁ + S₂)] at hscaled ⊢
  have hsumK' : (∑ k : Fin K, (k.val : ℝ)) =
      (K : ℝ) * (K - 1) / 2 := by linarith [hsumK]
  have hsumL' : (∑ l : Fin L, (l.val : ℝ)) =
      (L : ℝ) * (L - 1) / 2 := by linarith [hsumL]
  have hdiff' : (((∑ i : Fin (K * L), i.val) -
      L * ∑ k : Fin K, k.val : ℕ) : ℝ) =
        (K : ℝ) ^ 2 * L * (L - 1) / 2 := by linarith [hdiff]
  rw [hsumK', hsumL', hdiff']
  ring_nf at hscaled ⊢
  exact hscaled

end Erdos1058.BugeaudLaurent
