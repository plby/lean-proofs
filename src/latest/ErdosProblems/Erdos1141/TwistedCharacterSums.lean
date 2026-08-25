import ErdosProblems.Erdos1141.QuadraticCharacters

/-!
# A bounded auxiliary modulus in the fourth-moment estimate

The quadratic characters at moduli four and eight can be included by CRT.
-/

open scoped BigOperators

namespace Erdos1141.CharacterSums

/-- The external product of two Dirichlet characters. -/
noncomputable def crtMulChar {m n : ℕ} (hmn : m.Coprime n)
    (ψ : DirichletCharacter ℤ m) (χ : DirichletCharacter ℤ n) :
    DirichletCharacter ℤ (m * n) where
  toFun x := ψ (ZMod.chineseRemainder hmn x).1 * χ (ZMod.chineseRemainder hmn x).2
  map_one' := by simp only [map_one, Prod.fst_one, Prod.snd_one, mul_one]
  map_mul' x y := by
    simp only [map_mul, Prod.fst_mul, Prod.snd_mul]
    ring
  map_nonunit' x hx := by
    by_cases hfst : IsUnit (ZMod.chineseRemainder hmn x).1
    · have hsnd : ¬ IsUnit (ZMod.chineseRemainder hmn x).2 := by
        intro h
        apply hx
        have hp : IsUnit (ZMod.chineseRemainder hmn x) := Prod.isUnit_iff.mpr ⟨hfst, h⟩
        have hinv := hp.map (ZMod.chineseRemainder hmn).symm.toMonoidHom
        change IsUnit ((ZMod.chineseRemainder hmn).symm (ZMod.chineseRemainder hmn x)) at hinv
        simpa only [RingEquiv.symm_apply_apply] using hinv
      rw [MulChar.map_nonunit χ hsnd, mul_zero]
    · rw [MulChar.map_nonunit ψ hfst, zero_mul]

@[simp]
lemma crtMulChar_apply {m n : ℕ} (hmn : m.Coprime n)
    (ψ : DirichletCharacter ℤ m) (χ : DirichletCharacter ℤ n) (x : ZMod (m * n)) :
    crtMulChar hmn ψ χ x =
      ψ (ZMod.chineseRemainder hmn x).1 * χ (ZMod.chineseRemainder hmn x).2 := rfl

lemma abs_mulChar_le_one {R : Type*} [CommMonoid R] (χ : MulChar R ℤ)
    (hχ : χ.IsQuadratic) (x : R) : |(χ x : ℝ)| ≤ 1 := by
  rcases hχ x with h | h | h <;> rw [h] <;> norm_num

lemma abs_mulChar_of_isUnit {R : Type*} [CommMonoid R] (χ : MulChar R ℤ)
    (hχ : χ.IsQuadratic) (x : R) (hx : IsUnit x) : |(χ x : ℝ)| = 1 := by
  have hne : χ x ≠ 0 := (hx.map χ.toMonoidHom).ne_zero
  rcases hχ x with h | h | h
  · exact (hne h).elim
  · rw [h]; norm_num
  · rw [h]; norm_num

lemma mulChar_prefix_polyaVinogradov_bound {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℤ q)
    (hχ : χ.ringHomComp (Int.castRingHom ℂ) ≠ 1) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, (χ (n : ZMod q) : ℝ)| ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have h := BoundedGaps.Maynard.norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq (χ.ringHomComp (Int.castRingHom ℂ)) hχ N
  simp only [BoundedGaps.Maynard.dirichletCharacterIntervalSum,
    MulChar.ringHomComp_apply] at h
  change ‖∑ n ∈ Finset.Icc 1 N, (χ (n : ZMod q) : ℂ)‖ ≤
    2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) at h
  rw [← Int.cast_sum, Complex.norm_intCast] at h
  rw [← Int.cast_sum]
  exact h

lemma crtMulChar_isQuadratic {m n : ℕ} (hmn : m.Coprime n)
    (ψ : DirichletCharacter ℤ m) (χ : DirichletCharacter ℤ n)
    (hψ : ψ.IsQuadratic) (hχ : χ.IsQuadratic) : (crtMulChar hmn ψ χ).IsQuadratic := by
  intro x
  rcases hψ (ZMod.chineseRemainder hmn x).1 with h | h | h <;>
    rcases hχ (ZMod.chineseRemainder hmn x).2 with h' | h' | h' <;>
      simp only [crtMulChar_apply, h, h'] <;> norm_num

lemma sum_crtMulChar_quartic {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (ψ : DirichletCharacter ℤ m) (χ : DirichletCharacter ℤ n) (a b c d : ℤ) :
    (∑ x : ZMod (m * n), crtMulChar hmn ψ χ ((x - a) * (x - b) * (x - c) * (x - d))) =
      (∑ x : ZMod m, ψ ((x - a) * (x - b) * (x - c) * (x - d))) *
      (∑ x : ZMod n, χ ((x - a) * (x - b) * (x - c) * (x - d))) := by
  calc
    _ = ∑ x : ZMod m × ZMod n,
        ψ ((x.1 - a) * (x.1 - b) * (x.1 - c) * (x.1 - d)) *
        χ ((x.2 - a) * (x.2 - b) * (x.2 - c) * (x.2 - d)) := by
      apply Fintype.sum_equiv (ZMod.chineseRemainder hmn).toEquiv
      intro x
      change crtMulChar hmn ψ χ ((x - a) * (x - b) * (x - c) * (x - d)) =
        ψ (((ZMod.chineseRemainder hmn x).1 - a) * ((ZMod.chineseRemainder hmn x).1 - b) *
          ((ZMod.chineseRemainder hmn x).1 - c) * ((ZMod.chineseRemainder hmn x).1 - d)) *
        χ (((ZMod.chineseRemainder hmn x).2 - a) * ((ZMod.chineseRemainder hmn x).2 - b) *
          ((ZMod.chineseRemainder hmn x).2 - c) * ((ZMod.chineseRemainder hmn x).2 - d))
      simp only [crtMulChar_apply, map_mul, map_sub, map_intCast,
        Prod.fst_sub, Prod.snd_sub,
        Prod.fst_intCast, Prod.snd_intCast]
      ring
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

lemma abs_sum_mulChar_quartic_le {m : ℕ} [NeZero m]
    (ψ : DirichletCharacter ℤ m) (hψ : ψ.IsQuadratic) (a b c d : ℤ) :
    |((∑ x : ZMod m, ψ ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤ m := by
  push_cast
  calc
    _ ≤ ∑ x : ZMod m, |(ψ ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : ZMod m, (1 : ℝ) :=
      Finset.sum_le_sum fun _ _ ↦ abs_mulChar_le_one ψ hψ _
    _ = _ := by simp

lemma sum_quartic_plus_eq_minus {q : ℕ} [NeZero q] (χ : ZMod q → ℤ)
    (a b c d : ℕ) :
    (∑ x : ZMod q, χ ((x + a) * (x + b) * (x + c) * (x + d))) =
      ∑ x : ZMod q, χ ((x - a) * (x - b) * (x - c) * (x - d)) := by
  apply Fintype.sum_equiv (Equiv.neg (ZMod q))
  intro x
  congr 1
  change (x + a) * (x + b) * (x + c) * (x + d) =
    ((-x) - a) * ((-x) - b) * ((-x) - c) * ((-x) - d)
  ring

/-- A complete quartic bound implies the corresponding fourth moment. -/
theorem mulChar_fourth_moment_le_of_unpaired {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (B : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hunpaired : ∀ a b c d : ℕ, a ≤ B → b ≤ B → c ≤ B → d ≤ B →
      ¬ ((a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      |((∑ x : ZMod q, χ ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤ C)
    {κ : Type*} [Fintype κ] (f : κ → ℕ) (hf : Function.Injective f) (hB : ∀ k, f k ≤ B) :
    (∑ x : ZMod q, (∑ k : κ, (χ (x + f k) : ℝ)) ^ 4) ≤
      3 * (Fintype.card κ : ℝ) ^ 2 * q + (Fintype.card κ : ℝ) ^ 4 * C := by
  classical
  have hind : ∀ a b c d : κ,
      (∑ x : ZMod q, (χ ((x + f a) * (x + f b) * (x + f c) * (x + f d)) : ℝ)) ≤
        (if a = b ∧ c = d then (q : ℝ) else 0) +
        (if a = c ∧ b = d then (q : ℝ) else 0) +
        (if a = d ∧ b = c then (q : ℝ) else 0) + C := by
    intro a b c d
    have htriv : (∑ x : ZMod q,
        (χ ((x + f a) * (x + f b) * (x + f c) * (x + f d)) : ℝ)) ≤ q := by
      calc
        _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦
          (le_abs_self _).trans (abs_mulChar_le_one χ hχ _)
        _ = _ := by simp
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    split_ifs with h₁ h₂ h₃
    all_goals first
      | linarith
      | have hu := hunpaired (f a) (f b) (f c) (f d) (hB a) (hB b) (hB c) (hB d)
          (by simpa only [hf.eq_iff] using (show ¬ ((a = b ∧ c = d) ∨
            (a = c ∧ b = d) ∨ (a = d ∧ b = c)) by tauto))
        rw [← sum_quartic_plus_eq_minus χ (f a) (f b) (f c) (f d)] at hu
        push_cast at hu
        simpa using (le_abs_self _).trans hu
  have hexpand : ∀ x : ZMod q, (∑ k : κ, (χ (x + f k) : ℝ)) ^ 4 =
      ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        (χ ((x + f a) * (x + f b) * (x + f c) * (x + f d)) : ℝ) := by
    intro x
    rw [show (∑ k : κ, (χ (x + f k) : ℝ)) ^ 4 =
      (∑ k : κ, (χ (x + f k) : ℝ)) * (∑ k : κ, (χ (x + f k) : ℝ)) *
      (∑ k : κ, (χ (x + f k) : ℝ)) * (∑ k : κ, (χ (x + f k) : ℝ)) by ring]
    simp only [Finset.mul_sum, map_mul, Int.cast_mul, mul_comm, mul_assoc]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        ((if a = b ∧ c = d then (q : ℝ) else 0) +
         (if a = c ∧ b = d then (q : ℝ) else 0) +
         (if a = d ∧ b = c then (q : ℝ) else 0) + C) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro d _
      exact hind a b c d
    _ = _ := by
      simp only [ite_and, Finset.sum_add_distrib]
      simp [Finset.sum_ite_irrel, Finset.sum_const, nsmul_eq_mul]
      ring

variable {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise fun i j ↦ (p i).Coprime (p j))

lemma abs_sum_crt_primeProduct_unpaired_le {t : ℕ} [NeZero t]
    (ht : t.Coprime (∏ i, p i)) (ψ : DirichletCharacter ℤ t) (hψ : ψ.IsQuadratic)
    (hodd : ∀ i, p i ≠ 2) {B a b c d : ℕ}
    (ha : a ≤ B) (hb : b ≤ B) (hc' : c ≤ B) (hd : d ≤ B)
    (h : ¬ ((a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    |((∑ x : ZMod (t * ∏ i, p i),
      crtMulChar ht ψ (primeProductMulChar p hc)
        ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      t * (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3)) := by
  have hfactor := sum_crtMulChar_quartic ht ψ (primeProductMulChar p hc) a b c d
  simp only [Int.cast_natCast] at hfactor
  rw [hfactor, Int.cast_mul, abs_mul]
  apply mul_le_mul
  · simpa only [Int.cast_natCast] using abs_sum_mulChar_quartic_le ψ hψ a b c d
  · exact abs_sum_primeProductCharacter_unpaired_le p hc hodd ha hb hc' hd h
  · exact abs_nonneg _
  · positivity

theorem crt_primeProduct_fourth_moment_le {t : ℕ} [NeZero t]
    (ht : t.Coprime (∏ i, p i)) (ψ : DirichletCharacter ℤ t) (hψ : ψ.IsQuadratic)
    (hodd : ∀ i, p i ≠ 2) (B : ℕ) :
    (∑ x : ZMod (t * ∏ i, p i),
      (∑ b ∈ Finset.Icc 1 B, (crtMulChar ht ψ (primeProductMulChar p hc) (x + b) : ℝ)) ^ 4) ≤
      3 * (B : ℝ) ^ 2 * (t * ∏ i, p i : ℕ) +
      (B : ℝ) ^ 4 *
        (t * (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3))) := by
  classical
  let χ := crtMulChar ht ψ (primeProductMulChar p hc)
  have h := mulChar_fourth_moment_le_of_unpaired χ
    (crtMulChar_isQuadratic ht ψ (primeProductMulChar p hc) hψ
      (primeProductMulChar_isQuadratic p hc))
    B (t * (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3)))
    (by positivity)
    (fun a b c d ha hb hc' hd hu ↦
      abs_sum_crt_primeProduct_unpaired_le p hc ht ψ hψ hodd ha hb hc' hd hu)
    (κ := ↥(Finset.Icc 1 B)) Subtype.val Subtype.val_injective
    (fun k ↦ (Finset.mem_Icc.mp k.property).2)
  have hsubtype : ∀ x : ZMod (t * ∏ i, p i),
      (∑ k : ↥(Finset.Icc 1 B), (χ (x + (k.val : ℕ)) : ℝ)) =
        ∑ b ∈ Finset.Icc 1 B, (χ (x + b) : ℝ) := by
    intro x
    exact Finset.sum_coe_sort (Finset.Icc 1 B) (fun b : ℕ ↦ (χ (x + b) : ℝ))
  simp_rw [hsubtype] at h
  simpa only [Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using h

theorem crt_primeProduct_fourth_moment_short_le {t : ℕ} [NeZero t]
    (ht : t.Coprime (∏ i, p i)) (ψ : DirichletCharacter ℤ t) (hψ : ψ.IsQuadratic)
    (hodd : ∀ i, p i ≠ 2) (B : ℕ) (hB : B ^ 7 ≤ ∏ i, p i) :
    (∑ x : ZMod (t * ∏ i, p i),
      (∑ b ∈ Finset.Icc 1 B, (crtMulChar ht ψ (primeProductMulChar p hc) (x + b) : ℝ)) ^ 4) ≤
      (3 + 3 ^ Fintype.card ι) * (B : ℝ) ^ 2 * (t * ∏ i, p i : ℕ) := by
  have hsB := Real.sq_sqrt (show 0 ≤ (B : ℝ) ^ 3 by positivity)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (∏ i, p i : ℕ) by positivity)
  have hBr : (B : ℝ) ^ 7 ≤ (∏ i, p i : ℕ) := by exact_mod_cast hB
  have hroot : (B : ℝ) ^ 2 * Real.sqrt ((B : ℝ) ^ 3) ≤
      Real.sqrt (∏ i, p i : ℕ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hsB, hsq]
    nlinarith [hBr]
  have hmain := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (t : ℝ) * 3 ^ Fintype.card ι * (B : ℝ) ^ 2 *
      Real.sqrt (∏ i, p i : ℕ) by positivity)
  have hid : Real.sqrt (∏ i, p i : ℕ) * Real.sqrt (∏ i, p i : ℕ) =
      (∏ i, p i : ℕ) := Real.mul_self_sqrt (by positivity)
  have hmain' : (B : ℝ) ^ 4 *
      (t * (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3))) ≤
        3 ^ Fintype.card ι * (B : ℝ) ^ 2 * (t * ∏ i, p i : ℕ) := by
    calc
      _ = ((t : ℝ) * 3 ^ Fintype.card ι * (B : ℝ) ^ 2 * Real.sqrt (∏ i, p i : ℕ)) *
          ((B : ℝ) ^ 2 * Real.sqrt ((B : ℝ) ^ 3)) := by ring
      _ ≤ _ := by
        have h := hmain
        simp only [mul_assoc, hid, Nat.cast_mul] at h ⊢
        nlinarith [h]
  have hmoment := crt_primeProduct_fourth_moment_le p hc ht ψ hψ hodd B
  nlinarith [hmoment, hmain']

end Erdos1141.CharacterSums
