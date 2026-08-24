import ErdosProblems.Erdos587.ReciprocalPoisson
import ErdosProblems.Erdos587.FiniteFourier

/-!
# Finite quadratic Gauss sums

The modular representation supports exact translations and orthogonality.
It is identified with the integer-phase sums appearing in Poisson summation.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos587

noncomputable def modularQuadraticGaussSum {q : ℕ} [NeZero q] (a k : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar (a * x ^ 2 + k * x)

lemma stdAddChar_intCast_eq_phase {q : ℕ} [NeZero q] (z : ℤ) :
    ZMod.stdAddChar (z : ZMod q) = phase ((z : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe]
  simp only [phase, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

lemma modularQuadraticGaussSum_eq_complete {q : ℕ} [NeZero q] (a k : ℤ) :
    modularQuadraticGaussSum (a : ZMod q) (k : ZMod q) = completeQuadraticGaussSum q a k := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    unfold modularQuadraticGaussSum completeQuadraticGaussSum
    apply Finset.sum_congr rfl
    intro x hx
    have h := stdAddChar_intCast_eq_phase (q := q + 1)
      (a * (x.val : ℕ) ^ 2 + k * (x.val : ℕ))
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      ZMod.natCast_zmod_val] at h
    simpa only [ZMod.val, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using h

/-- Completing the square by a modular translation, without inverting two.
The even-modulus cases will specify which linear coefficients have this form. -/
lemma modularQuadraticGaussSum_complete_square {q : ℕ} [NeZero q]
    (a h : ZMod q) :
    modularQuadraticGaussSum a (2 * a * h) =
      ZMod.stdAddChar (-(a * h ^ 2)) * modularQuadraticGaussSum a 0 := by
  unfold modularQuadraticGaussSum
  simp only [zero_mul, add_zero]
  rw [Finset.mul_sum]
  have heq (x : ZMod q) : ZMod.stdAddChar (a * x ^ 2 + (2 * a * h) * x) =
      ZMod.stdAddChar (-(a * h ^ 2)) * ZMod.stdAddChar (a * (h + x) ^ 2) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [heq]
  exact (Fintype.sum_equiv (Equiv.addLeft h) _ _ (fun x => rfl))

/-- Exact complete-period autocorrelation. Only the kernel of multiplication
by `2*a` remains after character orthogonality. -/
lemma modularQuadraticGaussSum_mul_conj {q : ℕ} [NeZero q] (a k : ZMod q) :
    modularQuadraticGaussSum a k * conj (modularQuadraticGaussSum a k) =
      (q : ℂ) * ∑ h ∈ Finset.univ.filter (fun h : ZMod q => 2 * a * h = 0),
        ZMod.stdAddChar (a * h ^ 2 + k * h) := by
  classical
  let F : ZMod q → ℂ := fun x => ZMod.stdAddChar (a * x ^ 2 + k * x)
  have hcorr (y : ZMod q) : (∑ x : ZMod q, F x * conj (F y)) =
      ∑ h : ZMod q, ZMod.stdAddChar (a * h ^ 2 + k * h) *
        ZMod.stdAddChar ((2 * a * h) * y) := by
    have hshift : (∑ x : ZMod q, F x * conj (F y)) =
        ∑ h : ZMod q, F (y + h) * conj (F y) :=
      (Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun h => rfl)).symm
    rw [hshift]
    apply Finset.sum_congr rfl
    intro h hh
    dsimp [F]
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  change (∑ x : ZMod q, F x) * conj (∑ y : ZMod q, F y) = _
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [hcorr]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, cyclic_character_orthogonality]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> ring

lemma zmod_two_mul_zero_nonzero_val {q : ℕ} [NeZero q] (x : ZMod q)
    (hx : (2 : ZMod q) * x = 0) (hx0 : x ≠ 0) : 2 * x.val = q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hxval : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero x).not.mpr hx0)
  have hxq : x.val < q := ZMod.val_lt x
  have hcast : ((2 * x.val : ℕ) : ZMod q) = 0 := by simpa using hx
  have hdvd : q ∣ 2 * x.val := (CharP.cast_eq_zero_iff (ZMod q) q (2 * x.val)).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  have htpos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    rw [ht0, mul_zero] at ht
    omega
  have htlt : t < 2 := by
    apply (Nat.mul_lt_mul_left hq).mp
    rw [← ht]
    omega
  have ht1 : t = 1 := by omega
  simpa only [ht1, mul_one] using ht

/-- There are at most two residues killed by multiplication by two, even
when the modulus is composite. -/
lemma card_zmod_two_mul_zero_le {q : ℕ} [NeZero q] :
    (Finset.univ.filter (fun x : ZMod q => 2 * x = 0)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun x : ZMod q => 2 * x = 0)
  by_cases hzero : ∀ x ∈ S, x = 0
  · have hsub : S ⊆ {0} := fun x hx => by simpa using hzero x hx
    have hcard := Finset.card_le_card hsub
    simpa only [Finset.card_singleton] using hcard.trans (by norm_num : ({0} : Finset (ZMod q)).card ≤ 2)
  · push Not at hzero
    obtain ⟨x, hx, hx0⟩ := hzero
    have hxval := zmod_two_mul_zero_nonzero_val x (Finset.mem_filter.mp hx).2 hx0
    have hsub : S ⊆ {0, x} := by
      intro y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      · have hyval := zmod_two_mul_zero_nonzero_val y (Finset.mem_filter.mp hy).2 hy0
        have heq : y = x := ZMod.val_injective q (by omega)
        simp [heq]
    have hcard := Finset.card_le_card hsub
    simpa only [Finset.card_pair hx0.symm] using hcard

lemma card_zmod_two_mul_unit_zero_le {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    (Finset.univ.filter (fun x : ZMod q => 2 * a * x = 0)).card ≤ 2 := by
  classical
  have hsub : Finset.univ.filter (fun x : ZMod q => 2 * a * x = 0) ⊆
      Finset.univ.filter (fun x : ZMod q => 2 * x = 0) := by
    intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    obtain ⟨u, rfl⟩ := ha
    have hh' : (u : ZMod q) * (2 * x) = 0 := by
      rw [show (u : ZMod q) * (2 * x) = 2 * (u : ZMod q) * x by ring]
      exact hh
    have hcancel := congrArg (fun z : ZMod q => (↑(u⁻¹) : ZMod q) * z) hh'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [← mul_assoc] using hcancel
  exact (Finset.card_le_card hsub).trans card_zmod_two_mul_zero_le

/-- Square-root bound for a complete primitive quadratic Gauss sum, valid
uniformly for odd and even composite moduli and every linear term. -/
theorem norm_modularQuadraticGaussSum_sq_le {q : ℕ} [NeZero q]
    (a k : ZMod q) (ha : IsUnit a) :
    ‖modularQuadraticGaussSum a k‖ ^ 2 ≤ 2 * (q : ℝ) := by
  classical
  let S := Finset.univ.filter (fun h : ZMod q => 2 * a * h = 0)
  have hnorm : ‖modularQuadraticGaussSum a k‖ ^ 2 =
      (q : ℝ) * ‖∑ h ∈ S, ZMod.stdAddChar (a * h ^ 2 + k * h)‖ := by
    have h := congrArg norm (modularQuadraticGaussSum_mul_conj a k)
    simpa only [norm_mul, Complex.norm_conj, RCLike.norm_natCast, pow_two] using h
  have hsum : ‖∑ h ∈ S, ZMod.stdAddChar (a * h ^ 2 + k * h)‖ ≤ (S.card : ℝ) := by
    calc
      ‖∑ h ∈ S, ZMod.stdAddChar (a * h ^ 2 + k * h)‖ ≤
          ∑ h ∈ S, ‖ZMod.stdAddChar (a * h ^ 2 + k * h)‖ := norm_sum_le _ _
      _ = (S.card : ℝ) := by
        have hchar (z : ZMod q) : ‖ZMod.stdAddChar z‖ = 1 := Circle.norm_coe _
        simp only [hchar, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (S.card : ℝ) ≤ 2 := by exact_mod_cast card_zmod_two_mul_unit_zero_le a ha
  calc
    ‖modularQuadraticGaussSum a k‖ ^ 2 =
        (q : ℝ) * ‖∑ h ∈ S, ZMod.stdAddChar (a * h ^ 2 + k * h)‖ := hnorm
    _ ≤ (q : ℝ) * S.card := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (q : ℝ) * 2 := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    _ = 2 * (q : ℝ) := mul_comm _ _

theorem norm_completeQuadraticGaussSum_le_sqrt {q : ℕ} (hq : 0 < q) (a k : ℤ)
    (ha : IsUnit (a : ZMod q)) :
    ‖completeQuadraticGaussSum q a k‖ ≤ Real.sqrt (2 * (q : ℝ)) := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [← modularQuadraticGaussSum_eq_complete a k]
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (norm_modularQuadraticGaussSum_sq_le _ _ ha)

/-- Integer congruences may be used directly inside a rational phase. -/
lemma phase_div_eq_of_dvd_sub {q : ℕ} (hq : 0 < q) (a b : ℤ)
    (hab : (q : ℤ) ∣ a - b) : phase ((a : ℝ) / q) = phase ((b : ℝ) / q) := by
  obtain ⟨t, ht⟩ := hab
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hreal : (a : ℝ) - b = q * (t : ℝ) := by exact_mod_cast ht
  have heq : (a : ℝ) / q = (b : ℝ) / q + t := by
    field_simp
    linarith
  rw [heq, phase_add, show phase (t : ℝ) = 1 from fourierChar_intCast t, mul_one]

/-- The arithmetic reciprocity identity which combines the completed-square
Gauss phase with the exact Fresnel phase. The new denominator is `d`. -/
lemma reciprocal_quadratic_phase {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (B v inv k : ℤ) (hB : (q : ℤ) ∣ (d : ℤ) * B + v)
    (hinv : (d : ℤ) ∣ (q : ℤ) * inv - 1) :
    phase (((-B * k ^ 2 : ℤ) : ℝ) / q) *
        phase (((-v * k ^ 2 : ℤ) : ℝ) / ((d * q : ℕ) : ℝ)) =
      phase (((-v * inv * k ^ 2 : ℤ) : ℝ) / d) := by
  obtain ⟨t, ht⟩ := hB
  have htdiv : (d : ℤ) ∣ (q : ℤ) * t - v := by
    refine ⟨B, ?_⟩
    linarith
  have h₁ := dvd_mul_of_dvd_right htdiv inv
  have h₂ := dvd_mul_of_dvd_right hinv t
  have hrem : (d : ℤ) ∣ t - v * inv := by
    rw [show t - v * inv = inv * ((q : ℤ) * t - v) - t * ((q : ℤ) * inv - 1) by ring]
    exact dvd_sub h₁ h₂
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hreal : (d : ℝ) * B + v = q * (t : ℝ) := by exact_mod_cast ht
  have heq : (((-B * k ^ 2 : ℤ) : ℝ) / q) +
      (((-v * k ^ 2 : ℤ) : ℝ) / ((d * q : ℕ) : ℝ)) =
        (((-t * k ^ 2 : ℤ) : ℝ) / d) := by
    push_cast
    field_simp
    linear_combination -(k : ℝ) ^ 2 * hreal
  rw [← phase_add, heq]
  apply phase_div_eq_of_dvd_sub hd
  rw [show (-t * k ^ 2) - (-v * inv * k ^ 2) = (t - v * inv) * (-(k ^ 2)) by ring]
  exact dvd_mul_of_dvd_left hrem (-(k ^ 2))

lemma intCast_eq_zero_of_modulus_dvd {q : ℕ} (z : ℤ) (hz : (q : ℤ) ∣ z) :
    (z : ZMod q) = 0 := by
  obtain ⟨t, rfl⟩ := hz
  simp only [Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

/-- Completed-square formula when an inverse of `4*a` is supplied. -/
lemma modularQuadraticGaussSum_inverse_four {q : ℕ} [NeZero q]
    (a B k : ZMod q) (hmod : 4 * a * B = 1) :
    modularQuadraticGaussSum a k =
      ZMod.stdAddChar (-(B * k ^ 2)) * modularQuadraticGaussSum a 0 := by
  have hlin : 2 * a * (2 * B * k) = k := by linear_combination k * hmod
  have hquad : a * (2 * B * k) ^ 2 = B * k ^ 2 := by linear_combination B * k ^ 2 * hmod
  have h := modularQuadraticGaussSum_complete_square a (2 * B * k)
  rwa [hlin, hquad] at h

/-- Completed-square formula for an even linear coefficient, requiring
only an inverse of the quadratic coefficient. -/
lemma modularQuadraticGaussSum_inverse_even {q : ℕ} [NeZero q]
    (a B k : ZMod q) (hmod : a * B = 1) :
    modularQuadraticGaussSum a (2 * k) =
      ZMod.stdAddChar (-(B * k ^ 2)) * modularQuadraticGaussSum a 0 := by
  have hlin : 2 * a * (B * k) = 2 * k := by linear_combination 2 * k * hmod
  have hquad : a * (B * k) ^ 2 = B * k ^ 2 := by linear_combination B * k ^ 2 * hmod
  have h := modularQuadraticGaussSum_complete_square a (B * k)
  rwa [hlin, hquad] at h

lemma stdAddChar_neg_mul_sq {q : ℕ} [NeZero q] (B k : ℤ) :
    ZMod.stdAddChar (-((B : ZMod q) * (k : ZMod q) ^ 2)) =
      phase (((-B * k ^ 2 : ℤ) : ℝ) / q) := by
  have hcast : (((-B * k ^ 2 : ℤ) : ZMod q)) = -((B : ZMod q) * (k : ZMod q) ^ 2) := by
    rw [Int.cast_mul, Int.cast_neg, Int.cast_pow, neg_mul]
  rw [← hcast]
  exact stdAddChar_intCast_eq_phase (q := q) (-B * k ^ 2)

lemma completeQuadraticGaussSum_complete_square {q : ℕ} (hq : 0 < q)
    (a B k : ℤ) (hB : (q : ℤ) ∣ 4 * a * B - 1) :
    completeQuadraticGaussSum q a k = completeQuadraticGaussSum q a 0 *
      phase (((-B * k ^ 2 : ℤ) : ℝ) / q) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hz := intCast_eq_zero_of_modulus_dvd (4 * a * B - 1) hB
  have hmod : (4 : ZMod q) * a * B = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hz
  have h := modularQuadraticGaussSum_inverse_four (a : ZMod q) (B : ZMod q) (k : ZMod q) hmod
  have hzero : modularQuadraticGaussSum (a : ZMod q) 0 = completeQuadraticGaussSum q a 0 := by
    simpa only [Int.cast_zero] using modularQuadraticGaussSum_eq_complete (q := q) a 0
  rw [modularQuadraticGaussSum_eq_complete (q := q) a k, hzero,
    stdAddChar_neg_mul_sq (q := q) B k] at h
  exact h.trans (mul_comm _ _)

lemma completeQuadraticGaussSum_even_linear {q : ℕ} (hq : 0 < q)
    (a B k : ℤ) (hB : (q : ℤ) ∣ a * B - 1) :
    completeQuadraticGaussSum q a (2 * k) = completeQuadraticGaussSum q a 0 *
      phase (((-B * k ^ 2 : ℤ) : ℝ) / q) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hz := intCast_eq_zero_of_modulus_dvd (a * B - 1) hB
  have hmod : (a : ZMod q) * B = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using hz
  have h := modularQuadraticGaussSum_inverse_even (a : ZMod q) (B : ZMod q) (k : ZMod q) hmod
  have hzero : modularQuadraticGaussSum (a : ZMod q) 0 = completeQuadraticGaussSum q a 0 := by
    simpa only [Int.cast_zero] using modularQuadraticGaussSum_eq_complete (q := q) a 0
  have hlinCast : (2 : ZMod q) * k = ((2 * k : ℤ) : ZMod q) := by push_cast; rfl
  rw [hlinCast, modularQuadraticGaussSum_eq_complete (q := q) a (2 * k), hzero,
    stdAddChar_neg_mul_sq (q := q) B k] at h
  exact h.trans (mul_comm _ _)

lemma modulus_dvd_inverse_combination {q : ℕ} (d b B v : ℤ)
    (hB : (q : ℤ) ∣ d * b * B - 1) (hbv : (q : ℤ) ∣ b * v + 1) :
    (q : ℤ) ∣ d * B + v := by
  rw [show d * B + v = (-v) * (d * b * B - 1) + (d * B) * (b * v + 1) by ring]
  exact dvd_add (dvd_mul_of_dvd_right hB (-v))
    (dvd_mul_of_dvd_right hbv (d * B))

/-- Odd-modulus reciprocity, with explicit inverses. Their existence forces
the needed coprimality and keeps the identity valid also for modulus one. -/
theorem gauss_fresnel_reciprocity_odd {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (b B v inv k : ℤ) (hB : (q : ℤ) ∣ 4 * (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * v + 1)
    (hinv : ((4 * r : ℕ) : ℤ) ∣ (q : ℤ) * inv - 1) :
    completeQuadraticGaussSum q ((r : ℤ) * b) k *
        phase (((-v * k ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)) =
      completeQuadraticGaussSum q ((r : ℤ) * b) 0 *
        phase (((-v * inv * k ^ 2 : ℤ) : ℝ) / ((4 * r : ℕ) : ℝ)) := by
  have hB' : (q : ℤ) ∣ 4 * ((r : ℤ) * b) * B - 1 := by
    simpa only [mul_assoc] using hB
  have hcomb : (q : ℤ) ∣ ((4 * r : ℕ) : ℤ) * B + v := by
    have h := modulus_dvd_inverse_combination (4 * (r : ℤ)) b B v hB hbv
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  rw [completeQuadraticGaussSum_complete_square hq _ B k hB', mul_assoc]
  congr 1
  exact reciprocal_quadratic_phase (by omega : 0 < 4 * r) hq B v inv k hcomb hinv

/-- Reciprocity for even linear terms. This is the nonzero branch when the
modulus is divisible by four. -/
theorem gauss_fresnel_reciprocity_even {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (b B v inv k : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * v + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    completeQuadraticGaussSum q ((r : ℤ) * b) (2 * k) *
        phase (((-v * k ^ 2 : ℤ) : ℝ) / ((r * q : ℕ) : ℝ)) =
      completeQuadraticGaussSum q ((r : ℤ) * b) 0 *
        phase (((-v * inv * k ^ 2 : ℤ) : ℝ) / (r : ℝ)) := by
  have hcomb := modulus_dvd_inverse_combination (r : ℤ) b B v hB hbv
  rw [completeQuadraticGaussSum_even_linear hq _ B k hB, mul_assoc]
  congr 1
  exact reciprocal_quadratic_phase hr hq B v inv k hcomb hinv

lemma modularQuadraticGaussSum_translate {q : ℕ} [NeZero q] (a k h : ZMod q) :
    modularQuadraticGaussSum a k =
      ZMod.stdAddChar (a * h ^ 2 + k * h) *
        modularQuadraticGaussSum a (k + 2 * a * h) := by
  unfold modularQuadraticGaussSum
  rw [Finset.mul_sum]
  have heq (x : ZMod q) :
      ZMod.stdAddChar (a * h ^ 2 + k * h) *
          ZMod.stdAddChar (a * x ^ 2 + (k + 2 * a * h) * x) =
        ZMod.stdAddChar (a * (h + x) ^ 2 + k * (h + x)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [heq]
  exact (Fintype.sum_equiv (Equiv.addLeft h) _ _ (fun x => rfl)).symm

lemma phase_half_eq_neg_one : phase (1 / 2) = -1 := by
  rw [phase, Real.fourierChar_apply]
  have h : (2 * Real.pi * (1 / 2) : ℝ) = Real.pi := by ring
  rw [h, Complex.exp_pi_mul_I]

lemma phase_odd_half {z : ℤ} (hz : Odd z) : phase ((z : ℝ) / 2) = -1 := by
  obtain ⟨t, ht⟩ := hz
  have heq : (z : ℝ) / 2 = (t : ℝ) + 1 / 2 := by rw [ht]; push_cast; ring
  rw [heq, phase_add, show phase (t : ℝ) = 1 from fourierChar_intCast t,
    one_mul, phase_half_eq_neg_one]

lemma half_modulus_gauss_phase {s : ℕ} [NeZero (2 * s)] (hs : 0 < s) (a k : ℤ) :
    ZMod.stdAddChar ((a : ZMod (2 * s)) * (s : ZMod (2 * s)) ^ 2 +
        (k : ZMod (2 * s)) * (s : ZMod (2 * s))) =
      phase (((a * (s : ℤ) + k : ℤ) : ℝ) / 2) := by
  have h := stdAddChar_intCast_eq_phase (q := 2 * s) (a * (s : ℤ) ^ 2 + k * (s : ℤ))
  rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_mul, Int.cast_natCast] at h
  rw [h]
  congr 1
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

/-- The half-period translation kills exactly the wrong-parity Gauss sums.
This covers both even-modulus branches without assuming primality. -/
theorem completeQuadraticGaussSum_zero_of_odd_parity {s : ℕ} (hs : 0 < s)
    (a k : ℤ) (hodd : Odd (a * (s : ℤ) + k)) :
    completeQuadraticGaussSum (2 * s) a k = 0 := by
  let : NeZero (2 * s) := ⟨by omega⟩
  have htwo : (2 : ZMod (2 * s)) * (s : ZMod (2 * s)) = 0 := by
    have h := CharP.cast_eq_zero (ZMod (2 * s)) (2 * s)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hlin : (2 : ZMod (2 * s)) * a * s = 0 := by
    rw [show (2 : ZMod (2 * s)) * a * s = a * (2 * s) by ring, htwo, mul_zero]
  have h := modularQuadraticGaussSum_translate (a : ZMod (2 * s)) k s
  rw [hlin, add_zero, half_modulus_gauss_phase hs, phase_odd_half hodd] at h
  rw [modularQuadraticGaussSum_eq_complete (q := 2 * s) a k] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Completed squares with a fixed parity representative. No inverse of two
is required, so this single formula works for every modulus. -/
lemma modularQuadraticGaussSum_fixed_parity {q : ℕ} [NeZero q]
    (a B j e : ZMod q) (hB : a * B = 1) :
    modularQuadraticGaussSum a (2 * j + e) =
      ZMod.stdAddChar (-(B * (j ^ 2 + e * j))) * modularQuadraticGaussSum a e := by
  have hlin : e + 2 * a * (B * j) = 2 * j + e := by
    linear_combination 2 * j * hB
  have hquad : a * (B * j) ^ 2 + e * (B * j) = B * (j ^ 2 + e * j) := by
    linear_combination B * j ^ 2 * hB
  have h := modularQuadraticGaussSum_translate a e (B * j)
  rw [hlin, hquad] at h
  rw [h, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

lemma stdAddChar_neg_mul_parity_polynomial {q : ℕ} [NeZero q] (B j e : ℤ) :
    ZMod.stdAddChar (-((B : ZMod q) * ((j : ZMod q) ^ 2 + (e : ZMod q) * (j : ZMod q)))) =
      phase (((-B * (j ^ 2 + e * j) : ℤ) : ℝ) / q) := by
  have hcast : (((-B * (j ^ 2 + e * j) : ℤ) : ZMod q)) =
      -((B : ZMod q) * ((j : ZMod q) ^ 2 + (e : ZMod q) * (j : ZMod q))) := by
    rw [Int.cast_mul, Int.cast_neg, Int.cast_add, Int.cast_pow, Int.cast_mul, neg_mul]
  rw [← hcast]
  exact stdAddChar_intCast_eq_phase (q := q) (-B * (j ^ 2 + e * j))

lemma completeQuadraticGaussSum_fixed_parity {q : ℕ} (hq : 0 < q)
    (a B j e : ℤ) (hB : (q : ℤ) ∣ a * B - 1) :
    completeQuadraticGaussSum q a (2 * j + e) = completeQuadraticGaussSum q a e *
      phase (((-B * (j ^ 2 + e * j) : ℤ) : ℝ) / q) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hz := intCast_eq_zero_of_modulus_dvd (a * B - 1) hB
  have hmod : (a : ZMod q) * B = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using hz
  have h := modularQuadraticGaussSum_fixed_parity
    (a : ZMod q) (B : ZMod q) (j : ZMod q) (e : ZMod q) hmod
  have hcast : (2 : ZMod q) * j + e = ((2 * j + e : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hcast, modularQuadraticGaussSum_eq_complete (q := q) a (2 * j + e),
    modularQuadraticGaussSum_eq_complete (q := q) a e,
    stdAddChar_neg_mul_parity_polynomial (q := q) B j e] at h
  exact h.trans (mul_comm _ _)

/-- Arithmetic reciprocity for an arbitrary integer phase numerator. -/
lemma reciprocal_polynomial_phase {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (B v inv n : ℤ) (hB : (q : ℤ) ∣ (d : ℤ) * B + v)
    (hinv : (d : ℤ) ∣ (q : ℤ) * inv - 1) :
    phase (((-B * n : ℤ) : ℝ) / q) *
        phase (((-v * n : ℤ) : ℝ) / ((d * q : ℕ) : ℝ)) =
      phase (((-v * inv * n : ℤ) : ℝ) / d) := by
  obtain ⟨t, ht⟩ := hB
  have htdiv : (d : ℤ) ∣ (q : ℤ) * t - v := by
    refine ⟨B, ?_⟩
    linarith
  have h₁ := dvd_mul_of_dvd_right htdiv inv
  have h₂ := dvd_mul_of_dvd_right hinv t
  have hrem : (d : ℤ) ∣ t - v * inv := by
    rw [show t - v * inv = inv * ((q : ℤ) * t - v) - t * ((q : ℤ) * inv - 1) by ring]
    exact dvd_sub h₁ h₂
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hreal : (d : ℝ) * B + v = q * (t : ℝ) := by exact_mod_cast ht
  have heq : (((-B * n : ℤ) : ℝ) / q) +
      (((-v * n : ℤ) : ℝ) / ((d * q : ℕ) : ℝ)) =
        (((-t * n : ℤ) : ℝ) / d) := by
    push_cast
    field_simp
    linear_combination -(n : ℝ) * hreal
  rw [← phase_add, heq]
  apply phase_div_eq_of_dvd_sub hd
  rw [show (-t * n) - (-v * inv * n) = (t - v * inv) * (-n) by ring]
  exact dvd_mul_of_dvd_left hrem (-n)

/-- Uniform Gauss--Fresnel reciprocity on either parity class (`e = 0, 1`).
Splitting the dual frequencies, rather than the modulus, avoids all exceptional
even-modulus formulas. The constant is the complete Gauss sum with linear
coefficient `e`; the remaining frequency has denominator `r`. -/
theorem gauss_fresnel_reciprocity_parity {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (b B v inv j e : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * v + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    completeQuadraticGaussSum q ((r : ℤ) * b) (2 * j + e) *
        phase (((-v * (2 * j + e) ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)) =
      (completeQuadraticGaussSum q ((r : ℤ) * b) e *
        phase (((-v * e ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ))) *
        phase (((-v * inv * (j ^ 2 + e * j) : ℤ) : ℝ) / (r : ℝ)) := by
  have hcomb := modulus_dvd_inverse_combination (r : ℤ) b B v hB hbv
  have hsplit : (((-v * (2 * j + e) ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)) =
      (((-v * (j ^ 2 + e * j) : ℤ) : ℝ) / ((r * q : ℕ) : ℝ)) +
        (((-v * e ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)) := by
    push_cast
    ring
  rw [completeQuadraticGaussSum_fixed_parity hq _ B j e hB, hsplit, phase_add]
  calc
    _ = (completeQuadraticGaussSum q ((r : ℤ) * b) e *
        phase (((-v * e ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ))) *
        (phase (((-B * (j ^ 2 + e * j) : ℤ) : ℝ) / q) *
        phase (((-v * (j ^ 2 + e * j) : ℤ) : ℝ) / ((r * q : ℕ) : ℝ))) := by ring
    _ = _ := by rw [reciprocal_polynomial_phase hr hq B v inv _ hcomb hinv]

end Erdos587
