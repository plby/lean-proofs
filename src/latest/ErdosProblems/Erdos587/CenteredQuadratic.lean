import ErdosProblems.Erdos587.GaussReciprocity
import ErdosProblems.Erdos587.CorrectedWeyl
import ErdosProblems.Erdos587.ReciprocalWeyl

/-!
# Centering quadratic sums over the reduced period

Deleting complete periods before differencing leaves at most one nonzero
difference with zero phase. This removes the composite-modulus divisor loss
from the mean of the centered error.
-/

open scoped BigOperators

namespace Erdos587

open External.Erdos438.QuadraticWeyl

lemma periodic_nat_multiple (f : ℕ → ℂ) (q : ℕ) (hper : ∀ n, f (n + q) = f n)
    (n k : ℕ) : f (n + k * q) = f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← add_assoc, hper]
    exact ih

lemma sum_range_periodic_multiple (f : ℕ → ℂ) (q : ℕ)
    (hper : ∀ n, f (n + q) = f n) (k : ℕ) :
    (∑ n ∈ Finset.range (k * q), f n) = (k : ℂ) * ∑ n ∈ Finset.range q, f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hshift : (∑ n ∈ Finset.range q, f (k * q + n)) = ∑ n ∈ Finset.range q, f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [add_comm, periodic_nat_multiple f q hper]
    rw [hshift, Nat.cast_add, Nat.cast_one]
    ring

lemma sum_range_periodic_decomposition (f : ℕ → ℂ) (q N : ℕ)
    (hper : ∀ n, f (n + q) = f n) :
    (∑ n ∈ Finset.range N, f n) =
      ((N / q : ℕ) : ℂ) * (∑ n ∈ Finset.range q, f n) +
        ∑ n ∈ Finset.range (N % q), f n := by
  have hN : N = (N / q) * q + N % q := by nlinarith [Nat.mod_add_div N q]
  calc
    _ = (∑ n ∈ Finset.range ((N / q) * q), f n) +
        ∑ n ∈ Finset.range (N % q), f ((N / q) * q + n) := by
      conv_lhs => rw [hN]
      exact Finset.sum_range_add f _ _
    _ = _ := by
      rw [sum_range_periodic_multiple f q hper]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [add_comm, periodic_nat_multiple f q hper]

lemma centered_periodic_sum_eq_remainder (f : ℕ → ℂ) {q : ℕ} (hq : 0 < q) (N : ℕ)
    (hper : ∀ n, f (n + q) = f n) (G : ℂ) (hG : ∑ n ∈ Finset.range q, f n = G) :
    (∑ n ∈ Finset.range N, f n) - ((N : ℂ) / q) * G =
      (∑ n ∈ Finset.range (N % q), f n) - (((N % q : ℕ) : ℂ) / q) * G := by
  rw [sum_range_periodic_decomposition f q N hper, hG]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNnat : N = (N / q) * q + N % q := by nlinarith [Nat.mod_add_div N q]
  have hN : (N : ℂ) = ((N / q : ℕ) : ℂ) * q + ((N % q : ℕ) : ℂ) := by exact_mod_cast hNnat
  rw [hN]
  field_simp
  ring

noncomputable def exactQuadraticInterval (q : ℕ) (a s : ℤ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.range L, quadraticResiduePhase q a (s + n)

noncomputable def centeredQuadraticInterval (q : ℕ) (a s : ℤ) (L : ℕ) : ℂ :=
  exactQuadraticInterval q a s L - ((L : ℂ) / q) * completeQuadraticGaussSum q a 0

lemma quadraticResiduePhase_add_period {q : ℕ} (hq : 0 < q) (a z : ℤ) :
    quadraticResiduePhase q a (z + q) = quadraticResiduePhase q a z := by
  unfold quadraticResiduePhase
  apply phase_div_eq_of_dvd_sub hq
  refine ⟨a * (2 * z + q), ?_⟩
  ring

lemma completeQuadraticGaussSum_even_translate {q : ℕ} (hq : 0 < q) (a s : ℤ) :
    completeQuadraticGaussSum q a (2 * a * s) =
      phase (((-a * s ^ 2 : ℤ) : ℝ) / q) * completeQuadraticGaussSum q a 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  have h := modularQuadraticGaussSum_complete_square (a : ZMod q) (s : ZMod q)
  have hcast : (2 : ZMod q) * a * s = ((2 * a * s : ℤ) : ZMod q) := by push_cast; rfl
  have hzero : modularQuadraticGaussSum (a : ZMod q) 0 = completeQuadraticGaussSum q a 0 := by
    simpa only [Int.cast_zero] using modularQuadraticGaussSum_eq_complete (q := q) a 0
  rw [hcast, modularQuadraticGaussSum_eq_complete, hzero, stdAddChar_neg_mul_sq] at h
  exact h

lemma exactQuadraticInterval_period {q : ℕ} (hq : 0 < q) (a s : ℤ) :
    exactQuadraticInterval q a s q = completeQuadraticGaussSum q a 0 := by
  have hphase (n : ℕ) : quadraticResiduePhase q a (s + n) =
      phase (((a * s ^ 2 : ℤ) : ℝ) / q) *
        phase (((a * (n : ℤ) ^ 2 + (2 * a * s) * (n : ℤ) : ℤ) : ℝ) / q) := by
    rw [quadraticResiduePhase, ← phase_add]
    congr 1
    push_cast
    ring
  unfold exactQuadraticInterval
  simp_rw [hphase]
  rw [← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  change phase (((a * s ^ 2 : ℤ) : ℝ) / q) * completeQuadraticGaussSum q a (2 * a * s) = _
  rw [completeQuadraticGaussSum_even_translate hq, ← mul_assoc, ← phase_add]
  have heq : (((a * s ^ 2 : ℤ) : ℝ) / q) + (((-a * s ^ 2 : ℤ) : ℝ) / q) = 0 := by
    push_cast
    ring
  rw [heq, phase_zero, one_mul]

lemma centeredQuadraticInterval_eq_remainder {q : ℕ} (hq : 0 < q) (a s : ℤ) (L : ℕ) :
    centeredQuadraticInterval q a s L = centeredQuadraticInterval q a s (L % q) := by
  apply centered_periodic_sum_eq_remainder (fun n => quadraticResiduePhase q a (s + n)) hq L
  · intro n
    rw [Nat.cast_add, show s + ((n : ℤ) + (q : ℤ)) = s + n + q by ring]
    exact quadraticResiduePhase_add_period hq a (s + n)
  · exact exactQuadraticInterval_period hq a s

lemma norm_exactQuadraticInterval (q a : ℕ) (s : ℤ) (L : ℕ) :
    ‖exactQuadraticInterval q (a : ℤ) s L‖ =
      ‖quadraticSum ((a : ℝ) / q) (2 * ((a : ℝ) / q) * s) L‖ := by
  have heq : exactQuadraticInterval q (a : ℤ) s L =
      ∑ n ∈ Finset.range L, phase (((a : ℝ) / q) * ((s : ℝ) + n) ^ 2 + 0 * ((s : ℝ) + n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    unfold quadraticResiduePhase
    congr 1
    push_cast
    ring
  rw [heq, norm_shifted_quadraticSum]
  simp only [zero_add]

lemma residueDistance_zero_unique_of_lt {q a h : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (hh : 0 < h) (hhq : h < q) (hzero : residueDistance a q h = 0) : 2 * h = q := by
  have hmodlt : (2 * a * h) % q < q := Nat.mod_lt _ hq
  have hmodzero : (2 * a * h) % q = 0 := by
    unfold residueDistance at hzero
    omega
  have hdvd : q ∣ a * (2 * h) := by
    rw [show a * (2 * h) = 2 * a * h by ring]
    exact Nat.dvd_of_mod_eq_zero hmodzero
  have htwo : q ∣ 2 * h := ha.symm.dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := htwo
  have htpos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    rw [ht0, mul_zero] at ht
    omega
  have htlt : t < 2 := by
    by_contra hnot
    have hmul := Nat.mul_le_mul_left q (show 2 ≤ t by omega)
    omega
  have ht1 : t = 1 := by omega
  simpa only [ht1, mul_one] using ht

lemma card_zero_residue_differences_le_one {q a R : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (hR : R < q) :
    ((Finset.Icc 1 R).filter (fun h => residueDistance a q h = 0)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have hxI := Finset.mem_Icc.mp hx'.1
  have hyI := Finset.mem_Icc.mp hy'.1
  have hxeq := residueDistance_zero_unique_of_lt hq ha hxI.1 (hxI.2.trans_lt hR) hx'.2
  have hyeq := residueDistance_zero_unique_of_lt hq ha hyI.1 (hyI.2.trans_lt hR) hy'.2
  omega

lemma rationalMajorant_zero_cutoff_nonneg (a q h : ℕ) : 0 ≤ rationalMajorant a q 0 h := by
  unfold rationalMajorant
  split_ifs <;> positivity

/-- At a length shorter than the primitive period, the entire zero-residue
contribution to differencing is at most one copy of the length. -/
lemma sum_rationalMajorant_short_period_le {q a R : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (hR : R < q) :
    (∑ h ∈ Finset.Icc 1 R, rationalMajorant a q R h) ≤
      R + ∑ h ∈ Finset.Icc 1 R, rationalMajorant a q 0 h := by
  classical
  have heq (h : ℕ) : rationalMajorant a q R h =
      (if residueDistance a q h = 0 then (R : ℝ) else 0) + rationalMajorant a q 0 h := by
    unfold rationalMajorant
    split_ifs <;> simp
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  apply add_le_add _ le_rfl
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_zero_residue_differences_le_one hq ha hR
  have hcardR : ((((Finset.Icc 1 R).filter (fun h => residueDistance a q h = 0)).card : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcardR (Nat.cast_nonneg R)

lemma norm_primitive_period_mean_sq_le {q a R : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (hR : R ≤ q) :
    ‖((R : ℂ) / q) * completeQuadraticGaussSum q (a : ℤ) 0‖ ^ 2 ≤ 2 * R := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hRR : (R : ℝ) ≤ q := by exact_mod_cast hR
  have hu : IsUnit ((a : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime a q).mpr ha
  have hgauss := norm_completeQuadraticGaussSum_le_sqrt hq (a : ℤ) 0 hu
  have hnorm : ‖((R : ℂ) / q) * completeQuadraticGaussSum q (a : ℤ) 0‖ ≤
      ((R : ℝ) / q) * Real.sqrt (2 * q) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hgauss (by positivity)
  calc
    _ ≤ (((R : ℝ) / q) * Real.sqrt (2 * q)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = 2 * (R : ℝ) ^ 2 / q := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]
      field_simp
    _ ≤ 2 * (R : ℝ) := by
      apply (div_le_iff₀ hqR).mpr
      nlinarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]

lemma norm_sub_sq_le_twice_sq (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc
    _ ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The centered pointwise Weyl bound for a primitive period. Its majorant
has zero cutoff: the complete-period resonance is absent. -/
theorem norm_centeredQuadraticInterval_sq_le_primitive {q a : ℕ} (hq : 0 < q)
    (ha : a.Coprime q) (s : ℤ) (L : ℕ) :
    ‖centeredQuadraticInterval q (a : ℤ) s L‖ ^ 2 ≤
      10 * L + 4 * ∑ h ∈ Finset.Icc 1 L, rationalMajorant a q 0 h := by
  let R := L % q
  have hRq : R < q := Nat.mod_lt L hq
  have hRL : R ≤ L := Nat.mod_le L q
  have hraw : ‖exactQuadraticInterval q (a : ℤ) s R‖ ^ 2 ≤
      R + 2 * ∑ h ∈ Finset.Icc 1 R, rationalMajorant a q R h := by
    rw [norm_exactQuadraticInterval]
    simpa only [mul_one] using norm_quadraticSum_rational_mul_sq_le_majorants
      a q R 1 (2 * ((a : ℝ) / q) * s) hq
  have hshort := sum_rationalMajorant_short_period_le hq ha hRq
  have hext : (∑ h ∈ Finset.Icc 1 R, rationalMajorant a q 0 h) ≤
      ∑ h ∈ Finset.Icc 1 L, rationalMajorant a q 0 h := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro h hh
      have hh' := Finset.mem_Icc.mp hh
      exact Finset.mem_Icc.mpr ⟨hh'.1, hh'.2.trans hRL⟩
    · intro h hh hnot
      exact rationalMajorant_zero_cutoff_nonneg a q h
  have hRreal : (R : ℝ) ≤ L := by exact_mod_cast hRL
  have hsum : ‖exactQuadraticInterval q (a : ℤ) s R‖ ^ 2 ≤
      3 * L + 2 * ∑ h ∈ Finset.Icc 1 L, rationalMajorant a q 0 h := by linarith
  have hmean := norm_primitive_period_mean_sq_le hq ha hRq.le
  rw [centeredQuadraticInterval_eq_remainder hq]
  change ‖exactQuadraticInterval q (a : ℤ) s R -
    ((R : ℂ) / q) * completeQuadraticGaussSum q (a : ℤ) 0‖ ^ 2 ≤ _
  apply (norm_sub_sq_le_twice_sq _ _).trans
  linarith

lemma residueDistance_mul (d a q h : ℕ) :
    residueDistance (d * a) (d * q) h = d * residueDistance a q h := by
  unfold residueDistance
  rw [show 2 * (d * a) * h = d * (2 * a * h) by ring, Nat.mul_mod_mul_left,
    ← Nat.mul_sub_left_distrib, ← mul_min]

lemma rationalMajorant_zero_cutoff_mul {d : ℕ} (hd : 0 < d) (a q h : ℕ) :
    rationalMajorant (d * a) (d * q) 0 h = rationalMajorant a q 0 h := by
  unfold rationalMajorant
  rw [residueDistance_mul]
  by_cases hdist : residueDistance a q h = 0
  · simp [hdist]
  · rw [if_neg (mul_ne_zero hd.ne' hdist), if_neg hdist]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    exact mul_div_mul_left _ _ hdR

lemma exactQuadraticInterval_mul {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (a s : ℤ) (L : ℕ) :
    exactQuadraticInterval (d * q) ((d : ℤ) * a) s L = exactQuadraticInterval q a s L := by
  unfold exactQuadraticInterval
  apply Finset.sum_congr rfl
  intro n hn
  unfold quadraticResiduePhase
  congr 1
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

lemma completeQuadraticGaussSum_mul {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (a : ℤ) :
    completeQuadraticGaussSum (d * q) ((d : ℤ) * a) 0 =
      (d : ℂ) * completeQuadraticGaussSum q a 0 := by
  calc
    _ = exactQuadraticInterval (d * q) ((d : ℤ) * a) 0 (d * q) :=
      (exactQuadraticInterval_period (Nat.mul_pos hd hq) _ 0).symm
    _ = exactQuadraticInterval q a 0 (d * q) := exactQuadraticInterval_mul hd hq a 0 (d * q)
    _ = (d : ℂ) * exactQuadraticInterval q a 0 q := by
      apply sum_range_periodic_multiple
      intro n
      simp only [Nat.cast_add, zero_add]
      exact quadraticResiduePhase_add_period hq a (n : ℤ)
    _ = _ := by rw [exactQuadraticInterval_period hq]

lemma centeredQuadraticInterval_mul {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (a s : ℤ) (L : ℕ) :
    centeredQuadraticInterval (d * q) ((d : ℤ) * a) s L = centeredQuadraticInterval q a s L := by
  unfold centeredQuadraticInterval
  rw [exactQuadraticInterval_mul hd hq, completeQuadraticGaussSum_mul hd hq]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

/-- The centered pointwise estimate is uniform in the numerator's gcd with
the modulus. Reducing the period changes neither the centered sum nor its
nonzero-residue majorant. -/
theorem norm_centeredQuadraticInterval_sq_le {q : ℕ} (hq : 0 < q) (a : ℕ) (s : ℤ) (L : ℕ) :
    ‖centeredQuadraticInterval q (a : ℤ) s L‖ ^ 2 ≤
      10 * L + 4 * ∑ h ∈ Finset.Icc 1 L, rationalMajorant a q 0 h := by
  let d := a.gcd q
  let a' := a / d
  let q' := q / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right a hq
  have hq' : 0 < q' := Nat.div_pos (Nat.gcd_le_right a hq) hd
  have ha' : a'.Coprime q' := Nat.coprime_div_gcd_div_gcd hd
  have hqa : d * q' = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)
  have haa : d * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)
  have h := norm_centeredQuadraticInterval_sq_le_primitive hq' ha' s L
  have hcenter : centeredQuadraticInterval q (a : ℤ) s L =
      centeredQuadraticInterval q' (a' : ℤ) s L := by
    rw [← hqa, ← haa, Nat.cast_mul]
    exact centeredQuadraticInterval_mul hd hq' (a' : ℤ) s L
  have hmajor (i : ℕ) : rationalMajorant a q 0 i = rationalMajorant a' q' 0 i := by
    rw [← haa, ← hqa]
    exact rationalMajorant_zero_cutoff_mul hd a' q' i
  rw [hcenter]
  simp_rw [hmajor]
  exact h

end Erdos587
