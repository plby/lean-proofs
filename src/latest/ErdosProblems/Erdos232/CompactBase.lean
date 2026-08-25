import ErdosProblems.Erdos232.Optimized

open LeanCert.Core

namespace Erdos232

structure CompactCertificate where
  left : ℚ
  right : ℚ
  center : ℚ
  grid : Fin 27 → Fin 367
  point : Fin 27 → ℚ
  state : Fin 27 → IntervalRat × IntervalRat
  chunkTarget : Fin 5 → Fin 9 → IntervalRat
  coefficientTarget : Fin 5 → IntervalRat

def CompactCertificate.interval (C : CompactCertificate) : IntervalRat :=
  orderedInterval C.left C.right

def CompactCertificate.stateCheckAt (C : CompactCertificate) (j : ℕ) : Bool :=
  if h : j < 27 then
    besselStateSubset (besselStateAtRationalPoint (C.grid ⟨j, h⟩) 12 (C.point ⟨j, h⟩))
      (C.state ⟨j, h⟩)
  else true

def CompactCertificate.stateChecks (C : CompactCertificate) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => C.stateChecks start n && C.stateCheckAt (start + n)

theorem CompactCertificate.stateCheckAt_eq_true_of_stateChecks
    (C : CompactCertificate) (start n j : ℕ)
    (h : C.stateChecks start n = true) (hlo : start ≤ j) (hhi : j < start + n) :
    C.stateCheckAt j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [CompactCertificate.stateChecks, Bool.and_eq_true] at h
      by_cases hj : j = start + n
      · simpa [hj] using h.2
      · exact ih h.1 (by omega)

theorem CompactCertificate.statesValid_of_checks (C : CompactCertificate)
    (h0 : C.stateChecks 0 9 = true) (h1 : C.stateChecks 9 9 = true)
    (h2 : C.stateChecks 18 9 = true) :
    ∀ j, BesselStateValid (C.point j) (C.state j) := by
  intro j
  have hj : j.val < 27 := j.isLt
  have hc : C.stateCheckAt j.val = true := by
    by_cases h9 : j.val < 9
    · exact C.stateCheckAt_eq_true_of_stateChecks 0 9 j.val h0 (by omega) h9
    by_cases h18 : j.val < 18
    · exact C.stateCheckAt_eq_true_of_stateChecks 9 9 j.val h1 (by omega) h18
    · exact C.stateCheckAt_eq_true_of_stateChecks 18 9 j.val h2 (by omega) hj
  simp only [CompactCertificate.stateCheckAt, dif_pos hj] at hc
  exact BesselStateValid.mono hc (besselStateAtRationalPoint_valid (C.grid j) 12 (C.point j))

theorem CompactCertificate.statesValid_of_checks3 (C : CompactCertificate)
    (h0 : C.stateChecks 0 3 = true) (h1 : C.stateChecks 3 3 = true)
    (h2 : C.stateChecks 6 3 = true) (h3 : C.stateChecks 9 3 = true)
    (h4 : C.stateChecks 12 3 = true) (h5 : C.stateChecks 15 3 = true)
    (h6 : C.stateChecks 18 3 = true) (h7 : C.stateChecks 21 3 = true)
    (h8 : C.stateChecks 24 3 = true) :
    ∀ j, BesselStateValid (C.point j) (C.state j) := by
  intro j
  have hj : j.val < 27 := j.isLt
  have hc : C.stateCheckAt j.val = true := by
    by_cases h3' : j.val < 3
    · exact C.stateCheckAt_eq_true_of_stateChecks 0 3 j.val h0 (by omega) h3'
    by_cases h6' : j.val < 6
    · exact C.stateCheckAt_eq_true_of_stateChecks 3 3 j.val h1 (by omega) h6'
    by_cases h9' : j.val < 9
    · exact C.stateCheckAt_eq_true_of_stateChecks 6 3 j.val h2 (by omega) h9'
    by_cases h12' : j.val < 12
    · exact C.stateCheckAt_eq_true_of_stateChecks 9 3 j.val h3 (by omega) h12'
    by_cases h15' : j.val < 15
    · exact C.stateCheckAt_eq_true_of_stateChecks 12 3 j.val h4 (by omega) h15'
    by_cases h18' : j.val < 18
    · exact C.stateCheckAt_eq_true_of_stateChecks 15 3 j.val h5 (by omega) h18'
    by_cases h21' : j.val < 21
    · exact C.stateCheckAt_eq_true_of_stateChecks 18 3 j.val h6 (by omega) h21'
    by_cases h24' : j.val < 24
    · exact C.stateCheckAt_eq_true_of_stateChecks 21 3 j.val h7 (by omega) h24'
    · exact C.stateCheckAt_eq_true_of_stateChecks 24 3 j.val h8 (by omega) hj
  simp only [CompactCertificate.stateCheckAt, dif_pos hj] at hc
  exact BesselStateValid.mono hc (besselStateAtRationalPoint_valid (C.grid j) 12 (C.point j))

theorem CompactCertificate.statesValid_of_allChecks (C : CompactCertificate)
    (h : C.stateChecks 0 27 = true) :
    ∀ j, BesselStateValid (C.point j) (C.state j) := by
  intro j
  have hc := C.stateCheckAt_eq_true_of_stateChecks 0 27 j.val h (Nat.zero_le _) j.isLt
  simp only [CompactCertificate.stateCheckAt, dif_pos j.isLt] at hc
  exact BesselStateValid.mono hc (besselStateAtRationalPoint_valid (C.grid j) 12 (C.point j))

def intervalFinSumHull (n : ℕ) (F : Fin n → IntervalRat) : IntervalRat where
  lo := ∑ j, (F j).lo
  hi := ∑ j, (F j).hi
  le := Finset.sum_le_sum fun _ _ => IntervalRat.le _

theorem mem_intervalFinSumHull {n : ℕ} {x : Fin n → ℝ} {F : Fin n → IntervalRat}
    (hx : ∀ i, x i ∈ F i) : (∑ i, x i) ∈ intervalFinSumHull n F := by
  constructor
  · have h : ∑ i : Fin n, ((F i).lo : ℝ) ≤ ∑ i, x i :=
      Finset.sum_le_sum fun i _ => (hx i).1
    simpa [intervalFinSumHull] using h
  · have h : ∑ i, x i ≤ ∑ i : Fin n, ((F i).hi : ℝ) :=
      Finset.sum_le_sum fun i _ => (hx i).2
    simpa [intervalFinSumHull] using h

def coefficientBlockIndex (b : Fin 9) (k : Fin 3) : Fin 27 :=
  ⟨3 * b.val + k.val, by omega⟩

theorem sum_fin27_blocks {R : Type*} [CommRing R] (f : Fin 27 → R) :
    (∑ j, f j) = ∑ b : Fin 9, ∑ k : Fin 3, f (coefficientBlockIndex b k) := by
  simp [Fin.sum_univ_succ, coefficientBlockIndex]
  ring

def CompactCertificate.coefficientTerm (C : CompactCertificate) (r : ℕ)
    (j : Fin 27) : IntervalRat :=
    let Y := IntervalRat.scale C.center (dualDistanceInterval j)
    IntervalRat.scale (dualWeight j) <| IntervalRat.mul (intervalPow (dualDistanceInterval j) r) <|
      besselDerivativeNearFromState (C.point j) r Y (C.state j)

def CompactCertificate.coefficientChunk (C : CompactCertificate) (r : ℕ)
    (b : Fin 9) : IntervalRat :=
  intervalFinSumHull 3 fun k => C.coefficientTerm r (coefficientBlockIndex b k)

def CompactCertificate.coefficient (C : CompactCertificate) (r : ℕ) : IntervalRat :=
  intervalFinSumHull 27 (C.coefficientTerm r)

def CompactCertificate.chunkCheck (C : CompactCertificate) (r : Fin 5) (b : Fin 9) : Bool :=
  rationalIntervalSubset (C.coefficientChunk r b) (C.chunkTarget r b)

def CompactCertificate.chunkCheckAt (C : CompactCertificate) (r : Fin 5) (j : ℕ) : Bool :=
  if h : j < 9 then C.chunkCheck r ⟨j, h⟩ else true

def CompactCertificate.chunkChecks (C : CompactCertificate) (r : Fin 5) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => C.chunkChecks r start n && C.chunkCheckAt r (start + n)

theorem CompactCertificate.chunkCheckAt_eq_true_of_chunkChecks
    (C : CompactCertificate) (r : Fin 5) (start n j : ℕ)
    (h : C.chunkChecks r start n = true) (hlo : start ≤ j) (hhi : j < start + n) :
    C.chunkCheckAt r j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [CompactCertificate.chunkChecks, Bool.and_eq_true] at h
      by_cases hj : j = start + n
      · simpa [hj] using h.2
      · exact ih h.1 (by omega)

theorem CompactCertificate.chunkChecks_all (C : CompactCertificate)
    (h : ∀ r : Fin 5, C.chunkChecks r 0 9 = true) :
    ∀ r : Fin 5, ∀ b, C.chunkCheck r b = true := by
  intro r b
  have hc := C.chunkCheckAt_eq_true_of_chunkChecks r 0 9 b.val (h r) (Nat.zero_le _) b.isLt
  simpa [CompactCertificate.chunkCheckAt, b.isLt] using hc

theorem CompactCertificate.chunkChecks_nine_of_three (C : CompactCertificate) (r : Fin 5)
    (h0 : C.chunkChecks r 0 3 = true) (h1 : C.chunkChecks r 3 3 = true)
    (h2 : C.chunkChecks r 6 3 = true) : C.chunkChecks r 0 9 = true := by
  simp only [CompactCertificate.chunkChecks, Bool.and_eq_true] at h0 h1 h2 ⊢
  aesop

theorem CompactCertificate.coefficientTerm_mem (C : CompactCertificate)
    (hstate : ∀ j, BesselStateValid (C.point j) (C.state j)) (r : ℕ) (j : Fin 27) :
    (dualWeight j : ℝ) * dualDistance j ^ r *
      besselDerivative r ((C.center : ℝ) * dualDistance j) ∈ C.coefficientTerm r j := by
  have hd := dualDistance_mem j
  have hpow := IntervalRat.mem_pow hd r
  have harg := IntervalRat.mem_scale C.center hd
  have hb := mem_besselDerivativeNearFromState (C.point j) r _ (C.state j)
    (hstate j) harg
  simpa [CompactCertificate.coefficientTerm, mul_assoc] using
    IntervalRat.mem_scale (dualWeight j) (IntervalRat.mem_mul hpow hb)

theorem CompactCertificate.chunkTarget_mem (C : CompactCertificate)
    (hstate : ∀ j, BesselStateValid (C.point j) (C.state j))
    (hcheck : ∀ r : Fin 5, ∀ b, C.chunkCheck r b = true) (r : Fin 5) (b : Fin 9) :
    (∑ k : Fin 3, (dualWeight (coefficientBlockIndex b k) : ℝ) *
      dualDistance (coefficientBlockIndex b k) ^ (r : ℕ) *
      besselDerivative r ((C.center : ℝ) * dualDistance (coefficientBlockIndex b k))) ∈
        C.chunkTarget r b := by
  have hm := mem_intervalFinSumHull fun k =>
    C.coefficientTerm_mem hstate (r : ℕ) (coefficientBlockIndex b k)
  exact mem_of_rationalIntervalSubset (hcheck r b) hm

def CompactCertificate.coefficientCheck (C : CompactCertificate) (r : Fin 5) : Bool :=
  rationalIntervalSubset (intervalFinSumHull 9 (C.chunkTarget r)) (C.coefficientTarget r)

def CompactCertificate.coefficientTargetNat (C : CompactCertificate) (r : ℕ) : IntervalRat :=
  if h : r < 5 then C.coefficientTarget ⟨r, h⟩ else C.coefficient r

theorem CompactCertificate.coefficientTargetNat_mem (C : CompactCertificate)
    (hstate : ∀ j, BesselStateValid (C.point j) (C.state j))
    (hchunk : ∀ r : Fin 5, ∀ b, C.chunkCheck r b = true)
    (hcheck : ∀ r : Fin 5, C.coefficientCheck r = true) (r : ℕ) :
    (∑ j, (dualWeight j : ℝ) * dualDistance j ^ r *
      besselDerivative r ((C.center : ℝ) * dualDistance j)) ∈ C.coefficientTargetNat r := by
  by_cases hr : r < 5
  · have hc : rationalIntervalSubset (intervalFinSumHull 9 (C.chunkTarget ⟨r, hr⟩))
        (C.coefficientTarget ⟨r, hr⟩) = true := by
      simpa [CompactCertificate.coefficientCheck] using hcheck ⟨r, hr⟩
    have hm0 := mem_intervalFinSumHull fun b => C.chunkTarget_mem hstate hchunk ⟨r, hr⟩ b
    have hm : (∑ j, (dualWeight j : ℝ) * dualDistance j ^ r *
        besselDerivative r ((C.center : ℝ) * dualDistance j)) ∈ C.coefficientTarget ⟨r, hr⟩ := by
      rw [sum_fin27_blocks]
      exact mem_of_rationalIntervalSubset hc hm0
    simpa [CompactCertificate.coefficientCheck, CompactCertificate.coefficientTargetNat, hr] using hm
  · simpa [CompactCertificate.coefficientTargetNat, CompactCertificate.coefficient, hr] using
      mem_intervalFinSumHull fun j => C.coefficientTerm_mem hstate r j

def remainderTerm4 (j : Fin 27) : ℚ :=
  |dualWeight j| * intervalMaxAbs (dualDistanceInterval j) ^ 5

def remainderBlock4 (b : Fin 9) : ℚ :=
  ∑ k : Fin 3, remainderTerm4 (coefficientBlockIndex b k)

def remainderBlockBound4 (b : Fin 9) : ℚ :=
  match b.val with
  | 0 => 54 / 100
  | 1 => 68 / 100
  | 2 => 110 / 100
  | 3 => 1918 / 100
  | 4 => 168 / 100
  | 5 => 82 / 100
  | 6 => 21 / 100
  | 7 => 13 / 100
  | _ => 237 / 100

private theorem remainderBlock4_0 : remainderBlock4 0 ≤ remainderBlockBound4 0 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_1 : remainderBlock4 1 ≤ remainderBlockBound4 1 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_2 : remainderBlock4 2 ≤ remainderBlockBound4 2 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_3 : remainderBlock4 3 ≤ remainderBlockBound4 3 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_4 : remainderBlock4 4 ≤ remainderBlockBound4 4 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_5 : remainderBlock4 5 ≤ remainderBlockBound4 5 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_6 : remainderBlock4 6 ≤ remainderBlockBound4 6 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_7 : remainderBlock4 7 ≤ remainderBlockBound4 7 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

private theorem remainderBlock4_8 : remainderBlock4 8 ≤ remainderBlockBound4 8 := by
  norm_num [remainderBlock4, remainderTerm4, coefficientBlockIndex, Fin.sum_univ_succ,
    dualWeight, dualDistanceInterval, intervalMaxAbs, orderedInterval, remainderBlockBound4]

theorem remainderBlock4_le (b : Fin 9) : remainderBlock4 b ≤ remainderBlockBound4 b := by
  fin_cases b
  · exact remainderBlock4_0
  · exact remainderBlock4_1
  · exact remainderBlock4_2
  · exact remainderBlock4_3
  · exact remainderBlock4_4
  · exact remainderBlock4_5
  · exact remainderBlock4_6
  · exact remainderBlock4_7
  · exact remainderBlock4_8

theorem combinedRemainderConstant_four_le :
    combinedRemainderConstant dualWeight dualDistanceInterval 4 ≤ 27 := by
  rw [combinedRemainderConstant]
  change (∑ j, remainderTerm4 j) ≤ 27
  rw [sum_fin27_blocks]
  change (∑ b, remainderBlock4 b) ≤ 27
  exact (Finset.sum_le_sum fun b _ => remainderBlock4_le b).trans (by
    norm_num [remainderBlockBound4, Fin.sum_univ_succ])

def CompactCertificate.output (C : CompactCertificate) : IntervalRat :=
  let H := intervalSub C.interval (IntervalRat.singleton C.center)
  let P := IntervalRat.add (IntervalRat.singleton dualConstant) <|
    intervalTaylorSum C.coefficientTargetNat H 5
  widenInterval
    (27 *
      intervalMaxAbs H ^ 5 / (5 : ℕ).factorial) P

theorem CompactCertificate.output_mem (C : CompactCertificate)
    (hstate : ∀ j, BesselStateValid (C.point j) (C.state j))
    (hchunk : ∀ r : Fin 5, ∀ b, C.chunkCheck r b = true)
    (hcheck : ∀ r : Fin 5, C.coefficientCheck r = true)
    {t : ℝ} (ht : t ∈ C.interval) :
    (dualConstant : ℝ) + spectralSum dualWeight dualDistance t ∈ C.output := by
  let H := intervalSub C.interval (IntervalRat.singleton C.center)
  have hm : (C.center : ℝ) ∈ IntervalRat.singleton C.center := IntervalRat.mem_singleton _
  have hh : t - (C.center : ℝ) ∈ H := IntervalRat.mem_sub ht hm
  have hpoly0 := mem_intervalTaylorSum (C.coefficientTargetNat_mem hstate hchunk hcheck) hh 5
  have hpoly : (dualConstant : ℝ) +
      spectralTaylorValue dualWeight dualDistance C.center 4 t ∈
      IntervalRat.add (IntervalRat.singleton dualConstant)
        (intervalTaylorSum C.coefficientTargetNat H 5) := by
    apply IntervalRat.mem_add (IntervalRat.mem_singleton _)
    simpa [spectralTaylorValue] using hpoly0
  apply mem_widenInterval hpoly
  have hb := spectralTaylor_bound dualWeight dualDistanceInterval dualDistance dualDistance_mem
    (C.center : ℝ) t 4
  have hmabs := abs_le_intervalMaxAbs hh
  have hpow := (pow_le_pow_left₀ (abs_nonneg _) hmabs) 5
  have hC : 0 ≤ (combinedRemainderConstant dualWeight dualDistanceInterval 4 : ℝ) :=
    Rat.cast_nonneg.mpr (combinedRemainderConstant_nonneg _ _ _)
  have hCle : (combinedRemainderConstant dualWeight dualDistanceInterval 4 : ℝ) ≤ 27 :=
    Rat.cast_le.mpr combinedRemainderConstant_four_le
  have he : |((dualConstant : ℝ) + spectralSum dualWeight dualDistance t) -
      ((dualConstant : ℝ) + spectralTaylorValue dualWeight dualDistance C.center 4 t)| ≤
      ((27 * intervalMaxAbs H ^ 5 / (5 : ℕ).factorial : ℚ) : ℝ) := by
    rw [add_sub_add_left_eq_sub]
    push_cast
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul hCle hpow (pow_nonneg (abs_nonneg _) _) (by norm_num)) (by norm_num))
  change |((dualConstant : ℝ) + spectralSum dualWeight dualDistance t) -
      ((dualConstant : ℝ) + spectralTaylorValue dualWeight dualDistance C.center 4 t)| ≤
    |((27 *
      intervalMaxAbs H ^ 5 / (5 : ℕ).factorial : ℚ) : ℝ)|
  have herrQ : 0 ≤ (27 : ℚ) * intervalMaxAbs H ^ 5 /
      ((5 : ℕ).factorial : ℚ) := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg ((abs_nonneg _).trans (le_max_left _ _)) _)) (by positivity)
  have herrAbs : |((27 *
      intervalMaxAbs H ^ 5 / (5 : ℕ).factorial : ℚ) : ℝ)| =
      ((27 *
        intervalMaxAbs H ^ 5 / (5 : ℕ).factorial : ℚ) : ℝ) :=
    abs_of_nonneg (Rat.cast_nonneg.mpr herrQ)
  rw [herrAbs]
  exact he

theorem CompactCertificate.proves (C : CompactCertificate)
    (hstate : ∀ j, BesselStateValid (C.point j) (C.state j))
    (hchunk : ∀ r : Fin 5, ∀ b, C.chunkCheck r b = true)
    (hcheck : ∀ r : Fin 5, C.coefficientCheck r = true)
    (hlower : (1 : ℚ) ≤ C.output.lo) {t : ℝ} (ht : t ∈ C.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  have hm := C.output_mem hstate hchunk hcheck ht
  have h := (Rat.cast_le.mpr hlower).trans hm.1
  norm_num at h ⊢
  exact h

end Erdos232
