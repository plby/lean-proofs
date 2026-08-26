import ErdosProblems.Erdos67b.EulerResidue

/-!
# Shifting a residue-class Dirichlet series

This file formalizes the deterministic shift estimate used in Tao's
equation (15).  Absolute convergence holds for an arbitrary complex
exponent in the half-plane `re s > 1`.  The uniform `O(m)` comparison is
stated for a real exponent, as in Tao's application (`s = 1 + 1 / log X`).
This restriction is essential: with unbounded imaginary part the change of
phase between `n ^ (-s)` and `(n+m) ^ (-s)` has no uniform `O(m)` bound.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67b.ShiftedResidueSeries

noncomputable section

open EulerResidue

/-- The summand obtained by translating the coefficient, but not the
Dirichlet weight, by `m`. -/
def shiftedResidueSummand {r : ℕ} (h : ℕ →*₀ ℂ) (a : ZMod r)
    (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if (n : ZMod r) = a then h (n + m) * (n : ℂ) ^ (-s) else 0

/-- The shifted residue-class series in Tao's equation (15). -/
def shiftedResidueSeries {r : ℕ} (h : ℕ →*₀ ℂ) (a : ZMod r)
    (m : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, shiftedResidueSummand h a m s n

/-- The ordinary (unshifted) residue-class summand. -/
def residueSeriesSummand {r : ℕ} (h : ℕ →*₀ ℂ) (a : ZMod r)
    (s : ℂ) (n : ℕ) : ℂ :=
  if (n : ZMod r) = a then h n * (n : ℂ) ^ (-s) else 0

/-- Absolute convergence of the shifted series throughout `re s > 1`. -/
theorem shiftedResidueSummable {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (a : ZMod r) (m : ℕ) {s : ℂ}
    (hs : 1 < s.re) : Summable (shiftedResidueSummand h a m s) := by
  rw [← summable_norm_iff]
  apply (summable_riemannZetaSummand hs).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro n
  unfold shiftedResidueSummand
  split_ifs
  · rcases eq_or_ne (n + m) 0 with hzero | hne
    · simp [hzero]
    · rw [norm_mul, hh hne]
      simp [riemannZetaSummandHom]
  · simp

/-- Absolute convergence of the raw summands defining `residueLSeries`. -/
theorem residueSeriesSummable {r : ℕ} {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (a : ZMod r) {s : ℂ} (hs : 1 < s.re) :
    Summable (residueSeriesSummand h a s) := by
  rw [← summable_norm_iff]
  apply (summable_riemannZetaSummand hs).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro n
  unfold residueSeriesSummand
  split_ifs
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [norm_mul, hh hn]
      simp [riemannZetaSummandHom]
  · simp

/-- The raw residue summand agrees termwise with Mathlib's `LSeries.term`.
Keeping this lemma explicit makes the subsequent tail reindexing
independent of implementation details of `LSeries`. -/
theorem residueLSeries_eq_tsum {r : ℕ} (h : ℕ →*₀ ℂ)
    (a : ZMod r) (s : ℂ) :
    residueLSeries h a s = ∑' n : ℕ, residueSeriesSummand h a s n := by
  unfold residueLSeries LSeries
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, residueSeriesSummand]
  · simp [LSeries.term_of_ne_zero hn, residueCoefficient, residueSeriesSummand, div_eq_mul_inv,
      Complex.cpow_neg]

/-- Translating a natural number translates its residue class. -/
lemma cast_add_eq_add_iff {r n m : ℕ} {a : ZMod r} :
    ((n + m : ℕ) : ZMod r) = a + (m : ZMod r) ↔ (n : ZMod r) = a := by
  rw [Nat.cast_add]
  exact add_right_cancel_iff

/-- The positive real `p`-series weight.  We use the convention supplied by
`Real.rpow`, so its value at zero is zero for the negative exponents below. -/
def realDirichletWeight (u : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-u)

lemma summable_realDirichletWeight {u : ℝ} (hu : 1 < u) :
    Summable (realDirichletWeight u) := by
  unfold realDirichletWeight
  simpa [Real.rpow_neg (Nat.cast_nonneg _)] using
    (Real.summable_nat_rpow_inv.mpr hu)

lemma realDirichletWeight_nonneg (u : ℝ) (n : ℕ) :
    0 ≤ realDirichletWeight u n := by
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma realDirichletWeight_add_le {u : ℝ} (hu : 1 < u)
    {n m : ℕ} (hn : 0 < n) :
    realDirichletWeight u (n + m) ≤ realDirichletWeight u n := by
  unfold realDirichletWeight
  exact Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hn)
    (by exact_mod_cast Nat.le_add_right n m)
    (neg_nonpos.mpr (zero_le_one.trans hu.le))

lemma norm_cpow_sub_shift_eq_weight_sub {u : ℝ} (hu : 1 < u)
    {n m : ℕ} (hn : 0 < n) :
    ‖(n : ℂ) ^ (-(u : ℂ)) - ((n + m : ℕ) : ℂ) ^ (-(u : ℂ))‖ =
      realDirichletWeight u n - realDirichletWeight u (n + m) := by
  have hexp : -(u : ℂ) = ((-u : ℝ) : ℂ) := by simp
  rw [hexp]
  rw [← Complex.ofReal_natCast n, ← Complex.ofReal_natCast (n + m)]
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg n) (-u),
    ← Complex.ofReal_cpow (Nat.cast_nonneg (n + m)) (-u)]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  change |realDirichletWeight u n - realDirichletWeight u (n + m)| = _
  rw [abs_of_nonneg (sub_nonneg.mpr (realDirichletWeight_add_le hu hn))]

lemma shiftedResidueSummand_zero {r : ℕ} {h : ℕ →*₀ ℂ}
    (a : ZMod r) {u : ℝ} (hu : 1 < u) {m : ℕ} :
    shiftedResidueSummand h a m (u : ℂ) 0 = 0 := by
  have hu0 : -(u : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hu)))
  simp [shiftedResidueSummand, hu0]

lemma residueSeriesSummand_zero {r : ℕ} (h : ℕ →*₀ ℂ)
    (a : ZMod r) {u : ℝ} (_hu : 1 < u) :
    residueSeriesSummand h a (u : ℂ) 0 = 0 := by
  unfold residueSeriesSummand
  split_ifs
  · simp
  · rfl

/-- After discarding the zero term, the norm of the termwise shift error is
bounded by the telescoping real `p`-series difference. -/
lemma norm_shiftedSucc_sub_residueShift_le {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (a : ZMod r)
    (m n : ℕ) {u : ℝ} (hu : 1 < u) :
    ‖shiftedResidueSummand h a m (u : ℂ) (n + 1) -
        residueSeriesSummand h (a + (m : ZMod r)) (u : ℂ) (n + 1 + m)‖ ≤
      realDirichletWeight u (n + 1) -
        realDirichletWeight u (n + 1 + m) := by
  unfold shiftedResidueSummand residueSeriesSummand
  have hcast : ((n + 1 + m : ℕ) : ZMod r) = a + (m : ZMod r) ↔
      ((n + 1 : ℕ) : ZMod r) = a := by
    simpa only [Nat.add_assoc] using
      (cast_add_eq_add_iff (r := r) (n := n + 1) (m := m) (a := a))
  rcases em (((n + 1 : ℕ) : ZMod r) = a) with ha | ha
  · rw [if_pos ha, if_pos (hcast.mpr ha), ← mul_sub, norm_mul,
      hh (by omega : n + 1 + m ≠ 0),
      norm_cpow_sub_shift_eq_weight_sub hu (by omega : 0 < n + 1), one_mul]
  · rw [if_neg ha, if_neg (not_congr hcast |>.mpr ha)]
    simp only [sub_zero, norm_zero]
    exact sub_nonneg.mpr (realDirichletWeight_add_le hu (by omega))

lemma summable_norm_shiftedSucc_sub_residueShift {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (a : ZMod r)
    (m : ℕ) {u : ℝ} (hu : 1 < u) :
    Summable (fun n : ℕ ↦
      ‖shiftedResidueSummand h a m (u : ℂ) (n + 1) -
        residueSeriesSummand h (a + (m : ZMod r)) (u : ℂ) (n + 1 + m)‖) := by
  have hw : Summable (realDirichletWeight u) := summable_realDirichletWeight hu
  have hw1 : Summable (fun n : ℕ ↦ realDirichletWeight u (n + 1)) :=
    (summable_nat_add_iff 1).mpr hw
  have hwm : Summable (fun n : ℕ ↦ realDirichletWeight u (n + 1 + m)) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ((summable_nat_add_iff m).mpr hw1)
  exact (hw1.sub hwm).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_shiftedSucc_sub_residueShift_le hh a m n hu)

/-- The total tail discrepancy is at most `m`; the proof is the exact
telescoping identity for the summable real `p`-series. -/
theorem norm_tsum_shiftedSucc_sub_residueShift_le {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (a : ZMod r)
    (m : ℕ) {u : ℝ} (hu : 1 < u) :
    ‖(∑' n : ℕ, shiftedResidueSummand h a m (u : ℂ) (n + 1)) -
        ∑' n : ℕ,
          residueSeriesSummand h (a + (m : ZMod r)) (u : ℂ) (n + 1 + m)‖
      ≤ (m : ℝ) := by
  let A : ℕ → ℂ := fun n ↦ shiftedResidueSummand h a m (u : ℂ) (n + 1)
  let B : ℕ → ℂ := fun n ↦
    residueSeriesSummand h (a + (m : ZMod r)) (u : ℂ) (n + 1 + m)
  let W : ℕ → ℝ := fun n ↦ realDirichletWeight u (n + 1)
  have hA : Summable A := by
    exact (summable_nat_add_iff 1).mpr (shiftedResidueSummable hh a m
      (s := (u : ℂ)) (by simpa using hu))
  have hB : Summable B := by
    have hraw := residueSeriesSummable hh (a + (m : ZMod r))
      (s := (u : ℂ)) (by simpa using hu)
    have htail := (summable_nat_add_iff (m + 1)).mpr hraw
    simpa [B, Nat.add_assoc, Nat.add_comm m 1] using htail
  have hnorm : Summable (fun n ↦ ‖A n - B n‖) := by
    simpa [A, B] using summable_norm_shiftedSucc_sub_residueShift hh a m hu
  calc
    ‖(∑' n, A n) - ∑' n, B n‖ = ‖∑' n, (A n - B n)‖ := by rw [hA.tsum_sub hB]
    _ ≤ ∑' n, ‖A n - B n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, (W n - W (n + m)) := by
      apply Summable.tsum_le_tsum
      · intro n
        simpa [A, B, W, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (norm_shiftedSucc_sub_residueShift_le hh a m n hu)
      · exact hnorm
      · have hW : Summable W := by
          exact (summable_nat_add_iff 1).mpr (summable_realDirichletWeight hu)
        exact hW.sub ((summable_nat_add_iff m).mpr hW)
    _ = ∑ n ∈ Finset.range m, W n := by
      have hW : Summable W := by
        exact (summable_nat_add_iff 1).mpr (summable_realDirichletWeight hu)
      rw [hW.tsum_sub ((summable_nat_add_iff m).mpr hW)]
      linarith [hW.sum_add_tsum_nat_add m]
    _ ≤ ∑ _n ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
        (neg_nonpos.mpr (zero_le_one.trans hu.le))
    _ = (m : ℝ) := by simp

/-- The omitted initial segment of the target residue series has norm at
most `m`.  The zero term vanishes, leaving exactly `m` potentially nonzero
terms. -/
theorem norm_sum_initial_residueSeries_le {r : ℕ}
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (b : ZMod r)
    (m : ℕ) {u : ℝ} (hu : 1 < u) :
    ‖∑ n ∈ Finset.range (m + 1), residueSeriesSummand h b (u : ℂ) n‖ ≤
      (m : ℝ) := by
  rw [Finset.sum_range_succ']
  rw [residueSeriesSummand_zero h b hu, add_zero]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ n ∈ Finset.range m, ‖residueSeriesSummand h b (u : ℂ) (n + 1)‖ ≤
        ∑ _n ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      unfold residueSeriesSummand
      split_ifs
      · rw [norm_mul, hh (by omega : n + 1 ≠ 0), one_mul,
          Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1)]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
          (neg_nonpos.mpr (zero_le_one.trans hu.le))
      · simp
    _ = (m : ℝ) := by simp

/-- Tao's deterministic shifted-series estimate (equation (15)).  The
constant is completely uniform in the modulus, residue class, completely
multiplicative coefficient, and real exponent `u > 1`.

The two contributions are transparent in the proof: at most `m` from the
telescoping change of Dirichlet weights, and at most `m` from the omitted
initial segment. -/
theorem norm_shiftedResidueSeries_sub_residueLSeries_le_two_mul
    {r : ℕ} {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) (a : ZMod r)
    (m : ℕ) {u : ℝ} (hu : 1 < u) :
    ‖shiftedResidueSeries h a m (u : ℂ) -
        residueLSeries h (a + (m : ZMod r)) (u : ℂ)‖ ≤
      2 * (m : ℝ) := by
  let F : ℕ → ℂ := fun n ↦
    residueSeriesSummand h (a + (m : ZMod r)) (u : ℂ) n
  let S : ℂ := ∑' n : ℕ, shiftedResidueSummand h a m (u : ℂ) (n + 1)
  let T : ℂ := ∑' n : ℕ, F (n + 1 + m)
  let I : ℂ := ∑ n ∈ Finset.range (m + 1), F n
  have hsummableShift : Summable (shiftedResidueSummand h a m (u : ℂ)) :=
    shiftedResidueSummable hh a m (by simpa using hu)
  have hshift : shiftedResidueSeries h a m (u : ℂ) = S := by
    rw [shiftedResidueSeries, hsummableShift.tsum_eq_zero_add,
      shiftedResidueSummand_zero a hu, zero_add]
  have hsummableF : Summable F := by
    exact residueSeriesSummable hh (a + (m : ZMod r))
      (s := (u : ℂ)) (by simpa using hu)
  have htarget : residueLSeries h (a + (m : ZMod r)) (u : ℂ) = I + T := by
    rw [residueLSeries_eq_tsum]
    change (∑' n, F n) = I + T
    symm
    simpa [I, T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (hsummableF.sum_add_tsum_nat_add (m + 1))
  have htail : ‖S - T‖ ≤ (m : ℝ) := by
    simpa [S, T, F] using
      (norm_tsum_shiftedSucc_sub_residueShift_le hh a m hu)
  have hinitial : ‖I‖ ≤ (m : ℝ) := by
    simpa [I, F] using
      (norm_sum_initial_residueSeries_le hh (a + (m : ZMod r)) m hu)
  rw [hshift, htarget]
  calc
    ‖S - (I + T)‖ = ‖(S - T) - I‖ := by ring_nf
    _ ≤ ‖S - T‖ + ‖I‖ := norm_sub_le _ _
    _ ≤ (m : ℝ) + (m : ℝ) := add_le_add htail hinitial
    _ = 2 * (m : ℝ) := by ring

end

end Erdos67b.ShiftedResidueSeries
