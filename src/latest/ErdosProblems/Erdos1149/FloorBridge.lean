/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Floor and divisibility bridges for Erdős Problem 1149

This file turns the divisibility condition on `⌊n ^ α⌋` into the
fractional-part condition used in the analytic part of the proof.  It also
records the exact finite reindexing `n = d * m`.
-/

namespace Erdos1149

/-- For a nonnegative real, the integer floor and the natural floor have the
same value after coercion to `ℝ`. -/
lemma intFloor_cast_eq_natFloor_cast (x : ℝ) (hx : 0 ≤ x) :
    (⌊x⌋ : ℝ) = (⌊x⌋₊ : ℝ) := by
  exact_mod_cast (Int.natCast_floor_eq_floor hx).symm

/-- In particular, the natural floor of a nonnegative real power is the
integer floor, after the canonical cast to `ℤ`. -/
lemma natCast_natFloor_rpow_eq_intFloor (n : ℕ) (α : ℝ) :
    ((⌊Real.rpow (n : ℝ) α⌋₊ : ℕ) : ℤ) =
      ⌊Real.rpow (n : ℝ) α⌋ := by
  exact Int.natCast_floor_eq_floor
    (Real.rpow_nonneg (Nat.cast_nonneg n) α)

/-- The exact interval test for divisibility of a natural floor.  The
strictness of the right endpoint distinguishes remainder zero from all
positive remainders. -/
lemma dvd_natFloor_iff_fract_div_lt (x : ℝ) (hx : 0 ≤ x)
    (d : ℕ) (hd : 0 < d) :
    d ∣ ⌊x⌋₊ ↔ Int.fract (x / (d : ℝ)) < (d : ℝ)⁻¹ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hxdiv : 0 ≤ x / (d : ℝ) := div_nonneg hx hdR.le
  have hfloorDiv : (⌊x / (d : ℝ)⌋ : ℝ) = (⌊x⌋₊ / d : ℕ) := by
    rw [intFloor_cast_eq_natFloor_cast _ hxdiv]
    rw [Nat.floor_div_natCast]
  rw [← Int.self_sub_floor (x / (d : ℝ)), hfloorDiv]
  constructor
  · intro hdiv
    have hq : ⌊x⌋₊ / d * d = ⌊x⌋₊ := Nat.div_mul_cancel hdiv
    have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    rw [← hq] at hlt
    push_cast at hlt
    rw [inv_eq_one_div]
    apply (sub_lt_iff_lt_add).2
    apply (div_lt_iff₀ hdR).2
    rw [add_mul, div_mul_cancel₀ _ hdR.ne']
    simpa [mul_comm, add_comm] using hlt
  · intro hfract
    rw [inv_eq_one_div] at hfract
    have hlt : x < ((⌊x⌋₊ / d : ℕ) : ℝ) * d + 1 := by
      have h := (sub_lt_iff_lt_add).1 hfract
      have h := (div_lt_iff₀ hdR).1 h
      rw [add_mul, div_mul_cancel₀ _ hdR.ne'] at h
      simpa [add_comm] using h
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
    have hnatlt : ⌊x⌋₊ < ⌊x⌋₊ / d * d + 1 := by
      exact_mod_cast (lt_of_le_of_lt hfloor_le hlt)
    have hle : ⌊x⌋₊ ≤ ⌊x⌋₊ / d * d := by omega
    have heq : ⌊x⌋₊ / d * d = ⌊x⌋₊ :=
      Nat.le_antisymm (Nat.div_mul_le_self _ _) hle
    exact (Nat.dvd_iff_div_mul_eq _ _).2 heq

/-- Exact normalization of the phase after writing `n = d * m`. -/
lemma rpow_mul_div_nat (d m : ℕ) (hd : 0 < d) (α : ℝ) :
    Real.rpow ((d * m : ℕ) : ℝ) α / (d : ℝ) =
      Real.rpow (d : ℝ) (α - 1) * Real.rpow (m : ℝ) α := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmul : Real.rpow ((d : ℝ) * (m : ℝ)) α =
      Real.rpow (d : ℝ) α * Real.rpow (m : ℝ) α := by
    simpa only [Real.rpow_eq_pow] using
      Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg m) (z := α)
  have hsub : Real.rpow (d : ℝ) (α - 1) =
      Real.rpow (d : ℝ) α / (d : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_sub hdR α 1
  calc
    Real.rpow ((d * m : ℕ) : ℝ) α / (d : ℝ) =
        Real.rpow ((d : ℝ) * (m : ℝ)) α / (d : ℝ) := by norm_num
    _ = (Real.rpow (d : ℝ) α * Real.rpow (m : ℝ) α) / (d : ℝ) := by
      rw [hmul]
    _ = (Real.rpow (d : ℝ) α / (d : ℝ)) * Real.rpow (m : ℝ) α := by
      ring
    _ = Real.rpow (d : ℝ) (α - 1) * Real.rpow (m : ℝ) α := by
      rw [hsub]

/-- The monomial form of `dvd_natFloor_iff_fract_div_lt` after the
substitution `n = d * m`. -/
lemma dvd_natFloor_rpow_mul_iff_fract (d m : ℕ) (hd : 0 < d) (α : ℝ) :
    d ∣ ⌊Real.rpow ((d * m : ℕ) : ℝ) α⌋₊ ↔
      Int.fract
          (Real.rpow (d : ℝ) (α - 1) * Real.rpow (m : ℝ) α) <
        (d : ℝ)⁻¹ := by
  apply (dvd_natFloor_iff_fract_div_lt _
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) d hd).trans
  have harg := rpow_mul_div_nat d m hd α
  have hfract : Int.fract (((d * m : ℕ) : ℝ) ^ α / (d : ℝ)) =
      Int.fract ((d : ℝ) ^ (α - 1) * (m : ℝ) ^ α) := by
    simpa only [Real.rpow_eq_pow] using congrArg Int.fract harg
  rw [hfract]
  simp only [Real.rpow_eq_pow]

/-- Cardinality-preserving finite reindexing of multiples `n = d * m` in a
zero-based prefix.  Keeping `m` in `range N` gives a convenient common
ambient finite set; the sharper condition is the explicit inequality
`d * m < N`. -/
lemma card_filter_dvd_reindex_mul (P : ℕ → Prop) [DecidablePred P]
    (N d : ℕ) (hd : 0 < d) :
    ((Finset.range N).filter fun n ↦ d ∣ n ∧ P n).card =
      ((Finset.range N).filter fun m ↦ d * m < N ∧ P (d * m)).card := by
  let T := (Finset.range N).filter fun m ↦ d * m < N ∧ P (d * m)
  have hfinset :
      (Finset.range N).filter (fun n ↦ d ∣ n ∧ P n) =
        T.image (fun m ↦ d * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hnN, hdn, hPn⟩
      refine ⟨n / d, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Finset.mem_range]
        have hn_div_le : n / d ≤ n := Nat.div_le_self n d
        have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
        refine ⟨hn_div_le.trans_lt hnN, ?_, ?_⟩
        · rw [hmul]
          exact hnN
        · rw [hmul]
          exact hPn
      · exact Nat.mul_div_cancel' hdn
    · rintro ⟨m, hmT, rfl⟩
      have hm : m < N ∧ d * m < N ∧ P (d * m) := by
        simpa only [T, Finset.mem_filter, Finset.mem_range] using hmT
      exact ⟨hm.2.1, Nat.dvd_mul_right d m, hm.2.2⟩
  rw [hfinset]
  exact (Finset.card_image_iff.mpr fun a ha b hb hab ↦
    Nat.eq_of_mul_eq_mul_left hd hab)

/-- The full finite local-divisor count for Erdős 1149, reindexed as the
fractional-part count to which discrepancy estimates apply. -/
lemma card_localGcd_rpow_reindex (N d : ℕ) (hd : 0 < d) (α : ℝ) :
    ((Finset.range N).filter fun n ↦
      0 < n ∧ d ∣ Nat.gcd n ⌊Real.rpow (n : ℝ) α⌋₊).card =
    ((Finset.range N).filter fun m ↦
      0 < m ∧ d * m < N ∧
        Int.fract
            (Real.rpow (d : ℝ) (α - 1) * Real.rpow (m : ℝ) α) <
          (d : ℝ)⁻¹).card := by
  have hleft :
      (Finset.range N).filter (fun n ↦
        0 < n ∧ d ∣ Nat.gcd n ⌊Real.rpow (n : ℝ) α⌋₊) =
      (Finset.range N).filter (fun n ↦
        d ∣ n ∧ (0 < n ∧ d ∣ ⌊Real.rpow (n : ℝ) α⌋₊)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Nat.dvd_gcd_iff]
    tauto
  rw [hleft, card_filter_dvd_reindex_mul
    (fun n ↦ 0 < n ∧ d ∣ ⌊Real.rpow (n : ℝ) α⌋₊) N d hd]
  apply congrArg Finset.card
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [dvd_natFloor_rpow_mul_iff_fract d m hd α]
  have hmulpos : 0 < d * m ↔ 0 < m := by
    constructor
    · intro h
      have hm : m ≠ 0 := by
        intro hm
        subst m
        simp at h
      exact Nat.pos_of_ne_zero hm
    · exact fun hm ↦ mul_pos hd hm
  rw [hmulpos]
  tauto

end Erdos1149
