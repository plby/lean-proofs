import ErdosProblems.Erdos520.HarperRestrictedVerticalSet
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-!
# Dyadic decomposition of the central Rademacher shell

At height `|t|` the Rademacher Gaussian comparison must discard a number of
early prime blocks proportional to `log (1 / |t|)`.  Dyadic bands expose the
compensating length `2^-d`; the finite weighted geometric bounds below make
the total cost uniform.
-/

/-- Radius of the `d`-th nested central interval.  Thus radius zero is
`1/2`, the edge of the central unit shell. -/
noncomputable def harperDyadicRadius (d : Nat) : Real :=
  1 / (2 : Real) ^ (d + 1)

/-- One signed dyadic annulus between consecutive radii. -/
noncomputable def harperSignedDyadicBand
    (positive : Bool) (d : Nat) : Set Real :=
  if positive then Ioc (harperDyadicRadius (d + 1)) (harperDyadicRadius d)
  else Ico (-harperDyadicRadius d) (-harperDyadicRadius (d + 1))

theorem measurableSet_harperSignedDyadicBand
    (positive : Bool) (d : Nat) :
    MeasurableSet (harperSignedDyadicBand positive d) := by
  cases positive <;> simp [harperSignedDyadicBand]

theorem harperDyadicRadius_pos (d : Nat) :
    0 < harperDyadicRadius d := by
  unfold harperDyadicRadius
  positivity

theorem harperDyadicRadius_succ (d : Nat) :
    harperDyadicRadius (d + 1) = harperDyadicRadius d / 2 := by
  unfold harperDyadicRadius
  rw [pow_succ]
  ring

theorem harperDyadicRadius_succ_le (d : Nat) :
    harperDyadicRadius (d + 1) ≤ harperDyadicRadius d := by
  rw [harperDyadicRadius_succ]
  have h := harperDyadicRadius_pos d
  linarith

/-- Each signed band has exactly the next dyadic radius as its length. -/
theorem volume_real_harperSignedDyadicBand
    (positive : Bool) (d : Nat) :
    volume.real (harperSignedDyadicBand positive d) =
      harperDyadicRadius (d + 1) := by
  cases positive with
  | false =>
      simp only [harperSignedDyadicBand, Bool.false_eq_true, if_false,
        Measure.real, Real.volume_Ico]
      rw [ENNReal.toReal_ofReal]
      rw [harperDyadicRadius_succ]
      ring
      have h := harperDyadicRadius_succ_le d
      linarith
  | true =>
      simp only [harperSignedDyadicBand, if_true, Measure.real,
        Real.volume_Ioc]
      rw [ENNReal.toReal_ofReal]
      rw [harperDyadicRadius_succ]
      ring
      exact sub_nonneg.mpr (harperDyadicRadius_succ_le d)

theorem harperSignedDyadicBand_finite
    (positive : Bool) (d : Nat) :
    volume (harperSignedDyadicBand positive d) ≠ ∞ := by
  cases positive <;>
    simp [harperSignedDyadicBand, Real.volume_Ioc, Real.volume_Ico]

/-- The unresolved interval after the first `m` signed dyadic bands. -/
noncomputable def harperDyadicCore (m : Nat) : Set Real :=
  Icc (-harperDyadicRadius m) (harperDyadicRadius m)

theorem measurableSet_harperDyadicCore (m : Nat) :
    MeasurableSet (harperDyadicCore m) := by
  exact measurableSet_Icc

theorem harperDyadicCore_finite (m : Nat) :
    volume (harperDyadicCore m) ≠ ∞ := by
  simp [harperDyadicCore, Real.volume_Icc]

theorem volume_real_harperDyadicCore (m : Nat) :
    volume.real (harperDyadicCore m) = 2 * harperDyadicRadius m := by
  simp only [harperDyadicCore, Measure.real, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal]
  · ring
  · have h := harperDyadicRadius_pos m
    linarith

/-- The unresolved central core has exactly dyadic length `2^-m`. -/
theorem volume_real_harperDyadicCore_eq_inv_two_pow (m : Nat) :
    volume.real (harperDyadicCore m) = 1 / (2 : Real) ^ m := by
  rw [volume_real_harperDyadicCore]
  unfold harperDyadicRadius
  rw [pow_succ]
  ring

/-- Stopping at the binary ceiling logarithm leaves a core of length at
most `1 / n`.  The stronger `clog n` cutoff makes the final Jensen remainder
harmless. -/
theorem volume_real_harperDyadicCore_clog_le_inv
    {n : Nat} (hn : 1 ≤ n) :
    volume.real (harperDyadicCore (Nat.clog 2 n)) ≤ 1 / (n : Real) := by
  rw [volume_real_harperDyadicCore_eq_inv_two_pow]
  have hnPowNat : n ≤ 2 ^ Nat.clog 2 n :=
    Nat.le_pow_clog (by norm_num) n
  have hnPowReal : (n : Real) ≤ (2 : Real) ^ Nat.clog 2 n := by
    exact_mod_cast hnPowNat
  exact one_div_le_one_div_of_le (by exact_mod_cast hn) hnPowReal

/-- Refining the unresolved core by one scale gives exactly the two next
signed bands and the next core, with the half-open conventions assigning
every boundary once. -/
theorem harperDyadicCore_split (d : Nat) :
    harperDyadicCore d =
      harperSignedDyadicBand false d ∪
        harperDyadicCore (d + 1) ∪
          harperSignedDyadicBand true d := by
  ext t
  simp only [harperDyadicCore, harperSignedDyadicBand,
    Bool.false_eq_true, if_false, if_true,
    Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_union]
  rw [harperDyadicRadius_succ]
  have hr := harperDyadicRadius_pos d
  constructor
  · intro ht
    by_cases hleft : t < -(harperDyadicRadius d / 2)
    · exact Or.inl (Or.inl ⟨ht.1, hleft⟩)
    · by_cases hright : t ≤ harperDyadicRadius d / 2
      · exact Or.inl (Or.inr ⟨by linarith, hright⟩)
      · exact Or.inr ⟨by linarith, ht.2⟩
  · rintro ((ht | ht) | ht)
    · exact ⟨ht.1, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, ht.2⟩

/-- Union of both signed bands at the first `m` dyadic scales. -/
noncomputable def harperDyadicBandUnion (m : Nat) : Set Real :=
  ⋃ d ∈ Finset.range m,
    (harperSignedDyadicBand false d ∪
      harperSignedDyadicBand true d)

theorem measurableSet_harperDyadicBandUnion (m : Nat) :
    MeasurableSet (harperDyadicBandUnion m) := by
  unfold harperDyadicBandUnion
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun _hd =>
    (measurableSet_harperSignedDyadicBand false d).union
      (measurableSet_harperSignedDyadicBand true d)

@[simp] theorem mem_harperDyadicBandUnion
    {m : Nat} {t : Real} :
    t ∈ harperDyadicBandUnion m ↔
      ∃ d : Nat, d < m ∧
        (t ∈ harperSignedDyadicBand false d ∨
          t ∈ harperSignedDyadicBand true d) := by
  simp [harperDyadicBandUnion]

/-- The finite bands together with the final core cover exactly the central
half-unit interval, at every stopping depth. -/
theorem harperDyadicCore_union_bandUnion (m : Nat) :
    harperDyadicCore m ∪ harperDyadicBandUnion m =
      harperDyadicCore 0 := by
  induction m with
  | zero => simp [harperDyadicBandUnion]
  | succ m ih =>
      ext t
      have hsplit := Set.ext_iff.mp (harperDyadicCore_split m) t
      have hih := Set.ext_iff.mp ih t
      simp only [Set.mem_union, mem_harperDyadicBandUnion] at hsplit hih ⊢
      constructor
      · rintro (hcore | ⟨d, hd, hband⟩)
        · apply hih.mp
          left
          apply hsplit.mpr
          exact Or.inl (Or.inr hcore)
        · by_cases hdm : d < m
          · apply hih.mp
            exact Or.inr ⟨d, hdm, hband⟩
          · have hdeq : d = m := by omega
            subst d
            apply hih.mp
            left
            apply hsplit.mpr
            rcases hband with hneg | hpos
            · exact Or.inl (Or.inl hneg)
            · exact Or.inr hpos
      · intro hcore0
        rcases hih.mpr hcore0 with hcore | ⟨d, hd, hband⟩
        · rcases hsplit.mp hcore with (hneg | hsmall) | hpos
          · exact Or.inr ⟨m, by omega, Or.inl hneg⟩
          · exact Or.inl hsmall
          · exact Or.inr ⟨m, by omega, Or.inr hpos⟩
        · exact Or.inr ⟨d, by omega, hband⟩

/-- The two signs together cost exactly `2^(-d-1)` in vertical length. -/
theorem two_mul_volume_real_harperSignedDyadicBand
    (d : Nat) :
    2 * volume.real (harperSignedDyadicBand true d) =
      1 / (2 : Real) ^ (d + 1) := by
  rw [volume_real_harperSignedDyadicBand]
  unfold harperDyadicRadius
  rw [pow_succ]
  ring

/-- Finite geometric mass, in the normalization naturally supplied by the
two signed bands. -/
theorem sum_range_inv_two_pow_le_two (m : Nat) :
    (∑ d ∈ Finset.range m, (1 / 2 : Real) ^ d) ≤ 2 := by
  exact sum_le_hasSum (Finset.range m)
    (fun d _hd => by positivity) hasSum_geometric_two

/-- The logarithmic start-shift cost is summable against dyadic length. -/
theorem sum_range_nat_mul_inv_two_pow_le_two (m : Nat) :
    (∑ d ∈ Finset.range m, (d : Real) * (1 / 2 : Real) ^ d) ≤ 2 := by
  have hsum : HasSum
      (fun d : Nat => (d : Real) * (1 / 2 : Real) ^ d) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one
      (r := (1 / 2 : Real)) (by norm_num) using 1 <;> norm_num
  exact sum_le_hasSum (Finset.range m)
    (fun d _hd => mul_nonneg (Nat.cast_nonneg d) (by positivity)) hsum

/-- Uniform finite bound for any affine dyadic-band cost. -/
theorem sum_range_add_mul_inv_two_pow_le
    (m : Nat) {C : Real} (hC : 0 ≤ C) :
    (∑ d ∈ Finset.range m,
      ((d : Real) + C) * (1 / 2 : Real) ^ d) ≤ 2 + 2 * C := by
  calc
    (∑ d ∈ Finset.range m,
        ((d : Real) + C) * (1 / 2 : Real) ^ d) =
        (∑ d ∈ Finset.range m,
          (d : Real) * (1 / 2 : Real) ^ d) +
        C * ∑ d ∈ Finset.range m, (1 / 2 : Real) ^ d := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 + C * 2 := by
      exact add_le_add (sum_range_nat_mul_inv_two_pow_le_two m)
        (mul_le_mul_of_nonneg_left (sum_range_inv_two_pow_le_two m) hC)
    _ = 2 + 2 * C := by ring

end Problem520
end Erdos
