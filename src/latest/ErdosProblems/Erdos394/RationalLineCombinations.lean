import ErdosProblems.Erdos394.MixedRatio

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Escaping finitely many rational lines with a bounded combination

Two independent lattice directions cannot both remain trapped in the finite
union of root-label lines: among `u+n v` for `0 ≤ n < K²`, one escapes.
-/

open Nat Finset

namespace Erdos394

/-- Determinant of two signed integer vectors. -/
def intPairDet (u v : ℤ × ℤ) : ℤ :=
  u.1 * v.2 - u.2 * v.1

/-- The vector `u+n v`. -/
def intPairAddN (u v : ℤ × ℤ) (n : ℕ) : ℤ × ℤ :=
  (u.1 + (n : ℤ) * v.1, u.2 + (n : ℤ) * v.2)

/-- Sup-height of a signed integer vector. -/
def intPairHeight (u : ℤ × ℤ) : ℕ :=
  max u.1.natAbs u.2.natAbs

/-- Membership in one of the finitely many exact root-label lines. -/
def onSmallRatioLine (K : ℕ) (u : ℤ × ℤ) : Prop :=
  ∃ ab ∈ nonzeroLabelPairs K,
    (ab.1 : ℤ) * u.2 = (ab.2 : ℤ) * u.1

/-- There are exactly `K²-1` nonzero label pairs when `K>0`. -/
theorem card_nonzeroLabelPairs_eq {K : ℕ} (hK : 0 < K) :
    (nonzeroLabelPairs K).card = K * K - 1 := by
  unfold nonzeroLabelPairs
  rw [Finset.card_erase_of_mem]
  · simp
  · simp [hK]

/-- Determinant of two members of the affine combination family. -/
theorem intPairDet_addN_addN (u v : ℤ × ℤ) (n m : ℕ) :
    intPairDet (intPairAddN u v n) (intPairAddN u v m) =
      ((m : ℤ) - (n : ℤ)) * intPairDet u v := by
  simp only [intPairDet, intPairAddN]
  ring

/-- Two vectors on the same nonzero label line have determinant zero. -/
theorem intPairDet_eq_zero_of_same_ratio_line {A B : ℕ} {u v : ℤ × ℤ}
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hu : (A : ℤ) * u.2 = (B : ℤ) * u.1)
    (hv : (A : ℤ) * v.2 = (B : ℤ) * v.1) :
    intPairDet u v = 0 := by
  by_cases hA : A = 0
  · have hB : (B : ℤ) ≠ 0 := by
      exact_mod_cast hAB.resolve_left (fun hAne ↦ hAne hA)
    have hmul : (B : ℤ) * intPairDet u v = 0 := by
      unfold intPairDet
      calc
        (B : ℤ) * (u.1 * v.2 - u.2 * v.1) =
            ((B : ℤ) * u.1) * v.2 - u.2 * ((B : ℤ) * v.1) := by ring
        _ = ((A : ℤ) * u.2) * v.2 - u.2 * ((A : ℤ) * v.2) := by
          rw [← hu, ← hv]
        _ = 0 := by ring
    exact (mul_eq_zero.mp hmul).resolve_left hB
  · have hAz : (A : ℤ) ≠ 0 := by exact_mod_cast hA
    have hmul : (A : ℤ) * intPairDet u v = 0 := by
      unfold intPairDet
      calc
        (A : ℤ) * (u.1 * v.2 - u.2 * v.1) =
            u.1 * ((A : ℤ) * v.2) - ((A : ℤ) * u.2) * v.1 := by ring
        _ = u.1 * ((B : ℤ) * v.1) - ((B : ℤ) * u.1) * v.1 := by
          rw [hv, hu]
        _ = 0 := by ring
    exact (mul_eq_zero.mp hmul).resolve_left hAz

/-- Among `K²` combinations of two independent vectors, one lies on none of
the `K²-1` nonzero-label lines. -/
theorem exists_addN_not_onSmallRatioLine {K : ℕ} (hK : 0 < K)
    (u v : ℤ × ℤ) (hind : intPairDet u v ≠ 0) :
    ∃ n < K * K, ¬ onSmallRatioLine K (intPairAddN u v n) := by
  classical
  by_contra hnone
  push Not at hnone
  let S := Finset.range (K * K)
  have hall : ∀ n : ↥S,
      ∃ ab ∈ nonzeroLabelPairs K,
        (ab.1 : ℤ) * (intPairAddN u v n.1).2 =
          (ab.2 : ℤ) * (intPairAddN u v n.1).1 := by
    intro n
    exact hnone n.1 (Finset.mem_range.mp n.2)
  choose f hfmem hfeq using hall
  have hcard : (nonzeroLabelPairs K).card <
      (Finset.univ : Finset ↥S).card := by
    rw [card_nonzeroLabelPairs_eq hK, Finset.card_univ,
      Fintype.card_coe, Finset.card_range]
    have hKK : 0 < K * K := mul_pos hK hK
    omega
  have hmaps : Set.MapsTo f (↑(Finset.univ : Finset ↥S))
      (↑(nonzeroLabelPairs K)) := by
    intro n hn
    exact hfmem n
  obtain ⟨n, hn, m, hm, hnm, hfm⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have habmem := hfmem n
  have habnz : (f n).1 ≠ 0 ∨ (f n).2 ≠ 0 := by
    simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq, Prod.mk.injEq,
      Finset.mem_product, Finset.mem_range] at habmem
    by_contra hz
    push Not at hz
    apply habmem.1
    ext <;> simp_all
  have hnline := hfeq n
  have hmline : ((f n).1 : ℤ) * (intPairAddN u v m.1).2 =
      ((f n).2 : ℤ) * (intPairAddN u v m.1).1 := by
    rw [hfm]
    exact hfeq m
  have hdetzero :
      intPairDet (intPairAddN u v n.1) (intPairAddN u v m.1) = 0 :=
    intPairDet_eq_zero_of_same_ratio_line habnz hnline hmline
  rw [intPairDet_addN_addN] at hdetzero
  have hnmval : n.1 ≠ m.1 := by
    intro heq
    exact hnm (Subtype.ext heq)
  have hmn : (m.1 : ℤ) - (n.1 : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hnmval.symm)
  exact hind ((mul_eq_zero.mp hdetzero).resolve_left hmn)

/-- The escaping combination has sup-height at most `K²` times the larger
height of the two original directions. -/
theorem exists_short_addN_not_onSmallRatioLine {K : ℕ} (hK : 0 < K)
    (u v : ℤ × ℤ) (hind : intPairDet u v ≠ 0) :
    ∃ w : ℤ × ℤ,
      ¬ onSmallRatioLine K w ∧
      intPairHeight w ≤ K * K * max (intPairHeight u) (intPairHeight v) := by
  obtain ⟨n, hn, hline⟩ := exists_addN_not_onSmallRatioLine hK u v hind
  refine ⟨intPairAddN u v n, hline, ?_⟩
  let M := max (intPairHeight u) (intPairHeight v)
  have hu1 : u.1.natAbs ≤ M :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hu2 : u.2.natAbs ≤ M :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hv1 : v.1.natAbs ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hv2 : v.2.natAbs ≤ M :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hcoord1 : (intPairAddN u v n).1.natAbs ≤ K * K * M := by
    calc
      (intPairAddN u v n).1.natAbs ≤
          u.1.natAbs + ((n : ℤ) * v.1).natAbs := Int.natAbs_add_le _ _
      _ = u.1.natAbs + n * v.1.natAbs := by simp [Int.natAbs_mul]
      _ ≤ M + n * M := by gcongr
      _ ≤ K * K * M := by nlinarith
  have hcoord2 : (intPairAddN u v n).2.natAbs ≤ K * K * M := by
    calc
      (intPairAddN u v n).2.natAbs ≤
          u.2.natAbs + ((n : ℤ) * v.2).natAbs := Int.natAbs_add_le _ _
      _ = u.2.natAbs + n * v.2.natAbs := by simp [Int.natAbs_mul]
      _ ≤ M + n * M := by gcongr
      _ ≤ K * K * M := by nlinarith
  exact max_le hcoord1 hcoord2

end Erdos394
