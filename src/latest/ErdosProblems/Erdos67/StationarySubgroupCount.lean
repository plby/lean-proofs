import ErdosProblems.Erdos67.StationaryPositiveCRT

/-!
# The finite counting inequality for a proper residue subgroup

CRT supplies many integers in a prescribed unit class and coprime to a
chosen finite prime product. Every one has a bad prime factor outside that
product, so a finite union bound gives a reciprocal-prime tail lower bound.
-/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryModel

noncomputable def badPrimeTail (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (S : Finset ℕ)
    (T : ℕ) : Finset ℕ := by
  classical
  exact ((range (T + 1)).filter (BadResiduePrime q H)) \ S

theorem mem_badPrimeTail (q : ℕ+) (H : Subgroup (ZMod q.val)ˣ) (S : Finset ℕ) (T p : ℕ) :
    p ∈ badPrimeTail q H S T ↔ p ≤ T ∧ BadResiduePrime q H p ∧ p ∉ S := by
  classical
  simp only [badPrimeTail, mem_sdiff, mem_filter, mem_range, Nat.lt_succ_iff, and_assoc]

theorem positiveCRT_image_subset_bad_multiples (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (H : Subgroup (ZMod q.val)ˣ) (a : (ZMod q.val)ˣ) (ha : a ∉ H)
    (S : Finset ℕ) (hSP : ∀ p ∈ S, p ∣ P.val) :
    univ.image (positiveCRT q P hcop a) ⊆
      (badPrimeTail q H S (2 * (q.val * P.val))).biUnion
        (fun p ↦ (range (2 * (q.val * P.val) + 1)).filter (fun n ↦ n ≠ 0 ∧ p ∣ n)) := by
  classical
  intro n hn
  obtain ⟨b, _, rfl⟩ := mem_image.mp hn
  have hpos := positiveCRT_pos q P hcop a b
  have hlt := positiveCRT_lt q P hcop a b
  obtain ⟨p, hpn, hp⟩ := exists_bad_residue_prime_factor q H (positiveCRT q P hcop a b)
    hpos (positiveCRT_coprime_left q P hcop a b)
    (by rwa [residueUnit_positiveCRT])
  have hpT : p ≤ 2 * (q.val * P.val) := (Nat.le_of_dvd hpos hpn).trans hlt.le
  have hpS : p ∉ S := by
    intro hmem
    have hcp := positiveCRT_coprime_right q P hcop a b
    have hpd : p ∣ 1 := by
      rw [← hcp.gcd_eq_one]
      exact Nat.dvd_gcd hpn (hSP p hmem)
    exact hp.1.ne_one (Nat.dvd_one.mp hpd)
  apply mem_biUnion.mpr
  refine ⟨p, (mem_badPrimeTail q H S _ p).mpr ⟨hpT, hp, hpS⟩, ?_⟩
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hpos.ne', hpn⟩

theorem totient_le_bad_prime_tail (q P : ℕ+) (hcop : Nat.Coprime q.val P.val)
    (H : Subgroup (ZMod q.val)ˣ) (a : (ZMod q.val)ˣ) (ha : a ∉ H)
    (S : Finset ℕ) (hSP : ∀ p ∈ S, p ∣ P.val) :
    (P.val.totient : ℝ) ≤ (2 * (q.val * P.val) : ℕ) *
      ∑ p ∈ badPrimeTail q H S (2 * (q.val * P.val)), (1 / p : ℝ) := by
  classical
  have hcard := (card_le_card (positiveCRT_image_subset_bad_multiples q P hcop H a ha S hSP)).trans
    card_biUnion_le
  rw [card_positiveCRT_image] at hcard
  simp only [Nat.card_multiples'] at hcard
  calc
    _ ≤ ((∑ p ∈ badPrimeTail q H S (2 * (q.val * P.val)), 2 * (q.val * P.val) / p : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcard
    _ ≤ ∑ p ∈ badPrimeTail q H S (2 * (q.val * P.val)),
        ((2 * (q.val * P.val) : ℕ) : ℝ) / p := by
      rw [Nat.cast_sum]
      exact sum_le_sum fun p _ ↦ Nat.cast_div_le
    _ = _ := by simp only [mul_sum, mul_one_div]

end Erdos67.StationaryModel
