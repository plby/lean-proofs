/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedEdges

/-!
# A nonzero exceptional integer for the pinned graph

Its factors use the shift indices after cancellation of the common
primorial. A pinned prime at least the tuple size makes every cross
difference nonzero. Away from its prime divisors the graph is generic.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem pinnedIndexCrossDifference_ne_zero
    {K m p₀ : ℕ} (h : Fin K) (hm : 0 < m) (hKp₀ : K ≤ p₀)
    (i j : PinnedShiftIndex h) : pinnedIndexCrossDifference h m p₀ i j ≠ 0 := by
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hp₀K : (K : ℤ) ≤ p₀ := by exact_mod_cast hKp₀
  have hK0 : (0 : ℤ) < K := by exact_mod_cast h.pos
  have hi0 : (0 : ℤ) ≤ i.val.val := by positivity
  have hj0 : (0 : ℤ) ≤ j.val.val := by positivity
  have hh0 : (0 : ℤ) ≤ h.val := by positivity
  have hiK : (i.val.val : ℤ) < K := by exact_mod_cast i.val.isLt
  have hjK : (j.val.val : ℤ) < K := by exact_mod_cast j.val.isLt
  have hhK : (h.val : ℤ) < K := by exact_mod_cast h.isLt
  have hu : (K : ℤ) ≤ (m : ℤ) * p₀ := by nlinarith
  unfold pinnedIndexCrossDifference
  intro hz
  rcases lt_trichotomy i.val.val j.val.val with hij | hij | hij
  · have hijZ : (i.val.val : ℤ) + 1 ≤ j.val.val := by exact_mod_cast hij
    nlinarith
  · have heq : h.val = j.val.val := by
      rw [hij, sub_self, mul_zero, zero_add] at hz
      exact_mod_cast sub_eq_zero.mp hz
    exact i.property (Fin.ext (hij.trans heq.symm))
  · have hijZ : (j.val.val : ℤ) + 1 ≤ i.val.val := by exact_mod_cast hij
    nlinarith

def pinnedIndexExceptionalModulus {K : ℕ} (h : Fin K) (m p₀ : ℕ) : ℕ :=
  m * ∏ ij : PinnedShiftIndex h × PinnedShiftIndex h,
    (pinnedIndexCrossDifference h m p₀ ij.1 ij.2).natAbs

theorem pinnedIndexExceptionalModulus_pos
    {K m p₀ : ℕ} (h : Fin K) (hm : 0 < m) (hKp₀ : K ≤ p₀) :
    0 < pinnedIndexExceptionalModulus h m p₀ := by
  apply Nat.mul_pos hm
  apply Finset.prod_pos
  intro ij hij
  exact Int.natAbs_pos.mpr (pinnedIndexCrossDifference_ne_zero h hm hKp₀ ij.1 ij.2)

theorem prime_dvd_pinnedIndexExceptionalModulus_of_edge
    {K m p₀ p : ℕ} (h : Fin K) (ij : PinnedShiftIndex h × PinnedShiftIndex h)
    (hij : ij ∈ pinnedIndexFourierEdges h m p₀ p) :
    p ∣ pinnedIndexExceptionalModulus h m p₀ := by
  have hdiff : (p : ℤ) ∣ pinnedIndexCrossDifference h m p₀ ij.1 ij.2 :=
    (Finset.mem_filter.mp hij).2
  have hnat : p ∣ (pinnedIndexCrossDifference h m p₀ ij.1 ij.2).natAbs :=
    Int.natCast_dvd.mp hdiff
  apply dvd_mul_of_dvd_right _ m
  exact hnat.trans (Finset.dvd_prod_of_mem
    (fun ab : PinnedShiftIndex h × PinnedShiftIndex h ↦
      (pinnedIndexCrossDifference h m p₀ ab.1 ab.2).natAbs) (Finset.mem_univ ij))

theorem truncatedPinnedFourierEdges_generic
    {K m p₀ Y p : ℕ} (h : Fin K) (hnot : ¬p ∣ pinnedIndexExceptionalModulus h m p₀) :
    truncatedPinnedFourierEdges h m p₀ Y p = ∅ ∧
      truncatedPinnedFourierCompanion m Y p = true := by
  unfold truncatedPinnedFourierEdges truncatedPinnedFourierCompanion
  split_ifs with hpY
  · constructor
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij hij
      exact hnot (prime_dvd_pinnedIndexExceptionalModulus_of_edge h ij hij)
    · simp only [affineFourierCompanionSwitch, decide_eq_true_eq]
      exact fun hpm ↦ hnot (dvd_mul_of_dvd_left hpm _)
  · exact ⟨rfl, rfl⟩

end

end Erdos4b
