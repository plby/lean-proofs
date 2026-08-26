/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedLocalCompatibility
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularSeries
import ErdosProblems.Erdos4b.GeneralFourierPinnedAsymptotic

/-!
# Exact supported arithmetic meaning of the continued pinned graph

Individual companion coordinates are at most `Y`. Thus no companion
prime occurs above `Y`, where the Fourier graph has been continued
generically. The first coordinates are less than the pinned prime.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem prime_le_of_dvd_lcm_of_coordinate_le
    {p a b Y : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (haY : a ≤ Y) (hbY : b ≤ Y) (hdiv : p ∣ Nat.lcm a b) : p ≤ Y := by
  rcases (prime_dvd_lcm_iff_or hp).mp hdiv with hd | hd
  · exact (Nat.le_of_dvd ha hd).trans haY
  · exact (Nat.le_of_dvd hb hd).trans hbY

theorem prime_not_dvd_pinnedPrime_of_coordinate_lt
    {p p₀ a b : ℕ} (hp : p.Prime) (hp₀ : p₀.Prime)
    (ha : 0 < a) (hb : 0 < b) (ha₀ : a < p₀) (hb₀ : b < p₀)
    (hdiv : p ∣ Nat.lcm a b) : ¬p ∣ p₀ := by
  have hlt : p < p₀ := by
    rcases (prime_dvd_lcm_iff_or hp).mp hdiv with hd | hd
    · exact (Nat.le_of_dvd ha hd).trans_lt ha₀
    · exact (Nat.le_of_dvd hb hd).trans_lt hb₀
  intro hpdiv
  exact (ne_of_lt hlt) ((hp₀.dvd_iff_eq hp.ne_one).mp hpdiv).symm

theorem doubledDivisorPrimeCompatible_iff_pinnedLocalSolvable
    {K w m p₀ Y : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hd : d ∈ doubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y) :
    DoubledDivisorPrimeCompatible P (roughPinnedFourierEdges h w m p₀ Y)
        (truncatedPinnedFourierCompanion m Y) d ↔
      ∀ p : P, PinnedLocalDivisorSolvable h w m p₀ p.val
        (fun i ↦ Nat.lcm (d (.inl i) false) (d (.inl i) true))
        (fun i ↦ Nat.lcm (d (.inr i) false) (d (.inr i) true)) := by
  obtain ⟨hdiv, hwithin⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
  have hpos (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) (b : Bool) : 0 < d i b :=
    ((primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)).ne_zero.bot_lt
  obtain ⟨hDD, hEE⟩ := withinFamilyDivisorCoprime_lcm hwithin
  unfold DoubledDivisorPrimeCompatible
  apply forall_congr'
  intro p
  have hp := hP p p.property
  have hwp := hrough p p.property
  have hfirst : (∃ i, p.val ∣ Nat.lcm (d (.inl i) false) (d (.inl i) true)) → ¬p.val ∣ p₀ := by
    rintro ⟨i, hi⟩
    exact prime_not_dvd_pinnedPrime_of_coordinate_lt hp hp₀
      (hpos _ _) (hpos _ _) (hDsmall i false) (hDsmall i true) hi
  have hcomp (i : PinnedShiftIndex h)
      (hi : p.val ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true)) : p.val ≤ Y :=
    prime_le_of_dvd_lcm_of_coordinate_le hp (hpos _ _) (hpos _ _)
      (hEsmall i false) (hEsmall i true) hi
  have hnum : (∃ i, p.val ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true)) →
      (1 : ZMod p.val) - (m : ZMod p.val) * p₀ ≠ 0 := by
    rintro ⟨i, hi⟩
    exact pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop ⟨p.val, hp⟩ (hcomp i hi)
  rw [pinnedLocalDivisorSolvable_iff_graph h hp hKw hwp _ _ hDD hEE hfirst hnum]
  by_cases hpY : p.val ≤ Y
  · simp only [roughPinnedFourierEdges, if_pos hwp, truncatedPinnedFourierEdges,
      if_pos hpY, truncatedPinnedFourierCompanion, affineFourierCompanionSwitch,
      decide_eq_true_eq]
  · have hnone : ∀ i, ¬p.val ∣ Nat.lcm (d (.inr i) false) (d (.inr i) true) :=
      fun i hi ↦ hpY (hcomp i hi)
    simp only [hnone, IsEmpty.forall_iff, implies_true, and_self]

theorem withinFamilyDivisorCoprime_of_pinnedLocalSolvable
    {K w m p₀ Y : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y)
    (hsol : ∀ p : P, PinnedLocalDivisorSolvable h w m p₀ p.val
      (fun i ↦ Nat.lcm (d (.inl i) false) (d (.inl i) true))
      (fun i ↦ Nat.lcm (d (.inr i) false) (d (.inr i) true))) :
    WithinFamilyDivisorCoprime d := by
  have hpos (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) (b : Bool) : 0 < d i b :=
    ((primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)).ne_zero.bot_lt
  have hlcm (i : PinnedShiftIndex h ⊕ PinnedShiftIndex h) (b : Bool) :
      d i b ∣ Nat.lcm (d i false) (d i true) := by
    cases b
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_lcm_right _ _
  constructor
  · intro i j hij b c
    apply Nat.coprime_of_dvd
    intro p hp hpi hpj
    have hpP := (prime_dvd_primeFinsetProduct_iff P hP hp).mp (hpi.trans (hdiv _ _))
    have hi := hpi.trans (hlcm (.inl i) b)
    have hj := hpj.trans (hlcm (.inl j) c)
    exact hij (pinnedLocalDivisorSolvable_first_unique h hp hKw (hrough p hpP) _ _
      (prime_not_dvd_pinnedPrime_of_coordinate_lt hp hp₀
        (hpos _ _) (hpos _ _) (hDsmall i false) (hDsmall i true) hi)
      (hsol ⟨p, hpP⟩) hi hj)
  · intro i j hij b c
    apply Nat.coprime_of_dvd
    intro p hp hpi hpj
    have hpP := (prime_dvd_primeFinsetProduct_iff P hP hp).mp (hpi.trans (hdiv _ _))
    have hi := hpi.trans (hlcm (.inr i) b)
    have hj := hpj.trans (hlcm (.inr j) c)
    have hpY := prime_le_of_dvd_lcm_of_coordinate_le hp (hpos _ _) (hpos _ _)
      (hEsmall i false) (hEsmall i true) hi
    exact hij (pinnedLocalDivisorSolvable_companion_unique h hp hKw (hrough p hpP) _ _
      (pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop ⟨p, hp⟩ hpY)
      (hsol ⟨p, hpP⟩) hi hj)

end

end Erdos4b
