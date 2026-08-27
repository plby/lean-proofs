/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedTupleMass
import ErdosProblems.Erdos4b.FGKMTConditionalConcentration
import Mathlib.RingTheory.Int.Basic

/-! # Source tuples through a fixed vertex, and their exact intersections -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

def SourceProbabilityData.pinnedResidueTuple {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℤ) (j : Fin D.dimension × ℕ) : Finset ℤ :=
  D.residueTuple j.2 (q - (D.shifts j.1 : ℤ) * j.2)

theorem SourceProbabilityData.mem_pinnedResidueTuple {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℤ) (j : Fin D.dimension × ℕ) (n : ℤ) :
    n ∈ D.pinnedResidueTuple q j ↔
      ∃ i : Fin D.dimension, q + ((D.shifts i : ℤ) - D.shifts j.1) * j.2 = n := by
  rw [pinnedResidueTuple, D.mem_residueTuple]
  have heq (i : Fin D.dimension) :
      q - (D.shifts j.1 : ℤ) * j.2 + (D.shifts i : ℤ) * j.2 =
        q + ((D.shifts i : ℤ) - D.shifts j.1) * j.2 := by ring
  simp_rw [heq]

theorem SourceProbabilityData.pin_mem_pinnedResidueTuple {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℤ) (j : Fin D.dimension × ℕ) :
    q ∈ D.pinnedResidueTuple q j := by
  rw [D.mem_pinnedResidueTuple]
  exact ⟨j.1, by ring⟩

theorem SourceProbabilityData.pinnedResidueTuple_card {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℤ) {j : Fin D.dimension × ℕ} (hp : 0 < j.2) :
    (D.pinnedResidueTuple q j).card = D.dimension := D.residueTuple_card hp _

theorem SourceProbabilityData.pinnedTranslation_mem_window {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    {q : ℕ} (hqy : (q : ℝ) ≤ sourceIntervalLength c x)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (i : Fin D.dimension) :
    (q : ℤ) - (D.shifts i : ℤ) * p ∈ integerWeightWindow (sourceIntervalLength c x) := by
  rw [mem_integerWeightWindow]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hpR : (p : ℝ) ≤ x := by exact_mod_cast (mem_commonPinnedPrimeSet.mp hp).2.1
  have hhR : (D.shifts i : ℝ) ≤ 2 * (D.dimension : ℝ) ^ 2 := by
    exact_mod_cast (D.shifts_bounds i).2.2.le
  have hprod := (mul_le_mul hhR hpR (Nat.cast_nonneg p) (by positivity)).trans hshift
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hp0 : (0 : ℝ) ≤ (D.shifts i : ℝ) * p := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem SourceProbabilityData.pinnedResidueTuple_height {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (hy : 2 * sourceIntervalLength c x ≤ (x : ℝ) ^ 2)
    {q : ℕ} (hqy : (q : ℝ) ≤ sourceIntervalLength c x)
    {j : Fin D.dimension × ℕ} (hp : j.2 ∈ commonPinnedPrimeSet (x / 2) x) :
    ∀ n ∈ D.pinnedResidueTuple q j, |(n : ℝ)| ≤ (x : ℝ) ^ 2 :=
  D.residueTuple_height hshift hy hp (D.pinnedTranslation_mem_window hshift hqy hp j.1)

theorem SourceProbabilityData.pinnedResidueTuple_erase_disjoint {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℤ) {i j : Fin D.dimension × ℕ}
    (hp : i.2.Prime) (hp' : j.2.Prime) (hne : i.2 ≠ j.2)
    (hlarge : 2 * D.dimension ^ 2 < j.2) :
    Disjoint ((D.pinnedResidueTuple q i).erase q) ((D.pinnedResidueTuple q j).erase q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  obtain ⟨hnq, hnI⟩ := Finset.mem_erase.mp hni
  have hnJ := (Finset.mem_erase.mp hnj).2
  obtain ⟨u, hu⟩ := (D.mem_pinnedResidueTuple q i n).mp hnI
  obtain ⟨v, hv⟩ := (D.mem_pinnedResidueTuple q j n).mp hnJ
  have heq : ((D.shifts u : ℤ) - D.shifts i.1) * i.2 =
      ((D.shifts v : ℤ) - D.shifts j.1) * j.2 := by linarith
  have hdiv : (j.2 : ℤ) ∣ ((D.shifts u : ℤ) - D.shifts i.1) * i.2 := by
    rw [heq]
    exact dvd_mul_left _ _
  have hdiff : (j.2 : ℤ) ∣ (D.shifts u : ℤ) - D.shifts i.1 := by
    rcases Int.Prime.dvd_mul' hp' hdiv with h | h
    · exact h
    · have hnat : j.2 ∣ i.2 := by exact_mod_cast h
      have hh : j.2 = i.2 := (Nat.prime_dvd_prime_iff_eq hp' hp).mp hnat
      exact False.elim (hne hh.symm)
  have hult : D.shifts u < j.2 := (D.shifts_bounds u).2.2.trans hlarge
  have hilt : D.shifts i.1 < j.2 := (D.shifts_bounds i.1).2.2.trans hlarge
  have hultZ : (D.shifts u : ℤ) < j.2 := by exact_mod_cast hult
  have hiltZ : (D.shifts i.1 : ℤ) < j.2 := by exact_mod_cast hilt
  have hu0 : (0 : ℤ) ≤ D.shifts u := Int.natCast_nonneg _
  have hi0 : (0 : ℤ) ≤ D.shifts i.1 := Int.natCast_nonneg _
  have habs : |(D.shifts u : ℤ) - D.shifts i.1| < j.2 :=
    abs_lt.mpr ⟨by omega, by omega⟩
  have hnatabs : ((D.shifts u : ℤ) - D.shifts i.1).natAbs < (j.2 : ℤ).natAbs := by
    have hh : (((D.shifts u : ℤ) - D.shifts i.1).natAbs : ℤ) < j.2 := by
      simpa only [Int.natCast_natAbs] using habs
    simpa only [Int.natAbs_natCast] using (show
      ((D.shifts u : ℤ) - D.shifts i.1).natAbs < j.2 from by exact_mod_cast hh)
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiff hnatabs
  rw [hz, zero_mul, add_zero] at hu
  exact hnq hu.symm

theorem eventually_pinnedResidueTuple_ranges {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      2 * (D.dimension : ℝ) ≤ Real.log (x : ℝ) ∧
      (∀ q ∈ sourceSievingPrimes c x,
        ∀ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
          ∀ n ∈ D.pinnedResidueTuple q j, |(n : ℝ)| ≤ (x : ℝ) ^ 2) ∧
      (∀ q : ℤ, ∀ i ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
        ∀ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x, i.2 ≠ j.2 →
          Disjoint ((D.pinnedResidueTuple q i).erase q) ((D.pinnedResidueTuple q j).erase q)) := by
  filter_upwards [eventually_sourceTuple_ranges hc,
    eventually_sourceIntervalLength_bounds hc, eventually_dimensionPrimeCutoff_le_half]
    with x hranges hy hsmall
  intro D
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    rw [D.dimension_eq]
    exact growingSieveDimension_le x
  refine ⟨by simpa only [D.dimension_eq] using hranges.1, ?_, ?_⟩
  · intro q hq j hj
    have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
    exact D.pinnedResidueTuple_height (hy.2.2 D.dimension hk) hranges.2
      ((mem_sourceSievingPrimes hy0).mp hq).2.2 (Finset.mem_product.mp hj).2
  · intro q i hi j hj hne
    have hpi := mem_commonPinnedPrimeSet.mp (Finset.mem_product.mp hi).2
    have hpj := mem_commonPinnedPrimeSet.mp (Finset.mem_product.mp hj).2
    exact D.pinnedResidueTuple_erase_disjoint q hpi.2.2 hpj.2.2 hne
      ((hsmall D.dimension hk).trans_lt hpj.1)

end

end Erdos4b.FGKMT
