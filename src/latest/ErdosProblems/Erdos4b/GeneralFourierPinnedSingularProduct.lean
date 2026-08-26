/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularSeries
import ErdosProblems.Erdos4b.GeneralFourierSingularTailLimit

/-!
# Exact splitting of the pinned singular product

The continued graph is generic above the companion cutoff. Its full
singular product equals the literal finite pinned series times the
generic tail, which tends to one as the cutoff tends to infinity.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def genericPinnedFourierSingularTail {K : ℕ} (h : Fin K) (Y : ℕ) : ℂ :=
  ∏' p : Nat.Primes, roughDoubledFourierSingularFactor (ι := PinnedShiftIndex h)
    Y (fun _ ↦ ∅) (fun _ ↦ true) p

def extendedPinnedSingularFactor {K : ℕ} (h : Fin K) (w m p₀ Y : ℕ) (p : Nat.Primes) : ℂ :=
  if p.val ≤ Y then (pinnedLocalFactor h w m p₀ p : ℂ) else
    doubledFourierSingularFactor (ι := PinnedShiftIndex h) (fun _ ↦ ∅) (fun _ ↦ true) p

theorem hasProd_small_pinnedSingularFactors {K : ℕ} (h : Fin K) (w m p₀ Y : ℕ) :
    HasProd (fun p : Nat.Primes ↦ if p.val ≤ Y then (pinnedLocalFactor h w m p₀ p : ℂ) else 1)
      (pinnedSingularSeries h w m p₀ Y : ℂ) := by
  classical
  let f (p : Nat.Primes) : ℂ := if p.val ≤ Y then (pinnedLocalFactor h w m p₀ p : ℂ) else 1
  have hf : HasProd f (∏ p ∈ boundedFourierPrimes Y, f p) :=
    hasProd_prod_of_ne_finset_one (s := boundedFourierPrimes Y) (f := f)
      (fun p hp ↦ if_neg (fun h ↦ hp ((mem_boundedFourierPrimes Y p).mpr h)))
  have heq : (∏ p ∈ boundedFourierPrimes Y, f p) = (pinnedSingularSeries h w m p₀ Y : ℂ) := by
    rw [pinnedSingularSeries, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro p hp
    exact if_pos ((mem_boundedFourierPrimes Y p).mp hp)
  exact heq ▸ hf

theorem pinnedFourier_cutoff_large {K w : ℕ} (h : Fin K) (hw : 14 * K + 1 ≤ w) :
    7 * (Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) : ℝ) ≤ w := by
  simp only [Fintype.card_sum, Nat.cast_add]
  have hc : (Fintype.card (PinnedShiftIndex h) : ℝ) ≤ K := by
    exact_mod_cast card_pinnedShiftIndex_le h
  have hwR : 14 * (K : ℝ) + 1 ≤ w := by exact_mod_cast hw
  linarith

theorem multipliable_roughPinnedFourierSingularFactor
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hw : 14 * K + 1 ≤ w) (hwY : w ≤ Y) (hYp₀ : Y < p₀) :
    Multipliable (fun p : Nat.Primes ↦ roughDoubledFourierSingularFactor w
      (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y) p) := by
  apply multipliable_roughDoubledFourierSingularFactor
    (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y)
    (pinnedIndexExceptionalModulus_pos (p₀ := p₀) h hm (by omega))
    (pinnedFourier_cutoff_large h hw)
  · intro p hwp
    rw [roughPinnedFourierEdges, if_pos hwp]
    exact card_truncatedPinnedFourierEdges_le h p.property hp₀ (by omega) hwp hYp₀
  · intro p hwp hnot
    rw [roughPinnedFourierEdges, if_pos hwp]
    exact truncatedPinnedFourierEdges_generic h hnot

theorem hasProd_genericPinnedFourierSingularTail
    {K Y : ℕ} (h : Fin K)
    (hY : 7 * (Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) : ℝ) ≤ Y) :
    HasProd (fun p : Nat.Primes ↦ roughDoubledFourierSingularFactor (ι := PinnedShiftIndex h)
      Y (fun _ ↦ ∅) (fun _ ↦ true) p) (genericPinnedFourierSingularTail h Y) :=
  (multipliable_roughDoubledFourierSingularFactor (ι := PinnedShiftIndex h)
    (fun _ ↦ ∅) (fun _ ↦ true) (M := 1) (by norm_num) hY
    (fun p hp ↦ Nat.zero_le _) (fun p hp hn ↦ ⟨rfl, rfl⟩)).hasProd

theorem hasProd_extendedPinnedSingularFactor
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hw : 14 * K + 1 ≤ w) (hwY : w ≤ Y) (hYp₀ : Y < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    HasProd (extendedPinnedSingularFactor h w m p₀ Y)
      ((pinnedSingularSeries h w m p₀ w : ℂ) *
        ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w
          (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y) p) := by
  have hs := hasProd_small_pinnedSingularFactors h w m p₀ w
  have hr := (multipliable_roughPinnedFourierSingularFactor h hm hp₀ hw hwY hYp₀).hasProd
  convert! hs.mul hr using 1
  ext p
  by_cases hpw : p.val ≤ w
  · simp only [extendedPinnedSingularFactor, if_pos (hpw.trans hwY), if_pos hpw,
      roughDoubledFourierSingularFactor, if_neg (Nat.not_lt.mpr hpw), mul_one]
  · have hwp : w < p.val := Nat.lt_of_not_ge hpw
    by_cases hpY : p.val ≤ Y
    · simp only [extendedPinnedSingularFactor, if_pos hpY, if_neg hpw,
        roughDoubledFourierSingularFactor, if_pos hwp, one_mul]
      exact (roughPinnedFourierSingularFactor_eq_pinnedLocalFactor h p (by omega) hwp hpY
        (pinnedResidual_not_dvd_prime hp₀ hYp₀ p hpY)
        (pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop p hpY)).symm
    · simp only [extendedPinnedSingularFactor, if_neg hpY, if_neg hpw,
        roughDoubledFourierSingularFactor, if_pos hwp, one_mul,
        doubledFourierSingularFactor, roughPinnedFourierEdges,
        truncatedPinnedFourierEdges, truncatedPinnedFourierCompanion]

theorem pinnedSingularProduct_eq_finite_mul_genericTail
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hw : 14 * K + 1 ≤ w) (hwY : w ≤ Y) (hYp₀ : Y < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    (pinnedSingularSeries h w m p₀ w : ℂ) *
        (∏' p : Nat.Primes, roughDoubledFourierSingularFactor w
          (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y) p) =
      (pinnedSingularSeries h w m p₀ Y : ℂ) * genericPinnedFourierSingularTail h Y := by
  have hfull := hasProd_extendedPinnedSingularFactor h hm hp₀ hw hwY hYp₀ hcop
  have hs := hasProd_small_pinnedSingularFactors h w m p₀ Y
  have hYlarge : 7 * (Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) : ℝ) ≤ Y :=
    (pinnedFourier_cutoff_large h hw).trans (by exact_mod_cast hwY)
  have hr := hasProd_genericPinnedFourierSingularTail h hYlarge
  apply hfull.unique
  convert! hs.mul hr using 1
  ext p
  by_cases hpY : p.val ≤ Y
  · simp only [extendedPinnedSingularFactor, if_pos hpY, roughDoubledFourierSingularFactor,
      if_neg (Nat.not_lt.mpr hpY), mul_one]
  · simp only [extendedPinnedSingularFactor, if_neg hpY, roughDoubledFourierSingularFactor,
      if_pos (Nat.lt_of_not_ge hpY), one_mul]

theorem tendsto_genericPinnedFourierSingularTail_one
    {α : Type*} {l : Filter α} {K : ℕ} (h : Fin K) (Y : α → ℕ) (hY : Tendsto Y l atTop) :
    Tendsto (fun a ↦ genericPinnedFourierSingularTail h (Y a)) l (𝓝 1) := by
  apply tendsto_tprod_roughDoubledFourierSingularFactor_one
    (fun _ ↦ 1) Y (fun _ _ ↦ ∅) (fun _ _ ↦ true) hY
  · exact Eventually.of_forall fun _ ↦ Nat.zero_lt_one
  · simp only [Nat.cast_one, Real.log_one, zero_div]
    exact tendsto_const_nhds
  · exact Eventually.of_forall fun _ p hp ↦ Nat.zero_le _
  · exact Eventually.of_forall fun _ p hp hn ↦ ⟨rfl, rfl⟩

end

end Erdos4b
