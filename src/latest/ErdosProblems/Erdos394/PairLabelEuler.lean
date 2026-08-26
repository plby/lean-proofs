import ErdosProblems.Erdos394.ForcedPairQuotientHeight
import ErdosProblems.Erdos394.ThreeStateEuler
import ErdosProblems.Erdos394.CornerEuler
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Euler sums over global pairs of root labels
-/

open Nat Finset

namespace Erdos394

/-- All ordered pairs of root labels below `K`. -/
def allLabelPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range K ×ˢ Finset.range K

/-- All global choices of one ordered label pair at every prime in `P`. -/
def globalLabelPairs (P : Finset ℕ) (K : ℕ) :
    Finset (∀ _p : ↥P, ℕ × ℕ) :=
  Fintype.piFinset (fun _p : ↥P ↦ allLabelPairs K)

@[simp] theorem card_allLabelPairs (K : ℕ) :
    (allLabelPairs K).card = K * K := by
  simp [allLabelPairs]

/-- The all-zero pair belongs to the label square when `K>0`. -/
theorem zero_mem_allLabelPairs {K : ℕ} (hK : 0 < K) :
    (0, 0) ∈ allLabelPairs K := by
  simp [allLabelPairs, hK]

/-- Removing the zero pair leaves exactly `K²-1` label pairs. -/
theorem card_allLabelPairs_erase_zero {K : ℕ} (hK : 0 < K) :
    ((allLabelPairs K).erase (0, 0)).card = K * K - 1 := by
  rw [Finset.card_erase_of_mem (zero_mem_allLabelPairs hK),
    card_allLabelPairs]

/-- Sum a function which takes one value at the zero pair and another value
at every other pair. -/
theorem sum_allLabelPairs_zero_other {R : Type*} [AddCommMonoid R]
    {K : ℕ} (hK : 0 < K) (x y : R) :
    (∑ ab ∈ allLabelPairs K, if ab = (0, 0) then x else y) =
      x + (K * K - 1 : ℕ) • y := by
  let f : ℕ × ℕ → R := fun ab ↦ if ab = (0, 0) then x else y
  have hsplit := Finset.sum_erase_add (allLabelPairs K) f
    (zero_mem_allLabelPairs hK)
  have hzero : f (0, 0) = x := by simp [f]
  have hrest : (∑ ab ∈ (allLabelPairs K).erase (0, 0), f ab) =
      ((allLabelPairs K).erase (0, 0)).card • y := by
    apply Finset.sum_eq_card_nsmul
    intro ab hab
    have habne : ab ≠ (0, 0) := (Finset.mem_erase.mp hab).1
    simp [f, habne]
  rw [hzero, hrest, card_allLabelPairs_erase_zero hK] at hsplit
  change (∑ ab ∈ allLabelPairs K, f ab) = _
  rw [← hsplit]
  abel

/-- The normalized local area sum obtained by ignoring the removed origins in
an exact pair event. -/
noncomputable def pairAreaLocalFactor (p K : ℕ) (ab : ℕ × ℕ) : ℝ :=
  if ab = (0, 0) then ((p - 1 : ℕ) : ℝ) / (p : ℝ) ^ 2
  else 1 / (p : ℝ)

/-- The normalized local non-rational boundary factor after extracting the
both-zero prime product. -/
noncomputable def pairNonrationalLocalFactor (p K Z : ℕ)
    (ab : ℕ × ℕ) : ℝ :=
  if ab = (0, 0) then 1 / (p : ℝ)
  else 1 / ((Z : ℝ) * ((p - 1 : ℕ) : ℝ))

/-- The normalized local factor for an additive constant error. -/
noncomputable def pairConstantLocalFactor (p K : ℕ)
    (ab : ℕ × ℕ) : ℝ :=
  if ab = (0, 0) then 1
  else 1 / ((p - 1 : ℕ) : ℝ)

/-- Closed form of the local area-label sum. -/
theorem sum_pairAreaLocalFactor {p K : ℕ} (hK : 0 < K) :
    (∑ ab ∈ allLabelPairs K, pairAreaLocalFactor p K ab) =
      ((p - 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 +
        ((K * K - 1 : ℕ) : ℝ) / (p : ℝ) := by
  unfold pairAreaLocalFactor
  rw [sum_allLabelPairs_zero_other hK
    (((p - 1 : ℕ) : ℝ) / (p : ℝ) ^ 2) (1 / (p : ℝ))]
  push_cast
  ring

/-- Closed form of the local non-rational-boundary label sum. -/
theorem sum_pairNonrationalLocalFactor {p K Z : ℕ} (hK : 0 < K) :
    (∑ ab ∈ allLabelPairs K, pairNonrationalLocalFactor p K Z ab) =
      1 / (p : ℝ) +
        ((K * K - 1 : ℕ) : ℝ) /
          ((Z : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
  unfold pairNonrationalLocalFactor
  rw [sum_allLabelPairs_zero_other hK
    (1 / (p : ℝ)) (1 / ((Z : ℝ) * ((p - 1 : ℕ) : ℝ)))]
  push_cast
  ring

/-- Closed form of the local constant-error label sum. -/
theorem sum_pairConstantLocalFactor {p K : ℕ} (hK : 0 < K) :
    (∑ ab ∈ allLabelPairs K, pairConstantLocalFactor p K ab) =
      1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  unfold pairConstantLocalFactor
  rw [sum_allLabelPairs_zero_other hK
    (1 : ℝ) (1 / ((p - 1 : ℕ) : ℝ))]
  push_cast
  ring

/-- Global independent label sums factor coordinatewise. -/
theorem sum_globalLabelPairs_prod
    (P : Finset ℕ) (K : ℕ) (g : ↥P → (ℕ × ℕ) → ℝ) :
    (∑ f ∈ globalLabelPairs P K, ∏ p : ↥P, g p (f p)) =
      ∏ p : ↥P, ∑ ab ∈ allLabelPairs K, g p ab := by
  exact Finset.sum_prod_piFinset (allLabelPairs K) g

/-- The full normalized non-rational label sum is exactly its two-state
Euler product (and hence is bounded by F-036's larger three-state product). -/
theorem global_nonrational_label_sum_eq
    (P : Finset ℕ) (K Z : ℕ) (hK : 0 < K) :
    (∑ f ∈ globalLabelPairs P K,
      ∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) =
      ∏ p ∈ P, (1 / (p : ℝ) +
        ((K * K - 1 : ℕ) : ℝ) /
          ((Z : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  rw [sum_globalLabelPairs_prod]
  simp_rw [sum_pairNonrationalLocalFactor hK]
  rw [← Finset.attach_eq_univ]
  simpa using Finset.prod_attach P (fun p ↦
    1 / (p : ℝ) + ((K * K - 1 : ℕ) : ℝ) /
      ((Z : ℝ) * ((p - 1 : ℕ) : ℝ)))

/-- F-036 therefore bounds the two-state non-rational label sum with the
decisive reciprocal prime product. -/
theorem global_nonrational_label_sum_le
    (P : Finset ℕ) (K Z : ℕ) (hK : 0 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime) (hZp : ∀ p ∈ P, Z ≤ p) :
    (∑ f ∈ globalLabelPairs P K,
      ∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p)) ≤
      (1 / (primeProduct P : ℝ)) *
        ∏ _p ∈ P,
          (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ)) := by
  rw [global_nonrational_label_sum_eq P K Z hK]
  calc
    (∏ p ∈ P, (1 / (p : ℝ) +
        ((K * K - 1 : ℕ) : ℝ) /
          ((Z : ℝ) * ((p - 1 : ℕ) : ℝ)))) ≤
      nonRationalBoundaryEuler P (K * K - 1) Z := by
        unfold nonRationalBoundaryEuler
        apply Finset.prod_le_prod
        · intro p hp
          positivity
        · intro p hp
          have hp2 : 2 ≤ p := (hprime p hp).two_le
          have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
          have hp1R : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p - 1)
          have hc : (0 : ℝ) ≤ (K * K - 1 : ℕ) := by positivity
          have hmid : 0 ≤ ((K * K - 1 : ℕ) : ℝ) /
              ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by positivity
          linarith
    _ ≤ (1 / (primeProduct P : ℝ)) *
        ∏ _p ∈ P,
          (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ)) :=
      nonRationalBoundaryEuler_le P (K * K - 1) Z hZ hprime hZp

/-- The full normalized constant-error label sum has its elementary Euler
product. -/
theorem global_constant_label_sum_eq
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K) :
    (∑ f ∈ globalLabelPairs P K,
      ∏ p : ↥P, pairConstantLocalFactor p.val K (f p)) =
      ∏ p ∈ P,
        (1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  rw [sum_globalLabelPairs_prod]
  simp_rw [sum_pairConstantLocalFactor hK]
  exact Finset.prod_attach P (fun p ↦
    1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))

/-- The constant-error sum is bounded by F-037's uniform correction. -/
theorem global_constant_label_sum_le
    (P : Finset ℕ) (K Z : ℕ) (hK : 0 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime) (hZp : ∀ p ∈ P, Z * Z ≤ p) :
    (∑ f ∈ globalLabelPairs P K,
      ∏ p : ↥P, pairConstantLocalFactor p.val K (f p)) ≤
      ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
  rw [global_constant_label_sum_eq P K hK]
  calc
    (∏ p ∈ P,
      (1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))) ≤
        pairStateConstantEuler P (K * K - 1) := by
      unfold pairStateConstantEuler
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hp2 : 2 ≤ p := (hprime p hp).two_le
        have hp1 : (0 : ℝ) < (p - 1 : ℕ) := by
          exact_mod_cast (show 0 < p - 1 by omega)
        have hc : (0 : ℝ) ≤ (K * K - 1 : ℕ) := by positivity
        have hfrac : 0 ≤ ((K * K - 1 : ℕ) : ℝ) /
            ((p - 1 : ℕ) : ℝ) := by positivity
        calc
          1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
              1 + 2 * (((K * K - 1 : ℕ) : ℝ) /
                ((p - 1 : ℕ) : ℝ)) := by linarith
          _ = 1 + 2 * ((K * K - 1 : ℕ) : ℝ) /
                ((p - 1 : ℕ) : ℝ) := by ring
    _ ≤ ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) :=
      pairStateConstantEuler_le P (K * K - 1) Z hZ hprime hZp

/-- The full normalized area-label sum factors coordinatewise. -/
theorem global_area_label_sum_eq
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K) :
    (∑ f ∈ globalLabelPairs P K,
      ∏ p : ↥P, pairAreaLocalFactor p.val K (f p)) =
      ∏ p ∈ P,
        (((p - 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 +
          ((K * K - 1 : ℕ) : ℝ) / (p : ℝ)) := by
  rw [sum_globalLabelPairs_prod]
  simp_rw [sum_pairAreaLocalFactor hK]
  exact Finset.prod_attach P (fun p ↦
    ((p - 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 +
      ((K * K - 1 : ℕ) : ℝ) / (p : ℝ))

/-- After division by the local unit count, the area factor is the desired
`K²/p²` main term times a small explicit correction. -/
theorem normalized_sum_pairAreaLocalFactor {p K : ℕ}
    (hK : 0 < K) (hp : p.Prime) :
    (∑ ab ∈ allLabelPairs K, pairAreaLocalFactor p K ab) /
        ((p - 1 : ℕ) : ℝ) =
      ((K * K : ℕ) : ℝ) / (p : ℝ) ^ 2 *
        (1 + ((K * K - 1 : ℕ) : ℝ) /
          (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  rw [sum_pairAreaLocalFactor hK]
  have hp1 : 1 ≤ p := hp.one_le
  have hp2 : 2 ≤ p := hp.two_le
  have hp1R : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpminus : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hKKn : 1 ≤ K * K := by
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Nat.ne_of_gt hK) (Nat.ne_of_gt hK))
  have hKK : (0 : ℝ) < (K * K : ℕ) := by positivity
  rw [Nat.cast_sub hp1, Nat.cast_sub hKKn]
  norm_num only [Nat.cast_one]
  field_simp [ne_of_gt hpR, ne_of_gt hp1R, ne_of_gt hKK, hpminus]
  <;> ring

/-- Normalizing the global area sum by the CRT unit universe yields the square
of the first-moment density times the product of the local corrections. -/
theorem normalized_global_area_label_sum_eq
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ f ∈ globalLabelPairs P K,
      ∏ p : ↥P, pairAreaLocalFactor p.val K (f p)) /
        (primeUnitCount P : ℝ) =
      (((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
        ∏ p ∈ P,
          (1 + ((K * K - 1 : ℕ) : ℝ) /
            (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  rw [global_area_label_sum_eq P K hK]
  unfold primeUnitCount primeProduct
  push_cast
  rw [← Finset.prod_div_distrib]
  calc
    (∏ p ∈ P,
      ((((p - 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 +
        ((K * K - 1 : ℕ) : ℝ) / (p : ℝ)) /
          ((p - 1 : ℕ) : ℝ))) =
      ∏ p ∈ P,
        (((K * K : ℕ) : ℝ) / (p : ℝ) ^ 2 *
          (1 + ((K * K - 1 : ℕ) : ℝ) /
            (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [sum_pairAreaLocalFactor hK] using
        (normalized_sum_pairAreaLocalFactor hK (hprime p hp))
    _ = ((K : ℝ) * (K : ℝ)) ^ P.card /
          (∏ p ∈ P, (p : ℝ)) ^ 2 *
        ∏ p ∈ P,
          (1 + ((K * K - 1 : ℕ) : ℝ) /
            (((K : ℝ) * (K : ℝ)) * ((p - 1 : ℕ) : ℝ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_div_distrib,
        Finset.prod_const, Finset.prod_pow]
      push_cast
      rfl

end Erdos394
