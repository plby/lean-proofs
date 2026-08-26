import ErdosProblems.Erdos394.PairStateReduction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Product identities for one global pair-label state
-/

open Nat Finset

namespace Erdos394

/-- Local characterization of the both-zero set attached to a global label
state. -/
theorem mem_pairStateZeroPrimes_iff
    (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ) {p : ℕ} (hp : p ∈ P) :
    p ∈ pairStateZeroPrimes P f ↔ f ⟨p, hp⟩ = (0, 0) := by
  simp only [pairStateZeroPrimes, bothZeroLabelPrimes, Finset.mem_filter, hp,
    true_and]
  rw [globalLabelFirst_at P f hp, globalLabelSecond_at P f hp]
  constructor
  · intro h
    exact Prod.ext h.1 h.2
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The product of primes whose local label pair is zero. -/
theorem prod_pairStateZero_indicator
    (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ) :
    (∏ p : ↥P, if f p = (0, 0) then p.val else 1) =
      primeProduct (pairStateZeroPrimes P f) := by
  let g : ℕ → ℕ := fun p ↦
    if (globalLabelFirst P f p, globalLabelSecond P f p) = (0, 0)
      then p else 1
  calc
    (∏ p : ↥P, if f p = (0, 0) then p.val else 1) =
        ∏ p : ↥P, g p.val := by
      apply Fintype.prod_congr
      intro p
      simp [g, globalLabelFirst, globalLabelSecond, p.property,
        Prod.ext_iff]
    _ = ∏ p ∈ P, g p := Finset.prod_coe_sort P g
    _ = ∏ p ∈ pairStateZeroPrimes P f, p := by
      unfold pairStateZeroPrimes bothZeroLabelPrimes g
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      simp [Prod.ext_iff]
    _ = primeProduct (pairStateZeroPrimes P f) := rfl

/-- The complementary product of a constant `Z` has one factor at every
nonzero-label prime. -/
theorem prod_pairStateNonzero_constant
    (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ) (Z : ℕ) :
    (∏ p : ↥P, if f p = (0, 0) then 1 else Z) =
      Z ^ (P \ pairStateZeroPrimes P f).card := by
  let g : ℕ → ℕ := fun p ↦
    if (globalLabelFirst P f p, globalLabelSecond P f p) = (0, 0)
      then 1 else Z
  calc
    (∏ p : ↥P, if f p = (0, 0) then 1 else Z) =
        ∏ p : ↥P, g p.val := by
      apply Fintype.prod_congr
      intro p
      simp [g, globalLabelFirst, globalLabelSecond, p.property,
        Prod.ext_iff]
    _ = ∏ p ∈ P, g p := Finset.prod_coe_sort P g
    _ = ∏ p ∈ P,
        if p ∈ pairStateZeroPrimes P f then 1 else Z := by
      apply Finset.prod_congr rfl
      intro p hp
      unfold g pairStateZeroPrimes bothZeroLabelPrimes
      simp only [Finset.mem_filter, hp, true_and]
      rw [globalLabelFirst_at P f hp, globalLabelSecond_at P f hp]
      by_cases hz : f ⟨p, hp⟩ = (0, 0)
      · have hz' : (f ⟨p, hp⟩).1 = 0 ∧ (f ⟨p, hp⟩).2 = 0 :=
          ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
        simp [hz, hz']
      · have hz' : ¬((f ⟨p, hp⟩).1 = 0 ∧ (f ⟨p, hp⟩).2 = 0) := by
          intro h
          exact hz (Prod.ext h.1 h.2)
        simp [hz, hz']
    _ = ∏ _p ∈ P \ pairStateZeroPrimes P f, Z := by
      symm
      rw [show P \ pairStateZeroPrimes P f =
          P.filter (fun p ↦ p ∉ pairStateZeroPrimes P f) by
        ext p
        simp]
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hz : p ∈ pairStateZeroPrimes P f <;> simp [hz]
    _ = Z ^ (P \ pairStateZeroPrimes P f).card := by simp

/-- The product of all prime moduli as a subtype product. -/
theorem prod_primeSubtype_eq_primeProduct (P : Finset ℕ) :
    (∏ p : ↥P, p.val) = primeProduct P := by
  simpa [primeProduct] using
    (Finset.prod_coe_sort P (fun p : ℕ ↦ p))

/-- Local unit cardinality, named to make subtype-product coercions
unambiguous. -/
def primeUnitFactor (p : ℕ) : ℕ := p - 1

/-- The product of all local unit cardinalities as a subtype product. -/
theorem prod_primeSubtype_units_eq (P : Finset ℕ) :
    (∏ p : ↥P, primeUnitFactor p.val) = primeUnitCount P := by
  unfold primeUnitCount primeUnitFactor
  exact Finset.prod_coe_sort P (fun p : ℕ ↦ p - 1)

/-- Fixed-state area coefficient equals the product of F-059's local area
factors. -/
theorem pairState_area_factor
    (P : Finset ℕ) (K : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ) :
    (pairMultiplierGlobalWeight P f : ℝ) /
        ((primeProduct P * primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ) =
      ∏ p : ↥P, pairAreaLocalFactor p.val K (f p) := by
  unfold pairMultiplierGlobalWeight
  have hqR : (primeProduct P : ℝ) =
      ∏ p : ↥P, (p.val : ℝ) := by
    exact_mod_cast (prod_primeSubtype_eq_primeProduct P).symm
  have hzeroR : (primeProduct (pairStateZeroPrimes P f) : ℝ) =
      ∏ p : ↥P, (if f p = (0, 0) then (p.val : ℝ) else 1) := by
    exact_mod_cast (prod_pairStateZero_indicator P f).symm
  push_cast
  rw [hqR, hzeroR]
  rw [← Finset.prod_mul_distrib]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  unfold pairMultiplierLocalWeight pairAreaLocalFactor
  by_cases hz : f p = (0, 0)
  · simp [hz, pow_two]
  · simp [hz]

/-- Fixed-state normalized non-rational reciprocal coefficient equals the
product of F-059's local non-rational factors. -/
theorem pairState_nonrational_factor
    (P : Finset ℕ) (K Z : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hZ : 0 < Z) :
    ((pairMultiplierGlobalWeight P f : ℝ) / (primeUnitCount P : ℝ)) /
        (((primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ) *
          ((Z ^ (P \ pairStateZeroPrimes P f).card : ℕ) : ℝ)) =
      ∏ p : ↥P, pairNonrationalLocalFactor p.val K Z (f p) := by
  have hphiR : (primeUnitCount P : ℝ) =
      ∏ p : ↥P, ((primeUnitFactor p.val : ℕ) : ℝ) := by
    exact_mod_cast (prod_primeSubtype_units_eq P).symm
  have hzeroR : ((primeProduct (pairStateZeroPrimes P f) : ℕ) : ℝ) =
      ∏ p : ↥P, (if f p = (0, 0) then (p.val : ℝ) else 1) := by
    exact_mod_cast (prod_pairStateZero_indicator P f).symm
  have hpowR : ((Z ^ (P \ pairStateZeroPrimes P f).card : ℕ) : ℝ) =
      ∏ p : ↥P, (if f p = (0, 0) then 1 else (Z : ℝ)) := by
    exact_mod_cast (prod_pairStateNonzero_constant P f Z).symm
  rw [hphiR, hzeroR, hpowR]
  unfold pairMultiplierGlobalWeight primeUnitFactor
  push_cast
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP := p.property
  have hp2 : 2 ≤ p.val := (hprime p.val hpP).two_le
  have hp1R : (0 : ℝ) < (p.val - 1 : ℕ) := by
    exact_mod_cast (show 0 < p.val - 1 by omega)
  have hpR : (0 : ℝ) < p.val := by exact_mod_cast (hprime p.val hpP).pos
  have hZR : (0 : ℝ) < Z := by exact_mod_cast hZ
  unfold pairMultiplierLocalWeight pairNonrationalLocalFactor
  by_cases hz : f p = (0, 0)
  · simp [hz, ne_of_gt hp1R, ne_of_gt hpR, ne_of_gt hZR]
  · simp [hz, ne_of_gt hp1R, ne_of_gt hpR, ne_of_gt hZR]
    ring

end Erdos394
