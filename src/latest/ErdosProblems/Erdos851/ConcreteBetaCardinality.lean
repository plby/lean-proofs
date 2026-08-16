/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.ConcreteBetaCutoff
import ErdosProblems.Erdos851.FiniteBetaProductRatio
import ErdosProblems.Erdos851.FiniteSieveApplication
import ErdosProblems.Erdos851.SieveSpecialization
import ErdosProblems.Erdos851.EndpointBridge

/-!
# Concrete finite beta-sieve cardinality estimates

This module joins the concrete beta-100 main-term bounds to the finite
one- and two-shift interval sieves.  It aligns the ascending prime list with
the local Euler product, verifies Rosser support below `y ^ S`, controls the
CRT remainder by `(y ^ S) ^ 2`, and concludes estimates for the actual
finite candidate sets.
-/

namespace Erdos851
open FiniteCombinatorialSieve
open List
open ShiftSieve
open FiniteSieveApplication

/-- Finite lower main terms depend only on the values of the local density
on the ambient prime list. -/
theorem lowerMainTerm_congr_on {alpha : Type*}
    (A : List alpha → Prop) (g g' : alpha → ℝ) (P : List alpha)
    (h : ∀ p ∈ P, g p = g' p) :
    lowerMainTerm A g P = lowerMainTerm A g' P := by
  unfold lowerMainTerm
  congr 1
  apply List.map_congr_left
  intro t ht
  have hsub : t <+ P := List.mem_sublists.mp ht
  by_cases hadm : LowerAdmissible A t
  · simp only [lowerTerm, hadm, if_pos]
    apply congrArg ((-1 : ℝ) ^ t.length * ·)
    unfold chainWeight
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    exact h p (hsub.subset hp)
  · simp [lowerTerm, hadm]

/-- Finite upper main terms depend only on the values of the local density
on the ambient prime list. -/
theorem upperMainTerm_congr_on {alpha : Type*}
    (A : List alpha → Prop) (g g' : alpha → ℝ) (P : List alpha)
    (h : ∀ p ∈ P, g p = g' p) :
    upperMainTerm A g P = upperMainTerm A g' P := by
  unfold upperMainTerm
  congr 1
  apply List.map_congr_left
  intro t ht
  have hsub : t <+ P := List.mem_sublists.mp ht
  by_cases hadm : UpperAdmissible A t
  · simp only [upperTerm, hadm, if_pos]
    apply congrArg ((-1 : ℝ) ^ t.length * ·)
    unfold chainWeight
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    exact h p (hsub.subset hp)
  · simp [upperTerm, hadm]

/-- The local sieve interval `(z,y]`, listed increasingly as required by the
finite combinatorial sieve. -/
def ascendingSievePrimes (z y : ℕ) : List ℕ :=
  (sievePrimes z y).sort (fun a b ↦ a ≤ b)

theorem ascendingSievePrimes_prod (z y : ℕ) :
    (ascendingSievePrimes z y).prod =
      Erdos387.sievePrimeProduct z (y + 1) := by
  classical
  rw [erdos387_sievePrimeProduct_succ]
  unfold ascendingSievePrimes
  symm
  simpa using List.prod_toFinset id
    (Finset.sort_nodup (sievePrimes z y) (fun a b : ℕ ↦ a ≤ b))

theorem ascendingSievePrimes_pairwise (z y : ℕ) :
    (ascendingSievePrimes z y).Pairwise (· ≤ ·) := by
  exact Finset.pairwise_sort (sievePrimes z y) (fun a b : ℕ ↦ a ≤ b)

theorem ascendingSievePrimes_nodup (z y : ℕ) :
    (ascendingSievePrimes z y).Nodup := by
  exact Finset.sort_nodup (sievePrimes z y) (fun a b : ℕ ↦ a ≤ b)

@[simp] theorem mem_ascendingSievePrimes {z y p : ℕ} :
    p ∈ ascendingSievePrimes z y ↔ p ∈ sievePrimes z y := by
  simp [ascendingSievePrimes]

theorem ascendingSievePrimes_prime {z y : ℕ} :
    ∀ p ∈ ascendingSievePrimes z y, p.Prime := by
  intro p hp
  exact (mem_sievePrimes.mp (mem_ascendingSievePrimes.mp hp)).2.2

/-- The Rosser lower and upper main terms bound the actual sifted shifted
candidate cardinality, with the completely explicit square-level loss. -/
theorem boundingSieve_cardinality_between_mainTerms
    {shifts : Finset ℕ} (hshifts : shifts.Nonempty)
    (hcard : shifts.card ≤ 2) {X z y S : ℕ}
    (hz : 2 ≤ z) (hzy : z ≤ y) (hS : 1 ≤ S)
    (hshiftX : ∀ s ∈ shifts, s ≤ X) :
    let P := ascendingSievePrimes z y
    let D := y ^ S
    let stop := rosserStoppingPredicate 100 D
    (X : ℝ) * lowerMainTerm stop (shiftNu shifts) P - (D : ℝ) ^ 2 ≤
        ((siftedShiftCandidates shifts X z (y + 1)).card : ℝ) ∧
      ((siftedShiftCandidates shifts X z (y + 1)).card : ℝ) ≤
        (X : ℝ) * upperMainTerm stop (shiftNu shifts) P + (D : ℝ) ^ 2 := by
  classical
  dsimp only
  let P := ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := boundingSieve shifts hshifts hcard X z (y + 1) hz
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = Erdos387.sievePrimeProduct z (y + 1)
    exact ascendingSievePrimes_prod z y
  have hsort : P.Pairwise (· ≤ ·) :=
    ascendingSievePrimes_pairwise z y
  have hnodup : P.Nodup := ascendingSievePrimes_nodup z y
  have hprime : ∀ p ∈ P, p.Prime := ascendingSievePrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hlevel : ∀ p ∈ P, p ≤ D := by
    intro p hp
    have hpy : p ≤ y :=
      (mem_sievePrimes.mp (mem_ascendingSievePrimes.mp hp)).2.1
    exact hpy.trans (le_self_pow (by omega : 1 ≤ y) (by omega))
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hsq : Squarefree d :=
      Squarefree.squarefree_of_dvd hd sieve.prodPrimes_squarefree
    exact (boundingSieve_abs_rem_le_nuClasses hshiftX hd).trans
      (by exact_mod_cast nuClasses_le hsq)
  have hlower := boundingSieve_lowerMain_sub_sq_le_siftedSum
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro t ht hadm
      apply prod_le_of_lowerAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp ht))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
        (by
          intro p hp
          exact hlevel p ((List.mem_sublists.mp ht).subset hp)) hadm)
    hrem
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro t ht hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp ht))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
        hadm)
    hrem
  change
    sieve.totalMass * lowerMainTerm stop (fun p ↦ sieve.nu p) P -
        (D : ℝ) ^ 2 ≤ _ at hlower
  change _ ≤ sieve.totalMass * upperMainTerm stop (fun p ↦ sieve.nu p) P +
        (D : ℝ) ^ 2 at hupper
  rw [show sieve.totalMass = (X : ℝ) by exact boundingSieve_totalMass,
    show sieve.siftedSum =
        ((siftedShiftCandidates shifts X z (y + 1)).card : ℝ) by
      exact boundingSieve_siftedSum] at hlower hupper
  exact ⟨hlower, hupper⟩

open BetaSieveFundamental

/-- End-to-end dimension-one finite beta-sieve estimate for the actual
singleton-shift candidate set. -/
theorem exists_oneShift_concrete_cardinality_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ s X z y S : ℕ, s ≤ X → 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := localEulerProduct oneShiftDensity z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X : ℝ) * ((1 - eta) * V) - (D : ℝ) ^ 2 ≤
            ((siftedShiftCandidates {s} X z (y + 1)).card : ℝ) ∧
          ((siftedShiftCandidates {s} X z (y + 1)).card : ℝ) ≤
            (X : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_oneShift_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro s X z y S hsX hz hzy hy hS hlog
  dsimp only
  let P := ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  have hm := hmain z y S hz hzy hy hS hlog
  dsimp only at hm
  have hb := boundingSieve_cardinality_between_mainTerms
    (shifts := ({s} : Finset ℕ)) (X := X) (z := z) (y := y) (S := S)
    (by simp) (by simp)
    hz hzy (by omega) (by simpa using hsX)
  dsimp only at hb
  have hnu : ∀ p ∈ P, shiftNu {s} p = oneShiftDensity p := by
    intro p hp
    exact shiftNu_singleton_prime s
      (ascendingSievePrimes_prime p hp)
  rw [lowerMainTerm_congr_on stop (shiftNu {s}) oneShiftDensity P hnu,
    upperMainTerm_congr_on stop (shiftNu {s}) oneShiftDensity P hnu] at hb
  change
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          localEulerProduct oneShiftDensity z y ≤
        lowerMainTerm stop oneShiftDensity P ∧
      upperMainTerm stop oneShiftDensity P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          localEulerProduct oneShiftDensity z y at hm
  change
    (X : ℝ) * lowerMainTerm stop oneShiftDensity P - (D : ℝ) ^ 2 ≤
        ((siftedShiftCandidates {s} X z (y + 1)).card : ℝ) ∧
      ((siftedShiftCandidates {s} X z (y + 1)).card : ℝ) ≤
        (X : ℝ) * upperMainTerm stop oneShiftDensity P + (D : ℝ) ^ 2 at hb
  constructor
  · calc
      (X : ℝ) *
              ((1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                localEulerProduct oneShiftDensity z y) - (D : ℝ) ^ 2 ≤
          (X : ℝ) * lowerMainTerm stop oneShiftDensity P - (D : ℝ) ^ 2 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hm.1 (by positivity)) _
      _ ≤ ((siftedShiftCandidates {s} X z (y + 1)).card : ℝ) := hb.1
  · calc
      ((siftedShiftCandidates {s} X z (y + 1)).card : ℝ) ≤
          (X : ℝ) * upperMainTerm stop oneShiftDensity P + (D : ℝ) ^ 2 := hb.2
      _ ≤ (X : ℝ) *
              ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                localEulerProduct oneShiftDensity z y) + (D : ℝ) ^ 2 :=
        add_le_add
          (show (X : ℝ) * upperMainTerm stop oneShiftDensity P ≤
              (X : ℝ) *
                ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  localEulerProduct oneShiftDensity z y) from
            mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg X)) le_rfl

/-- End-to-end uniform dimension-two finite beta-sieve estimate for the
actual pair-shift candidate set. -/
theorem exists_pairShift_concrete_cardinality_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ s t X z y S : ℕ, s ≤ X → t ≤ X →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let V := localEulerProduct (pairShiftDensity (Nat.dist s t)) z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        (X : ℝ) * ((1 - eta) * V) - (D : ℝ) ^ 2 ≤
            ((siftedShiftCandidates {s, t} X z (y + 1)).card : ℝ) ∧
          ((siftedShiftCandidates {s, t} X z (y + 1)).card : ℝ) ≤
            (X : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_pairShift_concrete_finiteMainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro s t X z y S hsX htX hz hzy hy hS hlog
  dsimp only
  let P := ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  have hm := hmain (Nat.dist s t) z y S hz hzy hy hS hlog
  dsimp only at hm
  have hb := boundingSieve_cardinality_between_mainTerms
    (shifts := ({s, t} : Finset ℕ)) (X := X) (z := z) (y := y) (S := S)
    (by simp) Finset.card_le_two
    hz hzy (by omega) (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hsX
      · exact htX)
  dsimp only at hb
  have hnu : ∀ p ∈ P,
      shiftNu {s, t} p = pairShiftDensity (Nat.dist s t) p := by
    intro p hp
    exact shiftNu_pair_prime s t
      (ascendingSievePrimes_prime p hp)
  rw [lowerMainTerm_congr_on stop (shiftNu {s, t})
      (pairShiftDensity (Nat.dist s t)) P hnu,
    upperMainTerm_congr_on stop (shiftNu {s, t})
      (pairShiftDensity (Nat.dist s t)) P hnu] at hb
  change
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          localEulerProduct (pairShiftDensity (Nat.dist s t)) z y ≤
        lowerMainTerm stop (pairShiftDensity (Nat.dist s t)) P ∧
      upperMainTerm stop (pairShiftDensity (Nat.dist s t)) P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          localEulerProduct (pairShiftDensity (Nat.dist s t)) z y at hm
  change
    (X : ℝ) * lowerMainTerm stop (pairShiftDensity (Nat.dist s t)) P -
          (D : ℝ) ^ 2 ≤
        ((siftedShiftCandidates {s, t} X z (y + 1)).card : ℝ) ∧
      ((siftedShiftCandidates {s, t} X z (y + 1)).card : ℝ) ≤
        (X : ℝ) * upperMainTerm stop (pairShiftDensity (Nat.dist s t)) P +
          (D : ℝ) ^ 2 at hb
  constructor
  · calc
      (X : ℝ) *
              ((1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                localEulerProduct (pairShiftDensity (Nat.dist s t)) z y) -
              (D : ℝ) ^ 2 ≤
          (X : ℝ) * lowerMainTerm stop
              (pairShiftDensity (Nat.dist s t)) P - (D : ℝ) ^ 2 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hm.1 (by positivity)) _
      _ ≤ ((siftedShiftCandidates {s, t} X z (y + 1)).card : ℝ) := hb.1
  · calc
      ((siftedShiftCandidates {s, t} X z (y + 1)).card : ℝ) ≤
          (X : ℝ) * upperMainTerm stop
              (pairShiftDensity (Nat.dist s t)) P + (D : ℝ) ^ 2 := hb.2
      _ ≤ (X : ℝ) *
              ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                localEulerProduct (pairShiftDensity (Nat.dist s t)) z y) +
              (D : ℝ) ^ 2 :=
        add_le_add
          (show (X : ℝ) * upperMainTerm stop
                (pairShiftDensity (Nat.dist s t)) P ≤
              (X : ℝ) *
                ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  localEulerProduct (pairShiftDensity (Nat.dist s t)) z y) from
            mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg X)) le_rfl

end Erdos851
