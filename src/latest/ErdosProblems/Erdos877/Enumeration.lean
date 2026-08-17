/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos877.SchurHypergraph
import ErdosProblems.Erdos877.EnumerationContainer
import ErdosProblems.Erdos877.EnumerationFingerprints
import ErdosProblems.Erdos877.EnumerationSupersaturationAlt
import ErdosProblems.Erdos877.EnumerationArithmetic

/-!
# Enumeration of sum-free subsets

This file combines the finite Schur-hypergraph container, supersaturation,
and fingerprint count.  Its final theorem is the explicit eventual
`2^(1/2+o(1))` upper bound needed in the resolution of Erdős Problem 877.
-/

open Finset
open Filter
open scoped BigOperators

namespace Erdos877
namespace Enumeration

theorem fingerprintP_pos : 0 < fingerprintP := by
  norm_num [fingerprintP, fingerprintR, fingerprintK]

theorem fingerprintP_le_one : fingerprintP ≤ 1 := by
  norm_num [fingerprintP, fingerprintR, fingerprintK]

theorem fingerprintP_le_one_div_72 : fingerprintP ≤ 1 / 72 := by
  norm_num [fingerprintP, fingerprintR, fingerprintK]

@[simp] theorem card_naturalsOf {n : ℕ} (I : Finset (Fin n)) :
    (naturalsOf I).card = I.card := by
  exact Finset.card_image_iff.mpr vertexNat_injective.injOn

/-- A completely explicit threshold beyond which the quadratic
supersaturation term dominates the linear container edge bound. -/
def enumerationCutoff : ℕ :=
  4 * enumerationLinearConstant * (2 ^ 35) * (2 ^ 35)

/-- Uniformly in the fingerprint, every canonical container is eventually
within `2⁻³² n` of the half-size barrier. -/
theorem schurCanonicalContainer_card_le (n : ℕ) (hn : enumerationCutoff ≤ n)
    (S : Finset (Fin n)) :
    (schurCanonicalContainer (n := n) fingerprintP_pos S).card ≤
      n / 2 + n / 2 ^ 32 := by
  let C := schurCanonicalContainer (n := n) fingerprintP_pos S
  let A := naturalsOf C
  have hCcard : C.card ≤ n := by
    calc
      C.card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ C)
      _ = n := by simp
  have hnotDense :
      ¬ (((2 : ℕ) ^ 34 + 1) * n ≤ (2 : ℕ) ^ 35 * C.card) := by
    intro hdense
    have hAinterval : A ⊆ interval n := naturalsOf_subset_interval C
    have hdenseA :
        ((2 : ℕ) ^ 34 + 1) * n ≤ (2 : ℕ) ^ 35 * A.card := by
      simpa [A] using hdense
    have hsup := Erdos877.EnumerationAlt.fixedDensity_sq_le_schurPairs
      A n hAinterval hdenseA
    have hedgeC := schurCanonicalContainer_edge_bound
      fingerprintP_pos fingerprintP_le_one fingerprintP_le_one_div_72 S
    have hedgePairs :
        fingerprintP ^ 2 * ((schurPairs A).card : ℝ) ≤ 6 * (C.card : ℝ) := by
      change fingerprintP ^ 2 *
        ((schurPairs (naturalsOf C)).card : ℝ) ≤ 6 * (C.card : ℝ)
      rw [card_schurPairs_eq_card_schurHypergraph_restrict n C]
      exact hedgeC
    have hlinear :
        2 * (schurPairs A).card + 3 * n ≤ enumerationLinearConstant * n :=
      schur_linear_bound hCcard hedgePairs
    have hsquare :
        enumerationLinearConstant * n <
          (n / (2 : ℕ) ^ 35 - 1) * (n / (2 : ℕ) ^ 35 - 1) := by
      apply square_floor_sub_one_eventually
      · norm_num
      · exact enumerationLinearConstant_pos
      · exact hn
    omega
  have hsmall := card_le_half_add_small_of_fixedDensity_failure hnotDense
  simpa [C] using hsmall

/-- The explicit finite union of Boolean lattices supplied by the canonical
containers. -/
noncomputable def sumFreeContainerCover (n : ℕ) : Finset (Finset ℕ) :=
  (realCutoffFingerprints n).biUnion fun S ↦
    (naturalsOf (schurCanonicalContainer (n := n) fingerprintP_pos S)).powerset

theorem sumFreeSets_subset_containerCover (n : ℕ) :
    sumFreeSets n ⊆ sumFreeContainerCover n := by
  classical
  intro A hA
  have hAdata := mem_sumFreeSets.mp hA
  obtain ⟨S, hSA, hScard, hAC⟩ :=
    exists_schurCanonicalContainer hAdata.1 hAdata.2
      fingerprintP_pos fingerprintP_le_one_div_72
  rw [sumFreeContainerCover, Finset.mem_biUnion]
  refine ⟨S, mem_realCutoffFingerprints.mpr hScard, ?_⟩
  exact Finset.mem_powerset.mpr hAC

/-- Counting a finite union of Boolean lattices when all canonical
containers have cardinality at most `M`. -/
theorem sumFreeCount_le_fingerprints_mul_pow (n M : ℕ)
    (hsmall : ∀ S ∈ realCutoffFingerprints n,
      (schurCanonicalContainer (n := n) fingerprintP_pos S).card ≤ M) :
    sumFreeCount n ≤ (realCutoffFingerprints n).card * 2 ^ M := by
  classical
  calc
    sumFreeCount n = (sumFreeSets n).card := rfl
    _ ≤ (sumFreeContainerCover n).card :=
      Finset.card_le_card (sumFreeSets_subset_containerCover n)
    _ ≤ ∑ S ∈ realCutoffFingerprints n,
        ((naturalsOf (schurCanonicalContainer (n := n)
          fingerprintP_pos S)).powerset).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ realCutoffFingerprints n, 2 ^ M := by
      apply Finset.sum_le_sum
      intro S hS
      rw [Finset.card_powerset, card_naturalsOf]
      exact pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) (hsmall S hS)
    _ = (realCutoffFingerprints n).card * 2 ^ M := by simp

/-- Explicit finite form of the eventual Cameron--Erdős upper bound. -/
theorem sumFreeCount_le_pow (n : ℕ) (hn : enumerationCutoff ≤ n) :
    sumFreeCount n ≤ 2 ^ (n / 2 + n / 2 ^ 30) := by
  let M := n / 2 + n / 2 ^ 32
  have hcontainers : ∀ S ∈ realCutoffFingerprints n,
      (schurCanonicalContainer (n := n) fingerprintP_pos S).card ≤ M := by
    intro S hS
    exact schurCanonicalContainer_card_le n hn S
  have hcount := sumFreeCount_le_fingerprints_mul_pow n M hcontainers
  have hfingerprints := card_realCutoffFingerprints_le n
  have hexponent : n / 2 ^ 32 + M ≤ n / 2 + n / 2 ^ 30 := by
    dsimp [M]
    omega
  calc
    sumFreeCount n ≤ (realCutoffFingerprints n).card * 2 ^ M := hcount
    _ ≤ 2 ^ (n / 2 ^ 32) * 2 ^ M :=
      Nat.mul_le_mul_right (2 ^ M) hfingerprints
    _ = 2 ^ (n / 2 ^ 32 + M) := by
      simpa only using (pow_add 2 (n / 2 ^ 32) M).symm
    _ ≤ 2 ^ (n / 2 + n / 2 ^ 30) :=
      pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) hexponent

/-- All sum-free subsets of `[1,n]` are eventually bounded by
`2^(n/2+n/2³⁰)`. -/
theorem eventually_sumFreeCount_le_pow :
    ∀ᶠ n : ℕ in atTop,
      sumFreeCount n ≤ 2 ^ (n / 2 + n / 2 ^ 30) := by
  filter_upwards [eventually_ge_atTop enumerationCutoff] with n hn
  exact sumFreeCount_le_pow n hn

/-- Real-exponent form: for all sufficiently large `n`, the number of
sum-free subsets is at most `2^((1/2+2⁻³⁰)n)`. -/
theorem eventually_sumFreeCount_le_rpow :
    ∀ᶠ n : ℕ in atTop,
      (sumFreeCount n : ℝ) ≤
        Real.rpow 2 (((1 / 2 : ℝ) + 1 / (2 : ℝ) ^ 30) * n) := by
  filter_upwards [eventually_sumFreeCount_le_pow] with n hn
  let E := n / 2 + n / 2 ^ 30
  have htwoNat : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hlargeNat : (2 : ℕ) ^ 30 * (n / 2 ^ 30) ≤ n :=
    Nat.mul_div_le n (2 ^ 30)
  have htwo : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast htwoNat
  have hlarge : ((2 : ℕ) ^ 30 : ℝ) * ((n / 2 ^ 30 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hlargeNat
  have hexponent :
      (E : ℝ) ≤ ((1 / 2 : ℝ) + 1 / (2 : ℝ) ^ 30) * n := by
    dsimp [E]
    push_cast
    norm_num at hlarge ⊢
    nlinarith
  calc
    (sumFreeCount n : ℝ) ≤ ((2 ^ E : ℕ) : ℝ) := by
      exact_mod_cast hn
    _ = (2 : ℝ) ^ E := by norm_num
    _ = Real.rpow 2 (E : ℝ) := (Real.rpow_natCast 2 E).symm
    _ ≤ Real.rpow 2 (((1 / 2 : ℝ) + 1 / (2 : ℝ) ^ 30) * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

end Enumeration
end Erdos877
