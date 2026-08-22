/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AnnularOffspringKernel
import ErdosProblems.Erdos1165.AppendixDecoupling

/-!
# Endpoint-integrated kernels along a complete profile

Appendix A.6 integrates the spatial endpoint at every intermediate radial
word.  Consequently its one-level comparison is a scalar lower bound for a
weak composition, uniform in the random entrance positions.  This module
records the exact algebra which multiplies those heterogeneous one-level
bounds and then sums all weak-composition chains.

No fixed intermediate endpoint occurs here.  In particular, the theorem is
compatible with sequential strong Markov iteration: the endpoint produced
by one stopped word is merely the random entrance of the next stopped word.
-/

open scoped BigOperators

namespace Erdos1165.AnnularIntegratedProfileKernel

open AppendixFirstMoment PathInsertion ProfileGapChain ProfileSmallBall

noncomputable section

/-- Sum of `a+b` over all adjacent population pairs.  This is the exponent
with which a uniform one-step relative error is accumulated. -/
def radialWordLength : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => a + b + radialWordLength (b :: rest)

private lemma radialWordLength_cons_le (a : ℕ) : ∀ values : List ℕ,
    radialWordLength (a :: values) ≤ a + 2 * values.sum
  | [] => by simp [radialWordLength]
  | b :: rest => by
      have htail := radialWordLength_cons_le b rest
      simp only [radialWordLength, List.sum_cons]
      exact (Nat.add_le_add_left htail (a + b)).trans_eq (by ring)

lemma radialWordLength_le_two_mul_sum : ∀ values : List ℕ,
    radialWordLength values ≤ 2 * values.sum
  | [] => by simp [radialWordLength]
  | a :: rest => by
      have h := radialWordLength_cons_le a rest
      simp only [List.sum_cons]
      exact h.trans (by omega)

/-- The upper half of the parabolic window. -/
lemma inProfileWindow_le_three_mul_sq
    {delta : ℝ} (hdelta : delta ≤ 1) {l m : ℕ}
    (hl : 1 ≤ l) (hm : InProfileWindow delta l m) :
    m ≤ 3 * l ^ 2 := by
  have hlReal : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hexponent : 1 + delta ≤ (2 : ℝ) := by linarith
  have hpower : (l : ℝ) ^ (1 + delta) ≤ (l : ℝ) ^ 2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hlReal hexponent
  rw [InProfileWindow, abs_le] at hm
  dsimp only [profileCenter] at hm
  push_cast at hm
  have hmReal : (m : ℝ) ≤ 3 * (l : ℝ) ^ 2 := by linarith
  exact_mod_cast hmReal

lemma constrainedProfile_entry_le_three_mul_n_sq
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (i : Fin (n - 1)) :
    m i ≤ 3 * n ^ 2 := by
  have hlocal := inProfileWindow_le_three_mul_sq hdelta
    (show 1 ≤ scaleIndex i by simp [scaleIndex]) (hm i)
  have hscale : scaleIndex i ≤ n := by
    unfold scaleIndex
    omega
  exact hlocal.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hscale 2))

/-- A constrained HLOZ profile contains only `O(n^3)` radial letters.  The
constant six is deliberately coarse and is convenient for absorbing an
`O(n^-6)` row error. -/
theorem radialWordLength_profileList_le_six_mul_cube
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    radialWordLength (profileList m) ≤ 6 * n ^ 3 := by
  have hentry : ∀ a ∈ profileList m, a ≤ 3 * n ^ 2 := by
    rw [profileList, List.forall_mem_ofFn_iff]
    exact constrainedProfile_entry_le_three_mul_n_sq hdelta hm
  have hsum := List.sum_le_card_nsmul (profileList m) (3 * n ^ 2) hentry
  have hlength : (profileList m).length = n - 1 := by
    simp [profileList]
  have hsum' : (profileList m).sum ≤ 3 * n ^ 3 := by
    calc
      (profileList m).sum ≤ (n - 1) * (3 * n ^ 2) := by
        simpa [hlength, nsmul_eq_mul] using hsum
      _ ≤ n * (3 * n ^ 2) :=
        Nat.mul_le_mul_right (3 * n ^ 2) (Nat.sub_le n 1)
      _ = 3 * n ^ 3 := by ring
  exact (radialWordLength_le_two_mul_sum (profileList m)).trans
    (by nlinarith)

/-- A per-radial-letter error of order at most `n⁻³/12` loses at most a
factor two over every word of a constrained profile.  The actual radial
estimate is substantially smaller (`O(n⁻⁶)`). -/
theorem one_half_le_one_sub_pow_profileRadialWordLength
    {n : ℕ} {delta epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsmall : 12 * (n : ℝ) ^ 3 * epsilon ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (hdelta : delta ≤ 1) :
    (1 / 2 : ℝ) ≤
      (1 - epsilon) ^ radialWordLength (profileList m) := by
  have hlengthNat := radialWordLength_profileList_le_six_mul_cube hdelta hm
  have hlength : (radialWordLength (profileList m) : ℝ) ≤
      6 * (n : ℝ) ^ 3 := by
    exact_mod_cast hlengthNat
  have hcost : (radialWordLength (profileList m) : ℝ) * epsilon ≤ 1 / 2 := by
    nlinarith
  have hbern := AppendixDecoupling.one_sub_nat_mul_le_pow_one_sub
    hepsilon1 (radialWordLength (profileList m))
  calc
    (1 / 2 : ℝ) ≤
        1 - (radialWordLength (profileList m) : ℝ) * epsilon := by linarith
    _ ≤ (1 - epsilon) ^ radialWordLength (profileList m) := hbern

/-- Product of arbitrary endpoint-integrated one-level masses along a
weak-composition chain.  `edge depth a b g` may use a different literal
boundary state space at every depth; all that survives endpoint integration
is its scalar mass. -/
def integratedGapChainKernel
    (edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ) :
    (depth : ℕ) → (values : List ℕ) → GapChain values → ℝ
  | _, [], _ => 1
  | _, [_], _ => 1
  | depth, a :: b :: rest, chain =>
      edge depth a b chain.1 *
        integratedGapChainKernel edge (depth + 1) (b :: rest) chain.2

lemma integratedGapChainKernel_nonneg
    {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
    (hedge : ∀ depth a b g, 0 ≤ edge depth a b g) :
    ∀ depth values (chain : GapChain values),
      0 ≤ integratedGapChainKernel edge depth values chain
  | _, [], _ => by simp [integratedGapChainKernel]
  | _, [_], _ => by simp [integratedGapChainKernel]
  | depth, a :: b :: rest, chain => by
      exact mul_nonneg (hedge depth a b chain.1)
        (integratedGapChainKernel_nonneg hedge (depth + 1)
          (b :: rest) chain.2)

/-- Pointwise multiplication of the source-correct endpoint-integrated
one-level comparisons. -/
theorem one_sub_pow_radialWordLength_mul_gapChainMass_le :
    ∀ {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
      {epsilon : ℝ},
      0 ≤ epsilon → epsilon ≤ 1 →
      (∀ depth a b g, 0 ≤ edge depth a b g) →
      (∀ depth a b (g : GapPattern a b),
        (1 - epsilon) ^ (a + b) *
            (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
          edge depth a b g) →
      ∀ depth values (chain : GapChain values),
        (1 - epsilon) ^ radialWordLength values *
            gapChainMass values chain ≤
          integratedGapChainKernel edge depth values chain
  | edge, epsilon, hepsilon0, hepsilon1, hedge, hlower,
      _, [], _ => by simp [radialWordLength, gapChainMass,
        integratedGapChainKernel]
  | edge, epsilon, hepsilon0, hepsilon1, hedge, hlower,
      _, [_], _ => by simp [radialWordLength, gapChainMass,
        integratedGapChainKernel]
  | edge, epsilon, hepsilon0, hepsilon1, hedge, hlower,
      depth, a :: b :: rest, chain => by
      have hhead := hlower depth a b chain.1
      have htail := one_sub_pow_radialWordLength_mul_gapChainMass_le
        hepsilon0 hepsilon1 hedge hlower (depth + 1) (b :: rest) chain.2
      have hhead0 : 0 ≤ (1 - epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity chain.1 i)) :=
        mul_nonneg (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
          (Finset.prod_nonneg fun _ _ ↦ halfGeometricMass_nonneg _)
      have htail0 : 0 ≤ (1 - epsilon) ^ radialWordLength (b :: rest) *
          gapChainMass (b :: rest) chain.2 :=
        mul_nonneg (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
          (gapChainMass_nonneg chain.2)
      calc
        (1 - epsilon) ^ radialWordLength (a :: b :: rest) *
            gapChainMass (a :: b :: rest) chain =
          ((1 - epsilon) ^ (a + b) *
              (∏ i, halfGeometricMass (gapMultiplicity chain.1 i))) *
            ((1 - epsilon) ^ radialWordLength (b :: rest) *
              gapChainMass (b :: rest) chain.2) := by
                simp only [radialWordLength, gapChainMass, pow_add]
                ring
        _ ≤ edge depth a b chain.1 *
            integratedGapChainKernel edge (depth + 1)
              (b :: rest) chain.2 :=
          mul_le_mul hhead htail htail0 (hedge depth a b chain.1)
        _ = integratedGapChainKernel edge depth
              (a :: b :: rest) chain := rfl

/-- After summing every endpoint-integrated radial word, the reference sum
is exactly the negative-binomial transition product. -/
theorem one_sub_pow_radialWordLength_mul_transitionProduct_le_sum
    {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g, 0 ≤ edge depth a b g)
    (hlower : ∀ depth a b (g : GapPattern a b),
      (1 - epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
        edge depth a b g)
    (depth : ℕ) (values : List ℕ)
    (hpos : ∀ a ∈ values, 0 < a) :
    (1 - epsilon) ^ radialWordLength values * transitionProduct values ≤
      ∑ chain : GapChain values,
        integratedGapChainKernel edge depth values chain := by
  rw [← sum_gapChainMass_eq_transitionProduct values hpos,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun chain _ ↦
    one_sub_pow_radialWordLength_mul_gapChainMass_le
      hepsilon0 hepsilon1 hedge hlower depth values chain

/-- Profile specialization: the endpoint-integrated radial word sum is
bounded below by the exact HLOZ profile weight, with only the accumulated
relative row loss. -/
theorem one_sub_pow_profileRadialWordLength_mul_profileWeight_le_sum
    {n : ℕ} {delta epsilon : ℝ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
    (hedge : ∀ depth a b g, 0 ≤ edge depth a b g)
    (hlower : ∀ depth a b (g : GapPattern a b),
      (1 - epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
        edge depth a b g)
    (depth : ℕ) :
    (1 - epsilon) ^ radialWordLength (profileList m) * profileWeight m ≤
      ∑ chain : GapChain (profileList m),
        integratedGapChainKernel edge depth (profileList m) chain := by
  apply one_sub_pow_radialWordLength_mul_transitionProduct_le_sum
    hepsilon0 hepsilon1 hedge hlower
  intro a ha
  have hatwo := constrainedProfile_all_entries_two_le hdelta hm a ha
  omega

end

end Erdos1165.AnnularIntegratedProfileKernel
