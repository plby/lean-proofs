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

import ErdosProblems.Erdos1165.ProfileSmallBall

/-!
# Weak-composition chains realizing an Appendix-A profile

For a transition from `a` excursions to `b` excursions, a weak composition
`g : GapPattern a b` records the numbers of offspring produced by the `a`
parent excursions.  A `GapChain values` chooses such a composition at every
successive pair in `values`.

The principal theorem says that summing the product of the elementary
geometric offspring masses over every gap chain is exactly the profile's
negative-binomial transition product.  This is the combinatorial input used
by a full complementary-skeleton disintegration: marked Poisson-kernel
comparisons may be applied to the individual offspring pieces before the
weak compositions are summed.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.ProfileGapChain

open AppendixFirstMoment PathInsertion ProfileSmallBall

noncomputable section

/-- A weak composition at every edge of a list of excursion counts. -/
def GapChain : List ℕ → Type
  | [] => Unit
  | [_] => Unit
  | a :: b :: rest => GapPattern a b × GapChain (b :: rest)

/-- A positive offspring count cannot be distributed among zero parents. -/
lemma gapPattern_source_pos_of_target_pos
    {a b : ℕ} (pattern : GapPattern a b) (hb : 0 < b) :
    0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  subst a
  have hsum := sum_gapMultiplicity pattern
  simp at hsum
  omega

/-- If the last count in a gap chain is positive, every earlier count is
positive as well. -/
theorem gapChain_all_positive_of_last_positive :
    ∀ (head : ℕ) (tail : List ℕ) (chain : GapChain (head :: tail)),
      0 < (head :: tail).getLast (by simp) →
        ∀ a ∈ head :: tail, 0 < a
  | head, [], _chain, hlast => by
      simpa using hlast
  | head, next :: rest, chain, hlast => by
      have htail : ∀ a ∈ next :: rest, 0 < a :=
        gapChain_all_positive_of_last_positive next rest chain.2 (by
          simpa using hlast)
      have hnext : 0 < next := htail next (by simp)
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact gapPattern_source_pos_of_target_pos chain.1 hnext
      · exact htail a (by simpa using ha)

noncomputable instance instFintypeGapChain : ∀ values, Fintype (GapChain values)
  | [] => inferInstanceAs (Fintype Unit)
  | [_] => inferInstanceAs (Fintype Unit)
  | a :: b :: rest =>
      @instFintypeProd (GapPattern a b) (GapChain (b :: rest))
        inferInstance (instFintypeGapChain (b :: rest))

noncomputable instance instDecidableEqGapChain : ∀ values,
    DecidableEq (GapChain values)
  | [] => inferInstanceAs (DecidableEq Unit)
  | [_] => inferInstanceAs (DecidableEq Unit)
  | a :: b :: rest =>
      @instDecidableEqProd (GapPattern a b) (GapChain (b :: rest))
        inferInstance (instDecidableEqGapChain (b :: rest))

/-- Product of the elementary geometric offspring masses along a chain. -/
def gapChainMass : (values : List ℕ) → GapChain values → ℝ
  | [], _ => 1
  | [_], _ => 1
  | _a :: b :: rest, chain =>
      (∏ i, halfGeometricMass (gapMultiplicity chain.1 i)) *
        gapChainMass (b :: rest) chain.2

lemma gapChainMass_nonneg : ∀ {values} (chain : GapChain values),
    0 ≤ gapChainMass values chain
  | [], _ => by simp [gapChainMass]
  | [_], _ => by simp [gapChainMass]
  | _a :: b :: rest, chain => by
      exact mul_nonneg
        (Finset.prod_nonneg fun _ _ ↦ halfGeometricMass_nonneg _)
        (gapChainMass_nonneg (values := b :: rest) chain.2)

/-- The finite sum of all gap-chain masses is the exact product of
successive critical negative-binomial transition masses. -/
theorem sum_gapChainMass_eq_transitionProduct : ∀ values : List ℕ,
    (∀ a ∈ values, 0 < a) →
      ∑ chain : GapChain values, gapChainMass values chain =
        transitionProduct values
  | [], _ => by
      change ∑ _chain : Unit, (1 : ℝ) = 1
      simp
  | [_a], _ => by
      change ∑ _chain : Unit, (1 : ℝ) = 1
      simp
  | a :: b :: rest, hpos => by
      have ha : 0 < a := hpos a (by simp)
      have htail : ∀ c ∈ b :: rest, 0 < c := fun c hc ↦ hpos c (by simp [hc])
      rw [transitionProduct_cons_cons]
      change (∑ chain : GapPattern a b × GapChain (b :: rest),
        (∏ i, halfGeometricMass (gapMultiplicity chain.1 i)) *
          gapChainMass (b :: rest) chain.2) = _
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [sum_gapChainMass_eq_transitionProduct (b :: rest) htail]
      rw [transitionMass_eq_sum_geometric_offspring ha b]

/-- ENNReal form used directly in marked-kernel mass comparisons. -/
theorem sum_ofReal_gapChainMass_eq_ofReal_transitionProduct
    (values : List ℕ) (hpos : ∀ a ∈ values, 0 < a) :
    ∑ chain : GapChain values, ENNReal.ofReal (gapChainMass values chain) =
      ENNReal.ofReal (transitionProduct values) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun chain _ ↦ gapChainMass_nonneg chain),
    sum_gapChainMass_eq_transitionProduct values hpos]

/-- Profile specialization of the exact gap-chain identity. -/
theorem sum_gapChainMass_profile_eq_profileWeight
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    ∑ chain : GapChain (profileList m),
        gapChainMass (profileList m) chain = profileWeight m := by
  exact sum_gapChainMass_eq_transitionProduct (profileList m)
    (fun a ha ↦ by
      have := constrainedProfile_all_entries_two_le hdelta hm a ha
      omega)

/-- ENNReal profile specialization. -/
theorem sum_ofReal_gapChainMass_profile_eq_ofReal_profileWeight
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    ∑ chain : GapChain (profileList m),
        ENNReal.ofReal (gapChainMass (profileList m) chain) =
      ENNReal.ofReal (profileWeight m) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun chain _ ↦ gapChainMass_nonneg chain),
    sum_gapChainMass_profile_eq_profileWeight hdelta hm]

end

end Erdos1165.ProfileGapChain
