/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.SignedSliceConcentration

/-!
# Fixed-size sampling concentration for Erdős Problem 636

This file supplies the small adapter missing from the concentration library
developed for Erdős Problem 88.  The sampler in
`Erdos88.BooleanSlices.productSignedSliceDecode` is a product of independent
uniform permutations.  Its fibers all have the same cardinality, so pushing
the product-permutation Azuma--Hoeffding inequality through the decoder gives
the corresponding inequality for uniform fixed-cardinality slices.

Taking `minus = 0` gives ordinary uniform subsets of prescribed size.  Using
several buckets gives the independent fixed-size choices that occur when the
two sides of a switching construction are ordered separately.
-/

open scoped BigOperators

namespace Erdos636
namespace Hypergeometric

open Classical Finset
open Erdos88
open Erdos88.BooleanSlices
open Erdos88.FiniteSliceConcentration

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A two-sided bounded-difference inequality on a product of independent
uniform signed slices.  Bucket `k` contains exactly `plus k` coordinates
labelled `+1` and `minus k` coordinates labelled `-1`.  A legal switch
interchanges two labels in one bucket.

For an ordinary uniform `s`-subset, use one bucket and take `plus = s` and
`minus = 0`; the variance proxy in the conclusion is then `s * a^2`. -/
theorem productSignedSlice_two_sided_probability {K : ℕ}
    (P : BucketPartition α (Fin K)) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (g : ProductSignedSlicePoint P plus minus → ℝ) (a t : ℝ)
    (hL : 0 < Finset.univ.sum (fun k : Fin K => plus k + minus k))
    (ha : 0 < a) (ht : 0 ≤ t)
    (hswitch : ∀ S T, IsProductSignedSwitch P S T →
      |g S - g T| ≤ a) :
    Erdos88.Concentration.uniformProbability (fun S =>
        t ≤ |g S - Erdos88.Concentration.uniformExpectation g|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (Finset.univ.sum
          (fun k : Fin K => plus k + minus k)) * a ^ 2)) := by
  let F : ProductSignedSliceSampler P → ℝ := fun σ =>
    g (productSignedSliceDecode P plus minus hcount e σ)
  have hprefix : PermutationProductPrefixDependent hcount F := by
    intro σ τ hστ
    apply congrArg g
    exact productSignedSliceDecode_eq_of_prefix
      P plus minus hcount e σ τ hστ
  have hsamplerSwitch : PermutationProductSwitchLipschitz F a := by
    intro σ τ k p q hk hsame
    rcases productSignedSliceDecode_left_swap
        P plus minus hcount e σ τ k p q hk hsame with heq | hrel
    · simp only [F, heq, sub_self, abs_zero]
      exact ha.le
    · exact hswitch _ _ hrel
  have htail := permutationProduct_two_sided_probability
    hcount F a t hL ha ht hprefix hsamplerSwitch
  have hmean : Erdos88.Concentration.uniformExpectation F =
      Erdos88.Concentration.uniformExpectation g := by
    exact uniformExpectation_productSignedSliceDecode
      P plus minus hcount e g
  rw [hmean] at htail
  rw [← uniformProbability_productSignedSliceDecode
    P plus minus hcount e
      (fun S => t ≤ |g S - Erdos88.Concentration.uniformExpectation g|)]
  exact htail

end Hypergeometric
end Erdos636
