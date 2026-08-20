import ErdosProblems.Erdos980.ElliottTail.Assembly
import ErdosProblems.Erdos980.ElliottTail.ExponentReduction
import ErdosProblems.Erdos980.ElliottTail.ModelBridge
import ErdosProblems.Erdos980.ElliottTail.SmoothRarityApplication

/-!
# Final assembly of the exact Elliott tail

This file reduces the final uniform-integrability theorem to the one
remaining prime-exponent medium estimate.  The large part is discharged by
the unconditional smooth-amplifier theorem, and monotonicity upgrades the
single cutoff returned by the medium estimate to every later cutoff, as
required by `UniformlyNegligibleTail`.
-/

namespace Erdos980.ElliottTail

open Filter
open scoped Topology

noncomputable section

/-- The exact prime-exponent medium estimate needed after all finite
Fourier, reciprocity, and ray-class large-sieve reductions. -/
def PrimeExponentMediumEstimate (ell : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M X : ℕ, ∀ x : ℕ, X ≤ x →
    normalizedMediumWeightedTail ell (rationalPrime M - 1)
      (smoothParameterY x) x ≤ ε

lemma normalizedWeightedTail_antitone_primeIndex
    (k x : ℕ) (hx : 2 ≤ x) :
    Antitone (fun M ↦
      normalizedWeightedTail k (rationalPrime M - 1) x) := by
  intro M N hMN
  unfold normalizedWeightedTail
  apply mul_le_mul_of_nonneg_left
  · apply weightedTailSum_antitone_cutoff
    have hprime := rationalPrime_strictMono.monotone hMN
    omega
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))
      (by positivity)

/-- Medium-tail smallness plus the unconditional smooth large-tail theorem
gives uniform smallness of the complete normalized tail. -/
theorem normalizedWeightedTail_uniform_of_primeExponentMedium
    (ell : ℕ) (hell : 2 ≤ ell)
    (hmedium : PrimeExponentMediumEstimate ell) :
    ∀ ε > 0, ∃ M₀, ∀ M ≥ M₀,
      ∀ᶠ x : ℕ in atTop,
        normalizedWeightedTail ell (rationalPrime M - 1) x < ε := by
  have hlargeTendsto :=
    normalizedWeightedTail_smoothParameter_tendsto_zero ell hell
  have hassembled :
      ∀ ε : ℝ, 0 < ε → ∃ M X : ℕ, ∀ x : ℕ, X ≤ x →
        normalizedWeightedTail ell (rationalPrime M - 1) x ≤ ε := by
    apply weightedTail_uniformIntegrable_of_medium_large
      (fun M x ↦ normalizedWeightedTail ell (rationalPrime M - 1) x)
      (fun M x ↦ normalizedMediumWeightedTail ell
        (rationalPrime M - 1) (smoothParameterY x) x)
      (fun x ↦ normalizedWeightedTail ell (smoothParameterY x) x)
    · intro M
      have hcutoff : ∀ᶠ x : ℕ in atTop,
          rationalPrime M - 1 ≤ smoothParameterY x :=
        tendsto_smoothParameterY_atTop.eventually
          (eventually_ge_atTop (rationalPrime M - 1))
      obtain ⟨X, hX⟩ := eventually_atTop.mp hcutoff
      refine ⟨X, fun x hx ↦ ?_⟩
      rw [normalizedWeightedTail_eq_medium_add_large
        ell (rationalPrime M - 1) (smoothParameterY x) x (hX x hx)]
    · exact hmedium
    · intro ε hε
      have hevent : ∀ᶠ x : ℕ in atTop,
          normalizedWeightedTail ell (smoothParameterY x) x < ε :=
        (tendsto_order.1 hlargeTendsto).2 ε hε
      obtain ⟨X, hX⟩ := eventually_atTop.mp hevent
      exact ⟨X, fun x hx ↦ (hX x hx).le⟩
  intro ε hε
  obtain ⟨M₀, X, hX⟩ := hassembled (ε / 2) (by positivity)
  refine ⟨M₀, fun M hM ↦ ?_⟩
  filter_upwards [eventually_ge_atTop (max X 2)] with x hx
  have hxX : X ≤ x := (le_max_left X 2).trans hx
  have hx2 : 2 ≤ x := (le_max_right X 2).trans hx
  calc
    normalizedWeightedTail ell (rationalPrime M - 1) x ≤
        normalizedWeightedTail ell (rationalPrime M₀ - 1) x :=
      normalizedWeightedTail_antitone_primeIndex ell x hx2 hM
    _ ≤ ε / 2 := hX x hxX
    _ < ε := by linarith

/-- Exact final model-tail theorem once the unconditional prime-exponent
medium estimate has been supplied. -/
theorem uniformlyNegligibleTail_of_primeExponentMedium
    (ell : ℕ) (hell : 2 ≤ ell)
    (hmedium : PrimeExponentMediumEstimate ell) :
    UniformlyNegligibleTail
      (primeValueTail (leastNonresidueModel ell hell)) erdos980Scale :=
  uniformlyNegligibleTail_leastNonresidueModel_of_normalizedWeightedTail
    hell (normalizedWeightedTail_uniform_of_primeExponentMedium
      ell hell hmedium)

/-- Once the medium estimate is known for every prime exponent, reduction
to the least prime divisor gives the exact uniform tail for every
`k ≥ 2`.  This is the final exponent-reduction interface consumed by the
main Erdős 980 assembly. -/
theorem uniformlyNegligibleTail_of_all_primeExponentMedium
    (hmedium : ∀ ell : ℕ, ell.Prime → PrimeExponentMediumEstimate ell)
    (k : ℕ) (hk : 2 ≤ k) :
    UniformlyNegligibleTail
      (primeValueTail (leastNonresidueModel k hk)) erdos980Scale := by
  have hk1 : k ≠ 1 := by omega
  have hprime : k.minFac.Prime := Nat.minFac_prime hk1
  apply uniformlyNegligibleTail_leastNonresidueModel_of_minFac k hk
  exact uniformlyNegligibleTail_of_primeExponentMedium
    k.minFac hprime.two_le (hmedium k.minFac hprime)

/-- The prime-exponent analytic input naturally splits into the quadratic
case and the odd-prime case. -/
theorem allPrimeExponentMediumEstimate_of_two_of_odd
    (hquadratic : PrimeExponentMediumEstimate 2)
    (hodd : ∀ ell : ℕ, ell.Prime → Odd ell →
      PrimeExponentMediumEstimate ell) :
    ∀ ell : ℕ, ell.Prime → PrimeExponentMediumEstimate ell := by
  intro ell hell
  rcases hell.eq_two_or_odd' with rfl | hellOdd
  · exact hquadratic
  · exact hodd ell hell hellOdd

/-- Final all-exponent reduction from the separately established quadratic
and odd-prime medium estimates. -/
theorem uniformlyNegligibleTail_of_two_of_odd_primeExponentMedium
    (hquadratic : PrimeExponentMediumEstimate 2)
    (hodd : ∀ ell : ℕ, ell.Prime → Odd ell →
      PrimeExponentMediumEstimate ell)
    (k : ℕ) (hk : 2 ≤ k) :
    UniformlyNegligibleTail
      (primeValueTail (leastNonresidueModel k hk)) erdos980Scale :=
  uniformlyNegligibleTail_of_all_primeExponentMedium
    (allPrimeExponentMediumEstimate_of_two_of_odd hquadratic hodd) k hk

end

end Erdos980.ElliottTail
