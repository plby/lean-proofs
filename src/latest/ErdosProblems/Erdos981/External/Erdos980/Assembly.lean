/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The analytic assembly step in the proof of Erdos Problem 980.

The number-theoretic input naturally gives an asymptotic for each fixed value
of the least power nonresidue.  Passing from those fixed-value asymptotics to
the mean is not a formal interchange of two limits: one also needs uniform
integrability.  This file isolates and proves precisely that passage.
-/

import Mathlib

namespace Erdos980

open scoped BigOperators
open Asymptotics Filter

/-- A two-parameter remainder is uniformly negligible relative to `scale` if,
after deleting sufficiently many fixed levels, every later deletion has small
normalized remainder, uniformly for all sufficiently large cutoffs. -/
def UniformlyNegligibleTail (tail : ℕ → ℕ → ℝ) (scale : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ M₀, ∀ M ≥ M₀,
    ∀ᶠ x : ℕ in atTop, |tail M x / scale x| < ε

/-- Abstract fixed-pattern plus uniform-integrability assembly.

`piece j x` is the contribution of the `j`th fixed pattern below cutoff `x`,
and `tail M x` is the contribution remaining after the first `M` patterns.
The hypotheses say that every fixed normalized piece has limit `weight j`,
the weights form a convergent series, and the normalized tails are uniformly
negligible.  The conclusion is convergence of the normalized total to the
sum of the weights. -/
theorem tendsto_normalized_of_fixed_patterns_and_uniformTail
    (total scale : ℕ → ℝ) (piece : ℕ → ℕ → ℝ)
    (tail : ℕ → ℕ → ℝ) (weight : ℕ → ℝ)
    (hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop (nhds (weight j)))
    (hweight : Summable weight)
    (hdecomp : ∀ M x,
      total x = (∑ j ∈ Finset.range M, piece j x) + tail M x)
    (htail : UniformlyNegligibleTail tail scale) :
    Tendsto (fun x ↦ total x / scale x) atTop (nhds (∑' j, weight j)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hpartial := hweight.hasSum.tendsto_sum_nat
  have hpartialEventually :
      ∀ᶠ M : ℕ in atTop,
        dist (∑ j ∈ Finset.range M, weight j) (∑' j, weight j) < ε / 3 :=
    hpartial.eventually (Metric.ball_mem_nhds _ hthird)
  obtain ⟨Mpartial, hMpartial⟩ :=
    Filter.eventually_atTop.1 hpartialEventually
  obtain ⟨Mtail, hMtail⟩ := htail (ε / 3) hthird
  let M := max Mpartial Mtail
  have hhead :
      Tendsto
        (fun x ↦ ∑ j ∈ Finset.range M, piece j x / scale x)
        atTop (nhds (∑ j ∈ Finset.range M, weight j)) :=
    tendsto_finsetSum (Finset.range M) fun j _ ↦ hpiece j
  have hheadEventually :
      ∀ᶠ x : ℕ in atTop,
        dist (∑ j ∈ Finset.range M, piece j x / scale x)
          (∑ j ∈ Finset.range M, weight j) < ε / 3 :=
    hhead.eventually (Metric.ball_mem_nhds _ hthird)
  have htailEventually :
      ∀ᶠ x : ℕ in atTop, |tail M x / scale x| < ε / 3 :=
    hMtail M (le_max_right Mpartial Mtail)
  obtain ⟨Xhead, hXhead⟩ :=
    Filter.eventually_atTop.1 hheadEventually
  obtain ⟨Xtail, hXtail⟩ :=
    Filter.eventually_atTop.1 htailEventually
  refine ⟨max Xhead Xtail, ?_⟩
  intro x hx
  have hxHead := hXhead x ((le_max_left Xhead Xtail).trans hx)
  have hxTail := hXtail x ((le_max_right Xhead Xtail).trans hx)
  have hxPartial :
      dist (∑ j ∈ Finset.range M, weight j) (∑' j, weight j) < ε / 3 :=
    hMpartial M (le_max_left Mpartial Mtail)
  rw [Real.dist_eq] at hxHead hxPartial ⊢
  rw [hdecomp M x, add_div]
  rw [Finset.sum_div]
  calc
    |(∑ j ∈ Finset.range M, piece j x / scale x) +
          tail M x / scale x - ∑' j, weight j| =
        |((∑ j ∈ Finset.range M, piece j x / scale x) -
              ∑ j ∈ Finset.range M, weight j) +
            tail M x / scale x +
          ((∑ j ∈ Finset.range M, weight j) - ∑' j, weight j)| := by
            congr 1
            ring
    _ ≤ |(∑ j ∈ Finset.range M, piece j x / scale x) -
              ∑ j ∈ Finset.range M, weight j| +
            |tail M x / scale x| +
          |(∑ j ∈ Finset.range M, weight j) - ∑' j, weight j| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
    _ < ε := by linarith

/-- A fixed normalized pattern has a nonnegative limiting weight whenever the
pattern itself is nonnegative and the normalizing scale is eventually
positive. -/
lemma fixedPattern_weight_nonneg
    (scale : ℕ → ℝ) (piece : ℕ → ℕ → ℝ) (weight : ℕ → ℝ)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (hpiece_nonneg : ∀ j x, 0 ≤ piece j x)
    (hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop (nhds (weight j)))
    (j : ℕ) :
    0 ≤ weight j := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hpiece j)
  filter_upwards [hscale] with x hx
  exact div_nonneg (hpiece_nonneg j x) hx.le

/-- Uniform integrability itself forces convergence of the weighted density
series in the nonnegative situation.

Indeed, after fixing one uniformly small tail, every later partial head is at
most that fixed head plus the fixed tail.  Passing this inequality to the
fixed-pattern limits gives a uniform upper bound for all partial sums of the
nonnegative weights, ruling out divergence to `+∞`. -/
theorem summable_weight_of_fixed_patterns_and_uniformTail_of_nonneg
    (total scale : ℕ → ℝ) (piece : ℕ → ℕ → ℝ)
    (tail : ℕ → ℕ → ℝ) (weight : ℕ → ℝ)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (hpiece_nonneg : ∀ j x, 0 ≤ piece j x)
    (htail_nonneg : ∀ M x, 0 ≤ tail M x)
    (hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop (nhds (weight j)))
    (hdecomp : ∀ M x,
      total x = (∑ j ∈ Finset.range M, piece j x) + tail M x)
    (htail : UniformlyNegligibleTail tail scale) :
    Summable weight := by
  have hweight_nonneg : ∀ j, 0 ≤ weight j :=
    fixedPattern_weight_nonneg scale piece weight hscale hpiece_nonneg hpiece
  rw [summable_iff_not_tendsto_nat_atTop_of_nonneg hweight_nonneg]
  obtain ⟨M, hM⟩ := htail 1 zero_lt_one
  have htailM : ∀ᶠ x : ℕ in atTop, |tail M x / scale x| < 1 :=
    hM M le_rfl
  have hheadLimit (K : ℕ) :
      Tendsto
        (fun x ↦ (∑ j ∈ Finset.range K, piece j x) / scale x)
        atTop (nhds (∑ j ∈ Finset.range K, weight j)) := by
    simpa [Finset.sum_div] using
      (tendsto_finsetSum (Finset.range K) fun j _ ↦ hpiece j)
  have hbound_ge (N : ℕ) (hMN : M ≤ N) :
      (∑ j ∈ Finset.range N, weight j) ≤
        (∑ j ∈ Finset.range M, weight j) + 1 := by
    apply le_of_tendsto_of_tendsto (hheadLimit N) ((hheadLimit M).add_const 1)
    filter_upwards [hscale, htailM] with x hxScale hxTail
    have hhead_le :
        (∑ j ∈ Finset.range N, piece j x) ≤
          (∑ j ∈ Finset.range M, piece j x) + tail M x := by
      calc
        (∑ j ∈ Finset.range N, piece j x) ≤
            (∑ j ∈ Finset.range N, piece j x) + tail N x :=
              le_add_of_nonneg_right (htail_nonneg N x)
        _ = total x := (hdecomp N x).symm
        _ = (∑ j ∈ Finset.range M, piece j x) + tail M x := hdecomp M x
    have hnormalized_le :
        (∑ j ∈ Finset.range N, piece j x) / scale x ≤
          ((∑ j ∈ Finset.range M, piece j x) + tail M x) / scale x :=
      div_le_div_of_nonneg_right hhead_le hxScale.le
    have htail_lt : tail M x / scale x < 1 :=
      lt_of_le_of_lt (le_abs_self _) hxTail
    rw [add_div] at hnormalized_le
    linarith
  have hbound (N : ℕ) :
      (∑ j ∈ Finset.range N, weight j) ≤
        (∑ j ∈ Finset.range M, weight j) + 1 := by
    by_cases hMN : M ≤ N
    · exact hbound_ge N hMN
    · have hNM : N ≤ M := Nat.le_of_lt (Nat.lt_of_not_ge hMN)
      have hmono :
          (∑ j ∈ Finset.range N, weight j) ≤
            ∑ j ∈ Finset.range M, weight j := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hNM) fun j _ _ ↦ hweight_nonneg j
      linarith
  intro hdiverges
  have hlarge := hdiverges.eventually_gt_atTop
    ((∑ j ∈ Finset.range M, weight j) + 1)
  obtain ⟨N, hN⟩ := hlarge.exists
  exact (not_lt_of_ge (hbound N)) hN

/-- The asymptotic-equivalence form of the assembly theorem.  Positivity of
the assembled constant is exactly what makes multiplication by that constant
an admissible nonzero comparison function. -/
theorem isEquivalent_of_fixed_patterns_and_uniformTail
    (total scale : ℕ → ℝ) (piece : ℕ → ℕ → ℝ)
    (tail : ℕ → ℕ → ℝ) (weight : ℕ → ℝ)
    (hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop (nhds (weight j)))
    (hweight : Summable weight)
    (hdecomp : ∀ M x,
      total x = (∑ j ∈ Finset.range M, piece j x) + tail M x)
    (htail : UniformlyNegligibleTail tail scale)
    (hscale : ∀ᶠ x : ℕ in atTop, scale x ≠ 0)
    (hconstant : 0 < ∑' j, weight j) :
    total ~[atTop] (fun x ↦ (∑' j, weight j) * scale x) := by
  let c := ∑' j, weight j
  have hc : c ≠ 0 := ne_of_gt hconstant
  have hnormalized :
      Tendsto (fun x ↦ total x / scale x) atTop (nhds c) :=
    tendsto_normalized_of_fixed_patterns_and_uniformTail
      total scale piece tail weight hpiece hweight hdecomp htail
  have hden : ∀ᶠ x : ℕ in atTop, c * scale x ≠ 0 := by
    filter_upwards [hscale] with x hx
    exact mul_ne_zero hc hx
  apply (Asymptotics.isEquivalent_iff_tendsto_one hden).2
  have hratio :
      Tendsto (fun x ↦ (total x / scale x) / c) atTop (nhds (c / c)) :=
    hnormalized.div_const c
  have hratio' :
      Tendsto (fun x ↦ (total x / scale x) / c) atTop (nhds 1) := by
    simpa [hc] using hratio
  convert hratio' using 1
  funext x
  dsimp [c]
  ring

/-- Nonnegative assembly in which summability is a conclusion of uniform
integrability rather than a separate number-theoretic input. -/
theorem isEquivalent_of_fixed_patterns_and_uniformTail_of_nonneg
    (total scale : ℕ → ℝ) (piece : ℕ → ℕ → ℝ)
    (tail : ℕ → ℕ → ℝ) (weight : ℕ → ℝ)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (hpiece_nonneg : ∀ j x, 0 ≤ piece j x)
    (htail_nonneg : ∀ M x, 0 ≤ tail M x)
    (hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop (nhds (weight j)))
    (hdecomp : ∀ M x,
      total x = (∑ j ∈ Finset.range M, piece j x) + tail M x)
    (htail : UniformlyNegligibleTail tail scale)
    (hconstant : 0 < ∑' j, weight j) :
    total ~[atTop] (fun x ↦ (∑' j, weight j) * scale x) := by
  have hweight :=
    summable_weight_of_fixed_patterns_and_uniformTail_of_nonneg
      total scale piece tail weight hscale hpiece_nonneg htail_nonneg
        hpiece hdecomp htail
  apply isEquivalent_of_fixed_patterns_and_uniformTail
    total scale piece tail weight hpiece hweight hdecomp htail
  · filter_upwards [hscale] with x hx
    exact hx.ne'
  · exact hconstant

/-! ### A concrete interface for least-nonresidue values on primes -/

/-- Data expressing a prime-valued statistic by a monotone enumeration of its
nonzero values.  `level p = none` is the zero-valued (ineligible) case; a value
`some j` says that the statistic equals the `j`th enumerated value. -/
structure PrimeValueModel where
  value : ℕ → ℝ
  level : ℕ → Option ℕ
  enumeration : ℕ → ℝ
  enumeration_mono : Monotone enumeration
  value_spec : ∀ p,
    value p = match level p with
      | none => 0
      | some j => enumeration j

/-- Sum of the modeled statistic over primes strictly below `x`. -/
noncomputable def primeValueSum (model : PrimeValueModel) (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range x).filter Nat.Prime, model.value p

/-- Number of primes strictly below `x` having the `j`th modeled value. -/
noncomputable def primePatternCount
    (model : PrimeValueModel) (j x : ℕ) : ℝ :=
  (((Finset.range x).filter
    (fun p ↦ p.Prime ∧ model.level p = some j)).card : ℝ)

/-- Contribution of the first `M` fixed patterns. -/
noncomputable def primePatternHead
    (model : PrimeValueModel) (M x : ℕ) : ℝ :=
  ∑ j ∈ Finset.range M,
    model.enumeration j * primePatternCount model j x

/-- Exact remainder after the first `M` fixed-pattern contributions have been
removed from the prime sum.  Uniform integrability is precisely uniform
negligibility of this remainder. -/
noncomputable def primeValueTail
    (model : PrimeValueModel) (M x : ℕ) : ℝ :=
  primeValueSum model x - primePatternHead model M x

lemma primeValueSum_eq_head_add_tail
    (model : PrimeValueModel) (M x : ℕ) :
    primeValueSum model x =
      primePatternHead model M x + primeValueTail model M x := by
  simp [primeValueTail]

/-- Concrete assembly theorem for a statistic on primes whose values are
listed by a monotone enumeration.  The fixed-pattern input is stated as a
natural-density asymptotic for each individual pattern; multiplying by its
enumerated value produces the corresponding mean contribution. -/
theorem primeValueSum_isEquivalent_of_pattern_densities_and_uniformTail
    (model : PrimeValueModel) (scale density : ℕ → ℝ)
    (hpattern : ∀ j,
      Tendsto (fun x ↦ primePatternCount model j x / scale x)
        atTop (nhds (density j)))
    (hsummable : Summable (fun j ↦ model.enumeration j * density j))
    (htail : UniformlyNegligibleTail (primeValueTail model) scale)
    (hscale : ∀ᶠ x : ℕ in atTop, scale x ≠ 0)
    (hpositive : 0 < ∑' j, model.enumeration j * density j) :
    primeValueSum model ~[atTop]
      (fun x ↦ (∑' j, model.enumeration j * density j) * scale x) := by
  let piece : ℕ → ℕ → ℝ := fun j x ↦
    model.enumeration j * primePatternCount model j x
  have hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop
        (nhds (model.enumeration j * density j)) := by
    intro j
    simpa [piece, mul_div_assoc] using
      (tendsto_const_nhds.mul (hpattern j))
  apply isEquivalent_of_fixed_patterns_and_uniformTail
    (primeValueSum model) scale piece (primeValueTail model)
      (fun j ↦ model.enumeration j * density j)
      hpiece hsummable
  · intro M x
    rw [primeValueSum_eq_head_add_tail]
    rfl
  · exact htail
  · exact hscale
  · exact hpositive

/-- Concrete nonnegative assembly in which summability of the mean weights is
deduced from uniform integrability.  This is the form used for the exact
least-nonresidue model: its enumerated values and every finite pattern count
are nonnegative, and deleting a finite head leaves a nonnegative tail. -/
theorem primeValueSum_isEquivalent_of_pattern_densities_and_uniformTail_of_nonneg
    (model : PrimeValueModel) (scale density : ℕ → ℝ)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (henumeration : ∀ j, 0 ≤ model.enumeration j)
    (hpattern : ∀ j,
      Tendsto (fun x ↦ primePatternCount model j x / scale x)
        atTop (nhds (density j)))
    (htail_nonneg : ∀ M x, 0 ≤ primeValueTail model M x)
    (htail : UniformlyNegligibleTail (primeValueTail model) scale)
    (hpositive : 0 < ∑' j, model.enumeration j * density j) :
    primeValueSum model ~[atTop]
      (fun x ↦ (∑' j, model.enumeration j * density j) * scale x) := by
  let piece : ℕ → ℕ → ℝ := fun j x ↦
    model.enumeration j * primePatternCount model j x
  have hpiece_nonneg : ∀ j x, 0 ≤ piece j x := by
    intro j x
    exact mul_nonneg (henumeration j) (by
      unfold primePatternCount
      positivity)
  have hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop
        (nhds (model.enumeration j * density j)) := by
    intro j
    simpa [piece, mul_div_assoc] using
      (tendsto_const_nhds.mul (hpattern j))
  apply isEquivalent_of_fixed_patterns_and_uniformTail_of_nonneg
    (primeValueSum model) scale piece (primeValueTail model)
      (fun j ↦ model.enumeration j * density j)
      hscale hpiece_nonneg htail_nonneg hpiece
  · intro M x
    rw [primeValueSum_eq_head_add_tail]
    rfl
  · exact htail
  · exact hpositive

/-- Ratio-limit form of the concrete nonnegative assembly.  It deliberately
does not assume that the limiting mean is positive; positivity can therefore
be proved afterwards from a separate lower-density argument. -/
theorem primeValueSum_normalized_tendsto_of_pattern_densities_and_uniformTail_of_nonneg
    (model : PrimeValueModel) (scale density : ℕ → ℝ)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (henumeration : ∀ j, 0 ≤ model.enumeration j)
    (hpattern : ∀ j,
      Tendsto (fun x ↦ primePatternCount model j x / scale x)
        atTop (nhds (density j)))
    (htail_nonneg : ∀ M x, 0 ≤ primeValueTail model M x)
    (htail : UniformlyNegligibleTail (primeValueTail model) scale) :
    Tendsto (fun x ↦ primeValueSum model x / scale x) atTop
      (nhds (∑' j, model.enumeration j * density j)) := by
  let piece : ℕ → ℕ → ℝ := fun j x ↦
    model.enumeration j * primePatternCount model j x
  have hpiece_nonneg : ∀ j x, 0 ≤ piece j x := by
    intro j x
    exact mul_nonneg (henumeration j) (by
      unfold primePatternCount
      positivity)
  have hpiece : ∀ j,
      Tendsto (fun x ↦ piece j x / scale x) atTop
        (nhds (model.enumeration j * density j)) := by
    intro j
    simpa [piece, mul_div_assoc] using
      (tendsto_const_nhds.mul (hpattern j))
  have hdecomp : ∀ M x,
      primeValueSum model x =
        (∑ j ∈ Finset.range M, piece j x) + primeValueTail model M x := by
    intro M x
    rw [primeValueSum_eq_head_add_tail]
    rfl
  have hsummable :=
    summable_weight_of_fixed_patterns_and_uniformTail_of_nonneg
      (primeValueSum model) scale piece (primeValueTail model)
      (fun j ↦ model.enumeration j * density j)
      hscale hpiece_nonneg htail_nonneg hpiece hdecomp htail
  exact tendsto_normalized_of_fixed_patterns_and_uniformTail
    (primeValueSum model) scale piece (primeValueTail model)
      (fun j ↦ model.enumeration j * density j)
      hpiece hsummable hdecomp htail

/-- Positivity transfer for a normalized limit.  If an eventually positive
scale normalizes both a statistic and a pointwise lower bound, then a positive
limit for the lower bound forces a positive limit for the statistic. -/
theorem normalized_limit_pos_of_eventually_le
    (total lower scale : ℕ → ℝ) (c d : ℝ)
    (hscale : ∀ᶠ x : ℕ in atTop, 0 < scale x)
    (htotal : Tendsto (fun x ↦ total x / scale x) atTop (nhds c))
    (hlower : Tendsto (fun x ↦ lower x / scale x) atTop (nhds d))
    (hle : ∀ᶠ x : ℕ in atTop, lower x ≤ total x)
    (hd : 0 < d) :
    0 < c := by
  have hnormalized_le :
      ∀ᶠ x : ℕ in atTop, lower x / scale x ≤ total x / scale x := by
    filter_upwards [hscale, hle] with x hx hxt
    exact div_le_div_of_nonneg_right hxt hx.le
  have hdc : d ≤ c :=
    le_of_tendsto_of_tendsto hlower htotal hnormalized_le
  exact hd.trans_le hdc

end Erdos980
