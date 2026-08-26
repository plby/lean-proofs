import ErdosProblems.Erdos380.ProbabilityParameters

/-! # The short-interval bound at the concrete scale -/

open Filter
open scoped Topology

namespace Erdos380

/-- Every parameter hypothesis of the finite short-interval estimate has
now been discharged. The only counting error left here is the explicitly
defined set of ineligible singleton anchors. -/
theorem exists_eventually_shortExcess_scale_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ E : ℕ, ∀ᶠ N : ℕ in atTop,
      ((shortExcessPointsUpTo N (shortWidth N)).card : ℝ) ≤
        E + Nat.sqrt N + 2 * shortWidth N +
        (2 * shortWidth N + 1 : ℝ) *
          (ineligibleSingletons N (cofactorScale N) (mixingBase N ^ 110)).card +
        (8 * shortWidth N + 4 : ℝ) * N / (squareScale N + 1) +
        K * neighborErrorFactor N * (singletonBadUpTo N).card := by
  obtain ⟨C, K, U₀, hC, hK, hU₀, E, T₀, d₀, P₀, hbound⟩ :=
    exists_shortExcess_normalized_bound
  refine ⟨K, hK, E, ?_⟩
  filter_upwards [eventually_probability_scale_thresholds T₀ d₀ P₀,
    eventually_shortWidth_le_mixingBase, eventually_shortWidth_mixing_bound C hC.le,
    eventually_shortWidth_le_probabilityParameter_pow, eventually_probability_log_budget,
    probabilityParameter_tendsto_atTop.eventually (eventually_ge_atTop U₀),
    eventually_ge_atTop 1,
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ))]
      with N hth hWT hmix hWU hbudget hU hN hL
  obtain ⟨hT, hR, hQ, hdQ, hTQ, hPQ⟩ := hth
  have hW := (shortWidth_log_bound hN hL).1
  have hD : 0 < squareScale N := pow_pos
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N)) 3000
  have hM : 1 ≤ Nat.sqrt N := by simpa using Nat.sqrt_le_sqrt hN
  have h := hbound (mixingBase N) hT N (replacementScale N) (cofactorScale N)
    hN hR hQ hdQ hTQ hPQ (shortWidth N) hW hWT hmix (squareScale N) (Nat.sqrt N)
    hD hM (probabilityParameter N) (Real.log (Nat.sqrt N : ℝ)) hU hWU hbudget le_rfl
  convert h using 1
  unfold neighborErrorFactor
  ring

end Erdos380
