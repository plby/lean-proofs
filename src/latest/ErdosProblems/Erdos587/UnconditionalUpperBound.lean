import ErdosProblems.Erdos587.DyadicSquareForcing
import ErdosProblems.Erdos587.AmbientDyadicScales

/-!
The unconditional Nguyen--Vu upper bound. All structural, analytic, and
numerical inputs are proved in the imported development; this theorem has
no conjectural hypotheses.
-/

open Filter

namespace Erdos587

theorem unconditional_nguyen_vu :
    ∃ᵉ (O > 0) (K > 0), ∀ᶠ N : ℕ in atTop,
      (MaxNotSqSum N : ℝ) ≤ K * Real.nthRoot 3 N * (N : ℝ).log ^ O := by
  obtain ⟨Z, B, hZ, hB, hforce⟩ := exists_dyadic_finite_square_forcing
  let d := 4 * B
  let e₀ := Nat.log 2 (Z * 4 ^ (4 * B) + 4 * Z + 1) + 1
  have he₀ : Z * 4 ^ (4 * B) + 4 * Z + 1 ≤ 2 ^ e₀ :=
    (dyadic_round_up_bounds (by omega : 0 < Z * 4 ^ (4 * B) + 4 * Z + 1)).1
  let K := Z * 2 ^ (e₀ + d) * 16 * 13 ^ (d + 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hscale : ∀ᶠ t : ℕ in atTop, Z ≤ 2 ^ t := by
    simpa only [pow_zero, mul_one] using eventually_nat_polynomial_le_two_pow Z 0
  apply NVGeneration.nguyen_vu_of_eventual_dyadic_square_forcing (d + 2) K (by omega) hK
  filter_upwards [eventually_ge_atTop 1,
    tendsto_ambient_dyadic_scale.eventually (eventually_dyadic_extra_le e₀ d),
    tendsto_ambient_dyadic_scale.eventually hscale,
    tendsto_ambient_dyadic_scale.eventually eventually_dyadic_initial_budget]
    with N hN hextra hZscale hinitial
  intro A hA hlarge
  let t := Nat.log 4096 N + 1
  let l := 12 * t + 1
  let e := e₀ + d * (Nat.log 2 l + 1)
  let H := 2 ^ (4 * t + e)
  have ht : 0 < t := by dsimp [t]; omega
  have hambient := (ambient_dyadic_scales hN).1
  have hA' : A ⊆ Finset.Icc 1 (2 ^ (12 * t)) := by
    intro a ha
    obtain ⟨ha₁, haN⟩ := Finset.mem_Icc.mp (hA ha)
    exact Finset.mem_Icc.mpr ⟨ha₁, haN.trans hambient⟩
  have hcard : Z * l ^ 2 * H < A.card :=
    (ambient_dyadic_threshold_upper Z d e₀ N hN).trans_lt hlarge
  obtain ⟨hsize, hcubic⟩ := dyadic_surplus_budgets Z B e₀ t he₀
  have hnot : ¬ SquareSubsetSumFree A := hforce t e A hA' ht hextra hZscale hinitial
    hcard hsize (by exact_mod_cast hcubic)
  by_contra hnone
  apply hnot
  intro S hSA hSne hsq
  exact hnone ⟨S, hSA, hSne, hsq⟩

end Erdos587
