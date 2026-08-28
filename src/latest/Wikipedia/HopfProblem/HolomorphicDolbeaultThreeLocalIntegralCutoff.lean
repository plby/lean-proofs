import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalIntegral

/-!
# Coordinate cutoffs and preservation of vanishing

These are elementary consequences of the actual derivative and integral.
They isolate the support facts needed when constructing local primitives.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- A smooth function of one coordinate is jointly smooth. -/
theorem contDiff_coordinateScalar (i : Fin 3) {n : ℕ∞} {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ n χ) : ContDiff ℝ n (fun q : Coordinates => χ (q i)) :=
  hχ.comp (ContinuousLinearMap.proj i : Coordinates →L[ℝ] ℂ).contDiff

/-- A function of one complex coordinate has zero derivative in every other
antiholomorphic coordinate direction. -/
theorem coordinateDbar_coordinateScalar_of_ne (i j : Fin 3) (h : j ≠ i)
    {χ : ℂ → ℂ} {q : Coordinates} (hχ : DifferentiableAt ℝ χ (q i)) :
    coordinateDbar j (fun p : Coordinates => χ (p i)) q = 0 := by
  let L : Coordinates →L[ℂ] ℂ := ContinuousLinearMap.proj i
  change HolomorphicDolbeaultThree.dbar (χ ∘ L) q (basisVector j) = 0
  rw [dbar_complex_linear_comp L hχ]
  change HolomorphicDolbeaultThree.dbar χ (q i) (basisVector j i) = 0
  rw [basisVector_of_ne h.symm, map_zero]

/-- Every coordinate derivative vanishes outside a closed uniform support in
any one of the coordinates. -/
theorem coordinateDbar_eq_zero_off_coordinate_support (i j : Fin 3)
    {f : Coordinates → ℂ} {k : Set ℂ} (hk : IsClosed k)
    (hfk : ∀ q, q i ∉ k → f q = 0) {q : Coordinates} (hq : q i ∉ k) :
    coordinateDbar j f q = 0 := by
  have he : f =ᶠ[𝓝 q] fun _ => (0 : ℂ) := by
    have hn : (fun p : Coordinates => p i) ⁻¹' kᶜ ∈ 𝓝 q :=
      (hk.isOpen_compl.preimage (continuous_apply i)).mem_nhds hq
    filter_upwards [hn] with p hp
    exact hfk p hp
  rw [coordinateDbar_congr j he]
  simp only [coordinateDbar, dbar_const, zero_apply]

/-- The coordinate integral of a function vanishing on the entire integrated
slice is genuinely zero. -/
theorem coordinateCauchy_eq_zero_of_slice_zero (i : Fin 3)
    {f : Coordinates → ℂ} (q : Coordinates)
    (hf : ∀ z : ℂ, f (Function.update q i z) = 0) : coordinateCauchy i f q = 0 := by
  simp only [coordinateCauchy, HolomorphicCousin.cauchyGreen, hf,
    mul_zero, integral_zero]

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
