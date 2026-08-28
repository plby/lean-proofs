import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspToric
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionExponentialCore

/-!
# Literal vertical-action coordinates in every actual toric chart

The second fibre-torus cocharacter has weights `(-1, 0, 1)` in both kinds
of integral triangle, independently of its position. These are formulas
for the constructed monomial scaling and the actual toric inclusions, not
only pairings of abstract lattice vectors.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric

open ToricCharts ToricFan ToricFan.Triangle ToricSpace

/-- The literal second column of every triangle's dual character matrix. -/
theorem dual_second_column (a : Triangle) :
    (fun i : Fin 3 => a.dual i 1) = ![-1, 0, 1] := by
  ext i
  cases ha : a.upper <;> fin_cases i <;> simp [Triangle.dual, ha]

/-- The three actual monomial factors of vertical fibre multiplication. -/
theorem factors_verticalMultiplier (a : Triangle) (u : ℂˣ) :
    factors a (fibreMultiplier ![1, u]) = ![(u : ℂ)⁻¹, 1, (u : ℂ)] := by
  ext i
  cases ha : a.upper <;> fin_cases i <;>
    simp [factors, monomial, Triangle.dual, ha, fibreMultiplier, Fin.prod_univ_succ]

/-- The vertical multiplicative action in every affine toric chart. -/
theorem scale_verticalMultiplier (a : Triangle) (u : ℂˣ) (z : CoordinateSpace 3) :
    scale a (fibreMultiplier ![1, u]) z =
      ![(u : ℂ)⁻¹ * z 0, z 1, (u : ℂ) * z 2] := by
  rw [scale, factors_verticalMultiplier]
  ext i
  fin_cases i <;> simp

/-- The original additive flow uses precisely the proved normalized exponential. -/
theorem multiplier_eq_verticalMultiplier (s : ℂ) :
    Cusp.multiplier s = fibreMultiplier ![1, Exponential.normalizedExponential s] := rfl

/-- The requested literal exponential scaling, valid on the entire chart,
including every coordinate boundary stratum. -/
theorem scale_multiplier (s : ℂ) (a : Triangle) (z : CoordinateSpace 3) :
    scale a (Cusp.multiplier s) z =
      ![(Complex.exp (2 * Real.pi * Complex.I * s))⁻¹ * z 0,
        z 1, Complex.exp (2 * Real.pi * Complex.I * s) * z 2] := by
  rw [multiplier_eq_verticalMultiplier, scale_verticalMultiplier]
  rfl

/-- The actual toric action has the displayed coordinates in every chart. -/
theorem torusAction_vertical_inclusion (u : ℂˣ) (a : Triangle) (z : CoordinateSpace 3) :
    torusAction (fibreMultiplier ![1, u]) (inclusion a z) =
      inclusion a ![(u : ℂ)⁻¹ * z 0, z 1, (u : ℂ) * z 2] := by
  rw [torusAction_inclusion, scale_verticalMultiplier]

/-- The actual additive flow, rather than only its lattice weights, in
the native toric chart. -/
theorem toricFlow_inclusion_coordinates (s : ℂ) (a : Triangle) (z : CoordinateSpace 3) :
    Cusp.toricFlow s (inclusion a z) =
      inclusion a ![(Complex.exp (2 * Real.pi * Complex.I * s))⁻¹ * z 0,
        z 1, Complex.exp (2 * Real.pi * Complex.I * s) * z 2] := by
  rw [Cusp.toricFlow_inclusion, scale_multiplier]

/-- Any single nonidentity vertical scalar has exactly the middle
coordinate axis as its fixed locus in each toric chart. -/
theorem scale_verticalMultiplier_eq_self_iff (a : Triangle) (u : ℂˣ)
    (hu : u ≠ 1) (z : CoordinateSpace 3) :
    scale a (fibreMultiplier ![1, u]) z = z ↔ z 0 = 0 ∧ z 2 = 0 := by
  rw [scale_verticalMultiplier]
  have hune : (u : ℂ) ≠ 1 := fun h => hu (Units.ext h)
  have hinv : (u : ℂ)⁻¹ ≠ 1 := fun h => hune (inv_eq_one.mp h)
  constructor
  · intro h
    have hzero := congrFun h 0
    have htwo := congrFun h 2
    change (u : ℂ)⁻¹ * z 0 = z 0 at hzero
    change (u : ℂ) * z 2 = z 2 at htwo
    have hzero' : ((u : ℂ)⁻¹ - 1) * z 0 = 0 := by linear_combination hzero
    have htwo' : ((u : ℂ) - 1) * z 2 = 0 := by linear_combination htwo
    exact ⟨(mul_eq_zero.mp hzero').resolve_left (sub_ne_zero.mpr hinv),
      (mul_eq_zero.mp htwo').resolve_left (sub_ne_zero.mpr hune)⟩
  · rintro ⟨hzero, htwo⟩
    ext i
    fin_cases i <;> simp [hzero, htwo]

/-- Injectivity of the genuine affine toric inclusion turns the literal
scaling computation into an actual fixed-point characterization. -/
theorem torusAction_vertical_inclusion_fixed_iff (u : ℂˣ) (hu : u ≠ 1)
    (a : Triangle) (z : CoordinateSpace 3) :
    torusAction (fibreMultiplier ![1, u]) (inclusion a z) = inclusion a z ↔
      z 0 = 0 ∧ z 2 = 0 := by
  rw [torusAction_inclusion, (inclusion_openEmbedding a).injective.eq_iff]
  exact scale_verticalMultiplier_eq_self_iff a u hu z

/-- Every scalar fixes the displayed middle axis, including the identity. -/
theorem torusAction_vertical_inclusion_fixed (u : ℂˣ) (a : Triangle)
    (z : CoordinateSpace 3) (hz : z 0 = 0 ∧ z 2 = 0) :
    torusAction (fibreMultiplier ![1, u]) (inclusion a z) = inclusion a z := by
  rw [torusAction_vertical_inclusion]
  apply congrArg (inclusion a)
  ext i
  fin_cases i <;> simp [hz.1, hz.2]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric
