import Wikipedia.HopfProblem.HolomorphicDifferentialFormsCoordinates
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsTopCovariance

/-!
# Reconstruction from actual alternating-covector coefficients

The coefficients are evaluations on the genuine base-first basis of the
period-family model. Multilinearity and alternation reconstruct every
one-, two-, and three-covector, not just a chosen family of coordinate forms.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates

/-- Every actual model vector is the sum of its three original coordinate
components in the base-first basis. -/
theorem basis_decomposition (u : Model) :
    u = u.1 • basis 0 + u.2 0 • basis 1 + u.2 1 • basis 2 := by
  simpa [Fin.sum_univ_three, TrianglePeriodFamily.Canonical.basis_repr] using
    (basis.sum_repr u).symm

/-- Evaluation of an arbitrary genuine one-covector from its actual
base and fibre coefficients. -/
theorem one_evaluation (θ : Model [⋀^Fin 1]→L[ℂ] ℂ) (u : Model) :
    θ ![u] = oneBaseCoefficient θ * u.1 +
      dotProduct (oneFibreCoefficient θ) u.2 := by
  calc
    θ ![u] = θ ![u.1 • basis 0 + u.2 0 • basis 1 + u.2 1 • basis 2] := by
      rw [← basis_decomposition u]
    _ = _ := by
      simp only [ContinuousAlternatingMap.vecCons_add,
        ContinuousAlternatingMap.vecCons_smul, smul_eq_mul,
        oneBaseCoefficient_apply, dotProduct, Fin.sum_univ_two,
        oneFibreCoefficient_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      ring

private theorem two_swap (θ : Model [⋀^Fin 2]→L[ℂ] ℂ) (u v : Model) :
    θ ![v, u] = -θ ![u, v] := by
  have hv : ![u, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, u] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using
    θ.toAlternatingMap.map_swap ![u, v] (by decide : (0 : Fin 2) ≠ 1)

private theorem two_same (θ : Model [⋀^Fin 2]→L[ℂ] ℂ) (u : Model) :
    θ ![u, u] = 0 :=
  θ.map_eq_zero_of_eq ![u, u] (i := 0) (j := 1) rfl (by decide)

private theorem two_add_right (θ : Model [⋀^Fin 2]→L[ℂ] ℂ) (u v w : Model) :
    θ ![u, v + w] = θ ![u, v] + θ ![u, w] := by
  rw [two_swap θ (v + w) u, ContinuousAlternatingMap.vecCons_add,
    two_swap θ u v, two_swap θ u w]
  ring

private theorem two_smul_right (θ : Model [⋀^Fin 2]→L[ℂ] ℂ) (c : ℂ) (u v : Model) :
    θ ![u, c • v] = c * θ ![u, v] := by
  rw [two_swap θ (c • v) u, ContinuousAlternatingMap.vecCons_smul,
    two_swap θ u v]
  simp only [smul_eq_mul, mul_neg, neg_neg]

/-- Evaluation of every genuine two-covector, with the actual vertical
coefficient and the two actual mixed coefficients in their original order. -/
theorem two_evaluation (θ : Model [⋀^Fin 2]→L[ℂ] ℂ) (u v : Model) :
    θ ![u, v] =
      twoVerticalCoefficient θ * (u.2 0 * v.2 1 - u.2 1 * v.2 0) +
        u.1 * dotProduct (twoMixedCoefficient θ) v.2 -
        v.1 * dotProduct (twoMixedCoefficient θ) u.2 := by
  calc
    θ ![u, v] = θ ![
        u.1 • basis 0 + u.2 0 • basis 1 + u.2 1 • basis 2,
        v.1 • basis 0 + v.2 0 • basis 1 + v.2 1 • basis 2] := by
      rw [← basis_decomposition u, ← basis_decomposition v]
    _ = _ := by
      simp only [ContinuousAlternatingMap.vecCons_add,
        ContinuousAlternatingMap.vecCons_smul, smul_eq_mul]
      simp only [two_add_right θ, two_smul_right θ,
        two_same θ, twoVerticalCoefficient_apply,
        dotProduct, Fin.sum_univ_two, twoMixedCoefficient_apply,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        two_swap θ (basis 0) (basis 1), two_swap θ (basis 0) (basis 2),
        two_swap θ (basis 1) (basis 2)]
      ring

/-- The coefficient defined by the actual ordered basis agrees with the
coefficient of the already constructed genuine canonical volume. -/
theorem topCoefficient_eq_coefficient (θ : Model [⋀^Fin 3]→L[ℂ] ℂ) :
    topCoefficient θ = TrianglePeriodFamily.Canonical.coefficient θ := by
  change θ ![basis 0, basis 1, basis 2] = θ basis
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The existing genuine canonical volume evaluates as the original
coordinate determinant, in the same base-first orientation. -/
theorem volume_evaluation (u v w : Model) :
    TrianglePeriodFamily.Canonical.volume ![u, v, w] =
      PeriodFamilyHolomorphicForms.coordinateVolume u v w := by
  simp [TrianglePeriodFamily.Canonical.volume_apply, Matrix.det_fin_three,
    PeriodFamilyHolomorphicForms.coordinateVolume]
  ring

/-- Evaluation of an arbitrary genuine top covector from its actual
coefficient, not an independently supplied coordinate-form representation. -/
theorem top_evaluation (θ : Model [⋀^Fin 3]→L[ℂ] ℂ) (u v w : Model) :
    θ ![u, v, w] = topCoefficient θ *
      PeriodFamilyHolomorphicForms.coordinateVolume u v w := by
  calc
    θ ![u, v, w] = TrianglePeriodFamily.Canonical.coefficient θ *
        TrianglePeriodFamily.Canonical.volume ![u, v, w] :=
      congrArg (fun η : Model [⋀^Fin 3]→L[ℂ] ℂ => η ![u, v, w])
        (TrianglePeriodFamily.Canonical.eq_coefficient_smul_volume θ)
    _ = _ := by rw [← topCoefficient_eq_coefficient, volume_evaluation]

/-- The actual one-covector coefficients determine the full covector. -/
theorem one_ext {θ η : Model [⋀^Fin 1]→L[ℂ] ℂ}
    (hbase : oneBaseCoefficient θ = oneBaseCoefficient η)
    (hfibre : oneFibreCoefficient θ = oneFibreCoefficient η) : θ = η := by
  ext u
  have hu : u = ![u 0] := by
    funext i
    fin_cases i
    rfl
  rw [hu, one_evaluation, one_evaluation, hbase, hfibre]

/-- The actual vertical and mixed coefficients determine the full two-covector. -/
theorem two_ext {θ η : Model [⋀^Fin 2]→L[ℂ] ℂ}
    (hvertical : twoVerticalCoefficient θ = twoVerticalCoefficient η)
    (hmixed : twoMixedCoefficient θ = twoMixedCoefficient η) : θ = η := by
  ext u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu, two_evaluation, two_evaluation, hvertical, hmixed]

/-- The actual top coefficient determines the full top covector. -/
theorem top_ext {θ η : Model [⋀^Fin 3]→L[ℂ] ℂ}
    (htop : topCoefficient θ = topCoefficient η) : θ = η := by
  ext u
  have hu : u = ![u 0, u 1, u 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hu, top_evaluation, top_evaluation, htop]

theorem one_eq_zero_iff (θ : Model [⋀^Fin 1]→L[ℂ] ℂ) :
    θ = 0 ↔ oneBaseCoefficient θ = 0 ∧ oneFibreCoefficient θ = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hbase, hfibre⟩
    apply one_ext
    · simpa only [map_zero] using hbase
    · simpa only [map_zero] using hfibre

theorem two_eq_zero_iff (θ : Model [⋀^Fin 2]→L[ℂ] ℂ) :
    θ = 0 ↔ twoVerticalCoefficient θ = 0 ∧ twoMixedCoefficient θ = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hvertical, hmixed⟩
    apply two_ext
    · simpa only [map_zero] using hvertical
    · simpa only [map_zero] using hmixed

theorem top_eq_zero_iff (θ : Model [⋀^Fin 3]→L[ℂ] ℂ) :
    θ = 0 ↔ topCoefficient θ = 0 := by
  constructor
  · rintro rfl
    exact map_zero _
  · intro htop
    apply top_ext
    simpa only [map_zero] using htop

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates
