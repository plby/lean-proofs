import Wikipedia.HopfProblem.EllipticEquivariantFamilies
import Wikipedia.HopfProblem.EllipticBundleFixedCharacters

/-!
# The canonical multiplier of the varying elliptic family

The source's multiplier `χ` is the product of the derivative of the actual
disc rotation and the determinant of the actual varying complex monodromy.
These scalar results use every admissible equivariant period map; no fixed
surface canonical bundle is substituted for the ambient threefold bundle.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.Canonical

open SpecialPeriods

/-- The nontrivial fibre eigenvalue has exponent two at the order-three
point, and exponent one at the order-four point. -/
def canonicalExponent : Kind → ℕ
  | .three => 2
  | .four => 1

variable {j : Kind} (D : Equivariant.Data j)

/-- The top-Jacobian multiplier `ζ · det R(s)` for the actual local action. -/
def multiplier (s : Disc) : ℂ :=
  normalPhase j * (linearMatrix j (D.periods.point s)).det

theorem multiplier_three (D : Equivariant.Data .three) (s : Disc) :
    multiplier D s = rho / (D.periods.point s).val.τ := by
  simp [multiplier, normalPhase, linearMatrix, PeriodPoint.det_R₁, div_eq_mul_inv]

theorem multiplier_four (D : Equivariant.Data .four) (s : Disc) :
    multiplier D s = -Complex.I / (D.periods.point s).val.τ := by
  simp [multiplier, normalPhase, linearMatrix, PeriodPoint.det_R₂, div_eq_mul_inv]

/-- The genuine multiplier is holomorphic on the whole parameter disc. -/
theorem multiplier_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (multiplier D) := by
  have hτ0 : ∀ s : Disc, (D.periods.point s).val.τ ≠ 0 :=
    fun s => (D.periods.point s).val.τ_ne_zero (D.periods.point s).property.1
  cases j
  · convert (contMDiff_const (c := rho)).div₀ D.periods.holomorphic_tau hτ0 using 1
    funext s
    exact multiplier_three D s
  · convert (contMDiff_const (c := -Complex.I)).div₀ D.periods.holomorphic_tau hτ0 using 1
    funext s
    exact multiplier_four D s

/-- Admissibility makes the multiplier nowhere zero. -/
theorem multiplier_ne_zero (s : Disc) : multiplier D s ≠ 0 := by
  have hτ0 := (D.periods.point s).val.τ_ne_zero (D.periods.point s).property.1
  cases j
  · rw [multiplier_three]
    exact div_ne_zero (neg_ne_zero.mp (normalPhase_ne_zero .three)) hτ0
  · rw [multiplier_four]
    exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0

/-- At the centre, the determinant is that of the actual fixed period. -/
theorem multiplier_zero_eq_phase :
    multiplier D discZero = normalPhase j * (canonicalPhase j)⁻¹ := by
  unfold multiplier
  rw [show (linearMatrix j (D.periods.point discZero)).det = (canonicalPhase j)⁻¹ from
    fixedPeriod_linearMatrix_det j D.centralPeriod]

@[simp] theorem multiplier_three_zero (D : Equivariant.Data .three) :
    multiplier D discZero = 1 := by
  rw [multiplier_zero_eq_phase]
  exact mul_inv_cancel₀ (normalPhase_ne_zero .three)

@[simp] theorem multiplier_four_zero (D : Equivariant.Data .four) :
    multiplier D discZero = -1 := by
  rw [multiplier_zero_eq_phase]
  norm_num [normalPhase, canonicalPhase]

/-- The precise central multiplier in Lemma 9.10(ii). -/
theorem multiplier_zero :
    multiplier D discZero = normalPhase j ^ (1 + canonicalExponent j) := by
  cases j
  · rw [multiplier_three_zero]
    exact (normalPhase_pow_order .three).symm
  · rw [multiplier_four_zero]
    norm_num [normalPhase, canonicalExponent, pow_succ]

theorem tau_rotation_three (D : Equivariant.Data .three) (s : Disc) :
    (D.periods.point (familyRotation .three s)).val.τ =
      ((D.periods.point s).val.τ - 1) / (D.periods.point s).val.τ :=
  congrArg (fun p : PeriodDomain => p.val.τ) (D.covariance s)

theorem tau_rotation_four (D : Equivariant.Data .four) (s : Disc) :
    (D.periods.point (familyRotation .four s)).val.τ = -1 / (D.periods.point s).val.τ :=
  congrArg (fun p : PeriodDomain => p.val.τ) (D.covariance s)

/-- The finite norm identity follows from the actual period covariance. -/
theorem multiplier_norm (s : Disc) :
    ∏ i ∈ Finset.range j.order, multiplier D ((familyRotation j)^[i] s) = 1 := by
  cases j
  · have hτ0 := (D.periods.point s).val.τ_ne_zero (D.periods.point s).property.1
    have hτ1 := (D.periods.point s).val.τ_sub_one_ne_zero (D.periods.point s).property.1
    simp only [Kind.order, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      Function.iterate_zero_apply, Function.iterate_succ_apply', multiplier_three,
      tau_rotation_three]
    field_simp [hτ0, hτ1]
    linear_combination rho_cube
  · have hτ0 := (D.periods.point s).val.τ_ne_zero (D.periods.point s).property.1
    simp only [Kind.order, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      Function.iterate_zero_apply, Function.iterate_succ_apply', multiplier_four,
      tau_rotation_four]
    field_simp [hτ0]
    norm_num [Complex.I_sq]

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.Canonical
