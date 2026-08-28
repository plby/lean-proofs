import Wikipedia.HopfProblem.EllipticBundleCharacters

/-!
# Determinant characters at every admissible elliptic fixed period

The upper-half-plane condition singles out the specified elliptic fixed
point. Thus the canonical determinant character is the same for every
admissible fixed period, not only for the explicit central local family.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

theorem fixedPeriod_three_tau (p : FixedPeriod .three) : p.val.val.τ = rho := by
  let t := p.val.val.τ
  have ht : t ≠ 0 := p.val.val.τ_ne_zero p.val.property.1
  have hp : (t - 1) / t = t := congrArg (fun q : PeriodDomain => q.val.τ) p.property
  have he : t - 1 = t * t := (div_eq_iff ht).mp hp
  have hpoly : t ^ 2 - t + 1 = 0 := by linear_combination -he
  have hprod : (t - rho) * (t - (1 - rho)) = 0 := by
    linear_combination hpoly - rho_sq
  obtain h | h := mul_eq_zero.mp hprod
  · exact sub_eq_zero.mp h
  · have hval : t = 1 - rho := sub_eq_zero.mp h
    have him := congrArg Complex.im hval
    simp only [Complex.sub_im, Complex.one_im, zero_sub] at him
    have hpos : 0 < t.im := p.val.property.1
    linarith [rho_im_pos]

theorem fixedPeriod_four_tau (p : FixedPeriod .four) : p.val.val.τ = Complex.I := by
  let t := p.val.val.τ
  have ht : t ≠ 0 := p.val.val.τ_ne_zero p.val.property.1
  have hp : -1 / t = t := congrArg (fun q : PeriodDomain => q.val.τ) p.property
  have he : -1 = t * t := (div_eq_iff ht).mp hp
  have hpoly : t ^ 2 + 1 = 0 := by linear_combination -he
  have hprod : (t - Complex.I) * (t + Complex.I) = 0 := by
    calc
      (t - Complex.I) * (t + Complex.I) = t ^ 2 - Complex.I ^ 2 := by ring
      _ = 0 := by rw [Complex.I_sq]; linear_combination hpoly
  obtain h | h := mul_eq_zero.mp hprod
  · exact sub_eq_zero.mp h
  · have hval : t = -Complex.I := eq_neg_of_add_eq_zero_left h
    have him := congrArg Complex.im hval
    have hpos : 0 < t.im := p.val.property.1
    norm_num at him
    linarith

theorem fixedPeriod_linearMatrix_det (j : Kind) (p : FixedPeriod j) :
    (linearMatrix j p.val).det = (canonicalPhase j)⁻¹ := by
  cases j
  · change p.val.val.R₁.det = _
    rw [PeriodPoint.det_R₁, fixedPeriod_three_tau p]
    simp [canonicalPhase, div_eq_mul_inv]
  · change p.val.val.R₂.det = _
    rw [PeriodPoint.det_R₂, fixedPeriod_four_tau p]
    simp [canonicalPhase]

theorem fixedPeriod_linearEquiv_det (j : Kind) (p : FixedPeriod j) :
    LinearMap.det (linearEquiv j p).toLinearMap = (canonicalPhase j)⁻¹ := by
  have he : (linearEquiv j p).toLinearMap = Matrix.toLin' (linearMatrix j p.val) := by
    apply LinearMap.ext
    intro z
    exact linearEquiv_apply j p z
  rw [he, LinearMap.det_toLin']
  exact fixedPeriod_linearMatrix_det j p

end Wikipedia.HopfProblem.Elliptic
