import Wikipedia.HopfProblem.CuspQuotient
import Wikipedia.HopfProblem.ToricDeckVolume
import Wikipedia.HopfProblem.CoveringVolumeCoordinates

/-!
# The signed volume coordinates on the actual cusp quotient

The covering charts have constant nonzero volume coefficients.  Their
actual complex Jacobian determinants satisfy the canonical-bundle gluing
rule, including at points of the central normal-crossings fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The coefficient is the orientation sign of the toric chart used in
the chosen covering lift. -/
def volumeCoefficient (x : QuotientSpace C ε) : ℂ :=
  letI := tubeAction C (disc ε)
  ((preferredTriangle ((CoveringQuotient.representative
    (quotientMap_covering C ε hε hε1 hC hR) x : Tube (disc ε)) : Space)).rays.det : ℂ)

theorem volumeCoefficient_ne_zero (x : QuotientSpace C ε) :
    volumeCoefficient C ε hε hε1 hC hR x ≠ 0 := by
  let := tubeAction C (disc ε)
  exact ToricFan.Triangle.signed_volume_coefficient_ne_zero _

/-- This is the determinant of the derivative of the genuine quotient
chart transition, rather than of a separate formal monomial model. -/
theorem chart_transition_det_fderiv (x y : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∀ z ∈ ((chartAt (CoordinateSpace 3) x).symm.trans
      (chartAt (CoordinateSpace 3) y)).source,
      LinearMap.det (fderiv ℂ ((chartAt (CoordinateSpace 3) x).symm.trans
        (chartAt (CoordinateSpace 3) y)) z).toLinearMap =
      volumeCoefficient C ε hε hε1 hC hR x /
        volumeCoefficient C ε hε hε1 hC hR y := by
  let := tubeAction C (disc ε)
  let := chartedSpace C ε hε hε1 hC hR
  let hq := quotientMap_covering C ε hε hε1 hC hR
  intro z hz
  have hz' : z ∈ ((CoveringQuotient.chart (E := CoordinateSpace 3) hq x).symm.trans
      (CoveringQuotient.chart (E := CoordinateSpace 3) hq y)).source := hz
  obtain ⟨g, hg, he⟩ := CoveringQuotient.transition_eventually_deck hq
    (fun v : LatticeGroup => (tubeTranslate_holomorphic C (disc ε) v.toAdd hC).continuous)
    x y hz'
  change LinearMap.det (fderiv ℂ
    ((CoveringQuotient.chart (E := CoordinateSpace 3) hq x).symm.trans
      (CoveringQuotient.chart (E := CoordinateSpace 3) hq y)) z).toLinearMap = _
  rw [he.fderiv_eq]
  exact tubeTranslate_chart_det_fderiv C (disc ε) hC g.toAdd
    (CoveringQuotient.representative hq x) (CoveringQuotient.representative hq y) hz'.1.1 hg

/-- The covering projection itself has the same signed Jacobian law.
Consequently the volume constructed downstairs pulls back to the toric
volume upstairs, in the actual source and quotient coordinate charts. -/
theorem quotientMap_chart_det_fderiv (a : Tube (disc ε)) (y : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∀ z ∈ (chartAt (CoordinateSpace 3) a).target,
      quotientMap C ε ((chartAt (CoordinateSpace 3) a).symm z) ∈
        (chartAt (CoordinateSpace 3) y).source →
      LinearMap.det (fderiv ℂ (chartAt (CoordinateSpace 3) y ∘ quotientMap C ε ∘
        (chartAt (CoordinateSpace 3) a).symm) z).toLinearMap =
      ((preferredTriangle (a : Space)).rays.det : ℂ) /
        volumeCoefficient C ε hε hε1 hC hR y := by
  let := tubeAction C (disc ε)
  let := chartedSpace C ε hε hε1 hC hR
  let hq := quotientMap_covering C ε hε hε1 hC hR
  intro z hz hy
  have hy' : quotientMap C ε ((chartAt (CoordinateSpace 3) a).symm z) ∈
      (CoveringQuotient.chart (E := CoordinateSpace 3) hq y).source := hy
  obtain ⟨g, hg, he⟩ := CoveringQuotient.localInverse_eventually_deck hq
    (fun v : LatticeGroup => (tubeTranslate_holomorphic C (disc ε) v.toAdd hC).continuous)
    (CoveringQuotient.representative hq y) ((chartAt (CoordinateSpace 3) a).symm z) hy'.1
  have htarget : g • (chartAt (CoordinateSpace 3) a).symm z ∈
      (chartAt (CoordinateSpace 3) (CoveringQuotient.representative hq y)).source := by
    rw [← hg]
    exact hy'.2
  have heq : (chartAt (CoordinateSpace 3) y ∘ quotientMap C ε ∘
      (chartAt (CoordinateSpace 3) a).symm) =ᶠ[𝓝 z]
      (chartAt (CoordinateSpace 3) (CoveringQuotient.representative hq y) ∘
        (fun x : Tube (disc ε) => g • x) ∘ (chartAt (CoordinateSpace 3) a).symm) :=
    (he.comp_tendsto ((chartAt (CoordinateSpace 3) a).symm.continuousAt hz)).fun_comp
      (chartAt (CoordinateSpace 3) (CoveringQuotient.representative hq y))
  rw [heq.fderiv_eq]
  exact tubeTranslate_chart_det_fderiv C (disc ε) hC g.toAdd a
    (CoveringQuotient.representative hq y) hz htarget

end Wikipedia.HopfProblem.CuspQuotient
