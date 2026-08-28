import Wikipedia.HopfProblem.CuspNormalizationGermsNormalDirection
import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinateDivisionAlgebra
import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinates

/-!
# Simultaneous regularizing coordinates for actual analytic germs

The product of two nonzero analytic germs is nonzero.  A transverse line
for that product is therefore transverse to both factors.  An explicit
continuous complex-linear equivalence makes this line the second axis.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.Coordinates

/-- A nonzero vector in `ℂ × ℂ` is the second column of an actual
continuous complex-linear coordinate change. -/
theorem exists_axis_equiv_prod (v : ℂ × ℂ) (hv : v ≠ 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), ∀ t : ℂ, e (0, t) = t • v := by
  by_cases hv2 : v.2 ≠ 0
  · let e := (NormalDirection.triangularLinearEquiv v.1 v.2 hv2).toContinuousLinearEquiv
    refine ⟨e, ?_⟩
    intro t
    change NormalDirection.triangularLinearEquiv v.1 v.2 hv2 (0, t) = t • v
    rw [NormalDirection.triangularLinearEquiv_axis]
    rfl
  · have hv1 : v.1 ≠ 0 := by
      intro hzero
      exact hv (Prod.ext hzero (not_not.mp hv2))
    let e := ((NormalDirection.triangularLinearEquiv v.2 v.1 hv1).trans
      (LinearEquiv.prodComm ℂ ℂ ℂ)).toContinuousLinearEquiv
    refine ⟨e, ?_⟩
    intro t
    change (NormalDirection.triangularLinearEquiv v.2 v.1 hv1 (0, t)).swap = t • v
    rw [NormalDirection.triangularLinearEquiv_axis]
    rfl

section PairLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]

/-- Two nonzero actual analytic germs have a common nonzero line on which
neither restriction vanishes as a germ. -/
theorem exists_nonzero_line_pair {f g : E → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : ¬ f =ᶠ[𝓝 (0 : E)] 0) (hg0 : ¬ g =ᶠ[𝓝 (0 : E)] 0) :
    ∃ v : E, v ≠ 0 ∧
      (¬ (fun t : ℂ => f (t • v)) =ᶠ[𝓝 (0 : ℂ)] 0) ∧
      (¬ (fun t : ℂ => g (t • v)) =ᶠ[𝓝 (0 : ℂ)] 0) := by
  have hfg : ¬ (f * g) =ᶠ[𝓝 (0 : E)] 0 := by
    intro hzero
    exact (eq_zero_or_eq_zero_of_mul_eventuallyEq_zero hf hg hzero).elim hf0 hg0
  obtain ⟨v, hv, hline⟩ := NormalDirection.exists_nonzero_line (hf.mul hg) hfg
  refine ⟨v, hv, ?_, ?_⟩
  · intro hzero
    apply hline
    filter_upwards [hzero] with t ht
    simp only [Pi.mul_apply, ht, zero_mul, Pi.zero_apply]
  · intro hzero
    apply hline
    filter_upwards [hzero] with t ht
    simp only [Pi.mul_apply, ht, mul_zero, Pi.zero_apply]

end PairLines

/-- A single genuine linear coordinate change makes two nonzero
two-variable analytic germs simultaneously nonzero on the second axis. -/
theorem exists_pair_regularizing_coordinates {f g : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : ¬ f =ᶠ[𝓝 (0 : ℂ × ℂ)] 0) (hg0 : ¬ g =ᶠ[𝓝 (0 : ℂ × ℂ)] 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
      (¬ (fun w : ℂ => f (e (0, w))) =ᶠ[𝓝 (0 : ℂ)] 0) ∧
      (¬ (fun w : ℂ => g (e (0, w))) =ᶠ[𝓝 (0 : ℂ)] 0) := by
  obtain ⟨v, hv, hfline, hgline⟩ := exists_nonzero_line_pair hf hg hf0 hg0
  obtain ⟨e, he⟩ := exists_axis_equiv_prod v hv
  exact ⟨e, by simpa only [he] using hfline, by simpa only [he] using hgline⟩

/-- The same regularization stated with nonvanishing in the actual germ ring. -/
theorem exists_pair_regularizing_coordinates_of_germ_ne_zero {f g : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : ofAnalytic f hf ≠ 0) (hg0 : ofAnalytic g hg ≠ 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
      (¬ (fun w : ℂ => f (e (0, w))) =ᶠ[𝓝 (0 : ℂ)] 0) ∧
      (¬ (fun w : ℂ => g (e (0, w))) =ᶠ[𝓝 (0 : ℂ)] 0) :=
  exists_pair_regularizing_coordinates hf hg
    ((ofAnalytic_eq_zero_iff f hf).not.mp hf0) ((ofAnalytic_eq_zero_iff g hg).not.mp hg0)

/-- In the actual germ ring, one linear pullback makes both germs have
nonzero restriction to the second axis. -/
theorem exists_pair_regularizing_germ_coordinates
    (φ ψ : AnalyticGerm (0 : ℂ × ℂ)) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
      CoordinateDivision.axisRestriction (linearPullbackEquiv e φ) ≠ 0 ∧
      CoordinateDivision.axisRestriction (linearPullbackEquiv e ψ) ≠ 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  obtain ⟨g, hg, rfl⟩ := exists_representative ψ
  obtain ⟨e, hfe, hge⟩ :=
    exists_pair_regularizing_coordinates_of_germ_ne_zero hf hg hφ hψ
  refine ⟨e, ?_, ?_⟩
  · rw [linearPullbackEquiv_ofAnalytic, CoordinateDivision.axisRestriction_ofAnalytic,
      ne_eq, ofAnalytic_eq_zero_iff]
    exact hfe
  · rw [linearPullbackEquiv_ofAnalytic, CoordinateDivision.axisRestriction_ofAnalytic,
      ne_eq, ofAnalytic_eq_zero_iff]
    exact hge

end Wikipedia.HopfProblem.CuspNormalization.Germs.Coordinates
