import Wikipedia.HopfProblem.CuspCircleOrbitLocalDomain

/-!
# The actual coordinate-domain circle quotient

The quotient relation is defined by the original period-one circle action
on the original cusp coordinate domain. With its canonical quotient
topology, this orbit space is homeomorphic to the explicit invariant
domain `‖aβ/2‖ < radius`. The additional cusp deck quotient and the global
attachments are not included in this local statement.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

local notation "E₃" => ToricCharts.CoordinateSpace 3

/-- The relation is the original circle orbit, not equality of chosen invariant coordinates. -/
def localCircleOrbitSetoid : Setoid Domain where
  r z w := ∃ t : AddCircle (1 : ℝ),
    coordinateAction (Homology.DeltaSweep.circleParameter t) z = w
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro z
      exact (localOrbitProjection_eq_iff_circle z z).mp rfl
    · intro z w h
      exact (localOrbitProjection_eq_iff_circle w z).mp
        ((localOrbitProjection_eq_iff_circle z w).mpr h).symm
    · intro z w v hzw hwv
      exact (localOrbitProjection_eq_iff_circle z v).mp
        (((localOrbitProjection_eq_iff_circle z w).mpr hzw).trans
          ((localOrbitProjection_eq_iff_circle w v).mpr hwv))

/-- The original-domain orbit quotient, carrying the canonical quotient topology. -/
abbrev LocalOrbitSpace := Quotient localCircleOrbitSetoid

/-- The canonical orbit class of an original coordinate-domain point. -/
def localOrbitClass (z : Domain) : LocalOrbitSpace := Quotient.mk localCircleOrbitSetoid z

theorem localOrbitClass_continuous : Continuous localOrbitClass :=
  continuous_quotient_mk' (s := localCircleOrbitSetoid)

/-- Invariant coordinates descend to the actual circle-orbit quotient. -/
def localOrbitSpaceMap : LocalOrbitSpace → orbitDomain :=
  Quotient.lift localOrbitProjection fun z w h =>
    (localOrbitProjection_eq_iff_circle z w).mpr h

@[simp] theorem localOrbitSpaceMap_mk (z : Domain) :
    localOrbitSpaceMap (localOrbitClass z) = localOrbitProjection z := rfl

theorem localOrbitSpaceMap_continuous : Continuous localOrbitSpaceMap :=
  continuous_quot_lift _ localOrbitProjection_continuous

theorem localOrbitSpaceMap_injective : Function.Injective localOrbitSpaceMap := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro z w h
  exact Quotient.sound ((localOrbitProjection_eq_iff_circle z w).mp h)

theorem localOrbitSpaceMap_surjective : Function.Surjective localOrbitSpaceMap := by
  intro p
  obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
  exact ⟨localOrbitClass z, rfl⟩

/-- The exact orbit-fibre criterion supplies the bijection. -/
def localOrbitSpaceEquiv : LocalOrbitSpace ≃ orbitDomain :=
  Equiv.ofBijective localOrbitSpaceMap
    ⟨localOrbitSpaceMap_injective, localOrbitSpaceMap_surjective⟩

@[simp] theorem localOrbitSpaceEquiv_mk (z : Domain) :
    localOrbitSpaceEquiv (localOrbitClass z) = localOrbitProjection z := rfl

@[simp] theorem localOrbitSpaceEquiv_symm_projection (z : Domain) :
    localOrbitSpaceEquiv.symm (localOrbitProjection z) = localOrbitClass z := by
  apply localOrbitSpaceEquiv.injective
  rw [Equiv.apply_symm_apply, localOrbitSpaceEquiv_mk]

/-- The inverse is continuous for the original quotient topology. -/
theorem localOrbitSpaceEquiv_symm_continuous : Continuous localOrbitSpaceEquiv.symm := by
  apply localOrbitProjection_isQuotientMap.continuous_iff.mpr
  have h : localOrbitSpaceEquiv.symm ∘ localOrbitProjection = localOrbitClass :=
    funext localOrbitSpaceEquiv_symm_projection
  rw [h]
  exact localOrbitClass_continuous

/-- The native cusp coordinate-domain orbit space has the explicit invariant-coordinate model. -/
def localOrbitSpaceHomeomorph : LocalOrbitSpace ≃ₜ orbitDomain where
  toEquiv := localOrbitSpaceEquiv
  continuous_toFun := localOrbitSpaceMap_continuous
  continuous_invFun := localOrbitSpaceEquiv_symm_continuous

@[simp] theorem localOrbitSpaceHomeomorph_mk (z : Domain) :
    localOrbitSpaceHomeomorph (localOrbitClass z) = localOrbitProjection z := rfl

/-- The homeomorphism retains all three original invariant-coordinate values. -/
theorem localOrbitSpaceHomeomorph_mk_val (z : Domain) :
    (localOrbitSpaceHomeomorph (localOrbitClass z) : ℂ × ℂ × ℝ) =
      ((z : E₃) 1, 2 * (z : E₃) 0 * (z : E₃) 2,
        Complex.normSq ((z : E₃) 0) - Complex.normSq ((z : E₃) 2)) := rfl

/-- The original normal-crossing time is retained on every orbit representative. -/
theorem localOrbitSpaceHomeomorph_time (z : Domain) :
    orbitTime (localOrbitSpaceHomeomorph (localOrbitClass z)) =
      ToricFan.Triangle.time (z : E₃) :=
  orbitTime_localOrbitMap z

/-- The fixed axis maps exactly to the zero section of the normal invariant coordinates. -/
theorem localOrbitMap_normal_zero_iff (z : Domain) :
    (localOrbitMap z).2 = 0 ↔ (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0 := by
  constructor
  · intro h
    have hh : hopfMap ((z : E₃) 0, (z : E₃) 2) = hopfMap (0, 0) := by
      change hopfMap ((z : E₃) 0, (z : E₃) 2) = (0, 0) at h
      simpa only [hopfMap, mul_zero, Complex.normSq_zero, sub_self] using h
    obtain ⟨h₀, h₂⟩ := normSq_components_of_hopfMap_eq hh
    exact ⟨Complex.normSq_eq_zero.mp (by simpa using h₀),
      Complex.normSq_eq_zero.mp (by simpa using h₂)⟩
  · rintro ⟨h₀, h₂⟩
    simp [localOrbitMap, hopfMap, h₀, h₂]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
