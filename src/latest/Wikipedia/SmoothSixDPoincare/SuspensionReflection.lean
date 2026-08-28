import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopology
import Wikipedia.SmoothSixDPoincare.CoverConnectingSwap

/-!
# Actual reflection of the suspension and its middle band

Reverse the cylinder height before passing to the genuine suspension
quotient. This exchanges the two original cone charts and preserves the
middle band's original label projection exactly.
-/

noncomputable section

open Set Topology ContinuousMap Function
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.SuspensionReflection

open Wikipedia.HopfProblem.CuspCentralHomology

variable {X : Type} [TopologicalSpace X]

def reflect : C(Suspension X, Suspension X) where
  toFun := Quotient.lift (fun q => Suspension.mk (unitInterval.symm q.1) q.2) (by
    rintro a b ⟨ht, h0 | h1 | hx⟩
    · apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      refine ⟨congrArg unitInterval.symm ht, Or.inr (Or.inl ?_)⟩
      simp [h0]
    · apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      refine ⟨congrArg unitInterval.symm ht, Or.inl ?_⟩
      simp [h1]
    · exact (Suspension.mk_eq_mk_iff _ _ _ _).mpr
        ⟨congrArg unitInterval.symm ht, Or.inr (Or.inr hx)⟩)
  continuous_toFun := Suspension.isQuotientMap_mk.continuous_iff.mpr
    (Suspension.continuous_mk.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))

theorem reflect_mk (t : I) (x : X) :
    reflect (Suspension.mk t x) = Suspension.mk (unitInterval.symm t) x := rfl

theorem reflect_height (x : Suspension X) :
    Suspension.height (reflect x) = unitInterval.symm (Suspension.height x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.mk_surjective x
  rfl

theorem reflect_reflect (x : Suspension X) : reflect (reflect x) = x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.mk_surjective x
  rw [reflect_mk, reflect_mk, unitInterval.symm_symm]

theorem reflect_north : MapsTo (reflect (X := X)) Suspension.northOpen Suspension.southOpen := by
  intro x hx
  change (Suspension.height x : ℝ) < 3 / 4 at hx
  change 1 / 4 < (Suspension.height (reflect x) : ℝ)
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith

theorem reflect_south : MapsTo (reflect (X := X)) Suspension.southOpen Suspension.northOpen := by
  intro x hx
  change 1 / 4 < (Suspension.height x : ℝ) at hx
  change (Suspension.height (reflect x) : ℝ) < 3 / 4
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith

def middleMap : C(Suspension.middleBand X, Suspension.middleBand X) :=
  CoverNaturality.reversingIntersectionMap _ _ _ _ reflect reflect_north reflect_south

/-- The original label projection on the middle band is fixed by height reflection. -/
theorem middle_projection (x : Suspension.middleBand X) :
    Suspension.middleBandHomotopyEquiv (middleMap x) = Suspension.middleBandHomotopyEquiv x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.middleBandHomeomorph.symm.surjective x
  let q : Ioo (1 / 4 : ℝ) (3 / 4) × X :=
    (⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩, u)
  have hpoint : middleMap (Suspension.middleBandHomeomorph.symm (t, u)) =
      Suspension.middleBandHomeomorph.symm q := by
    apply Subtype.ext
    change reflect (Suspension.mk _ u) = Suspension.mk _ u
    rw [reflect_mk]
    congr 1
  rw [hpoint, Suspension.middleBandHomotopyEquiv_apply,
    Suspension.middleBandHomotopyEquiv_apply, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

theorem middle_projection_comp :
    (Suspension.middleBandHomotopyEquiv (X := X)).toFun.comp middleMap =
      (Suspension.middleBandHomotopyEquiv (X := X)).toFun :=
  ContinuousMap.ext middle_projection

end Wikipedia.SmoothSixDPoincare.SuspensionReflection
