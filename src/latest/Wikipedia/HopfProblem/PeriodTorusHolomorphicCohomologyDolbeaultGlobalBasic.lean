import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGeometry

/-!
# Global smooth sections and their literal periodic lifts

Global sections are smooth functions on the original native torus. Pullback
along the actual lattice projection identifies them with real smooth,
lattice-periodic functions on the covering vector space. The inverse uses
the existing quotient representative only to name a function; its smoothness
is proved by the exact lift identity and the native chart descent criterion.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- The actual lattice quotient projection is an open map. -/
theorem mkQ_isOpenMap (p : PeriodDomain) :
    IsOpenMap (p.lattice.mkQ : ComplexPlane₂ → p.Torus) :=
  p.lattice.isOpenMap_mkQ

/-- The literal pullback of an actual global smooth section to the cover. -/
def globalLift (p : PeriodDomain) (s : SmoothSection p ⊤) : ComplexPlane₂ → ℂ :=
  fun z => s ⟨p.lattice.mkQ z, by simp⟩

@[simp] theorem globalLift_apply (p : PeriodDomain) (s : SmoothSection p ⊤)
    (z : ComplexPlane₂) :
    globalLift p s z = s ⟨p.lattice.mkQ z, by simp⟩ := rfl

/-- The lift is smooth because the native section and the native quotient
projection are smooth maps for the unchanged real atlas. -/
theorem globalLift_contDiff (p : PeriodDomain) (s : SmoothSection p ⊤) :
    ContDiff ℝ ∞ (globalLift p s) := by
  have hs : ContMDiff IR₂ IR₁ ∞ (smoothExtend p ⊤ s) :=
    fun x => smoothExtend_contMDiffAt p ⊤ s x (by simp)
  have h := (hs.comp (mkQ_contMDiff_real p)).contDiff
  have he : smoothExtend p ⊤ s ∘ p.lattice.mkQ = globalLift p s := by
    funext z
    exact smoothExtend_apply p ⊤ s (p.lattice.mkQ z) (by simp)
  exact he ▸ h

/-- Its lattice periodicity is the literal quotient identity. -/
theorem globalLift_periodic (p : PeriodDomain) (s : SmoothSection p ⊤)
    (z : ComplexPlane₂) (l : p.lattice) :
    globalLift p s (z + (l : ComplexPlane₂)) = globalLift p s z := by
  apply congrArg s
  apply Subtype.ext
  change p.lattice.mkQ (z + (l : ComplexPlane₂)) = p.lattice.mkQ z
  have hl : p.lattice.mkQ (l : ComplexPlane₂) = 0 :=
    (Submodule.Quotient.mk_eq_zero p.lattice).mpr l.property
  rw [map_add, hl, add_zero]

/-- A quotient function named using the original chosen representative. No
regularity is asserted here without a periodicity hypothesis. -/
def periodicDescend (p : PeriodDomain) (u : ComplexPlane₂ → ℂ) : p.Torus → ℂ :=
  fun x => u (DiscreteQuotient.representative p.lattice x)

/-- Periodicity removes the choice of representative over every cover point. -/
theorem periodicDescend_mkQ (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z)
    (z : ComplexPlane₂) : periodicDescend p u (p.lattice.mkQ z) = u z := by
  let r := DiscreteQuotient.representative p.lattice (p.lattice.mkQ z)
  have hr : p.lattice.mkQ r = p.lattice.mkQ z :=
    DiscreteQuotient.mkQ_representative p.lattice (p.lattice.mkQ z)
  let l : p.lattice := ⟨r - z, (Submodule.Quotient.eq p.lattice).mp hr⟩
  have hl : z + (l : ComplexPlane₂) = r := by
    change z + (r - z) = r
    rw [add_comm z (r - z), sub_add_cancel]
  change u r = u z
  exact (congrArg u hl).symm.trans (hper z l)

theorem periodicDescend_comp_mkQ (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z) :
    periodicDescend p u ∘ p.lattice.mkQ = u :=
  funext (periodicDescend_mkQ p u hper)

/-- Smooth periodic functions descend to genuinely smooth native functions. -/
theorem periodicDescend_contMDiff (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z) :
    ContMDiff IR₂ IR₁ ∞ (periodicDescend p u) := by
  apply contMDiff_real_of_lift p ∞
  rw [periodicDescend_comp_mkQ p u hper]
  exact hu

/-- The actual global smooth section descended from a smooth periodic cover
function, in the original quotient atlas. -/
def ofPeriodicSmooth (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z) :
    SmoothSection p ⊤ :=
  sectionOfSmooth p ⊤ (periodicDescend p u)
    (fun x _ => periodicDescend_contMDiff p u hu hper x)

@[simp] theorem ofPeriodicSmooth_apply (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z)
    (x : (⊤ : Opens p.Torus)) :
    ofPeriodicSmooth p u hu hper x = periodicDescend p u x := rfl

/-- The descended native section has exactly the prescribed values on lifts. -/
@[simp] theorem ofPeriodicSmooth_mkQ (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z)
    (z : ComplexPlane₂) :
    ofPeriodicSmooth p u hu hper ⟨p.lattice.mkQ z, by simp⟩ = u z :=
  periodicDescend_mkQ p u hper z

@[simp] theorem globalLift_ofPeriodicSmooth (p : PeriodDomain) (u : ComplexPlane₂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z) :
    globalLift p (ofPeriodicSmooth p u hu hper) = u :=
  funext (ofPeriodicSmooth_mkQ p u hu hper)

/-- Equality of the literal lifts implies equality of the native sections. -/
theorem globalLift_injective (p : PeriodDomain) : Function.Injective (globalLift p) := by
  intro s t h
  apply ContMDiffMap.ext
  intro x
  obtain ⟨z, hz⟩ := p.lattice.mkQ_surjective (x : p.Torus)
  have hx : (⟨p.lattice.mkQ z, by simp⟩ : (⊤ : Opens p.Torus)) = x :=
    Subtype.ext hz
  have he := congrFun h z
  change s ⟨p.lattice.mkQ z, by simp⟩ = t ⟨p.lattice.mkQ z, by simp⟩ at he
  simpa only [hx] using he

@[simp] theorem ofPeriodicSmooth_globalLift (p : PeriodDomain) (s : SmoothSection p ⊤) :
    ofPeriodicSmooth p (globalLift p s) (globalLift_contDiff p s)
      (globalLift_periodic p s) = s := by
  apply globalLift_injective p
  exact globalLift_ofPeriodicSmooth p _ _ _

/-- The native global-section bijection with actual smooth periodic functions. -/
def globalLiftEquiv (p : PeriodDomain) : SmoothSection p ⊤ ≃
    {u : ComplexPlane₂ → ℂ //
      ContDiff ℝ ∞ u ∧ ∀ z (l : p.lattice), u (z + (l : ComplexPlane₂)) = u z} where
  toFun s := ⟨globalLift p s, globalLift_contDiff p s, globalLift_periodic p s⟩
  invFun u := ofPeriodicSmooth p u u.property.1 u.property.2
  left_inv := ofPeriodicSmooth_globalLift p
  right_inv u := Subtype.ext (globalLift_ofPeriodicSmooth p u u.property.1 u.property.2)

/-- Pullback is complex-linear for the actual pointwise scalar actions. -/
def globalLiftLinearMap (p : PeriodDomain) :
    SmoothSection p ⊤ →ₗ[ℂ] (ComplexPlane₂ → ℂ) where
  toFun := globalLift p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem globalLiftLinearMap_apply (p : PeriodDomain) (s : SmoothSection p ⊤) :
    globalLiftLinearMap p s = globalLift p s := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
