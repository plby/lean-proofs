import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSemidirect
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup

/-!
# Free-base coordinates for the actual regular-family fundamental group

Reparametrizing the proved split extension by a proved free-group
marking of the actual base gives the lattice-by-free-group form. The
action is still the actual loop-transport action; no values on an
arbitrarily chosen pair of meridians are assigned.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool)

/-- Actual transport in the specified, proved free coordinates on the base. -/
def freeFundamentalGroupAction : FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  (D.fundamentalGroupAction hq b).comp e.symm.toMonoidHom

/-- Changing only the quotient-group marking preserves the actual action. -/
def semidirectFreeReparametrization :
    (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
      (FundamentalGroup D.BaseSpace (D.baseQuotient b)) ≃*
        (Multiplicative Lattice) ⋊[D.freeFundamentalGroupAction hq b e] (FreeGroup Bool) := by
  refine SemidirectProduct.congr (MulEquiv.refl (Multiplicative Lattice)) e ?_
  intro β
  apply MulEquiv.ext
  intro v
  change D.fundamentalGroupAction hq b β v =
    D.fundamentalGroupAction hq b (e.symm (e β)) v
  rw [MulEquiv.symm_apply_apply]

@[simp] theorem semidirectFreeReparametrization_left
    (x : (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
      (FundamentalGroup D.BaseSpace (D.baseQuotient b))) :
    (D.semidirectFreeReparametrization hq b e x).left = x.left := rfl

@[simp] theorem semidirectFreeReparametrization_right
    (x : (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
      (FundamentalGroup D.BaseSpace (D.baseQuotient b))) :
    (D.semidirectFreeReparametrization hq b e x).right = e x.right := rfl

@[simp] theorem semidirectFreeReparametrization_inl (v : Multiplicative Lattice) :
    D.semidirectFreeReparametrization hq b e (SemidirectProduct.inl v) =
      SemidirectProduct.inl v := by
  apply SemidirectProduct.ext
  · rfl
  · exact e.map_one

@[simp] theorem semidirectFreeReparametrization_inr
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.semidirectFreeReparametrization hq b e (SemidirectProduct.inr β) =
      SemidirectProduct.inr (e β) := rfl

/-- The actual period-family group in lattice-by-free-group coordinates. -/
def fundamentalGroupFreeSemidirectEquiv :
    FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) ≃*
      (Multiplicative Lattice) ⋊[D.freeFundamentalGroupAction hq b e] (FreeGroup Bool) :=
  (D.fundamentalGroupSemidirectEquiv hq b).trans (D.semidirectFreeReparametrization hq b e)

@[simp] theorem fundamentalGroupFreeSemidirectEquiv_lattice (v : Multiplicative Lattice) :
    D.fundamentalGroupFreeSemidirectEquiv hq b e (D.latticeFundamentalGroupHom b v) =
      SemidirectProduct.inl v := by
  change D.semidirectFreeReparametrization hq b e
    (D.fundamentalGroupSemidirectEquiv hq b (D.latticeFundamentalGroupHom b v)) = _
  rw [D.fundamentalGroupSemidirectEquiv_lattice, D.semidirectFreeReparametrization_inl]

@[simp] theorem fundamentalGroupFreeSemidirectEquiv_section
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.fundamentalGroupFreeSemidirectEquiv hq b e (D.sectionFundamentalGroupHom b β) =
      SemidirectProduct.inr (e β) := by
  change D.semidirectFreeReparametrization hq b e
    (D.fundamentalGroupSemidirectEquiv hq b (D.sectionFundamentalGroupHom b β)) = _
  rw [D.fundamentalGroupSemidirectEquiv_section, D.semidirectFreeReparametrization_inr]

@[simp] theorem fundamentalGroupFreeSemidirectEquiv_projection
    (γ : FundamentalGroup D.Space (D.fundamentalGroupBasepoint b)) :
    (D.fundamentalGroupFreeSemidirectEquiv hq b e γ).right =
      e (D.projectionFundamentalGroupHom b γ) := by
  change e (D.fundamentalGroupSemidirectEquiv hq b γ).right = _
  rw [D.fundamentalGroupSemidirectEquiv_projection]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The actual regular-base marking supplies the free quotient coordinates. -/
def regularFundamentalGroupFreeAction (b : TriangleRegularPoint) :
    FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  (regularData P h₁ h₂).freeFundamentalGroupAction (regularCovering P h₁ h₂) b
    (Triangle.triangleRegularFundamentalGroupFreeEquivAt (triangleRegularProject b))

/-- The regular family's actual fundamental group is a lattice semidirect
the free group on two letters, with the action derived from actual transport. -/
def regularFundamentalGroupFreeEquiv (b : TriangleRegularPoint) :
    FundamentalGroup (regularData P h₁ h₂).Space
      ((regularData P h₁ h₂).fundamentalGroupBasepoint b) ≃*
        (Multiplicative Lattice) ⋊[regularFundamentalGroupFreeAction P h₁ h₂ b]
          (FreeGroup Bool) :=
  (regularData P h₁ h₂).fundamentalGroupFreeSemidirectEquiv (regularCovering P h₁ h₂) b
    (Triangle.triangleRegularFundamentalGroupFreeEquivAt (triangleRegularProject b))

@[simp] theorem regularFundamentalGroupFreeEquiv_lattice
    (b : TriangleRegularPoint) (v : Multiplicative Lattice) :
    regularFundamentalGroupFreeEquiv P h₁ h₂ b
      ((regularData P h₁ h₂).latticeFundamentalGroupHom b v) = SemidirectProduct.inl v :=
  (regularData P h₁ h₂).fundamentalGroupFreeSemidirectEquiv_lattice
    (regularCovering P h₁ h₂) b _ v

@[simp] theorem regularFundamentalGroupFreeEquiv_projection
    (b : TriangleRegularPoint)
    (γ : FundamentalGroup (regularData P h₁ h₂).Space
      ((regularData P h₁ h₂).fundamentalGroupBasepoint b)) :
    (regularFundamentalGroupFreeEquiv P h₁ h₂ b γ).right =
      Triangle.triangleRegularFundamentalGroupFreeEquivAt (triangleRegularProject b)
        ((regularData P h₁ h₂).projectionFundamentalGroupHom b γ) :=
  (regularData P h₁ h₂).fundamentalGroupFreeSemidirectEquiv_projection
    (regularCovering P h₁ h₂) b _ γ

end Wikipedia.HopfProblem.TrianglePeriodFamily
