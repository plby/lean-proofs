import Wikipedia.HopfProblem.TrianglePeriodFamilyTopology
import Mathlib.Topology.Homotopy.Lifting

/-!
# Closed lifts of loops with null projected class

For the actual diagonal quotient, a loop whose projected class is trivial
lifts to a closed loop in the product.  The first endpoint coordinate is
fixed by homotopy lifting for the base covering; the second is then fixed
by injectivity of the actual fibre inclusion.  No connectedness, simple
connectivity, or fixed-point hypothesis on the fibre action is needed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)

include hq

/-- Every loop class with null projection comes from an actual closed
loop in the product covering space. -/
theorem quotient_loop_lift_of_projection_eq_refl (b : B) (c : F)
    (γ : Path.Homotopic.Quotient (fibreInclusion G B F b c) (fibreInclusion G B F b c))
    (hγ : γ.map ⟨projection G B F, projection_continuous G B F⟩ =
      Path.Homotopic.Quotient.refl (baseQuotient G B b)) :
    ∃ δ : Path.Homotopic.Quotient (b, c) (b, c),
      δ.map ⟨quotient G B F, quotient_continuous G B F⟩ = γ := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      let cov := (quotientCoveringMap (F := F) hq).isCoveringMap
      let L : C(unitInterval, B × F) := cov.liftPath γ (b, c) γ.source
      let γb : Path (baseQuotient G B b) (baseQuotient G B b) :=
        γ.map (projection_continuous G B F)
      let Lb : C(unitInterval, B) :=
        ⟨fun t => (L t).1, continuous_fst.comp L.continuous⟩
      have hLb : Lb = hq.isCoveringMap.liftPath γb b γb.source := by
        apply (hq.isCoveringMap.eq_liftPath_iff' γb.source).mpr
        constructor
        · funext t
          exact congrArg (projection G B F)
            (congrFun (cov.liftPath_lifts γ (b, c) γ.source) t)
        · exact congrArg Prod.fst (cov.liftPath_zero γ (b, c) γ.source)
      have hnull : γb.Homotopic (Path.refl (baseQuotient G B b)) := by
        apply Path.Homotopic.Quotient.eq.mp
        exact hγ
      have hbaseEnd : hq.isCoveringMap.liftPath γb b γb.source 1 = b := by
        have h := hq.isCoveringMap.liftPath_apply_one_eq_of_homotopicRel
          hnull b γb.source rfl
        have hc : hq.isCoveringMap.liftPath (Path.refl (baseQuotient G B b)) b rfl 1 = b := by
          exact congrArg (fun p : C(unitInterval, B) => p 1)
            (hq.isCoveringMap.liftPath_const (e := b) rfl)
        exact h.trans hc
      have hfirst : (L 1).1 = b :=
        (congrArg (fun p : C(unitInterval, B) => p 1) hLb).trans hbaseEnd
      have hquot : quotient G B F (L 1) = quotient G B F (b, c) :=
        (congrFun (cov.liftPath_lifts γ (b, c) γ.source) 1).trans γ.target
      have hsecond : (L 1).2 = c := by
        apply fibreInclusion_injective (F := F) hq b
        have hp : (b, (L 1).2) = L 1 := Prod.ext hfirst.symm rfl
        exact (congrArg (quotient G B F) hp).trans hquot
      have hlast : L 1 = (b, c) := Prod.ext hfirst hsecond
      let δ : Path (b, c) (b, c) :=
        ⟨L, cov.liftPath_zero γ (b, c) γ.source, hlast⟩
      refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
      change Path.Homotopic.Quotient.mk (δ.map (quotient_continuous G B F)) =
        Path.Homotopic.Quotient.mk γ
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact congrFun (cov.liftPath_lifts γ (b, c) γ.source) t

end Wikipedia.HopfProblem.DiagonalQuotient
