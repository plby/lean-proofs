import Wikipedia.NoExoticSixSphere.RelativeCoefficientCycleRepresentatives
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles

/-!
# The actual coefficient homology connecting map of a pair

Every relative cycle has an ambient lift whose boundary is the inclusion
of a genuine subspace cycle. The original categorical connecting map is
the class of this cycle. Coefficients are arbitrary integral modules.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X] (U : Set X)

def connecting (n : ℕ) :
    (complex A U).homology (n + 1) →ₗ[ℤ] (coefficientComplex A U).homology n :=
  connectingMap (sequence_shortExact A U) n

theorem connecting_cycleClass (n : ℕ) (z : ModuleHomology.Cycle (complex A U) (n + 1))
    (c : CoefficientChains.Chains A X (n + 1)) (hc : quotientMap A U (n + 1) c = z.val)
    (w : ModuleHomology.Cycle (coefficientComplex A U) n)
    (hw : ((inclusion A U).f n).hom w.val =
      ((coefficientComplex A X).d (n + 1) n).hom c) :
    connecting A U n (ModuleHomology.cycleClass (complex A U) (n + 1) z) =
      ModuleHomology.cycleClass (coefficientComplex A U) n w :=
  PeriodTorusHigherHomology.connectingMap_cycleClass (sequence_shortExact A U) n z c hc w hw

theorem exists_connecting_lift (n : ℕ) (z : ModuleHomology.Cycle (complex A U) (n + 1)) :
    ∃ (c : CoefficientChains.Chains A X (n + 1))
      (_hc : quotientMap A U (n + 1) c = z.val)
      (w : ModuleHomology.Cycle (coefficientComplex A U) n),
      ((inclusion A U).f n).hom w.val =
        ((coefficientComplex A X).d (n + 1) n).hom c ∧
      connecting A U n (ModuleHomology.cycleClass (complex A U) (n + 1) z) =
        ModuleHomology.cycleClass (coefficientComplex A U) n w := by
  obtain ⟨c, hc⟩ := quotientMap_surjective A U (n + 1) z.val
  have hz : ((complex A U).d (n + 1) n).hom z.val = 0 :=
    (congrArg (fun j ↦ ((complex A U).d (n + 1) j).hom z.val = 0)
      (Nat.add_sub_cancel n 1)).mp (ModuleHomology.cycle_condition (complex A U) (n + 1) z)
  have hd : quotientMap A U n (((coefficientComplex A X).d (n + 1) n).hom c) = 0 :=
    (boundary_quotientMap A U (n + 1) n c).symm.trans
      ((congrArg ((complex A U).d (n + 1) n).hom hc).trans hz)
  obtain ⟨v, hv⟩ := (quotientMap_eq_zero_iff A U n _).mp hd
  let w := ModuleHomology.mkCycle (coefficientComplex A U) n v
    (connectingMap_lift_is_cycle (sequence_shortExact A U) n c v hv (n - 1))
  exact ⟨c, hc, w, hv, connecting_cycleClass A U n z c hc w hv⟩

theorem connecting_range (n : ℕ) :
    LinearMap.range (connecting A U n) =
      LinearMap.ker (homologyLinearMap (inclusion A U) n) :=
  exact_at_leftHomology (sequence_shortExact A U) n

end NoExoticSixSphere.RelativeCoefficients
