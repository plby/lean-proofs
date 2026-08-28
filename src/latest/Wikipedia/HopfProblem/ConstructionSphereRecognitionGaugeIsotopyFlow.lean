import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCapSmooth
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticBasic

/-!
# Cap translations commute with the original full vertical flow

Both maps preserve the original disc coordinate and add their exact
vectors in the same fibre. They commute on the original complex-vector
cover, on the actual varying-period torus family, and on the original
finite quotient. The flow parameter is arbitrary complex time; no fibre
coordinate or period contribution is removed.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods
open Threefold.VerticalAction

/-- Exact commutation already on the original complex-vector cover. -/
theorem capVectorTranslation_vectorFlow {j : Kind} (D : Equivariant.Data j)
    (c : Disc → RealCoordinates) (s : ℝ) (u : ℂ) (p : Disc × ComplexPlane₂) :
    capVectorTranslation D c s (Period.vectorFlow u p) =
      Period.vectorFlow u (capVectorTranslation D c s p) := by
  apply Prod.ext
  · rfl
  · change (p.2 + Period.vector u) + D.periods.periodEquiv p.1 (s • c p.1) =
      (p.2 + D.periods.periodEquiv p.1 (s • c p.1)) + Period.vector u
    abel

/-- The full original inverse-period vector is retained on the torus family. -/
theorem capFamilyTranslation_periodFlow (P : HolomorphicPeriodMap ℂ Disc)
    (c : Disc → RealCoordinates) (s : ℝ) (u : ℂ) (p : P.TotalSpace) :
    capFamilyTranslation c s (Period.flow P u p) =
      Period.flow P u (capFamilyTranslation c s p) := by
  apply Prod.ext
  · rfl
  · change (p.2 + standardLattice.mkQ ((P.periodEquiv p.1).symm (Period.vector u))) +
        standardLattice.mkQ (s • c p.1) =
      (p.2 + standardLattice.mkQ (s • c p.1)) +
        standardLattice.mkQ ((P.periodEquiv p.1).symm (Period.vector u))
    abel

variable {j : Kind} (D : Equivariant.Data j) (c : Disc → RealCoordinates)
  (hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, RealCoordinates) ∞ c)
  (hcov : ∀ z, c (familyRotation j z) = flatLinear j (c z))

/-- Every cap translation commutes with the actual vertical flow at every
complex time, on the unchanged original finite-orbit filling. -/
theorem capTranslation_flow (s : ℝ) (u : ℂ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    capTranslation D c hc hcov s
        (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u y) =
      Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u
        (capTranslation D c hc hcov s y) := by
  obtain ⟨p, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  change D.quotient j.twist (mainTwist_admissible j)
      (capFamilyTranslation c s (Period.flow D.periods u p)) =
    D.quotient j.twist (mainTwist_admissible j)
      (Period.flow D.periods u (capFamilyTranslation c s p))
  exact congrArg (D.quotient j.twist (mainTwist_admissible j))
    (capFamilyTranslation_periodFlow D.periods c s u p)

/-- Function-level commutation with the original full complex flow. -/
theorem capTranslation_commute_flow (s : ℝ) (u : ℂ) :
    Function.Commute (capTranslation D c hc hcov s)
      (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u) :=
  capTranslation_flow D c hc hcov s u

/-- The actual inverse cap map commutes with the same original flow. -/
theorem capTranslation_symm_flow (s : ℝ) (u : ℂ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    (capTranslation D c hc hcov s).symm
        (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u y) =
      Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u
        ((capTranslation D c hc hcov s).symm y) := by
  simp only [capTranslation_symm_apply]
  exact capTranslation_flow D c hc hcov (-s) u y

/-- The smooth upgrade retains this exact equivariance with the native complex flow. -/
theorem capTranslationDiffeomorph_flow (s : ℝ) (u : ℂ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    capTranslationDiffeomorph D c hc hcov s
        (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u y) =
      Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j) u
        (capTranslationDiffeomorph D c hc hcov s y) :=
  capTranslation_flow D c hc hcov s u y

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
