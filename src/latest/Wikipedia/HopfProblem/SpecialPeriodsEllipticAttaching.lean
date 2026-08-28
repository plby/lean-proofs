import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingFibres
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroup

/-!
# Exact local elliptic attaching relations for the special threefold

The relation is stated for the actual logarithmic meridian and the actual
positive period loop, inside the chosen small elliptic piece.  Both signs
are computed using its genuine retraction and affine universal cover.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge CuspUniformization

/-- The clockwise logarithmic meridian raised to the elliptic order is the
positive straight loop for the actual invariant twist vector. -/
theorem attachingLoop_pow_order (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    (FundamentalGroup.fromPath ⟦attachingLoop j s₀ hs₀ hr⟧) ^ j.order =
      FundamentalGroup.fromPath ⟦attachingFibreLoop j s₀ hs₀ hr j.twist⟧ := by
  apply (attachingDeckEquiv j s₀ hs₀ hr).injective
  rw [map_pow, attachingDeckEquiv_attachingLoop, attachingDeckEquiv_attachingFibreLoop,
    inv_pow, deckGenerator_pow_order j j.twist (mainTwist_admissible j).1]
  exact (map_inv (deckTranslationHom j j.twist) (Multiplicative.ofAdd j.twist)).symm

/-- The chosen positive small-disc radius always admits the displayed actual loops. -/
theorem exists_attaching_parameters (j : Kind) :
    ∃ s : ℂ, 0 < s.im ∧ ‖exponential s‖ ^ j.order < specialBaseCover.radius (some j) :=
  exists_logMeridian_parameters j _ (specialBaseCover.radius_pos (some j))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
