import Wikipedia.HopfProblem.CuspPositiveRetractionStraightened
import Wikipedia.HopfProblem.CuspPositiveRetractionDescent
import Wikipedia.HopfProblem.CuspRetractionPolarHomotopy

/-!
# Prescribed endpoints under straightening and quotient descent

The actual frozen straightening preserves the cusp parameter and fixes
the central fibre.  Conjugating a supplied homotopy therefore transports
its prescribed endpoint by precomposition with that straightening.
The endpoint formula then passes to the actual cusp quotient through
the already constructed equivariant homotopy descent.

These are transport lemmas, not existence assumptions about a controlled
collapse or about its geometric endpoint map.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}

/-- A pointwise prescribed endpoint gives the same class in the original
cusp quotient when the homotopy is descended. -/
theorem closedHomotopyDescentRetraction_endpoint_of_eq (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hHequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
      H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hCanalytic : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0)
    (hη : 0 ≤ η) (x : ClosedTube η) (y : CentralFibre)
    (hEndx : H (1, x) = centralIntoClosedTube η hη y) :
    (closedHomotopyDescentRetraction C hηε H hHequiv hCanalytic hone
      (closedQuotientMap C hηε x) : CuspQuotient.QuotientSpace C ε) =
      (closedQuotientMap C hηε (centralIntoClosedTube η hη y) :
        CuspQuotient.QuotientSpace C ε) := by
  change (closedHomotopyDescent C hηε H 1 (closedQuotientMap C hηε x) :
    CuspQuotient.QuotientSpace C ε) = _
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hHequiv, hEndx]

theorem closedHomotopyDescentRetraction_endpoint (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hHequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
      H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hCanalytic : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0)
    (hη : 0 ≤ η) (E : ClosedTube η → CentralFibre)
    (x : ClosedTube η) (hEndx : H (1, x) = centralIntoClosedTube η hη (E x)) :
    (closedHomotopyDescentRetraction C hηε H hHequiv hCanalytic hone
      (closedQuotientMap C hηε x) : CuspQuotient.QuotientSpace C ε) =
      (closedQuotientMap C hηε (centralIntoClosedTube η hη (E x)) :
        CuspQuotient.QuotientSpace C ε) :=
  closedHomotopyDescentRetraction_endpoint_of_eq C hηε H hHequiv hCanalytic hone
    hη x (E x) hEndx

section Straightening

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hCcont : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε) (hηε : η < ε)

local notation "G" => closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε

/-- The inverse of the actual straightening also fixes the literal central
fibre pointwise. -/
theorem closedFrozenStraightening_symm_fixed (x : ClosedTube η)
    (hx : time (x : Space) = 0) : (G).symm x = x := by
  apply (G).injective
  rw [(G).apply_symm_apply,
    closedFrozenStraightening_fixed C hε hε1 hCcont hRC hRD hηε x hx]

variable (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hη : 0 ≤ η) (E : ClosedTube η → CentralFibre) {ρ : ℝ}

local notation "Hₛ" => straightenedHomotopy C hε hε1 hCcont hRC hRD hηε H

/-- Pointwise transport does not require an endpoint map to be defined
away from the point under consideration. -/
theorem straightenedHomotopy_endpoint_of_eq (x : ClosedTube η) (y : CentralFibre)
    (he : H (1, G x) = centralIntoClosedTube η hη y) :
    Hₛ (1, x) = centralIntoClosedTube η hη y := by
  rw [straightenedHomotopy_apply, he]
  exact closedFrozenStraightening_symm_fixed C hε hε1 hCcont hRC hRD hηε
    (centralIntoClosedTube η hη y) y.2

theorem straightenedHomotopy_endpoint_of_eq_coe (x : ClosedTube η) (y : CentralFibre)
    (he : H (1, G x) = centralIntoClosedTube η hη y) :
    (Hₛ (1, x) : Space) = (y : Space) :=
  congrArg Subtype.val
    (straightenedHomotopy_endpoint_of_eq C hε hε1 hCcont hRC hRD hηε H hη x y he)

/-- On the prescribed norm-time sphere, straightening changes the endpoint
to `E ∘ G`; its inverse makes no further change on the central fibre. -/
theorem straightenedHomotopy_endpoint
    (hEnd : ∀ x : ClosedTube η, ‖time (x : Space)‖ = ρ →
      H (1, x) = centralIntoClosedTube η hη (E x))
    (x : ClosedTube η) (hx : ‖time (x : Space)‖ = ρ) :
    Hₛ (1, x) = centralIntoClosedTube η hη (E (G x)) := by
  have hGx : ‖time (G x : Space)‖ = ρ :=
    (congrArg norm (closedFrozenStraightening_base C hε hε1 hCcont hRC hRD hηε x)).trans hx
  exact straightenedHomotopy_endpoint_of_eq C hε hε1 hCcont hRC hRD hηε H hη
    x (E (G x)) (hEnd (G x) hGx)

/-- The same endpoint identity in the actual ambient toric space. -/
theorem straightenedHomotopy_endpoint_coe
    (hEnd : ∀ x : ClosedTube η, ‖time (x : Space)‖ = ρ →
      H (1, x) = centralIntoClosedTube η hη (E x))
    (x : ClosedTube η) (hx : ‖time (x : Space)‖ = ρ) :
    (Hₛ (1, x) : Space) = (E (G x) : Space) :=
  congrArg Subtype.val
    (straightenedHomotopy_endpoint C hε hε1 hCcont hRC hRD hηε H hη E hEnd x hx)

/-- Pointwise transport followed by descent, for a prescribed central
point that need not come from a globally defined endpoint map. -/
theorem straightenedDescentRetraction_endpoint_of_eq
    (hHequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
      H (s, closedTranslate (frozen C) η v x) =
        closedTranslate (frozen C) η v (H (s, x)))
    (hCanalytic : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0)
    (x : ClosedTube η) (y : CentralFibre)
    (he : H (1, G x) = centralIntoClosedTube η hη y) :
    (closedHomotopyDescentRetraction C hηε Hₛ
      (straightenedHomotopy_equivariant C hε hε1 hCcont hRC hRD hηε H hHequiv)
      hCanalytic (straightenedHomotopy_one_central C hε hε1 hCcont hRC hRD hηε H hone)
      (closedQuotientMap C hηε x) : CuspQuotient.QuotientSpace C ε) =
      (closedQuotientMap C hηε (centralIntoClosedTube η hη y) :
        CuspQuotient.QuotientSpace C ε) := by
  apply closedHomotopyDescentRetraction_endpoint_of_eq C hηε Hₛ
    (straightenedHomotopy_equivariant C hε hε1 hCcont hRC hRD hηε H hHequiv)
    hCanalytic (straightenedHomotopy_one_central C hε hε1 hCcont hRC hRD hηε H hone)
    hη x y
  exact straightenedHomotopy_endpoint_of_eq C hε hε1 hCcont hRC hRD hηε H hη x y he

/-- The actual quotient retraction of the straightened homotopy has the
prescribed endpoint class `E (G x)`. -/
theorem straightenedDescentRetraction_endpoint
    (hHequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
      H (s, closedTranslate (frozen C) η v x) =
        closedTranslate (frozen C) η v (H (s, x)))
    (hCanalytic : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0)
    (hEnd : ∀ x : ClosedTube η, ‖time (x : Space)‖ = ρ →
      H (1, x) = centralIntoClosedTube η hη (E x))
    (x : ClosedTube η) (hx : ‖time (x : Space)‖ = ρ) :
    (closedHomotopyDescentRetraction C hηε Hₛ
      (straightenedHomotopy_equivariant C hε hε1 hCcont hRC hRD hηε H hHequiv)
      hCanalytic (straightenedHomotopy_one_central C hε hε1 hCcont hRC hRD hηε H hone)
      (closedQuotientMap C hηε x) : CuspQuotient.QuotientSpace C ε) =
      (closedQuotientMap C hηε (centralIntoClosedTube η hη (E (G x))) :
        CuspQuotient.QuotientSpace C ε) := by
  apply closedHomotopyDescentRetraction_endpoint C hηε Hₛ
    (straightenedHomotopy_equivariant C hε hε1 hCcont hRC hRD hηε H hHequiv)
    hCanalytic (straightenedHomotopy_one_central C hε hε1 hCcont hRC hRD hηε H hone)
    hη (fun y => E (G y)) x
  exact straightenedHomotopy_endpoint C hε hε1 hCcont hRC hRD hηε H hη E hEnd x hx

end Straightening

end Wikipedia.HopfProblem.CuspControlledRetraction
