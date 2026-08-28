import Wikipedia.HopfProblem.CuspControlledRetractionPositiveInterpolation
import Wikipedia.HopfProblem.CuspControlledRetractionConcatenation

/-!
# Modifying the positive deformation at one prescribed height

Concatenate an actual positive deformation with its constructed,
height-supported central interpolation. The new homotopy retains the
original fixed set, lattice equivariance, and nonincreasing height, while
its endpoint is exactly the normalized honeycomb map at the chosen height.
The later existence theorem supplies the original deformation from the
unconditional construction, rather than assuming it.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspPositiveRetraction CuspHoneycomb CuspPositive

/-- The explicit two-stage modification retains all deformation
properties and has the required exact endpoint at the chosen height. -/
theorem exists_positive_modification
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε)
    (hηε : η < ε) (hη : 0 ≤ η) (ρ : ℝ) (hρ : 0 < ρ)
    (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
    (hzero : ∀ q, P (0, q) = q)
    (hfix : ∀ s (q : ClosedPositiveTube η), time (q.1 : Space) = 0 → P (s, q) = q)
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (hequiv : ∀ s v q, P (s, closedPositiveTranslate C₀ η v q) =
      closedPositiveTranslate C₀ η v (P (s, q)))
    (hmono : ∀ s q, positiveHeight (P (s, q)) ≤ positiveHeight q) :
    ∃ Q : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η),
      (∀ q, Q (0, q) = q) ∧
      (∀ s (q : ClosedPositiveTube η), time (q.1 : Space) = 0 → Q (s, q) = q) ∧
      (∀ q : ClosedPositiveTube η, time ((Q (1, q)).1 : Space) = 0) ∧
      (∀ s v q, Q (s, closedPositiveTranslate C₀ η v q) =
        closedPositiveTranslate C₀ η v (Q (s, q))) ∧
      (∀ s q, positiveHeight (Q (s, q)) ≤ positiveHeight q) ∧
      (∀ q, positiveHeight q = ρ → Q (1, q) =
        positiveCentralInclusion η hη
          (honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space)))) ∧
      (∀ q, positiveHeight q ≤ ρ / 2 → Q (1, q) = P (1, q)) := by
  let K := centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ
  have hjoin : ∀ q, K (0, q) = P (1, q) :=
    centralInterpolation_zero P hone C₀ hε1 hR hηε hη ρ hρ
  let Q := Concatenation.map P K hjoin
  let R : C(ClosedPositiveTube η, ClosedPositiveTube η) → Prop := fun f =>
    (∀ q : ClosedPositiveTube η, time (q.1 : Space) = 0 → f q = q) ∧
    (∀ v q, f (closedPositiveTranslate C₀ η v q) = closedPositiveTranslate C₀ η v (f q)) ∧
    (∀ q, positiveHeight (f q) ≤ positiveHeight q)
  have hQP (s : unitInterval) : R (Concatenation.slice Q s) := by
    apply Concatenation.map_property P K hjoin R
    · intro t
      exact ⟨hfix t, hequiv t, hmono t⟩
    · intro t
      exact ⟨centralInterpolation_fixed P hone C₀ hε1 hR hηε hη ρ hρ hfix t,
        centralInterpolation_equivariant P hone C₀ hε1 hR hηε hη ρ hρ hequiv t,
        centralInterpolation_nonincreasing P hone C₀ hε1 hR hηε hη ρ hρ t⟩
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    exact (Concatenation.map_zero P K hjoin q).trans (hzero q)
  · intro s q hq
    exact (hQP s).1 q hq
  · intro q
    change time (((Concatenation.map P K hjoin) (1, q)).1 : Space) = 0
    rw [Concatenation.map_one]
    exact centralInterpolation_central P hone C₀ hε1 hR hηε hη ρ hρ 1 q
  · intro s v q
    exact (hQP s).2.1 v q
  · intro s q
    exact (hQP s).2.2 q
  · intro q hq
    exact (Concatenation.map_one P K hjoin q).trans
      (centralInterpolation_one_of_height_eq P hone C₀ hε1 hR hηε hη ρ hρ q hq)
  · intro q hq
    exact (Concatenation.map_one P K hjoin q).trans
      (centralInterpolation_eq_endpoint_of_height_le_half P hone C₀ hε1 hR hηε hη ρ hρ 1 q hq)

end Wikipedia.HopfProblem.CuspControlledRetraction
