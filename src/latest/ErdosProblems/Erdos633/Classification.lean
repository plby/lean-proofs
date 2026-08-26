import ErdosProblems.Erdos633.RationalCornerPartitions
import ErdosProblems.Erdos633.RationalReptileNecessity

/-!
# The complete classification in Erdős problem 633

Every congruent triangular tiling with a nonsquare number of pieces has one
of the eight listed shapes, and every listed shape has an actual nonsquare
congruent tiling. Rational-angle nonreptile tilings are covered by the
geometrically extracted corner data and their complete finite classification.
No edge-to-edge, coordinate-field, rationality, or conjugation hypothesis is
assumed in the final equivalence.
-/

namespace Erdos633

theorem CongruentTiling.rational_scalene_angle_classification
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : R.CommensurableAngles) (hinj : Function.Injective P.cornerAngle) :
    PermutedTriple P.cornerAngle R.cornerAngle ∨
      PermutedTriple P.cornerAngle ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  obtain ⟨α, β, γ, hangle, ⟨D⟩⟩ := T.rationalCornerData_of_commensurableAngles hR
  have href : (fun j => Real.pi * (![α, β, γ] j : ℝ)) = R.cornerAngle :=
    funext (fun j => (hangle j).symm)
  rcases D.scalene_classification hinj with hsim | hthirty
  · exact Or.inl (href ▸ hsim)
  · exact Or.inr hthirty

theorem CongruentTiling.hasListedNonsquareShape_of_rational_tile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : R.CommensurableAngles) : HasListedNonsquareShape P := by
  by_cases hinj : Function.Injective P.cornerAngle
  · rcases T.rational_scalene_angle_classification hR hinj with hsim | hthirty
    · exact T.hasListedNonsquareShape_of_rational_reptile hN hR hsim
    · exact P.hasListedNonsquareShape_of_permuted_thirty hthirty
  · exact P.hasListedNonsquareShape_of_equal_angles
      (P.equal_angles_of_not_injective_cornerAngle hinj)

theorem CongruentTiling.hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) : HasListedNonsquareShape P := by
  by_cases hR : R.CommensurableAngles
  · exact T.hasListedNonsquareShape_of_rational_tile hN hR
  · exact T.hasListedNonsquareShape_of_irrational_tile hN hR

theorem Triangle.admitsNonsquareTiling_iff_listed (P : Triangle) :
    AdmitsNonsquareTiling P ↔ HasListedNonsquareShape P := by
  constructor
  · rintro ⟨N, R, hN, ⟨T⟩⟩
    exact T.hasListedNonsquareShape hN
  · exact P.admitsNonsquareTiling_of_listed_shape

def Triangle.OnlySquareTilings (P : Triangle) : Prop :=
  ∀ (N : ℕ) (R : Triangle), Nonempty (CongruentTiling P R N) → IsSquare N

/-- A triangle admits only square counts exactly when it lies outside all
eight explicitly listed nonsquare families. -/
theorem erdos_633 (P : Triangle) :
    (∀ (N : ℕ) (R : Triangle), Nonempty (CongruentTiling P R N) → IsSquare N) ↔
      ¬ ∃ Q : Triangle, Q.carrier = P.carrier ∧ ListedNonsquareAngles Q := by
  change P.OnlySquareTilings ↔ ¬ HasListedNonsquareShape P
  constructor
  · intro h hs
    obtain ⟨N, R, hN, hT⟩ := P.admitsNonsquareTiling_of_listed_shape hs
    exact hN (h N R hT)
  · intro hs N R hT
    by_contra hN
    exact hs ((Classical.choice hT).hasListedNonsquareShape hN)

end Erdos633
