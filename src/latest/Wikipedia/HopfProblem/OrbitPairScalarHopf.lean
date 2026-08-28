import Wikipedia.HopfProblem.OrbitPairRadialHopf
import Mathlib.Analysis.Complex.Isometry

/-!
# Radial Hopf coordinates for the scalar normal framing

The proved global normal framing of the fixed curve uses equal scalar
weights. Conjugating the first coordinate relates that action to the
original opposite-weight action. We make this change explicit and keep
the exact unit scalar in the orbit-fibre theorem.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

/-- Convert the scalar framing to the opposite-weight Euclidean normal coordinates. -/
def scalarCoordinates : (ℂ × ℂ) ≃L[ℝ] Normal :=
  (Complex.conjCLE.prodCongr (ContinuousLinearEquiv.refl ℝ ℂ)).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm

@[simp] theorem scalarCoordinates_apply (v : ℂ × ℂ) :
    scalarCoordinates v = WithLp.toLp 2 (starRingEnd ℂ v.1, v.2) := rfl

theorem norm_scalarCoordinates_sq (v : ℂ × ℂ) :
    ‖scalarCoordinates v‖ ^ 2 = Complex.normSq v.1 + Complex.normSq v.2 := by
  simp [WithLp.prod_norm_sq_eq_of_L2, Complex.normSq_eq_norm_sq]

/-- The parameter is unchanged when passing from equal to opposite weights. -/
theorem scalarCoordinates_smul (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (v : ℂ × ℂ) :
    scalarCoordinates ((u : ℂ) • v) = oppositeAction u (scalarCoordinates v) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change starRingEnd ℂ ((u : ℂ) * v.1) =
      (u : ℂ)⁻¹ * starRingEnd ℂ v.1
    rw [map_mul, Complex.inv_eq_conj hu]
  · rfl

/-- The radius-preserving quotient in the actual global scalar normal framing. -/
def scalarHopfMap (v : ℂ × ℂ) : Transverse := radialHopfMap (scalarCoordinates v)

@[simp] theorem scalarHopfMap_zero : scalarHopfMap 0 = 0 := by
  rw [scalarHopfMap, map_zero, radialHopfMap_zero]

theorem scalarHopfMap_eq_zero_iff (v : ℂ × ℂ) : scalarHopfMap v = 0 ↔ v = 0 := by
  rw [scalarHopfMap, radialHopfMap_eq_zero_iff, ← scalarCoordinates.map_zero]
  exact scalarCoordinates.injective.eq_iff

theorem norm_scalarHopfMap_sq (v : ℂ × ℂ) :
    ‖scalarHopfMap v‖ ^ 2 = Complex.normSq v.1 + Complex.normSq v.2 := by
  rw [scalarHopfMap, norm_radialHopfMap, norm_scalarCoordinates_sq]

theorem scalarHopfMap_eq_iff (v w : ℂ × ℂ) :
    scalarHopfMap v = scalarHopfMap w ↔
      ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ (u : ℂ) • v = w := by
  rw [scalarHopfMap, scalarHopfMap, radialHopfMap_eq_iff]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, scalarCoordinates.injective ?_⟩
    rw [scalarCoordinates_smul u hu]
    exact WithLp.ofLp_injective 2 he
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    exact congrArg WithLp.ofLp (scalarCoordinates_smul u hu v).symm

theorem scalarHopfMap_smul (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (v : ℂ × ℂ) :
    scalarHopfMap ((u : ℂ) • v) = scalarHopfMap v :=
  ((scalarHopfMap_eq_iff _ _).mpr ⟨u, hu, rfl⟩).symm

theorem scalarHopfMap_isOpenQuotientMap : IsOpenQuotientMap scalarHopfMap :=
  radialHopfMap_isOpenQuotientMap.comp scalarCoordinates.toHomeomorph.isOpenQuotientMap

theorem continuous_scalarHopfMap : Continuous scalarHopfMap :=
  scalarHopfMap_isOpenQuotientMap.continuous

theorem scalarHopfMap_surjective : Function.Surjective scalarHopfMap :=
  scalarHopfMap_isOpenQuotientMap.surjective

end Wikipedia.HopfProblem.OrbitPair
