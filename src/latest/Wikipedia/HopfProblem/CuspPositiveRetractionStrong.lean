import Wikipedia.HopfProblem.CuspPositiveRetractionExistence

/-!
# A genuine strong deformation retraction of the positive cusp tube

The already constructed positive deformation supplies a continuous
retraction onto the literal positive central fibre.  The accompanying
`HomotopyRel` fixes that fibre at every stage and retains equivariance
for the actual positive twisted lattice action.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

open ToricSpace

/-- The literal central fibre inside the actual positive part of the toric space. -/
abbrev PositiveCentralFibre := {q : PositivePart // time (q : Space) = 0}

/-- The inclusion of the actual positive central fibre into a closed positive tube. -/
def positiveCentralInclusion (η : ℝ) (hη : 0 ≤ η) :
    C(PositiveCentralFibre, ClosedPositiveTube η) where
  toFun q := ⟨q.1, by rw [q.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem positiveCentralInclusion_coe (η : ℝ) (hη : 0 ≤ η)
    (q : PositiveCentralFibre) : (positiveCentralInclusion η hη q).1 = q.1 := rfl

theorem positiveCentralInclusion_range (η : ℝ) (hη : 0 ≤ η) :
    range (positiveCentralInclusion η hη) =
      {q : ClosedPositiveTube η | time (q.1 : Space) = 0} := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    exact r.2
  · intro hq
    exact ⟨⟨q.1, hq⟩, rfl⟩

private def positiveEndpointRetraction {η : ℝ}
    (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) :
    C(ClosedPositiveTube η, PositiveCentralFibre) where
  toFun q := ⟨(P (1, q)).1, hone q⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      (P.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _

private theorem positiveEndpointRetraction_comp_inclusion {η : ℝ}
    (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
    (hfixed : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
      time (q.1 : Space) = 0 → P (s, q) = q)
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) (hη : 0 ≤ η) :
    (positiveEndpointRetraction P hone).comp (positiveCentralInclusion η hη) =
      ContinuousMap.id PositiveCentralFibre := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change (P (1, positiveCentralInclusion η hη q)).1 = q.1
  exact congrArg (fun x : ClosedPositiveTube η => x.1)
    (hfixed 1 (positiveCentralInclusion η hη q) q.2)

private def positiveHomotopyRel {η : ℝ}
    (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
    (hzero : ∀ q : ClosedPositiveTube η, P (0, q) = q)
    (hfixed : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
      time (q.1 : Space) = 0 → P (s, q) = q)
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0) (hη : 0 ≤ η) :
    (ContinuousMap.id (ClosedPositiveTube η)).HomotopyRel
      ((positiveCentralInclusion η hη).comp (positiveEndpointRetraction P hone))
      (range (positiveCentralInclusion η hη)) where
  toFun p := P p
  continuous_toFun := P.continuous
  map_zero_left := hzero
  map_one_left _ := rfl
  prop' s q hq := by
    obtain ⟨r, rfl⟩ := hq
    exact hfixed s (positiveCentralInclusion η hη r) r.2

/-- Lemma 7.8, expressed as an actual strong deformation retraction onto
the literal positive central fibre, uniformly for all smaller positive radii. -/
theorem exists_positive_strongDeformationRetraction (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ →
        ∃ R : C(ClosedPositiveTube η, PositiveCentralFibre),
          R.comp (positiveCentralInclusion η hη.le) = ContinuousMap.id PositiveCentralFibre ∧
          ∃ H : (ContinuousMap.id (ClosedPositiveTube η)).HomotopyRel
              ((positiveCentralInclusion η hη.le).comp R)
              (range (positiveCentralInclusion η hη.le)),
            (∀ s v q, H (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
              CuspPositive.closedPositiveTranslate C₀ η v (H (s, q))) ∧
            (∀ s q, ‖time ((H (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀1, hP⟩ := exists_positive_closed_deformation C₀
  refine ⟨η₀, hη₀, hη₀1, ?_⟩
  intro η hη hηη₀
  obtain ⟨P, hzero, hfixed, hone, hequiv, hnorm⟩ := hP η hη hηη₀
  refine ⟨positiveEndpointRetraction P hone,
    positiveEndpointRetraction_comp_inclusion P hfixed hone hη.le,
    positiveHomotopyRel P hzero hfixed hone hη.le, ?_, ?_⟩
  · exact hequiv
  · exact hnorm

end Wikipedia.HopfProblem.CuspPositiveRetraction
