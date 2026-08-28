import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusInjective

/-!
# Exact fibres of the actual base theta parametrization

For zero correction the genuine deck action has trivial phase multiplier.
Thus two planar representatives with the same marked base coordinate give
the same phase-one point of the original central quotient. On the three
chosen sides these are precisely the phase-one double cylinders. Their
proved exact fibre relation detects all the planar edge and corner
identifications, and forgetting the fixed circle phase gives exactly the
literal theta suspension relation.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

private theorem zeroCorrection_deckFibrePhase (v : Fin 2 → ℤ) :
    deckFibrePhase (0 : Matrix (Fin 2) (Fin 2) ℂ) v = 1 := by
  funext i
  simp [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_eq_exp]

/-- At zero correction, the constant phase-one lift respects the actual
integral translations detected by the marked base map. -/
private theorem phaseOneCollapse_eq_of_base_eq {y z : Plane}
    (h : baseTorusPoint y = baseTorusPoint z) :
    honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, y) =
      honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, z) := by
  obtain ⟨v, hv⟩ := (baseTorusPoint_eq_iff y z).mp h
  apply (honeycombCollapseMap_eq_iff (fun _ => 0) 1 zero_lt_one _ _).mpr
  refine ⟨v, hv, ?_⟩
  simp only [zeroCorrection_deckFibrePhase, inv_one, mul_one]
  exact (MulAction.stabilizer CompactFibreTorus
    ((honeycombHomeomorph 0 y).1 : Space)).one_mem

private theorem phaseOne_edgeCylinder (k : Fin 6) (t : unitInterval) :
    centralProject (fun _ => 0) 1 zero_lt_one (edgeCylinder 0 k (t, 1)) =
      honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, dualSidePoint k t) := by
  have h : centralProject (fun _ => 0) 1 zero_lt_one (edgeCylinder 0 k (t, 1)) =
      honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (hexagonCharacterSection k 1, (edgeArcBase 0 k t : Plane)) := by
    change centralCollapseMap (fun _ => 0) 1 zero_lt_one
      (hexagonCharacterSection k 1, edgeArcPositive 0 k t) =
        centralCollapseMap (fun _ => 0) 1 zero_lt_one
          (hexagonCharacterSection k 1, honeycombHomeomorph 0 (edgeArcBase 0 k t : Plane))
    rw [honeycombHomeomorph_edgeArcBase]
  simpa only [map_one, edgeArcBase_eq_dualSidePoint] using h

private theorem phaseOne_doubleCylinder (t : unitInterval) (j : Fin 3) :
    doubleCylinder (fun _ => 0) 1 zero_lt_one (t, thetaCircleInclusion j 1) =
      honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, orientedEdgeBasePoint t j) := by
  fin_cases j
  · exact phaseOne_edgeCylinder 0 t
  · exact phaseOne_edgeCylinder 1 (unitInterval.symm t)
  · exact phaseOne_edgeCylinder 2 t

/-- The first three oriented dual sides have exactly the theta suspension
fibres under the actual marked base quotient map. There are no additional
interior identifications, and the two endpoint classes remain distinct. -/
theorem thetaBaseCylinder_eq_iff (p q : unitInterval × Fin 3) :
    thetaBaseCylinder p = thetaBaseCylinder q ↔
      (suspensionSetoid (Fin 3)).r p q := by
  rcases p with ⟨s, j⟩
  rcases q with ⟨t, k⟩
  constructor
  · intro h
    have he : doubleCylinder (fun _ => 0) 1 zero_lt_one
        (s, thetaCircleInclusion j 1) =
          doubleCylinder (fun _ => 0) 1 zero_lt_one (t, thetaCircleInclusion k 1) := by
      rw [phaseOne_doubleCylinder, phaseOne_doubleCylinder]
      exact phaseOneCollapse_eq_of_base_eq h
    obtain ⟨hst, hzero | hone | hlabel⟩ :=
      (doubleCylinder_eq_iff (fun _ => 0) 1 zero_lt_one
        (s, thetaCircleInclusion j 1) (t, thetaCircleInclusion k 1)).mp he
    · exact ⟨hst, Or.inl hzero⟩
    · exact ⟨hst, Or.inr (Or.inl hone)⟩
    · refine ⟨hst, Or.inr (Or.inr ?_)⟩
      simpa only [thetaCircleLabel_inclusion] using congrArg thetaCircleLabel hlabel
  · exact thetaBaseCylinder_respects _ _

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
