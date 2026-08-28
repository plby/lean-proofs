import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusMap
import Wikipedia.HopfProblem.CuspCollapseCentralQuotient

/-!
# The six actual boundary cylinders reduce to three

The opposite-edge reduction uses the original twisted lattice action and
its compact phase factor. Character factorization then puts each resulting
phase in the chosen circle section. This includes both collapsed endpoints.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent CuspRetraction CuspPositiveRetraction CuspCollapse
open CuspHoneycombHexagon

theorem edgeArcPositive_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    edgeArcPositive C₀ (k + 3) (unitInterval.symm t) =
      positiveCentralTranslate C₀ (cuspVector (hexagonRay k)) (edgeArcPositive C₀ k t) := by
  apply Subtype.ext
  apply Subtype.ext
  exact compatibleBoundaryArc_opposite_coe C₀ k t

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original quotient map is unchanged by the exact central deck action. -/
theorem centralCollapseMap_phaseDeckMap (v : Fin 2 → ℤ) (p : PhasePositiveSpace) :
    centralCollapseMap C ε hε (phaseDeckMap (C 0) v p) =
      centralCollapseMap C ε hε p := by
  apply (centralProject_eq_iff C ε hε _ _).mpr
  exact ⟨v, (centralPolarMap_phaseDeckMap C v p).symm⟩

/-- Opposite edges have the same actual quotient image after the fixed
compact deck phase has been removed. -/
theorem centralCollapseMap_opposite (k : Fin 6) (t : unitInterval)
    (u : CompactFibreTorus) :
    centralCollapseMap C ε hε (u, edgeArcPositive (C 0) (k + 3) (unitInterval.symm t)) =
      centralCollapseMap C ε hε
        ((deckFibrePhase (C 0) (cuspVector (hexagonRay k)))⁻¹ * u,
          edgeArcPositive (C 0) k t) := by
  have h := centralCollapseMap_phaseDeckMap C ε hε (cuspVector (hexagonRay k))
    ((deckFibrePhase (C 0) (cuspVector (hexagonRay k)))⁻¹ * u,
      edgeArcPositive (C 0) k t)
  simpa only [phaseDeckMap, mul_inv_cancel_left, ← edgeArcPositive_opposite] using h

/-- The explicit change of the surviving circle phase across opposite edges. -/
theorem centralProject_edgeCylinder_opposite (k : Fin 6) (t : unitInterval) (a : Circle) :
    centralProject C ε hε (edgeCylinder (C 0) (k + 3) (unitInterval.symm t, a)) =
      centralProject C ε hε (edgeCylinder (C 0) k
        (t, hexagonCharacter k
          ((deckFibrePhase (C 0) (cuspVector (hexagonRay k)))⁻¹ *
            hexagonCharacterSection (k + 3) a))) := by
  change centralCollapseMap C ε hε
    (hexagonCharacterSection (k + 3) a,
      edgeArcPositive (C 0) (k + 3) (unitInterval.symm t)) = _
  rw [centralCollapseMap_opposite]
  exact (congrArg (centralProject C ε hε)
    (edgeCylinder_character_all (C 0) k t
      ((deckFibrePhase (C 0) (cuspVector (hexagonRay k)))⁻¹ *
        hexagonCharacterSection (k + 3) a))).symm

theorem centralProject_edgeCylinder_opposite_exists (k : Fin 6)
    (t : unitInterval) (a : Circle) :
    ∃ b : Circle,
      centralProject C ε hε (edgeCylinder (C 0) (k + 3) (unitInterval.symm t, a)) =
        centralProject C ε hε (edgeCylinder (C 0) k (t, b)) :=
  ⟨_, centralProject_edgeCylinder_opposite C ε hε k t a⟩

/-- Each of the six original boundary cylinders has a representative in
the chosen three-circle cylinder, including all boundary phases. -/
theorem edgeCylinder_mem_range_doubleCylinder (k : Fin 6) (t : unitInterval) (a : Circle) :
    centralProject C ε hε (edgeCylinder (C 0) k (t, a)) ∈
      Set.range (doubleCylinder C ε hε) := by
  fin_cases k
  · exact ⟨(t, Sum.inl a), rfl⟩
  · change centralProject C ε hε (edgeCylinder (C 0) (1 : Fin 6) (t, a)) ∈ _
    refine ⟨(unitInterval.symm t, Sum.inr (Sum.inl a)), ?_⟩
    rw [doubleCylinder_middle, unitInterval.symm_symm]
  · exact ⟨(t, Sum.inr (Sum.inr a)), rfl⟩
  · change centralProject C ε hε (edgeCylinder (C 0) (3 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 0
      (unitInterval.symm t) a
    refine ⟨(unitInterval.symm t, Sum.inl b), ?_⟩
    simpa only [show (0 + 3 : Fin 6) = 3 from by decide,
      doubleCylinder_first, unitInterval.symm_symm] using hb.symm
  · change centralProject C ε hε (edgeCylinder (C 0) (4 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 1
      (unitInterval.symm t) a
    refine ⟨(t, Sum.inr (Sum.inl b)), ?_⟩
    simpa only [show (1 + 3 : Fin 6) = 4 from by decide,
      doubleCylinder_middle, unitInterval.symm_symm] using hb.symm
  · change centralProject C ε hε (edgeCylinder (C 0) (5 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 2
      (unitInterval.symm t) a
    refine ⟨(unitInterval.symm t, Sum.inr (Sum.inr b)), ?_⟩
    simpa only [show (2 + 3 : Fin 6) = 5 from by decide,
      doubleCylinder_last, unitInterval.symm_symm] using hb.symm

/-- Every original compact fibre phase over any compatible edge is in
the actual image of the three chosen circle cylinders. -/
theorem centralCollapseMap_edgeArc_mem_range_doubleCylinder (k : Fin 6)
    (t : unitInterval) (u : CompactFibreTorus) :
    centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) ∈
      Set.range (doubleCylinder C ε hε) := by
  have h := edgeCylinder_mem_range_doubleCylinder C ε hε k t (hexagonCharacter k u)
  change centralProject C ε hε (centralPolarMap (u, edgeArcPositive (C 0) k t)) ∈ _
  rwa [edgeCylinder_character_all] at h

theorem range_doubleSuspensionMap :
    Set.range (doubleSuspensionMap C ε hε) = Set.range (doubleCylinder C ε hε) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨⟨t, z⟩, rfl⟩ := Suspension.mk_surjective p
    exact ⟨(t, z), rfl⟩
  · rintro ⟨⟨t, z⟩, rfl⟩
    exact ⟨Suspension.mk t z, rfl⟩

end Wikipedia.HopfProblem.CuspCentralHomology
