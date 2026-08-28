import Wikipedia.HopfProblem.CuspCentralHomologyEdgeCharacters
import Wikipedia.HopfProblem.CuspCentralHomologyEdgeStabilizers
import Wikipedia.HopfProblem.CuspCollapseCentralStrata

/-!
# Actual circle orbits over the open honeycomb edges

The determinant characters factor the actual compact fibre-torus action.
Over the interior of an actual compatible boundary arc this gives a
homeomorphism onto the literal modulus fibre. At the two endpoints all
phases collapse to the corresponding original toric triple point.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent CuspRetraction CuspPositiveRetraction CuspCollapse
open CuspHoneycombHexagon

theorem centralPhaseOrbit_eq_iff_character (k : Fin 6) (q : PositiveCentralFibre)
    (hq : MulAction.stabilizer CompactFibreTorus (q.1 : Space) =
      edgeCircle (hexagonRay k)) (u v : CompactFibreTorus) :
    centralPhaseOrbit q u = centralPhaseOrbit q v ↔
      hexagonCharacter k u = hexagonCharacter k v := by
  rw [centralPhaseOrbit_apply, centralPhaseOrbit_apply, centralPolarMap_eq_iff]
  simp only [true_and, hq]
  exact (hexagonCharacter_eq_iff k u v).symm

/-- The actual circle map obtained by applying the explicit character section. -/
def characterCircleOrbit (k : Fin 6) (q : PositiveCentralFibre) (a : Circle) :
    CentralModulusFibre q := centralPhaseOrbitToFibre q (hexagonCharacterSection k a)

theorem characterCircleOrbit_continuous (k : Fin 6) (q : PositiveCentralFibre) :
    Continuous (characterCircleOrbit k q) :=
  (centralPhaseOrbitToFibre_continuous q).comp (hexagonCharacterSection_continuous k)

/-- Every original phase acts through its determinant character. -/
theorem characterCircleOrbit_character (k : Fin 6) (q : PositiveCentralFibre)
    (hq : MulAction.stabilizer CompactFibreTorus (q.1 : Space) =
      edgeCircle (hexagonRay k)) (u : CompactFibreTorus) :
    characterCircleOrbit k q (hexagonCharacter k u) = centralPhaseOrbitToFibre q u := by
  apply Subtype.ext
  apply (centralPhaseOrbit_eq_iff_character k q hq _ _).mpr
  exact hexagonCharacter_section k _

theorem characterCircleOrbit_injective (k : Fin 6) (q : PositiveCentralFibre)
    (hq : MulAction.stabilizer CompactFibreTorus (q.1 : Space) =
      edgeCircle (hexagonRay k)) : Function.Injective (characterCircleOrbit k q) := by
  intro a b hab
  have he := (centralPhaseOrbit_eq_iff_character k q hq _ _).mp
    (congrArg Subtype.val hab)
  simpa only [hexagonCharacter_section] using he

theorem characterCircleOrbit_surjective (k : Fin 6) (q : PositiveCentralFibre)
    (hq : MulAction.stabilizer CompactFibreTorus (q.1 : Space) =
      edgeCircle (hexagonRay k)) : Function.Surjective (characterCircleOrbit k q) := by
  intro x
  obtain ⟨u, rfl⟩ := centralPhaseOrbitToFibre_surjective q x
  exact ⟨hexagonCharacter k u, characterCircleOrbit_character k q hq u⟩

/-- The original modulus fibre, with its inherited topology, is the circle
parametrized by the actual edge character. -/
def characterCircleOrbitHomeomorph (k : Fin 6) (q : PositiveCentralFibre)
    (hq : MulAction.stabilizer CompactFibreTorus (q.1 : Space) =
      edgeCircle (hexagonRay k)) : Circle ≃ₜ CentralModulusFibre q :=
  ((characterCircleOrbit_continuous k q).isClosedEmbedding
    (characterCircleOrbit_injective k q hq)).toIsEmbedding.toHomeomorphOfSurjective
    (characterCircleOrbit_surjective k q hq)

@[simp] theorem characterCircleOrbitHomeomorph_coe (k : Fin 6)
    (q : PositiveCentralFibre)
    (hq : MulAction.stabilizer CompactFibreTorus (q.1 : Space) =
      edgeCircle (hexagonRay k)) (a : Circle) :
    (characterCircleOrbitHomeomorph k q hq a : CentralFibre) =
      centralPolarMap (hexagonCharacterSection k a, q) := rfl

/-- The actual compatible edge point, regarded in the positive central fibre. -/
def edgeArcPositive (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) : PositiveCentralFibre :=
  ⟨⟨(compatibleBoundaryArc C₀ k t).1.1, (compatibleBoundaryArc C₀ k t).1.2⟩,
    time_eq_zero_of_mem_rayDivisor (compatibleBoundaryArc C₀ k t).1.1.2⟩

@[simp] theorem edgeArcPositive_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    (edgeArcPositive C₀ k t).1.1 = ((compatibleBoundaryArc C₀ k t).1.1 : Space) := rfl

theorem edgeArcPositive_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    Continuous (edgeArcPositive C₀ k) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (continuous_subtype_val.comp
    (continuous_subtype_val.comp (compatibleBoundaryArc C₀ k).continuous))

theorem edgeArcPositive_injective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    Function.Injective (edgeArcPositive C₀ k) := by
  intro s t h
  apply (compatibleBoundaryArc C₀ k).injective
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : PositiveCentralFibre => q.1.1) h

theorem edgeArcPositive_stabilizer (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    MulAction.stabilizer CompactFibreTorus ((edgeArcPositive C₀ k t).1 : Space) =
      edgeCircle (hexagonRay k) :=
  compatibleBoundaryArc_stabilizer C₀ k t ht0 ht1

/-- Circle phases over a literal compatible positive boundary arc. -/
def edgeCylinder (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) : CentralFibre :=
  centralPolarMap (hexagonCharacterSection k p.2, edgeArcPositive C₀ k p.1)

@[simp] theorem edgeCylinder_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) :
    (edgeCylinder C₀ k p : Space) = compactFibreAction (hexagonCharacterSection k p.2)
      ((compatibleBoundaryArc C₀ k p.1).1.1 : Space) := rfl

theorem edgeCylinder_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    Continuous (edgeCylinder C₀ k) :=
  centralPolarMap_continuous.comp (((hexagonCharacterSection_continuous k).comp
    continuous_snd).prodMk ((edgeArcPositive_continuous C₀ k).comp continuous_fst))

@[simp] theorem edgeCylinder_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) :
    centralModulus (edgeCylinder C₀ k p) = edgeArcPositive C₀ k p.1 :=
  centralModulus_centralPolarMap _

/-- The original phase action on an open edge factors through the explicit
character, with no change to its actual toric image. -/
theorem edgeCylinder_character (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (u : CompactFibreTorus) :
    edgeCylinder C₀ k (t, hexagonCharacter k u) =
      centralPolarMap (u, edgeArcPositive C₀ k t) :=
  congrArg Subtype.val (characterCircleOrbit_character k (edgeArcPositive C₀ k t)
    (edgeArcPositive_stabilizer C₀ k t ht0 ht1) u)

theorem edgeCylinder_eq_iff_of_interior (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (a b : Circle) :
    edgeCylinder C₀ k (s, a) = edgeCylinder C₀ k (t, b) ↔ s = t ∧ a = b := by
  constructor
  · intro h
    have hst : s = t := edgeArcPositive_injective C₀ k
      (by simpa only [edgeCylinder_modulus] using congrArg centralModulus h)
    subst t
    refine ⟨rfl, ?_⟩
    apply characterCircleOrbit_injective k (edgeArcPositive C₀ k s)
      (edgeArcPositive_stabilizer C₀ k s hs0 hs1)
    exact Subtype.ext h
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem edgeCylinder_zero_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (a : Circle) :
    (edgeCylinder C₀ k (0, a) : Space) = inclusion (zeroTriangle (k - 1)) 0 := by
  rw [edgeCylinder_coe, compatibleBoundaryArc_zero, positiveBoundaryArc_zero_coe,
    compactFibreAction_inclusion_zero]

@[simp] theorem edgeCylinder_one_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (a : Circle) :
    (edgeCylinder C₀ k (1, a) : Space) = inclusion (zeroTriangle k) 0 := by
  rw [edgeCylinder_coe, compatibleBoundaryArc_one, positiveBoundaryArc_one_coe,
    compactFibreAction_inclusion_zero]

/-- Character factorization remains valid at both collapsed endpoints. -/
theorem edgeCylinder_character_all (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (u : CompactFibreTorus) :
    edgeCylinder C₀ k (t, hexagonCharacter k u) =
      centralPolarMap (u, edgeArcPositive C₀ k t) := by
  by_cases ht0 : t = 0
  · subst t
    apply Subtype.ext
    rw [edgeCylinder_zero_coe, centralPolarMap_coe, edgeArcPositive_coe,
      compatibleBoundaryArc_zero, positiveBoundaryArc_zero_coe,
      compactFibreAction_inclusion_zero]
  by_cases ht1 : t = 1
  · subst t
    apply Subtype.ext
    rw [edgeCylinder_one_coe, centralPolarMap_coe, edgeArcPositive_coe,
      compatibleBoundaryArc_one, positiveBoundaryArc_one_coe,
      compactFibreAction_inclusion_zero]
  exact edgeCylinder_character C₀ k t ht0 ht1 u

/-- The ordinary circle is homeomorphic to the literal modulus fibre over
every interior point of an actual compatible edge. -/
def edgeArcCircleHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Circle ≃ₜ CentralModulusFibre (edgeArcPositive C₀ k t) :=
  characterCircleOrbitHomeomorph k (edgeArcPositive C₀ k t)
    (edgeArcPositive_stabilizer C₀ k t ht0 ht1)

@[simp] theorem edgeArcCircleHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : Circle) :
    (edgeArcCircleHomeomorph C₀ k t ht0 ht1 a : CentralFibre) =
      edgeCylinder C₀ k (t, a) := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
