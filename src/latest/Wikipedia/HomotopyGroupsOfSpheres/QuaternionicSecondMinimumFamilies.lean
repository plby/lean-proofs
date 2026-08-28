import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumDeformation

/-!
# Deformation to a continuous family of minimum rotation polygons

The minimum-locus homeomorphism identifies the endpoint with an actual
continuous family of anticommuting complex structures, the original midpoint
parameters of the second minimum-path family.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open ComplexStructures ComplexStructureVertices

variable {M : Type*} [TopologicalSpace M] {n m : ℕ}

noncomputable def rotationFamilyVertices {a : ComplexStructures.Space n}
    (τ : Fin (m + 2) → ℝ) (P : C(M, AnticommutingStructures.Space a)) :
    C(M, ComplexStructureVertices.Space n m) :=
  ⟨fun x ↦ rotationVertices τ (P x), (continuous_rotationVertices a τ).comp P.continuous⟩

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem exists_homotopy_to_rotation_family (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ P : AnticommutingStructures.Space a, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)
    (cap : ℝ) (hcap : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap)) (hd : finrank ℝ B < n)
    (p : C(M, ComplexStructureVertices.Space n m)) (hp : ∀ x, p x ∈ admissible a b m)
    (start : ℝ) (hstart : start < cap) (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ P : C(M, AnticommutingStructures.Space a),
      ∃ G : ContinuousMap.HomotopyRel p (rotationFamilyVertices τ P)
          (p ⁻¹' minimumSet a b τ),
        ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨q, hq, G, hG⟩ := exists_homotopy_into_minimum (I := I)
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact hd p hp start hstart hpstart
  let qm : C(M, minimumSet a b τ) := ⟨fun x ↦ ⟨q x, hq x⟩, q.continuous.subtype_mk _⟩
  let e := rotationMinimumHomeomorph a b τ hτ hzero hone hanti hsmall
    (isCompact_energySublevel_of_le a b τ hcap.le hcompact)
  let P : C(M, AnticommutingStructures.Space a) :=
    ⟨fun x ↦ e.symm (qm x), e.symm.continuous.comp qm.continuous⟩
  have hend : rotationFamilyVertices τ P = q := by
    apply ContinuousMap.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (qm x))
  exact ⟨P, G.cast rfl hend.symm, hG⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
