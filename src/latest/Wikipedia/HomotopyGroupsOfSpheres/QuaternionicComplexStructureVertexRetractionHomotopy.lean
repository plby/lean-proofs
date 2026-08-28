import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureVertexInterpolation
import Wikipedia.HomotopyGroupsOfSpheres.NeighborhoodRetractionHomotopy

/-!
# Controlled relative homotopies in complex-structure vertex products

Short logarithmic interpolation connects a neighborhood retraction to the
inclusion. Restricting to an open condition on the whole compact time interval
keeps the homotopy in any prescribed open neighborhood of the retract.
-/

open Set
open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructureVertices

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]

noncomputable def interpolationHomotopy (n m : ℕ) :
    C(unitInterval × interpolationDomain n m, Space n m) := by
  refine ⟨fun z ↦ interpolate (z.1 : ℝ) z.2.1.1 z.2.1.2 z.2.2, ?_⟩
  apply continuous_pi
  intro i
  let endpoints : C(interpolationDomain n m, ComplexStructures.ShortLog.domain n) :=
    ⟨fun d ↦ ⟨(d.1.1 i, d.1.2 i), d.2 i⟩,
      ((((continuous_apply i).comp continuous_fst).comp continuous_subtype_val).prodMk
        (((continuous_apply i).comp continuous_snd).comp continuous_subtype_val)).subtype_mk _⟩
  let input : C(unitInterval × interpolationDomain n m,
      ComplexStructures.ShortLog.domain n × ℝ) :=
    ⟨fun z ↦ (endpoints z.2, (z.1 : ℝ)),
      (endpoints.continuous.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)⟩
  exact (ComplexStructures.ShortLog.family.comp input).continuous

theorem interpolationHomotopy_zero (d : interpolationDomain n m) :
    interpolationHomotopy n m (0, d) = d.1.1 :=
  interpolate_zero d.1.1 d.1.2 d.2

theorem interpolationHomotopy_one (d : interpolationDomain n m) :
    interpolationHomotopy n m (1, d) = d.1.2 :=
  interpolate_one d.1.1 d.1.2 d.2

theorem interpolationHomotopy_self (y : Space n m)
    (h : (y, y) ∈ interpolationDomain n m) (t : unitInterval) :
    interpolationHomotopy n m (t, ⟨(y, y), h⟩) = y :=
  interpolate_self (t : ℝ) y h

theorem exists_retraction_homotopy_neighborhood (U K W : Set (Space n m))
    (hU : IsOpen U) (hKU : K ⊆ U) (r : C(U, K))
    (hr : ∀ u : U, u.1 ∈ K → (r u).1 = u.1)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ V : Set (Space n m), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ p : C(M, Space n m), (∀ x, p x ∈ V) →
        ∃ q : C(M, Space n m), (∀ x, q x ∈ K) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' K), ∀ t x, G (t, x) ∈ W := by
  exact RetractionInterpolation.exists_homotopy_neighborhood (Y := Space n m) (M := M)
    (interpolationDomain n m) (isOpen_interpolationDomain n m)
    diagonal_mem_interpolationDomain (interpolationHomotopy n m)
    interpolationHomotopy_zero interpolationHomotopy_one interpolationHomotopy_self
    U K W hU hKU r hr hW hKW

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructureVertices
