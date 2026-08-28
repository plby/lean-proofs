import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureVertices
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureSegments

/-!
# Continuous interpolation between nearby complex-structure vertex lists

Each vertex follows its actual short logarithmic segment in the
complex-structure locus. The interpolation depends jointly on both lists and
time, reaches its endpoints, and fixes equal lists at every time.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructureVertices

variable {n m : ℕ}

def interpolationDomain (n m : ℕ) : Set (Space n m × Space n m) :=
  {p | ∀ i, (p.1 i, p.2 i) ∈ ComplexStructures.ShortLog.domain n}

theorem isOpen_interpolationDomain (n m : ℕ) : IsOpen (interpolationDomain n m) := by
  change IsOpen {p : Space n m × Space n m |
    ∀ i, (p.1 i, p.2 i) ∈ ComplexStructures.ShortLog.domain n}
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (ComplexStructures.ShortLog.isOpen_domain n).preimage
    (((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd))

theorem diagonal_mem_interpolationDomain (v : Space n m) :
    (v, v) ∈ interpolationDomain n m :=
  fun i ↦ ComplexStructures.ShortLog.diagonal_mem_domain (v i)

def interpolate (t : ℝ) (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    Space n m :=
  fun i ↦ ComplexStructures.ShortLog.segment (v i) (w i) (h i) t

theorem interpolate_zero (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    interpolate 0 v w h = v :=
  funext (fun i ↦ ComplexStructures.ShortLog.segment_zero (v i) (w i) (h i))

theorem interpolate_one (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    interpolate 1 v w h = w :=
  funext (fun i ↦ ComplexStructures.ShortLog.segment_one (v i) (w i) (h i))

theorem interpolate_self (t : ℝ) (v : Space n m)
    (h : (v, v) ∈ interpolationDomain n m) : interpolate t v v h = v :=
  funext (fun i ↦ ComplexStructures.ShortLog.segment_self (v i) t)

theorem interpolate_of_eq (t : ℝ) (v w : Space n m)
    (h : (v, w) ∈ interpolationDomain n m) (he : w = v) : interpolate t v w h = v := by
  subst w
  exact interpolate_self t v h

theorem continuous_interpolate {X : Type*} [TopologicalSpace X]
    (p q : X → Space n m) (hp : Continuous p) (hq : Continuous q)
    (hpair : ∀ x, (p x, q x) ∈ interpolationDomain n m) :
    Continuous (fun z : ℝ × X ↦ interpolate z.1 (p z.2) (q z.2) (hpair z.2)) := by
  apply continuous_pi
  intro i
  let endpoints : C(X, ComplexStructures.ShortLog.domain n) :=
    ⟨fun x ↦ ⟨(p x i, q x i), hpair x i⟩,
      (((continuous_apply i).comp hp).prodMk
        ((continuous_apply i).comp hq)).subtype_mk _⟩
  let input : C(ℝ × X, ComplexStructures.ShortLog.domain n × ℝ) :=
    ⟨fun z ↦ (endpoints z.2, z.1),
      (endpoints.continuous.comp continuous_snd).prodMk continuous_fst⟩
  exact (ComplexStructures.ShortLog.family.comp input).continuous

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructureVertices
