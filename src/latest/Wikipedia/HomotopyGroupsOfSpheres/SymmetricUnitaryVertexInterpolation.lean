import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexSpace
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySegments
import Wikipedia.HomotopyGroupsOfSpheres.NeighborhoodRetractionHomotopy

/-! # Short constrained vertex interpolation and controlled relative retraction homotopies -/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

def interpolationDomain (N : Type*) [Fintype N] [DecidableEq N] (m : ℕ) :
    Set (Space N m × Space N m) := {p | ∀ i, (p.1 i, p.2 i) ∈ ShortLog.domain N}

theorem isOpen_interpolationDomain (N : Type*) [Fintype N] [DecidableEq N] (m : ℕ) :
    IsOpen (interpolationDomain N m) := by
  change IsOpen {p : Space N m × Space N m | ∀ i, (p.1 i, p.2 i) ∈ ShortLog.domain N}
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (ShortLog.isOpen_domain (N := N)).preimage
    (((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd))

theorem diagonal_mem_interpolationDomain (v : Space N m) :
    (v, v) ∈ interpolationDomain N m := fun i ↦ ShortLog.diagonal_mem_domain (v i)

def interpolate (t : ℝ) (v w : Space N m) (h : (v, w) ∈ interpolationDomain N m) : Space N m :=
  fun i ↦ ShortLog.segment (v i) (w i) (h i) t

theorem interpolate_zero (v w : Space N m) (h : (v, w) ∈ interpolationDomain N m) :
    interpolate 0 v w h = v := funext (fun i ↦ ShortLog.segment_zero (v i) (w i) (h i))

theorem interpolate_one (v w : Space N m) (h : (v, w) ∈ interpolationDomain N m) :
    interpolate 1 v w h = w := funext (fun i ↦ ShortLog.segment_one (v i) (w i) (h i))

theorem interpolate_self (t : ℝ) (v : Space N m) (h : (v, v) ∈ interpolationDomain N m) :
    interpolate t v v h = v := funext (fun i ↦ ShortLog.segment_self (v i) t)

theorem interpolate_of_eq (t : ℝ) (v w : Space N m) (h : (v, w) ∈ interpolationDomain N m)
    (he : w = v) : interpolate t v w h = v := by
  subst w
  exact interpolate_self t v h

theorem continuous_interpolate {X : Type*} [TopologicalSpace X]
    (p q : X → Space N m) (hp : Continuous p) (hq : Continuous q)
    (hpair : ∀ x, (p x, q x) ∈ interpolationDomain N m) :
    Continuous (fun z : ℝ × X ↦ interpolate z.1 (p z.2) (q z.2) (hpair z.2)) := by
  apply continuous_pi
  intro i
  let endpoints : C(X, ShortLog.domain N) :=
    ⟨fun x ↦ ⟨(p x i, q x i), hpair x i⟩,
      (((continuous_apply i).comp hp).prodMk
        ((continuous_apply i).comp hq)).subtype_mk _⟩
  let input : C(ℝ × X, ShortLog.domain N × ℝ) :=
    ⟨fun z ↦ (endpoints z.2, z.1),
      (endpoints.continuous.comp continuous_snd).prodMk continuous_fst⟩
  exact (ShortLog.family.comp input).continuous

def interpolationHomotopy (N : Type*) [Fintype N] [DecidableEq N] (m : ℕ) :
    C(unitInterval × interpolationDomain N m, Space N m) := by
  refine ⟨fun z ↦ interpolate (z.1 : ℝ) z.2.1.1 z.2.1.2 z.2.2, ?_⟩
  have h := continuous_interpolate
    (fun d : interpolationDomain N m ↦ d.val.1) (fun d : interpolationDomain N m ↦ d.val.2)
    (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
    (fun d ↦ d.property)
  exact h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem interpolationHomotopy_zero (d : interpolationDomain N m) :
    interpolationHomotopy N m (0, d) = d.1.1 := interpolate_zero d.1.1 d.1.2 d.2

theorem interpolationHomotopy_one (d : interpolationDomain N m) :
    interpolationHomotopy N m (1, d) = d.1.2 := interpolate_one d.1.1 d.1.2 d.2

theorem interpolationHomotopy_self (y : Space N m) (h : (y, y) ∈ interpolationDomain N m)
    (t : unitInterval) : interpolationHomotopy N m (t, ⟨(y, y), h⟩) = y :=
  interpolate_self (t : ℝ) y h

theorem exists_retraction_homotopy_neighborhood {M : Type*} [TopologicalSpace M]
    (U K W : Set (Space N m)) (hU : IsOpen U) (hKU : K ⊆ U) (r : C(U, K))
    (hr : ∀ u : U, u.1 ∈ K → (r u).1 = u.1) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ V : Set (Space N m), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ p : C(M, Space N m), (∀ x, p x ∈ V) →
        ∃ q : C(M, Space N m), (∀ x, q x ∈ K) ∧
          ∃ G : ContinuousMap.HomotopyRel p q (p ⁻¹' K), ∀ t x, G (t, x) ∈ W := by
  exact RetractionInterpolation.exists_homotopy_neighborhood (Y := Space N m) (M := M)
    (interpolationDomain N m) (isOpen_interpolationDomain N m)
    diagonal_mem_interpolationDomain (interpolationHomotopy N m)
    interpolationHomotopy_zero interpolationHomotopy_one interpolationHomotopy_self
    U K W hU hKU r hr hW hKW

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace
