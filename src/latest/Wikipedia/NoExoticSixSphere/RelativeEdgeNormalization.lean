import Wikipedia.NoExoticSixSphere.SimplexHomotopySubspace

/-!
# Based-edge contraction preserving the original subspace

An edge lying in the subspace uses its actual subspace nullhomotopy;
other edges use the ambient construction. Both choices fix every original
vertex. Thus the choices are compatible with zero-dimensional faces,
contract all based edges, and preserve the actual relative subcomplex.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeEdgeNormalization

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (U : Set X) [SimplyConnectedSpace U] (a : U)

def restrict (smp : C(Simplex 1, X)) (hs : ∀ s, smp s ∈ U) : C(Simplex 1, U) :=
  ⟨fun s ↦ ⟨smp s, hs s⟩, smp.continuous.subtype_mk _⟩

def homotopy (smp : C(Simplex 1, X)) : C(I × Simplex 1, X) := by
  classical
  exact if hs : ∀ s, smp s ∈ U then
    (subtypeInclusion U).comp (edgeStraighteningHomotopy a (restrict U smp hs))
  else edgeStraighteningHomotopy a.val smp

theorem homotopy_zero (smp : C(Simplex 1, X)) (s : Simplex 1) :
    homotopy U a smp (0, s) = smp s := by
  classical
  unfold homotopy
  split
  · rename_i hs
    exact congrArg Subtype.val (edgeStraighteningHomotopy_zero a (restrict U smp hs) s)
  · exact edgeStraighteningHomotopy_zero a.val smp s

theorem homotopy_one (smp : C(Simplex 1, X)) (h : VerticesBased a.val 1 smp)
    (s : Simplex 1) : homotopy U a smp (1, s) = a.val := by
  classical
  unfold homotopy
  split
  · rename_i hs
    exact congrArg Subtype.val (edgeStraighteningHomotopy_one a (restrict U smp hs)
      (Subtype.ext (h 0)) (Subtype.ext (h 1)) s)
  · exact edgeStraighteningHomotopy_one a.val smp (h 0) (h 1) s

theorem homotopy_vertex (smp : C(Simplex 1, X)) (i : Fin 2) (t : I) :
    homotopy U a smp (t, stdSimplex.vertex (S := ℝ) i) = smp (stdSimplex.vertex (S := ℝ) i) := by
  classical
  unfold homotopy
  split
  · rename_i hs
    exact congrArg Subtype.val (edgeStraighteningHomotopy_vertex a (restrict U smp hs) i t)
  · exact edgeStraighteningHomotopy_vertex a.val smp i t

theorem homotopy_mem (smp : C(Simplex 1, X)) (hs : ∀ s, smp s ∈ U) (p : I × Simplex 1) :
    homotopy U a smp p ∈ U := by
  classical
  rw [homotopy, dif_pos hs]
  exact (edgeStraighteningHomotopy a (restrict U smp hs) p).property

theorem homotopy_const : homotopy U a (ContinuousMap.const (Simplex 1) a.val) =
    ContinuousMap.const (I × Simplex 1) a.val := by
  classical
  have hs : ∀ s : Simplex 1, (ContinuousMap.const (Simplex 1) a.val) s ∈ U :=
    fun _ ↦ a.property
  rw [homotopy, dif_pos hs]
  ext p
  change (edgeStraighteningHomotopy a (ContinuousMap.const (Simplex 1) a) p).val = a.val
  rw [edgeStraighteningHomotopy_const]
  rfl

theorem homotopy_face :
    FaceCompatibleHomotopies 0 (stationarySimplexHomotopy 0) (homotopy U a) := by
  intro smp i
  ext p
  change homotopy U a smp (p.1, simplexFace 0 i p.2) = smp (simplexFace 0 i p.2)
  rw [simplexZero_eq_vertex p.2, simplexFace_vertex]
  exact homotopy_vertex U a smp _ p.1

end NoExoticSixSphere.RelativeEdgeNormalization
