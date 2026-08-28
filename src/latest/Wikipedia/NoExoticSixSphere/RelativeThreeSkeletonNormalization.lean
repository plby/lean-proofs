import Wikipedia.NoExoticSixSphere.RelativeThreeSimplexCompression
import Wikipedia.NoExoticSixSphere.RelativeNormalizationPairHomotopy

/-!
# Coherent compression of the actual three-skeleton into the subspace

The original two-skeleton normalization is followed by the checked
boundary-fixed tetrahedron compression. Its homotopies extend coherently
to every higher simplex while preserving subspace-valued inputs. The
endpoint tetrahedra lie in the subspace and every endpoint four-simplex
has its whole boundary there.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair
open SecondHurewicz.SimplyConnected ThirdHurewicz

namespace NoExoticSixSphere.RelativeThreeSkeletonNormalization

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  [SimplyConnectedSpace (Fiber U a)]
  [Subsingleton (π_ 2 (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a))]
  (hπ₃ : ∀ b : U, Function.Surjective
    (HigherHomotopy.map (N := Fin 3) (subtypeInclusion U) (y := b) rfl))

def tetrahedronInitialData : RelativeSimplexHomotopyFamily.Stage U 2 where
  lower := stationarySimplexHomotopy 2
  upper := RelativeThreeSimplexCompression.homotopy U a hπ₃
  lower_zero _ _ := rfl
  upper_zero := RelativeThreeSimplexCompression.homotopy_zero U a hπ₃
  face := RelativeThreeSimplexCompression.homotopy_face U a hπ₃
  lower_mem smp hs p := hs p.2
  upper_mem := RelativeThreeSimplexCompression.homotopy_mem U a hπ₃

def tetrahedronData : (k : ℕ) → RelativeSimplexHomotopyFamily.Stage U (k + 2)
  | 0 => tetrahedronInitialData U a hπ₃
  | k + 1 => (tetrahedronData k).next

def tetrahedronHomotopy : (n : ℕ) → C(Simplex n, X) → C(I × Simplex n, X)
  | 0 => stationarySimplexHomotopy 0
  | 1 => stationarySimplexHomotopy 1
  | n + 2 => (tetrahedronData U a hπ₃ n).lower

theorem tetrahedronHomotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    tetrahedronHomotopy U a hπ₃ n smp (0, s) = smp s := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => exact (tetrahedronData U a hπ₃ n).lower_zero smp s

theorem tetrahedronHomotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (tetrahedronHomotopy U a hπ₃ n)
      (tetrahedronHomotopy U a hπ₃ (n + 1)) := by
  cases n with
  | zero => intro smp i; ext p; rfl
  | succ n =>
    cases n with
    | zero => intro smp i; ext p; rfl
    | succ n => exact (tetrahedronData U a hπ₃ n).face

theorem tetrahedronHomotopy_mem (n : ℕ) (smp : C(Simplex n, X))
    (hs : ∀ s, smp s ∈ U) (p : I × Simplex n) : tetrahedronHomotopy U a hπ₃ n smp p ∈ U := by
  cases n with
  | zero => exact hs p.2
  | succ n =>
    cases n with
    | zero => exact hs p.2
    | succ n => exact (tetrahedronData U a hπ₃ n).lower_mem smp hs p

variable [SimplyConnectedSpace X] [SimplyConnectedSpace U]
  (hπ₂ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def homotopy (n : ℕ) (smp : C(Simplex n, X)) : C(I × Simplex n, X) :=
  composeSimplexHomotopies (RelativeTwoSkeletonNormalization.homotopy U a hπ₂ n)
    (tetrahedronHomotopy U a hπ₃ n) (RelativeTwoSkeletonNormalization.homotopy_zero U a hπ₂ n)
    (tetrahedronHomotopy_zero U a hπ₃ n) smp

theorem homotopy_zero (n : ℕ) (smp : C(Simplex n, X)) (s : Simplex n) :
    homotopy U a hπ₃ hπ₂ n smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem homotopy_face (n : ℕ) :
    FaceCompatibleHomotopies n (homotopy U a hπ₃ hπ₂ n) (homotopy U a hπ₃ hπ₂ (n + 1)) :=
  composeSimplexHomotopies_face _ _ _ _ _ _ _ _
    (RelativeTwoSkeletonNormalization.homotopy_face U a hπ₂ n)
    (tetrahedronHomotopy_face U a hπ₃ n)

theorem homotopy_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex n) : homotopy U a hπ₃ hπ₂ n smp p ∈ U :=
  RelativeSimplexHomotopyFamily.compose_mem U _ _ _ _
    (RelativeTwoSkeletonNormalization.homotopy_mem U a hπ₂ n)
    (tetrahedronHomotopy_mem U a hπ₃ n) smp hs p

def endpoint (n : ℕ) (smp : C(Simplex n, X)) : C(Simplex n, X) :=
  timeSlice (homotopy U a hπ₃ hπ₂ n smp) 1

theorem endpoint_face (n : ℕ) (smp : C(Simplex (n + 1), X)) (i : Fin (n + 2)) :
    (endpoint U a hπ₃ hπ₂ (n + 1) smp).comp (simplexFace n i) =
      endpoint U a hπ₃ hπ₂ n (smp.comp (simplexFace n i)) :=
  timeSlice_face (homotopy_face U a hπ₃ hπ₂ n) smp i 1

theorem endpoint_mem (n : ℕ) (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) (s : Simplex n) :
    endpoint U a hπ₃ hπ₂ n smp s ∈ U := homotopy_mem U a hπ₃ hπ₂ n smp hs (1, s)

theorem endpoint_verticesBased (n : ℕ) (smp : C(Simplex n, X)) :
    VerticesBased a.val n (endpoint U a hπ₃ hπ₂ n smp) := by
  induction n with
  | zero =>
    intro i
    change composeSimplexHomotopies _ _ _ _ smp (1, stdSimplex.vertex i) = a.val
    rw [composeSimplexHomotopies_one]
    exact RelativeTwoSkeletonNormalization.endpoint_verticesBased U a hπ₂ 0 smp i
  | succ n ih =>
    apply verticesBased_of_faces
    intro i
    rw [endpoint_face]
    exact ih (smp.comp (simplexFace n i))

theorem endpoint_edge (smp : C(Simplex 1, X)) :
    endpoint U a hπ₃ hπ₂ 1 smp = ContinuousMap.const (Simplex 1) a.val := by
  ext s
  change composeSimplexHomotopies _ _ _ _ smp (1, s) = a.val
  rw [composeSimplexHomotopies_one]
  exact congrArg (fun f : C(Simplex 1, X) ↦ f s)
    (RelativeTwoSkeletonNormalization.endpoint_edge U a hπ₂ smp)

theorem endpoint_tetrahedron_mem (smp : C(Simplex 3, X)) (s : Simplex 3) :
    endpoint U a hπ₃ hπ₂ 3 smp s ∈ U := by
  change composeSimplexHomotopies _ _ _ _ smp (1, s) ∈ U
  rw [composeSimplexHomotopies_one]
  exact RelativeThreeSimplexCompression.homotopy_one_mem U a hπ₃
    (RelativeTwoSkeletonNormalization.endpoint U a hπ₂ 3 smp)
    (RelativeTwoSkeletonNormalization.endpoint_tetrahedron_boundary U a hπ₂ smp)
    (RelativeTwoSkeletonNormalization.endpoint_verticesBased U a hπ₂ 3 smp 0) s

theorem endpoint_fourSimplex_boundary (smp : C(Simplex 4, X)) (s : Simplex 4)
    (hs : s ∈ simplexBoundary 4) : endpoint U a hπ₃ hπ₂ 4 smp s ∈ U := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 3 (⟨s, hs⟩ : SimplexBoundary 4)
  have he : simplexFace 3 i t = s := congrArg Subtype.val ht
  rw [← he]
  have hf := congrArg (fun f : C(Simplex 3, X) ↦ f t)
    (endpoint_face U a hπ₃ hπ₂ 3 smp i)
  change ((endpoint U a hπ₃ hπ₂ 4 smp).comp (simplexFace 3 i)) t ∈ U
  rw [hf]
  exact endpoint_tetrahedron_mem U a hπ₃ hπ₂ (smp.comp (simplexFace 3 i)) t

theorem homotopy_const_zero :
    homotopy U a hπ₃ hπ₂ 0 (ContinuousMap.const (Simplex 0) a.val) =
      ContinuousMap.const (I × Simplex 0) a.val := by
  apply composeSimplexHomotopies_const
  · exact RelativeTwoSkeletonNormalization.homotopy_const_zero U a hπ₂
  · rfl

theorem homotopy_vertex (n : ℕ) (smp : C(Simplex n, X)) (i : Fin (n + 1))
    (hi : smp (stdSimplex.vertex (S := ℝ) i) = a.val) (t : I) :
    homotopy U a hπ₃ hπ₂ n smp (t, stdSimplex.vertex i) = a.val :=
  SimplexHomotopyVertexFixing.vertex_fixed (homotopy U a hπ₃ hπ₂) (homotopy_face U a hπ₃ hπ₂)
    a.val (homotopy_const_zero U a hπ₃ hπ₂) n smp i hi t

theorem homotopy_boundary (n : ℕ) (smp : C(Simplex (n + 1), X))
    (hU : ∀ s ∈ simplexBoundary (n + 1), smp s ∈ U)
    (t : I) (s : Simplex (n + 1)) (hs : s ∈ simplexBoundary (n + 1)) :
    homotopy U a hπ₃ hπ₂ (n + 1) smp (t, s) ∈ U := by
  obtain ⟨i, z, hz⟩ := simplexBoundary_exists_face n (⟨s, hs⟩ : SimplexBoundary (n + 1))
  have he : simplexFace n i z = s := congrArg Subtype.val hz
  rw [← he]
  have hf : homotopy U a hπ₃ hπ₂ (n + 1) smp (t, simplexFace n i z) =
      homotopy U a hπ₃ hπ₂ n (smp.comp (simplexFace n i)) (t, z) :=
    congrArg (fun F : C(I × Simplex n, X) ↦ F (t, z)) (homotopy_face U a hπ₃ hπ₂ n smp i)
  rw [hf]
  exact homotopy_mem U a hπ₃ hπ₂ n (smp.comp (simplexFace n i))
    (fun q ↦ hU (simplexFace n i q) (simplexFace_mem_boundary n i q)) (t, z)

def pairHomotopy (n : ℕ) (smp : C(Simplex n, X)) :
    smp.Homotopy (endpoint U a hπ₃ hπ₂ n smp) :=
  simplexFamilyHomotopy (homotopy U a hπ₃ hπ₂ n) (homotopy_zero U a hπ₃ hπ₂ n) smp

end NoExoticSixSphere.RelativeThreeSkeletonNormalization
