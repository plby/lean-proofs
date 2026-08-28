import Wikipedia.NoExoticSixSphere.RelativeNormalizationData
import Wikipedia.NoExoticSixSphere.RelativeSimplexHomotopyTail
import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberCompression

/-!
# Raising the actual relative normalization by one degree

The new boundary-fixed simplex compression begins above the old normalized
skeleton. Its stationary lower family extends coherently in all higher
degrees. Composing the two actual homotopies preserves every field of the
normalization data and moves one further simplex dimension into the source.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected ThirdHurewicz

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U) (n : ℕ)
  [PathConnectedSpace (Fiber U a)]
  (hpi : ∀ k, 0 < k → k < n + 3 → ∀ p : Fiber U a, Subsingleton (π_ k (Fiber U a) p))
  (hs : ∀ b : U, Function.Surjective
    (HigherHomotopy.map (N := Fin (n + 3)) (subtypeInclusion U) (y := b) rfl))

def compressionStage : RelativeSimplexHomotopyFamily.Stage U (n + 2) where
  lower := stationarySimplexHomotopy (n + 2)
  upper := RelativeSimplexFiberCompression.homotopy U a (n + 3) hpi hs
  lower_zero _ _ := rfl
  upper_zero := RelativeSimplexFiberCompression.homotopy_zero U a (n + 3) hpi hs
  face := RelativeSimplexFiberCompression.homotopy_face U a (n + 2) hpi hs
  lower_mem _ hU p := hU p.2
  upper_mem := RelativeSimplexFiberCompression.homotopy_mem U a (n + 3) hpi hs

namespace Data

variable {U a n} (D : Data U a n)

def nextHomotopy (k : ℕ) (smp : C(Simplex k, X)) : C(I × Simplex k, X) :=
  composeSimplexHomotopies (D.homotopy k) ((compressionStage U a n hpi hs).totalFamily k)
    (D.initial k) ((compressionStage U a n hpi hs).totalFamily_initial k) smp

theorem nextHomotopy_initial (k : ℕ) (smp : C(Simplex k, X)) (s : Simplex k) :
    D.nextHomotopy hpi hs k smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem nextHomotopy_face (k : ℕ) :
    FaceCompatibleHomotopies k (D.nextHomotopy hpi hs k) (D.nextHomotopy hpi hs (k + 1)) :=
  composeSimplexHomotopies_face _ _ _ _ _ _ _ _ (D.face k)
    ((compressionStage U a n hpi hs).totalFamily_face rfl k)

theorem nextHomotopy_mem (k : ℕ) (smp : C(Simplex k, X)) (hU : ∀ s, smp s ∈ U)
    (p : I × Simplex k) : D.nextHomotopy hpi hs k smp p ∈ U :=
  RelativeSimplexHomotopyFamily.compose_mem U _ _ _ _ (D.preserves k)
    ((compressionStage U a n hpi hs).totalFamily_mem k) smp hU p

def nextEndpoint (k : ℕ) (smp : C(Simplex k, X)) : C(Simplex k, X) :=
  timeSlice (D.nextHomotopy hpi hs k smp) 1

theorem nextEndpoint_face (k : ℕ) (smp : C(Simplex (k + 1), X)) (i : Fin (k + 2)) :
    (D.nextEndpoint hpi hs (k + 1) smp).comp (simplexFace k i) =
      D.nextEndpoint hpi hs k (smp.comp (simplexFace k i)) :=
  timeSlice_face (D.nextHomotopy_face hpi hs k) smp i 1

theorem nextEndpoint_vertices (k : ℕ) (smp : C(Simplex k, X)) :
    VerticesBased a.val k (D.nextEndpoint hpi hs k smp) := by
  induction k with
  | zero =>
    intro i
    change composeSimplexHomotopies _ _ _ _ smp (1, stdSimplex.vertex i) = a.val
    rw [composeSimplexHomotopies_one]
    change (compressionStage U a n hpi hs).totalFamily 0 (D.endpoint 0 smp)
      (1, stdSimplex.vertex i) = a.val
    rw [(compressionStage U a n hpi hs).totalFamily_of_lt 0 (by omega)]
    exact D.vertices 0 smp i
  | succ k ih =>
    apply verticesBased_of_faces
    intro i
    rw [D.nextEndpoint_face]
    exact ih (smp.comp (simplexFace k i))

theorem nextEndpoint_edge (smp : C(Simplex 1, X)) :
    D.nextEndpoint hpi hs 1 smp = ContinuousMap.const (Simplex 1) a.val := by
  ext s
  change composeSimplexHomotopies _ _ _ _ smp (1, s) = a.val
  rw [composeSimplexHomotopies_one]
  change (compressionStage U a n hpi hs).totalFamily 1 (D.endpoint 1 smp) (1, s) = a.val
  rw [(compressionStage U a n hpi hs).totalFamily_of_lt 1 (by omega)]
  exact congrArg (fun f : C(Simplex 1, X) ↦ f s) (D.edge smp)

theorem nextEndpoint_lower_mem (smp : C(Simplex (n + 3), X)) (s : Simplex (n + 3)) :
    D.nextEndpoint hpi hs (n + 3) smp s ∈ U := by
  change composeSimplexHomotopies _ _ _ _ smp (1, s) ∈ U
  rw [composeSimplexHomotopies_one]
  change (compressionStage U a n hpi hs).totalFamily (n + 3)
    (D.endpoint (n + 3) smp) (1, s) ∈ U
  rw [(compressionStage U a n hpi hs).totalFamily_succ]
  exact RelativeSimplexFiberCompression.homotopy_one_mem U a (n + 3) hpi hs
    (D.endpoint (n + 3) smp) (D.endpoint_boundary smp) (D.vertices (n + 3) smp 0) s

theorem nextHomotopy_constant_zero :
    D.nextHomotopy hpi hs 0 (ContinuousMap.const (Simplex 0) a.val) =
      ContinuousMap.const (I × Simplex 0) a.val := by
  apply composeSimplexHomotopies_const
  · exact D.constant_zero
  · rw [(compressionStage U a n hpi hs).totalFamily_of_lt 0 (by omega)]
    rfl

def next : Data U a (n + 1) where
  homotopy := D.nextHomotopy hpi hs
  initial := D.nextHomotopy_initial hpi hs
  face := D.nextHomotopy_face hpi hs
  preserves := D.nextHomotopy_mem hpi hs
  vertices := D.nextEndpoint_vertices hpi hs
  edge := D.nextEndpoint_edge hpi hs
  lower_mem := D.nextEndpoint_lower_mem hpi hs
  constant_zero := D.nextHomotopy_constant_zero hpi hs

end Data

end NoExoticSixSphere.RelativeNormalization
