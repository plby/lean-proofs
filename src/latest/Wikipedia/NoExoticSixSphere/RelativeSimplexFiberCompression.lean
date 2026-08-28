import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberLifting
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeBasic

/-!
# Boundary-fixed relative simplex compression in every dimension

The actual fiber lifting theorem supplies the required deformations.
The total family is stationary on subspace-valued simplices and on inputs
not satisfying the boundary and based-vertex conditions. Every boundary
point is fixed, so the family has a stationary coherent lower face family.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexFiberCompression

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  [PathConnectedSpace (Fiber U a)]

section AtDegree

variable (n : ℕ)
  (hpi : ∀ k, 0 < k → k < n → ∀ p : Fiber U a, Subsingleton (π_ k (Fiber U a) p))
  (hs : ∀ b : U, Function.Surjective
    (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := b) rfl))

def liftedSimplex (smp : RelativeSimplex U n)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) = a.val) : C(Simplex n, U) :=
  (RelativeSimplexFiberLifting.exists_lift U a n hpi hs smp (stdSimplex.vertex 0) hv).choose

def liftHomotopy (smp : RelativeSimplex U n)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) = a.val) :
    smp.val.HomotopyRel ((subtypeInclusion U).comp (liftedSimplex U a n hpi hs smp hv))
      (simplexBoundary n) :=
  Classical.choice
    (RelativeSimplexFiberLifting.exists_lift U a n hpi hs smp
      (stdSimplex.vertex 0) hv).choose_spec.2

def homotopy (smp : C(Simplex n, X)) : C(I × Simplex n, X) := by
  classical
  exact if ∀ s, smp s ∈ U then stationarySimplexHomotopy n smp
    else if hb : (∀ s ∈ simplexBoundary n, smp s ∈ U) ∧
        smp (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) = a.val then
      (liftHomotopy U a n hpi hs ⟨smp, hb.1⟩ hb.2).toContinuousMap
    else stationarySimplexHomotopy n smp

theorem homotopy_zero (smp : C(Simplex n, X)) (s : Simplex n) :
    homotopy U a n hpi hs smp (0, s) = smp s := by
  classical
  unfold homotopy
  split
  · rfl
  · split
    · rename_i hb
      exact (liftHomotopy U a n hpi hs ⟨smp, hb.1⟩ hb.2).apply_zero s
    · rfl

theorem homotopy_of_mem (smp : C(Simplex n, X)) (hU : ∀ s, smp s ∈ U) :
    homotopy U a n hpi hs smp = stationarySimplexHomotopy n smp := by
  classical
  simp only [homotopy, if_pos hU]

theorem homotopy_mem (smp : C(Simplex n, X)) (hU : ∀ s, smp s ∈ U)
    (p : I × Simplex n) : homotopy U a n hpi hs smp p ∈ U := by
  rw [homotopy_of_mem U a n hpi hs smp hU]
  exact hU p.2

theorem homotopy_boundary (smp : C(Simplex n, X)) (t : I) (s : Simplex n)
    (hU : s ∈ simplexBoundary n) : homotopy U a n hpi hs smp (t, s) = smp s := by
  classical
  unfold homotopy
  split
  · rfl
  · split
    · rename_i hb
      exact (liftHomotopy U a n hpi hs ⟨smp, hb.1⟩ hb.2).eq_fst t hU
    · rfl

theorem homotopy_one_mem (smp : C(Simplex n, X))
    (hU : ∀ s ∈ simplexBoundary n, smp s ∈ U)
    (hv : smp (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))) = a.val) (s : Simplex n) :
    homotopy U a n hpi hs smp (1, s) ∈ U := by
  classical
  by_cases ht : ∀ t, smp t ∈ U
  · rw [homotopy_of_mem U a n hpi hs smp ht]
    exact ht s
  · rw [homotopy, if_neg ht, dif_pos ⟨hU, hv⟩]
    change liftHomotopy U a n hpi hs ⟨smp, hU⟩ hv (1, s) ∈ U
    rw [(liftHomotopy U a n hpi hs ⟨smp, hU⟩ hv).apply_one]
    exact (liftedSimplex U a n hpi hs ⟨smp, hU⟩ hv s).property

end AtDegree

theorem homotopy_face (n : ℕ)
    (hpi : ∀ k, 0 < k → k < n + 1 → ∀ p : Fiber U a, Subsingleton (π_ k (Fiber U a) p))
    (hs : ∀ b : U, Function.Surjective
      (HigherHomotopy.map (N := Fin (n + 1)) (subtypeInclusion U) (y := b) rfl)) :
    FaceCompatibleHomotopies n (stationarySimplexHomotopy n) (homotopy U a (n + 1) hpi hs) := by
  intro smp i
  ext p
  exact homotopy_boundary U a (n + 1) hpi hs smp p.1 (simplexFace n i p.2)
    (simplexFace_mem_boundary n i p.2)

end NoExoticSixSphere.RelativeSimplexFiberCompression
