import Wikipedia.NoExoticSixSphere.RelativeThreeSimplexLifting

/-!
# Boundary-fixed compression of actual relative tetrahedra

The family is total on singular tetrahedra. It is stationary on simplices
already in the subspace and on inputs not satisfying the relative based
vertex conditions. Every boundary point is fixed in all cases. On the
required relative tetrahedra, its endpoint lies in the actual subspace.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeThreeSimplexCompression

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  [SimplyConnectedSpace (Fiber U a)]
  [Subsingleton (π_ 2 (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a))]
  (hπ : ∀ b : U, Function.Surjective
    (HigherHomotopy.map (N := Fin 3) (subtypeInclusion U) (y := b) rfl))

def liftedSimplex (smp : RelativeSimplex U 3)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val) : C(Simplex 3, U) :=
  (RelativeThreeSimplexLifting.exists_lift U a hπ smp (stdSimplex.vertex 0) hv).choose

def liftHomotopy (smp : RelativeSimplex U 3)
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val) :
    smp.val.HomotopyRel ((subtypeInclusion U).comp (liftedSimplex U a hπ smp hv))
      (simplexBoundary 3) :=
  Classical.choice
    (RelativeThreeSimplexLifting.exists_lift U a hπ smp (stdSimplex.vertex 0) hv).choose_spec.2

def homotopy (smp : C(Simplex 3, X)) : C(I × Simplex 3, X) := by
  classical
  exact if ∀ s, smp s ∈ U then stationarySimplexHomotopy 3 smp
    else if hb : (∀ s ∈ simplexBoundary 3, smp s ∈ U) ∧
        smp (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val then
      (liftHomotopy U a hπ ⟨smp, hb.1⟩ hb.2).toContinuousMap
    else stationarySimplexHomotopy 3 smp

theorem homotopy_zero (smp : C(Simplex 3, X)) (s : Simplex 3) :
    homotopy U a hπ smp (0, s) = smp s := by
  classical
  unfold homotopy
  split
  · rfl
  · split
    · rename_i hb
      exact (liftHomotopy U a hπ ⟨smp, hb.1⟩ hb.2).apply_zero s
    · rfl

theorem homotopy_of_mem (smp : C(Simplex 3, X)) (hs : ∀ s, smp s ∈ U) :
    homotopy U a hπ smp = stationarySimplexHomotopy 3 smp := by
  classical
  simp only [homotopy, if_pos hs]

theorem homotopy_mem (smp : C(Simplex 3, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex 3) : homotopy U a hπ smp p ∈ U := by
  rw [homotopy_of_mem U a hπ smp hs]
  exact hs p.2

theorem homotopy_boundary (smp : C(Simplex 3, X)) (t : I) (s : Simplex 3)
    (hs : s ∈ simplexBoundary 3) : homotopy U a hπ smp (t, s) = smp s := by
  classical
  unfold homotopy
  split
  · rfl
  · split
    · rename_i hb
      exact (liftHomotopy U a hπ ⟨smp, hb.1⟩ hb.2).eq_fst t hs
    · rfl

theorem homotopy_one_mem (smp : C(Simplex 3, X))
    (hU : ∀ s ∈ simplexBoundary 3, smp s ∈ U)
    (hv : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val) (s : Simplex 3) :
    homotopy U a hπ smp (1, s) ∈ U := by
  classical
  by_cases hs : ∀ t, smp t ∈ U
  · rw [homotopy_of_mem U a hπ smp hs]
    exact hs s
  · rw [homotopy, if_neg hs, dif_pos ⟨hU, hv⟩]
    change liftHomotopy U a hπ ⟨smp, hU⟩ hv (1, s) ∈ U
    rw [(liftHomotopy U a hπ ⟨smp, hU⟩ hv).apply_one]
    exact (liftedSimplex U a hπ ⟨smp, hU⟩ hv s).property

theorem homotopy_face :
    FaceCompatibleHomotopies 2 (stationarySimplexHomotopy 2) (homotopy U a hπ) := by
  intro smp i
  ext p
  exact homotopy_boundary U a hπ smp p.1 (simplexFace 2 i p.2)
    (simplexFace_mem_boundary 2 i p.2)

end NoExoticSixSphere.RelativeThreeSimplexCompression
