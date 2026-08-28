import Wikipedia.NoExoticSixSphere.BasedSimplexLifting
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeBasic

/-!
# Boundary-fixed compression of based simplices into an actual subspace

Native homotopy surjectivity supplies actual lifts of based simplices.
The chosen homotopies are made into a total family by leaving all other
inputs stationary. In particular, simplices already in the subspace
remain literally stationary. Every boundary point is fixed in all cases.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris HigherHurewicz
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.BasedSimplexSubspaceCompression

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def liftedSimplex (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (τ : BasedSimplex n a.val) : BasedSimplex n a :=
  (BasedSimplexLifting.exists_lift n (subtypeInclusion U) a hπ τ).choose

def liftHomotopy (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (τ : BasedSimplex n a.val) :
    τ.val.HomotopyRel ((subtypeInclusion U).comp (liftedSimplex U a n hπ τ).val)
      (simplexBoundary n) :=
  Classical.choice (BasedSimplexLifting.exists_lift n (subtypeInclusion U) a hπ τ).choose_spec

def homotopy (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (smp : C(Simplex n, X)) : C(I × Simplex n, X) := by
  classical
  exact if ∀ s, smp s ∈ U then stationarySimplexHomotopy n smp
    else if hb : ∀ s ∈ simplexBoundary n, smp s = a.val then
      (liftHomotopy U a n hπ ⟨smp, hb⟩).toContinuousMap
    else stationarySimplexHomotopy n smp

theorem homotopy_zero (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (smp : C(Simplex n, X)) (s : Simplex n) : homotopy U a n hπ smp (0, s) = smp s := by
  classical
  unfold homotopy
  split
  · rfl
  · split
    · rename_i hb
      exact (liftHomotopy U a n hπ ⟨smp, hb⟩).apply_zero s
    · rfl

theorem homotopy_of_mem (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) :
    homotopy U a n hπ smp = stationarySimplexHomotopy n smp := by
  classical
  simp only [homotopy, if_pos hs]

theorem homotopy_mem (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (smp : C(Simplex n, X)) (hs : ∀ s, smp s ∈ U) (p : I × Simplex n) :
    homotopy U a n hπ smp p ∈ U := by
  rw [homotopy_of_mem U a n hπ smp hs]
  exact hs p.2

theorem homotopy_boundary (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (smp : C(Simplex n, X)) (t : I) (s : Simplex n) (hs : s ∈ simplexBoundary n) :
    homotopy U a n hπ smp (t, s) = smp s := by
  classical
  unfold homotopy
  split
  · rfl
  · split
    · rename_i hb
      exact (liftHomotopy U a n hπ ⟨smp, hb⟩).eq_fst t hs
    · rfl

theorem homotopy_one_mem (n : ℕ)
    (hπ : Function.Surjective (HigherHomotopy.map (N := Fin n) (subtypeInclusion U) (y := a) rfl))
    (smp : C(Simplex n, X)) (hb : ∀ s ∈ simplexBoundary n, smp s = a.val) (s : Simplex n) :
    homotopy U a n hπ smp (1, s) ∈ U := by
  classical
  by_cases hs : ∀ s, smp s ∈ U
  · rw [homotopy_of_mem U a n hπ smp hs]
    exact hs s
  · rw [homotopy, if_neg hs, dif_pos hb]
    change liftHomotopy U a n hπ ⟨smp, hb⟩ (1, s) ∈ U
    rw [(liftHomotopy U a n hπ ⟨smp, hb⟩).apply_one]
    exact (liftedSimplex U a n hπ ⟨smp, hb⟩).val s |>.property

theorem homotopy_face (n : ℕ)
    (hπ : Function.Surjective
      (HigherHomotopy.map (N := Fin (n + 1)) (subtypeInclusion U) (y := a) rfl)) :
    FaceCompatibleHomotopies n (stationarySimplexHomotopy n) (homotopy U a (n + 1) hπ) := by
  intro smp i
  ext p
  exact homotopy_boundary U a (n + 1) hπ smp p.1 (simplexFace n i p.2)
    (simplexFace_mem_boundary n i p.2)

end NoExoticSixSphere.BasedSimplexSubspaceCompression
