import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGluing
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometryIntersection

/-!
# Testing face compatibility by the usual coface identities

For positive-dimensional faces, it suffices to check the usual ordered
coface identities on their common codimension-two faces. This implies
agreement on every geometric overlap, not merely on a list of vertices.
For zero-dimensional faces there are no nontrivial overlaps.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- The usual ordered coface compatibility for a family of face homotopies. -/
def CofaceCompatible (F : Fin (n + 3) → C(I × Simplex (n + 1), X)) : Prop :=
  ∀ (i j : Fin (n + 2)), i ≤ j → ∀ (r : I) (u : Simplex n),
    F j.succ (r, simplexFace n i u) = F i.castSucc (r, simplexFace n j u)

private theorem faceCompatible_of_cofaceCompatible_lt
    (F : Fin (n + 3) → C(I × Simplex (n + 1), X)) (hF : CofaceCompatible F)
    {a b : Fin (n + 3)} (hab : a < b) {s t : Simplex (n + 1)}
    (hst : simplexFace (n + 1) a s = simplexFace (n + 1) b t) (r : I) :
    F a (r, s) = F b (r, t) := by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hab)
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (Fin.ne_zero_of_lt hab)
  have hij : i ≤ j := Fin.castSucc_lt_succ_iff.mp hab
  obtain ⟨u, hu, hv⟩ := simplexFace_intersection hij hst.symm
  rw [← hu, ← hv]
  exact (hF i j hij r u).symm

/-- Ordered coface agreement suffices for agreement on all geometric overlaps. -/
theorem faceCompatible_of_cofaceCompatible
    (F : Fin (n + 3) → C(I × Simplex (n + 1), X))
    (hF : CofaceCompatible F) : FaceCompatible F := by
  intro a b s t hst r
  rcases lt_trichotomy a b with hab | hab | hba
  · exact faceCompatible_of_cofaceCompatible_lt F hF hab hst r
  · subst b
    exact congrArg (fun u => F a (r, u)) (simplexFace_injective (n + 1) a hst)
  · exact (faceCompatible_of_cofaceCompatible_lt F hF hba hst.symm r).symm

/-- Geometric compatibility in particular includes every usual coface identity. -/
theorem cofaceCompatible_of_faceCompatible
    (F : Fin (n + 3) → C(I × Simplex (n + 1), X))
    (hF : FaceCompatible F) : CofaceCompatible F := by
  intro i j hij r u
  exact hF j.succ i.castSucc (simplexFace n i u) (simplexFace n j u)
    (DFunLike.congr_fun (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij) u) r

theorem faceCompatible_iff_cofaceCompatible
    (F : Fin (n + 3) → C(I × Simplex (n + 1), X)) :
    FaceCompatible F ↔ CofaceCompatible F :=
  ⟨cofaceCompatible_of_faceCompatible F, faceCompatible_of_cofaceCompatible F⟩

/-- The two vertex faces of an interval have no geometric overlap. -/
theorem faceCompatible_zero (F : Fin 2 → C(I × Simplex 0, X)) :
    FaceCompatible F := by
  intro i j s t hst r
  have hs : s = t := by rw [simplexZero_eq_vertex s, simplexZero_eq_vertex t]
  subst t
  fin_cases i <;> fin_cases j
  · rfl
  · have h : (1 : Fin 2) = 0 := stdSimplex.vertex_injective
      ((simplexFace_zero_zero s).symm.trans (hst.trans (simplexFace_zero_one s)))
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) h)
  · have h : (0 : Fin 2) = 1 := stdSimplex.vertex_injective
      ((simplexFace_zero_one s).symm.trans (hst.trans (simplexFace_zero_zero s)))
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h)
  · rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
