import Wikipedia.HopfProblem.FirstHurewiczSimplex

/-!
# Face identities for actual singular tetrahedra

The coface relation is transported through the actual topological simplex
functor. Its six low-dimensional instances identify each edge in the two
faces of a tetrahedron that contain it.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle

open CategoryTheory Simplicial FirstHurewicz

/-- The genuine topological face maps satisfy the coface composition identity. -/
theorem simplexFace_comp {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    (simplexFace (n + 1) j.succ).comp (simplexFace n i) =
      (simplexFace (n + 1) i.castSucc).comp (simplexFace n j) := by
  have hf := congrArg
    (fun f : ⦋n⦌ ⟶ ⦋n + 2⦌ => (SimplexCategory.toTop₀.map f).hom)
    (SimplexCategory.δ_comp_δ h)
  have hl := congrArg
    (fun f : SimplexCategory.toTop₀.obj ⦋n⦌ ⟶ SimplexCategory.toTop₀.obj ⦋n + 2⦌ => f.hom)
    (SimplexCategory.toTop₀.map_comp (SimplexCategory.δ i) (SimplexCategory.δ j.succ))
  have hr := congrArg
    (fun f : SimplexCategory.toTop₀.obj ⦋n⦌ ⟶ SimplexCategory.toTop₀.obj ⦋n + 2⦌ => f.hom)
    (SimplexCategory.toTop₀.map_comp (SimplexCategory.δ j) (SimplexCategory.δ i.castSucc))
  exact hl.symm.trans (hf.trans hr)

variable {X : Type*} [TopologicalSpace X]

/-- The corresponding faces of every actual continuous singular simplex agree. -/
theorem singularSimplex_face_face {n : ℕ} (σ : C(Simplex (n + 2), X))
    {i j : Fin (n + 2)} (h : i ≤ j) :
    (σ.comp (simplexFace (n + 1) j.succ)).comp (simplexFace n i) =
      (σ.comp (simplexFace (n + 1) i.castSucc)).comp (simplexFace n j) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(Simplex n, Simplex (n + 2)) => σ.comp f) (simplexFace_comp h)

/-- The edge `01`, viewed in faces `2` and `3`. -/
theorem tetrahedron_edge01 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 2)).comp (simplexFace 1 2) =
      (σ.comp (simplexFace 2 3)).comp (simplexFace 1 2) :=
  (singularSimplex_face_face σ (i := 2) (j := 2) (by decide)).symm

/-- The edge `02`, viewed in faces `1` and `3`. -/
theorem tetrahedron_edge02 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 1)).comp (simplexFace 1 2) =
      (σ.comp (simplexFace 2 3)).comp (simplexFace 1 1) :=
  (singularSimplex_face_face σ (i := 1) (j := 2) (by decide)).symm

/-- The edge `03`, viewed in faces `1` and `2`. -/
theorem tetrahedron_edge03 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 1)).comp (simplexFace 1 1) =
      (σ.comp (simplexFace 2 2)).comp (simplexFace 1 1) :=
  (singularSimplex_face_face σ (i := 1) (j := 1) (by decide)).symm

/-- The edge `12`, viewed in faces `0` and `3`. -/
theorem tetrahedron_edge12 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 0)).comp (simplexFace 1 2) =
      (σ.comp (simplexFace 2 3)).comp (simplexFace 1 0) :=
  (singularSimplex_face_face σ (i := 0) (j := 2) (by decide)).symm

/-- The edge `13`, viewed in faces `2` and `0`. -/
theorem tetrahedron_edge13 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 2)).comp (simplexFace 1 0) =
      (σ.comp (simplexFace 2 0)).comp (simplexFace 1 1) :=
  singularSimplex_face_face σ (i := 0) (j := 1) (by decide)

/-- The edge `23`, viewed in faces `0` and `1`. -/
theorem tetrahedron_edge23 (σ : C(Simplex 3, X)) :
    (σ.comp (simplexFace 2 0)).comp (simplexFace 1 0) =
      (σ.comp (simplexFace 2 1)).comp (simplexFace 1 0) :=
  (singularSimplex_face_face σ (i := 0) (j := 0) (by decide)).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCocycle
