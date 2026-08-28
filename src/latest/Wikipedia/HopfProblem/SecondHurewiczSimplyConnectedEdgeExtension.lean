import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeBasic

/-!
# Extending coherent singular-simplex homotopies by one dimension

The coface identities make the already constructed face homotopies
agree on their whole geometric overlaps. The proved simplex-cylinder
retraction then extends them, preserving their exact face restrictions.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- Coherent simplex homotopies agree on every overlap in the boundary of
the next simplex. -/
theorem nextFaceHomotopies_compatible
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularSimplex X (n + 2)) :
    FaceCompatible (fun i => H' (smp.comp (simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij t s
  have hi := congrArg (fun F : C(I × Simplex n, X) => F (t, s))
    (h (smp.comp (simplexFace (n + 1) j.succ)) i)
  have hj := congrArg (fun F : C(I × Simplex n, X) => F (t, s))
    (h (smp.comp (simplexFace (n + 1) i.castSucc)) j)
  change H' (smp.comp (simplexFace (n + 1) j.succ)) (t, simplexFace n i s) =
    H ((smp.comp (simplexFace (n + 1) j.succ)).comp (simplexFace n i)) (t, s) at hi
  change H' (smp.comp (simplexFace (n + 1) i.castSucc)) (t, simplexFace n j s) =
    H ((smp.comp (simplexFace (n + 1) i.castSucc)).comp (simplexFace n j)) (t, s) at hj
  rw [hi, hj]
  change H (smp.comp ((simplexFace (n + 1) j.succ).comp (simplexFace n i))) (t, s) =
    H (smp.comp ((simplexFace (n + 1) i.castSucc).comp (simplexFace n j))) (t, s)
  rw [PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij]

/-- The prescribed actual boundary homotopy in the next dimension. -/
def coherentFaceBoundaryHomotopy
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularSimplex X (n + 2)) :
    C(I × SimplexBoundary (n + 2), X) :=
  glueFaceHomotopies (fun i => H' (smp.comp (simplexFace (n + 1) i)))
    (nextFaceHomotopies_compatible H H' h smp)

@[simp] theorem coherentFaceBoundaryHomotopy_face
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularSimplex X (n + 2))
    (i : Fin (n + 3)) (t : I) (s : Simplex (n + 1)) :
    coherentFaceBoundaryHomotopy H H' h smp
      (t, simplexFaceBoundary (n + 1) i s) =
      H' (smp.comp (simplexFace (n + 1) i)) (t, s) :=
  glueFaceHomotopies_face _ _ i t s

theorem coherentFaceBoundaryHomotopy_zero
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularSimplex X (n + 2)) (b : SimplexBoundary (n + 2)) :
    coherentFaceBoundaryHomotopy H H' h smp (0, b) = smp b.val :=
  glueFaceHomotopies_zero _ _ smp (fun i s => h₀ (smp.comp (simplexFace (n + 1) i)) s) b

/-- Extend the given coherent family to genuine homotopies of the next
singular simplices. No extension hypothesis is an input. -/
def extendCoherentSimplexHomotopy
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularSimplex X (n + 2)) : C(I × Simplex (n + 2), X) :=
  extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
    (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)

@[simp] theorem extendCoherentSimplexHomotopy_zero
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularSimplex X (n + 2)) (s : Simplex (n + 2)) :
    extendCoherentSimplexHomotopy H H' h h₀ smp (0, s) = smp s :=
  extendBoundaryHomotopy_bottom _ _ _ s

/-- Literal face compatibility survives the genuine extension. -/
theorem extendCoherentSimplexHomotopy_face
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s) :
    FaceCompatibleHomotopies (n + 1) H' (extendCoherentSimplexHomotopy H H' h h₀) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
    (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp) (t, simplexFace (n + 1) i s) = _
  rw [extendBoundaryHomotopy_face]
  exact coherentFaceBoundaryHomotopy_face H H' h smp i t s

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
