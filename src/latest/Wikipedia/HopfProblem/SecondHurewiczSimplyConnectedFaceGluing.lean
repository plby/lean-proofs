import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceCover

/-!
# Pasting compatible homotopies on all simplex faces

A family of actual continuous face-cylinder maps which agrees at every
geometric overlap descends along the proved finite face quotient map. The
result restricts to the given map on each face, with exact endpoint formulas.
No separation assumption on the target is required.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- Agreement whenever two actual face points represent the same boundary point. -/
def FaceCompatible (F : Fin (n + 2) → C(I × Simplex n, X)) : Prop :=
  ∀ (i j : Fin (n + 2)) (s t : Simplex n),
    simplexFace n i s = simplexFace n j t → ∀ r : I, F i (r, s) = F j (r, t)

/-- The continuous map on the disjoint union determined by the face family. -/
def faceFamilyMap (F : Fin (n + 2) → C(I × Simplex n, X)) :
    C((Σ _i : Fin (n + 2), I × Simplex n), X) where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun i => (F i).continuous

@[simp] theorem faceFamilyMap_apply (F : Fin (n + 2) → C(I × Simplex n, X))
    (i : Fin (n + 2)) (r : I) (s : Simplex n) :
    faceFamilyMap F ⟨i, (r, s)⟩ = F i (r, s) := rfl

theorem faceFamilyMap_factorsThrough (F : Fin (n + 2) → C(I × Simplex n, X))
    (hF : FaceCompatible F) :
    Function.FactorsThrough (faceFamilyMap F) (simplexFaceCover n) := by
  rintro ⟨i, r, s⟩ ⟨j, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs : simplexFace n i s = simplexFace n j t :=
    congrArg (fun u : I × SimplexBoundary (n + 1) => u.2.val) h
  subst q
  exact hF i j s t hs r

/-- The actual continuous homotopy on the full boundary obtained by face pasting. -/
def glueFaceHomotopies (F : Fin (n + 2) → C(I × Simplex n, X))
    (hF : FaceCompatible F) : C(I × SimplexBoundary (n + 1), X) :=
  (simplexFaceCover_isQuotientMap n).lift (faceFamilyMap F)
    (faceFamilyMap_factorsThrough F hF)

/-- The pasted map is exactly the prescribed map on every actual face. -/
@[simp] theorem glueFaceHomotopies_face
    (F : Fin (n + 2) → C(I × Simplex n, X)) (hF : FaceCompatible F)
    (i : Fin (n + 2)) (r : I) (s : Simplex n) :
    glueFaceHomotopies F hF (r, simplexFaceBoundary n i s) = F i (r, s) := by
  exact congrArg (fun f => f ⟨i, (r, s)⟩)
    ((simplexFaceCover_isQuotientMap n).lift_comp (faceFamilyMap F)
      (faceFamilyMap_factorsThrough F hF))

theorem glueFaceHomotopies_comp_faceCylinder
    (F : Fin (n + 2) → C(I × Simplex n, X)) (hF : FaceCompatible F)
    (i : Fin (n + 2)) :
    (glueFaceHomotopies F hF).comp (simplexFaceCylinder n i) = F i := by
  ext u
  exact glueFaceHomotopies_face F hF i u.1 u.2

/-- A common value on all faces at one time is the value of the pasted map. -/
theorem glueFaceHomotopies_time
    (F : Fin (n + 2) → C(I × Simplex n, X)) (hF : FaceCompatible F)
    (r : I) (g : Simplex (n + 1) → X)
    (h : ∀ (i : Fin (n + 2)) (s : Simplex n), F i (r, s) = g (simplexFace n i s))
    (b : SimplexBoundary (n + 1)) :
    glueFaceHomotopies F hF (r, b) = g b.val := by
  obtain ⟨i, s, rfl⟩ := simplexBoundary_exists_face n b
  exact (glueFaceHomotopies_face F hF i r s).trans (h i s)

/-- In particular, the pasted homotopy has the prescribed bottom map. -/
theorem glueFaceHomotopies_zero
    (F : Fin (n + 2) → C(I × Simplex n, X)) (hF : FaceCompatible F)
    (g : C(Simplex (n + 1), X))
    (h : ∀ (i : Fin (n + 2)) (s : Simplex n), F i (0, s) = g (simplexFace n i s))
    (b : SimplexBoundary (n + 1)) :
    glueFaceHomotopies F hF (0, b) = g b.val :=
  glueFaceHomotopies_time F hF 0 g h b

/-- The same endpoint statement at the top of the cylinder. -/
theorem glueFaceHomotopies_one
    (F : Fin (n + 2) → C(I × Simplex n, X)) (hF : FaceCompatible F)
    (g : C(Simplex (n + 1), X))
    (h : ∀ (i : Fin (n + 2)) (s : Simplex n), F i (1, s) = g (simplexFace n i s))
    (b : SimplexBoundary (n + 1)) :
    glueFaceHomotopies F hF (1, b) = g b.val :=
  glueFaceHomotopies_time F hF 1 g h b

/-- A continuous map with the given face restrictions is the pasted map. -/
theorem glueFaceHomotopies_unique
    (F : Fin (n + 2) → C(I × Simplex n, X)) (hF : FaceCompatible F)
    (G : C(I × SimplexBoundary (n + 1), X))
    (hG : ∀ (i : Fin (n + 2)) (r : I) (s : Simplex n),
      G (r, simplexFaceBoundary n i s) = F i (r, s)) :
    G = glueFaceHomotopies F hF := by
  ext u
  rcases u with ⟨r, b⟩
  obtain ⟨i, s, rfl⟩ := simplexBoundary_exists_face n b
  exact (hG i r s).trans (glueFaceHomotopies_face F hF i r s).symm

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
