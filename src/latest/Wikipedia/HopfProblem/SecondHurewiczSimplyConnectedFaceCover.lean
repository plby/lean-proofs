import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# The actual finite face cover of a simplex cylinder

The face maps give a continuous surjection from a finite disjoint union of
compact simplex cylinders onto the boundary cylinder. Since that boundary
cylinder is Hausdorff, this is a quotient map. The eventual target of a
pasted map need not satisfy any separation assumption.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- An actual barycentric face, regarded as a map into the boundary subspace. -/
def simplexFaceBoundary (n : ℕ) (i : Fin (n + 2)) :
    C(Simplex n, SimplexBoundary (n + 1)) where
  toFun s := ⟨simplexFace n i s, simplexFace_mem_boundary n i s⟩
  continuous_toFun := (simplexFace n i).continuous.subtype_mk _

@[simp] theorem simplexFaceBoundary_val (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    (simplexFaceBoundary n i s).val = simplexFace n i s := rfl

/-- The closed coordinate face inside the actual boundary subspace. -/
def boundaryFace (n : ℕ) (i : Fin (n + 2)) : Set (SimplexBoundary (n + 1)) :=
  {s | s.val i = 0}

theorem isClosed_boundaryFace (n : ℕ) (i : Fin (n + 2)) :
    IsClosed (boundaryFace n i) :=
  isClosed_eq
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
    continuous_const

theorem iUnion_boundaryFace (n : ℕ) :
    (⋃ i : Fin (n + 2), boundaryFace n i) = Set.univ := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact s.property

/-- Every boundary point lies on an actual face with its own simplex coordinates. -/
theorem simplexBoundary_exists_face (n : ℕ) (s : SimplexBoundary (n + 1)) :
    ∃ i : Fin (n + 2), ∃ t : Simplex n, simplexFaceBoundary n i t = s := by
  obtain ⟨i, hi⟩ := s.property
  have hmem : s.val ∈ Set.range (simplexFace n i) := by
    rw [simplexFace_range]
    exact hi
  obtain ⟨t, ht⟩ := hmem
  exact ⟨i, t, Subtype.ext ht⟩

theorem simplexFaceBoundary_range (n : ℕ) (i : Fin (n + 2)) :
    Set.range (simplexFaceBoundary n i) = boundaryFace n i := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact simplexFace_apply_self n i t
  · intro hs
    have hmem : s.val ∈ Set.range (simplexFace n i) := by
      rw [simplexFace_range]
      exact hs
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, Subtype.ext ht⟩

/-- Inclusion of one actual face cylinder into the whole boundary cylinder. -/
def simplexFaceCylinder (n : ℕ) (i : Fin (n + 2)) :
    C(I × Simplex n, I × SimplexBoundary (n + 1)) :=
  (ContinuousMap.id I).prodMap (simplexFaceBoundary n i)

@[simp] theorem simplexFaceCylinder_apply (n : ℕ) (i : Fin (n + 2))
    (r : I) (s : Simplex n) :
    simplexFaceCylinder n i (r, s) = (r, simplexFaceBoundary n i s) := rfl

/-- The finite disjoint union of face cylinders maps onto the boundary cylinder. -/
def simplexFaceCover (n : ℕ) :
    C((Σ _i : Fin (n + 2), I × Simplex n), I × SimplexBoundary (n + 1)) where
  toFun a := simplexFaceCylinder n a.fst a.snd
  continuous_toFun := continuous_sigma fun i => (simplexFaceCylinder n i).continuous

@[simp] theorem simplexFaceCover_apply (n : ℕ) (i : Fin (n + 2))
    (r : I) (s : Simplex n) :
    simplexFaceCover n ⟨i, (r, s)⟩ = (r, simplexFaceBoundary n i s) := rfl

theorem simplexFaceCover_surjective (n : ℕ) :
    Function.Surjective (simplexFaceCover n) := by
  rintro ⟨r, s⟩
  obtain ⟨i, t, rfl⟩ := simplexBoundary_exists_face n s
  exact ⟨⟨i, (r, t)⟩, rfl⟩

/-- The genuine quotient-map property of the finite face cover. -/
theorem simplexFaceCover_isQuotientMap (n : ℕ) :
    IsQuotientMap (simplexFaceCover n) :=
  IsQuotientMap.of_surjective_continuous
    (simplexFaceCover_surjective n) (simplexFaceCover n).continuous

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
