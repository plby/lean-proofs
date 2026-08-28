import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedEdgeExtension

/-!
# Constant preservation by the genuine simplex homotopy extensions

The bottom-and-side pasting and the explicit cylinder retraction preserve
constant data literally. Consequently a coherent extension fixes the
constant simplex whenever its already constructed face homotopies do.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]

theorem gluedBoundaryMap_constant_value {n : ℕ} (f : C(Simplex n, X))
    (g : C(I × SimplexBoundary n, X)) (h₀ : ∀ s, g (0, s) = f s.val)
    (x : X) (hf : ∀ s, f s = x) (hg : ∀ u, g u = x) (u : ↥(bottomOrSide n)) :
    gluedBoundaryMap f g h₀ u = x := by
  rcases u.property with hb | hs
  · have hu : u = bottomInclusion n u.val.2 := by
      apply Subtype.ext
      exact Prod.ext hb rfl
    exact (congrArg (gluedBoundaryMap f g h₀) hu).trans
      ((gluedBoundaryMap_bottomInclusion f g h₀ _).trans (hf _))
  · have hu : u = sideInclusion n (u.val.1, ⟨u.val.2, hs⟩) := by
      apply Subtype.ext
      rfl
    exact (congrArg (gluedBoundaryMap f g h₀) hu).trans
      ((gluedBoundaryMap_sideInclusion f g h₀ _).trans (hg _))

@[simp] theorem gluedBoundaryMap_const (n : ℕ) (x : X) :
    gluedBoundaryMap (ContinuousMap.const (Simplex n) x)
      (ContinuousMap.const (I × SimplexBoundary n) x) (fun _ => rfl) =
      ContinuousMap.const (↥(bottomOrSide n)) x := by
  ext u
  exact gluedBoundaryMap_constant_value _ _ _ x (fun _ => rfl) (fun _ => rfl) u

/-- The actual radial extension of constant data is the literal constant map. -/
@[simp] theorem extendBoundaryHomotopy_const (n : ℕ) (x : X) :
    extendBoundaryHomotopy (ContinuousMap.const (Simplex n) x)
      (ContinuousMap.const (I × SimplexBoundary n) x) (fun _ => rfl) =
      ContinuousMap.const (I × Simplex n) x := by
  unfold extendBoundaryHomotopy
  rw [gluedBoundaryMap_const]
  rfl

variable {n : ℕ}

theorem coherentFaceBoundaryHomotopy_const
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (x : X)
    (hc : H' (ContinuousMap.const (Simplex (n + 1)) x) =
      ContinuousMap.const (I × Simplex (n + 1)) x) :
    coherentFaceBoundaryHomotopy H H' h (ContinuousMap.const (Simplex (n + 2)) x) =
      ContinuousMap.const (I × SimplexBoundary (n + 2)) x := by
  unfold coherentFaceBoundaryHomotopy
  apply (glueFaceHomotopies_unique _ _ (ContinuousMap.const _ x) ?_).symm
  intro i r s
  change x = H' (ContinuousMap.const (Simplex (n + 1)) x) (r, s)
  rw [hc]
  rfl

/-- The coherent extension has no movement at a constant simplex if its
face data have no movement there. -/
theorem extendCoherentSimplexHomotopy_const
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s) (x : X)
    (hc : H' (ContinuousMap.const (Simplex (n + 1)) x) =
      ContinuousMap.const (I × Simplex (n + 1)) x) :
    extendCoherentSimplexHomotopy H H' h h₀ (ContinuousMap.const (Simplex (n + 2)) x) =
      ContinuousMap.const (I × Simplex (n + 2)) x := by
  unfold extendCoherentSimplexHomotopy
  ext u
  change gluedBoundaryMap (ContinuousMap.const (Simplex (n + 2)) x)
    (coherentFaceBoundaryHomotopy H H' h (ContinuousMap.const (Simplex (n + 2)) x))
    (coherentFaceBoundaryHomotopy_zero H H' h h₀ (ContinuousMap.const (Simplex (n + 2)) x))
    (cylinderRetraction (n + 2) u) = x
  apply gluedBoundaryMap_constant_value _ _ _ x (fun _ => rfl)
  intro v
  exact congrArg (fun F : C(I × SimplexBoundary (n + 2), X) => F v)
    (coherentFaceBoundaryHomotopy_const H H' h x hc)

end Wikipedia.HopfProblem.ThirdHurewicz
