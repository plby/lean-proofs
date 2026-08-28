import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionRetraction
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionGluing

/-!
# Homotopy extension for the actual boundary of a standard simplex

Compatible bottom and boundary data extend to the full cylinder by
composition with an explicit continuous radial retraction. This proves
the extension property for every dimension and every target space;
neither a cofibration nor a homotopy extension theorem is an input.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- Extend the prescribed bottom map and a compatible boundary homotopy
to a jointly continuous map on the entire simplex cylinder. -/
def extendBoundaryHomotopy (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(unitInterval × Simplex n, X) :=
  (gluedBoundaryMap f h h0).comp (cylinderRetraction n)

@[simp] theorem extendBoundaryHomotopy_bottom (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (s : Simplex n) :
    extendBoundaryHomotopy f h h0 (0, s) = f s := by
  change gluedBoundaryMap f h h0 (cylinderRetraction n (0, s)) = f s
  rw [cylinderRetraction_bottom, gluedBoundaryMap_bottomInclusion]

@[simp] theorem extendBoundaryHomotopy_side (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval) (s : SimplexBoundary n) :
    extendBoundaryHomotopy f h h0 (t, s.val) = h (t, s) := by
  change gluedBoundaryMap f h h0 (cylinderRetraction n (t, s.val)) = h (t, s)
  rw [cylinderRetraction_side, gluedBoundaryMap_sideInclusion]

theorem extendBoundaryHomotopy_boundary (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval) (s : Simplex n)
    (hs : s ∈ simplexBoundary n) :
    extendBoundaryHomotopy f h h0 (t, s) = h (t, ⟨s, hs⟩) :=
  extendBoundaryHomotopy_side f h h0 t ⟨s, hs⟩

/-- The extension has the prescribed values on each literal face map. -/
theorem extendBoundaryHomotopy_face (f : C(Simplex (n + 1), X))
    (h : C(unitInterval × SimplexBoundary (n + 1), X))
    (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval) (i : Fin (n + 2))
    (s : Simplex n) :
    extendBoundaryHomotopy f h h0 (t, simplexFace n i s) =
      h (t, ⟨simplexFace n i s, simplexFace_mem_boundary n i s⟩) :=
  extendBoundaryHomotopy_boundary f h h0 t _ (simplexFace_mem_boundary n i s)

/-- The endpoint of the extended homotopy. -/
def boundaryExtensionEndpoint (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(Simplex n, X) :=
  (extendBoundaryHomotopy f h h0).comp
    ⟨fun s => (1, s), continuous_const.prodMk continuous_id⟩

/-- The same extension as a native continuous-map homotopy. -/
def extendedBoundaryHomotopy (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) :
    ContinuousMap.Homotopy f (boundaryExtensionEndpoint f h h0) where
  toContinuousMap := extendBoundaryHomotopy f h h0
  map_zero_left := extendBoundaryHomotopy_bottom f h h0
  map_one_left _ := rfl

@[simp] theorem extendedBoundaryHomotopy_apply (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (u : unitInterval × Simplex n) :
    extendedBoundaryHomotopy f h h0 u = extendBoundaryHomotopy f h h0 u := rfl

@[simp] theorem boundaryExtensionEndpoint_boundary (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (s : SimplexBoundary n) :
    boundaryExtensionEndpoint f h h0 s.val = h (1, s) :=
  extendBoundaryHomotopy_side f h h0 1 s

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
