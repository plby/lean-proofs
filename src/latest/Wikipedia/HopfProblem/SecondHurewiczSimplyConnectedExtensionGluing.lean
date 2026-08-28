import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# Pasting a simplex map and a boundary homotopy

The bottom and side of the actual simplex cylinder are closed subspaces.
Compatible continuous maps on them therefore give a continuous map on
their union, with no separation assumption on the target.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

private def gluedBoundaryFunction (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (u : ↥(bottomOrSide n)) : X :=
  if hu : u.val.1 = 0 then f u.val.2
  else h (u.val.1, ⟨u.val.2, u.property.resolve_left hu⟩)

private theorem gluedBoundaryFunction_bottom (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (u : ↥(bottomOrSide n)) (hu : u.val.1 = 0) :
    gluedBoundaryFunction f h u = f u.val.2 := by
  classical
  exact dif_pos hu

private theorem gluedBoundaryFunction_side (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val)
    (u : ↥(bottomOrSide n)) (hu : u.val.2 ∈ simplexBoundary n) :
    gluedBoundaryFunction f h u = h (u.val.1, ⟨u.val.2, hu⟩) := by
  classical
  by_cases ht : u.val.1 = 0
  · rw [gluedBoundaryFunction_bottom f h u ht]
    simpa only [ht] using (h0 ⟨u.val.2, hu⟩).symm
  · exact dif_neg ht

private theorem continuous_gluedBoundaryFunction (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : Continuous (gluedBoundaryFunction f h) := by
  let B : Set (↥(bottomOrSide n)) := {u | u.val.1 = 0}
  let S : Set (↥(bottomOrSide n)) := {u | u.val.2 ∈ simplexBoundary n}
  have hB : IsClosed B :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hS : IsClosed S :=
    (isClosed_simplexBoundary n).preimage (continuous_snd.comp continuous_subtype_val)
  have hcover : B ∪ S = univ := by
    apply eq_univ_of_forall
    intro u
    exact u.property
  have hbottom : ContinuousOn (gluedBoundaryFunction f h) B :=
    (f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn.congr
      (fun u hu => gluedBoundaryFunction_bottom f h u hu)
  have hside : ContinuousOn (gluedBoundaryFunction f h) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun u : S => h (u.val.val.1, ⟨u.val.val.2, u.property⟩)) :=
      h.continuous.comp
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _))
    exact hc.congr fun u => (gluedBoundaryFunction_side f h h0 u.val u.property).symm
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hbottom.union_of_isClosed hside hB hS

/-- The actual map on the bottom and side, pasted from compatible data. -/
def gluedBoundaryMap (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(↥(bottomOrSide n), X) where
  toFun := gluedBoundaryFunction f h
  continuous_toFun := continuous_gluedBoundaryFunction f h h0

@[simp] theorem gluedBoundaryMap_bottomInclusion (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (s : Simplex n) :
    gluedBoundaryMap f h h0 (bottomInclusion n s) = f s :=
  gluedBoundaryFunction_bottom f h (bottomInclusion n s) rfl

@[simp] theorem gluedBoundaryMap_sideInclusion (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) (u : unitInterval × SimplexBoundary n) :
    gluedBoundaryMap f h h0 (sideInclusion n u) = h u :=
  gluedBoundaryFunction_side f h h0 (sideInclusion n u) u.2.property

@[simp] theorem gluedBoundaryMap_comp_bottomInclusion (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) :
    (gluedBoundaryMap f h h0).comp (bottomInclusion n) = f := by
  ext s
  exact gluedBoundaryMap_bottomInclusion f h h0 s

@[simp] theorem gluedBoundaryMap_comp_sideInclusion (f : C(Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) :
    (gluedBoundaryMap f h h0).comp (sideInclusion n) = h := by
  ext u
  exact gluedBoundaryMap_sideInclusion f h h0 u

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
