import Wikipedia.HopfProblem.DegreeCollapseCylinderBoundaryGluing
import Wikipedia.HopfProblem.DegreeCollapseSphereBoundaryExtension

/-!
# Filling a full prescribed disk-cylinder boundary from native connectivity

This produces the comparison homotopy with exact bottom, top and side
values. The dimension of the filled ball is one greater than that of the
original cell; it therefore covers cells below the top obstruction degree.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.CylinderFilling

open DiskCylinder CylinderBall

variable {V X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [PathConnectedSpace X] {d : ℕ}

/-- Every compatible boundary family fills, retaining all values,
under native homotopy vanishing. -/
theorem exists_filling
    (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V + 1 ≤ d)
    (f g : C(Disk (E := V), X)) (H : C(I × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (boundaryToDisk s)) (x : X) :
    ∃ G : C(I × Disk (E := V), X),
      (∀ z, G (0, z) = f z) ∧ (∀ z, G (1, z) = g z) ∧
      ∀ t s, G (t, boundaryToDisk s) = H (t, s) := by
  let b := CylinderBoundary.glued f g H h0 h1
  let e := boundaryHomeomorph (V := V)
  let u := b.comp (e.symm : C(DiskCylinder.Sphere (E := ℝ × V), boundary (V := V)))
  have hdim : Module.finrank ℝ (ℝ × V) ≤ d := by
    simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using hd
  obtain ⟨v, hv, _⟩ := Sphere.exists_boundary_extension_of_pi hpi hdim u x
  let G : C(I × Disk (E := V), X) := v.comp (homeomorph (V := V) : C(_, _))
  have hb (p : boundary (V := V)) : G p.val = b p := by
    change v (boundaryToDisk (boundaryHomeomorph p)) = b p
    exact (hv (boundaryHomeomorph p)).trans
      (congrArg b (boundaryHomeomorph.symm_apply_apply p))
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    exact (hb (CylinderBoundary.lower (bottomMap z))).trans
      (CylinderBoundary.glued_bottom f g H h0 h1 z)
  · intro z
    exact (hb (CylinderBoundary.top z)).trans
      (CylinderBoundary.glued_top f g H h0 h1 z)
  · intro t s
    exact (hb (CylinderBoundary.lower (sideMap (t, s)))).trans
      (CylinderBoundary.glued_side f g H h0 h1 t s)

end Wikipedia.HopfProblem.DegreeCollapse.CylinderFilling
