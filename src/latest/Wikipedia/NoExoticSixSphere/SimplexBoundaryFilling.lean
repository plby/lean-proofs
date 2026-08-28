import Wikipedia.NoExoticSixSphere.RelativeSimplexLifting
import Wikipedia.HopfProblem.DegreeCollapseSphereBoundaryExtension

/-!
# Exact simplex-boundary filling from native connectivity in arbitrary dimension

The boundary-preserving disk/simplex homeomorphism transports the actual
native-connectivity disk extension. The resulting continuous simplex
agrees with every prescribed original boundary value, including in the
low-dimensional cases handled by the disk theorem.
-/

noncomputable section

open Metric
open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz
open SecondHurewicz.SimplyConnected DegreeCollapse DegreeCollapse.DiskCylinder

namespace NoExoticSixSphere.SimplexBoundaryFilling

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]

theorem exists_extension (n : ℕ)
    (hpi : ∀ k, 0 < k → k < n → ∀ x : X, Subsingleton (π_ k X x))
    (g : C(SimplexBoundary n, X)) (x : X) :
    ∃ G : C(Simplex n, X), ∀ s : SimplexBoundary n, G s.val = g s := by
  let e := RelativeSimplexLifting.diskSimplexHomeomorph n
  let b : C(Sphere (E := Fin n → ℝ), SimplexBoundary n) := {
    toFun s := ⟨e (boundaryToDisk s),
      (RelativeSimplexLifting.diskSimplexHomeomorph_boundary_iff n _).mpr
        (mem_sphere_zero_iff_norm.mp s.property)⟩
    continuous_toFun := (e.continuous.comp boundaryToDisk.continuous).subtype_mk _ }
  obtain ⟨F, hF, _⟩ := DegreeCollapse.Sphere.exists_boundary_extension_of_pi
    (V := Fin n → ℝ) hpi (by simp) (g.comp b) x
  refine ⟨F.comp (e.symm : C(_, _)), ?_⟩
  intro s
  have hn : ‖(e.symm s.val : Fin n → ℝ)‖ = 1 :=
    (RelativeSimplexLifting.diskSimplexHomeomorph_symm_boundary_iff n s.val).mpr s.property
  let q : Sphere (E := Fin n → ℝ) := ⟨(e.symm s.val).val, mem_sphere_zero_iff_norm.mpr hn⟩
  have hb : b q = s := Subtype.ext (e.apply_symm_apply s.val)
  exact (hF q).trans (congrArg g hb)

end NoExoticSixSphere.SimplexBoundaryFilling
