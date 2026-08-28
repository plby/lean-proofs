import Wikipedia.HopfProblem.OrbitPairRealizedSimplexBoundary
import Wikipedia.HopfProblem.DegreeCollapseDiskCube

/-!
# Homotopy extension for the literal simplex boundary

The existing disk homotopy-extension theorem is transported through
proved boundary-preserving homeomorphisms from a native norm disk to a
cube and from that cube to the actual barycentric simplex. The target
space is arbitrary, and the prescribed boundary homotopy is retained
at every time.
-/

noncomputable section

universe v

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SimplexHomotopyExtension

open FirstHurewicz SecondHurewicz.SimplyConnected DegreeCollapse

def diskHomeomorph (n : ℕ) : DiskCylinder.Disk (E := Fin n → ℝ) ≃ₜ Simplex n :=
  (DiskCube.homeomorph (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))).trans
    (HigherHurewicz.simplexCubeHomeomorph n).symm

theorem diskHomeomorph_boundary_iff (n : ℕ) (z : DiskCylinder.Disk (E := Fin n → ℝ)) :
    diskHomeomorph n z ∈ simplexBoundary n ↔ ‖(z : Fin n → ℝ)‖ = 1 :=
  (HigherHurewicz.simplexCubeHomeomorph_symm_boundary_iff n _).trans
    (DiskCube.boundary_iff (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)) z)

def boundaryMap (n : ℕ) : C(DiskCylinder.Sphere (E := Fin n → ℝ), ↥(simplexBoundary n)) where
  toFun s := ⟨diskHomeomorph n (DiskCylinder.boundaryToDisk s),
    (diskHomeomorph_boundary_iff n _).mpr (mem_sphere_zero_iff_norm.mp s.property)⟩
  continuous_toFun := ((diskHomeomorph n).continuous.comp
    DiskCylinder.boundaryToDisk.continuous).subtype_mk _

variable {Y : Type v} [TopologicalSpace Y]

theorem exists_extension (n : ℕ) (f : C(Simplex n, Y))
    (G : C(I × ↥(simplexBoundary n), Y)) (h0 : ∀ q, G (0, q) = f q.val) :
    ∃ H : C(I × Simplex n, Y),
      (∀ s, H (0, s) = f s) ∧ ∀ t q, H (t, q.val) = G (t, q) := by
  let e := diskHomeomorph n
  let f' : C(DiskCylinder.Disk (E := Fin n → ℝ), Y) := f.comp ⟨e, e.continuous⟩
  let G' : C(I × DiskCylinder.Sphere (E := Fin n → ℝ), Y) :=
    G.comp ((ContinuousMap.id I).prodMap (boundaryMap n))
  have h0' : ∀ s, G' (0, s) = f' (DiskCylinder.boundaryToDisk s) := fun s ↦ h0 (boundaryMap n s)
  let K := DiskCylinder.extend f' G' h0'
  let H := K.comp ((ContinuousMap.id I).prodMap ⟨e.symm, e.symm.continuous⟩)
  refine ⟨H, ?_, ?_⟩
  · intro s
    change K (0, e.symm s) = f s
    exact (DiskCylinder.extend_bottom f' G' h0' (e.symm s)).trans
      (congrArg f (e.apply_symm_apply s))
  · intro t q
    have hp : ‖((e.symm q.val).val : Fin n → ℝ)‖ = 1 :=
      (diskHomeomorph_boundary_iff n (e.symm q.val)).mp
        (by change e (e.symm q.val) ∈ simplexBoundary n; rw [e.apply_symm_apply]; exact q.property)
    let p : DiskCylinder.Sphere (E := Fin n → ℝ) :=
      ⟨(e.symm q.val).val, mem_sphere_zero_iff_norm.mpr hp⟩
    have hq : boundaryMap n p = q := Subtype.ext (e.apply_symm_apply q.val)
    change K (t, DiskCylinder.boundaryToDisk p) = G (t, q)
    exact (DiskCylinder.extend_side f' G' h0' t p).trans
      (congrArg (fun a ↦ G (t, a)) hq)

end Wikipedia.HopfProblem.OrbitPair.SimplexHomotopyExtension
