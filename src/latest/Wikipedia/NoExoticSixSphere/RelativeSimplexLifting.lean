import Wikipedia.NoExoticSixSphere.RelativeDiskLifting
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyHomeomorph

/-!
# Relative simplex lifting with prescribed boundary in every dimension

The exact disk/simplex homeomorphism carries the entire original boundary
to the disk boundary. Transporting the general relative disk lift gives
the source simplex and a homotopy fixing every original boundary point.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem FirstHurewicz
open SecondHurewicz.SimplyConnected DegreeCollapse DegreeCollapse.DiskCylinder

namespace NoExoticSixSphere.RelativeSimplexLifting

def diskSimplexHomeomorph (n : ℕ) : Disk (E := Fin n → ℝ) ≃ₜ Simplex n :=
  (DiskCube.homeomorph (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))).trans
    (HigherHurewicz.simplexCubeHomeomorph n).symm

theorem diskSimplexHomeomorph_boundary_iff (n : ℕ) (z : Disk (E := Fin n → ℝ)) :
    diskSimplexHomeomorph n z ∈ simplexBoundary n ↔ ‖(z : Fin n → ℝ)‖ = 1 := by
  change (HigherHurewicz.simplexCubeHomeomorph n).symm
    (DiskCube.homeomorph (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)) z) ∈ simplexBoundary n ↔ _
  rw [HigherHurewicz.simplexCubeHomeomorph_symm_boundary_iff, DiskCube.boundary_iff]

theorem diskSimplexHomeomorph_symm_boundary_iff (n : ℕ) (s : Simplex n) :
    ‖((diskSimplexHomeomorph n).symm s : Fin n → ℝ)‖ = 1 ↔ s ∈ simplexBoundary n := by
  rw [← diskSimplexHomeomorph_boundary_iff, Homeomorph.apply_symm_apply]

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

theorem exists_lift (n : ℕ) (F : C(A, B))
    (hF : ∀ x : A, Function.Surjective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    (a : C(Simplex n, A)) (u : C(Simplex n, B))
    (hu : ∀ s : SimplexBoundary n, u s.val = F (a s.val)) :
    ∃ v : C(Simplex n, A),
      (∀ s : SimplexBoundary n, v s.val = a s.val) ∧
      (F.comp v).HomotopicRel u (simplexBoundary n) := by
  let e := diskSimplexHomeomorph n
  let aD : C(Disk (E := Fin n → ℝ), A) := a.comp ⟨e, e.continuous⟩
  let uD : C(Disk (E := Fin n → ℝ), B) := u.comp ⟨e, e.continuous⟩
  have hD (s : Sphere (E := Fin n → ℝ)) :
      uD (boundaryToDisk s) = F (aD (boundaryToDisk s)) :=
    hu ⟨e (boundaryToDisk s), (diskSimplexHomeomorph_boundary_iff n _).mpr
      (mem_sphere_zero_iff_norm.mp s.property)⟩
  obtain ⟨vD, hvD, ⟨HD⟩⟩ := RelativeDiskLifting.exists_relative_lift F hF
    (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)) aD uD hD
  let v : C(Simplex n, A) := vD.comp (e.symm : C(_, _))
  have hv (s : SimplexBoundary n) : v s.val = a s.val := by
    have hn : ‖(e.symm s.val : Fin n → ℝ)‖ = 1 :=
      (diskSimplexHomeomorph_symm_boundary_iff n s.val).mpr s.property
    let q : Sphere (E := Fin n → ℝ) := ⟨(e.symm s.val).val, mem_sphere_zero_iff_norm.mpr hn⟩
    exact (hvD q).trans (congrArg a (e.apply_symm_apply s.val))
  refine ⟨v, hv, ⟨{
    toFun := fun z ↦ HD (z.1, e.symm z.2)
    continuous_toFun := HD.continuous.comp
      (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
    map_zero_left := fun s ↦ HD.apply_zero (e.symm s)
    map_one_left := fun s ↦ (HD.apply_one (e.symm s)).trans (congrArg u (e.apply_symm_apply s))
    prop' := fun t s hs ↦ HD.eq_fst t
      ((diskSimplexHomeomorph_symm_boundary_iff n s).mpr hs) }⟩⟩

end NoExoticSixSphere.RelativeSimplexLifting
