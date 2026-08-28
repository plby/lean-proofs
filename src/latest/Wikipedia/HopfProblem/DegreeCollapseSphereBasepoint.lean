import Wikipedia.HopfProblem.DegreeCollapseDiskCube
import Wikipedia.HopfProblem.DegreeCollapseSphereHomotopy
import Mathlib.Topology.Homotopy.Path

/-!
# Move the value of the sphere base point along an actual path

Disk homotopy extension moves the entire native cube boundary along one
path. Quotient descent then gives a sphere homotopy whose distinguished
point follows that path. No change to either topology is made.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereBasepoint

open SixSphereCube DiskCylinder

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

/-- Any specified path at the sphere base point is realized by an actual sphere homotopy. -/
theorem exists_adjustment (u : C(StandardSphere, Y)) (P : Path (u sphereBasePoint) y) :
    ∃ v : C(StandardSphere, Y), v sphereBasePoint = y ∧ u.Homotopic v := by
  let V := Fin 6 → ℝ
  let L : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  let e := DiskCube.homeomorph L
  let f : C(Disk (E := V), Y) := u.comp (cubeSphereMap.comp (e : C(_, _)))
  let side : C(I × Sphere (E := V), Y) := P.toContinuousMap.comp ContinuousMap.fst
  have h0 : ∀ s, side (0, s) = f (boundaryToDisk s) := by
    intro s
    have hs := (DiskCube.boundary_iff L (boundaryToDisk s)).mpr
      (mem_sphere_zero_iff_norm.mp s.property)
    exact P.source.trans (congrArg u (cubeSphereMap_boundary _ hs)).symm
  let W := DiskCylinder.extend f side h0
  let C : C(I × (Fin 6 → I), Y) :=
    W.comp ((ContinuousMap.id I).prodMap (e.symm : C(_, _)))
  have hCboundary (t : I) (z : Fin 6 → I) (hz : z ∈ Cube.boundary (Fin 6)) :
      C (t, z) = P t := by
    let s : Sphere (E := V) := ⟨(e.symm z).val,
      mem_sphere_zero_iff_norm.mpr ((DiskCube.symm_boundary_iff L z).mpr hz)⟩
    exact DiskCylinder.extend_side f side h0 t s
  have hfib : ∀ a b, cylinderQuotient a = cylinderQuotient b → C a = C b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : cubeSphereMap z = cubeSphereMap w := congrArg Prod.snd h
    rcases (cubeSphereMap_eq_iff z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hCboundary t z hz).trans (hCboundary t w hw).symm
  let G := cylinderQuotient_isQuotientMap.lift C hfib
  have hG (t : I) (z : Fin 6 → I) : G (t, cubeSphereMap z) = C (t, z) :=
    ContinuousMap.congr_fun (cylinderQuotient_isQuotientMap.lift_comp C hfib) (t, z)
  let v : C(StandardSphere, Y) :=
    G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  refine ⟨v, ?_, ⟨{
    toContinuousMap := G
    map_zero_left := ?_
    map_one_left := fun _ => rfl
  }⟩⟩
  · change G (1, sphereBasePoint) = y
    rw [← cubeSphereMap_boundary 0 zero_mem_cubeBoundary, hG]
    exact (hCboundary 1 0 zero_mem_cubeBoundary).trans P.target
  · intro z
    obtain ⟨w, rfl⟩ := cubeSphereMap_surjective z
    exact (hG 0 w).trans ((DiskCylinder.extend_bottom f side h0 (e.symm w)).trans
      (congrArg (fun q => u (cubeSphereMap q)) (e.apply_symm_apply w)))

end Wikipedia.HopfProblem.DegreeCollapse.SphereBasepoint
