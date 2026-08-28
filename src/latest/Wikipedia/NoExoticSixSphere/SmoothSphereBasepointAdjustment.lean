import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.HopfProblem.DegreeCollapseDiskCube
import Mathlib.Topology.Homotopy.Path

/-!
# Move the basepoint of an actual sphere map

Disk homotopy extension moves the entire native cube boundary along the
specified path. The joint cylinder quotient gives an ordinary homotopy of
the original sphere maps. This works in every positive dimension, and the
target is an arbitrary topological space.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.DegreeCollapse

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] {y : Y}

theorem exists_basepoint_adjustment (hn : 0 < n) (u : C(Sphere n, Y))
    (P : Path (u (spherePole n)) y) :
    ∃ v : BasedMap n Y y, u.Homotopic v.val := by
  let V := Fin n → ℝ
  let L : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  let e := DiskCube.homeomorph L
  let f : C(DiskCylinder.Disk (E := V), Y) :=
    u.comp ((quotient n).comp (e : C(_, _)))
  let side : C(I × DiskCylinder.Sphere (E := V), Y) :=
    P.toContinuousMap.comp ContinuousMap.fst
  have h0 : ∀ s, side (0, s) = f (DiskCylinder.boundaryToDisk s) := by
    intro s
    have hs := (DiskCube.boundary_iff L (DiskCylinder.boundaryToDisk s)).mpr
      (mem_sphere_zero_iff_norm.mp s.property)
    exact P.source.trans (congrArg u (quotient_boundary n _ hs)).symm
  let W := DiskCylinder.extend f side h0
  let C : C(I × (Fin n → I), Y) :=
    W.comp ((ContinuousMap.id I).prodMap (e.symm : C(_, _)))
  have hCboundary (t : I) (z : Fin n → I) (hz : z ∈ Cube.boundary (Fin n)) :
      C (t, z) = P t := by
    let s : DiskCylinder.Sphere (E := V) := ⟨(e.symm z).val,
      mem_sphere_zero_iff_norm.mpr ((DiskCube.symm_boundary_iff L z).mpr hz)⟩
    exact DiskCylinder.extend_side f side h0 t s
  have hfib : ∀ a b, cylinder n a = cylinder n b → C a = C b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hCboundary t z hz).trans (hCboundary t w hw).symm
  let G := (cylinder_isQuotientMap hn).lift C hfib
  have hG (t : I) (z : Fin n → I) : G (t, quotient n z) = C (t, z) :=
    ContinuousMap.congr_fun ((cylinder_isQuotientMap hn).lift_comp C hfib) (t, z)
  let v : C(Sphere n, Y) :=
    G.comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩
  have hv : v (spherePole n) = y := by
    change G (1, spherePole n) = y
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact (hCboundary 1 0 (zero_boundary hn)).trans P.target
  refine ⟨⟨v, hv⟩, ⟨{
    toContinuousMap := G
    map_zero_left := ?_
    map_one_left := fun _ ↦ rfl
  }⟩⟩
  intro z
  obtain ⟨w, rfl⟩ := quotient_surjective hn z
  exact (hG 0 w).trans ((DiskCylinder.extend_bottom f side h0 (e.symm w)).trans
    (congrArg (fun q ↦ u (quotient n q)) (e.apply_symm_apply w)))

theorem exists_based_map_homotopic [PathConnectedSpace Y] (hn : 0 < n)
    (u : C(Sphere n, Y)) (y : Y) : ∃ v : BasedMap n Y y, u.Homotopic v.val :=
  exists_basepoint_adjustment hn u (PathConnectedSpace.somePath (u (spherePole n)) y)

end NoExoticSixSphere.SmoothCube
