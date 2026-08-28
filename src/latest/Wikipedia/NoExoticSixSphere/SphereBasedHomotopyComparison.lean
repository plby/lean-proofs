import Wikipedia.NoExoticSixSphere.OrthogonalHomotopyLift
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Mathlib.Topology.Homotopy.Path

/-!
# Ordinary and based homotopies into a simply connected sphere

Contract the loop traced by the marked source point relative to both
endpoints. Its exact orthogonal column lift is the identity at both
endpoints. Applying the inverse lift to the original homotopy therefore
fixes the marked point without altering either endpoint map.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ} [SimplyConnectedSpace (UnitSphere (Vector n))]

theorem exists_closed_orthogonal_lift (b : UnitSphere (Vector n)) (P : Path b b) :
    ∃ A : C(I, OrthogonalOperators n), A 0 = identity n ∧ A 1 = identity n ∧
      ∀ t : I, (A t).val.val b.val = (P t).val := by
  obtain ⟨L⟩ := SimplyConnectedSpace.paths_homotopic (Path.refl b) P
  obtain ⟨A, G, hG⟩ := exists_exactColumnHomotopyRel L b
    (ContinuousMap.const I (identity n)) (fun _ ↦ rfl)
  refine ⟨A, ?_, ?_, ?_⟩
  · exact (G.apply_one 0).symm.trans (G.eq_fst 1 (by simp))
  · exact (G.apply_one 1).symm.trans (G.eq_fst 1 (by simp))
  · intro t
    have h := hG 1 t
    rwa [G.apply_one, L.apply_one] at h

variable {X : Type*} [TopologicalSpace X]

theorem sphere_homotopicRel_point_of_homotopic
    {f g : C(X, UnitSphere (Vector n))} (p : X) (hbase : f p = g p)
    (H : f.Homotopy g) : f.HomotopicRel g {p} := by
  let b := f p
  let P : Path b b := {
    toFun := fun t ↦ H (t, p)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
    source' := H.apply_zero p
    target' := (H.apply_one p).trans hbase.symm }
  obtain ⟨A, hA0, hA1, hAcol⟩ := exists_closed_orthogonal_lift b P
  let B : I × X → OrthogonalOperators n := fun q ↦ A q.1
  have hB : Continuous B := A.continuous.comp continuous_fst
  let v : I × X → Vector n := fun q ↦ (inverse (B q)).val.val (H q).val
  have hv : Continuous v :=
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_inverse B hB))).clm_apply
        (continuous_subtype_val.comp H.continuous)
  have hunit (q : I × X) : v q ∈ UnitSphere (Vector n) := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact ((inverse (B q)).property (H q).val).trans (ClosedHemisphere.unit_norm (H q))
  let K : C(I × X, UnitSphere (Vector n)) := ⟨fun q ↦ ⟨v q, hunit q⟩, hv.subtype_mk hunit⟩
  refine ⟨{ toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
  · intro x
    apply Subtype.ext
    change (inverse (A 0)).val.val (H (0, x)).val = (f x).val
    rw [hA0, inverse_identity, H.apply_zero]
    rfl
  · intro x
    apply Subtype.ext
    change (inverse (A 1)).val.val (H (1, x)).val = (g x).val
    rw [hA1, inverse_identity, H.apply_one]
    rfl
  · intro t x hx
    have hx' : x = p := mem_singleton_iff.mp hx
    subst x
    apply Subtype.ext
    change (inverse (A t)).val.val (H (t, p)).val = b.val
    change (inverse (A t)).val.val (P t).val = b.val
    rw [← hAcol]
    exact inverse_apply_self _ _

theorem sphere_homotopicRel_point_iff
    {f g : C(X, UnitSphere (Vector n))} (p : X) (hbase : f p = g p) :
    f.HomotopicRel g {p} ↔ f.Homotopic g := by
  constructor
  · exact ContinuousMap.HomotopicRel.homotopic
  · rintro ⟨H⟩
    exact sphere_homotopicRel_point_of_homotopic p hbase H

end NoExoticSixSphere
