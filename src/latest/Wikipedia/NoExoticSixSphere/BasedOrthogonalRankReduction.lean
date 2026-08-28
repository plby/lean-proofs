import Wikipedia.NoExoticSixSphere.BasedSphereConnectivity
import Wikipedia.NoExoticSixSphere.OrthogonalStabilization

/-!
# Based orthogonal rank reduction

The sphere nullhomotopy can be chosen relative to a base point, and the exact
column lift preserves it. Hence stabilization is surjective on based sphere
homotopy classes in the indicated range, with an actual relative homotopy.
This is a rank-reduction theorem, not the missing vanishing computation.
-/

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths ColumnFiber OrthogonalStabilization

/-- An identity-based sphere family above the source dimension is relatively homotopic to
an identity-based lower-rank family extended by one identity coordinate. -/
theorem exists_basedOrthogonalRankReduction {m r : ℕ} (hmr : m < r)
    (v : UnitSphere (Vector (r + 1))) (a : C(Sphere m, OrthogonalOperators (r + 1)))
    (p : Sphere m) (ha : a p = identity (r + 1)) :
    ∃ q : C(Sphere m, OrthogonalOperators r), q p = identity r ∧
      Nonempty (a.HomotopyRel (stabilizeMap v q) {p}) := by
  let f := column v a
  have hfp : f p = v := by
    apply Subtype.ext
    change (a p).1.1 (v : Vector (r + 1)) = (v : Vector (r + 1))
    rw [ha]
    rfl
  obtain ⟨H⟩ := sphere_sphere_nullhomotopicRel_point hmr f p
  have hc : ContinuousMap.const (Sphere m) (f p) = ContinuousMap.const (Sphere m) v :=
    congrArg (ContinuousMap.const (Sphere m)) hfp
  let H' : f.HomotopyRel (ContinuousMap.const _ v) {p} := H.cast rfl hc
  obtain ⟨b, G, hGcol⟩ := exists_exactColumnHomotopyRel H' v a (fun x ↦ rfl)
  have hcol : ∀ x, (b x).1.1 (v : Vector (r + 1)) = (v : Vector (r + 1)) := by
    intro x
    have h := hGcol 1 x
    rw [G.apply_one, H'.apply_one] at h
    exact h
  have hbp : b p = identity (r + 1) :=
    (G.fst_eq_snd (by simp)).symm.trans ha
  let q := residualMap v v b hcol
  have hrec : reconstructMap v v q = b := reconstructMap_residualMap v v b hcol
  refine ⟨q, ?_, ⟨G.cast rfl hrec.symm⟩⟩
  change residual v v (b p) (hcol p) = identity r
  have hid : reconstruct v v (identity r) = identity (r + 1) := stabilize_identity v
  simpa only [hid, hbp] using residual_reconstruct v v (identity r)

end NoExoticSixSphere
