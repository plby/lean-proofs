import Wikipedia.NoExoticSixSphere.CylinderSphereConnectivity
import Wikipedia.NoExoticSixSphere.OrthogonalHomotopyLift
import Wikipedia.NoExoticSixSphere.OrthogonalStabilization
import Mathlib.Topology.Homotopy.Path

/-!
# Injectivity of orthogonal stabilization in the stable range

A homotopy between stabilized families has a sphere-valued column cylinder with
constant ends. Contract that cylinder relative to both ends, lift the contraction
exactly, and extract its constant-column complement family. This produces a
homotopy in the lower-rank group. Together with rank reduction, nullhomotopy
vanishing is invariant under rank increase in the indicated range.
-/

open Set unitInterval

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths ColumnFiber OrthogonalStabilization

/-- Stabilization reflects homotopies once the sphere cylinder has lower dimension than
the column sphere. This concerns the actual orthogonal operator maps. -/
theorem homotopic_stabilizeMap_iff {m r : ℕ} (hd : m + 1 < r)
    (v : UnitSphere (Vector (r + 1))) (a b : C(Sphere m, OrthogonalOperators r)) :
    (stabilizeMap v a).Homotopic (stabilizeMap v b) ↔ a.Homotopic b := by
  constructor
  · rintro ⟨H⟩
    let C := column v H.toContinuousMap
    have hC0 : ∀ x, C (0, x) = v := by
      intro x
      apply Subtype.ext
      change (H (0, x)).1.1 (v : Vector (r + 1)) = (v : Vector (r + 1))
      rw [H.apply_zero]
      exact stabilize_column v (a x)
    have hC1 : ∀ x, C (1, x) = v := by
      intro x
      apply Subtype.ext
      change (H (1, x)).1.1 (v : Vector (r + 1)) = (v : Vector (r + 1))
      rw [H.apply_one]
      exact stabilize_column v (b x)
    obtain ⟨K⟩ := sphereCylinder_nullhomotopicRel_boundary hd C v hC0 hC1
    obtain ⟨B, L, hLcol⟩ := exists_exactColumnHomotopyRel K v H.toContinuousMap (fun q ↦ rfl)
    have hBcol : ∀ q, (B q).1.1 (v : Vector (r + 1)) = (v : Vector (r + 1)) := by
      intro q
      have h := hLcol 1 q
      rw [L.apply_one, K.apply_one] at h
      exact h
    have hB0 : ∀ x, B (0, x) = stabilize v (a x) := by
      intro x
      exact (L.fst_eq_snd (Or.inl rfl)).symm.trans (H.apply_zero x)
    have hB1 : ∀ x, B (1, x) = stabilize v (b x) := by
      intro x
      exact (L.fst_eq_snd (Or.inr rfl)).symm.trans (H.apply_one x)
    let Q := residualMap v v B hBcol
    refine ⟨{ toContinuousMap := Q, map_zero_left := ?_, map_one_left := ?_ }⟩
    · intro x
      change residual v v (B (0, x)) (hBcol (0, x)) = a x
      simpa only [hB0, stabilize] using residual_reconstruct v v (a x)
    · intro x
      change residual v v (B (1, x)) (hBcol (1, x)) = b x
      simpa only [hB1, stabilize] using residual_reconstruct v v (b x)
  · intro h
    exact homotopic_reconstructMap v v h

/-- In the stable range, vanishing at one rank is equivalent to vanishing at the next rank. -/
theorem sphereOrthogonalVanishing_iff_successor {m r : ℕ} (hd : m + 1 < r) :
    (∀ a : C(Sphere m, OrthogonalOperators r),
      ∃ q, a.Homotopic (ContinuousMap.const _ q)) ↔
    (∀ a : C(Sphere m, OrthogonalOperators (r + 1)),
      ∃ q, a.Homotopic (ContinuousMap.const _ q)) := by
  constructor
  · exact sphereOrthogonalVanishing_successor ((Nat.lt_succ_self m).trans hd)
  · intro h a
    let v : UnitSphere (Vector (r + 1)) :=
      Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
    let p : Sphere m := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
    obtain ⟨c, ⟨H⟩⟩ := h (stabilizeMap v a)
    have hvalue : (stabilizeMap v a).Homotopic
        (stabilizeMap v (ContinuousMap.const _ (a p))) :=
      ⟨H.trans ((H.evalAt p).symm.toHomotopyConst)⟩
    exact ⟨a p, (homotopic_stabilizeMap_iff hd v a (ContinuousMap.const _ (a p))).mp hvalue⟩

/-- A vanishing computation at a larger finite rank descends through the stable range. -/
theorem sphereOrthogonalVanishing_descends {m k : ℕ} (hmk : m + 1 < k) (r : ℕ) (hkr : k ≤ r) :
    (∀ a : C(Sphere m, OrthogonalOperators r),
      ∃ q, a.Homotopic (ContinuousMap.const _ q)) →
    ∀ a : C(Sphere m, OrthogonalOperators k),
      ∃ q, a.Homotopic (ContinuousMap.const _ q) := by
  induction r, hkr using Nat.le_induction with
  | base => exact id
  | succ r hkr ih =>
    intro h
    exact ih ((sphereOrthogonalVanishing_iff_successor (hmk.trans_le hkr)).mpr h)

end NoExoticSixSphere
