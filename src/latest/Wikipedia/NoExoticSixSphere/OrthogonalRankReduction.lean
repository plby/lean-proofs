import Wikipedia.NoExoticSixSphere.ColumnFiber
import Wikipedia.NoExoticSixSphere.OrthogonalColumnHomotopy

/-!
# Reducing the rank of sphere-valued orthogonal families

Above the source sphere's dimension, a family of orthogonal operators can be
homotoped to the reconstruction of a family of one lower rank. Thus a proved
nullhomotopy theorem at any rank greater than the sphere dimension propagates
to all larger ranks. This does not assert the missing dimension-specific
nullhomotopy theorem at the initial rank.
-/

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths

namespace ColumnFiber

variable {r : ℕ} {X : Type*} [TopologicalSpace X]
variable (v c : UnitSphere (Vector (r + 1)))

/-- Reconstruct a continuous family from its complement operators. -/
noncomputable def reconstructMap (a : C(X, OrthogonalOperators r)) :
    C(X, OrthogonalOperators (r + 1)) :=
  ⟨fun x ↦ reconstruct v c (a x), continuous_reconstruct v c a a.continuous⟩

/-- Extract the continuous complement family from a constant-column family. -/
noncomputable def residualMap (a : C(X, OrthogonalOperators (r + 1)))
    (ha : ∀ x, (a x).1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    C(X, OrthogonalOperators r) :=
  ⟨fun x ↦ residual v c (a x) (ha x), continuous_residual v c a a.continuous ha⟩

theorem reconstructMap_residualMap (a : C(X, OrthogonalOperators (r + 1)))
    (ha : ∀ x, (a x).1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    reconstructMap v c (residualMap v c a ha) = a := by
  apply ContinuousMap.ext
  intro x
  exact reconstruct_residual v c (a x) (ha x)

/-- Reconstruction preserves homotopies through actual orthogonal operators. -/
theorem homotopic_reconstructMap {a b : C(X, OrthogonalOperators r)} (h : a.Homotopic b) :
    (reconstructMap v c a).Homotopic (reconstructMap v c b) :=
  (ContinuousMap.Homotopic.refl
    (⟨reconstruct v c, continuous_reconstruct v c id continuous_id⟩ :
      C(OrthogonalOperators r, OrthogonalOperators (r + 1)))).comp h

theorem reconstructMap_const (q : OrthogonalOperators r) :
    reconstructMap v c (ContinuousMap.const X q) = ContinuousMap.const X (reconstruct v c q) :=
  rfl

end ColumnFiber

open ColumnFiber

/-- A sphere family above the source dimension is homotopic to a lower-rank reconstruction. -/
theorem exists_orthogonalRankReduction {m r : ℕ} (hmr : m < r)
    (v : UnitSphere (Vector (r + 1))) (a : C(Sphere m, OrthogonalOperators (r + 1))) :
    ∃ c : UnitSphere (Vector (r + 1)), ∃ q : C(Sphere m, OrthogonalOperators r),
      a.Homotopic (reconstructMap v c q) := by
  obtain ⟨c, b, hab, hb⟩ := exists_constantColumn_sphere hmr v a
  refine ⟨c, residualMap v c b hb, ?_⟩
  rw [reconstructMap_residualMap]
  exact hab

/-- Nullhomotopy in rank `r` propagates to rank `r + 1` when `m < r`. -/
theorem sphereOrthogonalVanishing_successor {m r : ℕ} (hmr : m < r)
    (hr : ∀ a : C(Sphere m, OrthogonalOperators r),
      ∃ q, a.Homotopic (ContinuousMap.const _ q)) :
    ∀ a : C(Sphere m, OrthogonalOperators (r + 1)),
      ∃ q, a.Homotopic (ContinuousMap.const _ q) := by
  intro a
  obtain ⟨v⟩ : Nonempty (UnitSphere (Vector (r + 1))) :=
    NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  obtain ⟨c, b, hab⟩ := exists_orthogonalRankReduction hmr v a
  obtain ⟨q, hbq⟩ := hr b
  refine ⟨reconstruct v c q, hab.trans ?_⟩
  simpa only [reconstructMap_const] using homotopic_reconstructMap v c hbq

/-- A nullhomotopy theorem at one rank above the source dimension suffices for every larger rank.
The base-rank theorem remains an explicit hypothesis. -/
theorem sphereOrthogonalVanishing_of_rank {m k : ℕ} (hmk : m < k)
    (hk : ∀ a : C(Sphere m, OrthogonalOperators k),
      ∃ q, a.Homotopic (ContinuousMap.const _ q)) (r : ℕ) (hkr : k ≤ r) :
    ∀ a : C(Sphere m, OrthogonalOperators r),
      ∃ q, a.Homotopic (ContinuousMap.const _ q) := by
  induction r, hkr using Nat.le_induction with
  | base => exact hk
  | succ r hkr ih => exact sphereOrthogonalVanishing_successor (hmk.trans_le hkr) ih

end NoExoticSixSphere
