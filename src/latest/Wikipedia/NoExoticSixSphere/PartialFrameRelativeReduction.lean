import Wikipedia.NoExoticSixSphere.PartialFrameColumnLift

/-!
# Relative rank reduction in the actual column fiber

A column contraction retaining a prescribed subset gives a reconstruction
representative while retaining the same subset. Reconstruction is injective.
-/

noncomputable section

open Set

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

variable {n r : ℕ}
variable (v : UnitSphere (Vector (r + 1))) (c : UnitSphere (Vector (n + 1)))

theorem reconstruction_injective : Function.Injective (ColumnFiber.reconstructionMap v c) := by
  intro p q h
  apply (ColumnFiber.homeomorph v c).symm.injective
  exact Subtype.ext h

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem exists_rankReductionRel_of_column_homotopy
    (a : C(X, Space (n + 1) (r + 1))) {S : Set X}
    (H : ((column v).comp a).HomotopyRel (ContinuousMap.const X c) S) :
    ∃ q : C(X, Space n r),
      Nonempty (a.HomotopyRel ((ColumnFiber.reconstructionMap v c).comp q) S) := by
  obtain ⟨b, G, hG⟩ := exists_columnHomotopyRel v a H
  have hb (x : X) : (b x).val v.val = c.val := by
    have h := hG 1 x
    rw [G.apply_one, H.apply_one] at h
    exact congrArg Subtype.val h
  let q : C(X, Space n r) :=
    ⟨fun x ↦ ColumnFiber.residual v c (b x) (hb x),
      ColumnFiber.continuous_residual v c b b.continuous hb⟩
  have he : b = (ColumnFiber.reconstructionMap v c).comp q := by
    apply ContinuousMap.ext
    intro x
    exact (ColumnFiber.reconstruct_residual v c (b x) (hb x)).symm
  exact ⟨q, ⟨G.cast rfl he⟩⟩

end NoExoticSixSphere.Stiefel
