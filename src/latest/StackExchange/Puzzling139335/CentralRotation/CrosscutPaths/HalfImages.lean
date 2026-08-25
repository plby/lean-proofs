import StackExchange.Puzzling139335.CentralRotation.CrosscutPaths.PathLoops

/-!
# The images of the two halves of a concatenated path

These image equalities hold for arbitrary paths in an arbitrary topological
space.  In particular, they do not require either path to be injective.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.CrosscutPaths

variable {X : Type*} [TopologicalSpace X] {p q r : X}

/-- The lower closed half of the concatenation traces exactly the first path. -/
theorem path_trans_extend_image_lowerHalf (m : Path p q) (n : Path q r) :
    (m.trans n).extend '' Icc (0 : ℝ) (1 / 2) = range m := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Path.extend_trans_of_le_half m n ht.2, ← m.extend_range]
    exact mem_range_self (2 * t)
  · rintro ⟨u, rfl⟩
    have huLower : 0 ≤ (u : ℝ) / 2 := by linarith [u.property.1]
    have huUpper : (u : ℝ) / 2 ≤ 1 / 2 := by linarith [u.property.2]
    refine ⟨(u : ℝ) / 2, ⟨huLower, huUpper⟩, ?_⟩
    rw [Path.extend_trans_of_le_half m n huUpper,
      show 2 * ((u : ℝ) / 2) = (u : ℝ) by ring, m.extend_extends']

/-- The upper closed half of the concatenation traces exactly the second path. -/
theorem path_trans_extend_image_upperHalf (m : Path p q) (n : Path q r) :
    (m.trans n).extend '' Icc (1 / 2 : ℝ) 1 = range n := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Path.extend_trans_of_half_le m n ht.1, ← n.extend_range]
    exact mem_range_self (2 * t - 1)
  · rintro ⟨u, rfl⟩
    have huLower : 1 / 2 ≤ ((u : ℝ) + 1) / 2 := by linarith [u.property.1]
    have huUpper : ((u : ℝ) + 1) / 2 ≤ 1 := by linarith [u.property.2]
    refine ⟨((u : ℝ) + 1) / 2, ⟨huLower, huUpper⟩, ?_⟩
    rw [Path.extend_trans_of_half_le m n huLower,
      show 2 * (((u : ℝ) + 1) / 2) - 1 = (u : ℝ) by ring, n.extend_extends']

end Puzzling139335.CentralRotation.CrosscutPaths
