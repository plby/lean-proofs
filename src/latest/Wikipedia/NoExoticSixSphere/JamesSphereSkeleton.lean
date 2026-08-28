import Wikipedia.NoExoticSixSphere.JamesSphereCWStructure
import Wikipedia.NoExoticSixSphere.JamesPathConnected
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Native CW skeletons are the actual word-length stages

This identifies Mathlib's cells and skeletons for the constructed CW
instance with the original finite James stages. In particular the zero
skeleton is the single empty word, and the length-`k` cell has dimension
`k * n`. No homotopy-group or loop-space comparison is inferred from this
identification alone.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.CW

variable (n : ℕ) [Fact (0 < n)]

theorem pathConnectedSpace : PathConnectedSpace (James.Space (Sphere n) (spherePole n)) := by
  have hn : 0 < n := Fact.out
  cases n with
  | zero => omega
  | succ m => infer_instance

theorem native_openCell (k : ℕ) :
    Topology.CWComplex.openCell (C := (univ : Set (James.Space (Sphere n) (spherePole n))))
      (k * n) (⟨k, rfl⟩ : CellIndex n (k * n)) =
        {w | James.size (spherePole n) w = k} :=
  attachingMap_image_ball n Fact.out (k * n) ⟨k, rfl⟩

theorem native_closedCell (k : ℕ) :
    Topology.CWComplex.closedCell (C := (univ : Set (James.Space (Sphere n) (spherePole n))))
      (k * n) (⟨k, rfl⟩ : CellIndex n (k * n)) = James.stage (spherePole n) k :=
  attachingMap_image_closedBall n Fact.out (k * n) ⟨k, rfl⟩

theorem skeleton_eq_stage (k : ℕ) :
    (Topology.CWComplex.skeleton (univ : Set (James.Space (Sphere n) (spherePole n)))
      ((k * n : ℕ) : ℕ∞) : Set (James.Space (Sphere n) (spherePole n))) =
        James.stage (spherePole n) k := by
  rw [← Topology.CWComplex.iUnion_openCell_eq_skeleton]
  change (⋃ (d : ℕ) (_ : (d : ℕ∞) < (k * n : ℕ) + 1) (i : CellIndex n d),
    attachingMap n d i '' Metric.ball 0 1) = James.stage (spherePole n) k
  ext w
  simp only [mem_iUnion, exists_prop]
  change (∃ d : ℕ, (d : ℕ∞) < (k * n : ℕ) + 1 ∧
    ∃ i : CellIndex n d, w ∈ attachingMap n d i '' Metric.ball 0 1) ↔
      James.size (spherePole n) w ≤ k
  constructor
  · rintro ⟨d, hd, ⟨l, hl⟩, hw⟩
    have hsize : James.size (spherePole n) w = l :=
      (Set.ext_iff.mp (attachingMap_image_ball n Fact.out d ⟨l, hl⟩) w).mp hw
    have hd' : d ≤ k * n := by
      exact_mod_cast ENat.lt_natCast_add_one_iff.mp hd
    have hl' : l ≤ k := by
      by_contra h
      have hlt : k * n < l * n := Nat.mul_lt_mul_of_pos_right (lt_of_not_ge h) Fact.out
      omega
    exact hsize.le.trans hl'
  · intro hw
    let l := James.size (spherePole n) w
    have hd : l * n ≤ k * n := Nat.mul_le_mul_right n hw
    refine ⟨l * n, ENat.lt_natCast_add_one_iff.mpr ?_, ⟨l, rfl⟩, ?_⟩
    · exact_mod_cast hd
    · exact (Set.ext_iff.mp (attachingMap_image_ball n Fact.out (l * n) ⟨l, rfl⟩) w).mpr rfl

theorem zero_skeleton :
    (Topology.CWComplex.skeleton (univ : Set (James.Space (Sphere n) (spherePole n))) 0 :
      Set (James.Space (Sphere n) (spherePole n))) = {1} := by
  have h := skeleton_eq_stage n 0
  simp only [Nat.zero_mul, Nat.cast_zero] at h
  rw [h]
  ext w
  change James.size (spherePole n) w ≤ 0 ↔ w = 1
  rw [Nat.le_zero, James.size_eq_zero_iff]

end NoExoticSixSphere.JamesSphere.CW
