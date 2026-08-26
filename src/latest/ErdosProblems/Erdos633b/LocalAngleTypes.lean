import ErdosProblems.Erdos633b.AngleRelationCounts
import ErdosProblems.Erdos633b.NonouterAngleSums

/-! Complete local angle-count tables for the two non-reptiling groups.
The tables are deduced from exact local sums and irrationality. -/

namespace Erdos633b

def GroupOneVertexType (p q r k : ℕ) : Prop :=
  (k = 1 ∧ ((p, q, r) = (1, 1, 1) ∨ (p, q, r) = (3, 2, 0))) ∨
  (k = 2 ∧ ((p, q, r) = (0, 1, 3) ∨ (p, q, r) = (2, 2, 2) ∨
    (p, q, r) = (4, 3, 1) ∨ (p, q, r) = (6, 4, 0)))

def GroupTwoVertexType (p q r k : ℕ) : Prop :=
  (k = 1 ∧ ((p, q, r) = (1, 1, 1) ∨ (p, q, r) = (3, 3, 0))) ∨
  (k = 2 ∧ ((p, q, r) = (0, 0, 3) ∨ (p, q, r) = (2, 2, 2) ∨
    (p, q, r) = (4, 4, 1) ∨ (p, q, r) = (6, 6, 0)))

theorem groupOne_vertex_types_of_equations (p q r k : ℕ) (hk : k = 1 ∨ k = 2)
    (hp : p + 3 * r = 3 * k + r) (hq : q + 2 * r = 2 * k + r) :
    GroupOneVertexType p q r k := by
  rcases hk with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    simp only [Prod.mk.injEq]
    omega
  · right
    refine ⟨rfl, ?_⟩
    simp only [Prod.mk.injEq]
    omega

theorem groupTwo_vertex_types_of_equations (p q r k : ℕ) (hk : k = 1 ∨ k = 2)
    (hp : p + 3 * r = 3 * k + r) (hq : q + 3 * r = 3 * k + r) :
    GroupTwoVertexType p q r k := by
  rcases hk with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    simp only [Prod.mk.injEq]
    omega
  · right
    refine ⟨rfl, ?_⟩
    simp only [Prod.mk.injEq]
    omega

theorem groupOne_vertex_count_mod_two (p q r k : ℕ) (h : GroupOneVertexType p q r k) :
    (p + q + r) % 2 = k % 2 := by
  rcases h with ⟨hk, h⟩ | ⟨hk, h⟩ <;> simp only [Prod.mk.injEq] at h <;> omega

namespace Triangle

theorem groupOne_local_angle_type (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi)
    (hirr : Irrational (S.angle 0 / Real.pi)) (p q r k : ℕ) (hk : k = 1 ∨ k = 2)
    (hs : (p : ℝ) * S.angle 0 + (q : ℝ) * S.angle 1 + (r : ℝ) * S.angle 2 = k * Real.pi) :
    GroupOneVertexType p q r k := by
  obtain ⟨hp, hq⟩ := S.local_angle_integer_equations 3 2 (by decide) hrel hirr p q r k hs
  exact groupOne_vertex_types_of_equations p q r k hk hp hq

theorem groupTwo_local_angle_type (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (hirr : Irrational (S.angle 0 / Real.pi)) (p q r k : ℕ) (hk : k = 1 ∨ k = 2)
    (hs : (p : ℝ) * S.angle 0 + (q : ℝ) * S.angle 1 + (r : ℝ) * S.angle 2 = k * Real.pi) :
    GroupTwoVertexType p q r k := by
  have hrel : 3 * S.angle 0 + 3 * S.angle 1 = Real.pi := by linarith [S.angle_sum]
  obtain ⟨hp, hq⟩ := S.local_angle_integer_equations 3 3 (by decide) hrel hirr p q r k hs
  exact groupTwo_vertex_types_of_equations p q r k hk hp hq

end Triangle
namespace Tiling

theorem groupOne_first_angle_irrational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    Irrational (d.tile.angle 0 / Real.pi) :=
  d.tile.irrational_first_of_angle_relation 3 2 (by decide) hrel
    (fun h => hirr (d.rational_angles_of_tile h))

theorem groupTwo_first_angle_irrational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    Irrational (d.tile.angle 0 / Real.pi) := by
  have hrel : 3 * d.tile.angle 0 + 3 * d.tile.angle 1 = Real.pi := by linarith [d.tile.angle_sum]
  exact d.tile.irrational_first_of_angle_relation 3 3 (by decide) hrel
    (fun h => hirr (d.rational_angles_of_tile h))

theorem nonouter_groupOne_vertex_type {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (v : d.NonouterVertex) :
    ∃ k : ℕ, GroupOneVertexType (d.vertexAngleCount v.val 0)
      (d.vertexAngleCount v.val 1) (d.vertexAngleCount v.val 2) k := by
  obtain ⟨k, hk0, hk2, hs⟩ := d.nonouter_vertex_angle_multiple v
  refine ⟨k, d.tile.groupOne_local_angle_type hrel (d.groupOne_first_angle_irrational hrel hirr)
    _ _ _ _ (by omega) ?_⟩
  simpa only [Fin.sum_univ_three] using hs

theorem nonouter_groupTwo_vertex_type {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (v : d.NonouterVertex) :
    ∃ k : ℕ, GroupTwoVertexType (d.vertexAngleCount v.val 0)
      (d.vertexAngleCount v.val 1) (d.vertexAngleCount v.val 2) k := by
  obtain ⟨k, hk0, hk2, hs⟩ := d.nonouter_vertex_angle_multiple v
  refine ⟨k, d.tile.groupTwo_local_angle_type hg (d.groupTwo_first_angle_irrational hg hirr)
    _ _ _ _ (by omega) ?_⟩
  simpa only [Fin.sum_univ_three] using hs

end Tiling
end Erdos633b
