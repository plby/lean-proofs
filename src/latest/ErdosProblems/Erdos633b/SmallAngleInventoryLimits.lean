import ErdosProblems.Erdos633b.SmallAngleLocalLimits

/-! Summation of exact local small-angle bounds through the geometric
nonouter inventory and angle multiplicities. -/

namespace Erdos633b
namespace Triangle

theorem small_first_angle_bounds (S : Triangle) (hα : S.angle 0 < Real.pi / 21)
    (hβ : S.angle 1 ≤ 2 * Real.pi / 5) (hγ : S.angle 2 ≤ 2 * Real.pi / 3) :
    2 * Real.pi / 7 < S.angle 1 ∧ Real.pi / 2 < S.angle 2 := by
  constructor <;> linarith [S.angle_sum, Real.pi_pos]

end Triangle
namespace Tiling

theorem corner_weight_lower_of_nonouter_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (a b : ℕ) (k : d.NonouterVertex → ℕ)
    (he : ∀ v, (∑ j : Fin 3, (d.vertexAngleCount v.val j : ℝ) * d.tile.angle j) =
      (k v : ℝ) * Real.pi)
    (hlocal : ∀ v, a * d.vertexAngleCount v.val 1 + b * d.vertexAngleCount v.val 2 ≤
      (a + b) * k v) :
    a + b ≤ a * d.cornerColumnCount 1 + b * d.cornerColumnCount 2 := by
  classical
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hlocal v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hi1 := congrArg (fun x : ℕ => a * x) (d.nonouter_inventory 1)
  have hi2 := congrArg (fun x : ℕ => b * x) (d.nonouter_inventory 2)
  have hk := congrArg (fun x : ℕ => (a + b) * x) (d.nonouter_angle_multiplicity_sum k he)
  nlinarith

theorem small_angle_thirds_corner_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hsmall : d.tile.angle 0 < Real.pi / 21)
    (hβ : d.tile.angle 1 ≤ 2 * Real.pi / 5) (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (u : ℝ) (hu : -3 ≤ u) (hu' : u ≤ 1)
    (hb : 3 * d.tile.angle 1 = Real.pi + u * d.tile.angle 0) :
    3 ≤ d.cornerColumnCount 1 + 2 * d.cornerColumnCount 2 := by
  classical
  obtain ⟨hbmin, hgmin⟩ := d.tile.small_first_angle_bounds hsmall hβ hγ
  choose k hk1 hk2 he using d.nonouter_vertex_angle_multiple
  have hlocal (v : d.NonouterVertex) : d.vertexAngleCount v.val 1 +
      2 * d.vertexAngleCount v.val 2 ≤ 3 * k v := by
    have hs := he v
    rw [Fin.sum_univ_three] at hs
    obtain ⟨hq, hr⟩ := small_angle_local_counts _ _ _ (d.tile.angle_pos 0)
      hbmin hgmin _ _ _ _ (hk2 v) hs
    exact small_angle_thirds_local_bound _ _ _ u (d.tile.angle_pos 0) hsmall
      d.tile.angle_sum hu hu' hb _ _ _ _ hq hr hs
  simpa only [one_mul, Nat.reduceAdd] using
    d.corner_weight_lower_of_nonouter_bound 1 2 k he (by simpa only [one_mul] using hlocal)

theorem small_angle_fifths_corner_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hsmall : d.tile.angle 0 < Real.pi / 21)
    (hβ : d.tile.angle 1 ≤ 2 * Real.pi / 5) (hγ : d.tile.angle 2 ≤ 2 * Real.pi / 3)
    (u : ℝ) (hu : -1 ≤ u) (hu' : u ≤ 0)
    (hb : 5 * d.tile.angle 1 = 2 * Real.pi + u * d.tile.angle 0) :
    5 ≤ 2 * d.cornerColumnCount 1 + 3 * d.cornerColumnCount 2 := by
  classical
  obtain ⟨hbmin, hgmin⟩ := d.tile.small_first_angle_bounds hsmall hβ hγ
  choose k hk1 hk2 he using d.nonouter_vertex_angle_multiple
  have hlocal (v : d.NonouterVertex) : 2 * d.vertexAngleCount v.val 1 +
      3 * d.vertexAngleCount v.val 2 ≤ 5 * k v := by
    have hs := he v
    rw [Fin.sum_univ_three] at hs
    obtain ⟨hq, hr⟩ := small_angle_local_counts _ _ _ (d.tile.angle_pos 0)
      hbmin hgmin _ _ _ _ (hk2 v) hs
    exact small_angle_fifths_local_bound _ _ _ u (d.tile.angle_pos 0) hsmall
      d.tile.angle_sum hu hu' hb _ _ _ _ hq hr hs
  exact d.corner_weight_lower_of_nonouter_bound 2 3 k he hlocal

end Tiling
end Erdos633b
