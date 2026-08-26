import ErdosProblems.Erdos633.CornerBoundaryEdges

/-!
# The two acute corners of an irrational right reptiling

Angle independence forces each acute outer corner to consist of one tile
corner with the same label. The incident boundary edges then either preserve
both adjacent side labels or swap both. All counts refer to the actual tiling.
-/

namespace Erdos633

open scoped BigOperators EuclideanGeometry

theorem independent_right_alpha_counts (α β : ℝ)
    (hind : IntegerIndependentAngles α β) (r s t : ℕ)
    (h : (r : ℝ) * α + (s : ℝ) * β + (t : ℝ) * (α + β) = α) :
    r = 1 ∧ s = 0 ∧ t = 0 := by
  obtain ⟨hr, hs⟩ := hind ((r : ℤ) + t - 1) ((s : ℤ) + t) (by push_cast; linarith)
  omega

theorem independent_right_beta_counts (α β : ℝ)
    (hind : IntegerIndependentAngles α β) (r s t : ℕ)
    (h : (r : ℝ) * α + (s : ℝ) * β + (t : ℝ) * (α + β) = β) :
    r = 0 ∧ s = 1 ∧ t = 0 := by
  obtain ⟨hr, hs⟩ := hind ((r : ℤ) + t) ((s : ℤ) + t - 1) (by push_cast; linarith)
  omega

theorem CongruentTiling.right_acute_corner_counts
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles) (hC : R.angleC = Real.pi / 2)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) :
    (T.cornerCount P.a 0 = 1 ∧ T.cornerCount P.a 1 = 0 ∧ T.cornerCount P.a 2 = 0) ∧
      (T.cornerCount P.b 0 = 0 ∧ T.cornerCount P.b 1 = 1 ∧ T.cornerCount P.b 2 = 0) := by
  have hrel : 2 * R.angleA + 2 * R.angleB = Real.pi := by linarith [R.angle_sum]
  have hgamma : R.angleC = R.angleA + R.angleB := by linarith [R.angle_sum]
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 2 2 (by simpa [Triangle.cornerAngle] using hrel)
  have heA : (T.cornerCount P.a 0 : ℝ) * R.angleA + (T.cornerCount P.a 1 : ℝ) * R.angleB +
      (T.cornerCount P.a 2 : ℝ) * (R.angleA + R.angleB) = R.angleA := by
    simpa [Fin.sum_univ_succ, Triangle.cornerAngle, Triangle.vertex, hA, hgamma, ← add_assoc]
      using T.outer_angle_count_identity 0
  have heB : (T.cornerCount P.b 0 : ℝ) * R.angleA + (T.cornerCount P.b 1 : ℝ) * R.angleB +
      (T.cornerCount P.b 2 : ℝ) * (R.angleA + R.angleB) = R.angleB := by
    simpa [Fin.sum_univ_succ, Triangle.cornerAngle, Triangle.vertex, hB, hgamma, ← add_assoc]
      using T.outer_angle_count_identity 1
  exact ⟨independent_right_alpha_counts _ _ hind _ _ _ heA,
    independent_right_beta_counts _ _ hind _ _ _ heB⟩

theorem CongruentTiling.right_acute_boundary_alternatives
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles) (hC : R.angleC = Real.pi / 2)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) :
    ((0 < T.boundarySideCount 1 1 ∧ 0 < T.boundarySideCount 2 2) ∨
      (0 < T.boundarySideCount 1 2 ∧ 0 < T.boundarySideCount 2 1)) ∧
    ((0 < T.boundarySideCount 0 0 ∧ 0 < T.boundarySideCount 2 2) ∨
      (0 < T.boundarySideCount 0 2 ∧ 0 < T.boundarySideCount 2 0)) := by
  obtain ⟨ha, hb⟩ := T.right_acute_corner_counts hR hC hA hB
  constructor
  · obtain ⟨u, v, hu, hv, huv, hku, hlv⟩ := T.two_boundary_edges_at_single_corner 0 1 2
      (by decide) (by decide) (by decide) ha.1 (by
        intro m hm
        have hmc : m = 1 ∨ m = 2 := by omega
        rcases hmc with rfl | rfl
        · exact ha.2.1
        · exact ha.2.2)
    have hcases : (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hku, hlv⟩
    · exact Or.inr ⟨hku, hlv⟩
  · obtain ⟨u, v, hu, hv, huv, hku, hlv⟩ := T.two_boundary_edges_at_single_corner 1 0 2
      (by decide) (by decide) (by decide) hb.2.1 (by
        intro m hm
        have hmc : m = 0 ∨ m = 2 := by omega
        rcases hmc with rfl | rfl
        · exact hb.1
        · exact hb.2.2)
    have hcases : (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hku, hlv⟩
    · exact Or.inr ⟨hku, hlv⟩

theorem Triangle.right_sideLength_pythagoras (R : Triangle) (hC : R.angleC = Real.pi / 2) :
    R.sideLength 0 ^ 2 + R.sideLength 1 ^ 2 = R.sideLength 2 ^ 2 := by
  have h := EuclideanGeometry.law_cos R.a R.c R.b
  change ∠ R.a R.c R.b = Real.pi / 2 at hC
  rw [hC, Real.cos_pi_div_two] at h
  simp only [mul_zero, sub_zero, ← pow_two] at h
  change dist R.b R.c ^ 2 + dist R.c R.a ^ 2 = dist R.a R.b ^ 2
  rw [dist_comm R.c R.a]
  linarith

end Erdos633
