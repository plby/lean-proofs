import ErdosProblems.Erdos941.Spheres

/-! # Exact pair geometry on an integral sphere -/

namespace Erdos941

def dot3 (v w : Triple) : ℤ := v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2

theorem norm_sub_identity (v w : Triple) :
    tripleNorm (v - w) = tripleNorm v + tripleNorm w - 2 * dot3 v w := by
  dsimp [tripleNorm, norm3, dot3]
  ring

theorem norm_add_identity (v w : Triple) :
    tripleNorm (v + w) = tripleNorm v + tripleNorm w + 2 * dot3 v w := by
  dsimp [tripleNorm, norm3, dot3]
  ring

theorem tripleNorm_eq_zero {v : Triple} : tripleNorm v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, tripleNorm, norm3]⟩
  have hx : v.1 = 0 := by
    dsimp [tripleNorm, norm3] at h
    nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2]
  have hy : v.2.1 = 0 := by
    dsimp [tripleNorm, norm3] at h
    nlinarith [sq_nonneg v.1, sq_nonneg v.2.2]
  have hz : v.2.2 = 0 := by
    dsimp [tripleNorm, norm3] at h
    nlinarith [sq_nonneg v.1, sq_nonneg v.2.1]
  exact Prod.ext hx (Prod.ext hy hz)

theorem dot3_bounds {n : ℕ} {v w : Triple}
    (hv : tripleNorm v = n) (hw : tripleNorm w = n) :
    -(n : ℤ) ≤ dot3 v w ∧ dot3 v w ≤ n := by
  have hplus := norm3_nonneg (v + w).1 (v + w).2.1 (v + w).2.2
  have hminus := norm3_nonneg (v - w).1 (v - w).2.1 (v - w).2.2
  change 0 ≤ tripleNorm (v + w) at hplus
  change 0 ≤ tripleNorm (v - w) at hminus
  rw [norm_add_identity, hv, hw] at hplus
  rw [norm_sub_identity, hv, hw] at hminus
  omega

theorem dot3_eq_norm_iff {n : ℕ} {v w : Triple}
    (hv : tripleNorm v = n) (hw : tripleNorm w = n) : dot3 v w = n ↔ v = w := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hzero : tripleNorm (v - w) = 0 := by
      rw [norm_sub_identity, hv, hw, h]
      ring
    exact sub_eq_zero.mp (tripleNorm_eq_zero.mp hzero)
  · rw [h]
    simpa only [tripleNorm, norm3, dot3, pow_two] using hw

theorem dot3_eq_neg_norm_iff {n : ℕ} {v w : Triple}
    (hv : tripleNorm v = n) (hw : tripleNorm w = n) :
    dot3 v w = -(n : ℤ) ↔ v = -w := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hzero : tripleNorm (v + w) = 0 := by
      rw [norm_add_identity, hv, hw, h]
      ring
    exact eq_neg_of_add_eq_zero_left (tripleNorm_eq_zero.mp hzero)
  · rw [h]
    have hself : dot3 w w = n := by
      simpa only [tripleNorm, norm3, dot3, pow_two] using hw
    calc
      dot3 (-w) w = -dot3 w w := by dsimp [dot3]; ring
      _ = _ := congrArg Neg.neg hself

theorem gram_determinant_identity (v w : Triple) :
    tripleNorm v * tripleNorm w - dot3 v w ^ 2 =
      (v.1 * w.2.1 - v.2.1 * w.1) ^ 2 +
        (v.1 * w.2.2 - v.2.2 * w.1) ^ 2 +
          (v.2.1 * w.2.2 - v.2.2 * w.2.1) ^ 2 := by
  dsimp [tripleNorm, norm3, dot3]
  ring

noncomputable def spherePairs (n : ℕ) (e : ℤ) : Finset (Triple × Triple) :=
  ((spherePoints n).product (spherePoints n)).filter fun p => dot3 p.1 p.2 = e

@[simp] theorem mem_spherePairs {n : ℕ} {e : ℤ} {v w : Triple} :
    (v, w) ∈ spherePairs n e ↔
      tripleNorm v = n ∧ tripleNorm w = n ∧ dot3 v w = e := by
  constructor
  · intro h
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp h
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hp
    exact ⟨mem_spherePoints.mp hv, mem_spherePoints.mp hw, he⟩
  · rintro ⟨hv, hw, he⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_spherePoints.mpr hv, mem_spherePoints.mpr hw⟩, he⟩

theorem spherePairs_diagonal (n : ℕ) :
    spherePairs n n = (spherePoints n).image fun v => (v, v) := by
  ext ⟨v, w⟩
  simp only [mem_spherePairs, Finset.mem_image, Prod.mk.injEq, mem_spherePoints]
  constructor
  · rintro ⟨hv, hw, he⟩
    have h := (dot3_eq_norm_iff hv hw).mp he
    exact ⟨v, hv, rfl, h⟩
  · rintro ⟨u, hu, rfl, rfl⟩
    exact ⟨hu, hu, (dot3_eq_norm_iff hu hu).mpr rfl⟩

theorem spherePairs_diagonal_card (n : ℕ) : (spherePairs n n).card = sphereCount n := by
  rw [spherePairs_diagonal, Finset.card_image_iff.mpr]
  · rfl
  · intro v _ w _ h
    exact congrArg Prod.fst h

end Erdos941
