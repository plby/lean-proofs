import ErdosProblems.Erdos941.HurwitzOrder

/-! # The Euclidean approximation property of the Hurwitz order -/

namespace Erdos941

open scoped Quaternion

private theorem floor_half_bounds (x : ℚ) :
    -(1 / 2 : ℚ) ≤ x - ⌊x + 1 / 2⌋ ∧ x - ⌊x + 1 / 2⌋ < 1 / 2 := by
  have hl := Int.floor_le (x + 1 / 2)
  have hu := Int.lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

private theorem half_interval_sq {x : ℚ} (hl : -(1 / 2 : ℚ) ≤ x) (hu : x < 1 / 2) :
    x ^ 2 ≤ 1 / 4 := by nlinarith

private theorem four_half_corner {x y z w : ℚ}
    (hx : -(1 / 2 : ℚ) ≤ x ∧ x < 1 / 2)
    (hy : -(1 / 2 : ℚ) ≤ y ∧ y < 1 / 2)
    (hz : -(1 / 2 : ℚ) ≤ z ∧ z < 1 / 2)
    (hw : -(1 / 2 : ℚ) ≤ w ∧ w < 1 / 2)
    (hs : 1 ≤ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) :
    x = -1 / 2 ∧ y = -1 / 2 ∧ z = -1 / 2 ∧ w = -1 / 2 := by
  have hx2 := half_interval_sq hx.1 hx.2
  have hy2 := half_interval_sq hy.1 hy.2
  have hz2 := half_interval_sq hz.1 hz.2
  have hw2 := half_interval_sq hw.1 hw.2
  have hx' : x ^ 2 = 1 / 4 := by linarith
  have hy' : y ^ 2 = 1 / 4 := by linarith
  have hz' : z ^ 2 = 1 / 4 := by linarith
  have hw' : w ^ 2 = 1 / 4 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem halfIntegralQuaternion_mem (a b c d : ℤ) :
    (⟨(a : ℚ) - 1 / 2, (b : ℚ) - 1 / 2, (c : ℚ) - 1 / 2,
      (d : ℚ) - 1 / 2⟩ : ℍ[ℚ]) ∈ hurwitzOrder := by
  refine ⟨a - d, b - d, c - d, 2 * d - 1, ?_⟩
  apply Quaternion.ext <;> dsimp [hurwitzCoordinates] <;> push_cast <;> ring

theorem hurwitz_approximation (x : ℍ[ℚ]) :
    ∃ q : hurwitzOrder, Quaternion.normSq (x - (q : ℍ[ℚ])) < 1 := by
  let a : ℤ := ⌊x.re + 1 / 2⌋
  let b : ℤ := ⌊x.imI + 1 / 2⌋
  let c : ℤ := ⌊x.imJ + 1 / 2⌋
  let d : ℤ := ⌊x.imK + 1 / 2⌋
  let q : ℍ[ℚ] := ⟨(a : ℚ), (b : ℚ), (c : ℚ), (d : ℚ)⟩
  have hq : q ∈ hurwitzOrder := integralQuaternion_mem a b c d
  by_cases hsmall : Quaternion.normSq (x - q) < 1
  · exact ⟨⟨q, hq⟩, hsmall⟩
  · have hnorm : Quaternion.normSq (x - q) =
        (x.re - (a : ℚ)) ^ 2 + (x.imI - (b : ℚ)) ^ 2 +
          (x.imJ - (c : ℚ)) ^ 2 + (x.imK - (d : ℚ)) ^ 2 := by
      rw [Quaternion.normSq_def']
      rw [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub]
    rw [hnorm] at hsmall
    obtain ⟨hA, hB, hC, hD⟩ := four_half_corner (floor_half_bounds x.re)
      (floor_half_bounds x.imI) (floor_half_bounds x.imJ) (floor_half_bounds x.imK)
      (le_of_not_gt hsmall)
    have hx : x = ⟨(a : ℚ) - 1 / 2, (b : ℚ) - 1 / 2,
        (c : ℚ) - 1 / 2, (d : ℚ) - 1 / 2⟩ := by
      apply Quaternion.ext <;> dsimp only
      · change x.re - a = -1 / 2 at hA
        linarith
      · change x.imI - b = -1 / 2 at hB
        linarith
      · change x.imJ - c = -1 / 2 at hC
        linarith
      · change x.imK - d = -1 / 2 at hD
        linarith
    have hxmem : x ∈ hurwitzOrder := hx ▸ halfIntegralQuaternion_mem a b c d
    refine ⟨⟨x, hxmem⟩, ?_⟩
    simp only [sub_self, map_zero, zero_lt_one]

end Erdos941
