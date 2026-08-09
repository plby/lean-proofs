import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2BluePowerBounds

/-!
# Blue-fit bound for the third-round second backward interval

This file connects the exact degree-49 blue-fit certificate to its
semantic upper bound on `[0.6, 1.0]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Bounds

noncomputable section

open BackwardBookRound3Back2Certificate

lemma blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    0 < backwardBlueUpperRound3Back2 z ∧
      backwardBlueUpperRound3Back2 z < 1 := by
  let u : ℝ := (1000 * z - 600) / 400
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hfit :
      backwardBlueUpperRound3Back2 z =
        
        (23511361296473 / 62500000000000) * (1 - u) ^ 4 +
          (101351000279239 / 62500000000000) * u * (1 - u) ^ 3 +
          (32106485575269 / 12500000000000) * u ^ 2 * (1 - u) ^ 2 +
          (4481062767481 / 2500000000000) * u ^ 3 * (1 - u) +
          (23312544711 / 50000000000) * u ^ 4 := by
    dsimp [u, backwardBlueUpperRound3Back2]
    ring
  have hone :
      1 - backwardBlueUpperRound3Back2 z =
        
        (38988638703527 / 62500000000000) * (1 - u) ^ 4 +
          (148648999720761 / 62500000000000) * u * (1 - u) ^ 3 +
          (42893514424731 / 12500000000000) * u ^ 2 * (1 - u) ^ 2 +
          (5518937232519 / 2500000000000) * u ^ 3 * (1 - u) +
          (26687455289 / 50000000000) * u ^ 4 := by
    dsimp [u, backwardBlueUpperRound3Back2]
    ring
  constructor
  · rw [hfit]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u :=
        lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity
  · rw [← sub_pos, hone]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u :=
        lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity

lemma raw_blue_le_fit {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    backwardBlueRawUpper (3 / 100) z ≤
      backwardBlueUpperRound3Back2 z := by
  have hzplus : 0 < 1 + z := by
    nlinarith [hz.1]
  rw [← sub_nonneg, blue_fit_sub_raw_identity hzplus]
  exact div_nonneg
    (div_nonneg (blue_power_positive hz).le (by positivity))
    (by positivity)

end

end BackwardBookRound3Back2Bounds
end Arxiv2407_19026
