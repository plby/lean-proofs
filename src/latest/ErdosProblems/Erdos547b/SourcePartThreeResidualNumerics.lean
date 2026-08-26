/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54AppendixA

/-!
# Source-faithful residual arithmetic for the Part-3 owner loop

Occupied counts include permanent deletions. Root degrees are tested on
the actual live endpoints, not inferred from whole-pair degrees. The
three-alternative invariant pays both Appendix-A.2 slot inequalities.
-/

noncomputable section

namespace Erdos547b.ZhaoSourcePartThreeResidualNumerics

/-- The symmetric occupied-side invariant, with the epsilon margins
needed by permanent cleanup and integer root reserves. -/
def ResidualInvariant (dx dy N error x y : ℝ) : Prop :=
  |x - y| ≤ 3 * error ∨
    (dx * N - 9 * error ≤ x ∧ dx * N - 9 * error ≤ y) ∨
    (dy * N - 9 * error ≤ x ∧ dy * N - 9 * error ≤ y)

theorem ResidualInvariant.swap {dx dy N error x y : ℝ}
    (h : ResidualInvariant dx dy N error x y) :
    ResidualInvariant dy dx N error y x := by
  rcases h with h | h | h
  · exact Or.inl (by rwa [abs_sub_comm])
  · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
  · exact Or.inr (Or.inl ⟨h.2, h.1⟩)

/-- The bilinear expression is minimized at an endpoint of the density
interval; splitting at half occupancy proves the uniform lower bound. -/
theorem density_occupancy_lower (N lambda d x : ℝ)
    (_hlambda : 0 ≤ lambda) (hlambdaHalf : lambda ≤ 1 / 2)
    (hdlo : lambda ≤ d) (hdhi : d ≤ 1 - lambda)
    (hx : 0 ≤ x) (hxN : x ≤ N) :
    lambda * N ≤ x + d * N - 2 * d * x := by
  by_cases hhalf : 2 * x ≤ N
  · have hmono := mul_nonneg (sub_nonneg.mpr hdlo) (sub_nonneg.mpr hhalf)
    have hsmall := mul_nonneg (by linarith only [hlambdaHalf] : 0 ≤ 1 - 2 * lambda) hx
    nlinarith only [hmono, hsmall]
  · have hmono := mul_nonneg (sub_nonneg.mpr hdhi)
      (by linarith only [hhalf] : 0 ≤ 2 * x - N)
    have hsmall := mul_nonneg (by linarith only [hlambdaHalf] : 0 ≤ 1 - 2 * lambda)
      (sub_nonneg.mpr hxN)
    nlinarith only [hmono, hsmall]

/-- The total mass leaves the two root-pool slot reserve. No balanced
occupied-side assumption is needed for this inequality. -/
theorem root_slots_real (N lambda dx dy error reserve x y f P Q : ℝ)
    (hN : 0 ≤ N) (hlambda : 0 ≤ lambda) (hlambdaHalf : lambda ≤ 1 / 2)
    (hdxlo : lambda ≤ dx) (hdxhi : dx ≤ 1 - lambda)
    (hdylo : lambda ≤ dy) (hdyhi : dy ≤ 1 - lambda)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hy : 0 ≤ y) (hyN : y ≤ N)
    (hreserve : 0 ≤ reserve)
    (hP : dx * (N - x) - 2 * error ≤ P)
    (hQ : dy * (N - y) - 2 * error ≤ Q)
    (hbudget : x + y + f ≤ (dx + dy + lambda) * N - 2 * reserve - 24 * error) :
    f + 16 * error ≤ 2 * P + 2 * Q := by
  have hxLower := density_occupancy_lower N lambda dx x hlambda hlambdaHalf hdxlo hdxhi hx hxN
  have hyLower := density_occupancy_lower N lambda dy y hlambda hlambdaHalf hdylo hdyhi hy hyN
  have hlambdaN := mul_nonneg hlambda hN
  nlinarith only [hxLower, hyLower, hlambdaN, hP, hQ, hbudget, hreserve]

private theorem ordered_side_lower (N lambda dx dy error x y P Q : ℝ)
    (hN : 0 ≤ N) (hlambda : 0 ≤ lambda) (herror : 0 ≤ error)
    (hdxlo : lambda ≤ dx) (hdxhi : dx ≤ 1 - lambda)
    (hdylo : lambda ≤ dy) (hdyhi : dy ≤ 1 - lambda)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hy : 0 ≤ y) (_hyx : y ≤ x)
    (hinv : ResidualInvariant dx dy N error x y)
    (hP : dx * (N - x) - 2 * error ≤ P)
    (hQ : dy * (N - y) - 2 * error ≤ Q) :
    (dx + dy + lambda) * N - 11 * error ≤ x + y + min P Q + (N - x) := by
  have hdx : 0 ≤ dx := hlambda.trans hdxlo
  have hdy : 0 ≤ dy := hlambda.trans hdylo
  have hdxN := mul_nonneg (by linarith only [hdxhi, hlambda] : 0 ≤ 1 - dx) hx
  have hdyN := mul_nonneg (by linarith only [hdyhi, hlambda] : 0 ≤ 1 - dy) hy
  have hdxBound := mul_le_mul_of_nonneg_right hdxhi hN
  have hdyBound := mul_le_mul_of_nonneg_right hdyhi hN
  by_cases hpq : P ≤ Q
  · rw [min_eq_left hpq]
    rcases hinv with hbal | hhigh | hhigh
    · have hdiff := (abs_le.mp hbal).2
      nlinarith only [hP, hdiff, hdxN, hdyBound, herror]
    · have hnonneg := mul_nonneg hdx (sub_nonneg.mpr hxN)
      nlinarith only [hP, hhigh.2, hnonneg, hdyBound]
    · have hnonneg := mul_nonneg hdx (sub_nonneg.mpr hxN)
      nlinarith only [hP, hhigh.2, hnonneg, hdxBound]
  · rw [min_eq_right (le_of_not_ge hpq)]
    nlinarith only [hQ, hdyN, hdxBound, herror]

/-- The three alternatives pay the smaller-live-side slot inequality.
The endpoints are ordered only locally for this proof. -/
theorem side_slots_real (N lambda dx dy error reserve x y f P Q : ℝ)
    (hN : 0 ≤ N) (hlambda : 0 ≤ lambda) (herror : 0 ≤ error)
    (hdxlo : lambda ≤ dx) (hdxhi : dx ≤ 1 - lambda)
    (hdylo : lambda ≤ dy) (hdyhi : dy ≤ 1 - lambda)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hy : 0 ≤ y) (hyN : y ≤ N)
    (hinv : ResidualInvariant dx dy N error x y)
    (hP : dx * (N - x) - 2 * error ≤ P)
    (hQ : dy * (N - y) - 2 * error ≤ Q)
    (hbudget : x + y + f ≤ (dx + dy + lambda) * N - 2 * reserve - 24 * error) :
    f + 2 * reserve + 13 * error ≤ min P Q + min (N - x) (N - y) := by
  rcases le_total y x with hyx | hxy
  · rw [min_eq_left (sub_le_sub_left hyx N)]
    have hside := ordered_side_lower N lambda dx dy error x y P Q hN hlambda herror
      hdxlo hdxhi hdylo hdyhi hx hxN hy hyx hinv hP hQ
    linarith only [hside, hbudget]
  · rw [min_eq_right (sub_le_sub_left hxy N)]
    have hside := ordered_side_lower N lambda dy dx error y x Q P hN hlambda herror
      hdylo hdyhi hdxlo hdxhi hy hyN hx hxy hinv.swap hQ hP
    rw [min_comm Q P] at hside
    linarith only [hside, hbudget]

/-- Live endpoints retain the gamma reserve before any current root is
chosen. Thus live-set typicality can be invoked without circularly using
the chosen root's degree inequalities to establish the set-size gate. -/
theorem live_reserve_of_source_budget (N lambda dx dy error reserve x y f : ℝ)
    (hN : 0 ≤ N) (hlambda : 0 ≤ lambda) (herror : 0 ≤ error)
    (hdxlo : lambda ≤ dx) (hdxhi : dx ≤ 1 - lambda)
    (hdylo : lambda ≤ dy) (hdyhi : dy ≤ 1 - lambda)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hy : 0 ≤ y) (hyN : y ≤ N) (hf : 0 ≤ f)
    (hinv : ResidualInvariant dx dy N error x y)
    (hbudget : x + y + f ≤ (dx + dy + lambda) * N - 2 * reserve - 24 * error) :
    reserve ≤ N - x ∧ reserve ≤ N - y := by
  let P := dx * (N - x) - 2 * error
  let Q := dy * (N - y) - 2 * error
  have hside := side_slots_real N lambda dx dy error reserve x y f P Q hN hlambda herror
    hdxlo hdxhi hdylo hdyhi hx hxN hy hyN hinv le_rfl le_rfl hbudget
  have hPX : P ≤ N - x := by
    have hm := mul_le_mul_of_nonneg_right
      (show dx ≤ 1 by linarith only [hdxhi, hlambda]) (sub_nonneg.mpr hxN)
    dsimp only [P]
    linarith only [hm, herror]
  have hQY : Q ≤ N - y := by
    have hm := mul_le_mul_of_nonneg_right
      (show dy ≤ 1 by linarith only [hdyhi, hlambda]) (sub_nonneg.mpr hyN)
    dsimp only [Q]
    linarith only [hm, herror]
  constructor
  · have hp := (min_le_left P Q).trans hPX
    have hx' := min_le_left (N - x) (N - y)
    linarith only [hside, hp, hx', hf, herror]
  · have hq := (min_le_right P Q).trans hQY
    have hy' := min_le_right (N - x) (N - y)
    linarith only [hside, hq, hy', hf, herror]

end Erdos547b.ZhaoSourcePartThreeResidualNumerics

#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.density_occupancy_lower
#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.root_slots_real
#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.side_slots_real
#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.live_reserve_of_source_budget
