import ErdosProblems.Erdos1141.BurgessBlocks

/-!
# Quadratic-character cancellation above the quarter-power scale
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem eventually_quarter_block_cancellation {c : ℝ}
    (hc : 1 / 4 < c) (hc' : c < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), primeModulus s = q → ∀ M : ℕ,
        |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, productChar s hs (M + i : ℕ)| ≤
          (q : ℝ) ^ (c - η) := by
  let e := c - 1 / 4
  have he : 0 < e := sub_pos.mpr hc
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / e)
  let v : ℝ := 1 / (2 * (k + 1 : ℝ))
  let u : ℝ := c - v - e / 4
  let η : ℝ := e / (64 * (k + 2 : ℝ))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hv0 : 0 < v := by dsimp [v]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hveq : v * (k + 1 : ℝ) = 1 / 2 := by dsimp [v]; field_simp
  have hηeq : η * (64 * (k + 2 : ℝ)) = e := by dsimp [η]; field_simp
  have hvsmall : v < e / 4 := by
    have hek : 2 < (k : ℝ) * e := (div_lt_iff₀ he).mp hk
    dsimp [v]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (k + 1 : ℝ))).mpr
    nlinarith only [hek, he]
  have hηsmall : η < e / 4 := by
    have hkη : 0 ≤ (k : ℝ) * η := mul_nonneg hk0 hη.le
    nlinarith only [hηeq, hkη, hη]
  have hu : 0 < u := by dsimp [u, e] at *; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; dsimp [e] at he; linarith
  have huδ : u ≤ c + η := by dsimp [u]; linarith
  have huv : u + v < c - η := by dsimp [u]; linarith
  have huc : u + c < 1 := by dsimp [u]; linarith
  have hgap : (c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * η <
      (u + v + c - η - η) * (2 * (k + 1) : ℕ) := by
    have hid : (u + v + c - η - η) * (2 * (k + 1) : ℕ) -
        ((c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * η) =
        2 * e - v - e / 4 - (4 * (k + 1 : ℝ) + 3) * η := by
      push_cast
      dsimp [u, e]
      nlinarith only [hveq]
    have hηloss : (4 * (k + 1 : ℝ) + 3) * η < e / 16 := by
      nlinarith only [hηeq, hη]
    apply sub_pos.mp
    rw [hid]
    nlinarith only [he, hvsmall, hηloss]
  exact ⟨η, hη, eventually_power_block_bound k (by linarith) hu hv0.le hη hη
    hu1 huδ huv huc hveq hgap⟩

end Pollack17.Burgess
