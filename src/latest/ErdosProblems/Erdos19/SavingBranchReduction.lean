import ErdosProblems.Erdos19.LargeMediumDichotomy
import ErdosProblems.Erdos19.LowIncidenceStarCompletion
import ErdosProblems.Erdos19.HighRankVolume

/-! # Eliminating the projective branch

The dense-window branch is now fully colored, including its small edges.
Only the alternative with a saved palette remains in the full EFL problem.
This theorem is a reduction, not the final asymptotic EFL theorem.
-/

namespace Erdos19.SetHypergraph

theorem eventually_colorable_or_controlled_saving (B₀ : ℕ) :
    ∃ b : ℕ, 655360 < b ∧ B₀ ≤ b ∧
      ∀ a u ell : ℕ, 512 ≤ a → 0 < u →
      ∃ R N : ℕ, ell * mediumMinimumSize a b ≤ R ∧ mediumMinimumSize a b < R ∧
        ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
          (∀ e : H, 2 ≤ e.1.ncard) →
          H.EdgeColorable n ∨
          (∃ color : (H.rankAtLeast (mediumMinimumSize a b)).EdgeColoring
              (Fin (n - n / (4 * b ^ 4))),
            ∃ palette : Finset (Fin (n - n / (4 * b ^ 4))),
              palette.card = n / (4 * b ^ 4) ∧
              (H.rankAtLeast (mediumMinimumSize a b)).HasControlledMediumPalette
                color palette R (16 * (n / u)) (n / a)) := by
  obtain ⟨b, hbt, hbB, hdichotomy⟩ :=
    eventually_large_medium_dichotomy 8192 (by norm_num) (max B₀ 655361)
  have hb : 655360 < b := by have := (le_max_right _ _).trans hbB; omega
  have hbpos : 0 < b := by omega
  refine ⟨b, hb, (le_max_left _ _).trans hbB, ?_⟩
  intro a u ell ha hu
  let r₁ := mediumMinimumSize a b
  have hr₁ : 3 ≤ r₁ := by
    have hb4 : 0 < b ^ 4 := pow_pos hbpos _
    dsimp only [r₁, mediumMinimumSize]
    nlinarith only [ha, hb4]
  obtain ⟨ell₀, N₀, _, hcomplete⟩ := eventually_complete_low_incidence_small_edges r₁ hr₁
  obtain ⟨R, N₁, hR, hrR, hN₁⟩ := hdichotomy a u (max ell ell₀) (by omega) hu
  have hellR : ell * r₁ ≤ R := (Nat.mul_le_mul_right r₁ (le_max_left _ _)).trans hR
  have hell₀R : ell₀ * r₁ ≤ R := (Nat.mul_le_mul_right r₁ (le_max_right _ _)).trans hR
  refine ⟨R, max N₀ (max N₁ 1), hellR, hrR, ?_⟩
  intro n hn H hlinear hmin
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnpos : 0 < n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  let L := H.rankAtLeast r₁
  rcases hN₁ n hn₁ L (H.rankAtLeast_linear hlinear r₁) (fun e ↦ e.2.2) with
    hsaving | ⟨color, palette, hcard, hcontrol, hcover, W, r, _, _, hvolume⟩
  · exact Or.inr hsaving
  · left
    apply hcomplete n hn₀ H hlinear hmin color palette
    · rw [hcard]
      have hb4 : 4 ^ 4 ≤ b ^ 4 := Nat.pow_le_pow_left (by omega : 4 ≤ b) 4
      apply Nat.div_le_div_left _ (by norm_num : 0 < 128)
      norm_num at hb4
      nlinarith only [hb4]
    · intro x
      have h16 := scaled_floor_le_div n 16 512 (by norm_num)
      have h2 := scaled_floor_le_div n 2 256 (by norm_num)
      norm_num only [Nat.reduceMul] at h16 h2
      have haDiv : n / a ≤ n / 512 := Nat.div_le_div_left ha (by norm_num)
      exact (hcover x).trans (by omega)
    · intro e he
      apply hell₀R.trans
      by_contra h
      exact he (hcontrol.1 e (Nat.lt_of_not_ge h))
    · exact (H.small_rank_incidence_of_dense_window n r₁ b 65536 hnpos (by omega)
        (by omega) hlinear hmin W hvolume).le

#print axioms eventually_colorable_or_controlled_saving

end Erdos19.SetHypergraph
