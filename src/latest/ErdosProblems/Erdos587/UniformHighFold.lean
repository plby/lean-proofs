import ErdosProblems.Erdos587.HighFoldDoubling

/-!
Uniform large-scale doubling from interval containment alone. The constants
depend only on the polynomial ambient exponent, not on the set or scale.
-/

open scoped Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem exists_uniform_highFold_doubling (b : ℕ) :
    ∃ C K : ℕ, 0 < C ∧ 0 < K ∧ ∀ (A : Finset ℤ) (N t : ℕ),
      A ⊆ Finset.Icc 0 (N : ℤ) → (0 : ℤ) ∈ A → 2 ≤ A.card → 0 < t →
      N ≤ (2 ^ t) ^ b → C ≤ 2 ^ t → ∀ H : ℕ, C * 2 ^ (t + t) ≤ H →
        (H • A + H • A).card ≤ K * (H • A).card := by
  classical
  let D := freimanTSizeFactor (2 ^ (b + 3)) 2
  let loss (d : ℕ) := nvDenseProperFactor D d * (nvDenseCount D d + 1) ^ d
  let C₀ := (Finset.range (b + 2)).sup (fun d => loss d + nvDenseCount D d)
  let C := 2 * D + 1 + C₀
  let K₀ := (Finset.range (b + 2)).sup (highFoldDoublingConstant D)
  let K := max 1 K₀
  have hC : 0 < C := by dsimp [C]; omega
  have hK : 0 < K := lt_of_lt_of_le (by omega) (le_max_left _ _)
  refine ⟨C, K, hC, hK, ?_⟩
  intro A N t hA hzero hcard ht hN hscale H hH
  have hscale' : 2 * D < 2 ^ t := by dsimp [C] at hscale; omega
  obtain ⟨k, htk, hkt, P, hPrank, hpos, hproper, _hPzero, hAP, hbox⟩ :=
    exists_polynomial_window_lowRank_model A N b t hA hzero ht hN hscale'
  have hdim : 0 < P.rank := by
    by_contra hn
    have hz : P.rank = 0 := by omega
    have hc := (Finset.card_le_card hAP).trans P.card_carrier_le_box
    change A.card ≤ P.boxCard at hc
    let : IsEmpty (Fin P.rank) := ⟨fun i => by have hi := i.isLt; omega⟩
    simp [GeneralizedAP.boxCard] at hc
    omega
  have hD : 0 < D := by
    have hp : 0 < (P.dilate (2 ^ k)).boxCard :=
      Finset.prod_pos (fun _ _ => Nat.succ_pos _)
    change (P.dilate (2 ^ k)).boxCard ≤ D * ((2 ^ k) • A).card at hbox
    by_contra hn
    have hz : D = 0 := by omega
    rw [hz, zero_mul] at hbox
    omega
  have hmem : P.rank ∈ Finset.range (b + 2) := Finset.mem_range.mpr (by omega)
  have hlocal : loss P.rank + nvDenseCount D P.rank ≤ C₀ :=
    Finset.le_sup (f := fun d => loss d + nvDenseCount D d) hmem
  have hClocal : C₀ ≤ C := by dsimp [C]; omega
  have hF : loss P.rank ≤ 2 ^ k :=
    (Nat.le_add_right _ _).trans (hlocal.trans (hClocal.trans
      (hscale.trans (Nat.pow_le_pow_right (by omega) htk))))
  have hq : nvDenseCount D P.rank ≤ C :=
    (Nat.le_add_left _ _).trans (hlocal.trans hClocal)
  have hH' : nvDenseCount D P.rank * 2 ^ k ≤ H := by
    exact (Nat.mul_le_mul hq (Nat.pow_le_pow_right (by omega) hkt.le)).trans hH
  have hsmall := highFold_doubling_of_dense_model A P hzero hAP hpos hdim
    (2 ^ k) D (by positivity) hD hproper hbox hF H hH'
  have hKlocal : highFoldDoublingConstant D P.rank ≤ K :=
    (Finset.le_sup (f := highFoldDoublingConstant D) hmem).trans (le_max_right 1 K₀)
  exact hsmall.trans (Nat.mul_le_mul_right _ hKlocal)

end Erdos587.CFP
