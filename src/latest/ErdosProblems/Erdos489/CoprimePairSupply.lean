import ErdosProblems.Erdos489.ProgressionCoprimePairs

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Ordered pairs of distinct coprime elements. -/
def coprimeOrderedPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.offDiag.filter fun z => Nat.Coprime z.1 z.2

lemma noncoprimeOrderedPairs_eq_offDiag_filter (S : Finset ℕ) :
    noncoprimeOrderedPairs S =
      S.offDiag.filter fun z => ¬Nat.Coprime z.1 z.2 := by
  ext z
  simp only [noncoprimeOrderedPairs, Finset.mem_filter,
    Finset.mem_product, Finset.mem_offDiag]
  tauto

/-- Good and bad ordered pairs partition the off-diagonal. -/
theorem coprime_add_noncoprime_card (S : Finset ℕ) :
    (coprimeOrderedPairs S).card + (noncoprimeOrderedPairs S).card =
      S.card * (S.card - 1) := by
  rw [noncoprimeOrderedPairs_eq_offDiag_filter]
  have h := Finset.card_filter_add_card_filter_not
    (s := S.offDiag) (fun z : ℕ × ℕ => Nat.Coprime z.1 z.2)
  rw [Finset.offDiag_card] at h
  simpa [coprimeOrderedPairs, Nat.mul_sub_left_distrib] using h

/-- If `S` has at least `dG` points and `dG≥2`, then at least
`d²G²/2-B` ordered pairs are coprime whenever at most `B` are bad. -/
theorem coprimeOrderedPairs_cast_lower_of_card
    (S : Finset ℕ) (G : ℕ) (d B : ℝ)
    (hd : 0 ≤ d)
    (hcard : d * (G : ℝ) ≤ (S.card : ℝ))
    (hlarge : 2 ≤ d * (G : ℝ))
    (hbad : ((noncoprimeOrderedPairs S).card : ℝ) ≤ B) :
    d ^ 2 * (G : ℝ) ^ 2 / 2 - B ≤
      ((coprimeOrderedPairs S).card : ℝ) := by
  have hm2 : 2 ≤ S.card := by exact_mod_cast hlarge.trans hcard
  have hpart := coprime_add_noncoprime_card S
  have hpartR : ((coprimeOrderedPairs S).card : ℝ) +
      ((noncoprimeOrderedPairs S).card : ℝ) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hpart
    norm_num only [Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ S.card by omega), Nat.cast_one] at hcast
    exact hcast
  have hm : d * (G : ℝ) ≤ (S.card : ℝ) := hcard
  have hdG : 0 ≤ d * (G : ℝ) := by positivity
  have hm0 : 0 ≤ (S.card : ℝ) := by positivity
  have hquad : d ^ 2 * (G : ℝ) ^ 2 / 2 ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hsquare : (d * (G : ℝ)) ^ 2 ≤ (S.card : ℝ) ^ 2 :=
      (sq_le_sq₀ hdG hm0).2 hm
    nlinarith
  linarith

/-- Explicit affine-progression corollary: a linearly large set has a
quadratic supply of coprime ordered pairs, up to the `Q,Y` union-bound error. -/
theorem progression_coprimeOrderedPairs_cast_lower
    (S : Finset ℕ) (L G Q Y : ℕ) (d : ℝ)
    (hQ : 0 < Q) (hY : 0 < Y)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q)
    (hd : 0 ≤ d) (hcard : d * (G : ℝ) ≤ (S.card : ℝ))
    (hlarge : 2 ≤ d * (G : ℝ)) :
    d ^ 2 * (G : ℝ) ^ 2 / 2 -
        (2 * (G : ℝ) ^ 2 / ((Q : ℝ) ^ 2 * (Y : ℝ)) +
          2 * ((G + 1 : ℕ) : ℝ)) ≤
      ((coprimeOrderedPairs S).card : ℝ) := by
  apply coprimeOrderedPairs_cast_lower_of_card S G d _ hd hcard hlarge
  exact noncoprimeOrderedPairs_cast_le_progression
    S L G Q Y hQ hY hinterval hcong hsmall

end Erdos489
