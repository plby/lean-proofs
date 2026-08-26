import ErdosProblems.Erdos489.CoprimePairSupply

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- A convenient integral form of the progression coprime-pair estimate.  The
loose constants isolate all endpoint losses: once `G ≥ 256 C²` and
`Q²Y ≥ 64 C²`, any `G/C`-point progression set has enough coprime ordered
pairs to pay for `G²` with multiplier `16 C²`. -/
theorem progression_many_coprime_pairs
    (S : Finset ℕ) (L G Q Y C : ℕ)
    (hQ : 0 < Q) (hY : 0 < Y) (hC : 0 < C)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q)
    (hcard : G / C ≤ S.card)
    (hG : 256 * C ^ 2 ≤ G)
    (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y) :
    G ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs S).card := by
  let q := G / C
  let d : ℝ := 1 / (2 * (C : ℝ))
  have hC1 : 1 ≤ C := hC
  have hCG : C ≤ G := by
    calc
      C ≤ 256 * C ^ 2 := by nlinarith
      _ ≤ G := hG
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hC).2 (by simpa using hCG)
  have hGlt : G < C * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ G hC
  have hGle2Cq : G ≤ 2 * C * q := by
    have hstep : C * (q + 1) ≤ C * (2 * q) :=
      Nat.mul_le_mul_left C (by omega)
    have := (Nat.le_of_lt hGlt).trans hstep
    nlinarith
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hC
  have hqbound : d * (G : ℝ) ≤ (q : ℝ) := by
    have hcast : (G : ℝ) ≤ ((2 * C * q : ℕ) : ℝ) := by exact_mod_cast hGle2Cq
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    dsimp [d]
    rw [show (1 / (2 * (C : ℝ))) * (G : ℝ) =
      (G : ℝ) / (2 * (C : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C)).2
    nlinarith
  have hcardR : (q : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (show q ≤ S.card by simpa [q] using hcard)
  have hdcard : d * (G : ℝ) ≤ (S.card : ℝ) := hqbound.trans hcardR
  have h4C : 4 * C ≤ G := by
    have : 4 * C ≤ 256 * C ^ 2 := by nlinarith
    exact this.trans hG
  have hdlarge : 2 ≤ d * (G : ℝ) := by
    have h4CR : (4 * C : ℕ) ≤ G := h4C
    have hcast : (4 : ℝ) * C ≤ G := by exact_mod_cast h4CR
    dsimp [d]
    rw [show (1 / (2 * (C : ℝ))) * (G : ℝ) =
      (G : ℝ) / (2 * (C : ℝ)) by ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)).2
    nlinarith
  have hpair := progression_coprimeOrderedPairs_cast_lower
    S L G Q Y d hQ hY hinterval hcong hsmall
    (by dsimp [d]; positivity) hdcard hdlarge
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hCYR : (64 * C ^ 2 : ℕ) ≤ Q ^ 2 * Y := hCY
  have hCYcast : (64 : ℝ) * (C : ℝ) ^ 2 ≤
      (Q : ℝ) ^ 2 * (Y : ℝ) := by exact_mod_cast hCYR
  have hquadcoeff : (2 : ℝ) / ((Q : ℝ) ^ 2 * (Y : ℝ)) ≤
      1 / (32 * (C : ℝ) ^ 2) := by
    calc
      (2 : ℝ) / ((Q : ℝ) ^ 2 * (Y : ℝ)) ≤
          2 / (64 * (C : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity)
          (by positivity) hCYcast
      _ = 1 / (32 * (C : ℝ) ^ 2) := by field_simp <;> ring
  have hquad : 2 * (G : ℝ) ^ 2 /
      ((Q : ℝ) ^ 2 * (Y : ℝ)) ≤
      (G : ℝ) ^ 2 / (32 * (C : ℝ) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right hquadcoeff
      (sq_nonneg (G : ℝ))
    ring_nf at hm ⊢
    exact hm
  have hGcast : (256 : ℝ) * (C : ℝ) ^ 2 ≤ (G : ℝ) := by
    exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := lt_of_lt_of_le (by positivity) hGcast
  have hend : 2 * ((G + 1 : ℕ) : ℝ) ≤
      (G : ℝ) ^ 2 / (64 * (C : ℝ) ^ 2) := by
    have hsucc : (((G + 1 : ℕ) : ℝ)) ≤ 2 * (G : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      have : (1 : ℝ) ≤ G := by exact_mod_cast (show 1 ≤ G by omega)
      linarith
    have hscaled := mul_le_mul_of_nonneg_right hGcast
      (show (0 : ℝ) ≤ G by positivity)
    have hfour : 4 * (G : ℝ) ≤
        (G : ℝ) ^ 2 / (64 * (C : ℝ) ^ 2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * C ^ 2)).2
      nlinarith
    linarith
  have hmain : d ^ 2 * (G : ℝ) ^ 2 / 2 =
      (G : ℝ) ^ 2 / (8 * (C : ℝ) ^ 2) := by
    dsimp [d]
    field_simp <;> ring
  have hlower : (G : ℝ) ^ 2 / (16 * (C : ℝ) ^ 2) ≤
      ((coprimeOrderedPairs S).card : ℝ) := by
    rw [hmain] at hpair
    ring_nf at hpair hquad hend ⊢
    linarith
  have hcross : (G : ℝ) ^ 2 ≤
      (16 * (C : ℝ) ^ 2) * ((coprimeOrderedPairs S).card : ℝ) := by
    have h := (div_le_iff₀
      (by positivity : (0 : ℝ) < 16 * C ^ 2)).mp hlower
    simpa [mul_comm] using h
  exact_mod_cast hcross

end Erdos489
