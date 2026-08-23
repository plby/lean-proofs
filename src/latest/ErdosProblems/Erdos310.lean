/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 310.
https://www.erdosproblems.com/forum/thread/310

Informal authors:
- Thomas Bloom
- Bhavik Mehta

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos310.md
-/
/-
Erdős Problem 310: bounded-denominator reciprocal subsums of dense finite sets.

The mathematical proof and Leanization plan are in `tex/310.tex` at the
repository root.  The analytic input below is Bloom's theorem, already proved
in the repository's `UnitFractions` development.
-/

import UnitFractions.ErdosProblems

open Filter Real
open scoped ArithmeticFunction.omega BigOperators

namespace Erdos310

open Finset

/-- The explicit reciprocal sum used in the problem is `UnitFractions.rec_sum`. -/
lemma sum_one_div_eq_recSum (S : Finset ℕ) :
    (∑ n ∈ S, (1 / n : ℚ)) = UnitFractions.rec_sum S := by
  simp [UnitFractions.rec_sum]

/--
Finite form of the Bloom--Mehta bounded-denominator extraction argument.

For fixed positive `D`, sufficiently large finite sets of density strictly
greater than `1 / D` contain a reciprocal subsum `1 / d`, where `d` belongs
to an interval depending only on `D`.
-/
theorem bloom_finite_bounded_denominator (D : ℝ) (hD : 0 < D) :
    ∃ N₀ : ℕ, ∃ y z : ℝ,
      1 ≤ y ∧ 0 ≤ z ∧
        ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A ⊆ range N →
          (N : ℝ) / D < A.card →
            ∃ d ∈ Icc ⌈y⌉₊ ⌊z⌋₊,
              ∃ S : Finset ℕ,
                S ⊆ A ∧ S.sum (fun n => (1 / n : ℚ)) = 1 / d := by
  classical
  rcases UnitFractions.final_large_N D hD with ⟨y, z, h1y, hyz, h0z, hfinal⟩
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hfinal.and UnitFractions.technical_prop)
  refine ⟨N₀, y, z, h1y, h0z.le, ?_⟩
  intro N hNN₀ A hAN hAcard
  have hlargeN := (hN₀ N hNN₀).1
  have htech := (hN₀ N hNN₀).2
  dsimp at hlargeN
  have hzN := hlargeN.2.2.2.2.2.1
  have hyN := hlargeN.2.2.2.2.2.2
  let A' := A
  have hA'card : (N : ℝ) / D < A'.card := by
    simpa [A'] using hAcard
  let M := (N : ℝ) ^ ((1 : ℝ) - 8 / log (log (N : ℝ)))
  let A0 := A'.filter fun n : ℕ =>
    (n : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))
  have hA0card : (A0.card : ℝ) < (N : ℝ) / (5 * D) := by
    calc
      (A0.card : ℝ) ≤
          ((range ⌈(N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))⌉₊).card : ℝ) := by
        norm_cast
        refine Finset.card_le_card ?_
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_range, Nat.lt_ceil]
        exact hn.2
      _ < (N : ℝ) / (5 * D) := by
        rw [Finset.card_range]
        refine lt_trans (Nat.ceil_lt_add_one ?_) hlargeN.2.1
        exact Real.rpow_nonneg (le_of_lt hlargeN.1) _
  let A1 := A'.filter fun n ↦ ∃ q : ℕ, IsPrimePow q ∧ M < q ∧ q ∣ n
  have hA1card : (A1.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.1 A' ?_
    simpa [A'] using hAN
  let A2 := A'.filter fun n ↦
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
      (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))
  have hA2card : (A2.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.1 A' ?_
    simpa [A'] using hAN
  let A3 := A'.filter fun n ↦
    ¬ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧
      4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)
  have hA3card : (A3.card : ℝ) ≤ (N : ℝ) / (5 * D) := by
    refine hlargeN.2.2.2.2.1 A' ?_
    simpa [A'] using hAN
  let A'' := A' \ (A0 ∪ A1 ∪ A2 ∪ A3)
  have hUnionSub : A0 ∪ A1 ∪ A2 ∪ A3 ⊆ A' := by
    intro n hn
    rcases Finset.mem_union.mp hn with h012 | h3
    · rcases Finset.mem_union.mp h012 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · exact (Finset.mem_filter.mp h0).1
        · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · exact (Finset.mem_filter.mp h3).1
  have hA''card : (N : ℝ) / (5 * D) ≤ A''.card := by
    let x : ℝ := (N : ℝ) / (5 * D)
    have hA'card5 : 5 * x < A'.card := by
      dsimp [x]
      have hx : 5 * ((N : ℝ) / (5 * D)) = (N : ℝ) / D := by
        field_simp [hD.ne']
      rw [hx]
      exact hA'card
    have hsum4 : ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤ 4 * x := by
      calc
        ((A0 ∪ A1 ∪ A2 ∪ A3).card : ℝ) ≤
            (A0.card + A1.card + A2.card + A3.card : ℕ) := by
          norm_cast
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [add_le_add_iff_right]
          exact Finset.card_union_le _ _
        _ ≤ 4 * x := by
          have hA0le : (A0.card : ℝ) ≤ x := le_of_lt hA0card
          dsimp [x] at hA0le hA1card hA2card hA3card ⊢
          push_cast
          nlinarith
    calc
      x ≤ (A'.card : ℝ) - (x + x + (x + x)) := by
        have hx4 : x + x + (x + x) = 4 * x := by ring
        rw [hx4]
        nlinarith
      _ ≤ (A'.card : ℝ) - (A0 ∪ A1 ∪ A2 ∪ A3).card := by
        dsimp [x] at hsum4 ⊢
        linarith
      _ ≤ A''.card := by
        dsimp [A'']
        rw [Finset.card_sdiff_of_subset hUnionSub]
        exact UnitFractions.nat_le_cast_real_sub
  clear hA'card hA0card hA1card hA2card hA3card
  have hnotA0 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A0 := by
    intro n hn hn0
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl hn0
  have hnotA1 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A1 := by
    intro n hn hn1
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr hn1
  have hnotA2 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A2 := by
    intro n hn hn2
    exact (Finset.mem_sdiff.mp hn).2 <|
      Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hn2
  have hnotA3 : ∀ {n : ℕ}, n ∈ A'' → n ∉ A3 := by
    intro n hn hn3
    exact (Finset.mem_sdiff.mp hn).2 <| Finset.mem_union.mpr <| Or.inr hn3
  have h0A'' : 0 ∉ A'' := by
    intro hz
    exact hnotA0 hz <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, by
      simpa using
        (Real.rpow_pos_of_pos hlargeN.1 (1 - (1 : ℝ) / log (log (N : ℝ))))⟩
  have hA''N : ∀ n ∈ A'', n < N := by
    intro n hn
    have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hn).1
    exact Finset.mem_range.mp (hAN (by simpa [A'] using hnA'))
  have hstep :
      ∃ S ⊆ A'', ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧
        UnitFractions.rec_sum S = 1 / d := by
    refine htech A'' ?_ y z h1y hyz hzN h0A'' ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_range]
      exact lt_of_lt_of_le (hA''N n hn) (Nat.le_succ N)
    · intro n hn
      rw [← not_lt]
      intro hbad
      exact hnotA0 hn <|
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · calc
        2 / y + log (N : ℝ) ^ (-((1 : ℝ) / 200)) ≤ (A''.card : ℝ) / N := by
          rw [le_div_iff₀ hlargeN.1]
          refine le_trans hyN hA''card
        _ ≤ UnitFractions.rec_sum A'' := by
          rw [Finset.card_eq_sum_ones, UnitFractions.rec_sum]
          push_cast
          rw [Finset.sum_div]
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnle : (n : ℝ) ≤ N := by
            exact_mod_cast Nat.le_of_lt (hA''N n hn)
          have hn0 : n ≠ 0 := by
            intro hzn
            exact h0A'' (hzn ▸ hn)
          have hnpos : 0 < (n : ℝ) := by
            exact Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hn0)
          exact one_div_le_one_div_of_le hnpos hnle
    · intro n hn
      by_contra hbad
      exact hnotA3 hn <|
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, hbad⟩
    · intro n hn
      rw [UnitFractions.is_smooth]
      intro q hq hqn
      rw [← not_lt]
      intro hbad
      exact hnotA1 hn <|
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1, ⟨q, hq, hbad, hqn⟩⟩
    · rw [UnitFractions.arith_regular]
      intro n hn
      by_contra hbad
      have hn0 : n ≠ 0 := by
        intro hz
        exact h0A'' (hz ▸ hn)
      exact hnotA2 hn <| Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hn).1,
        ⟨hn0, hbad⟩⟩
  rcases hstep with ⟨S, hS, d, hyd, hdz, hrecd⟩
  refine ⟨d, ?_, S, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hyd, (Nat.le_floor_iff h0z.le).mpr hdz⟩
  · intro s hs
    have hsA' : s ∈ A' := (Finset.mem_sdiff.mp (hS hs)).1
    simpa [A'] using hsA'
  · rw [sum_one_div_eq_recSum]
    exact hrecd

/--
Erdős Problem 310, with `b = O_α(1)` expressed by the quantifier
`∃ C, ∀ N A, ... b ≤ C`.  The subset is explicitly nonempty, so the theorem
cannot be solved by the zero reciprocal sum.
-/
theorem erdos_310 :
    ∀ α : ℝ, 0 < α →
      ∃ C : ℕ, 1 ≤ C ∧
        ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Icc 1 N →
          α * N ≤ A.card →
            ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
              ∃ a b : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ C ∧
                S.sum (fun n => (1 / n : ℚ)) = a / b := by
  intro α hα
  let D : ℝ := 4 / α
  have hD : 0 < D := div_pos (by norm_num) hα
  rcases bloom_finite_bounded_denominator D hD with
    ⟨N₀, y, z, h1y, h0z, hBloom⟩
  let C : ℕ := max 1 (max N₀ ⌊z⌋₊)
  refine ⟨C, by simp [C], ?_⟩
  intro N hN A hAIcc hAcard
  have hANrange : A ⊆ range (N + 1) := by
    intro n hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_Icc.mp (hAIcc hn)).2
  by_cases hlarge : N₀ ≤ N + 1
  · have hdense : ((N + 1 : ℕ) : ℝ) / D < A.card := by
      have hNcast : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      have hN1 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        have hN1nat : N + 1 ≤ 2 * N := by omega
        exact_mod_cast hN1nat
      have hhalf : α * ((N + 1 : ℕ) : ℝ) / 4 ≤ α * (N : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_left hN1 hα.le
        nlinarith
      have hstrict : α * (N : ℝ) / 2 < α * (N : ℝ) := by
        nlinarith [mul_pos hα hNcast]
      have hcalc : ((N + 1 : ℕ) : ℝ) / D = α * ((N + 1 : ℕ) : ℝ) / 4 := by
        dsimp [D]
        field_simp [hα.ne']
      rw [hcalc]
      exact lt_of_le_of_lt hhalf (lt_of_lt_of_le hstrict hAcard)
    rcases hBloom (N + 1) hlarge A hANrange hdense with
      ⟨d, hd, S, hSA, hsum⟩
    have hdLower : 1 ≤ d := by
      have hyd : y ≤ d := le_trans (Nat.le_ceil y) (by exact_mod_cast (Finset.mem_Icc.mp hd).1)
      exact_mod_cast h1y.trans hyd
    have hdC : d ≤ C := by
      have hdz : d ≤ ⌊z⌋₊ := (Finset.mem_Icc.mp hd).2
      exact hdz.trans (by simp [C])
    have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hSempty
      subst S
      have hdQ : (d : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdLower))
      have hzero : (0 : ℚ) = 1 / (d : ℚ) := by simpa using hsum
      exact (one_div_ne_zero hdQ) hzero.symm
    refine ⟨S, hSA, hSne, 1, d, by simp, hdLower, hdC, ?_⟩
    simpa using hsum
  · have hNlt : N < N₀ := by omega
    have hAne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      subst A
      simp at hAcard
      have : 0 < α * (N : ℝ) := by
        exact mul_pos hα (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
      linarith
    rcases hAne with ⟨n, hnA⟩
    have hnBounds := Finset.mem_Icc.mp (hAIcc hnA)
    have hnC : n ≤ C := by
      exact hnBounds.2.trans (Nat.le_of_lt hNlt) |>.trans (by simp [C])
    refine ⟨{n}, by simpa, by simp, 1, n, by simp, hnBounds.1, hnC, ?_⟩
    simp

end Erdos310

#print axioms Erdos310.erdos_310
