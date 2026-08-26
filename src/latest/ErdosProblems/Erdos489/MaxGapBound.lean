import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Distinct divisor ranks represented inside a gap are bounded by the
forbidden counting function at the right endpoint. -/
theorem divisor_rank_witness_card_le_count
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (T : Finset ℕ) (rank : ℕ → ℕ) (U : ℕ)
    (hinj : Set.InjOn rank (T : Set ℕ))
    (hpos : ∀ n ∈ T, 0 < n)
    (hupper : ∀ n ∈ T, n < U)
    (hdiv : ∀ n ∈ T, Nat.nth p (rank n) ∣ n) :
    T.card ≤ Nat.count p U := by
  have hrange : T.image rank ⊆ Finset.range (Nat.count p U) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    have hmodle : Nat.nth p (rank n) ≤ n :=
      Nat.le_of_dvd (hpos n hn) (hdiv n hn)
    have hnthlt : Nat.nth p (rank n) < U := hmodle.trans_lt (hupper n hn)
    exact Finset.mem_range.mpr ((Nat.lt_nth_iff_count_lt hp).2 hnthlt)
  calc
    T.card = (T.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (Nat.count p U)).card := Finset.card_le_card hrange
    _ = Nat.count p U := Finset.card_range _

/-- A sufficiently strong linear upper bound on the forbidden count forces all
gaps beginning below `x` to have length at most `x`, once each long gap has
`gap/C` distinct divisor-rank witnesses. -/
theorem eventual_gap_le_prefix
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (bseq gap rank : ℕ → ℕ) (C H0 N : ℕ) (hC : 0 < C)
    (hgap : ∀ i, bseq (i + 1) = bseq i + gap i)
    (hcount : ∀ n, N ≤ n → 8 * C * Nat.count p n ≤ n)
    (hwitness : ∀ i, H0 ≤ gap i →
      ∃ T : Finset ℕ, Set.InjOn rank (T : Set ℕ) ∧
        gap i / C ≤ T.card ∧
        (∀ n ∈ T, bseq i < n ∧ n < bseq (i + 1)) ∧
        (∀ n ∈ T, Nat.nth p (rank n) ∣ n)) :
    ∀ x, max (max H0 N) (2 * C) ≤ x →
      ∀ i, bseq i < x → gap i ≤ x := by
  intro x hx i hbix
  by_contra hnot
  have hxg : x < gap i := by omega
  have hgH : H0 ≤ gap i := by omega
  obtain ⟨T, hinj, hcard, hint, hdiv⟩ := hwitness i hgH
  have hTcount : T.card ≤ Nat.count p (bseq (i + 1)) := by
    apply divisor_rank_witness_card_le_count p hp T rank
      (bseq (i + 1)) hinj
    · intro n hn
      have := (hint n hn).1
      omega
    · intro n hn
      exact (hint n hn).2
    · exact hdiv
  have hbnext : bseq (i + 1) ≤ 2 * gap i := by
    rw [hgap i]
    omega
  have hcountmono : Nat.count p (bseq (i + 1)) ≤
      Nat.count p (2 * gap i) := Nat.count_monotone p hbnext
  have hN : N ≤ 2 * gap i := by omega
  have hc := hcount (2 * gap i) hN
  have hq : gap i / C ≤ Nat.count p (2 * gap i) :=
    hcard.trans (hTcount.trans hcountmono)
  have hdivlt : gap i < C * (gap i / C + 1) := Nat.lt_mul_div_succ _ hC
  have hupper : gap i < C * (Nat.count p (2 * gap i) + 1) :=
    hdivlt.trans_le (Nat.mul_le_mul_left C (by omega))
  have hgC : 2 * C ≤ gap i := by omega
  nlinarith

end Erdos489
