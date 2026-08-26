/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.Proposition73Discrete

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim712

open Finset SimpleGraph

/-- One-side reservoir construction in Claim 7.12.  `A` is the pruned set
of large vertices on a balanced side `Vᵢ`; every vertex of `A` has at most
`t` missing neighbours inside `Vᵢ`.  Discrete Proposition 7.3 prunes the
complementary side once more, at scale `s`, producing `B`.

The three explicit cardinal assumptions are exactly what is needed to turn
the Proposition 7.3 conclusions into the common threshold `Q` for
`A–A`, `A–B`, and `B–A`. -/
theorem exists_claim712_reservoir_side
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (Vᵢ A : Finset W) (n t s Q : ℕ)
    (hVcard : Vᵢ.card = n)
    (hA : A ⊆ Vᵢ)
    (hinternal : ∀ a ∈ A,
      n - t ≤ Erdos547EC2.degreeInto G a Vᵢ)
    (hAcardAA : Q + t ≤ A.card)
    (hAcardBA : Q + s ≤ A.card)
    (hBcardAB : Q + t + s ≤ (Vᵢ \ A).card)
    (hscale : t * n ≤ s * (s + 1)) :
    ∃ B : Finset W,
      B ⊆ Vᵢ \ A ∧ Disjoint A B ∧
      (∀ a ∈ A, Q ≤ Erdos547EC2.degreeInto G a A) ∧
      (∀ a ∈ A, Q ≤ Erdos547EC2.degreeInto G a B) ∧
      (∀ b ∈ B, Q ≤ Erdos547EC2.degreeInto G b A) := by
  classical
  let C : Finset W := Vᵢ \ A
  have hAC : Disjoint A C := Finset.disjoint_sdiff
  have hcover : A ∪ C = Vᵢ := Finset.union_sdiff_of_subset hA
  have hdegSplit (v : W) :
      Erdos547EC2.degreeInto G v A + Erdos547EC2.degreeInto G v C =
        Erdos547EC2.degreeInto G v Vᵢ := by
    rw [Erdos547EC2.degreeInto_union_of_disjoint G v hAC, hcover]
  have hAAraw : ∀ a ∈ A,
      A.card - t ≤ Erdos547EC2.degreeInto G a A := by
    intro a ha
    have htot := hinternal a ha
    have hCle := Erdos547EC2.degreeInto_le_card G a C
    have hsplit := hdegSplit a
    have hcards : A.card + C.card = n := by
      rw [← Finset.card_union_of_disjoint hAC, hcover, hVcard]
    omega
  have hACraw : ∀ a ∈ A,
      C.card - t ≤ Erdos547EC2.degreeInto G a C := by
    intro a ha
    have htot := hinternal a ha
    have hAle := Erdos547EC2.degreeInto_le_card G a A
    have hsplit := hdegSplit a
    have hcards : A.card + C.card = n := by
      rw [← Finset.card_union_of_disjoint hAC, hcover, hVcard]
    omega
  have hAcardN : A.card ≤ n := by
    rw [← hVcard]
    exact Finset.card_le_card hA
  obtain ⟨B, hBC, hremovedMul, hremoved, hBcard, hABraw, hBAraw⟩ :=
    Erdos547EC2.zhao_proposition_7_3_discrete74
      G hAC hACraw hAcardN hscale
  refine ⟨B, hBC, hAC.mono_right hBC, ?_, ?_, ?_⟩
  · intro a ha
    exact (by omega : Q ≤ A.card - t).trans (hAAraw a ha)
  · intro a ha
    have hQB : Q + t ≤ B.card := by
      have hB0 : Q + t + s ≤ C.card := by simpa [C] using hBcardAB
      omega
    exact (by omega : Q ≤ B.card - t).trans (hABraw a ha)
  · intro b hb
    exact (by omega : Q ≤ A.card - s).trans (hBAraw b hb)

/-- Source form with the heavy vertex `v₀` removed from the second
reservoir.  Constructing at threshold `Q+1` absorbs the loss of its possible
single contribution to an `A–B` degree. -/
theorem exists_claim712_reservoir_side_avoiding
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (Vᵢ A : Finset W) (v₀ : W) (n t s Q : ℕ)
    (hVcard : Vᵢ.card = n)
    (hA : A ⊆ Vᵢ)
    (hinternal : ∀ a ∈ A,
      n - t ≤ Erdos547EC2.degreeInto G a Vᵢ)
    (hAcardAA : Q + 1 + t ≤ A.card)
    (hAcardBA : Q + 1 + s ≤ A.card)
    (hBcardAB : Q + 1 + t + s ≤ (Vᵢ \ A).card)
    (hscale : t * n ≤ s * (s + 1)) :
    ∃ B : Finset W,
      B ⊆ Vᵢ \ A ∧ v₀ ∉ B ∧ Disjoint A B ∧
      (∀ a ∈ A, Q ≤ Erdos547EC2.degreeInto G a A) ∧
      (∀ a ∈ A, Q ≤ Erdos547EC2.degreeInto G a B) ∧
      (∀ b ∈ B, Q ≤ Erdos547EC2.degreeInto G b A) := by
  classical
  obtain ⟨B₀, hB₀, hAB₀, hAA, hAB, hBA⟩ :=
    exists_claim712_reservoir_side G Vᵢ A n t s (Q + 1)
      hVcard hA hinternal (by omega) (by omega) (by omega) hscale
  let B := B₀ \ {v₀}
  have hBB₀ : B ⊆ B₀ := Finset.sdiff_subset
  refine ⟨B, hBB₀.trans hB₀, by simp [B], hAB₀.mono_right hBB₀,
    ?_, ?_, ?_⟩
  · intro a ha
    exact (by omega : Q ≤ Q + 1).trans (hAA a ha)
  · intro a ha
    have hremoved : (B₀ \ B).card ≤ 1 := by
      apply (Finset.card_le_card (s := B₀ \ B) (t := {v₀}))
      intro x hx
      have hxB₀ := (Finset.mem_sdiff.mp hx).1
      have hxNotB := (Finset.mem_sdiff.mp hx).2
      simp only [B, Finset.mem_sdiff, Finset.mem_singleton] at hxNotB ⊢
      by_contra hxv
      exact hxNotB ⟨hxB₀, hxv⟩
    have hloss := Erdos547EC2.degreeInto_sub_le_of_removed_le
      G a (b := 1) hremoved
    have hbig := hAB a ha
    omega
  · intro b hb
    exact (by omega : Q ≤ Q + 1).trans (hBA b (hBB₀ hb))

end Erdos547b.ZhaoClaim712

#print axioms Erdos547b.ZhaoClaim712.exists_claim712_reservoir_side
#print axioms Erdos547b.ZhaoClaim712.exists_claim712_reservoir_side_avoiding
