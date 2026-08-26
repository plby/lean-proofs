/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EC2

open scoped SimpleGraph

noncomputable section

namespace Erdos547EC2

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On a set not containing `v`, adjacency and complementary adjacency
partition all possible neighbors. -/
theorem degreeInto_add_degreeInto_compl_discrete74
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (hvS : v ∉ S) :
    degreeInto G v S + degreeInto Gᶜ v S = S.card := by
  rw [degreeInto_eq_card_interedges_singleton,
    degreeInto_eq_card_interedges_singleton]
  simpa using G.card_interedges_add_card_interedges_compl
    (s := ({v} : Finset V)) (t := S) (by simpa [Finset.disjoint_left])

/-- Restricting the target can only decrease `degreeInto`. -/
theorem degreeInto_mono_discrete74
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : S ⊆ T) :
    degreeInto G v S ≤ degreeInto G v T := by
  unfold degreeInto
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hST hw.1, hw.2⟩

/-- The vertices on the second side with at most `s` missing neighbors
on the first side. -/
def zhaoPrunedSideDiscrete74 (G : SimpleGraph V) [DecidableRel G.Adj]
    (X B : Finset V) (s : ℕ) : Finset V :=
  B.filter fun b ↦ degreeInto Gᶜ b X ≤ s

/-- A discrete form of the finite-set pruning in Zhao's Proposition 7.3.

If every vertex of `X` misses at most `q` vertices of the disjoint set
`B`, discard from `B` the vertices which miss more than `s` vertices of
`X`.  The number discarded, multiplied by `s+1`, is at most `|X|q`.
The two surviving one-sided minimum-degree estimates are stated without
division, so the lemma is directly usable with natural-number parameters.
The last two hypotheses imply the convenient bound `|B \ B₁| ≤ s` whenever
`s(s+1) ≥ qn` and `|X| ≤ n`. -/
theorem zhao_proposition_7_3_discrete74
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {X B : Finset V} {q s n : ℕ}
    (hXB : Disjoint X B)
    (hXtoB : ∀ x ∈ X, B.card - q ≤ degreeInto G x B)
    (hXcard : X.card ≤ n)
    (hscale : q * n ≤ s * (s + 1)) :
    ∃ B₁ : Finset V,
      B₁ ⊆ B ∧
      (B \ B₁).card * (s + 1) ≤ X.card * q ∧
      (B \ B₁).card ≤ s ∧
      B.card ≤ B₁.card + s ∧
      (∀ x ∈ X, B₁.card - q ≤ degreeInto G x B₁) ∧
      ∀ b ∈ B₁, X.card - s ≤ degreeInto G b X := by
  classical
  let bad : Finset V := crossHeavy Gᶜ B X (s + 1)
  let B₁ : Finset V := B \ bad
  have hbadB : bad ⊆ B := crossHeavy_subset Gᶜ B X (s + 1)
  have hcomplRow : ∀ x ∈ X, degreeInto Gᶜ x B ≤ q := by
    intro x hx
    have hxB : x ∉ B := by
      intro hx'
      exact Finset.disjoint_left.mp hXB hx hx'
    have hpartition := degreeInto_add_degreeInto_compl_discrete74 G x B hxB
    have hlarge := hXtoB x hx
    omega
  have hcomplTotal : (Gᶜ.interedges X B).card ≤ X.card * q := by
    rw [← sum_degreeInto_eq_card_interedges]
    calc
      ∑ x ∈ X, degreeInto Gᶜ x B ≤ ∑ _x ∈ X, q := by
        exact Finset.sum_le_sum fun x hx ↦ hcomplRow x hx
      _ = X.card * q := by simp
  have hbadMul : bad.card * (s + 1) ≤ X.card * q := by
    calc
      bad.card * (s + 1) ≤ (Gᶜ.interedges B X).card := by
        exact crossHeavy_card_mul_le_interedges Gᶜ B X (s + 1)
      _ = (Gᶜ.interedges X B).card := by
        have := Gᶜ.symm
        exact Rel.card_interedges_comm B X
      _ ≤ X.card * q := hcomplTotal
  have hXq : X.card * q ≤ n * q := Nat.mul_le_mul_right q hXcard
  have hnq : n * q ≤ s * (s + 1) := by
    simpa [Nat.mul_comm] using hscale
  have hbadCard : bad.card ≤ s := by
    apply Nat.le_of_mul_le_mul_right (c := s + 1)
    · exact hbadMul.trans (hXq.trans hnq)
    · omega
  have hdiff : B \ B₁ = bad := by
    dsimp [B₁]
    exact Finset.sdiff_sdiff_eq_self hbadB
  have hB₁B : B₁ ⊆ B := Finset.sdiff_subset
  have hBcard : B.card ≤ B₁.card + s := by
    have hcardDiff := Finset.card_sdiff_of_subset hbadB
    dsimp [B₁]
    omega
  have hleft : ∀ x ∈ X, B₁.card - q ≤ degreeInto G x B₁ := by
    intro x hx
    have hxB₁ : x ∉ B₁ := by
      intro hx'
      exact Finset.disjoint_left.mp hXB hx (hB₁B hx')
    have hcomplB₁ : degreeInto Gᶜ x B₁ ≤ q :=
      (degreeInto_mono_discrete74 Gᶜ x hB₁B).trans (hcomplRow x hx)
    have hpartition := degreeInto_add_degreeInto_compl_discrete74 G x B₁ hxB₁
    omega
  have hright : ∀ b ∈ B₁, X.card - s ≤ degreeInto G b X := by
    intro b hb
    have hbB : b ∈ B := hB₁B hb
    have hbBad : b ∉ bad := (Finset.mem_sdiff.mp hb).2
    have hcompl : degreeInto Gᶜ b X ≤ s := by
      dsimp [bad] at hbBad
      simp only [crossHeavy, Finset.mem_filter, hbB, true_and, not_le] at hbBad
      omega
    have hbX : b ∉ X := by
      intro hb'
      exact Finset.disjoint_left.mp hXB hb' hbB
    have hpartition := degreeInto_add_degreeInto_compl_discrete74 G b X hbX
    omega
  refine ⟨B₁, hB₁B, ?_, ?_, hBcard, hleft, hright⟩
  · simpa [hdiff] using hbadMul
  · simpa [hdiff] using hbadCard

#print axioms zhao_proposition_7_3_discrete74

end Erdos547EC2
