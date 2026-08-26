import ErdosProblems.Erdos489.DistinctWitnesses
import ErdosProblems.Erdos489.Representatives
import ErdosProblems.Erdos489.HighRank

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- A dense set of divisor-labelled interval points with small reciprocal mass
has a linearly large transversal carrying high distinct ranks. -/
theorem exists_high_rank_divisor_representatives
    (S : Finset ℕ) (L G C : ℕ) (a label : ℕ → ℕ)
    (hC : 0 < C) (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n)
    (hdense : 4 * (G : ℝ) / (C : ℝ) ≤ (S.card : ℝ))
    (hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤
      1 / (C : ℝ)) :
    ∃ T : Finset ℕ,
      T ⊆ S ∧ Set.InjOn label (T : Set ℕ) ∧
      G / C ≤ T.card ∧ ∀ n ∈ T, G / C ≤ label n := by
  have hbasic := interval_label_card_le_reciprocal_mass
    S L G a label ha hinterval hdiv
  have hG0 : (0 : ℝ) ≤ G := by positivity
  have hmassmul := mul_le_mul_of_nonneg_left hmass hG0
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have himageR : 3 * (G : ℝ) / (C : ℝ) ≤
      ((S.image label).card : ℝ) := by
    have hrewrite : (G : ℝ) * (1 / (C : ℝ)) = (G : ℝ) / C := by
      simp [div_eq_mul_inv]
    rw [hrewrite] at hmassmul
    ring_nf at hdense hmassmul ⊢
    linarith
  let t := G / C
  have htcast : (t : ℝ) ≤ (G : ℝ) / (C : ℝ) := by
    dsimp [t]
    exact Nat.cast_div_le
  have htwiceR : ((2 * t : ℕ) : ℝ) ≤ ((S.image label).card : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (t : ℝ) ≤ 2 * ((G : ℝ) / (C : ℝ)) := by linarith
      _ ≤ 3 * (G : ℝ) / (C : ℝ) := by
        have hratio : 0 ≤ (G : ℝ) / (C : ℝ) := by positivity
        ring_nf
        ring_nf at hratio
        linarith
      _ ≤ ((S.image label).card : ℝ) := himageR
  have htwice : 2 * t ≤ (S.image label).card := by exact_mod_cast htwiceR
  obtain ⟨U, hUS, hinjU, hUcard⟩ :=
    Finset.exists_subset_injOn_card_eq_image S label
  let T := U.filter fun n => t ≤ label n
  have hlarge : t ≤ T.card := by
    apply card_rank_ge_of_twice_le_card U label hinjU t
    rwa [hUcard]
  refine ⟨T, ?_, ?_, hlarge, ?_⟩
  · exact (Finset.filter_subset _ _).trans hUS
  · exact hinjU.mono (by
      intro n hn
      exact (Finset.mem_filter.mp hn).1)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- Endpoint-robust variant: losing two candidate points still leaves the same
`G/C` high-rank transversal once `G≥2C`. -/
theorem exists_high_rank_divisor_representatives_sub_two
    (S : Finset ℕ) (L G C : ℕ) (a label : ℕ → ℕ)
    (hC : 0 < C) (hGC : 2 * C ≤ G) (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n)
    (hdense : 4 * (G : ℝ) / (C : ℝ) - 2 ≤ (S.card : ℝ))
    (hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤
      1 / (C : ℝ)) :
    ∃ T : Finset ℕ,
      T ⊆ S ∧ Set.InjOn label (T : Set ℕ) ∧
      G / C ≤ T.card ∧ ∀ n ∈ T, G / C ≤ label n := by
  have hbasic := interval_label_card_le_reciprocal_mass
    S L G a label ha hinterval hdiv
  have hmassmul := mul_le_mul_of_nonneg_left hmass
    (show (0 : ℝ) ≤ G by positivity)
  have hrewrite : (G : ℝ) * (1 / (C : ℝ)) = (G : ℝ) / C := by
    simp [div_eq_mul_inv]
  rw [hrewrite] at hmassmul
  have himageR : 3 * (G : ℝ) / (C : ℝ) - 2 ≤
      ((S.image label).card : ℝ) := by
    ring_nf at hdense hmassmul ⊢
    linarith
  let t := G / C
  have htcast : (t : ℝ) ≤ (G : ℝ) / (C : ℝ) := by
    dsimp [t]
    exact Nat.cast_div_le
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hC
  have hratio2 : (2 : ℝ) ≤ (G : ℝ) / (C : ℝ) := by
    apply (le_div_iff₀ hCposR).2
    exact_mod_cast hGC
  have htwiceR : ((2 * t : ℕ) : ℝ) ≤ ((S.image label).card : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hratio : 0 ≤ (G : ℝ) / (C : ℝ) := by positivity
    have hmid : 2 * (t : ℝ) ≤
        3 * (G : ℝ) / (C : ℝ) - 2 := by
      ring_nf at htcast hratio2 ⊢
      linarith
    exact hmid.trans himageR
  have htwice : 2 * t ≤ (S.image label).card := by exact_mod_cast htwiceR
  obtain ⟨U, hUS, hinjU, hUcard⟩ :=
    Finset.exists_subset_injOn_card_eq_image S label
  let T := U.filter fun n => t ≤ label n
  have hlarge : t ≤ T.card := by
    apply card_rank_ge_of_twice_le_card U label hinjU t
    rwa [hUcard]
  refine ⟨T, (Finset.filter_subset _ _).trans hUS,
    hinjU.mono (fun n hn => (Finset.mem_filter.mp hn).1), hlarge, ?_⟩
  intro n hn
  exact (Finset.mem_filter.mp hn).2

end Erdos489
