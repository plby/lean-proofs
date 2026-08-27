import Arxiv.Arxiv2411_18291.SparseLocalDecoders
import Arxiv.Arxiv2411_18291.CoefficientReduction

/-!
# Small corrections supported on separated local decoders

The local decoder regions are edge-disjoint, so a `q`-clique occurs in at
most one region. Corrections with coefficients in `{-1,0}` therefore retain
the individual decoder coefficient bound. The correction family is also
disjoint from any original family whose edges all lie in the root graph.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem two_le_choose_of_between {q m : ℕ} (hm : 0 < m) (hmq : m < q) :
    2 ≤ q.choose m := by
  have hp := Nat.choose_pos hmq.le
  have hne : q.choose m ≠ 1 := by
    intro h
    rcases Nat.choose_eq_one_iff.mp h with h | h <;> omega
  omega

theorem decoder_multiplier_bounds {q r : ℕ} (hqr : r + 1 < q) :
    2 ≤ (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∧
      (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ≤
        (2 ^ q * (r + 1).factorial : ℕ) := by
  constructor
  · have h := Nat.mul_le_mul (Nat.factorial_pos (r + 1))
      (two_le_choose_of_between (Nat.succ_pos r) hqr)
    exact_mod_cast (by simpa only [one_mul] using h)
  · have h := Nat.mul_le_mul_left (r + 1).factorial (Nat.choose_le_two_pow q (r + 1))
    exact_mod_cast (by simpa only [mul_comm] using h)

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem IsCliqueCover.refinement_disjoint_base (hqr : r + 1 < q)
    {B : Hypergraph V (r + 1)} {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z)
    (D : Finset (Block V q)) (hsupport : cliqueSupport (r + 1) D ⊆ B) :
    Disjoint D (cliqueRefinement q (univ.image Z)) := by
  apply disjoint_left.mpr
  intro P hPD hPZ
  obtain ⟨Q, hQ, hPQ⟩ := (mem_cliqueRefinement _ P).mp hPZ
  obtain ⟨i, _, rfl⟩ := mem_image.mp hQ
  have hsub : cliqueEdges (r + 1) P ⊆ {i.val} := by
    intro e he
    have heB := hsupport (mem_biUnion.mpr ⟨P, hPD, he⟩)
    rcases (hZ.punctured i).2 e (((mem_cliqueEdges _ _).mp he).trans hPQ) with heR | hei
    · exact ((mem_sdiff.mp heR).2 heB).elim
    · exact mem_singleton.mpr hei
  have hc := card_le_card hsub
  rw [card_cliqueEdges, card_singleton] at hc
  have htwo := two_le_choose_of_between (Nat.succ_pos r) hqr
  exact Nat.not_lt_of_ge hc htwo

def sumLocalDecoders {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) (c : B → ℤ) : Block V q → ℤ :=
  ∑ i : B, fun Q => c i * localDecoderOn q (Z i).val i.val Q

theorem boundary_sumLocalDecoders (hqr : r + 1 ≤ q) {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) (hZ : ∀ i : B, i.val.val ⊆ (Z i).val) (c : B → ℤ)
    (J : Block V (r + 1) → ℤ) (hs : ∀ e, e ∉ B → J e = 0)
    (hc : ∀ i : B, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) * c i = J i.val) :
    boundary (r + 1) (sumLocalDecoders Z c) = J := by
  let N : ℤ := ((r + 1).factorial * q.choose (r + 1) : ℕ)
  have hbd (i : B) : boundary (r + 1) (fun Q => c i * localDecoderOn q (Z i).val i.val Q) =
      fun e => c i * (if e = i.val then N else 0) := by
    rw [boundary_mul, boundary_localDecoderOn _ (Z i).property hqr i.val (hZ i)]
    simp only [Nat.descFactorial_eq_factorial_mul_choose, N]
  rw [sumLocalDecoders, boundary_sum]
  funext e
  simp only [Finset.sum_apply, hbd]
  by_cases he : e ∈ B
  · rw [sum_eq_single (⟨e, he⟩ : B)]
    · rw [if_pos rfl]
      exact (mul_comm _ _).trans (hc ⟨e, he⟩)
    · intro i _ hi
      have hne : e ≠ i.val := fun h => hi (Subtype.ext h.symm)
      simp only [hne, if_false, mul_zero]
    · intro h
      exact (h (mem_univ _)).elim
  · rw [hs e he]
    apply sum_eq_zero
    intro i _
    have hne : e ≠ i.val := fun h => he (h ▸ i.property)
    simp only [hne, if_false, mul_zero]

theorem sumLocalDecoders_support {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) (c : B → ℤ) (Q : Block V q)
    (hQ : Q ∉ cliqueRefinement q (univ.image Z)) : sumLocalDecoders Z c Q = 0 := by
  rw [sumLocalDecoders, Finset.sum_apply]
  apply sum_eq_zero
  intro i _
  have hnot : ¬Q.val ⊆ (Z i).val := by
    intro h
    exact hQ ((mem_cliqueRefinement _ Q).mpr ⟨Z i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, h⟩)
  simp only [localDecoderOn, hnot, if_false, mul_zero]

theorem IsCliqueCover.sumLocalDecoders_abs_le (hqr : r + 1 ≤ q)
    {R B : Hypergraph V (r + 1)} {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover R (fun e : B => e.val) Z) (c : B → ℤ)
    (hc : ∀ i, c i = -1 ∨ c i = 0) (Q : Block V q) :
    |sumLocalDecoders Z c Q| ≤ (2 ^ q * (r + 1).factorial : ℕ) := by
  rw [sumLocalDecoders, Finset.sum_apply]
  by_cases hex : ∃ i : B, Q.val ⊆ (Z i).val
  · obtain ⟨i, hi⟩ := hex
    rw [sum_eq_single i]
    · rcases hc i with h | h
      · simpa only [h, neg_one_mul, abs_neg] using
          localDecoderOn_abs_le hqr (Z i).val i.val Q
      · simp only [h, zero_mul, abs_zero, Nat.cast_nonneg]
    · intro j _ hji
      have hj : ¬Q.val ⊆ (Z j).val := fun h => hji (hZ.subclique_unique hqr Q h hi)
      simp only [localDecoderOn, hj, if_false, mul_zero]
    · intro h
      exact (h (mem_univ _)).elim
  · have hz : ∑ i : B, c i * localDecoderOn q (Z i).val i.val Q = 0 := by
      apply sum_eq_zero
      intro i _
      have hi : ¬Q.val ⊆ (Z i).val := fun h => hex ⟨i, h⟩
      simp only [localDecoderOn, hi, if_false, mul_zero]
    rw [hz, abs_zero]
    exact Nat.cast_nonneg _

end Arxiv2411_18291
