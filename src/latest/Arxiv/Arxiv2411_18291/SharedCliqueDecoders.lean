import Arxiv.Arxiv2411_18291.CliqueEnlargementExistence
import Arxiv.Arxiv2411_18291.CliqueRefinementDegrees
import Arxiv.Arxiv2411_18291.CliqueSupportBounds

/-! # Local decoding by sharing a region across each input clique -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem shared_decoder_coefficient_le {q r : ℕ} (hrq : r < q) :
    2 ^ (r + 2) * (r + 1).factorial * (q + 1).choose (q - r) ≤
      2 * (4 * q) ^ (r + 1) := by
  have hchoose : (q + 1).choose (q - r) = (q + 1).choose (r + 1) := by
    simpa only [show q + 1 - (r + 1) = q - r by omega] using
      Nat.choose_symm (by omega : r + 1 ≤ q + 1)
  rw [hchoose, mul_assoc, ← Nat.descFactorial_eq_factorial_mul_choose]
  calc
    _ ≤ 2 ^ (r + 2) * (q + 1) ^ (r + 1) :=
      Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
    _ ≤ 2 ^ (r + 2) * (2 * q) ^ (r + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      calc
        _ = 2 * (2 ^ (r + 1) * (2 * q) ^ (r + 1)) := by ring
        _ = _ := by rw [← mul_pow]; congr 2; ring

theorem exists_shared_clique_decoders_of_numerics
    {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (D : Finset (Block V q)) (hrq : r < q) {θ : ℝ} (hθ : 0 ≤ θ)
    (hD : IsCliqueFamilyBounded r D θ)
    (hn : q + (r + 1) ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsize : ((r + 1 : ℕ) : ℝ) * (q + (r + 1)) ≤ (Fintype.card V : ℝ) / 2)
    (hfailure : Fintype.card (Block V r) *
      Real.exp (-(2 ^ (r + 1) * (r + 1).factorial * (θ / (q - r : ℕ)) *
        Fintype.card V / 3)) < 1) :
    ∃ D' : Finset (Block V q), D ⊆ D' ∧
      IsCliqueFamilyBounded r D' (2 * (4 * q : ℝ) ^ (r + 1) * θ) ∧
      ∀ e ∈ cliqueSupport (r + 1) D, ∃ Z : Block V (q + (r + 1)), e.val ⊆ Z.val ∧
        ∀ Q : Block V q, Q.val ⊆ Z.val → Q ∈ D' := by
  obtain ⟨Z, hs, hZ⟩ := exists_clique_enlargements_of_boundary_bound D hrq
    (by omega : r ≤ r + 1) hθ hD hn hnpos
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsize) hfailure
  let D' := cliqueRefinement q (univ.image Z)
  have hbound := cliqueRefinement_bounded_of_face_bound Z hrq (Nat.le_add_right q (r + 1)) hZ
  have hcoef : (q - r : ℕ) * (q + (r + 1) - r).choose (q - r) *
      (2 ^ (r + 2) * ((r + 1).factorial : ℝ) * (θ / (q - r : ℕ))) ≤
        2 * (4 * q : ℝ) ^ (r + 1) * θ := by
    have hqr : (q - r : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hrq)
    rw [show q + (r + 1) - r = q + 1 by omega]
    calc
      _ = (2 ^ (r + 2) * ((r + 1).factorial : ℝ) * (q + 1).choose (q - r)) * θ := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast shared_decoder_coefficient_le hrq) hθ
  refine ⟨D', ?_, hbound.mono hcoef, ?_⟩
  · intro Q hQ
    exact (mem_cliqueRefinement _ Q).mpr
      ⟨Z ⟨Q, hQ⟩, mem_image.mpr ⟨⟨Q, hQ⟩, mem_univ _, rfl⟩, hs ⟨Q, hQ⟩⟩
  · intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    refine ⟨Z ⟨Q, hQ⟩, (mem_cliqueEdges _ _).mp heQ |>.trans (hs ⟨Q, hQ⟩), ?_⟩
    intro P hP
    exact (mem_cliqueRefinement _ P).mpr
      ⟨Z ⟨Q, hQ⟩, mem_image.mpr ⟨⟨Q, hQ⟩, mem_univ _, rfl⟩, hP⟩

end Arxiv2411_18291
