import Arxiv.Arxiv2411_18291.BoundedMultiplicityCorrection
import Arxiv.Arxiv2411_18291.CliqueMultiplicityBound

/-! # Decoder corrections controlled by the actual multiplicity at each edge

The correction quotients have a fixed nonpositive sign. Their absolute
values are bounded by the original boundary coordinate, so all face-degree
bounds are preserved without replacing the multiplicities by their maximum.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem reduced_boundary_correction_range (N : ℤ) (hN : 2 ≤ N)
    (D : Finset (Block V q)) (L : Hypergraph V r) (Φ : Block V q → ℤ)
    (hΦ : boundary r Φ = indicator L) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (e : Block V r) :
    -((D.filter fun Q => e.val ⊆ Q.val).card : ℤ) ≤
        (indicator L e - boundary r (fun Q => Φ Q % N) e) / N ∧
      (indicator L e - boundary r (fun Q => Φ Q % N) e) / N ≤ 0 := by
  have hNpos : 0 < N := by omega
  have hrem0 (Q : Block V q) : 0 ≤ Φ Q % N := Int.emod_nonneg _ hNpos.ne'
  have hrem1 (Q : Block V q) : Φ Q % N ≤ N - 1 := by
    have hh := Int.emod_lt_of_pos (Φ Q) hNpos
    omega
  have hsrem : ∀ Q, Q ∉ D → Φ Q % N = 0 := by
    intro Q hQ
    rw [hs Q hQ, Int.zero_emod]
  have hb0 := boundary_nonneg_int (fun Q => Φ Q % N) hrem0 e
  have hb1 := boundary_le_of_supported_coefficients D _ hsrem hrem1 e
  have hL0 : 0 ≤ indicator L e := by unfold indicator; split_ifs <;> omega
  have hL1 : indicator L e ≤ 1 := by unfold indicator; split_ifs <;> omega
  have hM : (0 : ℤ) ≤ (D.filter fun Q => e.val ⊆ Q.val).card := Nat.cast_nonneg _
  let J := indicator L e - boundary r (fun Q => Φ Q % N) e
  have hdiv : N ∣ J := by simpa only [hΦ, J] using boundary_remainder_congr N Φ e
  have hprod : N * (J / N) = J := Int.mul_ediv_cancel_of_dvd hdiv
  have hlo : -((D.filter fun Q => e.val ⊆ Q.val).card : ℤ) ≤ J / N := by
    apply (mul_le_mul_iff_right₀ hNpos).mp
    rw [hprod]
    dsimp only [J]
    nlinarith only [hb1, hL0, hM]
  have hhi : J / N < 1 := by
    apply (mul_lt_mul_iff_right₀ hNpos).mp
    rw [hprod]
    dsimp only [J]
    linarith only [hb0, hL1, hN]
  exact ⟨hlo, show J / N ≤ 0 by omega⟩

theorem reduced_boundary_correction_abs_le_edge (N : ℤ) (hN : 2 ≤ N)
    (D : Finset (Block V q)) (L : Hypergraph V r) (Φ : Block V q → ℤ)
    (hΦ : boundary r Φ = indicator L) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (e : Block V r) :
    |(indicator L e - boundary r (fun Q => Φ Q % N) e) / N| ≤
      (D.filter fun Q => e.val ⊆ Q.val).card := by
  obtain ⟨hlo, hhi⟩ := reduced_boundary_correction_range N hN D L Φ hΦ hs e
  exact abs_le.mpr ⟨hlo, hhi.trans (Nat.cast_nonneg _)⟩

theorem reduced_boundary_correction_degree_le (N : ℤ) (hN : 2 ≤ N)
    (D : Finset (Block V q)) (L : Hypergraph V r) (Φ : Block V q → ℤ)
    (hΦ : boundary r Φ = indicator L) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (S : Finset V) :
    degree (fun e => |(indicator L e - boundary r (fun Q => Φ Q % N) e) / N|) S ≤
      degree (boundary r (indicator D)) S := by
  apply degree_mono_int
  intro e
  rw [boundary_indicator]
  exact reduced_boundary_correction_abs_le_edge N hN D L Φ hΦ hs e

theorem IsCliqueFamilyBounded.correction_degree_lt {D : Finset (Block V q)} {θ : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (N : ℤ) (hN : 2 ≤ N)
    (L : Hypergraph V (r + 1)) (Φ : Block V q → ℤ)
    (hΦ : boundary (r + 1) Φ = indicator L) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (S : Block V r) :
    ((degree (fun e =>
      |(indicator L e - boundary (r + 1) (fun Q => Φ Q % N) e) / N|) S.val : ℤ) : ℝ) <
        θ * Fintype.card V := by
  have hle : ((degree (fun e =>
      |(indicator L e - boundary (r + 1) (fun Q => Φ Q % N) e) / N|) S.val : ℤ) : ℝ) ≤
        ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) := by
    exact_mod_cast reduced_boundary_correction_degree_le N hN D L Φ hΦ hs S.val
  exact hle.trans_lt (hD S)

end Arxiv2411_18291
