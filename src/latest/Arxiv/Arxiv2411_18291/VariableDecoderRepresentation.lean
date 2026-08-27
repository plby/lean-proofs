import Arxiv.Arxiv2411_18291.EdgewiseCorrection
import Arxiv.Arxiv2411_18291.VariableCliqueSlots

/-! # Uniform representations with capacities determined by edge multiplicities

The capacity function is fixed by the original generating family and decoder
regions before a represented leave is chosen. No uniform multiplicity bound
is assumed. Placement of these weighted decoder regions remains a separate
geometric task.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def edgewiseDecoderCapacity (D : Finset (Block V q)) {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) (Q : Block V q) : ℕ :=
  (2 ^ q * (r + 1).factorial) * ((if Q ∈ D then 1 else 0) +
    ∑ i : B, if Q.val ⊆ (Z i).val then (D.filter fun P => i.val.val ⊆ P.val).card else 0)

theorem edgewiseDecoderCapacity_support (D : Finset (Block V q))
    {B : Hypergraph V (r + 1)} (Z : B → Block V (q + (r + 1))) (Q : Block V q)
    (hQ : Q ∉ D ∪ cliqueRefinement q (univ.image Z)) : edgewiseDecoderCapacity D Z Q = 0 := by
  have hQD : Q ∉ D := fun h => hQ (mem_union_left _ h)
  have hQZ : Q ∉ cliqueRefinement q (univ.image Z) := fun h => hQ (mem_union_right _ h)
  unfold edgewiseDecoderCapacity
  rw [if_neg hQD, zero_add]
  have hzero : (∑ i : B, if Q.val ⊆ (Z i).val then
      (D.filter fun P => i.val.val ⊆ P.val).card else 0) = 0 := by
    apply sum_eq_zero
    intro i _
    apply if_neg
    intro hi
    exact hQZ ((mem_cliqueRefinement _ Q).mpr ⟨Z i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, hi⟩)
  rw [hzero, mul_zero]

omit [Fintype V] in
theorem sumLocalDecoders_abs_le_edgewise (hqr : r + 1 ≤ q)
    (D : Finset (Block V q)) {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) (c : B → ℤ)
    (hc : ∀ i, |c i| ≤ (D.filter fun P => i.val.val ⊆ P.val).card) (Q : Block V q) :
    |sumLocalDecoders Z c Q| ≤ (2 ^ q * (r + 1).factorial : ℕ) *
      ((∑ i : B, if Q.val ⊆ (Z i).val then
        (D.filter fun P => i.val.val ⊆ P.val).card else 0 : ℕ) : ℤ) := by
  rw [sumLocalDecoders, Finset.sum_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [Nat.cast_sum, mul_sum]
  apply sum_le_sum
  intro i _
  by_cases hi : Q.val ⊆ (Z i).val
  · rw [if_pos hi, abs_mul]
    have hh := mul_le_mul (hc i) (localDecoderOn_abs_le hqr (Z i).val i.val Q)
      (abs_nonneg _) (Nat.cast_nonneg _)
    simpa only [mul_comm] using hh
  · simp only [localDecoderOn, hi, if_false, mul_zero, abs_zero, Nat.cast_zero, le_refl]

theorem edgewise_representation_of_local_decoders (hqr : r + 1 < q)
    (D : Finset (Block V q)) (B L : Hypergraph V (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B) (hLB : L ⊆ B)
    (Z : B → Block V (q + (r + 1)))
    (hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z)
    (hgen : GeneratedBy D (indicator L)) :
    ∃ Φ : Block V q → ℤ, boundary (r + 1) Φ = indicator L ∧
      (∀ Q, Q ∉ D ∪ cliqueRefinement q (univ.image Z) → Φ Q = 0) ∧
      ∀ Q, |Φ Q| ≤ edgewiseDecoderCapacity D Z Q := by
  obtain ⟨Φ₀, hΦ₀, hs₀⟩ := hgen
  let N : ℤ := ((r + 1).factorial * q.choose (r + 1) : ℕ)
  have hN : 2 ≤ N := (decoder_multiplier_bounds hqr).1
  have hNC : N ≤ (2 ^ q * (r + 1).factorial : ℕ) := (decoder_multiplier_bounds hqr).2
  have hNpos : 0 < N := by omega
  let Φ₁ : Block V q → ℤ := fun Q => Φ₀ Q % N
  let J : Block V (r + 1) → ℤ := fun e => indicator L e - boundary (r + 1) Φ₁ e
  let c : B → ℤ := fun i => J i.val / N
  have hs₁ : ∀ Q, Q ∉ D → Φ₁ Q = 0 := by
    intro Q hQ
    dsimp only [Φ₁]
    rw [hs₀ Q hQ, Int.zero_emod]
  have hdiv (e : Block V (r + 1)) : N ∣ J e := by
    simpa only [hΦ₀, J, Φ₁] using boundary_remainder_congr N Φ₀ e
  have hc (i : B) : |c i| ≤ (D.filter fun P => i.val.val ⊆ P.val).card :=
    reduced_boundary_correction_abs_le_edge N hN D L Φ₀ hΦ₀ hs₀ i.val
  have hprod (i : B) : N * c i = J i.val := Int.mul_ediv_cancel_of_dvd (hdiv i.val)
  have hsJ : ∀ e, e ∉ B → J e = 0 := by
    intro e he
    have heL : e ∉ L := fun heL => he (hLB heL)
    dsimp only [J]
    rw [indicator_apply_of_notMem heL, boundary_zero_outside_support D B Φ₁ hs₁ hDB e he]
    exact sub_self _
  have hΦ₂ := boundary_sumLocalDecoders hqr.le Z (fun i => (hZ.punctured i).1) c J hsJ hprod
  refine ⟨Φ₁ + sumLocalDecoders Z c, ?_, ?_, ?_⟩
  · rw [boundary_add, hΦ₂]
    funext e
    simp only [Pi.add_apply, J, add_sub_cancel]
  · intro Q hQ
    have hQ₁ : Q ∉ D := fun h => hQ (mem_union_left _ h)
    have hQ₂ : Q ∉ cliqueRefinement q (univ.image Z) := fun h => hQ (mem_union_right _ h)
    simp only [Pi.add_apply, hs₁ Q hQ₁, sumLocalDecoders_support Z c Q hQ₂, add_zero]
  · intro Q
    have hΦ₁ : |Φ₁ Q| ≤ (2 ^ q * (r + 1).factorial : ℕ) *
        ((if Q ∈ D then 1 else 0 : ℕ) : ℤ) := by
      by_cases hQD : Q ∈ D
      · rw [if_pos hQD, Nat.cast_one, mul_one]
        rw [abs_of_nonneg (Int.emod_nonneg _ hNpos.ne')]
        exact (Int.emod_lt_of_pos (Φ₀ Q) hNpos).le.trans hNC
      · simp only [if_neg hQD, hs₁ Q hQD, abs_zero, Nat.cast_zero, mul_zero, le_refl]
    have hΦ₂Q := sumLocalDecoders_abs_le_edgewise hqr.le D Z c hc Q
    rw [Pi.add_apply]
    apply (abs_add_le _ _).trans
    have hh := add_le_add hΦ₁ hΦ₂Q
    simpa only [edgewiseDecoderCapacity, Nat.cast_mul, Nat.cast_add, mul_add] using hh

end Arxiv2411_18291
