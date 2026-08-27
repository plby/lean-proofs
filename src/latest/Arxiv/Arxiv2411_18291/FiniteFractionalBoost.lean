import Arxiv.Arxiv2411_18291.FractionalCorrectionBounds
import Arxiv.Arxiv2411_18291.RootedCliqueExtensions

/-!
# A finite criterion for regularizing clique sampling probabilities

Start every graph clique at probability one half. Averaged local decoders
correct the edge means exactly. If the explicit correction bound is at
most one half, all resulting coefficients remain valid probabilities.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_fractional_boost_of_uniform_correction (hqr : r ≤ q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val)
    (hZG : ∀ e ∈ G, ∀ z ∈ Z e, cliqueEdges r z ⊆ G)
    {d a : ℝ} (hnonempty : ∀ e ∈ G, (Z e).Nonempty)
    (hcounts : ∀ e ∈ G, |(((cliqueFamily G q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - d| ≤
      2 * a)
    (hbound : ∀ c : Block V r → ℝ, (∀ e ∈ G, |c e| ≤ a) →
      ∀ Q, |fractionalDecoderCorrection G Z c Q| ≤ 1 / 2) :
    ∃ p : Block V q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
      (∀ Q, ¬cliqueEdges r Q ⊆ G → p Q = 0) ∧
      boundary r p = fun e => if e ∈ G then d / 2 else 0 := by
  let D := cliqueFamily G q
  let w : Block V q → ℝ := fun Q => (1 / 2 : ℝ) * (indicator D Q : ℝ)
  let J : Block V r → ℝ := fun e => if e ∈ G then d / 2 else 0
  let c := J - boundary r w
  have hw (e : Block V r) : boundary r w e = ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) / 2 := by
    dsimp only [w]
    rw [boundary_mul]
    have hmap := boundary_map (r := r) (Int.castAddHom ℝ) (indicator D)
    simp only [Int.coe_castAddHom] at hmap
    rw [hmap]
    change (1 / 2 : ℝ) * ((boundary r (indicator D) e : ℤ) : ℝ) = _
    rw [boundary_indicator]
    push_cast
    ring
  have hwzero (e : Block V r) (he : e ∉ G) : boundary r w e = 0 := by
    rw [hw]
    have hzero : D.filter (fun Q => e.val ⊆ Q.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      have hQD : cliqueEdges r Q ⊆ G := (mem_filter.mp (mem_filter.mp hQ).1).2
      exact he (hQD ((mem_cliqueEdges _ _).mpr (mem_filter.mp hQ).2))
    simp only [hzero, card_empty, Nat.cast_zero, zero_div]
  have hc (e : Block V r) (he : e ∈ G) : |c e| ≤ a := by
    change |(if e ∈ G then d / 2 else 0) - boundary r w e| ≤ a
    rw [if_pos he, hw, abs_le]
    have hh := abs_le.mp (hcounts e he)
    change -(2 * a) ≤ ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - d ∧
      ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - d ≤ 2 * a at hh
    constructor <;> linarith only [hh.1, hh.2]
  let p := w + fractionalDecoderCorrection G Z c
  have hcorr (Q : Block V q) : |fractionalDecoderCorrection G Z c Q| ≤ 1 / 2 :=
    hbound c hc Q
  have hpzero (Q : Block V q) (hQ : ¬cliqueEdges r Q ⊆ G) : p Q = 0 := by
    have hQD : Q ∉ D := fun h => hQ (mem_filter.mp h).2
    change (1 / 2 : ℝ) * (indicator D Q : ℝ) + fractionalDecoderCorrection G Z c Q = 0
    rw [indicator_apply_of_notMem hQD, Int.cast_zero,
      fractionalDecoderCorrection_eq_zero G Z hZG c Q hQ, mul_zero, add_zero]
  refine ⟨p, ?_, hpzero, ?_⟩
  · intro Q
    by_cases hQ : cliqueEdges r Q ⊆ G
    · have hQD : Q ∈ D := mem_filter.mpr ⟨mem_univ _, hQ⟩
      have hh := abs_le.mp (hcorr Q)
      change 0 ≤ (1 / 2 : ℝ) * (indicator D Q : ℝ) + fractionalDecoderCorrection G Z c Q ∧
        (1 / 2 : ℝ) * (indicator D Q : ℝ) + fractionalDecoderCorrection G Z c Q ≤ 1
      rw [indicator_apply_of_mem hQD, Int.cast_one, mul_one]
      constructor <;> linarith only [hh.1, hh.2]
    · rw [hpzero Q hQ]
      norm_num
  · exact boundary_add_fractionalDecoderCorrection hqr G Z hnonempty hroot w J
      (fun e he => by simp only [J, if_neg he, hwzero e he])

theorem exists_fractional_boost_of_decoder_bounds (hqr : r ≤ q) (G : Hypergraph V r)
    (Z : Block V r → Finset (Block V (q + r)))
    (hroot : ∀ e ∈ G, ∀ z ∈ Z e, e.val ⊆ z.val)
    (hZG : ∀ e ∈ G, ∀ z ∈ Z e, cliqueEdges r z ⊆ G)
    {d a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (hsize : ∀ e ∈ G, L ≤ ((Z e).card : ℝ))
    (hcounts : ∀ e ∈ G, |(((cliqueFamily G q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - d| ≤
      2 * a)
    (hsmall : a / L * ((2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ)) *
      ((q + r).choose r * (Fintype.card V - q).choose r : ℕ) ≤ 1 / 2) :
    ∃ p : Block V q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
      (∀ Q, ¬cliqueEdges r Q ⊆ G → p Q = 0) ∧
      boundary r p = fun e => if e ∈ G then d / 2 else 0 := by
  refine exists_fractional_boost_of_uniform_correction hqr G Z hroot hZG ?_ hcounts ?_
  · intro e he
    apply card_pos.mp
    exact_mod_cast hL.trans_le (hsize e he)
  · intro c hc Q
    exact (fractionalDecoderCorrection_abs_le hqr G Z hroot c ha hL hsize hc Q).trans hsmall

end Arxiv2411_18291
