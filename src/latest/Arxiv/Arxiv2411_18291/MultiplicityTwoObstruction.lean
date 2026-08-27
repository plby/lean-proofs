import Arxiv.Arxiv2411_18291.MagnitudeLevelBoundary

/-!
# Multiplicity two cannot generate a single-edge vector

If every edge belongs to at most two cliques, any odd transformation of
the clique coefficients preserves every zero boundary coordinate. Apply
this to each absolute-value level. Each transformed boundary coordinate
has absolute value at most two. A boundary supported on one edge is also
divisible by `choose(q,r)`, so it vanishes whenever that number exceeds two.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem boundary_single_edge_dvd (Φ : Block V q → ℤ) (e : Block V r)
    (hs : ∀ f : Block V r, f ≠ e → boundary r Φ f = 0) :
    (q.choose r : ℤ) ∣ boundary r Φ e := by
  have hJ : IntegrallyDecomposable q (boundary r Φ) := ⟨Φ, rfl⟩
  have hd := hJ.degree_dvd ∅ (by simp)
  simp only [card_empty, Nat.sub_zero, degree, empty_subset, if_true] at hd
  have heq : (∑ f : Block V r, boundary r Φ f) = boundary r Φ e := by
    apply sum_eq_single e
    · intro f _ hfe
      exact hs f hfe
    · simp
  rwa [heq] at hd

theorem boundary_single_edge_eq_zero_of_multiplicity_two (D : Finset (Block V q))
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (hk : 2 < q.choose r) (Φ : Block V q → ℤ) (hΦ : ∀ Q, Q ∉ D → Φ Q = 0)
    (e : Block V r) (hs : ∀ f : Block V r, f ≠ e → boundary r Φ f = 0) :
    boundary r Φ e = 0 := by
  have hlevel (t : ℕ) : boundary r (fun Q => intMagnitudeLevel t (Φ Q)) e = 0 := by
    have hs' : ∀ f : Block V r, f ≠ e →
        boundary r (fun Q => intMagnitudeLevel t (Φ Q)) f = 0 := by
      intro f hf
      exact boundary_odd_zero_of_two D hmult Φ hΦ (intMagnitudeLevel t)
        (intMagnitudeLevel_zero t) (intMagnitudeLevel_neg t) f (hs f hf)
    have hd := boundary_single_edge_dvd (fun Q => intMagnitudeLevel t (Φ Q)) e hs'
    have ha := abs_boundary_magnitudeLevel_le_two D hmult Φ hΦ t e
    have ha' : (boundary r (fun Q => intMagnitudeLevel t (Φ Q)) e).natAbs ≤ 2 := by
      rw [Int.abs_eq_natAbs] at ha
      exact_mod_cast ha
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    simpa only [Int.natAbs_natCast] using ha'.trans_lt hk
  have hrec := boundary_magnitudeLevel_sum Φ e
  simp only [hlevel, mul_zero, sum_const_zero] at hrec
  exact hrec.symm

theorem GeneratedBy.eq_zero_of_multiplicity_two_supported_singleton
    {D : Finset (Block V q)}
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (hk : 2 < q.choose r) {J : Block V r → ℤ} (hJ : GeneratedBy D J)
    (e : Block V r) (hs : ∀ f : Block V r, f ≠ e → J f = 0) : J = 0 := by
  obtain ⟨Φ, hΦ, hsupport⟩ := hJ
  have he := boundary_single_edge_eq_zero_of_multiplicity_two D hmult hk Φ hsupport e
    (by simpa only [hΦ] using hs)
  rw [hΦ] at he
  funext f
  by_cases hf : f = e
  · simpa only [hf, Pi.zero_apply] using he
  · exact hs f hf

theorem not_generatedBy_single_edge_of_multiplicity_two (D : Finset (Block V q))
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (hk : 2 < q.choose r) (e : Block V r) {N : ℤ} (hN : N ≠ 0) :
    ¬GeneratedBy D (fun f => if f = e then N else 0) := by
  intro h
  have he := h.eq_zero_of_multiplicity_two_supported_singleton hmult hk e
    (fun f hf => if_neg hf)
  have hh := congrFun he e
  simp only [Pi.zero_apply] at hh
  exact hN hh

end Arxiv2411_18291
