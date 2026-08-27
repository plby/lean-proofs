import Arxiv.Arxiv2411_18291.DecoderBound

/-!
# Local decoders inside a larger vertex set

The absorber construction uses a decoder on each chosen `(q+r)`-set `Z_e`
inside `[n]`. This module checks that the decoder extended by zero has the
same boundary in the ambient graph, including at edges outside `Z_e`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

/-- Extend a decoder supported on `Z` by zero to the ambient clique space. -/
def localDecoderOn (q : ℕ) (Z : Finset V) (e : Block V r) (Q : Block V q) : ℤ :=
  if Q.val ⊆ Z then localDecoder q e Q else 0

private theorem decoder_sum_at_on (Z : Finset V) (hZ : Z.card = q + r)
    (hqr : r ≤ q) (e' : Block V r) (heZ : e'.val ⊆ Z)
    (I : Finset V) (hIZ : I ⊆ Z) (hIr : I.card ≤ r) :
    (∑ Q : Block V q, if e'.val ⊆ Q.val then if Q.val ⊆ Z then
        if Disjoint I Q.val then decoderWeight q r I.card else 0 else 0 else 0) =
      if Disjoint I e'.val then (-1 : ℤ) ^ I.card * q.descFactorial r else 0 := by
  by_cases hIe : Disjoint I e'.val
  · rw [if_pos hIe]
    have hcard : (univ.filter fun Q : Block V q => e'.val ⊆ Q.val ∧ Q.val ⊆ Z \ I).card =
        (q - I.card).choose (r - I.card) := by
      rw [card_blocks_between e'.val (Z \ I) (subset_sdiff.mpr ⟨heZ, hIe.symm⟩)
        (by simpa only [e'.property] using hqr),
        card_sdiff_of_subset hIZ, hZ, e'.property]
      have hsub : q + r - I.card - r = q - I.card := by omega
      rw [hsub, ← Nat.choose_symm (by omega : q - r ≤ q - I.card)]
      congr 1
      omega
    calc
      _ = ∑ Q ∈ univ.filter (fun Q : Block V q => e'.val ⊆ Q.val ∧ Q.val ⊆ Z \ I),
          decoderWeight q r I.card := by
        rw [sum_filter]
        apply sum_congr rfl
        intro Q _
        simp only [subset_sdiff]
        have hcomm : Disjoint Q.val I ↔ Disjoint I Q.val := disjoint_comm
        simp only [hcomm]
        split_ifs <;> simp_all
      _ = _ := by
        rw [sum_const, hcard, nsmul_eq_mul, mul_comm, decoderWeight_mul_choose hIr]
  · rw [if_neg hIe]
    apply sum_eq_zero
    intro Q _
    by_cases heQ : e'.val ⊆ Q.val
    · have hIQ : ¬Disjoint I Q.val := fun h => hIe (disjoint_of_subset_right heQ h)
      simp [heQ, hIQ]
    · simp [heQ]

/-- A decoder on `Z` decodes its distinguished edge in the entire ambient
hypergraph, not just in the induced graph on `Z`. -/
theorem boundary_localDecoderOn (Z : Finset V) (hZ : Z.card = q + r) (hqr : r ≤ q)
    (e : Block V r) (heZ : e.val ⊆ Z) :
    boundary r (localDecoderOn q Z e) =
      fun e' => if e' = e then (q.descFactorial r : ℤ) else 0 := by
  funext e'
  by_cases he'Z : e'.val ⊆ Z
  · unfold boundary localDecoderOn localDecoder
    simp only [Finset.ite_sum_zero]
    rw [sum_comm]
    calc
      _ = ∑ I ∈ e.val.powerset,
          if Disjoint I e'.val then (-1 : ℤ) ^ I.card * q.descFactorial r else 0 := by
        apply sum_congr rfl
        intro I hI
        have hIe := mem_powerset.mp hI
        exact decoder_sum_at_on Z hZ hqr e' he'Z I (hIe.trans heZ)
          (by simpa only [e.property] using card_le_card hIe)
      _ = _ := decoder_sign_sum e e' _
  · have hne : e' ≠ e := by
      rintro rfl
      exact he'Z heZ
    rw [if_neg hne]
    unfold boundary localDecoderOn
    apply sum_eq_zero
    intro Q _
    by_cases hQZ : Q.val ⊆ Z
    · have heQ : ¬e'.val ⊆ Q.val := fun h => he'Z (h.trans hQZ)
      simp [heQ]
    · simp [hQZ]

omit [Fintype V] in
theorem localDecoderOn_abs_le (hqr : r ≤ q) (Z : Finset V)
    (e : Block V r) (Q : Block V q) :
    |localDecoderOn q Z e Q| ≤ (2 ^ q * r.factorial : ℕ) := by
  unfold localDecoderOn
  split_ifs
  · exact localDecoder_abs_le hqr e Q
  · simp

/-- The exact form of the local decoder used in the absorber construction. -/
theorem local_decoder_on (Z : Finset V) (hZ : Z.card = q + r) (hqr : r ≤ q)
    (e : Block V r) (heZ : e.val ⊆ Z) :
    ∃ Ψ : Block V q → ℤ,
      boundary r Ψ = (fun e' => if e' = e then ((r.factorial * q.choose r : ℕ) : ℤ) else 0) ∧
      (∀ Q, ¬Q.val ⊆ Z → Ψ Q = 0) ∧
      ∀ Q, |Ψ Q| ≤ (2 ^ q * r.factorial : ℕ) := by
  refine ⟨localDecoderOn q Z e, ?_, ?_, localDecoderOn_abs_le hqr Z e⟩
  · simpa only [Nat.descFactorial_eq_factorial_mul_choose] using
      boundary_localDecoderOn Z hZ hqr e heZ
  · intro Q hQ
    simp [localDecoderOn, hQ]

end Arxiv2411_18291
