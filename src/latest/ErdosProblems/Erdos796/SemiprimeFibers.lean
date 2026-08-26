import ErdosProblems.Erdos796.PairwiseOverlap
import ErdosProblems.Erdos796.Bonferroni
import ErdosProblems.Erdos796.Baseline

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Combining the semiprime fibres

This module packages the finite part of the semiprime-form argument.  The
intersection of two multiplier fibres is exactly the labelled overlap graph;
a coarse Bonferroni estimate then bounds the sum of all fibre sizes by one
semiprime union plus the pairwise-overlap error.  The union injects into the
ordinary semiprime pairs counted by `semiprimeCount`.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

namespace SemiprimeFibers

open PairwiseOverlap

/-- Canonically oriented prime-pair edges belonging to multiplier `s`. -/
def semiprimeFiberEdges (A : Finset ℕ) (s : ℕ)
    (Q R : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Q ×ˢ R).filter fun qr =>
    qr.1.Prime ∧ qr.2.Prime ∧ qr.2 < qr.1 ∧
      multipliedPrimePair s qr.1 qr.2 ∈ A

@[simp]
theorem mem_semiprimeFiberEdges {A : Finset ℕ} {s : ℕ}
    {Q R : Finset ℕ} {q r : ℕ} :
    (q, r) ∈ semiprimeFiberEdges A s Q R ↔
      q ∈ Q ∧ r ∈ R ∧ q.Prime ∧ r.Prime ∧ r < q ∧
        multipliedPrimePair s q r ∈ A := by
  simp [semiprimeFiberEdges, and_assoc]

/-- Pairwise intersection is exactly the graph used in the C4 argument. -/
theorem inter_semiprimeFiberEdges
    (A : Finset ℕ) (s t : ℕ) (Q R : Finset ℕ) :
    semiprimeFiberEdges A s Q R ∩ semiprimeFiberEdges A t Q R =
      overlapGraph A s t Q R := by
  ext qr
  rcases qr with ⟨q, r⟩
  simp only [Finset.mem_inter, mem_semiprimeFiberEdges, mem_overlapGraph]
  tauto

/-- Bonferroni bound for the total number of canonical prime-pair edges. -/
theorem sum_card_semiprimeFibres_le_union_add
    (A : Finset ℕ) (M : Finset ℕ) (Q R : Finset ℕ) (K : ℕ)
    (hoverlap : ∀ s ∈ M, ∀ t ∈ M, s ≠ t →
      (overlapGraph A s t Q R).card ≤ K) :
    ∑ s ∈ M, (semiprimeFiberEdges A s Q R).card ≤
      (M.biUnion fun s => semiprimeFiberEdges A s Q R).card +
        M.card ^ 2 * K := by
  apply sum_card_le_card_biUnion_add_sq_mul
  intro s hs t ht hst
  rw [inter_semiprimeFiberEdges]
  exact hoverlap s hs t ht hst

/-- Swapping the two labelled prime coordinates is injective. -/
theorem swap_injective : Function.Injective (fun qr : ℕ × ℕ => (qr.2, qr.1)) := by
  intro a b h
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- The union of all canonical prime-pair edges injects into the ordinary
semiprime pairs up to `n`. -/
theorem card_semiprimeFiber_union_le_semiprimeCount
    {n : ℕ} {A M Q R : Finset ℕ}
    (hA : Admissible n A)
    (hMpos : ∀ s ∈ M, 0 < s) :
    (M.biUnion fun s => semiprimeFiberEdges A s Q R).card ≤
      semiprimeCount n := by
  let E := M.biUnion fun s => semiprimeFiberEdges A s Q R
  let swap : ℕ × ℕ → ℕ × ℕ := fun qr => (qr.2, qr.1)
  have himageCard : (E.image swap).card = E.card := by
    rw [Finset.card_image_of_injective]
    exact swap_injective
  have hsub : E.image swap ⊆ semiprimePairs n := by
    intro rq hrq
    rcases Finset.mem_image.mp hrq with ⟨qr, hqr, rfl⟩
    rcases Finset.mem_biUnion.mp hqr with ⟨s, hs, hqrs⟩
    have hedge := mem_semiprimeFiberEdges.mp hqrs
    have hvalue := mem_positiveIcc.mp (hA.1 hedge.2.2.2.2.2)
    have hqpos := hedge.2.2.1.pos
    have hrpos := hedge.2.2.2.1.pos
    have hspos := hMpos s hs
    have hdiv : qr.2 * qr.1 ∣ multipliedPrimePair s qr.1 qr.2 := by
      refine ⟨s, ?_⟩
      simp [multipliedPrimePair]
      ring
    have hpairle : qr.2 * qr.1 ≤ multipliedPrimePair s qr.1 qr.2 :=
      Nat.le_of_dvd (by
        show 0 < s * qr.1 * qr.2
        exact Nat.mul_pos (Nat.mul_pos hspos hqpos) hrpos) hdiv
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Nat.mem_primesLE.mpr ⟨
          (Nat.le_mul_of_pos_right qr.2 hqpos).trans
            (hpairle.trans hvalue.2), hedge.2.2.2.1⟩
      · exact Nat.mem_primesLE.mpr ⟨by
          exact (Nat.le_mul_of_pos_left qr.1 hrpos).trans (hpairle.trans hvalue.2),
          hedge.2.2.1⟩
    · exact ⟨hedge.2.2.2.2.1.le, hpairle.trans hvalue.2⟩
  rw [semiprimeCount, ← himageCard]
  exact Finset.card_le_card hsub

/-- Finite semiprime-form estimate with a supplied uniform overlap bound. -/
theorem sum_card_semiprimeFibres_le_semiprimeCount_add
    {n K : ℕ} {A M Q R : Finset ℕ}
    (hA : Admissible n A)
    (hMpos : ∀ s ∈ M, 0 < s)
    (hoverlap : ∀ s ∈ M, ∀ t ∈ M, s ≠ t →
      (overlapGraph A s t Q R).card ≤ K) :
    ∑ s ∈ M, (semiprimeFiberEdges A s Q R).card ≤
      semiprimeCount n + M.card ^ 2 * K := by
  exact (sum_card_semiprimeFibres_le_union_add A M Q R K hoverlap).trans
    (Nat.add_le_add_right
      (card_semiprimeFiber_union_le_semiprimeCount hA hMpos) _)

end SemiprimeFibers

end Erdos796
