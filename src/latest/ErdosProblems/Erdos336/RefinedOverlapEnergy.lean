import ErdosProblems.Erdos336.OverlapFourierIdentity
import ErdosProblems.Erdos336.HighPowerDifferenceBound

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise Combinatorics.Additive

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def singletonOverlapCount (A : Finset G) : ℕ :=
  ((Finset.univ : Finset G).filter fun x =>
    (differenceOverlap A x).card = 1).card

/-- Refined Katz--Koester lower bound: if every subset of size at least two
expands fully with `A`, the only losses are singleton difference fibres.  The
zero difference contributes the exact `|A||2A|` term. -/
theorem refined_overlap_lower_bound
    (A : Finset G)
    (hexpand : ∀ B : Finset G, B ⊆ A → 2 ≤ B.card →
      A.card + B.card ≤ (A + B).card) :
    A.card ^ 3 + A.addEnergy A + A.card * (A + A).card ≤
      overlapSigma A + 2 * A.card ^ 2 + singletonOverlapCount A := by
  have hpoint (x : G) :
      A.card * (differenceOverlap A x).card +
          (differenceOverlap A x).card ^ 2 +
          (if x = 0 then A.card * (A + A).card else 0) ≤
        (differenceOverlap A x).card *
            (A + differenceOverlap A x).card +
          (if x = 0 then 2 * A.card ^ 2 else 0) +
          (if (differenceOverlap A x).card = 1 then 1 else 0) := by
    by_cases hx : x = 0
    · subst x
      simp [differenceOverlap, pow_two]
      omega
    · by_cases hr0 : (differenceOverlap A x).card = 0
      · simp [hx, hr0]
      · by_cases hr1 : (differenceOverlap A x).card = 1
        · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hr1
          simp [hx, hr1, hb, Finset.card_add_singleton]
        · have hr2 : 2 ≤ (differenceOverlap A x).card := by omega
          have he := hexpand (differenceOverlap A x)
            Finset.inter_subset_left hr2
          have hm := Nat.mul_le_mul_left (differenceOverlap A x).card he
          simp only [hx, if_false, hr1]
          nlinarith
  have hsum := Finset.sum_le_sum
    (fun x (_hx : x ∈ (Finset.univ : Finset G)) => hpoint x)
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum, sum_card_differenceOverlap,
    sum_card_differenceOverlap_sq_eq_addEnergy] at hsum
  change A.card ^ 3 + A.addEnergy A + A.card * (A + A).card ≤
    overlapSigma A + 2 * A.card ^ 2 + singletonOverlapCount A
  have hzero₁ : (∑ x : G,
      if x = 0 then A.card * (A + A).card else 0) =
      A.card * (A + A).card := by simp
  have hzero₂ : (∑ x : G,
      if x = 0 then 2 * A.card ^ 2 else 0) = 2 * A.card ^ 2 := by simp
  have hsingle : (∑ x : G,
      if (differenceOverlap A x).card = 1 then 1 else 0) =
      singletonOverlapCount A := by
    rw [singletonOverlapCount, Finset.card_eq_sum_ones]
    simp
  rw [hzero₁, hzero₂, hsingle] at hsum
  simpa [overlapSigma, pow_succ, mul_assoc] using hsum

/-- Singleton overlap values form a subset of the whole difference set. -/
theorem singletonOverlapCount_le_card_sub (A : Finset G) :
    singletonOverlapCount A ≤ (A - A).card := by
  let U : Finset G := (Finset.univ : Finset G).filter fun x =>
    (differenceOverlap A x).card = 1
  have hsub : U ⊆ A - A := by
    intro x hx
    have hr : (differenceOverlap A x).card = 1 :=
      (Finset.mem_filter.mp hx).2
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hr
    have hyMem : y ∈ differenceOverlap A x := by simp [hy]
    obtain ⟨hyA, hyShift⟩ := Finset.mem_inter.mp hyMem
    obtain ⟨a, ha, hya⟩ := Finset.mem_vadd_finset.mp hyShift
    apply Finset.mem_sub.mpr
    refine ⟨y, hyA, a, ha, ?_⟩
    simp only [vadd_eq_add] at hya
    rw [← hya]
    abel
  simpa [singletonOverlapCount, U] using Finset.card_le_card hsub

/-- Under the corrected high-power quarter-square difference estimate, the
singleton-fibre error in the refined overlap bound is at most `|A|²/4`. -/
theorem four_mul_singletonOverlapCount_le_sq
    (A : Finset G) (hcard : 21 ≤ A.card)
    (hdoub : 4 * (A + A).card < 9 * A.card) :
    4 * singletonOverlapCount A ≤ A.card ^ 2 := by
  exact le_trans (Nat.mul_le_mul_left 4 (singletonOverlapCount_le_card_sub A))
    (four_mul_card_sub_le_sq_of_nine_four A hcard hdoub)

end Erdos336
