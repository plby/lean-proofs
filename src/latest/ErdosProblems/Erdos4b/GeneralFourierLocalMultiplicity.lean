/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAffineEdges
import ErdosProblems.Erdos4b.GeneralFourierRelativeComparison

/-!
# The Fourier exceptional count and the actual forbidden residues

Each affine edge is exactly one intersection of the two residue families.
Away from primes dividing the auxiliary variable, the Fourier singular
factor therefore agrees with the literal local singular factor, including
the primes dividing the companion slope.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem affine_modEq_iff_first_companion_residue
    {m p : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) (a b : ℕ) :
    m * a + 1 ≡ m * b [MOD p] ↔
      -(a : ZMod p) = (m : ZMod p)⁻¹ - (b : ZMod p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun h ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp h)
  have hnat : m * a + 1 ≡ m * b [MOD p] ↔
      (m : ZMod p) * (a : ZMod p) + 1 = (m : ZMod p) * (b : ZMod p) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (m * a + 1) (m * b) p).symm
  rw [hnat]
  constructor
  · intro h
    apply mul_left_cancel₀ hm0
    rw [mul_neg, mul_sub, mul_inv_cancel₀ hm0]
    linear_combination -h
  · intro h
    have hmul := congrArg (fun z : ZMod p ↦ (m : ZMod p) * z) h
    rw [mul_neg, mul_sub, mul_inv_cancel₀ hm0] at hmul
    linear_combination -hmul

theorem affineFourierEdge_iff_residue_eq {H : Finset ℕ} {m q p : ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m) (ij : H × H) :
    ij ∈ affineFourierCollisionEdges H m q p ↔
      -((ij.1.val * q : ℕ) : ZMod p) =
        (m : ZMod p)⁻¹ - ((ij.2.val * q : ℕ) : ZMod p) := by
  simp only [affineFourierCollisionEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact affine_modEq_iff_first_companion_residue hp hpm _ _

theorem card_affineFourierEdges_eq_card_residue_intersection
    (H : Finset ℕ) {m q p : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m)
    (hinj : Function.Injective (fun h : H ↦ -((h.val * q : ℕ) : ZMod p))) :
    (affineFourierCollisionEdges H m q p).card =
      (largeGapFirstLocalResidues H q p ∩ largeGapCompanionLocalResidues H m q p).card := by
  classical
  have hm0 : (m : ZMod p) ≠ 0 := fun h ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp h)
  apply Finset.card_bij (fun ij _ ↦ -((ij.1.val * q : ℕ) : ZMod p))
  · intro ij hij
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨ij.1, Finset.mem_attach _ _, rfl⟩
    · rw [largeGapCompanionLocalResidues, if_neg hm0]
      exact Finset.mem_image.mpr ⟨ij.2, Finset.mem_attach _ _,
        ((affineFourierEdge_iff_residue_eq hp hpm ij).mp hij).symm⟩
  · intro a ha b hb hab
    have hfst : a.1 = b.1 := hinj hab
    have haeq := (affineFourierEdge_iff_residue_eq hp hpm a).mp ha
    have hbeq := (affineFourierEdge_iff_residue_eq hp hpm b).mp hb
    have hcomp : (m : ZMod p)⁻¹ - ((a.2.val * q : ℕ) : ZMod p) =
        (m : ZMod p)⁻¹ - ((b.2.val * q : ℕ) : ZMod p) := haeq.symm.trans (hab.trans hbeq)
    exact Prod.ext hfst (hinj (congrArg Neg.neg (sub_right_inj.mp hcomp)))
  · intro z hz
    obtain ⟨hzF, hzE⟩ := Finset.mem_inter.mp hz
    obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hzF
    rw [largeGapCompanionLocalResidues, if_neg hm0] at hzE
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hzE
    refine ⟨(i, j), (affineFourierEdge_iff_residue_eq hp hpm (i, j)).mpr ?_, hiz⟩
    exact hiz.trans hjz.symm

theorem localMultiplicity_add_affineEdges_card_preSieved
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ m) :
    largeGapLocalMultiplicity (preSievedShifts K w) m q p +
      (affineFourierCollisionEdges (preSievedShifts K w) m q p).card = 2 * K := by
  have hinj : Function.Injective (fun h : preSievedShifts K w ↦
      -((h.val * q : ℕ) : ZMod p)) := by
    intro a b hab
    exact preSievedFirstResidueMap_injOn hp hKw hwp hpq (Set.mem_univ a) (Set.mem_univ b) hab
  rw [card_affineFourierEdges_eq_card_residue_intersection _ hp hpm hinj]
  unfold largeGapLocalMultiplicity largeGapLocalForbiddenResidues
  rw [Finset.card_union_add_card_inter,
    card_largeGapFirstLocalResidues_preSievedShifts hp hKw hwp hpq,
    card_largeGapCompanionLocalResidues_preSievedShifts hp hKw hwp hpq hpm]
  omega

theorem localMultiplicity_add_FourierExceptionalCount_preSieved
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p) (hpq : ¬p ∣ q) :
    largeGapLocalMultiplicity (preSievedShifts K w) m q p +
      doubledFourierExceptionalCount Finset.univ
        (affineFourierCollisionEdges (preSievedShifts K w) m q p)
        (affineFourierCompanionSwitch m p) = 2 * K := by
  by_cases hpm : p ∣ m
  · have hmult : largeGapLocalMultiplicity (preSievedShifts K w) m q p = K := by
      unfold largeGapLocalMultiplicity largeGapLocalForbiddenResidues
      rw [largeGapCompanionLocalResidues_eq_empty_of_dvd hpm, Finset.union_empty]
      exact card_largeGapFirstLocalResidues_preSievedShifts hp hKw hwp hpq
    rw [hmult, affineFourierCollisionEdges_eq_empty_of_dvd_m _ hp hpm]
    simp [doubledFourierExceptionalCount, affineFourierCompanionSwitch, hpm,
      card_preSievedShifts, two_mul]
  · simpa [doubledFourierExceptionalCount, affineFourierCompanionSwitch, hpm] using
      localMultiplicity_add_affineEdges_card_preSieved hp hKw hwp hpq hpm

theorem doubledFourierSingularFactor_eq_actual_localFactor
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p) (hpq : ¬p ∣ q) :
    doubledFourierSingularFactor (affineFourierCollisionEdges (preSievedShifts K w) m q)
      (affineFourierCompanionSwitch m) p =
        (largeGapLocalFactor (preSievedShifts K w) m q p : ℂ) := by
  have hcount := localMultiplicity_add_FourierExceptionalCount_preSieved (m := m) hp hKw hwp hpq
  have hcast : (Fintype.card (preSievedShifts K w ⊕ preSievedShifts K w) : ℂ) -
      doubledFourierExceptionalCount Finset.univ
        (affineFourierCollisionEdges (preSievedShifts K w) m q p)
        (affineFourierCompanionSwitch m p) =
      largeGapLocalMultiplicity (preSievedShifts K w) m q p := by
    have hc : (largeGapLocalMultiplicity (preSievedShifts K w) m q p : ℂ) +
        doubledFourierExceptionalCount Finset.univ
          (affineFourierCollisionEdges (preSievedShifts K w) m q p)
          (affineFourierCompanionSwitch m p) = 2 * (K : ℂ) := by exact_mod_cast hcount
    simp only [Fintype.card_sum, Fintype.card_coe, card_preSievedShifts, Nat.cast_add]
    linear_combination -hc
  unfold doubledFourierSingularFactor
  rw [hcast]
  unfold largeGapLocalFactor
  push_cast
  rw [div_eq_mul_inv, inv_pow]
  simp only [Fintype.card_sum, Fintype.card_coe, card_preSievedShifts, two_mul]

end

end Erdos4b
