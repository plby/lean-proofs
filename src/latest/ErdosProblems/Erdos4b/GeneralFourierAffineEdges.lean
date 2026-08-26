/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierArithmeticEuler
import ErdosProblems.Erdos4b.GeneralSingularSeries

/-!
# Matching and exceptional-prime bounds for the actual affine graph

Primes dividing either slope produce no collision edge. Away from those
primes, distinct pre-sieved shifts imply that each vertex is in at most
one edge. Every edge prime divides the literal affine exceptional modulus.
The shift equivalence places the cutoff-dependent tuple on a fixed `Fin K`
index type for the uniform analytic limit.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem affineFourierCollisionEdges_eq_empty_of_dvd_m
    (H : Finset ℕ) {m q p : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    affineFourierCollisionEdges H m q p = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ij hij
  have h := affineFourierCollisionEdges_companion hp ij hij
  simp only [affineFourierCompanionSwitch, decide_eq_true_eq] at h
  exact h hpm

theorem affineFourierCollisionEdges_eq_empty_of_dvd_q
    (H : Finset ℕ) {m q p : ℕ} (hp : p.Prime) (hpq : p ∣ q) :
    affineFourierCollisionEdges H m q p = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ij hij
  have hmod := (Finset.mem_filter.mp hij).2
  have ha : m * (ij.1.val * q) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpq _) _)
  have hb : m * (ij.2.val * q) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpq _) _)
  have h10 : 1 ≡ 0 [MOD p] := by simpa using ((ha.add_right 1).symm.trans hmod).trans hb
  exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)

theorem card_affineFourierCollisionEdges_le_of_residue_injective
    (H : Finset ℕ) {m q p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (fun h : H ↦ -((h.val * q : ℕ) : ZMod p))) :
    (affineFourierCollisionEdges H m q p).card ≤ H.card := by
  classical
  by_cases hpm : p ∣ m
  · rw [affineFourierCollisionEdges_eq_empty_of_dvd_m H hp hpm]
    simp
  have hfst : Set.InjOn (Prod.fst : H × H → H) (affineFourierCollisionEdges H m q p) := by
    intro a ha b hb hab
    apply Prod.ext hab
    have hma := (Finset.mem_filter.mp ha).2
    have hmb := (Finset.mem_filter.mp hb).2
    have hright : m * (a.2.val * q) ≡ m * (b.2.val * q) [MOD p] :=
      hma.symm.trans (by simpa only [hab] using hmb)
    have hcancel := hright.cancel_left_of_coprime ((hp.coprime_iff_not_dvd).mpr hpm)
    apply hinj
    exact congrArg Neg.neg ((ZMod.natCast_eq_natCast_iff _ _ p).mpr hcancel)
  have hcard := Finset.card_le_card_of_injOn (s := affineFourierCollisionEdges H m q p)
    (t := Finset.univ) Prod.fst (fun a ha ↦ Finset.mem_univ _) hfst
  simpa only [Finset.card_univ, Fintype.card_coe] using hcard

theorem card_affineFourierCollisionEdges_preSieved_le
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p) :
    (affineFourierCollisionEdges (preSievedShifts K w) m q p).card ≤ K := by
  by_cases hpq : p ∣ q
  · rw [affineFourierCollisionEdges_eq_empty_of_dvd_q _ hp hpq]
    simp
  conv_rhs => rw [← card_preSievedShifts K w]
  apply card_affineFourierCollisionEdges_le_of_residue_injective _ hp
  intro a b hab
  exact preSievedFirstResidueMap_injOn hp hKw hwp hpq (Set.mem_univ a) (Set.mem_univ b) hab

theorem prime_dvd_crossExceptionalModulus_of_affineFourierEdge
    {H : Finset ℕ} {m q p : ℕ} (ij : H × H)
    (hij : ij ∈ affineFourierCollisionEdges H m q p) :
    p ∣ crossExceptionalModulus H m q := by
  have hdiff : (p : ℤ) ∣ crossAffineDifference m q (ij.2, ij.1) :=
    Nat.modEq_iff_dvd.mp (Finset.mem_filter.mp hij).2
  have hnat : p ∣ (crossAffineDifference m q (ij.2, ij.1)).natAbs := Int.natCast_dvd.mp hdiff
  exact hnat.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ (ij.2, ij.1)))

theorem affineFourierCollisionEdges_generic (H : Finset ℕ) {m q p : ℕ}
    (hnot : ¬p ∣ m * crossExceptionalModulus H m q) :
    affineFourierCollisionEdges H m q p = ∅ ∧ affineFourierCompanionSwitch m p = true := by
  classical
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ij hij
    exact hnot (dvd_mul_of_dvd_right
      (prime_dvd_crossExceptionalModulus_of_affineFourierEdge ij hij) m)
  · simp only [affineFourierCompanionSwitch, decide_eq_true_eq]
    exact fun hpm ↦ hnot (dvd_mul_of_dvd_left hpm _)

def preSievedShiftIndex (K w : ℕ) (i : Fin K) : preSievedShifts K w :=
  ⟨primorial w * i.val, Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩⟩

theorem preSievedShiftIndex_bijective (K w : ℕ) : Function.Bijective (preSievedShiftIndex K w) := by
  constructor
  · intro i j hij
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (primorial_pos w) (congrArg Subtype.val hij)
  · intro h
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h.property
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, Subtype.ext heq⟩

def preSievedShiftEquiv (K w : ℕ) : Fin K ≃ preSievedShifts K w :=
  Equiv.ofBijective (preSievedShiftIndex K w) (preSievedShiftIndex_bijective K w)

@[simp] theorem preSievedShiftEquiv_apply_val (K w : ℕ) (i : Fin K) :
    (preSievedShiftEquiv K w i).val = primorial w * i.val := rfl

def indexedPreSievedFourierEdges (K w m q p : ℕ) : Finset (Fin K × Fin K) :=
  (affineFourierCollisionEdges (preSievedShifts K w) m q p).map
    ((preSievedShiftEquiv K w).symm.prodCongr (preSievedShiftEquiv K w).symm).toEmbedding

theorem card_indexedPreSievedFourierEdges_le
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p) :
    (indexedPreSievedFourierEdges K w m q p).card ≤ K := by
  rw [indexedPreSievedFourierEdges, Finset.card_map]
  exact card_affineFourierCollisionEdges_preSieved_le hp hKw hwp

theorem indexedPreSievedFourierEdges_companion {K w m q p : ℕ} (hp : p.Prime)
    (ij : Fin K × Fin K) (hij : ij ∈ indexedPreSievedFourierEdges K w m q p) :
    affineFourierCompanionSwitch m p = true := by
  obtain ⟨ab, hab, heq⟩ := Finset.mem_map.mp hij
  exact affineFourierCollisionEdges_companion hp ab hab

theorem indexedPreSievedFourierEdges_generic {K w m q p : ℕ}
    (hnot : ¬p ∣ m * crossExceptionalModulus (preSievedShifts K w) m q) :
    indexedPreSievedFourierEdges K w m q p = ∅ ∧ affineFourierCompanionSwitch m p = true := by
  obtain ⟨hedges, hcomp⟩ := affineFourierCollisionEdges_generic (preSievedShifts K w) hnot
  exact ⟨by rw [indexedPreSievedFourierEdges, hedges, Finset.map_empty], hcomp⟩

end

end Erdos4b
