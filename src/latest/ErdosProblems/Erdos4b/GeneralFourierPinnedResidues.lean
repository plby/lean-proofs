/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedRoots

/-!
# Literal forbidden residues for the pinned affine forms

The definition includes every shift, including the pinned coordinate.
Under the residual-prime conditions the pinned coordinate contributes
no root, and the forbidden set is exactly the union of the two reduced
root families. It is empty at the pre-sieved primes.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance pinnedResiduesDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def pinnedFirstAffine {K : ℕ} (h : Fin K) (w p₀ p : ℕ) (i : Fin K) (q : ZMod p) : ZMod p :=
  (p₀ : ZMod p) + (primorial w : ZMod p) * ((i.val : ZMod p) - h.val) * q

def pinnedLocalForbiddenResidues {K : ℕ} (h : Fin K) (w m p₀ : ℕ)
    (p : Nat.Primes) : Finset (ZMod p) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  exact Finset.univ.filter (fun q ↦ ∃ i : Fin K,
    pinnedFirstAffine h w p₀ p i q = 0 ∨ (m : ZMod p) * pinnedFirstAffine h w p₀ p i q = 1)

def pinnedLocalMultiplicity {K : ℕ} (h : Fin K) (w m p₀ : ℕ) (p : Nat.Primes) : ℕ :=
  (pinnedLocalForbiddenResidues h w m p₀ p).card

def pinnedFirstLocalResidues {K : ℕ} (h : Fin K) (w p₀ p : ℕ) : Finset (ZMod p) :=
  Finset.univ.image (pinnedFirstRoot h w p₀ p)

def pinnedCompanionLocalResidues {K : ℕ} (h : Fin K) (w m p₀ p : ℕ) : Finset (ZMod p) :=
  if p ∣ m then ∅ else Finset.univ.image (pinnedCompanionRoot h w m p₀ p)

theorem mem_pinnedLocalForbiddenResidues_iff
    {K : ℕ} (h : Fin K) (w m p₀ : ℕ) (p : Nat.Primes) (q : ZMod p) :
    q ∈ pinnedLocalForbiddenResidues h w m p₀ p ↔
      ∃ i : Fin K, pinnedFirstAffine h w p₀ p i q = 0 ∨
        (m : ZMod p) * pinnedFirstAffine h w p₀ p i q = 1 := by
  simp only [pinnedLocalForbiddenResidues, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pinnedLocalForbiddenResidues_eq_union
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    pinnedLocalForbiddenResidues h w m p₀ p =
      pinnedFirstLocalResidues h w p₀ p ∪ pinnedCompanionLocalResidues h w m p₀ p := by
  let : Fact p.val.Prime := ⟨p.property⟩
  ext q
  rw [mem_pinnedLocalForbiddenResidues_iff, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    have hih : i ≠ h := by
      intro heq
      subst i
      simp only [pinnedFirstAffine, sub_self, mul_zero, zero_mul, add_zero] at hi
      rcases hi with hi | hi
      · exact hpp₀ ((ZMod.natCast_eq_zero_iff p₀ p).mp hi)
      · exact hnum (sub_eq_zero.mpr hi.symm)
    let j : PinnedShiftIndex h := ⟨i, hih⟩
    rcases hi with hi | hi
    · left
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      exact ((pinnedFirstRoot_iff_affine_zero h p.property hKw hwp j q).mpr hi).symm
    · by_cases hpm : p.val ∣ m
      · have hm0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
        rw [hm0, zero_mul] at hi
        exact (zero_ne_one hi).elim
      · right
        rw [pinnedCompanionLocalResidues, if_neg hpm]
        apply Finset.mem_image.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        exact ((pinnedCompanionRoot_iff_affine_one h p.property hKw hwp hpm j q).mpr hi).symm
  · rintro (hq | hq)
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hq
      exact ⟨i.val, Or.inl
        ((pinnedFirstRoot_iff_affine_zero h p.property hKw hwp i q).mp heq.symm)⟩
    · unfold pinnedCompanionLocalResidues at hq
      split_ifs at hq with hpm
      · exact (Finset.notMem_empty _ hq).elim
      · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hq
        exact ⟨i.val, Or.inr
          ((pinnedCompanionRoot_iff_affine_one h p.property hKw hwp hpm i q).mp heq.symm)⟩

theorem pinnedLocalForbiddenResidues_eq_empty_of_le_cutoff
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hpw : p.val ≤ w)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    pinnedLocalForbiddenResidues h w m p₀ p = ∅ := by
  have hP : (primorial w : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr
    (p.property.dvd_primorial_iff.mpr hpw)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨i, hi⟩ := (mem_pinnedLocalForbiddenResidues_iff h w m p₀ p q).mp hq
  simp only [pinnedFirstAffine, hP, zero_mul, add_zero] at hi
  rcases hi with hi | hi
  · exact hpp₀ ((ZMod.natCast_eq_zero_iff p₀ p).mp hi)
  · exact hnum (sub_eq_zero.mpr hi.symm)

theorem card_pinnedFirstLocalResidues
    {K w p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p ∣ p₀) :
    (pinnedFirstLocalResidues h w p₀ p).card = Fintype.card (PinnedShiftIndex h) := by
  rw [pinnedFirstLocalResidues, Finset.card_image_of_injective _
    (pinnedFirstRoot_injective h hp hKw hwp hpp₀), Finset.card_univ]

theorem card_pinnedCompanionLocalResidues
    {K w m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpm : ¬p ∣ m) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    (pinnedCompanionLocalResidues h w m p₀ p).card = Fintype.card (PinnedShiftIndex h) := by
  rw [pinnedCompanionLocalResidues, if_neg hpm, Finset.card_image_of_injective _
    (pinnedCompanionRoot_injective h hp hKw hwp hpm hnum), Finset.card_univ]

end

end Erdos4b
