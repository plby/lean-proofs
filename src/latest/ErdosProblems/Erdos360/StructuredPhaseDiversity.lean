/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.OrdinaryBridge
import ErdosProblems.Erdos360.PrimeStructuredQuotientNormalForm
import ErdosProblems.Erdos360.PrimeStructuredCommonScale

/-!
# Phase diversity inherited from the prime-structured source

The modular recursion only tests remainders of its initial residue set.  If
such a remainder still contains more than `U` elements and `e` divides its
closure modulus, then `d * e` divides more than `U` elements of the original
prime-structured source.  Hence `d * e ∣ n`.  Applying the retained
prime-factor normal form to the pivot itself shows that `e` divides its
target-divisor coordinate, so `e ≤ U`.  Ordinary divisor diversity up to a
parameter at least `U - 1` therefore supplies the required phase diversity.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- Pull back a set of residues to those elements of an integer set which
represent one of the residues. -/
private def residuePreimage {t : ℕ} (A : Finset ℕ)
    (R : Finset (ZMod t)) : Finset ℕ :=
  A.filter fun a ↦ (a : ZMod t) ∈ R

private lemma image_residuePreimage_eq
    {t : ℕ} {A : Finset ℕ} {R : Finset (ZMod t)}
    (hR : R ⊆ A.image fun a : ℕ ↦ (a : ZMod t)) :
    (residuePreimage A R).image (fun a : ℕ ↦ (a : ZMod t)) = R := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ha).2
  · intro hx
    obtain ⟨a, haA, hax⟩ := Finset.mem_image.mp (hR hx)
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨haA, hax ▸ hx⟩, hax⟩

private lemma card_residuePreimage_eq
    {lo hi t : ℕ} {A : Finset ℕ} {R : Finset (ZMod t)}
    (hA : A ⊆ Finset.Ico lo hi) (hwidth : hi - lo ≤ t)
    (hR : R ⊆ A.image fun a : ℕ ↦ (a : ZMod t)) :
    (residuePreimage A R).card = R.card := by
  let AR := residuePreimage A R
  have hAR : AR ⊆ Finset.Ico lo hi := by
    exact (Finset.filter_subset _ A).trans hA
  have hcard := card_image_zmod_eq_of_subset_Ico AR hAR hwidth
  rw [image_residuePreimage_eq hR] at hcard
  exact hcard.symm

private lemma divisor_of_closureModulus_dvd_residuePreimage
    {t : ℕ} [NeZero t] (ht : 0 < t)
    {A : Finset ℕ} {R : Finset (ZMod t)} {e a : ℕ}
    (heq : e ∣ closureModulus ht R)
    (ha : a ∈ residuePreimage A R) : e ∣ a := by
  have haR : (a : ZMod t) ∈ R := (Finset.mem_filter.mp ha).2
  have hqval : closureModulus ht R ∣ (a : ZMod t).val :=
    (closureModulus_spec ht R).2.2.1 _ (AddSubgroup.subset_closure haR)
  have heval : e ∣ (a : ZMod t).val := heq.trans hqval
  have het : e ∣ t := heq.trans (closureModulus_dvd ht R)
  simpa [ZMod.val_natCast, Nat.dvd_mod_iff het] using heval

/-- The exact phase-diversity invariant for an extracted subset of the
prime-structured source.  The lower cardinal bound ensures that every wide
remainder contains more than `U` residues; the upper parameter bound turns
the source normal form into the ordinary diversity range. -/
theorem phaseDiverse_of_primeStructured_extraction
    {n y U d t K lo hi : ℕ} [NeZero t] (ht : 0 < t)
    {W Z A : Finset ℕ}
    (hd : 0 < d) (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hAZ : A ⊆ Z) (htZ : t ∈ Z)
    (hA : A ⊆ Finset.Ico lo hi) (hwidth : hi - lo ≤ t)
    (hdiverse : DiverseSampling.DiverseNat A K)
    (hlarge : 2 * U < A.card) (hUK : U ≤ K + 1) :
    PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)) := by
  apply phaseDiverse_cast_of_diverse_of_closure_bounded
    ht A hA hwidth hdiverse
  intro R hRsub hwide e he heq
  let AR := residuePreimage A R
  have hARsubA : AR ⊆ A := Finset.filter_subset _ _
  have hARsubZ : AR ⊆ Z := hARsubA.trans hAZ
  have hARcard : AR.card = R.card :=
    card_residuePreimage_eq hA hwidth hRsub
  have hUR : U < R.card := by
    have hAcard : A.card =
        (A.image fun a : ℕ ↦ (a : ZMod t)).card :=
      (card_image_zmod_eq_of_subset_Ico A hA hwidth).symm
    rw [hAcard] at hlarge
    omega
  let X := AR.image fun a : ℕ ↦ d * a
  have hXsource : X ⊆ primeStructuredTestSet n y U := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hW (hscale a (hARsubZ ha))
  have hXcard : X.card = AR.card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  have hdeX : ∀ x ∈ X, d * e ∣ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr⟩ :=
      divisor_of_closureModulus_dvd_residuePreimage ht heq ha
    refine ⟨r, ?_⟩
    rw [hr]
    ring
  have hdeN : d * e ∣ n := by
    apply commonScale_dvd_target_of_large_subset_primeStructuredTestSet
      hXsource (Nat.mul_pos hd (by omega)) hdeX
    rw [hXcard, hARcard]
    exact hUR
  let hnormal := Classical.choice
    (primeStructured_quotient_normalForm hdn (hW (hscale t htZ)))
  have heN : e ∣ n := by
    exact (show e ∣ d * e from ⟨d, by ring⟩).trans hdeN
  have hqnotN : ¬ hnormal.q ∣ n := by
    intro hqn
    exact hnormal.quotient_not_target_factor
      (Nat.mem_primeFactors.mpr
        ⟨hnormal.quotient_prime, hqn, hnormal.target_ne_zero⟩)
  have hqnotE : ¬ hnormal.q ∣ e := fun hqe ↦ hqnotN (hqe.trans heN)
  have heqPrime : Nat.Coprime e hnormal.q :=
    (hnormal.quotient_prime.coprime_iff_not_dvd.mpr hqnotE).symm
  have het : e ∣ t := heq.trans (closureModulus_dvd ht R)
  have heu' : e ∣ hnormal.u' := by
    apply heqPrime.dvd_of_dvd_mul_right
    simpa only [hnormal.z_eq] using het
  have hu'pos : 0 < hnormal.u' := by
    have hu := hnormal.u_pos
    rw [hnormal.u_eq_scale_mul] at hu
    exact Nat.pos_of_mul_pos_left hu
  have heU : e ≤ U :=
    (Nat.le_of_dvd hu'pos heu').trans hnormal.reduced_le_cutoff
  exact heU.trans hUK

end Erdos360

#print axioms Erdos360.phaseDiverse_of_primeStructured_extraction
