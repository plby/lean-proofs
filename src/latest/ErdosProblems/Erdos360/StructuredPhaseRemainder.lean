/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.CanonicalClosureCoordinates
import ErdosProblems.Erdos360.SourceAdaptiveIntegration
import ErdosProblems.Erdos360.PrimeStructuredCommonScale

/-!
# Integer representatives of source-adaptive remainders

Every remainder in the modular recursion is a subset of the initial image
of the integer seed.  Filtering the seed by that remainder gives canonical
integer representatives.  On the short dyadic interval reduction modulo
the pivot is injective, so this operation preserves cardinality as well as
all inherited arithmetic properties.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- Pull a residue subset back to its representatives in an integer seed. -/
def structuredResiduePreimage {t : ℕ} (A : Finset ℕ)
    (R : Finset (ZMod t)) : Finset ℕ :=
  A.filter fun a ↦ (a : ZMod t) ∈ R

lemma structuredResiduePreimage_subset
    {t : ℕ} (A : Finset ℕ) (R : Finset (ZMod t)) :
    structuredResiduePreimage A R ⊆ A :=
  Finset.filter_subset _ _

lemma ordinaryResidues_structuredResiduePreimage_eq
    {t : ℕ} {A : Finset ℕ} {R : Finset (ZMod t)}
    (hR : R ⊆ ordinaryResidues t A) :
    ordinaryResidues t (structuredResiduePreimage A R) = R := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ha).2
  · intro hx
    obtain ⟨a, haA, hax⟩ := Finset.mem_image.mp (hR hx)
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨haA, hax ▸ hx⟩, hax⟩

lemma card_structuredResiduePreimage_eq
    {lo hi t : ℕ} {A : Finset ℕ} {R : Finset (ZMod t)}
    (hA : A ⊆ Finset.Ico lo hi) (hwidth : hi - lo ≤ t)
    (hR : R ⊆ ordinaryResidues t A) :
    (structuredResiduePreimage A R).card = R.card := by
  let P := structuredResiduePreimage A R
  have hP : P ⊆ Finset.Ico lo hi :=
    (structuredResiduePreimage_subset A R).trans hA
  have hcard := card_image_zmod_eq_of_subset_Ico P hP hwidth
  rw [show P.image (fun a : ℕ ↦ (a : ZMod t)) = R by
    simpa [ordinaryResidues, P] using
      ordinaryResidues_structuredResiduePreimage_eq hR] at hcard
  exact hcard.symm

/-- Integer representatives of the remainder at a source-adaptive phase. -/
noncomputable def sourceAdaptiveIntegerRemainder
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (ordinaryResidues t A))
    (Q i : ℕ) : Finset ℕ :=
  structuredResiduePreimage A
    (sourceAdaptiveRemainder ht (ordinaryResidues t A) {0} (by simp)
      hdiverse Q i)

lemma sourceAdaptiveIntegerRemainder_subset
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (ordinaryResidues t A))
    (Q i : ℕ) :
    sourceAdaptiveIntegerRemainder ht A hdiverse Q i ⊆ A :=
  structuredResiduePreimage_subset _ _

lemma ordinaryResidues_sourceAdaptiveIntegerRemainder
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (ordinaryResidues t A))
    (Q i : ℕ) :
    ordinaryResidues t (sourceAdaptiveIntegerRemainder ht A hdiverse Q i) =
      sourceAdaptiveRemainder ht (ordinaryResidues t A) {0} (by simp)
        hdiverse Q i := by
  apply ordinaryResidues_structuredResiduePreimage_eq
  exact sourceAdaptiveRemainder_subset_initial
    ht (ordinaryResidues t A) {0} (by simp) hdiverse Q i

lemma card_sourceAdaptiveIntegerRemainder
    {lo hi t : ℕ} [NeZero t] (ht : 0 < t) {A : Finset ℕ}
    (hA : A ⊆ Finset.Ico lo hi) (hwidth : hi - lo ≤ t)
    (hdiverse : PhaseDiverse ht (ordinaryResidues t A))
    (Q i : ℕ) :
    (sourceAdaptiveIntegerRemainder ht A hdiverse Q i).card =
      (sourceAdaptiveRemainder ht (ordinaryResidues t A) {0} (by simp)
        hdiverse Q i).card := by
  apply card_structuredResiduePreimage_eq hA hwidth
  exact sourceAdaptiveRemainder_subset_initial
    ht (ordinaryResidues t A) {0} (by simp) hdiverse Q i

lemma sourceAdaptiveIntegerRemainder_lt
    {t : ℕ} [NeZero t] (ht : 0 < t) {A : Finset ℕ}
    (hAt : ∀ a ∈ A, a < t)
    (hdiverse : PhaseDiverse ht (ordinaryResidues t A))
    (Q i : ℕ) :
    ∀ p ∈ sourceAdaptiveIntegerRemainder ht A hdiverse Q i, p < t := by
  intro p hp
  exact hAt p (sourceAdaptiveIntegerRemainder_subset ht A hdiverse Q i hp)

lemma sourceAdaptiveIntegerRemainder_coprime
    {t M : ℕ} [NeZero t] (ht : 0 < t) {A : Finset ℕ}
    (hcop : ∀ a ∈ A, Nat.Coprime M a)
    (hdiverse : PhaseDiverse ht (ordinaryResidues t A))
    (Q i : ℕ) :
    ∀ p ∈ sourceAdaptiveIntegerRemainder ht A hdiverse Q i,
      Nat.Coprime M p := by
  intro p hp
  exact hcop p (sourceAdaptiveIntegerRemainder_subset ht A hdiverse Q i hp)

/-- A divisor of the closure modulus divides every integer representative
of a residue in the closed set.  The representative need not be smaller
than the ambient modulus: divisibility of the modulus removes the reduction
modulo `t`. -/
lemma divisor_of_closureModulus_dvd_structuredResiduePreimage
    {t : ℕ} [NeZero t] (ht : 0 < t)
    {A : Finset ℕ} {R : Finset (ZMod t)} {e a : ℕ}
    (heq : e ∣ closureModulus ht R)
    (ha : a ∈ structuredResiduePreimage A R) : e ∣ a := by
  have haR : (a : ZMod t) ∈ R := (Finset.mem_filter.mp ha).2
  have hqval : closureModulus ht R ∣ (a : ZMod t).val :=
    (closureModulus_spec ht R).2.2.1 _ (AddSubgroup.subset_closure haR)
  have heval : e ∣ (a : ZMod t).val := heq.trans hqval
  have het : e ∣ t := heq.trans (closureModulus_dvd ht R)
  simpa [ZMod.val_natCast, Nat.dvd_mod_iff het] using heval

/-- A wide remainder of a prime-structured extracted set has closure
modulus at most the divisor cutoff.  More than `U` representatives share
the accumulated divisor `d*q`, so that divisor divides the target.  The
retained prime coordinate of one pivot is absent from the target; cancelling
it forces `q` into the pivot's target-divisor coordinate, which is at most
`U`. -/
theorem scale_mul_closureModulus_le_cutoff_of_primeStructured_remainder
    {n y U d t lo hi : ℕ} [NeZero t] (ht : 0 < t)
    {W Z A : Finset ℕ} {R : Finset (ZMod t)}
    (hd : 0 < d) (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hAZ : A ⊆ Z) (htZ : t ∈ Z)
    (hA : A ⊆ Finset.Ico lo hi) (hwidth : hi - lo ≤ t)
    (hR : R ⊆ ordinaryResidues t A) (hwide : U < R.card) :
    d * closureModulus ht R ≤ U := by
  let q := closureModulus ht R
  let P := structuredResiduePreimage A R
  have hPsubA : P ⊆ A := structuredResiduePreimage_subset A R
  have hPsubZ : P ⊆ Z := hPsubA.trans hAZ
  have hPcard : P.card = R.card :=
    card_structuredResiduePreimage_eq hA hwidth hR
  let X := P.image fun a : ℕ ↦ d * a
  have hXsource : X ⊆ primeStructuredTestSet n y U := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hW (hscale a (hPsubZ ha))
  have hXcard : X.card = P.card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  have hdqX : ∀ x ∈ X, d * q ∣ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr⟩ :=
      divisor_of_closureModulus_dvd_structuredResiduePreimage ht
        (show q ∣ closureModulus ht R from dvd_rfl) ha
    refine ⟨r, ?_⟩
    rw [hr]
    ring
  have hdqN : d * q ∣ n := by
    apply commonScale_dvd_target_of_large_subset_primeStructuredTestSet
      hXsource (Nat.mul_pos hd (closureModulus_pos ht R)) hdqX
    rw [hXcard, hPcard]
    exact hwide
  let normal := Classical.choice
    (primeStructured_quotient_normalForm hdn (hW (hscale t htZ)))
  have hqN : q ∣ n := by
    exact (show q ∣ d * q from ⟨d, by ring⟩).trans hdqN
  have hprimeNotN : ¬ normal.q ∣ n := by
    intro hqn
    exact normal.quotient_not_target_factor
      (Nat.mem_primeFactors.mpr
        ⟨normal.quotient_prime, hqn, normal.target_ne_zero⟩)
  have hprimeNotQ : ¬ normal.q ∣ q :=
    fun hpq ↦ hprimeNotN (hpq.trans hqN)
  have hcop : Nat.Coprime q normal.q :=
    (normal.quotient_prime.coprime_iff_not_dvd.mpr hprimeNotQ).symm
  have hqt : q ∣ t := closureModulus_dvd ht R
  have hqu' : q ∣ normal.u' := by
    apply hcop.dvd_of_dvd_mul_right
    simpa only [normal.z_eq] using hqt
  have hu'pos : 0 < normal.u' := by
    have hu := normal.u_pos
    rw [normal.u_eq_scale_mul] at hu
    exact Nat.pos_of_mul_pos_left hu
  have hqu'le : q ≤ normal.u' := Nat.le_of_dvd hu'pos hqu'
  calc
    d * q ≤ d * normal.u' := Nat.mul_le_mul_left d hqu'le
    _ = normal.u := normal.u_eq_scale_mul.symm
    _ ≤ U := normal.u_le_cutoff

/-- In particular, the closure modulus itself is at most the cutoff. -/
theorem closureModulus_le_cutoff_of_primeStructured_remainder
    {n y U d t lo hi : ℕ} [NeZero t] (ht : 0 < t)
    {W Z A : Finset ℕ} {R : Finset (ZMod t)}
    (hd : 0 < d) (hdn : d ∣ n)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hAZ : A ⊆ Z) (htZ : t ∈ Z)
    (hA : A ⊆ Finset.Ico lo hi) (hwidth : hi - lo ≤ t)
    (hR : R ⊆ ordinaryResidues t A) (hwide : U < R.card) :
    closureModulus ht R ≤ U := by
  have hscaled :=
    scale_mul_closureModulus_le_cutoff_of_primeStructured_remainder
      ht hd hdn hW hscale hAZ htZ hA hwidth hR hwide
  exact (Nat.le_mul_of_pos_left _ hd).trans hscaled

end Erdos360

#print axioms Erdos360.ordinaryResidues_sourceAdaptiveIntegerRemainder
#print axioms Erdos360.card_sourceAdaptiveIntegerRemainder
#print axioms Erdos360.scale_mul_closureModulus_le_cutoff_of_primeStructured_remainder
#print axioms Erdos360.closureModulus_le_cutoff_of_primeStructured_remainder
