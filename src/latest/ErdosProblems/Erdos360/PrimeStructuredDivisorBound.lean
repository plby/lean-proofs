/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.GapAudit

/-!
# The common extraction divisor is a small divisor of the target

Every element of the prime-structured test set has the form `u * q`, where
`u ∣ n`, `u ≤ U`, and the prime quotient `q` is larger than the extraction
cutoff `B`.  Consequently, if a nonempty extracted set has common scale
`d ≤ B`, then Euclid's lemma and cancellation show that `d ∣ u`.  In
particular, `d ∣ n` and `d ≤ U`.

The first lemma is stated for natural-number finsets.  The second is the
source-facing form used after selecting a controlled subset of an integer
color class on `primeStructuredBelowTarget`.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- A nonempty common-divisor extraction from the prime-structured natural
test set has scale dividing the target and bounded by the divisor cutoff. -/
lemma extracted_scale_dvd_target_and_le_cutoff_of_subset_testSet
    {n y U B d : ℕ} {W Z : Finset ℕ}
    (hB : B ≤ y / U) (hd : 0 < d) (hdB : d ≤ B)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W) (hZ : Z.Nonempty) :
    d ∣ n ∧ d ≤ U := by
  obtain ⟨z, hz⟩ := hZ
  have ha : d * z ∈ primeStructuredTestSet n y U := hW (hscale z hz)
  obtain ⟨u, hun, hn0, huU, q, hyq, _hq2, hqprime, _hqn, heq⟩ :=
    mem_primeStructuredTestSet.mp ha
  have hu : 0 < u :=
    Nat.pos_of_dvd_of_pos hun (Nat.pos_of_ne_zero hn0)
  have hqB : B < q := by
    have hdiv : y / U ≤ y / u := Nat.div_le_div_left huU hu
    exact (hB.trans hdiv).trans_lt hyq
  have hqd : ¬q ∣ d := by
    intro hdiv
    have hqdle : q ≤ d := Nat.le_of_dvd hd hdiv
    omega
  have hqdz : q ∣ d * z := by
    rw [heq]
    exact dvd_mul_left q u
  have hqz : q ∣ z := (hqprime.dvd_mul.mp hqdz).resolve_left hqd
  obtain ⟨t, rfl⟩ := hqz
  have hcancel : q * (d * t) = q * u := by
    calc
      q * (d * t) = d * (q * t) := by ring
      _ = u * q := heq
      _ = q * u := by ring
  have hdu_eq : d * t = u :=
    Nat.eq_of_mul_eq_mul_left hqprime.pos hcancel
  have hdu : d ∣ u := ⟨t, hdu_eq.symm⟩
  exact ⟨hdu.trans hun, (Nat.le_of_dvd hu hdu).trans huU⟩

/-- Source-facing coloring-domain version of
`extracted_scale_dvd_target_and_le_cutoff_of_subset_testSet`. -/
lemma extracted_scale_dvd_target_and_le_cutoff
    {n colors y U B d : ℕ} {hy : 2 * y < n}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {W Z : Finset ℕ}
    (hB : B ≤ y / U) (hd : 0 < d) (hdB : d ≤ B)
    (hW : W ⊆ integerColorClass
      (primeStructuredBelowTarget n y U hy) c i)
    (hscale : ∀ z ∈ Z, d * z ∈ W) (hZ : Z.Nonempty) :
    d ∣ n ∧ d ≤ U := by
  apply extracted_scale_dvd_target_and_le_cutoff_of_subset_testSet
      hB hd hdB (W := W) (Z := Z)
  · intro a ha
    obtain ⟨x, hxY, _hxi, hxa⟩ := mem_integerColorClass.mp (hW ha)
    rw [← hxa]
    exact mem_primeStructuredBelowTarget_iff.mp hxY
  · exact hscale
  · exact hZ

end Erdos360
