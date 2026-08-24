/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeStructuredCommonScale
import ErdosProblems.Erdos360.StructuredPhaseCoordinates

/-!
# The accumulated scale in a structured modular phase

Suppose divisor extraction has written the current integer pivots as `d * z`
inside the prime-structured source.  The canonical closure modulus `q` of
their residues divides every `z`.  If more than `U` pivots remain, the
prime-factor argument for the source therefore shows that the accumulated
scale `d * q` divides the target.  This is the source invariant M1 at the
precise point where a modular fibre is normalized.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- More than `U` extracted pivots force the product of the extracted scale
and their canonical closure modulus to divide the target. -/
theorem extracted_closureScale_dvd_target
    {n y U d t : ℕ} [NeZero t] (ht : 0 < t)
    {W Z : Finset ℕ}
    (hd : 0 < d)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hZt : ∀ z ∈ Z, z < t)
    (hlarge : U < Z.card) :
    d * closureModulus ht (ordinaryResidues t Z) ∣ n := by
  let q := closureModulus ht (ordinaryResidues t Z)
  let X := Z.image fun z : ℕ ↦ d * z
  have hXsource : X ⊆ primeStructuredTestSet n y U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hW (hscale z hz)
  have hk : 0 < d * q := Nat.mul_pos hd
    (closureModulus_pos ht (ordinaryResidues t Z))
  have hkX : ∀ x ∈ X, d * q ∣ x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha⟩ := closureModulus_dvd_of_mem_ordinary ht hZt hz
    refine ⟨a, ?_⟩
    rw [ha]
    ring
  have hXcard : X.card = Z.card := by
    dsimp [X]
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  apply commonScale_dvd_target_of_large_subset_primeStructuredTestSet
    hXsource hk hkX
  simpa [hXcard] using hlarge

end Erdos360

#print axioms Erdos360.extracted_closureScale_dvd_target
