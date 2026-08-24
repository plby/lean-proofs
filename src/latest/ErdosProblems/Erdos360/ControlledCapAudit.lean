/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeStructuredDivisorBound

/-!
# Exact controlled-cap arithmetic for Erdős 360

This audit file isolates the three finite inequalities used by the
controlled prime/random ledger.  The first statement deliberately assumes
only the sharp real-valued count: it records the exact conversion from the
canonical square-root window to the integral cap `7n/(4y)`.  The second is
the endpoint reserve after choosing the extracted floor `3n/(2y)`.  The
third is the scale bound furnished by a nonempty divisor extraction.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- The canonical initial window pays the exact integral class cap. -/
lemma initialLowerY_controlled_cap_le_primeStructured_card
    {n colors y U : ℕ} (hn : 0 < n) (hcolors : 0 < colors)
    (hy : y = initialLowerY n colors)
    (hcount : initialMissingEulerProduct n colors * (y : ℝ) / 8 ≤
      ((primeStructuredTestSet n y U).card : ℝ)) :
    colors * (7 * n / (4 * y)) ≤
      (primeStructuredTestSet n y U).card := by
  have hVpos := initialMissingEulerProduct_pos n colors
  have hwindow := initialLowerY_parameter_window hn hcolors
  rw [← hy] at hwindow
  have hypos : 0 < y := by
    have hmass := one_le_initialLowerParameterMass hn hcolors
    have : (0 : ℝ) < y := by
      nlinarith [hwindow.1]
    exact_mod_cast this
  have hmain :
      (15 : ℝ) * colors * n ≤
        initialMissingEulerProduct n colors * (y : ℝ) ^ 2 := by
    unfold initialLowerParameterMass at hwindow
    calc
      (15 : ℝ) * colors * n =
          initialMissingEulerProduct n colors *
            (15 * ((colors : ℝ) * n /
              initialMissingEulerProduct n colors)) := by
        field_simp [hVpos.ne']
      _ ≤ initialMissingEulerProduct n colors * (y : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hwindow.1 hVpos.le
  have hcap : ((7 * n / (4 * y) : ℕ) : ℝ) ≤
      7 * (n : ℝ) / (4 * y) := by
    calc
      ((7 * n / (4 * y) : ℕ) : ℝ) ≤
          ((7 * n : ℕ) : ℝ) / ((4 * y : ℕ) : ℝ) :=
        Nat.cast_div_le
      _ = 7 * (n : ℝ) / (4 * y) := by push_cast; ring
  have hcapCount :
      (colors : ℝ) * (7 * n / (4 * y) : ℕ) ≤
        initialMissingEulerProduct n colors * (y : ℝ) / 8 := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
    have hcR : (0 : ℝ) ≤ colors := by positivity
    calc
      (colors : ℝ) * (7 * n / (4 * y) : ℕ) ≤
          (colors : ℝ) * (7 * (n : ℝ) / (4 * y)) :=
        mul_le_mul_of_nonneg_left hcap hcR
      _ = 7 * (colors : ℝ) * n / (4 * y) := by ring
      _ ≤ initialMissingEulerProduct n colors * (y : ℝ) / 8 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * y)
          (by norm_num : (0 : ℝ) < 8)]
        nlinarith
  exact_mod_cast hcapCount.trans hcount

/-- Once `n/y` exceeds the rounding threshold, the extracted floor leaves
the exact terminal reserve required by the seven-fold completion bound. -/
lemma controlled_extracted_floor_unused_reserve
    {n y : ℕ} (hy : 0 < y) (hlarge : 112 * y ≤ n) :
    n ≤ 7 * y * ((3 * n / (2 * y)) / 8) := by
  have hqmod : (3 * n / (2 * y)) % 8 < 8 := by omega
  have hrem : 3 * n < 2 * y * (3 * n / (2 * y) + 1) := by
    exact Nat.lt_mul_div_succ _ (by omega)
  have hqle : 3 * n / (2 * y) + 1 ≤
      8 * (3 * n / (2 * y) / 8 + 1) := by omega
  have hrem' : 3 * n <
      16 * y * (3 * n / (2 * y) / 8 + 1) := by
    calc
      3 * n < 2 * y * (3 * n / (2 * y) + 1) := hrem
      _ ≤ 2 * y * (8 * (3 * n / (2 * y) / 8 + 1)) :=
        Nat.mul_le_mul_left _ hqle
      _ = (2 * 8) * y * (3 * n / (2 * y) / 8 + 1) := by
        ac_rfl
      _ = 16 * y * (3 * n / (2 * y) / 8 + 1) := by rfl
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hrem' ⊢
  omega

/-- A nonempty controlled extraction has scale at most the structured-set
divisor cutoff. -/
lemma nonempty_extracted_scale_le_cutoff
    {n y U B d : ℕ} {W Z : Finset ℕ}
    (hB : B ≤ y / U) (hd : 0 < d) (hdB : d ≤ B)
    (hW : W ⊆ primeStructuredTestSet n y U)
    (hscale : ∀ z ∈ Z, d * z ∈ W) (hZ : Z.Nonempty) :
    d ≤ U := by
  exact (extracted_scale_dvd_target_and_le_cutoff_of_subset_testSet
    hB hd hdB hW hscale hZ).2

end Erdos360

#print axioms Erdos360.initialLowerY_controlled_cap_le_primeStructured_card
#print axioms Erdos360.controlled_extracted_floor_unused_reserve
#print axioms Erdos360.nonempty_extracted_scale_le_cutoff
