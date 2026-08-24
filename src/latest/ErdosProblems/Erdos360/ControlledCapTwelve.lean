/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeCountControlledSharp

/-!
# The sound `V y / 12` controlled cap

The cap/floor pair `5n/(4y), 6n/(5y)` leaves a gap of order `n/(20y)`
for divisor extraction.  Selecting one eighth of the extracted class spends
at most `5n/16`, while the remaining seven eighths of the floor have main
mass `21n/20`.  Thus both terminal inequalities retain fixed slack.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

def controlledPrimeClassCapTwelve (n y : ℕ) : ℕ :=
  5 * n / (4 * y)

def controlledPrimeExtractedFloorTwelve (n y : ℕ) : ℕ :=
  6 * n / (5 * y)

/-- The canonical square-root window converts the `V y / 12` test-set
count exactly into the controlled cap `5n/(4y)`. -/
lemma controlledPrimeClassCapTwelve_mul_le_primeStructured_card
    {n colors y U : ℕ} (hn : 0 < n) (hcolors : 0 < colors)
    (hy : y = initialLowerY n colors)
    (hcount : initialMissingEulerProduct n colors * (y : ℝ) / 12 ≤
      ((primeStructuredTestSet n y U).card : ℝ)) :
    colors * controlledPrimeClassCapTwelve n y ≤
      (primeStructuredTestSet n y U).card := by
  have hVpos := initialMissingEulerProduct_pos n colors
  have hwindow := initialLowerY_parameter_window hn hcolors
  rw [← hy] at hwindow
  have hypos : 0 < y := by
    have hmass := one_le_initialLowerParameterMass hn hcolors
    have : (0 : ℝ) < y := by nlinarith [hwindow.1]
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
  have hcap : (controlledPrimeClassCapTwelve n y : ℝ) ≤
      5 * (n : ℝ) / (4 * y) := by
    unfold controlledPrimeClassCapTwelve
    calc
      ((5 * n / (4 * y) : ℕ) : ℝ) ≤
          ((5 * n : ℕ) : ℝ) / ((4 * y : ℕ) : ℝ) := Nat.cast_div_le
      _ = 5 * (n : ℝ) / (4 * y) := by push_cast; ring
  have hcapCount :
      (colors : ℝ) * controlledPrimeClassCapTwelve n y ≤
        initialMissingEulerProduct n colors * (y : ℝ) / 12 := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
    have hcR : (0 : ℝ) ≤ colors := by positivity
    calc
      (colors : ℝ) * controlledPrimeClassCapTwelve n y ≤
          (colors : ℝ) * (5 * (n : ℝ) / (4 * y)) :=
        mul_le_mul_of_nonneg_left hcap hcR
      _ = 5 * (colors : ℝ) * n / (4 * y) := by ring
      _ ≤ initialMissingEulerProduct n colors * (y : ℝ) / 12 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * y)
          (by norm_num : (0 : ℝ) < 12)]
        nlinarith
  exact_mod_cast hcapCount.trans hcount

/-- The exact quotient gap pays any loss whose denominator-scaled size is
at most `n`. -/
lemma controlledPrimeTwelve_loss_room
    {n y loss : ℕ} (hy : 0 < y)
    (hroom : 20 * y * loss ≤ n) :
    controlledPrimeExtractedFloorTwelve n y + loss ≤
      controlledPrimeClassCapTwelve n y := by
  have hD : 0 < 20 * y := by positivity
  have hloss : loss ≤ n / (20 * y) :=
    (Nat.le_div_iff_mul_le hD).2 (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hroom)
  have hfloor : controlledPrimeExtractedFloorTwelve n y =
      24 * n / (20 * y) := by
    unfold controlledPrimeExtractedFloorTwelve
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.mul_div_mul_left (m := 4) (6 * n) (5 * y) (by norm_num)).symm
  have hcap : controlledPrimeClassCapTwelve n y =
      25 * n / (20 * y) := by
    unfold controlledPrimeClassCapTwelve
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.mul_div_mul_left (m := 5) (5 * n) (4 * y) (by norm_num)).symm
  rw [hfloor, hcap]
  refine (Nat.add_le_add_left hloss _).trans ?_
  calc
    24 * n / (20 * y) + n / (20 * y) ≤
        (24 * n + n) / (20 * y) :=
      Nat.div_add_div_le_add_div
    _ = 25 * n / (20 * y) := by ring_nf

/-- After integer rounding, the unused seven eighths of the floor still
cover the target. -/
lemma controlledPrimeTwelve_unused_reserve
    {n y : ℕ} (hy : 0 < y) (hlarge : 140 * y ≤ n) :
    n ≤ 7 * y * (controlledPrimeExtractedFloorTwelve n y / 8) := by
  unfold controlledPrimeExtractedFloorTwelve
  have hrem : 6 * n < 5 * y * (6 * n / (5 * y) + 1) :=
    Nat.lt_mul_div_succ _ (by positivity)
  have hqle : 6 * n / (5 * y) + 1 ≤
      8 * (6 * n / (5 * y) / 8 + 1) := by omega
  have hrem' : 6 * n <
      40 * y * (6 * n / (5 * y) / 8 + 1) := by
    calc
      6 * n < 5 * y * (6 * n / (5 * y) + 1) := hrem
      _ ≤ 5 * y * (8 * (6 * n / (5 * y) / 8 + 1)) :=
        Nat.mul_le_mul_left _ hqle
      _ = 40 * y * (6 * n / (5 * y) / 8 + 1) := by ring
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hrem' ⊢
  omega

end Erdos360

#print axioms Erdos360.controlledPrimeClassCapTwelve_mul_le_primeStructured_card
#print axioms Erdos360.controlledPrimeTwelve_loss_room
#print axioms Erdos360.controlledPrimeTwelve_unused_reserve
