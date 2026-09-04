import Util.Bernays.FullClassConstant
import Util.Bernays.SmoothCountingSeries

/-!
# Full asymptotic for represented norms in every ideal class
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def classValues {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ClassGroup (QuadraticAlgebra ℤ d b) → ℕ → Finset ℕ :=
  letI := quadraticOrderIsDomain hD
  fun C N => positiveValues (fun n => ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
    (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n ∧ I.idealClass = C) N

theorem classValues_card_eq_tsum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N : ℕ),
      ((classValues hD C N).card : ℝ) = ∑' m : Nat.factoredNumbers
        (discriminantLevel (b ^ 2 + 4 * d)).primeFactors,
        ((classSliceValues hD C m.val (N / m.val)).card : ℝ) := by
  let := quadraticOrderIsDomain hD
  intro C N
  exact positiveValues_card_eq_tsum _ (discriminantLevel_pos hD.ne).ne' N

theorem classValues_card_limit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b),
      Tendsto (fun N : ℕ => ((classValues hD C N).card : ℝ) / scale N)
        atTop (𝓝 (fullClassConstant hD)) := by
  let := quadraticOrderIsDomain hD
  intro C
  apply (classSlice_tsum_limit hD C).congr'
  filter_upwards [] with N
  rw [tsum_div_const, ← classValues_card_eq_tsum]

end Bernays
