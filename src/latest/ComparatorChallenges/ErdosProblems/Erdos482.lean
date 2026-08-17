import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos482

noncomputable def alpha (t : ℝ) : ℝ := 2 * (t + 1) / (t + 2)

end Erdos482

namespace Erdos482

noncomputable def beta (t : ℝ) : ℝ := (t + 2) / (t + 1)

end Erdos482

namespace Erdos482

noncomputable def stollBinary (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ⌊(if Even n then alpha t else beta t) *
          ((stollBinary t n : ℝ) + 1 / 2)⌋₊

end Erdos482

namespace Erdos482

noncomputable def grahamPollak : ℕ → ℕ
  | 0 => 0
  | n + 1 => stollBinary (Real.sqrt 2) n

end Erdos482

namespace Erdos482

noncomputable def binaryDigit (t : ℝ) : ℕ → Fin 2
  | 0 => 0
  | 1 => 1
  | k + 2 => Real.digits (t - 1) 2 k

end Erdos482

namespace Erdos482

theorem erdos_482 :
    grahamPollak 1 = 1 ∧
      (∀ n, 1 ≤ n →
        grahamPollak (n + 1) =
          ⌊Real.sqrt 2 * ((grahamPollak n : ℝ) + 1 / 2)⌋₊) ∧
      (∀ n, 1 ≤ n →
        grahamPollak (2 * n + 1) - 2 * grahamPollak (2 * n - 1) =
          (binaryDigit (Real.sqrt 2) n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit (Real.sqrt 2) (k + 2)) =
        Real.sqrt 2 - 1 ∧
      (∀ t : ℝ, 1 ≤ t → t < 2 →
        (∀ n, 1 ≤ n →
          stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) =
            (binaryDigit t n).val) ∧
        Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  sorry

end Erdos482

end
