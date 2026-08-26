import ErdosProblems.Erdos394.Proof

open Filter
open scoped Asymptotics

namespace Erdos394

/-- Both average-order questions have affirmative answers. -/
theorem erdos_394 :
    (∃ c : ℝ, c > 0 ∧
      (fun x : ℝ ↦ Tsum 2 x) =O[atTop]
        (fun x : ℝ ↦ x ^ 2 / (Real.log x) ^ c)) ∧
    ∀ k : ℕ, k ≥ 2 →
      (fun x : ℝ ↦ Tsum (k + 1) x) =o[atTop]
        (fun x : ℝ ↦ Tsum k x) :=
  ⟨erdos394_first_target, erdos394_second_target⟩

end Erdos394
