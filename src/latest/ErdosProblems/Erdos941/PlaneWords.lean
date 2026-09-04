import ErdosProblems.Erdos941.ConicWords
import ErdosProblems.Erdos941.WordPlaneLift

/-! # Finite-field plane hitting, including anisotropic reductions -/

namespace Erdos941

def fivePlaneWords : List (List Axis) :=
  [[],
    [(false, false)],
    [(false, true)],
    [(true, false)],
    [(true, true)],
    [(false, false), (true, false), (false, false)],
    [(false, false), (true, true)],
    [(false, true), (true, false)],
    [(true, false), (false, false)],
    [(true, false), (false, true)]]

theorem five_plane_word (v : ZMod 5 × ZMod 5 × ZMod 5) :
    ∃ w ∈ fivePlaneWords, (fun v : ZMod 5 × ZMod 5 × ZMod 5 => v.2.2 = 0)
      (linearWord 17 w v) := by
  rcases v with ⟨x, y, z⟩
  revert y z
  fin_cases x <;> decide

def sevenPlaneWords : List (List Axis) :=
  [[],
    [(false, false)],
    [(true, false), (false, false), (true, true), (true, false)],
    [(true, false), (true, true), (true, false), (true, true)],
    [(true, false)],
    [(true, true)],
    [(false, false), (true, false)],
    [(false, false), (true, true)],
    [(true, false), (false, false), (true, false)],
    [(true, false), (true, true), (false, false)],
    [(false, false), (true, false), (true, true)],
    [(false, false), (true, true), (false, false)],
    [(true, false), (false, false)],
    [(true, false), (true, true)]]

theorem seven_plane_word (v : ZMod 7 × ZMod 7 × ZMod 7) :
    ∃ w ∈ sevenPlaneWords, (fun v : ZMod 7 × ZMod 7 × ZMod 7 => -v.1 + v.2.1 - v.2.2 = 0)
      (linearWord 33 w v) := by
  rcases v with ⟨x, y, z⟩
  revert y z
  fin_cases x <;> decide

def thirteenPlaneWords : List (List Axis) :=
  [[],
    [(false, false)],
    [(false, true)],
    [(false, false), (false, true)],
    [(false, true), (false, false)],
    [(false, false), (false, true), (false, false)],
    [(false, true), (false, false), (false, true)],
    [(true, false)],
    [(true, true)],
    [(true, false), (true, true)],
    [(true, true), (true, false)],
    [(true, false), (true, true), (true, false)],
    [(true, true), (true, false), (true, true)],
    [(false, false), (true, false), (true, true)],
    [(false, false), (true, true), (true, false)],
    [(false, true), (true, false), (true, true)],
    [(false, true), (true, true), (true, false)],
    [(false, false), (false, true), (true, false), (false, true)],
    [(false, true), (false, false), (true, true), (false, false)],
    [(true, false), (true, true), (false, true), (true, true)],
    [(true, true), (true, false), (false, false), (true, false)],
    [(false, false), (true, false)],
    [(false, true), (true, true)],
    [(true, false), (false, true)],
    [(true, true), (false, false)],
    [(false, false), (true, false), (false, false)],
    [(false, false), (true, true), (false, false)],
    [(false, true), (true, false), (false, true)],
    [(false, true), (true, true), (false, true)],
    [(false, false), (true, false), (true, true), (false, false)]]

theorem thirteen_plane_first_chart (x z : ZMod 13) :
    ∃ w ∈ thirteenPlaneWords, (linearWord 113 w (x, 1, z)).2.2 = 0 := by
  revert z
  fin_cases x <;> decide

theorem thirteen_plane_second_chart (x : ZMod 13) :
    ∃ w ∈ thirteenPlaneWords, (linearWord 113 w (x, 0, 1)).2.2 = 0 := by
  fin_cases x <;> decide

theorem thirteen_plane_word (v : ZMod 13 × ZMod 13 × ZMod 13) :
    ∃ w : List Axis, (linearWord 113 w v).2.2 = 0 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h := exists_word_kill_of_normalized (113 : ZMod 13) (heightLinear 0 0 1)
    (by
      intro x z
      obtain ⟨w, _, hw⟩ := thirteen_plane_first_chart x z
      exact ⟨w, by simpa [heightLinear] using hw⟩)
    (by
      intro x
      obtain ⟨w, _, hw⟩ := thirteen_plane_second_chart x
      exact ⟨w, by simpa [heightLinear] using hw⟩)
    ⟨[], by simp [heightLinear]⟩ v
  simpa [heightLinear] using h

end Erdos941
