import ErdosProblems.Erdos941.ModularRotations

/-! # Small certificates for the three projective conics -/

namespace Erdos941

def OnTargetLine {R : Type*} [CommRing R] (r s : R) (v : R × R × R) : Prop :=
  v.1 = r * v.2.1 ∧ v.2.2 = s * v.2.1

instance {R : Type*} [CommRing R] [DecidableEq R] (r s : R) (v : R × R × R) :
    Decidable (OnTargetLine r s v) := inferInstanceAs (Decidable (_ ∧ _))

def fiveConicWords : List (List Axis) :=
  [[],
    [(false, false)],
    [(false, true)],
    [(true, false)],
    [(true, true)],
    [(true, false), (false, false)]]

theorem five_conic_word (v : ZMod 5 × ZMod 5 × ZMod 5)
    (hv : normThree v = 0) :
    ∃ w ∈ fiveConicWords, OnTargetLine 2 0 (linearWord 17 w v) := by
  rcases v with ⟨x, y, z⟩
  revert y z
  fin_cases x <;> decide

def sevenConicWords : List (List Axis) :=
  [[],
    [(false, false)],
    [(true, false)],
    [(true, true)],
    [(false, true), (false, false)],
    [(true, false), (false, false)],
    [(false, true), (true, false)],
    [(false, false), (false, true), (false, false)]]

theorem seven_conic_word (v : ZMod 7 × ZMod 7 × ZMod 7)
    (hv : normThree v = 0) :
    ∃ w ∈ sevenConicWords, OnTargetLine 3 5 (linearWord 33 w v) := by
  rcases v with ⟨x, y, z⟩
  revert y z
  fin_cases x <;> decide

def thirteenConicWords : List (List Axis) :=
  [[],
    [(false, false)],
    [(false, true)],
    [(true, false)],
    [(true, true)],
    [(false, true), (false, false)],
    [(true, false), (false, false)],
    [(false, false), (false, true)],
    [(true, true), (false, true)],
    [(true, false), (false, true), (false, false)],
    [(true, true), (false, true), (false, false)],
    [(false, false), (true, false), (false, false)],
    [(true, false), (false, false), (false, true)],
    [(true, true), (true, false), (false, true), (false, false)]]

theorem thirteen_conic_word (v : ZMod 13 × ZMod 13 × ZMod 13)
    (hv : normThree v = 0) :
    ∃ w ∈ thirteenConicWords, OnTargetLine 5 0 (linearWord 113 w v) := by
  rcases v with ⟨x, y, z⟩
  revert y z
  fin_cases x <;> decide

end Erdos941
