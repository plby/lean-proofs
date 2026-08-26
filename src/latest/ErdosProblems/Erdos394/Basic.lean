import ErdosProblems.Erdos394.FirstQuestion
import ErdosProblems.Erdos394.DenseHierarchyLittleO

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 394: faithful formal targets

The definitions and two propositions imported from `Erdos394.Defs` formalize
`problem.md`.  A full resolution must prove each proposition (an affirmative
answer) or its negation (a negative answer), without proof escape hatches.
The line-by-line fidelity audit is in `check_answer/README.md`.
-/

namespace Erdos394

/-- The first assertion of Erdős Problem 394. -/
theorem erdos394_first_target : FirstQuestion :=
  erdos394_first_question_proved

/-- The second assertion of Erdős Problem 394. -/
theorem erdos394_second_target : SecondQuestion :=
  erdos394_second_target_proved

end Erdos394
