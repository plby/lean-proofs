/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos353.Kovac

noncomputable def cross (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

end Erdos353.Kovac
