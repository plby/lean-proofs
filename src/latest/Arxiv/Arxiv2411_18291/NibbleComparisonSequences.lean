import Arxiv.Arxiv2411_18291.NibbleCliqueDrift
import Arxiv.Arxiv2411_18291.RemovalDensity

/-! # Deterministic comparison sequences along the clique-removal clock -/

noncomputable section

namespace Arxiv2411_18291

def nibbleDegreeUpperComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  nibbleDegreeUpper k a D (removalDensity k g i)

def nibbleDegreeLowerComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  nibbleDegreeLower k a D (removalDensity k g i)

def nibbleCliqueUpperComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  nibbleCliqueUpper k a g D (removalDensity k g i)

def nibbleCliqueLowerComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  nibbleCliqueLower k a g D (removalDensity k g i)

theorem removalDensity_difference (k : ℕ) (g : ℝ) (i : ℕ) :
    removalDensity k g i - removalDensity k g (i + 1) = (k : ℝ) / g := by
  rw [removalDensity_succ]
  ring

theorem NibbleCountConditions.sequence_steps {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) (Q : NibbleCountConditions k a g D p₀ L)
    (i : ℕ) (hi : p₀ ≤ removalDensity k g (i + 1)) :
    let δu := nibbleCliqueUpperComparison k a g D (i + 1) - nibbleCliqueUpperComparison k a g D i
    let δl := nibbleCliqueLowerComparison k a g D (i + 1) - nibbleCliqueLowerComparison k a g D i;
    -nibbleCliqueSlope k D (removalDensity k g i) ≤ δu ∧
      δl ≤ -nibbleCliqueSlope k D (removalDensity k g i) ∧
      |δu| ≤ 130 * (k : ℝ) ^ 3 * D ∧ |δl| ≤ 130 * (k : ℝ) ^ 3 * D :=
  Q.comparison_steps P hi (removalDensity_le_one k P.graph_pos i)
    (removalDensity_difference k g i)

end Arxiv2411_18291
