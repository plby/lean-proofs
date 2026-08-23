/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos379

open Filter

noncomputable def S (n : ℕ) : ℕ :=
  sSup {s | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p ^ s ∣ n.choose k}
namespace depth_0_lemma_1

end depth_0_lemma_1

namespace depth_0_lemma_2

end depth_0_lemma_2

namespace depth_0_lemma_3

end depth_0_lemma_3

namespace depth_0_lemma_4
end depth_0_lemma_4

namespace depth_0_lemma_5

end depth_0_lemma_5

end Erdos379

open Filter

namespace Erdos379

open scoped Classical in
theorem erdos_379 : atTop.limsup (fun n => (S n : ℕ∞)) = ⊤ := by
  sorry

end Erdos379
