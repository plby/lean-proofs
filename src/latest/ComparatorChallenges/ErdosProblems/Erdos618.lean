/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos618

noncomputable def maxDegreeFin {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Finset.univ.sup (fun v : Fin n =>
    letI : Fintype ↥(G.neighborSet v) := inferInstance
    G.degree v)

open scoped Classical in
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  exact sInf {k : ℕ |
    ∃ H : SimpleGraph (Fin n),
      G ≤ H ∧
      H.CliqueFree 3 ∧
      (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
      ((H.edgeFinset \ G.edgeFinset).card = k)}
end Erdos618


namespace Erdos618

open scoped Classical in
theorem erdos_618
    (G : ∀ n : ℕ, SimpleGraph (Fin n))
    (hTriangleFree : ∀ n : ℕ, (G n).CliqueFree 3)
    (hMaxDeg :
      (fun n : ℕ => (maxDegreeFin (G n) : ℝ))
        =o[Filter.atTop] (fun n : ℕ => Real.rpow (n : ℝ) ((1 : ℝ) / 2))) :
    (fun n : ℕ => (h2 (G n) : ℝ))
      =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (2 : ℕ)) := by
  sorry

end Erdos618
