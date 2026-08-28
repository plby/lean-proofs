import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Open boxes for successive antiholomorphic coordinate corrections

The coordinates already corrected lie in the smaller open discs.  The
remaining coordinates stay in the original larger discs, so that every
use of the closedness equation is within its stated domain.
-/

noncomputable section

open Complex Set Metric
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- The open box after correcting the coordinates in `S`. -/
def polydisc (S : Finset (Fin 3)) (x : Fin 3 → ℂ) (r R : ℝ) :
    Set (Fin 3 → ℂ) :=
  {q | ∀ i, dist (q i) (x i) < if i ∈ S then r else R}

theorem isOpen_polydisc (S : Finset (Fin 3)) (x : Fin 3 → ℂ) (r R : ℝ) :
    IsOpen (polydisc S x r R) := by
  have he : polydisc S x r R = ⋂ i : Fin 3, {q : Fin 3 → ℂ |
      dist (q i) (x i) < if i ∈ S then r else R} := by
    ext q
    simp only [polydisc, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).dist continuous_const) continuous_const

theorem mem_polydisc_center (S : Finset (Fin 3)) (x : Fin 3 → ℂ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) : x ∈ polydisc S x r R := by
  intro i
  by_cases hi : i ∈ S
  · simpa only [dist_self, if_pos hi] using hr
  · simpa only [dist_self, if_neg hi] using hR

theorem polydisc_mono {S T : Finset (Fin 3)} (hST : S ⊆ T)
    (x : Fin 3 → ℂ) {r R : ℝ} (hrR : r ≤ R) :
    polydisc T x r R ⊆ polydisc S x r R := by
  intro q hq i
  by_cases hiS : i ∈ S
  · simpa only [if_pos hiS, if_pos (hST hiS)] using hq i
  · by_cases hiT : i ∈ T
    · have hi : dist (q i) (x i) < r := by simpa only [if_pos hiT] using hq i
      simpa only [if_neg hiS] using hi.trans_le hrR
    · simpa only [if_neg hiS, if_neg hiT] using hq i

theorem polydisc_subset_empty (S : Finset (Fin 3)) (x : Fin 3 → ℂ)
    {r R : ℝ} (hrR : r ≤ R) :
    polydisc S x r R ⊆ polydisc ∅ x r R :=
  polydisc_mono (Finset.empty_subset S) x hrR

/-- Varying a new integration coordinate through the larger disc stays in
the previous open box. -/
theorem update_mem_polydisc {S : Finset (Fin 3)} {j : Fin 3} (hj : j ∉ S)
    {x q : Fin 3 → ℂ} {r R : ℝ} (hq : q ∈ polydisc (insert j S) x r R)
    {z : ℂ} (hz : z ∈ ball (x j) R) :
    Function.update q j z ∈ polydisc S x r R := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa only [Function.update_self, if_neg hj, mem_ball] using hz
  · simpa only [Function.update_of_ne hij, Finset.mem_insert, hij,
      false_or] using hq i

theorem mem_polydisc_univ_iff (x q : Fin 3 → ℂ) (r R : ℝ) :
    q ∈ polydisc Finset.univ x r R ↔ ∀ i, dist (q i) (x i) < r := by
  simp only [polydisc, mem_ofPred_eq, Finset.mem_univ, if_true]

theorem polydisc_empty_subset_ball (x : Fin 3 → ℂ) {r R : ℝ} (hR : 0 < R) :
    polydisc ∅ x r R ⊆ ball x R := by
  intro q hq
  apply (dist_pi_lt_iff hR).mpr
  intro i
  simpa only [Finset.notMem_empty, if_false] using hq i

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
