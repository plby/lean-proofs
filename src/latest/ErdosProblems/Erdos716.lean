/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the linked formalization.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 716, the Ruzsa–Szemerédi (6,3)-theorem.
Informal authors: Imre Z. Ruzsa, Endre Szemerédi.
Formal authors: Aristotle, JoshuaB.
The proof uses Mathlib's triangle-removal and tripartite-graph machinery
by Yaël Dillies and Bhavik Mehta.
Source: https://www.erdosproblems.com/716#post-7096
Original Lean/Mathlib version: 4.28.0, as specified in the linked editor project.
The full editor URL is preserved as JoshuaB_716 in data/urls.yaml.
-/
import ErdosProblems.Erdos716.Construction

open Asymptotics Filter

namespace Erdos716

theorem erdos_716 :
    (fun n => (ex3 n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_bound ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simpa only [norm_pow, Real.norm_natCast] using
    ex3_le_of_bound (fun H h3 h => hN n hn H h3 h)

#print axioms erdos_716
-- 'Erdos716.erdos_716' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos716
