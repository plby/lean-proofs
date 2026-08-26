import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Omega

/-! # Diagonal selection for countably many eventual constraints -/

namespace Erdos1123

open Filter
open scoped Topology

/-- A slowly growing initial segment satisfies every one of its constraints.
No uniform rate of convergence is required. -/
theorem exists_diagonal_scope (P : ℕ → ℕ → Prop)
    (hP : ∀ i, ∀ᶠ n in atTop, P i n) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ n i, i < k n → P i n := by
  classical
  have hex (n : ℕ) : ∃ i : ℕ, ¬(i ≤ n ∧ P i n) :=
    ⟨n + 1, fun h => Nat.not_succ_le_self n h.1⟩
  let k : ℕ → ℕ := fun n => Nat.find (hex n)
  have hgood (n i : ℕ) (hi : i < k n) : i ≤ n ∧ P i n := by
    by_contra h
    exact Nat.find_min (hex n) hi h
  refine ⟨k, tendsto_atTop.2 ?_, fun n i hi => (hgood n i hi).2⟩
  intro b
  have he : ∀ᶠ n in atTop, ∀ i ∈ Finset.range b, P i n :=
    (Filter.eventually_all_finset _).2 (fun i _ => hP i)
  filter_upwards [he, eventually_ge_atTop b] with n hn hbn
  by_contra hbk
  have hkb : k n < b := Nat.lt_of_not_ge hbk
  exact Nat.find_spec (hex n)
    ⟨(Nat.le_of_lt hkb).trans hbn, hn (k n) (Finset.mem_range.mpr hkb)⟩

/-- Choose a cofinal diagonal along which nonnegative row errors vanish. -/
theorem exists_diagonal_zero (e : ℕ → ℕ → ℝ)
    (he₀ : ∀ k n, 0 ≤ e k n) (he : ∀ k, Tendsto (e k) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ Tendsto (fun n => e (k n) n) atTop (𝓝 0) := by
  have hP (k : ℕ) : ∀ᶠ n in atTop, e k n < 1 / ((k : ℝ) + 1) :=
    (he k).eventually (gt_mem_nhds (by positivity))
  obtain ⟨scope, hscope, hgood⟩ := exists_diagonal_scope
    (fun k n => e k n < 1 / ((k : ℝ) + 1)) hP
  let k : ℕ → ℕ := fun n => scope n - 1
  have hk : Tendsto k atTop atTop := (tendsto_sub_atTop_nat 1).comp hscope
  refine ⟨k, hk, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun n => he₀ (k n) n))
    (g := fun n => 1 / ((k n : ℝ) + 1))
  · filter_upwards [hscope.eventually (eventually_ge_atTop 1)] with n hn
    exact (hgood n (k n) (by dsimp [k]; omega)).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hk

end Erdos1123
