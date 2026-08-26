/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.PiecewiseBohr

namespace Erdos254

open Filter Set
open scoped Topology BigOperators

lemma phaseDivergent_univ : PhaseDivergent (Set.univ : Set ℕ) := by
  intro θ hθ hs
  have hsum : Summable (fun n : ℕ ↦ ‖n • θ‖) := by
    exact hs.comp_injective (i := fun n : ℕ ↦ (⟨n, mem_univ n⟩ : (Set.univ : Set ℕ)))
      (fun _ _ h ↦ congrArg Subtype.val h)
  have ht : Tendsto (fun n : ℕ ↦ n • θ) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsum.tendsto_atTop_zero
  have hd := (ht.comp (tendsto_add_atTop_nat 1)).sub ht
  have hc : Tendsto (fun _ : ℕ ↦ θ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, add_nsmul, one_nsmul, add_sub_cancel_left, sub_zero] using hd
  exact hθ (tendsto_nhds_unique tendsto_const_nhds hc)

/-- A thick set intersects every open set visited by a finite torus rotation. -/
lemma thick_meets_bohr {d : ℕ} (θ : UnitAddTorus (Fin d))
    {U : Set (UnitAddTorus (Fin d))} (hU : IsOpen U) (hne : ∃ n : ℕ, n • θ ∈ U)
    {J : Set ℕ} (hJ : IsThick J) : ∃ n : ℕ, n ∈ J ∧ n • θ ∈ U := by
  obtain ⟨E, _, hcover⟩ := finite_orbit_cover Set.univ θ U hU hne
    (generator_mem_tailSubgroup phaseDivergent_univ θ)
  let M := ∑ e ∈ E, e
  obtain ⟨a, ha⟩ := hJ M
  obtain ⟨F, hF, hFU⟩ := hcover (a + M)
  let b := ∑ e ∈ F, e
  have hb : b ≤ M := Finset.sum_le_sum_of_subset hF
  have hba : b ≤ a + M := by omega
  refine ⟨a + M - b, ?_, ?_⟩
  · have hEq : a + (M - b) = a + M - b := by omega
    simpa only [hEq] using ha (M - b) (Nat.sub_le _ _)
  · have hEq := congrArg (fun n : ℕ ↦ n • θ) (Nat.sub_add_cancel hba)
    rw [add_nsmul] at hEq
    rw [eq_sub_iff_add_eq.mpr hEq]
    exact hFU

lemma thick_meets_bohr_zero {d : ℕ} (θ : UnitAddTorus (Fin d))
    {U : Set (UnitAddTorus (Fin d))} (hU : IsOpen U) (h0 : 0 ∈ U)
    {J : Set ℕ} (hJ : IsThick J) : ∃ n : ℕ, n ∈ J ∧ n • θ ∈ U :=
  thick_meets_bohr θ hU ⟨0, by simpa using h0⟩ hJ

end Erdos254
