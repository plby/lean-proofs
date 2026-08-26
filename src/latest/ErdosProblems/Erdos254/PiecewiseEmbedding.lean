/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.BohrReturns

namespace Erdos254

open Filter Set
open scoped Topology

/-- Every finite part of `A` has a translate in `B`. -/
def FiniteEmbeds (A B : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∃ t : ℕ, ∀ n ∈ F, t + n ∈ B

/-- Piecewise Bohr structure survives finite embeddability. Compactness of the
torus makes the translating phases converge along a subsequence. -/
theorem ContainsPiecewiseBohr.of_finiteEmbeds {A B : Set ℕ}
    (hA : ContainsPiecewiseBohr A) (hAB : FiniteEmbeds A B) : ContainsPiecewiseBohr B := by
  classical
  obtain ⟨d, θ, U, J, hU, hJ, ⟨n₀, _, hn₀⟩, hAU⟩ := hA
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (n₀ • θ) hn₀
  choose a ha using hJ
  let F : ℕ → Finset ℕ := fun N ↦ (Finset.Icc (a N) (a N + N)).filter (· ∈ A)
  have hF (N : ℕ) : (F N : Set ℕ) ⊆ A := fun _ hn ↦ (Finset.mem_filter.mp hn).2
  choose t ht using fun N ↦ hAB (F N) (hF N)
  obtain ⟨η, _, ρ, hρ, hlim⟩ := isCompact_univ.isSeqCompact
    (fun N ↦ (mem_univ (t N • θ)))
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim (ε / 4) (by positivity)
  let ζ := t (ρ K) • θ + n₀ • θ
  let V := Metric.ball ζ (ε / 4)
  have hV : IsOpen V := Metric.isOpen_ball
  have hVne : ∃ n : ℕ, n • θ ∈ V := by
    refine ⟨t (ρ K) + n₀, ?_⟩
    change dist ((t (ρ K) + n₀) • θ) ζ < ε / 4
    simp only [add_nsmul, ζ, dist_self]
    positivity
  have hVU {x : UnitAddTorus (Fin d)} (hx : x ∈ V) {j : ℕ} (hj : K ≤ j) :
      x - t (ρ j) • θ ∈ U := by
    apply hball
    change dist (x - t (ρ j) • θ) (n₀ • θ) < ε
    have hd := dist_sub_sub_le x (t (ρ j) • θ) ζ (t (ρ K) • θ)
    have hζ : ζ - t (ρ K) • θ = n₀ • θ := by dsimp [ζ]; abel
    rw [hζ] at hd
    have htri := dist_triangle (t (ρ j) • θ) η (t (ρ K) • θ)
    have hjdist := hK j hj
    have hKdist := hK K le_rfl
    change dist x ζ < ε / 4 at hx
    simp only [Function.comp_def] at hjdist hKdist
    rw [dist_comm η] at htri
    linarith
  let J' : Set ℕ := {n | ∃ j ≥ K, ∃ k ≤ ρ j, n = t (ρ j) + a (ρ j) + k}
  have hJ' : IsThick J' := by
    intro L
    let j := max K L
    refine ⟨t (ρ j) + a (ρ j), fun k hk ↦ ⟨j, le_max_left _ _, k, ?_, rfl⟩⟩
    exact hk.trans ((le_max_right K L).trans (hρ.id_le j))
  refine ⟨d, θ, V, J', hV, hJ', thick_meets_bohr θ hV hVne hJ', ?_⟩
  intro n hn hphase
  obtain ⟨j, hj, k, hk, rfl⟩ := hn
  have hphase' : (a (ρ j) + k) • θ ∈ U := by
    have h := hVU hphase hj
    simpa only [add_nsmul, add_sub_cancel_left, add_assoc] using h
  have hmem : a (ρ j) + k ∈ F (ρ j) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hAU _ (ha _ k hk) hphase'⟩
  simpa only [Nat.add_assoc] using ht (ρ j) (a (ρ j) + k) hmem

end Erdos254
