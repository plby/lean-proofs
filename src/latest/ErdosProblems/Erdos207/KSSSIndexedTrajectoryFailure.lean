/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectoryIndex
import ErdosProblems.Erdos207.IndexedBandFailure

/-! # The coupled trajectory failure bound from its two signed tails -/

namespace Erdos207

noncomputable section

def ksssCenteredTrajectoryObservable
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (a : ℕ → ℝ) (E₀ A₀ scale : ℝ) (B : ℕ)
    (σ t : ℝ) (S : GreedyStateOn V) (i : KSSSTrajectoryIndex V q) : ℝ :=
  σ * (ksssTrajectoryValue F S i - ksssTrajectoryTarget a E₀ A₀ t i) -
    ksssTrajectoryError E₀ A₀ scale B t i

theorem probability_not_ksssOnTrajectories_le_signed_tails
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (F : ForbiddenFamilyOn V) (q : ℕ)
    (S₀ : GreedyStateOn V) (S : Ω → GreedyStateOn V) (Q : Ω → Finset (Finset V)) (t : Ω → ℝ)
    (a : ℕ → ℝ) (E₀ A₀ scale : ℝ) (B : ℕ)
    (margin epsilonPlus epsilonMinus : KSSSTrajectoryIndex V q → ℝ)
    (hQ : ∀ ω P, P ∈ Q ω → P.card = 2)
    (hmargin : ∀ i ω, 0 < L.mass ω → ksssTrajectoryTracked (S ω) (Q ω) i →
      |ksssTrajectoryValue F S₀ i - ksssTrajectoryTarget a E₀ A₀ 0 i| + margin i ≤
        ksssTrajectoryError E₀ A₀ scale B 0 i)
    (hplus : ∀ i, (L.probability (fun ω ↦ ksssTrajectoryTracked (S ω) (Q ω) i ∧
      margin i ≤ ksssCenteredTrajectoryObservable F a E₀ A₀ scale B 1 (t ω) (S ω) i -
        ksssCenteredTrajectoryObservable F a E₀ A₀ scale B 1 0 S₀ i) : ℝ) ≤ epsilonPlus i)
    (hminus : ∀ i, (L.probability (fun ω ↦ ksssTrajectoryTracked (S ω) (Q ω) i ∧
      margin i ≤ ksssCenteredTrajectoryObservable F a E₀ A₀ scale B (-1) (t ω) (S ω) i -
        ksssCenteredTrajectoryObservable F a E₀ A₀ scale B (-1) 0 S₀ i) : ℝ) ≤ epsilonMinus i) :
    (L.probability (fun ω ↦ ¬ KSSSOnTrajectories F (S ω) q (Q ω) a E₀ A₀ scale B (t ω)) : ℝ) ≤
      ∑ i, (epsilonPlus i + epsilonMinus i) := by
  classical
  have heq : (fun ω ↦ ¬ KSSSOnTrajectories F (S ω) q (Q ω) a E₀ A₀ scale B (t ω)) =
      (fun ω ↦ ∃ i : KSSSTrajectoryIndex V q, ksssTrajectoryTracked (S ω) (Q ω) i ∧
        ksssTrajectoryError E₀ A₀ scale B (t ω) i <
          |ksssTrajectoryValue F (S ω) i - ksssTrajectoryTarget a E₀ A₀ (t ω) i|) := by
    funext ω
    exact propext (not_ksssOnTrajectories_iff_exists_index F (S ω) q (Q ω) a E₀ A₀ scale B (t ω) (hQ ω))
  rw [heq]
  apply probability_indexed_band_failure_le_two_tails L
    (fun i ω ↦ ksssTrajectoryTracked (S ω) (Q ω) i)
    (fun i ω ↦ ksssTrajectoryValue F (S ω) i - ksssTrajectoryTarget a E₀ A₀ (t ω) i)
    (fun i ω ↦ ksssTrajectoryError E₀ A₀ scale B (t ω) i)
    (fun i ↦ ksssTrajectoryValue F S₀ i - ksssTrajectoryTarget a E₀ A₀ 0 i)
    (fun i ↦ ksssTrajectoryError E₀ A₀ scale B 0 i)
    margin epsilonPlus epsilonMinus hmargin
  · intro i
    simpa only [ksssCenteredTrajectoryObservable, one_mul] using hplus i
  · intro i
    simpa only [ksssCenteredTrajectoryObservable, neg_one_mul] using hminus i

end

end Erdos207
