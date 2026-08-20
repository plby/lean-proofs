/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.HybridTaylor

/-!
# The negative-phase hybrid large sieve

The finite zero detector uses the phase `exp (-I * t * log n)`, whereas the
block estimate in `HybridTaylor` is stated with the positive phase.  Negating
both the block centres and their logarithmic offsets gives the required form
without changing any spacing or size hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

/-- Primitive-character mass of a Dirichlet polynomial with the phase used
by the zero detector. -/
noncomputable def primitiveNegativeDirichletBlockMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (s : ι → Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        ‖∑ i, ∑ n ∈ s i,
          c n * psi.1 n *
            Complex.exp (Complex.I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2

/-- The general hybrid polynomial becomes the negative-phase Dirichlet
polynomial after negating the usual block centre and logarithmic offset. -/
theorem primitiveHybridMass_neg_blockLogOffset_eq
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j)) (t : ℝ) :
    primitiveHybridMass Q (fun i ↦ -x i) s c
        (fun n ↦ -blockLogOffset x s n) t =
      primitiveNegativeDirichletBlockMass Q s c t := by
  classical
  unfold primitiveHybridMass primitiveNegativeDirichletBlockMass
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun z : ℝ ↦ (q : ℝ) / (q.totient : ℝ) * z)
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [blockLogOffset_eq x s hdisj i hn]
  congr 2
  push_cast
  ring

/-- Hybrid large sieve for the negative phase appearing in the finite zero
detector. -/
theorem intervalIntegral_primitiveNegativeDirichletBlockMass_le
    {ι : Type*} [Fintype ι]
    (Q H : ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hB : 0 ≤ B)
    (hoffset : ∀ i, ∀ n ∈ s i, |Real.log n - x i| ≤ B) :
    (∫ t in (0 : ℝ)..T,
        primitiveNegativeDirichletBlockMass Q s c t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
            ∑ i, ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let d : ℕ → ℝ := fun n ↦ -blockLogOffset x s n
  have hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B := by
    intro i n hn
    rw [show d n = -(Real.log n - x i) by
      dsimp [d]
      rw [blockLogOffset_eq x s hdisj i hn], abs_neg]
    exact hoffset i n hn
  have hsepNeg : ∀ r t, r ≠ t → δ ≤ |(-x r) - (-x t)| := by
    intro r t hrt
    simpa only [neg_sub_neg, abs_neg] using hsep t r hrt.symm
  have hmain := intervalIntegral_primitiveHybridMass_le
    Q H s m0 hs (fun i ↦ -x i) hδ hT hsepNeg c d hB hd
  rw [show primitiveHybridMass Q (fun i ↦ -x i) s c d =
      primitiveNegativeDirichletBlockMass Q s c by
    funext t
    exact primitiveHybridMass_neg_blockLogOffset_eq Q x s c hdisj t] at hmain
  exact hmain

end Erdos48
