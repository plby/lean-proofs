import ErdosProblems.Erdos906.Topology
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Set

namespace CofiniteDerivatives

/-- The zero set of the `n`-th complex derivative. -/
def derivativeZeroSet (f : ℂ → ℂ) (n : ℕ) : Set ℂ :=
  {z | iteratedDeriv n f z = 0}

/-- Every nonempty open set contains a zero of every sufficiently high derivative. -/
def DerivativesCofinitelyHit (f : ℂ → ℂ) : Prop :=
  CofinitelyHits (derivativeZeroSet f)

/-- Along every increasing sequence of derivative orders, the union of zero sets is dense. -/
def EveryDerivativeSubsequenceDense (f : ℂ → ℂ) : Prop :=
  EverySubsequenceDense (derivativeZeroSet f)

/-- Exact quantifier equivalence for zeros of iterated complex derivatives. -/
theorem derivativesCofinitelyHit_iff_everyDerivativeSubsequenceDense (f : ℂ → ℂ) :
    DerivativesCofinitelyHit f ↔ EveryDerivativeSubsequenceDense f :=
  cofiniteHits_iff_everySubsequenceDense (derivativeZeroSet f)

/-- The cofinite formulation, expanded into its original quantifier order. -/
theorem derivativesCofinitelyHit_iff (f : ℂ → ℂ) :
    DerivativesCofinitelyHit f ↔
      ∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0 := by
  unfold DerivativesCofinitelyHit CofinitelyHits goodOrders derivativeZeroSet
  constructor
  · intro h U hU hUne
    obtain ⟨N, hN⟩ := h U hU hUne
    refine ⟨N, fun n hn ↦ ?_⟩
    rcases hN n hn with ⟨z, hz, hzU⟩
    exact ⟨z, hzU, hz⟩
  · intro h U hU hUne
    obtain ⟨N, hN⟩ := h U hU hUne
    refine ⟨N, fun n hn ↦ ?_⟩
    rcases hN n hn with ⟨z, hzU, hz⟩
    exact ⟨z, hz, hzU⟩

/-- Under cofinite hitting, only finitely many derivatives can be zero-free on any fixed
positive-radius disk. -/
theorem finite_zeroFree_derivative_orders_on_ball
    (f : ℂ → ℂ) (hf : DerivativesCofinitelyHit f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    {n : ℕ | ∀ z ∈ Metric.ball c R, iteratedDeriv n f z ≠ 0}.Finite := by
  obtain ⟨N, hN⟩ := (derivativesCofinitelyHit_iff f).mp hf
    (Metric.ball c R) Metric.isOpen_ball (Metric.nonempty_ball.mpr hR)
  apply (finite_Iio N).subset
  intro n hn
  by_contra hnN
  obtain ⟨z, hzball, hzero⟩ := hN n (Nat.le_of_not_gt hnN)
  exact hn z hzball hzero

end CofiniteDerivatives
