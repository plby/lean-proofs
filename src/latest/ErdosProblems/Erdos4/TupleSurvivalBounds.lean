import ErdosProblems.Erdos4.AggregatedTupleMoments

/-!
# Joint survival supplies all three tuple moments

This file connects the proved uniform random-sieve estimate with the
actual tuple geometry and the aggregate moment inequalities. The
accuracy threshold is uniform over all moving prime-index types.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.TupleSurvivalBounds

open RandomResidueSieve AffineTuples TupleCollisionMass ConditionalTupleMoments
open AggregatedTupleMoments

universe u

def Accurate {P : Type*} [Fintype P] [DecidableEq P] (ell : P → ℕ)
    [∀ l, Fact (ell l).Prime] (B r : ℕ) (ε : ℝ) : Prop :=
  ∀ T : Finset ℕ, T.card ≤ r → (∀ n ∈ T, n ≤ B) →
    |survivalMass ell T / UnitFourier.unitDensity ell ^ T.card - 1| ≤ ε

theorem eventually_accurate (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (ell : P → ℕ) [∀ l, Fact (ell l).Prime],
      Function.Injective ell → (∀ l, Real.log (B : ℝ) ^ 2 ≤ ell l) → Accurate ell B r ε :=
  JointSurvivalAsymptotic.eventually_uniform_relative_error r hε

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem conditional_bounds {B r : ℕ} {ε : ℝ} (hacc : Accurate ell B r ε)
    (T : Finset ℕ) (hcard : T.card ≤ r) (hT : ∀ n ∈ T, n ≤ B) (q : ℕ) (hq : q ∈ T) :
    (1 - ε) * UnitFourier.unitDensity ell ^ (T.card - 1) ≤
      mean ell q (fun a => indicator ell a T) ∧
    mean ell q (fun a => indicator ell a T) ≤
      (1 + ε) * UnitFourier.unitDensity ell ^ (T.card - 1) := by
  have hrel := abs_le.mp (conditional_relative_error ell q T hq (hacc T hcard hT))
  have hpos := pow_pos (UnitFourier.unitDensity_pos ell) (T.card - 1)
  constructor
  · apply (le_div_iff₀ hpos).mp
    linarith
  · apply (div_le_iff₀ hpos).mp
    linarith

theorem union_points_bound {B : ℕ} {T U : Finset ℕ}
    (hT : ∀ n ∈ T, n ≤ B) (hU : ∀ n ∈ U, n ≤ B) : ∀ n ∈ T ∪ U, n ≤ B := by
  intro n hn
  exact (Finset.mem_union.mp hn).elim (hT n) (hU n)

variable {k : ℕ}

theorem tuple_points_bound (K X Y : ℕ) {p n : ℕ} (hp : p ≤ X) (hn : n ≤ Y) :
    ∀ y ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n, y ≤ Y + k * primorial K * X := by
  intro y hy
  obtain ⟨i, rfl⟩ := (mem_tuple (AffineWeights.shift K) p n y).mp hy
  exact Nat.add_le_add hn (Nat.mul_le_mul (AffineWeights.shift_le_bound K i) hp)

theorem anchored_union_card (K : ℕ) {p p' n n' q : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hK : K < p) (hk : k ≤ p) (hne : p ≠ p')
    (hq : q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n)
    (hq' : q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p' n') :
    (tuple (AffineWeights.shift K : Fin k → ℕ) p n ∪
      tuple (AffineWeights.shift K : Fin k → ℕ) p' n').card = 2 * k - 1 := by
  have hh := Finset.card_union_add_card_inter
    (tuple (AffineWeights.shift K : Fin k → ℕ) p n)
    (tuple (AffineWeights.shift K : Fin k → ℕ) p' n')
  rw [intersection_eq_singleton K hp hp' hK hk hne hq hq', Finset.card_singleton,
    card_tuple _ (shift_injective K) hp.pos n,
    card_tuple _ (shift_injective K) hp'.pos n'] at hh
  omega

/-- The three moment estimates for the actual affine tuple geometry.
The local accuracy premise is supplied uniformly by `eventually_accurate`.
The probability and atom premises are supplied by the checked affine
normalization theorem. -/
theorem three_moments (K : ℕ) (sources : Finset ℕ) (Y B : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ) {ε α : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α)
    (hacc : Accurate ell B (2 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ K < p ∧ k ≤ p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y,
      ∀ y ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n, y ≤ B)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α)
    (hμsum : ∀ p ∈ sources, ∑ n ∈ Finset.Icc 1 Y, μ p n = 1) :
    let h : Fin k → ℕ := AffineWeights.shift K
    let τ := ∑ p : sources, hitMass h p Y (μ p) q
    (1 - ε) * UnitFourier.unitDensity ell ^ (k - 1) * τ ≤
      mean ell q (fun a => ∑ p : sources, hittingMass ell h p Y (μ p) q a) ∧
    mean ell q (fun a => (∑ p : sources, hittingMass ell h p Y (μ p) q a) ^ 2) ≤
      ((1 + ε) * UnitFourier.unitDensity ell ^ (2 * k - 2)) * τ ^ 2 + (k : ℝ) * α * τ ∧
    mean ell q (fun a => ∑ p : sources,
      tupleMass ell h p Y (μ p) a * hittingMass ell h p Y (μ p) q a) ≤
      ((1 + ε) * UnitFourier.unitDensity ell ^ (2 * k - 1) + (k : ℝ) ^ 2 * α) * τ := by
  dsimp only
  have hV := UnitFourier.unitDensity_pos ell
  have hsingle : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, q ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n →
      (1 - ε) * UnitFourier.unitDensity ell ^ (k - 1) ≤
        mean ell q (fun a => indicator ell a (tuple (AffineWeights.shift K : Fin k → ℕ) p n)) := by
    intro p hp n hn hq
    have hc := card_tuple (AffineWeights.shift K : Fin k → ℕ) (shift_injective K) (hs p hp).1.pos n
    have hh := (conditional_bounds ell hacc _ (by rw [hc]; omega) (hpoints p hp n hn) q hq).1
    simpa only [hc] using hh
  refine ⟨firstMoment_lower ell (AffineWeights.shift K) sources Y μ q hμ0 hsingle, ?_, ?_⟩
  · apply secondMoment_le ell (AffineWeights.shift K) sources Y μ q hα (by positivity) hμ0 hμ
    intro p hp p' hp' hne n hn n' hn' hq hq'
    have hc := anchored_union_card K (hs p hp).1 (hs p' hp').1 (hs p hp).2.1
      (hs p hp).2.2 hne hq hq'
    have hh := (conditional_bounds ell hacc _ (by rw [hc]; omega)
      (union_points_bound (hpoints p hp n hn) (hpoints p' hp' n' hn')) q
      (Finset.mem_union_left _ hq)).2
    simpa only [hc, Nat.sub_sub, Nat.reduceAdd] using hh
  · apply mixedMoment_le ell (AffineWeights.shift K) (shift_injective K) sources
      (fun p hp => (hs p hp).1.pos) Y μ q hα (by positivity) hμ0 hμ hμsum
    intro p hp n hn n' hn' hq hd
    have hc : (tuple (AffineWeights.shift K : Fin k → ℕ) p n ∪
        tuple (AffineWeights.shift K : Fin k → ℕ) p n').card = 2 * k := by
      rw [Finset.card_union_of_disjoint hd,
        card_tuple _ (shift_injective K) (hs p hp).1.pos n,
        card_tuple _ (shift_injective K) (hs p hp).1.pos n']
      omega
    have hh := (conditional_bounds ell hacc _ (by rw [hc])
      (union_points_bound (hpoints p hp n hn) (hpoints p hp n' hn')) q
      (Finset.mem_union_right _ hq)).2
    simpa only [hc] using hh

end Erdos4.TupleSurvivalBounds
