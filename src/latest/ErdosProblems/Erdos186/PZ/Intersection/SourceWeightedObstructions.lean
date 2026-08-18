/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.WeightedSourceMassNumerics

/-!
# Sharp limitations of source weighted-slab variants

Two tempting variants cannot improve the source mass budget:

* Definition 9 and candidate closure transport only to a *larger* density
  threshold, whereas a weighted-slab improvement needs a smaller one.
* Every disjoint two-side partition has one coefficient mass at most half of
  the mass outside the distinguished point.  Thus using a different
  coefficient-balanced partition cannot give more than half the source mass
  simultaneously to both signs.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Local candidate closure is monotone toward larger density thresholds. -/
theorem Reduction.BoundedCFPSelector.candidateClosedAt_mono_density
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {d : ℕ} {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta delta' : ℝ} (hdelta : delta ≤ delta')
    (hclosed : selector.CandidateClosedAt A hA delta) :
    selector.CandidateClosedAt A hA delta' := by
  intro X hX hXne hdense x hx
  apply hclosed X hX hXne _ x hx
  exact (mul_le_mul_of_nonneg_right hdelta (by positivity)).trans hdense

/-- Bounded coordinate irreducibility has the same one-way density
monotonicity: a conclusion at `delta` applies at `delta'` only when
`delta ≤ delta'`. -/
theorem Reduction.isBoundedCoordinateIrreducible_mono_density
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {d : ℕ} {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta delta' gamma : ℝ} (hdelta : delta ≤ delta')
    (hirr : Reduction.IsBoundedCoordinateIrreducible
      selector A hA delta gamma) :
    Reduction.IsBoundedCoordinateIrreducible
      selector A hA delta' gamma := by
  dsimp only [Reduction.IsBoundedCoordinateIrreducible] at hirr ⊢
  intro X hX hXne hdense x hx hshift
  apply hirr X hX hXne _ x hx hshift
  exact (mul_le_mul_of_nonneg_right hdelta (by positivity)).trans hdense

/-- In every disjoint two-piece partition, at least one side has at most half
of the total weight. -/
theorem min_partitionWeight_le_half
    {α : Type*} [DecidableEq α]
    (S A₁ A₂ : Finset α) (q : α → ℝ)
    (hunion : A₁ ∪ A₂ = S) (hdisjoint : Disjoint A₁ A₂) :
    min (∑ x ∈ A₁, q x) (∑ x ∈ A₂, q x) ≤
      (∑ x ∈ S, q x) / 2 := by
  have hsum : (∑ x ∈ A₁, q x) + (∑ x ∈ A₂, q x) =
      ∑ x ∈ S, q x := by
    rw [← Finset.sum_union hdisjoint, hunion]
  rcases le_total (∑ x ∈ A₁, q x) (∑ x ∈ A₂, q x) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- Applied to the PZ source coefficients, no disjoint repartition of all
points away from `a` can give both signs more than half of
`1 - coefficient(a)`. -/
theorem min_partitionCoefficientMass_le_half
    (D : ConvexPoolsData A a₀ c mu)
    (B₁ B₂ : Finset (LatticePoint d))
    (hunion : B₁ ∪ B₂ = A.erase D.a)
    (hdisjoint : Disjoint B₁ B₂) :
    min (∑ x ∈ B₁, pullCoefficient A c x)
        (∑ x ∈ B₂, pullCoefficient A c x) ≤
      (1 - pullCoefficient A c D.a) / 2 := by
  have hhalf := min_partitionWeight_le_half (A.erase D.a) B₁ B₂
    (pullCoefficient A c) hunion hdisjoint
  have herase : (∑ x ∈ A.erase D.a, pullCoefficient A c x) =
      1 - pullCoefficient A c D.a := by
    have hsplit := Finset.sum_erase_add A (pullCoefficient A c) D.a_mem
    linarith [D.coefficient_sum]
  rwa [herase] at hhalf

/-- The existing alternating partition is optimal up to one coefficient cap:
its smaller side lies between half the off-center mass minus half a cap and
the universal half-mass upper bound. -/
theorem alternating_partition_min_mass_bounds
    (D : ConvexPoolsData A a₀ c mu) :
    (1 - pullCoefficient A c D.a - (mu * A.card)⁻¹) / 2 ≤
        min (∑ x ∈ D.A₁, pullCoefficient A c x)
          (∑ x ∈ D.A₂, pullCoefficient A c x) ∧
      min (∑ x ∈ D.A₁, pullCoefficient A c x)
          (∑ x ∈ D.A₂, pullCoefficient A c x) ≤
        (1 - pullCoefficient A c D.a) / 2 := by
  constructor
  · exact le_min D.coefficient_mass_lower_A₁ D.coefficient_mass_lower_A₂
  · exact D.min_partitionCoefficientMass_le_half D.A₁ D.A₂
      D.union_eq D.disjoint

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
