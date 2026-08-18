/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceWeightedObstructions

/-!
# Audit of the public post-CFP production statement

The public `ProducesTheorem4PostCFPData` proposition has a very strong logical
consequence: for every capped centered coefficient system to which it is
applied, it constructs data which refute nonaveraging.  This file records that
necessary consequence and a concrete three-point nonaveraging coefficient
system against which candidate source hypotheses can be tested.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A small nonaveraging set with a nontrivial real convex dependence. -/
def auditTriple : Finset ℕ := {0, 1, 3}

theorem auditTriple_nonaveraging : IsNonaveraging auditTriple := by
  intro a ha S hS hcard
  simp only [auditTriple, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · have hS' : S ⊆ ({1, 3} : Finset ℕ) := by
      intro x hx
      have hx' := Finset.mem_erase.mp (hS hx)
      simp only [auditTriple, Finset.mem_insert,
        Finset.mem_singleton] at hx' ⊢
      omega
    have hEq : S = ({1, 3} : Finset ℕ) := by
      apply Finset.eq_of_subset_of_card_le hS'
      simpa using hcard
    subst S
    norm_num
  · have hS' : S ⊆ ({0, 3} : Finset ℕ) := by
      intro x hx
      have hx' := Finset.mem_erase.mp (hS hx)
      simp only [auditTriple, Finset.mem_insert,
        Finset.mem_singleton] at hx' ⊢
      omega
    have hEq : S = ({0, 3} : Finset ℕ) := by
      apply Finset.eq_of_subset_of_card_le hS'
      simpa using hcard
    subst S
    norm_num
  · have hS' : S ⊆ ({0, 1} : Finset ℕ) := by
      intro x hx
      have hx' := Finset.mem_erase.mp (hS hx)
      simp only [auditTriple, Finset.mem_insert,
        Finset.mem_singleton] at hx' ⊢
      omega
    have hEq : S = ({0, 1} : Finset ℕ) := by
      apply Finset.eq_of_subset_of_card_le hS'
      simpa using hcard
    subst S
    norm_num

/-- The one-dimensional lattice realization of `auditTriple`. -/
def auditLatticeTriple : Finset (LatticePoint 1) :=
  OneDimensional.lift auditTriple

theorem auditLatticeTriple_nonaveraging :
    IsBoxNonaveraging auditLatticeTriple := by
  exact OneDimensional.isBoxNonaveraging_lift auditTriple_nonaveraging

def auditPoint (n : ℕ) : LatticePoint 1 :=
  OneDimensional.point n

theorem auditPoint_mem (n : ℕ) (hn : n ∈ auditTriple) :
    auditPoint n ∈ auditLatticeTriple := by
  exact Finset.mem_map.mpr ⟨n, hn, rfl⟩

/-- The middle lattice point, regarded as an element of the real image. -/
def auditAnchor : realImage auditLatticeTriple :=
  ⟨latticeEuclidean (auditPoint 1), mem_realImage_of_mem
    (auditPoint_mem 1 (by simp [auditTriple]))⟩

/-- The nonuniform weights `2/3, 0, 1/3` on `0, 1, 3`. -/
def auditWeight (x : LatticePoint 1) : ℝ :=
  if x = auditPoint 0 then 2 / 3
  else if x = auditPoint 3 then 1 / 3
  else 0

def auditCoefficient (y : realImage auditLatticeTriple) : ℝ :=
  auditWeight ((latticeRealImageEquiv auditLatticeTriple).symm y).1

theorem auditCoefficient_bounds (y : realImage auditLatticeTriple) :
    0 ≤ auditCoefficient y ∧
      auditCoefficient y ≤
        (((1 : ℝ) / 2) * auditLatticeTriple.card)⁻¹ := by
  have hcard : auditLatticeTriple.card = 3 := by
    simp [auditLatticeTriple, auditTriple]
  rw [hcard]
  unfold auditCoefficient auditWeight
  split_ifs <;> norm_num

@[simp] theorem pull_auditCoefficient_of_mem
    {x : LatticePoint 1} (hx : x ∈ auditLatticeTriple) :
    pullCoefficient auditLatticeTriple auditCoefficient x = auditWeight x := by
  rw [pullCoefficient_of_mem auditCoefficient hx]
  change auditWeight
      ((latticeRealImageEquiv auditLatticeTriple).symm
        ((latticeRealImageEquiv auditLatticeTriple) ⟨x, hx⟩)).1 =
    auditWeight x
  simp

theorem auditCoefficient_sum : (∑ y, auditCoefficient y) = 1 := by
  have h01 : auditPoint 0 ≠ auditPoint 1 := by
    intro h
    exact (by omega : (0 : ℕ) ≠ 1) (OneDimensional.point_injective h)
  have h03 : auditPoint 0 ≠ auditPoint 3 := by
    intro h
    exact (by omega : (0 : ℕ) ≠ 3) (OneDimensional.point_injective h)
  have h13 : auditPoint 1 ≠ auditPoint 3 := by
    intro h
    exact (by omega : (1 : ℕ) ≠ 3) (OneDimensional.point_injective h)
  rw [← sum_pullCoefficient auditLatticeTriple auditCoefficient]
  calc
    (∑ x ∈ auditLatticeTriple,
        pullCoefficient auditLatticeTriple auditCoefficient x) =
        ∑ x ∈ auditLatticeTriple, auditWeight x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact pull_auditCoefficient_of_mem hx
    _ = 1 := by
      simp [auditWeight, auditLatticeTriple, auditTriple, auditPoint,
        OneDimensional.lift, OneDimensional.pointEmbedding,
        Function.Injective.eq_iff OneDimensional.point_injective]
      norm_num

theorem auditCoefficient_centered :
    (∑ y, auditCoefficient y •
      ((y : EuclideanSpace ℝ (Fin 1)) - auditAnchor)) = 0 := by
  have h01 : auditPoint 0 ≠ auditPoint 1 := by
    intro h
    exact (by omega : (0 : ℕ) ≠ 1) (OneDimensional.point_injective h)
  have h03 : auditPoint 0 ≠ auditPoint 3 := by
    intro h
    exact (by omega : (0 : ℕ) ≠ 3) (OneDimensional.point_injective h)
  have h13 : auditPoint 1 ≠ auditPoint 3 := by
    intro h
    exact (by omega : (1 : ℕ) ≠ 3) (OneDimensional.point_injective h)
  change (∑ y, auditCoefficient y •
      ((y : EuclideanSpace ℝ (Fin 1)) -
        latticeEuclidean (auditPoint 1))) = 0
  rw [← sum_pullCoefficient_centered auditLatticeTriple auditCoefficient
    (auditPoint 1)]
  apply Eq.trans ?_ (show (∑ x ∈ auditLatticeTriple, auditWeight x •
      (latticeEuclidean x - latticeEuclidean (auditPoint 1))) = 0 by
    ext i
    fin_cases i
    simp [auditWeight, auditLatticeTriple, auditTriple,
      auditPoint, latticeEuclidean, OneDimensional.lift,
      OneDimensional.pointEmbedding, OneDimensional.point,
      Function.Injective.eq_iff OneDimensional.point_injective]
    norm_num)
  apply Finset.sum_congr rfl
  intro x hx
  rw [pull_auditCoefficient_of_mem hx]

/-- A concrete population on which all fields of `Theorem4Parameters` allow
the boundary regime `2 * delta = mu`.  Thus the public hierarchy, by itself,
does not imply the strict `2 * delta < mu` separation used by the weighted
two-side argument (and implicitly by the source proof of Lemma 14). -/
def auditParameterPopulation : Finset (LatticePoint 1) :=
  OneDimensional.lift (Finset.range 256)

@[simp] theorem auditParameterPopulation_card :
    auditParameterPopulation.card = 256 := by
  simp [auditParameterPopulation]

theorem auditParameters_allow_no_delta_mu_slack :
    Theorem4Parameters auditParameterPopulation 2 2 1 256
        ((9 : ℝ) / 20) ((1 : ℝ) / 5) ((9 : ℝ) / 10) ∧
      ¬ 2 * ((9 : ℝ) / 20) < (9 : ℝ) / 10 := by
  have hlog : (5 : ℝ) < Real.log (256 : ℝ) := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hlogPos : (0 : ℝ) < Real.log (256 : ℝ) := by linarith
  constructor
  · refine {
      beta_gt_one := by norm_num
      C_pos := by norm_num
      C'_pos := by norm_num
      delta_pos := by norm_num
      gamma_pos := by norm_num
      mu_pos := by norm_num
      delta_lt_one := by norm_num
      gamma_lt_one := by norm_num
      mu_lt_one := by norm_num
      gamma_le_delta := ?_
      delta_le_mu := ?_
      gamma_log_lower := ?_
      card_large := by simp }
    · norm_num [Real.rpow_two]
    · norm_num [Real.rpow_two]
    · norm_num
      rw [Real.rpow_neg_one]
      rw [inv_le_iff_one_le_mul₀ hlogPos]
      linarith
  · norm_num

/-- Exact logical audit of `ProducesTheorem4PostCFPData`: an irreducible
instance carrying a capped centered combination cannot be nonaveraging if
`Produces` holds.  This uses no feature of the weighted proof route. -/
theorem not_producesTheorem4PostCFPData_of_nonaveraging
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (hd : 0 < d) (rankCeiling : ℕ)
    (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
    {C C' : ℝ} {M : ℕ} {delta gamma mu : ℝ}
    (hparams : Theorem4Parameters A beta C C' M delta gamma mu)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ))
    (hirr : Reduction.IsBoundedCoordinateIrreducible
      selector A hA delta gamma)
    (hNA : IsBoxNonaveraging (selector.chosen A hA).identifiedCore)
    (a₀ : realImage (selector.chosen A hA).identifiedCore)
    (c : realImage (selector.chosen A hA).identifiedCore → ℝ)
    (hc : ∀ x, 0 ≤ c x ∧
      c x ≤ (mu * (selector.chosen A hA).identifiedCore.card)⁻¹)
    (hsum : (∑ x, c x) = 1)
    (hcenter : (∑ x, c x •
      ((x : EuclideanSpace ℝ
        (Fin (selector.chosen A hA).dimension)) - a₀)) = 0) :
    ¬ ProducesTheorem4PostCFPData selector A hA hd rankCeiling hrank
      delta gamma mu hparams hclosed hcoreRetention := by
  intro hproduces
  obtain ⟨D, _hanchor⟩ := hproduces hirr a₀ c hc hsum hcenter
  exact D.not_nonaveraging hNA

end

end Erdos186.PZ.Intersection
