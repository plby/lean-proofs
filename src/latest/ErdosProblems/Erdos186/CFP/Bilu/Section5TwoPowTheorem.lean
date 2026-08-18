/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5TwoPowInduction
import ErdosProblems.Erdos186.CFP.Bilu.Section5ProjectionSlice

/-!
# Freiman's affine-slice theorem below `2^n`

The quantitative `2^n` induction is specialized at an arbitrary positive
gap `epsilon`, and then transported through Bilu's generic projection.  The
resulting proportion constant depends only on the requested rank and gap.
-/

namespace Erdos186.CFP.Bilu.Section5TwoPowTheorem

open Set Module Submodule
open Section7FreimanMap Section5TwoN Section5EpsilonCalc
  Section5EpsilonInduction Section5TwoPowEpsilonCalc
  Section5TwoPowInduction Section5GenericProjection Section5ProjectionSlice

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The sparsity density which makes the quantitative error equal to the
prescribed positive gap below `2 ^ n`. -/
def twoPowTheoremDensity (n : ℕ) (epsilon : ℝ) : ℝ :=
  twoPowCubeDensity n / (4 * (n : ℝ)) *
    (epsilon / ((2 ^ n : ℕ) : ℝ)) ^
      (epsilonExponent n (twoPowCubeDensity n))⁻¹

theorem twoPowTheoremDensity_pos {n : ℕ} (hn : 0 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < twoPowTheoremDensity n epsilon := by
  unfold twoPowTheoremDensity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := twoPowCubeDensity_pos hn
  have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hx : 0 < epsilon / (((2 ^ n : ℕ) : ℝ)) := by positivity
  positivity

theorem twoPowNEpsilon_theoremDensity {n : ℕ} (hn : 0 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    twoPowNEpsilon n (twoPowCubeDensity n)
      (twoPowTheoremDensity n epsilon) = epsilon := by
  let d := twoPowCubeDensity n
  let nu := epsilonExponent n d
  let q : ℝ := ((2 ^ n : ℕ) : ℝ)
  let x : ℝ := epsilon / q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < d := twoPowCubeDensity_pos hn
  have hnu : 0 < nu := epsilonExponent_pos hn hd
  have hq : 0 < q := by unfold q; positivity
  have hx : 0 < x := by unfold x; positivity
  have hbase :
      4 * (n : ℝ) * twoPowTheoremDensity n epsilon /
          twoPowCubeDensity n = x ^ nu⁻¹ := by
    have hdCube : twoPowCubeDensity n ≠ 0 :=
      (twoPowCubeDensity_pos hn).ne'
    dsimp [x, q, nu, d]
    unfold twoPowTheoremDensity
    field_simp [hdCube]
  unfold twoPowNEpsilon
  rw [hbase]
  rw [← Real.rpow_mul hx.le]
  rw [inv_mul_cancel₀ hnu.ne', Real.rpow_one]
  dsimp [x, q]
  field_simp

/-- In full rank, doubling below `2^n - epsilon` forces a fixed-density
subset into a proper affine plane. -/
theorem exists_dense_hyperplane_twoPowGap
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [DecidableEq V]
    {n : ℕ} (hn : 0 < n) (hfinrank : finrank ℝ V = n)
    (S : Finset V) (hS : S.Nonempty)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdouble : ((pairSumset S).card : ℝ) <
      (((2 ^ n : ℕ) : ℝ) - epsilon) * S.card) :
    ∃ plane : AffineSubspace ℝ V,
      finrank ℝ plane.direction < n ∧
        twoPowTheoremDensity n epsilon * S.card ≤
          ((S.filter fun x ↦ x ∈ plane).card : ℝ) := by
  by_contra hnone
  have hsparse : HyperplaneSparse n (twoPowTheoremDensity n epsilon) S := by
    intro plane hplane
    have hnot : ¬ twoPowTheoremDensity n epsilon * S.card ≤
        ((S.filter fun x ↦ x ∈ plane).card : ℝ) := by
      intro hdense
      apply hnone
      exact ⟨plane, hplane, hdense⟩
    exact lt_of_not_ge hnot
  have hlower := pairSumset_card_twoPow_lower_bound hn hfinrank S hS
    (twoPowTheoremDensity n epsilon)
    (twoPowTheoremDensity_pos hn hepsilon) hsparse
  rw [twoPowNEpsilon_theoremDensity hn hepsilon] at hlower
  exact (not_lt_of_ge hlower) hdouble

/-- Exact full-dimensional proposition at a prescribed gap. -/
def RankTwoPowGapStatement
    (rank proportionConstant : ℕ) (epsilon : ℝ) : Prop :=
  ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [DecidableEq W],
    finrank ℝ W = rank →
    ∀ S : Finset W, S.Nonempty →
      ((pairSumset S).card : ℝ) <
        (((2 ^ rank : ℕ) : ℝ) - epsilon) * S.card →
      Nonempty (AffineSliceWitness rank proportionConstant S)

/-- The full-dimensional `2^n` theorem has a uniform natural packing
constant depending only on rank and the positive gap. -/
theorem exists_rankTwoPowGapStatement
    (rank : ℕ) (hrank : 0 < rank)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ proportionConstant : ℕ,
      RankTwoPowGapStatement.{u} rank proportionConstant epsilon := by
  let density := twoPowTheoremDensity rank epsilon
  have hdensity : 0 < density := twoPowTheoremDensity_pos hrank hepsilon
  obtain ⟨proportionConstant, hconstant⟩ :=
    exists_nat_gt (1 / density)
  refine ⟨proportionConstant, ?_⟩
  intro W _ _ _ _ hfinrank S hS hdouble
  obtain ⟨plane, hdim, hdense⟩ :=
    exists_dense_hyperplane_twoPowGap hrank hfinrank S hS hepsilon hdouble
  let slice := S.filter fun x ↦ x ∈ plane
  have hslice0 : (0 : ℝ) ≤ slice.card := by positivity
  have hrealCard : (S.card : ℝ) ≤
      (proportionConstant : ℝ) * slice.card := by
    have hinvpos : 0 < (1 / density : ℝ) := by positivity
    calc
      (S.card : ℝ) = (1 / density) * (density * S.card) := by
        field_simp
      _ ≤ (1 / density) * slice.card :=
        mul_le_mul_of_nonneg_left hdense hinvpos.le
      _ ≤ (proportionConstant : ℝ) * slice.card :=
        mul_le_mul_of_nonneg_right hconstant.le hslice0
  refine ⟨{
    plane := plane
    dimension_lt := hdim
    slice := slice
    slice_subset := Finset.filter_subset _ _
    slice_mem_plane := ?_
    card_le := ?_ }⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · exact_mod_cast hrealCard

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

local instance quotientDecidableEq (A : Submodule ℝ V) :
    DecidableEq (V ⧸ A) := Classical.decEq _

local instance finiteDimensionalSubmoduleIsClosed (A : Submodule ℝ V) :
    IsClosed (A : Set V) := A.closed_of_finiteDimensional

/-- Generic projection transports the gap theorem from exact ambient rank
to every ambient space of at least that rank. -/
theorem exists_affineSlice_of_rankTwoPowGap
    {rank proportionConstant : ℕ} {epsilon : ℝ}
    (hGap : RankTwoPowGapStatement.{u} rank proportionConstant epsilon)
    (S : Finset V) (hS : S.Nonempty)
    (hrank : 0 < rank) (hrank_le : rank ≤ finrank ℝ V)
    (hdouble : ((pairSumset S).card : ℝ) <
      (((2 ^ rank : ℕ) : ℝ) - epsilon) * S.card) :
    Nonempty (AffineSliceWitness rank proportionConstant S) := by
  let P : GenericProjection S rank := genericProjection S rank
  have hquotientRank : finrank ℝ (V ⧸ P.kernel) = rank :=
    P.finrank_quotient_eq hrank_le
  have hquotientNonempty : (S.image P.kernel.mkQ).Nonempty := hS.image _
  have hsourceCard : (S.image P.kernel.mkQ).card = S.card :=
    Finset.card_image_of_injOn (P.mkQ_injOn hS hrank)
  have hquotientDouble :
      ((pairSumset (S.image P.kernel.mkQ)).card : ℝ) <
        (((2 ^ rank : ℕ) : ℝ) - epsilon) *
          (S.image P.kernel.mkQ).card := by
    rw [card_pairSumset_image_mkQ P hrank, hsourceCard]
    exact hdouble
  have hW : Nonempty (AffineSliceWitness rank proportionConstant
      (S.image P.kernel.mkQ)) :=
    hGap (V ⧸ P.kernel) hquotientRank
      (S.image P.kernel.mkQ) hquotientNonempty hquotientDouble
  exact exists_affineSlice_of_quotient P hS hrank hW

/-- Uniform generalized Freiman theorem with arbitrary positive gap below
`2 ^ rank`. -/
theorem exists_constant_affineSlice_twoPowGap
    (rank : ℕ) (hrank : 0 < rank)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ proportionConstant : ℕ,
      ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W]
        [FiniteDimensional ℝ W] [DecidableEq W],
        rank ≤ finrank ℝ W →
        ∀ S : Finset W, S.Nonempty →
          ((pairSumset S).card : ℝ) <
            (((2 ^ rank : ℕ) : ℝ) - epsilon) * S.card →
          Nonempty (AffineSliceWitness rank proportionConstant S) := by
  obtain ⟨proportionConstant, hGap⟩ :=
    exists_rankTwoPowGapStatement rank hrank epsilon hepsilon
  refine ⟨proportionConstant, ?_⟩
  intro W _ _ _ _ hrank_le S hS hdouble
  exact exists_affineSlice_of_rankTwoPowGap hGap S hS hrank hrank_le hdouble

end


end Erdos186.CFP.Bilu.Section5TwoPowTheorem

#print axioms
  Erdos186.CFP.Bilu.Section5TwoPowTheorem.exists_dense_hyperplane_twoPowGap
#print axioms
  Erdos186.CFP.Bilu.Section5TwoPowTheorem.exists_constant_affineSlice_twoPowGap
