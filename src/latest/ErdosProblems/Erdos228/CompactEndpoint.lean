/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import ErdosProblems.Erdos228.Discrepancy

/-!
# The compactness endpoint in the partial-colouring argument

The finite Gaussian walk used in the Lovett--Meka argument naturally first
produces, for every positive tolerance, a cube point at which at least half of
the coordinates are within that tolerance of a face.  This file records the
compactness argument which removes the tolerance.  The linear discrepancy
inequalities are closed, so they pass to the limiting cube point as well.
-/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace Erdos228.Discrepancy

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Coordinates which are within `epsilon` of one of the two faces of the
cube.  On the cube this is the same as being within `epsilon` of `1` or
`-1`. -/
def approximateFixedCoordinates [DecidableEq I]
    (epsilon : ℝ) (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - epsilon ≤ |x i|

@[simp]
theorem mem_approximateFixedCoordinates [DecidableEq I]
    {epsilon : ℝ} {x : I → ℝ} {i : I} :
    i ∈ approximateFixedCoordinates epsilon x ↔ 1 - epsilon ≤ |x i| := by
  simp [approximateFixedCoordinates]

omit [Fintype I] in
/-- The coordinate cube is compact in the product topology. -/
theorem isCompact_inCube : IsCompact {x : I → ℝ | InCube x} := by
  have hset : {x : I → ℝ | InCube x} =
      Set.pi Set.univ (fun _ : I ↦ Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, mem_Icc]
    constructor
    · intro hx i
      simpa only [abs_le] using hx i
    · intro hx i
      simpa only [abs_le] using hx i
  rw [hset]
  exact isCompact_univ_pi fun _ ↦ isCompact_Icc

omit [Fintype J] in
/-- If arbitrarily accurate approximate partial colourings satisfy fixed
closed discrepancy bounds, then an exact partial colouring satisfies the same
bounds.  The cardinal inequality is the integer form of saying that at least
`ceil(card I / 2)` coordinates have reached a face. -/
theorem hasPartialColoring_of_approximate [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ x : I → ℝ,
        InCube x ∧
          Fintype.card I ≤
            2 * (approximateFixedCoordinates epsilon x).card ∧
          ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j)) :
    HasPartialColoring v x₀ c := by
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hepsilon_pos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hwitness : ∀ n : ℕ, ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤
          2 * (approximateFixedCoordinates (epsilon n) x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j) := by
    intro n
    exact happrox (epsilon n) (hepsilon_pos n)
  choose x hxCube hxCard hxDiscrepancy using hwitness
  obtain ⟨xLimit, hxLimitCube, phi, hphi, hxLimit⟩ :=
    isCompact_inCube.tendsto_subseq hxCube
  refine ⟨xLimit, hxLimitCube, ?_, ?_⟩
  · have hepsilon_tendsto :
        Tendsto epsilon atTop (nhds (0 : ℝ)) := by
      simpa only [epsilon, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
    have hepsilon_subseq :
        Tendsto (fun n ↦ epsilon (phi n)) atTop (nhds (0 : ℝ)) :=
      hepsilon_tendsto.comp hphi.tendsto_atTop
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hnotApprox (i : I) (hi : i ∉ fixedCoordinates xLimit) :
        ∀ᶠ n in atTop,
          i ∉ approximateFixedCoordinates (epsilon (phi n)) (x (phi n)) := by
      have habs_le : |xLimit i| ≤ 1 := hxLimitCube i
      have habs_ne : |xLimit i| ≠ 1 := by
        simpa [fixedCoordinates] using hi
      have hgap : 0 < 1 - |xLimit i| := sub_pos.mpr (lt_of_le_of_ne habs_le habs_ne)
      have htendsto :
          Tendsto
            (fun n ↦ 1 - epsilon (phi n) - |x (phi n) i|)
            atTop (nhds (1 - |xLimit i|)) := by
        simpa using
          (tendsto_const_nhds.sub hepsilon_subseq).sub
            ((hxCoordinate i).abs)
      have hpositive :
          ∀ᶠ n in atTop, 0 < 1 - epsilon (phi n) - |x (phi n) i| :=
        htendsto.eventually (isOpen_Ioi.mem_nhds hgap)
      filter_upwards [hpositive] with n hn
      simp only [mem_approximateFixedCoordinates, not_le]
      linarith
    have hsubset_eventually :
        ∀ᶠ n in atTop,
          approximateFixedCoordinates (epsilon (phi n)) (x (phi n)) ⊆
            fixedCoordinates xLimit := by
      have hall :
          ∀ᶠ n in atTop, ∀ i : I,
            i ∈ approximateFixedCoordinates (epsilon (phi n)) (x (phi n)) →
              i ∈ fixedCoordinates xLimit := by
        apply Filter.eventually_all.mpr
        intro i
        by_cases hfixed : i ∈ fixedCoordinates xLimit
        · exact Eventually.of_forall fun _ _ ↦ hfixed
        · exact (hnotApprox i hfixed).mono fun _ hnot hmem ↦
            False.elim (hnot hmem)
      exact hall.mono fun _ hn _ hi ↦ hn _ hi
    obtain ⟨n, hsubset⟩ := hsubset_eventually.exists
    have hcardSubset := Finset.card_le_card hsubset
    exact (hxCard (phi n)).trans (Nat.mul_le_mul_left 2 hcardSubset)
  · intro j
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hdot :
        Tendsto (fun n ↦ dot (x (phi n) - x₀) (v j)) atTop
          (nhds (dot (xLimit - x₀) (v j))) := by
      unfold dot
      apply tendsto_finsetSum
      intro i hi
      exact ((hxCoordinate i).sub tendsto_const_nhds).mul_const (v j i)
    exact le_of_tendsto' hdot.abs fun n ↦ hxDiscrepancy (phi n) j

end Erdos228.Discrepancy
