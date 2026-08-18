/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.FunctionalSlab
import ErdosProblems.Erdos186.PZ.Intersection.JohnDifferenceComparison
import ErdosProblems.Erdos186.PZ.Intersection.SlabJohnContradiction

/-!
# From a narrow functional slab to a John/CFP volume bound

This file composes the geometric functional-slab estimate with the
unconditional PZ Lemma 7 and the centered-John comparison for an enhanced
CFP witness.  The conclusion is the source dichotomy: either the John
progression loses dimension, or the selected CFP progression has volume at
most an explicit dimension-only/CFP-parameter multiple of the slab volume.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators ENNReal
open OneStepAssembly

noncomputable section

set_option autoImplicit false

/-- A lattice point satisfying the functional inequality belongs to the
literal lattice section of `functionalSlabInBox`. -/
theorem mem_boxLatticePointsIn_functionalSlabInBox {d : ℕ}
    (B : IntegerBox d) (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ)
    {x : LatticePoint d} (hxB : x ∈ B.carrier)
    (hxslab : |f (realVector x)| < t * coefficientMass f) :
    x ∈ boxLatticePointsIn B (functionalSlabInBox B f t) := by
  unfold boxLatticePointsIn
  rw [mem_latticeRestriction]
  refine ⟨hxB, ?_⟩
  rw [mem_functionalSlabInBox_iff]
  constructor
  · change ∀ i, (B.lower i : ℝ) ≤ (x i : ℝ) ∧
        (x i : ℝ) ≤ (B.upper i : ℝ)
    intro i
    have hxi := (IntegerBox.mem_carrier_iff.mp hxB) i
    exact ⟨by exact_mod_cast hxi.1, by exact_mod_cast hxi.2⟩
  · change |f (fun i ↦ (x i : ℝ))| < t * coefficientMass f
    exact hxslab

/-- Nonzero functionals have positive coefficient mass. -/
theorem coefficientMass_pos {d : ℕ}
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (hf : f ≠ 0) :
    0 < coefficientMass f := by
  have hd : 0 < d := by
    by_contra hdz
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hdz
    subst d
    exact hf (Subsingleton.elim _ _)
  cases d with
  | zero => omega
  | succ n =>
      obtain ⟨i, hi, _himax⟩ := exists_maximal_coefficient f hf
      have hsingle : |f (Pi.single i 1)| ≤ coefficientMass f := by
        exact Finset.single_le_sum
          (fun j _hj ↦ abs_nonneg (f (Pi.single j 1)))
          (Finset.mem_univ i)
      exact (abs_pos.mpr hi).trans_le hsingle

/-- The origin belongs to the lattice section of a positive functional
slab whenever it belongs to the integer box. -/
theorem zero_mem_boxLatticePointsIn_functionalSlabInBox {d : ℕ}
    (B : IntegerBox d) (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hf : f ≠ 0) (ht : 0 < t) (hzeroB : (0 : LatticePoint d) ∈ B.carrier) :
    (0 : LatticePoint d) ∈
      boxLatticePointsIn B (functionalSlabInBox B f t) := by
  apply mem_boxLatticePointsIn_functionalSlabInBox B f t hzeroB
  have hz : realVector (0 : LatticePoint d) = (0 : Fin d → ℝ) := by
    funext i
    simp [realVector]
  rw [hz, map_zero, abs_zero]
  exact mul_pos ht (coefficientMass_pos f hf)

/-- **Narrow-slab John/CFP bridge.**

Assume the selected enhanced CFP witness has full ambient rank and its core
lies in a positive centered functional slab.  PZ Lemma 7 produces a John
certificate.  Either that certificate has smaller rank, or the CFP
progression satisfies the displayed explicit volume bound.  No selector
minimality or additional structural proposition is assumed here. -/
theorem exists_rankDrop_or_cfpProgressionVolume_le_of_core_functionalSlab
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (hd : 0 < d) (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hB : ConvexDensity.IsConvexBody (boxRealization B))
    (hf : f ≠ 0) (ht : 0 < t)
    (hzeroB : (0 : LatticePoint d) ∈ B.carrier)
    (hcoreB : W.core ⊆ B.carrier)
    (hcoreSlab : ∀ x ∈ W.core,
      |f (realVector x)| < t * coefficientMass f)
    (hWrank : W.rank = d)
    (hlarge : 1 ≤
      (2 * (d : ℝ) * t) * (B.carrier.card : ℝ)) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∃ J : CenteredDiscreteJohnCertificate B
          (functionalSlabInBox B f t),
        J.factor ≤ factorBound ∧
        (J.certificate.outer.volume : ℝ) ≤
          constant * (B.carrier.card : ℝ) ∧
        (J.rank < d ∨
          (W.progression.volume : ℝ) ≤
            (2 : ℝ) ^ d * (2 * W.scaleDen) ^ d *
              ((3 : ℝ) ^ d *
                (constant *
                  ((2 * (d : ℝ) * t) * (B.carrier.card : ℝ))))) := by
  let eta : ℝ := 2 * (d : ℝ) * t
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have hcore : W.core ⊆
      boxLatticePointsIn B (functionalSlabInBox B f t) := by
    intro x hx
    exact mem_boxLatticePointsIn_functionalSlabInBox B f t
      (hcoreB hx) (hcoreSlab x hx)
  have hzero : (0 : LatticePoint d) ∈
      boxLatticePointsIn B (functionalSlabInBox B f t) :=
    zero_mem_boxLatticePointsIn_functionalSlabInBox B f t hf ht hzeroB
  have hnonempty :
      (boxLatticePointsIn B (functionalSlabInBox B f t)).Nonempty :=
    ⟨0, hzero⟩
  have hrelative :
      ConvexDensity.relativeVolume (functionalSlabInBox B f t)
          (boxRealization B) ≤ ENNReal.ofReal eta := by
    dsimp only [eta]
    exact relativeVolume_functionalSlabInBox_le_dimension
      hd B f t hB ht.le hf
  obtain ⟨factorBound, constant, hconstant, hPZ⟩ :=
    pzLemmaSeven d hd
  obtain ⟨J, hfactor, hcoarse, hbranch⟩ :=
    hPZ B (functionalSlabInBox B f t) eta hB heta
      (convex_functionalSlabInBox B f t)
      (functionalSlabInBox_subset B f t) hnonempty hrelative hlarge
  refine ⟨factorBound, constant, hconstant, J, hfactor, hcoarse, ?_⟩
  rcases hbranch with hrankDrop | ⟨hrank, hthin⟩
  · exact Or.inl hrankDrop
  · right
    have hJrank : J.rank ≤ W.rank := by
      rw [hWrank]
      exact J.rank_le
    have hcomparison :=
      cfpWitness_dimensionIncrease_centeredDiscreteJohn_real
        W J hcore hzero hJrank
    have hcomparison' : (W.progression.volume : ℝ) ≤
        (2 : ℝ) ^ d * (2 * W.scaleDen) ^ d *
          ((3 : ℝ) ^ d * (J.certificate.outer.volume : ℝ)) := by
      simpa only [hWrank, hrank, Nat.sub_self, pow_zero, one_mul] using
        hcomparison
    have hthin' : (J.certificate.outer.volume : ℝ) ≤
        constant * (eta * (B.carrier.card : ℝ)) := by
      simpa only [hrank, mul_assoc] using hthin
    calc
      (W.progression.volume : ℝ) ≤
          (2 : ℝ) ^ d * (2 * W.scaleDen) ^ d *
            ((3 : ℝ) ^ d * (J.certificate.outer.volume : ℝ)) :=
        hcomparison'
      _ ≤ (2 : ℝ) ^ d * (2 * W.scaleDen) ^ d *
          ((3 : ℝ) ^ d *
            (constant * (eta * (B.carrier.card : ℝ)))) := by
        gcongr

/-- Constants for the completed functional-slab contradiction.  This is the
direct source-facing specialization of `exists_slabJohnContradictionConstants`:
all geometric hypotheses about the thin region are discharged by
`functionalSlabInBox` and its relative-volume theorem above. -/
theorem exists_functionalSlabContradictionConstants
    (d : ℕ) (hd : 0 < d) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {s D k loss referenceVolume boxFactor : ℕ}
        {A : Finset (LatticePoint d)}
        (W : CFP.EnhancedCFPWitness A s D k loss)
        (B : IntegerBox d)
        (f : (Fin d → ℝ) →L[ℝ] ℝ) (t gamma : ℝ),
        W.rank = d →
        ConvexDensity.IsConvexBody (boxRealization B) →
        f ≠ 0 → 0 < t →
        (0 : LatticePoint d) ∈ B.carrier →
        W.core ⊆ B.carrier →
        (∀ x ∈ W.core,
          |f (realVector x)| < t * coefficientMass f) →
        1 ≤ (2 * (d : ℝ) * t) * (B.carrier.card : ℝ) →
        B.carrier.card ≤ boxFactor * referenceVolume →
        0 < referenceVolume → 0 < gamma →
        gamma * (referenceVolume : ℝ) ≤
          (W.progression.volume : ℝ) →
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * boxFactor < (k : ℝ) * gamma →
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * (2 * (d : ℝ) * t) * boxFactor < gamma →
        False := by
  obtain ⟨factorBound, constant, hconstant, hcontradiction⟩ :=
    exists_slabJohnContradictionConstants pzLemmaSeven d hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro s D k loss referenceVolume boxFactor A W B f t gamma hWrank hB hf ht
    hzeroB hcoreB hcoreSlab hscale hbox hrefPos hgamma hlower
    hlowHierarchy hfullHierarchy
  have hcore : W.core ⊆
      boxLatticePointsIn B (functionalSlabInBox B f t) := by
    intro x hx
    exact mem_boxLatticePointsIn_functionalSlabInBox B f t
      (hcoreB hx) (hcoreSlab x hx)
  have hzero : (0 : LatticePoint d) ∈
      boxLatticePointsIn B (functionalSlabInBox B f t) :=
    zero_mem_boxLatticePointsIn_functionalSlabInBox B f t hf ht hzeroB
  have hnonempty :
      (boxLatticePointsIn B (functionalSlabInBox B f t)).Nonempty :=
    ⟨0, hzero⟩
  apply hcontradiction W hWrank B (functionalSlabInBox B f t)
    (2 * (d : ℝ) * t) gamma hB
  · positivity
  · exact convex_functionalSlabInBox B f t
  · exact functionalSlabInBox_subset B f t
  · exact hnonempty
  · exact relativeVolume_functionalSlabInBox_le_dimension
      hd B f t hB ht.le hf
  · exact hscale
  · exact hcore
  · exact hzero
  · exact hbox
  · exact hrefPos
  · exact hgamma
  · exact hlower
  · exact hlowHierarchy
  · exact hfullHierarchy

end

end Erdos186.PZ.Intersection
