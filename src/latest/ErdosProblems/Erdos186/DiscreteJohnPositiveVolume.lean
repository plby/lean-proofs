/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohn
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecond
import Mathlib.Data.Sign.Basic

/-!
# The positive-inner-radius volume bridge for discrete John certificates

This file isolates the determinant argument in the full-dimensional case
where every shrunken radius is positive.  The mixed-radius case additionally
requires completing the positive-radius step vectors by lattice points of the
body; that completion is developed at the PZ assembly layer, where effective
section rank is available.
-/

namespace Erdos186
namespace DiscreteJohn

open scoped BigOperators
open Module CFP.Bilu.Mahler CFP.Bilu.MinkowskiSecond

variable {d factor : ℕ}

/-- Integer independence of a square tuple of lattice vectors implies real
linear independence after the canonical embedding. -/
theorem realLinearIndependent_of_integerIndependent
    (steps : Fin d → LatticePoint d) (hsteps : IntegerIndependent steps) :
    LinearIndependent ℝ (fun i ↦ integralEmbed (steps i)) := by
  have hInt : LinearIndependent ℤ steps := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hcomb : integerCombination steps c = integerCombination steps 0 := by
      funext j
      have hj := congrFun hc j
      simpa [integerCombination] using hj
    have heq := hsteps hcomb
    exact congrFun heq i
  have hReal : LinearIndependent ℝ
      (fun i ↦ algebraMap ℤ ℝ ∘ steps i) :=
    linearIndependent_algebraMap_comp_iff.mpr hInt
  convert hReal using 1
  funext i j
  simp [integralEmbed]

/-- Any centered integral coefficient vector lying between the displayed
radii represents a point of the corresponding symmetric GAP. -/
theorem integerCombination_mem_symmetricGAP
    (steps : Fin d → LatticePoint d) (radii : Fin d → ℕ)
    (c : Fin d → ℤ)
    (hc : ∀ i, -(radii i : ℤ) ≤ c i ∧ c i ≤ (radii i : ℤ)) :
    integerCombination steps c ∈ (symmetricGAP steps radii).carrier := by
  let n : (symmetricGAP steps radii).Coord := fun i ↦
    ⟨(c i + (radii i : ℤ)).toNat, by
      have hi := hc i
      have hnonneg : 0 ≤ c i + (radii i : ℤ) := by omega
      change (c i + (radii i : ℤ)).toNat < 2 * radii i + 1
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 (by omega)⟩
  apply GAP.mem_carrier_iff.mpr
  refine ⟨n, ?_⟩
  rw [symmetricGAP_coordPoint]
  congr 1
  funext i
  have hi := hc i
  have hnonneg : 0 ≤ c i + (radii i : ℤ) := by omega
  change (((c i + (radii i : ℤ)).toNat : ℕ) : ℤ) -
      (radii i : ℤ) = c i
  rw [Int.toNat_of_nonneg hnonneg]
  ring

/-- A positive shrunken coordinate step belongs to the body whenever the
certificate's inner GAP is contained in the exact lattice section. -/
theorem shrunkenStep_mem_body
    {points : Finset (LatticePoint d)} {K : Set (Fin d → ℝ)}
    (C : Certificate points d factor)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K) (i : Fin d) :
    ((C.radii i / factor : ℕ) : ℝ) • integralEmbed (C.steps i) ∈ K := by
  let q : ℕ := C.radii i / factor
  let c : Fin d → ℤ := Pi.single i (q : ℤ)
  have hc : ∀ j, -((shrinkRadii factor C.radii j : ℕ) : ℤ) ≤ c j ∧
      c j ≤ ((shrinkRadii factor C.radii j : ℕ) : ℤ) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [c, Pi.single_eq_same]
      rw [show shrinkRadii factor C.radii i = q by rfl]
      have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
      exact ⟨(neg_nonpos.mpr hq).trans hq, le_rfl⟩
    · have hij : i ≠ j := Ne.symm hji
      simp only [c, Pi.single_apply, hij, if_false]
      omega
  have hinner : integerCombination C.steps c ∈ C.inner.carrier := by
    exact integerCombination_mem_symmetricGAP C.steps
      (shrinkRadii factor C.radii) c hc
  have hbody := (hpoints _).mp (C.inner_carrier_subset hinner)
  have hembed : integralEmbed (integerCombination C.steps c) =
      ((q : ℕ) : ℝ) • integralEmbed (C.steps i) := by
    rw [integralEmbed_integerCombination]
    classical
    rw [Finset.sum_eq_single i]
    · simp [c]
    · intro j _hj hji
      simp [c, Ne.symm hji]
    · simp
  rwa [hembed] at hbody

/-- An integral crosspolytope whose scaled generators lie in a balanced
convex set is contained in that set.  This formulation is also used after
completing the positive-radius steps by full-span lattice points. -/
theorem scaledCrosspolytope_subset_balancedConvex
    {K : Set (Fin d → ℝ)} (a : Fin d → ℝ)
    (v : Fin d → LatticePoint d)
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hgen : ∀ i, a i • integralEmbed (v i) ∈ K) (hd : 0 < d) :
    (Matrix.toLin' (scaledRealColumns a v)) '' l1UnitBall d ⊆ K := by
  have hnonempty : K.Nonempty :=
    ⟨a ⟨0, hd⟩ • integralEmbed (v ⟨0, hd⟩), hgen ⟨0, hd⟩⟩
  have hzero : (0 : Fin d → ℝ) ∈ K := hbalanced.zero_mem hnonempty
  rintro _ ⟨x, hx, rfl⟩
  rw [Matrix.toLin'_apply, mulVec_scaledRealColumns]
  have hxsum : ∑ i, |x i| ≤ 1 := by
    simpa [l1UnitBall] using hx
  let w : Fin (d + 1) → ℝ :=
    Fin.cons (1 - ∑ i, |x i|) (fun i ↦ |x i|)
  let z : Fin (d + 1) → (Fin d → ℝ) :=
    Fin.cons 0
      (fun i ↦ (SignType.sign (x i) : ℝ) •
        (a i • integralEmbed (v i)))
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [w] using sub_nonneg.mpr hxsum
    · simp [w]
  have hw1 : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
  have hz : ∀ i, z i ∈ K := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [z] using hzero
    · apply hbalanced.smul_mem _ (hgen j)
      cases hsign : SignType.sign (x j) <;> simp
  have hsum := hconvex.sum_mem (t := Finset.univ) (w := w) (z := z)
    (fun i _ ↦ hw0 i) (by simpa using hw1) (fun i _ ↦ hz i)
  simpa [w, z, Fin.sum_univ_succ, scaledCombination, smul_smul,
    mul_assoc, mul_comm, mul_left_comm] using hsum

/-- The scaled crosspolytope generated by the shrunken steps lies in every
balanced convex body containing those steps. -/
theorem shrunkenCrosspolytope_subset_body
    {points : Finset (LatticePoint d)} {K : Set (Fin d → ℝ)}
    (C : Certificate points d factor)
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hd : 0 < d) :
    (Matrix.toLin' (scaledRealColumns
      (fun i ↦ ((C.radii i / factor : ℕ) : ℝ)) C.steps)) '' l1UnitBall d ⊆ K := by
  let a : Fin d → ℝ :=
    fun i ↦ ((C.radii i / factor : ℕ) : ℝ)
  have hgen (i : Fin d) : a i • integralEmbed (C.steps i) ∈ K := by
    exact shrunkenStep_mem_body C hpoints i
  exact scaledCrosspolytope_subset_balancedConvex a C.steps
    hbalanced hconvex hgen hd

/-- With every shrunken radius positive, the continuous body volume controls
their product by the integral determinant of the square step family. -/
theorem shrunkenRadii_product_volume_le
    {points : Finset (LatticePoint d)} {K : Set (Fin d → ℝ)}
    (C : Certificate points d factor)
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hd : 0 < d) :
    ENNReal.ofReal (∏ i, ((C.radii i / factor : ℕ) : ℝ)) *
        ENNReal.ofReal ((2 : ℝ) ^ d / (d.factorial : ℝ)) ≤
      MeasureTheory.volume K := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let a : Fin d → ℝ :=
    fun i ↦ ((C.radii i / factor : ℕ) : ℝ)
  have hLI := realLinearIndependent_of_integerIndependent C.steps C.independent
  have hlower := volume_image_l1UnitBall_scaledRealColumns_lower a C.steps hLI
  simpa [a] using hlower.trans (MeasureTheory.measure_mono
    (shrunkenCrosspolytope_subset_body C hbalanced hconvex hpoints hd))

end DiscreteJohn
end Erdos186
