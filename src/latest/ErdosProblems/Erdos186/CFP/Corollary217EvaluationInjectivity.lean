/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Corollary217FamilyTransport
import ErdosProblems.Erdos186.CFP.RandomGreedyCorollary217Density
import ErdosProblems.Erdos186.CFP.Centering

/-!
# No-carry evaluation for the Corollary 2.17 progression

The common Corollary 2.17 progression is constructed in the centered
coefficient lattice of a fixed bounding GAP.  Its geometric containment
controls pairwise coordinate differences.  Properness of the corresponding
dilate of the fixed GAP then says that evaluation by its steps has no carry.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise

noncomputable section

/-- The exact outer dilation scale needed to evaluate the `k`-dilate of a
Corollary 2.17 certificate built in the centered coefficient box at scale
`sourceScale`. -/
def corollary217NoCarryScale {d : ℕ} {Q : AxisBox d}
    {S : Finset (LatticePoint d)} (cert : Corollary217Certificate Q S)
    (sourceScale k : ℕ) : ℕ :=
  k * cert.constant * (2 * sourceScale)

/-- Properness of a coefficient GAP at scale `scale` makes evaluation by its
steps injective on any set whose pairwise coordinate differences fit inside
that scale. -/
theorem stepEvaluation_injOn_of_pairwise_difference_le
    {d scale : ℕ} (P : GAP 1 d)
    (hproper : (P.dilate scale).Proper)
    (T : Set (LatticePoint d))
    (hbound : ∀ x ∈ T, ∀ y ∈ T, ∀ i,
      |x i - y i| ≤ (scale * (P.widths i - 1) : ℕ)) :
    Set.InjOn (Preprocessing.stepEvaluation P) T := by
  intro x hx y hy heval
  let z : LatticePoint d := x - y
  let pos : (P.dilate scale).Coord := fun i ↦
    ⟨(z i).toNat, by
      simp only [GAP.dilate_widths]
      have hz := hbound x hx y hy i
      change |z i| ≤ (scale * (P.widths i - 1) : ℕ) at hz
      have hle : (z i).toNat ≤ scale * (P.widths i - 1) := by
        rw [Int.toNat_le]
        exact (le_abs_self (z i)).trans hz
      omega⟩
  let neg : (P.dilate scale).Coord := fun i ↦
    ⟨(-z i).toNat, by
      simp only [GAP.dilate_widths]
      have hz := hbound x hx y hy i
      change |z i| ≤ (scale * (P.widths i - 1) : ℕ) at hz
      have hzneg : |-z i| ≤ (scale * (P.widths i - 1) : ℕ) := by
        simpa only [abs_neg] using hz
      have hle : (-z i).toNat ≤ scale * (P.widths i - 1) := by
        rw [Int.toNat_le]
        exact (le_abs_self (-z i)).trans hzneg
      omega⟩
  have hstep : Preprocessing.stepEvaluation P z = 0 := by
    dsimp only [z]
    rw [map_sub, heval, sub_self]
  have hpoint : (P.dilate scale).coordPoint pos =
      (P.dilate scale).coordPoint neg := by
    funext j
    simp only [GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps]
    congr 1
    change (∑ i, z i * P.steps i 0) = 0 at hstep
    have hzsum : ∑ i, z i * P.steps i j = 0 := by
      simpa only [show j = 0 from Subsingleton.elim _ _] using hstep
    have hcoeff (i : Fin d) :
        (((pos i : ℕ) : ℤ) - ((neg i : ℕ) : ℤ)) = z i := by
      exact (z i).toNat_sub_toNat_neg
    have : (∑ i, ((pos i : ℕ) : ℤ) * P.steps i j) -
        ∑ i, ((neg i : ℕ) : ℤ) * P.steps i j = 0 := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← sub_mul, hcoeff]
      exact hzsum
    omega
  have hcoord := hproper hpoint
  have hz : z = 0 := by
    funext i
    change z i = 0
    have hi := congrArg Fin.val (congrFun hcoord i)
    change (z i).toNat = (-z i).toNat at hi
    have hdiff := (z i).toNat_sub_toNat_neg
    omega
  dsimp only [z] at hz
  exact sub_eq_zero.mp hz

/-- The geometric containment field of a Corollary 2.17 certificate bounds
differences of points in its base carrier by the side lengths of the
certificate's input box. -/
theorem Corollary217Certificate.abs_sub_apply_le
    {d : ℕ} {Q : AxisBox d} {S : Finset (LatticePoint d)}
    (cert : Corollary217Certificate Q S)
    {x y : LatticePoint d} (hx : x ∈ cert.progression.carrier)
    (hy : y ∈ cert.progression.carrier) (i : Fin d) :
    |x i - y i| ≤ (cert.constant * (Q.widths i - 1) : ℕ) := by
  obtain ⟨qx, hqx, hqx_eq⟩ :=
    Elementary.mem_translate_iff.mp (cert.geometric_bound hx)
  obtain ⟨qy, hqy, hqy_eq⟩ :=
    Elementary.mem_translate_iff.mp (cert.geometric_bound hy)
  have hqxi := (AxisBox.mem_carrier_iff _).mp hqx i
  have hqyi := (AxisBox.mem_carrier_iff _).mp hqy i
  simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
    zero_add] at hqxi hqyi
  have hxcoord := congrFun hqx_eq i
  have hycoord := congrFun hqy_eq i
  simp only [Pi.add_apply] at hxcoord hycoord
  rw [abs_le]
  constructor <;> push_cast <;> omega

/-- Pairwise coordinate differences in the `k`-dilate grow by at most the
factor `k`. -/
theorem Corollary217Certificate.abs_sub_apply_le_dilate
    {d k : ℕ} {Q : AxisBox d} {S : Finset (LatticePoint d)}
    (cert : Corollary217Certificate Q S)
    {x y : LatticePoint d} (hx : x ∈ (cert.progression.dilate k).carrier)
    (hy : y ∈ (cert.progression.dilate k).carrier) (i : Fin d) :
    |x i - y i| ≤ k * (cert.constant * (Q.widths i - 1) : ℕ) := by
  rw [dilate_carrier_eq_nsmul_carrier, Finset.mem_nsmul] at hx hy
  obtain ⟨xs, hxs⟩ := hx
  obtain ⟨ys, hys⟩ := hy
  have hxs' : (∑ j, (xs j : LatticePoint d)) = x := by
    simpa only [List.sum_ofFn] using hxs
  have hys' : (∑ j, (ys j : LatticePoint d)) = y := by
    simpa only [List.sum_ofFn] using hys
  calc
    |x i - y i| = |∑ j, ((xs j : LatticePoint d) i -
        (ys j : LatticePoint d) i)| := by
      rw [← hxs', ← hys']
      simp only [Finset.sum_apply, Finset.sum_sub_distrib]
    _ ≤ ∑ j, |(xs j : LatticePoint d) i -
        (ys j : LatticePoint d) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, (cert.constant * (Q.widths i - 1) : ℕ) := by
      push_cast
      apply Finset.sum_le_sum
      intro j _hj
      exact cert.abs_sub_apply_le (xs j).property (ys j).property i
    _ = k * (cert.constant * (Q.widths i - 1) : ℕ) := by simp

/-- Source-native no-carry theorem for the common Corollary 2.17
progression.  The only properness used is that of the displayed dilation of
the fixed reference GAP; the carrier bound comes from the certificate
itself. -/
theorem Corollary217Certificate.stepEvaluation_injOn_dilate
    {d sourceScale k : ℕ} {W : Finset ℤ}
    {S : Finset (LatticePoint d)}
    (P : BoundingBox.BoundingGAP W d)
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P.progression sourceScale)
      S)
    (hproper : (P.progression.dilate
      (corollary217NoCarryScale cert sourceScale k)).Proper) :
    Set.InjOn (Preprocessing.stepEvaluation P.progression)
      (cert.progression.dilate k).carrier := by
  apply stepEvaluation_injOn_of_pairwise_difference_le P.progression
    hproper (cert.progression.dilate k).carrier
  intro x hx y hy i
  have hcert := cert.abs_sub_apply_le_dilate hx hy i
  have hwidth :
      (Preprocessing.centeredCoordinateAxisBox P.progression sourceScale).widths i - 1 =
        2 * sourceScale * (P.progression.widths i - 1) := by
    simp only [Preprocessing.centeredCoordinateAxisBox, GAP.dilate_widths]
    omega
  rw [hwidth] at hcert
  calc
    |x i - y i| ≤
        (k * (cert.constant *
          (2 * sourceScale * (P.progression.widths i - 1))) : ℕ) := hcert
    _ = (corollary217NoCarryScale cert sourceScale k *
          (P.progression.widths i - 1) : ℕ) := by
      dsimp only [corollary217NoCarryScale]
      push_cast
      ring

end

end Erdos186.CFP

#print axioms Erdos186.CFP.stepEvaluation_injOn_of_pairwise_difference_le
#print axioms Erdos186.CFP.Corollary217Certificate.stepEvaluation_injOn_dilate
