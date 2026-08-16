import ErdosProblems.Erdos6.LargeFiberPointwise
import ErdosProblems.Erdos6.GenericOuterCollision
import BoundedGaps.Maynard.MaynardS2OuterTupleFactorization
import BoundedGaps.Maynard.MaynardS2GPositivity

/-!
# The generic coordinate-fiber square diagonal
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

def tupleCoordinateFiberSquareDiagonal
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) (m : H) : ℝ :=
  ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)).filter (fun r => r m = 1),
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N)
        (BoundedGaps.Maynard.maynardYValue H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N)
          (tupleLargeCandidate H)) m r ^ 2 /
      ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)

theorem tupleOffFaceExtension_outerProfile_sq
    {H : Finset ℕ} {R W : ℕ} (m : H)
    (u : tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R W) (hR : 1 < R) :
    tupleCoordinateOuterProfile R m (tupleOffFaceExtension m u) ^ 2 =
      largeOuterContinuousDensity
        (fun h : tupleOffFace H m => Real.log (u h) / Real.log R) := by
  have hbox :=
    (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu).mem_maynardDivisorTupleBox
  have hcoord : ∀ h : tupleOffFace H m,
      0 ≤ Real.log (u h) / Real.log R := fun h =>
    (BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR hbox h).1
  have hprod : tupleCoordinateOuterProfile R m
      (tupleOffFaceExtension m u) =
      ∏ h : tupleOffFace H m,
        largeFiberProfile (Real.log (u h) / Real.log R) := by
    unfold tupleCoordinateOuterProfile
    rw [prod_subtype_erase_eq_offFace]
    apply Finset.prod_congr rfl
    intro h hh
    have hhmem : h.1 ∈ H.erase m.1 := by
      simpa [tupleOffFace] using h.2
    let hfull : H := ⟨h.1, (Finset.mem_erase.mp hhmem).2⟩
    have hne : hfull ≠ m := by
      intro heq
      exact (Finset.mem_erase.mp hhmem).1
        (by simpa [hfull] using congrArg (fun z : H => z.1) heq)
    have hext : tupleOffFaceExtension m u hfull = u h := by
      rw [tupleOffFaceExtension_off m u hfull hne]
    simpa [hfull, tupleOffFace] using congrArg
      (fun n : ℕ => largeFiberProfile (Real.log n / Real.log R)) hext
  rw [hprod]
  unfold largeOuterContinuousDensity
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro h hh
  rw [largeFiberProfile_eq_largeG (hcoord h),
    largeContinuousG_eq_largeG
      (mul_nonneg (Nat.cast_nonneg largeK) (hcoord h))]

theorem tupleOffFaceExtension_outerWeight
    {H : Finset ℕ} {R W : ℕ} (m : H)
    (u : tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R W) :
    BoundedGaps.Maynard.maynardS2OuterSquarefreeAF W
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m
          (tupleOffFaceExtension m u)) =
      BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m) W u := by
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W
      (tupleOffFaceExtension m u) :=
    (isMaynardDivisorTuple_extension_iff R W m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  rw [BoundedGaps.Maynard.maynardS2OuterSquarefreeAF_offCoordinateProduct_eq_prod
    m (tupleOffFaceExtension m u) hr]
  unfold BoundedGaps.Maynard.outerTupleWeight
  rw [prod_subtype_erase_eq_offFace]
  apply Finset.prod_congr rfl
  intro h hh
  have hhmem : h.1 ∈ H.erase m.1 := by
    simpa [tupleOffFace] using h.2
  let hfull : H := ⟨h.1, (Finset.mem_erase.mp hhmem).2⟩
  have hne : hfull ≠ m := by
    intro heq
    exact (Finset.mem_erase.mp hhmem).1
      (by simpa [hfull] using congrArg (fun z : H => z.1) heq)
  have hext : tupleOffFaceExtension m u hfull = u h := by
    rw [tupleOffFaceExtension_off m u hfull hne]
  simpa [hfull, tupleOffFace] using congrArg
    (BoundedGaps.Maynard.maynardS2OuterSquarefreeAF W) hext

theorem tupleFiberArithmeticScale_eq_outer
    {H : Finset ℕ} {D R : ℕ} (m : H)
    (u : tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (tupleOffFace H m) R (primorial D)) (hR : 1 < R) :
    let r := tupleOffFaceExtension m u
    let O := tupleCoordinateOuterProfile R m r
    let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
    let L := Real.log R
    (O * S * L) ^ 2 /
        ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) =
      BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight (tupleOffFace H m)
          (primorial D) u *
        largeOuterContinuousDensity
          (fun h : tupleOffFace H m => Real.log (u h) / Real.log R)) := by
  dsimp only
  let r := tupleOffFaceExtension m u
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R (primorial D) r :=
    (isMaynardDivisorTuple_extension_iff R (primorial D) m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  have hrm : r m = 1 := tupleOffFaceExtension_at m u
  have hseries :=
    BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
      m r hr hrm
  have houter := tupleOffFaceExtension_outerWeight m u hu
  have hdensity := tupleOffFaceExtension_outerProfile_sq m u hu hR
  rw [show (tupleCoordinateOuterProfile R m r *
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
      Real.log R) ^ 2 /
      ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) =
      tupleCoordinateOuterProfile R m r ^ 2 * Real.log R ^ 2 *
        (BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r ^ 2 /
          ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)) by ring]
  rw [hseries, houter, hdensity]
  ring

end

end Erdos6.Maynard
