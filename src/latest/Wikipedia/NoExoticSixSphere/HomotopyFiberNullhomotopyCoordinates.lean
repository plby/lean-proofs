import Wikipedia.NoExoticSixSphere.HomotopyFiberHomotopyInvariance
import Mathlib.Topology.Homotopy.Path

/-!
# The literal inverse map of the nullhomotopy-fiber equivalence

The inverse follows the specified nullhomotopy from the source point to
the terminal point, then follows the supplied loop. This identifies the
constructed homotopy equivalence with the actual path concatenation map.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberHomotopyInvariance

open HomotopyFiber

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem mapCongr_val {f g : C(X, Y)} (h : f = g) (b : Y) (p : Space f b) :
    (mapCongr h b p).val = p.val := by
  subst g
  rfl

theorem mapCongr_symm_val {f g : C(X, Y)} (h : f = g) (b : Y) (p : Space g b) :
    ((mapCongr h b).symm p).val = p.val := by
  subst g
  rfl

theorem reversedSliceTime (t : I) :
    Set.Icc.convexComb (1 : I) 0 (reverseTime 1 t) =
      Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) := by
  have hc (s : I) : Set.Icc.convexComb (1 : I) 0 s = unitInterval.symm s := by
    apply Subtype.ext
    simp [Set.Icc.convexComb, unitInterval.symm]
  rw [hc, reverseTime, unitInterval.symm_projIcc]
  congr 1
  change (1 : ℝ) - (1 - 2 * (t : ℝ)) = 2 * (t : ℝ)
  ring

theorem remainingSliceTime (t : I) :
    remainingTime 1 t = Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) := by
  change Set.projIcc 0 1 zero_le_one ((2 * (t : ℝ) - 1) / ((2 : ℝ) - 1)) = _
  norm_num

theorem equivalence_symm_source {f g : C(X, Y)} (H : f.Homotopy g) (b : Y)
    (p : Space g b) : ((equivalence H b).symm p).val.1 = p.val.1 := by
  change ((mapCongr (zero_map H).symm b).symm
    ((sliceFiberEquiv H.toContinuousMap b 0).symm
      (sliceFiberEquiv H.toContinuousMap b 1 ((mapCongr (one_map H) b).symm p)))).val.1 = _
  rw [mapCongr_symm_val]
  change ((mapCongr (one_map H) b).symm p).val.1 = p.val.1
  rw [mapCongr_symm_val]

theorem equivalence_symm_path {f g : C(X, Y)} (H : f.Homotopy g) (b : Y)
    (p : Space g b) (t : I) :
    ((equivalence H b).symm p).val.2 t =
      ((H.evalAt p.val.1).trans
        { toContinuousMap := p.val.2, source' := p.property.1, target' := p.property.2 }) t := by
  change ((mapCongr (zero_map H).symm b).symm
    ((sliceFiberEquiv H.toContinuousMap b 0).symm
      (sliceFiberEquiv H.toContinuousMap b 1 ((mapCongr (one_map H) b).symm p)))).val.2 t = _
  rw [mapCongr_symm_val]
  change (if 2 * (t : ℝ) ≤ 1 then
    H (Set.Icc.convexComb 1 0 (reverseTime 1 t),
      ((mapCongr (one_map H) b).symm p).val.1)
    else ((mapCongr (one_map H) b).symm p).val.2 (remainingTime 1 t)) = _
  rw [mapCongr_symm_val, reversedSliceTime, remainingSliceTime]
  change (if 2 * (t : ℝ) ≤ 1 then H (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), p.val.1)
    else p.val.2 (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))) =
    (if (t : ℝ) ≤ 1 / 2 then H (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), p.val.1)
    else p.val.2 (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)))
  have he : 2 * (t : ℝ) ≤ 1 ↔ (t : ℝ) ≤ 1 / 2 := by constructor <;> intro h <;> linarith
  simp only [he]

theorem nullhomotopyEquiv_symm_source (f : C(X, Y)) (b : Y)
    (H : f.Homotopy (ContinuousMap.const X b)) (x : X) (p : Path b b) :
    ((nullhomotopyEquiv f b H).symm (x, p)).val.1 = x :=
  equivalence_symm_source H b ((constantFiberHomeomorph X b).symm (x, p))

theorem nullhomotopyEquiv_symm_path (f : C(X, Y)) (b : Y)
    (H : f.Homotopy (ContinuousMap.const X b)) (x : X) (p : Path b b) (t : I) :
    ((nullhomotopyEquiv f b H).symm (x, p)).val.2 t = ((H.evalAt x).trans p) t :=
  equivalence_symm_path H b ((constantFiberHomeomorph X b).symm (x, p)) t

end NoExoticSixSphere.HomotopyFiberHomotopyInvariance
