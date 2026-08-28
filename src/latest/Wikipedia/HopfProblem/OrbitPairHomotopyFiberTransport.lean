import Wikipedia.HopfProblem.OrbitPairHomotopyFiber
import Wikipedia.HopfProblem.OrbitPairHomotopyFiberTransportTimes

/-!
# Explicit transport in the actual homotopy fibre

The moving fibre path first follows the image of the base homotopy backward,
then follows the original fibre path. The first segment shrinks to zero at
deformation time zero. Thus transport starts with the exact original point,
not just a reparameterized path.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def transportedPathValue (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (s t : unitInterval) (z : Z) : Y :=
  if 2 * (t : ℝ) ≤ (s : ℝ) then f (H (reverseTime s t, z))
  else (p z).val.2 (remainingTime s t)

theorem continuous_transportedPathValue (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f b (p z)) :
    Continuous (fun z : unitInterval × (unitInterval × Z) ↦
      transportedPathValue f b p H z.2.1 z.1 z.2.2) := by
  have hs : Continuous (fun z : unitInterval × (unitInterval × Z) ↦ z.2.1) :=
    continuous_fst.comp continuous_snd
  have ht : Continuous (fun z : unitInterval × (unitInterval × Z) ↦ z.1) := continuous_fst
  have hz : Continuous (fun z : unitInterval × (unitInterval × Z) ↦ z.2.2) :=
    continuous_snd.comp continuous_snd
  have hleft : Continuous (fun z : unitInterval × (unitInterval × Z) ↦
      f (H (reverseTime z.2.1 z.1, z.2.2))) :=
    f.continuous.comp (H.continuous.comp
      (((continuous_reverseTime.comp (hs.prodMk ht))).prodMk hz))
  have hright : Continuous (fun z : unitInterval × (unitInterval × Z) ↦
      (p z.2.2).val.2 (remainingTime z.2.1 z.1)) :=
    continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp (p.continuous.comp hz))).prodMk
        (continuous_remainingTime.comp (hs.prodMk ht)))
  apply Continuous.if_le hleft hright
    ((continuous_subtype_val.comp ht).const_mul 2) (continuous_subtype_val.comp hs)
  intro z h
  rw [reverseTime_join _ _ h, remainingTime_join _ _ h, hzero]
  exact (p z.2.2).property.1.symm

theorem transportedPathValue_source (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (s : unitInterval) (z : Z) :
    transportedPathValue f b p H s 0 z = f (H (s, z)) := by
  rw [transportedPathValue, if_pos]
  · rw [reverseTime_zero]
  · simpa using s.property.1

theorem transportedPathValue_target (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (s : unitInterval) (z : Z) :
    transportedPathValue f b p H s 1 z = b := by
  have hs : ¬ 2 * ((1 : unitInterval) : ℝ) ≤ (s : ℝ) := by
    have hs := s.property.2
    norm_num
    linarith
  rw [transportedPathValue, if_neg hs, remainingTime_one]
  exact (p z).property.2

theorem transportedPathValue_initial (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f b (p z))
    (t : unitInterval) (z : Z) :
    transportedPathValue f b p H 0 t z = (p z).val.2 t := by
  by_cases ht : t = 0
  · subst t
    rw [transportedPathValue_source, hzero]
    exact (p z).property.1.symm
  · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun he ↦ ht (Subtype.ext he.symm))
    rw [transportedPathValue, if_neg (by simpa using (by linarith : ¬ 2 * (t : ℝ) ≤ 0)),
      remainingTime_zero]

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
