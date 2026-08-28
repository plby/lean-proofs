import Wikipedia.HopfProblem.OrbitPairHomotopyFiberLoopInclusion
import Wikipedia.HopfProblem.OrbitPairHomotopyLoopMap

/-!
# Images of source loops contract in the actual homotopy fibre

Move the source point along the loop, retaining the image of its remaining
tail as the fibre path. This contracts the image loop exactly to the fibre
basepoint and fixes all parameters whose source loop was constant.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def tailTime (s t : unitInterval) : unitInterval :=
  unitInterval.symm (unitInterval.symm s * unitInterval.symm t)

theorem continuous_tailTime : Continuous (fun z : unitInterval × unitInterval ↦
    tailTime z.1 z.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : unitInterval × unitInterval ↦
    1 - (1 - (z.1 : ℝ)) * (1 - (z.2 : ℝ)))
  exact continuous_const.sub
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)))

theorem tailTime_start (s : unitInterval) : tailTime s 0 = s := by simp [tailTime]

theorem tailTime_end (s : unitInterval) : tailTime s 1 = 1 := by simp [tailTime]

theorem tailTime_zero (t : unitInterval) : tailTime 0 t = t := by simp [tailTime]

theorem tailTime_one (t : unitInterval) : tailTime 1 t = 1 := by simp [tailTime]

def mappedLoopContraction (f : C(X, Y)) (x : X) (P : C(Z, Path x x)) :
    C(unitInterval × Z, Space f (f x)) := by
  let F : C(unitInterval × (unitInterval × Z), Y) := {
    toFun z := f (P z.2.2 (tailTime z.2.1 z.1))
    continuous_toFun := f.continuous.comp (continuous_eval.comp
      ((P.continuous.comp (continuous_snd.comp continuous_snd)).prodMk
        (continuous_tailTime.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst)))) }
  let paths : C(unitInterval × Z, C(unitInterval, Y)) :=
    (F.comp ⟨Prod.swap, continuous_swap⟩).curry
  exact {
    toFun z := ⟨(P z.2 z.1, paths z), by
      change f (P z.2 (tailTime z.1 0)) = f (P z.2 z.1)
      rw [tailTime_start], by
      change f (P z.2 (tailTime z.1 1)) = f x
      rw [tailTime_end, Path.target]⟩
    continuous_toFun := ((continuous_eval.comp
      ((P.continuous.comp continuous_snd).prodMk continuous_fst)).prodMk
        paths.continuous).subtype_mk _ }

theorem mappedLoopContraction_initial (f : C(X, Y)) (x : X) (P : C(Z, Path x x)) (z : Z) :
    mappedLoopContraction f x P (0, z) = loopInclusion f x (loopMap f x (P z)) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (P z).source
  · apply ContinuousMap.ext
    intro t
    change f (P z (tailTime 0 t)) = f (P z t)
    rw [tailTime_zero]

theorem mappedLoopContraction_final (f : C(X, Y)) (x : X) (P : C(Z, Path x x)) (z : Z) :
    mappedLoopContraction f x P (1, z) = basepoint f x := by
  apply Subtype.ext
  apply Prod.ext
  · exact (P z).target
  · apply ContinuousMap.ext
    intro t
    change f (P z (tailTime 1 t)) = f x
    rw [tailTime_one, Path.target]

theorem mappedLoopContraction_fixed (f : C(X, Y)) (x : X) (P : C(Z, Path x x))
    (z : Z) (hz : P z = Path.refl x) (s : unitInterval) :
    mappedLoopContraction f x P (s, z) = basepoint f x := by
  apply Subtype.ext
  apply Prod.ext
  · change P z s = x
    rw [hz]
    rfl
  · apply ContinuousMap.ext
    intro t
    change f (P z (tailTime s t)) = f x
    rw [hz]
    rfl

def mappedLoopNullhomotopy (f : C(X, Y)) (x : X) (P : C(Z, Path x x))
    (S : Set Z) (hP : ∀ z ∈ S, P z = Path.refl x) :
    ((loopInclusion f x).comp ((loopMap f x).comp P)).HomotopyRel
      (ContinuousMap.const _ (basepoint f x)) S where
  toContinuousMap := mappedLoopContraction f x P
  map_zero_left := mappedLoopContraction_initial f x P
  map_one_left := mappedLoopContraction_final f x P
  prop' s z hz := by
    change mappedLoopContraction f x P (s, z) = loopInclusion f x (loopMap f x (P z))
    rw [mappedLoopContraction_fixed f x P z (hP z hz) s, hP z hz,
      loopMap_base, loopInclusion_base]

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
