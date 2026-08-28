import Wikipedia.NoExoticSixSphere.EndingPathSpace
import Mathlib.Topology.Homotopy.HSpaces

/-!
# Appending a native loop to a variable-source ending path

The concatenation is jointly continuous in the actual compact-open
topology. It preserves the initial point and the fixed terminal point.
The constant-prefix operation is continuously homotopic to the identity.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.EndingPath

variable {Y : Type*} [TopologicalSpace Y] {b : Y}

def append (p : Space b) (c : Path b b) : Space b := ofPath ((toPath p).trans c)

theorem append_ofPath {x : Y} (p : Path x b) (c : Path b b) :
    append (ofPath p) c = ofPath (p.trans c) := rfl

theorem append_source (p : Space b) (c : Path b b) :
    source b (append p c) = source b p := ((toPath p).trans c).source

theorem continuous_append : Continuous (fun p : Space b × Path b b ↦ append p.1 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact Path.trans_continuous_family
    (fun p : Space b × Path b b ↦ toPath p.1)
    (continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd))
    (fun p : Space b × Path b b ↦ p.2)
    (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

theorem remainingTime_start (s : I) : remainingTime s 0 = s := by
  apply Subtype.ext
  simp [remainingTime]

theorem remainingTime_convexComb (s t : I) : remainingTime s t = Set.Icc.convexComb s 1 t := by
  apply Subtype.ext
  change (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) = (1 - (t : ℝ)) * (s : ℝ) + (t : ℝ) * 1
  ring

theorem shorten_source (s : I) (p : Space b) : source b (shorten s p) = p.val s := by
  change p.val (remainingTime s 0) = p.val s
  rw [remainingTime_start]

def constantPrefix : C(Path b b, Path b b) :=
  ⟨fun p ↦ (Path.refl b).trans p, continuous_const.path_trans continuous_id⟩

def constantPrefixHomotopy : constantPrefix.Homotopy (ContinuousMap.id (Path b b)) where
  toFun p := Path.delayReflLeft p.1 p.2
  continuous_toFun := Path.continuous_delayReflLeft
  map_zero_left := Path.delayReflLeft_zero
  map_one_left := Path.delayReflLeft_one

end NoExoticSixSphere.EndingPath
