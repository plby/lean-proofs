import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic.Linarith

/-!+# The contractible space of paths with a fixed terminal point

The topology is the actual compact-open subspace topology. Evaluation at
zero is the projection, and its fibers are homeomorphic to native path
spaces. Moving the initial time to one gives an explicit contraction.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.EndingPath

variable {Y : Type*} [TopologicalSpace Y] (y₀ : Y)

abbrev Space := {p : C(I, Y) // p 1 = y₀}

def constant : Space y₀ := ⟨ContinuousMap.const I y₀, rfl⟩

def source : C(Space y₀, Y) :=
  ⟨fun p ↦ p.val 0, continuous_eval.comp (continuous_subtype_val.prodMk continuous_const)⟩

variable {y₀}

def toPath (p : Space y₀) : Path (source y₀ p) y₀ where
  toContinuousMap := p.val
  source' := rfl
  target' := p.property

def ofPath {x : Y} (p : Path x y₀) : Space y₀ := ⟨p.toContinuousMap, p.target⟩

theorem ofPath_toPath (p : Space y₀) : ofPath (toPath p) = p := rfl

theorem continuous_ofPath {x : Y} : Continuous (ofPath : Path x y₀ → Space y₀) :=
  continuous_induced_dom.subtype_mk _

def fiberHomeomorph (x : Y) : {p : Space y₀ // source y₀ p = x} ≃ₜ Path x y₀ where
  toFun p := { toContinuousMap := p.val.val, source' := p.property, target' := p.val.property }
  invFun p := ⟨ofPath p, p.source⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := continuous_ofPath.subtype_mk _

def remainingTime (s t : I) : I :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ),
    add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) t.property.1) s.property.1,
    by nlinarith [s.property.2, t.property.2,
      mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr t.property.2)]⟩

theorem continuous_remainingTime : Continuous (fun p : I × I ↦ remainingTime p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

theorem remainingTime_zero (t : I) : remainingTime 0 t = t := by
  apply Subtype.ext
  simp [remainingTime]

theorem remainingTime_one (t : I) : remainingTime 1 t = 1 := by
  apply Subtype.ext
  simp [remainingTime]

theorem remainingTime_right_one (s : I) : remainingTime s 1 = 1 := by
  apply Subtype.ext
  simp [remainingTime]

def shorten (s : I) (p : Space y₀) : Space y₀ :=
  ⟨⟨fun t ↦ p.val (remainingTime s t),
    p.val.continuous.comp
      (continuous_remainingTime.comp (continuous_const.prodMk continuous_id))⟩,
    by
      change p.val (remainingTime s 1) = y₀
      rw [remainingTime_right_one, p.property]⟩

theorem continuous_shorten : Continuous (fun u : I × Space y₀ ↦ shorten u.1 u.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (I × Space y₀) × I ↦ p.1.2.val (remainingTime p.1.1 p.2))
  exact continuous_eval.comp
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
      (continuous_remainingTime.comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))

theorem shorten_zero (p : Space y₀) : shorten 0 p = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact congrArg p.val (remainingTime_zero t)

theorem shorten_one (p : Space y₀) : shorten 1 p = constant y₀ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change p.val (remainingTime 1 t) = y₀
  rw [remainingTime_one, p.property]

theorem shorten_constant (s : I) : shorten s (constant y₀) = constant y₀ := rfl

def contraction : (ContinuousMap.id (Space y₀)).Homotopy
    (ContinuousMap.const (Space y₀) (constant y₀)) where
  toFun u := shorten u.1 u.2
  continuous_toFun := continuous_shorten
  map_zero_left := shorten_zero
  map_one_left := shorten_one

instance : ContractibleSpace (Space y₀) :=
  (contractible_iff_id_nullhomotopic (Space y₀)).mpr ⟨constant y₀, ⟨contraction⟩⟩

end NoExoticSixSphere.EndingPath
