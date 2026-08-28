import Wikipedia.NoExoticSixSphere.OpenHomotopyExtension
import Wikipedia.NoExoticSixSphere.RealIntervalProgress
import Mathlib.Tactic.Linarith

/-!
# An upper energy cutoff for a sublevel homotopy

A homotopy below one energy ceiling can be extended to the whole space,
unchanged at sufficiently high energies. It still performs the full lowering
on a smaller sublevel and preserves any already-fixed lower sublevel.
-/

open Set unitInterval

namespace NoExoticSixSphere.UpperEnergyHomotopyCutoff

open RealIntervalProgress

variable {X : Type*} [TopologicalSpace X]

noncomputable def weight (f : C(X, ℝ)) (u v : ℝ) : C(X, ℝ) :=
  ⟨fun x ↦ 1 - progress u v (f x),
    continuous_const.sub ((continuous_progress u v).comp f.continuous)⟩

theorem weight_bounds (f : C(X, ℝ)) (u v : ℝ) (x : X) : weight f u v x ∈ I := by
  have hh : progress u v (f x) ∈ Icc (0 : ℝ) 1 :=
    (projIcc (0 : ℝ) 1 zero_le_one ((f x - u) / (v - u))).2
  change 0 ≤ 1 - progress u v (f x) ∧ 1 - progress u v (f x) ≤ 1
  constructor <;> linarith [hh.1, hh.2]

theorem weight_below (f : C(X, ℝ)) (u v : ℝ) (huv : u ≤ v) {x : X} (hx : f x ≤ u) :
    weight f u v x = 1 := by
  change 1 - progress u v (f x) = 1
  rw [progress_before huv hx, sub_zero]

theorem weight_above (f : C(X, ℝ)) (u v : ℝ) (huv : u < v) {x : X} (hx : v ≤ f x) :
    weight f u v x = 0 := by
  change 1 - progress u v (f x) = 0
  rw [progress_after huv hx, sub_self]

theorem tsupport_weight_subset (f : C(X, ℝ)) (u v E : ℝ) (huv : u < v) (hvE : v < E) :
    tsupport (weight f u v) ⊆ {x | f x < E} := by
  have hclosed : IsClosed {x | f x ≤ v} := isClosed_Iic.preimage f.continuous
  have hsub : tsupport (weight f u v) ⊆ {x | f x ≤ v} := by
    apply closure_minimal _ hclosed
    intro x hx
    by_contra h
    exact hx (weight_above f u v huv (le_of_not_ge h))
  exact fun x hx ↦ (hsub hx).trans_lt hvE

theorem exists_extension (f : C(X, ℝ)) (l k u v E : ℝ) (huv : u < v) (hvE : v < E)
    (H : C(I × {x | f x < E}, X)) (hzero : ∀ x : {x | f x < E}, H (0, x) = x.1)
    (hfixed : ∀ (t : I) (x : {x | f x < E}), f x.1 ≤ l → H (t, x) = x.1)
    (hle : ∀ (t : I) (x : {x | f x < E}), f (H (t, x)) ≤ f x.1)
    (hlow : ∀ x : {x | f x < E}, f (H (1, x)) ≤ k) :
    ∃ F : C(X, X), ∃ G : ContinuousMap.HomotopyRel (ContinuousMap.id X) F
      {x | f x ≤ l ∨ v ≤ f x},
      (∀ t x, f (G (t, x)) ≤ f x) ∧ ∀ x, f x ≤ u → f (F x) ≤ k := by
  let β := weight f u v
  have hβ : ∀ x, β x ∈ I := weight_bounds f u v
  have hA : IsOpen {x | f x < E} := isOpen_Iio.preimage f.continuous
  have hsupport : tsupport β ⊆ {x | f x < E} := tsupport_weight_subset f u v E huv hvE
  let G₀ := OpenHomotopyExtension.homotopy H β hβ hzero hA hsupport {x | f x ≤ l} hfixed
  let F := OpenHomotopyExtension.endpoint H β hβ hzero hA hsupport
  let G : ContinuousMap.HomotopyRel (ContinuousMap.id X) F {x | f x ≤ l ∨ v ≤ f x} :=
    { toHomotopy := G₀.toHomotopy
      prop' := fun t x hx ↦ G₀.eq_fst t (hx.elim Or.inl
        (fun hh ↦ Or.inr (weight_above f u v huv hh))) }
  refine ⟨F, G, fun t x ↦ ?_, fun x hx ↦ ?_⟩
  · change f (OpenHomotopyExtension.raw H β hβ (t, x)) ≤ f x
    by_cases hx : f x < E
    · rw [OpenHomotopyExtension.raw_of_mem H β hβ hx]
      exact hle _ _
    · rw [OpenHomotopyExtension.raw_of_notMem H β hβ hx]
  · have hxE : f x < E := hx.trans_lt (huv.trans hvE)
    change f (OpenHomotopyExtension.raw H β hβ (1, x)) ≤ k
    rw [OpenHomotopyExtension.raw_of_mem H β hβ hxE,
      CutoffHomotopyGluing.clock_one_of_one β hβ (weight_below f u v huv.le hx)]
    exact hlow _

end NoExoticSixSphere.UpperEnergyHomotopyCutoff
