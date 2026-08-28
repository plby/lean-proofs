import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Pasting a controlled core map to a punctured outer map

Two continuous maps whose original domains are respectively a closed
radius sublevel and the positive-radius locus paste across a positive
shell when they agree on that shell.  The resulting map is literally the
outer map beyond the shell, including the shell itself.  This is a
continuous pasting statement, not a smooth gluing or submersion theorem.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed core and its original punctured outer map, pasted at one
positive radius.  The formula does not extend either branch outside its
given domain. -/
def radiusPasteFun (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y)) (x : X) : Y :=
  if hx : radius x ≤ r then core ⟨x, hx⟩
  else outer ⟨x, hr.trans (lt_of_not_ge hx)⟩

theorem radiusPasteFun_inner (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y))
    (x : X) (hx : radius x ≤ r) :
    radiusPasteFun radius r hr core outer x = core ⟨x, hx⟩ := by
  simp only [radiusPasteFun, dif_pos hx]

theorem radiusPasteFun_outer (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y))
    (hshell : ∀ (x : X) (hx : radius x = r),
      core ⟨x, hx.le⟩ = outer ⟨x, hr.trans_eq hx.symm⟩)
    (x : X) (hx : r ≤ radius x) :
    radiusPasteFun radius r hr core outer x = outer ⟨x, hr.trans_le hx⟩ := by
  by_cases hxr : radius x ≤ r
  · rw [radiusPasteFun_inner radius r hr core outer x hxr]
    exact hshell x (le_antisymm hxr hx)
  · simp only [radiusPasteFun, dif_neg hxr]

/-- Closed-set pasting applies to the actual branch domains. -/
theorem radiusPasteFun_continuous (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y))
    (hshell : ∀ (x : X) (hx : radius x = r),
      core ⟨x, hx.le⟩ = outer ⟨x, hr.trans_eq hx.symm⟩) :
    Continuous (radiusPasteFun radius r hr core outer) := by
  have hcore : ContinuousOn (radiusPasteFun radius r hr core outer)
      {x : X | radius x ≤ r} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact core.continuous.congr fun x =>
      (radiusPasteFun_inner radius r hr core outer x.val x.property).symm
  have houter : ContinuousOn (radiusPasteFun radius r hr core outer)
      {x : X | r ≤ radius x} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hinc : Continuous (fun x : {x : X // r ≤ radius x} =>
        (⟨x.val, hr.trans_le x.property⟩ : {x : X // 0 < radius x})) :=
      continuous_subtype_val.subtype_mk _
    exact (outer.continuous.comp hinc).congr fun x =>
      (radiusPasteFun_outer radius r hr core outer hshell x.val x.property).symm
  have hu : {x : X | radius x ≤ r} ∪ {x : X | r ≤ radius x} = univ := by
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total _ _
  have hc := hcore.union_of_isClosed houter
    (isClosed_le radius.continuous continuous_const)
    (isClosed_le continuous_const radius.continuous)
  rw [hu] at hc
  exact continuousOn_univ.mp hc

/-- The actual continuous pasted map. -/
def radiusPaste (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y))
    (hshell : ∀ (x : X) (hx : radius x = r),
      core ⟨x, hx.le⟩ = outer ⟨x, hr.trans_eq hx.symm⟩) : C(X, Y) :=
  ⟨radiusPasteFun radius r hr core outer,
    radiusPasteFun_continuous radius r hr core outer hshell⟩

@[simp] theorem radiusPaste_apply (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y))
    (hshell : ∀ (x : X) (hx : radius x = r),
      core ⟨x, hx.le⟩ = outer ⟨x, hr.trans_eq hx.symm⟩) (x : X) :
    radiusPaste radius r hr core outer hshell x =
      radiusPasteFun radius r hr core outer x := rfl

/-- A radius-preserving map that preserves both original branches also
preserves their pasted map.  No continuity of that symmetry is needed
for this pointwise identity. -/
theorem radiusPaste_invariant (radius : C(X, ℝ)) (r : ℝ) (hr : 0 < r)
    (core : C({x : X // radius x ≤ r}, Y))
    (outer : C({x : X // 0 < radius x}, Y))
    (hshell : ∀ (x : X) (hx : radius x = r),
      core ⟨x, hx.le⟩ = outer ⟨x, hr.trans_eq hx.symm⟩)
    (f : X → X) (hf : ∀ x, radius (f x) = radius x)
    (hcore : ∀ x : {x : X // radius x ≤ r},
      core ⟨f x.val, (hf x.val).trans_le x.property⟩ = core x)
    (houter : ∀ x : {x : X // 0 < radius x},
      outer ⟨f x.val, x.property.trans_eq (hf x.val).symm⟩ = outer x)
    (x : X) :
    radiusPaste radius r hr core outer hshell (f x) =
      radiusPaste radius r hr core outer hshell x := by
  change radiusPasteFun radius r hr core outer (f x) =
    radiusPasteFun radius r hr core outer x
  by_cases hx : radius x ≤ r
  · rw [radiusPasteFun_inner radius r hr core outer (f x) ((hf x).trans_le hx),
      radiusPasteFun_inner radius r hr core outer x hx]
    exact hcore ⟨x, hx⟩
  · have hxf : ¬radius (f x) ≤ r := by rwa [hf x]
    simp only [radiusPasteFun, dif_neg hx, dif_neg hxf]
    exact houter ⟨x, hr.trans (lt_of_not_ge hx)⟩

end Wikipedia.HopfProblem.CuspCoinvariantExtension
