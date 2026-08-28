import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval

/-!
# Extending a homotopy fixed near the nonpositive sublevel

A continuous homotopy on the positive locus of a real-valued continuous
function extends by the identity if it fixes a positive sublevel.  Joint
continuity follows from the open cover given by the positive locus and the
fixed sublevel.  The defining function need not be nonnegative.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap unitInterval

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRetraction

variable {X : Type*} [TopologicalSpace X]

/-- The literal positive locus, with its inherited topology. -/
abbrev Positive (ρ : C(X, ℝ)) := {x : X // 0 < ρ x}

/-- A literal strict sublevel, with its inherited topology. -/
abbrev Sublevel (ρ : C(X, ℝ)) (δ : ℝ) := {x : X // ρ x < δ}

/-- Extend a homotopy on the positive locus by the identity elsewhere. -/
def extensionFun (ρ : C(X, ℝ)) (H : C(I × Positive ρ, Positive ρ))
    (s : I × X) : X := by
  classical
  exact if hx : 0 < ρ s.2 then (H (s.1, ⟨s.2, hx⟩)).val else s.2

theorem extensionFun_apply_of_pos (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (s : I × X) (hs : 0 < ρ s.2) :
    extensionFun ρ H s = (H (s.1, ⟨s.2, hs⟩)).val := by
  classical
  simp only [extensionFun, dif_pos hs]

theorem extensionFun_apply_of_nonpos (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (s : I × X) (hs : ρ s.2 ≤ 0) :
    extensionFun ρ H s = s.2 := by
  classical
  simp only [extensionFun, dif_neg (not_lt_of_ge hs)]

/-- Fixing the positive part of a sublevel makes the entire sublevel fixed. -/
theorem extensionFun_apply_of_small (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : I × X) (hs : ρ s.2 < η) : extensionFun ρ H s = s.2 := by
  by_cases hp : 0 < ρ s.2
  · rw [extensionFun_apply_of_pos ρ H s hp, hfix s.1 ⟨s.2, hp⟩ hs]
  · exact extensionFun_apply_of_nonpos ρ H s (le_of_not_gt hp)

/-- On the open positive locus, the extension is the given continuous homotopy. -/
theorem extensionFun_continuousOn_positive (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) :
    ContinuousOn (extensionFun ρ H) {s : I × X | 0 < ρ s.2} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hpair : Continuous (fun s : {s : I × X // 0 < ρ s.2} =>
      (s.val.1, (⟨s.val.2, s.property⟩ : Positive ρ))) :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  exact (continuous_subtype_val.comp (H.continuous.comp hpair)).congr
    (fun s => (extensionFun_apply_of_pos ρ H s.val s.property).symm)

/-- On the fixed sublevel, the extension is the second-coordinate projection. -/
theorem extensionFun_continuousOn_small (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    ContinuousOn (extensionFun ρ H) {s : I × X | ρ s.2 < η} :=
  continuous_snd.continuousOn.congr
    (fun s hs => extensionFun_apply_of_small ρ H η hfix s hs)

/-- Joint continuity of the extension, including at the zero locus. -/
theorem extensionFun_continuous (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    Continuous (extensionFun ρ H) := by
  have hρ : Continuous (fun s : I × X => ρ s.2) := ρ.continuous.comp continuous_snd
  have hopen : IsOpen {s : I × X | 0 < ρ s.2} := isOpen_lt continuous_const hρ
  have hsmall : IsOpen {s : I × X | ρ s.2 < η} := isOpen_lt hρ continuous_const
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : 0 < ρ s.2
  · exact (extensionFun_continuousOn_positive ρ H).continuousAt (hopen.mem_nhds hs)
  · exact (extensionFun_continuousOn_small ρ H η hfix).continuousAt
      (hsmall.mem_nhds ((le_of_not_gt hs).trans_lt hη))

/-- The actual jointly continuous extension by the identity. -/
def extension (ρ : C(X, ℝ)) (H : C(I × Positive ρ, Positive ρ))
    (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x) :
    C(I × X, X) :=
  ⟨extensionFun ρ H, extensionFun_continuous ρ H η hη hfix⟩

@[simp] theorem extension_apply (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : I × X) : extension ρ H η hη hfix s = extensionFun ρ H s := rfl

theorem extension_apply_of_pos (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : I × X) (hs : 0 < ρ s.2) :
    extension ρ H η hη hfix s = (H (s.1, ⟨s.2, hs⟩)).val :=
  extensionFun_apply_of_pos ρ H s hs

theorem extension_apply_of_nonpos (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : I × X) (hs : ρ s.2 ≤ 0) : extension ρ H η hη hfix s = s.2 :=
  extensionFun_apply_of_nonpos ρ H s hs

theorem extension_apply_of_small (ρ : C(X, ℝ))
    (H : C(I × Positive ρ, Positive ρ)) (η : ℝ) (hη : 0 < η)
    (hfix : ∀ (t : I) (x : Positive ρ), ρ x.val < η → H (t, x) = x)
    (s : I × X) (hs : ρ s.2 < η) : extension ρ H η hη hfix s = s.2 :=
  extensionFun_apply_of_small ρ H η hfix s hs

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRetraction
