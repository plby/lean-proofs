import Wikipedia.NoExoticSixSphere.NativeSphereConcatenation

/-!
# The two actual collapse projections of native sphere concatenation

Concatenating the identity with the constant map gives the left and right
collapse projections. Both are continuous on the original sphere. They
send the cube seam and the collapsed boundary to the pole. Their formulas
prove local constancy of any concatenation near such points when the
inputs are constant near the pole.
-/

noncomputable section

open Set Function Filter Topology
open scoped unitInterval

namespace NoExoticSixSphere.SmoothCube

def identityBased : BasedMap 3 (Sphere 3) (spherePole 3) := ⟨ContinuousMap.id _, rfl⟩

def constantBased : BasedMap 3 (Sphere 3) (spherePole 3) :=
  ⟨ContinuousMap.const _ (spherePole 3), rfl⟩

def leftCollapse : C(Sphere 3, Sphere 3) := (concatenate identityBased constantBased).val

def rightCollapse : C(Sphere 3, Sphere 3) := (concatenate constantBased identityBased).val

theorem leftCollapse_pole : leftCollapse (spherePole 3) = spherePole 3 :=
  (concatenate identityBased constantBased).property

theorem rightCollapse_pole : rightCollapse (spherePole 3) = spherePole 3 :=
  (concatenate constantBased identityBased).property

theorem leftCollapse_seam (u : Fin 3 → I) (hu : (u 0 : ℝ) = 1 / 2) :
    leftCollapse (quotient 3 u) = spherePole 3 :=
  concatenate_seam identityBased constantBased u hu

theorem rightCollapse_seam (u : Fin 3 → I) (hu : (u 0 : ℝ) = 1 / 2) :
    rightCollapse (quotient 3 u) = spherePole 3 :=
  concatenate_seam constantBased identityBased u hu

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem concatenate_eq_left_or_right (f g : BasedMap 3 X x) (y : Sphere 3) :
    (concatenate f g).val y = f.val (leftCollapse y) ∨
      (concatenate f g).val y = g.val (rightCollapse y) := by
  obtain ⟨u, rfl⟩ := quotient_surjective (by decide : 0 < 3) y
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · left
    change (concatenate f g).val (quotient 3 u) =
      f.val ((concatenate identityBased constantBased).val (quotient 3 u))
    rw [concatenate_formula, concatenate_formula, if_pos hu, if_pos hu]
    rfl
  · right
    change (concatenate f g).val (quotient 3 u) =
      g.val ((concatenate constantBased identityBased).val (quotient 3 u))
    rw [concatenate_formula, concatenate_formula, if_neg hu, if_neg hu]
    rfl

theorem concatenate_eventuallyEq_const (f g : BasedMap 3 X x)
    {U : Set (Sphere 3)} (hU : IsOpen U) (hb : spherePole 3 ∈ U)
    (hfU : EqOn f.val (fun _ ↦ x) U) (hgU : EqOn g.val (fun _ ↦ x) U)
    (y : Sphere 3) (hleft : leftCollapse y = spherePole 3)
    (hright : rightCollapse y = spherePole 3) :
    ((concatenate f g).val : Sphere 3 → X) =ᶠ[𝓝 y] fun _ ↦ x := by
  have hl : leftCollapse y ∈ U := hleft ▸ hb
  have hr : rightCollapse y ∈ U := hright ▸ hb
  filter_upwards [(hU.preimage leftCollapse.continuous).mem_nhds hl,
    (hU.preimage rightCollapse.continuous).mem_nhds hr] with z hzl hzr
  rcases concatenate_eq_left_or_right f g z with h | h
  · exact h.trans (hfU hzl)
  · exact h.trans (hgU hzr)

end NoExoticSixSphere.SmoothCube
