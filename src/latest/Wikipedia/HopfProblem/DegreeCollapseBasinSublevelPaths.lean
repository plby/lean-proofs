import Mathlib.Dynamics.Flow
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Forward basin points are joined inside the original sublevel

An antitone flow stays below the initial height. At a limit point strictly
below the level, a path-component neighborhood finishes the finite flow
segment to a path in the same sublevel. Thus two points with the same
forward limit cannot lie in distinct sublevel path components.
-/

noncomputable section

open Set Filter Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  (F : Flow ℝ X) {f : X → ℝ}

theorem joinedIn_sublevel_of_forward_limit (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {x p : X} {a : ℝ}
    (hx : f x ≤ a) (hp : f p < a) (hlim : Tendsto (fun t => F t x) atTop (𝓝 p)) :
    JoinedIn {y : X | f y ≤ a} x p := by
  have hU : {y : X | f y < a} ∈ 𝓝 p :=
    (isOpen_lt hf continuous_const).mem_nhds hp
  have hC := pathComponentIn_mem_nhds hU
  obtain ⟨T, hT, hFT⟩ := ((eventually_ge_atTop (0 : ℝ)).and (hlim.eventually hC)).exists
  have htail : JoinedIn {y : X | f y ≤ a} (F T x) p :=
    (show JoinedIn {y : X | f y < a} p (F T x) from hFT).symm.mono
      (fun y hy => (show f y < a from hy).le)
  have hsegment : JoinedIn {y : X | f y ≤ a} x (F T x) := by
    let γ : Path x (F T x) := {
      toFun := fun u => F ((u : ℝ) * T) x
      continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
      source' := by simp
      target' := by simp
    }
    refine ⟨γ, fun u => ?_⟩
    have htime : 0 ≤ (u : ℝ) * T := mul_nonneg u.property.1 hT
    have hh := hmono x htime
    have hh' : f (F ((u : ℝ) * T) x) ≤ f x := by simpa only [F.map_zero_apply] using hh
    exact hh'.trans hx
  exact hsegment.trans htail

theorem joined_sublevel_of_common_forward_limit (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {a : ℝ}
    (x y : {z : X // f z ≤ a}) {p : X} (hp : f p < a)
    (hx : Tendsto (fun t => F t x) atTop (𝓝 p))
    (hy : Tendsto (fun t => F t y) atTop (𝓝 p)) : Joined x y := by
  exact ((joinedIn_sublevel_of_forward_limit F hf hmono x.property hp hx).trans
    (joinedIn_sublevel_of_forward_limit F hf hmono y.property hp hy).symm).joined_subtype

theorem one_forward_limit_above_connected_cut (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {a b : ℝ} (hab : a ≤ b)
    [PathConnectedSpace {z : X // f z ≤ a}]
    (x y : {z : X // f z ≤ b}) (hnot : ¬Joined x y) {p r : X}
    (hp : f p < b) (hr : f r < b)
    (hx : Tendsto (fun t => F t x) atTop (𝓝 p))
    (hy : Tendsto (fun t => F t y) atTop (𝓝 r)) : a < f p ∨ a < f r := by
  by_contra h
  have hpa : f p ≤ a := le_of_not_gt (fun hp => h (Or.inl hp))
  have hra : f r ≤ a := le_of_not_gt (fun hr => h (Or.inr hr))
  let i : C({z : X // f z ≤ a}, {z : X // f z ≤ b}) :=
    ⟨fun z => ⟨z.val, z.property.trans hab⟩, continuous_subtype_val.subtype_mk _⟩
  have hpr : Joined (i ⟨p, hpa⟩) (i ⟨r, hra⟩) :=
    (PathConnectedSpace.joined (⟨p, hpa⟩ : {z : X // f z ≤ a}) ⟨r, hra⟩).map i.continuous
  have hxp : Joined x (i ⟨p, hpa⟩) :=
    (joinedIn_sublevel_of_forward_limit F hf hmono x.property hp hx).joined_subtype
  have hyr : Joined y (i ⟨r, hra⟩) :=
    (joinedIn_sublevel_of_forward_limit F hf hmono y.property hr hy).joined_subtype
  exact hnot (hxp.trans (hpr.trans hyr.symm))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
