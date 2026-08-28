import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoveringCore
import Mathlib.Topology.Covering.Quotient

/-!
# The actual deck action of a two-open transition covering

Right-multiplication changes of coordinates commute with the left group
action. This proves continuity in the constructed bundle topology. The
action is free and transitive on every fiber, so the genuine covering
projection is a quotient covering by this action.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem.TwoOpenTransition

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G)

/-- Left multiplication on the group fiber of the actual total space. -/
instance totalMulAction : MulAction G D.TotalSpace where
  smul g p := ⟨p.proj, g * (show G from p.2)⟩
  one_smul p := by
    rcases p with ⟨b, v⟩
    change G at v
    change (⟨b, 1 * v⟩ : D.TotalSpace) = ⟨b, v⟩
    exact congrArg (fun w : G => (⟨b, w⟩ : D.TotalSpace)) (one_mul v)
  mul_smul g h p := by
    rcases p with ⟨b, v⟩
    change G at v
    change (⟨b, (g * h) * v⟩ : D.TotalSpace) = ⟨b, g * (h * v)⟩
    exact congrArg (fun w : G => (⟨b, w⟩ : D.TotalSpace)) (mul_assoc g h v)

@[simp] theorem proj_smul (g : G) (p : D.TotalSpace) :
    D.proj (g • p) = D.proj p := rfl

/-- Every chart reads the same left multiplication on the group coordinate. -/
theorem localTriv_smul (i : Bool) (g : G) (p : D.TotalSpace) :
    D.core.localTriv i (g • p) =
      (D.proj p, g * (D.core.localTriv i p).2) := by
  apply Prod.ext
  · rfl
  exact D.coordChange_mul_left _ _ _ _ _

@[simp] theorem smul_pointU (g : G) (x : X) (w : G) :
    g • D.pointU x w = D.pointU x (g * w) := by
  change (⟨x, g * D.coordChange false (D.indexAt x) x w⟩ : D.TotalSpace) =
    ⟨x, D.coordChange false (D.indexAt x) x (g * w)⟩
  exact congrArg (fun v : G => (⟨x, v⟩ : D.TotalSpace))
    (D.coordChange_mul_left false (D.indexAt x) x g w).symm

@[simp] theorem smul_pointV (g : G) (x : X) (w : G) :
    g • D.pointV x w = D.pointV x (g * w) := by
  change (⟨x, g * D.coordChange true (D.indexAt x) x w⟩ : D.TotalSpace) =
    ⟨x, D.coordChange true (D.indexAt x) x (g * w)⟩
  exact congrArg (fun v : G => (⟨x, v⟩ : D.TotalSpace))
    (D.coordChange_mul_left true (D.indexAt x) x g w).symm

/-- Continuity is proved in the genuine local trivializations, not in an
unrelated product topology on the underlying set. -/
instance totalContinuousConstSMul : ContinuousConstSMul G D.TotalSpace where
  continuous_const_smul g := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := D.core.localTriv (D.core.indexAt p.proj)
    have he : D.proj p ∈ e.baseSet := D.core.mem_baseSet_at p.proj
    have hecont : ContinuousAt e p := e.continuousAt (e.mem_source.mpr he)
    apply e.continuousAt_of_comp_left
      (show ContinuousAt (D.proj ∘ (g • ·)) p from D.core.continuous_proj.continuousAt) he
    convert D.core.continuous_proj.continuousAt.prodMk
      ((show ContinuousAt (fun _ : D.TotalSpace => g) p from continuousAt_const).mul
        hecont.snd) using 1
    funext q
    exact D.localTriv_smul _ _ _

instance totalIsCancelSMul : IsCancelSMul G D.TotalSpace where
  right_cancel' g h p he := by
    have he' := congrArg (fun q : D.TotalSpace => (q.2 : G)) he
    exact mul_right_cancel he'

/-- The deck action is transitive exactly on the fibers of the projection. -/
theorem proj_eq_iff_mem_orbit {p q : D.TotalSpace} :
    D.proj p = D.proj q ↔ p ∈ MulAction.orbit G q := by
  constructor
  · cases p with
    | mk b w =>
      cases q with
      | mk c v =>
        change G at w v
        intro h
        change b = c at h
        subst c
        refine ⟨w * v⁻¹, ?_⟩
        change (⟨b, (w * v⁻¹) * v⟩ : D.TotalSpace) = ⟨b, w⟩
        exact congrArg (fun z : G => (⟨b, z⟩ : D.TotalSpace)) (inv_mul_cancel_right w v)
  · rintro ⟨g, rfl⟩
    rfl

/-- The transition construction gives an actual quotient covering by the
left group action, without any connectedness hypothesis on its total space. -/
theorem isQuotientCoveringMap : IsQuotientCoveringMap D.proj G := by
  apply (isQuotientCoveringMap_iff_isCoveringMap_and D.proj G).mpr
  exact ⟨D.isCoveringMap, fun x => ⟨D.pointU x 1, D.proj_pointU x 1⟩,
    inferInstance, inferInstance, D.proj_eq_iff_mem_orbit⟩

end Wikipedia.HopfProblem.TwoOpenTransition
