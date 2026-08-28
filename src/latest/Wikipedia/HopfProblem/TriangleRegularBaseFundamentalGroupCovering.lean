import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoveringAction
import Mathlib.Topology.Homotopy.Lifting

/-!
# Exact monodromy of the two-open transition covering

The genuine quotient covering supplies a homomorphism from the fundamental
group to the opposite deck group. If a loop first travels in `U` from `b`
to `c`, then returns in `V`, its lifted endpoint has `U` coordinate
`transition c * (transition b)⁻¹`. The initial point is chosen using the
actual `U` trivialization; the transition at the basepoint need not be one.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem.TwoOpenTransition

section ChartPaths

variable {E X F : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace F] {p : E → X}

private def chartPath (e : Trivialization F p) {b c : X} (γ : Path b c)
    (hγ : ∀ s, γ s ∈ e.baseSet) (v : F) :
    Path (e.toOpenPartialHomeomorph.symm (b, v))
      (e.toOpenPartialHomeomorph.symm (c, v)) where
  toFun s := e.toOpenPartialHomeomorph.symm (γ s, v)
  continuous_toFun := e.continuousOn_symm_prodMk_left.comp_continuous γ.continuous hγ
  source' := by simp
  target' := by simp

private theorem chartPath_monodromy (hp : IsCoveringMap p) (e : Trivialization F p)
    {b c : X} (γ : Path b c) (hγ : ∀ s, γ s ∈ e.baseSet)
    (hb : b ∈ e.baseSet) (hc : c ∈ e.baseSet) (v : F) :
    hp.monodromy (.mk γ)
      ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ =
      ⟨e.toOpenPartialHomeomorph.symm (c, v), e.proj_symm_apply' hc⟩ := by
  apply hp.monodromy_eq_of_map_eq (.mk (chartPath e γ hγ v))
  apply congrArg Path.Homotopic.Quotient.mk
  ext s
  exact e.proj_symm_apply' (hγ s)

end ChartPaths

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G)

/-- A point in the actual projection fiber, expressed in `U` coordinates. -/
def fiberPointU (b : X) (g : G) : D.proj ⁻¹' {b} :=
  ⟨D.pointU b g, D.proj_pointU b g⟩

/-- A point in the actual projection fiber, expressed in `V` coordinates. -/
def fiberPointV (b : X) (g : G) : D.proj ⁻¹' {b} :=
  ⟨D.pointV b g, D.proj_pointV b g⟩

@[simp] theorem fiberPointU_val (b : X) (g : G) :
    (D.fiberPointU b g : D.TotalSpace) = D.pointU b g := rfl

@[simp] theorem fiberPointV_val (b : X) (g : G) :
    (D.fiberPointV b g : D.TotalSpace) = D.pointV b g := rfl

theorem pointV_eq_pointU (b : X) (g : G)
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.pointV b g = D.pointU b (g * (D.transition b)⁻¹) := by
  simpa only [inv_mul_cancel_right] using
    (D.pointU_eq_pointV b (g * (D.transition b)⁻¹) hb).symm

theorem fiberPointU_eq_fiberPointV (b : X) (g : G)
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.fiberPointU b g = D.fiberPointV b (g * D.transition b) :=
  Subtype.ext (D.pointU_eq_pointV b g hb)

theorem fiberPointV_eq_fiberPointU (b : X) (g : G)
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.fiberPointV b g = D.fiberPointU b (g * (D.transition b)⁻¹) :=
  Subtype.ext (D.pointV_eq_pointU b g hb)

/-- Paths lying in `U` have constant `U` fiber coordinate under lifting. -/
theorem monodromy_of_path_U {b c : X} (α : Path b c)
    (hα : ∀ s, α s ∈ D.U) (g : G) :
    D.isCoveringMap.monodromy (.mk α) (D.fiberPointU b g) = D.fiberPointU c g := by
  exact chartPath_monodromy D.isCoveringMap D.localTrivU α hα
    (by simpa using hα 0) (by simpa using hα 1) g

/-- Paths lying in `V` have constant `V` fiber coordinate under lifting. -/
theorem monodromy_of_path_V {b c : X} (β : Path b c)
    (hβ : ∀ s, β s ∈ D.V) (g : G) :
    D.isCoveringMap.monodromy (.mk β) (D.fiberPointV b g) = D.fiberPointV c g := by
  exact chartPath_monodromy D.isCoveringMap D.localTrivV β hβ
    (by simpa using hβ 0) (by simpa using hβ 1) g

/-- Exact monodromy for a two-piece loop, for every initial fiber coordinate. -/
theorem monodromy_trans_U_V {b c : X}
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X))
    (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X))
    (α : Path b c) (β : Path c b)
    (hα : ∀ s, α s ∈ D.U) (hβ : ∀ s, β s ∈ D.V) (g : G) :
    D.isCoveringMap.monodromy (.mk (α.trans β)) (D.fiberPointU b g) =
      D.fiberPointU b ((g * D.transition c) * (D.transition b)⁻¹) := by
  rw [Path.Homotopic.Quotient.mk_trans, D.isCoveringMap.monodromy_trans_apply,
    D.monodromy_of_path_U α hα g, D.fiberPointU_eq_fiberPointV c g hc,
    D.monodromy_of_path_V β hβ, D.fiberPointV_eq_fiberPointU b _ hb]

/-- The chosen basepoint really is the point of `U` fiber coordinate one. -/
def basepointU (b : X) (hb : b ∈ D.U) : D.proj ⁻¹' {b} :=
  ⟨D.pointU b 1, D.localTrivU.proj_symm_apply' hb⟩

@[simp] theorem basepointU_val (b : X) (hb : b ∈ D.U) :
    (D.basepointU b hb : D.TotalSpace) = D.pointU b 1 := rfl

@[simp] theorem basepointU_eq_fiberPointU (b : X) (hb : b ∈ D.U) :
    D.basepointU b hb = D.fiberPointU b 1 := rfl

@[simp] theorem localTrivU_basepointU (b : X) (hb : b ∈ D.U) :
    D.localTrivU (D.basepointU b hb) = (b, 1) :=
  D.localTrivU_pointU b 1 hb

/-- The genuine quotient-covering monodromy, with Mathlib's opposite-group
convention for left deck actions. -/
def fundamentalGroupToMulOpposite (b : X) (hb : b ∈ D.U) :
    FundamentalGroup X b →* Gᵐᵒᵖ :=
  D.isQuotientCoveringMap.fundamentalGroupToMulOpposite (D.basepointU b hb)

/-- The endpoint of the unique actual path lift is read in the initial
`U` trivialization, with no normalization of the transition at `b`. -/
theorem liftPath_trans_U_V_endpoint {b c : X}
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X))
    (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X))
    (α : Path b c) (β : Path c b)
    (hα : ∀ s, α s ∈ D.U) (hβ : ∀ s, β s ∈ D.V) :
    D.isCoveringMap.liftPath (α.trans β) (D.pointU b 1)
      (by simp) 1 =
      D.pointU b (D.transition c * (D.transition b)⁻¹) := by
  simpa only [one_mul, IsCoveringMap.monodromy, fiberPointU,
    Path.Homotopic.Quotient.mk, Quotient.mk', Quotient.lift_mk] using
    congrArg Subtype.val (D.monodromy_trans_U_V hb hc α β hα hβ 1)

/-- Reading the lifted endpoint in the actual initial chart gives the
transition product itself. -/
theorem localTrivU_liftPath_trans_U_V_endpoint {b c : X}
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X))
    (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X))
    (α : Path b c) (β : Path c b)
    (hα : ∀ s, α s ∈ D.U) (hβ : ∀ s, β s ∈ D.V) :
    D.localTrivU (D.isCoveringMap.liftPath (α.trans β) (D.pointU b 1)
      (by simp) 1) = (b, D.transition c * (D.transition b)⁻¹) := by
  rw [D.liftPath_trans_U_V_endpoint hb hc α β hα hβ]
  exact D.localTrivU_pointU b _ hb.1

/-- The exact value of the opposite-valued fundamental-group homomorphism
on a loop going out in `U` and returning in `V`. -/
theorem fundamentalGroupToMulOpposite_trans_U_V {b c : X}
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X))
    (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X))
    (α : Path b c) (β : Path c b)
    (hα : ∀ s, α s ∈ D.U) (hβ : ∀ s, β s ∈ D.V) :
    D.fundamentalGroupToMulOpposite b hb.1 (.mk (α.trans β)) =
      MulOpposite.op (D.transition c * (D.transition b)⁻¹) := by
  apply (D.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  have hm := congrArg Subtype.val (D.monodromy_trans_U_V hb hc α β hα hβ 1)
  simpa only [MulOpposite.unop_op, basepointU_eq_fiberPointU, smul_pointU, mul_one,
    one_mul, fiberPointU_val] using hm.symm

end Wikipedia.HopfProblem.TwoOpenTransition
