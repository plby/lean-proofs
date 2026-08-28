import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Covering.Basic

/-!
# A discrete-group bundle glued across two open sets

A continuous transition on the overlap of two open sets gives a genuine
fiber bundle with discrete group fiber. Its coordinate changes act on
the right, so left multiplication commutes with every coordinate change.
The projection is a covering map, and its two local trivializations
give explicit points and their overlap relation.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem

/-- Two open sets covering a space, with a transition function continuous
on their overlap. No continuity is required away from the overlap. -/
structure TwoOpenTransition (X G : Type*) [TopologicalSpace X] [TopologicalSpace G] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ (V : Set X) = Set.univ
  transition : X → G
  continuousOn_transition : ContinuousOn transition ((U : Set X) ∩ (V : Set X))

namespace TwoOpenTransition

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
  (D : TwoOpenTransition X G)

/-- The two bundle charts, with `false` indexing `U` and `true` indexing `V`. -/
def baseSet : Bool → Set X
  | false => D.U
  | true => D.V

@[simp] theorem baseSet_false : D.baseSet false = (D.U : Set X) := rfl

@[simp] theorem baseSet_true : D.baseSet true = (D.V : Set X) := rfl

/-- Choose the `U` coordinates whenever they are available. -/
def indexAt (x : X) : Bool := by
  classical
  exact if x ∈ D.U then false else true

@[simp] theorem indexAt_of_mem_U {x : X} (hx : x ∈ D.U) : D.indexAt x = false := by
  simp [indexAt, hx]

@[simp] theorem indexAt_of_not_mem_U {x : X} (hx : x ∉ D.U) : D.indexAt x = true := by
  simp [indexAt, hx]

theorem mem_baseSet_indexAt (x : X) : x ∈ D.baseSet (D.indexAt x) := by
  by_cases hx : x ∈ D.U
  · simpa only [D.indexAt_of_mem_U hx, baseSet_false, SetLike.mem_coe] using hx
  · have hcover : x ∈ (D.U : Set X) ∪ (D.V : Set X) := by
      rw [D.cover]
      exact mem_univ x
    simpa only [D.indexAt_of_not_mem_U hx, baseSet_true] using hcover.resolve_left hx

variable [Group G]

/-- Coordinate changes multiply on the right by the transition or its inverse. -/
def coordChange : Bool → Bool → X → G → G
  | false, false, _, w => w
  | false, true, x, w => w * D.transition x
  | true, false, x, w => w * (D.transition x)⁻¹
  | true, true, _, w => w

@[simp] theorem coordChange_false_false (x : X) (w : G) :
    D.coordChange false false x w = w := rfl

@[simp] theorem coordChange_false_true (x : X) (w : G) :
    D.coordChange false true x w = w * D.transition x := rfl

@[simp] theorem coordChange_true_false (x : X) (w : G) :
    D.coordChange true false x w = w * (D.transition x)⁻¹ := rfl

@[simp] theorem coordChange_true_true (x : X) (w : G) :
    D.coordChange true true x w = w := rfl

@[simp] theorem coordChange_self (i : Bool) (x : X) (w : G) :
    D.coordChange i i x w = w := by
  cases i <;> rfl

theorem coordChange_comp (i j k : Bool) (x : X) (w : G) :
    D.coordChange j k x (D.coordChange i j x w) = D.coordChange i k x w := by
  cases i <;> cases j <;> cases k <;> simp [coordChange, mul_assoc]

/-- Left multiplication is independent of which local coordinates are used. -/
theorem coordChange_mul_left (i j : Bool) (x : X) (g w : G) :
    D.coordChange i j x (g * w) = g * D.coordChange i j x w := by
  cases i <;> cases j <;> simp [coordChange, mul_assoc]

variable [DiscreteTopology G]

theorem continuousOn_coordChange (i j : Bool) :
    ContinuousOn (fun p : X × G => D.coordChange i j p.1 p.2)
      ((D.baseSet i ∩ D.baseSet j) ×ˢ Set.univ) := by
  cases i <;> cases j
  · exact continuous_snd.continuousOn
  · exact continuous_snd.continuousOn.mul
      (D.continuousOn_transition.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  · exact continuous_snd.continuousOn.mul
      (D.continuousOn_transition.comp continuous_fst.continuousOn
        (fun _ hp => ⟨hp.1.2, hp.1.1⟩)).inv
  · exact continuous_snd.continuousOn

/-- The actual bundle core, with the specified right-multiplication transitions. -/
def core : FiberBundleCore Bool X G where
  baseSet := D.baseSet
  isOpen_baseSet := by
    intro i
    cases i
    · exact D.U.isOpen
    · exact D.V.isOpen
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet_indexAt
  coordChange := D.coordChange
  coordChange_self := fun i x _ w => D.coordChange_self i x w
  continuousOn_coordChange := D.continuousOn_coordChange
  coordChange_comp := fun i j k x _ w => D.coordChange_comp i j k x w

@[simp] theorem core_baseSet (i : Bool) : D.core.baseSet i = D.baseSet i := rfl

@[simp] theorem core_indexAt (x : X) : D.core.indexAt x = D.indexAt x := rfl

@[simp] theorem core_coordChange (i j : Bool) (x : X) (w : G) :
    D.core.coordChange i j x w = D.coordChange i j x w := rfl

/-- The total space with the topology constructed from the bundle core. -/
abbrev TotalSpace := D.core.TotalSpace

/-- Projection from the actual total space to the base. -/
abbrev proj : D.TotalSpace → X := D.core.proj

/-- The trivialization on `U`. -/
abbrev localTrivU : Trivialization G D.proj := D.core.localTriv false

/-- The trivialization on `V`. -/
abbrev localTrivV : Trivialization G D.proj := D.core.localTriv true

@[simp] theorem localTrivU_baseSet : D.localTrivU.baseSet = (D.U : Set X) := rfl

@[simp] theorem localTrivV_baseSet : D.localTrivV.baseSet = (D.V : Set X) := rfl

/-- A point expressed in `U` coordinates; defined on the whole ambient product. -/
def pointU (x : X) (g : G) : D.TotalSpace :=
  D.localTrivU.toOpenPartialHomeomorph.symm (x, g)

/-- A point expressed in `V` coordinates; defined on the whole ambient product. -/
def pointV (x : X) (g : G) : D.TotalSpace :=
  D.localTrivV.toOpenPartialHomeomorph.symm (x, g)

@[simp] theorem proj_pointU (x : X) (g : G) : D.proj (D.pointU x g) = x := rfl

@[simp] theorem proj_pointV (x : X) (g : G) : D.proj (D.pointV x g) = x := rfl

@[simp] theorem localTrivU_pointU (x : X) (g : G) (hx : x ∈ D.U) :
    D.localTrivU (D.pointU x g) = (x, g) :=
  D.localTrivU.toOpenPartialHomeomorph.right_inv ⟨hx, mem_univ g⟩

@[simp] theorem localTrivV_pointV (x : X) (g : G) (hx : x ∈ D.V) :
    D.localTrivV (D.pointV x g) = (x, g) :=
  D.localTrivV.toOpenPartialHomeomorph.right_inv ⟨hx, mem_univ g⟩

/-- The two expressions represent the same point precisely with the stated
right-multiplication change of fiber coordinate on the overlap. -/
theorem pointU_eq_pointV (x : X) (g : G)
    (hx : x ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.pointU x g = D.pointV x (g * D.transition x) := by
  change (⟨x, D.core.coordChange false (D.core.indexAt x) x g⟩ : D.TotalSpace) =
    ⟨x, D.core.coordChange true (D.core.indexAt x) x (g * D.transition x)⟩
  apply congrArg (fun w : G => (⟨x, w⟩ : D.TotalSpace))
  exact (D.core.coordChange_comp false true (D.core.indexAt x) x
    ⟨⟨hx.1, hx.2⟩, D.core.mem_baseSet_at x⟩ g).symm

/-- A bundle with a discrete group fiber is a covering of the base. -/
theorem isCoveringMap : IsCoveringMap D.proj := by
  exact FiberBundle.isCoveringMap (F := G) (E := D.core.Fiber)

end TwoOpenTransition
end Wikipedia.HopfProblem
