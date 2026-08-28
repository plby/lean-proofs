import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The cubical Samelson product

The commutator of an `M`-loop and an `N`-loop in a topological group is an
`M ⊕ N`-loop. This construction descends to Mathlib's homotopy groups.
It is the operation whose value on the identity class of the quaternion
three-sphere will be used in the calculation of `π₆(S³)`.

This file does not assert that that element generates, or has order twelve.
-/

noncomputable section

open scoped Topology unitInterval commutatorElement

namespace Wikipedia.HomotopyGroupsOfSpheres.Samelson

variable {M N G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Commutators on separate blocks of cube coordinates. -/
def loop (p : GenLoop M G 1) (q : GenLoop N G 1) : GenLoop (M ⊕ N) G 1 :=
  ⟨⟨fun t => ⁅p (t ∘ Sum.inl), q (t ∘ Sum.inr)⁆, by
      simp only [commutatorElement_def]
      fun_prop⟩, fun t ht => by
    change ⁅p.val (t ∘ Sum.inl), q.val (t ∘ Sum.inr)⁆ = 1
    rcases Cube.boundary_sum_iff.mp ht with hp | hq
    · rw [p.property _ hp, commutatorElement_one_left]
    · rw [q.property _ hq, commutatorElement_one_right]⟩

@[simp] theorem loop_apply (p : GenLoop M G 1) (q : GenLoop N G 1)
    (t : (M ⊕ N) → I) :
    loop p q t = ⁅p (t ∘ Sum.inl), q (t ∘ Sum.inr)⁆ := rfl

@[simp] theorem loop_const_left (q : GenLoop N G 1) :
    loop (GenLoop.const : GenLoop M G 1) q = GenLoop.const := by
  ext t
  simp

@[simp] theorem loop_const_right (p : GenLoop M G 1) :
    loop p (GenLoop.const : GenLoop N G 1) = GenLoop.const := by
  ext t
  simp

/-- Relative homotopies in both factors give a relative homotopy of commutators. -/
def homotopy {p p' : GenLoop M G 1} {q q' : GenLoop N G 1}
    (H : p.val.HomotopyRel p'.val (Cube.boundary M))
    (K : q.val.HomotopyRel q'.val (Cube.boundary N)) :
    (loop p q).val.HomotopyRel (loop p' q').val (Cube.boundary (M ⊕ N)) where
  toFun tx := ⁅H (tx.1, tx.2 ∘ Sum.inl), K (tx.1, tx.2 ∘ Sum.inr)⁆
  continuous_toFun := by simp only [commutatorElement_def]; fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    change ⁅H (s, t ∘ Sum.inl), K (s, t ∘ Sum.inr)⁆ = loop p q t
    have hboundary : loop p q t = 1 := (loop p q).property t ht
    rw [hboundary]
    rcases Cube.boundary_sum_iff.mp ht with hp | hq
    · rw [H.eq_fst s hp, p.property _ hp, commutatorElement_one_left]
    · rw [K.eq_fst s hq, q.property _ hq, commutatorElement_one_right]

theorem homotopic {p p' : GenLoop M G 1} {q q' : GenLoop N G 1}
    (hp : GenLoop.Homotopic p p') (hq : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (loop p q) (loop p' q') := by
  obtain ⟨H⟩ := hp
  obtain ⟨K⟩ := hq
  exact ⟨homotopy H K⟩

/-- The Samelson pairing on the original quotient by relative homotopy. -/
def product (a : HomotopyGroup M G 1) (b : HomotopyGroup N G 1) :
    HomotopyGroup (M ⊕ N) G 1 :=
  Quotient.liftOn₂ a b (fun p q => ⟦loop p q⟧)
    (fun _ _ _ _ hp hq => Quotient.sound (homotopic hp hq))

@[simp] theorem product_mk (p : GenLoop M G 1) (q : GenLoop N G 1) :
    product (⟦p⟧ : HomotopyGroup M G 1) (⟦q⟧ : HomotopyGroup N G 1) =
      (⟦loop p q⟧ : HomotopyGroup (M ⊕ N) G 1) := rfl

end Wikipedia.HomotopyGroupsOfSpheres.Samelson
