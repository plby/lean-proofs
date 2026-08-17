import Mathlib

open Filter
open scoped ENat Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos760.SimpleGraph

open _root_.SimpleGraph

def CochromPartable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, ∀ i : Fin n, G.IsClique (f ⁻¹' {i}) ∨ G.IsIndepSet (f ⁻¹' {i})

end Erdos760.SimpleGraph

namespace Erdos759.SimpleGraph

open _root_.SimpleGraph
open Erdos760.SimpleGraph

noncomputable def cochromaticNat {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | CochromPartable G k}

structure RotationSystem {V : Type*} (G : SimpleGraph V) where
  order : V → List V
  nodup_order : ∀ v, (order v).Nodup
  mem_order_iff : ∀ v w, w ∈ order v ↔ G.Adj v w

namespace RotationSystem

variable {V : Type*} {G : SimpleGraph V}

noncomputable def next (R : RotationSystem G) (v w : V) : V := by
  classical
  exact (R.order v).formPerm w

lemma next_mem_order_iff (R : RotationSystem G) (v w : V) :
    R.next v w ∈ R.order v ↔ w ∈ R.order v := by
  classical
  exact List.formPerm_mem_iff_mem

noncomputable def prev (R : RotationSystem G) (v w : V) : V := by
  classical
  exact (R.order v).formPerm.symm w

lemma prev_mem_order_iff (R : RotationSystem G) (v w : V) :
    R.prev v w ∈ R.order v ↔ w ∈ R.order v := by
  classical
  rw [← R.next_mem_order_iff v (R.prev v w)]
  simp [next, prev]

noncomputable def facePerm (R : RotationSystem G) : Equiv.Perm G.Dart := by
  classical
  refine
    { toFun := fun d =>
        ⟨(d.snd, R.next d.snd d.fst), ?_⟩
      invFun := fun d =>
        ⟨(R.prev d.fst d.snd, d.fst), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (R.mem_order_iff _ _).mp
      ((R.next_mem_order_iff _ _).mpr ((R.mem_order_iff _ _).mpr d.adj.symm))
  · exact ((R.mem_order_iff _ _).mp ((R.prev_mem_order_iff _ _).mpr
      ((R.mem_order_iff _ _).mpr d.adj))).symm
  · intro d
    apply Dart.ext
    simp [next, prev]
  · intro d
    apply Dart.ext
    simp [next, prev]

end RotationSystem

section FiniteRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def isolateCount : ℕ :=
  (Finset.univ.filter fun v ↦ ∀ w, ¬G.Adj v w).card

noncomputable def componentCount : ℕ :=
  Fintype.card G.ConnectedComponent

noncomputable def faceCount (R : RotationSystem G) : ℕ :=
  R.facePerm.cycleType.card + isolateCount G

def EmbedsOrientable (g : ℕ) : Prop :=
  ∃ R : RotationSystem G,
    2 * componentCount G + G.edgeFinset.card ≤
      Fintype.card V + faceCount G R + 2 * g

end FiniteRotation

universe u

noncomputable def EmbedsOnOrientableSurface {V : Type u} [Fintype V]
    (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (f : W ↪ V)
      [DecidableRel (G.comap f).Adj],
    EmbedsOrientable (G.comap f) g

def surfaceCochromaticValues (g : ℕ) : Set ℕ :=
  {k | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    EmbedsOnOrientableSurface G g ∧ cochromaticNat G = k}

noncomputable def zSurface (g : ℕ) : ℕ :=
  sSup (surfaceCochromaticValues g)

noncomputable def erdos759Scale (g : ℕ) : ℝ :=
  Real.sqrt (g : ℝ) / Real.log (g : ℝ)

theorem erdos_759 :
    (fun g : ℕ ↦ (zSurface g : ℝ)) =Θ[atTop] erdos759Scale := by
  sorry

end Erdos759.SimpleGraph

end
