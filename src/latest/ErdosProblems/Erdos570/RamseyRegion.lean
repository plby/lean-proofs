/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core

/-!
# Applying exact Ramsey bounds inside finite vertex regions
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- An exact-order Ramsey assertion can be applied inside any finite induced
region having at least that many vertices. -/
theorem RamseyAt.on_finset {F H : GraphCode} {N : ℕ}
    (h : RamseyAt F H N) {V : Type*} [Fintype V]
    (C : SimpleGraph V) (S : Finset V) (hNS : N ≤ S.card) :
    F.graph ⊑ C.induce (S : Set V) ∨
      H.graph ⊑ Cᶜ.induce (S : Set V) := by
  let Q := C.induce (S : Set V)
  have hc : Fintype.card (S : Set V) = S.card := by simp
  let e : Q ≃g Q.overFin hc := SimpleGraph.overFinIso (G := Q) hc
  have hlarge : RamseyAt F H S.card := h.mono_vertices hNS
  rcases hlarge (Q.overFin hc) with hred | hblue
  · left
    exact hred.trans ⟨e.symm.toCopy⟩
  · right
    let ec : Qᶜ ≃g (Q.overFin hc)ᶜ :=
      { toEquiv := e.toEquiv
        map_rel_iff' := by
          intro u v
          simp only [SimpleGraph.compl_adj]
          constructor
          · rintro ⟨hne, hnadj⟩
            exact ⟨fun huv ↦ hne (congrArg e.toEquiv huv),
              fun hadj ↦ hnadj (e.toHom.map_adj hadj)⟩
          · rintro ⟨hne, hnadj⟩
            exact ⟨fun huv ↦ hne (e.injective huv),
              fun hadj ↦ hnadj (e.map_rel_iff.mp hadj)⟩ }
    have hQ : Qᶜ = Cᶜ.induce (S : Set V) := by
      ext u v
      simp only [Q, SimpleGraph.compl_adj, SimpleGraph.induce_adj]
      rw [Subtype.val_injective.ne_iff]
    rw [← hQ]
    exact hblue.trans ⟨ec.symm.toCopy⟩

/-- Least-Ramsey-number specialization of `RamseyAt.on_finset`. -/
theorem graphRamseyNumber_on_finset (F H : GraphCode)
    {V : Type*} [Fintype V] (C : SimpleGraph V) (S : Finset V)
    (hsize : graphRamseyNumber F H ≤ S.card) :
    F.graph ⊑ C.induce (S : Set V) ∨
      H.graph ⊑ Cᶜ.induce (S : Set V) :=
  Erdos570.RamseyAt.on_finset (graphRamseyNumber_spec F H) C S hsize

end Erdos570
