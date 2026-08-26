import ErdosProblems.Erdos118.Reused591.GoodSequenceTwo
import Mathlib.Order.RelIso.Set

namespace Erdos118.Reused591

open Cardinal Ordinal

namespace Erdos591.Negative

universe u

/-- A graph on an ordered presentation `X` meets the range of every
relation embedding of a full `alpha`-copy.  For a well-order this is exactly
the anti-red-clique property needed below. -/
def MeetsEveryFullSet {X : Type u} (r : X → X → Prop)
    (alpha : Ordinal.{u}) (blue : SimpleGraph X) : Prop :=
  ∀ f : ((· < ·) : alpha.ToType → alpha.ToType → Prop) ↪r r,
    ∃ a b : alpha.ToType, a ≠ b ∧ blue.Adj (f a) (f b)

/-- A relation-isomorphic ordered model carrying a finite-clique-free graph
which meets every full-order copy gives the required negative ordinal
partition relation. -/
theorem not_ordinalCardinalRamsey_of_model
    {X : Type u} {r : X → X → Prop} [IsWellOrder X r]
    {alpha : Ordinal.{u}} {n : ℕ}
    (e : r ≃r ((· < ·) : alpha.ToType → alpha.ToType → Prop))
    (modelBlue : SimpleGraph X)
    (hfree : ¬ ∃ S : Set X, modelBlue.IsClique S ∧ #S = n)
    (hhit : MeetsEveryFullSet r alpha modelBlue) :
    ¬ OrdinalCardinalRamsey alpha alpha n := by
  let blue : SimpleGraph alpha.ToType := SimpleGraph.comap e.symm modelBlue
  let red : SimpleGraph alpha.ToType := blueᶜ
  intro hramsey
  rcases hramsey red blue (by simpa [red] using
    (isCompl_compl.symm : IsCompl blueᶜ blue)) with hred | hblue
  · rcases hred with ⟨S, hS, htype⟩
    have heq :
        Ordinal.type ((· < ·) : alpha.ToType → alpha.ToType → Prop) =
          Ordinal.type ((· < ·) : S → S → Prop) := by
      rw [Ordinal.type_toType, htype]
    let i : ((· < ·) : alpha.ToType → alpha.ToType → Prop) ≃r
        ((· < ·) : S → S → Prop) :=
      Classical.choice (Ordinal.type_eq.mp heq)
    let inclusion : ((· < ·) : S → S → Prop) ↪r
        ((· < ·) : alpha.ToType → alpha.ToType → Prop) :=
      { toFun := fun x ↦ x.1
        inj' := Subtype.val_injective
        map_rel_iff' := Iff.rfl }
    let f : ((· < ·) : alpha.ToType → alpha.ToType → Prop) ↪r r :=
      i.toRelEmbedding.trans (inclusion.trans e.symm.toRelEmbedding)
    rcases hhit f with ⟨a, b, hab, hmodel⟩
    have hiab : (i a).1 ≠ (i b).1 := by
      intro h
      apply hab
      apply i.injective
      exact Subtype.ext h
    have hredab : red.Adj (i a).1 (i b).1 :=
      hS (i a).2 (i b).2 hiab
    have hblueab : blue.Adj (i a).1 (i b).1 := by
      simpa [blue, f, inclusion] using hmodel
    exact ((blue.compl_adj (i a).1 (i b).1).mp hredab).2 hblueab
  · rcases hblue with ⟨S, hS, hcard⟩
    let T : Set X := e.toEquiv ⁻¹' S
    have hTclique : modelBlue.IsClique T := by
      intro x hx y hy hxy
      have hne : e x ≠ e y := fun h ↦ hxy (e.injective h)
      have := hS hx hy hne
      simpa [blue] using this
    let f : T ≃ S :=
      { toFun := fun x ↦ ⟨e x.1, x.2⟩
        invFun := fun y ↦ ⟨e.symm y.1, by
          change e (e.symm y.1) ∈ S
          simpa using y.2⟩
        left_inv := by intro x; apply Subtype.ext; simp
        right_inv := by intro y; apply Subtype.ext; simp }
    apply hfree
    exact ⟨T, hTclique, (Cardinal.mk_congr f).trans hcard⟩

/-- The concrete transport from height-two good sequences to
`omega^(omega^2)`. -/
noncomputable def g2RelIso :
    G2LT ≃r ((· < ·) : (ω ^ (ω ^ 2)).ToType →
      (ω ^ (ω ^ 2)).ToType → Prop) := by
  apply Classical.choice
  apply Ordinal.type_eq.mp
  rw [g2_type, Ordinal.type_toType]

theorem handbook_negative_six_of_graph
    (modelBlue : SimpleGraph G2)
    (hfree : ¬ ∃ S : Set G2, modelBlue.IsClique S ∧ #S = 6)
    (hhit : MeetsEveryFullSet G2LT
      (ω ^ (ω ^ 2) : Ordinal.{0}) modelBlue) :
    ¬ OrdinalCardinalRamsey (ω ^ (ω ^ 2) : Ordinal.{0})
      (ω ^ (ω ^ 2) : Ordinal.{0}) 6 := by
  exact not_ordinalCardinalRamsey_of_model (r := G2LT)
    g2RelIso modelBlue hfree hhit

end Erdos591.Negative

end Erdos118.Reused591
