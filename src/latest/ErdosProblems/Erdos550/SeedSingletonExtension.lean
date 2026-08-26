import Mathlib
import ErdosProblems.Erdos550.StatefulTauFineEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fresh extension by one seed vertex

The head-pair part of the off--Turán proof repeatedly chooses one unused
vertex from a seed pool.  This lemma turns the cardinality estimate for that
pool into the exact block-extension interface used by the global induction.
-/

open Finset

namespace Erdos550

open Classical

theorem seed_singleton_fresh_extension
    {A V : Type*} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V)
    (parent : A → Option A)
    (Inv : Finset A → (A → V) → Prop)
    (P : Finset A) (f : A → V)
    (a : A) (haP : a ∉ P)
    (hready : ∀ y, parent a = some y → y ∈ P)
    (pool : Finset V)
    (hcard : (P.image f ∩ pool).card < pool.card)
    (hparent : ∀ v ∈ pool, ∀ y, parent a = some y →
      G.Adj v (f y))
    (hInv : ∀ v ∈ pool, v ∉ P.image f →
      Inv (P ∪ {a}) (fun x => if x = a then v else f x)) :
    IsFreshBlockExtension G parent {a} P f Inv := by
  have hfresh : (pool \ P.image f).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have hsub : pool ⊆ P.image f := by
      intro v hv
      by_contra hvnot
      have : v ∈ pool \ P.image f :=
        Finset.mem_sdiff.mpr ⟨hv, hvnot⟩
      simpa [hempty] using! this
    have hinter : P.image f ∩ pool = pool := by
      ext z
      constructor
      · exact fun hz => (Finset.mem_inter.mp hz).2
      · intro hz
        exact Finset.mem_inter.mpr ⟨hsub hz, hz⟩
    rw [hinter] at hcard
    exact (Nat.lt_irrefl _ hcard)
  let v : V := hfresh.choose
  have hv := hfresh.choose_spec
  have hvPool : v ∈ pool := (Finset.mem_sdiff.mp hv).1
  have hvUnused : v ∉ P.image f := (Finset.mem_sdiff.mp hv).2
  let g : A → V := fun x =>
    if x = a then v else Classical.arbitrary V
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxa : x = a := Finset.mem_singleton.mp hx
    have hya : y = a := Finset.mem_singleton.mp hy
    simpa [g, hxa, hya]
  · rw [Finset.disjoint_left]
    intro z hzNew hzOld
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hzNew
    have hxa : x = a := Finset.mem_singleton.mp hx
    subst x
    have hzv : z = v := by simpa [g] using! hxz.symm
    exact hvUnused (hzv ▸ hzOld)
  · intro x hx y hxy
    have hxa : x = a := Finset.mem_singleton.mp hx
    subst x
    have hyNot : y ∉ ({a} : Finset A) := by
      intro hya
      have : y = a := Finset.mem_singleton.mp hya
      subst y
      exact haP (hready a hxy)
    simp only [hyNot, ↓reduceIte]
    simpa [g] using! hparent v hvPool y hxy
  · have hmap :
        (fun x => if x ∈ ({a} : Finset A) then g x else f x) =
          (fun x => if x = a then v else f x) := by
      funext x
      by_cases hxa : x = a <;> simp [g, hxa]
    rw [hmap]
    exact hInv v hvPool hvUnused

end Erdos550
