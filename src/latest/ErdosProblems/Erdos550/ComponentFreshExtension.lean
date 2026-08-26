import Mathlib
import ErdosProblems.Erdos550.ComponentBlockLift
import ErdosProblems.Erdos550.StatefulTauFineEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fresh extension by a whole rooted component

This is the gluing adapter between a local rooted-pair embedding and the
stateful τ-fine induction.  Readiness identifies the exposed source vertex
with the component root; all other predecessor edges are internal.
-/

open Finset

namespace Erdos550

open Classical

theorem component_fresh_block_extension
    {A : Type} {V : Type*} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (T : SimpleGraph A)
    (G : SimpleGraph V)
    (Sseed P : Finset A)
    (parent : A → Option A)
    (D : RootedSeedComponentData T Sseed parent)
    (hPblock : IsBlockClosed (tauFineBlock T Sseed) P)
    (f : A → V)
    (Inv : Finset A → (A → V) → Prop)
    (a : A) (haSeed : a ∉ Sseed) (haP : a ∉ P)
    (hready : ∀ y, parent a = some y → y ∈ P)
    (c : NonseedComponent T Sseed)
    (hc : c = nonseedComponentOf T Sseed a haSeed)
    (fC : RootedComponentVertex T Sseed c → V)
    (hfCinj : Function.Injective fC)
    (hfCfresh :
      Disjoint (Finset.univ.image fC) (P.image f))
    (hfCinternal :
      ∀ (x y : RootedComponentVertex T Sseed c),
        parent x.1 = some y.1 → G.Adj (fC x) (fC y))
    (hfCroot :
      ∀ y, parent (D.root c) = some y →
        G.Adj (fC (componentLocalRoot T Sseed D c)) (f y))
    (hInv :
      Inv (P ∪ tauFineBlock T Sseed a)
        (fun x => if x ∈ tauFineBlock T Sseed a then
          liftComponentMap T Sseed c fC x else f x)) :
    IsFreshBlockExtension G parent (tauFineBlock T Sseed a)
      P f Inv := by
  have haroot :
      a = D.root (nonseedComponentOf T Sseed a haSeed) :=
    ready_nonseed_eq_component_root T Sseed P parent D hPblock
      a haSeed haP hready
  have hblock :
      tauFineBlock T Sseed a =
        componentNonseedVertices T Sseed c.1 := by
    rw [tauFineBlock, dif_neg haSeed]
    simpa [hc]
  let g := liftComponentMap T Sseed c fC
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [hblock]
    exact liftComponentMap_injOn T Sseed c fC hfCinj
  · rw [hblock, image_liftComponentMap T Sseed c fC]
    exact hfCfresh
  · intro x hx y hxy
    have hxc :
        x ∈ componentNonseedVertices T Sseed c.1 := by
      simpa [hblock] using! hx
    by_cases hyc : y ∈ componentNonseedVertices T Sseed c.1
    · have hyBlock : y ∈ tauFineBlock T Sseed a := by
        simpa [hblock] using! hyc
      simp only [hyBlock, ↓reduceIte]
      simpa [g, liftComponentMap, hxc, hyc] using!
        hfCinternal
          (⟨x, hxc⟩ : RootedComponentVertex T Sseed c)
          (⟨y, hyc⟩ : RootedComponentVertex T Sseed c) hxy
    · have hyNotBlock : y ∉ tauFineBlock T Sseed a := by
        simpa [hblock] using! hyc
      simp only [hyNotBlock, ↓reduceIte]
      have hxroot : x = D.root c := by
        by_contra hxne
        obtain ⟨z, hzc, hxz⟩ :=
          D.parent_internal c x hxc hxne
        have hyz : y = z := by
          rw [hxz] at hxy
          exact (Option.some.inj hxy).symm
        subst y
        exact hyc hzc
      subst x
      simpa [g, liftComponentMap, D.root_mem c,
        componentLocalRoot] using! hfCroot y hxy
  · simpa [g] using! hInv

end Erdos550
