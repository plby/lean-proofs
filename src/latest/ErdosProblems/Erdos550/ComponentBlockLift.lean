import Mathlib
import ErdosProblems.Erdos550.RootedComponentLocal
import ErdosProblems.Erdos550.StatefulBlockGlue

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lifting a rooted-component embedding to a whole-source block map

The sharp pair lemma returns a map on the subtype consisting of one deleted
component.  Stateful block induction expects a total map on the source type.
This file provides that harmless lift and, importantly, keeps exact image
accounting available for the packedness update.
-/

open Finset

namespace Erdos550

open Classical

variable {A : Type} {V : Type*} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V] [Nonempty V]

/-- Extend a map on one deleted component arbitrarily outside that component. -/
noncomputable def liftComponentMap
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S)
    (f : RootedComponentVertex T S c → V) : A → V :=
  fun a =>
    if h : a ∈ componentNonseedVertices T S c.1 then f ⟨a, h⟩
    else Classical.arbitrary V

@[simp] lemma liftComponentMap_mem
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S)
    (f : RootedComponentVertex T S c → V)
    {a : A} (ha : a ∈ componentNonseedVertices T S c.1) :
    liftComponentMap T S c f a = f ⟨a, ha⟩ := by
  simp [liftComponentMap, ha]

lemma liftComponentMap_injOn
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S)
    (f : RootedComponentVertex T S c → V)
    (hfinj : Function.Injective f) :
    Set.InjOn (liftComponentMap T S c f)
      (componentNonseedVertices T S c.1) := by
  intro a ha b hb hab
  have hsub :
      f (⟨a, ha⟩ : RootedComponentVertex T S c) =
        f (⟨b, hb⟩ : RootedComponentVertex T S c) := by
    rw [liftComponentMap_mem T S c f ha,
      liftComponentMap_mem T S c f hb] at hab
    exact hab
  exact congrArg Subtype.val (hfinj hsub)

lemma image_liftComponentMap
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S)
    (f : RootedComponentVertex T S c → V) :
    (componentNonseedVertices T S c.1).image
        (liftComponentMap T S c f) =
      Finset.univ.image f := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨⟨a, ha⟩, Finset.mem_univ _, by
        simp [liftComponentMap, ha]⟩
  · intro hv
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨a.1, a.2, by simp [liftComponentMap, a.2]⟩

/-- Exact contribution of the lifted component to an arbitrary host region. -/
lemma card_image_liftComponentMap_inter
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S)
    (f : RootedComponentVertex T S c → V)
    (hfinj : Function.Injective f)
    (P : Finset V) :
    (((componentNonseedVertices T S c.1).image
        (liftComponentMap T S c f)) ∩ P).card =
      (Finset.univ.filter fun x : RootedComponentVertex T S c =>
        f x ∈ P).card := by
  rw [image_liftComponentMap T S c f]
  exact card_image_inter_eq_card_filter Finset.univ f P
    (fun _ _ _ _ h => hfinj h)

end Erdos550
