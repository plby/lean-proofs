import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Gluing compact coordinate tiles with identical fibres

Two continuous surjections from the same compact tile space to Hausdorff
spaces give a homeomorphism if their point-identifications agree exactly.
This elementary quotient argument will identify the actual positive toric
component with its explicitly tiled planar hexagon.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon.CommonFibres

variable {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f)

def descend (x : X) : Y := g (hf x).choose

theorem descend_apply (hfg : ∀ a b, f a = f b → g a = g b) (a : A) :
    descend f g hf (f a) = g a :=
  hfg _ a (hf (f a)).choose_spec

theorem descend_surjective (hfg : ∀ a b, f a = f b → g a = g b)
    (hg : Function.Surjective g) : Function.Surjective (descend f g hf) := by
  intro y
  obtain ⟨a, rfl⟩ := hg y
  exact ⟨f a, descend_apply f g hf hfg a⟩

theorem descend_injective (hgf : ∀ a b, g a = g b → f a = f b) :
    Function.Injective (descend f g hf) := by
  intro x y h
  have he := hgf (hf x).choose (hf y).choose h
  exact (hf x).choose_spec.symm.trans (he.trans (hf y).choose_spec)

variable [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

theorem descend_continuous (hq : IsQuotientMap f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b → g a = g b) : Continuous (descend f g hf) := by
  apply hq.continuous_iff.mpr
  have he : descend f g hf ∘ f = g := funext (descend_apply f g hf hfg)
  rwa [he]

variable [CompactSpace A] [T2Space X] [T2Space Y]

/-- The common-fibre equivalence respects both original quotient topologies. -/
def homeomorph (hfc : Continuous f) (hgc : Continuous g) (hg : Function.Surjective g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  have hX : IsCompact (Set.univ : Set X) := by
    rw [← Set.range_eq_univ.mpr hf]
    exact isCompact_range hfc
  letI : CompactSpace X := ⟨hX⟩
  have hd : Continuous (descend f g hf) := descend_continuous f g hf
    (hfc.isClosedMap.isQuotientMap hfc hf) hgc (fun a b => (hfg a b).mp)
  let e : X ≃ Y := Equiv.ofBijective (descend f g hf)
    ⟨descend_injective f g hf (fun a b => (hfg a b).mpr),
      descend_surjective f g hf (fun a b => (hfg a b).mp) hg⟩
  exact Equiv.toHomeomorphOfContinuousClosed e hd hd.isClosedMap

@[simp] theorem homeomorph_apply (hfc : Continuous f) (hgc : Continuous g)
    (hg : Function.Surjective g) (hfg : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    homeomorph f g hf hfc hgc hg hfg (f a) = g a :=
  descend_apply f g hf (fun a b => (hfg a b).mp) a

end Wikipedia.HopfProblem.CuspHoneycombHexagon.CommonFibres
