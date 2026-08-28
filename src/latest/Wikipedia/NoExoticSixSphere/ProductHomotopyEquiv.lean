import Wikipedia.NoExoticSixSphere.ProductHomotopyConnectivity
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The actual native homotopy group of a product

Pairing generalized loops supplies the inverse to the two projected maps.
These maps respect Mathlib's concatenation group law. This computes a product
of actual native homotopy groups, with both projections retained explicitly.
-/

noncomputable section

namespace NoExoticSixSphere.HigherHomotopy

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

def productGenLoop (p : GenLoop N X x) (q : GenLoop N Y y) : GenLoop N (X × Y) (x, y) :=
  ⟨p.val.prodMk q.val, fun a ha ↦ Prod.ext (p.property a ha) (q.property a ha)⟩

theorem genLoopMap_fst_product (p : GenLoop N X x) (q : GenLoop N Y y) :
    genLoopMap (z := x) ContinuousMap.fst rfl (productGenLoop p q) = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  rfl

theorem genLoopMap_snd_product (p : GenLoop N X x) (q : GenLoop N Y y) :
    genLoopMap (z := y) ContinuousMap.snd rfl (productGenLoop p q) = q := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  rfl

theorem product_map_surjective : Function.Surjective
    (fun a : HomotopyGroup N (X × Y) (x, y) ↦
      (map (z := x) ContinuousMap.fst rfl a, map (z := y) ContinuousMap.snd rfl a)) := by
  rintro ⟨a, b⟩
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q =>
      refine ⟨Quotient.mk' (productGenLoop p q), ?_⟩
      apply Prod.ext
      · exact congrArg (fun z : GenLoop N X x ↦ (Quotient.mk' z : HomotopyGroup N X x))
          (genLoopMap_fst_product p q)
      · exact congrArg (fun z : GenLoop N Y y ↦ (Quotient.mk' z : HomotopyGroup N Y y))
          (genLoopMap_snd_product p q)

variable [DecidableEq N] [Nonempty N]

def productMulEquiv : HomotopyGroup N (X × Y) (x, y) ≃*
    (HomotopyGroup N X x × HomotopyGroup N Y y) where
  toEquiv := Equiv.ofBijective
    (fun a ↦ (map (z := x) ContinuousMap.fst rfl a, map (z := y) ContinuousMap.snd rfl a))
    ⟨product_map_injective x y, product_map_surjective⟩
  map_mul' a b := Prod.ext (map_mul ContinuousMap.fst rfl a b)
    (map_mul ContinuousMap.snd rfl a b)

theorem productMulEquiv_fst (a : HomotopyGroup N (X × Y) (x, y)) :
    (productMulEquiv a).1 = map (z := x) ContinuousMap.fst rfl a := rfl

theorem productMulEquiv_snd (a : HomotopyGroup N (X × Y) (x, y)) :
    (productMulEquiv a).2 = map (z := y) ContinuousMap.snd rfl a := rfl

end NoExoticSixSphere.HigherHomotopy
