import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionCylinder

/-!
# Pasting parametrized extension data on the closed cylinder base

The bottom and side form a closed cover. The inverse of the given closed
embedding on its range identifies side data with the original domain.
This proves continuity for an arbitrary parameter space and target.
-/

noncomputable section

universe u

open CategoryTheory unitInterval Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

variable {A B K Z : TopCat.{u}} (i : A ⟶ B) (hi : IsClosedEmbedding i)
    (F : C(B × K, Z)) (G : C(I × (A × K), Z))

def cylinderProductFunction (p : ↥(cylinderBase i) × K) : Z :=
  if ht : p.1.val.1 = 0 then F (p.1.val.2, p.2)
  else G (p.1.val.1,
    (hi.isEmbedding.toHomeomorph.symm ⟨p.1.val.2, p.1.property.resolve_left ht⟩, p.2))

theorem cylinderProductFunction_bottom (p : ↥(cylinderBase i) × K) (ht : p.1.val.1 = 0) :
    cylinderProductFunction i hi F G p = F (p.1.val.2, p.2) := by
  classical
  exact dif_pos ht

theorem cylinderProductFunction_side
    (h0 : ∀ a k, G (0, (a, k)) = F (i a, k))
    (p : ↥(cylinderBase i) × K) (hp : p.1.val.2 ∈ Set.range i) :
    cylinderProductFunction i hi F G p =
      G (p.1.val.1, (hi.isEmbedding.toHomeomorph.symm ⟨p.1.val.2, hp⟩, p.2)) := by
  classical
  by_cases ht : p.1.val.1 = 0
  · rw [cylinderProductFunction_bottom i hi F G p ht, ht, h0]
    exact congrArg (fun b ↦ F (b, p.2))
      (congrArg Subtype.val (hi.isEmbedding.toHomeomorph.apply_symm_apply ⟨p.1.val.2, hp⟩)).symm
  · exact dif_neg ht

theorem continuous_cylinderProductFunction
    (h0 : ∀ a k, G (0, (a, k)) = F (i a, k)) :
    Continuous (cylinderProductFunction i hi F G) := by
  let bot : Set (↥(cylinderBase i) × K) := {p | p.1.val.1 = 0}
  let side : Set (↥(cylinderBase i) × K) := {p | p.1.val.2 ∈ Set.range i}
  have hbot : IsClosed bot := isClosed_eq
    (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hside : IsClosed side := hi.isClosed_range.preimage
    (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))
  have hcover : bot ∪ side = univ := eq_univ_of_forall (fun p ↦ p.1.property)
  have cb : ContinuousOn (cylinderProductFunction i hi F G) bot :=
    (F.continuous.comp
      ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)).continuousOn.congr
          (fun p hp ↦ cylinderProductFunction_bottom i hi F G p hp)
  have cs : ContinuousOn (cylinderProductFunction i hi F G) side := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun p : side ↦
        G (p.val.1.val.1,
          (hi.isEmbedding.toHomeomorph.symm ⟨p.val.1.val.2, p.property⟩, p.val.2))) := by
      apply G.continuous.comp
      apply Continuous.prodMk
      · exact continuous_fst.comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
      · apply Continuous.prodMk
        · exact hi.isEmbedding.toHomeomorph.symm.continuous.comp
            ((continuous_snd.comp
              (continuous_subtype_val.comp
                (continuous_fst.comp continuous_subtype_val))).subtype_mk _)
        · exact continuous_snd.comp continuous_subtype_val
    exact hc.congr (fun p ↦ (cylinderProductFunction_side i hi F G h0 p.val p.property).symm)
  apply continuousOn_univ.mp
  rw [← hcover]
  exact cb.union_of_isClosed cs hbot hside

def cylinderProductMap (h0 : ∀ a k, G (0, (a, k)) = F (i a, k)) :
    C(↥(cylinderBase i) × K, Z) :=
  ⟨cylinderProductFunction i hi F G, continuous_cylinderProductFunction i hi F G h0⟩

theorem cylinderProductMap_bottom (h0 : ∀ a k, G (0, (a, k)) = F (i a, k)) (b : B) (k : K) :
    cylinderProductMap i hi F G h0 (cylinderBottom i b, k) = F (b, k) :=
  cylinderProductFunction_bottom i hi F G _ rfl

theorem cylinderProductMap_side (h0 : ∀ a k, G (0, (a, k)) = F (i a, k))
    (t : I) (a : A) (k : K) :
    cylinderProductMap i hi F G h0 (cylinderSide i (t, a), k) = G (t, (a, k)) := by
  change cylinderProductFunction i hi F G _ = _
  rw [cylinderProductFunction_side i hi F G h0 _ ⟨a, rfl⟩]
  exact congrArg (fun a' ↦ G (t, (a', k)))
    (hi.isEmbedding.toHomeomorph.symm_apply_apply a)

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
