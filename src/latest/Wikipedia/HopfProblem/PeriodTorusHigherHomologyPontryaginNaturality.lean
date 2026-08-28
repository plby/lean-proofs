import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductNaturality

/-!
# Naturality of the actual Pontryagin products

Every equality below is induced by the actual continuous addition maps and
the proved naturality of the actual singular cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable {G H : Type} [TopologicalSpace G] [TopologicalSpace H]
  [AddCommGroup G] [AddCommGroup H] [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]

/-- An actual continuous additive map preserves the actual Pontryagin product. -/
theorem product_natural (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y)
    (n : ℕ) (a : SingularHomology G 1) (b : SingularHomology G n) :
    singularHomologyMap f (n + 1) (product G n a b) =
      product H n (singularHomologyMap f 1 a) (singularHomologyMap f n b) :=
  (LinearMap.congr_fun (addition_homology_natural f hf (n + 1))
    (crossProductHomology G G n a b)).trans
      (congrArg (singularHomologyMap (additionMap H) (n + 1))
        (crossProductHomology_natural f f n a b))

theorem product_natural_addHom (f : G →ₜ+ H) (n : ℕ)
    (a : SingularHomology G 1) (b : SingularHomology G n) :
    singularHomologyMap f.toContinuousMap (n + 1) (product G n a b) =
      product H n (singularHomologyMap f.toContinuousMap 1 a)
        (singularHomologyMap f.toContinuousMap n b) :=
  product_natural f.toContinuousMap f.map_add n a b

/-- Naturality of the actual right-associated triple product. -/
theorem tripleProduct_natural (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y)
    (a b c : SingularHomology G 1) :
    singularHomologyMap f 3 (tripleProduct G a b c) =
      tripleProduct H (singularHomologyMap f 1 a)
        (singularHomologyMap f 1 b) (singularHomologyMap f 1 c) := by
  change singularHomologyMap f 3 (product G 2 a (product G 1 b c)) =
    product H 2 (singularHomologyMap f 1 a)
      (product H 1 (singularHomologyMap f 1 b) (singularHomologyMap f 1 c))
  rw [product_natural f hf 2, product_natural f hf 1]

theorem tripleProduct_natural_addHom (f : G →ₜ+ H) (a b c : SingularHomology G 1) :
    singularHomologyMap f.toContinuousMap 3 (tripleProduct G a b c) =
      tripleProduct H (singularHomologyMap f.toContinuousMap 1 a)
        (singularHomologyMap f.toContinuousMap 1 b)
        (singularHomologyMap f.toContinuousMap 1 c) :=
  tripleProduct_natural f.toContinuousMap f.map_add a b c

variable (G) in
/-- The right-associated product is the pushforward of the nested actual cross product. -/
theorem tripleProduct_eq_cross (a b c : SingularHomology G 1) :
    tripleProduct G a b c =
      singularHomologyMap (rightAdditionMap G) 3
        (crossProductHomology G (G × G) 2 a (crossProductHomology G G 1 b c)) := by
  have h := crossProductHomology_natural (ContinuousMap.id G) (additionMap G) 2 a
    (crossProductHomology G G 1 b c)
  change singularHomologyMap ((ContinuousMap.id G).prodMap (additionMap G)) 3
      (crossProductHomology G (G × G) 2 a (crossProductHomology G G 1 b c)) =
    crossProductHomology G G 2 (singularHomologyMap (ContinuousMap.id G) 1 a)
      (singularHomologyMap (additionMap G) 2 (crossProductHomology G G 1 b c)) at h
  rw [singularHomologyMap_id, LinearMap.id_apply] at h
  calc
    tripleProduct G a b c = singularHomologyMap (additionMap G) 3
        (crossProductHomology G G 2 a
          (singularHomologyMap (additionMap G) 2 (crossProductHomology G G 1 b c))) := rfl
    _ = singularHomologyMap (additionMap G) 3
        (singularHomologyMap ((ContinuousMap.id G).prodMap (additionMap G)) 3
          (crossProductHomology G (G × G) 2 a (crossProductHomology G G 1 b c))) :=
      congrArg (singularHomologyMap (additionMap G) 3) h.symm
    _ = _ := (LinearMap.congr_fun
      (singularHomologyMap_comp ((ContinuousMap.id G).prodMap (additionMap G))
        (additionMap G) 3)
      (crossProductHomology G (G × G) 2 a (crossProductHomology G G 1 b c))).symm

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
