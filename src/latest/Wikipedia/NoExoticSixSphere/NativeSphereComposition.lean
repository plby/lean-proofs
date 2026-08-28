import Wikipedia.NoExoticSixSphere.CubicalSuspensionProductMap

/-!
# Native sphere-map composition and exact product-suspension naturality

Composition uses the actual based sphere maps and the original native
postcomposition homomorphism. Product suspension preserves this
composition exactly, including the compactification point. Its native
homomorphism therefore commutes with postcomposition by those maps.
-/

noncomputable section

open scoped Topology OnePoint

namespace NoExoticSixSphere.SphereComposition

open SmoothCube CubicalSphereSuspension

abbrev Based (m n : ℕ) := BasedMap m (Sphere n) (spherePole n)

def comp {l m n : ℕ} (f : Based m n) (g : Based l m) : Based l n :=
  ⟨f.val.comp g.val, (congrArg f.val g.property).trans f.property⟩

def mapHom {m n : ℕ} (f : Based m n) (d : ℕ) [NeZero d] :
    π_ d (Sphere m) (spherePole m) →* π_ d (Sphere n) (spherePole n) :=
  HigherHomotopy.mapMonoidHom (N := Fin d) f.val f.property

theorem mapHom_sphereClass {l m n : ℕ} [NeZero l] (f : Based m n) (g : Based l m) :
    mapHom f l (sphereClass g) = sphereClass (comp f g) := rfl

theorem compactMap_comp {l m n : ℕ} (f : Based m n) (g : Based l m)
    (x : OnePoint (EuclideanSpace ℝ (Fin l))) :
    compactMap (comp f g) x = compactMap f (compactMap g x) := by
  change (euclideanOnePointSphere n).symm (f.val (g.val (euclideanOnePointSphere l x))) =
    (euclideanOnePointSphere n).symm (f.val (euclideanOnePointSphere m
      ((euclideanOnePointSphere m).symm (g.val (euclideanOnePointSphere l x)))))
  rw [Homeomorph.apply_symm_apply]

theorem productBasedMap_comp {l m n : ℕ} (f : Based m n) (g : Based l m) :
    productBasedMap (comp f g) = comp (productBasedMap f) (productBasedMap g) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨p, hp⟩ := OnePointProduct.map_surjective ((sphereHomeomorph l).symm z)
  have hz : z = sphereHomeomorph l (OnePointProduct.map p) := by
    rw [hp, Homeomorph.apply_symm_apply]
  rw [hz]
  change SuspensionProductComparison.productSphereMap (compactMap (comp f g)) _
      (sphereHomeomorph l (OnePointProduct.map p)) =
    SuspensionProductComparison.productSphereMap (compactMap f) _
      (SuspensionProductComparison.productSphereMap (compactMap g) _
        (sphereHomeomorph l (OnePointProduct.map p)))
  rw [productSphereMap_product_formula, productSphereMap_product_formula,
    productSphereMap_product_formula, compactMap_comp]

theorem suspension_mapHom {m n : ℕ} (f : Based m n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere m) (spherePole m)) :
    hom d n (mapHom f d c) =
      mapHom (productBasedMap f) (d + 1) (hom d m c) := by
  obtain ⟨g, rfl⟩ := sphereClass_surjective (Nat.pos_of_neZero d) c
  rw [mapHom_sphereClass, hom_sphereClass, hom_sphereClass,
    mapHom_sphereClass, productBasedMap_comp]

end NoExoticSixSphere.SphereComposition
