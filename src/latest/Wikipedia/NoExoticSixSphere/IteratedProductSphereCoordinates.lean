import Wikipedia.NoExoticSixSphere.NativeSphereComposition

/-!
# Exact coordinates for successive original product suspensions

Successive product suspensions prepend the specified cube coordinates.
The formulas hold on the whole compactification, including every
collapsed face, and retain the original based map at the last factor.
-/

noncomputable section

open scoped Topology unitInterval OnePoint

namespace NoExoticSixSphere.IteratedProductSphere

open SmoothCube SphereComposition CubicalSphereSuspension

def prefixCube (n : ℕ) : (q : ℕ) → (Fin q → I) → (Fin n → I) → (Fin (n + q) → I)
  | 0, _, v => v
  | q + 1, u, v => Fin.cons (u 0) (prefixCube n q (Fin.tail u) v)

def prefixSphere (n : ℕ) : (q : ℕ) → (Fin q → I) → Sphere n → Sphere (n + q)
  | 0, _, x => x
  | q + 1, u, x => sphereHomeomorph (n + q) (OnePointProduct.map
      (CubicalProductSuspension.clock (u 0),
        (euclideanOnePointSphere (n + q)).symm (prefixSphere n q (Fin.tail u) x)))

theorem prefixSphere_quotient (n q : ℕ) (u : Fin q → I) (v : Fin n → I) :
    prefixSphere n q u (SmoothCube.quotient n v) =
      SmoothCube.quotient (n + q) (prefixCube n q u v) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change sphereHomeomorph (n + q) (OnePointProduct.map
      (CubicalProductSuspension.clock (u 0),
        (euclideanOnePointSphere (n + q)).symm
          (prefixSphere n q (Fin.tail u) (SmoothCube.quotient n v)))) = _
    rw [ih]
    exact quotient_product (n + q) (Fin.cons (u 0) (prefixCube n q (Fin.tail u) v))

def iterate {m n : ℕ} (f : Based m n) : (q : ℕ) → Based (m + q) (n + q)
  | 0 => f
  | q + 1 => productBasedMap (iterate f q)

theorem productBasedMap_prefix {m n : ℕ} (f : Based m n) (t : I) (x : Sphere m) :
    (productBasedMap f).val (sphereHomeomorph m (OnePointProduct.map
      (CubicalProductSuspension.clock t, (euclideanOnePointSphere m).symm x))) =
      sphereHomeomorph n (OnePointProduct.map
        (CubicalProductSuspension.clock t, (euclideanOnePointSphere n).symm (f.val x))) := by
  change SuspensionProductComparison.productSphereMap (compactMap f) _ _ = _
  rw [productSphereMap_product_formula]
  change sphereHomeomorph n (OnePointProduct.map
    (CubicalProductSuspension.clock t, (euclideanOnePointSphere n).symm
      (f.val (euclideanOnePointSphere m ((euclideanOnePointSphere m).symm x))))) = _
  rw [Homeomorph.apply_symm_apply]

theorem iterate_prefix {m n : ℕ} (f : Based m n) (q : ℕ)
    (u : Fin q → I) (x : Sphere m) :
    (iterate f q).val (prefixSphere m q u x) = prefixSphere n q u (f.val x) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change (productBasedMap (iterate f q)).val (sphereHomeomorph (m + q)
      (OnePointProduct.map (CubicalProductSuspension.clock (u 0),
        (euclideanOnePointSphere (m + q)).symm (prefixSphere m q (Fin.tail u) x)))) = _
    rw [productBasedMap_prefix, ih]
    rfl

end NoExoticSixSphere.IteratedProductSphere
