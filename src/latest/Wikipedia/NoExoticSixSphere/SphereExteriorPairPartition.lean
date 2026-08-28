import Wikipedia.NoExoticSixSphere.SphereExteriorCapEquiv
import Wikipedia.NoExoticSixSphere.ImmersedSphereDoublePoints

/-!
# The four actual exterior-cap types of ordered double point

When every double point lies outside the neck, its two source points have
unique northern or southern labels. This gives an exact disjoint-sum
partition of the original ordered-pair type, with a forgetful inverse.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*}

def capPairs (K : Sphere 3 → M) (A B : Set (Sphere 3)) : Type :=
  {p : SphereSelfIntersections.pairs K // p.val.1 ∈ A ∧ p.val.2 ∈ B}

def capPairSwapEquiv (K : Sphere 3 → M) (A B : Set (Sphere 3)) :
    capPairs K A B ≃ capPairs K B A where
  toFun p := ⟨SphereSelfIntersections.swap K p.val, p.property.2, p.property.1⟩
  invFun p := ⟨SphereSelfIntersections.swap K p.val, p.property.2, p.property.1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

abbrev exteriorPairSum (K : Sphere 3 → M) :=
  (capPairs K northExterior northExterior ⊕ capPairs K northExterior southExterior) ⊕
    (capPairs K southExterior northExterior ⊕ capPairs K southExterior southExterior)

def exteriorPairForget (K : Sphere 3 → M) : exteriorPairSum K → SphereSelfIntersections.pairs K
  | .inl (.inl p) => p.val
  | .inl (.inr p) => p.val
  | .inr (.inl p) => p.val
  | .inr (.inr p) => p.val

def exteriorPairClassify (K : Sphere 3 → M)
    (hout : ∀ p : SphereSelfIntersections.pairs K,
      p.val.1 ∉ neckRegion ∧ p.val.2 ∉ neckRegion)
    (p : SphereSelfIntersections.pairs K) : exteriorPairSum K := by
  classical
  exact if hx : p.val.1 ∈ northExterior then
    if hy : p.val.2 ∈ northExterior then .inl (.inl ⟨p, hx, hy⟩)
    else .inl (.inr ⟨p, hx, (exterior_cover (hout p).2).resolve_left hy⟩)
  else if hy : p.val.2 ∈ northExterior then
    .inr (.inl ⟨p, (exterior_cover (hout p).1).resolve_left hx, hy⟩)
  else .inr (.inr ⟨p, (exterior_cover (hout p).1).resolve_left hx,
    (exterior_cover (hout p).2).resolve_left hy⟩)

theorem exteriorPair_forget_classify (K : Sphere 3 → M)
    (hout : ∀ p : SphereSelfIntersections.pairs K,
      p.val.1 ∉ neckRegion ∧ p.val.2 ∉ neckRegion)
    (p : SphereSelfIntersections.pairs K) :
    exteriorPairForget K (exteriorPairClassify K hout p) = p := by
  classical
  unfold exteriorPairClassify
  split_ifs <;> rfl

theorem exteriorPair_classify_forget (K : Sphere 3 → M)
    (hout : ∀ p : SphereSelfIntersections.pairs K,
      p.val.1 ∉ neckRegion ∧ p.val.2 ∉ neckRegion)
    (p : exteriorPairSum K) :
    exteriorPairClassify K hout (exteriorPairForget K p) = p := by
  classical
  rcases p with (p | p) | (p | p)
  · simp [exteriorPairForget, exteriorPairClassify, p.property.1, p.property.2]
    rfl
  · have hy : p.val.val.2 ∉ northExterior := fun h ↦
      disjoint_left.mp disjoint_exterior h p.property.2
    simp [exteriorPairForget, exteriorPairClassify, p.property.1, hy]
    rfl
  · have hx : p.val.val.1 ∉ northExterior := fun h ↦
      disjoint_left.mp disjoint_exterior h p.property.1
    simp [exteriorPairForget, exteriorPairClassify, hx, p.property.2]
    rfl
  · have hx : p.val.val.1 ∉ northExterior := fun h ↦
      disjoint_left.mp disjoint_exterior h p.property.1
    have hy : p.val.val.2 ∉ northExterior := fun h ↦
      disjoint_left.mp disjoint_exterior h p.property.2
    simp [exteriorPairForget, exteriorPairClassify, hx, hy]
    rfl

def exteriorPairPartition (K : Sphere 3 → M)
    (hout : ∀ p : SphereSelfIntersections.pairs K,
      p.val.1 ∉ neckRegion ∧ p.val.2 ∉ neckRegion) :
    SphereSelfIntersections.pairs K ≃ exteriorPairSum K where
  toFun := exteriorPairClassify K hout
  invFun := exteriorPairForget K
  left_inv := exteriorPair_forget_classify K hout
  right_inv := exteriorPair_classify_forget K hout

end NoExoticSixSphere.SphereSumNeck
