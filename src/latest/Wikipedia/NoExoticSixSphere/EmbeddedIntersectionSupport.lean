import Wikipedia.NoExoticSixSphere.NativeTransverseSpherePairFiniteness

/-!
# Actual intersection pairs and inverse-image support for an embedded first sphere

If the first map is injective, the second source coordinate identifies
the original intersection-pair set with the literal inverse image of
the first image. The second map need not be injective: its distinct
source points are still counted separately. Native transversality then
proves that this actual support is finite.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.MapIntersections

variable {X Y Z : Type*}

/-- The original second source point, with its actual image-membership witness. -/
def sourcePoint (f : X → Z) (g : Y → Z) (a : pairs f g) : g ⁻¹' range f :=
  ⟨a.val.2, a.val.1, a.property⟩

/-- Injectivity of the first map is exactly what makes this original projection bijective. -/
theorem sourcePoint_bijective (f : X → Z) (g : Y → Z) (hf : Injective f) :
    Bijective (sourcePoint f g) := by
  constructor
  · intro a b hab
    have hy : a.val.2 = b.val.2 := congrArg Subtype.val hab
    have hx : f a.val.1 = f b.val.1 :=
      a.property.trans ((congrArg g hy).trans b.property.symm)
    exact Subtype.ext (Prod.ext (hf hx) hy)
  · rintro ⟨y, x, hxy⟩
    exact ⟨⟨(x, y), hxy⟩, rfl⟩

/-- The equivalence retains the original source projection in its forward direction. -/
def sourceEquiv (f : X → Z) (g : Y → Z) (hf : Injective f) : pairs f g ≃ g ⁻¹' range f :=
  Equiv.ofBijective (sourcePoint f g) (sourcePoint_bijective f g hf)

theorem sourceEquiv_apply (f : X → Z) (g : Y → Z) (hf : Injective f) (a : pairs f g) :
    (sourceEquiv f g hf a).val = a.val.2 := rfl

/-- Original source-pair cardinality is the cardinality of the literal inverse-image support. -/
theorem pairs_ncard_eq_preimage (f : X → Z) (g : Y → Z) (hf : Injective f) :
    (pairs f g).ncard = (g ⁻¹' range f).ncard := Set.ncard_congr' (sourceEquiv f g hf)

theorem parity_eq_preimage_count (f : X → Z) (g : Y → Z) (hf : Injective f) :
    parity f g = ((g ⁻¹' range f).ncard : ZMod 2) :=
  congrArg (fun n : ℕ => (n : ZMod 2)) (pairs_ncard_eq_preimage f g hf)

/-- Finiteness transfers through the proved original projection equivalence. -/
theorem finite_preimage_range_of_finite_pairs (f : X → Z) (g : Y → Z) (hf : Injective f)
    (hfin : (pairs f g).Finite) : (g ⁻¹' range f).Finite := by
  let := hfin.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv (pairs f g) (sourceEquiv f g hf))

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  [T2Space M]

/-- Native transversality makes the actual embedded-sphere pullback support finite. -/
theorem finite_preimage_range_of_nativeTransverse {f g : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) (hi : Injective f)
    (ht : ∀ x y, f x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) :
    (g ⁻¹' range f).Finite :=
  finite_preimage_range_of_finite_pairs f g hi (finite_pairs_of_nativeTransverse hf hg ht)

end NoExoticSixSphere.MapIntersections
