import Wikipedia.NoExoticSixSphere.CompactSupportMayerVietorisLeft

/-!
# The degree-zero start of the actual compact-support Mayer--Vietoris sequence

The original small-cochain row is degreewise injective at its first
term. Since the cochain complex has no incoming differential in degree
zero, this gives injectivity on original degree-zero relative
cohomology. Genuine supported kernel representatives then give the
degree-zero injectivity on compact-support cohomology as well.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)

/-- The original relative cohomological first map is injective in degree zero. -/
theorem firstMap_zero_injective : Function.Injective (firstMap U V hU hV 0) := by
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (smallSequence U V)).mp (smallSequence_shortExact U V) 0
  let : Mono (((smallSequence U V).f).f 0) := hd.mono_f
  let : Mono (HomologicalComplex.homologyMap (smallSequence U V).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (smallSequence U V).f 0
      (by intro i; simp)
  have hi : Function.Injective (smallFirstMap U V 0) :=
    (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap (smallSequence U V).f 0)).mp
      inferInstance
  intro a b hab
  apply (smallUnionEquiv U V hU hV 0).injective
  apply hi
  exact (middleEquiv U V 0).injective hab

end NoExoticSixSphere.RelativeModTwoMayerVietoris

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)

include hK hL in
/-- Original intersection-support extension is jointly injective in degree zero. -/
theorem intersectionMap_zero_injective : Function.Injective (intersectionMap K L 0) := by
  intro a b hab
  apply (interComplementEquiv K L 0).injective
  apply RelativeModTwoMayerVietoris.firstMap_zero_injective Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl
  exact (firstMap_interComplement K L hK hL 0 a).trans
    (hab.trans (firstMap_interComplement K L hK hL 0 b).symm)

end NoExoticSixSphere.SupportedModTwoCohomology

namespace NoExoticSixSphere.CompactSupportMayerVietoris

open CompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V)

/-- An original degree-zero overlap class killed in both open sets is zero. -/
theorem eq_zero_of_firstMap_zero (a : Cohomology (U ∩ V : Set X) 0)
    (ha : firstMap U V hU hV 0 a = 0) : a = 0 := by
  obtain ⟨A, B, hAU, hBV, d, hd, he⟩ :=
    exists_supported_kernel_representative U V hU hV 0 a ha
  have hd0 : d = 0 := SupportedModTwoCohomology.intersectionMap_zero_injective
    (A : Set X) (B : Set X) A.isCompact.isClosed B.isCompact.isClosed
    (hd.trans (SupportedModTwoCohomology.intersectionMap (A : Set X) (B : Set X) 0).map_zero.symm)
  exact he.symm.trans
    ((congrArg (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
      (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) 0) hd0).trans
      (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
        (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) 0).map_zero)

/-- The initial map in the genuine compact-support sequence is injective. -/
theorem firstMap_zero_injective : Function.Injective (firstMap U V hU hV 0) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply eq_zero_of_firstMap_zero U V hU hV (a - b)
  exact ((firstMap U V hU hV 0).map_sub a b).trans (sub_eq_zero.mpr hab)

end NoExoticSixSphere.CompactSupportMayerVietoris
