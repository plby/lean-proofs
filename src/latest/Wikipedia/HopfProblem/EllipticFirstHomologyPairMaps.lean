import Wikipedia.HopfProblem.EllipticFirstHomologyGroups

/-!
# Paired elliptic translation maps

Lemma 7.19(b) uses the common kernel of the two elliptic lattice maps.
Here that kernel is computed for the maps into the actual surface and
filling loop-group abelianizations. The main-twist coordinate formula
uses the marking in which each affine generator is the first basis vector.
No Mayer--Vietoris or singular-homology identification is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

/-- The source's primitive common vanishing vector `ν₀ = -û-ŵ+δ̂`. -/
def pairVanishingVector : Lattice := ![0, -1, -1, 1]

/-- The intersection is an exact integral rank-one lattice. -/
theorem coinvariantKernels_intersection :
    LinearMap.ker (coinvariantMap .three) ⊓ LinearMap.ker (coinvariantMap .four) =
      ℤ ∙ pairVanishingVector := by
  ext w
  constructor
  · rintro ⟨hthree, hfour⟩
    have h0 : w 0 = 0 := congrFun hthree 0
    have h1 : 2 * w 1 + w 2 + 3 * w 3 = 0 := congrFun hthree 1
    have h2 : w 1 + w 2 + 2 * w 3 = 0 := congrFun hfour 1
    apply Submodule.mem_span_singleton.mpr
    refine ⟨w 3, ?_⟩
    ext i
    fin_cases i <;> simp [pairVanishingVector] <;> omega
  · intro hw
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hthree : coinvariantMap .three pairVanishingVector = 0 := by decide
    have hfour : coinvariantMap .four pairVanishingVector = 0 := by decide
    constructor
    · change coinvariantMap .three (n • pairVanishingVector) = 0
      rw [map_smul, hthree, smul_zero]
    · change coinvariantMap .four (n • pairVanishingVector) = 0
      rw [map_smul, hfour, smul_zero]

/-- The two actual surface translation maps, with the sign convention in `α₁`. -/
def surfacePairTranslation (p₁ : FixedPeriod .three) (p₂ : FixedPeriod .four)
    (v₁ v₂ : Lattice) (h₁ : AdmissibleTwist .three v₁) (h₂ : AdmissibleTwist .four v₂)
    (y₁ y₂ : RealCoordinates) : Lattice →ₗ[ℤ]
      SurfaceAbelianization .three p₁ v₁ h₁ y₁ × SurfaceAbelianization .four p₂ v₂ h₂ y₂ :=
  (surfaceAbelianTranslation .three p₁ v₁ h₁ y₁).prod
    (-surfaceAbelianTranslation .four p₂ v₂ h₂ y₂)

theorem surfacePairTranslation_ker (p₁ : FixedPeriod .three) (p₂ : FixedPeriod .four)
    (v₁ v₂ : Lattice) (h₁ : AdmissibleTwist .three v₁) (h₂ : AdmissibleTwist .four v₂)
    (y₁ y₂ : RealCoordinates) :
    LinearMap.ker (surfacePairTranslation p₁ p₂ v₁ v₂ h₁ h₂ y₁ y₂) =
      ℤ ∙ pairVanishingVector := by
  rw [surfacePairTranslation, LinearMap.ker_prod, LinearMap.ker_neg,
    surfaceAbelianTranslation_ker, surfaceAbelianTranslation_ker,
    ← coinvariantMap_ker_eq_range, ← coinvariantMap_ker_eq_range,
    coinvariantKernels_intersection]

/-- The paired actual filling translation map used by the two elliptic caps. -/
def fillingPairTranslation (v₁ v₂ : Lattice)
    (h₁ : AdmissibleTwist .three v₁) (h₂ : AdmissibleTwist .four v₂)
    (y₁ y₂ : RealCoordinates) : Lattice →ₗ[ℤ]
      FillingAbelianization .three v₁ h₁ y₁ × FillingAbelianization .four v₂ h₂ y₂ :=
  (fillingAbelianTranslation .three v₁ h₁ y₁).prod
    (-fillingAbelianTranslation .four v₂ h₂ y₂)

theorem fillingPairTranslation_ker (v₁ v₂ : Lattice)
    (h₁ : AdmissibleTwist .three v₁) (h₂ : AdmissibleTwist .four v₂)
    (y₁ y₂ : RealCoordinates) :
    LinearMap.ker (fillingPairTranslation v₁ v₂ h₁ h₂ y₁ y₂) =
      ℤ ∙ pairVanishingVector := by
  rw [fillingPairTranslation, LinearMap.ker_prod, LinearMap.ker_neg,
    fillingAbelianTranslation_ker, fillingAbelianTranslation_ker,
    ← coinvariantMap_ker_eq_range, ← coinvariantMap_ker_eq_range,
    coinvariantKernels_intersection]

/-- The main paired surface map in the two actual rank-two markings. -/
theorem mainSurfacePairTranslation_coordinates (p₁ : FixedPeriod .three)
    (p₂ : FixedPeriod .four) (y₁ y₂ : RealCoordinates) (w : Lattice) :
    let z := surfacePairTranslation p₁ p₂ Kind.three.twist Kind.four.twist
      (mainTwist_admissible .three) (mainTwist_admissible .four) y₁ y₂ w
    (mainSurfaceAbelianizationEquiv .three p₁ y₁ z.1,
      mainSurfaceAbelianizationEquiv .four p₂ y₂ z.2) =
        (![3 * γ w, psiOne w], ![4 * γ w, -psiTwo w]) := by
  change (mainSurfaceAbelianizationEquiv .three p₁ y₁
      (surfaceAbelianTranslation .three p₁ Kind.three.twist
        (mainTwist_admissible .three) y₁ w),
    mainSurfaceAbelianizationEquiv .four p₂ y₂
      (-surfaceAbelianTranslation .four p₂ Kind.four.twist
        (mainTwist_admissible .four) y₂ w)) = _
  rw [map_neg, mainSurfaceAbelianizationEquiv_translation,
    mainSurfaceAbelianizationEquiv_translation]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [mainAbelianSign, Kind.order, psi]
  · ext i
    fin_cases i <;> simp [mainAbelianSign, Kind.order, psi]

/-- The same explicit integral map holds for the actual fillings. -/
theorem mainFillingPairTranslation_coordinates (y₁ y₂ : RealCoordinates) (w : Lattice) :
    let z := fillingPairTranslation Kind.three.twist Kind.four.twist
      (mainTwist_admissible .three) (mainTwist_admissible .four) y₁ y₂ w
    (mainFillingAbelianizationEquiv .three y₁ z.1,
      mainFillingAbelianizationEquiv .four y₂ z.2) =
        (![3 * γ w, psiOne w], ![4 * γ w, -psiTwo w]) := by
  change (mainFillingAbelianizationEquiv .three y₁
      (fillingAbelianTranslation .three Kind.three.twist
        (mainTwist_admissible .three) y₁ w),
    mainFillingAbelianizationEquiv .four y₂
      (-fillingAbelianTranslation .four Kind.four.twist
        (mainTwist_admissible .four) y₂ w)) = _
  rw [map_neg, mainFillingAbelianizationEquiv_translation,
    mainFillingAbelianizationEquiv_translation]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [mainAbelianSign, Kind.order, psi]
  · ext i
    fin_cases i <;> simp [mainAbelianSign, Kind.order, psi]

end Wikipedia.HopfProblem.Elliptic
