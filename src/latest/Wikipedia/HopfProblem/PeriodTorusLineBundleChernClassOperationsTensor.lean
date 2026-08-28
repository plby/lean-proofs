import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassOperations
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreTensor

/-!
# Canonical Chern additivity with the actual fibre tensor identifications

The sum-form factor is exactly the proved pointwise product factor.
Its native first Chern class is therefore the sum of the two classes.
The tensor compatibility statement retains the existing actual fibre
tensor equivalences and their full coordinate-change and local-chart
identities. It does not introduce a generic topological tensor-bundle
construction or assume a tensor identification as a hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusTypeOneOne PeriodTorusLineBundleChernLog

private theorem factor_eq_of_values {p : PeriodDomain} {F G : FactorOfAutomorphy p}
    (h : ∀ l z, F.factor l z = G.factor l z) : F = G := by
  cases F
  cases G
  congr 1
  funext l z
  exact h l z

variable (p : PeriodDomain) (E F : Fin 6 → ℤ)
  (hE : IsTypeOneOne (tangentForm p E)) (hF : IsTypeOneOne (tangentForm p F))

/-- Equality of the actual bundled factors, not merely a chosen cohomology presentation. -/
theorem integralFactor_eq_factorProduct :
    integralFactor p (E + F) (integralType_add p E F hE hF) =
      factorProduct (integralFactor p E hE) (integralFactor p F hF) := by
  apply factor_eq_of_values
  exact integralFactor_add_coefficients p E F hE hF

/-- Native first-Chern additivity for the canonical sum-form bundle. -/
theorem firstChernClass_integral_add :
    firstChernClass (integralFactor p (E + F) (integralType_add p E F hE hF)) =
      firstChernClass (integralFactor p E hE) + firstChernClass (integralFactor p F hF) := by
  rw [integralFactor_eq_factorProduct p E F hE hF, firstChernClass_factorProduct]

/-- The class addition accompanies the actual fibre tensor map and its original atlas identities. -/
theorem firstChernClass_integral_add_tensor_data :
    (firstChernClass (integralFactor p (E + F) (integralType_add p E F hE hF)) =
      firstChernClass (integralFactor p E hE) + firstChernClass (integralFactor p F hF)) ∧
    (∀ i j b : p.Torus,
      (Core.fibreTensorEquiv p E F hE hF b).toLinearMap ∘ₗ
          TensorProduct.map
            ((Core.data (integralFactor p E hE)).core.coordChange i j b).toLinearMap
            ((Core.data (integralFactor p F hF)).core.coordChange i j b).toLinearMap =
        ((Core.data (integralFactor p (E + F) (integralType_add p E F hE hF))).core.coordChange
            i j b).toLinearMap ∘ₗ (Core.fibreTensorEquiv p E F hE hF b).toLinearMap) ∧
    (∀ i b : p.Torus, b ∈ Core.baseSet p i →
      ((Core.data (integralFactor p (E + F)
          (integralType_add p E F hE hF))).core.localTriv i).linearMapAt ℂ b ∘ₗ
          (Core.fibreTensorEquiv p E F hE hF b).toLinearMap =
        (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
          TensorProduct.map
            (((Core.data (integralFactor p E hE)).core.localTriv i).linearMapAt ℂ b)
            (((Core.data (integralFactor p F hF)).core.localTriv i).linearMapAt ℂ b)) :=
  ⟨firstChernClass_integral_add p E F hE hF,
    Core.fibreTensorEquiv_coordChange p E F hE hF,
    Core.fibreTensorEquiv_localTriv p E F hE hF⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
