import Wikipedia.HopfProblem.DegreeCollapseIntegralClosedBallCap

/-!
# Actual cap bijectivity from a primitive supported class

In an actual cyclic homology group, a generating class has value one or
minus one in every integral marking. Evaluation on that class is therefore
an isomorphism of the actual integral dual. Universal coefficients and
the proved cap-augmentation identity turn this into bijectivity of the
original top cap. No preferred sign of the class is needed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralPrimitiveCap

open FirstHurewicz NoExoticSixSphere

variable {H : Type} [AddCommGroup H] [Module ℤ H]

theorem marking_generator_unit (e : H ≃ₗ[ℤ] ℤ) (c : H)
    (hc : ∀ a : H, ∃ k : ℤ, k • c = a) : e c = 1 ∨ e c = -1 := by
  obtain ⟨k, hk⟩ := hc (e.symm 1)
  have he := congrArg e hk
  rw [map_zsmul, LinearEquiv.apply_symm_apply] at he
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := k)
  simpa only [zsmul_eq_mul, Int.cast_id, mul_comm] using he

theorem exists_marking_generator (e : H ≃ₗ[ℤ] ℤ) (c : H)
    (hc : ∀ a : H, ∃ k : ℤ, k • c = a) : ∃ m : H ≃ₗ[ℤ] ℤ, m c = 1 := by
  rcases marking_generator_unit e c hc with he | he
  · exact ⟨e, he⟩
  · refine ⟨e.trans (LinearEquiv.neg ℤ), ?_⟩
    change -(e c) = 1
    rw [he]
    decide

/-- Evaluation on any original primitive is bijective on the actual integer dual. -/
theorem functional_bijective (e : H ≃ₗ[ℤ] ℤ) (c : H)
    (hc : ∀ a : H, ∃ k : ℤ, k • c = a) :
    Function.Bijective (fun φ : H →ₗ[ℤ] ℤ => φ c) := by
  obtain ⟨m, hm⟩ := exists_marking_generator e c hc
  have hmc : m.symm 1 = c := m.injective ((m.apply_symm_apply 1).trans hm.symm)
  let C := IntegralClosedBallCohomology.cyclicFunctionalEquiv m
  have he (φ : H →ₗ[ℤ] ℤ) : C φ = φ c :=
    (IntegralClosedBallCohomology.cyclicFunctionalEquiv_apply m φ).trans (congrArg φ hmc)
  constructor
  · intro φ ψ h
    exact C.injective ((he φ).trans (h.trans (he ψ).symm))
  · intro k
    exact ⟨C.symm k, (he _).symm.trans (C.apply_symm_apply k)⟩

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]

/-- Original top cap is bijective for an actual primitive cyclic supported class. -/
theorem topCap_bijective (K : Set X) (p : ℕ)
    [Module.Projective ℤ (RelativeSingularHomology.Homology Kᶜ p)]
    (e : RelativeSingularHomology.Homology Kᶜ (p + 1) ≃ₗ[ℤ] ℤ)
    (c : RelativeSingularHomology.Homology Kᶜ (p + 1))
    (hc : ∀ a : RelativeSingularHomology.Homology Kᶜ (p + 1), ∃ k : ℤ, k • c = a) :
    Function.Bijective
      (IntegralCompactSupportCap.componentMap K (q := 0) (Nat.add_zero (p + 1)) c) := by
  let A : (singularComplex X).homology 0 ≃ₗ[ℤ] ℤ :=
    CoefficientChains.connectedZeroEquiv (ModuleCat.of ℤ ℤ) X
  let F : IntegralSupportedCohomology.Cohomology K (p + 1) ≃ₗ[ℤ]
      (RelativeSingularHomology.Homology Kᶜ (p + 1) →ₗ[ℤ] ℤ) :=
    RelativeIntegralCap.evaluationSuccEquiv Kᶜ p
  have hF : Function.Bijective
      (fun a : IntegralSupportedCohomology.Cohomology K (p + 1) => F a c) :=
    (functional_bijective e c hc).comp F.bijective
  have he (a : IntegralSupportedCohomology.Cohomology K (p + 1)) :
      A (IntegralCompactSupportCap.componentMap K (q := 0) (Nat.add_zero (p + 1)) c a) = F a c :=
    RelativeIntegralCap.augmentation_capProduct Kᶜ (p + 1) a c
  constructor
  · intro a b hab
    exact hF.1 ((he a).symm.trans ((congrArg A hab).trans (he b)))
  · intro b
    obtain ⟨a, ha⟩ := hF.2 (A b)
    exact ⟨a, A.injective ((he a).trans ha)⟩

open SupportedRelativeHomology

/-- Primitivity is stated on the original point evaluations of the actual supported class. -/
def IsPrimitiveOn (K : Set X) (d : ℕ) (c : Homology (ModuleCat.of ℤ ℤ) K d) : Prop :=
  ∀ (x : X) (hx : x ∈ K) (a : Homology (ModuleCat.of ℤ ℤ) {x} d),
    ∃ k : ℤ, k • evaluate (ModuleCat.of ℤ ℤ) K x hx d c = a

omit [PathConnectedSpace X] in
theorem generates_of_evaluate_injective (K : Set X) (d : ℕ)
    (c : Homology (ModuleCat.of ℤ ℤ) K d) (hc : IsPrimitiveOn K d c)
    (x : X) (hx : x ∈ K) (hi : Function.Injective (evaluate (ModuleCat.of ℤ ℤ) K x hx d)) :
    ∀ a : Homology (ModuleCat.of ℤ ℤ) K d, ∃ k : ℤ, k • c = a := by
  intro a
  obtain ⟨k, hk⟩ := hc x hx (evaluate (ModuleCat.of ℤ ℤ) K x hx d a)
  exact ⟨k, hi ((map_zsmul (evaluate (ModuleCat.of ℤ ℤ) K x hx d) k c).trans hk)⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralPrimitiveCap

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap

open TopologicalSpace FirstHurewicz NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] {p q d : ℕ}

/-- Bijective caps on a cofinal family of original compact supports detect the actual limit cap. -/
theorem withClasses_bijective_of_cofinal (h : p + q = d)
    (c : ∀ K : Compacts X, Homology (ModuleCat.of ℤ ℤ) (K : Set X) d)
    (hc : ∀ (K L : Compacts X) (hKL : K ≤ L), restrict (ModuleCat.of ℤ ℤ) hKL d (c L) = c K)
    (hB : ∀ K : Compacts X, ∃ L : Compacts X, K ≤ L ∧
      Function.Bijective (componentMap (L : Set X) h (c L))) :
    Function.Bijective (withClasses h c hc) := by
  have hext (K L : Compacts X) (hKL : K ≤ L) (a : Component X p K) :
      componentMap (L : Set X) h (c L) (transition X p K L hKL a) =
        componentMap (K : Set X) h (c K) a :=
    (componentMap_extend hKL h (c L) a).trans
      (congrArg (fun z => componentMap (K : Set X) h z a) (hc K L hKL))
  constructor
  · intro a b hab
    obtain ⟨K, a, rfl⟩ := exists_representative X p a
    obtain ⟨L, b, rfl⟩ := exists_representative X p b
    have hab' := (withClasses_of h c hc K a).symm.trans
      (hab.trans (withClasses_of h c hc L b))
    obtain ⟨B, hBKL, hi, _⟩ := hB (K ⊔ L)
    have hK : K ≤ B := le_sup_left.trans hBKL
    have hL : L ≤ B := le_sup_right.trans hBKL
    have he : transition X p K B hK a = transition X p L B hL b :=
      hi ((hext K B hK a).trans (hab'.trans (hext L B hL b).symm))
    exact (of_transition X p hK a).symm.trans
      ((congrArg (of X p B) he).trans (of_transition X p hL b))
  · intro b
    obtain ⟨K, _, _, hs⟩ := hB ⊥
    obtain ⟨a, ha⟩ := hs b
    exact ⟨of X p K a, (withClasses_of h c hc K a).trans ha⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap
