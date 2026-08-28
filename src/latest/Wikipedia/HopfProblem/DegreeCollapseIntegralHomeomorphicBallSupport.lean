import Wikipedia.HopfProblem.DegreeCollapseIntegralPrimitiveCap
import Wikipedia.NoExoticSixSphere.SupportedHomeomorph

/-!
# Original integral cap calculations on homeomorphic closed balls

Pull back actual closed Euclidean balls through an actual homeomorphism.
Original supported homology and evaluation naturality give the integral
groups, their projectivity, and injectivity of every point evaluation.
A class with primitive local evaluations consequently generates the
actual top supported group. The original cap map is then bijective in
every complementary degree, without prescribing the class's sign.
-/

noncomputable section

open Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralHomeomorphicBall

open FirstHurewicz NoExoticSixSphere SupportedRelativeHomology

variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def support (e : X ≃ₜ E) (R : ℝ) : Set X := e ⁻¹' closedBall (0 : E) R

theorem support_isCompact (e : X ≃ₜ E) (R : ℝ) : IsCompact (support e R) :=
  e.isCompact_preimage.mpr (isCompact_closedBall (0 : E) R)

def homologyEquiv (e : X ≃ₜ E) (R : ℝ) (k : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) (support e R) k ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) (closedBall (0 : E) R) k :=
  homeomorphEquiv (ModuleCat.of ℤ ℤ) e (fun _ => Iff.rfl) k

omit [FiniteDimensional ℝ E] in
theorem evaluate_injective (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R)
    (x : X) (hx : x ∈ support e R) (k : ℕ) :
    Function.Injective (evaluate (ModuleCat.of ℤ ℤ) (support e R) x hx k) := by
  let F : Homology (ModuleCat.of ℤ ℤ) (closedBall (0 : E) R) k ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) {e x} k :=
    IntegralBallOrientation.evaluationEquiv R hR (e x) hx k
  let G := RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ ℤ) e x k
  intro a b hab
  apply (homologyEquiv e R k).injective
  apply F.injective
  have he := evaluate_homeomorphEquiv (ModuleCat.of ℤ ℤ) e
    (K := support e R) (L := closedBall (0 : E) R) (fun _ => Iff.rfl) x hx k
  exact (LinearMap.congr_fun he a).trans
    ((congrArg G hab).trans (LinearMap.congr_fun he b).symm)

variable (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

theorem homology_subsingleton (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : k ≠ n + 3) :
    Subsingleton (Homology (ModuleCat.of ℤ ℤ) (support e R) k) := by
  let : Subsingleton (Homology (ModuleCat.of ℤ ℤ) (closedBall (0 : E) R) k) :=
    ClosedBallLocalHomology.integral_subsingleton E n R hR k hk
  exact (homologyEquiv e R k).injective.subsingleton

include n in
theorem homology_projective (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    Module.Projective ℤ (Homology (ModuleCat.of ℤ ℤ) (support e R) k) := by
  let : Module.Projective ℤ (Homology (ModuleCat.of ℤ ℤ) (closedBall (0 : E) R) k) :=
    ClosedBallLocalHomology.integral_projective E n R hR k
  exact Module.Projective.of_equiv (homologyEquiv e R k).symm

def topMark (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R) :
    Homology (ModuleCat.of ℤ ℤ) (support e R) (n + 3) ≃ₗ[ℤ] ℤ :=
  (homologyEquiv e R (n + 3)).trans (ClosedBallLocalHomology.integralTopEquiv E n R hR)

omit [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = (n + 2) + 1)] in
/-- Primitive original localizations make this actual supported class a generator. -/
theorem class_generates (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R)
    (c : Homology (ModuleCat.of ℤ ℤ) (support e R) (n + 3))
    (hc : IntegralPrimitiveCap.IsPrimitiveOn (support e R) (n + 3) c) :
    ∀ a : Homology (ModuleCat.of ℤ ℤ) (support e R) (n + 3), ∃ k : ℤ, k • c = a := by
  have hx : e.symm 0 ∈ support e R := by
    change e (e.symm 0) ∈ closedBall (0 : E) R
    rw [e.apply_symm_apply]
    exact mem_closedBall_self hR
  exact IntegralPrimitiveCap.generates_of_evaluate_injective (support e R) (n + 3) c hc
    (e.symm 0) hx (evaluate_injective e R hR (e.symm 0) hx (n + 3))

theorem cohomology_subsingleton (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : k ≠ n + 3) :
    Subsingleton (IntegralSupportedCohomology.Cohomology (support e R) k) := by
  let : Subsingleton (RelativeSingularHomology.Homology (support e R)ᶜ k) :=
    homology_subsingleton n e R hR k hk
  cases k with
  | zero => exact (RelativeIntegralCap.evaluationZeroEquiv (support e R)ᶜ).injective.subsingleton
  | succ k =>
      let : Module.Projective ℤ (RelativeSingularHomology.Homology (support e R)ᶜ k) :=
        homology_projective n e R hR k
      exact (RelativeIntegralCap.evaluationSuccEquiv (support e R)ᶜ k).injective.subsingleton

/-- The original cap is bijective for every primitive class on the pulled-back ball. -/
theorem cap_bijective (e : X ≃ₜ E) (R : ℝ) (hR : 0 ≤ R)
    (c : Homology (ModuleCat.of ℤ ℤ) (support e R) (n + 3))
    (hc : IntegralPrimitiveCap.IsPrimitiveOn (support e R) (n + 3) c)
    (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (IntegralCompactSupportCap.componentMap (support e R) h c) := by
  let : ContractibleSpace X := e.contractibleSpace
  by_cases hq : q = 0
  · subst q
    have hp : p = n + 3 := by omega
    subst p
    let : Module.Projective ℤ (RelativeSingularHomology.Homology (support e R)ᶜ (n + 2)) :=
      homology_projective n e R hR (n + 2)
    exact IntegralPrimitiveCap.topCap_bijective (support e R) (n + 2) (topMark n e R hR) c
      (class_generates n e R hR c hc)
  · let := cohomology_subsingleton n e R hR p (by omega)
    let : Subsingleton ((singularComplex X).homology q) :=
      PeriodTorusHigherHomology.contractible_homology_subsingleton X q hq
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralHomeomorphicBall
