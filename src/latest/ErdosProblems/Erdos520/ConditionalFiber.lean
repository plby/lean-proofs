import ErdosProblems.Erdos520.BonamiModel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

open Filtration

/-- Integrate a function over a finite set of coordinates, leaving all other
coordinates frozen. -/
noncomputable def finiteCoinFiberIntegral (t : Finset ℕ) (F : Omega → ℝ)
    (omega : Omega) : ℝ :=
  ∫ eta : t → Bool, F (Function.updateFinset omega t eta)
    ∂Measure.pi (fun _ : t => coin)

lemma measurable_restrict_piFinset (s : Finset ℕ) :
    Measurable[piFinset s] (s.restrict : Omega → (s → Bool)) := by
  rw [piFinset_eq_comap_restrict]
  exact Measurable.of_comap_le le_rfl

/-- Updating one coordinate block by constants sends the remaining-coordinate
sigma algebra measurably into the sigma algebra on the union. -/
lemma measurable_updateFinset_piFinset {s t : Finset ℕ} (eta : t → Bool) :
    Measurable[piFinset s, piFinset (s ∪ t)]
      (fun omega : Omega => Function.updateFinset omega t eta) := by
  have hrest : Measurable[piFinset s]
      (fun omega : Omega =>
        (s ∪ t).restrict (Function.updateFinset omega t eta)) := by
    rw [@measurable_pi_iff Omega ↥(s ∪ t) (fun _ => Bool) (piFinset s)]
    intro i
    by_cases hit : (i : ℕ) ∈ t
    · have heq :
          (fun omega : Omega =>
            (s ∪ t).restrict (Function.updateFinset omega t eta) i) =
            fun _ => eta ⟨i, hit⟩ := by
        funext omega
        simp [Function.updateFinset, hit]
      rw [heq]
      exact measurable_const
    · have his : (i : ℕ) ∈ s := by
        rcases Finset.mem_union.mp i.property with hi | hi
        · exact hi
        · exact (hit hi).elim
      have heq :
          (fun omega : Omega =>
            (s ∪ t).restrict (Function.updateFinset omega t eta) i) =
            fun omega => s.restrict omega ⟨i, his⟩ := by
        funext omega
        simp [Function.updateFinset, hit]
      rw [heq]
      exact (measurable_pi_apply ⟨i, his⟩).comp
        (measurable_restrict_piFinset s)
  apply Measurable.of_comap_le
  simpa [piFinset_eq_comap_restrict, MeasurableSpace.comap_comp,
    Function.comp_def] using! hrest.comap_le

lemma stronglyMeasurable_updateFinset_of_piFinset_union {s t : Finset ℕ}
    {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F) (eta : t → Bool) :
    StronglyMeasurable[piFinset s]
      (fun omega => F (Function.updateFinset omega t eta)) := by
  exact hF.comp_measurable (measurable_updateFinset_piFinset eta)

/-- Finite-fiber integration removes the fresh-coordinate dependence. -/
lemma stronglyMeasurable_finiteCoinFiberIntegral {s t : Finset ℕ}
    {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F) :
    StronglyMeasurable[piFinset s] (finiteCoinFiberIntegral t F) := by
  rw [show finiteCoinFiberIntegral t F = fun omega =>
      fintypeAverage (fun eta : t → Bool =>
        F (Function.updateFinset omega t eta)) by
    funext omega
    rw [finiteCoinFiberIntegral, integral_coin_eq_fintypeAverage]]
  unfold fintypeAverage
  apply StronglyMeasurable.div
  · exact Finset.univ.stronglyMeasurable_fun_sum fun eta _heta =>
      stronglyMeasurable_updateFinset_of_piFinset_union hF eta
  · exact stronglyMeasurable_const

/-- Fubini on two disjoint finite coordinate blocks, in `updateFinset`
notation. -/
lemma integral_updateFinset_union {s t : Finset ℕ} (hst : Disjoint s t)
    (F : Omega → ℝ) (base : Omega) :
    (∫ old : s → Bool,
        ∫ fresh : t → Bool,
          F (Function.updateFinset
            (Function.updateFinset base s old) t fresh)
          ∂Measure.pi (fun _ : t => coin)
      ∂Measure.pi (fun _ : s => coin)) =
      ∫ both : ↥(s ∪ t) → Bool,
        F (Function.updateFinset base (s ∪ t) both)
        ∂Measure.pi (fun _ : ↥(s ∪ t) => coin) := by
  let e := MeasurableEquiv.piFinsetUnion (fun _ : ℕ => Bool) hst
  let G : ((s → Bool) × (t → Bool)) → ℝ := fun p =>
    F (Function.updateFinset
      (Function.updateFinset base s p.1) t p.2)
  have hG : Integrable G
      ((Measure.pi (fun _ : s => coin)).prod
        (Measure.pi (fun _ : t => coin))) := Integrable.of_finite
  calc
    (∫ old : s → Bool,
        ∫ fresh : t → Bool,
          F (Function.updateFinset
            (Function.updateFinset base s old) t fresh)
          ∂Measure.pi (fun _ : t => coin)
      ∂Measure.pi (fun _ : s => coin)) =
        ∫ p, G p
          ∂((Measure.pi (fun _ : s => coin)).prod
            (Measure.pi (fun _ : t => coin))) :=
      (integral_prod G hG).symm
    _ = ∫ p,
          F (Function.updateFinset base (s ∪ t) (e p))
          ∂((Measure.pi (fun _ : s => coin)).prod
            (Measure.pi (fun _ : t => coin))) := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        exact congrArg F (Function.updateFinset_updateFinset hst)
    _ = ∫ both : ↥(s ∪ t) → Bool,
          F (Function.updateFinset base (s ∪ t) both)
          ∂Measure.pi (fun _ : ↥(s ∪ t) => coin) := by
      exact (measurePreserving_piFinsetUnion hst (fun _ : ℕ => coin)).integral_comp'
        (fun both => F (Function.updateFinset base (s ∪ t) both))

/-- Averaging over the fresh coordinates preserves the total integral for a
function depending only on the old and fresh finite blocks. -/
theorem integral_finiteCoinFiberIntegral_eq {s t : Finset ℕ}
    (hst : Disjoint s t) {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F) :
    ∫ omega, finiteCoinFiberIntegral t F omega ∂μ =
      ∫ omega, F omega ∂μ := by
  let base : Omega := fun _ => false
  have hleft := integral_infinitePi_of_piFinset
    (μ := fun _ : ℕ => coin)
    (stronglyMeasurable_finiteCoinFiberIntegral hF) base
  have hright := integral_infinitePi_of_piFinset
    (μ := fun _ : ℕ => coin) hF base
  rw [show (∫ omega, finiteCoinFiberIntegral t F omega ∂μ) =
      ∫ old : s → Bool,
        finiteCoinFiberIntegral t F
          (Function.updateFinset base s old)
        ∂Measure.pi (fun _ : s => coin) by simpa only [μ] using! hleft]
  rw [show (∫ omega, F omega ∂μ) =
      ∫ both : ↥(s ∪ t) → Bool,
        F (Function.updateFinset base (s ∪ t) both)
        ∂Measure.pi (fun _ : ↥(s ∪ t) => coin) by
      simpa only [μ] using! hright]
  exact integral_updateFinset_union hst F base

/-- A real-valued function depending on finitely many Boolean coordinates is
automatically integrable under the fair infinite product law. -/
theorem integrable_of_stronglyMeasurable_piFinset {s : Finset ℕ}
    {F : Omega → ℝ} (hF : StronglyMeasurable[piFinset s] F) :
    Integrable F μ := by
  let base : Omega := fun _ => false
  let C : ℝ := ∑ eta : s → Bool,
    |F (Function.updateFinset base s eta)|
  have hdep : DependsOn F (s : Set ℕ) :=
    hF.dependsOn_of_piFinset
  have hbound : ∀ omega : Omega, ‖F omega‖ ≤ C := by
    intro omega
    have heq : F omega =
        F (Function.updateFinset base s (s.restrict omega)) := by
      apply hdep
      intro i hi
      have hi' : i ∈ s := hi
      simp [Function.updateFinset, hi']
    rw [heq, Real.norm_eq_abs]
    exact Finset.single_le_sum
      (fun eta _heta => abs_nonneg
        (F (Function.updateFinset base s eta)))
      (Finset.mem_univ (s.restrict omega))
  apply Integrable.of_bound
    ((hF.mono (piFinset.le s)).aestronglyMeasurable) C
  exact ae_of_all μ hbound

/-- An event measurable with respect to the old coordinates is unchanged by
updating a disjoint fresh block. -/
lemma mem_updateFinset_iff_of_measurableSet_piFinset {s t : Finset ℕ}
    (hst : Disjoint s t) {A : Set Omega}
    (hA : MeasurableSet[piFinset s] A) (omega : Omega) (eta : t → Bool) :
    Function.updateFinset omega t eta ∈ A ↔ omega ∈ A := by
  let I : Omega → ℝ := A.indicator fun _ => 1
  have hI : StronglyMeasurable[piFinset s] I := by
    exact stronglyMeasurable_const.indicator hA
  have hdep : DependsOn I (s : Set ℕ) := hI.dependsOn_of_piFinset
  have heq : I (Function.updateFinset omega t eta) = I omega := by
    apply hdep
    intro i hi
    have hi' : i ∈ s := hi
    have hit : i ∉ t := fun hit => Finset.disjoint_left.mp hst hi' hit
    simp [Function.updateFinset, hit]
  constructor
  · intro hup
    by_contra hω
    simp [I, Set.indicator_of_mem hup, Set.indicator_of_notMem hω] at heq
  · intro hω
    by_contra hup
    simp [I, Set.indicator_of_notMem hup, Set.indicator_of_mem hω] at heq

/-- Fiber integration commutes pointwise with an indicator of an old-coordinate
event. -/
lemma finiteCoinFiberIntegral_indicator {s t : Finset ℕ}
    (hst : Disjoint s t) {A : Set Omega}
    (hA : MeasurableSet[piFinset s] A) (F : Omega → ℝ) (omega : Omega) :
    finiteCoinFiberIntegral t (A.indicator F) omega =
      A.indicator (finiteCoinFiberIntegral t F) omega := by
  by_cases hω : omega ∈ A
  · rw [Set.indicator_of_mem hω]
    unfold finiteCoinFiberIntegral
    apply integral_congr_ae
    exact ae_of_all _ fun eta => by
      change A.indicator F (Function.updateFinset omega t eta) =
        F (Function.updateFinset omega t eta)
      rw [Set.indicator_of_mem
        ((mem_updateFinset_iff_of_measurableSet_piFinset hst hA omega eta).2 hω)]
  · rw [Set.indicator_of_notMem hω]
    unfold finiteCoinFiberIntegral
    have hzero : (fun eta : t → Bool =>
        A.indicator F (Function.updateFinset omega t eta)) = 0 := by
      funext eta
      have hnot : Function.updateFinset omega t eta ∉ A := fun hup => hω <|
        (mem_updateFinset_iff_of_measurableSet_piFinset hst hA omega eta).1 hup
      simp [Set.indicator_of_notMem hnot]
    rw [hzero]
    simp

/-- Set-integral characterization of the finite fresh-coordinate fiber
average.  This is the defining identity needed for conditional expectation. -/
theorem setIntegral_finiteCoinFiberIntegral_eq {s t : Finset ℕ}
    (hst : Disjoint s t) {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F)
    {A : Set Omega} (hA : MeasurableSet[piFinset s] A) :
    ∫ omega in A, finiteCoinFiberIntegral t F omega ∂μ =
      ∫ omega in A, F omega ∂μ := by
  have hAambient : MeasurableSet A := (piFinset.le s) A hA
  have hAunion : MeasurableSet[piFinset (s ∪ t)] A :=
    (piFinset.mono Finset.subset_union_left) A hA
  have hIndicator :
      StronglyMeasurable[piFinset (s ∪ t)] (A.indicator F) :=
    hF.indicator hAunion
  rw [← integral_indicator hAambient, ← integral_indicator hAambient]
  rw [← integral_finiteCoinFiberIntegral_eq hst hIndicator]
  apply integral_congr_ae
  exact ae_of_all μ fun omega =>
    (finiteCoinFiberIntegral_indicator hst hA F omega).symm

/-- Conditional expectation onto the old-coordinate sigma algebra is exactly
integration over the disjoint finite fresh-coordinate fiber, for every
function depending only on the two finite blocks. -/
theorem finiteCoinFiberIntegral_ae_eq_condExp {s t : Finset ℕ}
    (hst : Disjoint s t) {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F) :
    finiteCoinFiberIntegral t F =ᵐ[μ] μ[F | piFinset s] := by
  let G := finiteCoinFiberIntegral t F
  have hG : StronglyMeasurable[piFinset s] G :=
    stronglyMeasurable_finiteCoinFiberIntegral hF
  have hFint : Integrable F μ :=
    integrable_of_stronglyMeasurable_piFinset hF
  have hGint : Integrable G μ :=
    integrable_of_stronglyMeasurable_piFinset hG
  apply ae_eq_condExp_of_forall_setIntegral_eq (piFinset.le s) hFint
  · intro A _hA _hAfin
    exact hGint.integrableOn
  · intro A hA _hAfin
    exact setIntegral_finiteCoinFiberIntegral_eq hst hF hA
  · exact hG.aestronglyMeasurable

/-- Equivalent normalized-finite-average form of the conditional-fiber
identity. -/
theorem finiteCoinAverage_updateFinset_ae_eq_condExp {s t : Finset ℕ}
    (hst : Disjoint s t) {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F) :
    (fun omega => fintypeAverage (fun eta : t → Bool =>
      F (Function.updateFinset omega t eta))) =ᵐ[μ]
        μ[F | piFinset s] := by
  have heq : (fun omega => fintypeAverage (fun eta : t → Bool =>
      F (Function.updateFinset omega t eta))) =
      finiteCoinFiberIntegral t F := by
    funext omega
    rw [finiteCoinFiberIntegral, integral_coin_eq_fintypeAverage]
  rw [heq]
  exact finiteCoinFiberIntegral_ae_eq_condExp hst hF

/-- A pointwise finite-fiber estimate immediately becomes the corresponding
conditional-expectation estimate. -/
theorem condExp_le_of_finiteCoinFiberIntegral_le {s t : Finset ℕ}
    (hst : Disjoint s t) {F B : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset (s ∪ t)] F)
    (hbound : ∀ omega, finiteCoinFiberIntegral t F omega ≤ B omega) :
    μ[F | piFinset s] ≤ᵐ[μ] B := by
  filter_upwards [finiteCoinFiberIntegral_ae_eq_condExp hst hF] with omega heq
  rw [← heq]
  exact hbound omega

/-- Prime-block specialization: the old primes at most `a` are disjoint from
the fresh primes in `(a,b]`. -/
theorem freshPrimeFiberIntegral_ae_eq_condExp {a b : ℕ} {F : Omega → ℝ}
    (hF : StronglyMeasurable[piFinset
      ((a + 1).primesBelow ∪ freshPrimes a b)] F) :
    finiteCoinFiberIntegral (freshPrimes a b) F =ᵐ[μ]
      μ[F | piFinset ((a + 1).primesBelow)] := by
  exact finiteCoinFiberIntegral_ae_eq_condExp
    (primesBelow_succ_disjoint_freshPrimes a b) hF

end Problem520
end Erdos
