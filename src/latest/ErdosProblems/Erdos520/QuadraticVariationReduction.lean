import ErdosProblems.Erdos520.CaichReduction
import ErdosProblems.Erdos520.LargestPrimeTestUnion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# Deterministic reduction of Caich's quadratic variation

This file separates the three inputs to Caich's equation (9):

* the concrete smoothing inequality for the test-point quadratic variation;
* the maximal thin-block energy bound; and
* the auxiliary smoothing-remainder bound.

The passage from those inputs to the stopped-Hoeffding variance scale is
entirely deterministic.  In particular, this file assumes no concentration
estimate.
-/

/-! ## Scalar bookkeeping -/

/-- The square-root cancellation behind equation (29). -/
theorem mul_sqrt_div_eq_sqrt_mul
    {A T : ℝ} (hA : 0 < A) (hT : 0 ≤ T) :
    A * Real.sqrt (T / A) = Real.sqrt (T * A) := by
  rw [Real.sqrt_div hT, Real.sqrt_mul hT]
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsquare : Real.sqrt A * Real.sqrt A = A :=
    Real.mul_self_sqrt hA.le
  calc
    A * (Real.sqrt T / Real.sqrt A) =
        (Real.sqrt A * Real.sqrt A) *
          (Real.sqrt T / Real.sqrt A) := by rw [hsquare]
    _ = Real.sqrt T * Real.sqrt A := by field_simp

/-- Granular deterministic form of the equation-(9) reduction. -/
theorem quadraticVariation_le_of_smoothing_block_aux
    {ell K : ℕ} {V x D M E B T : ℝ}
    (hell : 1 < ell) (hx : 0 < x) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hT : 0 ≤ T)
    (hsmoothing :
      V / x ≤ D *
        ((ell : ℝ) * Real.log (ell : ℝ) * M + E))
    (hblock :
      M ≤ B *
        Real.sqrt
          (T / ((ell : ℝ) * Real.log (ell : ℝ))) /
        (ell : ℝ) ^ ((K : ℝ) / 2))
    (haux : E ≤ B * T / (ell : ℝ) ^ ((K : ℝ) / 2))
    (hprefactor :
      Real.sqrt
          (T * (ell : ℝ) * Real.log (ell : ℝ)) ≤ T) :
    V ≤ (2 * D * B) * x * T /
      (ell : ℝ) ^ ((K : ℝ) / 2) := by
  let A : ℝ := (ell : ℝ) * Real.log (ell : ℝ)
  let Q : ℝ := (ell : ℝ) ^ ((K : ℝ) / 2)
  have hellR : 0 < (ell : ℝ) := by positivity
  have hlog : 0 < Real.log (ell : ℝ) :=
    Real.log_pos (by exact_mod_cast hell)
  have hA : 0 < A := mul_pos hellR hlog
  have hQ : 0 < Q := Real.rpow_pos_of_pos hellR _
  have hAM : A * M ≤ B * T / Q := by
    calc
      A * M ≤ A * (B * Real.sqrt (T / A) / Q) :=
        mul_le_mul_of_nonneg_left hblock hA.le
      _ = B * (A * Real.sqrt (T / A)) / Q := by ring
      _ = B * Real.sqrt (T * A) / Q := by
        rw [mul_sqrt_div_eq_sqrt_mul hA hT]
      _ ≤ B * T / Q := by
        have hprefactor' : Real.sqrt (T * A) ≤ T := by
          simpa only [A, mul_assoc] using! hprefactor
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprefactor' hB) hQ.le
  have hinside : A * M + E ≤ 2 * (B * T / Q) := by
    calc
      A * M + E ≤ B * T / Q + B * T / Q := add_le_add hAM haux
      _ = 2 * (B * T / Q) := by ring
  have hratio : V / x ≤ 2 * D * B * T / Q := by
    calc
      V / x ≤ D * (A * M + E) := hsmoothing
      _ ≤ D * (2 * (B * T / Q)) :=
        mul_le_mul_of_nonneg_left hinside hD
      _ = 2 * D * B * T / Q := by ring
  have hmul : V ≤ (2 * D * B * T / Q) * x :=
    (div_le_iff₀ hx).1 hratio
  simpa [A, Q] using! hmul.trans_eq (by ring)

/-- Specialization to Caich's choice `T(ell) = ell^10`. -/
theorem quadraticVariation_le_of_smoothing_block_aux_caich
    {ell K : ℕ} {V x D M E B : ℝ}
    (hell : 1 < ell) (hx : 0 < x) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hsmoothing :
      V / x ≤ D *
        ((ell : ℝ) * Real.log (ell : ℝ) * M + E))
    (hblock :
      M ≤ B *
        Real.sqrt
          ((ell : ℝ) ^ 10 /
            ((ell : ℝ) * Real.log (ell : ℝ))) /
        (ell : ℝ) ^ ((K : ℝ) / 2))
    (haux :
      E ≤ B * (ell : ℝ) ^ 10 /
        (ell : ℝ) ^ ((K : ℝ) / 2)) :
    V ≤ (2 * D * B) * x * (ell : ℝ) ^ 10 /
      (ell : ℝ) ^ ((K : ℝ) / 2) := by
  apply quadraticVariation_le_of_smoothing_block_aux
    hell hx hD hB (pow_nonneg (Nat.cast_nonneg ell) 10)
    hsmoothing hblock haux
  simpa only [mul_assoc] using! caich_qv_prefactor_le (show 1 ≤ ell by omega)

/-! ## Test-point properties and events -/

/-- The maximum of the block energies `U_j`, including indices
`0 ≤ j ≤ J(ell)`. -/
noncomputable def caichBlockEnergyMax
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) : ℝ :=
  (Finset.range (J ell + 1)).sup' Finset.nonempty_range_add_one
    (fun j => U ell j omega)

/-- The deterministic equation-(9) smoothing inequality, simultaneously at
the selected test points of one scale. -/
def qvSmoothingGoodAtScale
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) (D : ℝ)
    (ell : ℕ) (omega : Omega) : Prop :=
  ∀ r ∈ tests ell,
    largestPrimeQuadraticVariation omega
        (x ell r) (a ell r) (b ell r) / (x ell r : ℝ) ≤
      D * ((ell : ℝ) * Real.log (ell : ℝ) *
        caichBlockEnergyMax J U ell omega + E ell r omega)

/-- The high-moment conclusion for the largest thin-block energy. -/
def blockEnergyMaxGoodAtScale
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K ell : ℕ) (omega : Omega) : Prop :=
  caichBlockEnergyMax J U ell omega ≤
    B * Real.sqrt
      ((ell : ℝ) ^ 10 /
        ((ell : ℝ) * Real.log (ell : ℝ))) /
      (ell : ℝ) ^ ((K : ℝ) / 2)

/-- Good auxiliary-remainder property at every selected test point. -/
def auxiliaryRemainderGoodAtScale
    (tests : ℕ → Finset ℕ) (E : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K ell : ℕ) (omega : Omega) : Prop :=
  ∀ r ∈ tests ell,
    E ell r omega ≤
      B * (ell : ℝ) ^ 10 / (ell : ℝ) ^ ((K : ℝ) / 2)

/-- The stopped-Hoeffding quadratic-variation threshold produced by the
reduction. -/
noncomputable def caichQuadraticVariationThreshold
    (C : ℝ) (K : ℕ) (x : ℕ → ℕ → ℕ)
    (ell r : ℕ) : ℝ :=
  C * (x ell r : ℝ) * (ell : ℝ) ^ 10 /
    (ell : ℝ) ^ ((K : ℝ) / 2)

/-- Good predictable quadratic variation at every selected test point.  This
is in exactly the shape consumed by `LargestPrimeTestUnion`. -/
def testPointQuadraticVariationGoodAtScale
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (C : ℝ) (K ell : ℕ) (omega : Omega) : Prop :=
  ∀ r ∈ tests ell,
    largestPrimeQuadraticVariation omega
        (x ell r) (a ell r) (b ell r) ≤
      caichQuadraticVariationThreshold C K x ell r

def qvSmoothingGoodEvent
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) (D : ℝ) (ell : ℕ) : Set Omega :=
  {omega | qvSmoothingGoodAtScale tests x a b J U E D ell omega}

def blockEnergyMaxGoodEvent
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K ell : ℕ) : Set Omega :=
  {omega | blockEnergyMaxGoodAtScale J U B K ell omega}

def auxiliaryRemainderGoodEvent
    (tests : ℕ → Finset ℕ) (E : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K ell : ℕ) : Set Omega :=
  {omega | auxiliaryRemainderGoodAtScale tests E B K ell omega}

def testPointQuadraticVariationGoodEvent
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (C : ℝ) (K ell : ℕ) : Set Omega :=
  {omega | testPointQuadraticVariationGoodAtScale tests x a b C K ell omega}

def qvSmoothingFailure
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) (D : ℝ) (ell : ℕ) : Set Omega :=
  (qvSmoothingGoodEvent tests x a b J U E D ell)ᶜ

def blockEnergyMaxFailure
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K ell : ℕ) : Set Omega :=
  (blockEnergyMaxGoodEvent J U B K ell)ᶜ

/-- This is the sole auxiliary analytic failure whose summability is needed
after the deterministic reduction. -/
def auxiliaryRemainderFailure
    (tests : ℕ → Finset ℕ) (E : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K ell : ℕ) : Set Omega :=
  (auxiliaryRemainderGoodEvent tests E B K ell)ᶜ

/-- The union of precisely the three ways the deterministic reduction can
fail. -/
def quadraticVariationReductionFailure
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) (D B : ℝ) (K ell : ℕ) :
    Set Omega :=
  qvSmoothingFailure tests x a b J U E D ell ∪
    blockEnergyMaxFailure J U B K ell ∪
    auxiliaryRemainderFailure tests E B K ell

/-! ## Deterministic and almost-sure wrappers -/

theorem testPointQuadraticVariationGoodAtScale_of_reduction
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) {D B : ℝ} {K ell : ℕ}
    {omega : Omega} (hell : 1 < ell)
    (hx : ∀ r ∈ tests ell, 0 < x ell r) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hsmoothing : qvSmoothingGoodAtScale tests x a b J U E D ell omega)
    (hblock : blockEnergyMaxGoodAtScale J U B K ell omega)
    (haux : auxiliaryRemainderGoodAtScale tests E B K ell omega) :
    testPointQuadraticVariationGoodAtScale
      tests x a b (2 * D * B) K ell omega := by
  intro r hr
  exact quadraticVariation_le_of_smoothing_block_aux_caich
    hell (by exact_mod_cast hx r hr) hD hB
    (hsmoothing r hr) hblock (haux r hr)

/-- Outside the explicit failure union, equation (29) holds at all test
points. -/
theorem testPointQuadraticVariationGoodAtScale_of_not_failure
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) {D B : ℝ} {K ell : ℕ}
    {omega : Omega} (hell : 1 < ell)
    (hx : ∀ r ∈ tests ell, 0 < x ell r) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hgood : omega ∉ quadraticVariationReductionFailure
      tests x a b J U E D B K ell) :
    testPointQuadraticVariationGoodAtScale
      tests x a b (2 * D * B) K ell omega := by
  have hsmoothing : omega ∈ qvSmoothingGoodEvent tests x a b J U E D ell := by
    by_contra hnot
    exact hgood (Or.inl (Or.inl hnot))
  have hblock : omega ∈ blockEnergyMaxGoodEvent J U B K ell := by
    by_contra hnot
    exact hgood (Or.inl (Or.inr hnot))
  have haux : omega ∈ auxiliaryRemainderGoodEvent tests E B K ell := by
    by_contra hnot
    exact hgood (Or.inr hnot)
  exact testPointQuadraticVariationGoodAtScale_of_reduction
    tests x a b J U E hell hx hD hB hsmoothing hblock haux

/-- Almost-sure eventual form of the deterministic reduction. -/
theorem ae_eventually_testPointQuadraticVariationGood_of_reduction
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) {D B : ℝ} {K : ℕ}
    (hx : ∀ ell r, r ∈ tests ell → 0 < x ell r)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale tests x a b J U E D ell omega)
    (hblock : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale J U B K ell omega)
    (haux : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale tests E B K ell omega) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      testPointQuadraticVariationGoodAtScale
        tests x a b (2 * D * B) K ell omega := by
  filter_upwards [hsmoothing, hblock, haux] with omega hsOmega hbOmega haOmega
  filter_upwards [hsOmega, hbOmega, haOmega,
    eventually_ge_atTop (2 : ℕ)] with ell hsEll hbEll haEll hell
  exact testPointQuadraticVariationGoodAtScale_of_reduction
    tests x a b J U E (by omega) (hx ell) hD hB hsEll hbEll haEll

/-! ## Failure-union and summability wrappers -/

theorem measureReal_quadraticVariationReductionFailure_le
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) (D B : ℝ) (K ell : ℕ) :
    μ.real (quadraticVariationReductionFailure
      tests x a b J U E D B K ell) ≤
      μ.real (qvSmoothingFailure tests x a b J U E D ell) +
        μ.real (blockEnergyMaxFailure J U B K ell) +
        μ.real (auxiliaryRemainderFailure tests E B K ell) := by
  unfold quadraticVariationReductionFailure
  calc
    μ.real
        ((qvSmoothingFailure tests x a b J U E D ell ∪
            blockEnergyMaxFailure J U B K ell) ∪
          auxiliaryRemainderFailure tests E B K ell) ≤
        μ.real
            (qvSmoothingFailure tests x a b J U E D ell ∪
              blockEnergyMaxFailure J U B K ell) +
          μ.real (auxiliaryRemainderFailure tests E B K ell) :=
      measureReal_union_le _ _
    _ ≤
        (μ.real (qvSmoothingFailure tests x a b J U E D ell) +
          μ.real (blockEnergyMaxFailure J U B K ell)) +
          μ.real (auxiliaryRemainderFailure tests E B K ell) :=
      add_le_add
        (measureReal_union_le
          (qvSmoothingFailure tests x a b J U E D ell)
          (blockEnergyMaxFailure J U B K ell)) le_rfl

theorem summable_measureReal_quadraticVariationReductionFailure
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) (D B : ℝ) (K : ℕ)
    (hsmoothing : Summable fun ell =>
      μ.real (qvSmoothingFailure tests x a b J U E D ell))
    (hblock : Summable fun ell =>
      μ.real (blockEnergyMaxFailure J U B K ell))
    (haux : Summable fun ell =>
      μ.real (auxiliaryRemainderFailure tests E B K ell)) :
    Summable fun ell => μ.real (quadraticVariationReductionFailure
      tests x a b J U E D B K ell) := by
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _
    ((hsmoothing.add hblock).add haux)
  intro ell
  exact measureReal_quadraticVariationReductionFailure_le
    tests x a b J U E D B K ell

/-- A summable auxiliary-remainder failure budget gives the required
almost-sure eventual auxiliary bound. -/
theorem ae_eventually_auxiliaryRemainderGood_of_summable
    (tests : ℕ → Finset ℕ) (E : ℕ → ℕ → Omega → ℝ)
    (B : ℝ) (K : ℕ)
    (haux : Summable fun ell =>
      μ.real (auxiliaryRemainderFailure tests E B K ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale tests E B K ell omega := by
  have hnot := ae_eventually_notMem_of_summable_measureReal haux
  filter_upwards [hnot] with omega hnotOmega
  filter_upwards [hnotOmega] with ell hnotEll
  exact not_not.mp hnotEll

/-- The common use case: equation (9) and the maximal block estimate are
available almost surely eventually, while only summability of the auxiliary
remainder failures remains to be supplied. -/
theorem ae_eventually_testPointQuadraticVariationGood_of_aux_summable
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) {D B : ℝ} {K : ℕ}
    (hx : ∀ ell r, r ∈ tests ell → 0 < x ell r)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hsmoothing : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      qvSmoothingGoodAtScale tests x a b J U E D ell omega)
    (hblock : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      blockEnergyMaxGoodAtScale J U B K ell omega)
    (haux : Summable fun ell =>
      μ.real (auxiliaryRemainderFailure tests E B K ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        largestPrimeQuadraticVariation omega
            (x ell r) (a ell r) (b ell r) ≤
          caichQuadraticVariationThreshold (2 * D * B) K x ell r := by
  exact ae_eventually_testPointQuadraticVariationGood_of_reduction
    tests x a b J U E hx hD hB hsmoothing hblock
      (ae_eventually_auxiliaryRemainderGood_of_summable tests E B K haux)

/-- Summability of the complete explicit failure union directly yields the
quadratic-variation hypothesis expected by `LargestPrimeTestUnion`. -/
theorem ae_eventually_testPointQuadraticVariationGood_of_failure_summable
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (E : ℕ → ℕ → Omega → ℝ) {D B : ℝ} {K : ℕ}
    (hx : ∀ ell r, r ∈ tests ell → 0 < x ell r)
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hfailure : Summable fun ell =>
      μ.real (quadraticVariationReductionFailure
        tests x a b J U E D B K ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        largestPrimeQuadraticVariation omega
            (x ell r) (a ell r) (b ell r) ≤
          caichQuadraticVariationThreshold (2 * D * B) K x ell r := by
  have hnot := ae_eventually_notMem_of_summable_measureReal hfailure
  filter_upwards [hnot] with omega hnotOmega
  filter_upwards [hnotOmega, eventually_ge_atTop (2 : ℕ)] with ell hgood hell
  exact testPointQuadraticVariationGoodAtScale_of_not_failure
    tests x a b J U E (by omega) (hx ell) hD hB hgood

end Problem520
end Erdos
