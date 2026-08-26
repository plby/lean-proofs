import ErdosProblems.Erdos1002.GaussPrefixAnnularBoundaryAssembly
import ErdosProblems.Erdos1002.GaussPrefixAnnularInteriorMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly of the interior Gauss-prefix factorial limits

There are two logically independent inputs in the interior argument.
The marked Fourier theorem evaluates the canonical, chronologically
ordered tuple measure.  The literal-transfer theorem identifies the
original mixed falling-factorial moment with that canonical measure.
This file records their exact interface and combines them without any
probabilistic or asymptotic loss.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

/-- Exact asymptotic identification of the literal mixed factorial
moment with the canonical marked tuple measure on its labeled torus
box.  The quantification over the reference order makes the statement
independent of the noncomputable enumeration chosen in the assembly
theorem. -/
def GaussPrefixAnnularLiteralCanonicalBoxTransfer : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ {grid : ℕ}, 0 < grid →
      ∀ (k : AnnularGridIndex grid → ℕ),
        0 < MixedOccurrenceCount k →
        (∀ i, 0 < k i → i.time.1 < grid) →
        (∀ i, 0 < k i → i.signed.1 < grid) →
        (∀ i, 0 < k i → i.torus.1 < grid) →
        ∀ e₀ : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          Tendsto
            (fun N : ℕ ↦
              mixedFactorialMoment
                  (gaussPrefixMarkedCountVectorLaw N
                    (annularGridCell ε A grid)
                    (fun i ↦
                      measurableSet_annularGridCell ε A grid i))
                  k -
                (reindexedAnnularUniformMarkedTupleFiniteMeasure
                    (ε := ε) (A := A) N k e₀ :
                  Measure
                    (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
                  (unitTorusHalfOpenBox
                    (flattenedAnnularTorusLower e₀)
                    (flattenedAnnularTorusUpper e₀)))
            atTop (nhds 0)

/-- The two exact interior inputs imply every nonterminal mixed
factorial limit. -/
theorem gaussPrefixNonterminalAnnularGridFactorialLimits_of_fourier_transfer
    (hFourier : GaussPrefixAnnularReindexedNonzeroFourierLimits)
    (hTransfer : GaussPrefixAnnularLiteralCanonicalBoxTransfer) :
    GaussPrefixNonterminalAnnularGridFactorialLimits := by
  intro ε A hε hεA m k hinterior
  by_cases hr : 0 < MixedOccurrenceCount k
  · let e₀ : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k :=
      (Fintype.equivFin (GaussPrefixMixedOccurrence k)).symm
    have htime :
        ∀ i, 0 < k i → i.time.1 < m + 1 :=
      fun i hi ↦ (hinterior i hi).1
    have hsigned :
        ∀ i, 0 < k i → i.signed.1 < m + 1 :=
      fun i hi ↦ (hinterior i hi).2.1
    have htorus :
        ∀ i, 0 < k i → i.torus.1 < m + 1 :=
      fun i hi ↦ (hinterior i hi).2.2
    have hcanonical :=
      tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_real_torusBox
        hFourier hε hεA (by omega) k hr htime hsigned htorus e₀
    have hliteral :=
      hTransfer hε hεA (by omega) k hr htime hsigned htorus e₀
    convert! hliteral.add hcanonical using 1 <;>
      simp only [sub_add_cancel, zero_add]
  · have hcard : MixedOccurrenceCount k = 0 :=
      Nat.eq_zero_of_not_pos hr
    have hsum : ∑ i, k i = 0 := by
      rw [← card_gaussPrefixMixedOccurrence]
      exact hcard
    have hkzero : ∀ i, k i = 0 := by
      intro i
      have hle : k i ≤ ∑ j, k j :=
        Finset.single_le_sum
          (fun j _hj ↦ Nat.zero_le (k j))
          (Finset.mem_univ i)
      omega
    have hk : k = fun _i ↦ 0 := funext hkzero
    subst k
    exact gaussPrefixAnnularGridFactorialLimit_zero m

/-- Fourier cancellation plus literal-to-canonical transfer give the
complete annular grid statement, including terminal cells. -/
theorem gaussPrefixAnnularGridFactorialLimits_of_fourier_transfer
    (hFourier : GaussPrefixAnnularReindexedNonzeroFourierLimits)
    (hTransfer : GaussPrefixAnnularLiteralCanonicalBoxTransfer) :
    GaussPrefixAnnularGridFactorialLimits :=
  gaussPrefixAnnularGridFactorialLimits_of_nonterminal
    (gaussPrefixNonterminalAnnularGridFactorialLimits_of_fourier_transfer
      hFourier hTransfer)

end

end Erdos1002
