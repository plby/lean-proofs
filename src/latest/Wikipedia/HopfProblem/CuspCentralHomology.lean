import Wikipedia.HopfProblem.CuspCentralHomologyLowDegrees
import Wikipedia.HopfProblem.CuspCentralHomologyMiddle
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegrees
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusStrata
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationOne

/-!
# Integral singular homology of the actual central cusp fibre

The literal central fibre has integral homology ranks `(1, 2, 4, 2, 1)`,
is torsion-free in every degree, and has no homology above degree four.
The proof uses its actual compact phase-hexagon presentation, the genuine
radial open cover, the actual double-locus suspension homeomorphism, and
the proved singular Mayer–Vietoris sequence.  Its attaching maps are
computed using actual phase actions and integral cross-product naturality.

The imported specialization result concerns the independently defined
polar/honeycomb collapse and proves its genuine degree-one map and exact
integral monodromy-image kernel.  Higher-degree specialization formulas
are separate from the all-degree homology calculation completed here.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open CuspRetraction SingularMayerVietoris

/-- The ranks in Proposition 7.11 and Appendix A.3, extended by zero. -/
def centralBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 2
  | 4 => 1
  | _ => 0

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- A finite free integral coordinate model for every actual singular
homology group of the original central fibre. -/
def centralSingularHomologyEquiv (n : ℕ) :
    SingularHomology (QuotientCentralFibre C r) n ≃ₗ[ℤ] (Fin (centralBetti n) → ℤ) :=
  match n with
  | 0 => (centralSingularH0Equiv C r hr).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => centralSingularH1Equiv C r hr hC
  | 2 => centralSingularH2Equiv C r hr hC
  | 3 => centralSingularH3Equiv C r hr hC
  | 4 => (centralSingularH4Equiv C r hr hC).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 => centralSingularHomologyHigherEquivZero C r hr hC n

include hr hC

theorem centralSingularHomology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) n) :=
  Module.Free.of_equiv (centralSingularHomologyEquiv C r hr hC n).symm

theorem centralSingularHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) n) :=
  Module.Finite.of_surjective (centralSingularHomologyEquiv C r hr hC n).symm.toLinearMap
    (centralSingularHomologyEquiv C r hr hC n).symm.surjective

theorem centralSingularHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) n) = centralBetti n := by
  rw [(centralSingularHomologyEquiv C r hr hC n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem centralSingularHomology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) n) := by
  let := centralSingularHomology_free C r hr hC n
  infer_instance

/-- The displayed rank table is a table of the actual singular homology
modules, not a separately defined chain complex. -/
theorem centralSingularHomology_finranks :
    (fun i : Fin 5 => Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) i)) =
      ![1, 2, 4, 2, 1] := by
  funext i
  rw [centralSingularHomology_finrank C r hr hC]
  fin_cases i <;> rfl

omit hr hC in
/-- The finite alternating sum of actual integral singular-homology ranks. -/
def centralSingularEulerCharacteristic : ℤ :=
  ∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) *
    (Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) i) : ℤ)

/-- The vanishing theorem above degree four makes this the full Euler
characteristic of the computed actual singular homology. -/
theorem centralSingularEulerCharacteristic_eq_two :
    centralSingularEulerCharacteristic C r = 2 := by
  unfold centralSingularEulerCharacteristic
  simp_rw [centralSingularHomology_finrank C r hr hC]
  norm_num [Fin.sum_univ_succ, centralBetti]

/-- Proposition 7.11 and Appendix A.3 for the actual central fibre,
including all-degree freeness and torsion-freeness. -/
theorem central_singular_homology :
    (∀ n, Nonempty
      (SingularHomology (QuotientCentralFibre C r) n ≃ₗ[ℤ] (Fin (centralBetti n) → ℤ))) ∧
    (∀ n, Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) n)) ∧
    (∀ n, Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) n)) ∧
    (∀ n, Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) n)) ∧
    (∀ n, 4 < n → Subsingleton (SingularHomology (QuotientCentralFibre C r) n)) ∧
    centralSingularEulerCharacteristic C r = 2 :=
  ⟨fun n => ⟨centralSingularHomologyEquiv C r hr hC n⟩,
    centralSingularHomology_free C r hr hC,
    centralSingularHomology_finite C r hr hC,
    centralSingularHomology_torsionFree C r hr hC,
    fun _ hn => centralSingularHomology_subsingleton_of_four_lt C r hr hC hn,
    centralSingularEulerCharacteristic_eq_two C r hr hC⟩

end Wikipedia.HopfProblem.CuspCentralHomology
