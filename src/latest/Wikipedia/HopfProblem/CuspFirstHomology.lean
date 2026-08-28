import Wikipedia.HopfProblem.CuspFirstHomologyTopology
import Wikipedia.HopfProblem.PeriodTorusFirstHomology
import Wikipedia.HopfProblem.CuspUniversalCover

/-!
# Integral singular first homology of the actual cusp quotient

The universal-cover marking of the cusp fundamental group is transported
through the proved singular Hurewicz isomorphism. Thus the resulting
rank-two lattice is Mathlib's actual integral singular first homology.
The marking at an upstairs point agrees with the endpoint of lifted loops,
which is the marking used for the nonzero-fibre inclusion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace FirstHurewicz

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual singular first homology in the deck-translation marking
determined by an upstairs point. -/
def singularH1EquivAt (e : Tube (disc ε)) :
    SingularH1 (QuotientSpace C ε) ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let := quotient_pathConnected C ε hε
  exact singularH1EquivOfPi1 (quotientMap C ε e)
    (fundamentalGroupEquivAt C ε hε hε1 hC hR e)

@[simp] theorem singularH1EquivAt_hurewiczFunction (e : Tube (disc ε))
    (γ : FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e)) :
    singularH1EquivAt C ε hε hε1 hC hR e
        (hurewiczFunction (quotientMap C ε e) γ) =
      (fundamentalGroupEquivAt C ε hε hε1 hC hR e γ).toAdd := by
  let := quotient_pathConnected C ε hε
  exact singularH1EquivOfPi1_hurewiczFunction (quotientMap C ε e)
    (fundamentalGroupEquivAt C ε hε hε1 hC hR e) γ

@[simp] theorem singularH1EquivAt_loopHomologyClass (e : Tube (disc ε))
    (p : Path (quotientMap C ε e) (quotientMap C ε e)) :
    singularH1EquivAt C ε hε hε1 hC hR e (loopHomologyClass p) =
      (fundamentalGroupEquivAt C ε hε hε1 hC hR e (loopQuotient p)).toAdd :=
  singularH1EquivAt_hurewiczFunction C ε hε hε1 hC hR e (loopQuotient p)

/-- A marked rank-two isomorphism at any actual cusp basepoint. -/
def singularH1Equiv (x : QuotientSpace C ε) :
    SingularH1 (QuotientSpace C ε) ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let := quotient_pathConnected C ε hε
  exact singularH1EquivOfPi1 x (fundamentalGroupEquiv C ε hε hε1 hC hR x)

@[simp] theorem singularH1Equiv_hurewiczFunction (x : QuotientSpace C ε)
    (γ : FundamentalGroup (QuotientSpace C ε) x) :
    singularH1Equiv C ε hε hε1 hC hR x (hurewiczFunction x γ) =
      (fundamentalGroupEquiv C ε hε hε1 hC hR x γ).toAdd := by
  let := quotient_pathConnected C ε hε
  exact singularH1EquivOfPi1_hurewiczFunction x
    (fundamentalGroupEquiv C ε hε hε1 hC hR x) γ

include hε hε1 hC hR in
/-- Integral singular first homology of the actual cusp is free. -/
theorem singularH1_free : Module.Free ℤ (SingularH1 (QuotientSpace C ε)) := by
  let := quotient_pathConnected C ε hε
  exact Module.Free.of_equiv (singularH1Equiv C ε hε hε1 hC hR
    (Classical.choice inferInstance)).symm

include hε hε1 hC hR in
theorem singularH1_finite : Module.Finite ℤ (SingularH1 (QuotientSpace C ε)) := by
  let := quotient_pathConnected C ε hε
  let e := singularH1Equiv C ε hε hε1 hC hR (Classical.choice inferInstance)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

include hε hε1 hC hR in
/-- Corollary 4.8 at the level of actual integral singular homology. -/
theorem singularH1_finrank : Module.finrank ℤ (SingularH1 (QuotientSpace C ε)) = 2 := by
  let := quotient_pathConnected C ε hε
  rw [(singularH1Equiv C ε hε hε1 hC hR (Classical.choice inferInstance)).finrank_eq]
  simp

include hε hε1 hC hR in
theorem singularH1_torsionFree :
    Module.IsTorsionFree ℤ (SingularH1 (QuotientSpace C ε)) := by
  let := singularH1_free C ε hε hε1 hC hR
  infer_instance

/-- Holomorphic cusp input on any positive disc supplies a genuine smaller
cusp whose actual integral first singular homology is the rank-two lattice.
The required small-drift estimate is derived, not assumed in the conclusion. -/
theorem exists_singularH1Equiv {r : ℝ} (hr : 0 < r)
    (hCr : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η : ℝ, 0 < η ∧ η < r ∧
      Nonempty (SingularH1 (QuotientSpace C η) ≃ₗ[ℤ] (Fin 2 → ℤ)) := by
  obtain ⟨η, hη, hηr, hη1, hRη, hCη⟩ := exists_admissible_radius C hr hCr
  let := quotient_pathConnected C η hη
  exact ⟨η, hη, hηr, ⟨singularH1Equiv C η hη hη1 hCη hRη
    (Classical.choice inferInstance)⟩⟩

end Wikipedia.HopfProblem.CuspQuotient
