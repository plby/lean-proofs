import Wikipedia.HopfProblem.CuspCentralHomologyOpenRetraction
import Wikipedia.HopfProblem.CuspCentralHomologyFibreRadius
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.CuspFirstHomologyFibre

/-!
# Actual singular homology maps of a central retraction

Restricting a genuine norm-monotone cusp deformation gives homotopy
inverse maps between the central fibre and a smaller open cusp.  This
file identifies the homology map of its literal fibre restriction with
the already computed fibre inclusion, in every degree.  In degree one
the resulting map is the actual source lattice projection.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspQuotient CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)

/-- The actual fibre restriction of the endpoint retraction, using the
original fibre topology at the original ambient radius. -/
def retractedFibreMap (hδη : δ ≤ η)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (t : ℂ) (htδ : ‖t‖ < δ) :
    C(ActualQuotientFibre C r t, QuotientCentralFibre C r) :=
  (restrictClosedRetraction C r δ η hδη R).comp (fibreIntoOpen C r δ t htδ)

variable (hδ : 0 < δ) (hδη : δ ≤ η) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hR : R.comp (quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
      ContinuousMap.id (QuotientCentralFibre C r))
    (H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
      ((quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
      {q : ClosedQuotient C r η | projection C r q = 0})
    (hmono : ∀ s q, ‖projection C r (H (s, q))‖ ≤ ‖projection C r q‖)

/-- The homotopy equivalence constructed from this actual deformation,
with forward map central inclusion and inverse the actual endpoint. -/
def retractionCentralHomotopyEquiv :
    QuotientCentralFibre C r ≃ₕ QuotientSpace C δ :=
  (openCentralHomotopyEquiv C r δ η hδ hδη R hR H hmono).trans
    (openQuotientRadiusHomeomorph C hδr hC).symm.toHomotopyEquiv

/-- The representative-preserving fibre homeomorphism intertwines
restriction of the retraction with its homotopy inverse on the open cusp. -/
theorem retractionCentralHomotopyEquiv_inv_comp_fibre (t : ℂ) (htδ : ‖t‖ < δ) :
    ((retractionCentralHomotopyEquiv C r δ η hδ hδη hδr hC R hR H hmono).symm.toFun).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(ActualQuotientFibre C δ t, QuotientSpace C δ)) =
      (retractedFibreMap C r δ η hδη R t htδ).comp
        ((fibreRadiusHomeomorph C r δ t hδr hC htδ) :
          C(ActualQuotientFibre C δ t, ActualQuotientFibre C r t)) := by
  apply ContinuousMap.ext
  intro q
  have he := ContinuousMap.congr_fun (fibreRadiusHomeomorph_inclusion C r δ t hδr hC htδ) q
  exact congrArg (restrictClosedRetraction C r δ η hδη R) he.symm

/-- Equality of genuine induced singular homology maps, in every degree. -/
theorem retractedFibreMap_homology (t : ℂ) (htδ : ‖t‖ < δ) (n : ℕ)
    (a : SingularHomology (ActualQuotientFibre C r t) n) :
    homotopyEquivHomologyEquiv
        (retractionCentralHomotopyEquiv C r δ η hδ hδη hδr hC R hR H hmono) n
        (singularHomologyMap (retractedFibreMap C r δ η hδη R t htδ) n a) =
      singularHomologyMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(ActualQuotientFibre C δ t, QuotientSpace C δ)) n
        ((homeomorphHomologyEquiv (fibreRadiusHomeomorph C r δ t hδr hC htδ) n).symm a) := by
  let E := homotopyEquivHomologyEquiv
    (retractionCentralHomotopyEquiv C r δ η hδ hδη hδr hC R hR H hmono) n
  let F := homeomorphHomologyEquiv (fibreRadiusHomeomorph C r δ t hδr hC htδ) n
  obtain ⟨b, rfl⟩ := F.surjective a
  have hf := congrArg (fun f : C(ActualQuotientFibre C δ t, QuotientCentralFibre C r) =>
    singularHomologyMap f n)
    (retractionCentralHomotopyEquiv_inv_comp_fibre C r δ η hδ hδη hδr hC R hR H hmono t htδ)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hf
  have hb := LinearMap.congr_fun hf b
  change E.symm (singularHomologyMap
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(ActualQuotientFibre C δ t, QuotientSpace C δ)) n b) =
    singularHomologyMap (retractedFibreMap C r δ η hδη R t htδ) n (F b) at hb
  change E (singularHomologyMap (retractedFibreMap C r δ η hδη R t htδ) n (F b)) =
    singularHomologyMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(ActualQuotientFibre C δ t, QuotientSpace C δ)) n (F.symm (F b))
  rw [F.symm_apply_apply, ← hb, E.apply_symm_apply]

include hδ hδr hC hR H hmono in
/-- The actual degree-one map of a retraction restriction is precisely
the source lattice projection; no homology comparison is supplied. -/
theorem retractedFibreMap_singularH1_projection (hδ1 : δ < 1) (hDrift : SmallDrift C δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ) :
    ∃ ef : SingularHomology (ActualQuotientFibre C r t) 1 ≃ₗ[ℤ] Lattice,
      ∃ eq : SingularHomology (QuotientCentralFibre C r) 1 ≃ₗ[ℤ] (Fin 2 → ℤ),
        ∀ a, eq (singularHomologyMap (retractedFibreMap C r δ η hδη R t htδ) 1 a) =
          CuspUniformization.cuspLatticeProjection (ef a) := by
  have hCδ : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    fun i j => (hC i j).mono (Metric.ball_subset_ball hδr)
  obtain ⟨efδ, eqδ, hm⟩ :=
    CuspUniformization.nonzero_fibre_singularH1_projection C δ hδ hδ1 hCδ hDrift ht htδ
  let E := homotopyEquivHomologyEquiv
    (retractionCentralHomotopyEquiv C r δ η hδ hδη hδr hC R hR H hmono) 1
  let F := homeomorphHomologyEquiv (fibreRadiusHomeomorph C r δ t hδr hC htδ) 1
  refine ⟨F.symm.trans efδ, E.trans eqδ, ?_⟩
  intro a
  change eqδ (E (singularHomologyMap (retractedFibreMap C r δ η hδη R t htδ) 1 a)) =
    CuspUniformization.cuspLatticeProjection (efδ (F.symm a))
  rw [show E (singularHomologyMap (retractedFibreMap C r δ η hδη R t htδ) 1 a) =
    singularHomologyMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(ActualQuotientFibre C δ t, QuotientSpace C δ)) 1 (F.symm a) from
        retractedFibreMap_homology C r δ η hδ hδη hδr hC R hR H hmono t htδ 1 a]
  exact hm (F.symm a)

end Wikipedia.HopfProblem.CuspCentralHomology
