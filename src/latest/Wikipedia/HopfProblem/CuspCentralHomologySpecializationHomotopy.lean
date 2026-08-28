import Wikipedia.HopfProblem.CuspCentralHomologySpecializationTransport

/-!
# Compatibility of the prescribed cusp collapse on all other levels

For a fixed central inclusion, any two retractions coming from the
constructed deformation are homotopic: compose the second deformation
with the first retraction.  Applying the already proved controlled
endpoint theorem separately at each other level gives the precise
homotopy assertion of Lemma 7.10(iii).  It does not assert exact endpoint
control simultaneously at every level.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open CuspQuotient CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology

section General

variable {X A : Type} [TopologicalSpace X] [TopologicalSpace A]

/-- Compose a genuine deformation with a retraction that is the identity
on its central subspace.  This constructs the homotopy between endpoints. -/
def retractionEndpointHomotopy (i : C(A, X)) (R S : C(X, A))
    (hR : R.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).Homotopy (i.comp S)) : R.Homotopy S where
  toFun p := R (H p)
  continuous_toFun := R.continuous.comp H.continuous
  map_zero_left x := congrArg R (H.map_zero_left x)
  map_one_left x := (congrArg R (H.map_one_left x)).trans
    (ContinuousMap.congr_fun hR (S x))

end General

/-- The original fibre as a literal subspace of the closed cusp tube. -/
def actualFibreIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) :
    C(ActualQuotientFibre C r t, ClosedQuotient C r η) where
  toFun q := ⟨q.1, by rw [q.2]; exact htη⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- A single constructed retraction has the prescribed endpoint on one
chosen nonzero fibre and the prescribed homotopy class on every other
nonzero fibre of its closed tube.  Consequently all actual induced
singular homology maps agree there in every degree. -/
theorem exists_controlled_retraction_all_levels
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < r ∧ η₀ < 1 ∧
      ∀ (η : ℝ) (hη : 0 < η), η ≤ η₀ → ∀ (hηr : η < r)
        (t₀ : ℂ) (ht₀ : t₀ ≠ 0) (ht₀η : ‖t₀‖ ≤ η),
        ∃ R : C(ClosedQuotient C r η, QuotientCentralFibre C r),
          R.comp (quotientCentralIntoClosed C r η hη.le) =
            ContinuousMap.id (QuotientCentralFibre C r) ∧
          ∃ H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
              ((quotientCentralIntoClosed C r η hη.le).comp R)
              {q : ClosedQuotient C r η | projection C r q = 0},
            (∀ s q, ‖projection C r (H (s, q))‖ ≤ ‖projection C r q‖) ∧
            ∃ hc₀ : Continuous
                (prescribedActualFibreCollapse C r hr hηr t₀ ht₀ ht₀η),
              R.comp (actualFibreIntoClosed C r η t₀ ht₀η) =
                ⟨prescribedActualFibreCollapse C r hr hηr t₀ ht₀ ht₀η, hc₀⟩ ∧
              ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η),
                ∃ hc : Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη),
                  (R.comp (actualFibreIntoClosed C r η t htη)).Homotopic
                    ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ ∧
                  ∀ n, singularHomologyMap (R.comp (actualFibreIntoClosed C r η t htη)) n =
                    singularHomologyMap
                      ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ n := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hret⟩ :=
    exists_controlled_actual_fibre_retraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ hηr t₀ ht₀ ht₀η
  obtain ⟨R, hR, H, hmono, hendpoint⟩ := hret η hη hηη₀ t₀ ht₀ ht₀η
  obtain ⟨hc₀, he₀, _hrep₀⟩ := hendpoint hηr
  refine ⟨R, hR, H, hmono, hc₀, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro q
    exact he₀ q
  · intro t ht htη
    obtain ⟨S, _hS, HS, _hmonoS, hendpointS⟩ := hret η hη hηη₀ t ht htη
    obtain ⟨hc, he, _hrep⟩ := hendpointS hηr
    have hemap : S.comp (actualFibreIntoClosed C r η t htη) =
        (⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :
          C(ActualQuotientFibre C r t, QuotientCentralFibre C r)) := by
      apply ContinuousMap.ext
      intro q
      exact he q
    let K := retractionEndpointHomotopy (quotientCentralIntoClosed C r η hη.le)
      R S hR HS.toHomotopy
    have hk : (R.comp (actualFibreIntoClosed C r η t htη)).Homotopic
        ⟨prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :=
      ⟨(K.comp (ContinuousMap.Homotopy.refl (actualFibreIntoClosed C r η t htη))).cast
        rfl hemap⟩
    exact ⟨hc, hk, fun n => homotopic_homologyMap hk n⟩

end Wikipedia.HopfProblem.CuspCentralHomology
