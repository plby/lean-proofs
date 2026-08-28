import Wikipedia.HopfProblem.CuspCentralHomologyRadius
import Wikipedia.HopfProblem.CuspPositiveRetractionCusp
import Mathlib.Topology.Homotopy.Equiv

/-!
# Restricting the constructed cusp deformation to smaller open tubes

The closed-tube deformation already proved for the actual cusp has
nonincreasing base norm.  It therefore restricts to every smaller open
tube, with the central fibre fixed pointwise.  This gives a genuine
homotopy equivalence with the actual central fibre and identifies its
forward map with inclusion, followed by the representative-preserving
change of ambient radius.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspQuotient CuspRetraction

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)

/-- The literal central inclusion in an open sub-tube. -/
def centralIntoOpen (hδ : 0 < δ) :
    C(QuotientCentralFibre C r, OpenQuotient C r δ) where
  toFun q := ⟨q.1, by
    rw [q.2, norm_zero]
    exact hδ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- The inclusion of a smaller open tube into a closed one. -/
def openIntoClosed (hδη : δ ≤ η) :
    C(OpenQuotient C r δ, ClosedQuotient C r η) where
  toFun q := ⟨q, q.2.le.trans hδη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem openIntoClosed_centralIntoOpen (hδ : 0 < δ) (hδη : δ ≤ η)
    (q : QuotientCentralFibre C r) :
    openIntoClosed C r δ η hδη (centralIntoOpen C r δ hδ q) =
      quotientCentralIntoClosed C r η (hδ.le.trans hδη) q := rfl

/-- Restrict the endpoint of a genuine closed-tube deformation. -/
def restrictClosedRetraction (hδη : δ ≤ η)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r)) :
    C(OpenQuotient C r δ, QuotientCentralFibre C r) :=
  R.comp (openIntoClosed C r δ η hδη)

theorem restrictClosedRetraction_comp_inclusion (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hR : R.comp (quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
      ContinuousMap.id (QuotientCentralFibre C r)) :
    (restrictClosedRetraction C r δ η hδη R).comp (centralIntoOpen C r δ hδ) =
      ContinuousMap.id (QuotientCentralFibre C r) := by
  apply ContinuousMap.ext
  intro q
  exact ContinuousMap.congr_fun hR q

/-- The norm estimate, rather than an assumed deformation theorem,
makes the constructed homotopy remain in the open subspace. -/
def restrictClosedHomotopy (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
      ((quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
      {q : ClosedQuotient C r η | projection C r q = 0})
    (hmono : ∀ s q, ‖projection C r (H (s, q))‖ ≤ ‖projection C r q‖) :
    (ContinuousMap.id (OpenQuotient C r δ)).HomotopyRel
      ((centralIntoOpen C r δ hδ).comp (restrictClosedRetraction C r δ η hδη R))
      {q : OpenQuotient C r δ | projection C r q = 0} where
  toFun p := ⟨H (p.1, openIntoClosed C r δ η hδη p.2),
    (hmono p.1 (openIntoClosed C r δ η hδη p.2)).trans_lt p.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (H.continuous.comp (continuous_fst.prodMk
        ((openIntoClosed C r δ η hδη).continuous.comp continuous_snd)))
  map_zero_left q := by
    apply Subtype.ext
    exact congrArg (fun x : ClosedQuotient C r η => (x : QuotientSpace C r))
      (H.map_zero_left (openIntoClosed C r δ η hδη q))
  map_one_left q := by
    apply Subtype.ext
    exact congrArg (fun x : ClosedQuotient C r η => (x : QuotientSpace C r))
      (H.map_one_left (openIntoClosed C r δ η hδη q))
  prop' s q hq := by
    apply Subtype.ext
    exact congrArg (fun x : ClosedQuotient C r η => (x : QuotientSpace C r))
      (H.eq_fst s (show projection C r (openIntoClosed C r δ η hδη q) = 0 from hq))

/-- Actual central inclusion is a homotopy equivalence on every open
sub-tube to which the proved norm-monotone deformation restricts. -/
def openCentralHomotopyEquiv (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(ClosedQuotient C r η, QuotientCentralFibre C r))
    (hR : R.comp (quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
      ContinuousMap.id (QuotientCentralFibre C r))
    (H : (ContinuousMap.id (ClosedQuotient C r η)).HomotopyRel
      ((quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
      {q : ClosedQuotient C r η | projection C r q = 0})
    (hmono : ∀ s q, ‖projection C r (H (s, q))‖ ≤ ‖projection C r q‖) :
    QuotientCentralFibre C r ≃ₕ OpenQuotient C r δ where
  toFun := centralIntoOpen C r δ hδ
  invFun := restrictClosedRetraction C r δ η hδη R
  left_inv := by rw [restrictClosedRetraction_comp_inclusion C r δ η hδ hδη R hR]
  right_inv := ⟨(restrictClosedHomotopy C r δ η hδ hδη R H hmono).toHomotopy.symm⟩

/-- Central inclusion expressed in the quotient constructed directly at
the smaller radius.  It preserves the same actual toric representative. -/
def centralIntoSmallerQuotient (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    C(QuotientCentralFibre C r, QuotientSpace C δ) :=
  ((openQuotientRadiusHomeomorph C hδr hC).symm :
    C(OpenQuotient C r δ, QuotientSpace C δ)).comp (centralIntoOpen C r δ hδ)

/-- A direct consequence of the constructed closed-tube deformation:
all sufficiently small actual open cusp quotients are homotopy
equivalent to the literal central fibre of the original cusp. -/
theorem exists_centralHomotopyEquiv (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < r ∧ δ₀ < 1 ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ → ∀ hδr : δ ≤ r,
        ∃ e : QuotientCentralFibre C r ≃ₕ QuotientSpace C δ,
          e.toFun = centralIntoSmallerQuotient C r δ hδ hδr hC := by
  obtain ⟨δ₀, hδ₀, hδ₀r, hδ₀1, hex⟩ :=
    CuspPositiveRetraction.exists_closed_quotient_strongDeformationRetraction C hr hC
  refine ⟨δ₀, hδ₀, hδ₀r, hδ₀1, ?_⟩
  intro δ hδ hδδ₀ hδr
  obtain ⟨R, hR, H, hmono⟩ := hex δ₀ hδ₀ le_rfl
  let e := openCentralHomotopyEquiv C r δ δ₀ hδ hδδ₀ R hR H hmono
  refine ⟨e.trans (openQuotientRadiusHomeomorph C hδr hC).symm.toHomotopyEquiv, rfl⟩

end Wikipedia.HopfProblem.CuspCentralHomology
