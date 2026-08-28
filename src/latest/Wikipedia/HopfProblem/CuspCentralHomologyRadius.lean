import Wikipedia.HopfProblem.CuspRetractionRadius
import Wikipedia.HopfProblem.CuspHoneycombHexagonGluing

/-!
# Actual open sub-tubes and change of ambient cusp radius

The open radius-`δ` subspace of a cusp quotient of radius `r` is the
quotient of the literal radius-`δ` toric tube.  Its fibres are exactly the
original twisted lattice orbits.  Thus it is homeomorphic to the cusp
quotient constructed directly at radius `δ`, without a properness or
Hausdorff hypothesis.  All maps preserve the toric representative.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

theorem cuspQuotientMap_surjective (δ : ℝ) :
    Function.Surjective (quotientMap C δ) := Quotient.mk_surjective

/-- A literal open sub-tube of the actual cusp quotient. -/
abbrev OpenQuotient (r δ : ℝ) :=
  {q : QuotientSpace C r // ‖projection C r q‖ < δ}

/-- Projection from the smaller toric tube to the actual open subspace. -/
def openQuotientMap {r δ : ℝ} (hδr : δ ≤ r) (x : Tube (disc δ)) :
    OpenQuotient C r δ :=
  ⟨quotientMap C r ⟨x, by
    have hx : time (x : Space) ∈ Metric.ball 0 δ := x.2
    exact Metric.ball_subset_ball hδr hx⟩, by
      change ‖time (x : Space)‖ < δ
      have hx : time (x : Space) ∈ Metric.ball 0 δ := x.2
      simpa only [Metric.mem_ball, dist_zero_right] using hx⟩

@[simp] theorem openQuotientMap_projection {r δ : ℝ} (hδr : δ ≤ r)
    (x : Tube (disc δ)) :
    projection C r (openQuotientMap C hδr x) = time (x : Space) := rfl

theorem openQuotientMap_surjective {r δ : ℝ} (hδr : δ ≤ r) :
    Function.Surjective (openQuotientMap C hδr) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  change ‖time (x : Space)‖ < δ at hq
  refine ⟨⟨x, ?_⟩, rfl⟩
  change time (x : Space) ∈ Metric.ball 0 δ
  simpa only [Metric.mem_ball, dist_zero_right] using hq

private def openTubePreimageHomeomorph {r δ : ℝ} (hδr : δ ≤ r) :
    Tube (disc δ) ≃ₜ
      (quotientMap C r ⁻¹' {q : QuotientSpace C r | ‖projection C r q‖ < δ}) where
  toFun x := ⟨⟨x, Metric.ball_subset_ball hδr x.2⟩, by
    change ‖time (x : Space)‖ < δ
    have hx : time (x : Space) ∈ Metric.ball 0 δ := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
  invFun x := ⟨x.1.1, by
    change time (x.1 : Space) ∈ Metric.ball 0 δ
    have hx : ‖time (x.1 : Space)‖ < δ := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem openQuotientMap_isOpenQuotientMap {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsOpenQuotientMap (openQuotientMap C hδr) := by
  let := tubeAction C (disc r)
  let := continuous_action C r hC
  have hq : IsOpenQuotientMap (quotientMap C r) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact (hq.restrictPreimage {q : QuotientSpace C r | ‖projection C r q‖ < δ}).comp
    (openTubePreimageHomeomorph C hδr).isOpenQuotientMap

/-- Changing only the ambient radius does not change any orbit relation. -/
theorem openQuotientMap_eq_iff {r δ : ℝ} (hδr : δ ≤ r)
    (x y : Tube (disc δ)) :
    openQuotientMap C hδr x = openQuotientMap C hδr y ↔
      quotientMap C δ x = quotientMap C δ y := by
  let := tubeAction C (disc r)
  let := tubeAction C (disc δ)
  constructor
  · intro h
    have hrel := Quotient.exact (congrArg Subtype.val h)
    change (⟨(x : Space), _⟩ : Tube (disc r)) ∈
      MulAction.orbit LatticeGroup (⟨(y : Space), _⟩ : Tube (disc r)) at hrel
    obtain ⟨g, hg⟩ := hrel
    have hg' : twistedTranslate C g.toAdd (y : Space) = (x : Space) :=
      congrArg (fun z : Tube (disc r) => (z : Space)) hg
    apply Quotient.sound
    change x ∈ MulAction.orbit LatticeGroup y
    exact ⟨g, Subtype.ext hg'⟩
  · intro h
    have hrel := Quotient.exact h
    change x ∈ MulAction.orbit LatticeGroup y at hrel
    obtain ⟨g, hg⟩ := hrel
    have hg' : twistedTranslate C g.toAdd (y : Space) = (x : Space) :=
      congrArg (fun z : Tube (disc δ) => (z : Space)) hg
    apply Subtype.ext
    apply Quotient.sound
    change (⟨(x : Space), _⟩ : Tube (disc r)) ∈
      MulAction.orbit LatticeGroup (⟨(y : Space), _⟩ : Tube (disc r))
    exact ⟨g, Subtype.ext hg'⟩

open CuspHoneycombHexagon.CommonFibres

/-- The actual smaller quotient and the inherited open subspace have the
same original quotient topology, and the map keeps representatives. -/
def openQuotientRadiusHomeomorph {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    QuotientSpace C δ ≃ₜ OpenQuotient C r δ where
  toFun := descend (quotientMap C δ) (openQuotientMap C hδr)
    (cuspQuotientMap_surjective C δ)
  invFun := descend (openQuotientMap C hδr) (quotientMap C δ)
    (openQuotientMap_surjective C hδr)
  left_inv q := by
    obtain ⟨x, rfl⟩ := cuspQuotientMap_surjective C δ q
    rw [descend_apply _ _ _ (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr),
      descend_apply _ _ _ (fun x y => (openQuotientMap_eq_iff C hδr x y).mp)]
  right_inv q := by
    obtain ⟨x, rfl⟩ := openQuotientMap_surjective C hδr q
    rw [descend_apply _ _ _ (fun x y => (openQuotientMap_eq_iff C hδr x y).mp),
      descend_apply _ _ _ (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr)]
  continuous_toFun := descend_continuous _ _ _ isQuotientMap_quotient_mk'
    (openQuotientMap_isOpenQuotientMap C hδr hC).continuous
    (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr)
  continuous_invFun := descend_continuous _ _ _
    (openQuotientMap_isOpenQuotientMap C hδr hC).isQuotientMap
    (quotientMap_continuous C δ)
    (fun x y => (openQuotientMap_eq_iff C hδr x y).mp)

@[simp] theorem openQuotientRadiusHomeomorph_quotientMap {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (x : Tube (disc δ)) :
    openQuotientRadiusHomeomorph C hδr hC (quotientMap C δ x) =
      openQuotientMap C hδr x :=
  descend_apply _ _ _ (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr) x

@[simp] theorem openQuotientRadiusHomeomorph_symm_openQuotientMap {r δ : ℝ}
    (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (x : Tube (disc δ)) :
    (openQuotientRadiusHomeomorph C hδr hC).symm (openQuotientMap C hδr x) =
      quotientMap C δ x :=
  descend_apply _ _ _ (fun x y => (openQuotientMap_eq_iff C hδr x y).mp) x

theorem openQuotientRadiusHomeomorph_projection {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (q : QuotientSpace C δ) :
    projection C r (openQuotientRadiusHomeomorph C hδr hC q) = projection C δ q := by
  obtain ⟨x, rfl⟩ := cuspQuotientMap_surjective C δ q
  rw [openQuotientRadiusHomeomorph_quotientMap]
  rfl

end Wikipedia.HopfProblem.CuspCentralHomology
