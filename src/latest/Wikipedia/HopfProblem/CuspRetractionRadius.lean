import Wikipedia.HopfProblem.CuspRetractionQuotient
import Mathlib.Topology.LocalAtTarget

/-!
# Independence of the ambient radius for closed cusp quotients

For `η < ε`, the literal closed subspace of the radius-`ε` cusp quotient is
an open quotient of the same closed toric tube `ClosedTube η`.  Its fibres
are the twisted lattice orbits, independently of the ambient radius.
This gives the representative-preserving homeomorphism between two such
closed subspaces, without a properness or small-drift hypothesis.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- The quotient map from the radius-independent closed toric tube. -/
def closedQuotientMap {ε η : ℝ} (hηε : η < ε) (x : ClosedTube η) :
    ClosedQuotient C ε η :=
  ⟨quotientMap C ε ⟨x, by
      change time (x : Space) ∈ Metric.ball 0 ε
      simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩, x.2⟩

@[simp] theorem closedQuotientMap_projection {ε η : ℝ} (hηε : η < ε)
    (x : ClosedTube η) :
    projection C ε (closedQuotientMap C hηε x) = time (x : Space) := rfl

theorem closedQuotientMap_surjective {ε η : ℝ} (hηε : η < ε) :
    Function.Surjective (closedQuotientMap C hηε) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨⟨x, hq⟩, rfl⟩

private def closedTubePreimageHomeomorph {ε η : ℝ} (hηε : η < ε) :
    ClosedTube η ≃ₜ
      (quotientMap C ε ⁻¹' {q : QuotientSpace C ε | ‖projection C ε q‖ ≤ η}) where
  toFun x := ⟨⟨x, by
    change time (x : Space) ∈ Metric.ball 0 ε
    simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem closedQuotientMap_isOpenQuotientMap {ε η : ℝ} (hηε : η < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (closedQuotientMap C hηε) := by
  let := tubeAction C (disc ε)
  let := continuous_action C ε hC
  have hq : IsOpenQuotientMap (quotientMap C ε) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact (hq.restrictPreimage {q : QuotientSpace C ε | ‖projection C ε q‖ ≤ η}).comp
    (closedTubePreimageHomeomorph C hηε).isOpenQuotientMap

theorem closedQuotientMap_eq_iff {ε η : ℝ} (hηε : η < ε) (x y : ClosedTube η) :
    closedQuotientMap C hηε x = closedQuotientMap C hηε y ↔
      ∃ v : Fin 2 → ℤ, twistedTranslate C v (y : Space) = (x : Space) := by
  let := tubeAction C (disc ε)
  constructor
  · intro h
    have hrel := Quotient.exact (congrArg Subtype.val h)
    change (⟨(x : Space), _⟩ : Tube (disc ε)) ∈
      MulAction.orbit LatticeGroup (⟨(y : Space), _⟩ : Tube (disc ε)) at hrel
    obtain ⟨g, hg⟩ := hrel
    exact ⟨g.toAdd, congrArg Subtype.val hg⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    apply Quotient.sound
    change (⟨(x : Space), _⟩ : Tube (disc ε)) ∈
      MulAction.orbit LatticeGroup (⟨(y : Space), _⟩ : Tube (disc ε))
    exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩

private def closedRepresentative {ε η : ℝ} (hηε : η < ε)
    (q : ClosedQuotient C ε η) : ClosedTube η :=
  (closedQuotientMap_surjective C hηε q).choose

private theorem closedRepresentative_spec {ε η : ℝ} (hηε : η < ε)
    (q : ClosedQuotient C ε η) :
    closedQuotientMap C hηε (closedRepresentative C hηε q) = q :=
  (closedQuotientMap_surjective C hηε q).choose_spec

/-- Change only the ambient radius, keeping the toric representative. -/
def closedQuotientRadiusChange {δ ε η : ℝ} (hηδ : η < δ) (hηε : η < ε)
    (q : ClosedQuotient C δ η) : ClosedQuotient C ε η :=
  closedQuotientMap C hηε (closedRepresentative C hηδ q)

@[simp] theorem closedQuotientRadiusChange_closedQuotientMap {δ ε η : ℝ}
    (hηδ : η < δ) (hηε : η < ε) (x : ClosedTube η) :
    closedQuotientRadiusChange C hηδ hηε (closedQuotientMap C hηδ x) =
      closedQuotientMap C hηε x := by
  apply (closedQuotientMap_eq_iff C hηε _ _).mpr
  exact (closedQuotientMap_eq_iff C hηδ _ _).mp
    (closedRepresentative_spec C hηδ (closedQuotientMap C hηδ x))

theorem closedQuotientRadiusChange_inverse {δ ε η : ℝ}
    (hηδ : η < δ) (hηε : η < ε) (q : ClosedQuotient C δ η) :
    closedQuotientRadiusChange C hηε hηδ (closedQuotientRadiusChange C hηδ hηε q) = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηδ q
  simp only [closedQuotientRadiusChange_closedQuotientMap]

theorem closedQuotientRadiusChange_continuous {δ ε η : ℝ}
    (hηδ : η < δ) (hηε : η < ε)
    (hCδ : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ))
    (hCε : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Continuous (closedQuotientRadiusChange C hηδ hηε) := by
  apply (closedQuotientMap_isOpenQuotientMap C hηδ hCδ).continuous_comp_iff.mp
  have he : closedQuotientRadiusChange C hηδ hηε ∘ closedQuotientMap C hηδ =
      closedQuotientMap C hηε := by
    funext x
    exact closedQuotientRadiusChange_closedQuotientMap C hηδ hηε x
  rw [he]
  exact (closedQuotientMap_isOpenQuotientMap C hηε hCε).continuous

/-- The literal closed cusp subspace is independent of an ambient radius
larger than its closed radius. No positivity or smallness assumption is needed. -/
def closedQuotientRadiusHomeomorph {δ ε η : ℝ} (hδε : δ ≤ ε) (hηδ : η < δ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    ClosedQuotient C δ η ≃ₜ ClosedQuotient C ε η where
  toFun := closedQuotientRadiusChange C hηδ (hηδ.trans_le hδε)
  invFun := closedQuotientRadiusChange C (hηδ.trans_le hδε) hηδ
  left_inv := closedQuotientRadiusChange_inverse C hηδ (hηδ.trans_le hδε)
  right_inv := closedQuotientRadiusChange_inverse C (hηδ.trans_le hδε) hηδ
  continuous_toFun := closedQuotientRadiusChange_continuous C hηδ (hηδ.trans_le hδε)
    (fun i j => (hC i j).mono (Metric.ball_subset_ball hδε)) hC
  continuous_invFun := closedQuotientRadiusChange_continuous C (hηδ.trans_le hδε) hηδ
    hC (fun i j => (hC i j).mono (Metric.ball_subset_ball hδε))

@[simp] theorem closedQuotientRadiusHomeomorph_closedQuotientMap {δ ε η : ℝ}
    (hδε : δ ≤ ε) (hηδ : η < δ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (x : ClosedTube η) :
    closedQuotientRadiusHomeomorph C hδε hηδ hC (closedQuotientMap C hηδ x) =
      closedQuotientMap C (hηδ.trans_le hδε) x :=
  closedQuotientRadiusChange_closedQuotientMap C hηδ (hηδ.trans_le hδε) x

@[simp] theorem closedQuotientRadiusHomeomorph_symm_closedQuotientMap {δ ε η : ℝ}
    (hδε : δ ≤ ε) (hηδ : η < δ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (x : ClosedTube η) :
    (closedQuotientRadiusHomeomorph C hδε hηδ hC).symm
      (closedQuotientMap C (hηδ.trans_le hδε) x) = closedQuotientMap C hηδ x :=
  closedQuotientRadiusChange_closedQuotientMap C (hηδ.trans_le hδε) hηδ x

theorem closedQuotientRadiusHomeomorph_base {δ ε η : ℝ}
    (hδε : δ ≤ ε) (hηδ : η < δ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (q : ClosedQuotient C δ η) :
    projection C ε (closedQuotientRadiusHomeomorph C hδε hηδ hC q) = projection C δ q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηδ q
  simp only [closedQuotientRadiusHomeomorph_closedQuotientMap, closedQuotientMap_projection]

theorem closedQuotientRadiusHomeomorph_symm_base {δ ε η : ℝ}
    (hδε : δ ≤ ε) (hηδ : η < δ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (q : ClosedQuotient C ε η) :
    projection C δ ((closedQuotientRadiusHomeomorph C hδε hηδ hC).symm q) =
      projection C ε q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C (hηδ.trans_le hδε) q
  simp only [closedQuotientRadiusHomeomorph_symm_closedQuotientMap, closedQuotientMap_projection]

end Wikipedia.HopfProblem.CuspRetraction
