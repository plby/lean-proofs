/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualStageReduction
import ErdosProblems.Erdos599.GroundingWeakChronology
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# The diagonal-emergence form of source Lemma 7.27

The successor-normalized bookkeeping records a path from
`IE (Y_(a+1))` at stage `a`.  Its coherent emergence index is therefore a
rung index: it is at most `a`, and the exact alternatives are strict prior
emergence and diagonal emergence.  This file records that split without
asserting a false same-stage strict-roof conclusion.

The only graph-specific input is `DiagonalEmergenceClassified`: a record
which first becomes inessential at its own successor rung is accounted for
by the hindrance-rung/new-ray exceptional set.  The theorems below prove
the complete stationary/cardinal consequence of that input.  In
particular, after the exceptional set is removed, stationary many grounded
records have strict prior emergence and hence are already inessential in
the current warp.  If all successor-inessential families have cardinality
below `kappa`, the emergence-fiber injection rules this out.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Obstruction records whose first successor-inessential rung is strictly
earlier than their selection rung. -/
def strictPriorEmergenceStages
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    Set (Stage kappa) :=
  {a | a ∈ L.phi ∧
    L.emergenceIndex hlegal.validBookkeeping a < a}

/-- Obstruction records which first become inessential in the successor
warp immediately following their own selection rung. -/
def diagonalEmergenceStages
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    Set (Stage kappa) :=
  {a | a ∈ L.phi ∧
    L.emergenceIndex hlegal.validBookkeeping a = a}

/-- The full diagonal-classification statement used in the stationary
argument.  The ray half is automatic from minimality of the emergence
index; `FiniteDiagonalEmergenceClassified` below isolates the only genuine
local geometric obligation. -/
def DiagonalEmergenceClassified
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) : Prop :=
  L.diagonalEmergenceStages hlegal ⊆ L.exceptionalStages

/-- The only graph-specific gap in diagonal classification: a selected
finite path whose first successor-inessential rung is its own rung must
come from a hindrance rung.  Rays require no hypothesis; they are handled
by `diagonalEmergence_ray_mem_phiNewRay`. -/
def FiniteDiagonalEmergenceClassified
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) : Prop :=
  ∀ (a : Stage kappa), a ∈ L.diagonalEmergenceStages hlegal →
    ∀ (p : Gamma.DPath) (x : V), L.chosen a = some p →
      Gamma.terminal? p = some x → a ∈ L.phiHindrance

/-- Minimality of the emergence index classifies every diagonal selected
ray as a genuinely new ray of the successor warp.  This is precisely why
the source exceptional set must use successor-normalized indexing. -/
theorem diagonalEmergence_ray_mem_phiNewRay
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} (ha : a ∈ L.diagonalEmergenceStages hlegal)
    {r : DirectedPath.Ray Gamma.graph}
    (hrChosen : L.chosen a = some (Sum.inr r : Gamma.DPath)) :
    a ∈ L.phiNewRay := by
  let B := L.concreteBookkeeping
  let hB : B.IsValid :=
    L.concreteBookkeeping_isValid hlegal.validBookkeeping
  have hrSelected :
      B.selectedPath hB ⟨a, ha.1⟩ = (Sum.inr r : Gamma.DPath) := by
    apply Option.some.inj
    exact (B.chosen_selectedPath hB ⟨a, ha.1⟩).symm.trans hrChosen
  have hemergence : B.emergenceIndex hB a = a := ha.2
  have hrNext : (Sum.inr r : Gamma.DPath) ∈ L.successorWarp a := by
    have hselected := B.selectedPath_mem_emergenceIndex hB ha.1
    rw [hemergence] at hselected
    exact (hrSelected ▸ hselected).1
  refine ⟨(Sum.inr r : Gamma.DPath), hrNext, by simp, ?_⟩
  intro b hba hrEarlier
  have hlt : b < B.emergenceIndex hB a := by
    rw [hemergence]
    exact hba
  have hnot := B.not_mem_inessentialNext_of_lt_emergenceIndex
    hB ha.1 hlt
  apply hnot
  rw [hrSelected]
  exact Gamma.ray_mem_inessentialPaths hrEarlier

/-- Once the finite diagonal case is classified, the full diagonal branch
is exceptional: finite selected paths yield hindrance rungs, while selected
rays yield genuinely new successor rays. -/
theorem diagonalEmergenceClassified_of_finite
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hfinite : L.FiniteDiagonalEmergenceClassified hlegal) :
    L.DiagonalEmergenceClassified hlegal := by
  intro a ha
  obtain ⟨p, hpChosen⟩ :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hlegal.validBookkeeping).1 ha.1
  rcases p with p | r
  · exact Or.inl (hfinite a ha (Sum.inl p) p.finish hpChosen rfl)
  · exact Or.inr
      (L.diagonalEmergence_ray_mem_phiNewRay hlegal ha hpChosen)

theorem phi_eq_strictPriorEmergence_union_diagonalEmergence
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    L.phi = L.strictPriorEmergenceStages hlegal ∪
      L.diagonalEmergenceStages hlegal := by
  ext a
  constructor
  · intro ha
    have hle : L.emergenceIndex hlegal.validBookkeeping a ≤ a :=
      L.emergenceIndex_le hlegal.validBookkeeping ha
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inl ⟨ha, hlt⟩
    · exact Or.inr ⟨ha, heq⟩
  · rintro (ha | ha) <;> exact ha.1

/-- The grounded obstruction stages inherit the exact prior/diagonal
emergence split. -/
theorem phiGround_eq_strictPriorEmergence_union_diagonalEmergence
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    L.phiGround =
      (L.phiGround ∩ L.strictPriorEmergenceStages hlegal) ∪
        (L.phiGround ∩ L.diagonalEmergenceStages hlegal) := by
  have hground : L.phiGround ⊆ L.phi := by
    rintro a ⟨p, hp, _⟩
    exact (L.bookkeeping.mem_phi_iff_exists_chosen
      hlegal.validBookkeeping).2 ⟨p, hp⟩
  rw [← Set.inter_union_distrib_left,
    ← L.phi_eq_strictPriorEmergence_union_diagonalEmergence hlegal]
  exact (Set.inter_eq_left.2 hground).symm

/-- Diagonal classification and nonstationarity of the ordinary
hindrance/new-ray alternative make the grounded diagonal branch
nonstationary. -/
theorem diagonalEmergenceGround_not_stationary
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hclassified : L.DiagonalEmergenceClassified hlegal)
    (hexceptional :
      ¬ Stationary.IsStationaryBelow kappa L.exceptionalStages) :
    ¬ Stationary.IsStationaryBelow kappa
      (L.phiGround ∩ L.diagonalEmergenceStages hlegal) := by
  intro hstationary
  apply hexceptional
  exact hstationary.mono fun _ ha ↦ hclassified ha.2

/-- After diagonal exceptional stages are discarded, a ladder
`kappa`-hindrance retains stationary many grounded records with strict
prior emergence. -/
theorem IsKappaHindrance.strictPriorEmergenceGround_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hclassified : L.DiagonalEmergenceClassified hL.legal)
    (hexceptional :
      ¬ Stationary.IsStationaryBelow kappa L.exceptionalStages) :
    Stationary.IsStationaryBelow kappa
      (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal) := by
  have hground : Stationary.IsStationaryBelow kappa L.phiGround :=
    KappaLadder.IsKappaHindrance.phiGround_isStationary L hL
      hL.legal.regular hL.legal.uncountable
  rw [L.phiGround_eq_strictPriorEmergence_union_diagonalEmergence
    hL.legal] at hground
  have hcof : Order.cof (Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hL.legal.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hL.legal.uncountable).ne'
  exact (isStationary_union_iff hcof).mp hground |>.resolve_right
    (L.diagonalEmergenceGround_not_stationary hL.legal
      hclassified hexceptional)

/-- Strict prior emergence puts the selected record in the current
inessential family.  This is the precise bridge from the rung-index form
of Lemma 7.27 to the old-record branch used by Lemma 7.17. -/
theorem strictPriorEmergenceGround_subset_priorInessentialGround
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    L.phiGround ∩ L.strictPriorEmergenceStages hlegal ⊆
      L.priorInessentialGroundStages := by
  rintro a ⟨hground, ha, hemergence⟩
  let B := L.concreteBookkeeping
  let hB : B.IsValid :=
    L.concreteBookkeeping_isValid hlegal.validBookkeeping
  let e : Stage kappa := L.emergenceIndex hlegal.validBookkeeping a
  let b : Stage kappa := L.successorStage hlegal e
  have hba : b ≤ a :=
    (L.successorStage_le_iff_lt hlegal).2 hemergence
  have hselectedNext :
      B.selectedPath hB ⟨a, ha⟩ ∈
        Gamma.inessentialPaths (L.successorWarp e) := by
    exact B.selectedPath_mem_emergenceIndex hB ha
  have hsuccessor : L.successorWarp e = L.warpAt b := by
    apply congrArg L.accumulated
    apply Subtype.ext
    rfl
  have hselectedCurrent :
      B.selectedPath hB ⟨a, ha⟩ ∈
        Gamma.inessentialPaths (L.warpAt a) := by
    apply hlegal.inessentialPaths_mono_stage hba
    rw [← hsuccessor]
    exact hselectedNext
  refine ⟨hground, B.selectedPath hB ⟨a, ha⟩, ?_, hselectedCurrent⟩
  exact B.chosen_selectedPath hB ⟨a, ha⟩

/-- Source-faithful grounded consequence of Lemma 7.27: the stationary
prior-emergence set is a stationary subset of the records for which the
same-index strict-roof argument is valid. -/
theorem IsKappaHindrance.priorInessentialGround_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hclassified : L.DiagonalEmergenceClassified hL.legal)
    (hexceptional :
      ¬ Stationary.IsStationaryBelow kappa L.exceptionalStages) :
    Stationary.IsStationaryBelow kappa
      L.priorInessentialGroundStages :=
  (KappaLadder.IsKappaHindrance.strictPriorEmergenceGround_isStationary
    L hL hclassified hexceptional).mono
      (L.strictPriorEmergenceGround_subset_priorInessentialGround hL.legal)

/-- If every successor-inessential family has cardinality below `kappa`,
strict prior-emergence stages are nonstationary by pressing down and the
injective emergence-fiber bound. -/
theorem strictPriorEmergenceStages_not_stationary_of_all_small
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hsmall : ∀ i : Stage kappa,
      #(Gamma.inessentialPaths (L.successorWarp i)) < kappa) :
    ¬ Stationary.IsStationaryBelow kappa
      (L.strictPriorEmergenceStages hlegal) := by
  let B := L.concreteBookkeeping
  let hB : B.IsValid :=
    L.concreteBookkeeping_isValid hlegal.validBookkeeping
  have hlarge : ¬ (B.largeInessentialStages).Nonempty := by
    rintro ⟨i, hi⟩
    exact (not_le_of_gt (hsmall i)) hi
  have hreg : Stationary.IsRegressiveOn
      (B.phi \ L.diagonalEmergenceStages hlegal)
      (B.emergenceIndex hB) := by
    intro a ha
    have hle : B.emergenceIndex hB a ≤ a :=
      B.emergenceIndex_le hB ha.1
    exact lt_of_le_of_ne hle fun heq ↦ ha.2 ⟨ha.1, heq⟩
  have hnot := B.regularEmergence_not_stationary
    hlegal.regular hlegal.uncountable hB
      (L.diagonalEmergenceStages hlegal) hlarge hreg
  intro hstationary
  apply hnot
  apply hstationary.mono
  intro a ha
  exact ⟨ha.1, fun hdiag ↦ (ne_of_lt ha.2) hdiag.2⟩

/-- Full forward contradiction behind source Lemma 7.27.  Under the
absence of a stationary ordinary hindrance/new-ray alternative and of a
large earlier inessential family, diagonal classification rules out a
ladder `kappa`-hindrance. -/
theorem not_isKappaHindrance_of_classified_exceptional_nonstationary_all_small
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hclassified : L.DiagonalEmergenceClassified hlegal)
    (hexceptional :
      ¬ Stationary.IsStationaryBelow kappa L.exceptionalStages)
    (hsmall : ∀ i : Stage kappa,
      #(Gamma.inessentialPaths (L.successorWarp i)) < kappa) :
    ¬ L.IsKappaHindrance := by
  intro hL
  have hprior : Stationary.IsStationaryBelow kappa
      (L.phiGround ∩ L.strictPriorEmergenceStages hlegal) := by
    exact KappaLadder.IsKappaHindrance.strictPriorEmergenceGround_isStationary
      L hL hclassified hexceptional
  exact L.strictPriorEmergenceStages_not_stationary_of_all_small
    hlegal hsmall (hprior.mono Set.inter_subset_right)

end KappaLadder
end DWeb
end Erdos599
