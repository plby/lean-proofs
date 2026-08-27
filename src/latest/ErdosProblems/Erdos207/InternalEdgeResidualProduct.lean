/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeScheduledStarBound
import ErdosProblems.Erdos207.PreliminaryOuterResidual
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The residual-edge factor for scheduled internal triangles

An internal triangle can be selected only if its unique outside--outside
edge survived the preliminary phase.  This file identifies that edge
canonically, so the preliminary residual factor and the conditional
internal-selection factor can later be multiplied instead of estimated
separately.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Graph edges of a triangle whose two endpoints lie outside `U`. -/
def triangleOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (T : TripleOn V) : Finset (Sym2 V) :=
  (tripleEdgeFinset T).filter fun e ↦ e.out.1 ∉ U ∧ e.out.2 ∉ U

@[simp]
lemma mem_triangleOuterEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {T : TripleOn V} {e : Sym2 V} :
    e ∈ triangleOuterEdges U T ↔
      e ∈ tripleEdgeFinset T ∧ e.out.1 ∉ U ∧ e.out.2 ∉ U := by
  simp [triangleOuterEdges]

/-- The unique outside edge of a scheduled internal triangle is its
scheduled edge. -/
lemma triangleOuterEdges_internalEdgeTriangle
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} (e : Sym2 V) (hne : e.out.1 ≠ e.out.2)
    (w : ThirdVertex e.out.1 e.out.2)
    (hleft : e.out.1 ∉ U) (hright : e.out.2 ∉ U) (hw : w.1 ∈ U) :
    triangleOuterEdges U (internalEdgeTriangle e hne w) = {e} := by
  ext f
  simp only [mem_triangleOuterEdges_iff, mem_singleton]
  constructor
  · rintro ⟨hfT, hfleft, hfright⟩
    have hfT' : s(f.out.1, f.out.2) ∈
        tripleEdgeFinset (internalEdgeTriangle e hne w) := by
      simpa only [f.out_eq] using hfT
    obtain ⟨hfstT, hsndT, hfne⟩ := mk_mem_tripleEdgeFinset_iff.mp hfT'
    have hfst : f.out.1 = e.out.1 ∨ f.out.1 = e.out.2 ∨ f.out.1 = w.1 := by
      simpa [internalEdgeTriangle, thirdVertexTriple, tripleOfThree] using hfstT
    have hsnd : f.out.2 = e.out.1 ∨ f.out.2 = e.out.2 ∨ f.out.2 = w.1 := by
      simpa [internalEdgeTriangle, thirdVertexTriple, tripleOfThree] using hsndT
    have hfst' : f.out.1 = e.out.1 ∨ f.out.1 = e.out.2 := by
      rcases hfst with hfst | hfst | hfst
      · exact Or.inl hfst
      · exact Or.inr hfst
      · exact (hfleft (hfst ▸ hw)).elim
    have hsnd' : f.out.2 = e.out.1 ∨ f.out.2 = e.out.2 := by
      rcases hsnd with hsnd | hsnd | hsnd
      · exact Or.inl hsnd
      · exact Or.inr hsnd
      · exact (hfright (hsnd ▸ hw)).elim
    apply Sym2.eq_of_ne_mem hfne (Sym2.out_fst_mem f)
      (Sym2.out_snd_mem f)
    · rw [← e.out_eq, Sym2.mem_iff]
      exact hfst'
    · rw [← e.out_eq, Sym2.mem_iff]
      exact hsnd'
  · intro hfe
    rw [hfe]
    exact ⟨by
      change e ∈ tripleEdgeFinset (thirdVertexTriple hne w)
      simpa only [e.out_eq] using mk_mem_tripleEdgeFinset_iff.mpr
        ⟨left_mem_thirdVertexTriple hne w,
          right_mem_thirdVertexTriple hne w, hne⟩,
      hleft, hright⟩

/-- All canonical outside edges required by a fixed family of proposed
internal triangles. -/
def internalRequiredOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (Q : TripleSystemOn V) : Finset (Sym2 V) :=
  Q.biUnion (triangleOuterEdges U)

lemma internalRequiredOuterEdges_subset_of_usesScheduled
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {P0 P Q : TripleSystemOn V}
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 P)
    (hQ : Q ⊆ P \ P0) :
    internalRequiredOuterEdges U Q ⊆ E := by
  intro e he
  obtain ⟨T, hTQ, heT⟩ := mem_biUnion.mp he
  obtain ⟨f, hfE, hne, w, hwU, hTf⟩ := huse T (hQ hTQ)
  have hout := houter f hfE
  have hsingleton := triangleOuterEdges_internalEdgeTriangle
    f hne w hout.1 hout.2 hwU
  rw [hTf, hsingleton] at heT
  have hef : e = f := by simpa only [mem_singleton] using heT
  rw [hef]
  exact hfE

lemma pairwiseDisjoint_triangleOuterEdges_of_packing
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {P Q : TripleSystemOn V}
    (hpacking : IsPackingOn P) (hQP : Q ⊆ P) :
    (Q : Set (TripleOn V)).PairwiseDisjoint (triangleOuterEdges U) := by
  intro T hTQ T' hT'Q hTT'
  change Disjoint (triangleOuterEdges U T) (triangleOuterEdges U T')
  rw [Finset.disjoint_left]
  intro e heT heT'
  have heTedge := (mem_triangleOuterEdges_iff.mp heT).1
  have heT'edge := (mem_triangleOuterEdges_iff.mp heT').1
  have heTedge' : s(e.out.1, e.out.2) ∈ tripleEdgeFinset T := by
    simpa only [e.out_eq] using heTedge
  have heT'edge' : s(e.out.1, e.out.2) ∈ tripleEdgeFinset T' := by
    simpa only [e.out_eq] using heT'edge
  obtain ⟨he1T, he2T, hene⟩ := mk_mem_tripleEdgeFinset_iff.mp heTedge'
  obtain ⟨he1T', he2T', _⟩ := mk_mem_tripleEdgeFinset_iff.mp heT'edge'
  exact hTT' (hpacking e.out.1 e.out.2 hene T (hQP hTQ)
    he1T he2T T' (hQP hT'Q) he1T' he2T')

/-- A feasible fixed family of new internal triangles has exactly one
distinct required preliminary residual edge per triangle. -/
lemma card_internalRequiredOuterEdges_of_usesScheduled
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {P0 P Q : TripleSystemOn V}
    (hpacking : IsPackingOn P)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 P)
    (hQ : Q ⊆ P \ P0) :
    (internalRequiredOuterEdges U Q).card = Q.card := by
  rw [internalRequiredOuterEdges,
    Finset.card_biUnion (pairwiseDisjoint_triangleOuterEdges_of_packing
      hpacking (fun T hT ↦ (mem_sdiff.mp (hQ hT)).1))]
  calc
    ∑ T ∈ Q, (triangleOuterEdges U T).card = ∑ _T ∈ Q, 1 := by
      apply sum_congr rfl
      intro T hTQ
      obtain ⟨e, heE, hne, w, hwU, hTeq⟩ := huse T (hQ hTQ)
      have hout := houter e heE
      rw [hTeq, triangleOuterEdges_internalEdgeTriangle
        e hne w hout.1 hout.2 hwU, card_singleton]
    _ = Q.card := by simp

/-- A crossing edge still uncovered after both subphases was already a
residual outer edge after the preliminary subphase. -/
lemma preliminaryResidualCrossingEdges_union_subset_residualOuter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P Q : TripleSystemOn V) :
    preliminaryResidualCrossingEdges G U (P ∪ Q) ⊆
      preliminaryResidualOuterEdges G U P := by
  intro e he
  have hdata := mem_sdiff.mp he
  apply mem_sdiff.mpr
  refine ⟨crossingEdges_subset_outerGraphEdges G U hdata.1, ?_⟩
  intro heCovered
  exact hdata.2 (graphEdges_coveredGraph_mono subset_union_left heCovered)

/-- Required outside--outside edges of internal triangles are disjoint from
the final residual crossing reserve. -/
lemma internalRequiredOuterEdges_disjoint_residualCrossing
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P0 P Q : TripleSystemOn V}
    (houter : ∀ e ∈ preliminaryResidualInternalEdges G U P0,
      e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U
      (preliminaryResidualInternalEdges G U P0) P0 P)
    (hQ : Q ⊆ P \ P0) :
    Disjoint (internalRequiredOuterEdges U Q)
      (preliminaryResidualCrossingEdges G U P) := by
  apply Disjoint.mono
    (internalRequiredOuterEdges_subset_of_usesScheduled houter huse hQ)
    (preliminaryResidualCrossingEdges_subset_crossingEdges G U P)
  apply Disjoint.mono_left
    (preliminaryResidualInternalEdges_subset_internalOuterEdges G U P0)
  exact internalOuterEdges_disjoint_crossingEdges G U

/-- The internal requirements and final crossing requirements therefore
have additive cardinalities. -/
lemma card_internalRequired_union_residualCrossing_of_usesScheduled
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P0 P Q : TripleSystemOn V}
    (hpacking : IsPackingOn P)
    (houter : ∀ e ∈ preliminaryResidualInternalEdges G U P0,
      e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U
      (preliminaryResidualInternalEdges G U P0) P0 P)
    (hQ : Q ⊆ P \ P0) (E : Finset (Sym2 V))
    (hE : E ⊆ preliminaryResidualCrossingEdges G U P) :
    (internalRequiredOuterEdges U Q ∪ E).card = Q.card + E.card := by
  rw [card_union_of_disjoint
    ((internalRequiredOuterEdges_disjoint_residualCrossing
      houter huse hQ).mono_right hE),
    card_internalRequiredOuterEdges_of_usesScheduled
      hpacking houter huse hQ]

/-- The union of the preliminary family and the subsequently selected
internal family. -/
def preliminaryInternalCombinedAdded
    {Xi Zeta V : Type*} [DecidableEq V]
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (z : Xi × Zeta) : TripleSystemOn V :=
  addedPre z.1 ∪ addedInt z.1 z.2

lemma FiniteLaw.exists_mass_pos_and_of_probability_pos
    {Omega : Type*} [Fintype Omega]
    (L : FiniteLaw Omega) {P : Omega → Prop}
    (hP : 0 < L.probability P) : ∃ omega, 0 < L.mass omega ∧ P omega := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : L.probability P = 0 := by
    unfold FiniteLaw.probability
    apply Finset.sum_eq_zero
    intro omega _homega
    by_cases h : P omega
    · have hmass : L.mass omega = 0 :=
        le_antisymm (not_lt.mp (fun hmass ↦ hnone omega hmass h)) zero_le
      simp [h, hmass]
    · simp [h]
  exact (hzero ▸ hP).false

/-- Fixed-part product estimate for the preliminary/internal composition.
The preliminary residual factor is charged once for the unique scheduled
outside edge of every prescribed internal triangle. -/
theorem FiniteLaw.jointBind_probability_preliminary_internal_parts_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V]
    (Kpre : FiniteLaw Xi) (Kint : Xi → FiniteLaw Zeta)
    (G : SimpleGraph V) (U : Finset V)
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (alpha eta delta : ℝ≥0)
    (hpre : ∀ Q E,
      Kpre.probability (fun xi ↦
        Q ⊆ addedPre xi ∧
          E ⊆ preliminaryResidualOuterEdges G U (addedPre xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hC4 : ∀ xi Q,
      (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤
        delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Qpre Qint : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z)) ≤
      alpha ^ Qpre.card * (eta * delta) ^ Qint.card * eta ^ Efix.card := by
  classical
  let Required : Finset (Sym2 V) :=
    internalRequiredOuterEdges U Qint ∪ Efix
  let PreEvent : Xi → Prop := fun xi ↦
    Qpre ⊆ addedPre xi ∧
      Required ⊆ preliminaryResidualOuterEdges G U (addedPre xi)
  let IntEvent : Xi → Zeta → Prop := fun xi z ↦
    Qint ⊆ addedInt xi z ∧
      Efix ⊆ preliminaryResidualCrossingEdges G U
        (preliminaryInternalCombinedAdded addedPre addedInt (xi, z))
  have houter : ∀ xi e,
      e ∈ preliminaryResidualInternalEdges G U (addedPre xi) →
      e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro xi e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        G U (addedPre xi) he)).2
  have hsupportImp : ∀ z,
      (IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z)) →
      (Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z)) →
      PreEvent z.1 := by
    intro z hs hz
    refine ⟨hz.1, ?_⟩
    have hQdiff : Qint ⊆
        preliminaryInternalCombinedAdded addedPre addedInt z \ addedPre z.1 := by
      intro T hT
      exact mem_sdiff.mpr ⟨mem_union_right _ (hz.2.1 hT),
        fun hTpre ↦
          Finset.disjoint_left.mp hs.2.1 hTpre (hz.2.1 hT)⟩
    have hrequired : internalRequiredOuterEdges U Qint ⊆
        preliminaryResidualOuterEdges G U (addedPre z.1) :=
      (internalRequiredOuterEdges_subset_of_usesScheduled
        (houter z.1) hs.2.2 hQdiff).trans
          (preliminaryResidualInternalEdges_subset_residualOuterEdges
            G U (addedPre z.1))
    have hresidual : Efix ⊆
        preliminaryResidualOuterEdges G U (addedPre z.1) :=
      hz.2.2.trans
        (preliminaryResidualCrossingEdges_union_subset_residualOuter
          G U (addedPre z.1) (addedInt z.1 z.2))
    exact union_subset hrequired hresidual
  have hmono :
      (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z)) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          PreEvent z.1 ∧ IntEvent z.1 z.2) := by
    apply (Kpre.jointBind Kint).probability_mono_of_supported hstruct
    intro z hs hz
    exact ⟨hsupportImp z hs hz, ⟨hz.2.1, hz.2.2⟩⟩
  have hconditional : ∀ xi, 0 < Kpre.mass xi → PreEvent xi →
      (Kint xi).probability (IntEvent xi) ≤ delta ^ Qint.card := by
    intro xi hmass _hpre
    have hfiber : (Kint xi).SupportedOn fun z ↦
        IsPackingOn
            (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) ∧
          Disjoint (addedPre xi) (addedInt xi z) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges G U (addedPre xi))
            (addedPre xi)
            (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) := by
      intro z hz
      exact hstruct (xi, z)
        (FiniteLaw.jointBind_mass_pos_iff Kpre Kint xi z |>.2
          ⟨hmass, hz⟩)
    calc
      (Kint xi).probability (IntEvent xi) ≤
          (Kint xi).probability (fun z ↦ Qint ⊆ addedInt xi z) := by
        apply (Kint xi).probability_mono_of_supported hfiber
        intro z _hs hz
        exact hz.1
      _ ≤ delta ^ Qint.card := hC4 xi Qint
  have hjoint :
      (Kpre.jointBind Kint).probability (fun z ↦
        PreEvent z.1 ∧ IntEvent z.1 z.2) ≤
        delta ^ Qint.card * Kpre.probability PreEvent := by
    exact Kpre.jointBind_probability_and_le_on_support Kint PreEvent IntEvent
      (delta ^ Qint.card) hconditional
  by_cases hzero :
      (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z)) = 0
  · rw [hzero]
    exact zero_le
  have hpos : 0 < (Kpre.jointBind Kint).probability (fun z ↦
      Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z)) :=
    pos_iff_ne_zero.mpr hzero
  obtain ⟨zWitness, hmassWitness, hzWitness⟩ :=
    (Kpre.jointBind Kint).exists_mass_pos_and_of_probability_pos hpos
  have hsWitness := hstruct zWitness hmassWitness
  have hQdiffWitness : Qint ⊆
      preliminaryInternalCombinedAdded addedPre addedInt zWitness \
        addedPre zWitness.1 := by
    intro T hT
    exact mem_sdiff.mpr ⟨mem_union_right _ (hzWitness.2.1 hT),
      fun hTpre ↦
        Finset.disjoint_left.mp hsWitness.2.1 hTpre (hzWitness.2.1 hT)⟩
  have hcard : Required.card = Qint.card + Efix.card := by
    exact card_internalRequired_union_residualCrossing_of_usesScheduled
      hsWitness.1 (houter zWitness.1) hsWitness.2.2 hQdiffWitness Efix
        hzWitness.2.2
  calc
    (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z)) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          PreEvent z.1 ∧ IntEvent z.1 z.2) := hmono
    _ ≤ delta ^ Qint.card * Kpre.probability PreEvent := hjoint
    _ ≤ delta ^ Qint.card *
        (alpha ^ Qpre.card * eta ^ Required.card) := by
      gcongr
      exact hpre Qpre Required
    _ = alpha ^ Qpre.card * (eta * delta) ^ Qint.card *
        eta ^ Efix.card := by
      rw [hcard, pow_add, mul_pow]
      ring

/-- The binomial expansion indexed by the subsets of a fixed finite set. -/
lemma sum_powerset_pow_card_mul_pow_sdiff_card
    {A : Type*} [DecidableEq A] (Q : Finset A) (a b : ℝ≥0) :
    (∑ S ∈ Q.powerset, a ^ S.card * b ^ (Q \ S).card) =
      (a + b) ^ Q.card := by
  calc
    (∑ S ∈ Q.powerset, a ^ S.card * b ^ (Q \ S).card) =
        ∑ S ∈ Q.powerset,
          (∏ _x ∈ S, a) * ∏ _x ∈ Q \ S, b := by simp
    _ = ∏ _x ∈ Q, (a + b) :=
      (Finset.prod_add (fun _x : A ↦ a) (fun _x : A ↦ b) Q).symm
    _ = (a + b) ^ Q.card := by simp

/-- A fixed family contained in the union of the preliminary and internal
families admits a powerset partition according to which triangles were
already selected by the preliminary phase. -/
lemma subset_preliminaryInternalCombinedAdded_partition
    {Xi Zeta V : Type*} [DecidableEq V]
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (Q : TripleSystemOn V) (z : Xi × Zeta)
    (hQ : Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z) :
    ∃ S ∈ Q.powerset,
      S ⊆ addedPre z.1 ∧ Q \ S ⊆ addedInt z.1 z.2 := by
  classical
  let S := Q ∩ addedPre z.1
  refine ⟨S, mem_powerset.mpr inter_subset_left, inter_subset_right, ?_⟩
  intro T hT
  obtain ⟨hTQ, hTnotS⟩ := mem_sdiff.mp hT
  have hTunion := hQ hTQ
  rw [preliminaryInternalCombinedAdded, mem_union] at hTunion
  exact hTunion.resolve_left fun hTpre ↦
    hTnotS (mem_inter.mpr ⟨hTQ, hTpre⟩)

/-- Joint inclusion estimate for the union of the preliminary and internal
families.  The factor for an internal triangle is `eta * delta`: its unique
scheduled outside edge must survive the preliminary phase, and then the
conditional internal sampler must select the triangle. -/
theorem FiniteLaw.jointBind_probability_preliminaryInternalCombinedAdded_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V]
    (Kpre : FiniteLaw Xi) (Kint : Xi → FiniteLaw Zeta)
    (G : SimpleGraph V) (U : Finset V)
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (alpha eta delta : ℝ≥0)
    (hpre : ∀ Q E,
      Kpre.probability (fun xi ↦
        Q ⊆ addedPre xi ∧
          E ⊆ preliminaryResidualOuterEdges G U (addedPre xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hC4 : ∀ xi Q,
      (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤
        delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Q : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z)) ≤
      (alpha + eta * delta) ^ Q.card * eta ^ Efix.card := by
  classical
  let Event : TripleSystemOn V → (Xi × Zeta) → Prop := fun S z ↦
    S ⊆ addedPre z.1 ∧ Q \ S ⊆ addedInt z.1 z.2 ∧
      Efix ⊆ preliminaryResidualCrossingEdges G U
        (preliminaryInternalCombinedAdded addedPre addedInt z)
  have hmono :
      (Kpre.jointBind Kint).probability (fun z ↦
        Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z)) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          ∃ S ∈ Q.powerset, Event S z) := by
    apply (Kpre.jointBind Kint).probability_mono
    intro z hz
    obtain ⟨S, hSQ, hSpre, hSInt⟩ :=
      subset_preliminaryInternalCombinedAdded_partition
        addedPre addedInt Q z hz.1
    exact ⟨S, hSQ, hSpre, hSInt, hz.2⟩
  calc
    (Kpre.jointBind Kint).probability (fun z ↦
        Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z)) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          ∃ S ∈ Q.powerset, Event S z) := hmono
    _ ≤ ∑ S ∈ Q.powerset,
        (Kpre.jointBind Kint).probability (Event S) :=
      (Kpre.jointBind Kint).probability_exists_le Q.powerset Event
    _ ≤ ∑ S ∈ Q.powerset,
        alpha ^ S.card * (eta * delta) ^ (Q \ S).card *
          eta ^ Efix.card := by
      apply sum_le_sum
      intro S hS
      exact Kpre.jointBind_probability_preliminary_internal_parts_le
        Kint G U addedPre addedInt alpha eta delta hpre hC4 hstruct
          S (Q \ S) Efix
    _ = (alpha + eta * delta) ^ Q.card * eta ^ Efix.card := by
      rw [← Finset.sum_mul]
      congr 1
      exact sum_powerset_pow_card_mul_pow_sdiff_card Q alpha (eta * delta)

/-- Fixed-part product estimate when a sampled crossing reserve was exposed
before the preliminary phase.  Only final residual crossing edges outside
that old reserve are new reserve requirements. -/
theorem FiniteLaw.jointBind_probability_protectedPreliminary_internal_parts_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V]
    (Kpre : FiniteLaw Xi) (Kint : Xi → FiniteLaw Zeta)
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hreserve : reserve ⊆ crossingEdges G U)
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (alpha eta delta : ℝ≥0)
    (hpre : ∀ Q E,
      Kpre.probability (fun xi ↦
        Q ⊆ addedPre xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph G U reserve) U (addedPre xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hC4 : ∀ xi Q,
      (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤
        delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Qpre Qint : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
      alpha ^ Qpre.card * (eta * delta) ^ Qint.card *
        eta ^ Efix.card := by
  classical
  let Required : Finset (Sym2 V) :=
    internalRequiredOuterEdges U Qint ∪ Efix
  let PreEvent : Xi → Prop := fun xi ↦
    Qpre ⊆ addedPre xi ∧
      Required ⊆ preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U reserve) U (addedPre xi)
  let IntEvent : Xi → Zeta → Prop := fun xi z ↦
    Qint ⊆ addedInt xi z ∧
      Efix ⊆ preliminaryResidualCrossingEdges G U
        (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) \ reserve
  have houter : ∀ xi e,
      e ∈ preliminaryResidualInternalEdges G U (addedPre xi) →
      e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro xi e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        G U (addedPre xi) he)).2
  have hsupportImp : ∀ z,
      (IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z)) →
      (Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) →
      PreEvent z.1 := by
    intro z hs hz
    refine ⟨hz.1, ?_⟩
    have hQdiff : Qint ⊆
        preliminaryInternalCombinedAdded addedPre addedInt z \ addedPre z.1 := by
      intro T hT
      exact mem_sdiff.mpr ⟨mem_union_right _ (hz.2.1 hT),
        fun hTpre ↦
          Finset.disjoint_left.mp hs.2.1 hTpre (hz.2.1 hT)⟩
    have hrequired : internalRequiredOuterEdges U Qint ⊆
        preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U reserve) U (addedPre z.1) :=
      (internalRequiredOuterEdges_subset_of_usesScheduled
        (houter z.1) hs.2.2 hQdiff).trans
          (preliminaryResidualInternalEdges_subset_protectedResidualOuter
            G U reserve (addedPre z.1) hreserve)
    have hresidual : Efix ⊆
        preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U reserve) U (addedPre z.1) := by
      rw [preliminaryResidualOuterEdges_reserveProtectedOuterGraph]
      intro e he
      have hedata := mem_sdiff.mp (hz.2.2 he)
      exact mem_sdiff.mpr
        ⟨preliminaryResidualCrossingEdges_union_subset_residualOuter
          G U (addedPre z.1) (addedInt z.1 z.2) hedata.1,
          hedata.2⟩
    exact union_subset hrequired hresidual
  have hmono :
      (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          PreEvent z.1 ∧ IntEvent z.1 z.2) := by
    apply (Kpre.jointBind Kint).probability_mono_of_supported hstruct
    intro z hs hz
    exact ⟨hsupportImp z hs hz, ⟨hz.2.1, hz.2.2⟩⟩
  have hconditional : ∀ xi, 0 < Kpre.mass xi → PreEvent xi →
      (Kint xi).probability (IntEvent xi) ≤ delta ^ Qint.card := by
    intro xi hmass _hpre
    have hfiber : (Kint xi).SupportedOn fun z ↦
        IsPackingOn
            (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) ∧
          Disjoint (addedPre xi) (addedInt xi z) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges G U (addedPre xi))
            (addedPre xi)
            (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) := by
      intro z hz
      exact hstruct (xi, z)
        (FiniteLaw.jointBind_mass_pos_iff Kpre Kint xi z |>.2
          ⟨hmass, hz⟩)
    calc
      (Kint xi).probability (IntEvent xi) ≤
          (Kint xi).probability (fun z ↦ Qint ⊆ addedInt xi z) := by
        apply (Kint xi).probability_mono_of_supported hfiber
        intro z _hs hz
        exact hz.1
      _ ≤ delta ^ Qint.card := hC4 xi Qint
  have hjoint :
      (Kpre.jointBind Kint).probability (fun z ↦
        PreEvent z.1 ∧ IntEvent z.1 z.2) ≤
        delta ^ Qint.card * Kpre.probability PreEvent := by
    exact Kpre.jointBind_probability_and_le_on_support Kint PreEvent IntEvent
      (delta ^ Qint.card) hconditional
  by_cases hzero :
      (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) = 0
  · rw [hzero]
    exact zero_le
  have hpos : 0 < (Kpre.jointBind Kint).probability (fun z ↦
      Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) :=
    pos_iff_ne_zero.mpr hzero
  obtain ⟨zWitness, hmassWitness, hzWitness⟩ :=
    (Kpre.jointBind Kint).exists_mass_pos_and_of_probability_pos hpos
  have hsWitness := hstruct zWitness hmassWitness
  have hQdiffWitness : Qint ⊆
      preliminaryInternalCombinedAdded addedPre addedInt zWitness \
        addedPre zWitness.1 := by
    intro T hT
    exact mem_sdiff.mpr ⟨mem_union_right _ (hzWitness.2.1 hT),
      fun hTpre ↦
        Finset.disjoint_left.mp hsWitness.2.1 hTpre (hzWitness.2.1 hT)⟩
  have hcard : Required.card = Qint.card + Efix.card := by
    exact card_internalRequired_union_residualCrossing_of_usesScheduled
      hsWitness.1 (houter zWitness.1) hsWitness.2.2 hQdiffWitness Efix
        (fun e he ↦ (mem_sdiff.mp (hzWitness.2.2 he)).1)
  calc
    (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          PreEvent z.1 ∧ IntEvent z.1 z.2) := hmono
    _ ≤ delta ^ Qint.card * Kpre.probability PreEvent := hjoint
    _ ≤ delta ^ Qint.card *
        (alpha ^ Qpre.card * eta ^ Required.card) := by
      gcongr
      exact hpre Qpre Required
    _ = alpha ^ Qpre.card * (eta * delta) ^ Qint.card *
        eta ^ Efix.card := by
      rw [hcard, pow_add, mul_pow]
      ring

/-- Correlated union estimate in the reserve-protected setting. -/
theorem FiniteLaw.jointBind_probability_protectedPreliminaryInternalCombined_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V]
    (Kpre : FiniteLaw Xi) (Kint : Xi → FiniteLaw Zeta)
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hreserve : reserve ⊆ crossingEdges G U)
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (alpha eta delta : ℝ≥0)
    (hpre : ∀ Q E,
      Kpre.probability (fun xi ↦
        Q ⊆ addedPre xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph G U reserve) U (addedPre xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hC4 : ∀ xi Q,
      (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤
        delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Q : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
      (alpha + eta * delta) ^ Q.card * eta ^ Efix.card := by
  classical
  let Event : TripleSystemOn V → (Xi × Zeta) → Prop := fun S z ↦
    S ⊆ addedPre z.1 ∧ Q \ S ⊆ addedInt z.1 z.2 ∧
      Efix ⊆ preliminaryResidualCrossingEdges G U
        (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve
  have hmono :
      (Kpre.jointBind Kint).probability (fun z ↦
        Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          ∃ S ∈ Q.powerset, Event S z) := by
    apply (Kpre.jointBind Kint).probability_mono
    intro z hz
    obtain ⟨S, hSQ, hSpre, hSInt⟩ :=
      subset_preliminaryInternalCombinedAdded_partition
        addedPre addedInt Q z hz.1
    exact ⟨S, hSQ, hSpre, hSInt, hz.2⟩
  calc
    (Kpre.jointBind Kint).probability (fun z ↦
        Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          ∃ S ∈ Q.powerset, Event S z) := hmono
    _ ≤ ∑ S ∈ Q.powerset,
        (Kpre.jointBind Kint).probability (Event S) :=
      (Kpre.jointBind Kint).probability_exists_le Q.powerset Event
    _ ≤ ∑ S ∈ Q.powerset,
        alpha ^ S.card * (eta * delta) ^ (Q \ S).card *
          eta ^ Efix.card := by
      apply sum_le_sum
      intro S hS
      exact Kpre.jointBind_probability_protectedPreliminary_internal_parts_le
        Kint G U reserve hreserve addedPre addedInt alpha eta delta hpre hC4
          hstruct S (Q \ S) Efix
    _ = (alpha + eta * delta) ^ Q.card * eta ^ Efix.card := by
      rw [← Finset.sum_mul]
      congr 1
      exact sum_powerset_pow_card_mul_pow_sdiff_card Q alpha (eta * delta)

end

end Erdos207
