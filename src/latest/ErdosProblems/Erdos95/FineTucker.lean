/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.Barycentric
import ErdosProblems.Erdos95.External.Tucker

/-!
# Tucker parity on iterated barycentric subdivisions

This file proves the refinement-stable Tucker lemma needed for the finite
Stone--Tukey theorem.  The proof is the mod-two Ky Fan incidence argument:
alternating boundary ridges are counted against alternating top simplices.
-/

open scoped BigOperators

namespace Erdos95.FineTucker

open Barycentric
open ProofsInTheBook.Chapter39

/-- Faces of cardinality `d` satisfying a vertex predicate. -/
abbrev RestrictedTopFace (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :=
  {s : Finset K.Vertex // K.IsFace s ∧ s.card = d ∧ ∀ v ∈ s, U v}

/-- Faces of cardinality `d-1` satisfying a vertex predicate. -/
abbrev RestrictedRidge (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :=
  {s : Finset K.Vertex // K.IsFace s ∧ s.card = d - 1 ∧ ∀ v ∈ s, U v}

noncomputable instance restrictedTopFaceFintype
    (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :
    Fintype (RestrictedTopFace K U d) := by
  classical
  infer_instance

noncomputable instance restrictedRidgeFintype
    (K : FiniteComplex) (U : K.Vertex → Prop) (d : ℕ) :
    Fintype (RestrictedRidge K U d) := by
  classical
  infer_instance

/-- Incidence is inclusion of the ridge in the top face. -/
def FaceIncident {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (R : RestrictedRidge K U d) (T : RestrictedTopFace K U d) : Prop :=
  R.1 ⊆ T.1

noncomputable instance faceIncidentDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} :
    DecidableRel (FaceIncident (K := K) (U := U) (d := d)) := by
  classical
  infer_instance

/-- A chosen enumeration of a finite face of known cardinality. -/
noncomputable def faceEnum {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) : Fin d → α := by
  let e : {x // x ∈ s} ≃ Fin d :=
    Fintype.equivFinOfCardEq (by simpa using hs)
  exact fun i ↦ (e.symm i).1

theorem faceEnum_mem {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) (i : Fin d) :
    faceEnum s d hs i ∈ s := by
  classical
  unfold faceEnum
  simp

theorem faceEnum_injective {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) :
    Function.Injective (faceEnum s d hs) := by
  classical
  let e : {x // x ∈ s} ≃ Fin d :=
    Fintype.equivFinOfCardEq (by simpa using hs)
  change Function.Injective (fun i ↦ (e.symm i).1)
  intro i j hij
  apply e.symm.injective
  apply Subtype.ext
  exact hij

theorem faceEnum_surjective_subtype {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (d : ℕ) (hs : s.card = d) :
    Function.Surjective
      (fun i : Fin d ↦ (⟨faceEnum s d hs i, faceEnum_mem s d hs i⟩ : {x // x ∈ s})) := by
  classical
  unfold faceEnum
  exact (Fintype.equivFinOfCardEq (by simpa using hs)).symm.surjective

/-- The labels on a top face, in an arbitrary enumeration.  Alternation is
permutation invariant, so no ordering choice enters the theorem statement. -/
noncomputable def topLabelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    Fin d → SignedLabel m :=
  fun i ↦ label (faceEnum T.1 d T.2.2.1 i)

/-- A ridge has the positive alternating label set. -/
def IsPositiveAlternatingRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (R : RestrictedRidge K U d) : Prop :=
  ∃ idx : Fin (d - 1) → Fin m,
    StrictMono idx ∧ R.1.image label = alternatingLabelSetOf idx

noncomputable instance isPositiveAlternatingRidgeDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) :
    DecidablePred (IsPositiveAlternatingRidge (U := U) (d := d) label) := by
  classical
  intro R
  infer_instance

/-- Positive-or-negative alternating top faces. -/
def IsAlternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) : Prop :=
  (∃ idx : Fin d → Fin m,
      StrictMono idx ∧ T.1.image label = alternatingLabelSetOf idx) ∨
    (∃ idx : Fin d → Fin m,
      StrictMono idx ∧ T.1.image label = alternatingNegLabelSetOf idx)

noncomputable instance isAlternatingTopDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) :
    DecidablePred (IsAlternatingTop (U := U) (d := d) label) := by
  classical
  intro T
  infer_instance

/-! ## Ridges inside one top face -/

noncomputable def eraseRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) (x : {v // v ∈ T.1}) :
    RestrictedRidge K U d := by
  classical
  refine ⟨T.1.erase x.1, ?_, ?_, ?_⟩
  · apply K.face_of_nonempty_subset T.2.1 (Finset.erase_subset _ _)
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem x.2, T.2.2.1]
    omega
  · rw [Finset.card_erase_of_mem x.2, T.2.2.1]
  · intro v hv
    exact T.2.2.2 v (Finset.mem_of_mem_erase hv)

theorem eraseRidge_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) (x : {v // v ∈ T.1}) :
    FaceIncident (eraseRidge hd T x) T :=
  Finset.erase_subset _ _

theorem eraseRidge_injective
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    Function.Injective (eraseRidge hd T) := by
  classical
  intro x y hxy
  apply Subtype.ext
  apply (Finset.erase_inj T.1 x.2).mp
  exact congrArg Subtype.val hxy

theorem eraseRidge_surjective_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    Function.Surjective
      (fun x : {v // v ∈ T.1} ↦
        (⟨eraseRidge hd T x, eraseRidge_incident hd T x⟩ :
          {R : RestrictedRidge K U d // FaceIncident R T})) := by
  classical
  rintro ⟨R, hRT⟩
  have hnot : ¬T.1 ⊆ R.1 := by
    intro hTR
    have hc := Finset.card_le_card hTR
    rw [T.2.2.1, R.2.2.1] at hc
    omega
  have hex : ∃ x ∈ T.1, x ∉ R.1 := by
    by_contra hnone
    apply hnot
    intro x hxT
    by_contra hxR
    exact hnone ⟨x, hxT, hxR⟩
  obtain ⟨x, hxT, hxR⟩ := hex
  let xT : {v // v ∈ T.1} := ⟨x, hxT⟩
  refine ⟨xT, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    change v ∈ R.1 at hv
    change v ∈ T.1.erase x
    rw [Finset.mem_erase]
    exact ⟨fun hvx ↦ hxR (hvx ▸ hv), hRT hv⟩
  · rw [(eraseRidge hd T xT).2.2.1, R.2.2.1]

/-- Deleting one vertex gives all and only the ridges incident to a fixed top
face. -/
noncomputable def eraseRidgeEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    {v // v ∈ T.1} ≃ {R : RestrictedRidge K U d // FaceIncident R T} :=
  Equiv.ofBijective
    (fun x ↦ ⟨eraseRidge hd T x, eraseRidge_incident hd T x⟩)
    ⟨fun _ _ h ↦ eraseRidge_injective hd T (congrArg Subtype.val h),
      eraseRidge_surjective_incident hd T⟩

/-- The chosen enumeration as an equivalence onto the vertices of a top
face. -/
noncomputable def faceEnumEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (T : RestrictedTopFace K U d) : Fin d ≃ {v // v ∈ T.1} := by
  classical
  exact Equiv.ofBijective
    (fun i ↦ ⟨faceEnum T.1 d T.2.2.1 i,
      faceEnum_mem T.1 d T.2.2.1 i⟩)
    ⟨fun _ _ h ↦ faceEnum_injective T.1 d T.2.2.1 (congrArg Subtype.val h),
      faceEnum_surjective_subtype T.1 d T.2.2.1⟩

/-- Incident ridges are canonically indexed by the deleted position in the
chosen top-face enumeration. -/
noncomputable def deletionRidgeEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) :
    Fin d ≃ {R : RestrictedRidge K U d // FaceIncident R T} :=
  (faceEnumEquiv T).trans (eraseRidgeEquiv hd T)

theorem deletionRidgeEquiv_val
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ} (hd : 2 ≤ d)
    (T : RestrictedTopFace K U d) (i : Fin d) :
    (deletionRidgeEquiv hd T i).1.1 =
      T.1.erase (faceEnum T.1 d T.2.2.1 i) := by
  rfl

theorem image_label_deletion_eq_labelSeqSet
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) (i : Fin (k + 1)) :
    ((deletionRidgeEquiv (by omega : 2 ≤ k + 1) T i).1.1.image label) =
      labelSeqSet (fun a : Fin k ↦ topLabelSeq label T (i.succAbove a)) := by
  classical
  rw [deletionRidgeEquiv_val]
  ext z
  simp only [Finset.mem_image, labelSeqSet]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' := Finset.mem_erase.mp hv
    obtain ⟨j, hj⟩ := faceEnum_surjective_subtype
      T.1 (k + 1) T.2.2.1 ⟨v, hv'.2⟩
    have hjval : faceEnum T.1 (k + 1) T.2.2.1 j = v :=
      congrArg Subtype.val hj
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hv'.1 hjval.symm
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hji
    refine ⟨a, Finset.mem_univ _, ?_⟩
    change label (faceEnum T.1 (k + 1) T.2.2.1 (i.succAbove a)) = label v
    rw [ha, hjval]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨faceEnum T.1 (k + 1) T.2.2.1 (i.succAbove a), ?_, rfl⟩
    rw [Finset.mem_erase]
    refine ⟨?_, faceEnum_mem _ _ _ _⟩
    intro heq
    exact Fin.succAbove_ne i a
      (faceEnum_injective T.1 (k + 1) T.2.2.1 heq)

theorem positiveAlternating_deletionRidge_iff
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) (i : Fin (k + 1)) :
    IsPositiveAlternatingRidge label
        (deletionRidgeEquiv (by omega : 2 ≤ k + 1) T i).1 ↔
      i ∈ labelSeqAltPosDeletionSet (topLabelSeq label T) := by
  classical
  rw [show i ∈ labelSeqAltPosDeletionSet (topLabelSeq label T) ↔
      IsAltPosLabelSeq
        (fun a : Fin k ↦ topLabelSeq label T (i.succAbove a)) by
    simp [labelSeqAltPosDeletionSet]]
  unfold IsPositiveAlternatingRidge IsAltPosLabelSeq
  rw [image_label_deletion_eq_labelSeqSet hk label T i]
  rfl

theorem image_label_top_eq_labelSeqSet
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    T.1.image label = labelSeqSet (topLabelSeq label T) := by
  classical
  ext z
  simp only [Finset.mem_image, labelSeqSet]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi⟩ := faceEnum_surjective_subtype
      T.1 d T.2.2.1 ⟨v, hv⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change label (faceEnum T.1 d T.2.2.1 i) = label v
    exact congrArg label (congrArg Subtype.val hi)
  · rintro ⟨i, hi, rfl⟩
    exact ⟨faceEnum T.1 d T.2.2.1 i,
      faceEnum_mem T.1 d T.2.2.1 i, rfl⟩

theorem alternatingTop_iff_labelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsAlternatingTop label T ↔
      IsAltPosLabelSeq (topLabelSeq label T) ∨
        IsAltNegLabelSeq (topLabelSeq label T) := by
  unfold IsAlternatingTop IsAltPosLabelSeq IsAltNegLabelSeq
  rw [← image_label_top_eq_labelSeqSet label T]

/-- No face contains a complementary pair of labels. -/
def NoComplementaryFaceLabels
    (K : FiniteComplex) {m : ℕ} (label : K.Vertex → SignedLabel m) : Prop :=
  ∀ ⦃s : Finset K.Vertex⦄, K.IsFace s →
    ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → label v ≠ (label w).neg

/-- Positive alternating ridges as a finite type. -/
abbrev PositiveAlternatingRidge
    (K : FiniteComplex) (U : K.Vertex → Prop) (d m : ℕ)
    (label : K.Vertex → SignedLabel m) :=
  {R : RestrictedRidge K U d // IsPositiveAlternatingRidge label R}

noncomputable def altIncidentReassociate
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    {R : {R : RestrictedRidge K U d // FaceIncident R T} //
      IsPositiveAlternatingRidge label R.1} ≃
      {R : PositiveAlternatingRidge K U d m label // FaceIncident R.1 T} where
  toFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  invFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  left_inv R := by cases R; rfl
  right_inv R := by cases R; rfl

/-- Alternating incident ridges are exactly the deletion positions in the
local Ky Fan door set. -/
noncomputable def altIncidentEquivDeletion
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) :
    {i : Fin (k + 1) // i ∈ labelSeqAltPosDeletionSet (topLabelSeq label T)} ≃
      {R : PositiveAlternatingRidge K U (k + 1) m label // FaceIncident R.1 T} :=
  ((deletionRidgeEquiv (by omega : 2 ≤ k + 1) T).subtypeEquiv
    (fun i ↦ (positiveAlternating_deletionRidge_iff hk label T i).symm)).trans
      (altIncidentReassociate label T)

theorem card_altIncident_eq_deletionSet_card
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) (label : K.Vertex → SignedLabel m)
    (T : RestrictedTopFace K U (k + 1)) :
    Fintype.card
        {R : PositiveAlternatingRidge K U (k + 1) m label // FaceIncident R.1 T} =
      (labelSeqAltPosDeletionSet (topLabelSeq label T)).card := by
  classical
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (altIncidentEquivDeletion hk label T).symm

theorem topLabelSeq_noOpposite
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    {label : K.Vertex → SignedLabel m} (hno : NoComplementaryFaceLabels K label)
    (T : RestrictedTopFace K U d) :
    NoOppositeLabelSeq (topLabelSeq label T) := by
  intro i j
  apply hno T.2.1
  · exact faceEnum_mem T.1 d T.2.2.1 i
  · exact faceEnum_mem T.1 d T.2.2.1 j

/-- The local sigma-degree parity: a top simplex has an odd number of
alternating ridge doors exactly when its complete label set is alternating. -/
theorem odd_altIncident_iff_alternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {k m : ℕ}
    (hk : 1 ≤ k) {label : K.Vertex → SignedLabel m}
    (hno : NoComplementaryFaceLabels K label)
    (T : RestrictedTopFace K U (k + 1)) :
    Odd (Fintype.card
        {R : PositiveAlternatingRidge K U (k + 1) m label // FaceIncident R.1 T}) ↔
      IsAlternatingTop label T := by
  rw [card_altIncident_eq_deletionSet_card hk label T,
    labelSeq_deletionParity_of_noOpposite (topLabelSeq_noOpposite hno T),
    ← alternatingTop_iff_labelSeq label T]

/-! ## Abstract hemisphere handshaking -/

/-- The sole geometric input to Ky Fan handshaking: every upper-hemisphere
ridge has one top coface on the equator boundary and two otherwise. -/
structure HemisphereGeometry
    (K : FiniteComplex) (U E : K.Vertex → Prop) (d : ℕ)
    [equatorDecidable : DecidablePred E] where
  ridge_degree : ∀ R : RestrictedRidge K U d,
    Fintype.card {T : RestrictedTopFace K U d // FaceIncident R T} =
      if (∀ v ∈ R.1, E v) then 1 else 2

def IsEquatorRidge
    {K : FiniteComplex} {U E : K.Vertex → Prop} {d : ℕ}
    (R : RestrictedRidge K U d) : Prop :=
  ∀ v ∈ R.1, E v

noncomputable instance isEquatorRidgeDecidable
    {K : FiniteComplex} {U E : K.Vertex → Prop} {d : ℕ}
    [DecidablePred E] :
    DecidablePred (IsEquatorRidge (K := K) (U := U) (E := E) (d := d)) := by
  classical
  intro R
  infer_instance

noncomputable def alternatingRhoData
    {K : FiniteComplex} {U E : K.Vertex → Prop} {k m : ℕ}
    [DecidablePred E]
    (label : K.Vertex → SignedLabel m)
    (H : HemisphereGeometry K U E (k + 1))
    (hne : Nonempty (PositiveAlternatingRidge K U (k + 1) m label)) :
    RhoDegreeManifoldData
      (PositiveAlternatingRidge K U (k + 1) m label)
      (RestrictedTopFace K U (k + 1)) where
  edge R T := FaceIncident R.1 T
  edge_decidable := inferInstance
  boundary R := IsEquatorRidge (E := E) R.1
  boundary_decidable := inferInstance
  nonempty_R := hne
  degree_card R := by
    have hdeg := H.ridge_degree R.1
    change Fintype.card {T : RestrictedTopFace K U (k + 1) //
      FaceIncident R.1 T} = if IsEquatorRidge (E := E) R.1 then 1 else 2
    by_cases h : ∀ v ∈ R.1.1, E v
    · rw [if_pos h] at hdeg
      rw [if_pos (show IsEquatorRidge (E := E) R.1 from h)]
      exact hdeg
    · rw [if_neg h] at hdeg
      rw [if_neg (show ¬IsEquatorRidge (E := E) R.1 from h)]
      exact hdeg

/-- The global Ky Fan handshaking step for an arbitrary triangulated
hemisphere satisfying the `1/2` ridge-degree law. -/
theorem odd_alternatingTop_of_odd_equatorRidge
    {K : FiniteComplex} {U E : K.Vertex → Prop} {k m : ℕ}
    [DecidablePred E]
    (hk : 1 ≤ k) {label : K.Vertex → SignedLabel m}
    (hno : NoComplementaryFaceLabels K label)
    (H : HemisphereGeometry K U E (k + 1))
    (hboundary : Odd (Fintype.card
      {R : PositiveAlternatingRidge K U (k + 1) m label //
        IsEquatorRidge (E := E) R.1})) :
    Odd (Fintype.card
      {T : RestrictedTopFace K U (k + 1) // IsAlternatingTop label T}) := by
  have hpos : 0 < Fintype.card
      {R : PositiveAlternatingRidge K U (k + 1) m label //
        IsEquatorRidge (E := E) R.1} := by
    rcases hboundary with ⟨a, ha⟩
    omega
  have hne : Nonempty (PositiveAlternatingRidge K U (k + 1) m label) := by
    obtain ⟨R⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨R.1⟩
  exact kyFan_parity_step_from_rho_sigma_data
    (alternatingRhoData label H hne)
    (IsAlternatingTop label)
    (fun T ↦ odd_altIncident_iff_alternatingTop hk hno T)
    hboundary

/-! ## The refined cross-polytope hemispheres -/

/-- Vertex predicate for the closed upper hemisphere in every subdivision of
the boundary of the `(d+1)`-cross-polytope. -/
def UpperVertex (d : ℕ) :
    ∀ r, (iteratedBoundary (d + 1) r).Vertex → Prop
  | 0, v => v ≠ (Fin.last d, false)
  | r + 1, F => ∀ v ∈ F.1, UpperVertex d r v

/-- Vertex predicate for the equator in every subdivision. -/
def EquatorVertex (d : ℕ) :
    ∀ r, (iteratedBoundary (d + 1) r).Vertex → Prop
  | 0, v => v.1 ≠ Fin.last d
  | r + 1, F => ∀ v ∈ F.1, EquatorVertex d r v

noncomputable instance upperVertexDecidable (d r : ℕ) :
    DecidablePred (UpperVertex d r) := by
  classical
  intro v
  infer_instance

noncomputable instance equatorVertexDecidable (d r : ℕ) :
    DecidablePred (EquatorVertex d r) := by
  classical
  intro v
  infer_instance

theorem equatorVertex_upperVertex (d r : ℕ)
    {v : (iteratedBoundary (d + 1) r).Vertex}
    (hv : EquatorVertex d r v) : UpperVertex d r v := by
  induction r with
  | zero =>
      intro heq
      exact hv (congrArg Prod.fst heq)
  | succ r ih =>
      intro w hw
      exact ih (hv w hw)

theorem upperVertex_face_downward (d r : ℕ)
    {s t : Finset (iteratedBoundary (d + 1) r).Vertex}
    (hst : t ⊆ s) (hs : ∀ v ∈ s, UpperVertex d r v) :
    ∀ v ∈ t, UpperVertex d r v :=
  fun v hv ↦ hs v (hst hv)

theorem equatorVertex_face_downward (d r : ℕ)
    {s t : Finset (iteratedBoundary (d + 1) r).Vertex}
    (hst : t ⊆ s) (hs : ∀ v ∈ s, EquatorVertex d r v) :
    ∀ v ∈ t, EquatorVertex d r v :=
  fun v hv ↦ hs v (hst hv)

/-! ### The unsubdivided hemisphere -/

def BaseUpperVertex (d : ℕ)
    (v : (crossPolytopeBoundary (d + 1)).Vertex) : Prop :=
  v ≠ (Fin.last d, false)

def BaseEquatorVertex (d : ℕ)
    (v : (crossPolytopeBoundary (d + 1)).Vertex) : Prop :=
  v.1 ≠ Fin.last d

noncomputable instance baseUpperVertexDecidable (d : ℕ) :
    DecidablePred (BaseUpperVertex d) := by
  classical
  intro v
  infer_instance

noncomputable instance baseEquatorVertexDecidable (d : ℕ) :
    DecidablePred (BaseEquatorVertex d) := by
  classical
  intro v
  infer_instance

def ridgeCoordinateImage (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Finset (Fin (d + 1)) :=
  R.1.image (fun v : (crossPolytopeBoundary (d + 1)).Vertex ↦ v.1)

theorem card_ridgeCoordinateImage (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    (ridgeCoordinateImage d R).card = d := by
  have hinj : Set.InjOn
      (fun v : (crossPolytopeBoundary (d + 1)).Vertex ↦ v.1) (↑R.1) := by
    rintro ⟨i, b⟩ hib ⟨j, c⟩ hjc hij
    simp only at hij
    subst j
    have hbc : b = c := by
      by_contra hbc
      have hbool : (b = false ∧ c = true) ∨ (c = false ∧ b = true) := by
        cases b <;> cases c <;> simp_all
      rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact R.2.1.2 i ⟨hib, hjc⟩
      · exact R.2.1.2 i ⟨hjc, hib⟩
    exact Prod.ext rfl hbc
  rw [ridgeCoordinateImage, Finset.card_image_iff.mpr hinj]
  simpa using R.2.2.1

theorem exists_missingCoordinate (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    ∃ i : Fin (d + 1), i ∉ ridgeCoordinateImage d R := by
  by_contra h
  have hall : ridgeCoordinateImage d R = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  have hc := card_ridgeCoordinateImage d R
  rw [hall] at hc
  simp at hc

noncomputable def missingCoordinate (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Fin (d + 1) :=
  Classical.choose (exists_missingCoordinate d R)

theorem missingCoordinate_not_mem (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    missingCoordinate d R ∉ ridgeCoordinateImage d R :=
  Classical.choose_spec (exists_missingCoordinate d R)

theorem ridgeCoordinateImage_eq_erase_missing (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    ridgeCoordinateImage d R =
      (Finset.univ : Finset (Fin (d + 1))).erase (missingCoordinate d R) := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun him ↦ missingCoordinate_not_mem d R (him ▸ hi), Finset.mem_univ i⟩
  · rw [card_ridgeCoordinateImage]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp

theorem coordinate_mem_ridge_of_ne_missing (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    {i : Fin (d + 1)} (hi : i ≠ missingCoordinate d R) :
    i ∈ ridgeCoordinateImage d R := by
  rw [ridgeCoordinateImage_eq_erase_missing]
  simp [hi]

theorem equatorRidge_iff_missingCoordinate_last (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    IsEquatorRidge (E := BaseEquatorVertex d) R ↔
      missingCoordinate d R = Fin.last d := by
  constructor
  · intro hEq
    by_contra hne
    obtain ⟨v, hvR, hvcoord⟩ := Finset.mem_image.mp
      (coordinate_mem_ridge_of_ne_missing d R (Ne.symm hne))
    have := hEq v hvR
    exact this hvcoord
  · intro hlast v hvR
    intro hvlast
    apply missingCoordinate_not_mem d R
    rw [hlast, ridgeCoordinateImage]
    exact Finset.mem_image.mpr ⟨v, hvR, hvlast⟩

def AllowedMissingSign (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : Bool) : Prop :=
  missingCoordinate d R ≠ Fin.last d ∨ b = true

noncomputable instance allowedMissingSignDecidable (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    DecidablePred (AllowedMissingSign d R) := by
  classical
  intro b
  infer_instance

theorem missingAtom_not_mem (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : Bool) :
    (missingCoordinate d R, b) ∉ R.1 := by
  intro h
  exact missingCoordinate_not_mem d R
    (Finset.mem_image.mpr ⟨(missingCoordinate d R, b), h, rfl⟩)

noncomputable def addMissingTop (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : {b : Bool // AllowedMissingSign d R b}) :
    RestrictedTopFace (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1) := by
  classical
  let a : (crossPolytopeBoundary (d + 1)).Vertex := (missingCoordinate d R, b.1)
  refine ⟨insert a R.1, ?_, ?_, ?_⟩
  · refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro i hi
    by_cases hiMissing : i = missingCoordinate d R
    · subst i
      have hfalse : (missingCoordinate d R, false) = a ∨
          (missingCoordinate d R, false) ∈ R.1 := Finset.mem_insert.mp hi.1
      have htrue : (missingCoordinate d R, true) = a ∨
          (missingCoordinate d R, true) ∈ R.1 := Finset.mem_insert.mp hi.2
      rcases hfalse with hfalse | hfalse <;>
        rcases htrue with htrue | htrue
      · dsimp [a] at hfalse htrue
        cases b.1 <;> simp_all
      · exact missingAtom_not_mem d R true htrue
      · exact missingAtom_not_mem d R false hfalse
      · exact R.2.1.2 (missingCoordinate d R) ⟨hfalse, htrue⟩
    · have hfalseR : (i, false) ∈ R.1 := by
        have := Finset.mem_insert.mp hi.1
        rcases this with h | h
        · have := congrArg Prod.fst h
          exact False.elim (hiMissing this)
        · exact h
      have htrueR : (i, true) ∈ R.1 := by
        have := Finset.mem_insert.mp hi.2
        rcases this with h | h
        · have := congrArg Prod.fst h
          exact False.elim (hiMissing this)
        · exact h
      exact R.2.1.2 i ⟨hfalseR, htrueR⟩
  · dsimp [a]
    let atom : (crossPolytopeBoundary (d + 1)).Vertex :=
      (missingCoordinate d R, b.1)
    have hatom : atom ∉ R.1 := by
      exact missingAtom_not_mem d R b.1
    change (insert atom R.1).card = d + 1
    rw [Finset.card_insert_of_notMem hatom, R.2.2.1]
    omega
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvR
    · intro heq
      have hcoord := congrArg Prod.fst heq
      have hsign := congrArg Prod.snd heq
      dsimp [a] at hcoord hsign
      rcases b.2 with hm | hb
      · exact hm hcoord
      · cases b.1 <;> simp_all
    · exact R.2.2.2 v hvR

theorem addMissingTop_incident (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1))
    (b : {b : Bool // AllowedMissingSign d R b}) :
    FaceIncident R (addMissingTop d R b) := by
  intro v hv
  exact Finset.mem_insert_of_mem hv

theorem addMissingTop_injective (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Function.Injective (addMissingTop d R) := by
  classical
  intro b c hbc
  apply Subtype.ext
  by_contra hne
  have hsets : (addMissingTop d R b).1 = (addMissingTop d R c).1 :=
    congrArg (fun T => T.1) hbc
  have hmem : (missingCoordinate d R, b.1) ∈
      (addMissingTop d R c).1 := by
    rw [← hsets]
    let atom : (crossPolytopeBoundary (d + 1)).Vertex :=
      (missingCoordinate d R, b.1)
    change atom ∈ insert atom R.1
    exact Finset.mem_insert.mpr (Or.inl rfl)
  rcases Finset.mem_insert.mp hmem with heq | hR
  · exact hne (congrArg Prod.snd heq)
  · exact missingAtom_not_mem d R b.1 hR

theorem addMissingTop_surjective_incident (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Function.Surjective
      (fun b : {b : Bool // AllowedMissingSign d R b} ↦
        (⟨addMissingTop d R b, addMissingTop_incident d R b⟩ :
          {T : RestrictedTopFace (crossPolytopeBoundary (d + 1))
            (BaseUpperVertex d) (d + 1) // FaceIncident R T})) := by
  classical
  rintro ⟨T, hRT⟩
  have hnot : ¬T.1 ⊆ R.1 := by
    intro hTR
    have hc := Finset.card_le_card hTR
    rw [T.2.2.1, R.2.2.1] at hc
    omega
  have hex : ∃ x ∈ T.1, x ∉ R.1 := by
    by_contra hnone
    apply hnot
    intro x hxT
    by_contra hxR
    exact hnone ⟨x, hxT, hxR⟩
  obtain ⟨x, hxT, hxR⟩ := hex
  have hxcoord : x.1 = missingCoordinate d R := by
    by_contra hne
    obtain ⟨v, hvR, hvcoord⟩ := Finset.mem_image.mp
      (coordinate_mem_ridge_of_ne_missing d R hne)
    have hvT := hRT hvR
    have hsame : v.2 = x.2 := by
      cases hvb : v.2 <;> cases hxb : x.2
      · rfl
      · exfalso
        have hvEq : v = (x.1, false) := Prod.ext hvcoord hvb
        have hxEq : x = (x.1, true) := Prod.ext rfl hxb
        exact T.2.1.2 x.1 ⟨hvEq ▸ hvT, hxEq ▸ hxT⟩
      · exfalso
        have hxEq : x = (x.1, false) := Prod.ext rfl hxb
        have hvEq : v = (x.1, true) := Prod.ext hvcoord hvb
        exact T.2.1.2 x.1 ⟨hxEq ▸ hxT, hvEq ▸ hvT⟩
      · rfl
    have hxv : x = v := Prod.ext hvcoord.symm hsame.symm
    exact hxR (hxv ▸ hvR)
  have hxAllowed : AllowedMissingSign d R x.2 := by
    by_cases hm : missingCoordinate d R = Fin.last d
    · right
      have hxUpper := T.2.2.2 x hxT
      cases hxsign : x.2
      · exfalso
        apply hxUpper
        apply Prod.ext
        · exact hxcoord.trans hm
        · exact hxsign
      · rfl
    · exact Or.inl hm
  let b : {b : Bool // AllowedMissingSign d R b} := ⟨x.2, hxAllowed⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hx : x = (missingCoordinate d R, b.1) :=
    Prod.ext hxcoord rfl
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvR
    · simpa [← hx] using hxT
    · exact hRT hvR
  · rw [(addMissingTop d R b).2.2.1, T.2.2.1]

noncomputable def missingTopEquiv (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    {b : Bool // AllowedMissingSign d R b} ≃
      {T : RestrictedTopFace (crossPolytopeBoundary (d + 1))
        (BaseUpperVertex d) (d + 1) // FaceIncident R T} :=
  Equiv.ofBijective
    (fun b ↦ ⟨addMissingTop d R b, addMissingTop_incident d R b⟩)
    ⟨fun _ _ h ↦ addMissingTop_injective d R (congrArg Subtype.val h),
      addMissingTop_surjective_incident d R⟩

theorem card_allowedMissingSign (d : ℕ)
    (R : RestrictedRidge (crossPolytopeBoundary (d + 1)) (BaseUpperVertex d) (d + 1)) :
    Fintype.card {b : Bool // AllowedMissingSign d R b} =
      if IsEquatorRidge (E := BaseEquatorVertex d) R then 1 else 2 := by
  classical
  by_cases hEq : IsEquatorRidge (E := BaseEquatorVertex d) R
  · rw [if_pos hEq]
    have h := (equatorRidge_iff_missingCoordinate_last d R).mp hEq
    simp [AllowedMissingSign, h]
  · rw [if_neg hEq]
    have h : missingCoordinate d R ≠ Fin.last d := by
      intro hm
      exact hEq ((equatorRidge_iff_missingCoordinate_last d R).mpr hm)
    simp [AllowedMissingSign, h]

noncomputable def baseHemisphereGeometry (d : ℕ) :
    HemisphereGeometry (crossPolytopeBoundary (d + 1))
      (BaseUpperVertex d) (BaseEquatorVertex d) (d + 1) where
  ridge_degree R := by
    have hequiv : Fintype.card
        {T : RestrictedTopFace (crossPolytopeBoundary (d + 1))
          (BaseUpperVertex d) (d + 1) // FaceIncident R T} =
        Fintype.card {b : Bool // AllowedMissingSign d R b} :=
      Fintype.card_congr (missingTopEquiv d R).symm
    rw [hequiv]
    have hc := card_allowedMissingSign d R
    by_cases h : ∀ v ∈ R.1, BaseEquatorVertex d v
    · rw [if_pos h]
      rw [if_pos (show IsEquatorRidge (E := BaseEquatorVertex d) R from h)] at hc
      exact hc
    · rw [if_neg h]
      rw [if_neg (show ¬IsEquatorRidge (E := BaseEquatorVertex d) R from h)] at hc
      exact hc

/-! ### Barycentric preservation of the ridge-degree law -/

def BaryUpper {K : FiniteComplex} (U : K.Vertex → Prop)
    (F : (barycentricSubdivision K).Vertex) : Prop :=
  ∀ v ∈ F.1, U v

noncomputable instance baryUpperDecidable
    {K : FiniteComplex} (U : K.Vertex → Prop) [DecidablePred U] :
    DecidablePred (BaryUpper U) := by
  classical
  intro F
  infer_instance

noncomputable def baryRank {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (F : (barycentricSubdivision K).Vertex) : Fin d :=
  ⟨F.1.card - 1, by
    have hp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
    have hl := hcard F.2
    omega⟩

theorem baryRank_injective_on_chain
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    {S : Finset (barycentricSubdivision K).Vertex}
    (hS : IsFaceChain K S) :
    Set.InjOn (baryRank d hcard) (↑S) := by
  intro F hF G hG hrank
  apply Subtype.ext
  have hcardEq : F.1.card = G.1.card := by
    have hFp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
    have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
    have hv := congrArg Fin.val hrank
    dsimp [baryRank] at hv
    omega
  rcases hS.2 F hF G hG with hFG | hGF
  · exact Finset.eq_of_subset_of_card_le hFG hcardEq.ge
  · exact (Finset.eq_of_subset_of_card_le hGF hcardEq.le).symm

noncomputable def baryRidgeRankImage
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    Finset (Fin d) :=
  R.1.image (baryRank d hcard)

theorem card_baryRidgeRankImage
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    (baryRidgeRankImage d hcard R).card = d - 1 := by
  rw [baryRidgeRankImage, Finset.card_image_iff.mpr
    (baryRank_injective_on_chain d hcard R.2.1)]
  exact R.2.2.1

theorem exists_missingBaryRank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    ∃ i : Fin d, i ∉ baryRidgeRankImage d hcard R := by
  by_contra h
  have hall : baryRidgeRankImage d hcard R = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  have hc := card_baryRidgeRankImage d hcard R
  rw [hall] at hc
  simp at hc
  omega

noncomputable def missingBaryRank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) : Fin d :=
  Classical.choose (exists_missingBaryRank d hd hcard R)

theorem missingBaryRank_not_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    missingBaryRank d hd hcard R ∉ baryRidgeRankImage d hcard R :=
  Classical.choose_spec (exists_missingBaryRank d hd hcard R)

theorem baryRidgeRankImage_eq_erase_missing
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    baryRidgeRankImage d hcard R =
      (Finset.univ : Finset (Fin d)).erase (missingBaryRank d hd hcard R) := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun him ↦ missingBaryRank_not_mem d hd hcard R (him ▸ hi),
      Finset.mem_univ i⟩
  · rw [card_baryRidgeRankImage]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp

theorem baryRank_eq_missing_of_not_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : (barycentricSubdivision K).Vertex)
    (hF : baryRank d hcard F ∉ baryRidgeRankImage d hcard R) :
    baryRank d hcard F = missingBaryRank d hd hcard R := by
  by_contra hne
  apply hF
  rw [baryRidgeRankImage_eq_erase_missing d hd hcard R]
  simp [hne]

/-- Old faces which can fill the unique missing rank of a barycentric ridge. -/
def IsBaryInsertionFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : (barycentricSubdivision K).Vertex) : Prop :=
  baryRank d hcard F = missingBaryRank d hd hcard R ∧
    (∀ G ∈ R.1, F.1 ⊆ G.1 ∨ G.1 ⊆ F.1) ∧ BaryUpper U F

noncomputable instance isBaryInsertionFaceDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} [DecidablePred U]
    (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    DecidablePred (IsBaryInsertionFace d hd hcard R) := by
  classical
  intro F
  infer_instance

abbrev BaryInsertionFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :=
  {F : (barycentricSubdivision K).Vertex // IsBaryInsertionFace d hd hcard R F}

theorem baryInsertionFace_not_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : BaryInsertionFace d hd hcard R) : F.1 ∉ R.1 := by
  intro hFR
  exact missingBaryRank_not_mem d hd hcard R
    (Finset.mem_image.mpr ⟨F.1, hFR, F.2.1⟩)

noncomputable def addBaryInsertionFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : BaryInsertionFace d hd hcard R) :
    RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) d := by
  classical
  refine ⟨insert F.1 R.1, ?_, ?_, ?_⟩
  · refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with rfl | hAR <;>
      rcases Finset.mem_insert.mp hB with rfl | hBR
    · exact Or.inl Finset.Subset.rfl
    · exact F.2.2.1 B hBR
    · rcases F.2.2.1 A hAR with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact R.2.1.2 A hAR B hBR
  · rw [Finset.card_insert_of_notMem (baryInsertionFace_not_mem d hd hcard R F),
      R.2.2.1]
    omega
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAR
    · exact F.2.2.2
    · exact R.2.2.2 A hAR

theorem addBaryInsertionFace_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (F : BaryInsertionFace d hd hcard R) :
    FaceIncident R (addBaryInsertionFace d hd hcard R F) := by
  intro A hA
  exact Finset.mem_insert_of_mem hA

theorem addBaryInsertionFace_injective
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    Function.Injective (addBaryInsertionFace d hd hcard R) := by
  classical
  intro F G hFG
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  have hsets : (addBaryInsertionFace d hd hcard R F).1 =
      (addBaryInsertionFace d hd hcard R G).1 :=
    congrArg (fun T => T.1) hFG
  have hmem : F.1 ∈ (addBaryInsertionFace d hd hcard R G).1 := by
    rw [← hsets]
    exact Finset.mem_insert.mpr (Or.inl rfl)
  rcases Finset.mem_insert.mp hmem with h | h
  · exact hne (congrArg Subtype.val h)
  · exact baryInsertionFace_not_mem d hd hcard R F h

theorem addBaryInsertionFace_surjective_incident
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    Function.Surjective
      (fun F : BaryInsertionFace d hd hcard R ↦
        (⟨addBaryInsertionFace d hd hcard R F,
          addBaryInsertionFace_incident d hd hcard R F⟩ :
          {T : RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) d //
            FaceIncident R T})) := by
  classical
  rintro ⟨T, hRT⟩
  have hnot : ¬T.1 ⊆ R.1 := by
    intro hTR
    have hc := Finset.card_le_card hTR
    rw [T.2.2.1, R.2.2.1] at hc
    omega
  have hex : ∃ F ∈ T.1, F ∉ R.1 := by
    by_contra hnone
    apply hnot
    intro F hFT
    by_contra hFR
    exact hnone ⟨F, hFT, hFR⟩
  obtain ⟨F, hFT, hFR⟩ := hex
  have hrankNot : baryRank d hcard F ∉ baryRidgeRankImage d hcard R := by
    intro hrank
    rcases Finset.mem_image.mp hrank with ⟨G, hGR, hGF⟩
    have hcardEq : F.1.card = G.1.card := by
      have hFp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
      have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
      have hv := congrArg Fin.val hGF
      dsimp [baryRank] at hv
      omega
    rcases T.2.1.2 F hFT G (hRT hGR) with hFG | hGFsub
    · exact hFR (by
        have : F = G := Subtype.ext (Finset.eq_of_subset_of_card_le hFG hcardEq.ge)
        simpa [this] using hGR)
    · exact hFR (by
        have : G = F := Subtype.ext
          (Finset.eq_of_subset_of_card_le hGFsub hcardEq.le)
        simpa [← this] using hGR)
  have hInsert : IsBaryInsertionFace d hd hcard R F := by
    refine ⟨baryRank_eq_missing_of_not_mem d hd hcard R F hrankNot, ?_, ?_⟩
    · intro G hGR
      exact T.2.1.2 F hFT G (hRT hGR)
    · exact T.2.2.2 F hFT
  let FI : BaryInsertionFace d hd hcard R := ⟨F, hInsert⟩
  refine ⟨FI, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hGR
    · exact hFT
    · exact hRT hGR
  · rw [(addBaryInsertionFace d hd hcard R FI).2.2.1, T.2.2.1]

noncomputable def baryInsertionFaceEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d) :
    BaryInsertionFace d hd hcard R ≃
      {T : RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) d //
        FaceIncident R T} :=
  Equiv.ofBijective
    (fun F ↦ ⟨addBaryInsertionFace d hd hcard R F,
      addBaryInsertionFace_incident d hd hcard R F⟩)
    ⟨fun _ _ h ↦ addBaryInsertionFace_injective d hd hcard R
      (congrArg Subtype.val h),
      addBaryInsertionFace_surjective_incident d hd hcard R⟩

theorem rank_mem_baryRidge_of_ne_missing
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    {i : Fin d} (hi : i ≠ missingBaryRank d hd hcard R) :
    i ∈ baryRidgeRankImage d hcard R := by
  rw [baryRidgeRankImage_eq_erase_missing d hd hcard R]
  simp [hi]

noncomputable def baryRidgeMemberAtRank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    (barycentricSubdivision K).Vertex :=
  Classical.choose (Finset.mem_image.mp
    (rank_mem_baryRidge_of_ne_missing d hd hcard R hi))

theorem baryRidgeMemberAtRank_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    baryRidgeMemberAtRank d hd hcard R i hi ∈ R.1 :=
  (Classical.choose_spec (Finset.mem_image.mp
    (rank_mem_baryRidge_of_ne_missing d hd hcard R hi))).1

theorem baryRidgeMemberAtRank_rank
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    baryRank d hcard (baryRidgeMemberAtRank d hd hcard R i hi) = i :=
  (Classical.choose_spec (Finset.mem_image.mp
    (rank_mem_baryRidge_of_ne_missing d hd hcard R hi))).2

theorem baryRidgeMemberAtRank_card
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) d)
    (i : Fin d) (hi : i ≠ missingBaryRank d hd hcard R) :
    (baryRidgeMemberAtRank d hd hcard R i hi).1.card = i.val + 1 := by
  have hp : 0 < (baryRidgeMemberAtRank d hd hcard R i hi).1.card :=
    Finset.card_pos.mpr (K.face_nonempty
      (baryRidgeMemberAtRank d hd hcard R i hi).2)
  have hr := congrArg Fin.val
    (baryRidgeMemberAtRank_rank d hd hcard R i hi)
  dsimp [baryRank] at hr
  omega

noncomputable def terminalOldRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    RestrictedRidge K U (k + 2) := by
  let p : Fin (k + 2) := ⟨k, by omega⟩
  have hp : p ≠ missingBaryRank (k + 2) (by omega) hcard R := by
    rw [hlast]
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    simp [Fin.last] at hv
  let M := baryRidgeMemberAtRank (k + 2) (by omega) hcard R p hp
  refine ⟨M.1, M.2, ?_, ?_⟩
  · rw [baryRidgeMemberAtRank_card]
    change k + 1 = k + 2 - 1
    omega
  · exact R.2.2.2 M (baryRidgeMemberAtRank_mem _ _ _ _ _ _)

theorem terminalOldRidge_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    (⟨(terminalOldRidge k hcard R hlast).1,
      (terminalOldRidge k hcard R hlast).2.1⟩ : BaryVertex K) ∈ R.1 := by
  let p : Fin (k + 2) := ⟨k, by omega⟩
  have hp : p ≠ missingBaryRank (k + 2) (by omega) hcard R := by
    rw [hlast]
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    simp [Fin.last] at hv
  change baryRidgeMemberAtRank (k + 2) (by omega) hcard R p hp ∈ R.1
  exact baryRidgeMemberAtRank_mem (k + 2) (by omega) hcard R p hp

theorem member_subset_terminalOldRidge
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1))
    {G : (barycentricSubdivision K).Vertex} (hGR : G ∈ R.1) :
    G.1 ⊆ (terminalOldRidge k hcard R hlast).1 := by
  let M : (barycentricSubdivision K).Vertex :=
    ⟨(terminalOldRidge k hcard R hlast).1,
      (terminalOldRidge k hcard R hlast).2.1⟩
  have hMR : M ∈ R.1 := terminalOldRidge_mem k hcard R hlast
  rcases R.2.1.2 G hGR M hMR with hGM | hMG
  · exact hGM
  · have hGcard : G.1.card ≤ k + 1 := by
      have hrankMem : baryRank (k + 2) hcard G ∈
          baryRidgeRankImage (k + 2) hcard R :=
        Finset.mem_image.mpr ⟨G, hGR, rfl⟩
      rw [baryRidgeRankImage_eq_erase_missing (k + 2) (by omega) hcard R,
        hlast] at hrankMem
      have hval : (baryRank (k + 2) hcard G).val ≤ k := by
        have hne := (Finset.mem_erase.mp hrankMem).1
        have hlt := (baryRank (k + 2) hcard G).isLt
        have hneVal : (baryRank (k + 2) hcard G).val ≠ k + 1 := by
          intro hv
          apply hne
          apply Fin.ext
          simpa [Fin.last] using hv
        omega
      have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
      dsimp [baryRank] at hval
      omega
    have hMcard : M.1.card = k + 1 := (terminalOldRidge k hcard R hlast).2.2.1
    have heq : M.1 = G.1 :=
      Finset.eq_of_subset_of_card_le hMG (by omega)
    change G.1 ⊆ M.1
    rw [heq]

noncomputable def terminalCandidateToOldTop
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1))
    (F : BaryInsertionFace (k + 2) (by omega) hcard R) :
    {T : RestrictedTopFace K U (k + 2) //
      FaceIncident (terminalOldRidge k hcard R hlast) T} := by
  have hFcard : F.1.1.card = k + 2 := by
    have hp : 0 < F.1.1.card := Finset.card_pos.mpr (K.face_nonempty F.1.2)
    have hr := congrArg Fin.val F.2.1
    rw [hlast] at hr
    dsimp [baryRank] at hr
    simp [Fin.last] at hr
    omega
  refine ⟨⟨F.1.1, F.1.2, hFcard, F.2.2.2⟩, ?_⟩
  have hcomp := F.2.2.1
    (⟨(terminalOldRidge k hcard R hlast).1,
      (terminalOldRidge k hcard R hlast).2.1⟩ : BaryVertex K)
    (terminalOldRidge_mem k hcard R hlast)
  rcases hcomp with hFM | hMF
  · have hc := Finset.card_le_card hFM
    rw [hFcard, (terminalOldRidge k hcard R hlast).2.2.1] at hc
    omega
  · exact hMF

noncomputable def oldTopToTerminalCandidate
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1))
    (T : {T : RestrictedTopFace K U (k + 2) //
      FaceIncident (terminalOldRidge k hcard R hlast) T}) :
    BaryInsertionFace (k + 2) (by omega) hcard R := by
  let F : (barycentricSubdivision K).Vertex := ⟨T.1.1, T.1.2.1⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · apply Fin.ext
    have hpos : 0 < T.1.1.card := by rw [T.1.2.2.1]; omega
    dsimp [baryRank, F]
    rw [T.1.2.2.1, hlast]
    simp [Fin.last]
  · intro G hGR
    right
    exact (member_subset_terminalOldRidge k hcard R hlast hGR).trans T.2
  · exact T.1.2.2.2

noncomputable def terminalCandidateEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    BaryInsertionFace (k + 2) (by omega) hcard R ≃
      {T : RestrictedTopFace K U (k + 2) //
        FaceIncident (terminalOldRidge k hcard R hlast) T} where
  toFun := terminalCandidateToOldTop k hcard R hlast
  invFun := oldTopToTerminalCandidate k hcard R hlast
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-! The internal-rank count is the elementary fact that between nested faces
whose cardinalities differ by two there are exactly two intermediate faces. -/

def IsIntermediateFace {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ) (F : BaryVertex K) : Prop :=
  A ⊆ F.1 ∧ F.1 ⊆ B ∧ F.1.card = q + 1

abbrev IntermediateFace {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ) :=
  {F : BaryVertex K // IsIntermediateFace A B q F}

noncomputable instance intermediateFaceFintype {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ) :
    Fintype (IntermediateFace A B q) := by
  classical
  infer_instance

noncomputable def eraseIntermediateFace {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2)
    (x : {x // x ∈ B \ A}) : IntermediateFace A B q := by
  classical
  have hxB : x.1 ∈ B := (Finset.mem_sdiff.mp x.2).1
  have hxA : x.1 ∉ A := (Finset.mem_sdiff.mp x.2).2
  have hnonempty : (B.erase x.1).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hxB, hBcard]
    omega
  refine ⟨⟨B.erase x.1,
    K.face_of_nonempty_subset hBface (Finset.erase_subset _ _) hnonempty⟩, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_erase]
    exact ⟨fun hax ↦ hxA (hax ▸ ha), hAB ha⟩
  · exact Finset.erase_subset _ _
  · rw [Finset.card_erase_of_mem hxB, hBcard]
    omega

theorem eraseIntermediateFace_injective {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    Function.Injective (eraseIntermediateFace A B q hAB hBface hAcard hBcard) := by
  classical
  intro x y hxy
  apply Subtype.ext
  apply (Finset.erase_inj B (Finset.mem_sdiff.mp x.2).1).mp
  exact congrArg (fun F => F.1.1) hxy

theorem eraseIntermediateFace_surjective {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    Function.Surjective (eraseIntermediateFace A B q hAB hBface hAcard hBcard) := by
  classical
  intro F
  have hnot : ¬B ⊆ F.1.1 := by
    intro hBF
    have hc := Finset.card_le_card hBF
    rw [hBcard, F.2.2.2] at hc
    omega
  have hex : ∃ x ∈ B, x ∉ F.1.1 := by
    by_contra hnone
    apply hnot
    intro x hxB
    by_contra hxF
    exact hnone ⟨x, hxB, hxF⟩
  obtain ⟨x, hxB, hxF⟩ := hex
  have hxA : x ∉ A := fun hx ↦ hxF (F.2.1 hx)
  let xBA : {x // x ∈ B \ A} := ⟨x, Finset.mem_sdiff.mpr ⟨hxB, hxA⟩⟩
  refine ⟨xBA, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    change v ∈ B.erase x
    rw [Finset.mem_erase]
    exact ⟨fun hvx ↦ hxF (hvx ▸ hv), F.2.2.1 hv⟩
  · rw [(eraseIntermediateFace A B q hAB hBface hAcard hBcard xBA).2.2.2,
      F.2.2.2]

noncomputable def intermediateFaceEquiv {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    {x // x ∈ B \ A} ≃ IntermediateFace A B q :=
  Equiv.ofBijective
    (eraseIntermediateFace A B q hAB hBface hAcard hBcard)
    ⟨eraseIntermediateFace_injective A B q hAB hBface hAcard hBcard,
      eraseIntermediateFace_surjective A B q hAB hBface hAcard hBcard⟩

theorem card_intermediateFace_eq_two {K : FiniteComplex}
    (A B : Finset K.Vertex) (q : ℕ)
    (hAB : A ⊆ B) (hBface : K.IsFace B)
    (hAcard : A.card = q) (hBcard : B.card = q + 2) :
    Fintype.card (IntermediateFace A B q) = 2 := by
  classical
  rw [← Fintype.card_congr
    (intermediateFaceEquiv A B q hAB hBface hAcard hBcard)]
  rw [Fintype.card_coe, Finset.card_sdiff_of_subset hAB, hBcard, hAcard]
  omega

theorem baryRank_card
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (F : (barycentricSubdivision K).Vertex) :
    F.1.card = (baryRank d hcard F).val + 1 := by
  have hp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  dsimp [baryRank]
  omega

noncomputable def internalUpperFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    (barycentricSubdivision K).Vertex := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  have hi : i.val < k + 1 := by
    have hlt := i.isLt
    have hneVal : i.val ≠ k + 1 := by
      intro hval
      apply hinternal
      apply Fin.ext
      simpa [i, Fin.last] using hval
    omega
  let u : Fin (k + 2) := ⟨i.val + 1, by omega⟩
  have hu : u ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [u] at hv
    omega
  exact baryRidgeMemberAtRank (k + 2) (by omega) hcard R u hu

theorem internalUpperFace_mem
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    internalUpperFace k hcard R hinternal ∈ R.1 := by
  unfold internalUpperFace
  exact baryRidgeMemberAtRank_mem _ _ _ _ _ _

theorem internalUpperFace_card
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    (internalUpperFace k hcard R hinternal).1.card =
      (missingBaryRank (k + 2) (by omega) hcard R).val + 2 := by
  unfold internalUpperFace
  rw [baryRidgeMemberAtRank_card]

noncomputable def internalLowerSet
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2)) :
    Finset K.Vertex := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  if hi : i.val = 0 then exact ∅
  else
    let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
    have hl : l ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [l] at hv
      omega
    exact (baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl).1

theorem internalLowerSet_card
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2)) :
    (internalLowerSet k hcard R).card =
      (missingBaryRank (k + 2) (by omega) hcard R).val := by
  simp only [internalLowerSet]
  split_ifs with hi
  · simp [hi]
  · rw [baryRidgeMemberAtRank_card]
    change (missingBaryRank (k + 2) (by omega) hcard R).val - 1 + 1 =
      (missingBaryRank (k + 2) (by omega) hcard R).val
    omega

theorem internalLowerSet_subset_upperFace
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    internalLowerSet k hcard R ⊆ (internalUpperFace k hcard R hinternal).1 := by
  simp only [internalLowerSet]
  split_ifs with hi
  · exact Finset.empty_subset _
  · let i := missingBaryRank (k + 2) (by omega) hcard R
    let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
    have hl : l ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [l] at hv
      omega
    let L := baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl
    let B := internalUpperFace k hcard R hinternal
    have hLR : L ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
    have hBR : B ∈ R.1 := internalUpperFace_mem k hcard R hinternal
    rcases R.2.1.2 L hLR B hBR with hLB | hBL
    · exact hLB
    · have hLc : L.1.card = i.val := by
        rw [baryRidgeMemberAtRank_card]
        dsimp [l]
        omega
      have hBc : B.1.card = i.val + 2 := internalUpperFace_card k hcard R hinternal
      have hc := Finset.card_le_card hBL
      rw [hLc, hBc] at hc
      omega

noncomputable def candidate_to_internalIntermediate
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1))
    (F : BaryInsertionFace (k + 2) (by omega) hcard R) :
    IntermediateFace (internalLowerSet k hcard R)
      (internalUpperFace k hcard R hinternal).1
      (missingBaryRank (k + 2) (by omega) hcard R).val := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  have hFcard : F.1.1.card = i.val + 1 := by
    rw [baryRank_card (k + 2) hcard F.1]
    rw [F.2.1]
  refine ⟨F.1, ?_, ?_, hFcard⟩
  · simp only [internalLowerSet]
    split_ifs with hi
    · exact Finset.empty_subset _
    · let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
      have hl : l ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [l] at hv
        omega
      let L := baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl
      have hLR : L ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
      rcases F.2.2.1 L hLR with hFL | hLF
      · have hLc : L.1.card = i.val := by
          rw [baryRidgeMemberAtRank_card]
          dsimp [l]
          omega
        have hc := Finset.card_le_card hFL
        rw [hFcard, hLc] at hc
        omega
      · exact hLF
  · let B := internalUpperFace k hcard R hinternal
    have hBR : B ∈ R.1 := internalUpperFace_mem k hcard R hinternal
    rcases F.2.2.1 B hBR with hFB | hBF
    · exact hFB
    · have hBc : B.1.card = i.val + 2 := internalUpperFace_card k hcard R hinternal
      have hc := Finset.card_le_card hBF
      rw [hBc, hFcard] at hc
      omega

noncomputable def internalIntermediate_to_candidate
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1))
    (F : IntermediateFace (internalLowerSet k hcard R)
      (internalUpperFace k hcard R hinternal).1
      (missingBaryRank (k + 2) (by omega) hcard R).val) :
    BaryInsertionFace (k + 2) (by omega) hcard R := by
  let i := missingBaryRank (k + 2) (by omega) hcard R
  refine ⟨F.1, ?_, ?_, ?_⟩
  · apply Fin.ext
    have hp : 0 < F.1.1.card := Finset.card_pos.mpr (K.face_nonempty F.1.2)
    dsimp [baryRank]
    rw [F.2.2.2]
    omega
  · intro G hGR
    have hGrankMem : baryRank (k + 2) hcard G ∈
        baryRidgeRankImage (k + 2) hcard R :=
      Finset.mem_image.mpr ⟨G, hGR, rfl⟩
    have hGrankNe : baryRank (k + 2) hcard G ≠ i := by
      intro heq
      exact missingBaryRank_not_mem (k + 2) (by omega) hcard R
        (heq ▸ hGrankMem)
    by_cases hlt : (baryRank (k + 2) hcard G).val < i.val
    · right
      have hi0 : i.val ≠ 0 := by omega
      let l : Fin (k + 2) := ⟨i.val - 1, by omega⟩
      have hl : l ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [l] at hv
        omega
      let L := baryRidgeMemberAtRank (k + 2) (by omega) hcard R l hl
      have hLR : L ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
      have hGL : G.1 ⊆ L.1 := by
        rcases R.2.1.2 G hGR L hLR with hGL | hLG
        · exact hGL
        · have hGc : G.1.card = (baryRank (k + 2) hcard G).val + 1 :=
            baryRank_card _ _ _
          have hLc : L.1.card = i.val := by
            rw [baryRidgeMemberAtRank_card]
            dsimp [l]
            omega
          have hc := Finset.card_le_card hLG
          rw [hLc, hGc] at hc
          have heq : L.1 = G.1 :=
            Finset.eq_of_subset_of_card_le hLG (by omega)
          simpa [heq]
      have hLF : L.1 ⊆ F.1.1 := by
        have hbase := F.2.1
        simpa [internalLowerSet, i, hi0, l, L] using hbase
      exact hGL.trans hLF
    · left
      have hgt : i.val < (baryRank (k + 2) hcard G).val := by
        have hneVal : (baryRank (k + 2) hcard G).val ≠ i.val := by
          intro hv
          exact hGrankNe (Fin.ext hv)
        omega
      let B := internalUpperFace k hcard R hinternal
      have hBR : B ∈ R.1 := internalUpperFace_mem k hcard R hinternal
      have hBG : B.1 ⊆ G.1 := by
        rcases R.2.1.2 B hBR G hGR with hBG | hGB
        · exact hBG
        · have hBc : B.1.card = i.val + 2 :=
            internalUpperFace_card k hcard R hinternal
          have hGc : G.1.card = (baryRank (k + 2) hcard G).val + 1 :=
            baryRank_card _ _ _
          have hc := Finset.card_le_card hGB
          rw [hGc, hBc] at hc
          have heq : G.1 = B.1 :=
            Finset.eq_of_subset_of_card_le hGB (by omega)
          simpa [heq]
      exact F.2.2.1.trans hBG
  · intro v hv
    exact R.2.2.2 (internalUpperFace k hcard R hinternal)
      (internalUpperFace_mem k hcard R hinternal) v (F.2.2.1 hv)

noncomputable def internalCandidateEquiv
    {K : FiniteComplex} {U : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    BaryInsertionFace (k + 2) (by omega) hcard R ≃
      IntermediateFace (internalLowerSet k hcard R)
        (internalUpperFace k hcard R hinternal).1
        (missingBaryRank (k + 2) (by omega) hcard R).val where
  toFun := candidate_to_internalIntermediate k hcard R hinternal
  invFun := internalIntermediate_to_candidate k hcard R hinternal
  left_inv F := by
    apply Subtype.ext
    rfl
  right_inv F := by
    apply Subtype.ext
    rfl

/-! The missing rank is terminal exactly on the equatorial boundary.  This is
the point where the codimension-one bound on equatorial faces is used. -/

theorem baryEquatorRidge_iff
    {K : FiniteComplex} {U E : K.Vertex → Prop} (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (hEcard : ∀ {s : Finset K.Vertex}, K.IsFace s →
      (∀ v ∈ s, E v) → s.card ≤ k + 1)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2)) :
    IsEquatorRidge (E := BaryUpper E) R ↔
      ∃ hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1),
        IsEquatorRidge (E := E) (terminalOldRidge k hcard R hlast) := by
  constructor
  · intro hEq
    have hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1) := by
      by_contra hinternal
      let p : Fin (k + 2) := Fin.last (k + 1)
      have hp : p ≠ missingBaryRank (k + 2) (by omega) hcard R := by
        exact fun h ↦ hinternal h.symm
      let M := baryRidgeMemberAtRank (k + 2) (by omega) hcard R p hp
      have hMR : M ∈ R.1 := baryRidgeMemberAtRank_mem _ _ _ _ _ _
      have hME : ∀ v ∈ M.1, E v := hEq M hMR
      have hsmall : M.1.card ≤ k + 1 := hEcard M.2 hME
      have hlarge : M.1.card = k + 2 := by
        rw [baryRidgeMemberAtRank_card]
        simp [p, Fin.last]
      omega
    refine ⟨hlast, ?_⟩
    intro v hv
    exact hEq
      ⟨(terminalOldRidge k hcard R hlast).1,
        (terminalOldRidge k hcard R hlast).2.1⟩
      (terminalOldRidge_mem k hcard R hlast) v hv
  · rintro ⟨hlast, hterminal⟩
    intro G hGR v hv
    exact hterminal v
      (member_subset_terminalOldRidge k hcard R hlast hGR hv)

theorem card_internalBaryInsertionFace_eq_two
    {K : FiniteComplex} {U : K.Vertex → Prop} [DecidablePred U] (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hinternal : missingBaryRank (k + 2) (by omega) hcard R ≠ Fin.last (k + 1)) :
    Fintype.card (BaryInsertionFace (k + 2) (by omega) hcard R) = 2 := by
  classical
  rw [Fintype.card_congr (internalCandidateEquiv k hcard R hinternal)]
  exact card_intermediateFace_eq_two
    (internalLowerSet k hcard R)
    (internalUpperFace k hcard R hinternal).1
    (missingBaryRank (k + 2) (by omega) hcard R).val
    (internalLowerSet_subset_upperFace k hcard R hinternal)
    (internalUpperFace k hcard R hinternal).2
    (internalLowerSet_card k hcard R)
    (internalUpperFace_card k hcard R hinternal)

theorem card_terminalBaryInsertionFace
    {K : FiniteComplex} {U E : K.Vertex → Prop}
    [DecidablePred U] [DecidablePred E] (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (H : HemisphereGeometry K U E (k + 2))
    (R : RestrictedRidge (barycentricSubdivision K) (BaryUpper U) (k + 2))
    (hlast : missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)) :
    Fintype.card (BaryInsertionFace (k + 2) (by omega) hcard R) =
      if IsEquatorRidge (E := E) (terminalOldRidge k hcard R hlast) then 1 else 2 := by
  classical
  rw [Fintype.card_congr (terminalCandidateEquiv k hcard R hlast)]
  have hdeg := H.ridge_degree (terminalOldRidge k hcard R hlast)
  by_cases h : ∀ v ∈ (terminalOldRidge k hcard R hlast).1, E v
  · rw [if_pos h] at hdeg
    rw [if_pos (show IsEquatorRidge (E := E)
      (terminalOldRidge k hcard R hlast) from h)]
    exact hdeg
  · rw [if_neg h] at hdeg
    rw [if_neg (show ¬IsEquatorRidge (E := E)
      (terminalOldRidge k hcard R hlast) from h)]
    exact hdeg

/-- Barycentric subdivision preserves the one-or-two coface law for a
triangulated hemisphere. -/
noncomputable def barycentricHemisphereGeometry
    {K : FiniteComplex} {U E : K.Vertex → Prop}
    [DecidablePred U] [DecidablePred E] (k : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ k + 2)
    (hEcard : ∀ {s : Finset K.Vertex}, K.IsFace s →
      (∀ v ∈ s, E v) → s.card ≤ k + 1)
    (H : HemisphereGeometry K U E (k + 2)) :
    HemisphereGeometry (barycentricSubdivision K) (BaryUpper U) (BaryUpper E)
      (k + 2) where
  ridge_degree R := by
    classical
    have hcofaces : Fintype.card
        {T : RestrictedTopFace (barycentricSubdivision K) (BaryUpper U) (k + 2) //
          FaceIncident R T} =
        Fintype.card (BaryInsertionFace (k + 2) (by omega) hcard R) :=
      Fintype.card_congr (baryInsertionFaceEquiv (k + 2) (by omega) hcard R).symm
    rw [hcofaces]
    by_cases hEq : ∀ v ∈ R.1, BaryUpper E v
    · rw [if_pos hEq]
      obtain ⟨hlast, hterminal⟩ :=
        (baryEquatorRidge_iff k hcard hEcard R).mp hEq
      rw [card_terminalBaryInsertionFace k hcard H R hlast, if_pos hterminal]
    · rw [if_neg hEq]
      by_cases hlast :
          missingBaryRank (k + 2) (by omega) hcard R = Fin.last (k + 1)
      · rw [card_terminalBaryInsertionFace k hcard H R hlast]
        rw [if_neg (fun hterminal ↦
          hEq ((baryEquatorRidge_iff k hcard hEcard R).mpr ⟨hlast, hterminal⟩))]
      · exact card_internalBaryInsertionFace_eq_two k hcard R hlast

/-! ### Iterating the hemisphere geometry -/

/-- A chain has at most `d` members if every face occurring as one of its
vertices has at most `d` old vertices. -/
theorem card_baryFace_le_of_vertex_card_bound
    {K : FiniteComplex} (d : ℕ)
    {S : Finset (barycentricSubdivision K).Vertex}
    (hS : (barycentricSubdivision K).IsFace S)
    (hbound : ∀ F ∈ S, F.1.card ≤ d) :
    S.card ≤ d := by
  classical
  have hdpos : 0 < d := by
    obtain ⟨G, hGS⟩ := hS.1
    have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
    have hGl := hbound G hGS
    omega
  let rank : BaryVertex K → Fin d := fun F ↦
    if hFS : F ∈ S then
      ⟨F.1.card - 1, by
        have hp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
        have hl := hbound F hFS
        omega⟩
    else ⟨0, hdpos⟩
  have hinj : Set.InjOn rank (↑S : Set (barycentricSubdivision K).Vertex) := by
    intro F hFS G hGS hrank
    have hFS' : F ∈ S := hFS
    have hGS' : G ∈ S := hGS
    apply Subtype.ext
    have hcardEq : F.1.card = G.1.card := by
      have hFp : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
      have hGp : 0 < G.1.card := Finset.card_pos.mpr (K.face_nonempty G.2)
      have hv := congrArg Fin.val hrank
      simp only [rank, hFS', hGS', dite_true] at hv
      omega
    rcases hS.2 F hFS G hGS with hFG | hGF
    · exact Finset.eq_of_subset_of_card_le hFG hcardEq.ge
    · exact (Finset.eq_of_subset_of_card_le hGF hcardEq.le).symm
  calc
    S.card = (S.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_card (by simp)
    _ = d := by simp

/-- Equatorial faces in the `r`th subdivision of the `(d+1)`-cross-polytope
have at most `d` vertices. -/
theorem card_equatorFace_iteratedBoundary_le (d r : ℕ)
    {s : Finset (iteratedBoundary (d + 1) r).Vertex}
    (hs : (iteratedBoundary (d + 1) r).IsFace s)
    (hEq : ∀ v ∈ s, EquatorVertex d r v) :
    s.card ≤ d := by
  induction r with
  | zero =>
      change Finset (crossPolytopeBoundary (d + 1)).Vertex at s
      change (crossPolytopeBoundary (d + 1)).IsFace s at hs
      change ∀ v ∈ s, BaseEquatorVertex d v at hEq
      have hinj : Set.InjOn Prod.fst
          (↑s : Set (crossPolytopeBoundary (d + 1)).Vertex) := by
        rintro ⟨i, b⟩ hib ⟨j, c⟩ hjc hij
        simp only [Prod.fst] at hij
        subst j
        have hbc : b = c := by
          by_contra hbc
          have hbool : (b = false ∧ c = true) ∨ (c = false ∧ b = true) := by
            cases b <;> cases c <;> simp_all
          rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hs.2 i ⟨hib, hjc⟩
          · exact hs.2 i ⟨hjc, hib⟩
        exact Prod.ext rfl hbc
      have hsubset : s.image Prod.fst ⊆
          (Finset.univ : Finset (Fin (d + 1))).erase (Fin.last d) := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨v, hv, rfl⟩
        exact Finset.mem_erase.mpr
          ⟨hEq v hv, Finset.mem_univ _⟩
      calc
        s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
        _ ≤ ((Finset.univ : Finset (Fin (d + 1))).erase (Fin.last d)).card :=
          Finset.card_le_card hsubset
        _ = d := by simp
  | succ r ih =>
      apply card_baryFace_le_of_vertex_card_bound d hs
      intro F hFs
      exact ih F.2 (hEq F hFs)

/-- Every iterated barycentric subdivision carries the same exact
upper-hemisphere ridge-degree law. -/
noncomputable def iteratedHemisphereGeometry (k r : ℕ) :
    HemisphereGeometry (iteratedBoundary (k + 2) r)
      (UpperVertex (k + 1) r) (EquatorVertex (k + 1) r) (k + 2) := by
  induction r with
  | zero =>
      have H := baseHemisphereGeometry (k + 1)
      refine ⟨?_⟩
      intro R
      have hdeg := H.ridge_degree R
      by_cases hEq : ∀ v ∈ R.1, EquatorVertex (k + 1) 0 v
      · rw [if_pos hEq]
        split at hdeg
        · exact hdeg
        · rename_i hnot
          exact (hnot hEq).elim
      · rw [if_neg hEq]
        split at hdeg
        · rename_i hyes
          exact (hEq hyes).elim
        · exact hdeg
  | succ r ih =>
      have H := barycentricHemisphereGeometry k
        (fun {s} hs ↦ card_face_iteratedBoundary_le (k + 2) r hs)
        (fun {s} hs hEq ↦
          card_equatorFace_iteratedBoundary_le (k + 1) r hs hEq)
        ih
      refine ⟨?_⟩
      intro R
      have hdeg := H.ridge_degree R
      by_cases hEq : ∀ v ∈ R.1, EquatorVertex (k + 1) (r + 1) v
      · rw [if_pos hEq]
        split at hdeg
        · exact hdeg
        · rename_i hnot
          exact (hnot hEq).elim
      · rw [if_neg hEq]
        split at hdeg
        · rename_i hyes
          exact (hEq hyes).elim
        · exact hdeg

/-! ### The refined equator as a lower-dimensional refined sphere -/

/-- The vertex equivalence between the equator and the lower-dimensional
sphere, bundled with preservation of all finite faces. -/
structure EquatorEquivData (d r : ℕ) where
  equiv : {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v} ≃
    (iteratedBoundary d r).Vertex
  face_iff : ∀ s : Finset {v : (iteratedBoundary (d + 1) r).Vertex //
      EquatorVertex d r v},
    (iteratedBoundary (d + 1) r).IsFace
        (s.map (Function.Embedding.subtype _)) ↔
      (iteratedBoundary d r).IsFace (s.map equiv.toEmbedding)

noncomputable def baseEquatorVertexEquiv (d : ℕ) :
    {v : (crossPolytopeBoundary (d + 1)).Vertex // BaseEquatorVertex d v} ≃
      (crossPolytopeBoundary d).Vertex where
  toFun v := (finPredOfNotLast v.1.1 v.2, v.1.2)
  invFun v := ⟨(Fin.castSucc v.1, v.2), by
    intro h
    have hv := congrArg Fin.val h
    have hlt := v.1.isLt
    simp [Fin.last] at hv
    omega⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (castSucc_finPredOfNotLast v.1.1 v.2) rfl
  right_inv v := by
    exact Prod.ext (by apply Fin.ext; rfl) rfl

theorem baseEquatorVertexEquiv_face_iff (d : ℕ)
    (s : Finset {v : (crossPolytopeBoundary (d + 1)).Vertex //
      BaseEquatorVertex d v}) :
    (crossPolytopeBoundary (d + 1)).IsFace
        (s.map (Function.Embedding.subtype _)) ↔
      (crossPolytopeBoundary d).IsFace
        (s.map (baseEquatorVertexEquiv d).toEmbedding) := by
  constructor
  · intro hs
    refine ⟨Finset.map_nonempty.mpr
      (Finset.map_nonempty.mp hs.1), ?_⟩
    intro i hi
    apply hs.2 (Fin.castSucc i)
    constructor
    · rcases Finset.mem_map.mp hi.1 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      change v.1 = (Fin.castSucc i, false)
      apply Prod.ext
      · calc
          v.1.1 = Fin.castSucc (finPredOfNotLast v.1.1 v.2) :=
            (castSucc_finPredOfNotLast v.1.1 v.2).symm
          _ = Fin.castSucc i := congrArg Fin.castSucc (congrArg Prod.fst heq)
      · have hbool := congrArg Prod.snd heq
        change v.1.2 = false at hbool
        exact hbool
    · rcases Finset.mem_map.mp hi.2 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      change v.1 = (Fin.castSucc i, true)
      apply Prod.ext
      · calc
          v.1.1 = Fin.castSucc (finPredOfNotLast v.1.1 v.2) :=
            (castSucc_finPredOfNotLast v.1.1 v.2).symm
          _ = Fin.castSucc i := congrArg Fin.castSucc (congrArg Prod.fst heq)
      · have hbool := congrArg Prod.snd heq
        change v.1.2 = true at hbool
        exact hbool
  · intro hs
    refine ⟨Finset.map_nonempty.mpr
      (Finset.map_nonempty.mp hs.1), ?_⟩
    intro i hi
    have hine : i ≠ Fin.last d := by
      intro hilast
      have hmem : (i, false) ∈ s.map (Function.Embedding.subtype _) := hi.1
      rcases Finset.mem_map.mp hmem with ⟨v, hv, heq⟩
      have hcoord : v.1.1 = i := congrArg Prod.fst heq
      exact v.2 (hcoord.trans hilast)
    let j := finPredOfNotLast i hine
    apply hs.2 j
    constructor
    · rcases Finset.mem_map.mp hi.1 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      have hcoord : v.1.1 = i := congrArg Prod.fst heq
      have hbool : v.1.2 = false := congrArg Prod.snd heq
      apply Prod.ext
      · apply Fin.ext
        dsimp [baseEquatorVertexEquiv, j, finPredOfNotLast]
        exact congrArg Fin.val hcoord
      · exact hbool
    · rcases Finset.mem_map.mp hi.2 with ⟨v, hv, heq⟩
      apply Finset.mem_map.mpr
      refine ⟨v, hv, ?_⟩
      have hcoord : v.1.1 = i := congrArg Prod.fst heq
      have hbool : v.1.2 = true := congrArg Prod.snd heq
      apply Prod.ext
      · apply Fin.ext
        dsimp [baseEquatorVertexEquiv, j, finPredOfNotLast]
        exact congrArg Fin.val hcoord
      · exact hbool

noncomputable def baseEquatorEquivData (d : ℕ) : EquatorEquivData d 0 where
  equiv := baseEquatorVertexEquiv d
  face_iff := by
    intro s
    exact baseEquatorVertexEquiv_face_iff d s

noncomputable def equatorBaryVertexToLower
    {d r : ℕ} (D : EquatorEquivData d r)
    (F : {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v}) :
    (iteratedBoundary d (r + 1)).Vertex := by
  let sE := F.1.1.subtype (EquatorVertex d r)
  refine ⟨sE.map D.equiv.toEmbedding, ?_⟩
  apply (D.face_iff sE).mp
  rw [Finset.subtype_map_of_mem F.2]
  exact F.1.2

noncomputable def lowerBaryVertexToEquator
    {d r : ℕ} (D : EquatorEquivData d r)
    (F : (iteratedBoundary d (r + 1)).Vertex) :
    {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v} := by
  let sE := F.1.map D.equiv.symm.toEmbedding
  have hface : (iteratedBoundary (d + 1) r).IsFace
      (sE.map (Function.Embedding.subtype _)) := by
    apply (D.face_iff sE).mpr
    simpa [sE, Finset.map_map] using F.2
  refine ⟨⟨sE.map (Function.Embedding.subtype _), hface⟩, ?_⟩
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
  exact w.2

noncomputable def equatorBaryVertexEquiv
    {d r : ℕ} (D : EquatorEquivData d r) :
    {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v} ≃
      (iteratedBoundary d (r + 1)).Vertex where
  toFun := equatorBaryVertexToLower D
  invFun := lowerBaryVertexToEquator D
  left_inv F := by
    have hFE : ∀ v ∈ F.1.1, EquatorVertex d r v := F.2
    apply Subtype.ext
    apply Subtype.ext
    ext v
    simp [equatorBaryVertexToLower, lowerBaryVertexToEquator,
      Finset.map_map, hFE]
    exact fun hv ↦ hFE v hv
  right_inv F := by
    have heq : ∀ a b : (iteratedBoundary d r).Vertex,
        (D.equiv.symm a).1 = (D.equiv.symm b).1 ↔ a = b := by
      intro a b
      constructor
      · intro h
        exact D.equiv.symm.injective (Subtype.ext h)
      · rintro rfl
        rfl
    apply Subtype.ext
    ext v
    simp [equatorBaryVertexToLower, lowerBaryVertexToEquator,
      Finset.map_map, heq]

theorem equatorBaryVertex_subset_iff
    {d r : ℕ} (D : EquatorEquivData d r)
    (F G : {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v}) :
    F.1.1 ⊆ G.1.1 ↔
      (equatorBaryVertexToLower D F).1 ⊆
        (equatorBaryVertexToLower D G).1 := by
  constructor
  · intro hFG x hx
    rcases Finset.mem_map.mp hx with ⟨w, hw, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨w, Finset.mem_subtype.mpr (hFG (Finset.mem_subtype.mp hw)), rfl⟩
  · intro hFG v hv
    let wF : {v : (iteratedBoundary (d + 1) r).Vertex //
        EquatorVertex d r v} := ⟨v, F.2 v hv⟩
    have hwF : wF ∈ F.1.1.subtype (EquatorVertex d r) :=
      Finset.mem_subtype.mpr hv
    have himage : D.equiv wF ∈ (equatorBaryVertexToLower D F).1 := by
      exact Finset.mem_map.mpr ⟨wF, hwF, rfl⟩
    have himageG := hFG himage
    rcases Finset.mem_map.mp himageG with ⟨wG, hwG, heq⟩
    have hwEq : wG = wF := D.equiv.injective heq
    exact Finset.mem_subtype.mp (hwEq ▸ hwG)

theorem equatorBaryVertexEquiv_face_iff
    {d r : ℕ} (D : EquatorEquivData d r)
    (s : Finset {v : (iteratedBoundary (d + 1) (r + 1)).Vertex //
      EquatorVertex d (r + 1) v}) :
    (iteratedBoundary (d + 1) (r + 1)).IsFace
        (s.map (Function.Embedding.subtype _)) ↔
      (iteratedBoundary d (r + 1)).IsFace
        (s.map (equatorBaryVertexEquiv D).toEmbedding) := by
  constructor
  · intro hs
    refine ⟨Finset.map_nonempty.mpr (Finset.map_nonempty.mp hs.1), ?_⟩
    intro A hA B hB
    rcases Finset.mem_map.mp hA with ⟨F, hF, rfl⟩
    rcases Finset.mem_map.mp hB with ⟨G, hG, rfl⟩
    have hF' : F.1 ∈ s.map (Function.Embedding.subtype _) :=
      Finset.mem_map.mpr ⟨F, hF, rfl⟩
    have hG' : G.1 ∈ s.map (Function.Embedding.subtype _) :=
      Finset.mem_map.mpr ⟨G, hG, rfl⟩
    rcases hs.2 F.1 hF' G.1 hG' with hFG | hGF
    · exact Or.inl ((equatorBaryVertex_subset_iff D F G).mp hFG)
    · exact Or.inr ((equatorBaryVertex_subset_iff D G F).mp hGF)
  · intro hs
    refine ⟨Finset.map_nonempty.mpr (Finset.map_nonempty.mp hs.1), ?_⟩
    intro A hA B hB
    rcases Finset.mem_map.mp hA with ⟨F, hF, rfl⟩
    rcases Finset.mem_map.mp hB with ⟨G, hG, rfl⟩
    have hF' : equatorBaryVertexToLower D F ∈
        s.map (equatorBaryVertexEquiv D).toEmbedding :=
      Finset.mem_map.mpr ⟨F, hF, rfl⟩
    have hG' : equatorBaryVertexToLower D G ∈
        s.map (equatorBaryVertexEquiv D).toEmbedding :=
      Finset.mem_map.mpr ⟨G, hG, rfl⟩
    rcases hs.2 _ hF' _ hG' with hFG | hGF
    · exact Or.inl ((equatorBaryVertex_subset_iff D F G).mpr hFG)
    · exact Or.inr ((equatorBaryVertex_subset_iff D G F).mpr hGF)

noncomputable def succEquatorEquivData
    {d r : ℕ} (D : EquatorEquivData d r) : EquatorEquivData d (r + 1) where
  equiv := equatorBaryVertexEquiv D
  face_iff := equatorBaryVertexEquiv_face_iff D

noncomputable def equatorEquivData (d : ℕ) : ∀ r, EquatorEquivData d r
  | 0 => baseEquatorEquivData d
  | r + 1 => succEquatorEquivData (equatorEquivData d r)

/-- Positive-first alternating top faces, separated from the
positive-or-negative predicate used by hemisphere handshaking. -/
def IsPositiveAlternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) : Prop :=
  ∃ idx : Fin d → Fin m,
    StrictMono idx ∧ T.1.image label = alternatingLabelSetOf idx

noncomputable instance isPositiveAlternatingTopDecidable
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) :
    DecidablePred (IsPositiveAlternatingTop (U := U) (d := d) label) := by
  classical
  intro T
  infer_instance

abbrev FullPositiveAlternatingTop
    (K : FiniteComplex) (d m : ℕ) (label : K.Vertex → SignedLabel m) :=
  {T : RestrictedTopFace K (fun _ ↦ True) d //
    IsPositiveAlternatingTop label T}

noncomputable def equatorRidgeToLowerTop (d r : ℕ)
    (R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R}) :
    RestrictedTopFace (iteratedBoundary d r) (fun _ ↦ True) d := by
  let D := equatorEquivData d r
  let sE := R.1.1.subtype (EquatorVertex d r)
  refine ⟨sE.map D.equiv.toEmbedding, ?_, ?_, ?_⟩
  · apply (D.face_iff sE).mp
    rw [Finset.subtype_map_of_mem R.2]
    exact R.1.2.1
  · rw [Finset.card_map]
    have hall : R.1.1.filter (EquatorVertex d r) = R.1.1 :=
      Finset.filter_eq_self.mpr R.2
    rw [show sE.card = (R.1.1.filter (EquatorVertex d r)).card by
      simp [sE, Finset.subtype]]
    rw [hall, R.1.2.2.1]
    omega
  · simp

noncomputable def lowerTopToEquatorRidge (d r : ℕ)
    (T : RestrictedTopFace (iteratedBoundary d r) (fun _ ↦ True) d) :
    {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R} := by
  let D := equatorEquivData d r
  let sE := T.1.map D.equiv.symm.toEmbedding
  let s := sE.map (Function.Embedding.subtype _)
  have hsface : (iteratedBoundary (d + 1) r).IsFace s := by
    apply (D.face_iff sE).mpr
    simpa [sE, Finset.map_map] using T.2.1
  have hsEq : ∀ v ∈ s, EquatorVertex d r v := by
    intro v hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact w.2
  refine ⟨⟨s, hsface, ?_, ?_⟩, hsEq⟩
  · dsimp [s]
    rw [Finset.card_map, Finset.card_map, T.2.2.1]
  · intro v hv
    exact equatorVertex_upperVertex d r (hsEq v hv)

noncomputable def equatorRidgeEquivLowerTop (d r : ℕ) :
    {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R} ≃
    RestrictedTopFace (iteratedBoundary d r) (fun _ ↦ True) d where
  toFun := equatorRidgeToLowerTop d r
  invFun := lowerTopToEquatorRidge d r
  left_inv R := by
    apply Subtype.ext
    apply Subtype.ext
    ext v
    simp [equatorRidgeToLowerTop, lowerTopToEquatorRidge,
      Finset.map_map]
    exact R.2 v
  right_inv T := by
    apply Subtype.ext
    ext v
    have heq : ∀ a b : (iteratedBoundary d r).Vertex,
        ((equatorEquivData d r).equiv.symm a).1 =
          ((equatorEquivData d r).equiv.symm b).1 ↔ a = b := by
      intro a b
      constructor
      · intro h
        exact (equatorEquivData d r).equiv.symm.injective (Subtype.ext h)
      · rintro rfl
        rfl
    simp [equatorRidgeToLowerTop, lowerTopToEquatorRidge,
      Finset.map_map, heq]

noncomputable def equatorRestrictedLabel (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    (iteratedBoundary d r).Vertex → SignedLabel m :=
  fun v ↦ label (((equatorEquivData d r).equiv.symm v).1)

theorem image_equatorRestrictedLabel_equatorRidgeToLowerTop
    (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m)
    (R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R}) :
    (equatorRidgeToLowerTop d r R).1.image (equatorRestrictedLabel d r m label) =
      R.1.1.image label := by
  classical
  apply Finset.ext
  intro z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    refine ⟨w.1, Finset.mem_subtype.mp hw, ?_⟩
    symm
    change label (((equatorEquivData d r).equiv.symm
      ((equatorEquivData d r).equiv w)).1) = label w.1
    rw [(equatorEquivData d r).equiv.symm_apply_apply]
  · rintro ⟨v, hv, rfl⟩
    let w : {v : (iteratedBoundary (d + 1) r).Vertex //
        EquatorVertex d r v} := ⟨v, R.2 v hv⟩
    refine ⟨(equatorEquivData d r).equiv w, ?_, ?_⟩
    · exact Finset.mem_map.mpr
        ⟨w, Finset.mem_subtype.mpr hv, rfl⟩
    · change label (((equatorEquivData d r).equiv.symm
        ((equatorEquivData d r).equiv w)).1) = label v
      rw [(equatorEquivData d r).equiv.symm_apply_apply]

theorem positiveAlternating_equatorRidge_iff_lowerTop
    (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m)
    (R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) // IsEquatorRidge (E := EquatorVertex d r) R}) :
    IsPositiveAlternatingRidge label R.1 ↔
      IsPositiveAlternatingTop (equatorRestrictedLabel d r m label)
        (equatorRidgeToLowerTop d r R) := by
  unfold IsPositiveAlternatingRidge IsPositiveAlternatingTop
  rw [image_equatorRestrictedLabel_equatorRidgeToLowerTop]
  rfl

noncomputable def equatorPositiveReassociate (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) m label //
        IsEquatorRidge (E := EquatorVertex d r) R.1} ≃
    {R : {R : RestrictedRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) //
        IsEquatorRidge (E := EquatorVertex d r) R} //
      IsPositiveAlternatingRidge label R.1} where
  toFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  invFun R := ⟨⟨R.1.1, R.2⟩, R.1.2⟩
  left_inv R := by cases R; rfl
  right_inv R := by cases R; rfl

noncomputable def positiveEquatorRidgeEquivLowerTop (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
      (UpperVertex d r) (d + 1) m label //
        IsEquatorRidge (E := EquatorVertex d r) R.1} ≃
      FullPositiveAlternatingTop (iteratedBoundary d r) d m
        (equatorRestrictedLabel d r m label) :=
  (equatorPositiveReassociate d r m label).trans
    ((equatorRidgeEquivLowerTop d r).subtypeEquiv
      (positiveAlternating_equatorRidge_iff_lowerTop d r m label))

theorem odd_positiveEquatorRidge_iff_lowerTop (d r m : ℕ)
    (label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m) :
    Odd (Fintype.card
      {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
        (UpperVertex d r) (d + 1) m label //
          IsEquatorRidge (E := EquatorVertex d r) R.1}) ↔
    Odd (Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary d r) d m
        (equatorRestrictedLabel d r m label))) := by
  rw [Fintype.card_congr (positiveEquatorRidgeEquivLowerTop d r m label)]

/-! The equator equivalence is antipodal. -/

theorem equatorVertex_antipode_iff (d r : ℕ)
    (v : (iteratedBoundary (d + 1) r).Vertex) :
    EquatorVertex d r ((iteratedAntipode (d + 1) r).neg v) ↔
      EquatorVertex d r v := by
  induction r with
  | zero =>
      rcases v with ⟨i, b⟩
      cases b <;> rfl
  | succ r ih =>
      constructor
      · intro h w hw
        have hneg : (iteratedAntipode (d + 1) r).neg w ∈
            ((iteratedAntipode (d + 1) (r + 1)).neg v).1 := by
          exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
        exact (ih w).mp (h _ hneg)
      · intro h w hw
        rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
        exact (ih u).mpr (h u hu)

noncomputable def equatorAntipodeVertex (d r : ℕ)
    (v : {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v}) :
    {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v} :=
  ⟨(iteratedAntipode (d + 1) r).neg v.1,
    (equatorVertex_antipode_iff d r v.1).mpr v.2⟩

theorem equatorEquivData_antipode (d r : ℕ)
    (v : {v : (iteratedBoundary (d + 1) r).Vertex // EquatorVertex d r v}) :
    (equatorEquivData d r).equiv (equatorAntipodeVertex d r v) =
      (iteratedAntipode d r).neg ((equatorEquivData d r).equiv v) := by
  induction r with
  | zero =>
      rcases v with ⟨⟨i, b⟩, hi⟩
      cases b <;> rfl
  | succ r ih =>
      apply Subtype.ext
      ext w
      constructor
      · intro hw
        rcases Finset.mem_map.mp hw with ⟨u, hu, heq⟩
        rcases Finset.mem_subtype.mp hu with hu
        rcases Finset.mem_image.mp hu with ⟨a, ha, hau⟩
        have haEq : EquatorVertex d r a := v.2 a ha
        let aE : {x : (iteratedBoundary (d + 1) r).Vertex //
            EquatorVertex d r x} := ⟨a, haEq⟩
        have hueq : equatorAntipodeVertex d r aE = u := by
          apply Subtype.ext
          exact hau
        have hcomm := ih aE
        apply Finset.mem_image.mpr
        refine ⟨(equatorEquivData d r).equiv aE, ?_, ?_⟩
        · exact Finset.mem_map.mpr
            ⟨aE, Finset.mem_subtype.mpr ha, rfl⟩
        · calc
            (iteratedAntipode d r).neg ((equatorEquivData d r).equiv aE) =
                (equatorEquivData d r).equiv (equatorAntipodeVertex d r aE) :=
              hcomm.symm
            _ = (equatorEquivData d r).equiv u := congrArg _ hueq
            _ = w := heq
      · intro hw
        rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
        rcases Finset.mem_map.mp hu with ⟨aE, haE, rfl⟩
        have hcomm := ih aE
        apply Finset.mem_map.mpr
        let naE := equatorAntipodeVertex d r aE
        refine ⟨naE, ?_, ?_⟩
        · apply Finset.mem_subtype.mpr
          exact Finset.mem_image.mpr ⟨aE.1, Finset.mem_subtype.mp haE, rfl⟩
        · exact hcomm

theorem equatorRestrictedLabel_antipodal (d r m : ℕ)
    {label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m}
    (hanti : ∀ v, label ((iteratedAntipode (d + 1) r).neg v) = (label v).neg) :
    ∀ v, equatorRestrictedLabel d r m label ((iteratedAntipode d r).neg v) =
      (equatorRestrictedLabel d r m label v).neg := by
  intro v
  let w := (equatorEquivData d r).equiv.symm v
  have hcomm := equatorEquivData_antipode d r w
  have hpre : (equatorEquivData d r).equiv.symm
      ((iteratedAntipode d r).neg v) = equatorAntipodeVertex d r w := by
    apply (equatorEquivData d r).equiv.injective
    rw [(equatorEquivData d r).equiv.apply_symm_apply]
    simpa [w] using hcomm.symm
  change label (((equatorEquivData d r).equiv.symm
      ((iteratedAntipode d r).neg v)).1) =
    (label (((equatorEquivData d r).equiv.symm v).1)).neg
  rw [hpre]
  exact hanti w.1

theorem equatorRestrictedLabel_noComplementary (d r m : ℕ)
    {label : (iteratedBoundary (d + 1) r).Vertex → SignedLabel m}
    (hno : NoComplementaryFaceLabels (iteratedBoundary (d + 1) r) label) :
    NoComplementaryFaceLabels (iteratedBoundary d r)
      (equatorRestrictedLabel d r m label) := by
  intro s hs v hv w hw
  let D := equatorEquivData d r
  let sE := s.map D.equiv.symm.toEmbedding
  have hface : (iteratedBoundary (d + 1) r).IsFace
      (sE.map (Function.Embedding.subtype _)) := by
    apply (D.face_iff sE).mpr
    simpa [sE, Finset.map_map] using hs
  apply hno hface
  · exact Finset.mem_map.mpr
      ⟨D.equiv.symm v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩
  · exact Finset.mem_map.mpr
      ⟨D.equiv.symm w, Finset.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩

/-! ### Maximal faces split into two antipodal hemispheres -/

abbrev FullTopFace (K : FiniteComplex) (d : ℕ) :=
  RestrictedTopFace K (fun _ ↦ True) d

noncomputable def antipodeFullTop
    {K : FiniteComplex} (A : ComplexInvolution K) {d : ℕ}
    (T : FullTopFace K d) : FullTopFace K d := by
  refine ⟨T.1.image A.neg, A.face_neg T.2.1, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr A.neg_injective.injOn, T.2.2.1]
  · simp

noncomputable def antipodeFullTopEquiv
    {K : FiniteComplex} (A : ComplexInvolution K) (d : ℕ) :
    FullTopFace K d ≃ FullTopFace K d where
  toFun := antipodeFullTop A
  invFun := antipodeFullTop A
  left_inv T := by
    apply Subtype.ext
    exact A.image_neg_image_neg T.1
  right_inv T := by
    apply Subtype.ext
    exact A.image_neg_image_neg T.1

def IsUpperFullTop
    {K : FiniteComplex} (U : K.Vertex → Prop) {d : ℕ}
    (T : FullTopFace K d) : Prop :=
  ∀ v ∈ T.1, U v

noncomputable instance isUpperFullTopDecidable
    {K : FiniteComplex} (U : K.Vertex → Prop) [DecidablePred U] {d : ℕ} :
    DecidablePred (IsUpperFullTop U (d := d)) := by
  classical
  intro T
  infer_instance

theorem fullTopFace_coordinate_exists (d : ℕ)
    (T : FullTopFace (crossPolytopeBoundary d) d) (i : Fin d) :
    (i, false) ∈ T.1 ∨ (i, true) ∈ T.1 := by
  by_contra hnone
  push_neg at hnone
  have hinj : Set.InjOn Prod.fst
      (↑T.1 : Set (crossPolytopeBoundary d).Vertex) := by
    rintro ⟨j, b⟩ hj ⟨l, c⟩ hl heq
    simp only [Prod.fst] at heq
    subst l
    have hbc : b = c := by
      by_contra hbc
      cases b <;> cases c
      · exact hbc rfl
      · exact (T.2.1.2 j ⟨hj, hl⟩).elim
      · exact (T.2.1.2 j ⟨hl, hj⟩).elim
      · exact hbc rfl
    exact Prod.ext rfl hbc
  have hsubset : T.1.image Prod.fst ⊆ (Finset.univ : Finset (Fin d)).erase i := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨v, hv, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hvi
    rcases v with ⟨j, b⟩
    simp only [Prod.fst] at hvi
    subst j
    cases b
    · exact hnone.1 hv
    · exact hnone.2 hv
  have hc : d ≤ d - 1 := by
    calc
      d = T.1.card := T.2.2.1.symm
      _ = (T.1.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ ((Finset.univ : Finset (Fin d)).erase i).card :=
        Finset.card_le_card hsubset
      _ = d - 1 := by simp
  have hd : 0 < d := by have := i.isLt; omega
  omega

theorem baseFullTop_hemisphere_xor (k : ℕ)
    (T : FullTopFace (crossPolytopeBoundary (k + 1)) (k + 1)) :
    Xor (IsUpperFullTop (BaseUpperVertex k) T)
      (IsUpperFullTop (BaseUpperVertex k)
        (antipodeFullTop (crossPolytopeAntipode (k + 1)) T)) := by
  rcases fullTopFace_coordinate_exists (k + 1) T (Fin.last k) with hneg | hpos
  · refine Or.inr ⟨?_, ?_⟩
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      intro heq
      have hwpos : (Fin.last k, true) ∈ T.1 := by
        rcases w with ⟨i, b⟩
        cases b
        · have hbool : true = false := congrArg Prod.snd heq
          exact Bool.noConfusion hbool
        · have hi : i = Fin.last k := congrArg Prod.fst heq
          subst i
          exact hw
      exact T.2.1.2 (Fin.last k) ⟨hneg, hwpos⟩
    · intro hupper
      exact hupper (Fin.last k, false) hneg rfl
  · refine Or.inl ⟨?_, ?_⟩
    · intro v hv heq
      exact T.2.1.2 (Fin.last k) ⟨heq ▸ hv, hpos⟩
    · intro hanti
      have hmem : (Fin.last k, false) ∈
          (antipodeFullTop (crossPolytopeAntipode (k + 1)) T).1 :=
        Finset.mem_image.mpr ⟨(Fin.last k, true), hpos, rfl⟩
      exact hanti _ hmem rfl

noncomputable def baryTopRankImage
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) : Finset (Fin d) :=
  T.1.image (baryRank d hcard)

def topLastRank (d : ℕ) (hd : 1 ≤ d) : Fin d :=
  ⟨d - 1, by omega⟩

theorem baryTopRankImage_eq_univ
    {K : FiniteComplex} (d : ℕ)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    baryTopRankImage d hcard T = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (by simp)
  rw [baryTopRankImage, Finset.card_image_iff.mpr
    (baryRank_injective_on_chain d hcard T.2.1), T.2.2.1]
  simp

noncomputable def baryTopMaxFace
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) : BaryVertex K :=
  Classical.choose (Finset.mem_image.mp (show topLastRank d hd ∈
      baryTopRankImage d hcard T by
    rw [baryTopRankImage_eq_univ]
    simp))

theorem baryTopMaxFace_mem
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    baryTopMaxFace d hd hcard T ∈ T.1 :=
  (Classical.choose_spec (Finset.mem_image.mp (show topLastRank d hd ∈
      baryTopRankImage d hcard T by
    rw [baryTopRankImage_eq_univ]
    simp))).1

theorem baryTopMaxFace_rank
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    baryRank d hcard (baryTopMaxFace d hd hcard T) = topLastRank d hd :=
  (Classical.choose_spec (Finset.mem_image.mp (show topLastRank d hd ∈
      baryTopRankImage d hcard T by
    rw [baryTopRankImage_eq_univ]
    simp))).2

theorem baryTopMaxFace_card
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    (baryTopMaxFace d hd hcard T).1.card = d := by
  have hr := baryRank_card d hcard (baryTopMaxFace d hd hcard T)
  rw [baryTopMaxFace_rank] at hr
  dsimp [topLastRank] at hr
  omega

noncomputable def baryTopMaxOldTop
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) : FullTopFace K d :=
  ⟨(baryTopMaxFace d hd hcard T).1,
    (baryTopMaxFace d hd hcard T).2,
    baryTopMaxFace_card d hd hcard T,
    by simp⟩

theorem baryTop_member_subset_max
    {K : FiniteComplex} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d)
    {G : BaryVertex K} (hG : G ∈ T.1) :
    G.1 ⊆ (baryTopMaxFace d hd hcard T).1 := by
  let M := baryTopMaxFace d hd hcard T
  have hM : M ∈ T.1 := baryTopMaxFace_mem d hd hcard T
  rcases T.2.1.2 G hG M hM with hGM | hMG
  · exact hGM
  · have hc : G.1.card ≤ M.1.card := by
      rw [baryTopMaxFace_card]
      exact hcard G.2
    have heq := Finset.eq_of_subset_of_card_le hMG hc
    simpa [M, heq]

theorem baryFullTop_upper_iff_max
    {K : FiniteComplex} {U : K.Vertex → Prop} (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    IsUpperFullTop (BaryUpper U) T ↔
      IsUpperFullTop U (baryTopMaxOldTop d hd hcard T) := by
  constructor
  · intro h v hv
    exact h (baryTopMaxFace d hd hcard T)
      (baryTopMaxFace_mem d hd hcard T) v hv
  · intro h G hG v hv
    exact h v (baryTop_member_subset_max d hd hcard T hG hv)

theorem baryAntipodeFullTop_upper_iff_max
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (T : FullTopFace (barycentricSubdivision K) d) :
    IsUpperFullTop (BaryUpper U)
        (antipodeFullTop A.barycentricLift T) ↔
      IsUpperFullTop U
        (antipodeFullTop A (baryTopMaxOldTop d hd hcard T)) := by
  constructor
  · intro h v hv
    have hM : baryTopMaxFace d hd hcard T ∈ T.1 :=
      baryTopMaxFace_mem d hd hcard T
    have hnegM : A.barycentricLift.neg (baryTopMaxFace d hd hcard T) ∈
        (antipodeFullTop A.barycentricLift T).1 :=
      Finset.mem_image.mpr ⟨_, hM, rfl⟩
    exact h _ hnegM v hv
  · intro h F hF v hv
    rcases Finset.mem_image.mp hF with ⟨G, hG, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    apply h (A.neg w)
    apply Finset.mem_image.mpr
    exact ⟨w, baryTop_member_subset_max d hd hcard T hG hw, rfl⟩

theorem baryFullTop_hemisphere_xor
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    (d : ℕ) (hd : 1 ≤ d)
    (hcard : ∀ {s : Finset K.Vertex}, K.IsFace s → s.card ≤ d)
    (hold : ∀ T : FullTopFace K d,
      Xor (IsUpperFullTop U T)
        (IsUpperFullTop U (antipodeFullTop A T)))
    (T : FullTopFace (barycentricSubdivision K) d) :
    Xor (IsUpperFullTop (BaryUpper U) T)
      (IsUpperFullTop (BaryUpper U)
        (antipodeFullTop A.barycentricLift T)) := by
  rw [baryFullTop_upper_iff_max d hd hcard T,
    baryAntipodeFullTop_upper_iff_max A d hd hcard T]
  exact hold (baryTopMaxOldTop d hd hcard T)

theorem iteratedFullTop_hemisphere_xor (k r : ℕ)
    (T : FullTopFace (iteratedBoundary (k + 1) r) (k + 1)) :
    Xor (IsUpperFullTop (UpperVertex k r) T)
      (IsUpperFullTop (UpperVertex k r)
        (antipodeFullTop (iteratedAntipode (k + 1) r) T)) := by
  induction r with
  | zero => exact baseFullTop_hemisphere_xor k T
  | succ r ih =>
      exact baryFullTop_hemisphere_xor (iteratedAntipode (k + 1) r)
        (k + 1) (by omega)
        (fun {s} hs ↦ card_face_iteratedBoundary_le (k + 1) r hs)
        ih T

def IsNegativeAlternatingTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) : Prop :=
  ∃ idx : Fin d → Fin m,
    StrictMono idx ∧ T.1.image label = alternatingNegLabelSetOf idx

@[simp] theorem signedLabel_neg_neg {m : ℕ} (z : SignedLabel m) :
    z.neg.neg = z := by
  rcases z with ⟨b, i⟩
  cases b <;> rfl

theorem image_neg_alternatingLabelSetOf {d m : ℕ} (idx : Fin d → Fin m) :
    (alternatingLabelSetOf idx).image SignedLabel.neg =
      alternatingNegLabelSetOf idx := by
  classical
  ext z
  simp [alternatingLabelSetOf, alternatingNegLabelSetOf]

theorem image_neg_alternatingNegLabelSetOf {d m : ℕ} (idx : Fin d → Fin m) :
    (alternatingNegLabelSetOf idx).image SignedLabel.neg =
      alternatingLabelSetOf idx := by
  classical
  ext z
  simp [alternatingLabelSetOf, alternatingNegLabelSetOf]

theorem image_label_antipodeFullTop
    {K : FiniteComplex} (A : ComplexInvolution K) {d m : ℕ}
    (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : FullTopFace K d) :
    (antipodeFullTop A T).1.image label =
      (T.1.image label).image SignedLabel.neg := by
  classical
  change (T.1.image A.neg).image label =
    (T.1.image label).image SignedLabel.neg
  apply Finset.ext
  intro z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨label w, ⟨w, hw, rfl⟩, (hanti w).symm⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨A.neg w, ⟨w, hw, rfl⟩, hanti w⟩

theorem positive_antipodeFullTop_iff_negative
    {K : FiniteComplex} (A : ComplexInvolution K) {d m : ℕ}
    (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : FullTopFace K d) :
    IsPositiveAlternatingTop label (antipodeFullTop A T) ↔
      IsNegativeAlternatingTop label T := by
  unfold IsPositiveAlternatingTop IsNegativeAlternatingTop
  rw [image_label_antipodeFullTop A label hanti T]
  constructor
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    calc
      T.1.image label =
          ((T.1.image label).image SignedLabel.neg).image SignedLabel.neg := by
        ext z
        simp [SignedLabel.neg]
      _ = (alternatingLabelSetOf idx).image SignedLabel.neg := by rw [hset]
      _ = alternatingNegLabelSetOf idx := image_neg_alternatingLabelSetOf idx
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    rw [hset, image_neg_alternatingNegLabelSetOf]

theorem negative_antipodeFullTop_iff_positive
    {K : FiniteComplex} (A : ComplexInvolution K) {d m : ℕ}
    (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : FullTopFace K d) :
    IsNegativeAlternatingTop label (antipodeFullTop A T) ↔
      IsPositiveAlternatingTop label T := by
  unfold IsNegativeAlternatingTop IsPositiveAlternatingTop
  rw [image_label_antipodeFullTop A label hanti T]
  constructor
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    calc
      T.1.image label =
          ((T.1.image label).image SignedLabel.neg).image SignedLabel.neg := by
        ext z
        simp
      _ = (alternatingNegLabelSetOf idx).image SignedLabel.neg := by rw [hset]
      _ = alternatingLabelSetOf idx := image_neg_alternatingNegLabelSetOf idx
  · rintro ⟨idx, hidx, hset⟩
    refine ⟨idx, hidx, ?_⟩
    rw [hset, image_neg_alternatingLabelSetOf]

theorem alternatingTop_iff_positive_or_negative
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsAlternatingTop label T ↔
      IsPositiveAlternatingTop label T ∨ IsNegativeAlternatingTop label T := by
  rfl

theorem positiveAlternatingTop_iff_labelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsPositiveAlternatingTop label T ↔ IsAltPosLabelSeq (topLabelSeq label T) := by
  unfold IsPositiveAlternatingTop IsAltPosLabelSeq
  rw [← image_label_top_eq_labelSeqSet]

theorem negativeAlternatingTop_iff_labelSeq
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d) :
    IsNegativeAlternatingTop label T ↔ IsAltNegLabelSeq (topLabelSeq label T) := by
  unfold IsNegativeAlternatingTop IsAltNegLabelSeq
  rw [← image_label_top_eq_labelSeqSet]

theorem positiveAlternatingTop_not_negative
    {K : FiniteComplex} {U : K.Vertex → Prop} {d m : ℕ} (hd : 0 < d)
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U d)
    (hpos : IsPositiveAlternatingTop label T)
    (hneg : IsNegativeAlternatingTop label T) : False :=
  IsAltPosLabelSeq.not_isAltNeg hd
    ((positiveAlternatingTop_iff_labelSeq label T).mp hpos)
    ((negativeAlternatingTop_iff_labelSeq label T).mp hneg)

noncomputable def restrictFullTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (T : FullTopFace K d) (hU : IsUpperFullTop U T) :
    RestrictedTopFace K U d :=
  ⟨T.1, T.2.1, T.2.2.1, hU⟩

def forgetUpperTop
    {K : FiniteComplex} {U : K.Vertex → Prop} {d : ℕ}
    (T : RestrictedTopFace K U d) : FullTopFace K d :=
  ⟨T.1, T.2.1, T.2.2.1, by simp⟩

noncomputable def fullPositiveToUpperAlternating
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    {d m : ℕ} (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (hsplit : ∀ T : FullTopFace K d,
      Xor (IsUpperFullTop U T)
        (IsUpperFullTop U (antipodeFullTop A T)))
    (T : FullPositiveAlternatingTop K d m label) :
    {T : RestrictedTopFace K U d // IsAlternatingTop label T} := by
  by_cases hU : IsUpperFullTop U T.1
  · exact ⟨restrictFullTop T.1 hU, Or.inl T.2⟩
  · have hAU : IsUpperFullTop U (antipodeFullTop A T.1) := by
      rcases hsplit T.1 with h | h
      · exact False.elim (hU h.1)
      · exact h.1
    refine ⟨restrictFullTop (antipodeFullTop A T.1) hAU, Or.inr ?_⟩
    exact (negative_antipodeFullTop_iff_positive A label hanti T.1).mpr T.2

noncomputable def upperAlternatingToFullPositive
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    {d m : ℕ} (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (T : {T : RestrictedTopFace K U d // IsAlternatingTop label T}) :
    FullPositiveAlternatingTop K d m label := by
  by_cases hpos : IsPositiveAlternatingTop label T.1
  · exact ⟨forgetUpperTop T.1, hpos⟩
  · have hneg : IsNegativeAlternatingTop label T.1 :=
      (alternatingTop_iff_positive_or_negative label T.1).mp T.2 |>.resolve_left hpos
    exact ⟨antipodeFullTop A (forgetUpperTop T.1),
      (positive_antipodeFullTop_iff_negative A label hanti _).mpr hneg⟩

noncomputable def fullPositiveEquivUpperAlternating
    {K : FiniteComplex} {U : K.Vertex → Prop} (A : ComplexInvolution K)
    {d m : ℕ} (hd : 0 < d) (label : K.Vertex → SignedLabel m)
    (hanti : ∀ v, label (A.neg v) = (label v).neg)
    (hsplit : ∀ T : FullTopFace K d,
      Xor (IsUpperFullTop U T)
        (IsUpperFullTop U (antipodeFullTop A T))) :
    FullPositiveAlternatingTop K d m label ≃
      {T : RestrictedTopFace K U d // IsAlternatingTop label T} where
  toFun := fullPositiveToUpperAlternating A label hanti hsplit
  invFun := upperAlternatingToFullPositive A label hanti
  left_inv T := by
    classical
    unfold fullPositiveToUpperAlternating upperAlternatingToFullPositive
    split <;> rename_i hU
    · simp only
      split <;> rename_i hpos
      · apply Subtype.ext
        apply Subtype.ext
        rfl
      · exact False.elim (hpos T.2)
    · simp only
      have hnegAnti : IsNegativeAlternatingTop label
          (restrictFullTop (antipodeFullTop A T.1) (by
            rcases hsplit T.1 with h | h
            · exact False.elim (hU h.1)
            · exact h.1)) :=
        (negative_antipodeFullTop_iff_positive A label hanti T.1).mpr T.2
      split <;> rename_i hposAnti
      · exact False.elim
          (positiveAlternatingTop_not_negative hd label _ hposAnti hnegAnti)
      · apply Subtype.ext
        apply Subtype.ext
        exact A.image_neg_image_neg T.1.1
  right_inv T := by
    classical
    unfold upperAlternatingToFullPositive fullPositiveToUpperAlternating
    split <;> rename_i hpos
    · simp only
      split <;> rename_i hU
      · apply Subtype.ext
        apply Subtype.ext
        rfl
      · exact False.elim (hU T.1.2.2.2)
    · simp only
      have hneg : IsNegativeAlternatingTop label T.1 :=
        (alternatingTop_iff_positive_or_negative label T.1).mp T.2 |>.resolve_left hpos
      have hnotAntiUpper : ¬IsUpperFullTop U
          (antipodeFullTop A (forgetUpperTop T.1)) := by
        intro hAU
        rcases hsplit (forgetUpperTop T.1) with h | h
        · exact h.2 hAU
        · exact False.elim (h.2 T.1.2.2.2)
      split <;> rename_i hAU
      · exact False.elim (hnotAntiUpper hAU)
      · apply Subtype.ext
        apply Subtype.ext
        exact A.image_neg_image_neg T.1.1

/-! ### The one-dimensional base of Ky Fan parity -/

noncomputable def upperZeroVertex : ∀ r, (iteratedBoundary 1 r).Vertex
  | 0 => (Fin.last 0, true)
  | r + 1 => ⟨{upperZeroVertex r},
      (iteratedBoundary 1 r).singleton_face (upperZeroVertex r)⟩

theorem upperZeroVertex_upper (r : ℕ) : UpperVertex 0 r (upperZeroVertex r) := by
  induction r with
  | zero =>
      intro h
      exact Bool.noConfusion (congrArg Prod.snd h)
  | succ r ih => simpa [upperZeroVertex, UpperVertex] using ih

theorem upperVertex_zero_eq (r : ℕ)
    {v : (iteratedBoundary 1 r).Vertex} (hv : UpperVertex 0 r v) :
    v = upperZeroVertex r := by
  induction r with
  | zero =>
      rcases v with ⟨i, b⟩
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      cases b
      · exact False.elim (hv rfl)
      · rfl
  | succ r ih =>
      apply Subtype.ext
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · obtain ⟨w, hw⟩ := (iteratedBoundary 1 r).face_nonempty v.2
        have hweq : w = upperZeroVertex r := ih (hv w hw)
        simpa [hweq] using hw
      · intro w hw
        exact ih (hv w hw)

noncomputable instance uniqueUpperZeroVertex (r : ℕ) :
    Unique {v : (iteratedBoundary 1 r).Vertex // UpperVertex 0 r v} where
  default := ⟨upperZeroVertex r, upperZeroVertex_upper r⟩
  uniq v := by
    apply Subtype.ext
    exact upperVertex_zero_eq r v.2

noncomputable def upperTopFaceOneEquiv
    {K : FiniteComplex} (U : K.Vertex → Prop) :
    RestrictedTopFace K U 1 ≃ {v : K.Vertex // U v} where
  toFun T := ⟨faceEnum T.1 1 T.2.2.1 0,
    T.2.2.2 _ (faceEnum_mem T.1 1 T.2.2.1 0)⟩
  invFun v := ⟨{v.1}, K.singleton_face v.1, by simp, by simpa using v.2⟩
  left_inv T := by
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      exact faceEnum_mem T.1 1 T.2.2.1 0
    · simp [T.2.2.1]
  right_inv v := by
    apply Subtype.ext
    have hm := faceEnum_mem ({v.1} : Finset K.Vertex) 1 (by simp) 0
    simpa using (Finset.mem_singleton.mp hm)

theorem every_one_top_alternating
    {K : FiniteComplex} {U : K.Vertex → Prop} {m : ℕ}
    (label : K.Vertex → SignedLabel m) (T : RestrictedTopFace K U 1) :
    IsAlternatingTop label T := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp T.2.2.1
  rcases hlabel : label v with ⟨b, i⟩
  cases b
  · right
    refine ⟨fun _ ↦ i, ?_, ?_⟩
    · intro a c hac
      omega
    · simp [hv, hlabel, alternatingNegLabelSetOf, alternatingLabelOf,
        SignedLabel.neg]
  · left
    refine ⟨fun _ ↦ i, ?_, ?_⟩
    · intro a c hac
      omega
    · simp [hv, hlabel, alternatingLabelSetOf, alternatingLabelOf]

noncomputable def upperOneAlternatingEquiv
    (r m : ℕ) (label : (iteratedBoundary 1 r).Vertex → SignedLabel m) :
    {T : RestrictedTopFace (iteratedBoundary 1 r) (UpperVertex 0 r) 1 //
      IsAlternatingTop label T} ≃
      RestrictedTopFace (iteratedBoundary 1 r) (UpperVertex 0 r) 1 where
  toFun T := T.1
  invFun T := ⟨T, every_one_top_alternating label T⟩
  left_inv T := by cases T; rfl
  right_inv T := rfl

theorem odd_fullPositiveAlternatingTop_one
    (r m : ℕ) (label : (iteratedBoundary 1 r).Vertex → SignedLabel m)
    (hanti : ∀ v, label ((iteratedAntipode 1 r).neg v) = (label v).neg) :
    Odd (Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary 1 r) 1 m label)) := by
  rw [Fintype.card_congr
    (fullPositiveEquivUpperAlternating (iteratedAntipode 1 r) (by omega)
      label hanti (iteratedFullTop_hemisphere_xor 0 r))]
  rw [Fintype.card_congr (upperOneAlternatingEquiv r m label)]
  rw [Fintype.card_congr (upperTopFaceOneEquiv (UpperVertex 0 r))]
  simp

/-! ### Ky Fan parity and fine Tucker lemma -/

theorem odd_fullPositiveAlternatingTop
    (d r m : ℕ) (hd : 0 < d)
    (label : (iteratedBoundary d r).Vertex → SignedLabel m)
    (hanti : ∀ v, label ((iteratedAntipode d r).neg v) = (label v).neg)
    (hno : NoComplementaryFaceLabels (iteratedBoundary d r) label) :
    Odd (Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary d r) d m label)) := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd0 : d = 0
      · subst d
        exact odd_fullPositiveAlternatingTop_one r m label hanti
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        let lowerLabel := equatorRestrictedLabel d r m label
        have hantiLower : ∀ v,
            lowerLabel ((iteratedAntipode d r).neg v) = (lowerLabel v).neg :=
          equatorRestrictedLabel_antipodal d r m hanti
        have hnoLower : NoComplementaryFaceLabels (iteratedBoundary d r) lowerLabel :=
          equatorRestrictedLabel_noComplementary d r m hno
        have hlower : Odd (Fintype.card
            (FullPositiveAlternatingTop (iteratedBoundary d r) d m lowerLabel)) :=
          ih hdpos lowerLabel hantiLower hnoLower
        have hboundary : Odd (Fintype.card
            {R : PositiveAlternatingRidge (iteratedBoundary (d + 1) r)
              (UpperVertex d r) (d + 1) m label //
                IsEquatorRidge (E := EquatorVertex d r) R.1}) :=
          (odd_positiveEquatorRidge_iff_lowerTop d r m label).mpr hlower
        have H : HemisphereGeometry (iteratedBoundary (d + 1) r)
            (UpperVertex d r) (EquatorVertex d r) (d + 1) := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
          exact iteratedHemisphereGeometry k r
        have hupper : Odd (Fintype.card
            {T : RestrictedTopFace (iteratedBoundary (d + 1) r)
              (UpperVertex d r) (d + 1) // IsAlternatingTop label T}) :=
          odd_alternatingTop_of_odd_equatorRidge hdpos hno H hboundary
        rw [Fintype.card_congr
          (fullPositiveEquivUpperAlternating (iteratedAntipode (d + 1) r)
            (by omega) label hanti (iteratedFullTop_hemisphere_xor d r))]
        exact hupper

/-- Fine Tucker lemma on every iterated barycentric cross-polytope: an
antipodal labeling by fewer absolute labels has a complementary pair in one
face. -/
theorem exists_complementary_face_of_antipodal_of_lt
    (d r m : ℕ) (hd : 0 < d) (hmd : m < d)
    (label : (iteratedBoundary d r).Vertex → SignedLabel m)
    (hanti : ∀ v, label ((iteratedAntipode d r).neg v) = (label v).neg) :
    ∃ (s : Finset (iteratedBoundary d r).Vertex),
      (iteratedBoundary d r).IsFace s ∧
        ∃ v ∈ s, ∃ w ∈ s, label v = (label w).neg := by
  by_contra hnone
  push Not at hnone
  have hno : NoComplementaryFaceLabels (iteratedBoundary d r) label := by
    intro s hs v hv w hw hcomp
    exact hnone s hs v hv w hw hcomp
  have hodd := odd_fullPositiveAlternatingTop d r m hd label hanti hno
  have hpos : 0 < Fintype.card
      (FullPositiveAlternatingTop (iteratedBoundary d r) d m label) := by
    rcases hodd with ⟨q, hq⟩
    omega
  obtain ⟨T⟩ := Fintype.card_pos_iff.mp hpos
  rcases T.2 with ⟨idx, hidx, hlabels⟩
  have hcard := Fintype.card_le_of_injective idx hidx.injective
  simp only [Fintype.card_fin] at hcard
  omega

end Erdos95.FineTucker
