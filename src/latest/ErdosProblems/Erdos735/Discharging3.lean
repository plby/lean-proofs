/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.Discharging12

/-!
# The third ABKPR discharging step for Erdős Problem 735

This file formalizes the large-face donations and the resulting
evil-triangle classification in integer quarter-units.
-/

namespace Erdos735

open scoped BigOperators

universe uV uE uF

namespace ABKPR.Data

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

/-- A triangle which has lost one quarter-unit to its unique neighboring bad
quadrangle after Step 2. -/
def IsBadTriangle (t : Face) : Prop :=
  C.faceDegree t = 3 ∧ A.badNeighborCount t = 1

instance (t : Face) : Decidable (A.IsBadTriangle t) := by
  unfold IsBadTriangle
  infer_instance

/-- The exact Stage-3 geometric relation.  A donor `f` has at least five
sides, the recipient `t` is a bad triangle, and, for the bad quadrangle `d`
across its unique bad edge, `f` shares a boundary edge with `d` and a
boundary vertex with `t`. -/
def DonationGeometry (f t : Face) : Prop :=
  A.IsBadTriangle t ∧ 5 ≤ C.faceDegree f ∧
    ∃ it : Fin (C.faceDegree t), it ∈ A.badNeighborIndices t ∧
      let d := (A.across ⟨t, it⟩).1
      (∃ jf : Fin (C.faceDegree f), ∃ jd : Fin (C.faceDegree d),
        A.boundaryEdge f jf = A.boundaryEdge d jd) ∧
      (∃ vf : Fin (C.faceDegree f), ∃ vt : Fin (C.faceDegree t),
        A.boundaryVertex f vf = A.boundaryVertex t vt)

noncomputable instance (f t : Face) : Decidable (A.DonationGeometry f t) := Classical.dec _

/-- Bad triangles to which `f` donates one quarter-unit in Stage 3. -/
noncomputable def donationRecipients (f : Face) : Finset Face :=
  Finset.univ.filter fun t => A.DonationGeometry f t

/-- Faces which donate one quarter-unit to `t` in Stage 3. -/
noncomputable def donationDonors (t : Face) : Finset Face :=
  Finset.univ.filter fun f => t ∈ A.donationRecipients f

lemma mem_donationRecipients_iff (f t : Face) :
    t ∈ A.donationRecipients f ↔ A.DonationGeometry f t := by
  simp [donationRecipients]

lemma mem_donationDonors_iff (t f : Face) :
    f ∈ A.donationDonors t ↔ A.DonationGeometry f t := by
  simp [donationDonors, A.mem_donationRecipients_iff]

lemma recipient_isBadTriangle {f t : Face} (h : t ∈ A.donationRecipients f) :
    A.IsBadTriangle t := (A.mem_donationRecipients_iff f t).mp h |>.1

lemma donor_degree_five_le {f t : Face} (h : t ∈ A.donationRecipients f) :
    5 ≤ C.faceDegree f := (A.mem_donationRecipients_iff f t).mp h |>.2.1

lemma donationRecipients_eq_empty_of_degree_lt_five {f : Face}
    (hf : C.faceDegree f < 5) : A.donationRecipients f = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨t, ht⟩
  exact (not_le_of_gt hf) (A.donor_degree_five_le ht)

lemma donationDonors_eq_empty_of_not_badTriangle {t : Face}
    (ht : ¬ A.IsBadTriangle t) : A.donationDonors t = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨f, hf⟩
  exact ht ((A.mem_donationDonors_iff t f).mp hf).1

/-- The remaining local input needed for Stage 3.  The first field is the
one-bad-quadrangle-per-triangle lemma.  The second is the free-vertex bound
on donations.  The last four fields are precisely the finite pentagon case
split in the ABKPR proof. -/
structure Stage3Hypotheses : Prop where
  oneBadQuadranglePerTriangle : ∀ t, C.faceDegree t = 3 → A.badNeighborCount t ≤ 1
  donation_count_bound : ∀ f,
    (A.donationRecipients f).card + 2 * (A.redChords f).card ≤ C.faceDegree f
  pentagon_twoChords : ∀ f, C.faceDegree f = 5 → (A.redChords f).card = 2 →
    A.badNeighborCount f = 0 ∧ (A.donationRecipients f).card = 0
  pentagon_oneChord : ∀ f, C.faceDegree f = 5 → (A.redChords f).card = 1 →
    A.badNeighborCount f ≤ 1 ∧ (A.donationRecipients f).card ≤ 1
  pentagon_noChord_allBad : ∀ f, C.faceDegree f = 5 →
    (A.redChords f).card = 0 → A.badNeighborCount f = 5 →
    (A.donationRecipients f).card = 0
  pentagon_noChord_allDonate : ∀ f, C.faceDegree f = 5 →
    (A.redChords f).card = 0 → (A.donationRecipients f).card = 5 →
    A.badNeighborCount f ≤ 2

/-- Step 3 subtracts one quarter-unit for every recipient and adds one for
every donor. -/
noncomputable def step3FaceCharge4 (f : Face) : ℤ :=
  A.step2FaceCharge4 f - (A.donationRecipients f).card +
    (A.donationDonors f).card

private lemma sum_card_incidence
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (row : α → Finset β) (column : β → Finset α)
    (h : ∀ a b, b ∈ row a ↔ a ∈ column b) :
    (∑ a, (row a).card) = ∑ b, (column b).card := by
  classical
  calc
    (∑ a, (row a).card) = ∑ a, ∑ b, if b ∈ row a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b, ∑ a, if b ∈ row a then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, if a ∈ column b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      simp only [h a b]
    _ = ∑ b, (column b).card := by
      apply Finset.sum_congr rfl
      intro b _
      simp

lemma sum_donationCounts :
    (∑ f, (A.donationRecipients f).card) =
      ∑ t, (A.donationDonors t).card := by
  apply sum_card_incidence A.donationRecipients A.donationDonors
  intro f t
  simp [donationDonors]

/-- Stage 3 is a redistribution, so the total charge remains `-24`. -/
theorem step3_total_charge :
    (∑ v, A.step1VertexCharge4 v) + (∑ f, A.step3FaceCharge4 f) = -24 := by
  have hcountNat := A.sum_donationCounts
  have hcount :
      (∑ f, ((A.donationRecipients f).card : ℤ)) =
        ∑ t, ((A.donationDonors t).card : ℤ) := by
    exact_mod_cast hcountNat
  have hstep2 := A.step2_total_charge
  simp only [step3FaceCharge4, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcount]
  linarith

lemma step3FaceCharge4_triangle (t : Face) (ht : C.faceDegree t = 3) :
    A.step3FaceCharge4 t =
      -(A.badNeighborCount t : ℤ) + (A.donationDonors t).card := by
  have hout := A.donationRecipients_eq_empty_of_degree_lt_five (f := t) (by omega)
  rw [step3FaceCharge4, A.step2FaceCharge4_triangle t ht, hout]
  simp

/-- The scaled `k >= 6` part of the large-face lemma after the Stage-3
donations. -/
lemma step3FaceCharge4_six_le_nonnegative
    (H : A.Stage3Hypotheses) (hpack : A.NeighborPacking)
    {f : Face} (hf : 6 ≤ C.faceDegree f) :
    0 ≤ A.step3FaceCharge4 f := by
  have hc := A.stage1Corners_card_le_twice_chords f
  have hb := hpack.1 f
  have hd := H.donation_count_bound f
  have hnotbad : ¬ A.IsBadTwoQuadrangle f := by
    intro h
    have h4 := h.1.1
    omega
  simp only [step3FaceCharge4, step2FaceCharge4, step1FaceCharge4,
    initialFaceCharge4, BlueCellulation.faceCharge, hnotbad, if_false]
  omega

/-- The three pentagon cases in the large-face lemma. -/
lemma step3FaceCharge4_pentagon_nonnegative
    (H : A.Stage3Hypotheses) (hpack : A.NeighborPacking)
    {f : Face} (hf : C.faceDegree f = 5) :
    0 ≤ A.step3FaceCharge4 f := by
  have hr := A.redChord_count_twice_le_degree f
  have hrle : (A.redChords f).card ≤ 2 := by omega
  have hc := A.stage1Corners_card_le_twice_chords f
  have hb := hpack.1 f
  have hd := H.donation_count_bound f
  have hnotbad : ¬ A.IsBadTwoQuadrangle f := by
    intro h
    have h4 := h.1.1
    omega
  have hnottriangle : ¬ A.IsBadTriangle f := by
    intro h
    have h3 := h.1
    omega
  have hin := A.donationDonors_eq_empty_of_not_badTriangle hnottriangle
  simp only [step3FaceCharge4, step2FaceCharge4, step1FaceCharge4,
    initialFaceCharge4, BlueCellulation.faceCharge, hnotbad, if_false, hin,
    Finset.card_empty, Nat.cast_zero, add_zero, hf]
  interval_cases hrn : (A.redChords f).card
  · by_cases hb5 : A.badNeighborCount f = 5
    · have hd0 := H.pentagon_noChord_allBad f hf hrn hb5
      omega
    · by_cases hd5 : (A.donationRecipients f).card = 5
      · have hb2 := H.pentagon_noChord_allDonate f hf hrn hd5
        omega
      · omega
  · have hcase := H.pentagon_oneChord f hf hrn
    omega
  · have hcase := H.pentagon_twoChords f hf hrn
    omega

/-- Every face with at least five sides remains nonnegative after Stage 3. -/
theorem step3FaceCharge4_large_nonnegative
    (H : A.Stage3Hypotheses) (hpack : A.NeighborPacking)
    {f : Face} (hf : 5 ≤ C.faceDegree f) :
    0 ≤ A.step3FaceCharge4 f := by
  rcases eq_or_lt_of_le hf with h5 | h6
  · exact A.step3FaceCharge4_pentagon_nonnegative H hpack h5.symm
  · exact A.step3FaceCharge4_six_le_nonnegative H hpack (by omega)

/-- A bad triangle which receives no Stage-3 donation. -/
def IsEvilTriangle (t : Face) : Prop :=
  A.IsBadTriangle t ∧ A.donationDonors t = ∅

noncomputable instance (t : Face) : Decidable (A.IsEvilTriangle t) := Classical.dec _

lemma step3FaceCharge4_evil {t : Face} (ht : A.IsEvilTriangle t) :
    A.step3FaceCharge4 t = -1 := by
  rw [A.step3FaceCharge4_triangle t ht.1.1, ht.1.2, ht.2]
  norm_num

/-- After Stage 3 the only negative faces are evil triangles, each of charge
`-1` in quarter-units. -/
theorem step3FaceCharge4_negative_iff_evil
    (H : A.Stage3Hypotheses) (hrest : A.EndpointRestriction)
    (hpack : A.NeighborPacking) (f : Face) :
    A.step3FaceCharge4 f < 0 ↔ A.IsEvilTriangle f := by
  constructor
  · intro hneg
    have hk : 3 ≤ C.faceDegree f := by
      simpa [BlueCellulation.faceDegree] using C.faceDegree_three_le f
    by_cases h3 : C.faceDegree f = 3
    · have htri := A.step3FaceCharge4_triangle f h3
      have hb := H.oneBadQuadranglePerTriangle f h3
      have hbad : A.badNeighborCount f = 1 := by
        rw [htri] at hneg
        omega
      have hin : A.donationDonors f = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [htri] at hneg
        omega
      exact ⟨⟨h3, hbad⟩, hin⟩
    · by_cases h4 : C.faceDegree f = 4
      · have hout := A.donationRecipients_eq_empty_of_degree_lt_five (f := f) (by omega)
        have hnottri : ¬ A.IsBadTriangle f := by
          intro h
          have ht3 := h.1
          omega
        have hin := A.donationDonors_eq_empty_of_not_badTriangle hnottri
        have hnon := A.step2FaceCharge4_quadrangle_nonnegative hrest hpack h4
        simp only [step3FaceCharge4, hout, hin, Finset.card_empty, Nat.cast_zero,
          sub_zero, add_zero] at hneg
        exact (not_lt_of_ge hnon hneg).elim
      · have h5 : 5 ≤ C.faceDegree f := by omega
        exact (not_lt_of_ge (A.step3FaceCharge4_large_nonnegative H hpack h5) hneg).elim
  · intro hevil
    rw [A.step3FaceCharge4_evil hevil]
    norm_num

end ABKPR.Data

end Erdos735
