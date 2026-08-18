/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# A finite symmetric Lovasz local lemma

This file gives a cardinality version of the symmetric local lemma on a
uniform finite probability space.  The formulation of independence is
deliberately local: a bad event must be independent of the simultaneous
avoidance of any collection of its non-neighbours.  In particular, it applies
to independent uniform coordinate colourings when each bad event is a
cylinder event and two events are declared adjacent whenever their coordinate
supports meet.
-/

open scoped BigOperators

namespace Erdos136
namespace LocalLemma

variable {Ω ι : Type*}

/-- Uniform probability of a finset in a nonempty finite sample space. -/
noncomputable def uniformProbability [Fintype Ω] (s : Finset Ω) : ℝ :=
  (s.card : ℝ) / Fintype.card Ω

/-- The assignments avoiding every event whose index belongs to `S`. -/
def avoiding [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (event : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ event i

section Elementary

variable [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]

lemma card_pos : 0 < (Fintype.card Ω : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma uniformProbability_nonneg (s : Finset Ω) : 0 ≤ uniformProbability s := by
  exact div_nonneg (by positivity) card_pos.le

lemma uniformProbability_mono {s t : Finset Ω} (hst : s ⊆ t) :
    uniformProbability s ≤ uniformProbability t := by
  unfold uniformProbability
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hst) card_pos.le

lemma uniformProbability_univ : uniformProbability (Finset.univ : Finset Ω) = 1 := by
  simp [uniformProbability, ne_of_gt card_pos]

lemma uniformProbability_union_le (s t : Finset Ω) :
    uniformProbability (s ∪ t) ≤ uniformProbability s + uniformProbability t := by
  unfold uniformProbability
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le s t) card_pos.le

lemma uniformProbability_biUnion_le [DecidableEq ι]
    (S : Finset ι) (f : ι → Finset Ω) :
    uniformProbability (S.biUnion f) ≤ ∑ i ∈ S, uniformProbability (f i) := by
  unfold uniformProbability
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (by
    exact_mod_cast (Finset.card_biUnion_le (s := S) (t := f))) card_pos.le

lemma uniformProbability_pos_iff_nonempty (s : Finset Ω) :
    0 < uniformProbability s ↔ s.Nonempty := by
  constructor
  · intro h
    rw [uniformProbability, div_pos_iff] at h
    rcases h with h | h
    · exact Finset.card_pos.mp (by exact_mod_cast h.1)
    · exfalso
      linarith [card_pos (Ω := Ω)]
  · intro hs
    exact div_pos (by exact_mod_cast hs.card_pos) card_pos

end Elementary

section Avoiding

variable [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable [Fintype ι] [DecidableEq ι]
variable (event : ι → Finset Ω)

@[simp] lemma avoiding_empty : avoiding event ∅ = Finset.univ := by
  ext
  simp [avoiding]

lemma avoiding_mono {S T : Finset ι} (hST : S ⊆ T) :
    avoiding event T ⊆ avoiding event S := by
  intro ω hω
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  intro i hi
  exact hω i (hST hi)

lemma avoiding_insert (i : ι) (S : Finset ι) :
    avoiding event (insert i S) = avoiding event S \ event i := by
  ext ω
  simp [avoiding, and_comm]

lemma avoiding_partition (i : ι) (S : Finset ι) :
    avoiding event S = avoiding event (insert i S) ∪ (event i ∩ avoiding event S) := by
  ext ω
  by_cases h : ω ∈ event i <;> simp [avoiding, h]

end Avoiding

section GeneralLocalLemma

variable [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable [Fintype ι] [DecidableEq ι]

/--
The finite symmetric local lemma in its usual auxiliary-parameter form.

`dep i j` says that the events with indices `i` and `j` may depend on one
another.  `h_indep` is precisely the independence needed in the proof: event
`i` is independent of avoiding any finite collection of its non-neighbours.
The hypotheses `h_px` and `h_Dx` are the standard inequalities
`p ≤ x(1-Dx)` and `Dx ≤ 1`.
-/
theorem exists_avoiding_of_aux
    (event : ι → Finset Ω) (dep : ι → ι → Prop) [DecidableRel dep]
    (p x : ℝ) (D : ℕ)
    (hp : 0 ≤ p) (hx : 0 < x) (hx1 : x < 1)
    (h_Dx : (D : ℝ) * x ≤ 1)
    (h_px : p ≤ x * (1 - (D : ℝ) * x))
    (h_event : ∀ i, uniformProbability (event i) ≤ p)
    (h_degree : ∀ i, ((Finset.univ.erase i).filter (dep i)).card ≤ D)
    (h_indep : ∀ i S, (∀ j ∈ S, ¬ dep i j) →
      uniformProbability (event i ∩ avoiding event S) =
        uniformProbability (event i) * uniformProbability (avoiding event S)) :
    ∃ ω : Ω, ∀ i, ω ∉ event i := by
  have hp_le_x : p ≤ x := by
    have hnonneg : 0 ≤ (D : ℝ) * x := mul_nonneg (by positivity) hx.le
    calc
      p ≤ x * (1 - (D : ℝ) * x) := h_px
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left (sub_le_self 1 hnonneg) hx.le
      _ = x := mul_one x

  /- The inductive conditional estimate
       P(A_i ∩ avoid S) ≤ x P(avoid S).
     It is stated without division, so it remains meaningful even if an
     intermediate avoidance set is empty. -/
  have conditional : ∀ S : Finset ι, ∀ i ∉ S,
      uniformProbability (event i ∩ avoiding event S) ≤
        x * uniformProbability (avoiding event S) := by
    intro S
    induction n : S.card using Nat.strong_induction_on generalizing S with
    | h n ih =>
      intro i hiS
      let N : Finset ι := S.filter (dep i)
      let F : Finset ι := S.filter fun j ↦ ¬ dep i j
      have hNF : S = N ∪ F := by
        ext j
        by_cases h : dep i j <;> simp [N, F, h]
      have hFsub : F ⊆ S := Finset.filter_subset _ _
      have hNsub : N ⊆ S := Finset.filter_subset _ _
      have hNFdisj : Disjoint N F := by
        rw [Finset.disjoint_left]
        intro j hjN hjF
        have hdep : dep i j := by
          change j ∈ S.filter (dep i) at hjN
          exact (Finset.mem_filter.mp hjN).2
        have hn_dep : ¬ dep i j := by
          change j ∈ S.filter (fun k ↦ ¬ dep i k) at hjF
          exact (Finset.mem_filter.mp hjF).2
        exact hn_dep hdep
      have hiF : i ∉ F := fun h ↦ hiS (hFsub h)
      have hF_non_neighbour (j : ι) (hj : j ∈ F) : ¬ dep i j :=
        (Finset.mem_filter.mp hj).2
      have hN_degree : N.card ≤ D := by
        apply (Finset.card_le_card ?_).trans (h_degree i)
        intro j hj
        have hjS : j ∈ S := hNsub hj
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hiS hjS
        have hdep : dep i j := by
          change j ∈ S.filter (dep i) at hj
          exact (Finset.mem_filter.mp hj).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hdep⟩
      have havoidS : avoiding event S = avoiding event (N ∪ F) := by rw [← hNF]
      have havoid_sub : avoiding event S ⊆ avoiding event F :=
        avoiding_mono event hFsub
      have hevent_sub : event i ∩ avoiding event S ⊆ event i ∩ avoiding event F :=
        Finset.inter_subset_inter (fun _ h ↦ h) havoid_sub
      have hnum : uniformProbability (event i ∩ avoiding event S) ≤
          p * uniformProbability (avoiding event F) := by
        calc
          uniformProbability (event i ∩ avoiding event S)
              ≤ uniformProbability (event i ∩ avoiding event F) :=
            uniformProbability_mono hevent_sub
          _ = uniformProbability (event i) * uniformProbability (avoiding event F) :=
            h_indep i F hF_non_neighbour
          _ ≤ p * uniformProbability (avoiding event F) :=
            mul_le_mul_of_nonneg_right (h_event i)
              (uniformProbability_nonneg (avoiding event F))
      have hcover : avoiding event F ⊆
          avoiding event S ∪ N.biUnion (fun j ↦ event j ∩ avoiding event F) := by
        intro ω hωF
        by_cases hωS : ω ∈ avoiding event S
        · exact Finset.mem_union_left _ hωS
        · have : ∃ j ∈ N, ω ∈ event j := by
            simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at hωF hωS
            push_neg at hωS
            obtain ⟨j, hjS, hωj⟩ := hωS
            have hjN_or_F : j ∈ N ∨ j ∈ F := by
              rw [← Finset.mem_union, ← hNF]
              exact hjS
            cases hjN_or_F with
            | inl hjN => exact ⟨j, hjN, hωj⟩
            | inr hjF => exact (hωF j hjF hωj).elim
          obtain ⟨j, hjN, hωj⟩ := this
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨j, hjN, Finset.mem_inter.mpr ⟨hωj, hωF⟩⟩)
      have hloss : uniformProbability (avoiding event F) ≤
          uniformProbability (avoiding event S) +
            ∑ j ∈ N, uniformProbability (event j ∩ avoiding event F) := by
        calc
          uniformProbability (avoiding event F) ≤
              uniformProbability
                (avoiding event S ∪ N.biUnion (fun j ↦ event j ∩ avoiding event F)) :=
            uniformProbability_mono hcover
          _ ≤ uniformProbability (avoiding event S) +
              uniformProbability (N.biUnion (fun j ↦ event j ∩ avoiding event F)) :=
            uniformProbability_union_le _ _
          _ ≤ uniformProbability (avoiding event S) +
              ∑ j ∈ N, uniformProbability (event j ∩ avoiding event F) := by
            gcongr
            exact uniformProbability_biUnion_le N _
      have hsum : ∑ j ∈ N, uniformProbability (event j ∩ avoiding event F) ≤
          (N.card : ℝ) * (x * uniformProbability (avoiding event F)) := by
        calc
          ∑ j ∈ N, uniformProbability (event j ∩ avoiding event F)
              ≤ ∑ _j ∈ N, x * uniformProbability (avoiding event F) := by
            gcongr with j hjN
            by_cases hNempty : N = ∅
            · simp [hNempty] at hjN
            · apply ih F.card
              · have hNpos : 0 < N.card := Finset.card_pos.mpr (by
                  simpa [Finset.nonempty_iff_ne_empty] using hNempty)
                have hFS : F.card < S.card := by
                  calc
                    F.card < N.card + F.card := by omega
                    _ = (N ∪ F).card := (Finset.card_union_of_disjoint hNFdisj).symm
                    _ = S.card := congrArg Finset.card hNF.symm
                omega
              · rfl
              · intro hjF
                exact Finset.disjoint_left.mp hNFdisj hjN hjF
          _ = (N.card : ℝ) * (x * uniformProbability (avoiding event F)) := by
            simp
      have hNcast : (N.card : ℝ) ≤ D := by exact_mod_cast hN_degree
      have hfar_nonneg : 0 ≤ uniformProbability (avoiding event F) :=
        uniformProbability_nonneg _
      have hdenom : (1 - (D : ℝ) * x) * uniformProbability (avoiding event F) ≤
          uniformProbability (avoiding event S) := by
        have hsum' : ∑ j ∈ N, uniformProbability (event j ∩ avoiding event F) ≤
            (D : ℝ) * x * uniformProbability (avoiding event F) := by
          calc
            _ ≤ (N.card : ℝ) * (x * uniformProbability (avoiding event F)) := hsum
            _ ≤ (D : ℝ) * (x * uniformProbability (avoiding event F)) := by
              gcongr
            _ = (D : ℝ) * x * uniformProbability (avoiding event F) := by ring
        nlinarith
      calc
        uniformProbability (event i ∩ avoiding event S)
            ≤ p * uniformProbability (avoiding event F) := hnum
        _ ≤ (x * (1 - (D : ℝ) * x)) * uniformProbability (avoiding event F) := by
          gcongr
        _ = x * ((1 - (D : ℝ) * x) * uniformProbability (avoiding event F)) := by ring
        _ ≤ x * uniformProbability (avoiding event S) :=
          mul_le_mul_of_nonneg_left hdenom hx.le

  have havoid_pos : ∀ S : Finset ι, 0 < uniformProbability (avoiding event S) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      rw [avoiding_empty, uniformProbability_univ]
      norm_num
    | @insert i S hi ih =>
      have hpart := avoiding_partition event i S
      have hcardpart : uniformProbability (avoiding event S) =
          uniformProbability (avoiding event (insert i S)) +
            uniformProbability (event i ∩ avoiding event S) := by
        calc
          uniformProbability (avoiding event S) =
              uniformProbability
                (avoiding event (insert i S) ∪ (event i ∩ avoiding event S)) :=
            congrArg uniformProbability hpart
          _ = uniformProbability (avoiding event (insert i S)) +
                uniformProbability (event i ∩ avoiding event S) := by
            unfold uniformProbability
            rw [Finset.card_union_of_disjoint]
            · push_cast
              ring
            · rw [Finset.disjoint_left]
              intro ω hωavoid hωevent
              rw [avoiding_insert] at hωavoid
              have hωi : ω ∉ event i := (Finset.mem_sdiff.mp hωavoid).2
              exact hωi (Finset.mem_inter.mp hωevent).1
      have hc := conditional S i hi
      have hfactor : 0 < 1 - x := sub_pos.mpr hx1
      nlinarith
  have hall := havoid_pos (Finset.univ : Finset ι)
  have hnonempty : (avoiding event (Finset.univ : Finset ι)).Nonempty :=
    (uniformProbability_pos_iff_nonempty _).mp hall
  obtain ⟨ω, hω⟩ := hnonempty
  refine ⟨ω, fun i ↦ ?_⟩
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  exact hω i trivial

/-- The convenient `4 p D ≤ 1` symmetric local lemma, for positive `D`. -/
theorem exists_avoiding_of_four_mul
    (event : ι → Finset Ω) (dep : ι → ι → Prop) [DecidableRel dep]
    (p : ℝ) (D : ℕ)
    (hp : 0 ≤ p)
    (h_event : ∀ i, uniformProbability (event i) ≤ p)
    (h_degree : ∀ i, ((Finset.univ.erase i).filter (dep i)).card ≤ D)
    (h_indep : ∀ i S, (∀ j ∈ S, ¬ dep i j) →
      uniformProbability (event i ∩ avoiding event S) =
        uniformProbability (event i) * uniformProbability (avoiding event S))
    (hD : 0 < D)
    (h_four : 4 * p * (D : ℝ) ≤ 1) :
    ∃ ω : Ω, ∀ i, ω ∉ event i := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  let x : ℝ := 1 / (2 * (D : ℝ))
  have hx : 0 < x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
    rw [div_lt_one (by positivity)]
    nlinarith
  have hDx : (D : ℝ) * x ≤ 1 := by
    dsimp [x]
    field_simp
    nlinarith
  have hpx : p ≤ x * (1 - (D : ℝ) * x) := by
    dsimp [x]
    field_simp
    nlinarith
  exact exists_avoiding_of_aux event dep p x D hp hx hx1 hDx hpx
    h_event h_degree h_indep

end GeneralLocalLemma

end LocalLemma
end Erdos136

#print axioms Erdos136.LocalLemma.exists_avoiding_of_four_mul
