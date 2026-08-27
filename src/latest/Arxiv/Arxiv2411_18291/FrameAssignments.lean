import Arxiv.Arxiv2411_18291.FrameChoiceSequences
import Arxiv.Arxiv2411_18291.ChoiceSequenceAssignments
import Mathlib.Data.List.Pairwise

/-!
# Many indexed assignments of near-frame cliques

The sequential choices inject into assignments indexed by the frame pieces.
Every assigned clique belongs to its prescribed rooted family, meets the
base exactly in its prescribed root, and has private vertices disjoint from
those of every other assigned clique.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {a q : ℕ}

open Classical in
def frameAssignments (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (t : ℕ) : Finset (Fin t → Block V q) :=
  univ.filter fun Q => (∀ i : Fin t, Q i ∈ D i ∧ (Q i).val ∩ B = (e i).val) ∧
    Pairwise (fun i j => Disjoint ((Q i).val \ B) ((Q j).val \ B))

theorem choiceAssignment_mem_frameAssignments (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (heB : ∀ i, (e i).val ⊆ B)
    (hD : ∀ i, ∀ Q ∈ D i, (e i).val ⊆ Q.val) (t : ℕ)
    (xs : frameChoiceSequences B e D t) :
    choiceAssignment (frameChoices B e D) t xs ∈ frameAssignments B e D t := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_, ?_⟩
  · intro i
    exact choiceAssignment_property (frameChoices B e D)
      (fun n Q => Q ∈ D n ∧ Q.val ∩ B = (e n).val)
      (fun n ys _ Q hQ => ⟨(mem_filter.mp hQ).1,
        frameChoices_inter_base B e D n ys (heB n) (hD n) hQ⟩) t xs i
  · intro i j hij
    have hp := frameChoiceSequences_private_pairwise B e D heB xs.property
    have hr := hp.reverse
    let i' : Fin xs.val.reverse.length := ⟨i.val, by
      rw [List.length_reverse, choiceSequences_length _ xs.property]
      exact i.isLt⟩
    let j' : Fin xs.val.reverse.length := ⟨j.val, by
      rw [List.length_reverse, choiceSequences_length _ xs.property]
      exact j.isLt⟩
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (hr.rel_get_of_lt (show i' < j' from hij)).symm
    · exact hr.rel_get_of_lt (show j' < i' from hji)

theorem frameChoiceSequences_card_le_assignments (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (heB : ∀ i, (e i).val ⊆ B)
    (hD : ∀ i, ∀ Q ∈ D i, (e i).val ⊆ Q.val) (t : ℕ) :
    (frameChoiceSequences B e D t).card ≤ (frameAssignments B e D t).card := by
  let f : frameChoiceSequences B e D t ↪ frameAssignments B e D t :=
    ⟨fun xs => ⟨choiceAssignment (frameChoices B e D) t xs,
      choiceAssignment_mem_frameAssignments B e D heB hD t xs⟩,
      fun xs ys hxy => choiceAssignment_injective (frameChoices B e D) t
        (congrArg Subtype.val hxy)⟩
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f f.injective

theorem frameAssignments_card_lower (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (t : ℕ) (haq : a < q)
    (heB : ∀ i, (e i).val ⊆ B) (hD : ∀ i, ∀ Q ∈ D i, (e i).val ⊆ Q.val)
    {L : ℝ} (hL : 0 ≤ L) (hsize : ∀ i < t, L ≤ (D i).card)
    (hsmall : ((B.card + t * q : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (q - a - 1) ≤ L / 2) :
    (L / 2) ^ t ≤ (frameAssignments B e D t).card := by
  have hs := frameChoiceSequences_card_lower B e D t haq (fun i _ => hD i) hL hsize hsmall
  exact hs.trans (by exact_mod_cast frameChoiceSequences_card_le_assignments B e D heB hD t)

end Arxiv2411_18291
