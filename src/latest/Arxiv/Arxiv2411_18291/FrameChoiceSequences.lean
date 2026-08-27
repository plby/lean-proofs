import Arxiv.Arxiv2411_18291.FiniteChoiceSequences
import Arxiv.Arxiv2411_18291.RootedCliqueAvoidance

/-!
# Counting compatible choices for the near frame

At each stage, choose a rooted clique whose nonroot vertices avoid the base
and all preceding cliques. A uniform collision budget leaves at least half
the rooted-clique choices at every stage, giving a product lower bound.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {a q : ℕ}

def historyVertices (xs : List (Block V q)) : Finset V := xs.toFinset.biUnion Subtype.val

theorem mem_historyVertices (xs : List (Block V q)) (v : V) :
    v ∈ historyVertices xs ↔ ∃ Q ∈ xs, v ∈ Q.val := by
  simp only [historyVertices, mem_biUnion, List.mem_toFinset]

theorem historyVertices_cons (Q : Block V q) (xs : List (Block V q)) :
    historyVertices (Q :: xs) = Q.val ∪ historyVertices xs := by
  simp only [historyVertices, List.toFinset_cons, biUnion_insert]

theorem historyVertices_card_le (xs : List (Block V q)) :
    (historyVertices xs).card ≤ xs.length * q := by
  have hc (Q : Block V q) : Q.val.card = q := Q.property
  calc
    _ ≤ ∑ Q ∈ xs.toFinset, Q.val.card := card_biUnion_le
    _ = xs.toFinset.card * q := by simp only [hc, sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right q xs.toFinset_card_le

def frameChoices (B : Finset V) (e : ℕ → Block V a) (D : ℕ → Finset (Block V q))
    (n : ℕ) (xs : List (Block V q)) : Finset (Block V q) :=
  avoidingRootedCliques (D n) (e n) (B ∪ historyVertices xs)

def frameChoiceSequences (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (t : ℕ) : Finset (List (Block V q)) :=
  choiceSequences (frameChoices B e D) t

theorem frameChoiceSequences_card_lower [Fintype V] (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (t : ℕ) (haq : a < q)
    (hD : ∀ i < t, ∀ Q ∈ D i, (e i).val ⊆ Q.val) {L : ℝ} (hL : 0 ≤ L)
    (hsize : ∀ i < t, L ≤ (D i).card)
    (hsmall : ((B.card + t * q : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (q - a - 1) ≤ L / 2) :
    (L / 2) ^ t ≤ (frameChoiceSequences B e D t).card := by
  apply choiceSequences_card_lower _ t (div_nonneg hL (by norm_num))
  intro i hi xs hxs
  have hlen := choiceSequences_length _ hxs
  have hU : (B ∪ historyVertices xs).card ≤ B.card + t * q := by
    calc
      _ ≤ B.card + (historyVertices xs).card := card_union_le _ _
      _ ≤ B.card + xs.length * q := Nat.add_le_add le_rfl (historyVertices_card_le xs)
      _ ≤ _ := Nat.add_le_add le_rfl (Nat.mul_le_mul_right q (by rw [hlen]; exact hi.le))
  have hUR : ((B ∪ historyVertices xs).card : ℝ) ≤ ((B.card + t * q : ℕ) : ℝ) := by
    exact_mod_cast hU
  exact avoidingRootedCliques_card_half (D i) (e i) haq (hD i hi) _ (hsize i hi)
    ((mul_le_mul_of_nonneg_right hUR (by positivity)).trans hsmall)

theorem frameChoices_inter_base (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (i : ℕ) (xs : List (Block V q))
    (heB : (e i).val ⊆ B) (hD : ∀ Q ∈ D i, (e i).val ⊆ Q.val)
    {Q : Block V q} (hQ : Q ∈ frameChoices B e D i xs) : Q.val ∩ B = (e i).val := by
  obtain ⟨hQD, hd⟩ := mem_filter.mp hQ
  apply Subset.antisymm
  · intro v hv
    by_contra hve
    exact disjoint_left.mp hd (mem_sdiff.mpr ⟨(mem_inter.mp hv).1, hve⟩)
      (mem_union_left _ (mem_inter.mp hv).2)
  · exact subset_inter (hD Q hQD) heB

theorem frameChoices_private_disjoint (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (i : ℕ) (xs : List (Block V q))
    (heB : (e i).val ⊆ B) {Q : Block V q} (hQ : Q ∈ frameChoices B e D i xs)
    {P : Block V q} (hP : P ∈ xs) : Disjoint (Q.val \ B) (P.val \ B) := by
  have hd := (mem_filter.mp hQ).2
  apply disjoint_left.mpr
  intro v hvQ hvP
  exact disjoint_left.mp hd
    (mem_sdiff.mpr ⟨(mem_sdiff.mp hvQ).1, fun h => (mem_sdiff.mp hvQ).2 (heB h)⟩)
    (mem_union_right _ ((mem_historyVertices xs v).mpr ⟨P, hP, (mem_sdiff.mp hvP).1⟩))

theorem frameChoiceSequences_private_pairwise (B : Finset V) (e : ℕ → Block V a)
    (D : ℕ → Finset (Block V q)) (heB : ∀ i, (e i).val ⊆ B) {t : ℕ}
    {xs : List (Block V q)} (hxs : xs ∈ frameChoiceSequences B e D t) :
    xs.Pairwise (fun P Q => Disjoint (P.val \ B) (Q.val \ B)) := by
  induction t generalizing xs with
  | zero =>
      have hnil : xs = [] := mem_singleton.mp hxs
      rw [hnil]
      exact List.Pairwise.nil
  | succ t ih =>
      obtain ⟨ys, hys, Q, hQ, rfl⟩ := (mem_choiceSequences_succ _ t xs).mp hxs
      apply List.pairwise_cons.mpr
      exact ⟨fun P hP => frameChoices_private_disjoint B e D t ys (heB t) hQ hP, ih hys⟩

end Arxiv2411_18291
