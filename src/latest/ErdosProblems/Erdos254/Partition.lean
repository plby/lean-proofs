/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.BlockSums
import ErdosProblems.Erdos254.Deletion
import ErdosProblems.Erdos254.ExceptionalPhases

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- The key partition step of Fan's Theorem 4.1. Reserve four elements per
block while retaining divergence at every nonzero phase. -/
theorem reserve_four_per_block (F : ℕ → Finset ℕ)
    (hF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (hcard : ∀ k, 6 ≤ (F k).card)
    (c : ℕ → ℕ) (hc : ∀ k, c k ∈ F k)
    (hunbounded : ∀ M, ∃ k, M < c k) {L : ℝ} (hL : 1 < L)
    (hratio : ∀ k, (c (k + 1) : ℝ) ≤ L * c k)
    (hdiv : PhaseDivergent (blockUnion F)) :
    ∃ D : ℕ → Finset ℕ,
      (∀ k, D k ⊆ F k ∧ (D k).card = 4 ∧ c k ∉ D k) ∧
      PhaseDivergent (blockUnion F \ blockUnion D) := by
  classical
  let X : ℕ → Finset ℕ := fun k ↦ (F k).erase (c k)
  have hXcard : ∀ k, 5 ≤ (X k).card := by
    intro k
    dsimp [X]
    rw [Finset.card_erase_of_mem (hc k)]
    have := hcard k
    omega
  have hXsub : ∀ k, X k ⊆ F k := fun k ↦ Finset.erase_subset _ _
  let H : Set UnitAddCircle := {θ | Summable (fun k ↦ ‖c k • θ‖) ∧ θ ≠ 0}
  have hH : H.Countable := (countable_summable_circle_phases hunbounded hL hratio).mono
    (fun _ h ↦ h.1)
  let : Countable H := hH.to_subtype
  let f : H → ℕ → ℝ := fun θ a ↦ ‖a • (θ : UnitAddCircle)‖
  have hsumX : ∀ θ : H, ¬ Summable (fun k ↦ ∑ x ∈ X k, f θ x) := by
    intro θ hs
    have hsF : Summable (fun k ↦ ∑ x ∈ F k, f θ x) := by
      apply (hs.add θ.2.1).congr
      intro k
      exact Finset.sum_erase_add _ _ (hc k)
    exact hdiv θ θ.2.2 ((summable_blockUnion_iff F hF (f θ) (fun _ ↦ norm_nonneg _)).mpr hsF)
  have hweighted : ∀ θ : H, ¬ Summable (fun k ↦
      (((X k).card - 4 : ℕ) : ℝ) / (X k).card * ∑ x ∈ X k, f θ x) := by
    intro θ hs
    apply hsumX θ
    apply (hs.mul_left 5).of_nonneg_of_le (fun k ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
    intro k
    have hq : (5 : ℝ) ≤ (X k).card := by exact_mod_cast hXcard k
    have hqpos : (0 : ℝ) < (X k).card := by linarith
    have hfour : 4 ≤ (X k).card := by have := hXcard k; omega
    have hfac : (1 : ℝ) ≤ 5 * (((X k).card - 4 : ℕ) : ℝ) / (X k).card := by
      rw [Nat.cast_sub hfour, Nat.cast_ofNat, le_div_iff₀ hqpos]
      linarith
    have hnon : 0 ≤ ∑ x ∈ X k, f θ x := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    have h := mul_le_mul_of_nonneg_right hfac hnon
    simpa only [one_mul, mul_div_assoc, mul_assoc] using h
  obtain ⟨D, hD, hDdiv⟩ := deletion_lemma_countable X (fun _ ↦ 4)
    (fun k ↦ by have := hXcard k; omega) f (fun _ _ ↦ norm_nonneg _) hweighted
  have hDsub : ∀ k, D k ⊆ F k := fun k ↦ (hD k).1.trans (hXsub k)
  have hcD : ∀ k, c k ∉ D k := fun k h ↦ (Finset.mem_erase.mp ((hD k).1 h)).1 rfl
  refine ⟨D, fun k ↦ ⟨hDsub k, (hD k).2, hcD k⟩, ?_⟩
  let C := blockUnion F \ blockUnion D
  have hcC : ∀ k, c k ∈ C := by
    intro k
    refine ⟨⟨k, hc k⟩, ?_⟩
    rintro ⟨j, hj⟩
    by_cases heq : j = k
    · subst j
      exact hcD k hj
    · exact Finset.disjoint_left.mp (hF heq) (hDsub j hj) (hc k)
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hF hne) (hc i) (hij.symm ▸ hc j)
  intro θ hθ hsC
  by_cases hex : Summable (fun k ↦ ‖c k • θ‖)
  · let θH : H := ⟨θ, hex, hθ⟩
    let R : ℕ → Finset ℕ := fun k ↦ X k \ D k
    have hRsub : ∀ k, R k ⊆ F k := fun k ↦ Finset.sdiff_subset.trans (hXsub k)
    have hRpair : Pairwise (fun i j ↦ Disjoint (R i) (R j)) :=
      fun i j hij ↦ (hF hij).mono (hRsub i) (hRsub j)
    have hRC : blockUnion R ⊆ C := by
      rintro x ⟨k, hk⟩
      refine ⟨⟨k, hRsub k hk⟩, ?_⟩
      rintro ⟨j, hj⟩
      by_cases heq : k = j
      · subst j
        exact (Finset.mem_sdiff.mp hk).2 hj
      · exact Finset.disjoint_left.mp (hF heq) (hRsub k hk) (hDsub j hj)
    have hsR : Summable (fun a : blockUnion R ↦ ‖(a : ℕ) • θ‖) :=
      summable_on_subset (f := fun x ↦ ‖x • θ‖) hRC hsC
    exact hDdiv θH ((summable_blockUnion_iff R hRpair (fun x ↦ ‖x • θ‖)
      (fun _ ↦ norm_nonneg _)).mp hsR)
  · have hi : Function.Injective (fun k ↦ (⟨c k, hcC k⟩ : C)) := by
      intro i j h
      exact hcinj (congrArg (fun x : C ↦ (x : ℕ)) h)
    exact hex (Summable.comp_injective (f := fun a : C ↦ ‖(a : ℕ) • θ‖)
      (i := fun k ↦ (⟨c k, hcC k⟩ : C)) hsC hi)

/-- The two reserved components in Fan's partition, with the divergence
condition on the complement. -/
structure BlockPartition (F : ℕ → Finset ℕ) where
  left : ℕ → Finset ℕ
  right : ℕ → Finset ℕ
  left_subset : ∀ k, left k ⊆ F k
  right_subset : ∀ k, right k ⊆ F k
  left_card : ∀ k, (left k).card = 2
  right_card : ∀ k, (right k).card = 2
  disjoint : ∀ k, Disjoint (left k) (right k)
  divergent : PhaseDivergent (blockUnion F \ (blockUnion left ∪ blockUnion right))

/-- Split the four reserved elements into two disjoint pairs in every block. -/
theorem exists_blockPartition (F : ℕ → Finset ℕ)
    (hF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (hcard : ∀ k, 6 ≤ (F k).card)
    (c : ℕ → ℕ) (hc : ∀ k, c k ∈ F k)
    (hunbounded : ∀ M, ∃ k, M < c k) {L : ℝ} (hL : 1 < L)
    (hratio : ∀ k, (c (k + 1) : ℝ) ≤ L * c k)
    (hdiv : PhaseDivergent (blockUnion F)) : Nonempty (BlockPartition F) := by
  classical
  obtain ⟨D, hD, hdivD⟩ := reserve_four_per_block F hF hcard c hc hunbounded hL hratio hdiv
  choose P hP hPcard using fun k ↦
    Finset.exists_subset_card_eq (s := D k) (n := 2) (by rw [(hD k).2.1]; omega)
  let Q : ℕ → Finset ℕ := fun k ↦ D k \ P k
  have hunion : blockUnion P ∪ blockUnion Q = blockUnion D := by
    ext a
    constructor
    · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
      · exact ⟨k, hP k hk⟩
      · exact ⟨k, Finset.sdiff_subset hk⟩
    · rintro ⟨k, hk⟩
      by_cases hp : a ∈ P k
      · exact Or.inl ⟨k, hp⟩
      · exact Or.inr ⟨k, Finset.mem_sdiff.mpr ⟨hk, hp⟩⟩
  refine ⟨{
    left := P
    right := Q
    left_subset := fun k ↦ (hP k).trans (hD k).1
    right_subset := fun k ↦ Finset.sdiff_subset.trans (hD k).1
    left_card := hPcard
    right_card := ?_
    disjoint := fun k ↦ Finset.disjoint_left.mpr
      (fun _ hx hy ↦ (Finset.mem_sdiff.mp hy).2 hx)
    divergent := ?_ }⟩
  · intro k
    dsimp [Q]
    rw [Finset.card_sdiff_of_subset (hP k), (hD k).2.1, hPcard k]
  · simpa only [hunion] using hdivD

lemma BlockPartition.remainder_card {F : ℕ → Finset ℕ} (P : BlockPartition F)
    (hcard : ∀ k, 6 ≤ (F k).card) (k : ℕ) :
    2 ≤ (F k \ (P.left k ∪ P.right k)).card := by
  rw [Finset.card_sdiff_of_subset (Finset.union_subset (P.left_subset k) (P.right_subset k)),
    Finset.card_union_of_disjoint (P.disjoint k), P.left_card, P.right_card]
  have := hcard k
  omega

end Erdos254
