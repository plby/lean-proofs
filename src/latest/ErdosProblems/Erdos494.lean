/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 494.
https://www.erdosproblems.com/forum/thread/494

Informal authors:
- Basil Gordon
- Aviezri S. Fraenkel
- Ernst G. Straus

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos494.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/494.lean
-/
import Mathlib

/-!
# Erdős Problem 494

For a finite set `A ⊆ ℂ`, `sumMultiset A k` is the multiset of sums of
the `k`-element subsets of `A`.
-/

open Filter
open scoped BigOperators

namespace Erdos494

noncomputable section

/-- The multiset of sums of the `k`-element subsets of `A`. -/
def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

/-- Uniqueness of a finite complex set of a prescribed cardinality from its
`k`-sum multiset. -/
def Erdos494Unique (k : ℕ) (card : ℕ) : Prop :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card →
    sumMultiset A k = sumMultiset B k → A = B

private def negEmbedding : ℂ ↪ ℂ where
  toFun z := -z
  inj' := neg_injective

@[simp]
lemma sumMultiset_map_neg (A : Finset ℂ) (k : ℕ) :
    sumMultiset (A.map negEmbedding) k = (sumMultiset A k).map (-·) := by
  unfold sumMultiset
  rw [Finset.powersetCard_map, Finset.map_val]
  simp only [Multiset.map_map, Function.comp_apply]
  congr 1
  funext I
  simpa [negEmbedding] using
    (Finset.sum_neg_distrib (s := I) (fun z : ℂ => z))

lemma powersetCard_map_compl_val (A : Finset ℂ) (k : ℕ)
    (hcard : A.card = 2 * k) :
    (A.powersetCard k).val.map (fun I => A \ I) =
      (A.powersetCard k).val := by
  let P := A.powersetCard k
  have hmem (I : Finset ℂ) : I ∈ P → A \ I ∈ P := by
    intro hI
    have hsub : I ⊆ A := (Finset.mem_powersetCard.mp hI).1
    have hIcard : I.card = k := (Finset.mem_powersetCard.mp hI).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.sdiff_subset
    · rw [Finset.card_sdiff_of_subset hsub, hcard, hIcard]
      omega
  have hinj : Set.InjOn (fun I : Finset ℂ => A \ I) P := by
    intro I hI J hJ h
    have hIsub : I ⊆ A := (Finset.mem_powersetCard.mp hI).1
    have hJsub : J ⊆ A := (Finset.mem_powersetCard.mp hJ).1
    have := congrArg (fun T : Finset ℂ => A \ T) h
    simpa [Finset.sdiff_sdiff_eq_self hIsub,
      Finset.sdiff_sdiff_eq_self hJsub] using this
  have himage : P.image (fun I => A \ I) = P := by
    apply Finset.Subset.antisymm
    · intro I hI
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
      exact hmem J hJ
    · intro I hI
      have hsub : I ⊆ A := (Finset.mem_powersetCard.mp hI).1
      have hcompl : A \ I ∈ P := hmem I hI
      apply Finset.mem_image.mpr
      refine ⟨A \ I, hcompl, ?_⟩
      exact Finset.sdiff_sdiff_eq_self hsub
  rw [← Finset.image_val_of_injOn hinj, himage]

lemma sumMultiset_map_neg_eq_self_of_card_twice_of_sum_eq_zero
    (A : Finset ℂ) (k : ℕ) (hcard : A.card = 2 * k)
    (hsum : ∑ a ∈ A, a = 0) :
    sumMultiset (A.map negEmbedding) k = sumMultiset A k := by
  rw [sumMultiset_map_neg]
  unfold sumMultiset
  rw [Multiset.map_map]
  have hcompl := powersetCard_map_compl_val A k hcard
  calc
    ((A.powersetCard k).val.map fun I => -(∑ a ∈ I, a)) =
        ((A.powersetCard k).val.map fun I => ∑ a ∈ A \ I, a) := by
      refine Multiset.map_congr rfl ?_
      intro I hI
      have hsub : I ⊆ A := (Finset.mem_powersetCard.mp hI).1
      have hadd : (∑ a ∈ A \ I, a) + ∑ a ∈ I, a = 0 :=
        (Finset.sum_sdiff (f := id) hsub).trans hsum
      exact neg_eq_of_add_eq_zero_left hadd
    _ = ((A.powersetCard k).val.map fun I => ∑ a ∈ I, a) := by
      calc
        ((A.powersetCard k).val.map fun I => ∑ a ∈ A \ I, a) =
            (((A.powersetCard k).val.map fun I => A \ I).map
              fun I => ∑ a ∈ I, a) := by
          symm
          exact Multiset.map_map _ _ _
        _ = _ := congrArg (Multiset.map fun I : Finset ℂ => ∑ a ∈ I, a) hcompl

/-! ## The literal problem has a negative answer

For `k > 2` we use four real numbers `0, 1, 2, -3`, whose sum is zero,
and add `k - 2` cancelling pairs on the imaginary axis.  Negation changes
the resulting set but, because its cardinality is `2k` and its total sum is
zero, complementation identifies its `k`-sum multiset with that of its
negative.
-/

private def baseValue (i : Fin 4) : ℂ :=
  match i.1 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => -3

@[simp] private lemma baseValue_im (i : Fin 4) : (baseValue i).im = 0 := by
  fin_cases i <;> norm_num [baseValue]

private def witnessValue (m : ℕ) : Fin 4 ⊕ (Fin m × Bool) → ℂ
  | Sum.inl i => baseValue i
  | Sum.inr (j, false) => ⟨0, (j.1 + 1 : ℝ)⟩
  | Sum.inr (j, true) => ⟨0, -(j.1 + 1 : ℝ)⟩

private lemma witnessValue_injective (m : ℕ) :
    Function.Injective (witnessValue m) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          congr 1
          apply Fin.ext
          fin_cases i <;> fin_cases j
          all_goals have hre := congrArg Complex.re hxy
          all_goals norm_num [witnessValue, baseValue] at hre
          all_goals rfl
      | inr jb =>
          rcases jb with ⟨j, b⟩
          have him := congrArg Complex.im hxy
          exfalso
          have hj : (0 : ℝ) ≤ (j.1 : ℝ) := by positivity
          cases b <;> simp [witnessValue] at him <;> linarith
  | inr ib =>
      rcases ib with ⟨i, b⟩
      cases y with
      | inl j =>
          have him := congrArg Complex.im hxy
          exfalso
          have hi : (0 : ℝ) ≤ (i.1 : ℝ) := by positivity
          cases b <;> simp [witnessValue] at him <;> linarith
      | inr jc =>
          rcases jc with ⟨j, c⟩
          have him := congrArg Complex.im hxy
          cases b <;> cases c
          · congr 2
            apply Fin.ext
            simp [witnessValue] at him
            exact him
          · exfalso
            simp [witnessValue] at him
            have hi : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
            have hj : (0 : ℝ) < (j.1 : ℝ) + 1 := by positivity
            linarith
          · exfalso
            simp [witnessValue] at him
            have hi : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
            have hj : (0 : ℝ) < (j.1 : ℝ) + 1 := by positivity
            linarith
          · congr 2
            apply Fin.ext
            simp [witnessValue] at him
            exact him

private def witnessEmbedding (m : ℕ) : Fin 4 ⊕ (Fin m × Bool) ↪ ℂ :=
  ⟨witnessValue m, witnessValue_injective m⟩

private def taoWitness (k : ℕ) : Finset ℂ :=
  Finset.univ.map (witnessEmbedding (k - 2))

private lemma card_taoWitness {k : ℕ} (hk : 2 < k) :
    (taoWitness k).card = 2 * k := by
  simp [taoWitness]
  omega

private lemma sum_taoWitness (k : ℕ) :
    ∑ z ∈ taoWitness k, z = 0 := by
  rw [taoWitness, Finset.sum_map]
  change ∑ x : Fin 4 ⊕ (Fin (k - 2) × Bool), witnessValue (k - 2) x = 0
  rw [Fintype.sum_sum_type]
  have hbase : ∑ i : Fin 4, baseValue i = 0 := by
    norm_num [Fin.sum_univ_succ, baseValue]
  change (∑ i : Fin 4, baseValue i) +
      (∑ p : Fin (k - 2) × Bool, witnessValue (k - 2) (Sum.inr p)) = 0
  rw [hbase, zero_add, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i hi
  apply Complex.ext <;> simp [witnessValue]

private lemma one_mem_taoWitness (k : ℕ) : (1 : ℂ) ∈ taoWitness k := by
  rw [taoWitness, Finset.mem_map]
  exact ⟨Sum.inl 1, Finset.mem_univ _, by norm_num [witnessEmbedding, witnessValue, baseValue]⟩

private lemma neg_one_not_mem_taoWitness (k : ℕ) : (-1 : ℂ) ∉ taoWitness k := by
  rw [taoWitness, Finset.mem_map]
  rintro ⟨x, -, hx⟩
  cases x with
  | inl i =>
      fin_cases i <;>
        norm_num [witnessEmbedding, witnessValue, baseValue, Fin.ext_iff] at hx
  | inr jb =>
      rcases jb with ⟨j, b⟩
      have hre := congrArg Complex.re hx
      cases b <;> norm_num [witnessEmbedding, witnessValue] at hre

private lemma taoWitness_ne_neg (k : ℕ) :
    taoWitness k ≠ (taoWitness k).map negEmbedding := by
  intro h
  have hmem : (1 : ℂ) ∈ (taoWitness k).map negEmbedding := h ▸ one_mem_taoWitness k
  rw [Finset.mem_map] at hmem
  obtain ⟨z, hz, hneg⟩ := hmem
  have : z = -1 := by
    dsimp [negEmbedding] at hneg
    linear_combination -hneg
  exact neg_one_not_mem_taoWitness k (this ▸ hz)

/-- Tao's counterexample: at cardinality `2k`, negating a nonsymmetric
zero-sum set preserves the multiset of its `k`-element sums. -/
theorem card_eq_2k_counterexample :
    ∀ k > 2, ¬ Erdos494Unique k (2 * k) := by
  intro k hk hUnique
  let A := taoWitness k
  let B := A.map negEmbedding
  have hAcard : A.card = 2 * k := card_taoWitness hk
  have hBcard : B.card = 2 * k := by simp [B, hAcard]
  have hsums : sumMultiset A k = sumMultiset B k :=
    (sumMultiset_map_neg_eq_self_of_card_twice_of_sum_eq_zero
      A k hAcard (sum_taoWitness k)).symm
  exact taoWitness_ne_neg k (hUnique A B hAcard hBcard hsums)

namespace erdos_494.variants

/-- The exact `card = 2k` variant from the formal-conjectures specification. -/
theorem card_eq_2k : ∀ k > 2, ¬ Erdos494Unique k (2 * k) :=
  card_eq_2k_counterexample

end erdos_494.variants

end

end Erdos494
