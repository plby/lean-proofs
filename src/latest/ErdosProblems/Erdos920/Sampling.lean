import ErdosProblems.Erdos920.Averaging

/-!
# Bernoulli sampling and deletion for Erdős Problem 920

The probability space in this file is the powerset of the finite vertex set,
weighted by `bernoulliMass`.  We choose a sample for which

`|W| - #{independent m-sets contained in W}`

is at least its expectation, delete one vertex from every surviving
independent set, and compare the resulting graph with the defining Ramsey
property.
-/

open scoped BigOperators

namespace Erdos920

open Erdos202.ParkPham

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite weighted average cannot be smaller than every value in its
support when the nonnegative weights have total mass one. -/
lemma exists_ge_of_bernoulli_average_ge (X : Finset V) {p a : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset V → ℝ)
    (havg : a ≤ ∑ W ∈ X.powerset, bernoulliMass X W p * F W) :
    ∃ W ∈ X.powerset, a ≤ F W := by
  by_contra hnone
  push_neg at hnone
  have hsum_lt :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) <
        ∑ W ∈ X.powerset, bernoulliMass X W p * a := by
    apply Finset.sum_lt_sum
    · intro W hW
      exact mul_le_mul_of_nonneg_left (le_of_lt (hnone W hW))
        (bernoulliMass_nonneg hp0 hp1)
    · have hone : (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := by
        symm
        exact sum_bernoulliMass_eq_one X (by ring)
      have hposmass : ∃ W ∈ X.powerset, 0 < bernoulliMass X W p := by
        by_contra hz
        push_neg at hz
        have hallzero : ∀ W ∈ X.powerset, bernoulliMass X W p = 0 := by
          intro W hW
          exact le_antisymm (hz W hW) (bernoulliMass_nonneg hp0 hp1)
        have : (1 : ℝ) = 0 := by
          calc
            (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := hone
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro W hW
              exact hallzero W hW
        norm_num at this
      rcases hposmass with ⟨W, hW, hmass⟩
      refine ⟨W, hW, ?_⟩
      exact mul_lt_mul_of_pos_left (hnone W hW) hmass
  have hconst :
      (∑ W ∈ X.powerset, bernoulliMass X W p * a) = a := by
    rw [← Finset.sum_mul, sum_bernoulliMass_eq_one X (by ring), one_mul]
  linarith

/-- Independent sets in an induced graph inject into the independent sets of
the original graph which are contained in the inducing set. -/
lemma card_indepSetFinset_induce_le_surviving
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (m : ℕ) :
    ((G.induce (W : Set V)).indepSetFinset m).card ≤
      ((G.indepSetFinset m).filter (fun T => T ⊆ W)).card := by
  classical
  let e : {x // x ∈ (W : Set V)} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let f : Finset {x // x ∈ (W : Set V)} → Finset V := fun T => T.map e
  apply Finset.card_le_card_of_injOn f
  · intro T hT
    have hTi : (G.induce (W : Set V)).IsNIndepSet m T :=
      SimpleGraph.mem_indepSetFinset_iff.mp hT
    have hmap : G.IsNIndepSet m (f T) := by
      have hTi' :
          (((⊤ : SimpleGraph.Subgraph G).induce (W : Set V)).coe).IsNIndepSet m T := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact hTi
      simpa [f, e] using
        (SimpleGraph.isNIndepSet_induce (G := G) (F := (W : Set V))
          (s := T) (n := m)).mp hTi'
    have hsub : f T ⊆ W := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
      exact x.property
    exact Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_indepSetFinset_iff.mpr hmap, hsub⟩
  · exact (Finset.mapEmbedding e).injective.injOn

/-- If a graph on a finite type avoids both forbidden configurations, its
number of vertices is strictly below the Ramsey number. -/
lemma card_lt_ramseyNumber_of_cliqueFree_indepSetFree
    {U : Type*} [Fintype U] (G : SimpleGraph U) {s m : ℕ}
    (hcf : G.CliqueFree s) (hif : G.IndepSetFree m) :
    Fintype.card U < Ramsey.ramseyNumber s m := by
  by_contra hn
  have hR : Ramsey.ramseyNumber s m ≤ Fintype.card U := Nat.le_of_not_gt hn
  have hprop : Ramsey.RamseyProperty s m (Fintype.card U) :=
    Ramsey.ramseyProperty_of_ramseyNumber_le hR
  exact Ramsey.ramseyProperty_of_card rfl hprop G ⟨hcf, hif⟩

/-- Bernoulli sampling followed by one-vertex-per-independent-set deletion.

The non-strict hypothesis on the expected number of surviving independent
sets yields a strict conclusion because the cleaned graph has an integral
number of vertices strictly below the Ramsey number. -/
theorem sampling_deletion_ramsey_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] {s m : ℕ}
    (hm : 1 ≤ m) (hcf : G.CliqueFree s) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcount : p ^ m * (G.indepSetFinset m).card ≤ 1) :
    p * Fintype.card V - 1 < (Ramsey.ramseyNumber s m : ℝ) := by
  classical
  let X : Finset V := Finset.univ
  let A : Finset (Finset V) := G.indepSetFinset m
  let Y : Finset V → ℝ := fun W =>
    (W.card : ℝ) - ((A.filter (fun T => T ⊆ W)).card : ℝ)
  have hAX : ∀ T ∈ A, T ⊆ X := by
    intro T hT
    exact Finset.subset_univ T
  have hAcard : ∀ T ∈ A, T.card = m := by
    intro T hT
    exact (SimpleGraph.mem_indepSetFinset_iff.mp hT).card_eq
  have havg_eq :
      (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        p * Fintype.card V - p ^ m * A.card := by
    rw [show (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) -
        ∑ W ∈ X.powerset,
          bernoulliMass X W p * ((A.filter (fun T => T ⊆ W)).card : ℝ) by
      simp only [Y, mul_sub, Finset.sum_sub_distrib]]
    rw [sum_bernoulliMass_card X hp0 hp1,
      sum_bernoulliMass_contained_count X A hAX hAcard hp0 hp1]
    simp [X]
  have havg :
      p * Fintype.card V - 1 ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * Y W := by
    rw [havg_eq]
    have : p ^ m * A.card ≤ 1 := by simpa [A] using hcount
    linarith
  obtain ⟨W, hWX, hWY⟩ :=
    exists_ge_of_bernoulli_average_ge X hp0 hp1 Y havg
  let GW : SimpleGraph {x // x ∈ (W : Set V)} := G.induce (W : Set V)
  have hGWcf : GW.CliqueFree s :=
    hcf.comap (SimpleGraph.Embedding.induce (G := G) (s := (W : Set V))).isContained
  obtain ⟨U, hUcard, hUfree⟩ :=
    exists_induced_indepSetFree_subgraph (G := GW) hm
  let GU : SimpleGraph {x // x ∈ (U : Set {x // x ∈ (W : Set V)})} :=
    GW.induce (U : Set {x // x ∈ (W : Set V)})
  have hGUcf : GU.CliqueFree s :=
    hGWcf.comap (SimpleGraph.Embedding.induce (G := GW)
      (s := (U : Set {x // x ∈ (W : Set V)}))).isContained
  have hUramsey : U.card < Ramsey.ramseyNumber s m := by
    have hcardU : Fintype.card {x // x ∈ (U : Set {x // x ∈ (W : Set V)})} = U.card := by
      simp
    rw [← hcardU]
    exact card_lt_ramseyNumber_of_cliqueFree_indepSetFree GU hGUcf hUfree
  have hinduce_le : (GW.indepSetFinset m).card ≤
      (A.filter (fun T => T ⊆ W)).card := by
    simpa [GW, A] using card_indepSetFinset_induce_le_surviving G W m
  have hnat : W.card - (A.filter (fun T => T ⊆ W)).card ≤ U.card := by
    have hUcard' : W.card - (GW.indepSetFinset m).card ≤ U.card := by
      simpa using hUcard
    exact (Nat.sub_le_sub_left hinduce_le W.card).trans hUcard'
  have hreal : Y W ≤ (U.card : ℝ) := by
    by_cases hsurv_le : (A.filter (fun T => T ⊆ W)).card ≤ W.card
    · rw [show Y W =
          ((W.card - (A.filter (fun T => T ⊆ W)).card : ℕ) : ℝ) by
        simp only [Y]
        exact (Nat.cast_sub hsurv_le).symm]
      exact_mod_cast hnat
    · have hYnonpos : Y W ≤ 0 := by
        simp only [Y]
        exact sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_not_ge hsurv_le))
      exact hYnonpos.trans (Nat.cast_nonneg U.card)
  exact lt_of_le_of_lt (hWY.trans hreal) (by exact_mod_cast hUramsey)

end

end Erdos920
