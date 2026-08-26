import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Removing the few low-degree vertices of an almost regular graph

The estimates here turn an average-degree bound together with a maximum-degree
bound into a nonempty induced subgraph with large minimum degree. All constants
and hypotheses are explicit.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An upper degree bound and a stronger upper bound on `Z` control the size
of `Z` through the deficit of the total degree. -/
theorem degree_deficit_bound [DecidableEq V] (S Z : Finset V) (hZS : Z ⊆ S)
    (b c : ℝ) (hZ : ∀ v ∈ Z, (degreeIn G S v : ℝ) ≤ c)
    (hrest : ∀ v ∈ S \ Z, (degreeIn G S v : ℝ) ≤ b) :
    (b - c) * Z.card ≤ b * S.card - degreeMass G S := by
  have hdis : Disjoint Z (S \ Z) := by
    apply Finset.disjoint_left.mpr
    intro v hvz hvr
    exact (Finset.mem_sdiff.mp hvr).2 hvz
  have hunion : Z ∪ (S \ Z) = S := Finset.union_sdiff_of_subset hZS
  have hsplit : degreeMass G S = (∑ v ∈ Z, (degreeIn G S v : ℝ)) +
      ∑ v ∈ S \ Z, (degreeIn G S v : ℝ) := by
    rw [← Finset.sum_union hdis, hunion]
    rfl
  have hZsum : (∑ v ∈ Z, (degreeIn G S v : ℝ)) ≤ c * Z.card := by
    calc
      (∑ v ∈ Z, (degreeIn G S v : ℝ)) ≤ ∑ _v ∈ Z, c :=
        Finset.sum_le_sum hZ
      _ = c * Z.card := by simp [mul_comm]
  have hRsum : (∑ v ∈ S \ Z, (degreeIn G S v : ℝ)) ≤ b * (S \ Z).card := by
    calc
      (∑ v ∈ S \ Z, (degreeIn G S v : ℝ)) ≤ ∑ _v ∈ S \ Z, b :=
        Finset.sum_le_sum hrest
      _ = b * (S \ Z).card := by simp [mul_comm]
  have hcard : ((S \ Z).card : ℝ) + Z.card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hZS
  rw [← hcard]
  nlinarith

/-- The degree-cleaning lemma used after removing the exceptional high-degree
vertices. It returns an actual nonempty induced core. -/
theorem exists_near_regular_core (S : Finset V) (m a ε : ℝ)
    (hS : S.Nonempty) (hm : 0 < m) (hsize : (S.card : ℝ) ≤ 2 * m)
    (ha : 0 ≤ a) (hε : 0 < ε) (hε_small : ε ≤ 1)
    (ha_small : a ≤ ε ^ 2 / 1000)
    (hmass : (1 - 8 * a) * m * S.card ≤ degreeMass G S)
    (hmax : ∀ v ∈ S, (degreeIn G S v : ℝ) ≤ (1 + a) * m) :
    ∃ Q ⊆ S, Q.Nonempty ∧ ∀ v ∈ Q, (1 - ε) * m ≤ (degreeIn G Q v : ℝ) := by
  classical
  let Z := S.filter fun v ↦ (degreeIn G S v : ℝ) < (1 - ε / 2) * m
  have hZS : Z ⊆ S := Finset.filter_subset _ _
  have hdef := degree_deficit_bound G S Z hZS ((1 + a) * m) ((1 - ε / 2) * m)
    (by
      intro v hv
      exact (Finset.mem_filter.mp hv).2.le)
    (by
      intro v hv
      exact hmax v (Finset.mem_sdiff.mp hv).1)
  have hcount : ε * (Z.card : ℝ) ≤ 18 * a * S.card := by
    have hzero : 0 ≤ a * m * (Z.card : ℝ) := by positivity
    refine le_of_mul_le_mul_left (a := m) ?_ hm
    nlinarith only [hdef, hmass, hzero]
  have hε_square : ε ^ 2 ≤ ε := by
    have hprod := mul_nonneg hε.le (sub_nonneg.mpr hε_small)
    nlinarith
  have hsmall : 18 * a < ε := by nlinarith
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hZlt : Z.card < S.card := by
    have hlt := mul_lt_mul_of_pos_right hsmall hSpos
    have hreal : (Z.card : ℝ) < S.card := lt_of_mul_lt_mul_left
      (hcount.trans_lt (by nlinarith only [hlt])) hε.le
    exact_mod_cast hreal
  have hZbound : (Z.card : ℝ) ≤ ε * m / 2 := by
    have hsize_mul := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 18 * a by positivity)
    have ha_sq : 36 * a ≤ ε ^ 2 / 2 := by nlinarith [sq_nonneg ε]
    have ha_mul := mul_le_mul_of_nonneg_right ha_sq hm.le
    refine le_of_mul_le_mul_left (a := ε) ?_ hε
    nlinarith only [hcount, hsize_mul, ha_mul]
  let Q := S \ Z
  have hQS : Q ⊆ S := Finset.sdiff_subset
  have hQpos : Q.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [Q]
    rw [Finset.card_sdiff_of_subset hZS]
    omega
  have hremoved : S \ Q = Z := Finset.sdiff_sdiff_eq_self hZS
  refine ⟨Q, hQS, hQpos, ?_⟩
  intro v hv
  obtain ⟨hvs, hvz⟩ := Finset.mem_sdiff.mp hv
  have hdegree : (1 - ε / 2) * m ≤ (degreeIn G S v : ℝ) := by
    apply le_of_not_gt
    intro hlow
    exact hvz (Finset.mem_filter.mpr ⟨hvs, hlow⟩)
  have hdrop : (degreeIn G S v : ℝ) ≤ degreeIn G Q v + (Z.card : ℝ) := by
    have h := degreeIn_le_add_removed G S Q v
    rw [hremoved] at h
    exact_mod_cast h
  nlinarith

end Erdos547

#print axioms Erdos547.degree_deficit_bound
#print axioms Erdos547.exists_near_regular_core
