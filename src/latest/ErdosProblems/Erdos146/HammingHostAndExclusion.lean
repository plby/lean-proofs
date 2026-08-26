/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos146.SamplingAndHammingBalls

set_option linter.mathlibStandardSet false

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos146

attribute [local instance] Classical.propDecidable

section HammingHostAndExclusion

def hammingHost (dimension radius : ℕ) :
    SimpleGraph (Bool × HammingWord dimension) :=
  SimpleGraph.fromRel
    (fun x y => x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius)

theorem hammingHost_adj_iff (dimension radius : ℕ)
    (x y : Bool × HammingWord dimension) :
    (hammingHost dimension radius).Adj x y ↔
      x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius := by
  rw [hammingHost, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hforward | hbackward⟩
    · exact hforward
    · exact ⟨Ne.symm hbackward.1, by
        simpa [hammingDist_comm] using hbackward.2⟩
  · intro hxy
    refine ⟨?_, Or.inl hxy⟩
    intro heq
    exact hxy.1 (congrArg Prod.fst heq)

theorem hammingBall_card_ge_boundary_binomial
    (dimension radius : ℕ)
    (word : HammingWord dimension) :
    dimension.choose radius ≤ (hammingBall dimension radius word).card := by
  rw [hammingBall_card]
  apply Finset.single_le_sum
    (s := Finset.range (radius + 1))
    (f := fun distance => dimension.choose distance)
  · intro distance _
    exact Nat.zero_le _
  · simp

theorem hammingWordNeighbor_sum_const
    (dimension radius : ℕ) (left : HammingWord dimension)
    (weight : ℝ) :
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
      ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
        ∑ _right ∈ hammingBall dimension radius left, weight := by
          rw [← Finset.sum_filter]
          rfl
    _ = ((hammingBall dimension radius left).card : ℝ) * weight := by
      simp [nsmul_eq_mul]
    _ = ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
      rw [hammingBall_card]

theorem hammingWordEdge_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius then weight else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  simp_rw [hammingWordNeighbor_sum_const]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring

theorem hammingWordEdgePair_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              weight
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) ^ 2 *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            weight
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((2 ^ dimension : ℕ) : ℝ) *
            ((∑ distance ∈ Finset.range (radius + 1),
              dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hammingWordEdge_sum_const dimension radius weight
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring

theorem hammingWordEdgePairSharedLeft_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hshared (firstLeft : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
    calc
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        ∑ secondLeft : HammingWord dimension,
          if firstLeft = secondLeft then
            ∑ secondRight : HammingWord dimension,
              if hammingDist secondLeft secondRight ≤ radius then
                weight else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro secondLeft _
            by_cases hleft : firstLeft = secondLeft
            · subst secondLeft
              simp
            · simp [hleft]
      _ = ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) * weight := by
        simp [hammingWordNeighbor_sum_const]
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hshared firstLeft
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring

theorem hammingWordEdgePairSharedRight_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  calc
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      (∑ firstRight : HammingWord dimension,
        ∑ firstLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            ∑ secondLeft : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if firstRight = secondRight then weight else 0
              else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro firstRight _
        apply Finset.sum_congr rfl
        intro firstLeft _
        rw [Finset.sum_comm]
    _ = ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
      simpa only [hammingDist_comm] using
        hammingWordEdgePairSharedLeft_sum_const dimension radius weight

theorem hammingWordEdgePairIdentical_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    _ = ∑ firstLeft : HammingWord dimension,
          ∑ firstRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius then weight else 0 := by
      apply Finset.sum_congr rfl
      intro firstLeft _
      apply Finset.sum_congr rfl
      intro firstRight _
      by_cases hedge : hammingDist firstLeft firstRight ≤ radius
      · simp only [hedge, true_and, if_true]
        have hpoint (secondLeft secondRight : HammingWord dimension) :
            (if hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
              if firstLeft = secondLeft then
                if firstRight = secondRight then weight else 0
              else 0 := by
          split_ifs <;> simp_all
        simp_rw [hpoint]
        simp
      · simp [hedge]
    _ = _ := hammingWordEdge_sum_const dimension radius weight

noncomputable def hammingExpectedRetainedEdgeCount
    (dimension radius : ℕ) : ℝ :=
  ∑ left : HammingWord dimension,
    ∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then
        (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained}
      else 0

theorem hammingExpectedRetainedEdgeCount_eq
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeCount dimension radius =
      hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) := by
  classical
  have hpair (left right : HammingWord dimension) :
      (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained} =
        hammingRetentionProbability dimension ^ 2 :=
    hammingRetentionMeasure_real_contains_pair
      dimension (false, left) (true, right) (by simp)
  unfold hammingExpectedRetainedEdgeCount
  simp_rw [hpair]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    hammingWordEdge_sum_const dimension radius
      (hammingRetentionProbability dimension ^ 2)

theorem hammingExpectedRetainedEdgeCount_pos
    (dimension radius : ℕ) :
    0 < hammingExpectedRetainedEdgeCount dimension radius := by
  have hterm :
      1 ≤ ∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance := by
    have hzero := Finset.single_le_sum
      (s := Finset.range (radius + 1))
      (f := fun distance : ℕ => dimension.choose distance)
      (fun distance _ => Nat.zero_le _)
      (show 0 ∈ Finset.range (radius + 1) by simp)
    simpa using hzero
  have hdegree :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  rw [hammingExpectedRetainedEdgeCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

noncomputable def hammingExpectedRetainedEdgeSquare
    (dimension radius : ℕ) : ℝ :=
  ∑ firstLeft : HammingWord dimension,
    ∑ firstRight : HammingWord dimension,
      ∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            (hammingRetentionMeasure dimension).real
              {retained : Set (Bool × HammingWord dimension) |
                (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained}
          else 0

theorem hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧
                      firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 := by
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_le_sum
  intro firstLeft _
  apply Finset.sum_le_sum
  intro firstRight _
  apply Finset.sum_le_sum
  intro secondLeft _
  apply Finset.sum_le_sum
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    exact hammingRetentionMeasure_real_contains_edgePair_le
      dimension firstLeft firstRight secondLeft secondRight
  · simp [hedge]

theorem hammingExpectedRetainedEdgeSquare_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  classical
  have hpoint
      (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
      (if hammingDist firstLeft firstRight ≤ radius ∧
          hammingDist secondLeft secondRight ≤ radius then
        hammingRetentionProbability dimension ^ 4 +
          (if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0)
      else 0) =
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          hammingRetentionProbability dimension ^ 4 else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0
        else 0) := by
    split <;> simp
  calc
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧ firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 :=
        hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
          dimension radius
    _ = hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [hammingWordEdgePair_sum_const,
        hammingWordEdgePairSharedLeft_sum_const,
        hammingWordEdgePairSharedRight_sum_const,
        hammingWordEdgePairIdentical_sum_const,
        hammingExpectedRetainedEdgeCount_eq]
      ring

theorem hammingExpectedRetainedEdgeVariance_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  have hsecond := hammingExpectedRetainedEdgeSquare_le dimension radius
  linarith

noncomputable def retainedHammingWordEdges
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    Finset (HammingWord dimension × HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun edge =>
    hammingDist edge.1 edge.2 ≤ radius ∧
      (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained)

noncomputable def hammingRetainedEdgeCount
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact
    ∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then 1 else 0

theorem hammingRetainedEdgeCount_eq_wordEdges_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
  classical
  unfold hammingRetainedEdgeCount
  calc
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0) =
      ∑ edge : HammingWord dimension × HammingWord dimension,
        if hammingDist edge.1 edge.2 ≤ radius ∧
            (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained
        then (1 : ℝ) else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ _edge ∈ retainedHammingWordEdges dimension radius retained,
          (1 : ℝ) := by
      unfold retainedHammingWordEdges
      rw [← Finset.sum_filter]
    _ = ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
      simp

theorem hammingRetainedEdgeCount_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeCount dimension radius := by
  classical
  unfold hammingRetainedEdgeCount hammingExpectedRetainedEdgeCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun left _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ right : HammingWord dimension,
          if hammingDist left right ≤ radius ∧
              (false, left) ∈ retained ∧ (true, right) ∈ retained
          then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro left _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun right _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hedge : hammingDist left right ≤ radius
  · simp only [hedge, true_and, if_true]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, left) ∈ retained ∧ (true, right) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

open Classical in
theorem hammingRetainedEdgeCount_sq
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained ^ 2 =
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0 := by
  classical
  unfold hammingRetainedEdgeCount
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstRight _
  apply Finset.sum_congr rfl
  intro secondLeft _
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hfirst_edge : hammingDist firstLeft firstRight ≤ radius <;>
    by_cases hsecond_edge : hammingDist secondLeft secondRight ≤ radius <;>
    by_cases hfirst_left : (false, firstLeft) ∈ retained <;>
    by_cases hfirst_right : (true, firstRight) ∈ retained <;>
    by_cases hsecond_left : (false, secondLeft) ∈ retained <;>
    by_cases hsecond_right : (true, secondRight) ∈ retained <;>
    simp [hfirst_edge, hsecond_edge, hfirst_left, hfirst_right,
      hsecond_left, hsecond_right]

theorem hammingRetainedEdgeCount_sq_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius := by
  classical
  simp_rw [hammingRetainedEdgeCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0))]
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if (false, firstLeft) ∈ retained ∧
                  (true, firstRight) ∈ retained ∧
                  (false, secondLeft) ∈ retained ∧
                  (true, secondRight) ∈ retained
              then (1 : ℝ) else 0
            else 0))]
  apply Finset.sum_congr rfl
  intro firstRight _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained
            then (1 : ℝ) else 0
          else 0))]
  apply Finset.sum_congr rfl
  intro secondLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if (false, firstLeft) ∈ retained ∧
              (true, firstRight) ∈ retained ∧
              (false, secondLeft) ∈ retained ∧
              (true, secondRight) ∈ retained
          then (1 : ℝ) else 0
        else 0))]
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, firstLeft) ∈ retained ∧
          (true, firstRight) ∈ retained ∧
          (false, secondLeft) ∈ retained ∧
          (true, secondRight) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

theorem hammingRetainedEdgeCount_variance_eq
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedEdgeCount dimension radius))]
  change
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedEdgeCount dimension radius retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2
  rw [hammingRetainedEdgeCount_sq_integral_eq,
    hammingRetainedEdgeCount_integral_eq]

theorem hammingRetainedEdgeCount_variance_le
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  rw [hammingRetainedEdgeCount_variance_eq]
  exact hammingExpectedRetainedEdgeVariance_le dimension radius

theorem hammingRetainedEdgeCount_deviation_probability_le
    (dimension radius : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedEdgeCount dimension radius)
    threshold hthreshold
  rw [hammingRetainedEdgeCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      ProbabilityTheory.variance
          (hammingRetainedEdgeCount dimension radius)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedEdgeCount_variance_le dimension radius

theorem hammingRetainedEdgeCount_lower_tail_probability_le
    (dimension radius : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedEdgeCount_pos dimension radius
  have hthreshold :
      0 < hammingExpectedRetainedEdgeCount dimension radius / 2 := by
    positivity
  have hchebyshev := hammingRetainedEdgeCount_deviation_probability_le
    dimension radius
    (hammingExpectedRetainedEdgeCount dimension radius / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} := by
    intro retained hretained
    change
      hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
        |hammingRetainedEdgeCount dimension radius retained -
          hammingExpectedRetainedEdgeCount dimension radius|
    have habsolute := neg_le_abs
      (hammingRetainedEdgeCount dimension radius retained -
        hammingExpectedRetainedEdgeCount dimension radius)
    change
      hammingRetainedEdgeCount dimension radius retained <
        hammingExpectedRetainedEdgeCount dimension radius / 2 at hretained
    linarith
  have hdegree_positive :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    have hterm :
        1 ≤ ∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance := by
      have hzero := Finset.single_le_sum
        (s := Finset.range (radius + 1))
        (f := fun distance : ℕ => dimension.choose distance)
        (fun distance _ => Nat.zero_le _)
        (show 0 ∈ Finset.range (radius + 1) by simp)
      simpa using hzero
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  have hprobability := hammingRetentionProbability_pos dimension
  have hwords : 0 < ((2 ^ dimension : ℕ) : ℝ) := by
    positivity
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        (hammingExpectedRetainedEdgeCount dimension radius / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
      rw [hammingExpectedRetainedEdgeCount_eq]
      field_simp [hprobability.ne', hwords.ne', hdegree_positive.ne']
      ring

def retainedHammingHost (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : SimpleGraph retained :=
  (hammingHost dimension radius).induce retained

open Classical in
theorem retainedHammingHost_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    (retainedHammingHost dimension radius retained).edgeFinset.card =
      (retainedHammingWordEdges dimension radius retained).card := by
  classical
  let toEdge :
      ∀ edge ∈ retainedHammingWordEdges dimension radius retained,
        Sym2 retained := fun edge hedge =>
    s(⟨(false, edge.1), by
        exact (Finset.mem_filter.mp hedge).2.2.1⟩,
      ⟨(true, edge.2), by
        exact (Finset.mem_filter.mp hedge).2.2.2⟩)
  have hcard :
      (retainedHammingWordEdges dimension radius retained).card =
        (retainedHammingHost dimension radius retained).edgeFinset.card := by
    apply Finset.card_bij toEdge
    · intro edge hedge
      have hdata := (Finset.mem_filter.mp hedge).2
      change
        s(⟨(false, edge.1), hdata.2.1⟩,
          ⟨(true, edge.2), hdata.2.2⟩) ∈
          (retainedHammingHost dimension radius retained).edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change (hammingHost dimension radius).Adj
        (false, edge.1) (true, edge.2)
      apply (hammingHost_adj_iff dimension radius _ _).mpr
      exact ⟨by simp, hdata.1⟩
    · intro first hfirst second hsecond hequal
      dsimp [toEdge] at hequal
      rcases (Sym2.eq_iff.mp hequal) with
        ⟨hleft, hright⟩ | ⟨hswap, _⟩
      · apply Prod.ext
        · exact congrArg (fun vertex : retained => vertex.val.2) hleft
        · exact congrArg (fun vertex : retained => vertex.val.2) hright
      · have hside :=
          congrArg (fun vertex : retained => vertex.val.1) hswap
        simp at hside
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | hf first second =>
        have hadj :
            (retainedHammingHost dimension radius retained).Adj
              first second := by
          exact (SimpleGraph.mem_edgeSet
            (retainedHammingHost dimension radius retained)).mp
              ((SimpleGraph.mem_edgeFinset).mp hedge)
        have hhost :
            (hammingHost dimension radius).Adj
              first.val second.val := hadj
        rcases first with ⟨⟨firstSide, firstWord⟩, hfirst⟩
        rcases second with ⟨⟨secondSide, secondWord⟩, hsecond⟩
        have hdata :=
          (hammingHost_adj_iff dimension radius
            (firstSide, firstWord) (secondSide, secondWord)).mp hhost
        cases firstSide <;> cases secondSide
        · simp at hdata
        · refine ⟨(firstWord, secondWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hdata.2, hfirst, hsecond]
          · simp [toEdge]
        · have hreverse : hammingDist secondWord firstWord ≤ radius := by
            simpa [hammingDist_comm] using hdata.2
          refine ⟨(secondWord, firstWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hreverse, hfirst, hsecond]
          · dsimp [toEdge]
            exact Sym2.eq_swap
        · simp at hdata
  exact hcard.symm

open Classical in
theorem hammingRetainedEdgeCount_eq_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingHost dimension radius retained).edgeFinset.card : ℝ) := by
  rw [hammingRetainedEdgeCount_eq_wordEdges_card,
    retainedHammingHost_edgeFinset_card]

theorem pairGraphCopy_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize layer) :
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) second)).val.1 := by
  classical
  by_cases hequal : first = second
  · subst second
    rfl
  · let bridge : PairLayer baseSize (layer + 1) :=
      ⟨{first, second}, Finset.card_pair hequal⟩
    have hfirst_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) first) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge first
        (by simp [bridge])
    have hsecond_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) second) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge second
        (by simp [bridge])
    have hfirst_edge := copy.toHom.map_rel hfirst_source
    have hsecond_edge := copy.toHom.map_rel hsecond_source
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val at hfirst_edge
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val at hsecond_edge
    have hfirst_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
    have hsecond_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
    cases hbridge :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer bridge)).val.1 <;>
      cases hfirst :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val.1 <;>
      cases hsecond :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val.1 <;>
      simp_all

theorem pairGraphCopy_child_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize (layer + 1)) :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer second)).val.1 := by
  classical
  have hfirst_nonempty : first.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [first.property]
    norm_num
  have hsecond_nonempty : second.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [second.property]
    norm_num
  obtain ⟨firstParent, hfirstParent⟩ := hfirst_nonempty
  obtain ⟨secondParent, hsecondParent⟩ := hsecond_nonempty
  have hparent_side := pairGraphCopy_layer_side_eq
    retained copy layer hlayer firstParent secondParent
  have hfirst_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer first firstParent hfirstParent)
  have hsecond_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer second secondParent hsecondParent)
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer first)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val at hfirst_edge
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val at hsecond_edge
  have hfirst_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
  have hsecond_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
  cases hfirst :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 <;>
    cases hsecond :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val.1 <;>
    cases hfirstParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val.1 <;>
    cases hsecondParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val.1 <;>
    simp_all

noncomputable def pairGraphCopyParentWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Fin (Fintype.card (PairLayer baseSize layer.val)) →
      HammingWord dimension :=
  fun parent =>
    (copy
      (pairLayerEmbedding baseSize depth layer.val (by omega)
        ((pairLayerFinEquiv baseSize layer.val).symm parent))).val.2

noncomputable def pairGraphCopyChildWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1 →
      HammingWord dimension :=
  fun pair =>
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).val.2

noncomputable def pairGraphCopyChildSide
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) : Bool :=
  (copy
    (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((pairLayerPairEquiv baseSize layer.val) reference))).val.1

noncomputable def pairGraphCopyLayerPotential
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : PairLayer baseSize layer.val =>
          (copy
            (pairLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
        (Fintype.card (PairLayer baseSize layer.val) : ℝ))) /
    (dimension : ℝ)

theorem pairGraphCopy_parentPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairParentArrayEntropyPotential
        (pairGraphCopyParentWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val, by omega⟩ := by
  unfold pairParentArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount pairGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (pairLayerFinEquiv baseSize layer.val).symm
    (fun vertex : PairLayer baseSize layer.val =>
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          vertex)).val.2 coordinate)]

theorem pairGraphCopy_childPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayEntropyPotential
        (pairGraphCopyChildWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val + 1, by omega⟩ := by
  unfold pairChildArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairChildCoordinateOneCount pairGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (pairLayerPairEquiv baseSize layer.val)
    (fun vertex : PairLayer baseSize (layer.val + 1) =>
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          vertex)).val.2 coordinate)]
  rw [pairLayer_card_succ]

theorem pairGraphCopyLayerPotential_mem_Icc
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) :
    0 ≤ pairGraphCopyLayerPotential retained copy layer ∧
      pairGraphCopyLayerPotential retained copy layer ≤ 1 := by
  classical
  have hlayer :
      0 < Fintype.card (PairLayer baseSize layer.val) := by
    have hcard := pairLayer_card_ge_base
      baseSize layer.val hbase
    omega
  have hlayer_real :
      0 < (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card ≤
          Fintype.card (PairLayer baseSize layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (PairLayer baseSize layer.val))
          (fun vertex =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate = true))
    have hzero :
        0 ≤
          ((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
      positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone,
      binaryEntropy_le_one _⟩
  unfold pairGraphCopyLayerPotential
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg
        (fun coordinate _ => (hterm coordinate).1)
    · exact hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc
      (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) := by
          exact Finset.sum_le_sum
            (fun coordinate _ => (hterm coordinate).2)
      _ = (dimension : ℝ) := by
        simp

theorem pairGraphCopy_layer_entropy_upper_of_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdisagreement :
      pairChildArrayAverageDisagreement
        (hbase.trans
          (pairLayer_card_ge_base baseSize layer.val hbase))
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    pairChildArrayEntropy
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        entropyLowerEndpoint +
          (pairGraphCopyLayerPotential retained copy
              ⟨layer.val + 1, by omega⟩ -
            pairGraphCopyLayerPotential retained copy
              ⟨layer.val, by omega⟩) / 2 +
          empiricalEntropyError
            (Fintype.card (PairLayer baseSize layer.val)) := by
  have hparents :
      4 ≤ Fintype.card (PairLayer baseSize layer.val) :=
    hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase)
  have hbound := pairChildArrayEntropy_empirical_bound
    hparents hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
  rw [pairGraphCopy_childPotential_eq retained copy layer,
    pairGraphCopy_parentPotential_eq retained copy layer] at hbound
  have hscaled := mul_le_mul_of_nonneg_left
    hdisagreement logTwo_three_pos.le
  unfold entropyLowerEndpoint
  nlinarith

theorem pairGraphCopyChildWords_injective
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Function.Injective (pairGraphCopyChildWords retained copy layer) := by
  intro first second hwords
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) first)
    ((pairLayerPairEquiv baseSize layer.val) second)
  have hvertices :
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first))).val =
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second))).val := by
    apply Prod.ext
    · exact hside
    · exact hwords
  have himages :
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first)) =
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second)) :=
    Subtype.ext hvertices
  have hsources := copy.injective himages
  have hpairs :=
    (pairLayerEmbedding baseSize depth (layer.val + 1)
      (by omega)).injective hsources
  exact (pairLayerPairEquiv baseSize layer.val).injective hpairs

theorem pairGraphCopyChildWords_retained
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) :
    retained ∈
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference)
        (pairGraphCopyChildWords retained copy layer) := by
  intro pair
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) reference)
    ((pairLayerPairEquiv baseSize layer.val) pair)
  have hretained :=
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).property
  change
    (pairGraphCopyChildSide retained copy layer reference,
      pairGraphCopyChildWords retained copy layer pair) ∈ retained
  unfold pairGraphCopyChildSide pairGraphCopyChildWords
  rw [hside]
  exact hretained

theorem pairGraphCopy_parent_child_hammingDist_le
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (pair :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (parent :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 0)
    (hparent : parent ∈ pair.val) :
    hammingDist
      (pairGraphCopyParentWords retained copy layer parent)
      (pairGraphCopyChildWords retained copy layer pair) ≤ radius := by
  have hactualParent :
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        ((pairLayerPairEquiv baseSize layer.val) pair).val := by
    change
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        pair.val.map
          (pairLayerFinEquiv baseSize layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := pairGraph_parent_child_adj
    baseSize depth layer.val (by omega)
      ((pairLayerPairEquiv baseSize layer.val) pair)
      ((pairLayerFinEquiv baseSize layer.val).symm parent)
      hactualParent
  have hedge := copy.toHom.map_rel hsource
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) pair))).val
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          ((pairLayerFinEquiv baseSize layer.val).symm parent))).val at hedge
  have hdist :=
    ((hammingHost_adj_iff dimension radius _ _).mp hedge).2
  simpa [pairGraphCopyParentWords, pairGraphCopyChildWords,
    hammingDist_comm] using hdist

theorem pairGraphCopy_averageDisagreement_le_radius
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) := by
  apply pairChildArrayAverageDisagreement_le_radius
    (hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase))
    hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
    radius
  intro pair parent hparent
  exact pairGraphCopy_parent_child_hammingDist_le
    retained copy layer pair parent hparent

theorem pairGraphCopy_averageDisagreement_le_tau
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤ tau := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) :=
      pairGraphCopy_averageDisagreement_le_radius
        hbase hdimension retained copy layer
    _ ≤ tau :=
      (div_le_iff₀ hdimension_real).mpr hradius

theorem pairGraphCopy_entropy_lower_of_exclusion
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (threshold : ℝ)
    (hexclusion :
      retained ∉
        badPairLayerRetentionEvent
          (Fintype.card (PairLayer baseSize layer.val)) dimension
          (pairGraphCopyChildSide retained copy layer reference)
          threshold) :
    threshold <
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) := by
  classical
  by_contra hnot
  have hbad_entropy :
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ threshold :=
    le_of_not_gt hnot
  have hbad_array :
      pairGraphCopyChildWords retained copy layer ∈
        badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold := by
    unfold badPairChildArrays
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hbad_entropy⟩
  have hinjective :
      pairGraphCopyChildWords retained copy layer ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective :=
    Finset.mem_filter.mpr
      ⟨hbad_array,
        pairGraphCopyChildWords_injective retained copy layer⟩
  apply hexclusion
  change retained ∈
    ⋃ parents :
        Fin (Fintype.card (PairLayer baseSize layer.val)) →
          HammingWord dimension,
      badPairChildRetentionEvent parents
        (pairGraphCopyChildSide retained copy layer reference) threshold
  apply Set.mem_iUnion.mpr
  refine ⟨pairGraphCopyParentWords retained copy layer, ?_⟩
  change retained ∈
    ⋃ children ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective,
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference) children
  exact Set.mem_iUnion.mpr
    ⟨pairGraphCopyChildWords retained copy layer,
      Set.mem_iUnion.mpr
        ⟨hinjective,
          pairGraphCopyChildWords_retained
            retained copy layer reference⟩⟩

theorem pairGraph_free_of_layer_exclusion_and_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairParentSystem baseSize depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  let potential : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth + 1 then
      pairGraphCopyLayerPotential retained copy ⟨layer, hlevel⟩
    else 0
  let conditionalEntropy : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy ⟨layer, hlevel⟩)
        (pairGraphCopyChildWords retained copy ⟨layer, hlevel⟩)
    else 0
  let error : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      empiricalEntropyError
        (Fintype.card (PairLayer baseSize layer))
    else 0
  apply entropy_layer_exclusion depth
    potential conditionalEntropy error
  · intro layer hlayer
    have hinrange : layer < depth + 1 := by omega
    have hle : layer ≤ depth := by omega
    simpa [potential, hinrange, hle] using
      pairGraphCopyLayerPotential_mem_Icc
        hbase hdimension retained copy ⟨layer, hinrange⟩
  · intro layer hlayer
    simpa [error, hlayer] using
      herror ⟨layer, hlayer⟩
  · intro layer hlayer
    have hsize :
        2 ≤ Fintype.card (PairLayer baseSize layer) := by
      have hcard := pairLayer_card_ge_base
        baseSize layer hbase
      omega
    let reference :
        PairLayer (Fintype.card (PairLayer baseSize layer)) 1 :=
      Classical.choice (pairLayerPair_nonempty hsize)
    have hlower := pairGraphCopy_entropy_lower_of_exclusion
      retained copy ⟨layer, hlayer⟩ reference
        (midpointBeta - entropySlack)
        (hexclusion
          (pairGraphCopyChildSide
            retained copy ⟨layer, hlayer⟩ reference)
          ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, hlayer] using hlower
  · intro layer hlayer
    have hnext : layer + 1 < depth + 1 := by omega
    have hcurrent : layer < depth + 1 := by omega
    have hnext_le : layer + 1 ≤ depth := by omega
    have hcurrent_le : layer ≤ depth := by omega
    have hupper := pairGraphCopy_layer_entropy_upper_of_disagreement
      hbase hdimension retained copy ⟨layer, hlayer⟩
      (hdisagreement copy ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, potential, error,
      hlayer, hnext, hcurrent, hnext_le, hcurrent_le] using hupper
  · exact hdepth

theorem pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  exact (SimpleGraph.free_congr_left
    (pairGraphOverFinIso baseSize depth)).mp
      (pairGraph_free_of_layer_exclusion_and_disagreement
        hbase hdimension hdepth retained hexclusion herror hdisagreement)

theorem pairGraphOverFin_free_of_layer_exclusion
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  apply pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    hbase hdimension hdepth retained hexclusion herror
  intro copy layer
  exact pairGraphCopy_averageDisagreement_le_tau
    hbase hdimension hradius retained copy layer

end HammingHostAndExclusion

end Erdos146
