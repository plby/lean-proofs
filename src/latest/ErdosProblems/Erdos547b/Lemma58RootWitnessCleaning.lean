/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58RootCandidateCleaning

/-!
# Upper-typical witnesses for the Lemma-5.8 source-density row

The source row in Claim 6.15 is measured at one selected vertex of the
distinguished cluster.  Later component roots are selected from the same
cluster.  Regularity transfers the source row only when the selected witness
is not atypically *high* and the later roots are not atypically low.  This
module supplies the missing upper half of that standard argument.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma58RootWitnessCleaning

open Finset Fintype SimpleGraph

universe u w x

/-- Vertices of `S ⊆ C` whose degree into `T ⊆ D` is above the upper
regular-pair threshold. -/
noncomputable def targetHighDegreeVertices
    {B : Type u} [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (C D S T : Finset B) : Finset B :=
  {z ∈ S | (G.edgeDensity C D + rho) * #T <
    (#(T.filter (G.Adj z)) : ℝ)}

/-- Whole-pair uniformity bounds the target-relative upper-atypical set by
the same `rho |C|` loss as the usual lower-atypical set. -/
theorem card_targetHighDegreeVertices_le
    {B : Type u} [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {rho : ℝ} {C D S T : Finset B}
    (huniform : G.IsUniform rho C D)
    (hSC : S ⊆ C) (hTD : T ⊆ D)
    (_hSlarge : rho * #C ≤ #S) (hTlarge : rho * #D ≤ #T) :
    (#(targetHighDegreeVertices G rho C D S T) : ℝ) ≤ rho * #C := by
  classical
  let bad := targetHighDegreeVertices G rho C D S T
  by_contra! hbad
  have hbadLarge : (#C : ℝ) * rho ≤ #bad := by
    rw [mul_comm]
    exact hbad.le
  have hbadSub : bad ⊆ C := (filter_subset _ _).trans hSC
  have hTLarge : (#D : ℝ) * rho ≤ #T := by
    simpa only [mul_comm] using hTlarge
  have hunifBad :
      |(G.edgeDensity bad T : ℝ) - G.edgeDensity C D| < rho :=
    huniform hbadSub hTD hbadLarge hTLarge
  have hbadNe : bad.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    change rho * #C < (#bad : ℝ) at hbad
    rw [h] at hbad
    simp only [Finset.card_empty, Nat.cast_zero] at hbad
    exact (not_lt_of_ge (mul_nonneg huniform.pos.le (by positivity))) hbad
  have hinteredges :
      (#bad : ℝ) * #T * (G.edgeDensity C D + rho) <
        (#(Rel.interedges G.Adj bad T) : ℝ) := by
    rw [Rel.interedges_eq_biUnion, Finset.card_biUnion]
    · push_cast
      simp_rw [Finset.card_map]
      rw [mul_assoc, mul_comm (#T : ℝ), ← nsmul_eq_mul,
        ← Finset.sum_const]
      exact Finset.sum_lt_sum_of_nonempty hbadNe (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
    · intro z hz z' hz' hne
      change Disjoint
        ({y ∈ T | G.Adj z y}.map ⟨(z, ·), Prod.mk_right_injective z⟩)
        ({y ∈ T | G.Adj z' y}.map ⟨(z', ·), Prod.mk_right_injective z'⟩)
      rw [Finset.disjoint_left]
      intro p hp hp'
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨y', -, hy'⟩ := Finset.mem_map.mp hp'
      have : z = z' := by
        simpa using congrArg Prod.fst hy'.symm
      exact hne this
  have hTpos : 0 < (#T : ℝ) := by
    obtain ⟨z, hz⟩ := hbadNe
    have hz' := (Finset.mem_filter.mp hz).2
    by_contra h
    have hzero : (#T : ℝ) = 0 :=
      le_antisymm (le_of_not_gt h) (by positivity)
    have hTcard : #T = 0 := by exact_mod_cast hzero
    have hTempty : T = ∅ := Finset.card_eq_zero.mp hTcard
    rw [hTempty] at hz'
    simp at hz'
  have hbadPos : 0 < (#bad : ℝ) := by positivity
  have hdensity :
      (G.edgeDensity C D : ℝ) + rho < G.edgeDensity bad T := by
    change (#bad : ℝ) * #T * (G.edgeDensity C D + rho) <
      (#(G.interedges bad T) : ℝ) at hinteredges
    rw [G.edgeDensity_def bad T]
    push_cast
    apply (lt_div_iff₀ (mul_pos hbadPos hTpos)).2
    simpa only [mul_assoc, mul_comm] using hinteredges
  rw [abs_sub_lt_iff] at hunifBad
  linarith

/-- Avoiding the upper-atypical set gives the required upper degree
estimate. -/
theorem target_degree_le_of_not_mem_highDegree
    {B : Type u} [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (C D S T : Finset B) (z : B)
    (hzS : z ∈ S)
    (hzGood : z ∉ targetHighDegreeVertices G rho C D S T) :
    (#(T.filter (G.Adj z)) : ℝ) ≤
      (G.edgeDensity C D + rho) * #T := by
  apply le_of_not_gt
  intro hlt
  exact hzGood (by
    simpa only [targetHighDegreeVertices, Finset.mem_filter, hzS, true_and]
      using hlt)

/-- Union of all upper-atypical sets which can corrupt the source row of one
selected witness. -/
noncomputable def rootTargetHighBad
    {B : Type u} [DecidableEq B]
    {R : Type x} {Target : Type w} [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole : Target → Finset B)
    (q : R) : Finset B :=
  (targets q).biUnion fun t ↦
    targetHighDegreeVertices G rho (rootWhole q) (targetWhole t)
      (rootRaw q) (targetWhole t)

/-- The upper-atypical union has the same finite-union loss as the usual
lower cleaning. -/
theorem card_rootTargetHighBad_le
    {B : Type u} [DecidableEq B]
    {R : Type x} {Target : Type w} [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole : Target → Finset B)
    (q : R)
    (huniform : ∀ t ∈ targets q,
      G.IsUniform rho (rootWhole q) (targetWhole t))
    (hrootSub : rootRaw q ⊆ rootWhole q)
    (hrootLarge : rho * #(rootWhole q) ≤ #(rootRaw q))
    (hrho : rho ≤ 1) :
    (#(rootTargetHighBad G rho rootWhole rootRaw targets targetWhole q) : ℝ)
      ≤ (#(targets q) : ℝ) * (rho * #(rootWhole q)) := by
  have hcardNat :
      #(rootTargetHighBad G rho rootWhole rootRaw targets targetWhole q) ≤
        ∑ t ∈ targets q,
          #(targetHighDegreeVertices G rho (rootWhole q) (targetWhole t)
            (rootRaw q) (targetWhole t)) := by
    exact Finset.card_biUnion_le
  calc
    (#(rootTargetHighBad G rho rootWhole rootRaw targets targetWhole q) : ℝ)
        ≤ ∑ t ∈ targets q,
          (#(targetHighDegreeVertices G rho (rootWhole q) (targetWhole t)
            (rootRaw q) (targetWhole t)) : ℝ) := by
      exact_mod_cast hcardNat
    _ ≤ ∑ _t ∈ targets q, rho * #(rootWhole q) := by
      apply Finset.sum_le_sum
      intro t ht
      apply card_targetHighDegreeVertices_le G (huniform t ht)
        hrootSub Finset.Subset.rfl hrootLarge
      have hcard : rho * (#(targetWhole t) : ℝ) ≤ #(targetWhole t) := by
        nlinarith [mul_nonneg (huniform t ht).pos.le
          (Nat.cast_nonneg (#(targetWhole t)))]
      exact hcard
    _ = (#(targets q) : ℝ) * (rho * #(rootWhole q)) := by simp

/-- A witness outside the upper bad union has degree at most the upper
regular-pair threshold toward every listed whole target. -/
theorem rootWitness_target_degree_upper
    {B : Type u} [DecidableEq B]
    {R : Type x} {Target : Type w} [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole : Target → Finset B)
    (q : R) (z : B)
    (hzRaw : z ∈ rootRaw q)
    (hzGood : z ∉ rootTargetHighBad G rho rootWhole rootRaw targets
      targetWhole q)
    (t : Target) (ht : t ∈ targets q) :
    (#((targetWhole t).filter (G.Adj z)) : ℝ) ≤
      (G.edgeDensity (rootWhole q) (targetWhole t) + rho) *
        #(targetWhole t) := by
  apply target_degree_le_of_not_mem_highDegree G rho (rootWhole q)
    (targetWhole t) (rootRaw q) (targetWhole t) z hzRaw
  intro hzHigh
  exact hzGood (Finset.mem_biUnion.mpr ⟨t, ht, hzHigh⟩)

/-- The elementary two-sided transfer inequality.  A witness which is at
most `rho` above the pair density and a candidate which is at most `rho`
below it differ by no more than the deleted target vertices plus
`2 rho |D|`. -/
theorem upper_lower_degree_transfer
    {d rho wholeCard rawCard removed witnessDegree candidateDegree : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hrho : 0 ≤ rho)
    (hraw0 : 0 ≤ rawCard) (hrawWhole : rawCard ≤ wholeCard)
    (hremoved : wholeCard ≤ rawCard + removed)
    (hwitness : witnessDegree ≤ (d + rho) * wholeCard)
    (hcandidate : (d - rho) * rawCard ≤ candidateDegree) :
    witnessDegree ≤ candidateDegree + removed + 2 * rho * wholeCard := by
  have hgap : 0 ≤ wholeCard - rawCard := sub_nonneg.mpr hrawWhole
  have hdGap : 0 ≤ (1 - d) * (wholeCard - rawCard) :=
    mul_nonneg (sub_nonneg.mpr hd1) hgap
  have hrhoGap : 0 ≤ rho * (wholeCard - rawCard) :=
    mul_nonneg hrho hgap
  nlinarith

/-- Concrete graph form of `upper_lower_degree_transfer`. -/
theorem target_degree_transfer
    {B : Type u} [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (C D S T : Finset B) (witness candidate : B)
    (hTsub : T ⊆ D) (removed : ℕ)
    (hremoved : #D ≤ #T + removed)
    (hwitness : (#(D.filter (G.Adj witness)) : ℝ) ≤
      (G.edgeDensity C D + rho) * #D)
    (hcandidate : (G.edgeDensity C D - rho) * #T ≤
      (#(T.filter (G.Adj candidate)) : ℝ))
    (hrho : 0 ≤ rho) :
    (#(D.filter (G.Adj witness)) : ℝ) ≤
      (#(T.filter (G.Adj candidate)) : ℝ) + removed +
        2 * rho * #D := by
  apply upper_lower_degree_transfer
    (d := (G.edgeDensity C D : ℝ)) (rho := rho)
    (wholeCard := (#D : ℝ)) (rawCard := (#T : ℝ))
    (removed := removed)
    (witnessDegree := (#(D.filter (G.Adj witness)) : ℝ))
    (candidateDegree := (#(T.filter (G.Adj candidate)) : ℝ))
  · exact_mod_cast G.edgeDensity_nonneg C D
  · exact_mod_cast G.edgeDensity_le_one C D
  · exact hrho
  · positivity
  · exact_mod_cast Finset.card_le_card hTsub
  · exact_mod_cast hremoved
  · exact hwitness
  · exact hcandidate

end Erdos547b.ZhaoLemma58RootWitnessCleaning

#print axioms Erdos547b.ZhaoLemma58RootWitnessCleaning.card_targetHighDegreeVertices_le
#print axioms Erdos547b.ZhaoLemma58RootWitnessCleaning.card_rootTargetHighBad_le
#print axioms Erdos547b.ZhaoLemma58RootWitnessCleaning.rootWitness_target_degree_upper
#print axioms Erdos547b.ZhaoLemma58RootWitnessCleaning.target_degree_transfer
