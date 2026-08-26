/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

/-!
# Regular-pair slicing for Erdős Problem 547

This is the precise restriction lemma needed when the equitable partition
from Mathlib's regularity lemma is cleaned and trimmed in the degree-form
decomposition used by Zhao.
-/

open Finset

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
  {ε ε' : ℝ} {s t s' t' : Finset α}

/-- Vertices whose degree into `t` is more than `ε * #t` below the density-predicted degree. -/
noncomputable def lowerAtypicalVertices (G : SimpleGraph α) [DecidableRel G.Adj]
    (ε : ℝ) (s t : Finset α) : Finset α :=
  {x ∈ s | (#{y ∈ t | G.Adj x y} : ℝ) <
    ((G.edgeDensity s t : ℝ) - ε) * #t}

/-- Vertices whose degree into `t` is more than `ε * #t` above the density-predicted degree. -/
noncomputable def upperAtypicalVertices (G : SimpleGraph α) [DecidableRel G.Adj]
    (ε : ℝ) (s t : Finset α) : Finset α :=
  {x ∈ s | ((G.edgeDensity s t : ℝ) + ε) * #t <
    (#{y ∈ t | G.Adj x y} : ℝ)}

private theorem card_interedges_eq_sum_neighborCounts (G : SimpleGraph α)
    [DecidableRel G.Adj] (s t : Finset α) :
    #(G.interedges s t) = ∑ x ∈ s, #{y ∈ t | G.Adj x y} := by
  classical
  have hdisjoint : (s : Set α).PairwiseDisjoint
      (fun x => {y ∈ t | G.Adj x y}.map ⟨(x, ·), Prod.mk_right_injective x⟩) := by
    intro x hx y hy hxy
    change Disjoint
      ({z ∈ t | G.Adj x z}.map ⟨(x, ·), Prod.mk_right_injective x⟩)
      ({z ∈ t | G.Adj y z}.map ⟨(y, ·), Prod.mk_right_injective y⟩)
    rw [Finset.disjoint_left]
    intro p hpx hpy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.1 hpx
    obtain ⟨w, hw, hEq⟩ := Finset.mem_map.1 hpy
    exact hxy (congrArg Prod.fst hEq).symm
  change #(Rel.interedges G.Adj s t) = ∑ x ∈ s, #{y ∈ t | G.Adj x y}
  rw [Rel.interedges_eq_biUnion, Finset.card_biUnion hdisjoint]
  simp

private theorem card_interedges_lowerAtypical_lt
    (hbad : (lowerAtypicalVertices G ε s t).Nonempty) :
    (#(G.interedges (lowerAtypicalVertices G ε s t) t) : ℝ) <
      (#(lowerAtypicalVertices G ε s t) : ℝ) * #t *
        ((G.edgeDensity s t : ℝ) - ε) := by
  classical
  calc
    (#(G.interedges (lowerAtypicalVertices G ε s t) t) : ℝ) =
        ∑ x ∈ lowerAtypicalVertices G ε s t,
          (#{y ∈ t | G.Adj x y} : ℝ) := by
            rw [card_interedges_eq_sum_neighborCounts]
            push_cast
            rfl
    _ < ∑ _x ∈ lowerAtypicalVertices G ε s t,
          ((G.edgeDensity s t : ℝ) - ε) * #t := by
            apply Finset.sum_lt_sum_of_nonempty hbad
            intro x hx
            exact (Finset.mem_filter.1 hx).2
    _ = (#(lowerAtypicalVertices G ε s t) : ℝ) * #t *
        ((G.edgeDensity s t : ℝ) - ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

private theorem card_interedges_upperAtypical_gt
    (hbad : (upperAtypicalVertices G ε s t).Nonempty) :
    (#(upperAtypicalVertices G ε s t) : ℝ) * #t *
        ((G.edgeDensity s t : ℝ) + ε) <
      (#(G.interedges (upperAtypicalVertices G ε s t) t) : ℝ) := by
  classical
  calc
    (#(upperAtypicalVertices G ε s t) : ℝ) * #t *
        ((G.edgeDensity s t : ℝ) + ε) =
        ∑ _x ∈ upperAtypicalVertices G ε s t,
          ((G.edgeDensity s t : ℝ) + ε) * #t := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    _ < ∑ x ∈ upperAtypicalVertices G ε s t,
          (#{y ∈ t | G.Adj x y} : ℝ) := by
            apply Finset.sum_lt_sum_of_nonempty hbad
            intro x hx
            exact (Finset.mem_filter.1 hx).2
    _ = (#(G.interedges (upperAtypicalVertices G ε s t) t) : ℝ) := by
          rw [card_interedges_eq_sum_neighborCounts]
          push_cast
          rfl

private theorem edgeDensity_lowerAtypical_lt
    (hbad : (lowerAtypicalVertices G ε s t).Nonempty) :
    (G.edgeDensity (lowerAtypicalVertices G ε s t) t : ℝ) <
      (G.edgeDensity s t : ℝ) - ε := by
  have hcount := card_interedges_lowerAtypical_lt (G := G) (ε := ε) (s := s) (t := t) hbad
  have hb : 0 < (#(lowerAtypicalVertices G ε s t) : ℝ) := by
    exact_mod_cast hbad.card_pos
  have hright : 0 < (#(lowerAtypicalVertices G ε s t) : ℝ) * #t *
      ((G.edgeDensity s t : ℝ) - ε) :=
    (Nat.cast_nonneg _).trans_lt hcount
  rw [mul_assoc] at hright
  have htd : 0 < (#t : ℝ) * ((G.edgeDensity s t : ℝ) - ε) :=
    pos_of_mul_pos_right hright hb.le
  have hd : 0 < (G.edgeDensity s t : ℝ) - ε :=
    pos_of_mul_pos_right htd (Nat.cast_nonneg _)
  have ht : 0 < (#t : ℝ) := pos_of_mul_pos_left htd hd.le
  rw [edgeDensity_def (G := G) (s := lowerAtypicalVertices G ε s t) (t := t)]
  push_cast
  rw [div_lt_iff₀ (mul_pos hb ht)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcount

private theorem edgeDensity_upperAtypical_gt
    (hbad : (upperAtypicalVertices G ε s t).Nonempty) :
    (G.edgeDensity s t : ℝ) + ε <
      (G.edgeDensity (upperAtypicalVertices G ε s t) t : ℝ) := by
  have hb : 0 < (#(upperAtypicalVertices G ε s t) : ℝ) := by
    exact_mod_cast hbad.card_pos
  obtain rfl | ht_nonempty := t.eq_empty_or_nonempty
  · simp [upperAtypicalVertices] at hbad
  have ht : 0 < (#t : ℝ) := by exact_mod_cast ht_nonempty.card_pos
  have hcount := card_interedges_upperAtypical_gt (G := G) (ε := ε) (s := s) (t := t) hbad
  rw [edgeDensity_def (G := G) (s := upperAtypicalVertices G ε s t) (t := t)]
  push_cast
  rw [lt_div_iff₀ (mul_pos hb ht)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcount

/-- In an `ε`-uniform pair, at most an `ε`-fraction of the left-hand vertices have degree
more than `ε * #t` below the density-predicted degree.  No density lower bound is needed. -/
theorem IsUniform.card_lowerAtypicalVertices_le
    (h : G.IsUniform ε s t) :
    (#(lowerAtypicalVertices G ε s t) : ℝ) ≤ (#s : ℝ) * ε := by
  by_cases hε_one : ε ≤ 1
  · by_contra! hcard
    have hbad : (lowerAtypicalVertices G ε s t).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty, Nat.cast_zero] at hcard
      exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg _) h.pos.le)) hcard
    have huniform := h
      (show lowerAtypicalVertices G ε s t ⊆ s from Finset.filter_subset _ _)
      (Subset.rfl)
      hcard.le
      (mul_le_of_le_one_right (Nat.cast_nonneg _) hε_one)
    have hdensity := edgeDensity_lowerAtypical_lt
      (G := G) (ε := ε) (s := s) (t := t) hbad
    rw [abs_sub_lt_iff] at huniform
    linarith
  · calc
      (#(lowerAtypicalVertices G ε s t) : ℝ) ≤ #s := by
        exact_mod_cast Finset.card_filter_le s _
      _ ≤ (#s : ℝ) * ε :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) (le_of_not_ge hε_one)

/-- In an `ε`-uniform pair, at most an `ε`-fraction of the left-hand vertices have degree
more than `ε * #t` above the density-predicted degree.  No density upper bound is needed. -/
theorem IsUniform.card_upperAtypicalVertices_le
    (h : G.IsUniform ε s t) :
    (#(upperAtypicalVertices G ε s t) : ℝ) ≤ (#s : ℝ) * ε := by
  by_cases hε_one : ε ≤ 1
  · by_contra! hcard
    have hbad : (upperAtypicalVertices G ε s t).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty, Nat.cast_zero] at hcard
      exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg _) h.pos.le)) hcard
    have huniform := h
      (show upperAtypicalVertices G ε s t ⊆ s from Finset.filter_subset _ _)
      (Subset.rfl)
      hcard.le
      (mul_le_of_le_one_right (Nat.cast_nonneg _) hε_one)
    have hdensity := edgeDensity_upperAtypical_gt
      (G := G) (ε := ε) (s := s) (t := t) hbad
    rw [abs_sub_lt_iff] at huniform
    linarith
  · calc
      (#(upperAtypicalVertices G ε s t) : ℝ) ≤ #s := by
        exact_mod_cast Finset.card_filter_le s _
      _ ≤ (#s : ℝ) * ε :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) (le_of_not_ge hε_one)


/-- If `s'` and `t'` are large subsets of an `ε`-uniform pair, restriction
preserves uniformity with any error `ε' ≥ 2 * ε`, provided an `ε'`-large
subset of a restricted side is still `ε`-large in the original side. -/
theorem IsUniform.mono_subsets
    (h : G.IsUniform ε s t)
    (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hs_large : (#s : ℝ) * ε ≤ #s')
    (ht_large : (#t : ℝ) * ε ≤ #t')
    (hs_scale : (#s : ℝ) * ε ≤ (#s' : ℝ) * ε')
    (ht_scale : (#t : ℝ) * ε ≤ (#t' : ℝ) * ε')
    (herror : 2 * ε ≤ ε') :
    G.IsUniform ε' s' t' := by
  intro u hu v hv hu_card hv_card
  have hu_original : (#s : ℝ) * ε ≤ #u := hs_scale.trans hu_card
  have hv_original : (#t : ℝ) * ε ≤ #v := ht_scale.trans hv_card
  have huv := h (hu.trans hs) (hv.trans ht) hu_original hv_original
  have hrestricted := h hs ht hs_large ht_large
  calc
    |(G.edgeDensity u v : ℝ) - G.edgeDensity s' t'| =
        |((G.edgeDensity u v : ℝ) - G.edgeDensity s t) +
          ((G.edgeDensity s t : ℝ) - G.edgeDensity s' t')| := by ring_nf
    _ ≤ |(G.edgeDensity u v : ℝ) - G.edgeDensity s t| +
        |(G.edgeDensity s t : ℝ) - G.edgeDensity s' t'| := abs_add_le _ _
    _ = |(G.edgeDensity u v : ℝ) - G.edgeDensity s t| +
        |(G.edgeDensity s' t' : ℝ) - G.edgeDensity s t| := by
          rw [abs_sub_comm (G.edgeDensity s t : ℝ) (G.edgeDensity s' t' : ℝ)]
    _ < ε + ε := add_lt_add huv hrestricted
    _ = 2 * ε := by ring
    _ ≤ ε' := herror

end SimpleGraph

namespace Finpartition

variable [DecidableEq α] {A : Finset α} (P : Finpartition A)

/-- The ordered nonuniform pairs whose first coordinate is `U`.  Keeping the pair,
rather than projecting to its second coordinate, makes the ensuing double count literal. -/
noncomputable def irregularPairsFrom (G : SimpleGraph α) [DecidableRel G.Adj]
    (η : ℝ) (U : Finset α) : Finset (Finset α × Finset α) :=
  (P.nonUniforms G η).filter fun UV => UV.1 = U

/-- Clusters having more than a `q`-fraction of all clusters as nonuniform partners. -/
noncomputable def badClusters (G : SimpleGraph α) [DecidableRel G.Adj]
    (η q : ℝ) : Finset (Finset α) :=
  P.parts.filter fun U =>
    q * (#P.parts : ℝ) < (#(P.irregularPairsFrom G η U) : ℝ)

private theorem sum_card_irregularPairsFrom
    (G : SimpleGraph α) [DecidableRel G.Adj] (η : ℝ) :
    ∑ U ∈ P.parts, #(P.irregularPairsFrom G η U) = #(P.nonUniforms G η) := by
  classical
  have hfilter : (P.nonUniforms G η).filter (fun UV => UV.1 ∈ P.parts) =
      P.nonUniforms G η := Finset.filter_true_of_mem fun UV hUV =>
    (Finpartition.mk_mem_nonUniforms (P := P) (G := G) (ε := η)).1 hUV |>.1
  simpa [irregularPairsFrom, hfilter] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (P.nonUniforms G η) P.parts Prod.fst)

/-- The first Markov-type cleanup estimate.  If at most an `η`-fraction of ordered
cluster pairs are nonuniform and `η ≤ q²`, then fewer than a `q`-fraction of clusters
have more than a `q`-fraction of nonuniform partners. -/
theorem IsUniform.card_badClusters_lt
    {G : SimpleGraph α} [DecidableRel G.Adj] {η q : ℝ}
    (hP : P.IsUniform G η) (hparts : P.parts.Nonempty)
    (hη : 0 ≤ η) (hq : 0 < q) (hηq : η ≤ q ^ 2) :
    (#(P.badClusters G η q) : ℝ) < q * (#P.parts : ℝ) := by
  classical
  let B := P.badClusters G η q
  let k : ℝ := (#P.parts : ℝ)
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hparts.card_pos
  by_cases hB : B.Nonempty
  · have hsmall :
        ∑ U ∈ B, q * k < ∑ U ∈ B, (#(P.irregularPairsFrom G η U) : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hB
      intro U hU
      exact (Finset.mem_filter.1 hU).2
    have hsubset : B ⊆ P.parts := Finset.filter_subset _ _
    have hsubsum :
        ∑ U ∈ B, (#(P.irregularPairsFrom G η U) : ℝ) ≤
          ∑ U ∈ P.parts, (#(P.irregularPairsFrom G η U) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => Nat.cast_nonneg _
    have hsum :
        ∑ U ∈ P.parts, (#(P.irregularPairsFrom G η U) : ℝ) =
          (#(P.nonUniforms G η) : ℝ) := by
      exact_mod_cast sum_card_irregularPairsFrom P G η
    have hcoeff :
        ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) ≤ k * k := by
      dsimp [k]
      exact_mod_cast Nat.mul_le_mul_left #P.parts (Nat.sub_le #P.parts 1)
    have htotal :
        (#(P.nonUniforms G η) : ℝ) ≤ k * k * (q ^ 2) := by
      calc
        (#(P.nonUniforms G η) : ℝ) ≤
            ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * η := hP
        _ ≤ (k * k) * η := mul_le_mul_of_nonneg_right hcoeff hη
        _ ≤ (k * k) * (q ^ 2) :=
          mul_le_mul_of_nonneg_left hηq (mul_nonneg hk.le hk.le)
    have hmain : (#B : ℝ) * (q * k) < k * k * (q ^ 2) := by
      calc
        (#B : ℝ) * (q * k) = ∑ _U ∈ B, q * k := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ < ∑ U ∈ B, (#(P.irregularPairsFrom G η U) : ℝ) := hsmall
        _ ≤ ∑ U ∈ P.parts, (#(P.irregularPairsFrom G η U) : ℝ) := hsubsum
        _ = (#(P.nonUniforms G η) : ℝ) := hsum
        _ ≤ k * k * (q ^ 2) := htotal
    have hqk : 0 < q * k := mul_pos hq hk
    dsimp [B, k] at hmain ⊢
    nlinarith
  · have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (#B : ℝ) < q * k
    rw [hB0, Finset.card_empty, Nat.cast_zero]
    exact mul_pos hq hk

/-- Regular partner clusters for which `x ∈ U` has degree more than `η * #V`
above the density-predicted degree. -/
noncomputable def upperAtypicalPartnersAt
    (G : SimpleGraph α) [DecidableRel G.Adj] (η : ℝ)
    (U : Finset α) (x : α) : Finset (Finset α) :=
  P.parts.filter fun V =>
    U ≠ V ∧ G.IsUniform η U V ∧
      x ∈ SimpleGraph.upperAtypicalVertices G η U V

/-- Vertices which are upper-atypical into more than a `q`-fraction of all clusters. -/
noncomputable def upperBadVertices
    (G : SimpleGraph α) [DecidableRel G.Adj] (η q : ℝ)
    (U : Finset α) : Finset α :=
  U.filter fun x =>
    q * (#P.parts : ℝ) < (#(P.upperAtypicalPartnersAt G η U x) : ℝ)

private theorem sum_card_upperAtypicalPartnersAt
    (G : SimpleGraph α) [DecidableRel G.Adj] (η : ℝ) (U : Finset α) :
    ∑ x ∈ U, #(P.upperAtypicalPartnersAt G η U x) =
      ∑ V ∈ P.parts.filter (fun V => U ≠ V ∧ G.IsUniform η U V),
        #(SimpleGraph.upperAtypicalVertices G η U V) := by
  classical
  simp only [upperAtypicalPartnersAt,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  congr 1 with V
  by_cases hV : U ≠ V ∧ G.IsUniform η U V
  · rcases hV with ⟨hne, huni⟩
    simp [hne, huni, SimpleGraph.upperAtypicalVertices]
    apply congrArg Finset.card
    ext x
    simp
  · by_cases hne : U ≠ V
    · have hnuni : ¬G.IsUniform η U V := fun huni => hV ⟨hne, huni⟩
      simp [hne, hnuni]
    · simp [hne]

private theorem sum_card_upperAtypicalPartnersAt_le
    (G : SimpleGraph α) [DecidableRel G.Adj] {η : ℝ} (hη : 0 ≤ η)
    (U : Finset α) :
    ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) ≤
      (#P.parts : ℝ) * (#U : ℝ) * η := by
  classical
  let R := P.parts.filter (fun V => U ≠ V ∧ G.IsUniform η U V)
  have hcount :
      ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) =
        ∑ V ∈ R, (#(SimpleGraph.upperAtypicalVertices G η U V) : ℝ) := by
    exact_mod_cast sum_card_upperAtypicalPartnersAt P G η U
  calc
    ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) =
        ∑ V ∈ R, (#(SimpleGraph.upperAtypicalVertices G η U V) : ℝ) := hcount
    _ ≤ ∑ _V ∈ R, (#U : ℝ) * η := by
      apply Finset.sum_le_sum
      intro V hV
      exact SimpleGraph.IsUniform.card_upperAtypicalVertices_le
        ((Finset.mem_filter.1 hV).2.2)
    _ = (#R : ℝ) * ((#U : ℝ) * η) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (#P.parts : ℝ) * ((#U : ℝ) * η) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_filter_le P.parts _
      · exact mul_nonneg (Nat.cast_nonneg _) hη
    _ = (#P.parts : ℝ) * (#U : ℝ) * η := by ring

/-- The second Markov cleanup estimate.  Within every cluster, fewer than a
`q`-fraction of vertices are upper-atypical into more than a `q`-fraction of all
clusters, provided the original uniformity parameter satisfies `η ≤ q²`. -/
theorem card_upperBadVertices_lt
    {G : SimpleGraph α} [DecidableRel G.Adj] {η q : ℝ} {U : Finset α}
    (hU : U ∈ P.parts) (hη : 0 ≤ η) (hq : 0 < q) (hηq : η ≤ q ^ 2) :
    (#(P.upperBadVertices G η q U) : ℝ) < q * (#U : ℝ) := by
  classical
  let B := P.upperBadVertices G η q U
  let k : ℝ := (#P.parts : ℝ)
  have hparts : P.parts.Nonempty := ⟨U, hU⟩
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hparts.card_pos
  have hUnonempty : U.Nonempty := P.nonempty_of_mem_parts hU
  have hUcard : 0 < (#U : ℝ) := by exact_mod_cast hUnonempty.card_pos
  by_cases hB : B.Nonempty
  · have hsmall :
        ∑ x ∈ B, q * k <
          ∑ x ∈ B, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hB
      intro x hx
      exact (Finset.mem_filter.1 hx).2
    have hsubset : B ⊆ U := Finset.filter_subset _ _
    have hsubsum :
        ∑ x ∈ B, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) ≤
          ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => Nat.cast_nonneg _
    have htotal :
        ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) ≤
          k * (#U : ℝ) * (q ^ 2) := by
      calc
        ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) ≤
            (#P.parts : ℝ) * (#U : ℝ) * η :=
          sum_card_upperAtypicalPartnersAt_le P G hη U
        _ ≤ k * (#U : ℝ) * (q ^ 2) := by
          dsimp [k]
          exact mul_le_mul_of_nonneg_left hηq
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hmain : (#B : ℝ) * (q * k) < k * (#U : ℝ) * (q ^ 2) := by
      calc
        (#B : ℝ) * (q * k) = ∑ _x ∈ B, q * k := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ < ∑ x ∈ B, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) := hsmall
        _ ≤ ∑ x ∈ U, (#(P.upperAtypicalPartnersAt G η U x) : ℝ) := hsubsum
        _ ≤ k * (#U : ℝ) * (q ^ 2) := htotal
    have hqk : 0 < q * k := mul_pos hq hk
    change (#B : ℝ) < q * (#U : ℝ)
    nlinarith
  · have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (#B : ℝ) < q * (#U : ℝ)
    rw [hB0, Finset.card_empty, Nat.cast_zero]
    exact mul_pos hq hUcard

/-- A finite cleanup construction specialized to `Fin n`.  Starting from an equitable
partition, discard a chosen family of bad clusters and at most `r` chosen bad vertices
from every remaining cluster, then trim every remaining cluster to the common size
`n / k - r`.  The output records the exceptional set exactly, including the rounding
loss from the original equitable partition. -/
theorem exists_cleaned_equal_partition_fin
    {n r : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hP : P.IsEquipartition) (badC : Finset (Finset (Fin n)))
    (hbadC : badC ⊆ P.parts)
    (badV : Finset (Fin n) → Finset (Fin n))
    (hbadV_subset : ∀ U ∈ P.parts \ badC, badV U ⊆ U)
    (hbadV_card : ∀ U ∈ P.parts \ badC, #(badV U) ≤ r)
    (hr : r < n / #P.parts) :
    ∃ E : Finset (Fin n), ∃ Q : Finpartition (Finset.univ \ E),
      #Q.parts = #P.parts - #badC ∧
      #E = n - ((#P.parts - #badC) * (n / #P.parts - r)) ∧
      ∀ W ∈ Q.parts,
        #W = n / #P.parts - r ∧
          ∃ U ∈ P.parts \ badC, W ⊆ U \ badV U := by
  classical
  let Good := P.parts \ badC
  let m := n / #P.parts - r
  have hm : 0 < m := by
    dsimp [m]
    exact Nat.sub_pos_of_lt hr
  have hchoose : ∀ i : {U // U ∈ Good},
      ∃ W : Finset (Fin n), W ⊆ i.1 \ badV i.1 ∧ #W = m := by
    intro i
    have hiGood : i.1 ∈ P.parts \ badC := i.2
    have hiP : i.1 ∈ P.parts := (Finset.mem_sdiff.1 hiGood).1
    have havg : n / #P.parts ≤ #i.1 := by
      simpa using hP.average_le_card_part hiP
    have hbad := hbadV_card i.1 hiGood
    have havailable : m ≤ #(i.1 \ badV i.1) := by
      rw [Finset.card_sdiff_of_subset (hbadV_subset i.1 hiGood)]
      dsimp [m]
      omega
    obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq havailable
    exact ⟨W, hWsub, hWcard⟩
  choose f hfsub hfcard using hchoose
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hval
    have hiP : i.1 ∈ P.parts := (Finset.mem_sdiff.1 i.2).1
    have hjP : j.1 ∈ P.parts := (Finset.mem_sdiff.1 j.2).1
    have hd : Disjoint i.1 j.1 := P.disjoint hiP hjP hval
    have hfi : (f i).Nonempty := Finset.card_pos.1 (hfcard i ▸ hm)
    obtain ⟨x, hxi⟩ := hfi
    have hxj : x ∈ f j := by rwa [← hij]
    exact (Finset.disjoint_left.1 hd)
      ((Finset.mem_sdiff.1 (hfsub i hxi)).1)
      ((Finset.mem_sdiff.1 (hfsub j hxj)).1)
  let I := Good.attach
  let C := I.image f
  have hCcard : #C = #Good := by
    dsimp [C, I]
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_attach]
  have hCspec : ∀ W ∈ C,
      #W = m ∧ ∃ U ∈ Good, W ⊆ U \ badV U := by
    intro W hW
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.1 hW
    exact ⟨hfcard i, i.1, i.2, hfsub i⟩
  have hCdisjoint : (C : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro W hW Z hZ hWZ
    change W ∈ C at hW
    change Z ∈ C at hZ
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.1 hW
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.1 hZ
    have hij : i ≠ j := fun hij => hWZ (congrArg f hij)
    have hval : i.1 ≠ j.1 := fun hval => hij (Subtype.ext hval)
    have hiP : i.1 ∈ P.parts := (Finset.mem_sdiff.1 i.2).1
    have hjP : j.1 ∈ P.parts := (Finset.mem_sdiff.1 j.2).1
    exact (P.disjoint hiP hjP hval).mono
      ((hfsub i).trans (Finset.sdiff_subset))
      ((hfsub j).trans (Finset.sdiff_subset))
  have hCempty : ∅ ∉ C := by
    intro hzero
    have hz := (hCspec ∅ hzero).1
    have hmzero : m = 0 := by simpa using hz.symm
    exact hm.ne' hmzero
  let S := C.sup id
  have hSuniv : S ⊆ (Finset.univ : Finset (Fin n)) := fun _ _ => Finset.mem_univ _
  let E : Finset (Fin n) := Finset.univ \ S
  have hcomp : (Finset.univ : Finset (Fin n)) \ E = S := by
    dsimp [E]
    exact Finset.sdiff_sdiff_eq_self hSuniv
  let Q0 : Finpartition S := Finpartition.ofPairwiseDisjoint C hCdisjoint
  have hQ0parts : Q0.parts = C := by
    dsimp [Q0]
    rw [Finpartition.ofPairwiseDisjoint_parts,
      Finset.erase_eq_of_notMem (by simpa using hCempty)]
  let Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E) := Q0.copy hcomp.symm
  have hQparts : Q.parts = C := by
    dsimp [Q]
    rw [Finpartition.copy_parts, hQ0parts]
  have hScard : #S = #Good * m := by
    calc
      #S = #(C.biUnion id) := by dsimp [S]; rw [Finset.sup_eq_biUnion]
      _ = ∑ W ∈ C, #W := Finset.card_biUnion hCdisjoint
      _ = #C * m := Finset.sum_const_nat fun W hW => (hCspec W hW).1
      _ = #Good * m := by rw [hCcard]
  refine ⟨E, Q, ?_, ?_, ?_⟩
  · rw [hQparts, hCcard]
    dsimp [Good]
    exact Finset.card_sdiff_of_subset hbadC
  · dsimp [E]
    rw [Finset.card_sdiff_of_subset hSuniv, Finset.card_univ, Fintype.card_fin,
      hScard]
    dsimp [Good, m]
    rw [Finset.card_sdiff_of_subset hbadC]
  · intro W hW
    rw [hQparts] at hW
    simpa [Good, m] using hCspec W hW

/-- Combined bad-cluster/bad-vertex cleanup for a regular equitable partition of a
finite `Fin n` host.  Besides constructing equal cleaned clusters, this theorem
retains the two pointwise incidence bounds needed by a degree-form regularity proof. -/
theorem IsUniform.exists_degree_cleanup_partition_fin
    {n r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    {η q : ℝ} (hequip : P.IsEquipartition) (hreg : P.IsUniform G η)
    (hη : 0 ≤ η) (hq : 0 < q) (hηq : η ≤ q ^ 2)
    (hcap : q * ((n / #P.parts + 1 : ℕ) : ℝ) ≤ (r : ℝ))
    (hr : r < n / #P.parts) :
    ∃ E : Finset (Fin n), ∃ Q : Finpartition (Finset.univ \ E),
      (#(P.badClusters G η q) : ℝ) < q * (#P.parts : ℝ) ∧
      #Q.parts = #P.parts - #(P.badClusters G η q) ∧
      #E = n - ((#P.parts - #(P.badClusters G η q)) *
        (n / #P.parts - r)) ∧
      ∀ W ∈ Q.parts,
        #W = n / #P.parts - r ∧
          ∃ U ∈ P.parts \ P.badClusters G η q,
            W ⊆ U \ P.upperBadVertices G η q U ∧
            (#(P.irregularPairsFrom G η U) : ℝ) ≤ q * (#P.parts : ℝ) ∧
            ∀ x ∈ W,
              (#(P.upperAtypicalPartnersAt G η U x) : ℝ) ≤
                q * (#P.parts : ℝ) := by
  classical
  have hk : 0 < #P.parts := by
    by_contra hk
    have hk0 : #P.parts = 0 := Nat.eq_zero_of_not_pos hk
    simp [hk0] at hr
  have hparts : P.parts.Nonempty := Finset.card_pos.1 hk
  have hbadC : P.badClusters G η q ⊆ P.parts := Finset.filter_subset _ _
  have hbadVsubset : ∀ U ∈ P.parts \ P.badClusters G η q,
      P.upperBadVertices G η q U ⊆ U := by
    intro U _
    exact Finset.filter_subset _ _
  have hbadVcard : ∀ U ∈ P.parts \ P.badClusters G η q,
      #(P.upperBadVertices G η q U) ≤ r := by
    intro U hU
    have hUP : U ∈ P.parts := (Finset.mem_sdiff.1 hU).1
    have htail := card_upperBadVertices_lt (G := G) (η := η) (q := q) (U := U)
      P hUP hη hq hηq
    have hUsize : #U ≤ n / #P.parts + 1 := by
      simpa using hequip.card_part_le_average_add_one hUP
    have htailr : (#(P.upperBadVertices G η q U) : ℝ) < (r : ℝ) :=
      htail.trans_le <| calc
        q * (#U : ℝ) ≤ q * ((n / #P.parts + 1 : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hUsize) hq.le
        _ ≤ (r : ℝ) := hcap
    have htailNat : #(P.upperBadVertices G η q U) < r := by exact_mod_cast htailr
    exact htailNat.le
  obtain ⟨E, Q, hQcard, hEcard, hQspec⟩ :=
    exists_cleaned_equal_partition_fin P hequip (P.badClusters G η q) hbadC
      (P.upperBadVertices G η q) hbadVsubset hbadVcard hr
  refine ⟨E, Q, hreg.card_badClusters_lt P hparts hη hq hηq,
    hQcard, hEcard, ?_⟩
  intro W hW
  obtain ⟨hWcard, U, hUgood, hWsub⟩ := hQspec W hW
  have hUP : U ∈ P.parts := (Finset.mem_sdiff.1 hUgood).1
  have hUnotbad : U ∉ P.badClusters G η q := (Finset.mem_sdiff.1 hUgood).2
  have hirregular : (#(P.irregularPairsFrom G η U) : ℝ) ≤
      q * (#P.parts : ℝ) := by
    apply le_of_not_gt
    intro hlarge
    exact hUnotbad (Finset.mem_filter.2 ⟨hUP, hlarge⟩)
  refine ⟨hWcard, U, hUgood, hWsub, hirregular, ?_⟩
  intro x hxW
  have hxavailable := hWsub hxW
  have hxU : x ∈ U := (Finset.mem_sdiff.1 hxavailable).1
  have hxnotbad : x ∉ P.upperBadVertices G η q U :=
    (Finset.mem_sdiff.1 hxavailable).2
  apply le_of_not_gt
  intro hlarge
  exact hxnotbad (Finset.mem_filter.2 ⟨hxU, hlarge⟩)

/-- Uniformity survives the equal-size trimming used above, with explicit global
size hypotheses.  Equitability reduces all four local size checks in the slicing
lemma to the two displayed inequalities. -/
theorem IsEquipartition.isUniform_of_cleaned_subsets_fin
    {n r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    {η η' : ℝ} (hequip : P.IsEquipartition) (hη : 0 ≤ η)
    (hlarge : ((n / #P.parts + 1 : ℕ) : ℝ) * η ≤
      ((n / #P.parts - r : ℕ) : ℝ))
    (hscale : ((n / #P.parts + 1 : ℕ) : ℝ) * η ≤
      ((n / #P.parts - r : ℕ) : ℝ) * η')
    (herror : 2 * η ≤ η')
    {U V W Z : Finset (Fin n)}
    (hU : U ∈ P.parts) (hV : V ∈ P.parts)
    (hWsub : W ⊆ U) (hZsub : Z ⊆ V)
    (hWcard : #W = n / #P.parts - r)
    (hZcard : #Z = n / #P.parts - r)
    (hUV : G.IsUniform η U V) :
    G.IsUniform η' W Z := by
  have hUsize : #U ≤ n / #P.parts + 1 := by
    simpa using hequip.card_part_le_average_add_one hU
  have hVsize : #V ≤ n / #P.parts + 1 := by
    simpa using hequip.card_part_le_average_add_one hV
  have hWcast : (#W : ℝ) = ((n / #P.parts - r : ℕ) : ℝ) := by
    exact_mod_cast hWcard
  have hZcast : (#Z : ℝ) = ((n / #P.parts - r : ℕ) : ℝ) := by
    exact_mod_cast hZcard
  have hUlarge : (#U : ℝ) * η ≤ (#W : ℝ) := by
    calc
      (#U : ℝ) * η ≤ ((n / #P.parts + 1 : ℕ) : ℝ) * η := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hUsize) hη
      _ ≤ ((n / #P.parts - r : ℕ) : ℝ) := hlarge
      _ = (#W : ℝ) := hWcast.symm
  have hVlarge : (#V : ℝ) * η ≤ (#Z : ℝ) := by
    calc
      (#V : ℝ) * η ≤ ((n / #P.parts + 1 : ℕ) : ℝ) * η := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hVsize) hη
      _ ≤ ((n / #P.parts - r : ℕ) : ℝ) := hlarge
      _ = (#Z : ℝ) := hZcast.symm
  have hUscale : (#U : ℝ) * η ≤ (#W : ℝ) * η' := by
    calc
      (#U : ℝ) * η ≤ ((n / #P.parts + 1 : ℕ) : ℝ) * η := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hUsize) hη
      _ ≤ ((n / #P.parts - r : ℕ) : ℝ) * η' := hscale
      _ = (#W : ℝ) * η' := by rw [hWcast]
  have hVscale : (#V : ℝ) * η ≤ (#Z : ℝ) * η' := by
    calc
      (#V : ℝ) * η ≤ ((n / #P.parts + 1 : ℕ) : ℝ) * η := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hVsize) hη
      _ ≤ ((n / #P.parts - r : ℕ) : ℝ) * η' := hscale
      _ = (#Z : ℝ) * η' := by rw [hZcast]
  exact SimpleGraph.IsUniform.mono_subsets hUV hWsub hZsub
    hUlarge hVlarge hUscale hVscale herror

end Finpartition

#print axioms SimpleGraph.IsUniform.mono_subsets
#print axioms Finpartition.IsUniform.exists_degree_cleanup_partition_fin
#print axioms Finpartition.IsEquipartition.isUniform_of_cleaned_subsets_fin
