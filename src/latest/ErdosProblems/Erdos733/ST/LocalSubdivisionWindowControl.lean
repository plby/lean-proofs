import ErdosProblems.Erdos733.ST.PolygonalPath
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Convex

open Classical
noncomputable section

-- [TABLET NODE: LocalSubdivisionWindowControl]
lemma LocalSubdivisionWindowControl
    (U : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath) (δ : ℝ) :
    IsOpen U →
      γ.carrier ⊆ U →
        0 < δ →
          ∃ ρ : ℝ, 0 < ρ ∧
            ∀ anchors xs : List (EuclideanSpace ℝ (Fin 2)),
              xs.length = anchors.length →
                (∀ (i : ℕ) (hi : i + 1 < anchors.length),
                  segment ℝ anchors[i] anchors[i + 1] ⊆ γ.carrier) →
                  (∀ (i : ℕ) (hxi : i < xs.length) (hai : i < anchors.length),
                    dist xs[i] anchors[i] < ρ) →
                    (({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                        {p : EuclideanSpace ℝ (Fin 2) |
                          ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                            p ∈ segment ℝ xs[i] xs[i + 1]}) ⊆ U ∧
                      (({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                          {p : EuclideanSpace ℝ (Fin 2) |
                            ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                              p ∈ segment ℝ xs[i] xs[i + 1]}) ⊆
                        {p : EuclideanSpace ℝ (Fin 2) |
                          ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ γ.carrier ∧ dist p q < δ} := by
-- BODY
  intro hU hγU hδ
  let E := EuclideanSpace ℝ (Fin 2)
  have compact_segment : ∀ x y : E, IsCompact (segment ℝ x y) := by
    intro x y
    rw [segment_eq_image' ℝ x y]
    exact (isCompact_Icc.image (by fun_prop : Continuous (fun θ : ℝ => x + θ • (y - x))))
  have hγcompact : IsCompact γ.carrier := by
    rw [γ.carrier_eq]
    apply IsCompact.union
    · exact (((Set.finite_singleton γ.target).insert γ.source).isCompact)
    · let idxSet : Set ℕ := {i | i + 1 < γ.vertices.length}
      have hidx_finite : Set.Finite idxSet := by
        refine (Set.finite_lt_nat γ.vertices.length).subset ?_
        intro i hi
        exact Nat.lt_of_succ_lt hi
      haveI : Finite {i : ℕ // i + 1 < γ.vertices.length} := hidx_finite
      rw [show {p : E | ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
            p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1]} =
          (⋃ i : {i : ℕ // i + 1 < γ.vertices.length},
            segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1]) by
        ext p
        simp]
      apply isCompact_iUnion
      intro i
      exact compact_segment γ.vertices[i.1] γ.vertices[i.1 + 1]
  obtain ⟨η, hηpos, hηU⟩ := hγcompact.exists_thickening_subset_open hU hγU
  let ρ : ℝ := min η δ / 2
  have hminpos : 0 < min η δ := lt_min hηpos hδ
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_min : ρ < min η δ := by
    dsimp [ρ]
    linarith
  have hρη : ρ < η := lt_of_lt_of_le hρ_lt_min (min_le_left η δ)
  have hρδ : ρ < δ := lt_of_lt_of_le hρ_lt_min (min_le_right η δ)
  have hsource_carrier : γ.source ∈ γ.carrier := by
    rw [γ.carrier_eq]
    left
    simp
  have htarget_carrier : γ.target ∈ γ.carrier := by
    rw [γ.carrier_eq]
    left
    simp
  have segment_near :
      ∀ {a b x y p : E},
        dist x a < ρ → dist y b < ρ → p ∈ segment ℝ x y →
          ∃ q ∈ segment ℝ a b, dist p q < ρ := by
    intro a b x y p hx hy hp
    rcases hp with ⟨s, t, hs, ht, hst, rfl⟩
    let q : E := s • a + t • b
    have hq : q ∈ segment ℝ a b := ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨q, hq, ?_⟩
    have hle : dist (s • x + t • y) q ≤ s * dist x a + t * dist y b := by
      dsimp [q]
      calc
        dist (s • x + t • y) (s • a + t • b)
            = ‖s • (x - a) + t • (y - b)‖ := by
              rw [dist_eq_norm]
              congr 1
              module
        _ ≤ ‖s • (x - a)‖ + ‖t • (y - b)‖ := norm_add_le _ _
        _ = s * dist x a + t * dist y b := by
          rw [norm_smul_of_nonneg hs, norm_smul_of_nonneg ht]
          rw [dist_eq_norm x a, dist_eq_norm y b]
    have hlt : s * dist x a + t * dist y b < ρ := by
      by_cases hs0 : s = 0
      · have ht1 : t = 1 := by nlinarith
        rw [hs0, ht1]
        simpa using hy
      · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
        have h1 : s * dist x a < s * ρ := mul_lt_mul_of_pos_left hx hspos
        have h2 : t * dist y b ≤ t * ρ := mul_le_mul_of_nonneg_left (le_of_lt hy) ht
        have hlt_sum : s * dist x a + t * dist y b < s * ρ + t * ρ :=
          add_lt_add_of_lt_of_le h1 h2
        have hsumρ : s * ρ + t * ρ = ρ := by
          calc
            s * ρ + t * ρ = (s + t) * ρ := by ring
            _ = ρ := by rw [hst, one_mul]
        exact hsumρ ▸ hlt_sum
    exact lt_of_le_of_lt hle hlt
  refine ⟨ρ, hρpos, ?_⟩
  intro anchors xs hlen hanchors hclose
  constructor
  · intro p hp
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp
    rcases hp with hp_end | hp_seg
    · rcases hp_end with rfl | rfl
      · exact hγU hsource_carrier
      · exact hγU htarget_carrier
    · rcases hp_seg with ⟨i, hi, hpseg⟩
      have hxi : i < xs.length := Nat.lt_of_succ_lt hi
      have hxnext : i + 1 < xs.length := hi
      have hainext : i + 1 < anchors.length := by
        simpa [hlen] using hi
      have hai : i < anchors.length := Nat.lt_of_succ_lt hainext
      obtain ⟨q, hqseg, hpq⟩ :=
        segment_near (hclose i hxi hai) (hclose (i + 1) hxnext hainext) hpseg
      have hqγ : q ∈ γ.carrier := hanchors i hainext hqseg
      apply hηU
      rw [Metric.mem_thickening_iff]
      exact ⟨q, hqγ, lt_trans hpq hρη⟩
  · intro p hp
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp
    rcases hp with hp_end | hp_seg
    · rcases hp_end with rfl | rfl
      · exact ⟨γ.source, hsource_carrier, by simpa using hδ⟩
      · exact ⟨γ.target, htarget_carrier, by simpa using hδ⟩
    · rcases hp_seg with ⟨i, hi, hpseg⟩
      have hxi : i < xs.length := Nat.lt_of_succ_lt hi
      have hxnext : i + 1 < xs.length := hi
      have hainext : i + 1 < anchors.length := by
        simpa [hlen] using hi
      have hai : i < anchors.length := Nat.lt_of_succ_lt hainext
      obtain ⟨q, hqseg, hpq⟩ :=
        segment_near (hclose i hxi hai) (hclose (i + 1) hxnext hainext) hpseg
      exact ⟨q, hanchors i hainext hqseg, lt_trans hpq hρδ⟩
