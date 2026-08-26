import ErdosProblems.Erdos19.BufferedListColoring
import ErdosProblems.Erdos19.BufferCapacityParameters
import ErdosProblems.Erdos19.FiniteModel

/-! # Eventual sparse-list coloring with a buffer in every block

A fixed degree deficit on each disjoint buffer leaves a linear number of
vertices unused there by every color. All codegree and pool-size conditions
of the capacity construction are discharged.
-/

namespace Erdos19.SetHypergraph

open Finset Erdos76 Erdos76.FiniteHypergraph

attribute [local instance] Classical.propDecidable

theorem eventually_bounded_rank_buffered_lists (R s t : ℕ)
    (hR : 0 < R) (hs : 2 ≤ s) (ht : 0 < t)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, e.1.ncard ≤ R) →
      ∀ D : ℕ, n ≤ 2 * D → D ≤ n → (∀ v, (H.incidentEdges v).ncard ≤ D) →
      ∀ (I P : Type) [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P],
      ∀ B : I → Finset (Fin n),
        (Pairwise fun i j ↦ Disjoint (B i) (B j)) → (∀ i, n / t ≤ (B i).card) →
        (∀ i v, v ∈ B i → (H.incidentEdges v).ncard ≤ D - n / s) →
        ∀ F : H → Finset P, (∀ e, ((F e).card : ℝ) ≤ delta * n) →
          (1 + epsilon) * (D : ℝ) ≤ Fintype.card P →
          ∃ c : H.EdgeColoring P, (∀ e, c e ∉ F e) ∧
            ∀ i a, n / (16 * s * t) ≤
              (B i \ (H.coveredVertices {e | c e = a}).toFinset).card := by
  classical
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    bounded_approximate_buffered_coloring R 4 hR epsilon hepsilon
  obtain ⟨M, D₁, hcodegree⟩ := exists_codegree_parameter delta hdelta
  let Dmin := max D₀ (max D₁ 1)
  let overhead := 2 * R + (2 * R) * (2 * R * M)
  let N := max s (max (2 * Dmin) ((16 * s * t) * (overhead + 1)))
  refine ⟨delta / 2, by positivity, N, ?_⟩
  intro n hn H hlinear hmax D hDlow hDhigh hdegree I P _ _ _ _ B hB hBsize hlow F hF hpalette
  let q := n / (16 * s * t)
  let p : I → ℕ := fun i ↦ (B i).card - q
  let T : I → ℕ := fun i ↦ (B i).card * (D - n / s)
  have hspos : 0 < s := by omega
  have hDmin : Dmin ≤ D := by
    have h : 2 * Dmin ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
    omega
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDmin
  have hD₁ : D₁ ≤ D := ((le_max_left _ _).trans (le_max_right _ _)).trans hDmin
  have hDpos : 0 < D := ((le_max_right _ _).trans (le_max_right _ _)).trans hDmin
  have hns : s ≤ n := (le_max_left _ _).trans hn
  have hq : overhead + 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 16 * s * t)).mpr
    have h : (16 * s * t) * (overhead + 1) ≤ n :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hn
    simpa only [Nat.mul_comm] using h
  have hqB : ∀ i, q ≤ (B i).card := by
    intro i
    have h := scaled_floor_le_div n (16 * s) t ht
    change (16 * s) * q ≤ n / t at h
    have hsize := hBsize i
    nlinarith only [h, hsize, hs]
  obtain ⟨L, hL, hLsmall, hDM⟩ := hcodegree D hD₁ hDpos
  have hbound : H.finiteModel.IsBounded R := by
    intro e
    simpa only [H.finiteModel_support_card] using hmax e
  have hsumB : (∑ i : I, (B i).card) ≤ n := by
    have h := sum_inter_card_le_of_disjoint (univ : Finset (Fin n)) B hB
    simpa only [univ_inter, card_univ, Fintype.card_fin] using h
  have hvertices : H.finiteModel.vertexSet.card + (∑ i : I, p i) ≤ 4 * D := by
    have hsum : (∑ i : I, p i) ≤ ∑ i : I, (B i).card :=
      sum_le_sum (fun i _ ↦ Nat.sub_le _ _)
    rw [H.finiteModel_vertex_card, Fintype.card_fin]
    omega
  have hdegree' : ∀ v ∈ H.finiteModel.vertexSet, H.finiteModel.edgeDegree v ≤ D := by
    intro v _
    simpa only [H.finiteModel_edgeDegree] using hdegree v
  have hpair : ∀ u ∈ H.finiteModel.vertexSet, ∀ v ∈ H.finiteModel.vertexSet, u ≠ v →
      H.finiteModel.edgePairDegree u v ≤ L := by
    intro u _ v _ huv
    exact (H.finiteModel_edgePairDegree_le_one hlinear huv).trans hL
  have htotal : ∀ i, (∑ e : H, (H.finiteModel.support e ∩ B i).card) ≤ T i := by
    apply buffered_coloring_total_demand_of_low_degree
    intro i v hv
    simpa only [H.finiteModel_edgeDegree] using hlow i v hv
  have hroom : ∀ i, T i / D + 2 * R + (2 * R) * ((2 * R) * D / L) < p i := by
    intro i
    exact buffer_capacity_room n D (B i).card R L M s t hs ht hns hDpos hDlow hDhigh
      (hBsize i) hDM hq
  have hF' : ∀ e, ((F e).card : ℝ) ≤ delta * D := by
    intro e
    have hDlowR : (n : ℝ) ≤ 2 * D := by exact_mod_cast hDlow
    have hmul := mul_le_mul_of_nonneg_left hDlowR hdelta.le
    exact (hF e).trans (by nlinarith only [hmul])
  obtain ⟨c, hcF, hcBuffer⟩ := hround (Fin n) H I P H.finiteModel D L B p T F
    hD₀ hL hLsmall hbound hvertices hdegree' hpair hB htotal hroom hF' hpalette
  refine ⟨H.edgeColoringOfFiniteModel c, hcF, ?_⟩
  intro i a
  have hcap := hcBuffer i a
  have hp : (B i).card - p i = q := by dsimp only [p]; have := hqB i; omega
  rw [hp] at hcap
  have hset : B i \ ((univ.filter fun e ↦ c e = a).biUnion
        fun e ↦ H.finiteModel.support e ∩ B i) =
      B i \ (H.coveredVertices {e | (H.edgeColoringOfFiniteModel c) e = a}).toFinset := by
    ext v
    simp only [mem_sdiff]
    constructor
    · rintro ⟨hv, hnot⟩
      refine ⟨hv, ?_⟩
      intro hcov
      have hcov' := Set.mem_toFinset.mp hcov
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hcov'
      obtain ⟨hea, hve⟩ := Set.mem_iUnion.mp he
      apply hnot
      exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, hea⟩,
        mem_inter.mpr ⟨(H.finiteModel_mem_support e v).mpr hve, hv⟩⟩
    · rintro ⟨hv, hnot⟩
      refine ⟨hv, ?_⟩
      intro hcov
      obtain ⟨e, he, hve⟩ := mem_biUnion.mp hcov
      apply hnot
      apply Set.mem_toFinset.mpr
      exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨(mem_filter.mp he).2,
        (H.finiteModel_mem_support e v).mp (mem_inter.mp hve).1⟩⟩
  simpa only [hset] using hcap

#print axioms eventually_bounded_rank_buffered_lists

end Erdos19.SetHypergraph
