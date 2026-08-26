import ErdosProblems.Erdos19.LowIncidenceExtension
import ErdosProblems.Erdos19.ProjectiveCompletionParameters
import ErdosProblems.Erdos19.SubhypergraphStarCompletion
import ErdosProblems.Erdos19.EdgeIncidenceSums

/-! # Completing the small edges in the low-incidence case

Only pairs touching vertices of large graph degree are reserved. All other
small edges are colored by the proved sparse-list capacity theorem. A palette
kept out of that coloring then completes the reserved stars by Hall's theorem.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_complete_low_incidence_small_edges (R : ℕ) (hR : 3 ≤ R) :
    ∃ ell N : ℕ, 2 ≤ ell ∧ ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, 2 ≤ e.1.ncard) →
      ∀ color : (H.rankAtLeast R).EdgeColoring (Fin n), ∀ B : Finset (Fin n),
        B.card ≤ n / 128 →
        (∀ a, ((H.rankAtLeast R).coveredVertices {e | color e = a}).ncard ≤ n / 256) →
        (∀ e : H.rankAtLeast R, color e ∉ B → ell * R ≤ e.1.ncard) →
        65536 * (∑ e : H.rankBelow R, e.1.ncard) ≤ n ^ 2 →
        H.EdgeColorable n := by
  classical
  obtain ⟨ell₀, N₀, hell₀, hN₀⟩ :=
    eventually_color_low_incidence_around_large_palette R 8 1024
      (by omega) (by norm_num) (by norm_num)
  let ell := max ell₀ 1025
  refine ⟨ell, max N₀ 1, hell₀.trans (le_max_left _ _), ?_⟩
  intro n hn H hlinear hmin color B hB hcover hlarge htotal
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (le_max_right _ _).trans hn
  let L := H.rankAtLeast R
  let M := H.rankBelow R
  let U := H.highPairVertices (n - 2 * (n / 8))
  let K : SetHypergraph (Fin n) := M ∩ H.pairStarRemainder (U : Set (Fin n))
  have hLM : L.IsLinear := H.rankAtLeast_linear hlinear R
  have hKH : K ⊆ H := fun _ he ↦ he.1.1
  have hKM : K ⊆ M := Set.inter_subset_left
  have hKstar : K ⊆ H.pairStarRemainder (U : Set (Fin n)) := Set.inter_subset_right
  have hKlinear : K.IsLinear := hlinear.mono hKH
  have hpairs : ∀ e ∈ H, e.ncard = 2 → e ∈ M := by
    intro e he hsize
    exact ⟨he, by omega⟩
  have hU : U.card ≤ n / 1024 :=
    H.highPairVertices_small_of_low_incidence n hnpos M hpairs htotal
  obtain ⟨reserved, palette, hreserved, hreservedB, hpalette, hpaletteB, hpaletteR⟩ :=
    exists_small_completion_palettes n B hB
  have hminPalette : ∀ e : L, color e ∈ palette → ell₀ * R ≤ e.1.ncard := by
    intro e he
    exact (Nat.mul_le_mul_right R (le_max_left _ _)).trans
      (hlarge e (disjoint_left.mp hpaletteB he))
  have hKmax : ∀ e : K, e.1.ncard ≤ R := fun e ↦ e.2.1.2.le
  have hKdegree : ∀ v, (K.incidentEdges v).ncard ≤ n - n / 8 := by
    intro v
    exact (incident_degree_mono hKstar v).trans
      (H.pairStarRemainder_degree_le n 8 (by norm_num) hlinear hmin v)
  have hKtotal : 16 * 1024 * (∑ e : K, e.1.ncard) ≤ n ^ 2 := by
    have hsum := sum_edge_weight_mono hKM (fun e ↦ e.ncard)
    nlinarith only [hsum, htotal]
  obtain ⟨cK, hcompatible, hKcover⟩ := hN₀ n hn₀ L K hLM hKlinear color palette
    hminPalette hKmax hKdegree hKtotal (by simpa only [Nat.reduceMul] using hpalette)
  have hbounded : L.IsCoverBoundedColoring color (n / 256) := fun a ↦ Or.inr (hcover a)
  obtain ⟨cJ, hagree, hnew, hcoverJ, _⟩ := L.extend_coloring_into_palette K n
    (n / 256) (n / 1024) color hbounded palette cK hcompatible hKcover
  have hmissing : ∀ e ∈ H, e ∉ L ∪ K → e.ncard = 2 ∧ ∃ v ∈ U, v ∈ e := by
    intro e he hnot
    have heL : e ∉ L := fun h ↦ hnot (Or.inl h)
    have heM : e ∈ M := ⟨he, by
      by_contra h
      exact heL ⟨he, Nat.le_of_not_gt h⟩⟩
    have heK : e ∉ K := fun h ↦ hnot (Or.inr h)
    have hpair : e.ncard = 2 := by
      by_contra h
      exact heK ⟨heM, he, fun h' ↦ (h h').elim⟩
    refine ⟨hpair, ?_⟩
    by_contra hno
    apply heK
    refine ⟨heM, he, fun _ v hv hvU ↦ ?_⟩
    exact hno ⟨v, hvU, hv⟩
  have hJcover : ∀ a, ((L ∪ K).coveredVertices {e | cJ e = a}).ncard ≤
      n / 256 + n / 1024 := by
    intro a
    exact (hcoverJ a).trans (Nat.add_le_add_right (hcover a) _)
  have hlarge1025 : 1025 ≤ ell * R := by
    have hell : 1025 ≤ ell := le_max_right _ _
    nlinarith only [hell, hR]
  have hreserveRank : ∀ e : ↥(L ∪ K), cJ e ∈ reserved → 1025 ≤ e.1.ncard := by
    intro e he
    by_cases heL : e.1 ∈ L
    · have hc : cJ e = color ⟨e.1, heL⟩ := hagree ⟨e.1, heL⟩
      have hnotB : color ⟨e.1, heL⟩ ∉ B :=
        disjoint_left.mp hreservedB (by simpa only [hc] using he)
      exact hlarge1025.trans (hlarge ⟨e.1, heL⟩ hnotB)
    · have hp : cJ e ∈ palette := hnew ⟨e.1, e.2.resolve_left heL⟩ heL
      exact (disjoint_left.mp hpaletteR hp he).elim
  have hslack : (n / 256 + n / 1024) + 2 * ((n - 1) / (1025 - 1)) +
      4 * U.card ≤ reserved.card := by
    rw [hreserved]
    apply pair_star_completion_slack
    · norm_num only [Nat.reduceSub]
      exact Nat.div_le_div_right (Nat.sub_le n 1)
    · exact hU
  obtain ⟨c, _⟩ := H.exists_coloring_completing_pair_stars (L ∪ K) hlinear hmin n hnpos
    (Fintype.card_fin n) cJ U hmissing reserved (n / 256 + n / 1024) 1025
    (by norm_num) hJcover hreserveRank hslack
  exact ⟨c⟩

#print axioms eventually_complete_low_incidence_small_edges

end Erdos19.SetHypergraph
