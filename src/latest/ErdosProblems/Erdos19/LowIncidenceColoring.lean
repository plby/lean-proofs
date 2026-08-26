import ErdosProblems.Erdos19.FiniteModel
import ErdosProblems.Erdos19.TotalIncidenceColoring
import ErdosProblems.Erdos19.LowIncidenceParameters

/-! # Almost full palettes with small color coverage

The degree deficit and the total-incidence bound have independent roles:
the former supplies the approximate-coloring slack, and the latter supplies
the dummy capacity needed to bound every color's covered vertices.
-/

namespace Erdos19.SetHypergraph

open Erdos76 Erdos76.FiniteHypergraph

theorem eventually_low_incidence_covered_lists (R s a : ℕ)
    (hR : 0 < R) (hs : 2 ≤ s) (ha : 0 < a) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, e.1.ncard ≤ R) →
      (∀ v, (H.incidentEdges v).ncard ≤ n - n / s) →
      16 * a * (∑ e : H, e.1.ncard) ≤ n ^ 2 →
      ∀ (P : Type) [Fintype P] [DecidableEq P], ∀ F : H → Finset P,
        (∀ e, ((F e).card : ℝ) ≤ delta * n) →
        n - n / (2 * s) ≤ Fintype.card P →
        ∃ c : H.EdgeColoring P, (∀ e, c e ∉ F e) ∧
          ∀ x, (H.coveredVertices {e : H | c e = x}).ncard ≤ n / a := by
  classical
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    bounded_approximate_covered_coloring_of_total_incidence R 4 hR
      (1 / (4 * (s : ℝ))) (by positivity)
  obtain ⟨M, D₁, hcodegree⟩ := exists_codegree_parameter delta hdelta
  let Dmin := max D₀ (max D₁ 1)
  let B := 2 * R + (2 * R) * (2 * R * M)
  let N := max (max s (2 * Dmin)) (a * (2 * B + 2))
  refine ⟨delta / 2, by positivity, N, ?_⟩
  intro n hn H hlinear hmax hdegree htotal P _ _ F hF hpalette
  let D := n - n / s
  let p := n / a
  let T := ∑ e : H, e.1.ncard
  have hDlower : n ≤ 2 * D := near_full_degree_lower n s hs
  have hDmin : Dmin ≤ D := by
    have h : 2 * Dmin ≤ n :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hn
    omega
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDmin
  have hD₁ : D₁ ≤ D := ((le_max_left _ _).trans (le_max_right _ _)).trans hDmin
  have hDpos : 0 < D := ((le_max_right _ _).trans (le_max_right _ _)).trans hDmin
  have hp : 2 * B + 2 ≤ p := by
    apply (Nat.le_div_iff_mul_le ha).mpr
    have h : a * (2 * B + 2) ≤ n := (le_max_right _ _).trans hn
    simpa only [Nat.mul_comm] using h
  obtain ⟨L, hL, hLsmall, hDM⟩ := hcodegree D hD₁ hDpos
  have hbound : H.finiteModel.IsBounded R := by
    intro e
    simpa only [H.finiteModel_support_card] using hmax e
  have hvertices : H.finiteModel.vertexSet.card + p ≤ 4 * D := by
    rw [H.finiteModel_vertex_card, Fintype.card_fin]
    have hp' : p ≤ n := Nat.div_le_self _ _
    omega
  have hdegree' : ∀ v ∈ H.finiteModel.vertexSet, H.finiteModel.edgeDegree v ≤ D := by
    intro v _
    simpa only [H.finiteModel_edgeDegree] using hdegree v
  have htotal' : (∑ e : H, (H.finiteModel.support e).card) ≤ T := by
    simp only [H.finiteModel_support_card, T, le_refl]
  have hpair : ∀ u ∈ H.finiteModel.vertexSet, ∀ v ∈ H.finiteModel.vertexSet, u ≠ v →
      H.finiteModel.edgePairDegree u v ≤ L := by
    intro u _ v _ huv
    exact (H.finiteModel_edgePairDegree_le_one hlinear huv).trans hL
  have hroom : T / D + 2 * R + (2 * R) * ((2 * R) * D / L) < p :=
    total_incidence_capacity_room n D T a R L M ha hDpos hDlower htotal hDM hp
  have hF' : ∀ e, ((F e).card : ℝ) ≤ delta * D := by
    intro e
    have hDlowerR : (n : ℝ) ≤ 2 * D := by exact_mod_cast hDlower
    have hmul := mul_le_mul_of_nonneg_left hDlowerR hdelta.le
    exact (hF e).trans (by nlinarith only [hmul])
  have hpalette' : (1 + 1 / (4 * (s : ℝ))) * (D : ℝ) ≤ Fintype.card P := by
    have hsn : s ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
    exact (near_full_palette_slack n s hs hsn).trans (by exact_mod_cast hpalette)
  obtain ⟨c, hcF, hcCover⟩ := hround (Fin n) H P H.finiteModel D L T p F
    hD₀ hL hLsmall hbound hvertices hdegree' htotal' hpair hroom hF' hpalette'
  refine ⟨H.edgeColoringOfFiniteModel c, hcF, ?_⟩
  intro x
  simpa only [H.finiteModel_covered_card, edgeColoringOfFiniteModel, p] using hcCover x

#print axioms eventually_low_incidence_covered_lists

end Erdos19.SetHypergraph
