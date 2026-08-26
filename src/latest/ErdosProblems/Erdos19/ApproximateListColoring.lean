import ErdosProblems.Erdos19.SparseForbiddenColoring
import ErdosProblems.Erdos19.FactorialSlack

/-!
# Approximate coloring with sparse forbidden sets

For fixed rank, slack, and a linear vertex-count bound, a small-codegree
hypergraph can be colored from a common palette of size `(1 + epsilon) * D`
while avoiding a sufficiently small forbidden set on every edge. The proof
uses the proved ordinary approximation theorem, a permutation count, and greedy
recoloring. No external list-coloring theorem is assumed.
-/

namespace Erdos19

open Erdos76 Erdos76.FiniteHypergraph

theorem bounded_approximate_coloring_avoiding_sparse
    (r C : ℕ) (hr : 0 < r) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E P : Type) [DecidableEq V] [Fintype E] [DecidableEq E]
        [Fintype P] [DecidableEq P],
        ∀ (H : FiniteHypergraph V E) (D : ℕ) (F : E → Finset P),
          D₀ ≤ D → H.IsBounded r → H.vertexSet.card ≤ C * D →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
            (H.edgePairDegree u v : ℝ) < delta * (D : ℝ)) →
          (∀ e, ((F e).card : ℝ) ≤ delta * (D : ℝ)) →
          (1 + epsilon) * (D : ℝ) ≤ Fintype.card P →
          ∃ c : H.conflictGraph.Coloring P, ∀ e, c e ∉ F e := by
  classical
  obtain ⟨delta₀, hdelta₀, D₀, hround⟩ :=
    bounded_approximate_edgeColoring r hr (epsilon / 4) (by positivity)
  let theta : ℝ := epsilon / (8 * ((r : ℝ) + 1))
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have htheta_eq : theta * (8 * ((r : ℝ) + 1)) = epsilon := by
    dsimp [theta]
    exact div_mul_cancel₀ _ (by positivity)
  let delta : ℝ := min delta₀ (theta / 16)
  have hdelta : 0 < delta := lt_min hdelta₀ (by positivity)
  have hdelta₀le : delta ≤ delta₀ := min_le_left _ _
  have hdeltatheta : delta ≤ theta / 16 := min_le_right _ _
  let threshold : ℝ := max (4 / theta)
    (max ((C : ℝ) / theta ^ 2) (8 * ((r : ℝ) + 1) / epsilon))
  obtain ⟨D₁, hD₁⟩ := exists_nat_ge threshold
  refine ⟨delta, hdelta, max D₀ D₁, ?_⟩
  intro V E P _ _ _ _ _ H D F hDlarge hbound hvertices hdegree hpair hF hpalette
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDlarge
  have hD₁le : D₁ ≤ D := (le_max_right _ _).trans hDlarge
  have hDreal : threshold ≤ (D : ℝ) := hD₁.trans (by exact_mod_cast hD₁le)
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDtheta : 4 / theta ≤ (D : ℝ) := (le_max_left _ _).trans hDreal
  have hDC : (C : ℝ) / theta ^ 2 ≤ (D : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hDreal)
  have hDepsilon : 8 * ((r : ℝ) + 1) / epsilon ≤ (D : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hDreal)
  have hfour : 4 ≤ theta * (D : ℝ) := by
    have h := (div_le_iff₀ htheta).mp hDtheta
    nlinarith
  have hC : (C : ℝ) ≤ (D : ℝ) * theta ^ 2 :=
    (div_le_iff₀ (pow_pos htheta 2)).mp hDC
  have hrounding : (r : ℝ) + 1 ≤ epsilon * (D : ℝ) / 8 := by
    have h := (div_le_iff₀ hepsilon).mp hDepsilon
    nlinarith
  let s : ℕ := ⌈theta * (D : ℝ)⌉₊
  let f : ℕ := ⌊delta * (D : ℝ)⌋₊
  have hslo : theta * (D : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  have hshi : (s : ℝ) ≤ theta * (D : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg htheta.le hDnonneg)).le
  have hfhi : (f : ℝ) ≤ delta * (D : ℝ) :=
    Nat.floor_le (mul_nonneg hdelta.le hDnonneg)
  have hs4 : 4 ≤ s := by exact_mod_cast hfour.trans hslo
  have hsize : H.vertexSet.card ≤ s ^ 2 := by
    have hsq : (theta * (D : ℝ)) ^ 2 ≤ (s : ℝ) ^ 2 := by
      gcongr
    have hprod := mul_le_mul_of_nonneg_right hC hDnonneg
    have hverticesR : (H.vertexSet.card : ℝ) ≤ (C : ℝ) * D := by
      exact_mod_cast hvertices
    have hfinal : (H.vertexSet.card : ℝ) ≤ (s : ℝ) ^ 2 := by
      nlinarith only [hsq, hprod, hverticesR]
    exact_mod_cast hfinal
  have h8f : 8 * f ≤ s := by
    have hprod := mul_le_mul_of_nonneg_right hdeltatheta hDnonneg
    have hfinal : (8 : ℝ) * f ≤ s := by
      nlinarith only [hprod, hfhi, hslo, hfour]
    exact_mod_cast hfinal
  have hsmall : H.vertexSet.card * f ^ s < s.factorial :=
    mul_pow_lt_factorial_of_square_bound hs4 hsize h8f
  have hFNat : ∀ e, (F e).card ≤ f := by
    intro e
    exact Nat.le_floor (hF e)
  have hpair₀ : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < delta₀ * (D : ℝ) := by
    intro u hu v hv huv
    exact (hpair u hu v hv huv).trans_le
      (mul_le_mul_of_nonneg_right hdelta₀le hDnonneg)
  obtain ⟨q, _, hq, ⟨c⟩⟩ := hround V E H D hD₀ hbound hdegree hpair₀
  have hrtheta : (r : ℝ) * theta ≤ epsilon / 8 := by
    nlinarith only [htheta_eq, htheta]
  have hthetale : theta ≤ epsilon / 8 := by
    have hnonneg : 0 ≤ (r : ℝ) * theta := mul_nonneg (Nat.cast_nonneg _) htheta.le
    nlinarith only [htheta_eq, hnonneg]
  have hdeltaeps : delta ≤ epsilon / 8 := by
    nlinarith only [hdeltatheta, hthetale, htheta]
  have htotal : q + (r * s + f + 1) ≤ Fintype.card P := by
    have hrshi := mul_le_mul_of_nonneg_left hshi (Nat.cast_nonneg r)
    have hrthetaD := mul_le_mul_of_nonneg_right hrtheta hDnonneg
    have hdeltaD := mul_le_mul_of_nonneg_right hdeltaeps hDnonneg
    have htotalR : (q : ℝ) + ((r : ℝ) * s + f + 1) ≤ (Fintype.card P : ℝ) := by
      nlinarith only [hq, hrshi, hfhi, hrthetaD, hdeltaD, hrounding, hpalette,
        mul_nonneg hepsilon.le hDnonneg]
    exact_mod_cast htotalR
  exact exists_edgeColoring_avoiding_sparse_palette H r f s q hbound c F hFNat hsmall htotal

#print axioms bounded_approximate_coloring_avoiding_sparse

end Erdos19
