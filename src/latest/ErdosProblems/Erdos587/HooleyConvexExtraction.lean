import ErdosProblems.Erdos587.HooleyFullWidthBox
import ErdosProblems.Erdos587.HooleyBasisSpan

/-! # Full-width, large-cardinality, bounded-height extraction from a robust convex progression -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

theorem delta_full_width_convex_extraction (X : ConvexProgression) (hX : 0 < X.rank)
    (U : Finset (Fin X.rank → ℤ)) (hU : 0 < U.card) (k : ℕ) (hk : 2 * k ≤ U.card)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin X.rank → ℤ)),
      δ • x ∈ X.body)
    (hround : ∀ x : Fin X.rank → ℝ, ∃ v : Fin X.rank → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) X.body)
    (hproper : X.SProper 1) (hbase : ∃ c : Fin X.rank → ℤ, X.eval c = X.base)
    (hbaseMass : (X.base : ℝ) ≤ C * ∑ u ∈ U, (X.eval u : ℝ))
    (hlarge : 16 * ((4 ^ X.rank : ℕ) : ℝ) ≤ δ * U.card) :
    let K := ⌈32 * ((4 ^ X.rank : ℕ) : ℝ) / δ⌉₊
    let F := 9 * X.rank * K
    0 < F ∧ ∃ Q : GeneralizedAP, Q.rank = X.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      (Q.carrier : Set ℤ) ⊆ X.carrier ∧ (∀ i, U.card ≤ F * Q.length i) ∧
      U.card ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ (C * K + 1) * Q.coefficientSpan := by
  obtain ⟨D, hDscale, _henergy⟩ := MahlerBoxData.exists_adapted X
  have hlargeD : 16 * (D.scale : ℝ) ≤ δ * U.card := by rwa [hDscale]
  obtain ⟨hF, Q, hQrank, hQproper, hQhom, hQsub, hside, hcard, hQeq⟩ :=
    delta_full_width_adapted_inner_box X hX D U hU k hk hspan hδ hsub hround
      hproper hbase hlargeD
  let K := ⌈32 * (D.scale : ℝ) / δ⌉₊
  let R : Fin X.rank → ℕ := fun i => ⌊D.bound i / D.scale⌋₊
  have hmass (i : Fin X.rank) :
      (∑ u ∈ U, ((|latticeCoordinates D.basis u i| : ℤ) : ℝ)) ≤ (K : ℝ) * R i := by
    have hwidth := delta_adapted_width_of_robust_spanning X D U k hk hspan hδ hsub hround i
    have hrounded := (delta_inner_radius_budgets D.scale_pos hU hδ hwidth hlargeD).2
    calc
      _ ≤ 4 * D.bound i / δ := delta_adapted_coordinate_mass X D U hδ hsub hround i
      _ ≤ 8 * D.bound i / δ :=
        div_le_div_of_nonneg_right (by have := D.bound_nonneg i; linarith) hδ.le
      _ ≤ (⌈8 * D.bound i / δ⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (K : ℝ) * R i := by
        have hroundedK : ⌈8 * D.bound i / δ⌉₊ ≤ K * R i := hrounded
        exact_mod_cast hroundedK
  have hheight : (Q.upperEndpoint : ℝ) ≤ (C * K + 1) * Q.coefficientSpan := by
    rw [hQeq]
    exact deltaBasisBox_height_of_coordinate_mass X D.basis U R hC (Nat.cast_nonneg K)
      hmass hbaseMass
  refine ⟨?_, Q, hQrank, hQproper, hQhom, hQsub, ?_, ?_, ?_⟩
  · simpa only [hDscale] using hF
  · simpa only [hDscale] using hside
  · simpa only [hDscale] using hcard
  · simpa only [K, hDscale] using hheight

end Erdos587.GeneralizedAP
