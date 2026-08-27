import ErdosProblems.Erdos587.HooleySeedProgression
import ErdosProblems.Erdos587.HooleyRobustConvexExtraction

/-! # From a robust full lattice seed to a full-width homogeneous subset-sum GAP -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

theorem delta_full_width_GAP_of_lattice_seed {d : ℕ} (U : Finset (Fin d → ℤ))
    (f : (Fin d → ℤ) →+ ℤ) (c₀ : Fin d → ℤ) (A : Finset ℤ)
    (L R : Fin d → ℝ) (hL : ∀ i, 0 ≤ L i) (hR : ∀ i, 2 ≤ R i)
    (hRcube : ∀ i, (4 : ℝ) ^ (d + 2) ≤ 2 * R i)
    (hUbound : ∀ u ∈ U, ∀ i, |(u i : ℝ)| ≤ L i)
    (hseed : ∀ w : Fin d → ℤ, (∀ i, |(w i : ℝ)| ≤ R i + (d : ℝ) * L i + 1 / 2) →
      f (c₀ + w) ∈ A.subsetSum)
    (hdisjoint : Disjoint A (U.image f)) (hU : 0 < U.card) (hinj : Set.InjOn f U)
    (hnonzero : ∃ u ∈ U, f u ≠ 0) (k : ℕ) (hk : 2 * k ≤ U.card)
    (hspan : ∀ V ⊆ U, k ≤ V.card → Submodule.span ℝ (intCastVec '' (V : Set (Fin d → ℤ))) = ⊤)
    (C : ℝ) (hC : 0 ≤ C) (hbaseMass : (f c₀ : ℝ) ≤ C * ∑ u ∈ U, (f u : ℝ))
    (hlarge : 16 * ((4 ^ d : ℕ) : ℝ) ≤
      (1 / ((4 ^ (d + 1) : ℕ) : ℝ)) * U.card) :
    let K := ⌈32 * ((4 ^ d : ℕ) : ℝ) / (1 / ((4 ^ (d + 1) : ℕ) : ℝ))⌉₊
    let F := 9 * d * K
    0 < F ∧ ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ d ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      (Q.carrier : Set ℤ) ⊆ ((A ∪ U.image f).subsetSum : Set ℤ) ∧
      (∀ i, U.card ≤ F * Q.length i) ∧
      U.card ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ ((C + 1 / 2) * K + 1) * Q.coefficientSpan := by
  classical
  let v : U → Fin d → ℤ := fun u => u.val
  obtain ⟨c, hc, hcenter⟩ := delta_exists_lower_half_center v f
  let Y := deltaSeedProgression v f (c₀ + c) R hR
  have himage : Finset.univ.image (fun u : U => f (v u)) = U.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image_of_mem f u.property
    · intro hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩
  have hv : ∀ u i, |(v u i : ℝ)| ≤ L i := fun u i => hUbound u u.property i
  have hvinj : Function.Injective (fun u : U => f (v u)) := by
    intro u w h
    exact Subtype.ext (hinj u.property w.property h)
  have hYsub : Y.carrier ⊆ ((A ∪ U.image f).subsetSum : Set ℤ) := by
    have hh := deltaSeedProgression_carrier_subset v f c₀ c L R hL hR hv hc A hseed hvinj
      (by rwa [himage])
    rwa [himage] at hh
  have hsum : (∑ u : U, (f (v u) : ℝ)) = ∑ u ∈ U, (f u : ℝ) :=
    Finset.sum_coe_sort U (fun u => (f u : ℝ))
  have hYmass : (Y.base : ℝ) ≤ (C + 1 / 2) * ∑ u ∈ U, (f u : ℝ) := by
    have hh := deltaSeedProgression_base_mass v f c₀ c R hR C (by rwa [hsum]) hcenter
    rwa [hsum] at hh
  have hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension (LinearMap.id : (Fin d → ℤ) →ₗ[ℤ] _) e ∈
        bodyDilate (1 / 4 ^ (Y.rank + 2)) Y.body := by
    intro e he
    rw [delta_intLinearMapRealExtension_id, LinearMap.id_apply]
    exact deltaSeedBody_small_cube v R hRcube e he
  have hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin d → ℤ)),
      (1 : ℝ) • x ∈ Y.body := by
    intro x hx
    rw [one_smul]
    exact deltaSeedBody_zonotope v R (fun i => by linarith [hR i]) hx
  have hnonzero' : ∃ u, Y.eval u ≠ 0 := by
    obtain ⟨u, _, hu⟩ := hnonzero
    exact ⟨u, hu⟩
  obtain ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hcard, hheight⟩ :=
    delta_robust_convex_extraction Y (LinearMap.id : (Fin d → ℤ) →ₗ[ℤ] _)
      Function.surjective_id hcube U hU hinj hnonzero' k hk hspan (by norm_num : (0 : ℝ) < 1)
      (by linarith : (0 : ℝ) ≤ C + 1 / 2) hsub ⟨c₀ + c, rfl⟩ hYmass hlarge
  exact ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub.trans hYsub, hside, hcard, hheight⟩

end Erdos587.GeneralizedAP
