import ErdosProblems.Erdos587.HooleyAdaptedSeed
import ErdosProblems.Erdos587.HooleySeedToGAP

/-! # Full-width extraction from a seed in the generated lattice -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

theorem delta_full_width_GAP_of_generated_lattice_seed (X : ConvexProgression)
    (Γ : AddSubgroup (Fin X.rank → ℤ)) (hfinite : Γ.FiniteIndex)
    (hperiod : ∀ i, intCastVec (Γ.index • Pi.single i (1 : ℤ)) ∈ X.body)
    (U : Finset (Fin X.rank → ℤ)) (hUΓ : ∀ u ∈ U, u ∈ Γ)
    (hUbody : ∀ u ∈ U, intCastVec u ∈ X.body)
    (f : (Fin X.rank → ℤ) →+ ℤ) (c : Γ.toIntSubmodule) (A : Finset ℤ)
    (hseed : ∀ w : Γ.toIntSubmodule,
      intCastVec w.val ∈ bodyDilate (deltaSeedLatticeFactor X.rank : ℝ) X.body →
        f (c.val + w.val) ∈ A.subsetSum)
    (hdisjoint : Disjoint A (U.image f)) (hU : 0 < U.card) (hinj : Set.InjOn f U)
    (hnonzero : ∃ u ∈ U, f u ≠ 0) (k : ℕ) (hk : 2 * k ≤ U.card)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤)
    (C : ℝ) (hC : 0 ≤ C) (hbaseMass : (f c.val : ℝ) ≤ C * ∑ u ∈ U, (f u : ℝ))
    (hlarge : 16 * ((4 ^ X.rank : ℕ) : ℝ) ≤
      (1 / ((4 ^ (X.rank + 1) : ℕ) : ℝ)) * U.card) :
    let K := ⌈32 * ((4 ^ X.rank : ℕ) : ℝ) / (1 / ((4 ^ (X.rank + 1) : ℕ) : ℝ))⌉₊
    let F := 9 * X.rank * K
    0 < F ∧ ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ X.rank ∧ Q.Proper ∧
      Q.HasHomogeneousBase ∧ (Q.carrier : Set ℤ) ⊆ ((A ∪ U.image f).subsetSum : Set ℤ) ∧
      (∀ i, U.card ≤ F * Q.length i) ∧
      U.card ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ ((C + 1 / 2) * K + 1) * Q.coefficientSpan := by
  classical
  let _ : Γ.FiniteIndex := hfinite
  obtain ⟨D⟩ := delta_exists_adapted_lattice_model X Γ hperiod
  let V := U.image D.coordinateMap
  let g := D.coordinateEval f
  have hψinj : Set.InjOn D.coordinateMap U := D.coordinateMap_injOn f U hUΓ hinj
  have hcard : V.card = U.card := Finset.card_image_of_injOn hψinj
  have heval (u) (hu : u ∈ U) : g (D.coordinateMap u) = f u :=
    D.coordinateEval_map f (hUΓ u hu)
  have himage : V.image g = U.image f := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun u hu => heval u hu)
  have hginj : Set.InjOn g V := by
    intro v hv w hw h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [heval u hu, heval z hz] at h
    exact congrArg D.coordinateMap (hinj hu hz h)
  have hsum : (∑ v ∈ V, (g v : ℝ)) = ∑ u ∈ U, (f u : ℝ) := by
    rw [Finset.sum_image hψinj]
    exact Finset.sum_congr rfl (fun u hu => by rw [heval u hu])
  have hbounds : ∀ v ∈ V, ∀ i, |(v i : ℝ)| ≤ D.bound i := by
    intro v hv i
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact D.coordinateMap_bound (hUΓ u hu) (hUbody u hu) i
  have hmass : (g (D.coordinates c) : ℝ) ≤ C * ∑ v ∈ V, (g v : ℝ) := by
    have hc : g (D.coordinates c) = f c.val := by
      change f (D.coordinates.symm (D.coordinates c)).val = f c.val
      rw [D.coordinates.symm_apply_apply]
    rwa [hc, hsum]
  have hnonzero' : ∃ v ∈ V, g v ≠ 0 := by
    obtain ⟨u, hu, hfu⟩ := hnonzero
    exact ⟨D.coordinateMap u, Finset.mem_image_of_mem _ hu, by rwa [heval u hu]⟩
  obtain ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩ :=
    delta_full_width_GAP_of_lattice_seed V g (D.coordinates c) A D.bound D.seedRadius
      D.bound_nonneg (fun i => (delta_adapted_seed_radius D i).1)
      (fun i => (delta_adapted_seed_radius D i).2) hbounds
      (delta_adapted_seed_coverage D f c A hseed) (by rwa [himage])
      (by rwa [hcard]) hginj hnonzero' k (by rwa [hcard])
      (D.robust_spanning_image U hUΓ k hspan) C hC hmass (by rwa [hcard])
  rw [himage] at hQsub
  rw [hcard] at hside hsize
  exact ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩

end Erdos587.GeneralizedAP
