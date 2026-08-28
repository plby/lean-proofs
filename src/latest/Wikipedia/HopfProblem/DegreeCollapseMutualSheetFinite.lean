import Wikipedia.HopfProblem.DegreeCollapseMutualSheetStep
import Mathlib.Data.Set.Card

/-!
# Finite reduction of the actual signed mutual intersections

Repeat constructed ambient Whitney moves until no opposite signs remain.
The original second sheet is fixed, every surviving first-map germ is
retained, and the signed count is unchanged. The endpoint crossing set
therefore has cardinality equal to the absolute original integer count.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare
open OrbitPair.DeterminantSignCover

variable {D E M N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [T2Space N] [CompactSpace N] [PathConnectedSpace N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space P] [CompactSpace P] [PathConnectedSpace P]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, D) N))
  (oP : Orientation (tangentBundleCore 𝓘(ℝ, D) P))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (K : (D × D) ≃L[ℝ] E)

theorem finite_crossingPoints
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    {F : N → M} {G : P → M}
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G) (hinjG : Injective G)
    (hgood : Good (D := D) (E := E) G F) : (crossingPoints F G).Finite := by
  obtain ⟨hF, hinjF, _, ht⟩ := hgood
  have hcodim : Module.finrank ℝ D + Module.finrank ℝ D = Module.finrank ℝ E := by omega
  have hfin := finite_transverse_intersections hF hG hinjF hinjG hcodim ht
  have he : F ⁻¹' (range F ∩ range G) = crossingPoints F G := by
    ext x
    change (F x ∈ range F ∧ F x ∈ range G) ↔ F x ∈ range G
    exact and_iff_right (mem_range_self x)
  rw [← he]
  exact hfin.preimage hinjF.injOn

def signedCount (F : N → M) (G : P → M) (hf : (crossingPoints F G).Finite) : ℤ :=
  ∑ x ∈ hf.toFinset, (pointSign oN oP oM K F G x : ℤ)

open Classical in
theorem exists_finite_reduction
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    (G : C(P, M)) (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G) (hinjG : Injective G)
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (s : Finset N) (F : C(N, M)) (hs : (s : Set N) = crossingPoints F G)
    (hgood : Good (D := D) (E := E) G F) :
    ∃ ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ F' : C(N, M), ∃ s' : Finset N,
        SupportedDiffeomorph.IsotopicToIdentity ψ ∧ (∀ x, F' x = ψ (F x)) ∧
        Good (D := D) (E := E) G F' ∧
        (s' : Set N) = crossingPoints F' G ∧ s' ⊆ s ∧
        (∀ x ∈ s', (F' : N → M) =ᶠ[𝓝 x] F) ∧
        (∑ x ∈ s', (pointSign oN oP oM K F' G x : ℤ)) =
          ∑ x ∈ s, (pointSign oN oP oM K F G x : ℤ) ∧
        ∀ x ∈ s', ∀ y ∈ s',
          pointSign oN oP oM K F' G x * pointSign oN oP oM K F' G y ≠ -1 := by
  induction s using Finset.strongInductionOn generalizing F with
  | _ s ih =>
    by_cases hpair : ∃ x ∈ s, ∃ y ∈ s,
        pointSign oN oP oM K F G x * pointSign oN oP oM K F G y = -1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
      obtain ⟨ψ₁, F₁, hiso₁, heq₁, hgood₁, hpoints, hgerm₁, hsign₁⟩ :=
        exists_signed_cancellation_step oN oP oM K hdim hsheet F G hG hinjG hiG hgood
          x y (hs ▸ hx) (hs ▸ hy) hxy
      let r : Finset N := s \ {x, y}
      have hr : (r : Set N) = crossingPoints F₁ G := by
        rw [hpoints, ← hs]
        simp only [r, Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
      have hsum₁ : (∑ z ∈ r, (pointSign oN oP oM K F₁ G z : ℤ)) =
          ∑ z ∈ s, (pointSign oN oP oM K F G z : ℤ) :=
        FiniteSignedCancellation.sum_sdiff_pair_of_eq s
          (pointSign oN oP oM K F G) (pointSign oN oP oM K F₁ G) hx hy hxy
          (fun z hz => hsign₁ z (hr ▸ hz))
      have hsubpair : ({x, y} : Finset N) ⊆ s := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_singleton.mp hz ▸ hy
      have hrlt : r ⊂ s := Finset.sdiff_ssubset hsubpair ⟨x, by simp⟩
      obtain ⟨ψ₂, F₂, s₂, hiso₂, heq₂, hgood₂, hs₂, hsub₂, hgerm₂, hsum₂, hno₂⟩ :=
        ih r hrlt F₁ hr hgood₁
      refine ⟨ψ₁.trans ψ₂, F₂, s₂, hiso₁.trans hiso₂, ?_, hgood₂, hs₂,
        hsub₂.trans Finset.sdiff_subset, ?_, hsum₂.trans hsum₁, hno₂⟩
      · intro z
        change F₂ z = ψ₂ (ψ₁ (F z))
        rw [heq₂, heq₁]
      · intro z hz
        exact (hgerm₂ z hz).trans (hgerm₁ z (hr ▸ hsub₂ hz))
    · refine ⟨Diffeomorph.refl _ _ _, F, s, SupportedDiffeomorph.isotopicToIdentity_refl,
        fun _ => rfl, hgood, hs, fun _ hx => hx, fun _ _ => Filter.EventuallyEq.refl _ _,
        rfl, ?_⟩
      intro x hx y hy hxy
      exact hpair ⟨x, hx, y, hy, hxy⟩

open Classical in
theorem exists_minimal_crossing_sheet
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    (F : C(N, M)) (G : C(P, M))
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G) (hinjG : Injective G)
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (hgood : Good (D := D) (E := E) G F) :
    ∃ ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∃ F' : C(N, M),
      SupportedDiffeomorph.IsotopicToIdentity ψ ∧ (∀ x, F' x = ψ (F x)) ∧
      Good (D := D) (E := E) G F' ∧ crossingPoints F' G ⊆ crossingPoints F G ∧
      (∀ x ∈ crossingPoints F' G, (F' : N → M) =ᶠ[𝓝 x] F) ∧
      (crossingPoints F' G).ncard =
        (signedCount oN oP oM K F G (finite_crossingPoints hdim hsheet hG hinjG hgood)).natAbs := by
  let hfin := finite_crossingPoints hdim hsheet hG hinjG hgood
  obtain ⟨ψ, F', s', hiso, heq, hgood', hs', hsub, hgerm, hsum, hno⟩ :=
    exists_finite_reduction oN oP oM K hdim hsheet G hG hinjG hiG
      hfin.toFinset F hfin.coe_toFinset hgood
  have hmem (x : N) (hx : x ∈ crossingPoints F' G) : x ∈ s' := by
    change x ∈ (s' : Set N)
    rw [hs']
    exact hx
  refine ⟨ψ, F', hiso, heq, hgood', ?_, fun x hx => hgerm x (hmem x hx), ?_⟩
  · intro x hx
    exact hfin.mem_toFinset.mp (hsub (hmem x hx))
  · calc
      (crossingPoints F' G).ncard = s'.card := by rw [← hs', Set.ncard_coe_finset]
      _ = (∑ x ∈ s', (pointSign oN oP oM K F' G x : ℤ)).natAbs :=
        FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite s'
          (pointSign oN oP oM K F' G) (fun x _ => pointSign_unit oN oP oM K F' G x) hno
      _ = _ := congrArg Int.natAbs hsum

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
