import ErdosProblems.Erdos538.DaisyPalettePattern
import ErdosProblems.Erdos538.IntegerLayerLower

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

noncomputable section
open Erdos538.IsotropicKernel

/-- The weighted-support selection predicate is exactly the daisy multiset
pattern after composing the coloring with the chosen palette permutation. -/
theorem paletteSelected_iff_daisyPalettePattern
    (k m : ℕ) (hk : 0 < k) (c : ℕ → Fin m)
    (σ : Equiv.Perm (Fin m))
    (F : Finset (UniformChildren m (k - 1))) (S : Finset ℕ) :
    PaletteSelected k m hk c σ F S ↔
      DaisyPalettePattern k m F
        (supportSignature (fun x => σ (c x)) S) := by
  classical
  constructor
  · rintro ⟨hr, hF⟩
    refine ⟨?_, ?_, ⟨σ • rainbowChild k m hk c S hr, hF, ?_⟩⟩
    · change (S.1.map (σ ∘ c)).Nodup
      rw [← Multiset.map_map]
      exact Multiset.nodup_map_iff_of_injective σ.injective |>.mpr hr.1
    · simp [supportSignature, hr.2]
    · apply Finset.ext
      intro y
      change y ∈ (S.image c).map σ.toEmbedding ↔
        y ∈ (supportSignature (σ ∘ c) S).toFinset
      simp only [Finset.mem_map, Finset.mem_image, Multiset.mem_toFinset,
        supportSignature, Multiset.toFinset_map]
      constructor
      · rintro ⟨z, ⟨a, ha, hca⟩, hzy⟩
        refine ⟨a, ha, ?_⟩
        change σ (c a) = y
        rw [hca]
        exact hzy
      · rintro ⟨a, ha, hca⟩
        exact ⟨c a, ⟨a, ha, rfl⟩, hca⟩
  · rintro ⟨hnodup, hcard, E, hEF, hE⟩
    have hcNodup : (S.1.map c).Nodup := by
      change (S.1.map (σ ∘ c)).Nodup at hnodup
      rw [← Multiset.map_map] at hnodup
      exact (Multiset.nodup_map_iff_of_injective σ.injective).mp hnodup
    have hScard : S.card = k := by
      simpa [supportSignature] using hcard
    let hr : RainbowSupport k c S := ⟨hcNodup, hScard⟩
    refine ⟨hr, ?_⟩
    have hchild : σ • rainbowChild k m hk c S hr = E := by
      apply Subtype.ext
      rw [hE]
      apply Finset.ext
      intro y
      change y ∈ (S.image c).map σ.toEmbedding ↔
        y ∈ (supportSignature (σ ∘ c) S).toFinset
      simp only [Finset.mem_map, Finset.mem_image, Multiset.mem_toFinset,
        supportSignature, Multiset.toFinset_map]
      constructor
      · rintro ⟨z, ⟨a, ha, hca⟩, hzy⟩
        refine ⟨a, ha, ?_⟩
        change σ (c a) = y
        rw [hca]
        exact hzy
      · rintro ⟨a, ha, hca⟩
        exact ⟨c a, ⟨a, ha, rfl⟩, hca⟩
    exact hchild ▸ hEF

/-- Every squarefree exact-`k` integer layer with `k≥2` has an admissible
cap-two subfamily retaining at least a `1/(128k)` share of reciprocal mass. -/
theorem exists_admissible_squarefreeLayer_linear_with_subset
    (N k : ℕ) (hk : 2 ≤ k) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      A ⊆ squarefreePrimeLayer N k ∧
      reciprocalMassNN (squarefreePrimeLayer N k) ≤
        (128 * k) • reciprocalMassNN A := by
  classical
  let layer := squarefreePrimeLayer N k
  let supports := layer.image Nat.primeFactors
  let w := primeSupportPushWeight layer
  have hsub : ∀ S ∈ supports, S ⊆ Finset.range (N + 1) := by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
    exact primeFactors_subset_range_succ_of_mem_layer hn
  have hcard : ∀ S ∈ supports, S.card = k := by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
    exact (Finset.mem_filter.mp hn).2.2
  obtain ⟨c, σ, F, hdense, hcap, hmass⟩ :=
    exists_weighted_linear_palette (N + 1) k hk supports w hsub hcard
  let color : ℕ → Fin (2 * k * k) := fun x => σ (c x)
  let P := DaisyPalettePattern k (2 * k * k) F
  let A := patternIntegerFamily N color P
  have hPattern : PatternCap 2 P :=
    daisyPalette_patternCap_two k (2 * k * k) (by omega) F hcap
  have hAdm : Admissible 2 N A :=
    patternIntegerFamily_admissible_of_patternCap (by omega) color P hPattern
  have htotal : (∑ S ∈ supports, w S) = reciprocalMassNN layer := by
    simpa [supports, w] using sum_primeSupportPushWeight layer
  have hselected : weightedSupportMass supports
      (PaletteSelected k (2 * k * k) (by omega) c σ F) w =
      ∑ n ∈ layer with P (supportSignature color n.primeFactors),
        (1 : ℚ≥0) / n := by
    have hfilter := sum_primeSupportPushWeight_filter layer
      (fun S => P (supportSignature color S))
    have hpred : ∀ S : Finset ℕ,
        PaletteSelected k (2 * k * k) (by omega) c σ F S ↔
          P (supportSignature color S) := by
      intro S
      exact paletteSelected_iff_daisyPalettePattern
        k (2 * k * k) (by omega) c σ F S
    calc
      weightedSupportMass supports
          (PaletteSelected k (2 * k * k) (by omega) c σ F) w =
          weightedSupportMass supports
            (fun S => P (supportSignature color S)) w := by
        unfold weightedSupportMass
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hs : PaletteSelected k (2 * k * k) (by omega) c σ F S
        · have hp := (hpred S).mp hs
          simp [hs, hp]
        · have hp : ¬ P (supportSignature color S) :=
            fun hp => hs ((hpred S).mpr hp)
          simp [hs, hp]
      _ = weightedFilterMass layer
          (fun n => P (supportSignature color n.primeFactors))
          (fun n => (1 : ℚ≥0) / n) := by
        simpa [supports, w] using hfilter
      _ = ∑ n ∈ layer with P (supportSignature color n.primeFactors),
          (1 : ℚ≥0) / n := rfl
  have hA : A = layer.filter fun n =>
      P (supportSignature color n.primeFactors) := by
    ext n
    simp only [A, P, patternIntegerFamily, layer, squarefreePrimeLayer,
      Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hsq, hselect⟩
      have hkcard : n.primeFactors.card = k := by
        simpa [supportSignature] using hselect.2.1
      exact ⟨⟨⟨hn1, hnN⟩, hsq, hkcard⟩, hselect⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hsq, hkcard⟩, hselect⟩
      exact ⟨⟨hn1, hnN⟩, hsq, hselect⟩
  have hAsub : A ⊆ squarefreePrimeLayer N k := by
    rw [hA]
    exact Finset.filter_subset _ _
  refine ⟨A, hAdm, hAsub, ?_⟩
  rw [htotal, hselected] at hmass
  simpa [reciprocalMassNN, hA] using hmass

end

end Erdos538
