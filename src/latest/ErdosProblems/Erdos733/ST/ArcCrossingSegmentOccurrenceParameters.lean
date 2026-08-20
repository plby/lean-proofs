import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalPath
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingSegmentOccurrenceParameters]
lemma ArcCrossingSegmentOccurrenceParameters
    (γ : PolygonalArc) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length) :
    Set.Finite (α.carrier ∩ γ.carrier) →
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ γ.carrier) →
        ∃ params : List ℝ,
          params.Nodup ∧
            params.SortedLT ∧
              (∀ t : ℝ, t ∈ params ↔
                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
                  openSegment ℝ α.vertices[i] α.vertices[i + 1] ∩ γ.carrier) ∧
                (∀ t : ℝ, t ∈ params → 0 < t ∧ t < 1) ∧
                  (∀ x : EuclideanSpace ℝ (Fin 2),
                    x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                      x ∈ γ.carrier →
                        ∃ t : ℝ,
                          t ∈ params ∧ 0 < t ∧ t < 1 ∧
                            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t = x) ∧
                    (∀ n (hn : n + 1 < params.length), params[n] < params[n + 1]) ∧
                      (∀ n (hn : n + 1 < params.length) t,
                        0 < t → t < 1 →
                          AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
                            γ.carrier →
                            ¬ (params[n] < t ∧ t < params[n + 1])) := by
-- BODY
  intro hfinite hverticesAvoid
  let E := EuclideanSpace ℝ (Fin 2)
  let A : E := α.vertices[i]
  let B : E := α.vertices[i + 1]
  have hA_mem : A ∈ α.vertices :=
    List.getElem_mem (l := α.vertices) (n := i) (Nat.lt_of_succ_lt hi)
  have hB_mem : B ∈ α.vertices :=
    List.getElem_mem (l := α.vertices) (n := i + 1) hi
  have hA_notγ : A ∉ γ.carrier := hverticesAvoid A hA_mem
  have hB_notγ : B ∉ γ.carrier := hverticesAvoid B hB_mem
  by_cases hABeq : A = B
  · refine ⟨[], by simp, List.Pairwise.nil.sortedLT, ?_, ?_, ?_, ?_, ?_⟩
    · intro t
      constructor
      · intro ht
        simp at ht
      · intro ht
        have hline : AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t = B := by
          simp [A, B, hABeq]
        exact (hB_notγ (by simpa [hline] using ht.2)).elim
    · intro t ht
      simp at ht
    · intro x hxOpen hxγ
      have hx_eq : x = B := by simpa [A, B, hABeq] using hxOpen
      exact (hB_notγ (by simpa [hx_eq] using hxγ)).elim
    · intro n hn
      simp at hn
    · intro n hn t _ht0 _ht1 _htγ
      simp at hn
  · have hAB : A ≠ B := hABeq
    let X : Set E := openSegment ℝ A B ∩ γ.carrier
    have hXfinite : Set.Finite X := by
      refine hfinite.subset ?_
      intro z hz
      have hzseg : z ∈ segment ℝ A B := openSegment_subset_segment ℝ A B hz.1
      have hzα : z ∈ α.carrier := by
        rw [α.carrier_eq]
        right
        exact ⟨i, hi, by simpa [A, B] using hzseg⟩
      exact ⟨hzα, hz.2⟩
    let f : ℝ → E := fun t => AffineMap.lineMap A B t
    let Xfin : Finset E := hXfinite.toFinset
    let pulled : Finset ℝ := Xfin.preimage f (AffineMap.lineMap_injective ℝ hAB).injOn
    let params : List ℝ := pulled.sort (· ≤ ·)
    have hmemX : ∀ t : ℝ, t ∈ params ↔ f t ∈ X := by
      intro t
      dsimp [params, pulled, Xfin]
      rw [Finset.mem_sort, Finset.mem_preimage]
      exact Set.Finite.mem_toFinset hXfinite
    have hmem : ∀ t : ℝ, t ∈ params ↔
        AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
          openSegment ℝ α.vertices[i] α.vertices[i + 1] ∩ γ.carrier := by
      intro t
      simpa [X, f, A, B] using hmemX t
    have hbounds : ∀ t : ℝ, t ∈ params → 0 < t ∧ t < 1 := by
      intro t ht
      have hftX : f t ∈ X := (hmemX t).mp ht
      have hftOpen : f t ∈ openSegment ℝ A B := hftX.1
      rw [openSegment_eq_image_lineMap] at hftOpen
      rcases hftOpen with ⟨s, hsIoo, hsf⟩
      have hs_eq_t : s = t :=
        (AffineMap.lineMap_injective ℝ hAB) (by simpa [f] using hsf)
      simpa [hs_eq_t] using hsIoo
    have hno_between :
        ∀ n (hn : n + 1 < params.length) t,
          t ∈ params → ¬ (params[n] < t ∧ t < params[n + 1]) := by
      intro n hn t ht hbetween
      rcases List.mem_iff_get.mp ht with ⟨k, hk⟩
      subst t
      have hmono : StrictMono params.get := by
        simpa [params] using (Finset.sortedLT_sort pulled).strictMono_get
      by_cases hkn : k ≤ n
      · have hle : params.get k ≤ params.get ⟨n, Nat.lt_of_succ_lt hn⟩ := by
          by_cases heq : k = ⟨n, Nat.lt_of_succ_lt hn⟩
          · simp [heq]
          · have hlt : k < ⟨n, Nat.lt_of_succ_lt hn⟩ := lt_of_le_of_ne hkn heq
            exact (hmono hlt).le
        exact not_lt_of_ge hle hbetween.1
      · have hle_k : ⟨n + 1, hn⟩ ≤ k :=
          Nat.succ_le_of_lt (lt_of_not_ge hkn)
        have hle : params.get ⟨n + 1, hn⟩ ≤ params.get k := by
          by_cases heq : ⟨n + 1, hn⟩ = k
          · simp [heq]
          · have hlt : ⟨n + 1, hn⟩ < k := lt_of_le_of_ne hle_k heq
            exact (hmono hlt).le
        exact not_lt_of_ge hle hbetween.2
    refine ⟨params, Finset.sort_nodup pulled (· ≤ ·), ?_, hmem, hbounds, ?_, ?_, ?_⟩
    · simpa [params] using Finset.sortedLT_sort pulled
    · intro x hxOpen hxγ
      rw [openSegment_eq_image_lineMap] at hxOpen
      rcases hxOpen with ⟨t, htIoo, htx⟩
      have ht_mem : t ∈ params := by
        apply (hmemX t).mpr
        have htOpen : f t ∈ openSegment ℝ A B := by
          simpa [f] using lineMap_mem_openSegment (𝕜 := ℝ) A B htIoo
        exact ⟨htOpen, by simpa [f, ← htx] using hxγ⟩
      exact ⟨t, ht_mem, htIoo.1, htIoo.2, by simpa [A, B, f] using htx⟩
    · intro n hn
      have hmono : StrictMono params.get := by
        simpa [params] using (Finset.sortedLT_sort pulled).strictMono_get
      exact hmono (by simp [Fin.lt_def])
    · intro n hn t ht0 ht1 htγ hbetween
      have htOpen : AffineMap.lineMap A B t ∈ openSegment ℝ A B :=
        lineMap_mem_openSegment (𝕜 := ℝ) A B ⟨ht0, ht1⟩
      have ht_mem : t ∈ params := (hmemX t).mpr ⟨htOpen, htγ⟩
      exact hno_between n hn t ht_mem hbetween
