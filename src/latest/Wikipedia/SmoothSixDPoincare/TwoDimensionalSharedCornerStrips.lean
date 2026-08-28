import Wikipedia.SmoothSixDPoincare.ConnectingArcTubularNeighborhood
import Wikipedia.SmoothSixDPoincare.TubularArcCorner
import Wikipedia.SmoothSixDPoincare.TubularArcStrip
import Wikipedia.SmoothSixDPoincare.FiniteTransverseIntersections
import Wikipedia.SmoothSixDPoincare.StripPairOverlap
import Wikipedia.SmoothSixDPoincare.StripPatchRestriction
import Wikipedia.SmoothSixDPoincare.ConstructedCleanBigonBoundary

/-!
# Shared native corner strips for sheets of dimension at least two

Construct both embedded arcs, their genuine inside-sheet tubular charts,
the two common clean corner maps, and both matching clean strips. The
second strip uses the same corner maps with swapped axes. The complete
clean cornered boundary neighborhood is constructed without prescribed
arc germs, initial charts, normal fields, or strips.

This includes two-plus-three sheets in dimension five. Filling the boundary
in the required sheet complement and constructing its Whitney framing
remain separate obligations.
-/

noncomputable section

open Set Function Module Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
  [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P]

/-- Construct shared clean strips and their whole boundary neighborhood in dimension two and up. -/
theorem exists_native_shared_corner_strip_pair_dim_two {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))
    (hdimD : 2 ≤ finrank ℝ D) (hdimZ : 2 ≤ finrank ℝ Z)
    (hcodim : finrank ℝ D + finrank ℝ Z = finrank ℝ E)
    (ht : ∀ x y, G y = F x → Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁)
    (hxy : x₀ ≠ x₁) (γ : Path x₀ x₁) (η : Path y₀ y₁) :
    ∃ f : C(ℝ, N), ∃ g : C(ℝ, P),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ g ∧
      f 0 = x₀ ∧ f 1 = x₁ ∧ g 0 = y₀ ∧ g 1 = y₁ ∧
      IsClosedEmbedding (fun t : unitInterval => f t) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) g t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, G (g t) ∉ range F) ∧
      range (fun t : unitInterval => F (f t)) ∩ range (fun t : unitInterval => G (g t)) =
        {F x₀, F x₁} ∧
      ∃ c₀ : CleanCornerPatch (E := E) (range F) (range G) (F ∘ f) (G ∘ g),
        ∃ c₁ : CleanCornerPatch (E := E) (range F) (range G)
            (fun t => F (f (1 - t))) (fun t => G (g (1 - t))),
          ∃ k : CleanStripPatch (E := E) (range F) (range G) (F ∘ f) c₀.map c₁.map,
            ∃ l : CleanStripPatch (E := E) (range G) (range F) (G ∘ g)
                c₀.swap.map c₁.swap.map,
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin (finrank ℝ D - 1)))
                (EuclideanSpace ℝ (Fin (finrank ℝ Z))) (E := E) (range F) k.map) ∧
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin (finrank ℝ Z - 1)))
                (EuclideanSpace ℝ (Fin (finrank ℝ D))) (E := E) (range G) l.map) ∧
              (∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
                p = q.swap ∨
                  StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) ∧
              ∀ h : ℝ, 0 < h →
                Nonempty (CleanBigonBoundary (E := E)
                  (range F) (range G) (F ∘ f) (G ∘ g) k.map l.map h) := by
  have hfinite : (range F ∩ range G).Finite :=
    finite_transverse_intersections hF hG hinjF hinjG hcodim ht
  have hSF : (F ⁻¹' range G).Finite := by
    have hpre : F ⁻¹' (range F ∩ range G) = F ⁻¹' range G := by
      ext z
      simp only [mem_preimage, mem_inter_iff]
      exact and_iff_right (mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjF.injOn
  have hSG : (G ⁻¹' range F).Finite := by
    have hpre : G ⁻¹' (range F ∩ range G) = G ⁻¹' range F := by
      ext z
      simp only [mem_preimage, mem_inter_iff]
      exact and_iff_left (mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjG.injOn
  have hy : y₀ ≠ y₁ := by
    intro heq
    apply hxy
    exact hinjF (hcross₀.symm.trans ((congrArg G heq).trans hcross₁))
  obtain ⟨f, hf, hf0, hf1, hembf, hif, havoidf, ρ, hρ, c, hsourceC, hzeroC, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero γ hxy hdimD
      (finrank ℝ D - 1) (by omega) hSF
  obtain ⟨g, hg, hg0, hg1, hembg, hig, havoidg, σ, hσ, d, hsourceD, hzeroD, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero η hy hdimZ
      (finrank ℝ Z - 1) (by omega) hSG
  have hinjf : InjOn f (Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembf.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinjg : InjOn g (Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembg.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinter :
      range (fun t : unitInterval => F (f t)) ∩ range (fun t : unitInterval => G (g t)) =
        {F x₀, F x₁} := by
    ext w
    constructor
    · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
      by_cases ht0 : (t : ℝ) = 0
      · simp only [ht0, hf0]
        exact mem_insert _ _
      by_cases ht1 : (t : ℝ) = 1
      · simp only [ht1, hf1]
        exact mem_insert_of_mem _ (mem_singleton _)
      have hti : (t : ℝ) ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
      exact (havoidf t hti ⟨g s, hs⟩).elim
    · intro hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨⟨0, congrArg F hf0⟩, ⟨0, (congrArg G hg0).trans hcross₀⟩⟩
      · exact ⟨⟨1, congrArg F hf1⟩, ⟨1, (congrArg G hg1).trans hcross₁⟩⟩
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  have hc₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, mem_closedBall_self hρ.le⟩
  have hc₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, mem_closedBall_self hρ.le⟩
  have hd₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, mem_closedBall_self hσ.le⟩
  have hd₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, mem_closedBall_self hσ.le⟩
  have hcross₀' : G (g 0) = F (f 0) := by rw [hf0, hg0]; exact hcross₀
  have hcross₁' : G (g 1) = F (f 1) := by rw [hf1, hg1]; exact hcross₁
  have ht₀ := ht (f 0) (g 0) hcross₀'
  have ht₁ := ht (f 1) (g 1) hcross₁'
  have hcoord : finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ D - 1))) +
      finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ Z - 1))) = finrank ℝ E := by
    simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
    omega
  have hcorner₀ : Nonempty (CleanCornerPatch (E := E) (range F) (range G) (F ∘ f) (G ∘ g)) := by
    simpa only [zero_add, mul_one, Function.comp_def] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD
        hc₀ hd₀ hcross₀' hcoord ht₀ (σ := 1) (τ := 1) one_ne_zero one_ne_zero
  have hcorner₁ : Nonempty (CleanCornerPatch (E := E) (range F) (range G)
      (fun t => F (f (1 - t))) (fun t => G (g (1 - t)))) := by
    simpa only [mul_neg_one, ← sub_eq_add_neg] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD
        hc₁ hd₁ hcross₁' hcoord ht₁ (σ := -1) (τ := -1) (by norm_num) (by norm_num)
  obtain ⟨c₀⟩ := hcorner₀
  obtain ⟨c₁⟩ := hcorner₁
  obtain ⟨stripF, hnormalF, _⟩ := exists_cleanStripPatch_of_tubular_arc_corners
    hF hG hembF hiF hf hinjf hif d hzeroD hd₀ hd₁ hcross₀' hcross₁' ht₀ ht₁
    (finrank ℝ D - 1) (by omega) hcodim hdimZ havoidf c₀ c₁ isOpen_univ
    (fun _ _ => mem_univ _)
  let DF₀ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)
  let DF₁ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)
  let DG₀ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0)
  let DG₁ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1)
  have ht₀' : Surjective (DG₀.coprod DF₀) :=
    TransverseCoordinates.surjective_coprod_swap DF₀ DG₀ ht₀
  have ht₁' : Surjective (DG₁.coprod DF₁) :=
    TransverseCoordinates.surjective_coprod_swap DF₁ DG₁ ht₁
  have hcodim' : finrank ℝ Z + finrank ℝ D = finrank ℝ E := by omega
  obtain ⟨stripG, hnormalG, _⟩ := exists_cleanStripPatch_of_tubular_arc_corners
    hG hF hembG hiG hg hinjg hig c hzeroC hc₀ hc₁ hcross₀'.symm hcross₁'.symm ht₀' ht₁'
    (finrank ℝ Z - 1) (by omega) hcodim' hdimD havoidg c₀.swap c₁.swap isOpen_univ
    (fun _ _ => mem_univ _)
  have hcoinc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (F ∘ f) t = (G ∘ g) s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
    intro t ht s hs heq
    have hmem : F (f t) ∈ ({F x₀, F x₁} : Set M) := by
      rw [← hinter]
      exact ⟨⟨⟨t, ht⟩, rfl⟩, ⟨⟨s, hs⟩, heq.symm⟩⟩
    change F (f t) = F x₀ ∨ F (f t) = F x₁ at hmem
    have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    rcases hmem with hleft | hright
    · left
      constructor
      · exact hinjf ht h0 (hinjF (hleft.trans (congrArg F hf0).symm))
      · apply hinjg hs h0
        apply hinjG
        exact heq.symm.trans (hleft.trans ((congrArg G hg0).trans hcross₀).symm)
    · right
      constructor
      · exact hinjf ht h1 (hinjF (hright.trans (congrArg F hf1).symm))
      · apply hinjg hs h1
        apply hinjG
        exact heq.symm.trans (hright.trans ((congrArg G hg1).trans hcross₁).symm)
  obtain ⟨ε', hε', δ', hδ', U', V', hU', hV', hrectU', hrectV', hU'sub, hV'sub,
      hoverlap⟩ := exists_clean_strip_pair_neighborhoods c₀ c₁ stripF stripG hcoinc
  let k' := stripF.restrict hε' hU' hrectU' hU'sub
  let l' := stripG.restrict hδ' hV' hrectV' hV'sub
  have hoverlap' : ∀ p ∈ k'.domain, ∀ q ∈ l'.domain, k'.map p = l'.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap := hoverlap
  refine ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg,
    hinter, c₀, c₁, k', l', hnormalF, hnormalG, hoverlap', ?_⟩
  intro h hh
  exact nonempty_cleanBigonBoundary hh c₀ c₁ k' l' hoverlap'

end Wikipedia.SmoothSixDPoincare
