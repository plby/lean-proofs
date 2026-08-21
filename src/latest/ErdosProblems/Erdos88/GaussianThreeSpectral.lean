import ErdosProblems.Erdos88.GaussianNonuniformSmallCoordinates

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

noncomputable def threeSpectralEnvelope (s t : ℝ) : ℝ :=
  (1 + 4 * s * t ^ 2) ^ (-3 / 4 : ℝ)

noncomputable def threeSpectralMass : ℝ :=
  ∫ t : ℝ, (1 + t ^ 2) ^ (-3 / 4 : ℝ)

lemma threeSpectralBase_integrable :
    Integrable (fun t : ℝ ↦ (1 + t ^ 2) ^ (-3 / 4 : ℝ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq
    (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num)
  convert h using 1 <;> norm_num [Real.norm_eq_abs, sq_abs]

lemma threeSpectralEnvelope_nonneg {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    0 ≤ threeSpectralEnvelope s t := by
  unfold threeSpectralEnvelope
  exact Real.rpow_nonneg (by positivity) _

lemma threeSpectralEnvelope_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (threeSpectralEnvelope s) := by
  let R : ℝ := (2 * Real.sqrt s)⁻¹
  let g : ℝ → ℝ := fun t ↦ (1 + t ^ 2) ^ (-3 / 4 : ℝ)
  have hR : R ≠ 0 := by
    dsimp only [R]
    positivity
  have hg : Integrable g := by
    exact threeSpectralBase_integrable
  have hscaled := hg.comp_div hR
  refine hscaled.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [g, R]
  unfold threeSpectralEnvelope
  congr 1
  field_simp [(Real.sqrt_pos.2 hs).ne']
  rw [Real.sq_sqrt hs.le]
  ring

lemma threeSpectralMass_nonneg : 0 ≤ threeSpectralMass := by
  unfold threeSpectralMass
  apply integral_nonneg
  intro t
  exact Real.rpow_nonneg (by positivity) _

lemma integral_threeSpectralEnvelope {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, threeSpectralEnvelope s t) =
      threeSpectralMass / (2 * Real.sqrt s) := by
  let R : ℝ := (2 * Real.sqrt s)⁻¹
  let g : ℝ → ℝ := fun t ↦ (1 + t ^ 2) ^ (-3 / 4 : ℝ)
  have hfun : threeSpectralEnvelope s = fun t ↦ g (t / R) := by
    funext t
    dsimp only [g, R]
    unfold threeSpectralEnvelope
    congr 1
    field_simp [(Real.sqrt_pos.2 hs).ne']
    rw [Real.sq_sqrt hs.le]
    ring
  rw [hfun, Measure.integral_comp_div g R, abs_of_pos (by positivity : 0 < R)]
  dsimp only [R, g, threeSpectralMass]
  rw [smul_eq_mul]
  field_simp [(Real.sqrt_pos.2 hs).ne']

theorem diagonalCharModulus_le_threeSpectralEnvelope
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 3)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) (t : ℝ) :
    diagonalCharModulus a lam t ≤ threeSpectralEnvelope s t := by
  have h := diagonalCharModulus_le_of_spectralBlocks
    a lam B hdisj hs hblock t
  rw [hcard] at h
  norm_num [threeSpectralEnvelope] at h ⊢
  exact h

theorem diagonalCenteredCharProduct_integrable_of_three_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 3)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    Integrable (diagonalCenteredCharProduct a lam) := by
  apply (threeSpectralEnvelope_integrable hs).mono
  · exact (continuous_diagonalCenteredCharProduct a lam).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_diagonalCenteredCharProduct, Real.norm_eq_abs,
      abs_of_nonneg (threeSpectralEnvelope_nonneg hs.le t)]
    exact diagonalCharModulus_le_threeSpectralEnvelope
      a lam B hcard hdisj hs.le hblock t

lemma abs_inverseFourierDensityCandidate_le_of_three_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 3)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    (u : ℝ) :
    |inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) u| ≤
      threeSpectralMass / (4 * Real.pi * Real.sqrt s) := by
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate phi
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_three_spectralBlocks
      a lam B hcard hdisj hs hblock
  have hInv : HasInverseFourierDensity p phi :=
    inverseFourierDensityCandidate_hasInverse
      (diagonalCenteredCharProduct_neg a lam)
  have hphase (t : ℝ) :
      ‖phi t * Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))‖ =
        ‖phi t‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hnormInt : (∫ t : ℝ, ‖phi t‖) ≤
      threeSpectralMass / (2 * Real.sqrt s) := by
    calc
      (∫ t : ℝ, ‖phi t‖) ≤ ∫ t : ℝ, threeSpectralEnvelope s t := by
        apply integral_mono hchar.norm (threeSpectralEnvelope_integrable hs)
        intro t
        dsimp only [phi]
        rw [norm_diagonalCenteredCharProduct]
        exact diagonalCharModulus_le_threeSpectralEnvelope
          a lam B hcard hdisj hs.le hblock t
      _ = threeSpectralMass / (2 * Real.sqrt s) :=
        integral_threeSpectralEnvelope hs
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hInv u, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ t : ℝ, phi t * Complex.exp
          (-(((t * u : ℝ) : ℂ) * Complex.I))‖ ≤
        (2 * Real.pi)⁻¹ *
          ∫ t : ℝ, ‖phi t * Complex.exp
            (-(((t * u : ℝ) : ℂ) * Complex.I))‖ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖phi t‖ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hphase
    _ ≤ (2 * Real.pi)⁻¹ *
        (threeSpectralMass / (2 * Real.sqrt s)) := by gcongr
    _ = threeSpectralMass / (4 * Real.pi * Real.sqrt s) := by
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hs).ne']
      ring

theorem smallBall_diagonalCenteredLaw_le_of_three_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 3)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      eps * threeSpectralMass / (2 * Real.pi * Real.sqrt s) := by
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  let phi := diagonalCenteredCharProduct a lam
  let p := inverseFourierDensityCandidate (charFun (diagonalCenteredLaw a lam))
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_three_spectralBlocks
      a lam B hcard hdisj hs hblock
  have hlawChar : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw]
    exact hchar
  have hdens : Erdos88.Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p :=
    hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) hlawChar
  rw [hdens.smallBall_eq_integral eps x heps]
  calc
    (∫ y in (x - eps)..(x + eps), p y) ≤
        ∫ _y in (x - eps)..(x + eps),
          (threeSpectralMass / (4 * Real.pi * Real.sqrt s) : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.continuous.intervalIntegrable _ _) intervalIntegrable_const
      intro y hy
      exact (le_abs_self (p y)).trans (by
        dsimp only [p]
        rw [charFun_diagonalCenteredLaw]
        exact abs_inverseFourierDensityCandidate_le_of_three_spectralBlocks
          a lam B hcard hdisj hs hblock y)
    _ = eps * threeSpectralMass / (2 * Real.pi * Real.sqrt s) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hs).ne']
      ring

private lemma exists_three_disjoint_blocks_of_sum
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (S : Finset ι) {c : ℝ} (hc : 0 < c)
    (hsmall : ∀ i ∈ S, w i < c)
    (hsum : 6 * c ≤ ∑ i ∈ S, w i) :
    ∃ B : Fin 3 → Finset ι,
      Set.PairwiseDisjoint (Set.univ : Set (Fin 3)) B ∧
        ∀ j, c ≤ ∑ i ∈ B j, w i := by
  classical
  obtain ⟨B0, hB0S, hB0c, hB0lt⟩ :=
    exists_subset_sum_between_one_two_public w S hc hsmall (by linarith)
  let S1 := S \ B0
  have hsumS1 : ∑ i ∈ S1, w i =
      (∑ i ∈ S, w i) - ∑ i ∈ B0, w i := by
    exact Finset.sum_sdiff_eq_sub (f := w) hB0S
  have h4 : 4 * c ≤ ∑ i ∈ S1, w i := by linarith
  have hsmall1 : ∀ i ∈ S1, w i < c := fun i hi ↦
    hsmall i (Finset.sdiff_subset hi)
  obtain ⟨B1, hB1S1, hB1c, hB1lt⟩ :=
    exists_subset_sum_between_one_two_public w S1 hc hsmall1 (by linarith)
  let S2 := S1 \ B1
  have hsumS2 : ∑ i ∈ S2, w i =
      (∑ i ∈ S1, w i) - ∑ i ∈ B1, w i := by
    exact Finset.sum_sdiff_eq_sub (f := w) hB1S1
  have h2 : 2 * c ≤ ∑ i ∈ S2, w i := by linarith
  have hsmall2 : ∀ i ∈ S2, w i < c := fun i hi ↦
    hsmall1 i (Finset.sdiff_subset hi)
  obtain ⟨B2, hB2S2, hB2c, hB2lt⟩ :=
    exists_subset_sum_between_one_two_public w S2 hc hsmall2 (by linarith)
  have hd01 : Disjoint B0 B1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    exact (Finset.mem_sdiff.mp (hB1S1 hx1)).2 hx0
  have hd02 : Disjoint B0 B2 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx2
    have hxS1 := Finset.sdiff_subset (hB2S2 hx2)
    exact (Finset.mem_sdiff.mp hxS1).2 hx0
  have hd12 : Disjoint B1 B2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp (hB2S2 hx2)).2 hx1
  have hd10 : Disjoint B1 B0 := hd01.symm
  have hd20 : Disjoint B2 B0 := hd02.symm
  have hd21 : Disjoint B2 B1 := hd12.symm
  let B : Fin 3 → Finset ι := fun j ↦
    if j = 0 then B0 else if j = 1 then B1 else B2
  refine ⟨B, ?_, ?_⟩
  · intro i hi j hj hij
    change Disjoint (B i) (B j)
    fin_cases i <;> fin_cases j <;> simp_all [B]
  · intro j
    fin_cases j <;> simp only [B, Fin.zero_eta, ↓reduceIte, OfNat.ofNat]
    all_goals assumption

theorem exists_three_disjoint_blocks_of_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      s ≤ ∑ i with i ∉ S, w i) :
    ∃ B : Fin 3 → Finset ι,
      Set.PairwiseDisjoint (Set.univ : Set (Fin 3)) B ∧
        ∀ j, s / 6 ≤ ∑ i ∈ B j, w i := by
  classical
  let c : ℝ := s / 6
  let L : Finset ι := Finset.univ.filter fun i ↦ c ≤ w i
  have hc : 0 < c := by dsimp only [c]; positivity
  by_cases hthree : 3 ≤ L.card
  · obtain ⟨T, hTL, hTcard⟩ := Finset.exists_subset_card_eq hthree
    let e : Fin 3 ≃ T := (Finset.equivFinOfCardEq hTcard).symm
    let B : Fin 3 → Finset ι := fun j ↦ {(e j).1}
    refine ⟨B, ?_, ?_⟩
    · intro i hi j hj hij
      simp only [B, Finset.disjoint_singleton]
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    · intro j
      simp only [B, Finset.sum_singleton]
      have hejL : (e j : ι) ∈ L := hTL (e j).property
      exact (Finset.mem_filter.mp hejL).2
  · have hLcard : L.card ≤ 2 := by omega
    have htailL := htail L hLcard
    let S : Finset ι := Finset.univ \ L
    have hsumS : 6 * c ≤ ∑ i ∈ S, w i := by
      have hcEq : 6 * c = s := by dsimp only [c]; ring
      rw [hcEq]
      have hset : Finset.univ.filter (fun i ↦ i ∉ L) = S := by
        ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_sdiff, true_and]
      simpa only [hset] using htailL
    have hsmall : ∀ i ∈ S, w i < c := by
      intro i hi
      have hiL : i ∉ L := (Finset.mem_sdiff.mp hi).2
      simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and,
        not_le] using hiL
    simpa only [c] using
      exists_three_disjoint_blocks_of_sum w S hc hsmall hsumS

theorem smallBall_diagonalCenteredLaw_le_of_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      s ≤ ∑ i with i ∉ S, (lam i) ^ 2)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      eps * threeSpectralMass /
        (2 * Real.pi * Real.sqrt (s / 6)) := by
  obtain ⟨B, hdisj, hblock⟩ :=
    exists_three_disjoint_blocks_of_rankTwo_tail
      (fun i ↦ (lam i) ^ 2) hs htail
  exact smallBall_diagonalCenteredLaw_le_of_three_spectralBlocks
    a lam B (by norm_num)
      (by simpa only [Finset.coe_univ] using hdisj)
      (by positivity) hblock heps x

lemma diagonalPartialSum_smallBall_le_of_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι) {s : ℝ} (hs : 0 < s)
    (htail : ∀ T ⊆ S, T.card ≤ 2 →
      s ≤ ∑ i ∈ S \ T, (lam i) ^ 2)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam S)) eps x ≤
      eps * threeSpectralMass /
        (2 * Real.pi * Real.sqrt (s / 6)) := by
  classical
  rw [map_diagonalPartialSum_eq_diagonalCenteredLaw_subtype]
  apply smallBall_diagonalCenteredLaw_le_of_rankTwo_tail
      (fun i : S ↦ a i) (fun i : S ↦ lam i) hs _ heps x
  intro T hTcard
  let e : S ↪ ι := Function.Embedding.subtype fun i ↦ i ∈ S
  let U : Finset ι := T.map e
  have hUS : U ⊆ S := by
    intro i hi
    obtain ⟨j, hjT, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have hUcard : U.card ≤ 2 := by
    simpa only [U, Finset.card_map] using hTcard
  have hraw := htail U hUS hUcard
  have hsum : (∑ i : S with i ∉ T, (lam i) ^ 2) =
      ∑ i ∈ S \ U, (lam i) ^ 2 := by
    change (∑ i : S with i ∉ T, (lam (e i)) ^ 2) = _
    rw [← Finset.sum_map (Finset.univ.filter fun i : S ↦ i ∉ T) e
      (fun i : ι ↦ (lam i) ^ 2)]
    congr 1
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff, U, e]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j.property, ?_⟩
      intro hU
      obtain ⟨k, hk, hkj⟩ := hU
      apply hj
      have : k = j := e.injective hkj
      simpa only [this] using hk
    · intro hi
      let j : S := ⟨i, hi.1⟩
      refine ⟨j, ?_, rfl⟩
      intro hj
      exact hi.2 ⟨j, hj, rfl⟩
  rw [hsum]
  exact hraw

end Erdos88.GaussianQuadratic
