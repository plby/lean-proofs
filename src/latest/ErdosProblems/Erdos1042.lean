/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the resolution of Erdős Problem 1042, on the number of
connected components of polynomial lemniscates whose zeros are constrained to
a fixed closed subset of the complex plane.

Informal authors:
- Subhajit Ghosh
- K. Ramachandran

Formal author:
- OpenAI Codex

The definition `HasTransfiniteDiameter` below is the Fekete-point definition
appearing in the problem.  In particular, no potential-theoretic notion of
capacity is hidden in the statement of the main theorem.
-/

import Mathlib

open scoped BigOperators ENNReal NNReal Topology
open Filter Metric Polynomial Set Topology
open MeasureTheory

noncomputable section

namespace Erdos1042

/-! ### Transfinite diameter -/

/-- The product of the mutual distances of an ordered `n`-tuple.  Every
unordered pair occurs exactly once. -/
def mutualDistanceProduct {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖

/-- The value of an ordered Fekete `n`-tuple, with the normalization used in
the definition of transfinite diameter.  The exceptional values `n = 0,1`
are set to zero and therefore do not affect the limit. -/
def feketeValue {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  if 2 ≤ n then
    Real.rpow (mutualDistanceProduct z) ((Nat.choose n 2 : ℝ)⁻¹)
  else 0

/-- The `n`-th Fekete diameter of `K`. -/
def feketeDiameter (K : Set ℂ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧ r = feketeValue z}

/-- `K` has transfinite diameter `d`, in exactly the sense of the displayed
limit in Erdős Problem 1042.  Boundedness records that this is a finite real
transfinite diameter; for an unbounded set the classical diameter is infinite. -/
def HasTransfiniteDiameter (K : Set ℂ) (d : ℝ) : Prop :=
  Bornology.IsBounded K ∧ Tendsto (feketeDiameter K) atTop (𝓝 d)

lemma mutualDistanceProduct_nonneg {n : ℕ} (z : Fin n → ℂ) :
    0 ≤ mutualDistanceProduct z := by
  unfold mutualDistanceProduct
  positivity

lemma bddAbove_feketeValues {K : Set ℂ} (hK : Bornology.IsBounded K) (n : ℕ) :
    BddAbove {r : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧ r = feketeValue z} := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK
  let B : ℝ := max 1 (2 * C)
  let e : ℝ := (Nat.choose n 2 : ℝ)⁻¹
  refine ⟨Real.rpow (B ^ (n * n)) e, ?_⟩
  rintro r ⟨z, hzK, rfl⟩
  by_cases hn : 2 ≤ n
  · rw [feketeValue, if_pos hn]
    apply Real.rpow_le_rpow (mutualDistanceProduct_nonneg z) ?_ (by positivity)
    calc
      mutualDistanceProduct z ≤ ∏ _i : Fin n, B ^ n := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ by positivity
        · intro i _
          calc
            ∏ j ∈ Finset.Ioi i, ‖z i - z j‖ ≤
                ∏ _j ∈ Finset.Ioi i, B := by
              apply Finset.prod_le_prod
              · exact fun _ _ ↦ norm_nonneg _
              · intro j _
                have hij : ‖z i - z j‖ ≤ ‖z i‖ + ‖z j‖ := norm_sub_le _ _
                have hiC := hC _ (hzK i)
                have hjC := hC _ (hzK j)
                have hBC : 2 * C ≤ B := le_max_right _ _
                linarith
            _ = B ^ (Finset.Ioi i).card := by simp
            _ ≤ B ^ n := by
              apply pow_le_pow_right₀ (le_max_left _ _)
              simpa using Finset.card_le_univ (Finset.Ioi i)
      _ = B ^ (n * n) := by simp [pow_mul]
  · rw [feketeValue, if_neg hn]
    exact Real.rpow_nonneg (by positivity) _

lemma feketeValue_le_feketeDiameter {K : Set ℂ} (hK : Bornology.IsBounded K)
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, z i ∈ K) :
    feketeValue z ≤ feketeDiameter K n := by
  apply le_csSup (bddAbove_feketeValues hK n)
  exact ⟨z, hz, rfl⟩

lemma exists_feketeDiameter_lt_one {K : Set ℂ} {d : ℝ}
    (hdiam : HasTransfiniteDiameter K d) (hd₀ : 0 < d) (hd₁ : d < 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧ feketeDiameter K m < q := by
  let q : ℝ := (d + 1) / 2
  have hdq : d < q := by dsimp [q]; linarith
  have hq₀ : 0 < q := by dsimp [q]; linarith
  have hq₁ : q < 1 := by dsimp [q]; linarith
  have hevent : ∀ᶠ m in atTop, feketeDiameter K m < q :=
    (tendsto_order.1 hdiam.2).2 q hdq
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 ≤ m := eventually_ge_atTop 2
  obtain ⟨m, hm, hmq⟩ := (hlarge.and hevent).exists
  exact ⟨m, hm, q, hq₀, hq₁, hmq⟩

lemma mutualDistanceProduct_lt_pow_of_feketeDiameter_lt
    {K : Set ℂ} (hK : Bornology.IsBounded K) {m : ℕ} (hm : 2 ≤ m)
    {q : ℝ} (hq₀ : 0 < q) (hfd : feketeDiameter K m < q)
    (z : Fin m → ℂ) (hz : ∀ i, z i ∈ K) :
    mutualDistanceProduct z < q ^ Nat.choose m 2 := by
  have hvalue : feketeValue z < q :=
    (feketeValue_le_feketeDiameter hK z hz).trans_lt hfd
  rw [feketeValue, if_pos hm] at hvalue
  have hchoose : 0 < (Nat.choose m 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hm
  have h := (Real.rpow_inv_lt_iff_of_pos
    (mutualDistanceProduct_nonneg z) hq₀.le hchoose).mp hvalue
  simpa [Real.rpow_natCast] using h

/-- Mutual-distance product with every distance truncated from below by
`ε`.  At `ε = 0` this is the ordinary Fekete product. -/
def regularizedDistanceProduct {K : Set ℂ} {m : ℕ} (ε : ℝ)
    (z : Fin m → K) : ℝ :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, max ‖(z i : ℂ) - z j‖ ε

lemma regularizedDistanceProduct_zero {K : Set ℂ} {m : ℕ}
    (z : Fin m → K) :
    regularizedDistanceProduct 0 z =
      mutualDistanceProduct (fun i ↦ (z i : ℂ)) := by
  simp [regularizedDistanceProduct, mutualDistanceProduct, max_eq_left]

lemma continuous_regularizedDistanceProduct {K : Set ℂ} {m : ℕ} :
    Continuous (fun p : ℝ × (Fin m → K) ↦
      regularizedDistanceProduct p.1 p.2) := by
  unfold regularizedDistanceProduct
  fun_prop

lemma exists_pos_regularization_of_zero_lt
    {K : Set ℂ} (hK : IsCompact K) {m : ℕ}
    (hzero : ∀ z : Fin m → K, regularizedDistanceProduct 0 z < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin m → K,
      regularizedDistanceProduct ε z < 1 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  cases isEmpty_or_nonempty (Fin m → K) with
  | inl hempty =>
      letI := hempty
      exact ⟨1, zero_lt_one, fun z ↦ isEmptyElim z⟩
  | inr hnonempty =>
    letI := hnonempty
    let M : ℝ → ℝ := fun ε ↦
      sSup ((fun z : Fin m → K ↦ regularizedDistanceProduct ε z) '' Set.univ)
    have hMcont : Continuous M := by
      apply isCompact_univ.continuous_sSup
      exact continuous_regularizedDistanceProduct
    have hMzero : M 0 < 1 := by
      apply (isCompact_univ.sSup_lt_iff_of_continuous Set.univ_nonempty
        (continuous_regularizedDistanceProduct.comp
          (continuous_const.prodMk continuous_id)).continuousOn 1).2
      exact fun z _ ↦ hzero z
    have hopen : IsOpen {ε : ℝ | M ε < 1} :=
      isOpen_lt hMcont continuous_const
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp hopen 0 hMzero
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    intro z
    have hhalf : M (δ / 2) < 1 := hball (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_div, abs_of_pos hδ]
      have htwo : |(2 : ℝ)| = 2 := by norm_num
      rw [htwo]
      exact half_lt_self hδ)
    exact (le_csSup (isCompact_univ.bddAbove_image
      (continuous_regularizedDistanceProduct.comp
        (continuous_const.prodMk continuous_id)).continuousOn)
        (Set.mem_image_of_mem _ (Set.mem_univ z))).trans_lt hhalf

lemma exists_regularization_lt_one
    {K : Set ℂ} (hK : IsCompact K) {m : ℕ} (hm : 2 ≤ m)
    {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1)
    (hfd : feketeDiameter K m < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin m → K,
      regularizedDistanceProduct ε z < 1 := by
  apply exists_pos_regularization_of_zero_lt hK
  intro z
  rw [regularizedDistanceProduct_zero]
  exact (mutualDistanceProduct_lt_pow_of_feketeDiameter_lt hK.isBounded hm hq₀ hfd
    (fun i ↦ (z i : ℂ)) (fun i ↦ (z i).2)).trans
      (pow_lt_one₀ hq₀.le hq₁ (Nat.choose_pos hm).ne')

/-! ### Regularized logarithmic energy -/

/-- The logarithmic kernel with its diagonal singularity truncated at `ε`. -/
def regularizedLog (ε : ℝ) (z w : ℂ) : ℝ :=
  Real.log (max ‖z - w‖ ε)

lemma continuous_regularizedLog {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℂ × ℂ ↦ regularizedLog ε p.1 p.2) := by
  apply Continuous.log
  · fun_prop
  · intro p
    exact ne_of_gt (hε.trans_le (le_max_right _ _))

lemma log_regularizedDistanceProduct {K : Set ℂ} {m : ℕ}
    {ε : ℝ} (hε : 0 < ε) (z : Fin m → K) :
    Real.log (regularizedDistanceProduct ε z) =
      ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
        regularizedLog ε (z i : ℂ) (z j : ℂ) := by
  unfold regularizedDistanceProduct
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_prod]
    · rfl
    · intro j _
      exact ne_of_gt (hε.trans_le (le_max_right _ _))
  · intro i _
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      ne_of_gt (hε.trans_le (le_max_right _ _))

/-- The regularized logarithmic energy of a probability measure. -/
def regularizedEnergy {K : Set ℂ} (ε : ℝ)
    (μ : MeasureTheory.ProbabilityMeasure K) : ℝ :=
  ∫ p : K × K, regularizedLog ε (p.1 : ℂ) (p.2 : ℂ)
    ∂((μ : Measure K).prod (μ : Measure K))

lemma integrable_regularizedLog_prod {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) (μ : MeasureTheory.ProbabilityMeasure K) :
    MeasureTheory.Integrable
      (fun p : K × K ↦ regularizedLog ε (p.1 : ℂ) (p.2 : ℂ))
      ((μ : Measure K).prod (μ : Measure K)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_regularizedLog hε |>.comp
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd))
  · exact HasCompactSupport.of_compactSpace _

lemma regularizedEnergy_neg_of_products_lt_one
    {K : Set ℂ} (hK : IsCompact K) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hprod : ∀ z : Fin m → K, regularizedDistanceProduct ε z < 1)
    (μ : MeasureTheory.ProbabilityMeasure K) :
    regularizedEnergy ε μ < 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let π : Measure (Fin m → K) := Measure.pi fun _ ↦ (μ : Measure K)
  let e : (Fin m → K) → ℝ := fun z ↦
    ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
      regularizedLog ε (z i : ℂ) (z j : ℂ)
  have hecont : Continuous e := by
    dsimp [e]
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact (continuous_regularizedLog hε).comp
      ((continuous_subtype_val.comp (continuous_apply i)).prodMk
        (continuous_subtype_val.comp (continuous_apply j)))
  have heint : MeasureTheory.Integrable e π := by
    apply Continuous.integrable_of_hasCompactSupport hecont
    exact HasCompactSupport.of_compactSpace _
  have heneg : ∀ z, e z < 0 := by
    intro z
    change (∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
      regularizedLog ε (z i : ℂ) (z j : ℂ)) < 0
    rw [← log_regularizedDistanceProduct hε z]
    exact Real.log_neg (by
      unfold regularizedDistanceProduct
      positivity) (hprod z)
  have hintneg : (∫ z, e z ∂π) < 0 := by
    have hsupp : Function.support (fun z ↦ -e z) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact neg_ne_zero.mpr (ne_of_lt (heneg z))
    have hpos : 0 < ∫ z, -e z ∂π :=
      (MeasureTheory.integral_pos_iff_support_of_nonneg
        (fun z ↦ neg_nonneg.mpr (heneg z).le) heint.neg).2 (by
          rw [hsupp]
          simp [π])
    have hpos' : 0 < -(∫ z, e z ∂π) := by
      simpa only [MeasureTheory.integral_neg] using hpos
    exact neg_pos.mp hpos'
  by_contra henergy
  have henergy_nonneg : 0 ≤ regularizedEnergy ε μ := le_of_not_gt henergy
  have hpair (i j : Fin m) (hij : i ≠ j) :
      (∫ z, regularizedLog ε (z i : ℂ) (z j : ℂ) ∂π) =
        regularizedEnergy ε μ := by
    have hind : ProbabilityTheory.IndepFun (fun z : Fin m → K ↦ z i)
        (fun z : Fin m → K ↦ z j) π :=
      (ProbabilityTheory.iIndepFun_pi (X := fun _ ↦ id)
        (fun _ ↦ aemeasurable_id)).indepFun hij
    have hmap : Measure.map (fun z : Fin m → K ↦ (z i, z j)) π =
        (μ : Measure K).prod (μ : Measure K) := by
      rw [hind.map_prod_eq_prod_map_map
          (measurable_pi_apply i).aemeasurable
          (measurable_pi_apply j).aemeasurable,
        (MeasureTheory.measurePreserving_eval (fun _ : Fin m ↦ (μ : Measure K)) i).map_eq,
        (MeasureTheory.measurePreserving_eval (fun _ : Fin m ↦ (μ : Measure K)) j).map_eq]
    have hmeas : AEStronglyMeasurable
        (fun p : K × K ↦ regularizedLog ε (p.1 : ℂ) (p.2 : ℂ))
        (Measure.map (fun z : Fin m → K ↦ (z i, z j)) π) := by
      rw [hmap]
      exact (integrable_regularizedLog_prod hK hε μ).aestronglyMeasurable
    rw [regularizedEnergy, ← hmap,
      MeasureTheory.integral_map
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable hmeas]
  have hterm (i j : Fin m) : Integrable
      (fun z : Fin m → K ↦ regularizedLog ε (z i : ℂ) (z j : ℂ)) π := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_regularizedLog hε).comp
        ((continuous_subtype_val.comp (continuous_apply i)).prodMk
          (continuous_subtype_val.comp (continuous_apply j)))
    · exact HasCompactSupport.of_compactSpace _
  have hint_nonneg : 0 ≤ ∫ z, e z ∂π := by
    change 0 ≤ ∫ z, (∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
      regularizedLog ε (z i : ℂ) (z j : ℂ)) ∂π
    rw [MeasureTheory.integral_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum (Finset.Ioi i) fun j _ ↦ hterm i j]
    apply Finset.sum_nonneg
    intro i _
    rw [MeasureTheory.integral_finsetSum (Finset.Ioi i) fun j _ ↦ hterm i j]
    apply Finset.sum_nonneg
    intro j hj
    rw [hpair i j (Finset.mem_Ioi.mp hj).ne]
    exact henergy_nonneg
  exact (not_lt_of_ge hint_nonneg) hintneg

/-- The regularized potential generated by `μ` at a point of its support set. -/
def regularizedPotential {K : Set ℂ} (ε : ℝ)
    (μ : ProbabilityMeasure K) (x : K) : ℝ :=
  ∫ y : K, regularizedLog ε (x : ℂ) (y : ℂ) ∂(μ : Measure K)

lemma exists_mem_support_regularizedPotential_neg
    {K : Set ℂ} (hK : IsCompact K) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hprod : ∀ z : Fin m → K, regularizedDistanceProduct ε z < 1)
    (μ : ProbabilityMeasure K) :
    ∃ x : K, x ∈ (μ : Measure K).support ∧
      regularizedPotential ε μ x < 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let kernel : K × K → ℝ := fun p ↦
    regularizedLog ε (p.1 : ℂ) (p.2 : ℂ)
  have hkernel : Integrable kernel ((μ : Measure K).prod (μ : Measure K)) := by
    simpa only [kernel] using integrable_regularizedLog_prod hK hε μ
  have henergy : regularizedEnergy ε μ < 0 :=
    regularizedEnergy_neg_of_products_lt_one hK hm hε hprod μ
  have hiter : (∫ x : K, regularizedPotential ε μ x ∂(μ : Measure K)) < 0 := by
    change (∫ x : K, ∫ y : K, kernel (x, y) ∂(μ : Measure K)
      ∂(μ : Measure K)) < 0
    rw [← MeasureTheory.integral_prod kernel hkernel]
    exact henergy
  by_contra h
  push_neg at h
  have hsupport : ∀ᵐ x : K ∂(μ : Measure K),
      x ∈ (μ : Measure K).support := Measure.support_mem_ae
  have hae : ∀ᵐ x : K ∂(μ : Measure K),
      0 ≤ regularizedPotential ε μ x :=
    hsupport.mono fun x hx ↦ h x hx
  exact (not_lt_of_ge (MeasureTheory.integral_nonneg_of_ae hae)) hiter

/-- Uniform continuity of the truncated kernel in its first variable, uniformly
over the compact set supporting the second variable. -/
lemma exists_ball_regularizedLog_lt_add
    {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (x : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ ball x r, ∀ y : K,
      regularizedLog ε w (y : ℂ) < regularizedLog ε x (y : ℂ) + a := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : ℂ → ℝ := fun w ↦
    sSup ((fun y : K ↦ regularizedLog ε w (y : ℂ) -
      regularizedLog ε x (y : ℂ)) '' Set.univ)
  have hDcont : Continuous D := by
    apply isCompact_univ.continuous_sSup
    exact ((continuous_regularizedLog hε).comp
      (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))).sub
      ((continuous_regularizedLog hε).comp
        (continuous_const.prodMk
          (continuous_subtype_val.comp continuous_snd)))
  have hDx : D x = 0 := by
    simp [D, hKne.to_subtype]
  have hopen : IsOpen {w : ℂ | D w < a} :=
    isOpen_lt hDcont continuous_const
  have hxopen : x ∈ {w : ℂ | D w < a} := by simpa [hDx] using ha
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hxopen
  refine ⟨r, hr, fun w hw y ↦ ?_⟩
  have hDwa : D w < a := hball hw
  have hyD : regularizedLog ε w (y : ℂ) - regularizedLog ε x (y : ℂ) ≤ D w := by
    change regularizedLog ε w (y : ℂ) - regularizedLog ε x (y : ℂ) ≤
      sSup ((fun t : K ↦ regularizedLog ε w (t : ℂ) -
        regularizedLog ε x (t : ℂ)) '' Set.univ)
    apply le_csSup (isCompact_univ.bddAbove_image
      (((continuous_regularizedLog hε).comp
        ((continuous_const : Continuous (fun _ : K ↦ w)).prodMk
          continuous_subtype_val)).sub
        ((continuous_regularizedLog hε).comp
          ((continuous_const : Continuous (fun _ : K ↦ x)).prodMk
            continuous_subtype_val))).continuousOn)
    exact Set.mem_image_of_mem _ (Set.mem_univ y)
  linarith

/-! ### Empirical measures of root families -/

/-- The uniform empirical probability measure of a nonempty indexed family. -/
noncomputable def empiricalProbability {K : Set ℂ} {n : ℕ} (hn : 0 < n)
    (z : Fin n → K) : ProbabilityMeasure K := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let ν : ProbabilityMeasure (Fin n) :=
    ⟨ProbabilityTheory.uniformOn (Set.univ : Set (Fin n)), inferInstance⟩
  exact ν.map (measurable_of_finite z).aemeasurable

lemma integral_empiricalProbability {K : Set ℂ} {n : ℕ} (hn : 0 < n)
    (z : Fin n → K) {f : K → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(empiricalProbability hn z : Measure K)) =
      (∑ i, f (z i)) / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change (∫ x, f x ∂Measure.map z
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n)))) = _
  rw [MeasureTheory.integral_map (measurable_of_finite z).aemeasurable (by
      exact hf.aestronglyMeasurable)]
  have hint : Integrable (fun i ↦ f (z i))
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_of_discreteTopology
    · exact HasCompactSupport.of_compactSpace _
  rw [MeasureTheory.integral_fintype hint]
  simp [ProbabilityTheory.uniformOn_univ, MeasureTheory.measureReal_def,
    ENNReal.toReal_div, hn.ne']
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

lemma empiricalProbability_apply {K : Set ℂ} {n : ℕ} (hn : 0 < n)
    (z : Fin n → K) {A : Set K} (hA : MeasurableSet A) :
    (empiricalProbability hn z : Measure K) A =
      ((z ⁻¹' A).ncard : ℝ≥0∞) / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change Measure.map z (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n))) A = _
  rw [Measure.map_apply (measurable_of_finite z) hA,
    ProbabilityTheory.uniformOn_univ,
    Measure.count_apply_finite (z ⁻¹' A) (Set.toFinite _)]
  rw [Set.ncard_eq_toFinset_card (z ⁻¹' A)]
  simp

/-- The product of root distances truncated from below by `ε`. -/
def regularizedRootProduct {K : Set ℂ} {n : ℕ} (ε : ℝ)
    (z : Fin n → K) (w : ℂ) : ℝ :=
  ∏ i, max ‖w - (z i : ℂ)‖ ε

lemma log_regularizedRootProduct {K : Set ℂ} {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (z : Fin n → K) (w : ℂ) :
    Real.log (regularizedRootProduct ε z w) =
      ∑ i, regularizedLog ε w (z i : ℂ) := by
  unfold regularizedRootProduct
  rw [Real.log_prod (fun i _ ↦
    ne_of_gt (hε.trans_le (le_max_right ‖w - (z i : ℂ)‖ ε)))]
  rfl

/-! ### Root polynomials and lemniscates -/

/-- The monic polynomial with the indicated ordered list of roots. -/
def rootPolynomial {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i, (X - C (z i))

/-- The open unit lemniscate of a complex polynomial. -/
def unitLemniscate (p : Polynomial ℂ) : Set ℂ :=
  {w | ‖p.eval w‖ < 1}

/-- The number of connected components of the open unit lemniscate. -/
def componentCount (p : Polynomial ℂ) : ℕ :=
  Nat.card (ConnectedComponents (unitLemniscate p))

lemma isOpen_unitLemniscate (p : Polynomial ℂ) : IsOpen (unitLemniscate p) := by
  exact isOpen_lt p.continuous.norm continuous_const

lemma rootPolynomial_monic {n : ℕ} (z : Fin n → ℂ) : (rootPolynomial z).Monic := by
  simpa [rootPolynomial] using monic_prod_X_sub_C z Finset.univ

lemma rootPolynomial_natDegree {n : ℕ} (z : Fin n → ℂ) :
    (rootPolynomial z).natDegree = n := by
  simp [rootPolynomial]

lemma eval_rootPolynomial {n : ℕ} (z : Fin n → ℂ) (w : ℂ) :
    (rootPolynomial z).eval w = ∏ i, (w - z i) := by
  rw [rootPolynomial, eval_prod]
  simp

lemma ball_subset_unitLemniscate_of_regularizedLog_sum_neg
    {K : Set ℂ} {n : ℕ} {ε r : ℝ} (hε : 0 < ε)
    (z : Fin n → K) (x : ℂ)
    (hsum : ∀ w ∈ ball x r,
      ∑ i, regularizedLog ε w (z i : ℂ) < 0) :
    ball x r ⊆ unitLemniscate (rootPolynomial fun i ↦ (z i : ℂ)) := by
  intro w hw
  have hregpos : 0 < regularizedRootProduct ε z w := by
    unfold regularizedRootProduct
    exact Finset.prod_pos fun i _ ↦ hε.trans_le (le_max_right _ _)
  have hreglt : regularizedRootProduct ε z w < 1 :=
    (Real.log_neg_iff hregpos).mp (by
      rw [log_regularizedRootProduct hε]
      exact hsum w hw)
  change ‖(rootPolynomial fun i ↦ (z i : ℂ)).eval w‖ < 1
  rw [eval_rootPolynomial, norm_prod]
  exact (Finset.prod_le_prod (fun i _ ↦ norm_nonneg _)
    (fun i _ ↦ le_max_left _ _)).trans_lt hreglt

lemma root_mem_unitLemniscate {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    z i ∈ unitLemniscate (rootPolynomial z) := by
  simp [unitLemniscate, eval_rootPolynomial, Finset.prod_eq_zero (Finset.mem_univ i)]

/-! The following small namespace contains the inverse-root construction from
the neighboring formalization of Erdős Problem 1048.  Keeping only the lemmas
used below makes this file self-contained without importing that development's
unrelated asymptotic-diameter half. -/

namespace Model

def f (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := z ^ n - (r : ℂ) ^ n

def S (n : ℕ) (r : ℝ) : Set ℂ := {z | ‖f n r z‖ ≤ 1}

lemma disk_in_right_half_plane {r : ℝ} (hr : r > 1) {n : ℕ} (hn : n > 0) :
    ∀ w ∈ closedBall (r ^ n : ℂ) 1, 0 < w.re := by
  intro w hw
  have h_re_w : w.re ≥ r ^ n - 1 := by
    norm_num [Complex.dist_eq, Complex.normSq, Complex.norm_def] at hw
    norm_cast at *
    nlinarith
  linarith [pow_lt_pow_right₀ hr hn]

noncomputable def branch (n : ℕ) (k : ℕ) (w : ℂ) : ℂ :=
  (Real.rpow (norm w) (1 / (n : ℝ)) : ℂ) *
    Complex.exp (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n : ℝ))

lemma branch_pow {n : ℕ} (hn : n > 0) (k : ℕ) (w : ℂ) :
    (branch n k w) ^ n = w := by
  unfold branch
  norm_num [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀,
    hn.ne', mul_div_cancel₀, Complex.exp_nat_mul]
  convert Complex.norm_mul_exp_arg_mul_I w using 1
  field_simp
  rw [← Complex.ofReal_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (by positivity),
    Real.rpow_one]
  rw [← Complex.exp_nat_mul]
  ring_nf
  norm_num [hn.ne']
  exact Or.inl
    (Complex.exp_eq_exp_iff_exists_int.mpr
      ⟨k, by simp [hn.ne', mul_assoc, mul_comm, mul_left_comm]⟩)

lemma branch_mem_S {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ)
    (w : ℂ) (hw : w ∈ closedBall (r ^ n : ℂ) 1) :
    branch n k w ∈ S n r := by
  rw [S, Set.mem_ofPred_eq, f]
  have hre : 0 < w.re := disk_in_right_half_plane hr hn w hw
  rw [branch_pow hn k w]
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  exact hw

set_option linter.flexible false in
lemma branch_continuous_on_disk {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
    ContinuousOn (branch n k) (closedBall (r ^ n : ℂ) 1) := by
  have h_arg_cont :
      ContinuousOn (fun z : ℂ ↦ Complex.arg z) (closedBall (r ^ n : ℂ) 1) := by
    refine continuousOn_of_forall_continuousAt fun z hz ↦ ?_
    refine Complex.continuousAt_arg ?_
    simp_all +decide [Complex.slitPlane]
    contrapose! hz
    norm_num [Complex.dist_eq, Complex.normSq, Complex.norm_def, hz]
    norm_cast
    norm_num
    rw [Real.sqrt_mul_self_eq_abs, abs_of_nonpos] <;>
      nlinarith [pow_le_pow_right₀ hr.le hn]
  refine ContinuousOn.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.rpow continuous_norm.continuousOn continuousOn_const <| by
        intro x hx
        exact Or.inr <| by positivity)
  · exact Complex.continuous_exp.comp_continuousOn
      (ContinuousOn.mul continuousOn_const <|
        Complex.continuous_ofReal.comp_continuousOn <|
          ContinuousOn.div_const (h_arg_cont.add continuousOn_const) _)

def component (n : ℕ) (r : ℝ) (k : ℕ) : Set ℂ :=
  branch n k '' closedBall (r ^ n : ℂ) 1

lemma S_subset_union_components {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) :
    S n r ⊆ ⋃ k ∈ Finset.range n, component n r k := by
  intro z hz
  rw [S, Set.mem_ofPred_eq, f] at hz
  let w := z ^ n
  have hw : w ∈ closedBall (r ^ n : ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    exact hz
  have h_root : z ^ n = w := rfl
  have hw_ne_zero : w ≠ 0 := by
    have : 0 < w.re := disk_in_right_half_plane hr hn w hw
    intro h
    rw [h] at this
    simp at this
  obtain ⟨k, hk⟩ : ∃ k ∈ Finset.range n, z = branch n k w := by
    obtain ⟨k, hk⟩ :
        ∃ k : ℤ,
          z = (Real.rpow (norm w) (1 / (n : ℝ)) : ℂ) *
            Complex.exp
              (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n : ℝ)) := by
      have h_exp :
          ∃ θ : ℝ,
            z = (Real.rpow (norm w) (1 / n) : ℂ) *
              Complex.exp (Complex.I * θ) := by
        have h_polar : z = ‖z‖ * Complex.exp (Complex.I * Complex.arg z) := by
          nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I z]
          ring_nf
        norm_num [← h_root, Complex.norm_exp] at *
        exact ⟨Complex.arg z, by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
            mul_inv_cancel₀ (by positivity), Real.rpow_one]
          exact h_polar⟩
      obtain ⟨θ, hθ⟩ := h_exp
      have h_eq : ∃ k : ℤ, n * θ = Complex.arg w + 2 * Real.pi * k := by
        have h_eq :
            Complex.exp (Complex.I * (n * θ)) =
              Complex.exp (Complex.I * Complex.arg w) := by
          have h_exp :
              z ^ n = (Real.rpow (norm w) (1 / n : ℝ)) ^ n *
                Complex.exp (Complex.I * (n * θ)) := by
            rw [hθ, mul_pow, ← Complex.exp_nat_mul]
            ring_nf
          have h_exp : (Real.rpow (norm w) (1 / n : ℝ)) ^ n = norm w := by
            norm_num [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), hn.ne']
          have h_exp : w = norm w * Complex.exp (Complex.I * Complex.arg w) := by
            nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I w]
            ring_nf
          norm_num [Complex.ext_iff] at *
          norm_cast at *
          aesop
        rw [Complex.exp_eq_exp_iff_exists_int] at h_eq
        obtain ⟨k, hk⟩ := h_eq
        exact ⟨k, by
          norm_num [Complex.ext_iff] at hk
          linarith⟩
      exact h_eq.imp fun k hk ↦ by
        rw [hθ, ← hk]
        push_cast
        ring_nf
        norm_num [hn.ne']
    obtain ⟨q, s, hs⟩ : ∃ q : ℤ, ∃ s : ℕ, s < n ∧ k = q * n + s := by
      exact ⟨k / n, Int.toNat (k % n), by
        linarith [Int.emod_lt_of_pos k (by positivity : 0 < (n : ℤ)),
          Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0),
          Int.toNat_of_nonneg
            (Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0))],
        by
          linarith [Int.emod_add_mul_ediv k n,
            Int.toNat_of_nonneg
              (Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0))]⟩
    refine ⟨s, Finset.mem_range.mpr hs.1, hk.trans ?_⟩
    norm_num [hs.2, branch]
    ring_nf
    norm_num [hn.ne']
    ring_nf
    exact Or.inl (Complex.exp_eq_exp_iff_exists_int.mpr ⟨q, by ring⟩)
  exact hk.2.symm ▸ Set.mem_iUnion₂.2 ⟨k, hk.1, ⟨w, hw, rfl⟩⟩

set_option linter.flexible false in
lemma components_disjoint {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1)
    (k l : ℕ) (hk : k < n) (hl : l < n)
    (h : (component n r k ∩ component n r l).Nonempty) : k = l := by
  obtain ⟨z, hz⟩ : ∃ z, z ∈ component n r k ∧ z ∈ component n r l := h
  obtain ⟨w1, hw1, hw1z⟩ : ∃ w1 ∈ closedBall (r ^ n : ℂ) 1, z = branch n k w1 := by
    exact hz.1.imp fun x hx ↦ ⟨hx.1, hx.2.symm⟩
  obtain ⟨w2, hw2, hw2z⟩ : ∃ w2 ∈ closedBall (r ^ n : ℂ) 1, z = branch n l w2 := by
    exact hz.2.imp fun x hx ↦ ⟨hx.1, hx.2.symm⟩
  have hw1w2 : w1 = w2 := by
    have hw1w2 : z ^ n = w1 ∧ z ^ n = w2 := by
      exact ⟨by rw [hw1z, branch_pow hn k w1], by rw [hw2z, branch_pow hn l w2]⟩
    grind
  have h_branch_eq : branch n k w1 = branch n l w1 := by grind
  have h_exp_eq :
      Complex.exp (Complex.I * ((Complex.arg w1 + 2 * Real.pi * k) / n)) =
        Complex.exp (Complex.I * ((Complex.arg w1 + 2 * Real.pi * l) / n)) := by
    unfold branch at h_branch_eq
    simp +zetaDelta at *
    refine h_branch_eq.resolve_right ?_
    refine ne_of_gt (Real.rpow_pos_of_pos ?_ ((n : ℝ)⁻¹))
    refine norm_pos_iff.mpr ?_
    rintro rfl
    norm_num at *
    exact hw1.not_gt
      (one_lt_pow₀ (by rw [abs_of_pos] <;> linarith) (by linarith))
  rw [Complex.exp_eq_exp_iff_exists_int] at h_exp_eq
  obtain ⟨m, hm⟩ := h_exp_eq
  rw [Complex.ext_iff] at hm
  simp_all +decide
  have hkl : k = l + m * n := by
    exact_mod_cast
      (by
        nlinarith [Real.pi_pos,
          mul_div_cancel₀ (w2.arg + 2 * Real.pi * k)
            (by positivity : (n : ℝ) ≠ 0),
          mul_div_cancel₀ (w2.arg + 2 * Real.pi * l)
            (by positivity : (n : ℝ) ≠ 0)] :
        (k : ℝ) = l + m * n)
  nlinarith [show m = 0 by nlinarith]

lemma component_isClosed {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
    IsClosed (component n r k) := by
  convert IsCompact.isClosed ?_
  · infer_instance
  · exact IsCompact.image_of_continuousOn (ProperSpace.isCompact_closedBall _ _)
      (branch_continuous_on_disk hn hr k)

/-- On the open disk tangent to the origin, the same polar inverse branch is
continuous.  This is the endpoint version needed for `r = 1`. -/
lemma branch_continuous_on_unit_ball {n : ℕ} (hn : n > 0) (k : ℕ) :
    ContinuousOn (branch n k) (ball (1 : ℂ) 1) := by
  have h_arg_cont :
      ContinuousOn (fun z : ℂ ↦ Complex.arg z) (ball (1 : ℂ) 1) :=
    Complex.continuousOn_arg.mono Complex.ball_one_subset_slitPlane
  refine ContinuousOn.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.rpow continuous_norm.continuousOn continuousOn_const <| by
        intro x hx
        exact Or.inr <| by positivity)
  · exact Complex.continuous_exp.comp_continuousOn
      (ContinuousOn.mul continuousOn_const <|
        Complex.continuous_ofReal.comp_continuousOn <|
          ContinuousOn.div_const (h_arg_cont.add continuousOn_const) _)

/-- Every nonzero `n`-th root is one of the explicitly indexed polar
branches. -/
lemma exists_branch_eq_of_pow_eq {n : ℕ} (hn : n > 0) {z w : ℂ}
    (h_root : z ^ n = w) (hw_ne_zero : w ≠ 0) :
    ∃ k ∈ Finset.range n, z = branch n k w := by
  obtain ⟨k, hk⟩ :
      ∃ k : ℤ,
        z = (Real.rpow (norm w) (1 / (n : ℝ)) : ℂ) *
          Complex.exp
            (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n : ℝ)) := by
    obtain ⟨θ, hθ⟩ :
        ∃ θ : ℝ,
          z = (Real.rpow (norm w) (1 / n) : ℂ) *
            Complex.exp (Complex.I * θ) := by
      have h_polar : z = ‖z‖ * Complex.exp (Complex.I * Complex.arg z) := by
        nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I z]
        ring_nf
      norm_num [← h_root, Complex.norm_exp] at *
      exact ⟨Complex.arg z, by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
          mul_inv_cancel₀ (by positivity), Real.rpow_one]
        exact h_polar⟩
    have h_eq : ∃ k : ℤ, n * θ = Complex.arg w + 2 * Real.pi * k := by
      have h_eq :
          Complex.exp (Complex.I * (n * θ)) =
            Complex.exp (Complex.I * Complex.arg w) := by
        have h_exp :
            z ^ n = (Real.rpow (norm w) (1 / n : ℝ)) ^ n *
              Complex.exp (Complex.I * (n * θ)) := by
          rw [hθ, mul_pow, ← Complex.exp_nat_mul]
          ring_nf
        have h_rpow : (Real.rpow (norm w) (1 / n : ℝ)) ^ n = norm w := by
          norm_num [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), hn.ne']
        have h_polar : w = norm w * Complex.exp (Complex.I * Complex.arg w) := by
          nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I w]
          ring_nf
        norm_num [Complex.ext_iff] at *
        norm_cast at *
        aesop
      rw [Complex.exp_eq_exp_iff_exists_int] at h_eq
      obtain ⟨k, hk⟩ := h_eq
      exact ⟨k, by
        norm_num [Complex.ext_iff] at hk
        linarith⟩
    exact h_eq.imp fun k hk ↦ by
      rw [hθ, ← hk]
      push_cast
      ring_nf
      norm_num [hn.ne']
  obtain ⟨q, s, hs⟩ : ∃ q : ℤ, ∃ s : ℕ, s < n ∧ k = q * n + s := by
    exact ⟨k / n, Int.toNat (k % n), by
      linarith [Int.emod_lt_of_pos k (by positivity : 0 < (n : ℤ)),
        Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0),
        Int.toNat_of_nonneg
          (Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0))],
      by
        linarith [Int.emod_add_mul_ediv k n,
          Int.toNat_of_nonneg
            (Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0))]⟩
  refine ⟨s, Finset.mem_range.mpr hs.1, hk.trans ?_⟩
  norm_num [hs.2, branch]
  ring_nf
  norm_num [hn.ne']
  ring_nf
  exact Or.inl (Complex.exp_eq_exp_iff_exists_int.mpr ⟨q, by ring⟩)

/-- Distinct branch indices below `n` give distinct roots of the same nonzero
point. -/
lemma branch_index_eq {n : ℕ} (hn : n > 0) {w : ℂ} (hw : w ≠ 0)
    {k l : ℕ} (hk : k < n) (hl : l < n)
    (h : branch n k w = branch n l w) : k = l := by
  have h_exp_eq :
      Complex.exp (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n)) =
        Complex.exp (Complex.I * ((Complex.arg w + 2 * Real.pi * l) / n)) := by
    unfold branch at h
    simp +zetaDelta at *
    refine h.resolve_right ?_
    exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) ((n : ℝ)⁻¹))
  rw [Complex.exp_eq_exp_iff_exists_int] at h_exp_eq
  obtain ⟨m, hm⟩ := h_exp_eq
  rw [Complex.ext_iff] at hm
  simp_all +decide
  have hkl : k = l + m * n := by
    exact_mod_cast
      (by
        nlinarith [Real.pi_pos,
          mul_div_cancel₀ (w.arg + 2 * Real.pi * k)
            (by positivity : (n : ℝ) ≠ 0),
          mul_div_cancel₀ (w.arg + 2 * Real.pi * l)
            (by positivity : (n : ℝ) ≠ 0)] :
      (k : ℝ) = l + m * n)
  nlinarith [show m = 0 by nlinarith]

end Model

/-! ### The open model lemniscate -/

/-- The open lemniscate `|z^n-r^n|<1`.  The closed counterpart is
`Model.S`; its inverse-branch construction is reused below. -/
def openModelSet (n : ℕ) (r : ℝ) : Set ℂ :=
  {z | ‖Model.f n r z‖ < 1}

/-- The part of the `k`-th closed inverse branch which lies in the open
lemniscate. -/
def openModelComponent (n : ℕ) (r : ℝ) (k : ℕ) : Set ℂ :=
  Model.component n r k ∩ openModelSet n r

lemma openModelSet_subset_S (n : ℕ) (r : ℝ) :
    openModelSet n r ⊆ Model.S n r := by
  intro z hz
  change ‖Model.f n r z‖ < 1 at hz
  change ‖Model.f n r z‖ ≤ 1
  exact le_of_lt hz

lemma branch_mem_openModelSet {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r)
    (k : ℕ) {w : ℂ} (hw : w ∈ ball (r ^ n : ℂ) 1) :
    Model.branch n k w ∈ openModelSet n r := by
  rw [openModelSet, Set.mem_setOf_eq, Model.f, Model.branch_pow hn]
  simpa [Complex.dist_eq] using hw

lemma openModel_cover {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    openModelSet n r ⊆ ⋃ k ∈ Finset.range n, openModelComponent n r k := by
  intro z hz
  have hzS : z ∈ Model.S n r := openModelSet_subset_S n r hz
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp (Model.S_subset_union_components hn hr hzS)
  exact Set.mem_iUnion₂.mpr ⟨k, hk, hzk, hz⟩

lemma openModelComponent_eq_image_ball {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r)
    (k : ℕ) :
    openModelComponent n r k =
      Model.branch n k '' ball (r ^ n : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    refine ⟨w, ?_, rfl⟩
    rw [openModelSet, Set.mem_setOf_eq, Model.f, Model.branch_pow hn] at hz
    simpa [Complex.dist_eq] using hz
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, ball_subset_closedBall hw, rfl⟩, branch_mem_openModelSet hn hr k hw⟩

lemma openModelComponent_connected {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r)
    (k : ℕ) : IsConnected (openModelComponent n r k) := by
  rw [openModelComponent_eq_image_ball hn hr]
  have hball : (ball (r ^ n : ℂ) 1).Nonempty :=
    ⟨(r ^ n : ℂ), mem_ball_self (by positivity)⟩
  refine ((convex_ball (r ^ n : ℂ) 1).isConnected hball).image
    (Model.branch n k) ?_
  exact (Model.branch_continuous_on_disk hn hr k).mono ball_subset_closedBall

/-- A branch component, regarded as a subset of the lemniscate subtype. -/
def openModelComponentSubtype (n : ℕ) (r : ℝ) (k : ℕ) :
    Set (openModelSet n r) :=
  {z | z.1 ∈ Model.component n r k}

lemma openModelComponentSubtype_isClosed {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1 < r) (k : ℕ) :
    IsClosed (openModelComponentSubtype n r k) := by
  exact (Model.component_isClosed hn hr k).preimage continuous_subtype_val

lemma openModelComponentSubtype_isOpen {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1 < r) (k : ℕ) (hk : k < n) :
    IsOpen (openModelComponentSubtype n r k) := by
  have hclosed :
      IsClosed (⋃ l ∈ Finset.erase (Finset.range n) k,
        openModelComponentSubtype n r l) := by
    exact isClosed_biUnion_finset fun l _ ↦ openModelComponentSubtype_isClosed hn hr l
  have heq :
      (⋃ l ∈ Finset.erase (Finset.range n) k,
          openModelComponentSubtype n r l) =
        (openModelComponentSubtype n r k)ᶜ := by
    ext z
    constructor
    · intro hz
      obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp hz
      have hlrange : l < n := Finset.mem_range.mp (Finset.mem_of_mem_erase hl)
      have hlne : l ≠ k := (Finset.mem_erase.mp hl).1
      intro hzk
      exact hlne (Model.components_disjoint hn hr l k hlrange hk
        ⟨z.1, hzl, hzk⟩)
    · intro hzk
      have hzcover := openModel_cover hn hr z.2
      obtain ⟨l, hl, hzl, _⟩ := Set.mem_iUnion₂.mp hzcover
      have hlne : l ≠ k := by
        rintro rfl
        exact hzk hzl
      exact Set.mem_iUnion₂.mpr ⟨l, Finset.mem_erase.mpr ⟨hlne, hl⟩, hzl⟩
  rw [← isClosed_compl_iff]
  simpa [← heq] using hclosed

lemma openModelComponentSubtype_connected {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1 < r) (k : ℕ) :
    IsConnected (openModelComponentSubtype n r k) := by
  let e : openModelComponent n r k → openModelSet n r :=
    fun z ↦ ⟨z.1, z.2.2⟩
  have himage : e '' Set.univ = openModelComponentSubtype n r k := by
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2.1
    · intro hz
      exact ⟨⟨z.1, hz, z.2⟩, Set.mem_univ _, rfl⟩
  have he : Continuous e := by
    exact Continuous.subtype_mk continuous_subtype_val
      (fun z : openModelComponent n r k ↦ z.2.2)
  letI : ConnectedSpace (openModelComponent n r k) :=
    Subtype.connectedSpace (openModelComponent_connected hn hr k)
  rw [← himage]
  exact (isConnected_univ : IsConnected (Set.univ :
    Set (openModelComponent n r k))).image e he.continuousOn

lemma openModel_components_pairwise_disjoint {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1 < r) :
    Pairwise (Function.onFun Disjoint
      (fun k : Fin n ↦ openModelComponentSubtype n r k)) := by
  intro i j hij
  change Disjoint (openModelComponentSubtype n r i)
    (openModelComponentSubtype n r j)
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hval : (i : ℕ) = j :=
    Model.components_disjoint hn hr i j i.isLt j.isLt ⟨z.1, hzi, hzj⟩
  exact hij (Fin.ext hval)

lemma openModel_components_cover {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    ⋃ k : Fin n, openModelComponentSubtype n r k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨k, hk, hzk, _⟩ := Set.mem_iUnion₂.mp (openModel_cover hn hr z.2)
  exact Set.mem_iUnion.mpr ⟨⟨k, Finset.mem_range.mp hk⟩, hzk⟩

lemma openModel_componentCount {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    Nat.card (ConnectedComponents (openModelSet n r)) = n := by
  let U : Fin n → Set (openModelSet n r) :=
    fun k ↦ openModelComponentSubtype n r k
  let e : ConnectedComponents (openModelSet n r) ≃ Fin n :=
    ConnectedComponents.equivOfIsClopenOfIsConnected
      (fun k ↦ ⟨openModelComponentSubtype_isClosed hn hr k,
        openModelComponentSubtype_isOpen hn hr k k.isLt⟩)
      (openModel_components_pairwise_disjoint hn hr)
      (openModel_components_cover hn hr)
      (fun k ↦ openModelComponentSubtype_connected hn hr k)
  simpa using Nat.card_congr e

/-- The ordered roots used by the model lemniscate. -/
def modelRoots (n : ℕ) (r : ℝ) (k : Fin n) : ℂ :=
  Model.branch n k (r ^ n)

lemma modelRoots_pow {n : ℕ} (hn : 0 < n) (r : ℝ) (k : Fin n) :
    modelRoots n r k ^ n = (r : ℂ) ^ n := by
  simpa [modelRoots] using Model.branch_pow hn (k : ℕ) (r ^ n : ℂ)

lemma modelRoots_injective {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    Function.Injective (modelRoots n r) := by
  intro i j hij
  apply Fin.ext
  apply Model.components_disjoint hn hr i j i.isLt j.isLt
  refine ⟨modelRoots n r i, ?_, ?_⟩
  · exact ⟨(r ^ n : ℂ), Metric.mem_closedBall_self (by positivity), rfl⟩
  · exact ⟨(r ^ n : ℂ), Metric.mem_closedBall_self (by positivity), hij.symm⟩

/-- Polynomial form of the model. -/
def modelPolynomial (n : ℕ) (r : ℝ) : Polynomial ℂ :=
  X ^ n - C ((r : ℂ) ^ n)

lemma modelPolynomial_monic {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (modelPolynomial n r).Monic := by
  exact monic_X_pow_sub_C _ hn.ne'

lemma modelPolynomial_natDegree {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (modelPolynomial n r).natDegree = n := by
  exact natDegree_X_pow_sub_C

lemma roots_modelPolynomial {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    (modelPolynomial n r).roots =
      (Finset.univ.image (modelRoots n r)).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro w hw
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
    simp [modelPolynomial, modelRoots_pow hn]
  · rw [modelPolynomial_natDegree hn]
    rw [Finset.card_image_of_injective _ (modelRoots_injective hn hr)]
    simp
  · exact (modelPolynomial_monic hn r).ne_zero

lemma rootPolynomial_modelRoots {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    rootPolynomial (modelRoots n r) = modelPolynomial n r := by
  apply Polynomial.funext
  intro w
  rw [eval_rootPolynomial,
    (IsAlgClosed.splits (modelPolynomial n r)).eval_eq_prod_roots_of_monic
      (modelPolynomial_monic hn r), roots_modelPolynomial hn hr]
  change (∏ i, (w - modelRoots n r i)) =
    ∏ x ∈ Finset.image (modelRoots n r) Finset.univ, (w - x)
  rw [Finset.prod_image (modelRoots_injective hn hr).injOn]

lemma unitLemniscate_modelRoots {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    unitLemniscate (rootPolynomial (modelRoots n r)) = openModelSet n r := by
  ext w
  simp [unitLemniscate, openModelSet, rootPolynomial_modelRoots hn hr,
    modelPolynomial, Model.f]

lemma componentCount_modelRoots {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 < r) :
    componentCount (rootPolynomial (modelRoots n r)) = n := by
  unfold componentCount
  rw [unitLemniscate_modelRoots hn hr]
  exact openModel_componentCount hn hr

/-! ### The tangent-disk endpoint `r = 1` -/

/-- The `k`-th inverse-root sheet over the open tangent disk `B(1,1)`. -/
def unitModelComponent (n k : ℕ) : Set ℂ :=
  Model.branch n k '' ball (1 : ℂ) 1

lemma openModelSet_one_pow_mem_ball {n : ℕ} {z : ℂ}
    (hz : z ∈ openModelSet n 1) : z ^ n ∈ ball (1 : ℂ) 1 := by
  rw [Metric.mem_ball, Complex.dist_eq]
  simpa [openModelSet, Model.f] using hz

lemma unitModelComponent_subset {n : ℕ} (hn : 0 < n) (k : ℕ) :
    unitModelComponent n k ⊆ openModelSet n 1 := by
  rintro z ⟨w, hw, rfl⟩
  change ‖Model.branch n k w ^ n - ((1 : ℝ) : ℂ) ^ n‖ < 1
  rw [Model.branch_pow hn]
  simpa [Complex.dist_eq] using hw

lemma unitModel_cover {n : ℕ} (hn : 0 < n) :
    openModelSet n 1 ⊆ ⋃ k ∈ Finset.range n, unitModelComponent n k := by
  intro z hz
  have hw : z ^ n ∈ ball (1 : ℂ) 1 := openModelSet_one_pow_mem_ball hz
  have hw0 : z ^ n ≠ 0 :=
    Complex.slitPlane_ne_zero (Complex.ball_one_subset_slitPlane hw)
  obtain ⟨k, hk, hzk⟩ := Model.exists_branch_eq_of_pow_eq hn rfl hw0
  exact Set.mem_iUnion₂.mpr ⟨k, hk, ⟨z ^ n, hw, hzk.symm⟩⟩

lemma unitModelComponent_connected {n : ℕ} (hn : 0 < n) (k : ℕ) :
    IsConnected (unitModelComponent n k) := by
  have hball : (ball (1 : ℂ) 1).Nonempty :=
    ⟨1, mem_ball_self (by positivity)⟩
  exact ((convex_ball (1 : ℂ) 1).isConnected hball).image
    (Model.branch n k) (Model.branch_continuous_on_unit_ball hn k)

/-- A tangent-disk branch, as an equalizer inside the open lemniscate.  The
equalizer presentation makes relative closedness immediate even though the
disk itself is not compact. -/
def unitModelComponentSubtype (n k : ℕ) : Set (openModelSet n 1) :=
  {z | z.1 = Model.branch n k (z.1 ^ n)}

lemma unitModelComponentSubtype_iff {n : ℕ} (hn : 0 < n) (k : ℕ)
    (z : openModelSet n 1) :
    z ∈ unitModelComponentSubtype n k ↔ z.1 ∈ unitModelComponent n k := by
  constructor
  · intro hz
    exact ⟨z.1 ^ n, openModelSet_one_pow_mem_ball z.2, hz.symm⟩
  · rintro ⟨w, hw, hwz⟩
    change z.1 = Model.branch n k (z.1 ^ n)
    have hpow : z.1 ^ n = w := by
      rw [← hwz, Model.branch_pow hn]
    simpa [hpow] using hwz.symm

lemma continuous_unitModel_branch_on_subtype {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Continuous (fun z : openModelSet n 1 ↦ Model.branch n k (z.1 ^ n)) := by
  exact (Model.branch_continuous_on_unit_ball hn k).comp_continuous
    (continuous_subtype_val.pow n) fun z ↦ openModelSet_one_pow_mem_ball z.2

lemma unitModelComponentSubtype_isClosed {n : ℕ} (hn : 0 < n) (k : ℕ) :
    IsClosed (unitModelComponentSubtype n k) := by
  exact isClosed_eq continuous_subtype_val
    (continuous_unitModel_branch_on_subtype hn k)

lemma unitModel_components_pairwise_disjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (Function.onFun Disjoint
      (fun k : Fin n ↦ unitModelComponentSubtype n k)) := by
  intro i j hij
  change Disjoint (unitModelComponentSubtype n i)
    (unitModelComponentSubtype n j)
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hw0 : z.1 ^ n ≠ 0 := Complex.slitPlane_ne_zero
    (Complex.ball_one_subset_slitPlane (openModelSet_one_pow_mem_ball z.2))
  have hij' : (i : ℕ) = j := Model.branch_index_eq hn hw0 i.isLt j.isLt
    (hzi.symm.trans hzj)
  exact hij (Fin.ext hij')

lemma unitModel_components_cover {n : ℕ} (hn : 0 < n) :
    ⋃ k : Fin n, unitModelComponentSubtype n k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp (unitModel_cover hn z.2)
  exact Set.mem_iUnion.mpr
    ⟨⟨k, Finset.mem_range.mp hk⟩, (unitModelComponentSubtype_iff hn k z).mpr hzk⟩

lemma unitModelComponentSubtype_isOpen {n : ℕ} (hn : 0 < n)
    (k : ℕ) (hk : k < n) : IsOpen (unitModelComponentSubtype n k) := by
  have hclosed :
      IsClosed (⋃ l ∈ Finset.erase (Finset.range n) k,
        unitModelComponentSubtype n l) := by
    exact isClosed_biUnion_finset fun l _ ↦ unitModelComponentSubtype_isClosed hn l
  have heq :
      (⋃ l ∈ Finset.erase (Finset.range n) k,
          unitModelComponentSubtype n l) =
        (unitModelComponentSubtype n k)ᶜ := by
    ext z
    constructor
    · intro hz
      obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp hz
      have hlrange : l < n := Finset.mem_range.mp (Finset.mem_of_mem_erase hl)
      have hlne : l ≠ k := (Finset.mem_erase.mp hl).1
      intro hzk
      have hw0 : z.1 ^ n ≠ 0 := Complex.slitPlane_ne_zero
        (Complex.ball_one_subset_slitPlane (openModelSet_one_pow_mem_ball z.2))
      exact hlne (Model.branch_index_eq hn hw0 hlrange hk
        (hzl.symm.trans hzk))
    · intro hzk
      have hzcover : z ∈ ⋃ l : Fin n, unitModelComponentSubtype n l := by
        rw [unitModel_components_cover hn]
        exact Set.mem_univ z
      obtain ⟨l, hzl⟩ := Set.mem_iUnion.mp hzcover
      have hlne : (l : ℕ) ≠ k := by
        rintro heq
        apply hzk
        simpa [heq] using hzl
      exact Set.mem_iUnion₂.mpr
        ⟨l, Finset.mem_erase.mpr ⟨hlne, Finset.mem_range.mpr l.isLt⟩, hzl⟩
  rw [← isClosed_compl_iff]
  simpa [← heq] using hclosed

lemma unitModelComponentSubtype_connected {n : ℕ} (hn : 0 < n) (k : ℕ) :
    IsConnected (unitModelComponentSubtype n k) := by
  let e : unitModelComponent n k → openModelSet n 1 :=
    fun z ↦ ⟨z.1, unitModelComponent_subset hn k z.2⟩
  have himage : e '' Set.univ = unitModelComponentSubtype n k := by
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩
      exact (unitModelComponentSubtype_iff hn k _).mpr w.2
    · intro hz
      exact ⟨⟨z.1, (unitModelComponentSubtype_iff hn k z).mp hz⟩,
        Set.mem_univ _, rfl⟩
  have he : Continuous e := by
    exact Continuous.subtype_mk continuous_subtype_val
      (fun z : unitModelComponent n k ↦ unitModelComponent_subset hn k z.2)
  letI : ConnectedSpace (unitModelComponent n k) :=
    Subtype.connectedSpace (unitModelComponent_connected hn k)
  rw [← himage]
  exact (isConnected_univ : IsConnected (Set.univ :
    Set (unitModelComponent n k))).image e he.continuousOn

lemma openModel_componentCount_one {n : ℕ} (hn : 0 < n) :
    Nat.card (ConnectedComponents (openModelSet n 1)) = n := by
  let e : ConnectedComponents (openModelSet n 1) ≃ Fin n :=
    ConnectedComponents.equivOfIsClopenOfIsConnected
      (fun k ↦ ⟨unitModelComponentSubtype_isClosed hn k,
        unitModelComponentSubtype_isOpen hn k k.isLt⟩)
      (unitModel_components_pairwise_disjoint hn)
      (unitModel_components_cover hn)
      (fun k ↦ unitModelComponentSubtype_connected hn k)
  simpa using Nat.card_congr e

lemma modelRoots_one_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (modelRoots n 1) := by
  intro i j hij
  apply Fin.ext
  exact Model.branch_index_eq hn one_ne_zero i.isLt j.isLt (by
    simpa [modelRoots] using hij)

lemma roots_modelPolynomial_one {n : ℕ} (hn : 0 < n) :
    (modelPolynomial n 1).roots =
      (Finset.univ.image (modelRoots n 1)).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro w hw
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
    simp [modelPolynomial, modelRoots_pow hn]
  · rw [modelPolynomial_natDegree hn]
    rw [Finset.card_image_of_injective _ (modelRoots_one_injective hn)]
    simp
  · exact (modelPolynomial_monic hn 1).ne_zero

lemma rootPolynomial_modelRoots_one {n : ℕ} (hn : 0 < n) :
    rootPolynomial (modelRoots n 1) = modelPolynomial n 1 := by
  apply Polynomial.funext
  intro w
  rw [eval_rootPolynomial,
    (IsAlgClosed.splits (modelPolynomial n 1)).eval_eq_prod_roots_of_monic
      (modelPolynomial_monic hn 1), roots_modelPolynomial_one hn]
  change (∏ i, (w - modelRoots n 1 i)) =
    ∏ x ∈ Finset.image (modelRoots n 1) Finset.univ, (w - x)
  rw [Finset.prod_image (modelRoots_one_injective hn).injOn]

lemma unitLemniscate_modelRoots_one {n : ℕ} (hn : 0 < n) :
    unitLemniscate (rootPolynomial (modelRoots n 1)) = openModelSet n 1 := by
  ext w
  simp [unitLemniscate, openModelSet, rootPolynomial_modelRoots_one hn,
    modelPolynomial, Model.f]

/-- The roots of `z^n - 1` have exactly `n` open unit-lemniscate
components, including at the tangent endpoint where the closed sheets meet at
the origin. -/
lemma componentCount_modelRoots_one {n : ℕ} (hn : 0 < n) :
    componentCount (rootPolynomial (modelRoots n 1)) = n := by
  unfold componentCount
  rw [unitLemniscate_modelRoots_one hn]
  exact openModel_componentCount_one hn

/-! ### Every component contains a root -/

lemma unitLemniscate_isBounded (p : Polynomial ℂ) (hp : p.Monic)
    (hpdeg : 1 ≤ p.natDegree) : Bornology.IsBounded (unitLemniscate p) := by
  have hgrowth : ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → 1 < ‖p.eval z‖ := by
    have htendsto :
        Tendsto (fun z : ℂ ↦ ‖p.eval z‖)
          (Filter.comap (fun z : ℂ ↦ ‖z‖) atTop) atTop := by
      apply_rules [Polynomial.tendsto_norm_atTop]
      · exact Polynomial.natDegree_pos_iff_degree_pos.mp hpdeg
      · exact Filter.tendsto_comap
    have hevent := htendsto.eventually_gt_atTop 1
    rw [Filter.eventually_comap, Filter.eventually_atTop] at hevent
    obtain ⟨R, hR⟩ := hevent
    exact ⟨R, fun z hz ↦ hR _ hz.le _ rfl⟩
  obtain ⟨R, hR⟩ := hgrowth
  rw [isBounded_iff_forall_norm_le]
  exact ⟨R, fun z hz ↦ not_lt.mp fun h ↦
    (not_le_of_gt (hR z h)) (le_of_lt hz)⟩

lemma frontier_maximal_open_preconnected_subset_compl
    {S : Set ℂ} (hS : IsOpen S) {U : Set ℂ}
    (hU : IsPreconnected U) (hUopen : IsOpen U) (hUS : U ⊆ S)
    (hUne : U.Nonempty)
    (hUmax : ∀ V : Set ℂ, IsPreconnected V → IsOpen V → U ⊆ V → V ⊆ S → V = U) :
    frontier U ⊆ Sᶜ := by
  contrapose! hUmax
  obtain ⟨z, hzfront, hzS⟩ : ∃ z, z ∈ frontier U ∧ z ∈ S := by
    grind
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ball z ε ⊆ S :=
    Metric.isOpen_iff.mp hS z hzS
  obtain ⟨w, hwU, hwball⟩ : ∃ w ∈ U, w ∈ ball z ε := by
    exact Exists.elim
      (mem_closure_iff_nhds_basis Metric.nhds_basis_ball |>.1 hzfront.1 ε hε)
      (fun w hw ↦ ⟨w, hw.1, hw.2⟩)
  refine ⟨U ∪ ball z ε, ?_, ?_, Set.subset_union_left,
    Set.union_subset hUS hball, ?_⟩
  · exact hU.union w hwU hwball (convex_ball z ε).isPreconnected
  · exact hUopen.union Metric.isOpen_ball
  · intro heq
    have hzU : z ∈ U := by
      rw [← heq]
      exact Set.mem_union_right U (mem_ball_self hε)
    have hzinterior : z ∈ interior U :=
      mem_interior_iff_mem_nhds.mpr (hUopen.mem_nhds hzU)
    exact hzfront.2 hzinterior

lemma one_le_norm_eval_of_mem_frontier {p : Polynomial ℂ} {U : Set ℂ}
    (hfront : frontier U ⊆ (unitLemniscate p)ᶜ) {z : ℂ}
    (hz : z ∈ frontier U) : 1 ≤ ‖p.eval z‖ := by
  have hz' := hfront hz
  simpa [unitLemniscate] using hz'

lemma eval_ne_zero_on_closure_of_no_root {p : Polynomial ℂ} {U : Set ℂ}
    (hnoRoot : ∀ z ∈ U, ¬p.IsRoot z)
    (hfront : frontier U ⊆ (unitLemniscate p)ᶜ) :
    ∀ z ∈ closure U, p.eval z ≠ 0 := by
  rw [closure_eq_self_union_frontier]
  intro z hz
  rcases hz with hz | hz
  · exact hnoRoot z hz
  · intro heval
    exact hfront hz (by simp [unitLemniscate, heval])

lemma diffContOnCl_inv_eval_of_ne_zero {p : Polynomial ℂ} {U : Set ℂ}
    (hne : ∀ z ∈ closure U, p.eval z ≠ 0) :
    DiffContOnCl ℂ (fun z ↦ (p.eval z)⁻¹) U := by
  refine ⟨p.differentiable.differentiableOn.inv ?_, ?_⟩
  · exact fun x hx ↦ hne x (subset_closure hx)
  · exact ContinuousOn.inv₀ p.continuous.continuousOn hne

/-- Every maximal open connected piece of a positive-degree monic unit
lemniscate contains a root. -/
theorem component_contains_root (p : Polynomial ℂ) (hp : p.Monic)
    (hpdeg : 1 ≤ p.natDegree) (U : Set ℂ)
    (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUS : U ⊆ unitLemniscate p) (hUne : U.Nonempty)
    (hUmax : ∀ V : Set ℂ, IsPreconnected V → IsOpen V →
      U ⊆ V → V ⊆ unitLemniscate p → V = U) :
    ∃ z ∈ U, p.IsRoot z := by
  by_contra hroot
  have hnoRoot : ∀ z ∈ U, ¬p.IsRoot z := by aesop
  have hfront : frontier U ⊆ (unitLemniscate p)ᶜ :=
    frontier_maximal_open_preconnected_subset_compl
      (isOpen_unitLemniscate p) hU hUopen hUS hUne hUmax
  have hne : ∀ z ∈ closure U, p.eval z ≠ 0 :=
    eval_ne_zero_on_closure_of_no_root hnoRoot hfront
  have hmax : ∀ z ∈ closure U, ‖(p.eval z)⁻¹‖ ≤ 1 := by
    apply_rules [Complex.norm_le_of_forall_mem_frontier_norm_le]
    · exact (unitLemniscate_isBounded p hp hpdeg).subset hUS
    · exact diffContOnCl_inv_eval_of_ne_zero hne
    · intro z hz
      simpa using inv_le_one_of_one_le₀
        (one_le_norm_eval_of_mem_frontier hfront hz)
  obtain ⟨z, hz⟩ := hUne
  have hzsmall : ‖p.eval z‖ < 1 := hUS hz
  have hzpos : 0 < ‖p.eval z‖ := norm_pos_iff.mpr (hnoRoot z hz)
  exact (not_le_of_gt (one_lt_inv₀ hzpos |>.2 hzsmall))
    (by simpa using hmax z (subset_closure hz))

/-- The component occupied by an indexed root. -/
noncomputable def indexedRootComponent {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    ConnectedComponents (unitLemniscate (rootPolynomial z)) :=
  ConnectedComponents.mk ⟨z i, root_mem_unitLemniscate z i⟩

lemma indexedRootComponent_surjective {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) :
    Function.Surjective (indexedRootComponent z) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let U := connectedComponentIn (unitLemniscate (rootPolynomial z)) x.1
  have hxU : x.1 ∈ U := mem_connectedComponentIn x.2
  obtain ⟨y, hyU, hyroot⟩ := component_contains_root
      (rootPolynomial z) (rootPolynomial_monic z)
      (by rw [rootPolynomial_natDegree]; omega) U
      isPreconnected_connectedComponentIn
      (isOpen_unitLemniscate (rootPolynomial z)).connectedComponentIn
      (connectedComponentIn_subset _ _) ⟨x.1, hxU⟩ (by
        intro V hV _ hUV hVS
        apply Set.Subset.antisymm
        · exact hV.subset_connectedComponentIn (hUV hxU) hVS
        · exact hUV)
  rw [Polynomial.IsRoot.def] at hyroot
  rw [eval_rootPolynomial] at hyroot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hyroot
  refine ⟨i, ?_⟩
  change ConnectedComponents.mk ⟨z i, root_mem_unitLemniscate z i⟩ =
    ConnectedComponents.mk x
  rw [ConnectedComponents.coe_eq_coe']
  dsimp [U] at hyU
  rw [connectedComponentIn_eq_image x.2] at hyU
  obtain ⟨y', hy'comp, hy'eq⟩ := hyU
  have hyval : y'.1 = z i := by
    exact hy'eq.trans (sub_eq_zero.mp hi)
  have hy'sub : y' = ⟨z i, root_mem_unitLemniscate z i⟩ := Subtype.ext hyval
  rw [hy'sub] at hy'comp
  simpa [indexedRootComponent] using hy'comp

lemma indexedRootComponent_eq_of_mem_connected {n : ℕ} (z : Fin n → ℂ)
    {B : Set ℂ} (hB : IsConnected B)
    (hBsub : B ⊆ unitLemniscate (rootPolynomial z))
    {i j : Fin n} (hi : z i ∈ B) (hj : z j ∈ B) :
    indexedRootComponent z i = indexedRootComponent z j := by
  let B' : Set (unitLemniscate (rootPolynomial z)) :=
    Subtype.val ⁻¹' B
  have himage : Subtype.val '' B' = B := by
    apply Set.Subset.antisymm
    · rintro x ⟨x', hx', rfl⟩
      exact hx'
    · intro x hx
      exact ⟨⟨x, hBsub hx⟩, hx, rfl⟩
  have hB' : IsPreconnected B' := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [himage]
    exact hB.isPreconnected
  change ConnectedComponents.mk
      (⟨z i, root_mem_unitLemniscate z i⟩ : unitLemniscate (rootPolynomial z)) =
    ConnectedComponents.mk
      (⟨z j, root_mem_unitLemniscate z j⟩ : unitLemniscate (rootPolynomial z))
  rw [ConnectedComponents.coe_eq_coe']
  exact hB'.subset_connectedComponent hj hi

/-- If a nonempty set of indexed roots lies in one connected subset of the
lemniscate, all those indices consume only one component. -/
lemma componentCount_le_sub_card_add_one {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ) (A : Finset (Fin n)) (hA : A.Nonempty)
    {B : Set ℂ} (hB : IsConnected B)
    (hBsub : B ⊆ unitLemniscate (rootPolynomial z))
    (hroots : ∀ i ∈ A, z i ∈ B) :
    componentCount (rootPolynomial z) ≤ n - A.card + 1 := by
  let i₀ : Fin n := hA.choose
  have hi₀A : i₀ ∈ A := hA.choose_spec
  let g : Option {i : Fin n // i ∉ A} →
      ConnectedComponents (unitLemniscate (rootPolynomial z))
    | none => indexedRootComponent z i₀
    | some i => indexedRootComponent z i.1
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨i, hi⟩ := indexedRootComponent_surjective hn z c
    by_cases hiA : i ∈ A
    · refine ⟨none, ?_⟩
      exact (indexedRootComponent_eq_of_mem_connected z hB hBsub
        (hroots i hiA) (hroots i₀ hi₀A)).symm.trans hi
    · exact ⟨some ⟨i, hiA⟩, hi⟩
  unfold componentCount
  calc
    Nat.card (ConnectedComponents (unitLemniscate (rootPolynomial z))) ≤
        Nat.card (Option {i : Fin n // i ∉ A}) :=
      Nat.card_le_card_of_surjective g hg
    _ = n - A.card + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_option,
        Fintype.card_subtype_compl (fun i : Fin n ↦ i ∈ A),
        Fintype.card_subtype]
      simp

/-! ### The asymptotic component gap -/

lemma eventually_component_gap_of_tendsto_empirical
    {K : Set ℂ} (hK : IsCompact K) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hprod : ∀ z : Fin m → K, regularizedDistanceProduct ε z < 1)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) (hn_top : Tendsto n atTop atTop)
    (z : ∀ k, Fin (n k) → K) (μ : ProbabilityMeasure K)
    (hμ : Tendsto (fun k ↦ empiricalProbability (hn k) (z k)) atTop (𝓝 μ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (componentCount (rootPolynomial fun i ↦ ((z k i : K) : ℂ)) : ℝ) ≤
        (1 - c) * n k := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨x, hxsupp, hxpot⟩ :=
    exists_mem_support_regularizedPotential_neg hK hm hε hprod μ
  let a : ℝ := -regularizedPotential ε μ x / 4
  have ha : 0 < a := by dsimp [a]; linarith
  obtain ⟨r, hr, hkernelBall⟩ :=
    exists_ball_regularizedLog_lt_add hK
      (by exact ⟨x, x.2⟩) hε ha (x : ℂ)
  let g := BoundedContinuousFunction.mkOfCompact
    ⟨fun y : K ↦ regularizedLog ε (x : ℂ) (y : ℂ),
      (continuous_regularizedLog hε).comp
        (continuous_const.prodMk continuous_subtype_val)⟩
  have hg_tendsto : Tendsto
      (fun k ↦ ∫ y, g y ∂(empiricalProbability (hn k) (z k) : Measure K))
      atTop (𝓝 (regularizedPotential ε μ x)) := by
    simpa [g, regularizedPotential] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g)
  have hpot_event : ∀ᶠ k in atTop,
      (∫ y, g y ∂(empiricalProbability (hn k) (z k) : Measure K)) <
        regularizedPotential ε μ x / 2 :=
    (tendsto_order.1 hg_tendsto).2 _ (by linarith)
  let G : Set K := {y | (y : ℂ) ∈ ball (x : ℂ) r}
  have hGopen : IsOpen G :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hxGnhds : G ∈ 𝓝 x := hGopen.mem_nhds (mem_ball_self hr)
  have hGpos : 0 < (μ : Measure K) G :=
    (Measure.mem_support_iff_forall x).mp hxsupp G hxGnhds
  let b : ℝ≥0∞ := (μ : Measure K) G / 2
  have hbpos : 0 < b := ENNReal.half_pos hGpos.ne'
  have hbtop : b ≠ ∞ := by
    exact (ENNReal.div_lt_top (measure_ne_top μ G)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).ne
  have hblt : b < (μ : Measure K) G :=
    ENNReal.half_lt_self hGpos.ne' (measure_ne_top μ G)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hGopen
  have hmass_event : ∀ᶠ k in atTop,
      b < (empiricalProbability (hn k) (z k) : Measure K) G :=
    eventually_lt_of_lt_liminf (hblt.trans_le hport)
  have hbReal : 0 < b.toReal := ENNReal.toReal_pos hbpos.ne' hbtop
  let c : ℝ := b.toReal / 2
  have hc : 0 < c := half_pos hbReal
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (1 / c)
  have hn_event : ∀ᶠ k in atTop, N ≤ n k := hn_top (eventually_ge_atTop N)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hpot_event, hmass_event, hn_event] with k hkpot hkmass hkn
  letI : Nonempty (Fin (n k)) := ⟨⟨0, hn k⟩⟩
  let A : Finset (Fin (n k)) :=
    Finset.univ.filter fun i ↦ ((z k i : K) : ℂ) ∈ ball (x : ℂ) r
  have hAcard : b.toReal * n k < (A.card : ℝ) := by
    have hmeasure :
        (empiricalProbability (hn k) (z k) : Measure K) G =
          ((z k ⁻¹' G).ncard : ℝ≥0∞) / n k :=
      empiricalProbability_apply (hn k) (z k) hGopen.measurableSet
    have hratio_top : ((z k ⁻¹' G).ncard : ℝ≥0∞) / n k ≠ ∞ := by
      rw [← hmeasure]
      exact measure_ne_top _ _
    have hreal := (ENNReal.toReal_lt_toReal hbtop hratio_top).2 (by
      rwa [hmeasure] at hkmass)
    have hnreal : (0 : ℝ) < n k := by exact_mod_cast hn k
    have hncard : (z k ⁻¹' G).ncard = A.card := by
      have hset : z k ⁻¹' G = (A : Set (Fin (n k))) := by
        ext i
        simp [A, G]
      rw [hset, Set.ncard_coe_finset]
    change b.toReal < (((z k ⁻¹' G).ncard : ℝ≥0∞) / n k).toReal at hreal
    rw [ENNReal.toReal_div, hncard] at hreal
    norm_num at hreal
    have hbformula : b.toReal = ((μ : Measure K) G).toReal / 2 := by
      simp [b]
    rw [← hbformula] at hreal
    exact (lt_div_iff₀ hnreal).mp hreal
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hAe
    have : A.card = 0 := by simp [hAe]
    rw [this, Nat.cast_zero] at hAcard
    exact (not_lt_of_ge (mul_nonneg hbReal.le (by positivity))) hAcard
  have hsumBall : ∀ w ∈ ball (x : ℂ) r,
      ∑ i, regularizedLog ε w ((z k i : K) : ℂ) < 0 := by
    intro w hw
    have hpoint : ∀ i : Fin (n k),
        regularizedLog ε w ((z k i : K) : ℂ) <
          regularizedLog ε (x : ℂ) ((z k i : K) : ℂ) + a :=
      fun i ↦ hkernelBall w hw (z k i)
    have hsumlt :
        (∑ i, regularizedLog ε w ((z k i : K) : ℂ)) <
          ∑ i, (regularizedLog ε (x : ℂ) ((z k i : K) : ℂ) + a) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ hpoint i
    have hkpot' :
        (∑ i, regularizedLog ε (x : ℂ) ((z k i : K) : ℂ)) / n k <
          regularizedPotential ε μ x / 2 := by
      calc
        _ = ∫ y, regularizedLog ε (x : ℂ) (y : ℂ)
              ∂(empiricalProbability (hn k) (z k) : Measure K) :=
          (integral_empiricalProbability (hn k) (z k)
            ((continuous_regularizedLog hε).comp
              (continuous_const.prodMk continuous_subtype_val))).symm
        _ < _ := by simpa [g] using hkpot
    have hnreal : (0 : ℝ) < n k := by exact_mod_cast hn k
    have hsumx :
        (∑ i, regularizedLog ε (x : ℂ) ((z k i : K) : ℂ)) <
          (regularizedPotential ε μ x / 2) * n k :=
      (div_lt_iff₀ hnreal).mp hkpot'
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsumlt
    dsimp [a] at hsumlt
    nlinarith
  have hballsub : ball (x : ℂ) r ⊆
      unitLemniscate (rootPolynomial fun i ↦ ((z k i : K) : ℂ)) :=
    ball_subset_unitLemniscate_of_regularizedLog_sum_neg hε (z k) (x : ℂ) hsumBall
  have hcomp := componentCount_le_sub_card_add_one (hn k)
    (fun i ↦ ((z k i : K) : ℂ)) A hAne
    (Metric.isConnected_ball hr) hballsub (by
      intro i hi
      simpa [A] using (Finset.mem_filter.mp hi).2)
  have hAcard_le : A.card ≤ n k := by simpa using Finset.card_le_univ A
  have hcompR :
      (componentCount (rootPolynomial fun i ↦ ((z k i : K) : ℂ)) : ℝ) ≤
        n k - A.card + 1 := by
    exact_mod_cast hcomp
  have hlarge : 1 ≤ c * n k := by
    have hcN : 1 / c ≤ n k := hN.trans (by exact_mod_cast hkn)
    calc
      1 = c * (1 / c) := by field_simp
      _ ≤ c * n k := mul_le_mul_of_nonneg_left hcN hc.le
  dsimp [c] at hlarge ⊢
  nlinarith

/-! ### The exact assertions resolved by Ghosh--Ramachandran -/

/-- The asymptotic gap assertion.  This spelling makes the eventual quantifier
explicit: the theorem is not a claim about the finitely many small degrees. -/
def HasUniformComponentGap (K : Set ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z : Fin n → ℂ,
    (∀ i, z i ∈ K) →
      (componentCount (rootPolynomial z) : ℝ) ≤ (1 - c) * n

theorem hasUniformComponentGap_of_transfiniteDiameter_lt_one
    {K : Set ℂ} (hK : IsCompact K) {d : ℝ}
    (hdiam : HasTransfiniteDiameter K d) (hd₀ : 0 < d) (hd₁ : d < 1) :
    HasUniformComponentGap K := by
  classical
  obtain ⟨m, hm, q, hq₀, hq₁, hmq⟩ :=
    exists_feketeDiameter_lt_one hdiam hd₀ hd₁
  obtain ⟨ε, hε, hprod⟩ :=
    exists_regularization_lt_one hK hm hq₀ hq₁ hmq
  by_contra hgap
  have hbad (k : ℕ) :
      ∃ n ≥ k + 1, ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧
        (1 - 1 / (k + 1 : ℝ)) * n <
          (componentCount (rootPolynomial z) : ℝ) := by
    by_contra hnone
    apply hgap
    refine ⟨1 / (k + 1 : ℝ), by positivity, k + 1, ?_⟩
    intro n hnlarge z hzK
    apply le_of_not_gt
    intro hviol
    apply hnone
    exact ⟨n, hnlarge, z, hzK, hviol⟩
  choose n hnlarge z hzK hzbad using hbad
  have hn : ∀ k, 0 < n k := fun k ↦ lt_of_lt_of_le (by omega) (hnlarge k)
  let zK : ∀ k, Fin (n k) → K := fun k i ↦ ⟨z k i, hzK k i⟩
  have hn_top : Tendsto n atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, fun k hk ↦ ?_⟩
    have hklarge := hnlarge k
    omega
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨μ, φ, hφmono, hμ⟩ := CompactSpace.tendsto_subseq
    (fun k ↦ empiricalProbability (hn k) (zK k))
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hnφtop : Tendsto (fun k ↦ n (φ k)) atTop atTop := hn_top.comp hφtop
  obtain ⟨c, hc, hgood⟩ := eventually_component_gap_of_tendsto_empirical
    hK hm hε hprod (fun k ↦ n (φ k)) (fun k ↦ hn (φ k)) hnφtop
    (fun k ↦ zK (φ k)) μ hμ
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / c)
  have hφlarge : ∀ᶠ k in atTop, N ≤ φ k := hφtop (eventually_ge_atTop N)
  obtain ⟨k, hgoodk, hφk⟩ := (hgood.and hφlarge).exists
  have hdenpos : (0 : ℝ) < φ k + 1 := by positivity
  have hrecip : 1 / (φ k + 1 : ℝ) < c := by
    apply (div_lt_iff₀ hdenpos).2
    have hcInv : c * (1 / c) = 1 := by field_simp
    have hNreal : (1 / c : ℝ) < N := hN
    have hNφ : (N : ℝ) ≤ φ k + 1 := by exact_mod_cast (hφk.trans (Nat.le_add_right _ _))
    nlinarith
  have hnreal : (0 : ℝ) < n (φ k) := by exact_mod_cast hn (φ k)
  have hcoeff :
      (1 - c) * n (φ k) <
        (1 - 1 / (φ k + 1 : ℝ)) * n (φ k) := by
    nlinarith
  exact (not_lt_of_ge hgoodk) (hcoeff.trans (hzbad (φ k)))

/-! ### A capacity-one set with maximal lemniscates -/

/-- The unit circle with one isolated outlier.  The outlier forces circumradius
strictly larger than one but, being finite, does not change the transfinite
diameter.  The latter fact is proved directly below from Vandermonde bounds. -/
def capacityOneSet : Set ℂ := sphere (0 : ℂ) 1 ∪ {(2 : ℂ)}

lemma mem_capacityOneSet_iff {z : ℂ} :
    z ∈ capacityOneSet ↔ ‖z‖ = 1 ∨ z = 2 := by
  simpa [capacityOneSet, or_comm]

lemma capacityOneSet_isClosed : IsClosed capacityOneSet :=
  Metric.isClosed_sphere.union isClosed_singleton

lemma mutualDistanceProduct_eq_norm_det_vandermonde {n : ℕ} (z : Fin n → ℂ) :
    mutualDistanceProduct z = ‖(Matrix.vandermonde z).det‖ := by
  rw [Matrix.det_vandermonde, norm_prod]
  simp_rw [norm_prod]
  unfold mutualDistanceProduct
  congr 1
  funext i
  apply Finset.prod_congr rfl
  intro j hj
  rw [norm_sub_rev]

lemma norm_vandermonde_term_le {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, z i ∈ capacityOneSet) (hinj : Function.Injective z)
    (σ : Equiv.Perm (Fin n)) :
    ‖Equiv.Perm.sign σ • ∏ i, Matrix.vandermonde z (σ i) i‖ ≤
      (2 : ℝ) ^ (n - 1) := by
  have hsign (x : ℂ) : ‖Equiv.Perm.sign σ • x‖ = ‖x‖ := by
    change ‖((Equiv.Perm.sign σ : ℤˣ) : ℤ) • x‖ = ‖x‖
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h]
  rw [hsign, norm_prod]
  simp_rw [Matrix.vandermonde_apply, norm_pow]
  by_cases hout : ∃ i : Fin n, z (σ i) = 2
  · obtain ⟨i₀, hi₀⟩ := hout
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    have hrest :
        ∏ i ∈ ({i₀}ᶜ : Finset (Fin n)), ‖z (σ i)‖ ^ (i : ℕ) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hine : i ≠ i₀ := by simpa using hi
      have hnot : z (σ i) ≠ 2 := by
        intro heq
        have : σ i = σ i₀ := hinj (heq.trans hi₀.symm)
        exact hine (σ.injective this)
      rcases mem_capacityOneSet_iff.mp (hz (σ i)) with hone | htwo
      · simp [hone]
      · exact (hnot htwo).elim
    rw [hrest, mul_one, hi₀]
    norm_num [Complex.norm_def, Complex.normSq]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · have hone : ∀ i : Fin n, ‖z (σ i)‖ = 1 := by
      intro i
      rcases mem_capacityOneSet_iff.mp (hz (σ i)) with h | h
      · exact h
      · exact (hout ⟨i, h⟩).elim
    simp [hone]
    exact one_le_pow₀ (by norm_num)

lemma norm_det_vandermonde_capacityOneSet_le {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, z i ∈ capacityOneSet) :
    ‖(Matrix.vandermonde z).det‖ ≤ (n : ℝ) ^ n * (2 : ℝ) ^ n := by
  by_cases hinj : Function.Injective z
  · rw [Matrix.det_apply]
    calc
      ‖∑ σ : Equiv.Perm (Fin n),
          Equiv.Perm.sign σ • ∏ i, Matrix.vandermonde z (σ i) i‖ ≤
          ∑ _σ : Equiv.Perm (Fin n), (2 : ℝ) ^ (n - 1) := by
            exact norm_sum_le_of_le _ fun σ _ ↦ norm_vandermonde_term_le z hz hinj σ
      _ = (n.factorial : ℝ) * (2 : ℝ) ^ (n - 1) := by
        simp [Fintype.card_perm]
      _ ≤ (n : ℝ) ^ n * (2 : ℝ) ^ n := by
        have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
          exact_mod_cast Nat.factorial_le_pow n
        have hpow : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := by
          exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
        exact mul_le_mul hfac hpow (by positivity) (by positivity)
  · have hdet : (Matrix.vandermonde z).det = 0 :=
      Matrix.det_vandermonde_eq_zero_iff.mpr (Function.not_injective_iff.mp hinj)
    rw [hdet, norm_zero]
    positivity

lemma norm_modelRoots_one {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ‖modelRoots n 1 i‖ = 1 := by
  simp [modelRoots, Model.branch]
  rw [Complex.norm_exp]
  norm_num

lemma prod_offdiag_modelRoots_one {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∏ j ∈ Finset.univ.erase i, ‖modelRoots n 1 i - modelRoots n 1 j‖ = n := by
  let p := modelPolynomial n 1
  have hi : modelRoots n 1 i ∈ p.roots := by
    rw [show p = modelPolynomial n 1 by rfl, roots_modelPolynomial_one hn]
    simp
  have hder := (IsAlgClosed.splits p).eval_root_derivative
    (modelPolynomial_monic hn 1) hi
  have herase :
      ((Finset.univ.image (modelRoots n 1)).val.erase (modelRoots n 1 i)) =
        (((Finset.univ.erase i).image (modelRoots n 1)).val) := by
    exact congrArg Finset.val
      (Finset.image_erase (modelRoots_one_injective hn) Finset.univ i).symm
  rw [show p = modelPolynomial n 1 by rfl, roots_modelPolynomial_one hn, herase] at hder
  have hnorm := congrArg norm hder
  simp only [modelPolynomial, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_natCast, norm_pow,
    norm_modelRoots_one hn i, one_pow, mul_one] at hnorm
  change (n : ℝ) = (normHom : ℂ →*₀ ℝ)
    (Multiset.map (fun x ↦ modelRoots n 1 i - x)
      ((Finset.univ.erase i).image (modelRoots n 1)).val).prod at hnorm
  rw [map_multiset_prod (normHom : ℂ →*₀ ℝ), Multiset.map_map] at hnorm
  change (n : ℝ) = ∏ x ∈ (Finset.univ.erase i).image (modelRoots n 1),
    ‖modelRoots n 1 i - x‖ at hnorm
  rw [Finset.prod_image (modelRoots_one_injective hn).injOn] at hnorm
  simpa using hnorm.symm

lemma mutualDistanceProduct_modelRoots_one_sq {n : ℕ} (hn : 0 < n) :
    mutualDistanceProduct (modelRoots n 1) ^ 2 = (n : ℝ) ^ n := by
  let z := modelRoots n 1
  have hoff := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
    (fun i j : Fin n ↦ ‖z i - z j‖)
  calc
    mutualDistanceProduct z ^ 2 =
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          ‖z j - z i‖ * ‖z i - z j‖ := by
      rw [pow_two]
      unfold mutualDistanceProduct
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      rw [norm_sub_rev]
    _ = ∏ i : Fin n, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), ‖z j - z i‖ := hoff
    _ = ∏ _i : Fin n, (n : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hcomp : ({i}ᶜ : Finset (Fin n)) = Finset.univ.erase i := by
        ext j
        simp [Ne, eq_comm]
      rw [hcomp]
      simpa [z, norm_sub_rev] using prod_offdiag_modelRoots_one hn i
    _ = (n : ℝ) ^ n := by simp

lemma one_le_mutualDistanceProduct_modelRoots_one {n : ℕ} (hn : 0 < n) :
    1 ≤ mutualDistanceProduct (modelRoots n 1) := by
  have hsq := mutualDistanceProduct_modelRoots_one_sq hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ n := by
    exact one_le_pow₀ (by exact_mod_cast hn)
  have hnonneg := mutualDistanceProduct_nonneg (modelRoots n 1)
  nlinarith

lemma one_le_feketeValue_modelRoots_one {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ feketeValue (modelRoots n 1) := by
  rw [feketeValue, if_pos hn]
  have hchoose : 0 < (Nat.choose n 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hn
  simpa using Real.rpow_le_rpow
    (by norm_num : (0 : ℝ) ≤ 1)
    (one_le_mutualDistanceProduct_modelRoots_one (by omega))
    (inv_nonneg.mpr hchoose.le)

lemma capacityOneSet_isBounded : Bornology.IsBounded capacityOneSet := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, fun z hz ↦ ?_⟩
  rcases mem_capacityOneSet_iff.mp hz with h | rfl
  · linarith
  · norm_num

lemma one_le_feketeDiameter_capacityOneSet {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ feketeDiameter capacityOneSet n := by
  apply le_csSup_of_le (bddAbove_feketeValues capacityOneSet_isBounded n)
    (show feketeValue (modelRoots n 1) ∈
      {r : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ capacityOneSet) ∧
        r = feketeValue z} from ⟨modelRoots n 1, fun i ↦
          mem_capacityOneSet_iff.mpr (Or.inl
            (norm_modelRoots_one (by omega) i)), rfl⟩)
  exact one_le_feketeValue_modelRoots_one hn

/-- A convenient explicit upper envelope for the Fekete diameters of
`capacityOneSet`. -/
def capacityOneUpper (n : ℕ) : ℝ :=
  Real.rpow (((2 : ℝ) * n) ^ n) ((Nat.choose n 2 : ℝ)⁻¹)

lemma feketeDiameter_capacityOneSet_le_upper {n : ℕ} (hn : 2 ≤ n) :
    feketeDiameter capacityOneSet n ≤ capacityOneUpper n := by
  unfold feketeDiameter
  apply csSup_le
  · refine ⟨feketeValue (fun _ : Fin n ↦ (1 : ℂ)), ?_⟩
    exact ⟨fun _ ↦ 1, fun _ ↦ mem_capacityOneSet_iff.mpr (Or.inl (by simp)), rfl⟩
  · intro b hb
    obtain ⟨z, hzK, rfl⟩ := hb
    rw [feketeValue, if_pos hn]
    unfold capacityOneUpper
    apply Real.rpow_le_rpow (mutualDistanceProduct_nonneg z)
    · calc
        mutualDistanceProduct z = ‖(Matrix.vandermonde z).det‖ :=
          mutualDistanceProduct_eq_norm_det_vandermonde z
        _ ≤ (n : ℝ) ^ n * (2 : ℝ) ^ n :=
          norm_det_vandermonde_capacityOneSet_le z hzK
        _ = ((2 : ℝ) * n) ^ n := by rw [mul_pow]; ring
    · have hchoose : 0 < (Nat.choose n 2 : ℝ) := by
        exact_mod_cast Nat.choose_pos hn
      exact inv_nonneg.mpr hchoose.le

lemma tendsto_capacityOneUpper : Tendsto capacityOneUpper atTop (𝓝 1) := by
  have hx : Tendsto (fun n : ℕ ↦ (2 : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := (tendsto_rpow_div_mul_add (4 : ℝ) 1 (-2) zero_ne_one).comp hx
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  unfold capacityOneUpper
  have hrpow :
      Real.rpow (((2 : ℝ) * n) ^ n) ((Nat.choose n 2 : ℝ)⁻¹) =
        Real.rpow ((2 : ℝ) * n) ((n : ℝ) * (Nat.choose n 2 : ℝ)⁻¹) := by
    calc
      _ = Real.rpow (Real.rpow ((2 : ℝ) * n) (n : ℝ))
          ((Nat.choose n 2 : ℝ)⁻¹) := by
            congr 2
            exact (Real.rpow_natCast _ n).symm
      _ = _ := (Real.rpow_mul (by positivity) _ _).symm
  rw [hrpow]
  change Real.rpow ((2 : ℝ) * n) (4 / (1 * ((2 : ℝ) * n) + -2)) =
    Real.rpow ((2 : ℝ) * n) ((n : ℝ) * (Nat.choose n 2 : ℝ)⁻¹)
  apply congrArg (Real.rpow ((2 : ℝ) * n))
  rw [Nat.cast_choose_two]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 1 by omega))
  have hnp : (n : ℝ) + -1 ≠ 0 := by
    simpa [sub_eq_add_neg] using hnm1
  field_simp [hn0, hnm1, hnp]
  <;> ring

theorem capacityOneSet_hasTransfiniteDiameter :
    HasTransfiniteDiameter capacityOneSet 1 := by
  unfold HasTransfiniteDiameter
  refine ⟨capacityOneSet_isBounded, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_capacityOneUpper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact one_le_feketeDiameter_capacityOneSet hn
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact feketeDiameter_capacityOneSet_le_upper hn

lemma capacityOneSet_not_contained_in_unit_closedBall :
    ¬ ∃ a : ℂ, capacityOneSet ⊆ closedBall a 1 := by
  rintro ⟨a, ha⟩
  have hm : (-1 : ℂ) ∈ capacityOneSet := by
    rw [mem_capacityOneSet_iff]
    left
    norm_num
  have ht : (2 : ℂ) ∈ capacityOneSet := by
    rw [mem_capacityOneSet_iff]
    exact Or.inr rfl
  have hma : dist (-1 : ℂ) a ≤ 1 := by
    simpa [mem_closedBall] using ha hm
  have hta : dist (2 : ℂ) a ≤ 1 := by
    simpa [mem_closedBall] using ha ht
  have htri := dist_triangle (-1 : ℂ) a 2
  have hdist : dist (-1 : ℂ) 2 = 3 := by
    norm_num [Complex.dist_eq, Complex.norm_def, Complex.normSq]
  rw [hdist, dist_comm a 2] at htri
  linarith

/-- A fixed set realizes the maximal possible number of components in
infinitely many degrees. -/
def HasInfinitelyManyMaximalLemniscates (K : Set ℂ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧ ∃ z : Fin n → ℂ,
    (∀ i, z i ∈ K) ∧ componentCount (rootPolynomial z) = n

theorem capacityOneSet_hasInfinitelyManyMaximalLemniscates :
    HasInfinitelyManyMaximalLemniscates capacityOneSet := by
  intro N
  let n := max N 1
  have hn : 0 < n := by simp [n]
  refine ⟨n, le_max_left N 1, hn, modelRoots n 1, ?_, ?_⟩
  · intro i
    rw [mem_capacityOneSet_iff]
    exact Or.inl (norm_modelRoots_one hn i)
  · exact componentCount_modelRoots_one hn

/-! ### The sharp connected-set conclusion -/

lemma mutualDistanceProduct_lastCases {n : ℕ} (z : Fin n → ℂ) (w : ℂ) :
    mutualDistanceProduct (Fin.lastCases w z) =
      mutualDistanceProduct z * ∏ i : Fin n, ‖z i - w‖ := by
  classical
  let z' : Fin (n + 1) → ℂ := Fin.lastCases w z
  have hIoi (i : Fin n) :
      ∏ j ∈ Finset.Ioi i.castSucc,
          ‖z' i.castSucc - z' j‖ =
        (∏ j ∈ Finset.Ioi i, ‖z i - z j‖) * ‖z i - w‖ := by
    have hs : Finset.Ioi i.castSucc =
        insert (Fin.last n) ((Finset.Ioi i).image Fin.castSucc) := by
      ext j
      refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simp
      · simp
        exact fun _ ↦ Fin.le_last _
    rw [hs, Finset.prod_insert]
    · rw [Finset.prod_image (Fin.castSucc_injective n).injOn]
      simp [z', mul_comm]
    · simp
  change mutualDistanceProduct z' = _
  unfold mutualDistanceProduct
  rw [Fin.prod_univ_castSucc]
  have hlast : Finset.Ioi (Fin.last n) = ∅ := by
    ext j
    constructor
    · intro hj
      exact (not_lt_of_ge (Fin.le_last j) (Finset.mem_Ioi.mp hj)).elim
    · intro hj
      simp at hj
  rw [hlast, Finset.prod_empty, mul_one]
  simp_rw [hIoi]
  rw [Finset.prod_mul_distrib]

/-- The Chebyshev minimax inequality in the form needed for the recursive
Fekete construction: a monic polynomial of degree `m` is at least
`2⁻^(m-1)` somewhere on `[-1,1]`. -/
lemma exists_abs_eval_ge_inv_two_pow_of_monic {m : ℕ} (hm : 2 ≤ m)
    (P : ℝ[X]) (hP : P.Monic) (hdeg : P.natDegree = m) :
    ∃ x ∈ Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (m - 1))⁻¹ ≤ |P.eval x| := by
  by_contra h
  push_neg at h
  let A : ℝ := (2 : ℝ) ^ (m - 1)
  let Q : ℝ[X] := Polynomial.C A * P
  have hA : 0 < A := by positivity
  have hQdeg : Q.degree ≤ (m : WithBot ℕ) := by
    change (Polynomial.C A * P).degree ≤ (m : WithBot ℕ)
    rw [Polynomial.degree_C_mul hA.ne']
    simpa [hdeg] using (Polynomial.degree_le_natDegree (p := P))
  have hQbnd : ∀ x ∈ Icc (-1 : ℝ) 1, |Q.eval x| ≤ 1 := by
    intro x hx
    have hx' := h x hx
    change |(Polynomial.C A * P).eval x| ≤ 1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
    rw [abs_of_pos hA]
    exact le_of_lt <| calc
      A * |P.eval x| < A * A⁻¹ := mul_lt_mul_of_pos_left hx' hA
      _ = 1 := mul_inv_cancel₀ hA.ne'
  have hQlead : Q.leadingCoeff = (2 : ℝ) ^ (m - 1) := by
    simpa [Q, A] using hP.leadingCoeff_C_mul ((2 : ℝ) ^ (m - 1))
  have hQT : Q = Polynomial.Chebyshev.T ℝ m :=
    (Polynomial.Chebyshev.leadingCoeff_eq_iff_of_forall_abs_le_one
      hm hQdeg hQbnd).mp hQlead
  have hQone := congrArg (fun R : ℝ[X] ↦ R.eval 1) hQT
  have hAP : A * P.eval 1 = 1 := by
    simpa [Q] using hQone
  have habs := congrArg abs hAP
  have hPeq : |P.eval 1| = A⁻¹ := by
    rw [abs_mul, abs_of_pos hA, abs_one] at habs
    nlinarith [mul_inv_cancel₀ hA.ne']
  have hstrict := h 1 (by simp)
  change |P.eval 1| < A⁻¹ at hstrict
  rw [hPeq] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Recursive real Fekete configurations on `[-1,1]`.  The exponent is the
telescoping sum of the sharp monic minimax constants. -/
lemma exists_interval_fekete_configuration (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : Fin n → ℝ,
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) ∧
      ((2 : ℝ) ^ Nat.choose (n - 1) 2)⁻¹ ≤
        mutualDistanceProduct (fun i ↦ (x i : ℂ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
      let x : Fin 2 → ℝ := ![-1, 1]
      refine ⟨x, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [x]
      · norm_num [mutualDistanceProduct, x, Complex.norm_def, Complex.normSq,
          show Finset.Ioi (1 : Fin 2) = ∅ by decide]
  | succ m hm ih =>
      obtain ⟨x, hx, hV⟩ := ih
      let P : ℝ[X] := ∏ i : Fin m, (Polynomial.X - Polynomial.C (x i))
      have hPmonic : P.Monic := by
        simpa [P] using Polynomial.monic_prod_X_sub_C x Finset.univ
      have hPdeg : P.natDegree = m := by
        simpa [P] using
          (Polynomial.natDegree_finsetProd_X_sub_C_eq_card
            (Finset.univ : Finset (Fin m)) x)
      obtain ⟨y, hyI, hy⟩ :=
        exists_abs_eval_ge_inv_two_pow_of_monic hm P hPmonic hPdeg
      let x' : Fin (m + 1) → ℝ := Fin.lastCases y x
      refine ⟨x', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [x'] using hyI
        · simpa [x'] using hx j
      · have hprod : ((2 : ℝ) ^ (m - 1))⁻¹ ≤
            ∏ i : Fin m, ‖(x i : ℂ) - (y : ℂ)‖ := by
          calc
            ((2 : ℝ) ^ (m - 1))⁻¹ ≤ |P.eval y| := hy
            _ = ∏ i : Fin m, ‖(x i : ℂ) - (y : ℂ)‖ := by
              have hPeval : P.eval y = ∏ i : Fin m, (y - x i) := by
                change Polynomial.eval y (∏ i : Fin m,
                  (Polynomial.X - Polynomial.C (x i))) = _
                have he :=
                  Polynomial.eval_prod (Finset.univ : Finset (Fin m))
                    (fun i ↦ Polynomial.X - Polynomial.C (x i)) y
                rw [he]
                simp
              rw [hPeval, Finset.abs_prod]
              apply Finset.prod_congr rfl
              intro i hi
              rw [show (x i : ℂ) - (y : ℂ) = ((x i - y : ℝ) : ℂ) by norm_num,
                Complex.norm_real]
              exact abs_sub_comm y (x i)
        have hmul :
            ((2 : ℝ) ^ Nat.choose (m - 1) 2)⁻¹ *
                ((2 : ℝ) ^ (m - 1))⁻¹ ≤
              mutualDistanceProduct (fun i ↦ (x i : ℂ)) *
                ∏ i : Fin m, ‖(x i : ℂ) - (y : ℂ)‖ :=
          mul_le_mul hV hprod (by positivity)
            (mutualDistanceProduct_nonneg (fun i ↦ (x i : ℂ)))
        have hx'cast : (fun i ↦ (x' i : ℂ)) =
            Fin.lastCases (y : ℂ) (fun i ↦ (x i : ℂ)) := by
          funext i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [x']
        rw [hx'cast, mutualDistanceProduct_lastCases]
        have hchoose : Nat.choose m 2 = Nat.choose (m - 1) 2 + (m - 1) := by
          conv_lhs => rw [show m = (m - 1) + 1 by omega]
          rw [Nat.choose_succ_succ']
          simp [Nat.add_comm]
        simp only [Nat.add_sub_cancel]
        rw [hchoose, pow_add, mul_inv]
        exact hmul

/-- Signed distance along the oriented line from `a` to `b`. -/
def lineCoordinate (a b z : ℂ) : ℝ :=
  (((z - a) * (starRingEnd ℂ) (b - a)).re) / ‖b - a‖

lemma continuous_lineCoordinate (a b : ℂ) : Continuous (lineCoordinate a b) := by
  unfold lineCoordinate
  fun_prop

lemma lineCoordinate_self_left {a b : ℂ} : lineCoordinate a b a = 0 := by
  simp [lineCoordinate]

lemma lineCoordinate_self_right {a b : ℂ} (hab : a ≠ b) :
    lineCoordinate a b b = ‖b - a‖ := by
  have hnorm : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab.symm)
  unfold lineCoordinate
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change ‖b - a‖ ^ 2 / ‖b - a‖ = ‖b - a‖
  field_simp

lemma abs_lineCoordinate_sub_le {a b : ℂ} (hab : a ≠ b) (z w : ℂ) :
    |lineCoordinate a b z - lineCoordinate a b w| ≤ ‖z - w‖ := by
  have hD : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hrew : lineCoordinate a b z - lineCoordinate a b w =
      (((z - w) * (starRingEnd ℂ) (b - a)).re) / ‖b - a‖ := by
    unfold lineCoordinate
    rw [← sub_div]
    congr 1
    rw [← Complex.sub_re]
    congr 1
    ring
  rw [hrew, abs_div, abs_of_pos hD]
  calc
    |(((z - w) * (starRingEnd ℂ) (b - a)).re)| / ‖b - a‖ ≤
        ‖(z - w) * (starRingEnd ℂ) (b - a)‖ / ‖b - a‖ :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hD.le
    _ = (‖z - w‖ * ‖b - a‖) / ‖b - a‖ := by
      rw [norm_mul, Complex.norm_conj]
    _ = ‖z - w‖ := by field_simp

lemma sum_card_Ioi_fin (n : ℕ) :
    ∑ i : Fin n, (Finset.Ioi i).card = Nat.choose n 2 := by
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i ↦ i) n, Finset.sum_range_id,
    Nat.choose_two_right]

lemma prod_prod_Ioi_const {M : Type*} [CommMonoid M] (n : ℕ) (c : M) :
    (∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, c) = c ^ Nat.choose n 2 := by
  simp_rw [Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum, sum_card_Ioi_fin]

lemma exists_connected_configuration_lower_bound {K : Set ℂ}
    (hK : IsConnected K) {a b : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧
      (‖b - a‖ / 4) ^ Nat.choose n 2 ≤ mutualDistanceProduct z := by
  let D : ℝ := ‖b - a‖
  have hD : 0 < D := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  obtain ⟨x, hxI, hxV⟩ := exists_interval_fekete_configuration n hn
  let t : Fin n → ℝ := fun i ↦ D / 2 * (x i + 1)
  have htI (i : Fin n) : t i ∈ Icc (0 : ℝ) D := by
    rcases hxI i with ⟨hxi0, hxi1⟩
    constructor <;> dsimp [t] <;> nlinarith
  have hIV : Icc (0 : ℝ) D ⊆ lineCoordinate a b '' K := by
    have h := hK.isPreconnected.intermediate_value ha hb
      (continuous_lineCoordinate a b).continuousOn
    simpa [lineCoordinate_self_left, lineCoordinate_self_right hab, D] using h
  have hex (i : Fin n) : ∃ w ∈ K, lineCoordinate a b w = t i := by
    simpa only [mem_image] using hIV (htI i)
  choose z hzK hzcoord using hex
  refine ⟨z, hzK, ?_⟩
  have hpair (i j : Fin n) :
      (D / 2) * ‖(x i : ℂ) - (x j : ℂ)‖ ≤ ‖z i - z j‖ := by
    calc
      (D / 2) * ‖(x i : ℂ) - (x j : ℂ)‖ =
          |(D / 2) * (x i - x j)| := by
        rw [show (x i : ℂ) - (x j : ℂ) = ((x i - x j : ℝ) : ℂ) by norm_num,
          Complex.norm_real, abs_mul, abs_of_pos (by positivity : 0 < D / 2)]
        rw [Real.norm_eq_abs]
      _ = |t i - t j| := by
        congr 1
        simp [t]
        ring
      _ = |lineCoordinate a b (z i) - lineCoordinate a b (z j)| := by
        rw [hzcoord i, hzcoord j]
      _ ≤ ‖z i - z j‖ := abs_lineCoordinate_sub_le hab _ _
  have hscale :
      (D / 2) ^ Nat.choose n 2 *
          mutualDistanceProduct (fun i ↦ (x i : ℂ)) ≤ mutualDistanceProduct z := by
    calc
      (D / 2) ^ Nat.choose n 2 *
          mutualDistanceProduct (fun i ↦ (x i : ℂ)) =
          (∏ i : Fin n, ∏ _j ∈ Finset.Ioi i, D / 2) *
            (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
              ‖(x i : ℂ) - (x j : ℂ)‖) := by
        rw [prod_prod_Ioi_const]
        rfl
      _ = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          ((D / 2) * ‖(x i : ℂ) - (x j : ℂ)‖) := by
        symm
        calc
          _ = ∏ i : Fin n,
              ((∏ _j ∈ Finset.Ioi i, D / 2) *
                ∏ j ∈ Finset.Ioi i, ‖(x i : ℂ) - (x j : ℂ)‖) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [Finset.prod_mul_distrib]
          _ = _ := by rw [Finset.prod_mul_distrib]
      _ ≤ ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z i - z j‖ := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          apply Finset.prod_le_prod
          · intro j hj
            positivity
          · intro j hj
            exact hpair i j
      _ = mutualDistanceProduct z := rfl
  have hbase :
      (D / 2) ^ Nat.choose n 2 *
          (((2 : ℝ) ^ Nat.choose (n - 1) 2)⁻¹) ≤
        mutualDistanceProduct z :=
    (mul_le_mul_of_nonneg_left hxV (by positivity)).trans hscale
  have hpow :
      (D / 4) ^ Nat.choose n 2 ≤
        (D / 2) ^ Nat.choose n 2 *
          (((2 : ℝ) ^ Nat.choose (n - 1) 2)⁻¹) := by
    have hE : Nat.choose (n - 1) 2 ≤ Nat.choose n 2 :=
      Nat.choose_le_choose 2 (Nat.sub_le n 1)
    have htwo :
        ((2 : ℝ) ^ Nat.choose (n - 1) 2) ≤
          (2 : ℝ) ^ Nat.choose n 2 := by
      exact pow_le_pow_right₀ (by norm_num) hE
    have hinv :
        ((2 : ℝ) ^ Nat.choose n 2)⁻¹ ≤
          ((2 : ℝ) ^ Nat.choose (n - 1) 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 htwo
    calc
      (D / 4) ^ Nat.choose n 2 =
          (D / 2) ^ Nat.choose n 2 *
            ((2 : ℝ) ^ Nat.choose n 2)⁻¹ := by
        rw [show D / 4 = (D / 2) / 2 by ring, div_pow, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  exact hpow.trans hbase

lemma quarter_dist_le_feketeDiameter {K : Set ℂ} (hK : IsCompact K)
    (hconn : IsConnected K) {a b : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖b - a‖ / 4 ≤ feketeDiameter K n := by
  obtain ⟨z, hzK, hzV⟩ :=
    exists_connected_configuration_lower_bound hconn ha hb hab n hn
  have hC : Nat.choose n 2 ≠ 0 := Nat.choose_ne_zero hn
  have hq : 0 ≤ ‖b - a‖ / 4 := by positivity
  have hvalue : ‖b - a‖ / 4 ≤ feketeValue z := by
    rw [feketeValue, if_pos hn]
    calc
      ‖b - a‖ / 4 =
          Real.rpow ((‖b - a‖ / 4) ^ Nat.choose n 2)
            ((Nat.choose n 2 : ℝ)⁻¹) := by
        symm
        exact Real.pow_rpow_inv_natCast hq hC
      _ ≤ Real.rpow (mutualDistanceProduct z)
          ((Nat.choose n 2 : ℝ)⁻¹) := by
        apply Real.rpow_le_rpow (pow_nonneg hq _) hzV
        positivity
  exact hvalue.trans (feketeValue_le_feketeDiameter hK.isBounded z hzK)

/-- Pólya's sharp continuum inequality in the exact Fekete-limit language
used in the statement: every chord has length at most four times capacity. -/
theorem dist_le_four_mul_transfiniteDiameter {K : Set ℂ} (hK : IsCompact K)
    (hconn : IsConnected K) {d : ℝ} (hd : HasTransfiniteDiameter K d)
    {a b : ℂ} (ha : a ∈ K) (hb : b ∈ K) :
    ‖b - a‖ ≤ 4 * d := by
  have hevent0 : ∀ᶠ n : ℕ in atTop, 0 ≤ feketeDiameter K n := by
    filter_upwards with n
    let z : Fin n → ℂ := fun _ ↦ a
    have hzvalue : 0 ≤ feketeValue z := by
      unfold feketeValue
      split
      · exact Real.rpow_nonneg (mutualDistanceProduct_nonneg z) _
      · exact le_rfl
    exact hzvalue.trans
      (feketeValue_le_feketeDiameter hK.isBounded z (fun _ ↦ ha))
  have hd0 : 0 ≤ d := ge_of_tendsto hd.2 hevent0
  by_cases hab : a = b
  · simp [hab, hd0]
  have hevent : ∀ᶠ n : ℕ in atTop, ‖b - a‖ / 4 ≤ feketeDiameter K n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact quarter_dist_le_feketeDiameter hK hconn ha hb hab hn
  have hquarter : ‖b - a‖ / 4 ≤ d := ge_of_tendsto hd.2 hevent
  linarith

lemma segment_subset_unitLemniscate_of_pairwise_norm_le_one
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hp : ∀ i j, ‖z i - z j‖ ≤ 1) (i₀ i : Fin n) :
    segment ℝ (z i₀) (z i) ⊆ unitLemniscate (rootPolynomial z) := by
  intro w hw
  rw [segment_eq_image] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  have hfactor (k : Fin n) :
      ‖(1 - t) • z i₀ + t • z i - z k‖ ≤ 1 := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    calc
      ‖(1 - t) • z i₀ + t • z i - z k‖ =
          ‖(1 - t) • (z i₀ - z k) + t • (z i - z k)‖ := by
        congr 1
        module
      _ ≤ ‖(1 - t) • (z i₀ - z k)‖ + ‖t • (z i - z k)‖ :=
        norm_add_le _ _
      _ = (1 - t) * ‖z i₀ - z k‖ + t * ‖z i - z k‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ht1, abs_of_nonneg ht0]
      _ ≤ (1 - t) * 1 + t * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (hp i₀ k) ht1)
          (mul_le_mul_of_nonneg_left (hp i k) ht0)
      _ = 1 := by ring
  change ‖(rootPolynomial z).eval ((1 - t) • z i₀ + t • z i)‖ < 1
  rw [eval_rootPolynomial, Complex.norm_prod]
  obtain ⟨k, hku, hklt⟩ : ∃ k ∈ (Finset.univ : Finset (Fin n)),
      ‖(1 - t) • z i₀ + t • z i - z k‖ < 1 := by
    by_cases htlt : t < 1
    · refine ⟨i₀, Finset.mem_univ _, ?_⟩
      have ht0 : 0 ≤ t := ht.1
      calc
        ‖(1 - t) • z i₀ + t • z i - z i₀‖ = ‖t • (z i - z i₀)‖ := by
          congr 1
          module
        _ = t * ‖z i - z i₀‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        _ ≤ t := by simpa using mul_le_mul_of_nonneg_left (hp i i₀) ht0
        _ < 1 := htlt
    · have htone : t = 1 := le_antisymm ht.2 (not_lt.mp htlt)
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp [htone]
  have herase :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase k,
        ‖(1 - t) • z i₀ + t • z i - z j‖) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j hj
      positivity
    · intro j hj
      exact hfactor j
  calc
    (∏ j : Fin n, ‖(1 - t) • z i₀ + t • z i - z j‖) =
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase k,
          ‖(1 - t) • z i₀ + t • z i - z j‖) *
          ‖(1 - t) • z i₀ + t • z i - z k‖ :=
      (Finset.prod_erase_mul Finset.univ _ hku).symm
    _ ≤ 1 * ‖(1 - t) • z i₀ + t • z i - z k‖ :=
      mul_le_mul_of_nonneg_right herase (norm_nonneg _)
    _ < 1 * 1 := mul_lt_mul_of_pos_left hklt zero_lt_one
    _ = 1 := one_mul 1

theorem componentCount_eq_one_of_pairwise_norm_le_one {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ) (hp : ∀ i j, ‖z i - z j‖ ≤ 1) :
    componentCount (rootPolynomial z) = 1 := by
  let i₀ : Fin n := ⟨0, hn⟩
  letI : Nonempty (Fin n) := ⟨i₀⟩
  let B : Set ℂ := ⋃ i : Fin n, segment ℝ (z i₀) (z i)
  have hBconn : IsConnected B := by
    dsimp [B]
    apply IsConnected.iUnion_of_reflTransGen
    · intro i
      exact (convex_segment (z i₀) (z i)).isConnected
        ⟨z i₀, left_mem_segment ℝ _ _⟩
    · intro i j
      apply Relation.ReflTransGen.single
      exact ⟨z i₀, left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  have hBsub : B ⊆ unitLemniscate (rootPolynomial z) := by
    intro w hw
    simp only [B, mem_iUnion] at hw
    obtain ⟨i, hi⟩ := hw
    exact segment_subset_unitLemniscate_of_pairwise_norm_le_one hn z hp i₀ i hi
  have hroots : ∀ i ∈ (Finset.univ : Finset (Fin n)), z i ∈ B := by
    intro i hi
    exact mem_iUnion.mpr ⟨i, right_mem_segment ℝ _ _⟩
  have hupper := componentCount_le_sub_card_add_one hn z Finset.univ
    Finset.univ_nonempty hBconn hBsub hroots
  haveI : Finite (ConnectedComponents (unitLemniscate (rootPolynomial z))) :=
    Finite.of_surjective (indexedRootComponent z) (indexedRootComponent_surjective hn z)
  haveI : Nonempty (ConnectedComponents (unitLemniscate (rootPolynomial z))) :=
    ⟨indexedRootComponent z i₀⟩
  have hpos : 0 < componentCount (rootPolynomial z) := by
    exact Nat.card_pos
  simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, zero_add] at hupper
  omega

theorem componentCount_eq_one_of_connected_transfiniteDiameter_le_quarter
    {K : Set ℂ} (hK : IsCompact K) (hconn : IsConnected K)
    {d : ℝ} (hd : HasTransfiniteDiameter K d) (hdq : d ≤ 1 / 4)
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) (hzK : ∀ i, z i ∈ K) :
    componentCount (rootPolynomial z) = 1 := by
  apply componentCount_eq_one_of_pairwise_norm_le_one hn z
  intro i j
  calc
    ‖z i - z j‖ ≤ 4 * d :=
      dist_le_four_mul_transfiniteDiameter hK hconn hd (hzK j) (hzK i)
    _ ≤ 1 := by norm_num at hdq ⊢; linarith

/-- The two answers requested in Erdős Problem 1042, together with the sharp
connected small-capacity conclusion in the published resolution. -/
def Erdos1042Resolution : Prop :=
  (∃ K : Set ℂ,
      IsClosed K ∧
      HasTransfiniteDiameter K 1 ∧
      (¬ ∃ a : ℂ, K ⊆ closedBall a 1) ∧
      HasInfinitelyManyMaximalLemniscates K) ∧
  (∀ K : Set ℂ, IsClosed K →
      ∀ d : ℝ, HasTransfiniteDiameter K d → 0 < d → d < 1 →
        HasUniformComponentGap K) ∧
  (∀ K : Set ℂ, IsClosed K → IsConnected K →
      ∀ d : ℝ, HasTransfiniteDiameter K d → d ≤ 1 / 4 →
        ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, z i ∈ K) →
          componentCount (rootPolynomial z) = 1)

/-- Complete formal resolution of Erdős Problem 1042. -/
theorem erdos1042_resolution : Erdos1042Resolution := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨capacityOneSet, capacityOneSet_isClosed,
      capacityOneSet_hasTransfiniteDiameter,
      capacityOneSet_not_contained_in_unit_closedBall,
      capacityOneSet_hasInfinitelyManyMaximalLemniscates⟩
  · intro K hK d hd hd0 hd1
    have hcompact : IsCompact K :=
      isCompact_iff_isClosed_bounded.mpr ⟨hK, hd.1⟩
    exact hasUniformComponentGap_of_transfiniteDiameter_lt_one
      hcompact hd hd0 hd1
  · intro K hK hconn d hd hdq n hn z hzK
    have hcompact : IsCompact K :=
      isCompact_iff_isClosed_bounded.mpr ⟨hK, hd.1⟩
    exact componentCount_eq_one_of_connected_transfiniteDiameter_le_quarter
      hcompact hconn hd hdq hn z hzK

#print axioms erdos1042_resolution

end Erdos1042
