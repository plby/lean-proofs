/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos615.Erdos615BrunnMinkowski

open Set Real MeasureTheory
open scoped ENNReal NNReal Pointwise Topology BigOperators

namespace Erdos615.Construction

lemma packingNumber_ne_top_of_isCompact
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    {ε : ℝ≥0} (hε : ε ≠ 0) (hA : IsCompact A) :
    Metric.packingNumber ε A ≠ ⊤ := by
  rcases Metric.exists_finite_isCover_of_isCompact (s := A) (ε := ε / 2)
      (by positivity) hA with ⟨D, hDA, hDfin, hDcover⟩
  have hp : Metric.packingNumber ε A ≤ D.encard := by
    calc
      Metric.packingNumber ε A = Metric.packingNumber (2 * (ε / 2)) A := by
        congr 2
        field_simp
      _ ≤ Metric.externalCoveringNumber (ε / 2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
      _ ≤ D.encard := hDcover.externalCoveringNumber_le_encard
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hDfin) hp

section Partition

variable (h : ℕ) (ρ : ℝ)

abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin h)) 1

noncomputable def net : Set (Sphere h) :=
  Metric.maximalSeparatedSet (Real.toNNReal ρ) Set.univ

lemma net_finite (hρ : 0 < ρ) : (net h ρ).Finite := by
  rw [← Set.encard_ne_top_iff]
  change (Metric.maximalSeparatedSet (Real.toNNReal ρ)
    (Set.univ : Set (Sphere h))).encard ≠ ⊤
  have htop : Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) ≠ ⊤ :=
    packingNumber_ne_top_of_isCompact (X := Sphere h)
      (A := Set.univ) (ne_of_gt (Real.toNNReal_pos.mpr hρ)) isCompact_univ
  rw [Metric.encard_maximalSeparatedSet htop]
  exact htop

noncomputable def netFintype (hρ : 0 < ρ) : Fintype (net h ρ) :=
  (net_finite h ρ hρ).fintype

noncomputable def netCard (hρ : 0 < ρ) : ℕ :=
  @Fintype.card (net h ρ) (netFintype h ρ hρ)

noncomputable def center (hρ : 0 < ρ) : Fin (netCard h ρ hρ) → Sphere h :=
  fun i ↦ ((@Fintype.equivFin (net h ρ)
    (netFintype h ρ hρ)).symm i : net h ρ).1

lemma center_mem_net (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) :
    center h ρ hρ i ∈ net h ρ :=
  ((@Fintype.equivFin (net h ρ) (netFintype h ρ hρ)).symm i : net h ρ).2

lemma center_injective (hρ : 0 < ρ) :
    Function.Injective (center h ρ hρ) := by
  intro i j hij
  apply (@Fintype.equivFin (net h ρ) (netFintype h ρ hρ)).symm.injective
  apply Subtype.ext
  exact hij

lemma netCard_pos (hh : 0 < h) (hρ : 0 < ρ) : 0 < netCard h ρ hρ := by
  have hsphere : (Set.univ : Set (Sphere h)).Nonempty := by
    let i : Fin h := ⟨0, hh⟩
    refine ⟨⟨EuclideanSpace.single i 1, ?_⟩, Set.mem_univ _⟩
    simp [Metric.mem_sphere, dist_zero_right]
  have hp : 0 < Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) := Metric.packingNumber_pos_iff.mpr hsphere
  have htop := packingNumber_ne_top_of_isCompact
    (A := (Set.univ : Set (Sphere h)))
    (ε := Real.toNNReal ρ) (ne_of_gt (Real.toNNReal_pos.mpr hρ)) isCompact_univ
  have henc : (net h ρ).encard = Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) := Metric.encard_maximalSeparatedSet htop
  have hnonempty : (net h ρ).Nonempty := Set.encard_pos.mp (henc.symm ▸ hp)
  exact (@Fintype.card_pos_iff (net h ρ) (netFintype h ρ hρ)).mpr
    (Set.nonempty_coe_sort.mpr hnonempty)

lemma net_isCover (hρ : 0 < ρ) :
    Metric.IsCover (Real.toNNReal ρ) (Set.univ : Set (Sphere h)) (net h ρ) := by
  have htop : Metric.packingNumber (Real.toNNReal ρ)
      (Set.univ : Set (Sphere h)) ≠ ⊤ :=
    packingNumber_ne_top_of_isCompact (X := Sphere h)
      (A := Set.univ) (ne_of_gt (Real.toNNReal_pos.mpr hρ)) isCompact_univ
  exact Metric.isCover_maximalSeparatedSet htop

lemma center_surjective (hρ : 0 < ρ) (z : Sphere h) (hz : z ∈ net h ρ) :
    ∃ i, center h ρ hρ i = z := by
  let z' : net h ρ := ⟨z, hz⟩
  let i := (@Fintype.equivFin (net h ρ) (netFintype h ρ hρ)) z'
  refine ⟨i, ?_⟩
  simp [center, i, z']

lemma center_cover (hρ : 0 < ρ) (y : Sphere h) :
    ∃ i : Fin (netCard h ρ hρ), dist y (center h ρ hρ i) ≤ ρ := by
  rcases net_isCover h ρ hρ (Set.mem_univ y) with ⟨z, hz, hyz⟩
  rcases center_surjective h ρ hρ z hz with ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  have hd : dist y (center h ρ hρ i) ≤ (Real.toNNReal ρ : ℝ) := by
    exact_mod_cast (edist_le_coe.mp hyz)
  simpa [Real.coe_toNNReal ρ hρ.le] using hd

noncomputable def coveringBall (hρ : 0 < ρ) (n : ℕ) : Set (Sphere h) :=
  if hn : n < netCard h ρ hρ then
    Metric.closedBall (center h ρ hρ ⟨n, hn⟩) ρ
  else ∅

noncomputable def cell (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) : Set (Sphere h) :=
  disjointed (coveringBall h ρ hρ) i

lemma coveringBall_measurable (hρ : 0 < ρ) (n : ℕ) :
    MeasurableSet (coveringBall h ρ hρ n) := by
  unfold coveringBall
  split_ifs
  · exact measurableSet_closedBall
  · exact MeasurableSet.empty

lemma cell_measurable (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) :
    MeasurableSet (cell h ρ hρ i) := by
  exact MeasurableSet.disjointed (coveringBall_measurable h ρ hρ) i

lemma cell_subset_ball (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ)) :
    cell h ρ hρ i ⊆ Metric.closedBall (center h ρ hρ i) ρ := by
  exact (disjointed_subset (coveringBall h ρ hρ) i).trans (by
    simp [coveringBall, i.isLt])

lemma cell_pairwiseDisjoint (hρ : 0 < ρ) :
    Pairwise (fun i j : Fin (netCard h ρ hρ) ↦
      Disjoint (cell h ρ hρ i) (cell h ρ hρ j)) := by
  intro i j hij
  exact disjoint_disjointed (coveringBall h ρ hρ)
    (fun hv ↦ hij (Fin.ext hv))

lemma iUnion_coveringBall (hρ : 0 < ρ) :
    ⋃ n : ℕ, coveringBall h ρ hρ n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases center_cover h ρ hρ y with ⟨i, hi⟩
  refine Set.mem_iUnion.mpr ⟨i.val, ?_⟩
  simp [coveringBall, i.isLt, Metric.mem_closedBall, hi]

lemma iUnion_cell (hρ : 0 < ρ) :
    ⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i = Set.univ := by
  have hall : ⋃ n : ℕ, disjointed (coveringBall h ρ hρ) n = Set.univ := by
    rw [iUnion_disjointed, iUnion_coveringBall h ρ hρ]
  apply Set.eq_univ_of_forall
  intro y
  have hy : y ∈ ⋃ n : ℕ, disjointed (coveringBall h ρ hρ) n := by
    rw [hall]
    trivial
  rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
  have hnlt : n < netCard h ρ hρ := by
    by_contra hnlt
    have hempty : coveringBall h ρ hρ n = ∅ := by
      simp [coveringBall, Nat.not_lt.mp hnlt]
    have : y ∈ coveringBall h ρ hρ n :=
      disjointed_subset (coveringBall h ρ hρ) n hn
    rw [hempty] at this
    exact this
  exact Set.mem_iUnion.mpr ⟨⟨n, hnlt⟩, hn⟩

lemma cell_dist_le_two_mul (hρ : 0 < ρ) (i : Fin (netCard h ρ hρ))
    {x y : Sphere h} (hx : x ∈ cell h ρ hρ i) (hy : y ∈ cell h ρ hρ i) :
    dist x y ≤ 2 * ρ := by
  have hxc := cell_subset_ball h ρ hρ i hx
  have hyc := cell_subset_ball h ρ hρ i hy
  rw [Metric.mem_closedBall] at hxc hyc
  calc
    dist x y ≤ dist x (center h ρ hρ i) + dist (center h ρ hρ i) y :=
      dist_triangle _ _ _
    _ ≤ ρ + ρ := add_le_add hxc (by simpa [dist_comm] using hyc)
    _ = 2 * ρ := by ring

lemma center_dist_gt (hρ : 0 < ρ)
    {i j : Fin (netCard h ρ hρ)} (hij : i ≠ j) :
    ρ < dist (center h ρ hρ i) (center h ρ hρ j) := by
  have hsep := Metric.isSeparated_maximalSeparatedSet
    (A := (Set.univ : Set (Sphere h))) (ε := Real.toNNReal ρ)
  have hed : (Real.toNNReal ρ : ℝ≥0∞) <
      edist (center h ρ hρ i) (center h ρ hρ j) :=
    hsep (center_mem_net h ρ hρ i) (center_mem_net h ρ hρ j)
      ((center_injective h ρ hρ).ne hij)
  rw [edist_dist] at hed
  apply (ENNReal.ofReal_lt_ofReal_iff
    (dist_pos.mpr ((center_injective h ρ hρ).ne hij))).mp
  simpa [ENNReal.ofReal, Real.coe_toNNReal ρ hρ.le] using hed

lemma netCard_mul_ballBound_le (hh : 0 < h) (hρ : 0 < ρ) :
    (netCard h ρ hρ : ℝ≥0∞) *
        (Measure.toSphereBallBound h (ρ / 2) : ℝ≥0∞) ≤ (h : ℝ≥0∞) := by
  let μ : Measure (Sphere h) :=
    (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere
  let q : ℝ≥0∞ := (Measure.toSphereBallBound h (ρ / 2) : ℝ≥0∞)
  let V : ℝ≥0∞ :=
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin h)) 1)
  let balls : Fin (netCard h ρ hρ) → Set (Sphere h) :=
    fun i ↦ Metric.ball (center h ρ hρ i) (ρ / 2)
  have hballs : (Set.univ : Set (Fin (netCard h ρ hρ))).PairwiseDisjoint balls := by
    intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    have hd := center_dist_gt h ρ hρ hij
    linarith
  have hlower (i : Fin (netCard h ρ hρ)) : q * V ≤ μ (balls i) := by
    simpa [q, V, μ, balls, finrank_euclideanSpace_fin] using
      Measure.toSphereBallBound_mul_measure_unitBall_le_toSphere_ball
        (volume : Measure (EuclideanSpace ℝ (Fin h))) (by positivity : 0 < ρ / 2)
        (center h ρ hρ i)
  have hsum : (netCard h ρ hρ : ℝ≥0∞) * (q * V) ≤ μ Set.univ := by
    calc
      (netCard h ρ hρ : ℝ≥0∞) * (q * V) =
          ∑ i : Fin (netCard h ρ hρ), q * V := by simp
      _ ≤ ∑ i : Fin (netCard h ρ hρ), μ (balls i) := by
        exact Finset.sum_le_sum fun i _ ↦ hlower i
      _ = μ (⋃ i ∈ (Finset.univ : Finset (Fin (netCard h ρ hρ))), balls i) := by
        exact (measure_biUnion_finset (f := balls)
          (by simpa using hballs) (fun i _ ↦ measurableSet_ball)).symm
      _ = μ (⋃ i : Fin (netCard h ρ hρ), balls i) := by simp
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  have hVpos : V ≠ 0 := by
    have hv : 0 < volume (Metric.ball
        (0 : EuclideanSpace ℝ (Fin h)) 1) :=
      Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin h)))
        (0 : EuclideanSpace ℝ (Fin h)) zero_lt_one
    exact ne_of_gt (by simpa [V] using hv)
  have hVtop : V ≠ ∞ := by
    exact ne_of_lt (by simpa [V] using
      (measure_ball_lt_top : volume
        (Metric.ball (0 : EuclideanSpace ℝ (Fin h)) 1) < ∞))
  have htotal : μ Set.univ = (h : ℝ≥0∞) * V := by
    simp [μ, V, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  rw [htotal] at hsum
  have : ((netCard h ρ hρ : ℝ≥0∞) * q) * V ≤ (h : ℝ≥0∞) * V := by
    simpa [mul_assoc] using hsum
  simpa [q] using (ENNReal.mul_le_mul_iff_left hVpos hVtop).mp this

lemma netCard_le_pow (hh : 0 < h) (hρ : 0 < ρ) (hρ4 : ρ ≤ 4) :
    (netCard h ρ hρ : ℝ) ≤ (8 / ρ) ^ h := by
  have hq : (Measure.toSphereBallBound h (ρ / 2) : ℝ) =
      (h : ℝ) * (ρ / 8) ^ h := by
    unfold Measure.toSphereBallBound
    rw [if_pos ⟨hh.ne', half_pos hρ⟩]
    norm_cast
    push_cast
    rw [min_eq_left]
    · congr 2
      · rw [Real.coe_toNNReal (ρ / 2) (half_pos hρ).le]
        ring
    · simp only [Real.coe_toNNReal (ρ / 2) (half_pos hρ).le,
        NNReal.coe_ofNat]
      linarith
  have hmain := netCard_mul_ballBound_le h ρ hh hρ
  have hmainReal : (netCard h ρ hρ : ℝ) *
      (Measure.toSphereBallBound h (ρ / 2) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast hmain
  rw [hq] at hmainReal
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hsmall : (netCard h ρ hρ : ℝ) * (ρ / 8) ^ h ≤ 1 := by
    nlinarith
  have hp : 0 < (ρ / 8) ^ h := pow_pos (by positivity) _
  have hinv : (ρ / 8) ^ h * (8 / ρ) ^ h = 1 := by
    rw [← mul_pow]
    have hρne : ρ ≠ 0 := hρ.ne'
    field_simp
    simp
  nlinarith

noncomputable def sphereNonempty (hh : 0 < h) : Nonempty (Sphere h) := by
  let i : Fin h := ⟨0, hh⟩
  exact ⟨⟨EuclideanSpace.single i 1, by simp⟩⟩

noncomputable def sphereFiniteMeasure : FiniteMeasure (Sphere h) :=
  ⟨(volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere, inferInstance⟩

noncomputable def sphereProbability (hh : 0 < h) : ProbabilityMeasure (Sphere h) :=
  letI : Nonempty (Sphere h) := sphereNonempty h hh
  (sphereFiniteMeasure h).normalize

lemma sphereProbability_le_of_toSphere_le (hh : 0 < h)
    (A : Set (Sphere h)) (c : ℝ) (hc : 0 ≤ c)
    (H : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere A ≤
      ENNReal.ofReal c *
        (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere Set.univ) :
    (sphereProbability h hh A : ℝ) ≤ c := by
  let : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  let : Nonempty (Sphere h) := sphereNonempty h hh
  let M := sphereFiniteMeasure h
  let P := sphereProbability h hh
  have Hnn : M A ≤ Real.toNNReal c * M Set.univ := by
    rw [← ENNReal.coe_le_coe]
    simp only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa [M, sphereFiniteMeasure, ENNReal.ofReal] using H
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg (fun N : FiniteMeasure (Sphere h) ↦
      (N : Measure (Sphere h))) hzero
    exact hμ (by simpa [M, sphereFiniteMeasure] using hcoe)
  have hmass : 0 < M.mass := pos_iff_ne_zero.mpr (M.mass_nonzero_iff.mpr hMne)
  have hleft : M A = M.mass * M.normalize A := M.self_eq_mass_mul_normalize A
  have huniv : M Set.univ = M.mass := by simp
  rw [hleft, huniv, mul_comm (Real.toNNReal c) M.mass] at Hnn
  have HP : M.normalize A ≤ Real.toNNReal c :=
    (mul_le_mul_iff_right₀ hmass).mp Hnn
  have hP_eq : M.normalize = P := by rfl
  rw [hP_eq] at HP
  have HPReal : ((P A : ℝ≥0) : ℝ) ≤ (Real.toNNReal c : ℝ) := by
    exact_mod_cast HP
  simpa [P, Real.coe_toNNReal c hc] using HPReal

lemma sphereProbability_strip_bound (hh : 1 < h) (x : EuclideanSpace ℝ (Fin h))
    (hx : ‖x‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    (sphereProbability h (Nat.zero_lt_of_lt hh)
      {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin h))| ≤ t} : ℝ) ≤
        2 * t * Real.sqrt h := by
  have hh0 : 0 < h := Nat.zero_lt_of_lt hh
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh0.ne'
  have hn : 0 < n := by omega
  have H' : (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤ t} ≤
      ENNReal.ofReal (2 * t * Real.sqrt (n + 1)) *
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ :=
    Erdos615.BrunnMinkowski.spherical_equatorial_strip_bound hn x hx t ht
  have HB := sphereProbability_le_of_toSphere_le (n + 1) hh0 _
    (2 * t * Real.sqrt ((n : ℝ) + 1))
    (mul_nonneg (mul_nonneg (by positivity) ht) (Real.sqrt_nonneg _)) H'
  simpa [Nat.cast_succ] using HB

lemma sphereProbability_neg_preimage (hh : 0 < h) (A : Set (Sphere h))
    (hA : MeasurableSet A) :
    sphereProbability h hh ((fun y : Sphere h ↦ -y) ⁻¹' A) =
      sphereProbability h hh A := by
  let : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  let : Nonempty (Sphere h) := sphereNonempty h hh
  let M := sphereFiniteMeasure h
  let P := sphereProbability h hh
  let negS : Sphere h → Sphere h := fun y ↦ -y
  let negE : EuclideanSpace ℝ (Fin h) → EuclideanSpace ℝ (Fin h) := fun y ↦ -y
  have hpreMeas : MeasurableSet (negS ⁻¹' A) := hA.preimage measurable_neg
  have hcone : Set.Ioo (0 : ℝ) 1 • ((↑) '' (negS ⁻¹' A)) =
      negE ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' A)) := by
    ext z
    constructor
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨r, hr, (-(w : EuclideanSpace ℝ (Fin h))), ⟨-w, hw, rfl⟩, ?_⟩
      simp [negE]
    · rintro ⟨r, hr, yr, ⟨w, hw, rfl⟩, hzw⟩
      refine ⟨r, hr, (-(w : EuclideanSpace ℝ (Fin h))),
        ⟨-w, ?_, rfl⟩, ?_⟩
      · simpa [negS] using hw
      · apply neg_injective
        simpa [negE] using hzw
  have Henn : (M : Measure (Sphere h)) (negS ⁻¹' A) =
      (M : Measure (Sphere h)) A := by
    rw [show (M : Measure (Sphere h)) =
      (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere by rfl]
    rw [Measure.toSphere_apply' volume hpreMeas, Measure.toSphere_apply' volume hA,
      hcone]
    congr 1
    have hvol : MeasurePreserving
        (⇑(MeasurableEquiv.neg (EuclideanSpace ℝ (Fin h)))) volume volume :=
      Measure.measurePreserving_neg _
    exact hvol.measure_preimage_equiv _
  have H : M (negS ⁻¹' A) = M A := by
    exact congrArg ENNReal.toNNReal Henn
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg (fun N : FiniteMeasure (Sphere h) ↦
      (N : Measure (Sphere h))) hzero
    exact hμ (by simpa [M, sphereFiniteMeasure] using hcoe)
  have hmass : M.mass ≠ 0 := M.mass_nonzero_iff.mpr hMne
  apply (mul_left_cancel₀ hmass)
  calc
    M.mass * P ((fun y : Sphere h ↦ -y) ⁻¹' A) =
        M ((fun y : Sphere h ↦ -y) ⁻¹' A) :=
      (M.self_eq_mass_mul_normalize _).symm
    _ = M A := H
    _ = M.mass * P A := M.self_eq_mass_mul_normalize A

lemma sphereProbability_positive_inner_bound (hh : 1 < h)
    (x : EuclideanSpace ℝ (Fin h)) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    1 / 2 - 2 * t * Real.sqrt h ≤
      (sphereProbability h (Nat.zero_lt_of_lt hh)
        {y | t < inner ℝ x (y : EuclideanSpace ℝ (Fin h))} : ℝ) := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  let Pos : Set (Sphere h) :=
    {y | t < inner ℝ x (y : EuclideanSpace ℝ (Fin h))}
  let Neg : Set (Sphere h) :=
    {y | inner ℝ x (y : EuclideanSpace ℝ (Fin h)) < -t}
  let Strip : Set (Sphere h) :=
    {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin h))| ≤ t}
  have hPos : MeasurableSet Pos := by
    dsimp only [Pos]
    measurability
  have hNeg : MeasurableSet Neg := by
    dsimp only [Neg]
    measurability
  have hStrip : MeasurableSet Strip := by
    dsimp only [Strip]
    measurability
  have hpre : (fun y : Sphere h ↦ -y) ⁻¹' Pos = Neg := by
    ext y
    change (t < inner ℝ x (-(y : EuclideanSpace ℝ (Fin h)))) ↔
      inner ℝ x (y : EuclideanSpace ℝ (Fin h)) < -t
    rw [inner_neg_right]
    constructor
    · intro H
      linarith
    · intro H
      linarith
  have hsymm : P Pos = P Neg := by
    rw [← hpre, sphereProbability_neg_preimage h (Nat.zero_lt_of_lt hh) Pos hPos]
  have hcover : (Set.univ : Set (Sphere h)) ⊆ Pos ∪ Neg ∪ Strip := by
    intro y hy
    simp only [Set.mem_union, Set.mem_setOf_eq, Pos, Neg, Strip]
    by_cases hp : t < inner ℝ x (y : EuclideanSpace ℝ (Fin h))
    · exact Or.inl (Or.inl hp)
    by_cases hn : inner ℝ x (y : EuclideanSpace ℝ (Fin h)) < -t
    · exact Or.inl (Or.inr hn)
    · right
      rw [abs_le]
      exact ⟨le_of_not_gt hn, le_of_not_gt hp⟩
  have hprobNN : (1 : ℝ≥0) ≤ P Pos + P Neg + P Strip := by
    calc
      (1 : ℝ≥0) = P Set.univ := by simp
      _ ≤ P (Pos ∪ Neg ∪ Strip) := P.apply_mono hcover
      _ ≤ P (Pos ∪ Neg) + P Strip := P.apply_union_le
      _ ≤ P Pos + P Neg + P Strip := by
        gcongr
        exact P.apply_union_le
  have hprob : (1 : ℝ) ≤ (P Pos : ℝ) + (P Neg : ℝ) + (P Strip : ℝ) := by
    exact_mod_cast hprobNN
  have hstrip : (P Strip : ℝ) ≤ 2 * t * Real.sqrt h := by
    simpa [P, Strip] using sphereProbability_strip_bound h hh x hx t ht
  have hsymmR : (P Pos : ℝ) = (P Neg : ℝ) := by exact_mod_cast hsymm
  simpa [P, Pos] using (by nlinarith : 1 / 2 - 2 * t * Real.sqrt h ≤ (P Pos : ℝ))

lemma dist_lt_sqrt_two_sub_of_inner_gt
    {u v : EuclideanSpace ℝ (Fin h)} {β : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (huv : 2 * β < inner ℝ u v) :
    dist u v < Real.sqrt 2 - β := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith
  have hprod : Real.sqrt 2 * β ≤ 2 * β :=
    mul_le_mul_of_nonneg_right hsqrt2 hβ0
  have hd : 0 ≤ Real.sqrt 2 - β := by linarith
  have hsq : ‖u - v‖ ^ 2 < (Real.sqrt 2 - β) ^ 2 := by
    rw [norm_sub_sq_real, hu, hv]
    calc
      1 ^ 2 - 2 * inner ℝ u v + 1 ^ 2 < 2 - 4 * β := by nlinarith
      _ ≤ (Real.sqrt 2 - β) ^ 2 := by nlinarith
  have hnorm : ‖u - v‖ < Real.sqrt 2 - β :=
    (sq_lt_sq₀ (norm_nonneg _) hd).mp hsq
  simpa [dist_eq_norm] using hnorm

lemma sphereProbability_near_fixed_bound (hh : 1 < h)
    (x : Sphere h) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    1 / 2 - 4 * β * Real.sqrt h ≤
      (sphereProbability h (Nat.zero_lt_of_lt hh)
        {y : Sphere h | dist x y < Real.sqrt 2 - β} : ℝ) := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  let Pos : Set (Sphere h) :=
    {y | 2 * β < inner ℝ (x : EuclideanSpace ℝ (Fin h))
      (y : EuclideanSpace ℝ (Fin h))}
  let Near : Set (Sphere h) := {y | dist x y < Real.sqrt 2 - β}
  have hx : ‖(x : EuclideanSpace ℝ (Fin h))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hsub : Pos ⊆ Near := by
    intro y hy
    have hyNorm : ‖(y : EuclideanSpace ℝ (Fin h))‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using y.property
    exact dist_lt_sqrt_two_sub_of_inner_gt (h := h) hx hyNorm hβ0 hβ1 hy
  have hcap := sphereProbability_positive_inner_bound h hh
    (x : EuclideanSpace ℝ (Fin h)) hx (2 * β) (mul_nonneg (by positivity) hβ0)
  have hmonoNN : P Pos ≤ P Near := P.apply_mono hsub
  have hmono : (P Pos : ℝ) ≤ (P Near : ℝ) := by exact_mod_cast hmonoNN
  have H := hcap.trans hmono
  simpa [P, Pos, Near] using (by nlinarith [H] :
    1 / 2 - 4 * β * Real.sqrt h ≤ (P Near : ℝ))

noncomputable def nearPairSet (β : ℝ) : Set (Sphere h × Sphere h) :=
  {z | dist z.1 z.2 < Real.sqrt 2 - β}

lemma nearPairSet_measurable (β : ℝ) : MeasurableSet (nearPairSet h β) := by
  unfold nearPairSet
  measurability

lemma sphereProbability_near_pair_bound (hh : 1 < h)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hsmall : 4 * β * Real.sqrt h ≤ 1 / 2) :
    1 / 2 - 4 * β * Real.sqrt h ≤
      ((sphereProbability h (Nat.zero_lt_of_lt hh)).prod
        (sphereProbability h (Nat.zero_lt_of_lt hh)) (nearPairSet h β) : ℝ) := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  let q : ℝ := 1 / 2 - 4 * β * Real.sqrt h
  have hq : 0 ≤ q := sub_nonneg.mpr hsmall
  have hcond (x : Sphere h) : ENNReal.ofReal q ≤
      (P : Measure (Sphere h)) ((Prod.mk x) ⁻¹' nearPairSet h β) := by
    have hx := sphereProbability_near_fixed_bound h hh x β hβ0 hβ1
    have Hof := ENNReal.ofReal_le_ofReal hx
    simpa [q, P, nearPairSet, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      using Hof
  have Hprod : ENNReal.ofReal q ≤
      ((P : Measure (Sphere h)).prod (P : Measure (Sphere h))) (nearPairSet h β) := by
    rw [Measure.prod_apply (nearPairSet_measurable h β)]
    calc
      ENNReal.ofReal q = ∫⁻ _ : Sphere h, ENNReal.ofReal q ∂(P : Measure (Sphere h)) := by
        simp
      _ ≤ ∫⁻ x : Sphere h,
          (P : Measure (Sphere h)) ((Prod.mk x) ⁻¹' nearPairSet h β)
          ∂(P : Measure (Sphere h)) := lintegral_mono hcond
  have Hcoe : ENNReal.ofReal q ≤ ((P.prod P (nearPairSet h β) : ℝ≥0) : ℝ≥0∞) := by
    simpa [ProbabilityMeasure.toMeasure_prod,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using Hprod
  exact (ENNReal.ofReal_le_coe.mp Hcoe)

noncomputable def weight (hh : 0 < h) (hρ : 0 < ρ)
    (i : Fin (netCard h ρ hρ)) : ℝ :=
  (sphereProbability h hh (cell h ρ hρ i) : ℝ≥0)

lemma weight_nonneg (hh : 0 < h) (hρ : 0 < ρ)
    (i : Fin (netCard h ρ hρ)) : 0 ≤ weight h ρ hh hρ i := by
  exact NNReal.zero_le_coe

lemma sum_weight (hh : 0 < h) (hρ : 0 < ρ) :
    ∑ i : Fin (netCard h ρ hρ), weight h ρ hh hρ i = 1 := by
  let P := sphereProbability h hh
  have hdis : (Set.univ : Set (Fin (netCard h ρ hρ))).PairwiseDisjoint
      (cell h ρ hρ) := by
    intro i hi j hj hij
    exact cell_pairwiseDisjoint h ρ hρ hij
  have hdis' : (↑(Finset.univ : Finset (Fin (netCard h ρ hρ))) :
      Set (Fin (netCard h ρ hρ))).PairwiseDisjoint (cell h ρ hρ) := by
    intro i hi j hj hij
    exact cell_pairwiseDisjoint h ρ hρ hij
  have heq : (P : Measure (Sphere h)) Set.univ =
      ∑ i : Fin (netCard h ρ hρ), (P : Measure (Sphere h)) (cell h ρ hρ i) := by
    calc
      (P : Measure (Sphere h)) Set.univ =
          (P : Measure (Sphere h))
            (⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i) := by
        rw [iUnion_cell h ρ hρ]
      _ = ∑ i : Fin (netCard h ρ hρ),
            (P : Measure (Sphere h)) (cell h ρ hρ i) := by
        simpa using (measure_biUnion_finset (s := Finset.univ)
          (f := cell h ρ hρ) hdis'
          (fun i _ ↦ cell_measurable h ρ hρ i))
  have heq' : (1 : ℝ≥0∞) =
      ∑ i : Fin (netCard h ρ hρ),
        ((P (cell h ρ hρ i) : ℝ≥0) : ℝ≥0∞) := by
    simpa [P, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using heq
  have heqNN : (1 : ℝ≥0) =
      ∑ i : Fin (netCard h ρ hρ), P (cell h ρ hρ i) := by
    exact_mod_cast heq'
  have heqReal := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) heqNN.symm
  simpa [weight, P] using heqReal

abbrev GoodIndexPair (hρ : 0 < ρ) (a : ℝ) :=
  {p : Fin (netCard h ρ hρ) × Fin (netCard h ρ hρ) //
    dist (center h ρ hρ p.1) (center h ρ hρ p.2) < Real.sqrt 2 - a}

noncomputable def goodRegion (hρ : 0 < ρ) (a : ℝ) : Set (Sphere h × Sphere h) :=
  ⋃ p : GoodIndexPair h ρ hρ a,
    cell h ρ hρ p.1.1 ×ˢ cell h ρ hρ p.1.2

lemma goodRegion_measurable (hρ : 0 < ρ) (a : ℝ) :
    MeasurableSet (goodRegion h ρ hρ a) := by
  unfold goodRegion
  exact MeasurableSet.iUnion fun p ↦
    (cell_measurable h ρ hρ p.1.1).prod (cell_measurable h ρ hρ p.1.2)

lemma goodRectangles_pairwiseDisjoint (hρ : 0 < ρ) (a : ℝ) :
    Pairwise fun p q : GoodIndexPair h ρ hρ a ↦
      Disjoint (cell h ρ hρ p.1.1 ×ˢ cell h ρ hρ p.1.2)
        (cell h ρ hρ q.1.1 ×ˢ cell h ρ hρ q.1.2) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro z hzp hzq
  by_cases hi : p.1.1 = q.1.1
  · have hj : p.1.2 ≠ q.1.2 := by
      intro hj
      apply hpq
      apply Subtype.ext
      exact Prod.ext hi hj
    exact (Set.disjoint_left.mp (cell_pairwiseDisjoint h ρ hρ hj)) hzp.2 hzq.2
  · exact (Set.disjoint_left.mp (cell_pairwiseDisjoint h ρ hρ hi)) hzp.1 hzq.1

lemma sum_good_weight_eq_probability (hh : 0 < h) (hρ : 0 < ρ) (a : ℝ) :
    ∑ p : GoodIndexPair h ρ hρ a,
        weight h ρ hh hρ p.1.1 * weight h ρ hh hρ p.1.2 =
      ((sphereProbability h hh).prod (sphereProbability h hh)
        (goodRegion h ρ hρ a) : ℝ) := by
  let P := sphereProbability h hh
  let R : GoodIndexPair h ρ hρ a → Set (Sphere h × Sphere h) :=
    fun p ↦ cell h ρ hρ p.1.1 ×ˢ cell h ρ hρ p.1.2
  have hdis : (↑(Finset.univ : Finset (GoodIndexPair h ρ hρ a)) :
      Set (GoodIndexPair h ρ hρ a)).PairwiseDisjoint R := by
    intro p hp q hq hpq
    exact goodRectangles_pairwiseDisjoint h ρ hρ a hpq
  have heqM : (P.prod P : Measure (Sphere h × Sphere h))
        (goodRegion h ρ hρ a) =
      ∑ p : GoodIndexPair h ρ hρ a,
        (P.prod P : Measure (Sphere h × Sphere h)) (R p) := by
    change (P.prod P : Measure (Sphere h × Sphere h)) (⋃ p, R p) = _
    simpa using (measure_biUnion_finset (μ := (P.prod P : Measure (Sphere h × Sphere h)))
      (s := Finset.univ) (f := R) hdis
      (fun p _ ↦ (cell_measurable h ρ hρ p.1.1).prod
        (cell_measurable h ρ hρ p.1.2)))
  have heqNN : P.prod P (goodRegion h ρ hρ a) =
      ∑ p : GoodIndexPair h ρ hρ a,
        P (cell h ρ hρ p.1.1) * P (cell h ρ hρ p.1.2) := by
    apply ENNReal.coe_injective
    simpa [R, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.toMeasure_prod, Measure.prod_prod] using heqM
  have heqReal := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) heqNN.symm
  simpa [weight, P] using heqReal

lemma nearPairSet_subset_goodRegion (hρ : 0 < ρ) (a : ℝ) :
    nearPairSet h (a + 2 * ρ) ⊆ goodRegion h ρ hρ a := by
  intro z hz
  have hxall : z.1 ∈ ⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i := by
    rw [iUnion_cell h ρ hρ]
    trivial
  have hyall : z.2 ∈ ⋃ i : Fin (netCard h ρ hρ), cell h ρ hρ i := by
    rw [iUnion_cell h ρ hρ]
    trivial
  rcases Set.mem_iUnion.mp hxall with ⟨i, hxi⟩
  rcases Set.mem_iUnion.mp hyall with ⟨j, hyj⟩
  have hxic := cell_subset_ball h ρ hρ i hxi
  have hyjc := cell_subset_ball h ρ hρ j hyj
  rw [Metric.mem_closedBall] at hxic hyjc
  have hgood : dist (center h ρ hρ i) (center h ρ hρ j) < Real.sqrt 2 - a := by
    have htri := dist_triangle4 (center h ρ hρ i) z.1 z.2 (center h ρ hρ j)
    have hnear : dist z.1 z.2 < Real.sqrt 2 - (a + 2 * ρ) := hz
    have hix : dist (center h ρ hρ i) z.1 ≤ ρ := by
      simpa [dist_comm] using hxic
    have hyj' : dist z.2 (center h ρ hρ j) ≤ ρ := by
      simpa [dist_comm] using hyjc
    linarith
  let p : GoodIndexPair h ρ hρ a := ⟨(i, j), hgood⟩
  exact Set.mem_iUnion.mpr ⟨p, ⟨hxi, hyj⟩⟩

lemma sum_good_weight_lower (hh : 1 < h) (hρ : 0 < ρ) (a : ℝ)
    (hβ0 : 0 ≤ a + 2 * ρ) (hβ1 : a + 2 * ρ ≤ 1)
    (hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2) :
    1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h ≤
      ∑ p : GoodIndexPair h ρ hρ a,
        weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.1 *
          weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.2 := by
  let P := sphereProbability h (Nat.zero_lt_of_lt hh)
  have hnear := sphereProbability_near_pair_bound h hh (a + 2 * ρ)
    hβ0 hβ1 hsmall
  have hmonoNN : P.prod P (nearPairSet h (a + 2 * ρ)) ≤
      P.prod P (goodRegion h ρ hρ a) :=
    (P.prod P).apply_mono (nearPairSet_subset_goodRegion h ρ hρ a)
  have hmono : (P.prod P (nearPairSet h (a + 2 * ρ)) : ℝ) ≤
      (P.prod P (goodRegion h ρ hρ a) : ℝ) := by exact_mod_cast hmonoNN
  calc
    1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h ≤
        (P.prod P (goodRegion h ρ hρ a) : ℝ) := hnear.trans hmono
    _ = ∑ p : GoodIndexPair h ρ hρ a,
        weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.1 *
          weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.2 := by
      simpa [P] using
        (sum_good_weight_eq_probability h ρ (Nat.zero_lt_of_lt hh) hρ a).symm

noncomputable def multiplicity (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (i : Fin (netCard h ρ hρ)) : ℕ :=
  ⌊(L : ℝ) * weight h ρ hh hρ i⌋₊ + 1

abbrev CopyVertex (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :=
  Σ i : Fin (netCard h ρ hρ), Fin (multiplicity h ρ hh hρ L i)

abbrev WeightedGoodCopyPair (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ) :=
  Σ p : GoodIndexPair h ρ hρ a,
    Fin (multiplicity h ρ hh hρ L p.1.1) ×
      Fin (multiplicity h ρ hh hρ L p.1.2)

noncomputable def copyCard (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) : ℕ :=
  Fintype.card (CopyVertex h ρ hh hρ L)

lemma multiplicity_lower (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (i : Fin (netCard h ρ hρ)) :
    (L : ℝ) * weight h ρ hh hρ i ≤ multiplicity h ρ hh hρ L i := by
  unfold multiplicity
  simpa using (Nat.lt_floor_add_one
    ((L : ℝ) * weight h ρ hh hρ i)).le

lemma multiplicity_upper (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (i : Fin (netCard h ρ hρ)) :
    (multiplicity h ρ hh hρ L i : ℝ) ≤
      (L : ℝ) * weight h ρ hh hρ i + 1 := by
  unfold multiplicity
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg L)
    (weight_nonneg h ρ hh hρ i))
  simpa using add_le_add_right hf 1

lemma copyCard_eq_sum (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :
    copyCard h ρ hh hρ L =
      ∑ i : Fin (netCard h ρ hρ), multiplicity h ρ hh hρ L i := by
  change Fintype.card (Σ i : Fin (netCard h ρ hρ),
    Fin (multiplicity h ρ hh hρ L i)) = _
  rw [Fintype.card_sigma]
  simp

lemma scale_le_copyCard (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :
    L ≤ copyCard h ρ hh hρ L := by
  have hsum : (L : ℝ) ≤
      ∑ i : Fin (netCard h ρ hρ),
        (multiplicity h ρ hh hρ L i : ℝ) := by
    calc
      (L : ℝ) = ∑ i : Fin (netCard h ρ hρ),
          (L : ℝ) * weight h ρ hh hρ i := by
        rw [← Finset.mul_sum, sum_weight h ρ hh hρ, mul_one]
      _ ≤ ∑ i : Fin (netCard h ρ hρ),
          (multiplicity h ρ hh hρ L i : ℝ) := by
        exact Finset.sum_le_sum fun i _ ↦ multiplicity_lower h ρ hh hρ L i
  rw [copyCard_eq_sum h ρ hh hρ L]
  exact_mod_cast hsum

lemma copyCard_le_scale_add (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) :
    copyCard h ρ hh hρ L ≤ L + netCard h ρ hρ := by
  rw [copyCard_eq_sum h ρ hh hρ L]
  have hsum : (∑ i : Fin (netCard h ρ hρ),
      multiplicity h ρ hh hρ L i : ℝ) ≤
      (L : ℝ) + netCard h ρ hρ := by
    calc
      (∑ i : Fin (netCard h ρ hρ),
          multiplicity h ρ hh hρ L i : ℝ) ≤
          ∑ i : Fin (netCard h ρ hρ),
            ((L : ℝ) * weight h ρ hh hρ i + 1) := by
        exact Finset.sum_le_sum fun i _ ↦ multiplicity_upper h ρ hh hρ L i
      _ = (L : ℝ) + netCard h ρ hρ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_weight h ρ hh hρ, mul_one]
        simp
  exact_mod_cast hsum

lemma weightedGoodCopyPair_card_eq_sum (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Fintype.card (WeightedGoodCopyPair h ρ hh hρ L a) =
      ∑ p : GoodIndexPair h ρ hρ a,
        multiplicity h ρ hh hρ L p.1.1 * multiplicity h ρ hh hρ L p.1.2 := by
  change Fintype.card (Σ p : GoodIndexPair h ρ hρ a,
    Fin (multiplicity h ρ hh hρ L p.1.1) ×
      Fin (multiplicity h ρ hh hρ L p.1.2)) = _
  rw [Fintype.card_sigma]
  simp

lemma scale_sq_mul_sum_good_weight_le_weightedGoodCopyPair_card
    (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ) :
    (L : ℝ) ^ 2 * (∑ p : GoodIndexPair h ρ hρ a,
      weight h ρ hh hρ p.1.1 * weight h ρ hh hρ p.1.2) ≤
        Fintype.card (WeightedGoodCopyPair h ρ hh hρ L a) := by
  rw [weightedGoodCopyPair_card_eq_sum h ρ hh hρ L a]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hi := multiplicity_lower h ρ hh hρ L p.1.1
  have hj := multiplicity_lower h ρ hh hρ L p.1.2
  calc
    (L : ℝ) ^ 2 *
        (weight h ρ hh hρ p.1.1 * weight h ρ hh hρ p.1.2) =
      ((L : ℝ) * weight h ρ hh hρ p.1.1) *
        ((L : ℝ) * weight h ρ hh hρ p.1.2) := by ring
    _ ≤ (multiplicity h ρ hh hρ L p.1.1 : ℝ) *
        multiplicity h ρ hh hρ L p.1.2 := by
      exact mul_le_mul hi hj
        (mul_nonneg (Nat.cast_nonneg L) (weight_nonneg h ρ hh hρ p.1.2))
        (Nat.cast_nonneg _)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_lt_one_sub_half_sq_of_unit_of_dist_gt
    {u v : E} {d : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hd : 0 ≤ d) (huv : d < dist u v) :
    inner ℝ u v < 1 - d ^ 2 / 2 := by
  have hsquare : d ^ 2 < ‖u - v‖ ^ 2 := by
    rw [sq_lt_sq₀ hd (norm_nonneg _)]
    simpa [dist_eq_norm] using huv
  rw [norm_sub_sq_real, hu, hv] at hsquare
  nlinarith

lemma one_sub_half_sq_lt_inner_of_unit_of_dist_lt
    {u v : E} {d : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hd : 0 ≤ d) (huv : dist u v < d) :
    1 - d ^ 2 / 2 < inner ℝ u v := by
  have hsquare : ‖u - v‖ ^ 2 < d ^ 2 := by
    rw [sq_lt_sq₀ (norm_nonneg _) hd]
    simpa [dist_eq_norm] using huv
  rw [norm_sub_sq_real, hu, hv] at hsquare
  nlinarith

lemma no_unit_far_triangle {u v w : E} {a : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (ha0 : 0 ≤ a) (ha4 : a < 1 / 4)
    (huv : 2 - a < dist u v) (huw : 2 - a < dist u w)
    (hvw : 2 - a < dist v w) : False := by
  have hd : 0 ≤ 2 - a := by linarith
  have huv' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hu hv hd huv
  have huw' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hu hw hd huw
  have hvw' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hv hw hd hvw
  have hnonneg : 0 ≤ inner ℝ (u + v + w) (u + v + w) := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, real_inner_comm u v,
    real_inner_comm u w, real_inner_comm v w,
    real_inner_self_eq_norm_sq, hu, hv, hw, one_pow] at hnonneg
  nlinarith

lemma no_unit_far_pair_near_cross {x x' y y' : E} {a : ℝ}
    (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1) (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (ha0 : 0 ≤ a) (ha : a < 2 * (Real.sqrt 2 - 1))
    (hxx : 2 - a < dist x x') (hyy : 2 - a < dist y y')
    (hxy : dist x y < Real.sqrt 2 - a)
    (hxy' : dist x y' < Real.sqrt 2 - a)
    (hx'y : dist x' y < Real.sqrt 2 - a)
    (hx'y' : dist x' y' < Real.sqrt 2 - a) : False := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hdFar : 0 ≤ 2 - a := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdNear : 0 ≤ Real.sqrt 2 - a := by linarith
  have hxx' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hx hx' hdFar hxx
  have hyy' := inner_lt_one_sub_half_sq_of_unit_of_dist_gt hy hy' hdFar hyy
  have hxyI := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx hy hdNear hxy
  have hxy'I := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx hy' hdNear hxy'
  have hx'yI := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx' hy hdNear hx'y
  have hx'y'I := one_sub_half_sq_lt_inner_of_unit_of_dist_lt hx' hy' hdNear hx'y'
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ inner ℝ (x + x' - y - y') (x + x' - y - y') :=
    real_inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_comm x x', real_inner_comm x y, real_inner_comm x y',
    real_inner_comm x' y, real_inner_comm x' y', real_inner_comm y y',
    real_inner_self_eq_norm_sq, hx, hx', hy, hy', one_pow] at hnonneg
  nlinarith

end Geometry

section Graph

lemma four_bool_cases (p₀ p₁ p₂ p₃ : Bool) :
    (p₀ = p₁ ∧ p₀ = p₂) ∨
    (p₀ = p₁ ∧ p₀ = p₃) ∨
    (p₀ = p₂ ∧ p₀ = p₃) ∨
    (p₁ = p₂ ∧ p₁ = p₃) ∨
    (p₀ = p₁ ∧ p₂ = p₃ ∧ p₀ ≠ p₂) ∨
    (p₀ = p₂ ∧ p₁ = p₃ ∧ p₀ ≠ p₁) ∨
    (p₀ = p₃ ∧ p₁ = p₂ ∧ p₀ ≠ p₁) := by
  rcases Bool.eq_false_or_eq_true p₀ with h₀ | h₀ <;>
    rcases Bool.eq_false_or_eq_true p₁ with h₁ | h₁ <;>
    rcases Bool.eq_false_or_eq_true p₂ with h₂ | h₂ <;>
    rcases Bool.eq_false_or_eq_true p₃ with h₃ | h₃ <;> simp_all

noncomputable def position (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (v : CopyVertex h ρ hh hρ L) : Sphere h :=
  center h ρ hρ v.1

def edgeRel (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (u v : Bool × CopyVertex h ρ hh hρ L) : Prop :=
  if u.1 = v.1 then
    2 - a < dist (position h ρ hh hρ L u.2) (position h ρ hh hρ L v.2)
  else
    dist (position h ρ hh hρ L u.2) (position h ρ hh hρ L v.2) <
      Real.sqrt 2 - a

lemma edgeRel_comm (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (u v : Bool × CopyVertex h ρ hh hρ L) :
    edgeRel h ρ hh hρ L a u v ↔ edgeRel h ρ hh hρ L a v u := by
  unfold edgeRel
  rw [dist_comm]
  by_cases huv : u.1 = v.1
  · rw [if_pos huv, if_pos huv.symm]
  · have hvu : v.1 ≠ u.1 := Ne.symm huv
    rw [if_neg huv, if_neg hvu]

noncomputable def BEGraph (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ) :
    SimpleGraph (Bool × CopyVertex h ρ hh hρ L) :=
  SimpleGraph.fromRel (edgeRel h ρ hh hρ L a)

lemma BEGraph_adj_iff (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (u v : Bool × CopyVertex h ρ hh hρ L) :
    (BEGraph h ρ hh hρ L a).Adj u v ↔
      u ≠ v ∧ edgeRel h ρ hh hρ L a u v := by
  rw [BEGraph, SimpleGraph.fromRel_adj]
  simp only [edgeRel_comm h ρ hh hρ L a v u, or_self]

noncomputable def weightedGoodLeftVertex (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (q : WeightedGoodCopyPair h ρ hh hρ L a) :
    Bool × CopyVertex h ρ hh hρ L :=
  (false, ⟨q.1.1.1, q.2.1⟩)

noncomputable def weightedGoodRightVertex (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (q : WeightedGoodCopyPair h ρ hh hρ L a) :
    Bool × CopyVertex h ρ hh hρ L :=
  (true, ⟨q.1.1.2, q.2.2⟩)

lemma weightedGoodEndpoints_injective (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Function.Injective fun q : WeightedGoodCopyPair h ρ hh hρ L a ↦
      (weightedGoodLeftVertex h ρ hh hρ L a q,
        weightedGoodRightVertex h ρ hh hρ L a q) := by
  intro q r hqr
  grind [weightedGoodLeftVertex, weightedGoodRightVertex]

noncomputable def weightedGoodCopyPairToEdge (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (q : WeightedGoodCopyPair h ρ hh hρ L a) :
    (BEGraph h ρ hh hρ L a).edgeSet := by
  let u := weightedGoodLeftVertex h ρ hh hρ L a q
  let v := weightedGoodRightVertex h ρ hh hρ L a q
  refine ⟨s(u, v), ?_⟩
  change (BEGraph h ρ hh hρ L a).Adj u v
  rw [BEGraph_adj_iff]
  refine ⟨?_, ?_⟩
  · intro huv
    have := congrArg Prod.fst huv
    simp [u, v, weightedGoodLeftVertex, weightedGoodRightVertex] at this
  · simpa [edgeRel, u, v, weightedGoodLeftVertex, weightedGoodRightVertex,
      position] using q.1.property

lemma weightedGoodCopyPairToEdge_injective (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Function.Injective (weightedGoodCopyPairToEdge h ρ hh hρ L a) := by
  intro q r hqr
  have hs := congrArg Subtype.val hqr
  change s(weightedGoodLeftVertex h ρ hh hρ L a q,
      weightedGoodRightVertex h ρ hh hρ L a q) =
    s(weightedGoodLeftVertex h ρ hh hρ L a r,
      weightedGoodRightVertex h ρ hh hρ L a r) at hs
  rw [Sym2.eq_iff] at hs
  apply weightedGoodEndpoints_injective h ρ hh hρ L a
  rcases hs with hdir | hswap
  · exact Prod.ext hdir.1 hdir.2
  · exfalso
    have hbool := congrArg Prod.fst hswap.1
    simp [weightedGoodLeftVertex, weightedGoodRightVertex] at hbool

lemma weightedGoodCopyPair_card_le_edges (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) :
    Nat.card (WeightedGoodCopyPair h ρ hh hρ L a) ≤
      Nat.card (BEGraph h ρ hh hρ L a).edgeSet := by
  exact Nat.card_le_card_of_injective
    (weightedGoodCopyPairToEdge h ρ hh hρ L a)
    (weightedGoodCopyPairToEdge_injective h ρ hh hρ L a)

lemma BEGraph_edgeCard_lower (hh : 1 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (hβ0 : 0 ≤ a + 2 * ρ) (hβ1 : a + 2 * ρ ≤ 1)
    (hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2) :
    (L : ℝ) ^ 2 * (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤
      Nat.card (BEGraph h ρ (Nat.zero_lt_of_lt hh) hρ L a).edgeSet := by
  have hsum := sum_good_weight_lower h ρ hh hρ a hβ0 hβ1 hsmall
  have hround := scale_sq_mul_sum_good_weight_le_weightedGoodCopyPair_card
    h ρ (Nat.zero_lt_of_lt hh) hρ L a
  have hcardNat := weightedGoodCopyPair_card_le_edges
    h ρ (Nat.zero_lt_of_lt hh) hρ L a
  have hcard : (Fintype.card (WeightedGoodCopyPair h ρ
      (Nat.zero_lt_of_lt hh) hρ L a) : ℝ) ≤
      Nat.card (BEGraph h ρ (Nat.zero_lt_of_lt hh) hρ L a).edgeSet := by
    rw [Nat.card_eq_fintype_card] at hcardNat
    exact_mod_cast hcardNat
  calc
    (L : ℝ) ^ 2 * (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤
        (L : ℝ) ^ 2 * (∑ p : GoodIndexPair h ρ hρ a,
          weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.1 *
            weight h ρ (Nat.zero_lt_of_lt hh) hρ p.1.2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ Fintype.card (WeightedGoodCopyPair h ρ
        (Nat.zero_lt_of_lt hh) hρ L a) := hround
    _ ≤ Nat.card (BEGraph h ρ (Nat.zero_lt_of_lt hh) hρ L a).edgeSet := hcard

lemma position_norm (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (v : CopyVertex h ρ hh hρ L) :
    ‖(position h ρ hh hρ L v : EuclideanSpace ℝ (Fin h))‖ = 1 := by
  simpa [position, Metric.mem_sphere, dist_zero_right] using
    (position h ρ hh hρ L v).property

lemma BEGraph_cliqueFree_four (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha4 : a < 1 / 4)
    (haMix : a < 2 * (Real.sqrt 2 - 1)) :
    (BEGraph h ρ hh hρ L a).CliqueFree 4 := by
  by_contra hfree
  rcases (SimpleGraph.not_cliqueFree_iff_top_isContained 4).mp hfree with ⟨f⟩
  have hadj (i j : Fin 4) (hij : i ≠ j) :
      (BEGraph h ρ hh hρ L a).Adj (f i) (f j) := by
    exact f.topEmbedding.map_adj_iff.mpr ((SimpleGraph.top_adj i j).mpr hij)
  have hvertex_ne (i j : Fin 4) (hij : i ≠ j) : f i ≠ f j :=
    f.injective.ne hij
  have hfar (i j : Fin 4) (hij : i ≠ j) (hpart : (f i).1 = (f j).1) :
      2 - a < dist (position h ρ hh hρ L (f i).2)
        (position h ρ hh hρ L (f j).2) := by
    have H := (BEGraph_adj_iff h ρ hh hρ L a (f i) (f j)).mp (hadj i j hij)
    simpa [edgeRel, hpart] using H.2
  have hnear (i j : Fin 4) (hij : i ≠ j) (hpart : (f i).1 ≠ (f j).1) :
      dist (position h ρ hh hρ L (f i).2)
          (position h ρ hh hρ L (f j).2) < Real.sqrt 2 - a := by
    have H := (BEGraph_adj_iff h ρ hh hρ L a (f i) (f j)).mp (hadj i j hij)
    simpa [edgeRel, hpart] using H.2
  have htri (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hpij : (f i).1 = (f j).1) (hpik : (f i).1 = (f k).1) : False := by
    apply no_unit_far_triangle
      (position_norm h ρ hh hρ L (f i).2)
      (position_norm h ρ hh hρ L (f j).2)
      (position_norm h ρ hh hρ L (f k).2) ha0 ha4
    · exact hfar i j hij hpij
    · exact hfar i k hik hpik
    · exact hfar j k hjk (hpij.symm.trans hpik)
  have hmix (i i' j j' : Fin 4)
      (hii' : i ≠ i') (hjj' : j ≠ j')
      (hij : i ≠ j) (hij' : i ≠ j') (hi'j : i' ≠ j) (hi'j' : i' ≠ j')
      (hpi : (f i).1 = (f i').1) (hpj : (f j).1 = (f j').1)
      (hpij : (f i).1 ≠ (f j).1) : False := by
    apply no_unit_far_pair_near_cross
      (position_norm h ρ hh hρ L (f i).2)
      (position_norm h ρ hh hρ L (f i').2)
      (position_norm h ρ hh hρ L (f j).2)
      (position_norm h ρ hh hρ L (f j').2) ha0 haMix
    · exact hfar i i' hii' hpi
    · exact hfar j j' hjj' hpj
    · exact hnear i j hij hpij
    · exact hnear i j' hij' (fun H ↦ hpij (H.trans hpj.symm))
    · exact hnear i' j hi'j (fun H ↦ hpij (hpi.trans H))
    · exact hnear i' j' hi'j' (fun H ↦ hpij (hpi.trans (H.trans hpj.symm)))
  rcases four_bool_cases (f 0).1 (f 1).1 (f 2).1 (f 3).1 with
    h012 | h013 | h023 | h123 | h01_23 | h02_13 | h03_12
  · exact htri 0 1 2 (by decide) (by decide) (by decide) h012.1 h012.2
  · exact htri 0 1 3 (by decide) (by decide) (by decide) h013.1 h013.2
  · exact htri 0 2 3 (by decide) (by decide) (by decide) h023.1 h023.2
  · exact htri 1 2 3 (by decide) (by decide) (by decide) h123.1 h123.2
  · exact hmix 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h01_23.1 h01_23.2.1 h01_23.2.2
  · exact hmix 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h02_13.1 h02_13.2.1 h02_13.2.2
  · exact hmix 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h03_12.1 h03_12.2.1 h03_12.2.2

noncomputable def cellUnion (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) : Set (Sphere h) :=
  ⋃ i ∈ J, cell h ρ hρ i

lemma cellUnion_measurable (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) :
    MeasurableSet (cellUnion h ρ hρ J) := by
  exact Finset.measurableSet_biUnion J fun i _ ↦ cell_measurable h ρ hρ i

lemma sum_weight_finset_eq_probability (hh : 0 < h) (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) :
    ∑ i ∈ J, weight h ρ hh hρ i =
      (sphereProbability h hh (cellUnion h ρ hρ J) : ℝ≥0) := by
  let P := sphereProbability h hh
  have hdis : (↑J : Set (Fin (netCard h ρ hρ))).PairwiseDisjoint
      (cell h ρ hρ) := by
    intro i hi j hj hij
    exact cell_pairwiseDisjoint h ρ hρ hij
  have heq : (P : Measure (Sphere h)) (cellUnion h ρ hρ J) =
      ∑ i ∈ J, (P : Measure (Sphere h)) (cell h ρ hρ i) := by
    exact measure_biUnion_finset hdis
      (fun i _ ↦ cell_measurable h ρ hρ i)
  have heq' : ((P (cellUnion h ρ hρ J) : ℝ≥0) : ℝ≥0∞) =
      ∑ i ∈ J, ((P (cell h ρ hρ i) : ℝ≥0) : ℝ≥0∞) := by
    simpa [P, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using heq
  have heqNN : P (cellUnion h ρ hρ J) =
      ∑ i ∈ J, P (cell h ρ hρ i) := by
    exact_mod_cast heq'
  have heqReal := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) heqNN.symm
  simpa [weight, P] using heqReal

lemma sphereProbability_le_isodiametric (hh : 0 < h)
    (A : Set (Sphere h)) (hA : MeasurableSet A) (d : ℝ) (hd1 : 1 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    (sphereProbability h hh A : ℝ) ≤ (d / 2) ^ h := by
  let : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  let : Nonempty (Sphere h) := sphereNonempty h hh
  let M := sphereFiniteMeasure h
  let P := sphereProbability h hh
  have hc : 0 ≤ (d / 2) ^ h := pow_nonneg (by linarith) _
  have H := Erdos615.BrunnMinkowski.sphere_isodiametric hh A hA d hd1 hdiam
  have Hnn : M A ≤ Real.toNNReal ((d / 2) ^ h) * M Set.univ := by
    rw [← ENNReal.coe_le_coe]
    simp only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa [M, sphereFiniteMeasure, ENNReal.ofReal] using H
  have hMne : M ≠ 0 := by
    have hμ : (volume : Measure (EuclideanSpace ℝ (Fin h))).toSphere ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin h)))
    intro hzero
    have hcoe := congrArg (fun N : FiniteMeasure (Sphere h) ↦ (N : Measure (Sphere h))) hzero
    exact hμ (by simpa [M, sphereFiniteMeasure] using hcoe)
  have hmass : 0 < M.mass := pos_iff_ne_zero.mpr (M.mass_nonzero_iff.mpr hMne)
  have hleft : M A = M.mass * M.normalize A := M.self_eq_mass_mul_normalize A
  have huniv : M Set.univ = M.mass := by simp
  rw [hleft, huniv, mul_comm (Real.toNNReal ((d / 2) ^ h)) M.mass] at Hnn
  have HP : M.normalize A ≤ Real.toNNReal ((d / 2) ^ h) :=
    (mul_le_mul_iff_right₀ hmass).mp Hnn
  have hP_eq : M.normalize = P := by
    rfl
  rw [hP_eq] at HP
  have HPReal : ((P A : ℝ≥0) : ℝ) ≤
      (Real.toNNReal ((d / 2) ^ h) : ℝ) := by exact_mod_cast HP
  simpa [P, Real.coe_toNNReal ((d / 2) ^ h) hc] using HPReal

lemma cellUnion_weight_isodiametric (hh : 0 < h) (hρ : 0 < ρ)
    (J : Finset (Fin (netCard h ρ hρ))) (a : ℝ)
    (hd1 : 1 ≤ 2 - a + 2 * ρ)
    (hcenters : ∀ i ∈ J, ∀ j ∈ J,
      dist (center h ρ hρ i) (center h ρ hρ j) ≤ 2 - a) :
    ∑ i ∈ J, weight h ρ hh hρ i ≤ ((2 - a + 2 * ρ) / 2) ^ h := by
  rw [sum_weight_finset_eq_probability h ρ hh hρ J]
  apply sphereProbability_le_isodiametric h hh
    (cellUnion h ρ hρ J) (cellUnion_measurable h ρ hρ J)
    (2 - a + 2 * ρ) hd1
  intro x hx y hy
  simp only [cellUnion, Set.mem_iUnion] at hx hy
  rcases hx with ⟨i, hiJ, hxi⟩
  rcases hy with ⟨j, hjJ, hyj⟩
  have hxc := cell_subset_ball h ρ hρ i hxi
  have hyc := cell_subset_ball h ρ hρ j hyj
  rw [Metric.mem_closedBall] at hxc hyc
  calc
    dist x y ≤ dist x (center h ρ hρ i) +
        dist (center h ρ hρ i) (center h ρ hρ j) +
        dist (center h ρ hρ j) y := by
      linarith [dist_triangle x (center h ρ hρ i) y,
        dist_triangle (center h ρ hρ i) (center h ρ hρ j) y]
    _ ≤ ρ + (2 - a) + ρ := by
      gcongr
      · exact hcenters i hiJ j hjJ
      · simpa [dist_comm] using hyc
    _ = 2 - a + 2 * ρ := by ring

noncomputable def partSet (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L)) (b : Bool) :=
  s.filter fun v ↦ v.1 = b

noncomputable def representedCells (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L)) (b : Bool) :
    Finset (Fin (netCard h ρ hρ)) :=
  (partSet h ρ hh hρ L s b).image fun v ↦ v.2.1

lemma partSet_card_le_sum_multiplicity (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L)) (b : Bool) :
    (partSet h ρ hh hρ L s b).card ≤
      ∑ i ∈ representedCells h ρ hh hρ L s b,
        multiplicity h ρ hh hρ L i := by
  classical
  let S := partSet h ρ hh hρ L s b
  let J := representedCells h ρ hh hρ L s b
  let U := Σ i : {i // i ∈ J}, Fin (multiplicity h ρ hh hρ L i.1)
  let F : S → U := fun v ↦
    ⟨⟨v.1.2.1, by
      apply Finset.mem_image.mpr
      exact ⟨v.1, v.2, rfl⟩⟩, v.1.2.2⟩
  have hF : Function.Injective F := by
    intro u v huv
    apply Subtype.ext
    apply Prod.ext
    · have huPart : u.1.1 = b := (Finset.mem_filter.mp u.2).2
      have hvPart : v.1.1 = b := (Finset.mem_filter.mp v.2).2
      exact huPart.trans hvPart.symm
    · let back : U → CopyVertex h ρ hh hρ L := fun z ↦ ⟨z.1.1, z.2⟩
      exact congrArg back huv
  have hcard := Fintype.card_le_of_injective F hF
  calc
    S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card U := hcard
    _ = ∑ i : {i // i ∈ J}, multiplicity h ρ hh hρ L i.1 := by
      change Fintype.card (Σ i : {i // i ∈ J},
        Fin (multiplicity h ρ hh hρ L i.1)) = _
      rw [Fintype.card_sigma]
      simp
    _ = ∑ i ∈ J, multiplicity h ρ hh hρ L i := by
      exact (Finset.sum_subtype J (fun _ ↦ Iff.rfl)
        (multiplicity h ρ hh hρ L)).symm

lemma independent_represented_center_dist (hh : 0 < h) (hρ : 0 < ρ)
    (L : ℕ) (a : ℝ) (ha2 : a ≤ 2)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L))
    (hs : (BEGraph h ρ hh hρ L a).IsIndepSet s) (b : Bool)
    (i : Fin (netCard h ρ hρ)) (hi : i ∈ representedCells h ρ hh hρ L s b)
    (j : Fin (netCard h ρ hρ)) (hj : j ∈ representedCells h ρ hh hρ L s b) :
    dist (center h ρ hρ i) (center h ρ hρ j) ≤ 2 - a := by
  classical
  rcases Finset.mem_image.mp hi with ⟨u, huPart, hui⟩
  rcases Finset.mem_image.mp hj with ⟨v, hvPart, hvj⟩
  have huS : u ∈ s := (Finset.mem_filter.mp huPart).1
  have hvS : v ∈ s := (Finset.mem_filter.mp hvPart).1
  have hub : u.1 = b := (Finset.mem_filter.mp huPart).2
  have hvb : v.1 = b := (Finset.mem_filter.mp hvPart).2
  subst i
  subst j
  by_contra hdist
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hdist (by simp [sub_nonneg.mpr ha2])
  have hadj : (BEGraph h ρ hh hρ L a).Adj u v := by
    rw [BEGraph_adj_iff]
    refine ⟨huv, ?_⟩
    rw [edgeRel, if_pos (hub.trans hvb.symm)]
    simpa [position] using lt_of_not_ge hdist
  exact hs huS hvS huv hadj

lemma partSet_card_bound (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha2 : a ≤ 2) (hd1 : 1 ≤ 2 - a + 2 * ρ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L))
    (hs : (BEGraph h ρ hh hρ L a).IsIndepSet s) (b : Bool) :
    ((partSet h ρ hh hρ L s b).card : ℝ) ≤
      (L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ := by
  classical
  let J := representedCells h ρ hh hρ L s b
  have hcard := partSet_card_le_sum_multiplicity h ρ hh hρ L s b
  have hmult : (∑ i ∈ J, multiplicity h ρ hh hρ L i : ℝ) ≤
      (L : ℝ) * (∑ i ∈ J, weight h ρ hh hρ i) + J.card := by
    calc
      (∑ i ∈ J, multiplicity h ρ hh hρ L i : ℝ) ≤
          ∑ i ∈ J, ((L : ℝ) * weight h ρ hh hρ i + 1) := by
        exact Finset.sum_le_sum fun i _ ↦ multiplicity_upper h ρ hh hρ L i
      _ = (L : ℝ) * (∑ i ∈ J, weight h ρ hh hρ i) + J.card := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp
  have hweight : ∑ i ∈ J, weight h ρ hh hρ i ≤
      ((2 - a + 2 * ρ) / 2) ^ h :=
    cellUnion_weight_isodiametric h ρ hh hρ J a hd1
      (independent_represented_center_dist h ρ hh hρ L a ha2 s hs b)
  have hJcard : J.card ≤ netCard h ρ hρ := by
    simpa using Finset.card_le_univ J
  calc
    ((partSet h ρ hh hρ L s b).card : ℝ) ≤
        (∑ i ∈ J, multiplicity h ρ hh hρ L i : ℕ) := by exact_mod_cast hcard
    _ = ∑ i ∈ J, (multiplicity h ρ hh hρ L i : ℝ) := by norm_cast
    _ ≤ (L : ℝ) * (∑ i ∈ J, weight h ρ hh hρ i) + J.card := hmult
    _ ≤ (L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ := by
      gcongr

lemma independent_finset_card_bound (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha2 : a ≤ 2) (hd1 : 1 ≤ 2 - a + 2 * ρ)
    (s : Finset (Bool × CopyVertex h ρ hh hρ L))
    (hs : (BEGraph h ρ hh hρ L a).IsIndepSet s) :
    (s.card : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ) := by
  have hf := partSet_card_bound h ρ hh hρ L a ha2 hd1 s hs false
  have ht := partSet_card_bound h ρ hh hρ L a ha2 hd1 s hs true
  have hsplit : (partSet h ρ hh hρ L s false).card +
      (partSet h ρ hh hρ L s true).card = s.card := by
    simpa [partSet] using
      (Finset.card_filter_add_card_filter_not (s := s) (fun v ↦ v.1 = false))
  have hsplitR : ((partSet h ρ hh hρ L s false).card : ℝ) +
      (partSet h ρ hh hρ L s true).card = s.card := by exact_mod_cast hsplit
  nlinarith

lemma BEGraph_indepNum_bound (hh : 0 < h) (hρ : 0 < ρ) (L : ℕ) (a : ℝ)
    (ha2 : a ≤ 2) (hd1 : 1 ≤ 2 - a + 2 * ρ) :
    ((BEGraph h ρ hh hρ L a).indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + netCard h ρ hρ) := by
  rcases (BEGraph h ρ hh hρ L a).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rw [← hs.card_eq]
  exact independent_finset_card_bound h ρ hh hρ L a ha2 hd1 s hs.isIndepSet

end Graph

end Partition

end Erdos615.Construction
