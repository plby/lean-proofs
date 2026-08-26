import ErdosProblems.Erdos1038.PlatformReferencePartition

/-!
# Almost-everywhere open residual-block partition

The cumulative residual masses cover the unit interval.  After applying the
strictly monotone reference cut, the corresponding angular blocks cover the
half-circle; deleting their finitely many endpoints gives the open-block
statement needed for pointwise boundary identification.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

omit [Fintype iota] in
private theorem exists_mem_ordered_cumulative_interval
    (s : Finset iota) (w : iota → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ ∑ i ∈ s, w i) :
    ∃ i ∈ s,
      (∑ j ∈ s with j < i, w j) ≤ u ∧
        u ≤ (∑ j ∈ s with j < i, w j) + w i := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
      simp only [Finset.sum_empty] at hu
      linarith
  | insert a s ha ih =>
      have has : a ∉ s := by
        intro has
        exact (lt_irrefl a) (ha a has)
      have hinner (i : iota) (hi : i ∈ s) :
          (∑ j ∈ insert a s with j < i, w j) =
            ∑ j ∈ s with j < i, w j := by
        rw [Finset.filter_insert]
        simp only [not_lt_of_ge (ha i hi).le, ↓reduceIte]
      have htop :
          (∑ j ∈ insert a s with j < a, w j) = ∑ j ∈ s, w j := by
        have hfilter :
            Finset.filter (fun j : iota ↦ j < a) (insert a s) = s := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hjaEq | hjs, hja⟩
            · exact False.elim ((ne_of_lt hja) hjaEq)
            · exact hjs
          · intro hjs
            exact ⟨Or.inr hjs, ha j hjs⟩
        rw [hfilter]
      by_cases huOld : u ≤ ∑ i ∈ s, w i
      · have hwOld : ∀ i ∈ s, 0 < w i := by
          intro i hi
          exact hw i (Finset.mem_insert_of_mem hi)
        rcases ih hwOld huOld with ⟨i, hi, hleft, hright⟩
        refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
        rw [hinner i hi]
        exact ⟨hleft, hright⟩
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        rw [htop]
        constructor
        · exact (lt_of_not_ge huOld).le
        · rw [Finset.sum_insert has] at hu
          linarith

private theorem exists_mem_Icc_platformResidualBlock
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) {theta : ℝ}
    (htheta : theta ∈ Ioc (0 : ℝ) Real.pi) :
    ∃ i, theta ∈ Icc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i) := by
  classical
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2⟩
  let u : ℝ := platformReferenceCumulative k a theta
  have huMem := platformReferenceCumulative_mem_Icc
    hk ha ha2 hthreshold hthetaIcc
  have hu0 : 0 < u := by
    dsimp only [u]
    have hmono := platformReferenceCumulative_strictMonoOn
      hk ha ha2 hthreshold
    simpa only [platformReferenceCumulative_zero] using!
      hmono (left_mem_Icc.2 Real.pi_pos.le) hthetaIcc htheta.1
  have hcover := exists_mem_ordered_cumulative_interval
    (Finset.univ : Finset iota) C.weight
      (fun i _hi ↦ C.weight_pos i) hu0 (by
        dsimp only [u]
        rw [C.sum_weight]
        exact huMem.2)
  rcases hcover with ⟨i, _hi, hleft, hright⟩
  have hmass : orderedResidualLeftMass C i ≤ u ∧
      u ≤ orderedResidualRightMass C i := by
    unfold orderedResidualLeftMass
    rw [orderedResidualRightMass_eq_left_add_weight]
    simpa only [Finset.mem_univ, true_and] using! And.intro hleft hright
  let usub : Icc (0 : ℝ) 1 := ⟨u, huMem⟩
  let lsub : Icc (0 : ℝ) 1 :=
    ⟨orderedResidualLeftMass C i,
      orderedResidualLeftMass_mem_Icc C i⟩
  let rsub : Icc (0 : ℝ) 1 :=
    ⟨orderedResidualRightMass C i,
      orderedResidualRightMass_mem_Icc C i⟩
  have hcutTheta :
      platformReferenceCut k a hk ha ha2 hthreshold usub = theta := by
    apply (platformReferenceCumulative_strictMonoOn
      hk ha ha2 hthreshold).injOn
      (platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold usub)
      hthetaIcc
    simp only [platformReferenceCumulative_cut]
    rfl
  have hcutMono :=
    (platformReferenceCut_strictMono k a hk ha ha2 hthreshold).monotone
  refine ⟨i, ?_⟩
  constructor
  · unfold platformResidualBlockLeft
    change platformReferenceCut k a hk ha ha2 hthreshold lsub ≤ theta
    rw [← hcutTheta]
    exact hcutMono hmass.1
  · unfold platformResidualBlockRight
    change theta ≤ platformReferenceCut k a hk ha ha2 hthreshold rsub
    rw [← hcutTheta]
    exact hcutMono hmass.2

/-- Away from the finite set of residual-block endpoints, every point of
the half-circle belongs to the interior of one residual block. -/
theorem ae_exists_mem_Ioo_platformResidualBlock
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    ∀ᵐ theta ∂volume, theta ∈ uIoc (0 : ℝ) Real.pi →
      ∃ i, theta ∈ Ioo
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i) := by
  have hneLeft : ∀ᵐ theta ∂volume, ∀ i,
      theta ≠ platformResidualBlockLeft C k a hk ha ha2 hthreshold i :=
    ae_all_iff.2 (fun i ↦ Measure.ae_ne (volume : Measure ℝ)
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i))
  have hneRight : ∀ᵐ theta ∂volume, ∀ i,
      theta ≠ platformResidualBlockRight C k a hk ha ha2 hthreshold i :=
    ae_all_iff.2 (fun i ↦ Measure.ae_ne (volume : Measure ℝ)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
  filter_upwards [hneLeft, hneRight] with theta hleftNe hrightNe
  intro htheta
  rw [uIoc_of_le Real.pi_pos.le] at htheta
  rcases exists_mem_Icc_platformResidualBlock
    C k a hk ha ha2 hthreshold htheta with ⟨i, hi⟩
  exact ⟨i,
    lt_of_le_of_ne hi.1 (hleftNe i).symm,
    lt_of_le_of_ne hi.2 (hrightNe i)⟩

end

end Erdos1038
