import ErdosProblems.Erdos1038.PlatformReferenceCDF
import ErdosProblems.Erdos1038.ResidualConfiguration

/-!
# Consecutive platform blocks for an ordered residual configuration

For a finite residual probability whose index order agrees with its spatial
order, the sums of all preceding weights and of all weights through the
current index are consecutive cumulative probabilities.  Applying the
inverse platform CDF gives the exact angular block assigned to that atom.
-/

set_option warningAsError false

open Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
/-- A finite telescoping identity in cumulative-mass coordinates.  This is
stated independently of probability weights and is later applied both to
the reference and adjoint cumulative functions. -/
theorem sum_cumulativeIncrement
    (s : Finset ι) (w : ι → ℝ) (F : ℝ → ℝ) :
    (∑ i ∈ s,
        (F ((∑ j ∈ s with j < i, w j) + w i) -
          F (∑ j ∈ s with j < i, w j))) =
      F (∑ i ∈ s, w i) - F 0 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
      have has : a ∉ s := by
        intro has
        exact (lt_irrefl a) (ha a has)
      have hinner (i : ι) (hi : i ∈ s) :
          (∑ j ∈ insert a s with j < i, w j) =
            ∑ j ∈ s with j < i, w j := by
        rw [Finset.filter_insert]
        simp only [not_lt_of_ge (ha i hi).le, ↓reduceIte]
      have htop :
          (∑ j ∈ insert a s with j < a, w j) = ∑ j ∈ s, w j := by
        have hfilter :
            Finset.filter (fun j : ι ↦ j < a) (insert a s) = s := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hjaEq | hjs, hja⟩
            · exact False.elim ((ne_of_lt hja) hjaEq)
            · exact hjs
          · intro hjs
            exact ⟨Or.inr hjs, ha j hjs⟩
        rw [hfilter]
      rw [Finset.sum_insert has, Finset.sum_insert has]
      have hold :
          (∑ i ∈ s,
              (F ((∑ j ∈ insert a s with j < i, w j) + w i) -
                F (∑ j ∈ insert a s with j < i, w j))) =
            ∑ i ∈ s,
              (F ((∑ j ∈ s with j < i, w j) + w i) -
                F (∑ j ∈ s with j < i, w j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hinner i hi]
      rw [hold, ih, htop]
      rw [add_comm (w a) (∑ i ∈ s, w i)]
      ring

/-- Target mass strictly before `i` in the spatial order. -/
def orderedResidualLeftMass (C : ResidualConfiguration ι) (i : ι) : ℝ :=
  ∑ j : ι with j < i, C.weight j

/-- Target mass through `i` in the spatial order. -/
def orderedResidualRightMass (C : ResidualConfiguration ι) (i : ι) : ℝ :=
  ∑ j : ι with j ≤ i, C.weight j

lemma orderedResidualLeftMass_mem_Icc
    (C : ResidualConfiguration ι) (i : ι) :
    orderedResidualLeftMass C i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ ↦ (C.weight_pos j).le
  · rw [← C.sum_weight]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      (fun j _ _ ↦ (C.weight_pos j).le)

lemma orderedResidualRightMass_mem_Icc
    (C : ResidualConfiguration ι) (i : ι) :
    orderedResidualRightMass C i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ ↦ (C.weight_pos j).le
  · rw [← C.sum_weight]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      (fun j _ _ ↦ (C.weight_pos j).le)

lemma orderedResidualRightMass_eq_left_add_weight
    (C : ResidualConfiguration ι) (i : ι) :
    orderedResidualRightMass C i =
      orderedResidualLeftMass C i + C.weight i := by
  have hfilter :
      Finset.filter (fun j : ι ↦ j ≤ i) Finset.univ =
        insert i (Finset.filter (fun j : ι ↦ j < i) Finset.univ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hji
      exact hji.eq_or_lt.elim Or.inl Or.inr
    · rintro (rfl | hji)
      · exact le_rfl
      · exact hji.le
  unfold orderedResidualRightMass orderedResidualLeftMass
  rw [hfilter, Finset.sum_insert (by simp)]
  ring

lemma orderedResidualLeftMass_lt_rightMass
    (C : ResidualConfiguration ι) (i : ι) :
    orderedResidualLeftMass C i < orderedResidualRightMass C i := by
  rw [orderedResidualRightMass_eq_left_add_weight]
  linarith [C.weight_pos i]

theorem sum_apply_orderedResidualRight_sub_left
    (C : ResidualConfiguration ι) (F : ℝ → ℝ) :
    (∑ i, (F (orderedResidualRightMass C i) -
      F (orderedResidualLeftMass C i))) = F 1 - F 0 := by
  have htel := sum_cumulativeIncrement (Finset.univ : Finset ι) C.weight F
  rw [C.sum_weight] at htel
  calc
    (∑ i, (F (orderedResidualRightMass C i) -
        F (orderedResidualLeftMass C i))) =
        ∑ i,
          (F (orderedResidualLeftMass C i + C.weight i) -
            F (orderedResidualLeftMass C i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [orderedResidualRightMass_eq_left_add_weight]
    _ = F 1 - F 0 := by
      simpa only [orderedResidualLeftMass] using! htel

theorem sum_apply_orderedResidualRight_sub_left_Icc
    (C : ResidualConfiguration ι) (F : Icc (0 : ℝ) 1 → ℝ) :
    (∑ i,
        (F ⟨orderedResidualRightMass C i,
            orderedResidualRightMass_mem_Icc C i⟩ -
          F ⟨orderedResidualLeftMass C i,
            orderedResidualLeftMass_mem_Icc C i⟩)) =
      F ⟨1, by constructor <;> norm_num⟩ -
        F ⟨0, by constructor <;> norm_num⟩ := by
  let F' : ℝ → ℝ := fun x ↦
    if hx : x ∈ Icc (0 : ℝ) 1 then F ⟨x, hx⟩ else 0
  have htel := sum_apply_orderedResidualRight_sub_left C F'
  simpa only [F', dif_pos (orderedResidualRightMass_mem_Icc C _),
    dif_pos (orderedResidualLeftMass_mem_Icc C _),
    show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num,
    show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num] using! htel

lemma orderedResidualRightMass_le_leftMass_of_lt
    (C : ResidualConfiguration ι) {i j : ι} (hij : i < j) :
    orderedResidualRightMass C i ≤ orderedResidualLeftMass C j := by
  unfold orderedResidualRightMass orderedResidualLeftMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.trans_lt hij)
    (fun x _ _ ↦ (C.weight_pos x).le)

/-- The left angular endpoint of the reference block assigned to `i`. -/
def platformResidualBlockLeft
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) : ℝ :=
  platformReferenceCut k a hk ha ha2 hthreshold
    ⟨orderedResidualLeftMass C i,
      orderedResidualLeftMass_mem_Icc C i⟩

/-- The right angular endpoint of the reference block assigned to `i`. -/
def platformResidualBlockRight
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) : ℝ :=
  platformReferenceCut k a hk ha ha2 hthreshold
    ⟨orderedResidualRightMass C i,
      orderedResidualRightMass_mem_Icc C i⟩

lemma platformResidualBlockLeft_mem_Icc
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    platformResidualBlockLeft C k a hk ha ha2 hthreshold i ∈
      Icc (0 : ℝ) Real.pi := by
  exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _

lemma platformResidualBlockRight_mem_Icc
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    platformResidualBlockRight C k a hk ha ha2 hthreshold i ∈
      Icc (0 : ℝ) Real.pi := by
  exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _

theorem platformResidualBlockLeft_lt_right
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    platformResidualBlockLeft C k a hk ha ha2 hthreshold i <
      platformResidualBlockRight C k a hk ha ha2 hthreshold i := by
  exact platformReferenceCut_strictMono k a hk ha ha2 hthreshold
    (orderedResidualLeftMass_lt_rightMass C i)

theorem platformResidualBlocks_ordered
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) {i j : ι} (hij : i < j) :
    platformResidualBlockRight C k a hk ha ha2 hthreshold i ≤
      platformResidualBlockLeft C k a hk ha ha2 hthreshold j := by
  exact (platformReferenceCut_strictMono k a hk ha ha2 hthreshold).monotone
    (orderedResidualRightMass_le_leftMass_of_lt C hij)

/-- Each angular block has exactly the target atom's physical reference
mass. -/
theorem platformReferenceIntervalMass_residualBlock
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    platformReferenceIntervalMass k a
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i) =
      C.weight i := by
  rw [platformResidualBlockLeft, platformResidualBlockRight,
    platformReferenceIntervalMass_cut k a hk ha ha2 hthreshold
      (orderedResidualLeftMass_lt_rightMass C i).le]
  change orderedResidualRightMass C i - orderedResidualLeftMass C i =
    C.weight i
  rw [orderedResidualRightMass_eq_left_add_weight]
  ring

end

end Erdos1038
