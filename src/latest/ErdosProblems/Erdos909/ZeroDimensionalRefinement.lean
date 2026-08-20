/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Topology.SmallInductiveDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Order.Disjointed

open Set Topology TopologicalSpace
open scoped Function

namespace Erdos909.ZeroDimensionalRefinement

variable {X : Type*} [TopologicalSpace X]

/-- A finite open cover of a second-countable zero-dimensional space has a
same-index disjoint clopen refinement. -/
theorem exists_disjoint_clopen_refinement
    [SecondCountableTopology X]
    (hzero : HasSmallInductiveDimensionLT X 1)
    {ι : Type*} [Finite ι] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ) :
    ∃ C : ι → Set X,
      (∀ i, IsClopen (C i)) ∧ Pairwise (Disjoint on C) ∧
        ⋃ i, C i = univ ∧ ∀ i, C i ⊆ U i := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      refine ⟨fun _ ↦ ∅, fun _ ↦ isClopen_empty, ?_,
        ?_, fun _ ↦ empty_subset _⟩
      · intro i j hij
        change Disjoint (∅ : Set X) ∅
        exact disjoint_empty ∅
      exact Subsingleton.elim _ _
  | inr hX =>
      letI : Nonempty X := hX
      have hclopenBasis : IsTopologicalBasis {V : Set X | IsClopen V} :=
        hasSmallInductiveDimensionLT_one_iff.mp hzero
      obtain ⟨b, hbsub, hbcount, hb⟩ := hclopenBasis.exists_countable
      let p : Set (Set X × ι) :=
        {q | q.1 ∈ b ∧ q.1 ⊆ U q.2}
      have hpcount : p.Countable := by
        apply (hbcount.prod (Set.to_countable (Set.univ : Set ι))).mono
        rintro ⟨V, i⟩ ⟨hV, -⟩
        exact ⟨hV, mem_univ i⟩
      have hpnonempty : p.Nonempty := by
        let x : X := Classical.choice hX
        obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by
          apply mem_iUnion.mp
          rw [hcover]
          exact mem_univ x
        obtain ⟨V, hVb, hxV, hVU⟩ := hb.exists_subset_of_mem_open hxi (hU i)
        exact ⟨(V, i), hVb, hVU⟩
      letI : Countable p := hpcount.to_subtype
      letI : Nonempty p := hpnonempty.to_subtype
      obtain ⟨e, he⟩ : ∃ e : ℕ → p, Function.Surjective e := exists_surjective_nat p
      let F : ℕ → Set X := fun k ↦ (e k : Set X × ι).1
      let a : ℕ → ι := fun k ↦ (e k : Set X × ι).2
      have hFclopen (k : ℕ) : IsClopen (F k) :=
        hbsub (e k).property.1
      have hFsub (k : ℕ) : F k ⊆ U (a k) :=
        (e k).property.2
      have hFcover : ⋃ k, F k = univ := by
        apply eq_univ_of_forall
        intro x
        obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by
          apply mem_iUnion.mp
          rw [hcover]
          exact mem_univ x
        obtain ⟨V, hVb, hxV, hVU⟩ := hb.exists_subset_of_mem_open hxi (hU i)
        obtain ⟨k, hk⟩ := he ⟨(V, i), hVb, hVU⟩
        exact mem_iUnion.mpr ⟨k, by simpa [F, hk] using hxV⟩
      let D : ℕ → Set X := disjointed F
      have hDclopen (k : ℕ) : IsClopen (D k) := by
        rw [show D k = F k \ ⋃ j ∈ Finset.Iio k, F j by
          simp [D, disjointed_apply, Finset.sup_eq_biUnion]]
        exact (hFclopen k).diff
          (isClopen_biUnion_finset fun j _ ↦ hFclopen j)
      have hDdisj : Pairwise (Disjoint on D) := by
        simpa [D] using disjoint_disjointed F
      have hDcover : ⋃ k, D k = univ := by
        rw [show (⋃ k, D k) = ⋃ k, F k by simpa [D] using iUnion_disjointed (f := F)]
        exact hFcover
      let C : ι → Set X := fun i ↦ ⋃ k, if a k = i then D k else ∅
      have hCopen (i : ι) : IsOpen (C i) := by
        apply isOpen_iUnion
        intro k
        split_ifs
        · exact (hDclopen k).isOpen
        · exact isOpen_empty
      have hCcover : ⋃ i, C i = univ := by
        rw [← hDcover]
        apply Subset.antisymm
        · intro x hx
          obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
          obtain ⟨k, hxk⟩ := mem_iUnion.mp hxi
          split_ifs at hxk with hki
          · exact mem_iUnion.mpr ⟨k, hxk⟩
          · exact hxk.elim
        · intro x hx
          obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨a k, mem_iUnion.mpr ⟨k, by simp [C, hxk]⟩⟩
      have hCdisj : Pairwise (Disjoint on C) := by
        intro i j hij
        change Disjoint (C i) (C j)
        rw [Set.disjoint_left]
        intro x hxi hxj
        obtain ⟨k, hxk⟩ := mem_iUnion.mp hxi
        obtain ⟨l, hxl⟩ := mem_iUnion.mp hxj
        split_ifs at hxk with hki
        · split_ifs at hxl with hlj
          · have hkl : k = l := by
              by_contra hne
              exact (Set.disjoint_left.mp (hDdisj hne) hxk hxl)
            exact hij (hki ▸ hkl ▸ hlj)
          · exact hxl.elim
        · exact hxk.elim
      have hCclosed (i : ι) : IsClosed (C i) := by
        rw [← isOpen_compl_iff]
        have heq : (C i)ᶜ = ⋃ j : {j : ι // j ≠ i}, C j := by
          ext x
          constructor
          · intro hxi
            have hxuniv : x ∈ ⋃ j, C j := by rw [hCcover]; exact mem_univ x
            obtain ⟨j, hxj⟩ := mem_iUnion.mp hxuniv
            have hji : j ≠ i := by
              intro h
              exact hxi (h ▸ hxj)
            exact mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩
          · rintro hx
            obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
            exact (show x ∉ C i from fun hxi ↦
              Set.disjoint_left.mp (hCdisj j.property) hxj hxi
            )
        rw [heq]
        exact isOpen_iUnion fun j ↦ hCopen j
      refine ⟨C, fun i ↦ ⟨hCclosed i, hCopen i⟩, hCdisj, hCcover, ?_⟩
      intro i x hxi
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hxi
      split_ifs at hxk with hki
      · exact hki ▸ hFsub k (disjointed_subset F k hxk)
      · exact hxk.elim

variable {Z : Type*} [PseudoMetricSpace Z]

/-- A finite ambient-open cover of a second-countable zero-dimensional
subspace of a pseudometric space has a same-index pairwise-disjoint
ambient-open refinement covering the subspace. -/
theorem exists_ambient_disjoint_open_refinement
    (s : Set Z) [SecondCountableTopology s]
    (hzero : HasSmallInductiveDimensionLT s 1)
    {ι : Type*} [Finite ι] (U : ι → Set Z)
    (hU : ∀ i, IsOpen (U i)) (hcover : s ⊆ ⋃ i, U i) :
    ∃ V : ι → Set Z,
      (∀ i, IsOpen (V i)) ∧ Pairwise (Disjoint on V) ∧
        s ⊆ ⋃ i, V i ∧ ∀ i, V i ⊆ U i := by
  classical
  let RU : ι → Set s := fun i ↦ Subtype.val ⁻¹' U i
  have hRUopen (i : ι) : IsOpen (RU i) := (hU i).preimage continuous_subtype_val
  have hRUcover : ⋃ i, RU i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ : ∃ i, (x : Z) ∈ U i := by
      apply mem_iUnion.mp
      exact hcover x.property
    exact mem_iUnion.mpr ⟨i, hxi⟩
  obtain ⟨C, hCclopen, hCdisj, hCcover, hCsub⟩ :=
    exists_disjoint_clopen_refinement hzero RU hRUopen hRUcover
  let A : ι → Set Z := fun i ↦ Subtype.val '' C i
  let W : ι → Set Z := fun i ↦
    if (C i).Nonempty then
      ⋂ j : {j : ι // j ≠ i ∧ (C j).Nonempty},
        {x | Metric.infDist x (A i) < Metric.infDist x (A j)}
    else ∅
  have hWopen (i : ι) : IsOpen (W i) := by
    by_cases hi : (C i).Nonempty
    · rw [show W i =
          ⋂ j : {j : ι // j ≠ i ∧ (C j).Nonempty},
            {x | Metric.infDist x (A i) < Metric.infDist x (A j)} by simp [W, hi]]
      apply isOpen_iInter_of_finite
      intro j
      exact isOpen_lt (Metric.continuous_infDist_pt (A i))
        (Metric.continuous_infDist_pt (A j))
    · simp [W, hi]
  have hWtrace (i : ι) : Subtype.val ⁻¹' W i = C i := by
    ext y
    constructor
    · intro hyW
      by_cases hi : (C i).Nonempty
      · have hyWi : (y : Z) ∈
            ⋂ j : {j : ι // j ≠ i ∧ (C j).Nonempty},
              {x | Metric.infDist x (A i) < Metric.infDist x (A j)} := by
          simpa [W, hi] using hyW
        have hycover : y ∈ ⋃ k, C k := by rw [hCcover]; exact mem_univ y
        obtain ⟨k, hyk⟩ := mem_iUnion.mp hycover
        by_contra hyi
        have hki : k ≠ i := fun h ↦ hyi (h ▸ hyk)
        have hkn : (C k).Nonempty := ⟨y, hyk⟩
        have hineq := mem_iInter.mp hyWi ⟨k, hki, hkn⟩
        have hyAk : (y : Z) ∈ A k := ⟨y, hyk, rfl⟩
        have hzeroAk : Metric.infDist (y : Z) (A k) = 0 :=
          Metric.infDist_zero_of_mem hyAk
        exact (not_lt_of_ge Metric.infDist_nonneg) (by simpa [hzeroAk] using hineq)
      · simpa [W, hi] using hyW
    · intro hyi
      have hi : (C i).Nonempty := ⟨y, hyi⟩
      have hyAi : (y : Z) ∈ A i := ⟨y, hyi, rfl⟩
      have hzeroAi : Metric.infDist (y : Z) (A i) = 0 :=
        Metric.infDist_zero_of_mem hyAi
      have hyall : (y : Z) ∈
          ⋂ j : {j : ι // j ≠ i ∧ (C j).Nonempty},
            {x | Metric.infDist x (A i) < Metric.infDist x (A j)} := by
        apply mem_iInter.mpr
        intro j
        have hydisj : y ∉ C j := fun hyj ↦
          Set.disjoint_left.mp (hCdisj j.property.1) hyj hyi
        have hynot' : y ∉ closure (C j) := by
          rw [(hCclopen j).isClosed.closure_eq]
          exact hydisj
        have hynot : (y : Z) ∉ closure (A j) := by
          simpa [A, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hynot'
        have hpos : 0 < Metric.infDist (y : Z) (A j) :=
          (Metric.infDist_pos_iff_notMem_closure
            (j.property.2.image Subtype.val)).1 hynot
        simpa [hzeroAi] using hpos
      simpa [W, hi] using hyall
  have hWdisj : Pairwise (Disjoint on W) := by
    intro i j hij
    change Disjoint (W i) (W j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hi : (C i).Nonempty := by
      by_contra hi
      simpa [W, hi] using hxi
    have hj : (C j).Nonempty := by
      by_contra hj
      simpa [W, hj] using hxj
    have hxi' : x ∈
        ⋂ k : {k : ι // k ≠ i ∧ (C k).Nonempty},
          {x | Metric.infDist x (A i) < Metric.infDist x (A k)} := by
      simpa [W, hi] using hxi
    have hxj' : x ∈
        ⋂ k : {k : ι // k ≠ j ∧ (C k).Nonempty},
          {x | Metric.infDist x (A j) < Metric.infDist x (A k)} := by
      simpa [W, hj] using hxj
    have hij' := mem_iInter.mp hxi' ⟨j, hij.symm, hj⟩
    have hji' := mem_iInter.mp hxj' ⟨i, hij, hi⟩
    have hij'' : Metric.infDist x (A i) < Metric.infDist x (A j) := by
      simpa using hij'
    have hji'' : Metric.infDist x (A j) < Metric.infDist x (A i) := by
      simpa using hji'
    exact lt_asymm hij'' hji''
  let V : ι → Set Z := fun i ↦ W i ∩ U i
  refine ⟨V, fun i ↦ (hWopen i).inter (hU i), ?_, ?_, fun i ↦ inter_subset_right⟩
  · intro i j hij
    change Disjoint (V i) (V j)
    exact (hWdisj hij).mono inter_subset_left inter_subset_left
  · intro x hxs
    let y : s := ⟨x, hxs⟩
    have hycover : y ∈ ⋃ i, C i := by rw [hCcover]; exact mem_univ y
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hycover
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hyW : y ∈ Subtype.val ⁻¹' W i := by
      rw [hWtrace i]
      exact hyi
    exact ⟨hyW, hCsub i hyi⟩

end Erdos909.ZeroDimensionalRefinement
