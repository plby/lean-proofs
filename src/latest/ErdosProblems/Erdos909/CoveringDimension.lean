/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Topology.SmallInductiveDimension
import Mathlib.Topology.Separation.DisjointCover

open Set Topology TopologicalSpace

namespace Erdos909.CoveringDimension

def IsOpenCoverFin {X : Type*} [TopologicalSpace X] {k : ℕ} (U : Fin k → Set X) : Prop :=
  (∀ i, IsOpen (U i)) ∧ ⋃ i, U i = univ

def RefinesFin {X : Type*} {k l : ℕ} (V : Fin l → Set X) (U : Fin k → Set X) : Prop :=
  ∀ j, ∃ i, V j ⊆ U i

def MultiplicityLE {X : Type*} {l : ℕ} (V : Fin l → Set X) (q : ℕ) : Prop :=
  ∀ x (J : Finset (Fin l)), (∀ j ∈ J, x ∈ V j) → J.card ≤ q

def IsOpenCoverOnFin {X : Type*} [TopologicalSpace X] (A : Set X) {k : ℕ}
    (U : Fin k → Set X) : Prop :=
  (∀ i, IsOpen (U i)) ∧ A ⊆ ⋃ i, U i

def HasDisjointOpenRefinements {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ {k : ℕ} (U : Fin k → Set X), IsOpenCoverOnFin A U →
    ∃ V : Fin k → Set X, (∀ i, IsOpen (V i)) ∧ A ⊆ ⋃ i, V i ∧
      (∀ i, V i ⊆ U i) ∧ (_root_.Pairwise fun i j ↦ Disjoint (V i) (V j))

def MultiplicityLEProd {X : Type*} {q k : ℕ} (V : Fin q × Fin k → Set X) (r : ℕ) : Prop :=
  ∀ x (J : Finset (Fin q × Fin k)), (∀ j ∈ J, x ∈ V j) → J.card ≤ r

theorem refinement_of_disjoint_layers
    {X : Type*} [TopologicalSpace X] {q k : ℕ} (A : Fin q → Set X)
    (hAcov : univ ⊆ ⋃ a, A a) (hA : ∀ a, HasDisjointOpenRefinements (A a))
    (U : Fin k → Set X) (hU : IsOpenCoverFin U) :
    ∃ V : Fin q × Fin k → Set X,
      (∀ j, IsOpen (V j)) ∧ (⋃ j, V j = univ) ∧
      (∀ j, V j ⊆ U j.2) ∧ MultiplicityLEProd V q := by
  classical
  have hAU (a : Fin q) : IsOpenCoverOnFin (A a) U :=
    ⟨hU.1, fun x hx ↦ by rw [hU.2]; exact mem_univ x⟩
  choose V hVo hVcov hVsub hVdisj using fun a ↦ hA a U (hAU a)
  refine ⟨fun j ↦ V j.1 j.2, fun j ↦ hVo j.1 j.2, ?_, fun j ↦ hVsub j.1 j.2, ?_⟩
  · apply subset_antisymm (subset_univ _)
    intro x hx
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (hAcov hx)
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hVcov a hxa)
    exact mem_iUnion.mpr ⟨(a, i), hxi⟩
  · intro x J hJ
    have hinj : Set.InjOn Prod.fst (J : Set (Fin q × Fin k)) := by
      intro p hp r hr heq
      apply Prod.ext heq
      by_contra hne
      have hd := hVdisj p.1 hne
      exact (Set.not_disjoint_iff_nonempty_inter.mpr
        ⟨x, hJ p hp, heq ▸ hJ r hr⟩) hd
    calc
      J.card = (J.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = q := Fintype.card_fin q

theorem exists_clopen_partition_subordinate
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    (hY : HasSmallInductiveDimensionLT Y 1) {k : ℕ} [Nonempty (Fin k)]
    (U : Fin k → Set Y) (hU : IsOpenCoverFin U) :
    ∃ C : Fin k → Set Y, (∀ i, IsClopen (C i)) ∧
      (⋃ i, C i = univ) ∧ (∀ i, C i ⊆ U i) ∧
      (_root_.Pairwise fun i j ↦ Disjoint (C i) (C j)) := by
  classical
  have hb : IsTopologicalBasis {s : Set Y | IsClopen s} :=
    hasSmallInductiveDimensionLT_one_iff.mp hY
  let T : Set (Set Y) := {s | IsClopen s ∧ ∃ i, s ⊆ U i}
  have hT : IsTopologicalBasis T := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨hs, -⟩
      exact hs.isOpen
    · intro y V hy hVo
      have hyU : y ∈ ⋃ i, U i := by rw [hU.2]; exact mem_univ y
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hyU
      have hyinter : y ∈ V ∩ U i := ⟨hy, hyi⟩
      obtain ⟨s, hs, hys, hsV⟩ :=
        hb.exists_subset_of_mem_open hyinter (hVo.inter (hU.1 i))
      exact ⟨s, ⟨hs, i, hsV.trans inter_subset_right⟩, hys,
        hsV.trans inter_subset_left⟩
  obtain ⟨B, hBT, hBc, hBbasis⟩ := hT.exists_countable
  let B' : Set (Set Y) := insert ∅ B
  have hB'c : B'.Countable := hBc.insert ∅
  have hB'T : B' ⊆ T := by
    intro s hs
    rcases hs with rfl | hs
    · exact ⟨isClopen_empty, Classical.arbitrary (Fin k), empty_subset _⟩
    · exact hBT hs
  let b : ℕ → Set Y := Set.enumerateCountable hB'c ∅
  have hbmem (n : ℕ) : b n ∈ B' := by
    have hrange : range b = B' := by
      exact Set.range_enumerateCountable_of_mem hB'c (mem_insert ∅ B)
    rw [← hrange]
    exact mem_range_self n
  have hbclopen (n : ℕ) : IsClopen (b n) := (hB'T (hbmem n)).1
  choose owner howner using fun n ↦ (hB'T (hbmem n)).2
  let d : ℕ → Set Y := disjointed b
  have hdclopen (n : ℕ) : IsClopen (d n) := by
    change IsClopen (disjointed b n)
    rw [disjointed_apply]
    apply (hbclopen n).diff
    rw [Finset.sup_eq_iSup]
    exact isClopen_biUnion_finset (s := Finset.Iio n)
      fun m _ ↦ hbclopen m
  have hdsub (n : ℕ) : d n ⊆ U (owner n) :=
    (disjointed_subset b n).trans (howner n)
  have hdpair : _root_.Pairwise fun n m ↦ Disjoint (d n) (d m) := by
    simpa [d] using disjoint_disjointed b
  have hbcover : ⋃ n, b n = univ := by
    apply subset_antisymm (subset_univ _)
    intro y hy
    obtain ⟨s, hsB, hys⟩ : ∃ s ∈ B, y ∈ s := by
      have hysU : y ∈ ⋃₀ B := by
        rw [hBbasis.sUnion_eq]
        exact mem_univ y
      exact mem_sUnion.mp hysU
    have hsB' : s ∈ B' := mem_insert_of_mem ∅ hsB
    have hsrange : s ∈ range b := by
      rw [Set.range_enumerateCountable_of_mem hB'c (mem_insert ∅ B)]
      exact hsB'
    obtain ⟨n, rfl⟩ := hsrange
    exact mem_iUnion.mpr ⟨n, hys⟩
  have hdcover : ⋃ n, d n = univ := by
    rw [show (⋃ n, d n) = ⋃ n, b n by simpa [d] using (iUnion_disjointed (f := b))]
    exact hbcover
  let C : Fin k → Set Y := fun i ↦ ⋃ n : {n : ℕ // owner n = i}, d n
  have hCopen (i : Fin k) : IsOpen (C i) :=
    isOpen_iUnion fun n ↦ (hdclopen n).isOpen
  have hCsub (i : Fin k) : C i ⊆ U i := by
    intro y hy
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hy
    rw [← n.property]
    exact hdsub n hyn
  have hCcover : ⋃ i, C i = univ := by
    apply subset_antisymm (subset_univ _)
    intro y hy
    have hyd : y ∈ ⋃ n, d n := by rw [hdcover]; exact mem_univ y
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hyd
    exact mem_iUnion.mpr ⟨owner n, mem_iUnion.mpr ⟨⟨n, rfl⟩, hyn⟩⟩
  have hCpair : _root_.Pairwise fun i j ↦ Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hyi
    obtain ⟨m, hym⟩ := mem_iUnion.mp hyj
    have hnm : (n : ℕ) ≠ m := by
      intro h
      apply hij
      rw [← n.property, ← m.property, h]
    exact Set.disjoint_left.mp (hdpair hnm) hyn hym
  have hCclopen (i : Fin k) : IsClopen (C i) := by
    let R : Set Y := ⋃ j : {j : Fin k // j ≠ i}, C j
    have hRopen : IsOpen R := isOpen_iUnion fun j ↦ hCopen j
    have hCR : Disjoint (C i) R := by
      rw [Set.disjoint_left]
      intro y hyi hyr
      obtain ⟨j, hyj⟩ := mem_iUnion.mp hyr
      exact Set.disjoint_left.mp (hCpair (Ne.symm j.property)) hyi hyj
    apply isClopen_of_disjoint_cover_open _ (hCopen i) hRopen hCR
    intro y hy
    have hyC : y ∈ ⋃ j, C j := by rw [hCcover]; exact mem_univ y
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyC
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  exact ⟨C, hCclopen, hCcover, hCsub, hCpair⟩

lemma multiplicityLE_one_of_pairwise_disjoint {X : Type*} {l : ℕ} {V : Fin l → Set X}
    (hV : _root_.Pairwise fun i j ↦ Disjoint (V i) (V j)) : MultiplicityLE V 1 := by
  intro x
  intro J hJ
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hij
  exact (Set.not_disjoint_iff_nonempty_inter.mpr ⟨x, hJ i hi, hJ j hj⟩) (hV hij)

theorem compact_zero_dimensional_refinement
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (hX : HasSmallInductiveDimensionLT X 1) {k : ℕ} (U : Fin k → Set X)
    (hU : IsOpenCoverFin U) :
    ∃ (l : ℕ) (V : Fin l → Set X), IsOpenCoverFin V ∧ RefinesFin V U ∧ MultiplicityLE V 1 := by
  have hb : IsTopologicalBasis {s : Set X | IsClopen s} :=
    hasSmallInductiveDimensionLT_one_iff.mp hX
  letI : TotallySeparatedSpace X := totallySeparatedSpace_of_t0_of_basis_clopen hb
  let U' : Fin k → Opens X := fun i ↦ ⟨U i, hU.1 i⟩
  have hU' : IsOpenCover U' := by
    apply IsOpenCover.of_sets
    simpa [U'] using hU.2
  obtain ⟨l, W, hWsub, hWcover, hWdisj⟩ := hU'.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨l, fun j ↦ (W j : Set X), ⟨fun j ↦ (W j).isOpen, ?_⟩, ?_, ?_⟩
  · exact subset_antisymm (subset_univ _) hWcover
  · intro j
    exact (hWsub j).2
  · apply multiplicityLE_one_of_pairwise_disjoint
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hx : x ∈ ((W i ⊓ W j : Clopens X) : Set X) := ⟨hxi, hxj⟩
    rw [(hWdisj hij).eq_bot] at hx
    exact hx

end Erdos909.CoveringDimension
