import ErdosProblems.Erdos590

namespace Erdos118.Reused591

open Ordinal

namespace FixedReindex

variable {A : Type*} [LinearOrder A] [WellFoundedLT A]

noncomputable def cut (F : Finset A) (x : A) : Finset A :=
  F.filter (fun a => a < x)

abbrev Cell (F s : Finset A) : Type _ :=
  {x : A // x ∉ F ∧ cut F x = s}

abbrev MCell (F : Finset A) (M : Set A) (s : Finset A) : Type _ :=
  {x : Cell F s // x.1 ∈ M}

theorem cut_subset {F : Finset A} {x y : A} (hxy : x ≤ y) :
    cut F x ⊆ cut F y := by
  classical
  intro a ha
  simp only [cut, Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.trans_le hxy⟩

/-- If moving from `x` to `y` crosses a point of `F`, then any two
points in the corresponding open cells occur in the same order. -/
theorem lt_of_cut_ne {F : Finset A} {x y u v : A}
    (hxy : x < y) (hcut : cut F x ≠ cut F y)
    (hu : cut F u = cut F x) (hv : cut F v = cut F y) : u < v := by
  classical
  have hsub : cut F x ⊆ cut F y := cut_subset hxy.le
  have hssub : cut F x ⊂ cut F y :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hcut⟩
  obtain ⟨a, haY, haX⟩ := Finset.exists_of_ssubset hssub
  have haF : a ∈ F := by
    exact (Finset.mem_filter.mp haY).1
  have hav : a < v := by
    have : a ∈ cut F v := by simpa only [hv] using haY
    exact (Finset.mem_filter.mp this).2
  have hnotau : ¬ a < u := by
    intro hau
    apply haX
    have : a ∈ cut F u := Finset.mem_filter.mpr ⟨haF, hau⟩
    simpa only [hu] using this
  exact (le_of_not_gt hnotau).trans_lt hav

/-- An open-cell point whose `F`-cut is the cut at an endpoint `y ∈ F`
lies strictly below `y`. -/
theorem lt_endpoint_of_same_cut {F : Finset A} {u y : A}
    (hyF : y ∈ F) (huF : u ∉ F) (hcut : cut F u = cut F y) : u < y := by
  classical
  by_contra h
  have hyu : y ≤ u := le_of_not_gt h
  rcases hyu.eq_or_lt with rfl | hyu
  · exact huF hyF
  · have hymem : y ∈ cut F u := Finset.mem_filter.mpr ⟨hyF, hyu⟩
    have : y ∈ cut F y := by simpa only [hcut] using hymem
    exact (lt_irrefl y) (Finset.mem_filter.mp this).2

/-- Equality of the ordinal types of every open cell with its part in
`M` supplies an order isomorphism for that cell. -/
noncomputable def cellIso (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    (s : Finset A) : Cell F s ≃o MCell F M s :=
  OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp (hlarge s)))

theorem cellIso_val_lt_of_eq (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    {s t : Finset A} (hst : s = t) (x : Cell F s) (y : Cell F t)
    (hxy : x.1 < y.1) :
    (cellIso F M hlarge s x).1.1 < (cellIso F M hlarge t y).1.1 := by
  subst t
  exact (cellIso F M hlarge s).strictMono hxy

noncomputable def reindexFun (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    (x : A) : A := by
  classical
  exact if hx : x ∈ F then x
    else (cellIso F M hlarge (cut F x) ⟨x, hx, rfl⟩).1.1

theorem reindexFun_of_mem (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    {x : A} (hx : x ∈ F) : reindexFun F M hlarge x = x := by
  classical
  simp [reindexFun, hx]

theorem reindexFun_of_not_mem (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    {x : A} (hx : x ∉ F) :
    reindexFun F M hlarge x =
      (cellIso F M hlarge (cut F x) ⟨x, hx, rfl⟩).1.1 := by
  classical
  simp [reindexFun, hx]

theorem cut_reindexFun (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    (x : A) : cut F (reindexFun F M hlarge x) = cut F x := by
  classical
  by_cases hx : x ∈ F
  · rw [reindexFun_of_mem F M hlarge hx]
  · rw [reindexFun_of_not_mem F M hlarge hx]
    exact (cellIso F M hlarge (cut F x) ⟨x, hx, rfl⟩).1.2.2

theorem reindexFun_not_mem (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    {x : A} (hx : x ∉ F) : reindexFun F M hlarge x ∉ F := by
  classical
  rw [reindexFun_of_not_mem F M hlarge hx]
  exact (cellIso F M hlarge (cut F x) ⟨x, hx, rfl⟩).1.2.1

theorem reindexFun_mem (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    (hFM : ∀ x ∈ F, x ∈ M) (x : A) : reindexFun F M hlarge x ∈ M := by
  classical
  by_cases hx : x ∈ F
  · rw [reindexFun_of_mem F M hlarge hx]
    exact hFM x hx
  · rw [reindexFun_of_not_mem F M hlarge hx]
    exact (cellIso F M hlarge (cut F x) ⟨x, hx, rfl⟩).2

theorem reindexFun_strictMono (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s)) :
    StrictMono (reindexFun F M hlarge) := by
  classical
  intro x y hxy
  by_cases hcuts : cut F x = cut F y
  · by_cases hxF : x ∈ F
    · exfalso
      have hxmem : x ∈ cut F y := Finset.mem_filter.mpr ⟨hxF, hxy⟩
      have : x ∈ cut F x := by simpa only [hcuts] using hxmem
      exact (lt_irrefl x) (Finset.mem_filter.mp this).2
    · by_cases hyF : y ∈ F
      · rw [reindexFun_of_mem F M hlarge hyF]
        exact lt_endpoint_of_same_cut hyF
          (reindexFun_not_mem F M hlarge hxF)
          ((cut_reindexFun F M hlarge x).trans hcuts)
      · rw [reindexFun_of_not_mem F M hlarge hxF,
          reindexFun_of_not_mem F M hlarge hyF]
        exact cellIso_val_lt_of_eq F M hlarge hcuts
          ⟨x, hxF, rfl⟩ ⟨y, hyF, rfl⟩ hxy
  · exact lt_of_cut_ne hxy hcuts
      (cut_reindexFun F M hlarge x) (cut_reindexFun F M hlarge y)

/-- A self-embedding with range in `M` that fixes every member of `F`.
The hypothesis is exactly the segment-by-segment largeness needed for
such a fixed-point reindexing. -/
noncomputable def fixedReindex (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s)) :
    A ↪o A :=
  OrderEmbedding.ofStrictMono (reindexFun F M hlarge)
    (reindexFun_strictMono F M hlarge)

theorem fixedReindex_fixes (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    {x : A} (hx : x ∈ F) : fixedReindex F M hlarge x = x :=
  reindexFun_of_mem F M hlarge hx

theorem fixedReindex_range (F : Finset A) (M : Set A)
    (hlarge : ∀ s : Finset A, typeLT (Cell F s) = typeLT (MCell F M s))
    (hFM : ∀ x ∈ F, x ∈ M) (x : A) : fixedReindex F M hlarge x ∈ M :=
  reindexFun_mem F M hlarge hFM x

/-! The concrete finite-power block used by the local
Erdős--Milner iteration.  `/tmp/WeakPigeon.lean` proves finite
indivisibility for precisely this ordinal model. -/

noncomputable abbrev B (n : ℕ) : Type :=
  (ω ^ (ω * (n + 1 : ℕ)) : Ordinal).ToType

theorem B_exists_fixedReindex (n : ℕ) (F : Finset (B n))
    (M : Set (B n))
    (hlarge : ∀ s : Finset (B n),
      typeLT (Cell F s) = typeLT (MCell F M s))
    (hFM : ∀ x ∈ F, x ∈ M) :
    ∃ g : B n ↪o B n,
      (∀ x, g x ∈ M) ∧ ∀ x ∈ F, g x = x := by
  let g : B n ↪o B n := fixedReindex F M hlarge
  refine ⟨g, ?_, ?_⟩
  · exact fun x ↦ fixedReindex_range F M hlarge hFM x
  · exact fun _ hx ↦ fixedReindex_fixes F M hlarge hx

end FixedReindex



end Erdos118.Reused591
