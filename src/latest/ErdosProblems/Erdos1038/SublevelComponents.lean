import ErdosProblems.Erdos1038.ComponentRoot

/-!
# Interval structure of sublevel components

Every connected component of an admissible polynomial's strict unit
sublevel set is a bounded open interval.  Its two endpoints lie on the
polynomial level set `|f| = 1`, and the component contains a root of `f`.
The last assertion uses the elementary midpoint-product argument from
`ComponentRoot.lean`.
-/

open Set Polynomial

namespace Erdos1038

noncomputable section

theorem eq_Ioo_sInf_sSup_of_isOpen_isConnected {s : Set ℝ}
    (ho : IsOpen s) (hc : IsConnected s) (hbelow : BddBelow s)
    (habove : BddAbove s) :
    s = Ioo (sInf s) (sSup s) := by
  apply Subset.antisymm
  · intro x hx
    have hlow : sInf s < x := by
      have hle : sInf s ≤ x := csInf_le hbelow hx
      apply lt_of_le_of_ne hle
      intro heq
      obtain ⟨l, u, hxl, hlu⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hx)
      let y : ℝ := (l + x) / 2
      have hyI : y ∈ Ioo l u := by
        constructor
        · dsimp [y]
          linarith [hxl.1]
        · dsimp [y]
          linarith [hxl.1, hxl.2]
      have hy := hlu hyI
      have hinf : sInf s ≤ y := csInf_le hbelow hy
      rw [heq] at hinf
      dsimp [y] at hinf
      linarith [hxl.1]
    have hupp : x < sSup s := by
      have hle : x ≤ sSup s := le_csSup habove hx
      apply lt_of_le_of_ne hle
      intro heq
      obtain ⟨l, u, hxu, hlu⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hx)
      let y : ℝ := (x + u) / 2
      have hyI : y ∈ Ioo l u := by
        constructor
        · dsimp [y]
          linarith [hxu.1, hxu.2]
        · dsimp [y]
          linarith [hxu.2]
      have hy := hlu hyI
      have hsup : y ≤ sSup s := le_csSup habove hy
      rw [← heq] at hsup
      dsimp [y] at hsup
      linarith [hxu.2]
    exact ⟨hlow, hupp⟩
  · exact hc.Ioo_csInf_csSup_subset hbelow habove

def sublevelComponent (f : Polynomial ℝ) (x : ℝ) : Set ℝ :=
  connectedComponentIn (sublevelSet f) x

/-- A root of an admissible polynomial belongs to its strict unit sublevel
set. -/
theorem root_mem_sublevelSet {f : Polynomial ℝ}
    {r : ℝ} (hr : r ∈ f.roots) : r ∈ sublevelSet f := by
  have hz : f.eval r = 0 := (Polynomial.mem_roots'.mp hr).2
  change |f.eval r| < 1
  rw [hz]
  norm_num

theorem rootSet_subset_sublevelSet (f : Polynomial ℝ) :
    rootSet f ⊆ sublevelSet f := by
  intro r hr
  exact root_mem_sublevelSet (mem_rootSet_iff.mp hr)

theorem sublevelComponent_eq_Ioo {f : Polynomial ℝ} (hf : IsAdmissible f)
    {x : ℝ} (hx : x ∈ sublevelSet f) :
    sublevelComponent f x =
      Ioo (sInf (sublevelComponent f x)) (sSup (sublevelComponent f x)) := by
  apply eq_Ioo_sInf_sSup_of_isOpen_isConnected
  · exact (isOpen_sublevelSet f).connectedComponentIn
  · exact isConnected_connectedComponentIn_iff.mpr hx
  · refine ⟨-2, ?_⟩
    intro y hy
    exact (hf.sublevelSet_subset_Ioo
      (connectedComponentIn_subset (sublevelSet f) x hy)).1.le
  · refine ⟨2, ?_⟩
    intro y hy
    exact (hf.sublevelSet_subset_Ioo
      (connectedComponentIn_subset (sublevelSet f) x hy)).2.le

theorem sublevelComponent_sInf_not_mem {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∈ sublevelSet f) :
    sInf (sublevelComponent f x) ∉ sublevelSet f := by
  intro ha
  let a := sInf (sublevelComponent f x)
  let b := sSup (sublevelComponent f x)
  have hC := sublevelComponent_eq_Ioo hf hx
  have hC' : sublevelComponent f x = Ioo a b := by
    simpa only [a, b] using! hC
  have hxC : x ∈ sublevelComponent f x := mem_connectedComponentIn hx
  have hxI : x ∈ Ioo a b := hC' ▸ hxC
  have hinterval : Icc a x ⊆ sublevelSet f := by
    intro y hy
    rcases hy.1.eq_or_lt with rfl | hay
    · exact ha
    · exact connectedComponentIn_subset (sublevelSet f) x (by
        change y ∈ sublevelComponent f x
        rw [hC']
        exact ⟨hay, hy.2.trans_lt hxI.2⟩)
  have hsubset := isPreconnected_Icc.subset_connectedComponentIn
    (show x ∈ Icc a x by simp [hxI.1.le]) hinterval
  have haa : a ∈ sublevelComponent f x := hsubset (by simp [hxI.1.le])
  rw [hC'] at haa
  exact haa.1.false

theorem sublevelComponent_sSup_not_mem {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∈ sublevelSet f) :
    sSup (sublevelComponent f x) ∉ sublevelSet f := by
  intro hbmem
  let a := sInf (sublevelComponent f x)
  let b := sSup (sublevelComponent f x)
  have hC := sublevelComponent_eq_Ioo hf hx
  have hC' : sublevelComponent f x = Ioo a b := by
    simpa only [a, b] using! hC
  have hxC : x ∈ sublevelComponent f x := mem_connectedComponentIn hx
  have hxI : x ∈ Ioo a b := hC' ▸ hxC
  have hinterval : Icc x b ⊆ sublevelSet f := by
    intro y hy
    rcases hy.2.eq_or_lt with rfl | hyb
    · exact hbmem
    · exact connectedComponentIn_subset (sublevelSet f) x (by
        change y ∈ sublevelComponent f x
        rw [hC']
        exact ⟨hxI.1.trans_le hy.1, hyb⟩)
  have hsubset := isPreconnected_Icc.subset_connectedComponentIn
    (show x ∈ Icc x b by simp [hxI.2.le]) hinterval
  have hbb : b ∈ sublevelComponent f x := hsubset (by simp [hxI.2.le])
  rw [hC'] at hbb
  exact hbb.2.false

theorem sublevelComponent_endpoints_frontier {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∈ sublevelSet f) :
    sInf (sublevelComponent f x) ∈ frontier (sublevelSet f) ∧
      sSup (sublevelComponent f x) ∈ frontier (sublevelSet f) := by
  let a := sInf (sublevelComponent f x)
  let b := sSup (sublevelComponent f x)
  have hC := sublevelComponent_eq_Ioo hf hx
  have hC' : sublevelComponent f x = Ioo a b := by
    simpa only [a, b] using! hC
  have hxC : x ∈ sublevelComponent f x := mem_connectedComponentIn hx
  have hxI : x ∈ Ioo a b := hC' ▸ hxC
  have hsub : sublevelComponent f x ⊆ sublevelSet f :=
    connectedComponentIn_subset _ _
  have haclos : a ∈ closure (sublevelSet f) := by
    apply closure_mono hsub
    rw [hC', closure_Ioo (ne_of_lt (hxI.1.trans hxI.2))]
    exact ⟨le_rfl, hxI.1.le.trans hxI.2.le⟩
  have hbclos : b ∈ closure (sublevelSet f) := by
    apply closure_mono hsub
    rw [hC', closure_Ioo (ne_of_lt (hxI.1.trans hxI.2))]
    exact ⟨hxI.1.le.trans hxI.2.le, le_rfl⟩
  rw [frontier, (isOpen_sublevelSet f).interior_eq]
  constructor
  · exact ⟨haclos, sublevelComponent_sInf_not_mem hf hx⟩
  · exact ⟨hbclos, sublevelComponent_sSup_not_mem hf hx⟩

theorem sublevelComponent_contains_root {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∈ sublevelSet f) :
    ∃ r ∈ f.roots, r ∈ sublevelComponent f x := by
  let a := sInf (sublevelComponent f x)
  let b := sSup (sublevelComponent f x)
  have hC := sublevelComponent_eq_Ioo hf hx
  have hC' : sublevelComponent f x = Ioo a b := by
    simpa only [a, b] using! hC
  have hxC : x ∈ sublevelComponent f x := mem_connectedComponentIn hx
  have hxI : x ∈ Ioo a b := hC' ▸ hxC
  have hend := sublevelComponent_endpoints_frontier hf hx
  have ha := frontier_sublevelSet_abs_eval_eq_one f hend.1
  have hb := frontier_sublevelSet_abs_eval_eq_one f hend.2
  obtain ⟨r, hr, hrI⟩ := interval_sublevel_contains_root hf
    (show a < b from hxI.1.trans hxI.2) ha hb (by
      rw [← hC']
      exact connectedComponentIn_subset _ _)
  exact ⟨r, hr, by rw [hC']; exact hrI⟩

/-- The family of connected components which meet the strict sublevel set. -/
def sublevelComponentFamily (f : Polynomial ℝ) : Set (Set ℝ) :=
  (fun x ↦ sublevelComponent f x) '' sublevelSet f

/-- Every sublevel component is represented by one of the finitely many
distinct roots. -/
theorem sublevelComponentFamily_eq_image_rootSet {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    sublevelComponentFamily f =
      (fun r ↦ sublevelComponent f r) '' rootSet f := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hrC⟩ := sublevelComponent_contains_root hf hx
    refine ⟨r, mem_rootSet_iff.mpr hr, ?_⟩
    exact (connectedComponentIn_eq hrC).symm
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, rootSet_subset_sublevelSet f hr, rfl⟩

/-- In particular, an admissible polynomial has only finitely many strict
sublevel components. -/
theorem finite_sublevelComponentFamily {f : Polynomial ℝ}
    (hf : IsAdmissible f) : (sublevelComponentFamily f).Finite := by
  rw [sublevelComponentFamily_eq_image_rootSet hf]
  exact (rootSet_finite f).image _

/-- The strict sublevel set is the union of its finite component family. -/
theorem sublevelSet_eq_biUnion_components (f : Polynomial ℝ) :
    sublevelSet f = ⋃ C ∈ sublevelComponentFamily f, C := by
  apply Subset.antisymm
  · intro x hx
    exact mem_iUnion₂.mpr
      ⟨sublevelComponent f x, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hy, rfl⟩ := hC
    exact connectedComponentIn_subset (sublevelSet f) y hxC

end

end Erdos1038
