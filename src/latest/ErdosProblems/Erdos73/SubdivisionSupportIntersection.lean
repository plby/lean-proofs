import ErdosProblems.Erdos73.SubdivisionAnchors

/-! Actual subdivision support preserves intersections and singleton junctions. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem branch_mem_supportOver_iff (S : GraphSubdivisionModel H G) (T : Finset W) (w : W) :
    S.branchVertex w ∈ S.supportOver T ↔ w ∈ T := by
  constructor
  · intro hw
    rcases (S.mem_supportOver T _).mp hw with ⟨u, hu, he⟩ | ⟨e, he, he', hw⟩
    · exact S.injective he ▸ hu
    · exact (S.branch_on_path e w hw).elim (fun h => h ▸ he) (fun h => h ▸ he')
  · intro hw
    exact (S.mem_supportOver T _).mpr (Or.inl ⟨w, hw, rfl⟩)

theorem supportOver_inter (S : GraphSubdivisionModel H G) (T R : Finset W) :
    S.supportOver (T ∩ R) = S.supportOver T ∩ S.supportOver R := by
  apply Subset.antisymm
  · exact subset_inter (S.supportOver_mono inter_subset_left) (S.supportOver_mono inter_subset_right)
  · intro x hx
    obtain ⟨hxT, hxR⟩ := mem_inter.mp hx
    rcases (S.mem_supportOver T x).mp hxT with ⟨w, hw, rfl⟩ | ⟨e, he, he', hxe⟩
    · exact (S.branch_mem_supportOver_iff _ w).mpr
        (mem_inter.mpr ⟨hw, (S.branch_mem_supportOver_iff R w).mp hxR⟩)
    · rcases (S.mem_supportOver R x).mp hxR with ⟨w, hw, rfl⟩ | ⟨d, hd, hd', hxd⟩
      · exact (S.branch_mem_supportOver_iff _ w).mpr
          (mem_inter.mpr ⟨(S.branch_mem_supportOver_iff T w).mp hxT, hw⟩)
      · by_cases hed : e = d
        · subst d
          exact (S.mem_supportOver _ x).mpr (Or.inr
            ⟨e, mem_inter.mpr ⟨he, hd⟩, mem_inter.mpr ⟨he', hd'⟩, hxe⟩)
        · obtain ⟨w, rfl, hwe, hwd⟩ := S.intersection hed x hxe hxd
          exact (S.branch_mem_supportOver_iff _ w).mpr (mem_inter.mpr
            ⟨hwe.elim (fun h => h ▸ he) (fun h => h ▸ he'),
              hwd.elim (fun h => h ▸ hd) (fun h => h ▸ hd')⟩)

theorem supportOver_singleton (S : GraphSubdivisionModel H G) (w : W) :
    S.supportOver {w} = {S.branchVertex w} := by
  ext x
  constructor
  · intro hx
    rcases (S.mem_supportOver _ x).mp hx with ⟨u, hu, he⟩ | ⟨e, he, he', _⟩
    · rw [mem_singleton] at hu
      exact mem_singleton.mpr (he.symm.trans (congrArg S.branchVertex hu))
    · have hh : e.lo = e.hi := (mem_singleton.mp he).trans (mem_singleton.mp he').symm
      exact (e.lo_lt_hi.ne hh).elim
  · intro hx
    rw [mem_singleton] at hx
    subst x
    exact (S.branch_mem_supportOver_iff _ w).mpr (mem_singleton_self w)

theorem supportOver_inter_subset_singleton (S : GraphSubdivisionModel H G)
    {T R : Finset W} {w : W} (hTR : T ∩ R ⊆ {w}) :
    S.supportOver T ∩ S.supportOver R ⊆ {S.branchVertex w} := by
  rw [← S.supportOver_inter, ← S.supportOver_singleton]
  exact S.supportOver_mono hTR

end
end Erdos73.GraphSubdivisionModel
