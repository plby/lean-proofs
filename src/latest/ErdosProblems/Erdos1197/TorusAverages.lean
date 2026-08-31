import ErdosProblems.Erdos1197.TorusFourierIntegral

namespace Erdos1197

open scoped BigOperators

noncomputable section

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

def torusAnnihilator (H : ClosedAddSubgroup (UnitAddTorus d)) : Set (d → ℤ) :=
  {n | ∀ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) = 1}

lemma avgOverSubgroup_mFourier_of_mem_ann
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ)
    (hn : n ∈ torusAnnihilator (d := d) H) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) = UnitAddTorus.mFourier n := by
  ext y
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using subgroup_univ_measure (d := d) H
  rw [avgOverSubgroup_apply]
  have hmul :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n (h : UnitAddTorus d) := by
    intro h
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]
  have hconst :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y := by
    intro h
    rw [hmul h, hn h, mul_one]
  calc
    ∫ h : H, UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) ∂μH
        = ∫ h : H, UnitAddTorus.mFourier n y ∂μH := by
            apply integral_congr_ae
            filter_upwards with h
            rw [hconst h]
    _ = UnitAddTorus.mFourier n y := by
          rw [integral_const, Measure.real_def, hμ, ENNReal.toReal_one, one_smul]

lemma avgOverSubgroup_mFourier_of_not_mem_ann
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ)
    (hn : n ∉ torusAnnihilator (d := d) H) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) = 0 := by
  ext y
  rw [avgOverSubgroup_apply]
  have hmul :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n (h : UnitAddTorus d) := by
    intro h
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]
  obtain ⟨h, hh⟩ : ∃ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) ≠ 1 := by
    by_contra hcontra
    apply hn
    intro h
    by_contra hh
    exact hcontra ⟨h, hh⟩
  calc
    ∫ h' : H, UnitAddTorus.mFourier n (y + (h' : UnitAddTorus d))
        ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H)))
        = ∫ h' : H, UnitAddTorus.mFourier n y *
            UnitAddTorus.mFourier n (h' : UnitAddTorus d)
            ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
              apply integral_congr_ae
              filter_upwards with h'
              rw [hmul h']
    _ = UnitAddTorus.mFourier n y *
          ∫ h' : H, UnitAddTorus.mFourier n (h' : UnitAddTorus d)
            ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
              rw [integral_const_mul]
    _ = 0 := by
          rw [integral_mFourier_eq_zero_of_nontrivial (d := d) n H h hh, mul_zero]

def annSubmodule (H : ClosedAddSubgroup (UnitAddTorus d)) :
    Submodule ℂ C(UnitAddTorus d, ℂ) :=
  Submodule.span ℂ ((fun n : d → ℤ => UnitAddTorus.mFourier n) '' torusAnnihilator (d := d) H)

lemma avgOverSubgroup_mem_annSubmodule_mFourier
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) ∈ annSubmodule (d := d) H := by
  by_cases hn : n ∈ torusAnnihilator (d := d) H
  · have hmem : UnitAddTorus.mFourier n ∈ annSubmodule (d := d) H := by
      exact Submodule.subset_span ⟨n, hn, rfl⟩
    simpa [avgOverSubgroup_mFourier_of_mem_ann (d := d) H n hn] using hmem
  · rw [avgOverSubgroup_mFourier_of_not_mem_ann (d := d) H n hn]
    exact Submodule.zero_mem (annSubmodule (d := d) H)

lemma avgOverSubgroup_mem_annSubmodule_of_mem_span
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {f : C(UnitAddTorus d, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d)))) :
    avgOverSubgroup (d := d) H f ∈ annSubmodule (d := d) H := by
  let p :
      (g : C(UnitAddTorus d, ℂ)) →
        g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))) → Prop :=
    fun g _ => avgOverSubgroup (d := d) H g ∈ annSubmodule (d := d) H
  change p f hf
  refine Submodule.span_induction
    (s := Set.range (UnitAddTorus.mFourier (d := d))) (p := p) ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨n, rfl⟩
    exact avgOverSubgroup_mem_annSubmodule_mFourier (d := d) H n
  · simp [p, avgOverSubgroup]
  · intro x y hx hy hxmem hymem
    simpa [p, avgOverSubgroup_add (d := d) H x y] using
      (annSubmodule (d := d) H).add_mem hxmem hymem
  · intro c x hx hxmem
    simpa [p, avgOverSubgroup_smul (d := d) H c x] using
      (annSubmodule (d := d) H).smul_mem c hxmem

lemma avgOverSubgroup_mem_closure_annSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H f ∈
      closure (annSubmodule (d := d) H : Set C(UnitAddTorus d, ℂ)) := by
  have hf :
      f ∈ closure (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))) :
        Set C(UnitAddTorus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe,
      UnitAddTorus.span_mFourier_closure_eq_top]
    simp
  refine map_mem_closure (avgOverSubgroup_continuous (d := d) H) hf ?_
  intro g hg
  exact avgOverSubgroup_mem_annSubmodule_of_mem_span (d := d) H hg

end

end Erdos1197
