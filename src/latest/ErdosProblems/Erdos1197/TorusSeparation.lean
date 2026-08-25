import ErdosProblems.Erdos1197.TorusAverages

namespace Erdos1197

open scoped BigOperators

noncomputable section

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

def sameValueCLM (x : UnitAddTorus d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ x : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ) -
    (ContinuousMap.evalCLM ℂ (0 : UnitAddTorus d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ)

def sameValueSubmodule (x : UnitAddTorus d) : Submodule ℂ C(UnitAddTorus d, ℂ) :=
  (sameValueCLM (d := d) x).toLinearMap.ker

omit [Fintype d] in
lemma mem_sameValueSubmodule_iff
    (x : UnitAddTorus d) (f : C(UnitAddTorus d, ℂ)) :
    f ∈ sameValueSubmodule (d := d) x ↔ f x = f 0 := by
  simp [sameValueSubmodule, sameValueCLM, sub_eq_zero]

omit [Fintype d] in
lemma isClosed_sameValueSubmodule (x : UnitAddTorus d) :
    IsClosed (sameValueSubmodule (d := d) x : Set C(UnitAddTorus d, ℂ)) := by
  simpa [sameValueSubmodule] using
    (ContinuousLinearMap.isClosed_ker (sameValueCLM (d := d) x))

lemma annSubmodule_le_sameValueSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    annSubmodule (d := d) H ≤ sameValueSubmodule (d := d) x := by
  refine Submodule.span_le.2 ?_
  intro f hf
  rcases hf with ⟨n, hn, rfl⟩
  show UnitAddTorus.mFourier n ∈ sameValueSubmodule (d := d) x
  rw [mem_sameValueSubmodule_iff]
  calc
    UnitAddTorus.mFourier n x = 1 := hx n hn
    _ = UnitAddTorus.mFourier n (0 : UnitAddTorus d) := by
      symm
      simp [UnitAddTorus.mFourier]

lemma closure_annSubmodule_le_sameValueSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    closure (annSubmodule (d := d) H : Set C(UnitAddTorus d, ℂ)) ⊆
      sameValueSubmodule (d := d) x := by
  have hclosure :
      (annSubmodule (d := d) H).topologicalClosure ≤ sameValueSubmodule (d := d) x :=
    Submodule.topologicalClosure_minimal (annSubmodule (d := d) H)
      (annSubmodule_le_sameValueSubmodule (d := d) H x hx)
      (isClosed_sameValueSubmodule (d := d) x)
  intro f hf
  apply hclosure
  rw [← Submodule.topologicalClosure_coe] at hf
  exact hf

lemma avgOverSubgroup_eq_at_zero_of_annihilator
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1)
    (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H f x = avgOverSubgroup (d := d) H f 0 := by
  have havg_closure :=
    avgOverSubgroup_mem_closure_annSubmodule (d := d) H f
  have havg_same :
      avgOverSubgroup (d := d) H f ∈ sameValueSubmodule (d := d) x :=
    closure_annSubmodule_le_sameValueSubmodule (d := d) H x hx havg_closure
  exact (mem_sameValueSubmodule_iff (d := d) x _).mp havg_same

def xPlusH (H : ClosedAddSubgroup (UnitAddTorus d)) (x : UnitAddTorus d) :
    Set (UnitAddTorus d) :=
  Set.range fun h : H => x + (h : UnitAddTorus d)

omit [Fintype d] in
lemma isCompact_xPlusH
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d) :
    IsCompact (xPlusH (d := d) H x) := by
  change IsCompact (Set.range fun h : H => x + (h : UnitAddTorus d))
  exact isCompact_range
    (continuous_const.add continuous_subtype_val :
      Continuous fun h : H => x + (h : UnitAddTorus d))

omit [Fintype d] in
lemma disjoint_xPlusH
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {x : UnitAddTorus d}
    (hx : x ∉ H) :
    Disjoint (xPlusH (d := d) H x) (H : Set (UnitAddTorus d)) := by
  refine Set.disjoint_left.2 ?_
  intro y hyx hyH
  rcases hyx with ⟨h, rfl⟩
  exact hx <| by
    change x ∈ (H : Set (UnitAddTorus d))
    have hx' : x + (h : UnitAddTorus d) - h = x := add_sub_cancel_right _ _
    rw [← hx']
    exact H.sub_mem hyH h.2

lemma integral_const_subgroup
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (c : ℂ) :
    (∫ _h : H, c ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H)))) = c := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using subgroup_univ_measure (d := d) H
  haveI : IsFiniteMeasure μH := ⟨by simp [hμ]⟩
  rw [integral_const, Measure.real_def, hμ, ENNReal.toReal_one, one_smul]

def ofRealContinuousMap (f : C(UnitAddTorus d, ℝ)) : C(UnitAddTorus d, ℂ) where
  toFun y := (f y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

lemma avgOverSubgroup_zero_at_zero
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ))
    (hf : Set.EqOn f (fun _ => 0) (H : Set (UnitAddTorus d))) :
    avgOverSubgroup (d := d) H f 0 = 0 := by
  rw [avgOverSubgroup_apply]
  have hconst : (fun h : H => f (0 + (h : UnitAddTorus d))) = fun _ : H => 0 := by
    funext h
    simpa using hf (x := (h : UnitAddTorus d)) h.2
  rw [hconst, integral_zero]

lemma avgOverSubgroup_one_at_x
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (f : C(UnitAddTorus d, ℂ))
    (hf : Set.EqOn f (fun _ => 1) (xPlusH (d := d) H x)) :
    avgOverSubgroup (d := d) H f x = 1 := by
  rw [avgOverSubgroup_apply]
  have hconst : (fun h : H => f (x + (h : UnitAddTorus d))) = fun _ : H => 1 := by
    funext h
    exact hf (x := x + (h : UnitAddTorus d)) ⟨h, rfl⟩
  rw [hconst]
  exact integral_const_subgroup (d := d) H 1

theorem mem_of_mFourier_eq_one_on_annihilator
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {x : UnitAddTorus d}
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    x ∈ H := by
  by_contra hxnot
  obtain ⟨fR, hfR0, hfR1, _⟩ :=
    exists_continuous_zero_one_of_isCompact'
      (isCompact_xPlusH (d := d) H x) H.isClosed'
      (disjoint_xPlusH (d := d) H hxnot)
  let f : C(UnitAddTorus d, ℂ) := ofRealContinuousMap (d := d) fR
  have hf0 : Set.EqOn f (fun _ => 0) (H : Set (UnitAddTorus d)) := by
    intro y hy
    change ((fR y : ℂ) = 0)
    simpa [f] using hfR0 (x := y) hy
  have hf1 : Set.EqOn f (fun _ => 1) (xPlusH (d := d) H x) := by
    intro y hy
    change ((fR y : ℂ) = 1)
    simpa [f] using hfR1 (x := y) hy
  have h_eq :
      avgOverSubgroup (d := d) H f x = avgOverSubgroup (d := d) H f 0 :=
    avgOverSubgroup_eq_at_zero_of_annihilator (d := d) H x hx f
  have h0 : avgOverSubgroup (d := d) H f 0 = 0 :=
    avgOverSubgroup_zero_at_zero (d := d) H f hf0
  have h1 : avgOverSubgroup (d := d) H f x = 1 :=
    avgOverSubgroup_one_at_x (d := d) H x f hf1
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = avgOverSubgroup (d := d) H f x := by simpa using h1.symm
      _ = avgOverSubgroup (d := d) H f 0 := h_eq
      _ = 0 := h0
  exact one_ne_zero this

lemma mFourier_eq_one_iff_exists_int
    (n : ℕ) (r : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) = 1 ↔
      ∃ z : ℤ, (∑ j, x j * (r j : ℝ)) = z := by
  have hmfourier :
      UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) =
        Complex.exp (2 * Real.pi * Complex.I * (∑ j, x j * (r j : ℝ))) := by
    calc
      UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) =
          ∏ j, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℝ) * x j)) := by
            simp [UnitAddTorus.mFourier, mul_assoc, mul_left_comm, mul_comm]
      _ = Complex.exp (∑ j, 2 * Real.pi * Complex.I * ((r j : ℝ) * x j)) := by
            rw [← Complex.exp_sum]
      _ = Complex.exp (2 * Real.pi * Complex.I * (∑ j, x j * (r j : ℝ))) := by
            congr 1
            rw [show ((↑(∑ j, x j * (r j : ℝ)) : ℝ) : ℂ) =
                ∑ j, (((x j * (r j : ℝ)) : ℝ) : ℂ) by
                  simp]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [hmfourier]
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    rcases h with ⟨m, hm⟩
    use m
    have him := congrArg Complex.im hm
    simp at him
    nlinarith [Real.pi_pos]
  · rintro ⟨z, hz⟩
    rw [hz]
    rw [Complex.exp_eq_one_iff]
    refine ⟨z, ?_⟩
    simp [mul_left_comm, mul_comm]

/-- A BM-facing specialization of Kronecker's hard direction: one common denominator for many
target coordinates. The nonzero-denominator normalization is deferred to the BM application. -/
theorem kronecker_intrel_implies_approx_common_q_int
    (n : ℕ) (α β : Fin n → ℝ)
    (h_intrel : ∀ r : Fin n → ℤ,
      (∃ z : ℤ, ∑ j, α j * (r j : ℝ) = z) →
      ∃ z : ℤ, ∑ j, β j * (r j : ℝ) = z) :
    ∀ ε > 0, ∃ q : ℤ, ∃ p : Fin n → ℤ,
      ∀ j, |(q : ℝ) * α j - (p j : ℝ) - β j| < ε := by
  intro ε hε
  let αbar : UnitAddTorus (Fin n) := fun j => ((α j : ℝ) : AddCircle (1 : ℝ))
  let βbar : UnitAddTorus (Fin n) := fun j => ((β j : ℝ) : AddCircle (1 : ℝ))
  let Z : AddSubgroup (UnitAddTorus (Fin n)) := AddSubgroup.zmultiples αbar
  let H : ClosedAddSubgroup (UnitAddTorus (Fin n)) :=
    ⟨Z.topologicalClosure, AddSubgroup.isClosed_topologicalClosure Z⟩
  have hα_mem : αbar ∈ H := by
    change αbar ∈ Z.topologicalClosure
    exact AddSubgroup.le_topologicalClosure Z <|
      by
        change αbar ∈ AddSubgroup.zmultiples αbar
        convert AddSubgroup.zsmul_mem_zmultiples αbar (1 : ℤ) using 1
        simp
  have hβ_mem : βbar ∈ H := by
    apply mem_of_mFourier_eq_one_on_annihilator (H := H)
    intro r hr
    have hα_fourier : UnitAddTorus.mFourier r αbar = 1 := by
      exact hr ⟨αbar, hα_mem⟩
    have hα_int : ∃ z : ℤ, (∑ j, α j * (r j : ℝ)) = z := by
      exact (mFourier_eq_one_iff_exists_int n r α).mp hα_fourier
    have hβ_int := h_intrel r hα_int
    exact (mFourier_eq_one_iff_exists_int n r β).mpr hβ_int
  have hβ_closure : βbar ∈ closure (Z : Set (UnitAddTorus (Fin n))) := by
    change βbar ∈ Z.topologicalClosure at hβ_mem
    rw [← AddSubgroup.topologicalClosure_coe]
    exact hβ_mem
  rw [Metric.mem_closure_iff] at hβ_closure
  obtain ⟨x, hxS, hxdist⟩ := hβ_closure ε hε
  obtain ⟨q, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hxS
  refine ⟨q, fun j => round ((q : ℝ) * α j - β j), ?_⟩
  intro j
  have hcoord :
      dist (((q • αbar) : UnitAddTorus (Fin n)) j) (βbar j) < ε := by
    simpa [dist_comm] using (dist_pi_lt_iff hε).mp hxdist j
  have hnorm :
      ‖((((q : ℝ) * α j - β j : ℝ) : AddCircle (1 : ℝ)))‖ < ε := by
    simpa [dist_eq_norm, αbar, βbar, zsmul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hcoord
  have hround :
      |((q : ℝ) * α j - β j) - round ((q : ℝ) * α j - β j)| < ε := by
    have := hnorm
    rw [AddCircle.norm_eq] at this
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hround

end

end Erdos1197
