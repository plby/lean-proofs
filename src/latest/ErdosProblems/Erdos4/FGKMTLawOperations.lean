import ErdosProblems.Erdos4.FGKMTFiniteLaw

/-! Exact finite-law operations used to construct successive covering rounds. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω Λ I : Type*} [Fintype Ω] [Fintype Λ] [Fintype I] [DecidableEq I]

noncomputable def dirac (o₀ : Ω) : FiniteLaw Ω := by
  classical
  exact ⟨fun o => if o = o₀ then 1 else 0,
    fun o => by split_ifs <;> norm_num, by simp⟩

theorem mean_dirac (o₀ : Ω) (f : Ω → ℝ) : (dirac o₀).mean f = f o₀ := by
  classical
  simp [mean, dirac]

noncomputable def bind (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Λ) : FiniteLaw Λ where
  weight l := ∑ o, μ.weight o * (ν o).weight l
  nonneg l := Finset.sum_nonneg (fun o _ho => mul_nonneg (μ.nonneg o) ((ν o).nonneg l))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, total, mul_one]

theorem mean_bind (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Λ) (f : Λ → ℝ) :
    (μ.bind ν).mean f = μ.mean (fun o => (ν o).mean f) := by
  simp only [mean, bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

noncomputable def map (μ : FiniteLaw Ω) (f : Ω → Λ) : FiniteLaw Λ :=
  μ.bind (fun o => dirac (f o))

theorem mean_map (μ : FiniteLaw Ω) (f : Ω → Λ) (g : Λ → ℝ) :
    (μ.map f).mean g = μ.mean (fun o => g (f o)) := by
  rw [map, mean_bind]
  simp only [mean_dirac]

theorem prob_map (μ : FiniteLaw Ω) (f : Ω → Λ) (E : Λ → Prop) :
    (μ.map f).prob E = μ.prob (fun o => E (f o)) := by
  classical
  rw [prob_eq_mean, mean_map, ← prob_eq_mean]

theorem prob_bind (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Λ) (E : Λ → Prop) :
    (μ.bind ν).prob E = μ.mean (fun o => (ν o).prob E) := by
  classical
  rw [prob_eq_mean, mean_bind]
  simp only [← prob_eq_mean]

noncomputable def independent (μ : I → FiniteLaw Ω) : FiniteLaw (I → Ω) where
  weight choice := ∏ i, (μ i).weight (choice i)
  nonneg choice := Finset.prod_nonneg (fun i _hi => (μ i).nonneg (choice i))
  total := by
    rw [← Fintype.prod_sum (fun i o => (μ i).weight o)]
    simp only [total, Finset.prod_const_one]

theorem independent_mean_prod (μ : I → FiniteLaw Ω) (f : I → Ω → ℝ) :
    (independent μ).mean (fun choice => ∏ i, f i (choice i)) =
      ∏ i, (μ i).mean (f i) := by
  simp only [mean, independent, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i o => (μ i).weight o * f i o)).symm

theorem independent_prob_all (μ : I → FiniteLaw Ω) (E : I → Ω → Prop) :
    (independent μ).prob (fun choice => ∀ i, E i (choice i)) = ∏ i, (μ i).prob (E i) := by
  classical
  rw [prob_eq_mean]
  calc
    _ = (independent μ).mean (fun choice => ∏ i, if E i (choice i) then (1 : ℝ) else 0) := by
      apply (independent μ).mean_congr
      intro choice
      by_cases he : ∀ i, E i (choice i)
      · simp [he]
      · rw [if_neg he]
        obtain ⟨i, hi⟩ := not_forall.mp he
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    _ = ∏ i, (μ i).mean (fun o => if E i o then 1 else 0) :=
      independent_mean_prod μ (fun (i : I) (o : Ω) => if E i o then (1 : ℝ) else 0)
    _ = _ := by simp only [← prob_eq_mean]

noncomputable def normalize (w : Ω → ℝ) (hw : ∀ o, 0 ≤ w o) (o₀ : Ω) : FiniteLaw Ω := by
  classical
  exact if hZ : (∑ o, w o) = 0 then dirac o₀ else
    ⟨fun o => w o / ∑ a, w a,
      fun o => div_nonneg (hw o) (Finset.sum_nonneg (fun a _ha => hw a)),
      by rw [← Finset.sum_div, div_self hZ]⟩

theorem normalize_weight (w : Ω → ℝ) (hw : ∀ o, 0 ≤ w o) (o₀ o : Ω)
    (hZ : (∑ a, w a) ≠ 0) : (normalize w hw o₀).weight o = w o / ∑ a, w a := by
  classical
  simp only [normalize, dif_neg hZ]

theorem normalize_support (w : Ω → ℝ) (hw : ∀ o, 0 ≤ w o) (o₀ o : Ω)
    (ho : 0 < (normalize w hw o₀).weight o) : o = o₀ ∨ 0 < w o := by
  classical
  by_cases hZ : (∑ a, w a) = 0
  · have hh : 0 < (dirac o₀).weight o := by simpa only [normalize, dif_pos hZ] using ho
    by_cases heq : o = o₀
    · exact Or.inl heq
    · simp only [dirac, if_neg heq] at hh
      linarith
  · right
    rw [normalize_weight w hw o₀ o hZ] at ho
    have hpos : 0 < ∑ a, w a := lt_of_le_of_ne (Finset.sum_nonneg (fun a _ha => hw a)) (Ne.symm hZ)
    exact (div_pos_iff.mp ho).resolve_right (fun hh => (not_lt_of_ge hpos.le) hh.2) |>.1

end Erdos4.FGKMT.FiniteLaw
