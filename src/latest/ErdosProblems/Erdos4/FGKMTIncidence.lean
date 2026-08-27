import ErdosProblems.Erdos4.FGKMTConditionalSurvival
import ErdosProblems.Erdos4.FGKMTLawMoments

/-!
# The aggregate edge law seen from a vertex

Sampling a source edge with weight proportional to its incidence at `v`,
then erasing `v`, converts pair-degree bounds into sparse marginals.
The construction also covers zero-degree vertices, using the empty edge.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def edgeIntensity (μ : I → FiniteLaw (Finset V)) (e : Finset V) : ℝ :=
  ∑ i, (μ i).weight e

noncomputable def vertexDegree (μ : I → FiniteLaw (Finset V)) (v : V) : ℝ :=
  ∑ i, (μ i).prob (fun e => v ∈ e)

noncomputable def pairDegree (μ : I → FiniteLaw (Finset V)) (v w : V) : ℝ :=
  ∑ i, (μ i).prob (fun e => v ∈ e ∧ w ∈ e)

omit [DecidableEq V] in
theorem edgeIntensity_nonneg (μ : I → FiniteLaw (Finset V)) (e : Finset V) :
    0 ≤ edgeIntensity μ e := Finset.sum_nonneg (fun i _hi => (μ i).nonneg e)

omit [DecidableEq V] in
theorem vertexDegree_nonneg (μ : I → FiniteLaw (Finset V)) (v : V) :
    0 ≤ vertexDegree μ v := Finset.sum_nonneg (fun i _hi => (μ i).prob_nonneg _)

omit [DecidableEq V] in
theorem pairDegree_nonneg (μ : I → FiniteLaw (Finset V)) (v w : V) :
    0 ≤ pairDegree μ v w := Finset.sum_nonneg (fun i _hi => (μ i).prob_nonneg _)

theorem incidence_mass_total (μ : I → FiniteLaw (Finset V)) (v : V) :
    (∑ e, if v ∈ e then edgeIntensity μ e else 0) = vertexDegree μ v := by
  classical
  unfold edgeIntensity vertexDegree FiniteLaw.prob
  calc
    _ = ∑ e : Finset V, ∑ i, if v ∈ e then (μ i).weight e else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hv : v ∈ e <;> simp [hv]
    _ = ∑ i, ∑ e : Finset V, if v ∈ e then (μ i).weight e else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hv : v ∈ e <;> simp [hv]

noncomputable def incidenceLaw (μ : I → FiniteLaw (Finset V)) (v : V) :
    FiniteLaw (Finset V) :=
  FiniteLaw.normalize (fun e => if v ∈ e then edgeIntensity μ e else 0)
    (fun e => by split_ifs; exact edgeIntensity_nonneg μ e; rfl) ∅

theorem incidenceLaw_weight (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : vertexDegree μ v ≠ 0) (e : Finset V) :
    (incidenceLaw μ v).weight e =
      (if v ∈ e then edgeIntensity μ e else 0) / vertexDegree μ v := by
  rw [incidenceLaw, FiniteLaw.normalize_weight]
  · rw [incidence_mass_total]
  · rwa [incidence_mass_total]

theorem incidenceLaw_mean (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : vertexDegree μ v ≠ 0) (f : Finset V → ℝ) :
    (incidenceLaw μ v).mean f =
      (∑ i, (μ i).mean (fun e => if v ∈ e then f e else 0)) / vertexDegree μ v := by
  unfold FiniteLaw.mean
  simp only [incidenceLaw_weight μ v hd, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  unfold edgeIntensity
  by_cases hv : v ∈ e <;> simp [hv, Finset.sum_mul]

theorem incidenceLaw_prob (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : vertexDegree μ v ≠ 0) (E : Finset V → Prop) :
    (incidenceLaw μ v).prob E =
      (∑ i, (μ i).prob (fun e => v ∈ e ∧ E e)) / vertexDegree μ v := by
  classical
  rw [FiniteLaw.prob_eq_mean, incidenceLaw_mean μ v hd]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [FiniteLaw.prob_eq_mean]
  apply (μ i).mean_congr
  intro e
  by_cases hv : v ∈ e <;> by_cases he : E e <;> simp [hv, he]

theorem incidenceLaw_support (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : 0 < vertexDegree μ v) (e : Finset V)
    (he : 0 < (incidenceLaw μ v).weight e) : v ∈ e ∧ ∃ i, 0 < (μ i).weight e := by
  rw [incidenceLaw_weight μ v (ne_of_gt hd)] at he
  have hmass : 0 < if v ∈ e then edgeIntensity μ e else 0 :=
    (div_pos_iff_of_pos_right hd).mp he
  have hv : v ∈ e := by
    by_contra hv
    simp only [if_neg hv] at hmass
    linarith
  rw [if_pos hv] at hmass
  refine ⟨hv, ?_⟩
  by_contra hnone
  have hzero : edgeIntensity μ e ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _hi
    exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
  linarith

noncomputable def erasedIncidence (μ : I → FiniteLaw (Finset V)) (v : V) :
    FiniteLaw (Finset V) := (incidenceLaw μ v).map (fun e => e.erase v)

theorem erasedIncidence_mean (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : vertexDegree μ v ≠ 0) (f : Finset V → ℝ) :
    (erasedIncidence μ v).mean f =
      (∑ i, (μ i).mean (fun e => if v ∈ e then f (e.erase v) else 0)) /
        vertexDegree μ v := by
  rw [erasedIncidence, FiniteLaw.mean_map, incidenceLaw_mean μ v hd]

theorem erasedIncidence_marginal (μ : I → FiniteLaw (Finset V)) (v w : V)
    (hd : vertexDegree μ v ≠ 0) :
    (erasedIncidence μ v).prob (fun e => w ∈ e) =
      if w = v then 0 else pairDegree μ v w / vertexDegree μ v := by
  classical
  rw [erasedIncidence, FiniteLaw.prob_map, incidenceLaw_prob μ v hd]
  by_cases hw : w = v
  · subst w
    simp [FiniteLaw.prob, Finset.mem_erase]
  · rw [if_neg hw]
    congr 1
    unfold pairDegree
    apply Finset.sum_congr rfl
    intro i _hi
    apply le_antisymm
    · exact (μ i).prob_mono (fun e he => ⟨he.1, (Finset.mem_erase.mp he.2).2⟩)
    · exact (μ i).prob_mono (fun e he => ⟨he.1, Finset.mem_erase.mpr ⟨hw, he.2⟩⟩)

theorem erasedIncidence_sparse (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : 0 < vertexDegree μ v) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpair : ∀ w, w ≠ v → pairDegree μ v w ≤ δ) :
    ∀ w, (erasedIncidence μ v).prob (fun e => w ∈ e) ≤ δ / vertexDegree μ v := by
  intro w
  rw [erasedIncidence_marginal μ v w (ne_of_gt hd)]
  split_ifs with hw
  · exact div_nonneg hδ hd.le
  · exact div_le_div_of_nonneg_right (hpair w hw) hd.le

end Erdos4.FGKMT
