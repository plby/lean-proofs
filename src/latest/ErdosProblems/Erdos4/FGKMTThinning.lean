import ErdosProblems.Erdos4.FGKMTProductMoments
import ErdosProblems.Erdos4.FGKMTSupport
import ErdosProblems.Erdos4.FGKMTIncidence

/-! Independent vertex thinning preserves legal edges and makes degrees exactly equal. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

noncomputable def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw Bool where
  weight b := if b = true then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith
  total := by simp

theorem bernoulli_prob_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulli p hp0 hp1).prob (fun b => b = true) = p := by
  simp [prob, bernoulli]

theorem independent_prob_coordinate {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (i : I) (E : Ω → Prop) :
    (independent μ).prob (fun a => E (a i)) = (μ i).prob E := by
  classical
  rw [prob_eq_mean, independent_mean_coordinate μ i (fun o => if E o then 1 else 0),
    ← prob_eq_mean]

end Erdos4.FGKMT.FiniteLaw

namespace Erdos4.FGKMT

open Classical

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

def thinnedEdge (choice : V → Bool) (e : Finset V) : Finset V :=
  e.filter (fun v => choice v = true)

theorem thinnedEdge_subset (choice : V → Bool) (e : Finset V) : thinnedEdge choice e ⊆ e :=
  Finset.filter_subset _ _

noncomputable def thinningKernel (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (e : Finset V) : FiniteLaw (Finset V) :=
  (FiniteLaw.independent (fun v => FiniteLaw.bernoulli (p v) (hp0 v) (hp1 v))).map
    (fun choice => thinnedEdge choice e)

noncomputable def thinningLaw (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) : FiniteLaw (Finset V) :=
  μ.bind (thinningKernel p hp0 hp1)

theorem thinningKernel_marginal (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (e : Finset V) (v : V) :
    (thinningKernel p hp0 hp1 e).prob (fun f => v ∈ f) = if v ∈ e then p v else 0 := by
  rw [thinningKernel, FiniteLaw.prob_map]
  by_cases hv : v ∈ e
  · simp only [thinnedEdge, Finset.mem_filter, hv, true_and, if_true]
    rw [FiniteLaw.independent_prob_coordinate
      (fun w => FiniteLaw.bernoulli (p w) (hp0 w) (hp1 w)) v (fun b : Bool => b = true),
      FiniteLaw.bernoulli_prob_true]
  · simp only [thinnedEdge, Finset.mem_filter, hv, false_and, if_false]
    simp [FiniteLaw.prob]

theorem thinningLaw_marginal (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) (v : V) :
    (thinningLaw μ p hp0 hp1).prob (fun e => v ∈ e) = p v * μ.prob (fun e => v ∈ e) := by
  rw [thinningLaw, FiniteLaw.prob_bind]
  simp_rw [thinningKernel_marginal]
  calc
    _ = μ.mean (fun e => p v * (if v ∈ e then 1 else 0)) := by
      apply μ.mean_congr
      intro e
      split_ifs <;> ring
    _ = _ := by rw [FiniteLaw.mean_const_mul, ← FiniteLaw.prob_eq_mean]

theorem thinningLaw_prob_le (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (E : Finset V → Prop) (hE : ∀ e f, e ⊆ f → E e → E f) :
    (thinningLaw μ p hp0 hp1).prob E ≤ μ.prob E := by
  rw [thinningLaw, FiniteLaw.prob_bind, μ.prob_eq_mean]
  apply μ.mean_mono
  intro e
  by_cases he : E e
  · rw [if_pos he]
    exact (thinningKernel p hp0 hp1 e).prob_le_one E
  · rw [if_neg he, thinningKernel, FiniteLaw.prob_map]
    have hfalse : (fun choice => E (thinnedEdge choice e)) = (fun _ => False) := by
      funext choice
      exact propext ⟨fun hh => he (hE _ _ (thinnedEdge_subset choice e) hh), False.elim⟩
    rw [hfalse]
    simp [FiniteLaw.prob]

theorem thinningLaw_marginal_le (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) (v : V) :
    (thinningLaw μ p hp0 hp1).prob (fun e => v ∈ e) ≤ μ.prob (fun e => v ∈ e) :=
  thinningLaw_prob_le μ p hp0 hp1 _ (fun _ _ hef hv => hef hv)

theorem thinningLaw_pair_le (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) (v w : V) :
    (thinningLaw μ p hp0 hp1).prob (fun e => v ∈ e ∧ w ∈ e) ≤
      μ.prob (fun e => v ∈ e ∧ w ∈ e) :=
  thinningLaw_prob_le μ p hp0 hp1 _ (fun _ _ hef hvw => ⟨hef hvw.1, hef hvw.2⟩)

theorem thinningLaw_support (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (f : Finset V) (hf : 0 < (thinningLaw μ p hp0 hp1).weight f) :
    ∃ e, 0 < μ.weight e ∧ f ⊆ e := by
  obtain ⟨e, he, hkernel⟩ := FiniteLaw.bind_support μ (thinningKernel p hp0 hp1) f hf
  obtain ⟨choice, _, hchoice⟩ := FiniteLaw.map_support
    (FiniteLaw.independent (fun v => FiniteLaw.bernoulli (p v) (hp0 v) (hp1 v)))
    (fun choice => thinnedEdge choice e) f hkernel
  refine ⟨e, he, ?_⟩
  rw [← hchoice]
  exact thinnedEdge_subset choice e

theorem thinningLaw_card_le (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    {r : ℕ} (hcard : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (f : Finset V) (hf : 0 < (thinningLaw μ p hp0 hp1).weight f) : f.card ≤ r := by
  obtain ⟨e, he, hsub⟩ := thinningLaw_support μ p hp0 hp1 f hf
  exact (Finset.card_le_card hsub).trans (hcard e he)

theorem thinning_vertexDegree (μ : I → FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) (v : V) :
    vertexDegree (fun i => thinningLaw (μ i) p hp0 hp1) v = p v * vertexDegree μ v := by
  simp only [vertexDegree, thinningLaw_marginal, Finset.mul_sum]

theorem thinning_pairDegree_le (μ : I → FiniteLaw (Finset V))
    (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) (v w : V) :
    pairDegree (fun i => thinningLaw (μ i) p hp0 hp1) v w ≤ pairDegree μ v w :=
  Finset.sum_le_sum (fun i _ => thinningLaw_pair_le (μ i) p hp0 hp1 v w)

noncomputable def equalizedFamily (μ : I → FiniteLaw (Finset V))
    (t : ℝ) (ht : 0 < t) (hd : ∀ v, t ≤ vertexDegree μ v) : I → FiniteLaw (Finset V) :=
  fun i => thinningLaw (μ i) (fun v => t / vertexDegree μ v)
    (fun v => div_nonneg ht.le (vertexDegree_nonneg μ v))
    (fun v => (div_le_iff₀ (ht.trans_le (hd v))).mpr (by simpa using hd v))

theorem equalizedFamily_degree (μ : I → FiniteLaw (Finset V))
    (t : ℝ) (ht : 0 < t) (hd : ∀ v, t ≤ vertexDegree μ v) (v : V) :
    vertexDegree (equalizedFamily μ t ht hd) v = t := by
  unfold equalizedFamily
  rw [thinning_vertexDegree]
  exact div_mul_cancel₀ t (ne_of_gt (ht.trans_le (hd v)))

theorem equalizedFamily_marginal_le (μ : I → FiniteLaw (Finset V))
    (t : ℝ) (ht : 0 < t) (hd : ∀ v, t ≤ vertexDegree μ v) (i : I) (v : V) :
    (equalizedFamily μ t ht hd i).prob (fun e => v ∈ e) ≤ (μ i).prob (fun e => v ∈ e) :=
  thinningLaw_marginal_le (μ i) _ _ _ v

theorem equalizedFamily_pairDegree_le (μ : I → FiniteLaw (Finset V))
    (t : ℝ) (ht : 0 < t) (hd : ∀ v, t ≤ vertexDegree μ v) (v w : V) :
    pairDegree (equalizedFamily μ t ht hd) v w ≤ pairDegree μ v w :=
  thinning_pairDegree_le μ _ _ _ v w

theorem equalizedFamily_support (μ : I → FiniteLaw (Finset V))
    (t : ℝ) (ht : 0 < t) (hd : ∀ v, t ≤ vertexDegree μ v) (i : I)
    (f : Finset V) (hf : 0 < (equalizedFamily μ t ht hd i).weight f) :
    ∃ e, 0 < (μ i).weight e ∧ f ⊆ e :=
  thinningLaw_support (μ i) _ _ _ f hf

end Erdos4.FGKMT
