import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-!
# Finite directed interval chains

A finite linear combination of directed interval densities which vanishes
away from a finite exceptional set has zero endpoint boundary. Consequently
it cancels against every endpoint potential, without any continuity or
monotonicity assumption on that potential. This is the one-dimensional
algebra needed to transport boundary cancellation through field embeddings.
-/

namespace Erdos633

open Filter
open scoped Topology BigOperators

noncomputable def leftStep (a t : ℝ) : ℝ := if a < t then 1 else 0

theorem finite_step_jump {ι : Type*} [Fintype ι]
    (x c : ι → ℝ) (F : Set ℝ) (hF : F.Finite) (K : ℝ)
    (h : ∀ t ∉ F, (∑ i : ι, c i * leftStep (x i) t) = K) (v : ℝ) :
    (∑ i : ι, if x i = v then c i else 0) = 0 := by
  classical
  have hnear : ∀ᶠ t in 𝓝 v, ∀ i : ι, x i ≠ v → (x i < t ↔ x i < v) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = v
    · exact Filter.Eventually.of_forall (fun _ hne => False.elim (hne hi))
    rcases lt_or_gt_of_ne hi with hi | hi
    · filter_upwards [eventually_gt_nhds hi] with t ht
      exact fun _ => ⟨fun _ => hi, fun _ => ht⟩
    · filter_upwards [eventually_lt_nhds hi] with t ht
      exact fun _ => ⟨fun hxt => False.elim ((not_lt_of_ge ht.le) hxt),
        fun hxv => False.elim ((not_lt_of_ge hi.le) hxv)⟩
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨u, hu, huF⟩ := (Set.Ioo_infinite (show v < v + ε by linarith)).exists_notMem_finite hF
  obtain ⟨l, hl, hlF⟩ := (Set.Ioo_infinite (show v - ε < v by linarith)).exists_notMem_finite hF
  have hunear := hnear (show dist u v < ε by
    rw [Real.dist_eq]
    exact abs_lt.mpr (by constructor <;> linarith [hu.1, hu.2]))
  have hlnear := hnear (show dist l v < ε by
    rw [Real.dist_eq]
    exact abs_lt.mpr (by constructor <;> linarith [hl.1, hl.2]))
  have hjump (i : ι) :
      c i * (leftStep (x i) u - leftStep (x i) l) = if x i = v then c i else 0 := by
    by_cases hi : x i = v
    · simp [leftStep, hi, hu.1, not_lt_of_ge hl.2.le]
    · have huu := hunear i hi
      have hll := hlnear i hi
      simp only [leftStep, huu, hll, sub_self, mul_zero, if_neg hi]
  calc
    (∑ i : ι, if x i = v then c i else 0) =
        ∑ i : ι, c i * (leftStep (x i) u - leftStep (x i) l) :=
      Finset.sum_congr rfl (fun i _ => (hjump i).symm)
    _ = (∑ i : ι, c i * leftStep (x i) u) -
        ∑ i : ι, c i * leftStep (x i) l := by simp only [mul_sub, Finset.sum_sub_distrib]
    _ = 0 := by rw [h u huF, h l hlF, sub_self]

theorem finite_endpoint_potential_zero {ι : Type*} [Fintype ι]
    (x c : ι → ℝ)
    (h : ∀ v : ℝ, (∑ i : ι, if x i = v then c i else 0) = 0) (g : ℝ → ℝ) :
    (∑ i : ι, c i * g (x i)) = 0 := by
  classical
  let s := Finset.univ.image x
  have hmem (i : ι) : x i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  calc
    (∑ i : ι, c i * g (x i)) = ∑ v ∈ s, ∑ i : ι, (if x i = v then c i else 0) * g v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp [hmem i]
    _ = ∑ v ∈ s, (∑ i : ι, if x i = v then c i else 0) * g v := by
      simp only [Finset.sum_mul]
    _ = 0 := by simp only [h, zero_mul, Finset.sum_const_zero]

theorem finite_step_balance_potential {ι : Type*} [Fintype ι]
    (x c : ι → ℝ) (F : Set ℝ) (hF : F.Finite) (K : ℝ)
    (h : ∀ t ∉ F, (∑ i : ι, c i * leftStep (x i) t) = K) (g : ℝ → ℝ) :
    (∑ i : ι, c i * g (x i)) = 0 :=
  finite_endpoint_potential_zero x c (finite_step_jump x c F hF K h) g

noncomputable def intervalFlow (a b t : ℝ) : ℝ := leftStep a t - leftStep b t

theorem interval_flow_balance_potential {ι : Type*} [Fintype ι]
    (a b w : ι → ℝ) (F : Set ℝ) (hF : F.Finite)
    (h : ∀ t ∉ F, (∑ i : ι, w i * intervalFlow (a i) (b i) t) = 0)
    (g : ℝ → ℝ) : (∑ i : ι, w i * (g (b i) - g (a i))) = 0 := by
  classical
  let x : ι ⊕ ι → ℝ := Sum.elim a b
  let c : ι ⊕ ι → ℝ := Sum.elim w (fun i => -w i)
  have hs (t : ℝ) (ht : t ∉ F) : (∑ i : ι ⊕ ι, c i * leftStep (x i) t) = 0 := by
    have hh := h t ht
    simp only [intervalFlow, mul_sub, Finset.sum_sub_distrib] at hh
    simpa only [x, c, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hh
  have hp := finite_step_balance_potential x c F hF 0 hs g
  simp only [x, c, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul,
    Finset.sum_neg_distrib] at hp
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

theorem interval_flow_balance_potential_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b w : ι → ℝ) (c d u : κ → ℝ) (F : Set ℝ) (hF : F.Finite)
    (h : ∀ t ∉ F, (∑ i : ι, w i * intervalFlow (a i) (b i) t) =
      ∑ j : κ, u j * intervalFlow (c j) (d j) t) (g : ℝ → ℝ) :
    (∑ i : ι, w i * (g (b i) - g (a i))) =
      ∑ j : κ, u j * (g (d j) - g (c j)) := by
  let x : ι ⊕ κ → ℝ := Sum.elim a c
  let y : ι ⊕ κ → ℝ := Sum.elim b d
  let v : ι ⊕ κ → ℝ := Sum.elim w (fun j => -u j)
  have hs (t : ℝ) (ht : t ∉ F) :
      (∑ i : ι ⊕ κ, v i * intervalFlow (x i) (y i) t) = 0 := by
    simp only [x, y, v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, h t ht, sub_self]
  have hp := interval_flow_balance_potential x y v F hF hs g
  simpa only [x, y, v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] using hp

end Erdos633
