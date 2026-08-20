module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import ErdosProblems.Erdos515.External.Ray.Analytic.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.Cases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Analytic.Holomorphic
import ErdosProblems.Erdos515.External.Ray.Analytic.Series
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds
import ErdosProblems.Erdos515.External.Ray.Misc.Finset

/-!
## Infinite products of analytic functions

We define convergence of infinite products, and show that uniform limits of products of
analytic functions are analytic.
-/

open Complex (exp log)
open Filter (atTop)
open Metric (ball closedBall sphere)
open Set
open scoped Classical Real NNReal ENNReal Topology
noncomputable section

variable {ι : Type}

/-!
### Basics about products of sequences
-/

/-- Powers commute with products -/
public theorem product_pow {f : ℕ → ℂ} {g : ℂ} (p : ℕ) (h : HasProd f g) :
    HasProd (fun n ↦ f n ^ p) (g ^ p) := by
  rw [HasProd]; simp_rw [Finset.prod_pow]
  exact Filter.Tendsto.comp (Continuous.tendsto (continuous_pow p) g) h

/-- Powers commute with products (`tprod` version) -/
public theorem product_pow' {f : ℕ → ℂ} {p : ℕ} (h : ProdExists f) :
    tprod f ^ p = tprod fun n ↦ f n ^ p := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_pow p h

/-- Adding one more term to a product multiplies by it, `Stream'.get` version to keep terms
    type-correct at low transparency -/
theorem product_cons_get {a t : ℂ} {q : Stream' ℂ} (h : HasProd q.get t) :
    HasProd (Stream'.cons a q).get (a * t) := by
  rw [HasProd] at h ⊢
  have ha := Filter.Tendsto.comp (Continuous.tendsto (continuous_const_mul a) t) h
  have s : ((fun z ↦ a * z) ∘ fun N : Finset ℕ ↦ N.prod q.get) =
      (fun N : Finset ℕ ↦ N.prod (Stream'.cons a q).get) ∘ push := by
    apply funext; intro N
    simp only [Function.comp_apply]
    exact push_prod_get
  rw [s] at ha
  exact tendsto_comp_push.mp ha

/-- Adding one more term to a product multiplies by it -/
theorem product_cons {a g : ℂ} {f : ℕ → ℂ} (h : HasProd f g) :
    HasProd (Stream'.cons a f) (a * g) :=
  product_cons_get (q := f) h

/-- Adding one more term to a product multiplies by it (`tprod` version) -/
theorem product_cons' {a : ℂ} {f : ℕ → ℂ} (h : ProdExists f) :
    tprod (Stream'.cons a f) = a * tprod f := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; exact HasProd.tprod_eq (product_cons h)

/-- Dropping a nonzero term divides by it, `Stream'.get` version -/
theorem product_drop_get {q : Stream' ℂ} {t : ℂ} (q0 : q.head ≠ 0) (h : HasProd q.get t) :
    HasProd q.tail.get (t / q.head) := by
  have c := product_cons_get (a := q.head⁻¹) h
  rw [HasProd]
  rw [inv_mul_eq_div, HasProd, SummationFilter.unconditional_filter, ← tendsto_comp_push,
    ← tendsto_comp_push] at c
  have s : ((fun N : Finset ℕ ↦ N.prod (Stream'.cons q.head⁻¹ q).get) ∘ push) ∘ push =
      fun N : Finset ℕ ↦ N.prod q.tail.get := by
    apply funext; intro N
    simp only [Function.comp_apply]
    have e1 := push_prod_get (a := q.head⁻¹) (g := q) (N := push N)
    have e2 := push_prod_get (a := q.head) (g := q.tail) (N := N)
    rw [Stream'.eta q] at e2
    rw [← e1, ← e2, ← mul_assoc, inv_mul_cancel₀ q0, one_mul]
  rw [s] at c; exact c

/-- Dropping a nonzero term divides by it -/
theorem product_drop {f : ℕ → ℂ} {g : ℂ} (f0 : f 0 ≠ 0) (h : HasProd f g) :
    HasProd (fun n ↦ f (n + 1)) (g / f 0) :=
  product_drop_get (q := f) f0 h

/-- Dropping a nonzero term divides by it (`tprod` version) -/
theorem product_drop' {f : ℕ → ℂ} (f0 : f 0 ≠ 0) (h : ProdExists f) :
    (tprod fun n ↦ f (n + 1)) = tprod f / f 0 := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_drop f0 h

/-- Products that start with zero are zero -/
theorem product_head_zero {f : ℕ → ℂ} (f0 : f 0 = 0) : HasProd f 0 := by
  rw [HasProd, SummationFilter.unconditional_filter, Metric.tendsto_atTop]; intro e ep
  use Finset.range 1; intro N N1
  simp at N1; rw [Finset.prod_eq_zero N1 f0]; simpa

/-- Separate out head and tail in a product -/
public theorem product_split {f : ℕ → ℂ} (h : ProdExists f) :
    tprod f = f 0 * tprod fun n ↦ f (n + 1) := by
  by_cases f0 : f 0 = 0; · rw [f0, (product_head_zero f0).tprod_eq]; simp
  rw [product_drop' f0 h]; field_simp

/-!
### Infinite products of analytic functions
-/

/-- Analytic products that converge exponentially converge to analytic functions.
    For now, we require the constant to be `≤ 1/2` so that we can take logs without
    care, and get nonzero results. -/
public theorem fast_products_converge {f : ℕ → ℂ → ℂ} {s : Set ℂ} {a c : ℝ} (o : IsOpen s)
    (c12 : c ≤ 1 / 2) (a0 : a ≥ 0) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z - 1‖ ≤ c * a ^ n) :
    ∃ g : ℂ → ℂ, HasProdOn f g s ∧ AnalyticOnNhd ℂ g s ∧ ∀ z, z ∈ s → g z ≠ 0 := by
  set fl := fun n z ↦ log (f n z)
  have near1 : ∀ n z, z ∈ s → ‖f n z - 1‖ ≤ 1 / 2 := by
    intro n z zs
    calc ‖f n z - 1‖
      _ ≤ c * a ^ n := hf n z zs
      _ ≤ (1 / 2 : ℝ) * (1:ℝ) ^ n := by bound
      _ = 1 / 2 := by norm_num
  have near1' : ∀ n z, z ∈ s → ‖f n z - 1‖ < 1 := fun n z zs ↦
    lt_of_le_of_lt (near1 n z zs) (by linarith)
  have expfl : ∀ n z, z ∈ s → exp (fl n z) = f n z := by
    intro n z zs; refine Complex.exp_log ?_
    exact near_one_avoids_zero (near1' n z zs)
  have hl : ∀ n, AnalyticOnNhd ℂ (fl n) s := fun n ↦
    (h n).clog (fun z m ↦ mem_slitPlane_of_near_one (near1' n z m))
  set c2 := 2 * c
  have hfl : ∀ n z, z ∈ s → ‖fl n z‖ ≤ c2 * a ^ n := by
    intro n z zs
    calc ‖fl n z‖
      _ = ‖log (f n z)‖ := rfl
      _ ≤ 2 * ‖f n z - 1‖ := (log_small (near1 n z zs))
      _ ≤ 2 * (c * a ^ n) := by linarith [hf n z zs]
      _ = 2 * c * a ^ n := by ring
      _ = c2 * a ^ n := rfl
  rcases fast_series_converge o a0 a1 hl hfl with ⟨gl, gla, us⟩
  generalize hg : (fun z ↦ exp (gl z)) = g
  use g; refine ⟨?_, ?_, ?_⟩
  · intro z zs
    specialize us z zs
    have comp :
      Filter.Tendsto (exp ∘ fun N : Finset ℕ ↦ N.sum fun n ↦ fl n z) atTop (𝓝 (exp (gl z))) :=
      Filter.Tendsto.comp (Continuous.tendsto Complex.continuous_exp _) us
    have expsum0 : (exp ∘ fun N : Finset ℕ ↦ N.sum fun n ↦ fl n z) = fun N : Finset ℕ ↦
        N.prod fun n ↦ f n z := by
      apply funext; intro N; simp; rw [Complex.exp_sum]; simp_rw [expfl _ z zs]
    rw [expsum0] at comp; rw [← hg]; assumption
  · rw [← hg]; exact fun z zs ↦ analyticAt_cexp.comp (gla z zs)
  · simp only [Complex.exp_ne_zero, Ne, not_false_iff, imp_true_iff, ← hg]

/-- Same as above, but remove the requirement that `c ≤ 1/2` by peeling off the first few terms -/
theorem fast_products_converge_eventually {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (fa : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (fb : ∀ᶠ n in atTop, ∀ z ∈ s, ‖f n z - 1‖ ≤ c * a ^ n) :
    ∃ g : ℂ → ℂ, HasProdOn f g s ∧ AnalyticOnNhd ℂ g s ∧
      ∀ z, z ∈ s → (∀ n, f n z ≠ 0) → g z ≠ 0 := by
  -- We need `c * a ^ n0 ≤ 1 / 2`, or `a ^ n0 ≤ 1 / (2 * c)`.
  have ta := (tendsto_const_nhds (x := c)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one a0 a1)
  simp only [mul_zero] at ta
  have low := ta.eventually_le_const (u := 1/2) (by norm_num)
  obtain ⟨N, h⟩ := Filter.eventually_atTop.mp (fb.and low)
  have fa' := fun n ↦ fa (N + n)
  have fb' : ∀ n z, z ∈ s → ‖f (N + n) z - 1‖ ≤ c * a ^ N * a ^ n := by
    intro n z zs
    exact le_trans ((h (N + n) (by omega)).1 z zs) (by simp only [pow_add, mul_assoc, le_refl])
  obtain ⟨g, fg, ga, g0⟩ := fast_products_converge o (h N (le_refl _)).2 a0 a1 fa' fb'
  refine ⟨fun z ↦ (∏ n ∈ Finset.range N, f n z) * g z, ?_, ?_, ?_⟩
  · intro z zs
    specialize fg z zs
    simp only at fg ⊢
    clear zs g0 ga fb' fa' h low ta fb fa a1 a0 o c a s
    suffices P : ∀ M, M ≤ N → HasProd (fun n ↦ f (N - M + n) z)
        ((∏ n ∈ Finset.range M, f (N - M + n) z) * g z) by
      simpa only [tsub_self, zero_add] using P N (le_refl _)
    intro M MN
    induction' M with M H
    · simpa using fg
    · specialize H (by omega)
      have e : ∀ k, (N - (M + 1) + (k + 1)) = (N - M + k) := by grind
      have ec : (Stream'.cons (f (N - (M + 1)) z) fun n ↦ f (N - M + n) z) =
          fun n ↦ f (N - (M + 1) + n) z := by
        ext n
        induction' n with n h
        · simp only [Stream'.get, Stream'.cons, add_zero]
        · simp only [Stream'.get, Stream'.cons]
          grind
      simpa only [Finset.prod_range_succ', e, add_zero, mul_comm _ (f _ _), mul_assoc (f _ _),
        ec] using product_cons (a := f (N - (M + 1)) z) H
  · exact (Finset.analyticOnNhd_fun_prod _ fun n _ ↦ fa n).mul ga
  · intro z zs f0
    simp [g0 z zs, Finset.prod_eq_zero_iff, f0]

/-- Same as `fast_products_converge`, but converge to `tprodOn` -/
public theorem fast_products_converge' {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (c12 : c ≤ 1 / 2) (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z - 1‖ ≤ c * a ^ n) :
    ProdExistsOn f s ∧ AnalyticOnNhd ℂ (tprodOn f) s ∧ ∀ z, z ∈ s → tprodOn f z ≠ 0 := by
  rcases fast_products_converge o c12 a0 a1 h hf with ⟨g, gp, ga, g0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact fun z zs ↦ ⟨g z, gp z zs⟩
  · rwa [← analyticOnNhd_congr o fun z zs ↦ (gp.tprodOn_eq z zs).symm]
  · intro z zs; rw [gp.tprodOn_eq z zs]; exact g0 z zs

/-- Same as `fast_products_converge_eventually`, but converge to `tprodOn` -/
public theorem fast_products_converge_eventually' {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ᶠ n in atTop, ∀ z ∈ s, ‖f n z - 1‖ ≤ c * a ^ n) :
    ProdExistsOn f s ∧ AnalyticOnNhd ℂ (tprodOn f) s ∧
      ∀ z, z ∈ s → (∀ n, f n z ≠ 0) → tprodOn f z ≠ 0 := by
  rcases fast_products_converge_eventually o a0 a1 h hf with ⟨g, gp, ga, g0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact fun z zs ↦ ⟨g z, gp z zs⟩
  · rwa [← analyticOnNhd_congr o fun z zs ↦ (gp.tprodOn_eq z zs).symm]
  · intro z zs; rw [gp.tprodOn_eq z zs]; exact g0 z zs

/-!
### Reasonably tight bounds on products
-/

lemma norm_mul_sub_one_le {a b : ℂ} :
    ‖a * b - 1‖ ≤ (1 + ‖a - 1‖) * (1 + ‖b - 1‖) - 1 := by
  -- Ugly semi-GPT 5.1 proof, but meh, it works.
  have h1 : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring_nf
  have h2 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1) + (a - 1)‖ + ‖b - 1‖ := by
    simpa [h1, add_assoc] using (norm_add_le ((a - 1) * (b - 1) + (a - 1)) (b - 1))
  have h3 : ‖(a - 1) * (b - 1) + (a - 1)‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ := by bound
  have h4 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ :=
    le_trans h2 (by simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right h3 ‖b - 1‖)
  have h5 : ‖a * b - 1‖ ≤ ‖a - 1‖ * ‖b - 1‖ + ‖a - 1‖ + ‖b - 1‖ := by
    simpa [norm_mul, add_comm, add_left_comm, add_assoc] using h4
  grind

lemma Finset.norm_prod_sub_one_le {f : ι → ℂ} {s : Finset ι} :
    ‖∏ i ∈ s, f i - 1‖ ≤ ∏ i ∈ s, (1 + ‖f i - 1‖) - 1 := by
  induction' s using Finset.induction with i s is h
  · simp only [prod_empty, sub_self, norm_zero, le_refl]
  · simp only [Finset.prod_insert is]
    exact le_trans norm_mul_sub_one_le (by bound)

/-- Bound a product in terms of bounds on the first few terms, and a geometric tail bound -/
public lemma HasProd.norm_sub_one_le {f : ℕ → ℂ} {g : ℂ} (fg : HasProd f g)
    {n : ℕ} {b : Fin n → ℝ} (lo : ∀ k : Fin n, ‖f k - 1‖ ≤ b k)
    {c a : ℝ} (hi : ∀ k ≥ n, ‖f k - 1‖ ≤ c * a ^ k)
    (b0 : ∀ k, 0 ≤ b k) (c0 : 0 ≤ c) (a0 : 0 ≤ a) (a1 : a < 1) (ca : c * a ^ n / (1 - a) ≤ 1 / 2) :
    ‖g - 1‖ ≤ (∏ k, (1 + b k)) * (1 + 4 * c * a ^ n / (1 - a)) - 1 := by
  have le1 : ‖∏ i ∈ .range n, f i - 1‖ ≤ ∏ i, (1 + b i) - 1 := by
    refine le_trans Finset.norm_prod_sub_one_le ?_
    simp only [Finset.prod_fin_eq_prod_range]
    refine tsub_le_tsub_right (Finset.prod_le_prod (by bound) fun i m ↦ ?_) _
    specialize lo ⟨i, by simpa using m⟩
    grind
  rw [le_sub_iff_add_le, add_comm] at le1
  simp only [HasProd] at fg
  apply le_of_tendsto (Filter.Tendsto.comp continuous_norm.continuousAt (fg.sub_const 1))
  simp only [Function.comp_apply, SummationFilter.unconditional_filter, Filter.eventually_atTop]
  refine ⟨Finset.range n, fun s ns ↦ ?_⟩
  have le2 : ‖∏ i ∈ s \ .range n, f i - 1‖ ≤ 4 * c * a ^ n / (1 - a) := by
    simp only [mul_assoc, div_eq_mul_inv]
    set t := (s \ .range n).image fun k ↦ k - n
    have st : s \ .range n = t.image fun k ↦ k + n := by
      simp only [t, Finset.image_image, Function.comp_def]
      rw [Finset.image_congr (g := id), Finset.image_id]
      intro k m
      simp at m ⊢
      omega
    have inj : InjOn (fun k ↦ k + n) t := by intro  a _ b _; simp
    simp only [st, Finset.prod_image inj, ← mul_assoc c]
    refine dist_prod_one_le_abs_sum ?_ ca
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (partial_geometric_bound t a0 a1) (by bound))
    simp only [Finset.mul_sum, mul_assoc, ← pow_add, add_comm n]
    exact Finset.sum_le_sum fun i m ↦ hi _ (by omega)
  have d : Disjoint (Finset.range n) (s \ Finset.range n) := Finset.disjoint_sdiff
  have e : s = (Finset.range n).disjUnion (s \ Finset.range n) d := by simpa using ns
  rw [e, Finset.prod_disjUnion]
  exact le_trans norm_mul_sub_one_le (by bound)
