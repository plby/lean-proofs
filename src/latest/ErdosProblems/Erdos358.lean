/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 358.
https://www.erdosproblems.com/forum/thread/358

Informal authors:
- Terence Tao

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos358.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/358.lean
-/
import Mathlib

/-!
# Erdős Problem 358

This file formalizes the statement from
`google-deepmind/formal-conjectures/FormalConjectures/ErdosProblems/358.lean`.
The mathematical construction is described in detail in `tex/358.tex`.
-/

open scoped BigOperators Topology

namespace Erdos358

open Filter Finset

/-- Pairs of positive endpoints whose corresponding consecutive `A`-sum is `n`. -/
def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

/-- The number of representations of `n` as a sum of consecutive terms of `A`. -/
noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

/-! ## The finite-cardinality interface -/

/-- A positive consecutive sum of a strictly increasing natural-valued sequence has
both endpoints at most the value of the sum. -/
lemma endpoints_le_of_mem_intervalRepresentations
    {A : ℕ → ℕ} (hA : StrictMono A) {n u v : ℕ} (hn : 0 < n)
    (huv : (u, v) ∈ intervalRepresentations A n) : u ≤ n ∧ v ≤ n := by
  rcases huv with ⟨hu, hv, hsum⟩
  have huv_order : u ≤ v := by
    by_contra h
    have : Icc u v = ∅ := Icc_eq_empty h
    simp [this] at hsum
    omega
  have hv_mem : v ∈ Icc u v := mem_Icc.mpr ⟨huv_order, le_rfl⟩
  have hAv_le : A v ≤ ∑ i ∈ Icc u v, A i := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hv_mem
  have hv_Av : v ≤ A v := hA.id_le v
  have hvn : v ≤ n := by omega
  exact ⟨huv_order.trans hvn, hvn⟩

/-- For a strictly increasing sequence, the representation set of a positive integer is finite. -/
lemma intervalRepresentations_finite
    {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) :
    (intervalRepresentations A n).Finite := by
  refine ((Set.finite_Iic n).prod (Set.finite_Iic n)).subset ?_
  rintro ⟨u, v⟩ huv
  exact endpoints_le_of_mem_intervalRepresentations hA hn huv

/-- Under strict monotonicity, `f` agrees with the ordinary finite-set cardinality. -/
lemma f_eq_ncard
    {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) :
    f A n = (intervalRepresentations A n).ncard := by
  simpa [f] using Nat.card_coe_set_eq (intervalRepresentations A n)

/-- An injectively indexed collection of representations gives a lower bound for `f`. -/
lemma le_f_of_injective_representations
    {A : ℕ → ℕ} (hA : StrictMono A) {n k : ℕ} (hn : 0 < n)
    (g : Fin k → ℕ × ℕ) (hg : Function.Injective g)
    (hrep : ∀ j, g j ∈ intervalRepresentations A n) :
    k ≤ f A n := by
  let e : Fin k → intervalRepresentations A n := fun j ↦ ⟨g j, hrep j⟩
  have he : Function.Injective e := fun i j hij ↦ hg (Subtype.ext_iff.mp hij)
  let : Fintype (intervalRepresentations A n) :=
    (intervalRepresentations_finite hA hn).fintype
  rw [f]
  simpa using Nat.card_le_card_of_injective e he

/-- A convenient criterion for proving that the representation count tends to infinity. -/
lemma tendsto_f_atTop_of_eventually_injective_representations
    {A : ℕ → ℕ} (hA : StrictMono A)
    (hrep : ∀ k : ℕ, ∀ᶠ n in atTop, ∃ g : Fin k → ℕ × ℕ,
      Function.Injective g ∧ ∀ j, g j ∈ intervalRepresentations A n) :
    Tendsto (f A) atTop atTop := by
  rw [tendsto_atTop]
  intro k
  filter_upwards [hrep k, eventually_gt_atTop (0 : ℕ)] with n hn hpos
  rcases hn with ⟨g, hg, hmem⟩
  exact le_f_of_injective_representations hA hpos g hg hmem

/-! ## Passing from an infinite set to its increasing enumeration -/

/-- The elements of `S` lying in the closed integer interval from `x` to `y`. -/
noncomputable def setInterval (S : Set ℕ) (x y : ℕ) : Finset ℕ := by
  classical
  exact (Icc x y).filter (· ∈ S)

@[simp] lemma mem_setInterval {S : Set ℕ} {x y z : ℕ} :
    z ∈ setInterval S x y ↔ x ≤ z ∧ z ≤ y ∧ z ∈ S := by
  classical
  simp [setInterval, and_assoc]

/-- A set-level version of a consecutive representation.  The lower endpoint is required to
exceed `1`; adjoining `1` will therefore make the resulting enumeration indices positive. -/
def setIntervalRepresentations (S : Set ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(x, y) | 1 < x ∧ x ∈ S ∧ y ∈ S ∧ x ≤ y ∧ n = ∑ z ∈ setInterval S x y, z}

lemma setIntervalRepresentations_finite (S : Set ℕ) (n : ℕ) :
    (setIntervalRepresentations S n).Finite := by
  refine ((Set.finite_Iic n).prod (Set.finite_Iic n)).subset ?_
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨_, hxS, hyS, hxy, hsum⟩
  have hy_mem : y ∈ setInterval S x y := by
    rw [mem_setInterval]
    exact ⟨hxy, le_rfl, hyS⟩
  have hyn : y ≤ n := by
    have : y ≤ ∑ z ∈ setInterval S x y, z :=
      Finset.single_le_sum (fun z _ ↦ Nat.zero_le z) hy_mem
    omega
  exact ⟨hxy.trans hyn, hyn⟩

/-- The increasing enumeration of an infinite set of natural numbers. -/
noncomputable def enumerate (S : Set ℕ) : ℕ → ℕ := Nat.nth (· ∈ S)

/-- The number of elements of `S` strictly below `x`; for `x ∈ S` this is the index of `x`
in the increasing enumeration. -/
noncomputable def setIndex (S : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact Nat.count (· ∈ S) x

lemma enumerate_strictMono {S : Set ℕ} (hS : S.Infinite) : StrictMono (enumerate S) :=
  Nat.nth_strictMono hS

lemma range_enumerate {S : Set ℕ} (hS : S.Infinite) : Set.range (enumerate S) = S :=
  Nat.range_nth_of_infinite hS

lemma enumerate_count {S : Set ℕ} {x : ℕ} (hx : x ∈ S) :
    enumerate S (setIndex S x) = x := by
  classical
  exact Nat.nth_count hx

lemma setIndex_injOn (S : Set ℕ) : S.InjOn (setIndex S) := by
  classical
  intro x hx y hy hxy
  exact Nat.count_injective hx hy hxy

/-- Mapping an index interval through the increasing enumeration gives exactly the elements of
the set between the two endpoint values. -/
lemma map_Icc_enumerate
    {S : Set ℕ} (hS : S.Infinite) {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) :
    (Icc (setIndex S x) (setIndex S y)).map
        ⟨enumerate S, (enumerate_strictMono hS).injective⟩ = setInterval S x y := by
  classical
  have hux : enumerate S (setIndex S x) = x := enumerate_count hx
  have hvy : enumerate S (setIndex S y) = y := enumerate_count hy
  ext z
  constructor
  · intro hz
    simp only [Finset.mem_map, mem_Icc] at hz
    rcases hz with ⟨i, ⟨hui, hiv⟩, rfl⟩
    rw [mem_setInterval]
    exact ⟨hux ▸ (enumerate_strictMono hS).monotone hui,
      hvy ▸ (enumerate_strictMono hS).monotone hiv,
      Nat.nth_mem_of_infinite hS i⟩
  · rw [mem_setInterval]
    rintro ⟨hxz, hzy, hzS⟩
    obtain ⟨i, hi⟩ := Nat.subset_range_nth hzS
    change enumerate S i = z at hi
    refine Finset.mem_map.mpr ⟨i, ?_, hi⟩
    rw [mem_Icc]
    constructor
    · apply (enumerate_strictMono hS).le_iff_le.mp
      simpa [hux, hi] using hxz
    · apply (enumerate_strictMono hS).le_iff_le.mp
      simpa [hi, hvy] using hzy

/-- The sum over a set interval is the sum over the corresponding interval of enumeration
indices. -/
lemma sum_Icc_enumerate
    {S : Set ℕ} (hS : S.Infinite) {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) :
    (∑ i ∈ Icc (setIndex S x) (setIndex S y), enumerate S i) =
      ∑ z ∈ setInterval S x y, z := by
  classical
  rw [← map_Icc_enumerate hS hx hy, Finset.sum_map]
  rfl

/-- Every set-level representation beyond the adjoined element `1` becomes a representation
with positive indices in the formal-conjecture sequence. -/
lemma countEndpoints_mem_intervalRepresentations
    {S : Set ℕ} (hS : S.Infinite) (h1 : 1 ∈ S) {n x y : ℕ}
    (hxy : (x, y) ∈ setIntervalRepresentations S n) :
    (setIndex S x, setIndex S y) ∈
      intervalRepresentations (enumerate S) n := by
  classical
  rcases hxy with ⟨hx1, hxS, hyS, hxy, hsum⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr ⟨1, hx1, h1⟩)
  · exact Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr ⟨1, hx1.trans_le hxy, h1⟩)
  · rw [sum_Icc_enumerate hS hxS hyS]
    exact hsum

/-- Set-level injective representation families transfer to the formal-conjecture count. -/
lemma tendsto_f_enumerate_of_eventually_set_representations
    {S : Set ℕ} (hS : S.Infinite) (h1 : 1 ∈ S)
    (hrep : ∀ k : ℕ, ∀ᶠ n in atTop, ∃ g : Fin k → ℕ × ℕ,
      Function.Injective g ∧ ∀ j, g j ∈ setIntervalRepresentations S n) :
    Tendsto (f (enumerate S)) atTop atTop := by
  apply tendsto_f_atTop_of_eventually_injective_representations (enumerate_strictMono hS)
  intro k
  filter_upwards [hrep k] with n hn
  rcases hn with ⟨g, hg, hmem⟩
  let g' : Fin k → ℕ × ℕ := fun j ↦
    (setIndex S (g j).1, setIndex S (g j).2)
  refine ⟨g', ?_, ?_⟩
  · intro i j hij
    apply hg
    apply Prod.ext
    · apply setIndex_injOn S (hmem i).2.1 (hmem j).2.1
      exact congrArg Prod.fst hij
    · apply setIndex_injOn S (hmem i).2.2.1 (hmem j).2.2.1
      exact congrArg Prod.snd hij
  · intro j
    exact countEndpoints_mem_intervalRepresentations hS h1 (hmem j)

/-- Cardinality-form criterion for the set construction. -/
lemma tendsto_f_enumerate_of_set_ncard
    {S : Set ℕ} (hS : S.Infinite) (h1 : 1 ∈ S)
    (hrep : ∀ k : ℕ, ∀ᶠ n in atTop, k ≤ (setIntervalRepresentations S n).ncard) :
    Tendsto (f (enumerate S)) atTop atTop := by
  apply tendsto_f_enumerate_of_eventually_set_representations hS h1
  intro k
  filter_upwards [hrep k] with n hn
  let : Fintype (setIntervalRepresentations S n) :=
    (setIntervalRepresentations_finite S n).fintype
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (setIntervalRepresentations S n) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
    exact hn
  obtain ⟨e : Fin k ↪ setIntervalRepresentations S n⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun j ↦ (e j).1, fun i j hij ↦ e.injective (Subtype.ext hij), fun j ↦ (e j).2⟩

/-! ## Prescribed sums in short intervals -/

namespace ShortInterval

/-- The `i`th point in the evenly distributed `q`-element set with excess `d` over
`L + (L+1) + ⋯ + (L+q-1)`. -/
def spreadValue (L q d i : ℕ) : ℕ :=
  L + i + d / q + if q - d % q ≤ i then 1 else 0

lemma spreadValue_strictOn (L q d : ℕ) :
    StrictMonoOn (spreadValue L q d) (Set.Iio q) := by
  intro i hi j hj hij
  simp only [spreadValue]
  split_ifs <;> omega

/-- The embedding whose image is the prescribed short-interval subset. -/
def spreadEmbedding (L q d : ℕ) : Fin q ↪ ℕ where
  toFun i := spreadValue L q d i
  inj' := by
    intro i j hij
    apply Fin.ext
    exact (spreadValue_strictOn L q d).injOn i.isLt j.isLt hij

/-- A `q`-element subset with controlled diameter and prescribed sum. -/
def spreadSet (L q d : ℕ) : Finset ℕ :=
  Finset.univ.map (spreadEmbedding L q d)

lemma card_spreadSet (L q d : ℕ) : (spreadSet L q d).card = q := by
  simp [spreadSet]

private lemma card_upper_tail (q r : ℕ) (hr : r ≤ q) :
    ((Finset.range q).filter (fun i ↦ q - r ≤ i)).card = r := by
  rw [show (Finset.range q).filter (fun i ↦ q - r ≤ i) = Finset.Ico (q - r) q by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega]
  simp only [Nat.card_Ico]
  omega

lemma sum_spreadValue (L q d : ℕ) (hq : 0 < q) :
    ∑ i : Fin q, spreadValue L q d i =
      q * L + q * (q - 1) / 2 + d := by
  rw [Fin.sum_univ_eq_sum_range]
  have hbase : ∑ i ∈ Finset.range q, (L + i) = q * L + q * (q - 1) / 2 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_range_id, Nat.mul_comm]
  have hbonus :
      ∑ i ∈ Finset.range q, (if q - d % q ≤ i then 1 else 0) = d % q := by
    rw [Finset.sum_boole]
    exact_mod_cast card_upper_tail q (d % q) (Nat.le_of_lt (Nat.mod_lt d hq))
  calc
    ∑ i ∈ Finset.range q, spreadValue L q d i =
        (∑ i ∈ Finset.range q, (L + i)) +
        (∑ _i ∈ Finset.range q, d / q) +
        ∑ i ∈ Finset.range q, (if q - d % q ≤ i then 1 else 0) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          simp [spreadValue, add_assoc]
    _ = q * L + q * (q - 1) / 2 + q * (d / q) + d % q := by
          rw [hbase, hbonus]
          simp [Nat.mul_comm]
    _ = q * L + q * (q - 1) / 2 + d := by
          have hmod := Nat.mod_add_div d q
          omega

lemma sum_spreadSet (L q d : ℕ) (hq : 0 < q) :
    ∑ x ∈ spreadSet L q d, x = q * L + q * (q - 1) / 2 + d := by
  rw [spreadSet, Finset.sum_map]
  exact sum_spreadValue L q d hq

lemma spreadSet_subset_Icc (L q d : ℕ) (hd : d ≤ 2 * q ^ 2) :
    ↑(spreadSet L q d) ⊆ Set.Icc L (L + 3 * q) := by
  intro x hx
  rw [Finset.mem_coe, spreadSet, Finset.mem_map] at hx
  rcases hx with ⟨i, -, rfl⟩
  constructor
  · change L ≤ spreadValue L q d i
    unfold spreadValue
    simpa [add_assoc] using
      Nat.le_add_right L (i.val + d / q + if q - d % q ≤ i.val then 1 else 0)
  · have hdiv : d / q ≤ 2 * q := by
      apply Nat.div_le_of_le_mul
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hd
    have hi : i.val < q := i.isLt
    have hi_div : i.val + d / q + 1 ≤ 3 * q := by omega
    change spreadValue L q d i ≤ L + 3 * q
    simp only [spreadValue]
    split_ifs <;> omega

/-- Every target lying at most `2q²` above the minimal `q`-term arithmetic-progression
sum is realized by `q` distinct integers in an interval of length `3q`. -/
theorem exists_card_eq_sum_of_mem_short_interval
    (L q n : ℕ) (hq : 0 < q)
    (hlower : q * L + q * (q - 1) / 2 ≤ n)
    (hupper : n ≤ q * L + q * (q - 1) / 2 + 2 * q ^ 2) :
    ∃ T : Finset ℕ, T.card = q ∧ ↑T ⊆ Set.Icc L (L + 3 * q) ∧
      ∑ x ∈ T, x = n := by
  let base := q * L + q * (q - 1) / 2
  let d := n - base
  have hd : d ≤ 2 * q ^ 2 := by
    dsimp [d, base]
    omega
  refine ⟨spreadSet L q d, card_spreadSet L q d, spreadSet_subset_Icc L q d hd, ?_⟩
  rw [sum_spreadSet L q d hq]
  dsimp [d, base] at *
  omega

end ShortInterval

/-! ## The weighted geometric law used in a red interval -/

namespace LocalLimit

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The fair parameter, viewed as an element of the unit interval. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The number of failures before a success in fair independent trials.  A gap between
successive selected integers is therefore `g + 1` for `g` with this law. -/
noncomputable def fairGeometric : Measure ℕ := geometricMeasure half

instance : IsProbabilityMeasure fairGeometric := by
  unfold fairGeometric
  infer_instance

lemma half_ne_zero : half ≠ 0 := by
  intro h
  have h' := congrArg ((↑·) : unitInterval → ℝ) h
  norm_num [half] at h'

lemma fairGeometric_real_singleton (n : ℕ) :
    fairGeometric.real {n} = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [fairGeometric, geometricMeasure_real_singleton half_ne_zero]
  norm_num [half, pow_succ]

/-- The weighted sum of positive fair-geometric gaps. -/
def weightedGapSum (q : ℕ) (g : Fin q → ℕ) : ℕ :=
  ∑ i, (i.val + 1) * (g i + 1)

/-- A finite independent vector of fair geometric random variables. -/
noncomputable def fairGeometricVector (q : ℕ) : Measure (Fin q → ℕ) :=
  Measure.pi (fun _ ↦ fairGeometric)

instance (q : ℕ) : IsProbabilityMeasure (fairGeometricVector q) := by
  dsimp [fairGeometricVector]
  infer_instance

private lemma singleton_pi (q : ℕ) (g : Fin q → ℕ) :
    ({g} : Set (Fin q → ℕ)) = Set.pi Set.univ (fun i ↦ {g i}) := by
  ext x
  simp [funext_iff]

lemma fairGeometricVector_singleton (q : ℕ) (g : Fin q → ℕ) :
    fairGeometricVector q {g} = ∏ i, fairGeometric {g i} := by
  rw [singleton_pi]
  exact Measure.pi_pi (fun _ ↦ fairGeometric) (fun i ↦ {g i})

/-! ### A uniform circle-rotation estimate

The February 2026 proof draft used a false pointwise assertion in its
middle-frequency estimate.  The following paired-frequency argument is the
aggregate replacement needed by the characteristic-function proof. -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def circleDist (x : ℝ) : ℝ := ‖(x : AddCircle (1 : ℝ))‖

lemma circleDist_eq_abs {x : ℝ} (hx : |x| ≤ 1 / 2) : circleDist x = |x| := by
  exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using hx)

lemma circleDist_nonneg (x : ℝ) : 0 ≤ circleDist x := norm_nonneg _

lemma circleDist_sub_le (x y : ℝ) :
    circleDist (x - y) ≤ circleDist x + circleDist y := by
  change ‖((x - y : ℝ) : AddCircle (1 : ℝ))‖ ≤ _
  rw [QuotientAddGroup.mk_sub]
  exact norm_sub_le _ _

/-- Two circle points separated by between `1/4` and `1/2` have a fixed
amount of squared distance from the origin between them. -/
lemma pair_circle_sq (x δ : ℝ) (hδ0 : 1 / 4 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    1 / 32 ≤ circleDist x ^ 2 + circleDist (x + δ) ^ 2 := by
  have hδabs : |δ| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by linarith)]
    exact hδ1
  have hd : circleDist ((x + δ) - x) = δ := by
    rw [show x + δ - x = δ by ring, circleDist_eq_abs hδabs,
      abs_of_nonneg (by linarith)]
  have htri : δ ≤ circleDist x + circleDist (x + δ) := by
    calc
      δ = circleDist ((x + δ) - x) := hd.symm
      _ ≤ circleDist (x + δ) + circleDist x := circleDist_sub_le (x + δ) x
      _ = circleDist x + circleDist (x + δ) := add_comm _ _
  have hx := circleDist_nonneg x
  have hy := circleDist_nonneg (x + δ)
  nlinarith [sq_nonneg (circleDist x - circleDist (x + δ))]

/-- The circle energy of the first `q - 1` multiples of `t`. -/
noncomputable def rotationEnergy (q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 q, circleDist ((r : ℝ) * t) ^ 2

private lemma rotationEnergy_large_aux (q h : ℕ) (t : ℝ)
    (hq : 40 ≤ q) (hh : 20 * h ≤ q)
    (hδ0 : 1 / 4 ≤ (h : ℝ) * t) (hδ1 : (h : ℝ) * t ≤ 1 / 2) :
    (q : ℝ) / 4096 ≤ rotationEnergy q t := by
  let e : ℕ → ℝ := fun r ↦ circleDist ((r : ℝ) * t) ^ 2
  let s := Finset.range (q / 2)
  have hp (r : ℕ) (hr : r ∈ s) :
      1 / 32 ≤ e (r + 1) + e (r + 1 + h) := by
    have hp' := pair_circle_sq ((r + 1 : ℕ) * t) ((h : ℝ) * t) hδ0 hδ1
    dsimp [e]
    rw [show ((r + 1 + h : ℕ) : ℝ) * t =
        ((r + 1 : ℕ) : ℝ) * t + (h : ℝ) * t by
      push_cast
      ring]
    exact hp'
  have hsum_pair :
      ((q / 2 : ℕ) : ℝ) * (1 / 32) ≤
        (∑ r ∈ s, e (r + 1)) + ∑ r ∈ s, e (r + 1 + h) := by
    rw [← Finset.sum_add_distrib]
    calc
      ((q / 2 : ℕ) : ℝ) * (1 / 32) = ∑ _r ∈ s, (1 / 32 : ℝ) := by simp [s]
      _ ≤ ∑ r ∈ s, (e (r + 1) + e (r + 1 + h)) :=
        Finset.sum_le_sum fun r hr ↦ hp r hr
  have hfirst : (∑ r ∈ s, e (r + 1)) ≤ rotationEnergy q t := by
    have hinj : Set.InjOn (fun r : ℕ ↦ r + 1) (s : Set ℕ) :=
      Set.injOn_of_injective (by intro a b hab; dsimp at hab; omega)
    rw [← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_image] at hx
      rcases hx with ⟨r, hr, rfl⟩
      simp only [Finset.mem_Ico]
      have hr' : r < q / 2 := Finset.mem_range.mp hr
      omega
    · intro i hi hni
      exact sq_nonneg _
  have hsecond : (∑ r ∈ s, e (r + 1 + h)) ≤ rotationEnergy q t := by
    have hinj : Set.InjOn (fun r : ℕ ↦ r + 1 + h) (s : Set ℕ) :=
      Set.injOn_of_injective (by intro a b hab; dsimp at hab; omega)
    rw [← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_image] at hx
      rcases hx with ⟨r, hr, rfl⟩
      simp only [Finset.mem_Ico]
      have hr' : r < q / 2 := Finset.mem_range.mp hr
      omega
    · intro i hi hni
      exact sq_nonneg _
  have hqhalf : (q : ℝ) / 4 ≤ ((q / 2 : ℕ) : ℝ) := by
    have hdiv : q ≤ 2 * (q / 2) + 1 := by omega
    have hdivR : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hdiv
    have hqR : (40 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hdouble : ((q / 2 : ℕ) : ℝ) * (1 / 32) ≤ 2 * rotationEnergy q t := by
    calc
      _ ≤ (∑ r ∈ s, e (r + 1)) + ∑ r ∈ s, e (r + 1 + h) := hsum_pair
      _ ≤ rotationEnergy q t + rotationEnergy q t := add_le_add hfirst hsecond
      _ = 2 * rotationEnergy q t := by ring
  norm_num at hdouble hqhalf ⊢
  nlinarith

/-- High frequencies have circle energy linear in `q`. -/
lemma rotationEnergy_large (q : ℕ) (t : ℝ) (hq : 40 ≤ q)
    (ht0 : 0 < t) (htq : 10 / (q : ℝ) ≤ t) (ht1 : t ≤ 1 / 2) :
    (q : ℝ) / 4096 ≤ rotationEnergy q t := by
  let h : ℕ := ⌊1 / (2 * t)⌋₊
  have hq0R : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have htprod : 0 < 2 * t := by positivity
  have hx0 : 0 ≤ (1 / (2 * t) : ℝ) := by positivity
  have hx1 : (1 : ℝ) ≤ 1 / (2 * t) := by
    rw [le_div_iff₀ htprod]
    linarith
  have hhpos : 0 < h := (Nat.floor_pos (a := (1 / (2 * t) : ℝ))).2 hx1
  have hhcast : (h : ℝ) ≤ 1 / (2 * t) := Nat.floor_le hx0
  have hh : 20 * h ≤ q := by
    have hhR : (20 : ℝ) * (h : ℝ) ≤ q := by
      have htq' : (10 : ℝ) ≤ t * q := (div_le_iff₀ hq0R).mp htq
      have hmul : (20 : ℝ) * h * t ≤ 10 := by
        calc
          (20 : ℝ) * h * t ≤ 20 * (1 / (2 * t)) * t := by gcongr
          _ = 10 := by field_simp; norm_num
      nlinarith
    exact_mod_cast hhR
  have hδ1 : (h : ℝ) * t ≤ 1 / 2 := by
    calc
      (h : ℝ) * t ≤ (1 / (2 * t)) * t := by gcongr
      _ = 1 / 2 := by field_simp
  have hδ0 : 1 / 4 ≤ (h : ℝ) * t := by
    by_cases ht : t ≤ 1 / 4
    · have hfloor := Nat.lt_floor_add_one (1 / (2 * t) : ℝ)
      change 1 / (2 * t) < (h : ℝ) + 1 at hfloor
      have : 1 / 2 - t < (h : ℝ) * t := by
        apply (div_lt_iff₀ htprod).mp at hfloor
        nlinarith
      linarith
    · have hx2 : (1 / (2 * t) : ℝ) < 2 := by
        rw [div_lt_iff₀ htprod]
        nlinarith
      have hh2 : h < 2 := (Nat.floor_lt hx0).2 hx2
      have hh1 : h = 1 := by omega
      rw [hh1]
      norm_num
      linarith
  exact rotationEnergy_large_aux q h t hq hh hδ0 hδ1

/-- Below frequency `10/q`, a fixed interval of small multiples has not yet
wrapped around the circle, giving the cubic-scale energy bound. -/
lemma rotationEnergy_small (q : ℕ) (t : ℝ) (hq : 800 ≤ q)
    (ht0 : 0 ≤ t) (htq : t ≤ 10 / (q : ℝ)) :
    (q : ℝ) ^ 3 * t ^ 2 / 64000000 ≤ rotationEnergy q t := by
  let s := Finset.Ico (q / 80) (q / 40)
  let e : ℕ → ℝ := fun r ↦ circleDist ((r : ℝ) * t) ^ 2
  have hq0 : 0 < q := by omega
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hs_card_nat : q / 200 ≤ s.card := by
    simp only [s, Nat.card_Ico]
    omega
  have hs_card : (q : ℝ) / 400 ≤ (s.card : ℝ) := by
    have hscale : q ≤ 400 * s.card := by omega
    have hscaleR : (q : ℝ) ≤ 400 * (s.card : ℝ) := by exact_mod_cast hscale
    linarith
  have hs_mem_energy : s ⊆ Finset.Ico 1 q := by
    intro r hr
    simp only [s, Finset.mem_Ico] at hr
    simp only [Finset.mem_Ico]
    have hlow : 1 ≤ q / 80 := by omega
    omega
  have hpoint (r : ℕ) (hr : r ∈ s) :
      ((q : ℝ) * t / 400) ^ 2 ≤ e r := by
    have hrnat : q / 80 ≤ r ∧ r < q / 40 := by simpa [s] using hr
    have hr_lower_nat : q / 200 ≤ r := by omega
    have hr_lower : (q : ℝ) / 400 ≤ (r : ℝ) := by
      have hscale : q ≤ 400 * r := by omega
      have hscaleR : (q : ℝ) ≤ 400 * (r : ℝ) := by exact_mod_cast hscale
      linarith
    have hr_upper : (r : ℝ) ≤ (q : ℝ) / 40 := by
      have hrq : 40 * r ≤ q := by omega
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 40)).2
      have hcast : (40 : ℝ) * r ≤ q := by exact_mod_cast hrq
      simpa [mul_comm] using hcast
    have hrt0 : 0 ≤ (r : ℝ) * t := mul_nonneg (by positivity) ht0
    have hrt1 : (r : ℝ) * t ≤ 1 / 2 := by
      have htq' : t * q ≤ 10 := (le_div_iff₀ hq0R).mp htq
      nlinarith
    have hdist : circleDist ((r : ℝ) * t) = (r : ℝ) * t := by
      rw [circleDist_eq_abs]
      · rw [abs_of_nonneg hrt0]
      · rw [abs_of_nonneg hrt0]
        exact hrt1
    dsimp [e]
    rw [hdist]
    have hb : 0 ≤ (q : ℝ) * t / 400 := by positivity
    have hle : (q : ℝ) * t / 400 ≤ (r : ℝ) * t := by nlinarith
    nlinarith [sq_nonneg ((r : ℝ) * t - (q : ℝ) * t / 400)]
  have hsum_lower :
      (s.card : ℝ) * (((q : ℝ) * t / 400) ^ 2) ≤ ∑ r ∈ s, e r := by
    calc
      _ = ∑ _r ∈ s, (((q : ℝ) * t / 400) ^ 2) := by simp
      _ ≤ ∑ r ∈ s, e r := Finset.sum_le_sum fun r hr ↦ hpoint r hr
  have hsum_upper : (∑ r ∈ s, e r) ≤ rotationEnergy q t := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hs_mem_energy
      (fun i hi hni ↦ sq_nonneg _)
  have hbase_nonneg : 0 ≤ ((q : ℝ) * t / 400) ^ 2 := sq_nonneg _
  have hcard_prod :
      ((q : ℝ) / 400) * (((q : ℝ) * t / 400) ^ 2) ≤
        (s.card : ℝ) * (((q : ℝ) * t / 400) ^ 2) :=
    mul_le_mul_of_nonneg_right hs_card hbase_nonneg
  calc
    (q : ℝ) ^ 3 * t ^ 2 / 64000000 =
        ((q : ℝ) / 400) * (((q : ℝ) * t / 400) ^ 2) := by ring
    _ ≤ (s.card : ℝ) * (((q : ℝ) * t / 400) ^ 2) := hcard_prod
    _ ≤ ∑ r ∈ s, e r := hsum_lower
    _ ≤ rotationEnergy q t := hsum_upper

/-! ### The geometric characteristic function -/

/-- Characteristic function of a fair geometric variable centered at its mean. -/
noncomputable def centeredGeometricCF (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * x) * Complex.I) /
    (2 - Complex.exp ((2 * Real.pi * x) * Complex.I))

private lemma norm_sq_two_sub_exp (x : ℝ) :
    ‖(2 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ ^ 2 =
      5 - 4 * Real.cos x := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- Exact squared modulus of the centered geometric characteristic function. -/
lemma centeredGeometricCF_norm_sq (x : ℝ) :
    ‖centeredGeometricCF x‖ ^ 2 =
      1 / (5 - 4 * Real.cos (2 * Real.pi * x)) := by
  rw [centeredGeometricCF, norm_div, div_pow]
  simp only [Complex.norm_exp]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, Complex.I_re, Complex.I_im, mul_one,
    sub_self, neg_zero, Real.exp_zero, one_pow, one_div, inv_inj]
  have hden :
      ‖(2 : ℂ) - Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)‖ ^ 2 =
        5 - 4 * Real.cos (2 * Real.pi * x) :=
    norm_sq_two_sub_exp (2 * Real.pi * x)
  convert hden using 1 <;> push_cast <;> ring

lemma circleDist_eq_round (x : ℝ) :
    circleDist x = |x - (round x : ℝ)| := by
  exact UnitAddCircle.norm_eq

/-- Cosine depends only on circle distance, since it is even and one-periodic
after the `2π` scaling. -/
lemma cos_two_pi_eq_cos_circleDist (x : ℝ) :
    Real.cos (2 * Real.pi * x) =
      Real.cos (2 * Real.pi * circleDist x) := by
  let y : ℝ := x - (round x : ℝ)
  have hper : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * y) := by
    rw [show 2 * Real.pi * x = 2 * Real.pi * y + (round x) * (2 * Real.pi) by
      dsimp [y]
      ring]
    exact Real.cos_add_int_mul_two_pi _ _
  rw [hper, circleDist_eq_round]
  dsimp [y]
  rw [show 2 * Real.pi * |x - (round x : ℝ)| =
      |2 * Real.pi * (x - (round x : ℝ))| by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]]
  exact (Real.cos_abs _).symm

lemma circleDist_le_half (x : ℝ) : circleDist x ≤ 1 / 2 := by
  simpa [circleDist] using
    AddCircle.norm_le_half_period (1 : ℝ) (by norm_num)
      (x := (x : AddCircle (1 : ℝ)))

/-- The global Gaussian-type modulus bound used outside the major arc. -/
lemma centeredGeometricCF_norm_sq_le_exp (x : ℝ) :
    ‖centeredGeometricCF x‖ ^ 2 ≤
      Real.exp (-(circleDist x ^ 2)) := by
  have hd0 : 0 ≤ circleDist x := norm_nonneg _
  have hd1 : circleDist x ≤ 1 / 2 := circleDist_le_half x
  have hzabs : |2 * Real.pi * circleDist x| ≤ Real.pi := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) hd0)]
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hzabs
  have hden :
      1 + 32 * circleDist x ^ 2 ≤
        5 - 4 * Real.cos (2 * Real.pi * x) := by
    rw [cos_two_pi_eq_cos_circleDist]
    have hp : 0 < Real.pi := Real.pi_pos
    field_simp [hp.ne'] at hcos
    nlinarith
  have hdsq : circleDist x ^ 2 ≤ 1 / 4 := by nlinarith
  have hexp : Real.exp (circleDist x ^ 2) ≤ 1 + 32 * circleDist x ^ 2 := by
    have he := Real.exp_le_two_add_div_two_sub (sq_nonneg (circleDist x)) (by nlinarith)
    have hpos : 0 < 2 - circleDist x ^ 2 := by nlinarith
    have he' := (le_div_iff₀ hpos).mp he
    nlinarith [sq_nonneg (circleDist x)]
  rw [centeredGeometricCF_norm_sq, Real.exp_neg]
  have hdenpos : 0 < 5 - 4 * Real.cos (2 * Real.pi * x) :=
    lt_of_lt_of_le (by positivity : 0 < 1 + 32 * circleDist x ^ 2) hden
  have hexppos := Real.exp_pos (circleDist x ^ 2)
  have hinv : (5 - 4 * Real.cos (2 * Real.pi * x))⁻¹ ≤
      (Real.exp (circleDist x ^ 2))⁻¹ := by
    exact (inv_le_inv₀ hdenpos hexppos).2 (hexp.trans hden)
  simpa only [one_div] using hinv

/-- Product form of the global characteristic-function estimate. -/
lemma centeredGeometricCF_prod_norm_sq_le (q : ℕ) (t : ℝ) :
    ‖∏ r ∈ Finset.Ico 1 q, centeredGeometricCF ((r : ℝ) * t)‖ ^ 2 ≤
      Real.exp (-(rotationEnergy q t)) := by
  rw [norm_prod, ← Finset.prod_pow]
  calc
    ∏ r ∈ Finset.Ico 1 q, ‖centeredGeometricCF ((r : ℝ) * t)‖ ^ 2 ≤
        ∏ r ∈ Finset.Ico 1 q,
          Real.exp (-(circleDist ((r : ℝ) * t) ^ 2)) := by
      exact Finset.prod_le_prod (fun r hr ↦ sq_nonneg _)
        (fun r hr ↦ centeredGeometricCF_norm_sq_le_exp _)
    _ = Real.exp
        (∑ r ∈ Finset.Ico 1 q, -(circleDist ((r : ℝ) * t) ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(rotationEnergy q t)) := by
      congr 1
      simp [rotationEnergy]

lemma centeredGeometricCF_prod_norm_le (q : ℕ) (t : ℝ) :
    ‖∏ r ∈ Finset.Ico 1 q, centeredGeometricCF ((r : ℝ) * t)‖ ≤
      Real.exp (-(rotationEnergy q t) / 2) := by
  have hs := centeredGeometricCF_prod_norm_sq_le q t
  have hr : Real.exp (-(rotationEnergy q t) / 2) ^ 2 =
      Real.exp (-(rotationEnergy q t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hr] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp hs

/-- A useful algebraic form: if `z = exp(2πix) - 1`, the characteristic
function is exactly `(1-z²)⁻¹`. -/
lemma centeredGeometricCF_eq_inv_one_sub_sq (x : ℝ) :
    centeredGeometricCF x =
      (1 - (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) - 1) ^ 2)⁻¹ := by
  let u : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (-(2 * Real.pi * x : ℝ) * Complex.I) = u⁻¹ := by
    rw [show (-(2 * Real.pi * x : ℝ) : ℂ) * Complex.I =
        -((2 * Real.pi * x : ℝ) * Complex.I) by push_cast; ring,
      Complex.exp_neg]
  unfold centeredGeometricCF
  have hc : (2 : ℂ) * Real.pi * x = ((2 * Real.pi * x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, hneg]
  change u⁻¹ / (2 - u) = _
  rw [div_eq_mul_inv, ← mul_inv_rev]
  congr 1
  ring

lemma norm_exp_real_I_sub_one (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
  simpa [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))

/-- Explicit cubic Taylor bound on the major arc.  It follows directly from
`φ = (1 - (exp(it)-1)²)⁻¹` and Mathlib's quadratic remainder bound for `exp`. -/
lemma centeredGeometricCF_local_expansion (x : ℝ)
    (hx : |2 * Real.pi * x| ≤ 1 / 2) :
    ‖centeredGeometricCF x - (1 - (2 * Real.pi * x) ^ 2)‖ ≤
      5 * |2 * Real.pi * x| ^ 3 := by
  let t : ℝ := 2 * Real.pi * x
  let z : ℂ := Complex.exp ((t : ℂ) * Complex.I) - 1
  let v : ℂ := (t : ℂ) * Complex.I
  have hc : (2 : ℂ) * Real.pi * x = (t : ℂ) := by
    dsimp [t]
    push_cast
    ring
  rw [hc]
  change ‖centeredGeometricCF x - (1 - (t : ℂ) ^ 2)‖ ≤
    5 * |2 * Real.pi * x| ^ 3
  have ht : |t| ≤ 1 / 2 := by simpa [t] using hx
  have ht1 : ‖(t : ℂ) * Complex.I‖ ≤ 1 := by
    simpa [norm_mul, Real.norm_eq_abs] using
      ht.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hz : ‖z‖ ≤ |t| := norm_exp_real_I_sub_one t
  have he : ‖z - v‖ ≤ |t| ^ 2 := by
    dsimp [z, v]
    simpa [Real.norm_eq_abs, norm_mul] using
      (Complex.norm_exp_sub_one_sub_id_le ht1)
  have ht0 : 0 ≤ |t| := abs_nonneg _
  have hzsq : ‖z ^ 2‖ ≤ 1 / 4 := by
    rw [norm_pow]
    have hzhalf : ‖z‖ ≤ 1 / 2 := hz.trans ht
    nlinarith [sq_nonneg (‖z‖ - 1 / 2), norm_nonneg z]
  have hden : ‖1 - z ^ 2‖⁻¹ ≤ 4 / 3 := by
    have hnorm : 3 / 4 ≤ ‖1 - z ^ 2‖ := by
      calc
        (3 / 4 : ℝ) = ‖(1 : ℂ)‖ - 1 / 4 := by norm_num
        _ ≤ ‖(1 : ℂ)‖ - ‖z ^ 2‖ := sub_le_sub_left hzsq _
        _ ≤ ‖1 - z ^ 2‖ := norm_sub_norm_le _ _
    have hp : 0 < ‖1 - z ^ 2‖ := lt_of_lt_of_le (by norm_num) hnorm
    rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith
  have hw : ‖z ^ 2 + (t : ℂ) ^ 2‖ ≤ 3 * |t| ^ 3 := by
    have hfac : z ^ 2 + (t : ℂ) ^ 2 = (z - v) * (z + v) := by
      calc
        z ^ 2 + (t : ℂ) ^ 2 = z ^ 2 - v ^ 2 := by
          dsimp [v]
          rw [mul_pow, Complex.I_sq]
          ring
        _ = (z - v) * (z + v) := by ring
    rw [hfac, norm_mul]
    have hv : ‖v‖ = |t| := by simp [v, Real.norm_eq_abs]
    have hzv : ‖z + v‖ ≤ 2 * |t| := by
      calc
        ‖z + v‖ ≤ ‖z‖ + ‖v‖ := norm_add_le _ _
        _ ≤ |t| + |t| := add_le_add hz (le_of_eq hv)
        _ = 2 * |t| := by ring
    calc
      ‖z - v‖ * ‖z + v‖ ≤ |t| ^ 2 * (2 * |t|) :=
        mul_le_mul he hzv (norm_nonneg _) (by positivity)
      _ ≤ 3 * |t| ^ 3 := by nlinarith [sq_nonneg |t|]
  have hrem :
      ‖(z ^ 2) ^ 2 * (1 - z ^ 2)⁻¹‖ ≤ 2 * |t| ^ 3 := by
    rw [norm_mul, norm_pow, norm_pow]
    rw [show (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 by ring]
    have hz4 : ‖z‖ ^ 4 ≤ |t| ^ 4 := by gcongr
    have ht4 : |t| ^ 4 ≤ (3 / 2) * |t| ^ 3 := by
      nlinarith [sq_nonneg (|t| ^ 2), mul_nonneg (pow_nonneg ht0 3) ht0]
    calc
      ‖z‖ ^ 4 * ‖(1 - z ^ 2)⁻¹‖ ≤ |t| ^ 4 * (4 / 3) :=
        mul_le_mul hz4 (by simpa using hden) (norm_nonneg _) (by positivity)
      _ ≤ 2 * |t| ^ 3 := by nlinarith
  rw [centeredGeometricCF_eq_inv_one_sub_sq]
  change ‖(1 - z ^ 2)⁻¹ - (1 - (t : ℂ) ^ 2)‖ ≤ _
  have hid : (1 - z ^ 2)⁻¹ - (1 - (t : ℂ) ^ 2) =
      (z ^ 2 + (t : ℂ) ^ 2) + (z ^ 2) ^ 2 * (1 - z ^ 2)⁻¹ := by
    have hnz : 1 - z ^ 2 ≠ 0 := by
      intro hzero
      have hone : ‖z ^ 2‖ = 1 := by
        rw [(sub_eq_zero.mp hzero).symm]
        norm_num
      linarith
    field_simp
    ring
  rw [hid]
  calc
    ‖(z ^ 2 + (t : ℂ) ^ 2) + (z ^ 2) ^ 2 * (1 - z ^ 2)⁻¹‖ ≤
        ‖z ^ 2 + (t : ℂ) ^ 2‖ +
          ‖(z ^ 2) ^ 2 * (1 - z ^ 2)⁻¹‖ := norm_add_le _ _
    _ ≤ 3 * |t| ^ 3 + 2 * |t| ^ 3 := add_le_add hw hrem
    _ = 5 * |2 * Real.pi * x| ^ 3 := by simp [t]; ring

lemma centeredGeometricCF_norm_le_one (x : ℝ) :
    ‖centeredGeometricCF x‖ ≤ 1 := by
  have hs := centeredGeometricCF_norm_sq_le_exp x
  have he : Real.exp (-(circleDist x ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (sq_nonneg _)
  have hs' : ‖centeredGeometricCF x‖ ^ 2 ≤ 1 := hs.trans he
  nlinarith [norm_nonneg (centeredGeometricCF x),
    sq_nonneg (‖centeredGeometricCF x‖ - 1)]

/-- Telescoping estimate for two products all of whose factors lie in the
closed unit ball. -/
lemma norm_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u v : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ ≤
      ∑ i ∈ s, ‖u i - v i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hua := hu a (by simp)
      have hva := hv a (by simp)
      have hus : ∀ i ∈ s, ‖u i‖ ≤ 1 := fun i hi ↦ hu i (by simp [hi])
      have hvs : ∀ i ∈ s, ‖v i‖ ≤ 1 := fun i hi ↦ hv i (by simp [hi])
      have hpu : ‖∏ i ∈ s, u i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i hi ↦ norm_nonneg _) hus
      calc
        ‖u a * (∏ i ∈ s, u i) - v a * ∏ i ∈ s, v i‖ =
            ‖(u a - v a) * (∏ i ∈ s, u i) +
              v a * ((∏ i ∈ s, u i) - ∏ i ∈ s, v i)‖ := by
                congr 1
                ring
        _ ≤ ‖(u a - v a) * (∏ i ∈ s, u i)‖ +
              ‖v a * ((∏ i ∈ s, u i) - ∏ i ∈ s, v i)‖ := norm_add_le _ _
        _ = ‖u a - v a‖ * ‖∏ i ∈ s, u i‖ +
              ‖v a‖ * ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ := by
                rw [norm_mul, norm_mul]
        _ ≤ ‖u a - v a‖ * 1 + 1 * (∑ i ∈ s, ‖u i - v i‖) := by
              gcongr
              exact ih hus hvs
        _ = ‖u a - v a‖ + ∑ i ∈ s, ‖u i - v i‖ := by ring

private lemma norm_one_sub_real_le_one (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(1 - y : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

private lemma norm_one_sub_sub_exp_neg_le_sq
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(1 - y : ℂ) - Real.exp (-y)‖ ≤ y ^ 2 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he := Real.abs_exp_sub_one_sub_id_le (x := -y)
    (by simpa [abs_of_nonneg hy0] using hy1)
  calc
    |1 - y - Real.exp (-y)| = |-(Real.exp (-y) - 1 - -y)| := by congr 1; ring
    _ = |Real.exp (-y) - 1 - -y| := abs_neg _
    _ ≤ y ^ 2 := by simpa using he

/-- The quadratic exponent occurring on the major arc. -/
noncomputable def quadraticSum (q : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 q, (2 * Real.pi * (r : ℝ) * t) ^ 2

lemma sum_range_sq_real (q : ℕ) :
    ∑ r ∈ Finset.range q, (r : ℝ) ^ 2 =
      (q : ℝ) * (q - 1 : ℝ) * (2 * (q : ℝ) - 1) / 6 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma sum_Ico_one_sq_real (q : ℕ) :
    ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2 =
      (q : ℝ) * (q - 1 : ℝ) * (2 * (q : ℝ) - 1) / 6 := by
  rw [show Finset.Ico 1 q = (Finset.range q).erase 0 by
    ext r
    simp
    omega]
  rw [Finset.sum_erase]
  · simp [sum_range_sq_real]
  · simp

lemma quadraticSum_formula (q : ℕ) (t : ℝ) :
    quadraticSum q t = (2 * Real.pi * t) ^ 2 *
      ((q : ℝ) * (q - 1 : ℝ) * (2 * (q : ℝ) - 1) / 6) := by
  rw [quadraticSum, ← sum_Ico_one_sq_real q, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma sum_Ico_one_sq_bounds (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) ^ 3 / 24 ≤
      ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2 ∧
      (∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2) ≤ (q : ℝ) ^ 3 := by
  rw [sum_Ico_one_sq_real]
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  constructor <;> nlinarith [sq_nonneg ((q : ℝ) - 1)]

/-- Uniform major-arc comparison with its Gaussian product. -/
lemma centeredGeometricCF_prod_local_approximation (q : ℕ) (t : ℝ)
    (hmajor : |2 * Real.pi * (q : ℝ) * t| ≤ 1 / 2) :
    ‖(∏ r ∈ Finset.Ico 1 q, centeredGeometricCF ((r : ℝ) * t)) -
        Real.exp (-(quadraticSum q t))‖ ≤
      (∑ r ∈ Finset.Ico 1 q,
        5 * |2 * Real.pi * (r : ℝ) * t| ^ 3) +
      ∑ r ∈ Finset.Ico 1 q, (2 * Real.pi * (r : ℝ) * t) ^ 4 := by
  let s := Finset.Ico 1 q
  let y : ℕ → ℝ := fun r ↦ (2 * Real.pi * (r : ℝ) * t) ^ 2
  have hy (r : ℕ) (hr : r ∈ s) : 0 ≤ y r ∧ y r ≤ 1 / 4 := by
    have hrq : r ≤ q := by simpa [s] using (Finset.mem_Ico.mp hr).2.le
    have habs : |2 * Real.pi * (r : ℝ) * t| ≤ 1 / 2 := by
      have hq0 : 0 ≤ (q : ℝ) := by positivity
      have hr0 : 0 ≤ (r : ℝ) := by positivity
      have hpi : 0 ≤ 2 * Real.pi := by positivity
      calc
        |2 * Real.pi * (r : ℝ) * t| =
            (2 * Real.pi) * (r : ℝ) * |t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hpi, abs_of_nonneg hr0]
        _ ≤ (2 * Real.pi) * (q : ℝ) * |t| := by gcongr
        _ = |2 * Real.pi * (q : ℝ) * t| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hpi, abs_of_nonneg hq0]
        _ ≤ 1 / 2 := hmajor
    constructor
    · exact sq_nonneg _
    · have hsquare :
          (2 * Real.pi * (r : ℝ) * t) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
      dsimp [y]
      norm_num at hsquare ⊢
      exact hsquare
  have hfirst :
      ‖(∏ r ∈ s, centeredGeometricCF ((r : ℝ) * t)) -
          ∏ r ∈ s, (1 - y r : ℂ)‖ ≤
        ∑ r ∈ s, 5 * |2 * Real.pi * (r : ℝ) * t| ^ 3 := by
    calc
      _ ≤ ∑ r ∈ s,
          ‖centeredGeometricCF ((r : ℝ) * t) - (1 - y r : ℂ)‖ :=
        norm_prod_sub_prod_le_sum s _ _
          (fun r hr ↦ centeredGeometricCF_norm_le_one _)
          (fun r hr ↦ norm_one_sub_real_le_one _ (hy r hr).1
            ((hy r hr).2.trans (by norm_num)))
      _ ≤ ∑ r ∈ s, 5 * |2 * Real.pi * (r : ℝ) * t| ^ 3 := by
        apply Finset.sum_le_sum
        intro r hr
        dsimp [y]
        have hlocal : |2 * Real.pi * ((r : ℝ) * t)| ≤ 1 / 2 := by
          have h := (hy r hr).2
          dsimp [y] at h
          rw [← sq_abs] at h
          apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp
          norm_num at h ⊢
          simpa [mul_assoc] using h
        have hl := centeredGeometricCF_local_expansion ((r : ℝ) * t) hlocal
        convert hl using 1
        · rfl
        · congr 2
          push_cast
          ring
        · congr 2
          ring_nf
  have hsecond :
      ‖(∏ r ∈ s, (1 - y r : ℂ)) -
          ∏ r ∈ s, (Real.exp (-(y r)) : ℂ)‖ ≤
        ∑ r ∈ s, (y r) ^ 2 := by
    calc
      _ ≤ ∑ r ∈ s, ‖(1 - y r : ℂ) - Real.exp (-(y r))‖ :=
        norm_prod_sub_prod_le_sum s _ _
          (fun r hr ↦ norm_one_sub_real_le_one _ (hy r hr).1
            ((hy r hr).2.trans (by norm_num)))
          (fun r hr ↦ by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
            exact neg_nonpos.mpr (hy r hr).1)
      _ ≤ ∑ r ∈ s, (y r) ^ 2 :=
        Finset.sum_le_sum fun r hr ↦
          norm_one_sub_sub_exp_neg_le_sq _ (hy r hr).1
            ((hy r hr).2.trans (by norm_num))
  have hexp : (∏ r ∈ s, (Real.exp (-(y r)) : ℂ)) =
      Real.exp (-(quadraticSum q t)) := by
    have hreal : (∏ r ∈ s, Real.exp (-(y r))) =
        Real.exp (-(quadraticSum q t)) := by
      calc
        (∏ r ∈ s, Real.exp (-(y r))) =
            Real.exp (∑ r ∈ s, -(y r)) := by rw [Real.exp_sum]
        _ = Real.exp (-(quadraticSum q t)) := by
          congr 1
          simp [quadraticSum, y, s]
    exact_mod_cast hreal
  rw [← hexp]
  calc
    ‖(∏ r ∈ s, centeredGeometricCF ((r : ℝ) * t)) -
        ∏ r ∈ s, (Real.exp (-(y r)) : ℂ)‖ ≤
      ‖(∏ r ∈ s, centeredGeometricCF ((r : ℝ) * t)) -
        ∏ r ∈ s, (1 - y r : ℂ)‖ +
      ‖(∏ r ∈ s, (1 - y r : ℂ)) -
        ∏ r ∈ s, (Real.exp (-(y r)) : ℂ)‖ := by
          rw [show (∏ r ∈ s, centeredGeometricCF ((r : ℝ) * t)) -
                ∏ r ∈ s, (Real.exp (-(y r)) : ℂ) =
              ((∏ r ∈ s, centeredGeometricCF ((r : ℝ) * t)) -
                ∏ r ∈ s, (1 - y r : ℂ)) +
              ((∏ r ∈ s, (1 - y r : ℂ)) -
                ∏ r ∈ s, (Real.exp (-(y r)) : ℂ)) by ring]
          exact norm_add_le _ _
    _ ≤ (∑ r ∈ s, 5 * |2 * Real.pi * (r : ℝ) * t| ^ 3) +
          ∑ r ∈ s, (y r) ^ 2 := add_le_add hfirst hsecond
    _ = _ := by
      congr 1
      simp [s, y]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- A deliberately loose bound for the summed cubic Taylor remainders. -/
lemma sum_cubic_majorant (q : ℕ) (t : ℝ) :
    (∑ r ∈ Finset.Ico 1 q,
        5 * |2 * Real.pi * (r : ℝ) * t| ^ 3) ≤
      5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 4 * |t| ^ 3 := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  calc
    (∑ r ∈ Finset.Ico 1 q, 5 * |2 * Real.pi * (r : ℝ) * t| ^ 3) ≤
        ∑ _r ∈ Finset.Ico 1 q,
          5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 3 * |t| ^ 3 := by
      apply Finset.sum_le_sum
      intro r hr
      have hrq : (r : ℝ) ≤ q := by
        exact_mod_cast (Finset.mem_Ico.mp hr).2.le
      rw [abs_mul, abs_mul, abs_of_nonneg hpi,
        abs_of_nonneg (Nat.cast_nonneg r)]
      have hrpow : (r : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := by gcongr
      calc
        5 * ((2 * Real.pi) * (r : ℝ) * |t|) ^ 3 =
            (5 * (2 * Real.pi) ^ 3 * |t| ^ 3) * (r : ℝ) ^ 3 := by ring
        _ ≤ (5 * (2 * Real.pi) ^ 3 * |t| ^ 3) * (q : ℝ) ^ 3 := by
          gcongr
        _ = 5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 3 * |t| ^ 3 := by ring
    _ = ((Finset.Ico 1 q).card : ℝ) *
          (5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 3 * |t| ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) *
          (5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 3 * |t| ^ 3) := by
      gcongr
      simp
    _ = 5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 4 * |t| ^ 3 := by ring

/-- A deliberately loose bound for the summed quartic Taylor remainders. -/
lemma sum_quartic_majorant (q : ℕ) (t : ℝ) :
    (∑ r ∈ Finset.Ico 1 q, (2 * Real.pi * (r : ℝ) * t) ^ 4) ≤
      (2 * Real.pi) ^ 4 * (q : ℝ) ^ 5 * |t| ^ 4 := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  calc
    (∑ r ∈ Finset.Ico 1 q, (2 * Real.pi * (r : ℝ) * t) ^ 4) =
        ∑ r ∈ Finset.Ico 1 q, |2 * Real.pi * (r : ℝ) * t| ^ 4 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Even.pow_abs (by decide : Even 4)]
    _ ≤ ∑ _r ∈ Finset.Ico 1 q,
          (2 * Real.pi) ^ 4 * (q : ℝ) ^ 4 * |t| ^ 4 := by
      apply Finset.sum_le_sum
      intro r hr
      have hrq : (r : ℝ) ≤ q := by
        exact_mod_cast (Finset.mem_Ico.mp hr).2.le
      rw [abs_mul, abs_mul, abs_of_nonneg hpi,
        abs_of_nonneg (Nat.cast_nonneg r)]
      have hrpow : (r : ℝ) ^ 4 ≤ (q : ℝ) ^ 4 := by gcongr
      calc
        ((2 * Real.pi) * (r : ℝ) * |t|) ^ 4 =
            ((2 * Real.pi) ^ 4 * |t| ^ 4) * (r : ℝ) ^ 4 := by ring
        _ ≤ ((2 * Real.pi) ^ 4 * |t| ^ 4) * (q : ℝ) ^ 4 := by
          gcongr
        _ = (2 * Real.pi) ^ 4 * (q : ℝ) ^ 4 * |t| ^ 4 := by ring
    _ = ((Finset.Ico 1 q).card : ℝ) *
          ((2 * Real.pi) ^ 4 * (q : ℝ) ^ 4 * |t| ^ 4) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) *
          ((2 * Real.pi) ^ 4 * (q : ℝ) ^ 4 * |t| ^ 4) := by
      gcongr
      simp
    _ = (2 * Real.pi) ^ 4 * (q : ℝ) ^ 5 * |t| ^ 4 := by ring

/-- Pointwise major-arc error with no remaining finite sums. -/
lemma centeredGeometricCF_prod_local_polynomial_bound (q : ℕ) (t : ℝ)
    (hmajor : |2 * Real.pi * (q : ℝ) * t| ≤ 1 / 2) :
    ‖(∏ r ∈ Finset.Ico 1 q, centeredGeometricCF ((r : ℝ) * t)) -
        Real.exp (-(quadraticSum q t))‖ ≤
      5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 4 * |t| ^ 3 +
      (2 * Real.pi) ^ 4 * (q : ℝ) ^ 5 * |t| ^ 4 :=
  (centeredGeometricCF_prod_local_approximation q t hmajor).trans
    (add_le_add (sum_cubic_majorant q t) (sum_quartic_majorant q t))

/-- The algebraic auxiliary scale `q^(1/16)`, expressed with square roots so
that no real-power normalization is needed later. -/
noncomputable def sixteenthRoot (q : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt q)))

lemma sixteenthRoot_nonneg (q : ℕ) : 0 ≤ sixteenthRoot q := by
  exact Real.sqrt_nonneg _

lemma sixteenthRoot_pos {q : ℕ} (hq : 0 < q) : 0 < sixteenthRoot q := by
  repeat' apply Real.sqrt_pos.2
  exact_mod_cast hq

/-- Four successive squarings recover `q`. -/
lemma sixteenthRoot_pow_sixteen (q : ℕ) : sixteenthRoot q ^ 16 = (q : ℝ) := by
  let r1 : ℝ := Real.sqrt q
  let r2 : ℝ := Real.sqrt r1
  let r3 : ℝ := Real.sqrt r2
  let r4 : ℝ := Real.sqrt r3
  have h1 : r1 ^ 2 = (q : ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
  have h2 : r2 ^ 2 = r1 := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : r3 ^ 2 = r2 := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : r4 ^ 2 = r3 := Real.sq_sqrt (Real.sqrt_nonneg _)
  change r4 ^ 16 = (q : ℝ)
  calc
    r4 ^ 16 = (r4 ^ 2) ^ 8 := by ring
    _ = r3 ^ 8 := by rw [h4]
    _ = (r3 ^ 2) ^ 4 := by ring
    _ = r2 ^ 4 := by rw [h3]
    _ = (r2 ^ 2) ^ 2 := by ring
    _ = r1 ^ 2 := by rw [h2]
    _ = (q : ℝ) := h1

lemma sqrt_nat_eq_sixteenthRoot_pow_eight (q : ℕ) :
    Real.sqrt q = sixteenthRoot q ^ 8 := by
  let r1 : ℝ := Real.sqrt q
  let r2 : ℝ := Real.sqrt r1
  let r3 : ℝ := Real.sqrt r2
  let r4 : ℝ := Real.sqrt r3
  have h2 : r2 ^ 2 = r1 := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : r3 ^ 2 = r2 := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : r4 ^ 2 = r3 := Real.sq_sqrt (Real.sqrt_nonneg _)
  change r1 = r4 ^ 8
  calc
    r1 = r2 ^ 2 := h2.symm
    _ = (r3 ^ 2) ^ 2 := by rw [h3]
    _ = r3 ^ 4 := by ring
    _ = (r4 ^ 2) ^ 4 := by rw [h4]
    _ = r4 ^ 8 := by ring

/-- The edge of the major arc.  If `z = q^(1/16)`, this is exactly
`z⁻²³`; its product with the standard deviation is of order `z`. -/
noncomputable def majorRadius (q : ℕ) : ℝ :=
  sixteenthRoot q / ((q : ℝ) * Real.sqrt q)

lemma majorRadius_eq_inv_pow (q : ℕ) (hq : 0 < q) :
    majorRadius q = 1 / sixteenthRoot q ^ 23 := by
  have hz := sixteenthRoot_pos hq
  rw [majorRadius, sqrt_nat_eq_sixteenthRoot_pow_eight q,
    ← sixteenthRoot_pow_sixteen q]
  field_simp

lemma majorRadius_pos {q : ℕ} (hq : 0 < q) : 0 < majorRadius q := by
  rw [majorRadius_eq_inv_pow q hq]
  exact one_div_pos.mpr (pow_pos (sixteenthRoot_pos hq) _)

/-- On the chosen major arc all individual factors are in the Taylor range. -/
lemma majorRadius_taylor_range {q : ℕ} (hq : 0 < q)
    (hz : 4 ≤ sixteenthRoot q) {t : ℝ} (ht : |t| ≤ majorRadius q) :
    |2 * Real.pi * (q : ℝ) * t| ≤ 1 / 2 := by
  let z := sixteenthRoot q
  have hz0 : 0 < z := sixteenthRoot_pos hq
  have hpi : 2 * Real.pi < 8 := by linarith [Real.pi_lt_four]
  rw [majorRadius_eq_inv_pow q hq] at ht
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
    abs_of_nonneg (Nat.cast_nonneg q)]
  calc
    2 * Real.pi * (q : ℝ) * |t| ≤
        2 * Real.pi * (q : ℝ) * (1 / z ^ 23) := by gcongr
    _ = 2 * Real.pi / z ^ 7 := by
      rw [← sixteenthRoot_pow_sixteen q]
      change 2 * Real.pi * z ^ 16 * (1 / z ^ 23) = _
      field_simp
    _ ≤ 8 / 4 ^ 7 := by
      apply div_le_div₀ (by positivity) (le_of_lt hpi) (by positivity)
      gcongr
    _ ≤ 1 / 2 := by norm_num

/-- On the full major arc the pointwise Taylor error is `O(z⁻⁵)`, where
`z = q^(1/16)`.  Constants are intentionally rounded upwards. -/
lemma major_arc_pointwise_error {q : ℕ} (hq : 0 < q)
    (hz : 4 ≤ sixteenthRoot q) {t : ℝ} (ht : |t| ≤ majorRadius q) :
    ‖(∏ r ∈ Finset.Ico 1 q, centeredGeometricCF ((r : ℝ) * t)) -
        Real.exp (-(quadraticSum q t))‖ ≤
      7000 / sixteenthRoot q ^ 5 := by
  let z := sixteenthRoot q
  have hz0 : 0 < z := sixteenthRoot_pos hq
  have htz : |t| ≤ 1 / z ^ 23 := by
    simpa [z, majorRadius_eq_inv_pow q hq] using ht
  have ht3 : |t| ^ 3 ≤ (1 / z ^ 23) ^ 3 := by gcongr
  have ht4 : |t| ^ 4 ≤ (1 / z ^ 23) ^ 4 := by gcongr
  have hpi : 2 * Real.pi ≤ 8 := le_of_lt (by linarith [Real.pi_lt_four])
  have hcubic : 5 * (2 * Real.pi) ^ 3 ≤ 2560 := by
    calc
      5 * (2 * Real.pi) ^ 3 ≤ 5 * 8 ^ 3 := by gcongr
      _ = 2560 := by norm_num
  have hquartic : (2 * Real.pi) ^ 4 ≤ 4096 := by
    calc
      (2 * Real.pi) ^ 4 ≤ 8 ^ 4 := by gcongr
      _ = 4096 := by norm_num
  have hfirst :
      5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 4 * |t| ^ 3 ≤ 2560 / z ^ 5 := by
    calc
      5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 4 * |t| ^ 3 ≤
          2560 * (q : ℝ) ^ 4 * (1 / z ^ 23) ^ 3 := by gcongr
      _ = 2560 / z ^ 5 := by
        rw [← sixteenthRoot_pow_sixteen q]
        change 2560 * (z ^ 16) ^ 4 * (1 / z ^ 23) ^ 3 = _
        field_simp
  have hsecond :
      (2 * Real.pi) ^ 4 * (q : ℝ) ^ 5 * |t| ^ 4 ≤ 4096 / z ^ 12 := by
    calc
      (2 * Real.pi) ^ 4 * (q : ℝ) ^ 5 * |t| ^ 4 ≤
          4096 * (q : ℝ) ^ 5 * (1 / z ^ 23) ^ 4 := by gcongr
      _ = 4096 / z ^ 12 := by
        rw [← sixteenthRoot_pow_sixteen q]
        change 4096 * (z ^ 16) ^ 5 * (1 / z ^ 23) ^ 4 = _
        field_simp
  have hzpow : z ^ 5 ≤ z ^ 12 := by
    have hz1 : 1 ≤ z := le_trans (by norm_num) hz
    exact pow_le_pow_right₀ hz1 (by norm_num)
  calc
    _ ≤ 5 * (2 * Real.pi) ^ 3 * (q : ℝ) ^ 4 * |t| ^ 3 +
          (2 * Real.pi) ^ 4 * (q : ℝ) ^ 5 * |t| ^ 4 :=
      centeredGeometricCF_prod_local_polynomial_bound q t
        (majorRadius_taylor_range hq hz ht)
    _ ≤ 2560 / z ^ 5 + 4096 / z ^ 12 := add_le_add hfirst hsecond
    _ ≤ 2560 / z ^ 5 + 4096 / z ^ 5 := by
      gcongr
    _ ≤ 7000 / z ^ 5 := by
      rw [← add_div]
      gcongr
      norm_num

private lemma centeredGeometricCF_denominator_ne (x : ℝ) :
    (2 : ℂ) - Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) ≠ 0 := by
  intro h
  have heq : (2 : ℂ) = Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) :=
    sub_eq_zero.mp h
  have hn := congrArg norm heq
  rw [Complex.norm_exp] at hn
  norm_num [Complex.mul_re] at hn

lemma continuous_centeredGeometricCF : Continuous centeredGeometricCF := by
  unfold centeredGeometricCF
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    convert centeredGeometricCF_denominator_ne x using 1 <;> push_cast <;> ring

/-- The Fourier phase associated with an integer target. -/
noncomputable def fourierPhase (a : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-((2 * Real.pi * (a : ℝ) * t : ℝ) : ℂ) * Complex.I)

@[simp] lemma fourierPhase_norm (a : ℤ) (t : ℝ) : ‖fourierPhase a t‖ = 1 := by
  rw [fourierPhase, Complex.norm_exp]
  simp

lemma continuous_fourierPhase (a : ℤ) : Continuous (fourierPhase a) := by
  unfold fourierPhase
  fun_prop

/-- The characteristic-function product appearing in Fourier inversion. -/
noncomputable def geometricProduct (q : ℕ) (t : ℝ) : ℂ :=
  ∏ r ∈ Finset.Ico 1 q, centeredGeometricCF ((r : ℝ) * t)

lemma continuous_geometricProduct (q : ℕ) : Continuous (geometricProduct q) := by
  unfold geometricProduct
  apply continuous_finset_prod
  intro r hr
  exact continuous_centeredGeometricCF.comp (continuous_const.mul continuous_id)

lemma continuous_quadraticGaussian (q : ℕ) :
    Continuous (fun t : ℝ ↦ (Real.exp (-(quadraticSum q t)) : ℂ)) := by
  unfold quadraticSum
  fun_prop

/-- After integration over the major arc, the product differs from its
Gaussian model by `O(z⁻²⁸)`. -/
lemma major_arc_integral_error {q : ℕ} (hq : 0 < q)
    (hz : 4 ≤ sixteenthRoot q) (a : ℤ) :
    ‖(∫ t : ℝ in -(majorRadius q)..majorRadius q,
          fourierPhase a t * geometricProduct q t) -
        ∫ t : ℝ in -(majorRadius q)..majorRadius q,
          fourierPhase a t * Real.exp (-(quadraticSum q t))‖ ≤
      14000 / sixteenthRoot q ^ 28 := by
  let η := majorRadius q
  let z := sixteenthRoot q
  have hη : 0 < η := majorRadius_pos hq
  have hz0 : 0 < z := sixteenthRoot_pos hq
  have hprod : Continuous (fun t : ℝ ↦ fourierPhase a t * geometricProduct q t) :=
    (continuous_fourierPhase a).mul (continuous_geometricProduct q)
  have hgauss : Continuous (fun t : ℝ ↦
      fourierPhase a t * (Real.exp (-(quadraticSum q t)) : ℂ)) :=
    (continuous_fourierPhase a).mul (continuous_quadraticGaussian q)
  rw [← intervalIntegral.integral_sub
    (hprod.intervalIntegrable _ _) (hgauss.intervalIntegrable _ _)]
  calc
    ‖∫ t : ℝ in -η..η,
        fourierPhase a t * geometricProduct q t -
          fourierPhase a t * Real.exp (-(quadraticSum q t))‖ ≤
        (7000 / z ^ 5) * |η - -η| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have htη : |t| ≤ η := by
        have ht' := Set.uIoc_subset_uIcc ht
        rw [Set.uIcc_of_le (by linarith : -η ≤ η)] at ht'
        exact abs_le.mpr ht'
      rw [← mul_sub, norm_mul, fourierPhase_norm, one_mul]
      exact major_arc_pointwise_error hq hz (by simpa [η] using htη)
    _ = 14000 / z ^ 28 := by
      rw [abs_of_pos (by linarith : 0 < η - -η)]
      dsimp [η]
      rw [majorRadius_eq_inv_pow q hq]
      change (7000 / z ^ 5) * (1 / z ^ 23 - -(1 / z ^ 23)) = _
      field_simp
      norm_num

/-- The positive quadratic coefficient in the Gaussian model. -/
noncomputable def gaussianCoeff (q : ℕ) : ℝ :=
  (2 * Real.pi) ^ 2 * ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2

lemma quadraticSum_eq_gaussianCoeff_mul (q : ℕ) (t : ℝ) :
    quadraticSum q t = gaussianCoeff q * t ^ 2 := by
  rw [quadraticSum, gaussianCoeff, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma gaussianCoeff_pos {q : ℕ} (hq : 2 ≤ q) : 0 < gaussianCoeff q := by
  rw [gaussianCoeff]
  have hs := (sum_Ico_one_sq_bounds q hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
  have hsum : 0 < ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2 :=
    lt_of_lt_of_le (by positivity) hs
  exact mul_pos (sq_pos_of_pos (by positivity)) hsum

/-- Exact Fourier transform of the full Gaussian model. -/
lemma integral_gaussian_model {q : ℕ} (hq : 2 ≤ q) (a : ℤ) :
    (∫ t : ℝ, fourierPhase a t * Real.exp (-(quadraticSum q t))) =
      ((Real.sqrt (Real.pi / gaussianCoeff q) *
        Real.exp (-((2 * Real.pi * (a : ℝ)) ^ 2) /
          (4 * gaussianCoeff q)) : ℝ) : ℂ) := by
  let b : ℝ := gaussianCoeff q
  let c : ℝ := -(2 * Real.pi * (a : ℝ))
  have hb : 0 < b := gaussianCoeff_pos hq
  have hformula := fourierIntegral_gaussian (b := (b : ℂ))
    (show 0 < (b : ℂ).re by simpa using hb) (c : ℂ)
  have hintegrand (t : ℝ) :
      fourierPhase a t * (Real.exp (-(quadraticSum q t)) : ℂ) =
        Complex.exp (Complex.I * (c : ℂ) * t) *
          Complex.exp (-(b : ℂ) * t ^ 2) := by
    rw [fourierPhase, quadraticSum_eq_gaussianCoeff_mul]
    dsimp [b, c]
    rw [Complex.ofReal_exp]
    congr 1 <;> push_cast <;> ring_nf
  simp_rw [hintegrand]
  rw [hformula]
  have hsqrt : (Real.sqrt (Real.pi / b) : ℂ) =
      ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_div]
    norm_num
  rw [← hsqrt]
  have he : -((c : ℂ) ^ 2) / (4 * (b : ℂ)) =
      ((-(c ^ 2) / (4 * b) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  dsimp [b, c]
  ring_nf

lemma gaussianCoeff_bounds (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) ^ 3 ≤ gaussianCoeff q ∧
      gaussianCoeff q ≤ 64 * (q : ℝ) ^ 3 := by
  have hs := sum_Ico_one_sq_bounds q hq
  have hfac_lower : (24 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hfac_upper : (2 * Real.pi) ^ 2 ≤ (64 : ℝ) := by
    have := Real.pi_lt_four
    nlinarith [Real.pi_pos]
  rw [gaussianCoeff]
  constructor
  · calc
      (q : ℝ) ^ 3 ≤ 24 * (∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2) := by
        linarith
      _ ≤ (2 * Real.pi) ^ 2 * ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2 := by
        gcongr
  · calc
      (2 * Real.pi) ^ 2 * ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2 ≤
          64 * ∑ r ∈ Finset.Ico 1 q, (r : ℝ) ^ 2 := by
        gcongr
      _ ≤ 64 * (q : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hs.2 (by norm_num)

/-- A uniform lower bound for the full Gaussian transform in the central
deviation range needed below. -/
lemma gaussian_model_lower {q : ℕ} (hq : 2 ≤ q) (a : ℤ)
    (ha : |(a : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q) :
    Real.exp (-1600) / (8 * sixteenthRoot q ^ 24) ≤
      Real.sqrt (Real.pi / gaussianCoeff q) *
        Real.exp (-((2 * Real.pi * (a : ℝ)) ^ 2) /
          (4 * gaussianCoeff q)) := by
  let z := sixteenthRoot q
  let b := gaussianCoeff q
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hz0 : 0 < z := sixteenthRoot_pos hq0
  have hb : 0 < b := gaussianCoeff_pos hq
  have hbounds := gaussianCoeff_bounds q hq
  have hratio : 1 / (64 * z ^ 48) ≤ Real.pi / b := by
    have hqpow : (q : ℝ) ^ 3 = z ^ 48 := by
      rw [← sixteenthRoot_pow_sixteen q]
      change (z ^ 16) ^ 3 = z ^ 48
      ring
    have hinv : 1 / (64 * (q : ℝ) ^ 3) ≤ 1 / b := by
      exact one_div_le_one_div_of_le hb (hbounds.2.trans_eq (by ring))
    calc
      1 / (64 * z ^ 48) = 1 / (64 * (q : ℝ) ^ 3) := by rw [hqpow]
      _ ≤ 1 / b := hinv
      _ ≤ Real.pi / b := by
        apply div_le_div_of_nonneg_right
          (le_of_lt Real.pi_gt_three |>.trans' (by norm_num)) hb.le
  have hsqrt : 1 / (8 * z ^ 24) ≤ Real.sqrt (Real.pi / b) := by
    have hdiv0 : 0 ≤ Real.pi / b := (div_pos Real.pi_pos hb).le
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hdiv0]
    calc
      (1 / (8 * z ^ 24)) ^ 2 = 1 / (64 * z ^ 48) := by
        field_simp
        ring
      _ ≤ Real.pi / b := hratio
  have ha2 : (a : ℝ) ^ 2 ≤ 100 * (q : ℝ) ^ 3 := by
    have hsqrtq : Real.sqrt q ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg q)
    have hsquare := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 ha
    rw [sq_abs] at hsquare
    nlinarith
  have hfac : (2 * Real.pi) ^ 2 ≤ (64 : ℝ) := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hnum : (2 * Real.pi * (a : ℝ)) ^ 2 ≤ 6400 * (q : ℝ) ^ 3 := by
    calc
      (2 * Real.pi * (a : ℝ)) ^ 2 =
          (2 * Real.pi) ^ 2 * (a : ℝ) ^ 2 := by ring
      _ ≤ 64 * (100 * (q : ℝ) ^ 3) := by gcongr
      _ = 6400 * (q : ℝ) ^ 3 := by ring
  have hexponent :
      ((2 * Real.pi * (a : ℝ)) ^ 2) / (4 * b) ≤ 1600 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * b)).2
    nlinarith [hbounds.1]
  have hexp : Real.exp (-1600) ≤
      Real.exp (-((2 * Real.pi * (a : ℝ)) ^ 2) / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg hexponent
  change Real.exp (-1600) / (8 * z ^ 24) ≤
    Real.sqrt (Real.pi / b) *
      Real.exp (-((2 * Real.pi * (a : ℝ)) ^ 2) / (4 * b))
  calc
    Real.exp (-1600) / (8 * z ^ 24) =
        (1 / (8 * z ^ 24)) * Real.exp (-1600) := by ring
    _ ≤ _ := mul_le_mul hsqrt hexp (Real.exp_nonneg _) (by positivity)

lemma integrable_gaussian_model {q : ℕ} (hq : 2 ≤ q) (a : ℤ) :
    Integrable (fun t : ℝ ↦
      fourierPhase a t * (Real.exp (-(quadraticSum q t)) : ℂ)) := by
  let b : ℝ := gaussianCoeff q
  have hb : 0 < b := gaussianCoeff_pos hq
  have hg : Integrable (fun t : ℝ ↦ Real.exp (-b * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  apply hg.mono'
  · exact ((continuous_fourierPhase a).mul
      (continuous_quadraticGaussian q)).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul, fourierPhase_norm, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      quadraticSum_eq_gaussianCoeff_mul]
    simpa [b]

/-- The omitted Gaussian tails are exponentially small at the algebraic major
radius. -/
lemma gaussian_truncation_error {q : ℕ} (hq : 2 ≤ q) (a : ℤ) :
    ‖(∫ t : ℝ, fourierPhase a t * Real.exp (-(quadraticSum q t))) -
        ∫ t : ℝ in -(majorRadius q)..majorRadius q,
          fourierPhase a t * Real.exp (-(quadraticSum q t))‖ ≤
      2 * Real.exp (-(sixteenthRoot q ^ 2)) /
        sixteenthRoot q ^ 25 := by
  let z := sixteenthRoot q
  let η := majorRadius q
  let b := gaussianCoeff q
  let f : ℝ → ℂ := fun t ↦
    fourierPhase a t * Real.exp (-(quadraticSum q t))
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hz0 : 0 < z := sixteenthRoot_pos hq0
  have hη : 0 < η := majorRadius_pos hq0
  have hb : 0 < b := gaussianCoeff_pos hq
  have hblower : (q : ℝ) ^ 3 ≤ b := (gaussianCoeff_bounds q hq).1
  change ‖(∫ t : ℝ, f t) - ∫ t : ℝ in -η..η, f t‖ ≤
    2 * Real.exp (-(z ^ 2)) / z ^ 25
  have hf : Integrable f := integrable_gaussian_model hq a
  have hnorm (t : ℝ) : ‖f t‖ = Real.exp (-(b * t ^ 2)) := by
    dsimp [f]
    rw [norm_mul, fourierPhase_norm, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      quadraticSum_eq_gaussianCoeff_mul]
  have hright : ‖∫ t : ℝ in Set.Ioi η, f t‖ ≤
      Real.exp (-(z ^ 2)) / z ^ 25 := by
    have hc : -((q : ℝ) ^ 3 * η) < 0 := by
      nlinarith [mul_pos (pow_pos hqR 3) hη]
    calc
      ‖∫ t : ℝ in Set.Ioi η, f t‖ ≤
          ∫ t : ℝ in Set.Ioi η, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in Set.Ioi η,
          Real.exp ((-((q : ℝ) ^ 3 * η)) * t) := by
        refine setIntegral_mono_on hf.norm.integrableOn
          (integrableOn_exp_mul_Ioi hc η) measurableSet_Ioi ?_
        intro t ht
        rw [hnorm]
        apply Real.exp_le_exp.mpr
        have htη : η ≤ t := le_of_lt ht
        have ht0 : 0 ≤ t := le_trans hη.le htη
        have h1 : (q : ℝ) ^ 3 * t ^ 2 ≤ b * t ^ 2 :=
          mul_le_mul_of_nonneg_right hblower (sq_nonneg t)
        have h2 : η * t ≤ t ^ 2 := by
          nlinarith [mul_nonneg ht0 (sub_nonneg.mpr htη)]
        nlinarith [mul_nonneg (show 0 ≤ (q : ℝ) ^ 3 by positivity)
          (sub_nonneg.mpr h2)]
      _ = Real.exp (-(z ^ 2)) / z ^ 25 := by
        rw [integral_exp_mul_Ioi hc]
        dsimp [η]
        rw [majorRadius_eq_inv_pow q hq0]
        rw [← sixteenthRoot_pow_sixteen q]
        dsimp [z]
        change -Real.exp (-((sixteenthRoot q ^ 16) ^ 3 *
            (1 / sixteenthRoot q ^ 23)) * (1 / sixteenthRoot q ^ 23)) /
          (-((sixteenthRoot q ^ 16) ^ 3 * (1 / sixteenthRoot q ^ 23))) = _
        field_simp
  have hleft : ‖∫ t : ℝ in Set.Iic (-η), f t‖ ≤
      Real.exp (-(z ^ 2)) / z ^ 25 := by
    have hc : 0 < (q : ℝ) ^ 3 * η := by positivity
    calc
      ‖∫ t : ℝ in Set.Iic (-η), f t‖ ≤
          ∫ t : ℝ in Set.Iic (-η), ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in Set.Iic (-η),
          Real.exp (((q : ℝ) ^ 3 * η) * t) := by
        refine setIntegral_mono_on hf.norm.integrableOn
          (integrableOn_exp_mul_Iic hc (-η)) measurableSet_Iic ?_
        intro t ht
        rw [hnorm]
        apply Real.exp_le_exp.mpr
        have htη : t ≤ -η := ht
        have ht0 : t ≤ 0 := le_trans htη (by linarith : -η ≤ 0)
        have h1 : (q : ℝ) ^ 3 * t ^ 2 ≤ b * t ^ 2 :=
          mul_le_mul_of_nonneg_right hblower (sq_nonneg t)
        have h2 : -η * t ≤ t ^ 2 := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos ht0
            (by linarith : t + η ≤ 0)]
        nlinarith [mul_nonneg (show 0 ≤ (q : ℝ) ^ 3 by positivity)
          (sub_nonneg.mpr h2)]
      _ = Real.exp (-(z ^ 2)) / z ^ 25 := by
        rw [integral_exp_mul_Iic hc]
        dsimp [η]
        rw [majorRadius_eq_inv_pow q hq0]
        rw [← sixteenthRoot_pow_sixteen q]
        dsimp [z]
        change Real.exp ((sixteenthRoot q ^ 16) ^ 3 *
            (1 / sixteenthRoot q ^ 23) * -(1 / sixteenthRoot q ^ 23)) /
          ((sixteenthRoot q ^ 16) ^ 3 * (1 / sixteenthRoot q ^ 23)) = _
        field_simp
  rw [intervalIntegral.integral_of_le (by linarith : -η ≤ η)]
  rw [← setIntegral_compl measurableSet_Ioc hf]
  rw [Set.compl_Ioc]
  rw [setIntegral_union (Set.Iic_disjoint_Ioi (by linarith : -η ≤ η))
    measurableSet_Ioi hf.integrableOn hf.integrableOn]
  calc
    ‖(∫ t : ℝ in Set.Iic (-η), f t) + ∫ t : ℝ in Set.Ioi η, f t‖ ≤
        ‖∫ t : ℝ in Set.Iic (-η), f t‖ +
          ‖∫ t : ℝ in Set.Ioi η, f t‖ := norm_add_le _ _
    _ ≤ Real.exp (-(z ^ 2)) / z ^ 25 +
        Real.exp (-(z ^ 2)) / z ^ 25 := add_le_add hleft hright
    _ = 2 * Real.exp (-(z ^ 2)) / z ^ 25 := by ring

@[simp] lemma circleDist_neg (x : ℝ) : circleDist (-x) = circleDist x := by
  simp [circleDist]

lemma rotationEnergy_abs (q : ℕ) (t : ℝ) :
    rotationEnergy q |t| = rotationEnergy q t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    unfold rotationEnergy
    apply Finset.sum_congr rfl
    intro r hr
    rw [show (r : ℝ) * -t = -((r : ℝ) * t) by ring, circleDist_neg]

/-- Uniform exponential decay everywhere outside the major arc but inside one
Fourier period. -/
lemma outer_arc_pointwise_bound {q : ℕ} (hq : 800 ≤ q)
    (hz : 4 ≤ sixteenthRoot q) {t : ℝ}
    (ht0 : majorRadius q ≤ |t|) (ht1 : |t| ≤ 1 / 2) :
    ‖geometricProduct q t‖ ≤
      Real.exp (-(sixteenthRoot q ^ 2) / 128000000) := by
  let z := sixteenthRoot q
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hz0 : 0 < z := sixteenthRoot_pos hq0
  have hη : 0 < majorRadius q := majorRadius_pos hq0
  have htpos : 0 < |t| := lt_of_lt_of_le hη ht0
  have henergy : z ^ 2 / 64000000 ≤ rotationEnergy q t := by
    by_cases hsmall : |t| ≤ 10 / (q : ℝ)
    · have hs := rotationEnergy_small q |t| hq (abs_nonneg t) hsmall
      rw [rotationEnergy_abs] at hs
      have ht_sq : majorRadius q ^ 2 ≤ |t| ^ 2 := by
        exact (pow_le_pow_left₀ (majorRadius_pos hq0).le ht0) 2
      have hscale : z ^ 2 = (q : ℝ) ^ 3 * majorRadius q ^ 2 := by
        rw [majorRadius_eq_inv_pow q hq0, ← sixteenthRoot_pow_sixteen q]
        change z ^ 2 = (z ^ 16) ^ 3 * (1 / z ^ 23) ^ 2
        field_simp
      rw [hscale]
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht_sq (by positivity)) (by norm_num)).trans hs
    · have hl := rotationEnergy_large q |t| (by omega) htpos
        (le_of_not_ge hsmall) ht1
      rw [rotationEnergy_abs] at hl
      have hz1 : 1 ≤ z := le_trans (by norm_num) hz
      have hzpow : z ^ 2 ≤ z ^ 16 := pow_le_pow_right₀ hz1 (by norm_num)
      have hqz : (q : ℝ) = z ^ 16 := (sixteenthRoot_pow_sixteen q).symm
      calc
        z ^ 2 / 64000000 ≤ z ^ 16 / 4096 := by
          nlinarith [sq_nonneg z]
        _ = (q : ℝ) / 4096 := by rw [hqz]
        _ ≤ rotationEnergy q t := hl
  calc
    ‖geometricProduct q t‖ ≤ Real.exp (-(rotationEnergy q t) / 2) :=
      centeredGeometricCF_prod_norm_le q t
    _ ≤ Real.exp (-(z ^ 2) / 128000000) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The two minor arcs together have length at most one, so the pointwise
decay gives the same bound after integration. -/
lemma outer_arc_integral_bound {q : ℕ} (hq : 800 ≤ q)
    (hz : 4 ≤ sixteenthRoot q) (a : ℤ) :
    ‖(∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          fourierPhase a t * geometricProduct q t) -
        ∫ t : ℝ in -(majorRadius q)..majorRadius q,
          fourierPhase a t * geometricProduct q t‖ ≤
      Real.exp (-(sixteenthRoot q ^ 2) / 128000000) := by
  let η := majorRadius q
  let C := Real.exp (-(sixteenthRoot q ^ 2) / 128000000)
  let F : ℝ → ℂ := fun t ↦ fourierPhase a t * geometricProduct q t
  have hq0 : 0 < q := by omega
  have hη : 0 < η := majorRadius_pos hq0
  have hz0 : 0 < sixteenthRoot q := sixteenthRoot_pos hq0
  have hηhalf : η ≤ 1 / 2 := by
    dsimp [η]
    rw [majorRadius_eq_inv_pow q hq0]
    have hz1 : 1 ≤ sixteenthRoot q := le_trans (by norm_num) hz
    have hzpow : sixteenthRoot q ≤ sixteenthRoot q ^ 23 := by
      simpa using pow_le_pow_right₀ hz1 (by norm_num : 1 ≤ 23)
    have hp : (4 : ℝ) ≤ sixteenthRoot q ^ 23 := hz.trans hzpow
    have hinv : 1 / sixteenthRoot q ^ 23 ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hp
    linarith
  have hF : Continuous F :=
    (continuous_fourierPhase a).mul (continuous_geometricProduct q)
  have hpoint {t : ℝ} (ht0 : η ≤ |t|) (ht1 : |t| ≤ 1 / 2) : ‖F t‖ ≤ C := by
    dsimp [F]
    rw [norm_mul, fourierPhase_norm, one_mul]
    exact outer_arc_pointwise_bound hq hz ht0 ht1
  have hleft : ‖∫ t : ℝ in (-1 / 2 : ℝ)..-η, F t‖ ≤ C * (1 / 2 - η) := by
    calc
      _ ≤ C * |-η - (-1 / 2 : ℝ)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        have ht' := Set.uIoc_subset_uIcc ht
        rw [Set.uIcc_of_le (by linarith : (-1 / 2 : ℝ) ≤ -η)] at ht'
        apply hpoint
        · have ht_nonpos : t ≤ 0 := ht'.2.trans (neg_nonpos.mpr hη.le)
          rw [abs_of_nonpos ht_nonpos]
          simpa using (neg_le_neg ht'.2)
        · have ht_nonpos : t ≤ 0 := ht'.2.trans (neg_nonpos.mpr hη.le)
          rw [abs_of_nonpos ht_nonpos]
          linarith [ht'.1]
      _ = C * (1 / 2 - η) := by
        congr 1
        rw [abs_of_nonneg (by linarith : 0 ≤ -η - (-1 / 2 : ℝ))]
        ring
  have hright : ‖∫ t : ℝ in η..(1 / 2 : ℝ), F t‖ ≤ C * (1 / 2 - η) := by
    calc
      _ ≤ C * |(1 / 2 : ℝ) - η| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        have ht' := Set.uIoc_subset_uIcc ht
        rw [Set.uIcc_of_le hηhalf] at ht'
        apply hpoint
        · rw [abs_of_nonneg (le_trans hη.le ht'.1)]
          exact ht'.1
        · rw [abs_of_nonneg (le_trans hη.le ht'.1)]
          exact ht'.2
      _ = C * (1 / 2 - η) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hηhalf)]
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable (-1 / 2 : ℝ) (-η))
    (hF.intervalIntegrable (-η) η)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hF.intervalIntegrable (-1 / 2 : ℝ) (-η)).trans
      (hF.intervalIntegrable (-η) η))
    (hF.intervalIntegrable η (1 / 2 : ℝ))
  change ‖(∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), F t) -
      ∫ t : ℝ in -η..η, F t‖ ≤ C
  calc
    ‖(∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), F t) -
        ∫ t : ℝ in -η..η, F t‖ =
      ‖(∫ t : ℝ in (-1 / 2 : ℝ)..-η, F t) +
        ∫ t : ℝ in η..(1 / 2 : ℝ), F t‖ := by
          rw [← hadd2, ← hadd1]
          congr 1
          ring
    _ ≤ ‖∫ t : ℝ in (-1 / 2 : ℝ)..-η, F t‖ +
        ‖∫ t : ℝ in η..(1 / 2 : ℝ), F t‖ := norm_add_le _ _
    _ ≤ C * (1 / 2 - η) + C * (1 / 2 - η) := add_le_add hleft hright
    _ ≤ C := by
      have hC : 0 ≤ C := Real.exp_nonneg _
      nlinarith

/-- The combined major-arc, Gaussian-tail, and minor-arc error. -/
noncomputable def analyticError (z : ℝ) : ℝ :=
  14000 / z ^ 28 + 2 * Real.exp (-(z ^ 2)) / z ^ 25 +
    Real.exp (-(z ^ 2) / 128000000)

lemma tendsto_scaled_analyticError :
    Tendsto (fun z : ℝ => analyticError z * z ^ 24) atTop (𝓝 0) := by
  have hp4 : Tendsto (fun z : ℝ => z ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have h1 : Tendsto (fun z : ℝ => 14000 / z ^ 4) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp4
  have hp2 : Tendsto (fun z : ℝ => z ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have he : Tendsto (fun z : ℝ => Real.exp (-(z ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp2)
  have hinv : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun z : ℝ => 2 * Real.exp (-(z ^ 2)) / z)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul he).mul hinv
  have hc : (0 : ℝ) < 1 / 128000000 := by positivity
  have h3' := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hc 24
  have h3at : Tendsto
      (fun z : ℝ => |z| ^ (24 : ℝ) *
        Real.exp (-(1 / 128000000) * z ^ 2)) atTop (𝓝 0) :=
    h3'.mono_left atTop_le_cocompact
  have h3 : Tendsto
      (fun z : ℝ => z ^ 24 * Real.exp (-(z ^ 2) / 128000000))
      atTop (𝓝 0) := by
    apply h3at.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    calc
      |z| ^ (24 : ℝ) * Real.exp (-(1 / 128000000) * z ^ 2) =
          z ^ 24 * Real.exp (-(1 / 128000000) * z ^ 2) := by
        rw [abs_of_pos hz]
        exact congrArg (fun w : ℝ ↦ w *
          Real.exp (-(1 / 128000000) * z ^ 2)) (Real.rpow_natCast z 24)
      _ = z ^ 24 * Real.exp (-(z ^ 2) / 128000000) := by
        congr 2
        ring
  have hsum := (h1.add h2).add h3
  simpa only [add_zero, zero_add] using hsum.congr' (by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with z hz
    dsimp [analyticError]
    field_simp)

lemma eventually_analyticError_le :
    ∀ᶠ z : ℝ in atTop,
      analyticError z ≤ Real.exp (-1600) / (16 * z ^ 24) := by
  have hc : 0 < Real.exp (-1600) / 16 := by positivity
  have hsmall := tendsto_scaled_analyticError.eventually (Iio_mem_nhds hc)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with z he hz
  have hzp : 0 < z ^ 24 := pow_pos hz _
  apply (le_div_iff₀ (mul_pos (by norm_num) hzp)).2
  have he' : analyticError z * z ^ 24 ≤ Real.exp (-1600) / 16 := he.le
  nlinarith [Real.exp_pos (-1600)]

lemma tendsto_sixteenthRoot : Tendsto sixteenthRoot atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp <| Real.tendsto_sqrt_atTop.comp <|
    Real.tendsto_sqrt_atTop.comp <| Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop

lemma eventually_local_limit_scales :
    ∀ᶠ q : ℕ in atTop,
      800 ≤ q ∧ 4 ≤ sixteenthRoot q ∧
        analyticError (sixteenthRoot q) ≤
          Real.exp (-1600) / (16 * sixteenthRoot q ^ 24) := by
  filter_upwards [eventually_ge_atTop (800 : ℕ),
    tendsto_sixteenthRoot.eventually (eventually_ge_atTop (4 : ℝ)),
    tendsto_sixteenthRoot.eventually eventually_analyticError_le] with q hq hz he
  exact ⟨hq, hz, he⟩

lemma fourier_integral_gaussian_error {q : ℕ} (hq : 800 ≤ q)
    (hz : 4 ≤ sixteenthRoot q) (a : ℤ) :
    ‖(∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          fourierPhase a t * geometricProduct q t) -
        ∫ t : ℝ, fourierPhase a t * Real.exp (-(quadraticSum q t))‖ ≤
      analyticError (sixteenthRoot q) := by
  let I := ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    fourierPhase a t * geometricProduct q t
  let P := ∫ t : ℝ in -(majorRadius q)..majorRadius q,
    fourierPhase a t * geometricProduct q t
  let T := ∫ t : ℝ in -(majorRadius q)..majorRadius q,
    fourierPhase a t * Real.exp (-(quadraticSum q t))
  let G := ∫ t : ℝ, fourierPhase a t * Real.exp (-(quadraticSum q t))
  have hout : ‖I - P‖ ≤
      Real.exp (-(sixteenthRoot q ^ 2) / 128000000) :=
    outer_arc_integral_bound hq hz a
  have hmajor : ‖P - T‖ ≤ 14000 / sixteenthRoot q ^ 28 :=
    major_arc_integral_error (by omega) hz a
  have htail : ‖G - T‖ ≤
      2 * Real.exp (-(sixteenthRoot q ^ 2)) / sixteenthRoot q ^ 25 :=
    gaussian_truncation_error (by omega) a
  have htail' : ‖T - G‖ ≤
      2 * Real.exp (-(sixteenthRoot q ^ 2)) / sixteenthRoot q ^ 25 := by
    rw [norm_sub_rev]
    exact htail
  change ‖I - G‖ ≤ analyticError (sixteenthRoot q)
  calc
    ‖I - G‖ = ‖(I - P) + (P - T) + (T - G)‖ := by congr 1; ring
    _ ≤ ‖I - P‖ + ‖P - T‖ + ‖T - G‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Real.exp (-(sixteenthRoot q ^ 2) / 128000000) +
        14000 / sixteenthRoot q ^ 28 +
        2 * Real.exp (-(sixteenthRoot q ^ 2)) /
          sixteenthRoot q ^ 25 := add_le_add (add_le_add hout hmajor) htail'
    _ = analyticError (sixteenthRoot q) := by
      simp [analyticError]
      ring

/-- Analytic local-limit lower bound, conditional only on the explicit
eventual error inequality. -/
lemma fourier_integral_lower {q : ℕ} (hq : 800 ≤ q)
    (hz : 4 ≤ sixteenthRoot q) (a : ℤ)
    (ha : |(a : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q)
    (herror : analyticError (sixteenthRoot q) ≤
      Real.exp (-1600) / (16 * sixteenthRoot q ^ 24)) :
    Real.exp (-1600) / (16 * sixteenthRoot q ^ 24) ≤
      (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        fourierPhase a t * geometricProduct q t).re := by
  let I := ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    fourierPhase a t * geometricProduct q t
  let G := ∫ t : ℝ, fourierPhase a t * Real.exp (-(quadraticSum q t))
  let g : ℝ := Real.sqrt (Real.pi / gaussianCoeff q) *
    Real.exp (-((2 * Real.pi * (a : ℝ)) ^ 2) / (4 * gaussianCoeff q))
  have hG : G = (g : ℂ) := integral_gaussian_model (by omega) a
  have hg : Real.exp (-1600) / (8 * sixteenthRoot q ^ 24) ≤ g :=
    gaussian_model_lower (by omega) a ha
  have herr : ‖I - G‖ ≤ analyticError (sixteenthRoot q) :=
    fourier_integral_gaussian_error hq hz a
  have hre : |I.re - G.re| ≤ ‖I - G‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  change Real.exp (-1600) / (16 * sixteenthRoot q ^ 24) ≤ I.re
  rw [hG] at hre herr
  norm_num at hre
  let m : ℝ := Real.exp (-1600) / (16 * sixteenthRoot q ^ 24)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hg' : 2 * m ≤ g := by
    dsimp [m]
    convert hg using 1 <;> ring
  have hnorm : ‖I - (g : ℂ)‖ ≤ m := herr.trans (herror.trans_eq rfl)
  have habs : |I.re - g| ≤ m := hre.trans hnorm
  have hdiff : g - I.re ≤ m := by
    exact (le_abs_self (g - I.re)).trans (by simpa [abs_sub_comm] using habs)
  change m ≤ I.re
  nlinarith

def centeredWeightedSum (q : ℕ) (g : Fin (q - 1) → ℕ) : ℤ :=
  ∑ i, (i.val + 1 : ℤ) * ((g i : ℤ) - 1)

noncomputable def geometricCharacter (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * x) * (((n : ℤ) : ℝ) - 1) : ℝ) * Complex.I)

lemma geometricCharacter_eq (x : ℝ) (n : ℕ) :
    geometricCharacter x n =
      Complex.exp (-(2 * Real.pi * x) * Complex.I) *
        Complex.exp ((2 * Real.pi * x) * Complex.I) ^ n := by
  rw [geometricCharacter]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fairGeometric_integral_geometricCharacter (x : ℝ) :
    ∫ n, geometricCharacter x n ∂fairGeometric = centeredGeometricCF x := by
  rw [fairGeometric, integral_geometricMeasure half_ne_zero]
  norm_num [half]
  rw [show (∑' n : ℕ, ((1 : ℂ) / 2) ^ n * ((1 : ℂ) / 2) * geometricCharacter x n) =
      ∑' n : ℕ, (Complex.exp (-(2 * Real.pi * x) * Complex.I) / 2) *
        (Complex.exp ((2 * Real.pi * x) * Complex.I) / 2) ^ n by
    congr 1
    funext n
    rw [geometricCharacter_eq]
    push_cast
    norm_num [div_pow]
    ring]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · rw [centeredGeometricCF]
    field_simp
  · rw [norm_div, Complex.norm_exp]
    norm_num

noncomputable def vectorCharacter (q : ℕ) (t : ℝ) (g : Fin (q - 1) → ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * t) * (centeredWeightedSum q g : ℝ) : ℝ) * Complex.I)

lemma vectorCharacter_eq_prod (q : ℕ) (t : ℝ) (g : Fin (q - 1) → ℕ) :
    vectorCharacter q t g =
      ∏ i, geometricCharacter (((i.val + 1 : ℕ) : ℝ) * t) (g i) := by
  rw [vectorCharacter, centeredWeightedSum]
  simp only [geometricCharacter]
  rw [← Complex.exp_sum Finset.univ]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma fin_prod_centeredGeometricCF_eq (q : ℕ) (t : ℝ) :
    (∏ i : Fin (q - 1), centeredGeometricCF (((i.val + 1 : ℕ) : ℝ) * t)) =
      geometricProduct q t := by
  rw [geometricProduct]
  classical
  by_cases hq : q = 0
  · subst q
    simp
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
  rw [Fin.prod_univ_eq_prod_range
    (fun i : ℕ ↦ centeredGeometricCF (((i + 1 : ℕ) : ℝ) * t)) (q - 1)]
  rw [Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  push_cast
  ring

lemma fairGeometricVector_integral_vectorCharacter (q : ℕ) (t : ℝ) :
    ∫ g, vectorCharacter q t g ∂fairGeometricVector (q - 1) = geometricProduct q t := by
  rw [show (fun g ↦ vectorCharacter q t g) =
      fun g ↦ ∏ i, geometricCharacter (((i.val + 1 : ℕ) : ℝ) * t) (g i) by
    funext g
    exact vectorCharacter_eq_prod q t g]
  rw [fairGeometricVector, integral_fintype_prod_eq_prod]
  simp_rw [fairGeometric_integral_geometricCharacter]
  exact fin_prod_centeredGeometricCF_eq q t

lemma integer_character_integral (k : ℤ) :
    (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
        if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num
  rw [if_neg hk]
  let c : ℂ := (2 * Real.pi * (k : ℝ)) * Complex.I
  have hc : c ≠ 0 := by
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hkreal)) Complex.I_ne_zero
  have hform : (fun t : ℝ ↦
      Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      fun t : ℝ ↦ Complex.exp (c * t) := by
    funext t
    dsimp [c]
    push_cast
    congr 1
    ring
  rw [hform, integral_exp_mul_complex hc]
  have hper : Complex.exp (c * (1 / 2 : ℝ)) =
      Complex.exp (c * (-1 / 2 : ℝ)) := by
    rw [← mul_one (Complex.exp (c * (-1 / 2 : ℝ))),
      ← Complex.exp_int_mul_two_pi_mul_I k, ← Complex.exp_add]
    congr 1
    dsimp [c]
    push_cast
    ring
  rw [hper]
  simp

lemma phase_mul_vectorCharacter (q : ℕ) (a : ℤ) (t : ℝ)
    (g : Fin (q - 1) → ℕ) :
    fourierPhase a t * vectorCharacter q t g =
      Complex.exp (((2 * Real.pi * ((centeredWeightedSum q g - a : ℤ) : ℝ) * t : ℝ) : ℂ) *
        Complex.I) := by
  rw [fourierPhase, vectorCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_mul_geometricProduct_eq_integral (q : ℕ) (a : ℤ) (t : ℝ) :
    fourierPhase a t * geometricProduct q t =
      ∫ g, fourierPhase a t * vectorCharacter q t g ∂fairGeometricVector (q - 1) := by
  rw [integral_const_mul, fairGeometricVector_integral_vectorCharacter]

lemma fourier_integrand_integrable (q : ℕ) (a : ℤ) :
    Integrable (Function.uncurry (fun t : ℝ ↦ fun g : Fin (q - 1) → ℕ ↦
      fourierPhase a t * vectorCharacter q t g))
      ((volume.restrict (Set.uIoc (-1 / 2 : ℝ) (1 / 2 : ℝ))).prod
        (fairGeometricVector (q - 1))) := by
  let : IsFiniteMeasure
      (volume.restrict (Set.uIoc (-1 / 2 : ℝ) (1 / 2 : ℝ))) := ⟨by
    simp [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]⟩
  let μ := (volume.restrict (Set.uIoc (-1 / 2 : ℝ) (1 / 2 : ℝ))).prod
    (fairGeometricVector (q - 1))
  have hfinite : IsFiniteMeasure μ := by infer_instance
  have hmeas : AEStronglyMeasurable (Function.uncurry
      (fun t : ℝ ↦ fun g : Fin (q - 1) → ℕ ↦
        fourierPhase a t * vectorCharacter q t g)) μ := by
    apply Measurable.aestronglyMeasurable
    rw [show Function.uncurry (fun t : ℝ ↦ fun g : Fin (q - 1) → ℕ ↦
        fourierPhase a t * vectorCharacter q t g) =
      fun z ↦ fourierPhase a z.1 * vectorCharacter q z.1 z.2 by rfl]
    unfold fourierPhase vectorCharacter
    fun_prop
  exact (integrable_const (μ := μ) (1 : ℂ)).mono hmeas (by
    filter_upwards [] with z
    rcases z with ⟨t, g⟩
    simp only [Function.uncurry, norm_one]
    rw [norm_mul, fourierPhase_norm]
    simp [vectorCharacter, Complex.norm_exp])

lemma fourier_inversion (q : ℕ) (a : ℤ) :
    (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      fourierPhase a t * geometricProduct q t) =
        ((fairGeometricVector (q - 1)).real
          {g | centeredWeightedSum q g = a} : ℂ) := by
  rw [show (fun t : ℝ ↦ fourierPhase a t * geometricProduct q t) =
      fun t : ℝ ↦ ∫ g, fourierPhase a t * vectorCharacter q t g
        ∂fairGeometricVector (q - 1) by
    funext t
    exact phase_mul_geometricProduct_eq_integral q a t]
  rw [intervalIntegral_integral_swap (fourier_integrand_integrable q a)]
  have hinner : ∀ g : Fin (q - 1) → ℕ,
      (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        fourierPhase a t * vectorCharacter q t g) =
          if centeredWeightedSum q g = a then 1 else 0 := by
    intro g
    rw [show (fun t : ℝ ↦ fourierPhase a t * vectorCharacter q t g) =
        fun t : ℝ ↦ Complex.exp
          (((2 * Real.pi * ((centeredWeightedSum q g - a : ℤ) : ℝ) * t : ℝ) : ℂ) *
            Complex.I) by
      funext t
      exact phase_mul_vectorCharacter q a t g]
    rw [integer_character_integral]
    simp only [sub_eq_zero]
  simp_rw [hinner]
  let s : Set (Fin (q - 1) → ℕ) := {g | centeredWeightedSum q g = a}
  have hs : MeasurableSet s := by
    exact MeasurableSet.of_discrete
  rw [show (fun g : Fin (q - 1) → ℕ ↦
      if centeredWeightedSum q g = a then (1 : ℂ) else 0) =
        s.indicator (fun _ ↦ (1 : ℂ)) by
    funext g
    by_cases h : centeredWeightedSum q g = a <;> simp [s, h]]
  rw [integral_indicator_const (1 : ℂ) hs]
  simp [s]

/-- Uniform lattice local limit for the centered weighted sum. -/
lemma eventually_centeredWeightedSum_probability_lower :
    ∀ᶠ q : ℕ in atTop, ∀ a : ℤ,
      |(a : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q →
        Real.exp (-1600) / (16 * sixteenthRoot q ^ 24) ≤
          (fairGeometricVector (q - 1)).real {g | centeredWeightedSum q g = a} := by
  filter_upwards [eventually_local_limit_scales] with q hq
  rcases hq with ⟨hq, hz, he⟩
  intro a ha
  have hlow := fourier_integral_lower hq hz a ha he
  rw [fourier_inversion q a] at hlow
  simpa using hlow



end LocalLimit

end Erdos358

open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace Erdos358.Global

noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
noncomputable def fairSetMeasure : Measure (Set ℕ) := setBernoulli Set.univ half

instance : IsProbabilityMeasure fairSetMeasure := by
  unfold fairSetMeasure
  infer_instance


lemma fairSetMeasure_cylinder {u s : Set ℕ} (hu : u.Finite) (hs : s ⊆ u) :
    fairSetMeasure.real {S | S ∩ u = s} = (1 / 2 : ℝ) ^ u.ncard := by
  classical
  rw [fairSetMeasure, measureReal_def, setBernoulli_apply']
  have hevent : ((fun p : ℕ → Prop ↦ {i | p i}) ⁻¹' {S | S ∩ u = s}) =
      MeasureTheory.cylinder hu.toFinset
        {v : ↥hu.toFinset → Prop | v = (fun i : ↥hu.toFinset ↦ (i : ℕ) ∈ s)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, MeasureTheory.cylinder,
      Set.mem_preimage]
    constructor
    · intro hset
      funext i
      apply propext
      have hiu : (i : ℕ) ∈ u := hu.mem_toFinset.mp i.property
      constructor
      · intro hpi
        have himem : (i : ℕ) ∈ {j | p j} ∩ u := ⟨hpi, hiu⟩
        rwa [hset] at himem
      · intro his
        have himem : (i : ℕ) ∈ {j | p j} ∩ u := by rwa [hset]
        exact himem.1
    · intro hfun
      ext i
      by_cases hiu : i ∈ u
      · have hi : i ∈ hu.toFinset := hu.mem_toFinset.mpr hiu
        have heq := congrFun hfun ⟨i, hi⟩
        change p i = (i ∈ s) at heq
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hiu, and_true]
        constructor
        · intro hpi
          rw [← heq]
          exact hpi
        · intro his
          rw [heq]
          exact his
      · have his : i ∉ s := fun his ↦ hiu (hs his)
        simp [hiu, his]
  rw [hevent]
  rw [show {v : ↥hu.toFinset → Prop | v = (fun i : ↥hu.toFinset ↦ (i : ℕ) ∈ s)} =
      {fun i : ↥hu.toFinset ↦ (i : ℕ) ∈ s} by ext; simp]
  let μ : ℕ → Measure Prop := fun i ↦
    unitInterval.toNNReal half • Measure.dirac (i ∈ Set.univ) +
      unitInterval.toNNReal (unitInterval.symm half) • Measure.dirac False
  have hcyl := Measure.infinitePi_cylinder μ
    (s := hu.toFinset) (S := ({fun i : ↥hu.toFinset ↦ (i : ℕ) ∈ s} :
      Set (↥hu.toFinset → Prop))) (MeasurableSet.singleton _)
  rw [hcyl]
  rw [show ({fun i : ↥hu.toFinset ↦ (i : ℕ) ∈ s} : Set (↥hu.toFinset → Prop)) =
      Set.univ.pi (fun i : ↥hu.toFinset ↦ ({((i : ℕ) ∈ s)} : Set Prop)) by
    ext v
    simp [funext_iff]]
  rw [Measure.pi_pi]
  have hcoord (i : ↥hu.toFinset) :
      ((μ i) {((i : ℕ) ∈ s)}).toReal = (1 / 2 : ℝ) := by
    dsimp [μ, half]
    by_cases hi : (i : ℕ) ∈ s <;> simp [hi] <;> norm_num
  rw [ENNReal.toReal_prod]
  simp_rw [hcoord]
  simpa [Set.ncard_eq_toFinset_card u hu]

def positiveGap {q : ℕ} (g : Fin (q - 1) → ℕ) (j : ℕ) : ℕ :=
  if h : j < q - 1 then g ⟨j, h⟩ + 1 else 0

def gapPoint {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) (i : Fin q) : ℕ :=
  m + ∑ j ∈ Finset.range i.val, positiveGap g j

def gapSpan {q : ℕ} (g : Fin (q - 1) → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (q - 1), positiveGap g j

noncomputable def gapPoints {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image (gapPoint m g)


lemma gapPoint_zero {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) (hq : 0 < q) :
    gapPoint m g ⟨0, hq⟩ = m := by simp [gapPoint]

lemma gapPoint_le_add_gapSpan {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ)
    (i : Fin q) : gapPoint m g i ≤ m + gapSpan g := by
  rw [gapPoint, gapSpan]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.le_pred_of_lt i.isLt)
  · intro j hj _
    exact Nat.zero_le _

lemma gapPoint_strictMono {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    StrictMono (gapPoint m g) := by
  intro i j hij
  rw [gapPoint, gapPoint]
  simp only [Nat.add_lt_add_iff_left]
  apply Finset.sum_lt_sum_of_subset (Finset.range_mono hij.le)
      (i := i.val)
  · simpa using hij
  · simp
  · have hiq : i.val < q - 1 := by omega
    simp [positiveGap, hiq]
  · intro x hx hxi
    exact Nat.zero_le _

lemma gapSpan_eq_finSum {q : ℕ} (g : Fin (q - 1) → ℕ) :
    gapSpan g = ∑ i, (g i + 1) := by
  rw [gapSpan, ← Fin.sum_univ_eq_sum_range (positiveGap g) (q - 1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [positiveGap, i.isLt]

lemma gapSpan_eq_card_add_sum {q : ℕ} (g : Fin (q - 1) → ℕ) :
    gapSpan g = q - 1 + ∑ i, g i := by
  rw [gapSpan_eq_finSum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

@[simp] lemma gapPoints_card {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    (gapPoints m g).card = q := by
  classical
  rw [gapPoints, Finset.card_image_of_injective _ (gapPoint_strictMono m g).injective]
  simp

lemma mem_gapPoints_iff {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) (x : ℕ) :
    x ∈ gapPoints m g ↔ ∃ i : Fin q, gapPoint m g i = x := by
  classical
  simp [gapPoints]

lemma gapPoints_subset_Icc {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    ↑(gapPoints m g) ⊆ Set.Icc m (m + gapSpan g) := by
  intro x hx
  change x ∈ gapPoints m g at hx
  rw [mem_gapPoints_iff] at hx
  rcases hx with ⟨i, rfl⟩
  exact ⟨Nat.le_add_right _ _, gapPoint_le_add_gapSpan m g i⟩

lemma gapPoint_last {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) (hq : 0 < q) :
    gapPoint m g ⟨q - 1, by omega⟩ = m + gapSpan g := by
  simp only [gapPoint, gapSpan]

def gapCylinder {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) : Set (Set ℕ) :=
  {S | S ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) = ↑(gapPoints m g)}

lemma measurableSet_gapCylinder {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    MeasurableSet (gapCylinder m g) := by
  classical
  let u := Finset.Icc m (m + gapSpan g)
  let s := gapPoints m g
  have hsu : (↑s : Set ℕ) ⊆ ↑u := by
    intro x hx
    change x ∈ Finset.Icc m (m + gapSpan g)
    rw [Finset.mem_Icc]
    exact gapPoints_subset_Icc m g hx
  have heq : gapCylinder m g =
      ⋂ x ∈ u, {S : Set ℕ | (x ∈ S) = (x ∈ s)} := by
    ext S
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h x hx
      change S ∩ (↑u : Set ℕ) = ↑s at h
      have hx' := Set.ext_iff.mp h x
      simp only [Set.mem_inter_iff, Finset.mem_coe, hx, and_true] at hx'
      exact propext hx'
    · intro h
      change S ∩ (↑u : Set ℕ) = ↑s
      ext x
      by_cases hx : x ∈ u
      · have hx' := h x hx
        simp only [Set.mem_inter_iff, Finset.mem_coe, hx, and_true]
        exact of_eq hx'
      · have hxs : x ∉ s := fun hxs ↦ hx (hsu hxs)
        simp [hx, hxs]
  rw [heq]
  apply Finset.measurableSet_biInter
  intro x hx
  exact measurableSet_eq_fun (measurable_set_mem x) measurable_const

lemma fairSetMeasure_gapCylinder {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    fairSetMeasure.real (gapCylinder m g) = (1 / 2 : ℝ) ^ (gapSpan g + 1) := by
  classical
  rw [gapCylinder]
  have hsub : (↑(gapPoints m g) : Set ℕ) ⊆
      ↑(Finset.Icc m (m + gapSpan g)) := by
    intro x hx
    have hx' := gapPoints_subset_Icc m g hx
    change x ∈ Finset.Icc m (m + gapSpan g)
    rw [Finset.mem_Icc]
    exact hx'
  rw [fairSetMeasure_cylinder (Set.toFinite _) hsub]
  congr 1
  rw [Set.ncard_coe_finset]
  simp only [Nat.card_Icc]
  omega

lemma fairGeometricVector_real_singleton (q : ℕ) (g : Fin q → ℕ) :
    (LocalLimit.fairGeometricVector q).real {g} =
      (1 / 2 : ℝ) ^ (q + ∑ i, g i) := by
  rw [measureReal_def, LocalLimit.fairGeometricVector_singleton]
  rw [ENNReal.toReal_prod]
  simp_rw [← measureReal_def, LocalLimit.fairGeometric_real_singleton]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

lemma fairSetMeasure_gapCylinder_eq_geometric {q : ℕ} (m : ℕ)
    (g : Fin (q - 1) → ℕ) :
    fairSetMeasure.real (gapCylinder m g) =
      (1 / 2 : ℝ) * (LocalLimit.fairGeometricVector (q - 1)).real {g} := by
  rw [fairSetMeasure_gapCylinder, fairGeometricVector_real_singleton,
    gapSpan_eq_card_add_sum]
  rw [pow_succ']

lemma strictMono_eq_of_image_univ_eq {n : ℕ} {u v : Fin n → ℕ}
    (hu : StrictMono u) (hv : StrictMono v)
    (himage : Finset.univ.image u = Finset.univ.image v) : u = v := by
  funext i
  have hpoint : ∀ k (hk : k < n), u ⟨k, hk⟩ = v ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let ik : Fin n := ⟨k, hk⟩
      apply le_antisymm
      · by_contra hle
        have hlt : v ik < u ik := Nat.lt_of_not_ge hle
        have hvmem : v ik ∈ Finset.univ.image u := by
          rw [himage]
          simp
        rw [Finset.mem_image] at hvmem
        rcases hvmem with ⟨j, _, hj⟩
        have hjik : j < ik := (hu.lt_iff_lt).mp (by simpa [hj] using hlt)
        have hprev := ih j.val hjik j.isLt
        change u j = v j at hprev
        have heq : v j = v ik := by rw [← hprev, hj]
        exact (Fin.ne_of_lt hjik) (hv.injective heq)
      · by_contra hle
        have hlt : u ik < v ik := Nat.lt_of_not_ge hle
        have humem : u ik ∈ Finset.univ.image v := by
          rw [← himage]
          simp
        rw [Finset.mem_image] at humem
        rcases humem with ⟨j, _, hj⟩
        have hjik : j < ik := (hv.lt_iff_lt).mp (by simpa [hj] using hlt)
        have hprev := ih j.val hjik j.isLt
        change u j = v j at hprev
        have heq : u j = u ik := by rw [hprev, hj]
        exact (Fin.ne_of_lt hjik) (hu.injective heq)
  exact hpoint i.val i.isLt

lemma gapPoint_succ {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ)
    (i : Fin (q - 1)) :
    gapPoint m g ⟨i.val + 1, by omega⟩ =
      gapPoint m g ⟨i.val, by omega⟩ + g i + 1 := by
  rw [gapPoint, gapPoint, Finset.sum_range_succ]
  simp [positiveGap, i.isLt]
  omega

lemma gapPoints_injective {q : ℕ} (m : ℕ) :
    Function.Injective (gapPoints (q := q) m) := by
  intro g h hgh
  have hpoint : gapPoint m g = gapPoint m h :=
    strictMono_eq_of_image_univ_eq (gapPoint_strictMono m g)
      (gapPoint_strictMono m h) (by simpa [gapPoints] using hgh)
  funext i
  have h0 := congrFun hpoint (⟨i.val, by omega⟩ : Fin q)
  have h1 := congrFun hpoint (⟨i.val + 1, by omega⟩ : Fin q)
  rw [gapPoint_succ m g i, gapPoint_succ m h i] at h1
  omega

lemma gapPoints_subset_of_mem_gapCylinders {q : ℕ} {m : ℕ}
    {g h : Fin (q - 1) → ℕ} {S : Set ℕ}
    (hspan : gapSpan g ≤ gapSpan h)
    (hg : S ∈ gapCylinder m g) (hh : S ∈ gapCylinder m h) :
    gapPoints m g ⊆ gapPoints m h := by
  classical
  intro x hx
  change S ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) =
    ↑(gapPoints m g) at hg
  change S ∩ (↑(Finset.Icc m (m + gapSpan h)) : Set ℕ) =
    ↑(gapPoints m h) at hh
  have hxsmall : x ∈ S ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) := by
    rw [hg]
    exact hx
  have hxlarge : x ∈ S ∩ (↑(Finset.Icc m (m + gapSpan h)) : Set ℕ) := by
    refine ⟨hxsmall.1, ?_⟩
    change x ∈ Finset.Icc m (m + gapSpan h)
    rw [Finset.mem_Icc]
    have hxsmall' : x ∈ Finset.Icc m (m + gapSpan g) := hxsmall.2
    rw [Finset.mem_Icc] at hxsmall'
    omega
  rw [hh] at hxlarge
  exact hxlarge

lemma gapCylinder_disjoint {q : ℕ} {m : ℕ} (hq : 0 < q)
    {g h : Fin (q - 1) → ℕ} (hgh : g ≠ h) :
    Disjoint (gapCylinder m g) (gapCylinder m h) := by
  rw [Set.disjoint_left]
  intro S hg hh
  apply hgh
  apply gapPoints_injective m
  by_cases hspan : gapSpan g ≤ gapSpan h
  · exact Finset.eq_of_subset_of_card_le
      (gapPoints_subset_of_mem_gapCylinders hspan hg hh) (by simp)
  · exact (Finset.eq_of_subset_of_card_le
      (gapPoints_subset_of_mem_gapCylinders (Nat.le_of_not_ge hspan) hh hg) (by simp)).symm

noncomputable def boundedGapVectors (q B : ℕ) : Finset (Fin (q - 1) → ℕ) := by
  classical
  exact (Finset.univ.image (fun g : Fin (q - 1) → Fin (B + 1) ↦
    fun i ↦ (g i : ℕ))).filter (fun g ↦ gapSpan g ≤ B)

lemma mem_boundedGapVectors_iff {q B : ℕ} {g : Fin (q - 1) → ℕ} :
    g ∈ boundedGapVectors q B ↔ gapSpan g ≤ B := by
  classical
  constructor
  · intro hg
    exact (Finset.mem_filter.mp hg).2
  · intro hspan
    rw [boundedGapVectors, Finset.mem_filter]
    refine ⟨?_, hspan⟩
    rw [Finset.mem_image]
    let h : Fin (q - 1) → Fin (B + 1) := fun i ↦ ⟨g i, by
      have hgi : g i + 1 ≤ gapSpan g := by
        rw [gapSpan_eq_finSum]
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (g j + 1))
          (Finset.mem_univ i)
      omega⟩
    refine ⟨h, Finset.mem_univ _, ?_⟩
    funext i
    rfl

lemma fairSetMeasure_iUnion_gapCylinder {q m : ℕ} (hq : 0 < q)
    (e : Finset (Fin (q - 1) → ℕ)) :
    fairSetMeasure.real (⋃ g ∈ e, gapCylinder m g) =
      (1 / 2 : ℝ) * (LocalLimit.fairGeometricVector (q - 1)).real (↑e : Set _) := by
  rw [measureReal_biUnion_finset]
  · simp_rw [fairSetMeasure_gapCylinder_eq_geometric]
    rw [← Finset.mul_sum, sum_measureReal_singleton]
  · intro g hg h hh hne
    exact gapCylinder_disjoint hq hne
  · intro g hg
    exact measurableSet_gapCylinder m g

noncomputable def gapMomentCoord (n : ℕ) : ℝ := (4 / 3 : ℝ) ^ n

lemma integrable_gapMomentCoord :
    Integrable gapMomentCoord LocalLimit.fairGeometric := by
  rw [LocalLimit.fairGeometric]
  apply (integrable_geometricMeasure_iff LocalLimit.half_ne_zero).2
  have hs : Summable (fun n : ℕ ↦ (2 / 3 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hs' := Summable.mul_left (1 / 2 : ℝ) hs
  have heq : (fun n : ℕ ↦
      (1 - (LocalLimit.half : ℝ)) ^ n * (LocalLimit.half : ℝ) *
        ‖gapMomentCoord n‖) =
      fun n : ℕ ↦ (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ n := by
    funext n
    rw [gapMomentCoord, Real.norm_eq_abs, abs_pow,
      abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num [LocalLimit.half]
    calc
      (1 / 2 : ℝ) ^ n * (1 / 2) * (4 / 3) ^ n =
          (1 / 2) * ((1 / 2) ^ n * (4 / 3) ^ n) := by ring
      _ = (1 / 2) * (2 / 3) ^ n := by rw [← mul_pow]; norm_num
  rw [heq]
  exact hs'

lemma integral_gapMomentCoord :
    ∫ n, gapMomentCoord n ∂LocalLimit.fairGeometric = (3 / 2 : ℝ) := by
  rw [LocalLimit.fairGeometric,
    integral_geometricMeasure LocalLimit.half_ne_zero]
  norm_num [LocalLimit.half, gapMomentCoord]
  rw [show (∑' n : ℕ, (1 / 2 : ℝ) ^ n * (1 / 2) * (4 / 3) ^ n) =
      (1 / 2 : ℝ) * ∑' n : ℕ, (2 / 3 : ℝ) ^ n by
    rw [← tsum_mul_left]
    congr 1
    funext n
    calc
      (1 / 2 : ℝ) ^ n * (1 / 2) * (4 / 3) ^ n =
          (1 / 2) * ((1 / 2) ^ n * (4 / 3) ^ n) := by ring
      _ = (1 / 2) * (2 / 3) ^ n := by rw [← mul_pow]; norm_num]
  rw [tsum_geometric_of_norm_lt_one (by norm_num)]
  norm_num

noncomputable def gapMoment {q : ℕ} (g : Fin (q - 1) → ℕ) : ℝ :=
  ∏ i, gapMomentCoord (g i)

lemma gapMoment_eq_pow_sum {q : ℕ} (g : Fin (q - 1) → ℕ) :
    gapMoment g = (4 / 3 : ℝ) ^ ∑ i, g i := by
  unfold gapMoment gapMomentCoord
  rw [Finset.prod_pow_eq_pow_sum]

lemma integrable_gapMoment (q : ℕ) :
    Integrable (gapMoment (q := q)) (LocalLimit.fairGeometricVector (q - 1)) := by
  unfold gapMoment
  rw [LocalLimit.fairGeometricVector]
  exact Integrable.fintype_prod (fun _ ↦ integrable_gapMomentCoord)

lemma integral_gapMoment (q : ℕ) :
    ∫ g, gapMoment g ∂LocalLimit.fairGeometricVector (q - 1) =
      (3 / 2 : ℝ) ^ (q - 1) := by
  unfold gapMoment
  rw [LocalLimit.fairGeometricVector, integral_fintype_prod_eq_prod]
  simp_rw [integral_gapMomentCoord]
  rw [Finset.prod_const]
  congr 1
  simp only [Finset.card_univ, Fintype.card_fin]

lemma gapMoment_nonneg {q : ℕ} (g : Fin (q - 1) → ℕ) : 0 ≤ gapMoment g := by
  rw [gapMoment_eq_pow_sum]
  positivity

lemma gapMoment_lower_of_gapSpan_gt {q : ℕ} (g : Fin (q - 1) → ℕ)
    (hspan : 4 * q < gapSpan g) :
    (4 / 3 : ℝ) ^ (3 * q) ≤ gapMoment g := by
  rw [gapMoment_eq_pow_sum]
  have hexp : 3 * q ≤ ∑ i, g i := by
    rw [gapSpan_eq_card_add_sum] at hspan
    omega
  exact pow_le_pow_right₀ (by norm_num) hexp

lemma moment_ratio_le (q : ℕ) :
    (3 / 2 : ℝ) ^ (q - 1) / (4 / 3 : ℝ) ^ (3 * q) ≤
      (81 / 128 : ℝ) ^ q := by
  cases q with
  | zero => norm_num
  | succ r =>
      rw [Nat.succ_sub_one]
      have hpow : 0 ≤ (81 / 128 : ℝ) ^ (r + 1) := by positivity
      have hcore :
          (3 / 2 : ℝ) ^ r / (4 / 3 : ℝ) ^ (3 * r) =
            (81 / 128 : ℝ) ^ r := by
        rw [show (4 / 3 : ℝ) ^ (3 * r) = ((4 / 3 : ℝ) ^ 3) ^ r by
          rw [← pow_mul]]
        rw [← div_pow]
        congr 1
        norm_num
      calc
        (3 / 2 : ℝ) ^ r / (4 / 3 : ℝ) ^ (3 * (r + 1)) =
            ((3 / 2 : ℝ) ^ r / (4 / 3 : ℝ) ^ (3 * r)) /
              (4 / 3 : ℝ) ^ 3 := by
          rw [show 3 * (r + 1) = 3 * r + 3 by omega, pow_add]
          field_simp
        _ = (2 / 3 : ℝ) * (81 / 128 : ℝ) ^ (r + 1) := by
          rw [hcore, pow_succ]
          norm_num
          ring
        _ ≤ (81 / 128 : ℝ) ^ (r + 1) := by nlinarith

lemma fairGeometricVector_gapSpan_tail (q : ℕ) :
    (LocalLimit.fairGeometricVector (q - 1)).real
        {g | 4 * q < gapSpan g} ≤ (81 / 128 : ℝ) ^ q := by
  let μ := LocalLimit.fairGeometricVector (q - 1)
  let c : ℝ := (4 / 3 : ℝ) ^ (3 * q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmeas : Measurable (fun g : Fin (q - 1) → ℕ ↦
      ENNReal.ofReal (gapMoment g)) := Measurable.of_discrete
  have hmarkov := mul_meas_ge_le_lintegral (μ := μ) hmeas (ENNReal.ofReal c)
  have hlin : (∫⁻ g, ENNReal.ofReal (gapMoment g) ∂μ) =
      ENNReal.ofReal ((3 / 2 : ℝ) ^ (q - 1)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gapMoment q)
      (Filter.Eventually.of_forall gapMoment_nonneg), integral_gapMoment]
  rw [hlin] at hmarkov
  have hsub : {g : Fin (q - 1) → ℕ | 4 * q < gapSpan g} ⊆
      {g | ENNReal.ofReal c ≤ ENNReal.ofReal (gapMoment g)} := by
    intro g hg
    exact ENNReal.ofReal_le_ofReal (gapMoment_lower_of_gapSpan_gt g hg)
  have hENN : ENNReal.ofReal c * μ {g | 4 * q < gapSpan g} ≤
      ENNReal.ofReal ((3 / 2 : ℝ) ^ (q - 1)) :=
    (by
      calc
        ENNReal.ofReal c * μ {g | 4 * q < gapSpan g} ≤
            ENNReal.ofReal c * μ {g | ENNReal.ofReal c ≤ ENNReal.ofReal (gapMoment g)} := by
          gcongr
        _ ≤ _ := hmarkov)
  have hreal := ENNReal.toReal_mono (by simp) hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ← measureReal_def,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  calc
    μ.real {g | 4 * q < gapSpan g} ≤
        (3 / 2 : ℝ) ^ (q - 1) / (4 / 3 : ℝ) ^ (3 * q) := by
      apply (le_div_iff₀ (by dsimp [c] at hreal ⊢; positivity)).2
      simpa [c, mul_comm] using hreal
    _ ≤ (81 / 128 : ℝ) ^ q := moment_ratio_le q

noncomputable def goodGapVectors (q : ℕ) (a : ℤ) :
    Finset (Fin (q - 1) → ℕ) :=
  (boundedGapVectors q (4 * q)).filter
    (fun g ↦ LocalLimit.centeredWeightedSum q g = a)

lemma mem_goodGapVectors_iff {q : ℕ} {a : ℤ} {g : Fin (q - 1) → ℕ} :
    g ∈ goodGapVectors q a ↔
      gapSpan g ≤ 4 * q ∧ LocalLimit.centeredWeightedSum q g = a := by
  classical
  simp [goodGapVectors, mem_boundedGapVectors_iff]

lemma goodGapVectors_probability_lower (q : ℕ) (a : ℤ) :
    (LocalLimit.fairGeometricVector (q - 1)).real
        {g | LocalLimit.centeredWeightedSum q g = a} - (81 / 128 : ℝ) ^ q ≤
      (LocalLimit.fairGeometricVector (q - 1)).real
        (↑(goodGapVectors q a) : Set _) := by
  let μ := LocalLimit.fairGeometricVector (q - 1)
  let E : Set (Fin (q - 1) → ℕ) :=
    {g | LocalLimit.centeredWeightedSum q g = a}
  let G : Set (Fin (q - 1) → ℕ) := ↑(goodGapVectors q a)
  let T : Set (Fin (q - 1) → ℕ) := {g | 4 * q < gapSpan g}
  have hsub : E ⊆ G ∪ T := by
    intro g hg
    by_cases hspan : gapSpan g ≤ 4 * q
    · left
      exact mem_goodGapVectors_iff.mpr ⟨hspan, hg⟩
    · right
      exact Nat.lt_of_not_ge hspan
  have hmono : μ.real E ≤ μ.real (G ∪ T) :=
    measureReal_mono hsub (by finiteness)
  have hunion : μ.real (G ∪ T) ≤ μ.real G + μ.real T := measureReal_union_le G T
  have htail : μ.real T ≤ (81 / 128 : ℝ) ^ q :=
    fairGeometricVector_gapSpan_tail q
  dsimp [E, G, T] at hmono hunion htail ⊢
  linarith

lemma sixteenthRoot_pow_twentyfour_le_sq {q : ℕ} (hq : 1 ≤ q) :
    LocalLimit.sixteenthRoot q ^ 24 ≤ (q : ℝ) ^ 2 := by
  rw [show 24 = 16 + 8 by omega, pow_add,
    LocalLimit.sixteenthRoot_pow_sixteen,
    ← LocalLimit.sqrt_nat_eq_sixteenthRoot_pow_eight]
  have hsqrt : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hq))
  nlinarith [show (0 : ℝ) ≤ q by positivity]

lemma eventually_gap_tail_le_local_half :
    ∀ᶠ q : ℕ in atTop,
      (81 / 128 : ℝ) ^ q ≤
        Real.exp (-1600) / (32 * LocalLimit.sixteenthRoot q ^ 24) := by
  have hlim : Tendsto
      (fun q : ℕ ↦ 32 * (q : ℝ) ^ 2 * (81 / 128 : ℝ) ^ q)
      atTop (𝓝 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
      (r := (81 / 128 : ℝ)) (by norm_num)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.const_mul 32
  have hsmall : ∀ᶠ q : ℕ in atTop,
      32 * (q : ℝ) ^ 2 * (81 / 128 : ℝ) ^ q < Real.exp (-1600) :=
    hlim.eventually (Iio_mem_nhds (Real.exp_pos _))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with q hqsmall hq
  have hzpos : 0 < LocalLimit.sixteenthRoot q :=
    LocalLimit.sixteenthRoot_pos (by omega)
  apply (le_div_iff₀ (by positivity)).2
  calc
    (81 / 128 : ℝ) ^ q * (32 * LocalLimit.sixteenthRoot q ^ 24) ≤
        (81 / 128 : ℝ) ^ q * (32 * (q : ℝ) ^ 2) := by
      gcongr
      exact sixteenthRoot_pow_twentyfour_le_sq hq
    _ = 32 * (q : ℝ) ^ 2 * (81 / 128 : ℝ) ^ q := by ring
    _ ≤ Real.exp (-1600) := hqsmall.le

lemma eventually_goodGapVectors_probability_lower :
    ∀ᶠ q : ℕ in atTop, ∀ a : ℤ,
      |(a : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q →
      Real.exp (-1600) / (32 * LocalLimit.sixteenthRoot q ^ 24) ≤
        (LocalLimit.fairGeometricVector (q - 1)).real
          (↑(goodGapVectors q a) : Set _) := by
  filter_upwards [LocalLimit.eventually_centeredWeightedSum_probability_lower,
    eventually_gap_tail_le_local_half] with q hlocal htail
  intro a ha
  have hgood := goodGapVectors_probability_lower q a
  have hloc := hlocal a ha
  have hhalf : Real.exp (-1600) / (16 * LocalLimit.sixteenthRoot q ^ 24) =
      2 * (Real.exp (-1600) / (32 * LocalLimit.sixteenthRoot q ^ 24)) := by ring
  rw [hhalf] at hloc
  linarith

lemma sum_prefix_sums (q : ℕ) (h : ℕ → ℕ) :
    (∑ i ∈ Finset.range q, ∑ j ∈ Finset.range i, h j) =
      ∑ j ∈ Finset.range q, (q - 1 - j) * h j := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hjq : j < q := Finset.mem_range.mp hj
      calc
        (q - 1 - j) * h j + h j = ((q - 1 - j) + 1) * h j := by
          rw [Nat.add_mul, one_mul]
        _ = (q - j) * h j := by congr 1; omega

lemma sum_gapPoints {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    ∑ x ∈ gapPoints m g, x =
      q * m + ∑ j ∈ Finset.range q, (q - 1 - j) * positiveGap g j := by
  classical
  rw [gapPoints, Finset.sum_image]
  · change Finset.sum Finset.univ
      (fun i : Fin q ↦ m + Finset.sum (Finset.range i.val) (positiveGap g)) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ m + ∑ j ∈ Finset.range i, positiveGap g j) q]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sum_prefix_sums]
    rw [Nat.cast_id]
  · exact (gapPoint_strictMono m g).injective.injOn

def actualCenteredWeightedSum (q : ℕ) (g : Fin (q - 1) → ℕ) : ℤ :=
  ∑ i, ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) - 1)

def actualWeightedPositiveGap (q : ℕ) (g : Fin (q - 1) → ℕ) : ℕ :=
  ∑ i, (q - 1 - i.val) * (g i + 1)

lemma range_weighted_positiveGap_eq {q : ℕ} (g : Fin (q - 1) → ℕ) :
    (∑ j ∈ Finset.range q, (q - 1 - j) * positiveGap g j) =
      actualWeightedPositiveGap q g := by
  cases q with
  | zero => simp [actualWeightedPositiveGap]
  | succ n =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, add_zero]
      rw [actualWeightedPositiveGap]
      simp only [Nat.add_sub_cancel]
      calc
        (∑ j ∈ Finset.range n, (n - j) * positiveGap g j) =
            Finset.univ.sum (fun i : Fin n ↦
              (n - i.val) * positiveGap g i.val) := by
          exact (Fin.sum_univ_eq_sum_range
            (fun j : ℕ ↦ (n - j) * positiveGap g j) n).symm
        _ = Finset.univ.sum (fun i : Fin n ↦ (n - i.val) * (g i + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [positiveGap, i.isLt]

lemma sum_gapPoints_eq_weighted {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    ∑ x ∈ gapPoints m g, x = q * m + actualWeightedPositiveGap q g := by
  rw [sum_gapPoints, range_weighted_positiveGap_eq]

lemma two_mul_sum_descending_weights (q : ℕ) :
    2 * Finset.univ.sum (fun i : Fin (q - 1) ↦ q - 1 - i.val) =
      q * (q - 1) := by
  cases q with
  | zero => simp
  | succ n =>
      simp only [Nat.add_sub_cancel]
      change 2 * Finset.univ.sum (fun i : Fin n ↦ n - i.val) =
        (n + 1) * n
      have hfin : Finset.univ.sum (fun i : Fin n ↦ n - i.val) =
          (Finset.range n).sum (fun j ↦ n - j) := by
        exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ n - j) n
      rw [hfin]
      have hsum : (Finset.range n).sum (fun j ↦ n - j) =
          (Finset.range n).sum (fun j ↦ j) + n := by
        calc
          (Finset.range n).sum (fun j ↦ n - j) =
              (Finset.range n).sum (fun j ↦ (n - 1 - j) + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjn : j < n := Finset.mem_range.mp hj
            omega
          _ = (Finset.range n).sum (fun j ↦ n - 1 - j) + n := by
            rw [Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            simp
          _ = (Finset.range n).sum (fun j ↦ j) + n := by
            congr 1
            exact Finset.sum_range_reflect (fun j : ℕ ↦ j) n
      rw [hsum, Nat.mul_add]
      rw [Nat.mul_comm 2 ((Finset.range n).sum (fun j ↦ j)),
        Finset.sum_range_id_mul_two]
      cases n <;> simp <;> ring

lemma actualWeightedPositiveGap_int (q : ℕ) (g : Fin (q - 1) → ℕ) :
    (actualWeightedPositiveGap q g : ℤ) =
      (q * (q - 1) : ℕ) + actualCenteredWeightedSum q g := by
  rw [actualWeightedPositiveGap, actualCenteredWeightedSum]
  push_cast
  have hweights := congrArg ((↑·) : ℕ → ℤ) (two_mul_sum_descending_weights q)
  push_cast at hweights
  change Finset.univ.sum (fun i : Fin (q - 1) ↦
      ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) + 1)) =
    (q : ℤ) * ((q - 1 : ℕ) : ℤ) +
      Finset.univ.sum (fun i : Fin (q - 1) ↦
        ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) - 1))
  calc
    Finset.univ.sum (fun i : Fin (q - 1) ↦
        ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) + 1)) =
        Finset.univ.sum (fun i : Fin (q - 1) ↦
          ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) - 1) +
            2 * ((q - 1 - i.val : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = Finset.univ.sum (fun i : Fin (q - 1) ↦
          ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) - 1)) +
        2 * Finset.univ.sum (fun i : Fin (q - 1) ↦
          ((q - 1 - i.val : ℕ) : ℤ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (q : ℤ) * ((q - 1 : ℕ) : ℤ) +
        Finset.univ.sum (fun i : Fin (q - 1) ↦
          ((q - 1 - i.val : ℕ) : ℤ) * ((g i : ℤ) - 1)) := by
      rw [hweights]
      ring

def reverseGap {q : ℕ} (g : Fin (q - 1) → ℕ) : Fin (q - 1) → ℕ :=
  fun i ↦ g i.rev

lemma reverseGap_involutive {q : ℕ} :
    Function.Involutive (reverseGap (q := q)) := by
  intro g
  funext i
  simp [reverseGap]

lemma reverseGap_injective {q : ℕ} :
    Function.Injective (reverseGap (q := q)) := reverseGap_involutive.injective

lemma gapSpan_reverseGap {q : ℕ} (g : Fin (q - 1) → ℕ) :
    gapSpan (reverseGap g) = gapSpan g := by
  rw [gapSpan_eq_finSum, gapSpan_eq_finSum]
  exact Equiv.sum_comp Fin.revPerm (fun i ↦ g i + 1)

lemma actualCenteredWeightedSum_reverseGap {q : ℕ} (g : Fin (q - 1) → ℕ) :
    actualCenteredWeightedSum q (reverseGap g) =
      LocalLimit.centeredWeightedSum q g := by
  rw [actualCenteredWeightedSum, LocalLimit.centeredWeightedSum]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  apply Fintype.sum_congr
  intro i
  simp only [Fin.revPerm_apply, reverseGap, Fin.rev_rev]
  congr 2
  rw [Fin.val_rev]
  push_cast
  omega

lemma sum_gapPoints_int {q : ℕ} (m : ℕ) (g : Fin (q - 1) → ℕ) :
    ((∑ x ∈ gapPoints m g, x : ℕ) : ℤ) =
      (q : ℤ) * (m : ℤ) + (q : ℤ) * ((q - 1 : ℕ) : ℤ) +
        actualCenteredWeightedSum q g := by
  rw [sum_gapPoints_eq_weighted]
  push_cast
  rw [actualWeightedPositiveGap_int]
  push_cast
  ring

lemma sum_gapPoints_reverseGap {q m n : ℕ} (g : Fin (q - 1) → ℕ)
    (hcenter : LocalLimit.centeredWeightedSum q g =
      (n : ℤ) - (q : ℤ) * (m : ℤ) - (q : ℤ) * ((q - 1 : ℕ) : ℤ)) :
    ∑ x ∈ gapPoints m (reverseGap g), x = n := by
  have hz : ((∑ x ∈ gapPoints m (reverseGap g), x : ℕ) : ℤ) = (n : ℤ) := by
    rw [sum_gapPoints_int, actualCenteredWeightedSum_reverseGap, hcenter]
    ring
  exact_mod_cast hz

noncomputable def reverseGoodGapVectors (q : ℕ) (a : ℤ) :
    Finset (Fin (q - 1) → ℕ) := by
  classical
  exact (goodGapVectors q a).image reverseGap

lemma mem_reverseGoodGapVectors_iff {q : ℕ} {a : ℤ}
    {g : Fin (q - 1) → ℕ} :
    g ∈ reverseGoodGapVectors q a ↔
      gapSpan g ≤ 4 * q ∧ actualCenteredWeightedSum q g = a := by
  classical
  rw [reverseGoodGapVectors, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [gapSpan_reverseGap, actualCenteredWeightedSum_reverseGap]
    exact mem_goodGapVectors_iff.mp hh
  · intro hg
    refine ⟨reverseGap g, ?_, reverseGap_involutive g⟩
    rw [mem_goodGapVectors_iff, gapSpan_reverseGap]
    refine ⟨hg.1, ?_⟩
    rw [← actualCenteredWeightedSum_reverseGap, reverseGap_involutive]
    exact hg.2

lemma sum_reverseGap {q : ℕ} (g : Fin (q - 1) → ℕ) :
    ∑ i, reverseGap g i = ∑ i, g i := by
  exact Equiv.sum_comp Fin.revPerm g

lemma fairGeometricVector_reverseGap_singleton {q : ℕ}
    (g : Fin (q - 1) → ℕ) :
    (LocalLimit.fairGeometricVector (q - 1)).real {reverseGap g} =
      (LocalLimit.fairGeometricVector (q - 1)).real {g} := by
  rw [fairGeometricVector_real_singleton,
    fairGeometricVector_real_singleton, sum_reverseGap]

lemma reverseGoodGapVectors_probability {q : ℕ} {a : ℤ} :
    (LocalLimit.fairGeometricVector (q - 1)).real
        (↑(reverseGoodGapVectors q a) : Set _) =
      (LocalLimit.fairGeometricVector (q - 1)).real
        (↑(goodGapVectors q a) : Set _) := by
  classical
  rw [reverseGoodGapVectors, ← sum_measureReal_singleton,
    Finset.sum_image (reverseGap_injective.injOn)]
  simp_rw [fairGeometricVector_reverseGap_singleton]
  exact sum_measureReal_singleton
    (μ := LocalLimit.fairGeometricVector (q - 1)) (goodGapVectors q a)

lemma eventually_reverseGoodGapVectors_probability_lower :
    ∀ᶠ q : ℕ in atTop, ∀ a : ℤ,
      |(a : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q →
      Real.exp (-1600) / (32 * LocalLimit.sixteenthRoot q ^ 24) ≤
        (LocalLimit.fairGeometricVector (q - 1)).real
          (↑(reverseGoodGapVectors q a) : Set _) := by
  filter_upwards [eventually_goodGapVectors_probability_lower] with q hq
  intro a ha
  rw [reverseGoodGapVectors_probability]
  exact hq a ha

/-- The centered value required of a gap vector so that a `q`-point run beginning
at `m` has sum `n`. -/
def targetCenter (q m n : ℕ) : ℤ :=
  (n : ℤ) - (q : ℤ) * (m : ℤ) - (q : ℤ) * ((q - 1 : ℕ) : ℤ)

/-- The finite union of Bernoulli cylinders which realize `n` from `q` selected
points beginning at `m`, with total span at most `4q`. -/
noncomputable def fixedStartEvent (q m n : ℕ) : Set (Set ℕ) :=
  ⋃ g ∈ reverseGoodGapVectors q (targetCenter q m n), gapCylinder m g

lemma measurableSet_fixedStartEvent (q m n : ℕ) :
    MeasurableSet (fixedStartEvent q m n) := by
  classical
  exact Finset.measurableSet_biUnion _ (fun g _ ↦ measurableSet_gapCylinder m g)

lemma fairSetMeasure_fixedStartEvent {q m n : ℕ} (hq : 0 < q) :
    fairSetMeasure.real (fixedStartEvent q m n) =
      (1 / 2 : ℝ) *
        (LocalLimit.fairGeometricVector (q - 1)).real
          (↑(reverseGoodGapVectors q (targetCenter q m n)) : Set _) := by
  exact fairSetMeasure_iUnion_gapCylinder hq _

lemma eventually_fixedStartEvent_probability_lower :
    ∀ᶠ q : ℕ in atTop, ∀ m n : ℕ,
      |(targetCenter q m n : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q →
      Real.exp (-1600) / (64 * LocalLimit.sixteenthRoot q ^ 24) ≤
        fairSetMeasure.real (fixedStartEvent q m n) := by
  filter_upwards [eventually_reverseGoodGapVectors_probability_lower,
    eventually_gt_atTop (0 : ℕ)] with q hq hqpos
  intro m n hcenter
  rw [fairSetMeasure_fixedStartEvent hqpos]
  have h := hq (targetCenter q m n) hcenter
  calc
    Real.exp (-1600) / (64 * LocalLimit.sixteenthRoot q ^ 24) =
        (1 / 2 : ℝ) *
          (Real.exp (-1600) / (32 * LocalLimit.sixteenthRoot q ^ 24)) := by
      ring
    _ ≤ (1 / 2 : ℝ) *
        (LocalLimit.fairGeometricVector (q - 1)).real
          (↑(reverseGoodGapVectors q (targetCenter q m n)) : Set _) :=
      mul_le_mul_of_nonneg_left h (by norm_num)

lemma setInterval_eq_gapPoints_of_mem_gapCylinder {q m : ℕ}
    {g : Fin (q - 1) → ℕ} {S : Set ℕ} (hS : S ∈ gapCylinder m g) :
    setInterval S m (m + gapSpan g) = gapPoints m g := by
  classical
  change S ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) =
    ↑(gapPoints m g) at hS
  ext x
  rw [mem_setInterval]
  have hx := Set.ext_iff.mp hS x
  change (x ∈ S ∧ x ∈ Finset.Icc m (m + gapSpan g)) ↔
    x ∈ gapPoints m g at hx
  rw [Finset.mem_Icc] at hx
  tauto

lemma gapPoints_sum_eq_of_mem_reverseGood {q m n : ℕ}
    {g : Fin (q - 1) → ℕ}
    (hg : g ∈ reverseGoodGapVectors q (targetCenter q m n)) :
    ∑ x ∈ gapPoints m g, x = n := by
  have hgood := mem_reverseGoodGapVectors_iff.mp hg
  have hz : ((∑ x ∈ gapPoints m g, x : ℕ) : ℤ) = (n : ℤ) := by
    rw [sum_gapPoints_int, hgood.2]
    simp only [targetCenter]
    ring
  exact_mod_cast hz

lemma fixedStartEvent_subset_representation {q m n : ℕ} (hq : 0 < q)
    (hm : 1 < m) :
    fixedStartEvent q m n ⊆
      {S | (setIntervalRepresentations S n).Nonempty} := by
  classical
  intro S hS
  rw [fixedStartEvent] at hS
  simp only [Set.mem_iUnion] at hS
  rcases hS with ⟨g, hgmem, hgCyl⟩
  let e := m + gapSpan g
  have hinter : setInterval S m e = gapPoints m g := by
    exact setInterval_eq_gapPoints_of_mem_gapCylinder hgCyl
  have hmPoints : m ∈ gapPoints m g := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨0, hq⟩, gapPoint_zero m g hq⟩
  have hePoints : e ∈ gapPoints m g := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨q - 1, by omega⟩, gapPoint_last m g hq⟩
  have hmS : m ∈ S := by
    have : m ∈ setInterval S m e := by simpa [hinter] using hmPoints
    exact (mem_setInterval.mp this).2.2
  have heS : e ∈ S := by
    have : e ∈ setInterval S m e := by simpa [hinter] using hePoints
    exact (mem_setInterval.mp this).2.2
  refine ⟨(m, e), hm, hmS, heS, Nat.le_add_right _ _, ?_⟩
  rw [hinter]
  exact (gapPoints_sum_eq_of_mem_reverseGood hgmem).symm

private lemma finset_sum_lt_sum_of_equal_card_ordered_sdiff
    (s t : Finset ℕ) (hcard : s.card = t.card)
    (hne : (s \ t).Nonempty)
    (horder : ∀ a ∈ s \ t, ∀ b ∈ t \ s, a < b) :
    (∑ a ∈ s, a) < ∑ b ∈ t, b := by
  classical
  have hdiffcard : (s \ t).card = (t \ s).card :=
    Finset.card_sdiff_eq_card_sdiff_iff.mpr hcard
  let e : ↥(s \ t) ≃ ↥(t \ s) :=
    Fintype.equivOfCardEq (by simpa using hdiffcard)
  have hdiff : (∑ a ∈ s \ t, a) < ∑ b ∈ t \ s, b := by
    calc
      (∑ a ∈ s \ t, a) = ∑ a : ↥(s \ t), (a : ℕ) := by
        exact (Finset.sum_attach (s \ t) (fun a : ℕ ↦ a)).symm
      _ < ∑ a : ↥(s \ t), ((e a : ↥(t \ s)) : ℕ) := by
        apply Finset.sum_lt_sum_of_nonempty
        · simpa using hne
        · intro a ha
          exact horder a a.property (e a) (e a).property
      _ = ∑ b : ↥(t \ s), (b : ℕ) := by
        exact Equiv.sum_comp e (fun b : ↥(t \ s) ↦ (b : ℕ))
      _ = ∑ b ∈ t \ s, b := by
        exact Finset.sum_attach (t \ s) (fun b : ℕ ↦ b)
  let c := s ∩ t
  have hsc : c ∪ (s \ t) = s := by
    ext x
    simp [c]
    tauto
  have htc : c ∪ (t \ s) = t := by
    ext x
    simp [c]
    tauto
  have hdisjs : Disjoint c (s \ t) := by
    rw [Finset.disjoint_left]
    intro a hac has
    have hac' := Finset.mem_inter.mp hac
    have has' := Finset.mem_sdiff.mp has
    exact has'.2 hac'.2
  have hdisjt : Disjoint c (t \ s) := by
    rw [Finset.disjoint_left]
    intro a hac hat
    have hac' := Finset.mem_inter.mp hac
    have hat' := Finset.mem_sdiff.mp hat
    exact hat'.2 hac'.1
  calc
    (∑ a ∈ s, a) = (∑ a ∈ c, a) + ∑ a ∈ s \ t, a := by
      rw [← Finset.sum_union hdisjs, hsc]
    _ < (∑ a ∈ c, a) + ∑ b ∈ t \ s, b := Nat.add_lt_add_left hdiff _
    _ = ∑ b ∈ t, b := by rw [← Finset.sum_union hdisjt, htc]

/-- If the common part lies strictly between each removed and inserted point,
then shifting a nonempty finite window raises its sum by at least its cardinality. -/
private lemma finset_sum_add_card_le_sum_of_equal_card_ordered_sdiff
    (s t : Finset ℕ) (hcard : s.card = t.card)
    (hne : (s \ t).Nonempty)
    (hgap : ∀ a ∈ s \ t, ∀ b ∈ t \ s,
      a + (s ∩ t).card + 1 ≤ b) :
    (∑ a ∈ s, a) + s.card ≤ ∑ b ∈ t, b := by
  classical
  let c := s ∩ t
  let d := s \ t
  let e : ↥d ≃ ↥(t \ s) :=
    Fintype.equivOfCardEq (by
      dsimp [d]
      simpa using Finset.card_sdiff_eq_card_sdiff_iff.mpr hcard)
  have hpoint : ∀ a : ↥d, (a : ℕ) + c.card + 1 ≤ (e a : ℕ) := by
    intro a
    exact hgap a a.property (e a) (e a).property
  have hdiff : (∑ a ∈ d, a) + d.card * (c.card + 1) ≤
      ∑ b ∈ t \ s, b := by
    calc
      (∑ a ∈ d, a) + d.card * (c.card + 1) =
          (∑ a : ↥d, (a : ℕ)) + d.card * (c.card + 1) := by
        exact congrArg (fun z ↦ z + d.card * (c.card + 1))
          (Finset.sum_attach d (fun a : ℕ ↦ a)).symm
      _ = ∑ a : ↥d, ((a : ℕ) + c.card + 1) := by
        simp [Finset.sum_add_distrib, Nat.mul_add, Nat.add_assoc]
      _ ≤ ∑ a : ↥d, (e a : ℕ) := Finset.sum_le_sum (fun a _ ↦ hpoint a)
      _ = ∑ b : ↥(t \ s), (b : ℕ) :=
        Equiv.sum_comp e (fun b : ↥(t \ s) ↦ (b : ℕ))
      _ = ∑ b ∈ t \ s, b := Finset.sum_attach (t \ s) (fun b : ℕ ↦ b)
  have hdpos : 1 ≤ d.card := Finset.one_le_card.mpr (by simpa [d] using hne)
  have hc_le : c.card ≤ d.card * c.card := by
    calc
      c.card = 1 * c.card := by simp
      _ ≤ d.card * c.card := Nat.mul_le_mul_right _ hdpos
  have hcard_decomp : s.card = c.card + d.card := by
    dsimp [c, d]
    rw [Finset.card_inter_add_card_sdiff]
  have hboost : s.card ≤ d.card * (c.card + 1) := by
    rw [hcard_decomp, Nat.mul_add]
    omega
  have hsc : c ∪ d = s := by
    ext x
    simp [c, d]
    tauto
  have htc : c ∪ (t \ s) = t := by
    ext x
    simp [c]
    tauto
  have hdisjs : Disjoint c d := by
    rw [Finset.disjoint_left]
    intro a hac had
    exact (Finset.mem_sdiff.mp had).2 (Finset.mem_inter.mp hac).2
  have hdisjt : Disjoint c (t \ s) := by
    rw [Finset.disjoint_left]
    intro a hac hat
    exact (Finset.mem_sdiff.mp hat).2 (Finset.mem_inter.mp hac).1
  calc
    (∑ a ∈ s, a) + s.card =
        ((∑ a ∈ c, a) + ∑ a ∈ d, a) + s.card := by
      rw [← Finset.sum_union hdisjs, hsc]
    _ ≤ ((∑ a ∈ c, a) + ∑ a ∈ d, a) + d.card * (c.card + 1) :=
      Nat.add_le_add_left hboost _
    _ = (∑ a ∈ c, a) +
        ((∑ a ∈ d, a) + d.card * (c.card + 1)) := by omega
    _ ≤ (∑ a ∈ c, a) + ∑ b ∈ t \ s, b := Nat.add_le_add_left hdiff _
    _ = ∑ b ∈ t, b := by rw [← Finset.sum_union hdisjt, htc]

/-- Two equally long consecutive runs in a set have strictly increasing sums
when their starting elements increase. -/
lemma sum_setInterval_lt_of_start_lt {S : Set ℕ} {x y x' y' q : ℕ}
    (hxS : x ∈ S) (hx'S : x' ∈ S) (hyS : y ∈ S) (hy'S : y' ∈ S)
    (hxy : x ≤ y) (hx'y' : x' ≤ y') (hxx' : x < x')
    (hcard : (setInterval S x y).card = q)
    (hcard' : (setInterval S x' y').card = q) :
    (∑ z ∈ setInterval S x y, z) <
      ∑ z ∈ setInterval S x' y', z := by
  classical
  let s := setInterval S x y
  let t := setInterval S x' y'
  have hyy' : y < y' := by
    by_contra hnot
    have hy'y : y' ≤ y := Nat.le_of_not_gt hnot
    have hsub : t ⊆ s := by
      intro z hz
      rw [mem_setInterval] at hz ⊢
      exact ⟨le_trans hxx'.le hz.1, hz.2.1.trans hy'y, hz.2.2⟩
    have hxmem : x ∈ s := by
      rw [mem_setInterval]
      exact ⟨le_rfl, hxy, hxS⟩
    have hxnot : x ∉ t := by
      rw [mem_setInterval]
      omega
    have hne : t ≠ s := by
      intro heq
      exact hxnot (heq ▸ hxmem)
    have hltcard : t.card < s.card :=
      Finset.card_lt_card (_root_.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    dsimp [s, t] at hltcard
    omega
  have hcards : s.card = t.card := by dsimp [s, t]; omega
  have hxmem : x ∈ s := by
    rw [mem_setInterval]
    exact ⟨le_rfl, hxy, hxS⟩
  have hxnot : x ∉ t := by
    rw [mem_setInterval]
    omega
  have hne : (s \ t).Nonempty := ⟨x, Finset.mem_sdiff.mpr ⟨hxmem, hxnot⟩⟩
  apply finset_sum_lt_sum_of_equal_card_ordered_sdiff s t hcards hne
  intro a ha b hb
  rw [Finset.mem_sdiff] at ha hb
  have haI := (mem_setInterval.mp ha.1)
  have hbI := (mem_setInterval.mp hb.1)
  have hax' : a < x' := by
    by_contra hnot
    apply ha.2
    rw [mem_setInterval]
    exact ⟨Nat.le_of_not_gt hnot, haI.2.1.trans hyy'.le, haI.2.2⟩
  have hyb : y < b := by
    by_contra hnot
    apply hb.2
    rw [mem_setInterval]
    exact ⟨hxx'.le.trans hbI.1, Nat.le_of_not_gt hnot, hbI.2.2⟩
  omega

/-- Quantitative sliding-window inequality: moving a consecutive window of
`q` distinct natural numbers to the right raises its sum by at least `q`. -/
lemma sum_setInterval_add_card_le_of_start_lt {S : Set ℕ} {x y x' y' q : ℕ}
    (hxS : x ∈ S) (hx'S : x' ∈ S) (hyS : y ∈ S) (hy'S : y' ∈ S)
    (hxy : x ≤ y) (hx'y' : x' ≤ y') (hxx' : x < x')
    (hcard : (setInterval S x y).card = q)
    (hcard' : (setInterval S x' y').card = q) :
    (∑ z ∈ setInterval S x y, z) + q ≤
      ∑ z ∈ setInterval S x' y', z := by
  classical
  let s := setInterval S x y
  let t := setInterval S x' y'
  have hyy' : y < y' := by
    by_contra hnot
    have hy'y : y' ≤ y := Nat.le_of_not_gt hnot
    have hsub : t ⊆ s := by
      intro z hz
      rw [mem_setInterval] at hz ⊢
      exact ⟨le_trans hxx'.le hz.1, hz.2.1.trans hy'y, hz.2.2⟩
    have hxmem : x ∈ s := by
      rw [mem_setInterval]
      exact ⟨le_rfl, hxy, hxS⟩
    have hxnot : x ∉ t := by
      rw [mem_setInterval]
      omega
    have hne : t ≠ s := by
      intro heq
      exact hxnot (heq ▸ hxmem)
    have hltcard : t.card < s.card :=
      Finset.card_lt_card (_root_.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    dsimp [s, t] at hltcard
    omega
  have hcards : s.card = t.card := by dsimp [s, t]; omega
  have hxmem : x ∈ s := by
    rw [mem_setInterval]
    exact ⟨le_rfl, hxy, hxS⟩
  have hxnot : x ∉ t := by
    rw [mem_setInterval]
    omega
  have hne : (s \ t).Nonempty := ⟨x, Finset.mem_sdiff.mpr ⟨hxmem, hxnot⟩⟩
  have hmain := finset_sum_add_card_le_sum_of_equal_card_ordered_sdiff
    s t hcards hne (by
      intro a ha b hb
      rw [Finset.mem_sdiff] at ha hb
      have haI := mem_setInterval.mp ha.1
      have hbI := mem_setInterval.mp hb.1
      have hax' : a < x' := by
        by_contra hnot
        apply ha.2
        rw [mem_setInterval]
        exact ⟨Nat.le_of_not_gt hnot, haI.2.1.trans hyy'.le, haI.2.2⟩
      have hyb : y < b := by
        by_contra hnot
        apply hb.2
        rw [mem_setInterval]
        exact ⟨hxx'.le.trans hbI.1, Nat.le_of_not_gt hnot, hbI.2.2⟩
      have hcsub : s ∩ t ⊆ Finset.Ioo a b := by
        intro z hz
        have hz' := Finset.mem_inter.mp hz
        have hzs := mem_setInterval.mp hz'.1
        have hzt := mem_setInterval.mp hz'.2
        rw [Finset.mem_Ioo]
        exact ⟨hax'.trans_le hzt.1, hzs.2.1.trans_lt hyb⟩
      have hcCard := Finset.card_le_card hcsub
      rw [Nat.card_Ioo] at hcCard
      omega)
  dsimp [s, t] at hmain
  omega

lemma fixedStartEvent_disjoint {q m m' n : ℕ} (hq : 0 < q) (hmm' : m ≠ m') :
    Disjoint (fixedStartEvent q m n) (fixedStartEvent q m' n) := by
  classical
  rw [Set.disjoint_left]
  intro S hSm hSm'
  wlog hlt : m < m' generalizing m m'
  · exact this (m := m') (m' := m) hmm'.symm hSm' hSm (by omega)
  rw [fixedStartEvent] at hSm hSm'
  simp only [Set.mem_iUnion] at hSm hSm'
  rcases hSm with ⟨g, hg, hgCyl⟩
  rcases hSm' with ⟨g', hg', hg'Cyl⟩
  let y := m + gapSpan g
  let y' := m' + gapSpan g'
  have hinter : setInterval S m y = gapPoints m g :=
    setInterval_eq_gapPoints_of_mem_gapCylinder hgCyl
  have hinter' : setInterval S m' y' = gapPoints m' g' :=
    setInterval_eq_gapPoints_of_mem_gapCylinder hg'Cyl
  have hmPoints : m ∈ gapPoints m g := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨0, hq⟩, gapPoint_zero m g hq⟩
  have hm'Points : m' ∈ gapPoints m' g' := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨0, hq⟩, gapPoint_zero m' g' hq⟩
  have hyPoints : y ∈ gapPoints m g := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨q - 1, by omega⟩, gapPoint_last m g hq⟩
  have hy'Points : y' ∈ gapPoints m' g' := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨q - 1, by omega⟩, gapPoint_last m' g' hq⟩
  have hmS : m ∈ S :=
    (mem_setInterval.mp (hinter.symm ▸ hmPoints)).2.2
  have hm'S : m' ∈ S :=
    (mem_setInterval.mp (hinter'.symm ▸ hm'Points)).2.2
  have hyS : y ∈ S :=
    (mem_setInterval.mp (hinter.symm ▸ hyPoints)).2.2
  have hy'S : y' ∈ S :=
    (mem_setInterval.mp (hinter'.symm ▸ hy'Points)).2.2
  have hltSum := sum_setInterval_lt_of_start_lt (q := q) hmS hm'S hyS hy'S
    (Nat.le_add_right _ _) (Nat.le_add_right _ _) hlt
    (by simpa [hinter]) (by simpa [hinter'])
  have hsum : (∑ z ∈ setInterval S m y, z) = n := by
    rw [hinter]
    exact gapPoints_sum_eq_of_mem_reverseGood hg
  have hsum' : (∑ z ∈ setInterval S m' y', z) = n := by
    rw [hinter']
    exact gapPoints_sum_eq_of_mem_reverseGood hg'
  omega

def baseStart (q n : ℕ) : ℕ := n / q - (q - 1)

def candidateStarts (q n : ℕ) : Finset ℕ :=
  Finset.Icc (baseStart q n) (baseStart q n + Nat.sqrt q)

@[simp] lemma card_candidateStarts (q n : ℕ) :
    (candidateStarts q n).card = Nat.sqrt q + 1 := by
  simp [candidateStarts]
  omega

lemma mem_candidateStarts_iff {q n m : ℕ} :
    m ∈ candidateStarts q n ↔
      baseStart q n ≤ m ∧ m - baseStart q n ≤ Nat.sqrt q := by
  rw [candidateStarts, Finset.mem_Icc]
  omega

lemma targetCenter_eq_mod_sub {q m n : ℕ} (hq : 0 < q)
    (hqn : q * (q - 1) ≤ n) (hm : baseStart q n ≤ m) :
    targetCenter q m n =
      (n % q : ℕ) - (q : ℤ) * ((m - baseStart q n : ℕ) : ℤ) := by
  have hdiv : q - 1 ≤ n / q :=
    (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hqn)
  have hbase : baseStart q n + (q - 1) = n / q := by
    rw [baseStart, Nat.sub_add_cancel hdiv]
  have hm' : baseStart q n + (m - baseStart q n) = m :=
    Nat.add_sub_of_le hm
  have hn : n % q + q * (n / q) = n := Nat.mod_add_div n q
  have hbaseZ : (baseStart q n : ℤ) + ((q - 1 : ℕ) : ℤ) =
      ((n / q : ℕ) : ℤ) := by exact_mod_cast hbase
  have hmZ : (baseStart q n : ℤ) + ((m - baseStart q n : ℕ) : ℤ) =
      (m : ℤ) := by exact_mod_cast hm'
  have hnZ : ((n % q : ℕ) : ℤ) + (q : ℤ) * ((n / q : ℕ) : ℤ) =
      (n : ℤ) := by exact_mod_cast hn
  rw [targetCenter, ← hnZ, ← hmZ, ← hbaseZ]
  ring

lemma natSqrt_cast_le_realSqrt (q : ℕ) :
    (Nat.sqrt q : ℝ) ≤ Real.sqrt q := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  rw [Real.le_sqrt (by positivity) hq0]
  exact_mod_cast Nat.sqrt_le' q

lemma realSqrt_lt_natSqrt_add_one (q : ℕ) :
    Real.sqrt q < (Nat.sqrt q + 1 : ℕ) := by
  rw [Real.sqrt_lt' (by positivity)]
  exact_mod_cast Nat.lt_succ_sqrt' q

lemma targetCenter_bound_of_mem_candidateStarts {q m n : ℕ} (hq : 0 < q)
    (hqn : q * (q - 1) ≤ n) (hm : m ∈ candidateStarts q n) :
    |(targetCenter q m n : ℝ)| ≤ 10 * (q : ℝ) * Real.sqrt q := by
  rw [mem_candidateStarts_iff] at hm
  rw [targetCenter_eq_mod_sub hq hqn hm.1]
  push_cast
  have hmod : n % q < q := Nat.mod_lt n hq
  have hdNatCast : ((m - baseStart q n : ℕ) : ℝ) ≤ (Nat.sqrt q : ℝ) := by
    exact_mod_cast hm.2
  have hd : ((m - baseStart q n : ℕ) : ℝ) ≤ Real.sqrt q :=
    hdNatCast.trans (natSqrt_cast_le_realSqrt q)
  have hsqrt : 1 ≤ Real.sqrt q := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hq
  rw [abs_le]
  have hmod0 : (0 : ℝ) ≤ (n % q : ℕ) := by positivity
  have hd0 : (0 : ℝ) ≤ (m - baseStart q n : ℕ) := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hmodR : ((n % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hmod
  have hqd : (q : ℝ) * ((m - baseStart q n : ℕ) : ℝ) ≤
      (q : ℝ) * Real.sqrt q := mul_le_mul_of_nonneg_left hd hq0
  have hone : (q : ℝ) ≤ (q : ℝ) * Real.sqrt q := by
    calc
      (q : ℝ) = (q : ℝ) * 1 := by ring
      _ ≤ (q : ℝ) * Real.sqrt q := mul_le_mul_of_nonneg_left hsqrt hq0
  have hten : (q : ℝ) * Real.sqrt q ≤ 10 * (q : ℝ) * Real.sqrt q := by
    have : (0 : ℝ) ≤ (q : ℝ) * Real.sqrt q := mul_nonneg hq0 (Real.sqrt_nonneg _)
    nlinarith
  constructor
  · calc
      -(10 * (q : ℝ) * Real.sqrt q) ≤ -((q : ℝ) * Real.sqrt q) :=
        neg_le_neg hten
      _ ≤ -((q : ℝ) * ((m - baseStart q n : ℕ) : ℝ)) := neg_le_neg hqd
      _ ≤ ((n % q : ℕ) : ℝ) -
          (q : ℝ) * ((m - baseStart q n : ℕ) : ℝ) := by linarith
  · calc
      ((n % q : ℕ) : ℝ) - (q : ℝ) * ((m - baseStart q n : ℕ) : ℝ) ≤
          ((n % q : ℕ) : ℝ) := sub_le_self _ (mul_nonneg hq0 hd0)
      _ ≤ (q : ℝ) := hmodR.le
      _ ≤ (q : ℝ) * Real.sqrt q := hone
      _ ≤ 10 * (q : ℝ) * Real.sqrt q := hten

noncomputable def lengthEvent (q n : ℕ) : Set (Set ℕ) :=
  ⋃ m ∈ candidateStarts q n, fixedStartEvent q m n

lemma measurableSet_lengthEvent (q n : ℕ) : MeasurableSet (lengthEvent q n) := by
  classical
  exact Finset.measurableSet_biUnion _
    (fun m _ ↦ measurableSet_fixedStartEvent q m n)

lemma fairSetMeasure_lengthEvent {q n : ℕ} (hq : 0 < q) :
    fairSetMeasure.real (lengthEvent q n) =
      ∑ m ∈ candidateStarts q n,
        fairSetMeasure.real (fixedStartEvent q m n) := by
  rw [lengthEvent, measureReal_biUnion_finset]
  · intro m hm m' hm' hmm'
    exact fixedStartEvent_disjoint hq hmm'
  · intro m hm
    exact measurableSet_fixedStartEvent q m n

lemma lengthEvent_gives_representation_with_card {q n : ℕ} (hq : 0 < q)
    (hbase : 1 < baseStart q n) {S : Set ℕ} (hS : S ∈ lengthEvent q n) :
    ∃ x y, (x, y) ∈ setIntervalRepresentations S n ∧
      (setInterval S x y).card = q := by
  classical
  rw [lengthEvent] at hS
  simp only [Set.mem_iUnion] at hS
  rcases hS with ⟨m, hm, hmEvent⟩
  have hmBounds := mem_candidateStarts_iff.mp hm
  have hmgt : 1 < m := hbase.trans_le hmBounds.1
  rw [fixedStartEvent] at hmEvent
  simp only [Set.mem_iUnion] at hmEvent
  rcases hmEvent with ⟨g, hg, hgCyl⟩
  let y := m + gapSpan g
  have hinter : setInterval S m y = gapPoints m g :=
    setInterval_eq_gapPoints_of_mem_gapCylinder hgCyl
  have hmPoints : m ∈ gapPoints m g := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨0, hq⟩, gapPoint_zero m g hq⟩
  have hyPoints : y ∈ gapPoints m g := by
    rw [mem_gapPoints_iff]
    exact ⟨⟨q - 1, by omega⟩, gapPoint_last m g hq⟩
  have hmS : m ∈ S :=
    (mem_setInterval.mp (hinter.symm ▸ hmPoints)).2.2
  have hyS : y ∈ S :=
    (mem_setInterval.mp (hinter.symm ▸ hyPoints)).2.2
  refine ⟨m, y, ⟨hmgt, hmS, hyS, Nat.le_add_right _ _, ?_⟩, ?_⟩
  · rw [hinter]
    exact (gapPoints_sum_eq_of_mem_reverseGood hg).symm
  · rw [hinter]
    exact gapPoints_card m g

/-- For a fixed length `q`, two target events whose distinct target sums differ
by less than `q` are disjoint. -/
lemma lengthEvent_disjoint_of_lt {q n n' : ℕ} (hq : 0 < q)
    (hbase : 1 < baseStart q n) (hbase' : 1 < baseStart q n')
    (hnn' : n < n') (hn'q : n' < n + q) :
    Disjoint (lengthEvent q n) (lengthEvent q n') := by
  classical
  rw [Set.disjoint_left]
  intro S hnS hn'S
  obtain ⟨x, y, hrep, hcard⟩ :=
    lengthEvent_gives_representation_with_card hq hbase hnS
  obtain ⟨x', y', hrep', hcard'⟩ :=
    lengthEvent_gives_representation_with_card hq hbase' hn'S
  rcases hrep with ⟨hx, hxS, hyS, hxy, hsum⟩
  rcases hrep' with ⟨hx', hx'S, hy'S, hx'y', hsum'⟩
  have hxx' : x ≠ x' := by
    intro heq
    subst x'
    have hsets : setInterval S x y = setInterval S x y' := by
      rcases le_total y y' with hyy' | hy'y
      · apply Finset.eq_of_subset_of_card_le
        · intro z hz
          rw [mem_setInterval] at hz ⊢
          exact ⟨hz.1, hz.2.1.trans hyy', hz.2.2⟩
        · omega
      · symm
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          rw [mem_setInterval] at hz ⊢
          exact ⟨hz.1, hz.2.1.trans hy'y, hz.2.2⟩
        · omega
    rw [hsets] at hsum
    omega
  rcases lt_or_gt_of_ne hxx' with hlt | hgt
  · have hquant := sum_setInterval_add_card_le_of_start_lt
      hxS hx'S hyS hy'S hxy hx'y' hlt hcard hcard'
    omega
  · have hquant := sum_setInterval_add_card_le_of_start_lt
      hx'S hxS hy'S hyS hx'y' hxy hgt hcard' hcard
    omega

lemma lengthEvent_disjoint_of_ne_of_absDiff_lt {q n n' : ℕ} (hq : 0 < q)
    (hbase : 1 < baseStart q n) (hbase' : 1 < baseStart q n')
    (hne : n ≠ n') (hdiff : n.max n' - n.min n' < q) :
    Disjoint (lengthEvent q n) (lengthEvent q n') := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply lengthEvent_disjoint_of_lt hq hbase hbase' hlt
    simp only [Nat.max_eq_right hlt.le, Nat.min_eq_left hlt.le] at hdiff
    omega
  · exact (lengthEvent_disjoint_of_lt hq hbase' hbase hgt (by
      simp only [Nat.max_eq_left hgt.le, Nat.min_eq_right hgt.le] at hdiff
      omega)).symm

lemma eventually_lengthEvent_probability_lower :
    ∀ᶠ q : ℕ in atTop, ∀ n : ℕ,
      q * (q - 1) ≤ n →
      Real.exp (-1600) / (64 * (q : ℝ)) ≤
        fairSetMeasure.real (lengthEvent q n) := by
  filter_upwards [eventually_fixedStartEvent_probability_lower,
    eventually_gt_atTop (0 : ℕ)] with q hfixed hq
  intro n hqn
  rw [fairSetMeasure_lengthEvent hq]
  let c := Real.exp (-1600) /
    (64 * LocalLimit.sixteenthRoot q ^ 24)
  have heach : ∀ m ∈ candidateStarts q n,
      c ≤ fairSetMeasure.real (fixedStartEvent q m n) := by
    intro m hm
    exact hfixed m n (targetCenter_bound_of_mem_candidateStarts hq hqn hm)
  have hsum : (candidateStarts q n).card * c ≤
      ∑ m ∈ candidateStarts q n,
        fairSetMeasure.real (fixedStartEvent q m n) := by
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum heach
  have hroot : LocalLimit.sixteenthRoot q ^ 24 =
      (q : ℝ) * Real.sqrt q := by
    rw [show 24 = 16 + 8 by omega, pow_add,
      LocalLimit.sixteenthRoot_pow_sixteen,
      ← LocalLimit.sqrt_nat_eq_sixteenthRoot_pow_eight]
  have hcard : Real.sqrt q ≤ ((candidateStarts q n).card : ℝ) := by
    rw [card_candidateStarts]
    exact (realSqrt_lt_natSqrt_add_one q).le
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hqreal
  have hexp : 0 < Real.exp (-1600) := Real.exp_pos _
  dsimp [c] at hsum
  rw [hroot] at hsum
  calc
    Real.exp (-1600) / (64 * (q : ℝ)) ≤
        ((candidateStarts q n).card : ℝ) *
          (Real.exp (-1600) / (64 * ((q : ℝ) * Real.sqrt q))) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (q : ℝ))).2
      field_simp
      nlinarith
    _ ≤ _ := hsum

/-- All coordinates inspected by `lengthEvent q n`. -/
def lengthSupport (q n : ℕ) : Finset ℕ :=
  Finset.Icc (baseStart q n)
    (baseStart q n + Nat.sqrt q + 4 * q)

lemma gapInterval_subset_lengthSupport {q m n : ℕ}
    {g : Fin (q - 1) → ℕ}
    (hm : m ∈ candidateStarts q n)
    (hg : g ∈ reverseGoodGapVectors q (targetCenter q m n)) :
    Finset.Icc m (m + gapSpan g) ⊆ lengthSupport q n := by
  intro x hx
  rw [Finset.mem_Icc] at hx
  rw [lengthSupport, Finset.mem_Icc]
  have hm' := mem_candidateStarts_iff.mp hm
  have hg' := mem_reverseGoodGapVectors_iff.mp hg
  constructor
  · exact hm'.1.trans hx.1
  · omega

lemma inter_eq_on_subset {S T : Set ℕ} {u v : Finset ℕ}
    (huv : u ⊆ v)
    (hST : S ∩ (v : Set ℕ) = T ∩ (v : Set ℕ)) :
    S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) := by
  ext x
  constructor
  · rintro ⟨hxS, hxu⟩
    have hxv : x ∈ v := huv hxu
    have : x ∈ S ∩ (v : Set ℕ) := ⟨hxS, hxv⟩
    rw [hST] at this
    exact ⟨this.1, hxu⟩
  · rintro ⟨hxT, hxu⟩
    have hxv : x ∈ v := huv hxu
    have : x ∈ T ∩ (v : Set ℕ) := ⟨hxT, hxv⟩
    rw [← hST] at this
    exact ⟨this.1, hxu⟩

lemma lengthEvent_congr_of_inter_support_eq {q n : ℕ} {S T : Set ℕ}
    (hST : S ∩ (lengthSupport q n : Set ℕ) =
      T ∩ (lengthSupport q n : Set ℕ)) :
    S ∈ lengthEvent q n ↔ T ∈ lengthEvent q n := by
  classical
  simp only [lengthEvent, fixedStartEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm, g, hg, hSCyl⟩
    refine ⟨m, hm, g, hg, ?_⟩
    change T ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) =
      ↑(gapPoints m g)
    change S ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) =
      ↑(gapPoints m g) at hSCyl
    rw [← hSCyl]
    exact (inter_eq_on_subset (gapInterval_subset_lengthSupport hm hg) hST).symm
  · rintro ⟨m, hm, g, hg, hTCyl⟩
    refine ⟨m, hm, g, hg, ?_⟩
    change S ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) =
      ↑(gapPoints m g)
    change T ∩ (↑(Finset.Icc m (m + gapSpan g)) : Set ℕ) =
      ↑(gapPoints m g) at hTCyl
    rw [← hTCyl]
    exact inter_eq_on_subset (gapInterval_subset_lengthSupport hm hg) hST

/-! ### Independent finite coordinate restrictions -/

noncomputable def fairCoordinate (i : ℕ) : Measure Prop :=
  unitInterval.toNNReal half • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm half) • Measure.dirac False

noncomputable def fairBits : Measure (ℕ → Prop) :=
  Measure.infinitePi fairCoordinate

instance (i : ℕ) : IsProbabilityMeasure (fairCoordinate i) := by
  rw [fairCoordinate]
  infer_instance

instance : IsProbabilityMeasure fairBits := by
  rw [fairBits]
  infer_instance

def bitsToSet (ω : ℕ → Prop) : Set ℕ := {i | ω i}

lemma fairBits_real_preimage (E : Set (Set ℕ)) :
    fairBits.real (bitsToSet ⁻¹' E) = fairSetMeasure.real E := by
  rw [measureReal_def, measureReal_def]
  congr 1
  rw [fairSetMeasure, setBernoulli_apply']
  rfl

def restrictBits (u : Finset ℕ) (ω : ℕ → Prop) : ↥u → Prop :=
  fun i ↦ ω i

def allowedRestrictions (u : Finset ℕ) (E : Set (Set ℕ)) : Set (↥u → Prop) :=
  {v | ∃ ω, restrictBits u ω = v ∧ bitsToSet ω ∈ E}

lemma preimage_allowedRestrictions_of_supported
    {u : Finset ℕ} {E : Set (Set ℕ)}
    (hE : ∀ {S T : Set ℕ}, S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) →
      (S ∈ E ↔ T ∈ E)) :
    bitsToSet ⁻¹' E = restrictBits u ⁻¹' allowedRestrictions u E := by
  ext ω
  constructor
  · intro hω
    exact ⟨ω, rfl, hω⟩
  · rintro ⟨η, hη, hηE⟩
    apply (hE ?_).mpr hηE
    ext x
    constructor
    · rintro ⟨hxω, hxu⟩
      have heq := congrFun hη ⟨x, hxu⟩
      exact ⟨heq.symm.mp hxω, hxu⟩
    · rintro ⟨hxη, hxu⟩
      have heq := congrFun hη ⟨x, hxu⟩
      exact ⟨heq.mp hxη, hxu⟩

lemma preimage_lengthEvent_eq_restrictBits {q n : ℕ} :
    bitsToSet ⁻¹' lengthEvent q n =
      restrictBits (lengthSupport q n) ⁻¹'
        allowedRestrictions (lengthSupport q n) (lengthEvent q n) := by
  exact preimage_allowedRestrictions_of_supported
    (fun h ↦ lengthEvent_congr_of_inter_support_eq h)

lemma restrictBits_iIndep {ι : Type*} (u : ι → Finset ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j)) :
    iIndepFun (fun i ↦ restrictBits (u i)) fairBits := by
  let κ : ι → Type := fun i ↦ ↥(u i)
  let F : (Σ i, κ i) → ℕ := fun p ↦ (p.2 : ℕ)
  have hF : Function.Injective F := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hab))
    · have hd := hdisj i j hij
      rw [Finset.disjoint_left] at hd
      change (a : ℕ) = (b : ℕ) at hab
      have ha_j : (a : ℕ) ∈ u j := by simpa [hab] using b.property
      exact False.elim (hd a.property ha_j)
  let flat : (ℕ → Prop) → ((p : Σ i, κ i) → Prop) :=
    fun ω p ↦ ω (F p)
  let grouped : (ℕ → Prop) → ((i : ι) → κ i → Prop) :=
    fun ω i a ↦ ω a
  let e := MeasurableEquiv.piCurry (fun i : ι ↦ fun _ : κ i ↦ Prop)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    exact measurable_pi_lambda _ (fun j ↦ by
      simpa only [restrictBits] using (measurable_pi_apply (j : ℕ))))]
  change fairBits.map grouped =
    Measure.infinitePi (fun i ↦ fairBits.map (restrictBits (u i)))
  calc
    fairBits.map grouped = (fairBits.map flat).map e := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop
    _ = (Measure.infinitePi (fun p : Σ i, κ i ↦ fairCoordinate (F p))).map e := by
      congr 1
      exact Measure.map_infinitePi_infinitePi_of_inj hF
    _ = Measure.infinitePi (fun i ↦
          Measure.infinitePi (fun a : κ i ↦ fairCoordinate a)) := by
      simpa [e, F, κ] using
        (Measure.infinitePi_map_piCurry
          (fun i : ι ↦ fun a : ↥(u i) ↦ fairCoordinate (a : ℕ)))
    _ = Measure.infinitePi (fun i ↦ fairBits.map (restrictBits (u i))) := by
      congr 1
      funext i
      rw [fairBits]
      exact (Measure.map_infinitePi_infinitePi_of_inj
        (f := fun a : κ i ↦ (a : ℕ)) Subtype.val_injective).symm

lemma fairBits_measure_biInter_supported_eq_prod {ι : Type*}
    (u : ι → Finset ℕ) (E : ι → Set (Set ℕ)) (s : Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j))
    (hE : ∀ i, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i)) :
    fairBits (⋂ i ∈ s, bitsToSet ⁻¹' E i) =
      ∏ i ∈ s, fairBits (bitsToSet ⁻¹' E i) := by
  have hind := restrictBits_iIndep u hdisj
  have hprod := hind.measure_inter_preimage_eq_mul s
    (sets := fun i ↦ allowedRestrictions (u i) (E i))
    (fun i hi ↦ MeasurableSet.of_discrete)
  have heq : ∀ i, bitsToSet ⁻¹' E i =
      restrictBits (u i) ⁻¹' allowedRestrictions (u i) (E i) :=
    fun i ↦ preimage_allowedRestrictions_of_supported (hE i)
  simpa only [heq] using hprod

lemma fairBits_measureReal_biInter_supported_eq_prod {ι : Type*}
    (u : ι → Finset ℕ) (E : ι → Set (Set ℕ)) (s : Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j))
    (hE : ∀ i, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i)) :
    fairBits.real (⋂ i ∈ s, bitsToSet ⁻¹' E i) =
      ∏ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i) := by
  rw [measureReal_def,
    fairBits_measure_biInter_supported_eq_prod u E s hdisj hE,
    ENNReal.toReal_prod]
  simp only [← measureReal_def]

lemma fairBits_measure_biInter_lengthEvents_eq_prod {ι : Type*}
    (q n : ι → ℕ) (s : Finset ι)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (lengthSupport (q i) (n i)) (lengthSupport (q j) (n j))) :
    fairBits (⋂ i ∈ s, bitsToSet ⁻¹' lengthEvent (q i) (n i)) =
      ∏ i ∈ s, fairBits (bitsToSet ⁻¹' lengthEvent (q i) (n i)) := by
  apply fairBits_measure_biInter_supported_eq_prod
    (fun i ↦ lengthSupport (q i) (n i))
    (fun i ↦ lengthEvent (q i) (n i)) s hdisj
  intro i S T hST
  exact lengthEvent_congr_of_inter_support_eq hST

/-- The real-valued indicator of a set-event. -/
noncomputable def eventIndicator (E : Set (Set ℕ)) (ω : ℕ → Prop) : ℝ := by
  classical
  exact if bitsToSet ω ∈ E then 1 else 0

lemma eventIndicator_eq_indicator (E : Set (Set ℕ)) :
    eventIndicator E = (bitsToSet ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext ω
  change (if bitsToSet ω ∈ E then 1 else 0) =
    (if bitsToSet ω ∈ E then 1 else 0)
  rfl

lemma measurable_eventIndicator_of_supported {u : Finset ℕ} {E : Set (Set ℕ)}
    (hE : ∀ {S T : Set ℕ}, S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) →
      (S ∈ E ↔ T ∈ E)) :
    Measurable (eventIndicator E) := by
  rw [eventIndicator_eq_indicator]
  apply Measurable.indicator measurable_const
  rw [preimage_allowedRestrictions_of_supported hE]
  exact (MeasurableSet.of_discrete :
    MeasurableSet (allowedRestrictions u E)).preimage
      (measurable_pi_lambda _ (fun j ↦ by
        simpa only [restrictBits] using (measurable_pi_apply (j : ℕ))))

lemma integral_eventIndicator_of_supported {u : Finset ℕ} {E : Set (Set ℕ)}
    (hE : ∀ {S T : Set ℕ}, S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) →
      (S ∈ E ↔ T ∈ E)) :
    fairBits[eventIndicator E] = fairBits.real (bitsToSet ⁻¹' E) := by
  rw [eventIndicator_eq_indicator, integral_indicator_const]
  · simp [measureReal_def]
  · rw [preimage_allowedRestrictions_of_supported hE]
    exact (MeasurableSet.of_discrete :
      MeasurableSet (allowedRestrictions u E)).preimage
        (measurable_pi_lambda _ (fun j ↦ by
          simpa only [restrictBits] using (measurable_pi_apply (j : ℕ))))

lemma eventIndicator_iIndep {ι : Type*} (u : ι → Finset ℕ)
    (E : ι → Set (Set ℕ))
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j))
    (hE : ∀ i, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i)) :
    iIndepFun (fun i ↦ eventIndicator (E i)) fairBits := by
  classical
  let g : ∀ i, (↥(u i) → Prop) → ℝ :=
    fun i v ↦ if v ∈ allowedRestrictions (u i) (E i) then 1 else 0
  have hind := (restrictBits_iIndep u hdisj).comp g (fun _ ↦ Measurable.of_discrete)
  apply hind.congr
  intro i
  filter_upwards [] with ω
  change g i (restrictBits (u i) ω) = eventIndicator (E i) ω
  have heq := Set.ext_iff.mp (preimage_allowedRestrictions_of_supported (hE i)) ω
  simp only [Set.mem_preimage] at heq
  simp only [g, eventIndicator]
  exact if_congr heq.symm rfl rfl

/-- Hoeffding's inequality for finitely many event indicators on pairwise
disjoint finite coordinate supports.  It is stated for the centered lower-tail
variables `E[1_E] - 1_E`, which is the form used below. -/
lemma eventIndicator_centered_lowerTail {ι : Type*}
    (u : ι → Finset ℕ) (E : ι → Set (Set ℕ)) (s : Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j))
    (hE : ∀ i, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    fairBits.real {ω | ε ≤ ∑ i ∈ s,
        (fairBits[eventIndicator (E i)] - eventIndicator (E i) ω)} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ _i ∈ s, (1 / 4 : ℝ≥0))) := by
  let Y : ι → (ℕ → Prop) → ℝ := fun i ↦ eventIndicator (E i)
  let X : ι → (ℕ → Prop) → ℝ :=
    fun i ω ↦ fairBits[Y i] - Y i ω
  have hYind : iIndepFun Y fairBits := eventIndicator_iIndep u E hdisj hE
  have hXind : iIndepFun X fairBits := by
    exact hYind.comp (fun i z ↦ fairBits[Y i] - z) (fun _ ↦ by fun_prop)
  have hsubG : ∀ i ∈ s,
      HasSubgaussianMGF (X i) (1 / 4 : ℝ≥0) fairBits := by
    intro i hi
    have hmeas : AEMeasurable (Y i) fairBits :=
      (measurable_eventIndicator_of_supported (hE i)).aemeasurable
    have hbounds : ∀ᵐ ω ∂fairBits, Y i ω ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [] with ω
      classical
      simp only [Y, eventIndicator]
      split_ifs <;> simp
    have h := hasSubgaussianMGF_of_mem_Icc hmeas hbounds
    have hn := h.neg
    have hfun : -(fun ω ↦ Y i ω - fairBits[Y i]) = X i := by
      funext ω
      simp only [X, Pi.neg_apply]
      ring
    rw [hfun] at hn
    convert hn using 1 <;> norm_num
  simpa only [X, Y] using
    (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      hXind hsubG hε)

noncomputable def eventCount {ι : Type*} (s : Finset ι)
    (E : ι → Set (Set ℕ)) (ω : ℕ → Prop) : ℕ := by
  classical
  exact (s.filter fun i ↦ bitsToSet ω ∈ E i).card

lemma sum_eventIndicator_eq_eventCount {ι : Type*} (s : Finset ι)
    (E : ι → Set (Set ℕ)) (ω : ℕ → Prop) :
    ∑ i ∈ s, eventIndicator (E i) ω = (eventCount s E ω : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eventCount]
  | @insert i s hi ih =>
      by_cases hmem : bitsToSet ω ∈ E i
      · simp [eventCount, eventIndicator, hi, hmem, ih]
      · simp [eventCount, eventIndicator, hi, hmem, ih]

lemma integrable_eventIndicator_of_supported {u : Finset ℕ} {E : Set (Set ℕ)}
    (hE : ∀ {S T : Set ℕ}, S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) →
      (S ∈ E ↔ T ∈ E)) : Integrable (eventIndicator E) fairBits := by
  refine (integrable_const (1 : ℝ)).mono
    (measurable_eventIndicator_of_supported hE).aestronglyMeasurable ?_
  filter_upwards [] with ω
  classical
  simp only [eventIndicator]
  split_ifs <;> norm_num

lemma mgf_eventIndicator_neg_one {u : Finset ℕ} {E : Set (Set ℕ)}
    (hE : ∀ {S T : Set ℕ}, S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) →
      (S ∈ E ↔ T ∈ E)) :
    ProbabilityTheory.mgf (eventIndicator E) fairBits (-1) =
      1 - (1 - Real.exp (-1)) * fairBits.real (bitsToSet ⁻¹' E) := by
  have hpoint : (fun ω ↦ Real.exp ((-1 : ℝ) * eventIndicator E ω)) =
      fun ω ↦ 1 - (1 - Real.exp (-1)) * eventIndicator E ω := by
    funext ω
    classical
    simp only [eventIndicator]
    split_ifs <;> norm_num
  rw [ProbabilityTheory.mgf, hpoint]
  have hI := integrable_eventIndicator_of_supported hE
  rw [integral_sub (integrable_const _) (hI.const_mul _), integral_const,
    integral_const_mul, integral_eventIndicator_of_supported hE]
  simp

lemma mgf_eventIndicator_neg_one_le {u : Finset ℕ} {E : Set (Set ℕ)}
    (hE : ∀ {S T : Set ℕ}, S ∩ (u : Set ℕ) = T ∩ (u : Set ℕ) →
      (S ∈ E ↔ T ∈ E)) :
    ProbabilityTheory.mgf (eventIndicator E) fairBits (-1) ≤
      Real.exp (-(fairBits.real (bitsToSet ⁻¹' E) / 2)) := by
  rw [mgf_eventIndicator_neg_one hE]
  have hp : 0 ≤ fairBits.real (bitsToSet ⁻¹' E) := measureReal_nonneg
  calc
    1 - (1 - Real.exp (-1)) * fairBits.real (bitsToSet ⁻¹' E) ≤
        1 - fairBits.real (bitsToSet ⁻¹' E) / 2 := by
      nlinarith [Real.exp_neg_one_lt_half]
    _ ≤ Real.exp (-(fairBits.real (bitsToSet ⁻¹' E) / 2)) :=
      Real.one_sub_le_exp_neg _

/-- A Poisson--binomial Chernoff bound at the fixed exponential parameter
`-1`.  Unlike Hoeffding, its exponent is linear in the total success
probability, which is essential when there are exponentially many rare trials. -/
lemma independent_event_lower_tail_bound {ι : Type*}
    (u : ι → Finset ℕ) (E : ι → Set (Set ℕ)) (s : Finset ι) (t : ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j))
    (hE : ∀ i, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i)) :
    fairBits.real {ω | eventCount s E ω < t} ≤
      Real.exp ((t : ℝ) -
        (1 / 2) * ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i)) := by
  classical
  let X : ι → (ℕ → Prop) → ℝ := fun i ↦ eventIndicator (E i)
  have hXm : ∀ i, Measurable (X i) :=
    fun i ↦ measurable_eventIndicator_of_supported (hE i)
  have hXi : iIndepFun X fairBits := eventIndicator_iIndep u E hdisj hE
  have hsingleInt : ∀ i ∈ s,
      Integrable (fun ω ↦ Real.exp ((-1 : ℝ) * X i ω)) fairBits := by
    intro i hi
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards [] with ω
    dsimp [X]
    simp only [eventIndicator]
    split_ifs <;> norm_num
  have hsumInt : Integrable
      (fun ω ↦ Real.exp ((-1 : ℝ) * (∑ i ∈ s, X i) ω)) fairBits :=
    hXi.integrable_exp_mul_sum hXm hsingleInt
  have hchern := ProbabilityTheory.measure_le_le_exp_mul_mgf
    (X := ∑ i ∈ s, X i) (t := (-1 : ℝ)) (μ := fairBits)
    (t : ℝ) (by norm_num) hsumInt
  have hmgfEq : ProbabilityTheory.mgf (∑ i ∈ s, X i) fairBits (-1) =
      ∏ i ∈ s, ProbabilityTheory.mgf (X i) fairBits (-1) :=
    hXi.mgf_sum hXm s
  have hmgf : ProbabilityTheory.mgf (∑ i ∈ s, X i) fairBits (-1) ≤
      Real.exp (-(1 / 2) *
        ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i)) := by
    rw [hmgfEq]
    calc
      ∏ i ∈ s, ProbabilityTheory.mgf (X i) fairBits (-1) ≤
          ∏ i ∈ s,
            Real.exp (-(fairBits.real (bitsToSet ⁻¹' E i) / 2)) := by
        exact Finset.prod_le_prod
          (fun i hi ↦ ProbabilityTheory.mgf_nonneg)
          (fun i hi ↦ mgf_eventIndicator_neg_one_le (hE i))
      _ = Real.exp (∑ i ∈ s,
          -(fairBits.real (bitsToSet ⁻¹' E i) / 2)) := by
        rw [Real.exp_sum]
      _ = Real.exp (-(1 / 2) *
          ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i)) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hsubset : {ω | eventCount s E ω < t} ⊆
      {ω | (∑ i ∈ s, X i) ω ≤ (t : ℝ)} := by
    intro ω hω
    change eventCount s E ω < t at hω
    show (∑ i ∈ s, X i) ω ≤ (t : ℝ)
    dsimp [X]
    simp only [Finset.sum_apply]
    rw [sum_eventIndicator_eq_eventCount]
    exact_mod_cast hω.le
  calc
    fairBits.real {ω | eventCount s E ω < t} ≤
        fairBits.real {ω | (∑ i ∈ s, X i) ω ≤ (t : ℝ)} :=
      measureReal_mono hsubset (measure_lt_top fairBits _).ne
    _ ≤ Real.exp (-(-1 : ℝ) * (t : ℝ)) *
        ProbabilityTheory.mgf (∑ i ∈ s, X i) fairBits (-1) := hchern
    _ ≤ Real.exp (t : ℝ) *
        Real.exp (-(1 / 2) *
          ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i)) := by
      have hm : ProbabilityTheory.mgf (∑ i ∈ s, X i) fairBits (-1) ≤
          Real.exp (-(1 / 2) *
            ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i)) := hmgf
      have hm' : ProbabilityTheory.mgf (∑ i ∈ s, X i) fairBits (-1) ≤
          Real.exp (-(1 / 2 *
            ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i))) := by
        convert hm using 1 <;> ring_nf
      norm_num
      exact mul_le_mul_of_nonneg_left hm' (Real.exp_pos _).le
    _ = Real.exp ((t : ℝ) -
        (1 / 2) * ∑ i ∈ s, fairBits.real (bitsToSet ⁻¹' E i)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A deliberately crude finite lower-tail bound.  Its exponential factor is
enough for the alteration argument, and its proof uses only independence and a
union bound over subsets of failed trials. -/
lemma independent_lower_tail_bound {ι : Type*}
    (u : ι → Finset ℕ) (E : ι → Set (Set ℕ)) (s : Finset ι)
    (p : ℝ) (t : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : t ≤ s.card)
    (hdisj : ∀ i j, i ≠ j → Disjoint (u i) (u j))
    (hE : ∀ i, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i))
    (hprob : ∀ i ∈ s, p ≤ fairBits.real (bitsToSet ⁻¹' E i)) :
    fairBits.real {ω | eventCount s E ω < t} ≤
      (2 : ℝ) ^ s.card * (1 - p) ^ (s.card - t + 1) := by
  classical
  let r := s.card - t + 1
  let largeFailures := s.powerset.filter (fun F ↦ r ≤ F.card)
  let failureEvent : Finset ι → Set (ℕ → Prop) :=
    fun F ↦ ⋂ i ∈ F, (bitsToSet ⁻¹' E i)ᶜ
  have hmeas : ∀ i, MeasurableSet (bitsToSet ⁻¹' E i) := by
    intro i
    rw [preimage_allowedRestrictions_of_supported (hE i)]
    exact (MeasurableSet.of_discrete :
      MeasurableSet (allowedRestrictions (u i) (E i))).preimage
        (measurable_pi_lambda _ (fun j ↦ by
          simpa only [restrictBits] using (measurable_pi_apply (j : ℕ))))
  have hsubset : {ω | eventCount s E ω < t} ⊆
      ⋃ F ∈ largeFailures, failureEvent F := by
    intro ω hω
    change eventCount s E ω < t at hω
    let good := s.filter fun i ↦ bitsToSet ω ∈ E i
    let bad := s.filter fun i ↦ bitsToSet ω ∉ E i
    have hpartition : good.card + bad.card = s.card := by
      dsimp [good, bad]
      simpa only [not_not] using Finset.card_filter_add_card_filter_not
        (s := s) (fun i ↦ bitsToSet ω ∈ E i)
    have hbadcard : r ≤ bad.card := by
      have hgoodcard : good.card < t := by
        simpa only [good, eventCount] using hω
      dsimp [r]
      omega
    obtain ⟨F, hFbad, hFcard⟩ := Finset.exists_subset_card_eq hbadcard
    have hFL : F ∈ largeFailures := by
      simp only [largeFailures, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hFbad.trans (Finset.filter_subset _ _), by omega⟩
    simp only [Set.mem_iUnion]
    refine ⟨F, hFL, ?_⟩
    dsimp [failureEvent]
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
    intro i hi
    exact (Finset.mem_filter.mp (hFbad hi)).2
  have hfailure : ∀ F ∈ largeFailures,
      fairBits.real (failureEvent F) ≤ (1 - p) ^ r := by
    intro F hFL
    have hFL' := Finset.mem_filter.mp hFL
    have hprod := fairBits_measureReal_biInter_supported_eq_prod u
      (fun i ↦ (E i)ᶜ) F hdisj (by
        intro i S T hST
        simpa only [Set.mem_compl_iff] using not_congr (hE i hST))
    have hcomp : ∀ i ∈ F,
        fairBits.real (bitsToSet ⁻¹' (E i)ᶜ) ≤ 1 - p := by
      intro i hi
      have hiS : i ∈ s := (Finset.mem_powerset.mp hFL'.1) hi
      rw [Set.preimage_compl, measureReal_compl (hmeas i)]
      have huniv : fairBits.real Set.univ = 1 := by simp
      rw [huniv]
      linarith [hprob i hiS]
    have hbase0 : 0 ≤ 1 - p := by linarith
    have hbase1 : 1 - p ≤ 1 := by linarith
    calc
      fairBits.real (failureEvent F) =
          ∏ i ∈ F, fairBits.real (bitsToSet ⁻¹' (E i)ᶜ) := by
        simpa only [failureEvent, Set.preimage_compl] using hprod
      _ ≤ ∏ _i ∈ F, (1 - p) := by
        exact Finset.prod_le_prod (fun i hi ↦ measureReal_nonneg) hcomp
      _ = (1 - p) ^ F.card := by simp
      _ ≤ (1 - p) ^ r :=
        pow_le_pow_of_le_one hbase0 hbase1 hFL'.2
  have hlargecard : largeFailures.card ≤ 2 ^ s.card := by
    calc
      largeFailures.card ≤ s.powerset.card := Finset.card_filter_le _ _
      _ = 2 ^ s.card := Finset.card_powerset s
  have hpow0 : 0 ≤ (1 - p) ^ r := pow_nonneg (by linarith) _
  calc
    fairBits.real {ω | eventCount s E ω < t} ≤
        fairBits.real (⋃ F ∈ largeFailures, failureEvent F) :=
      measureReal_mono hsubset (measure_lt_top fairBits _).ne
    _ ≤ ∑ F ∈ largeFailures, fairBits.real (failureEvent F) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _F ∈ largeFailures, (1 - p) ^ r :=
      Finset.sum_le_sum hfailure
    _ = (largeFailures.card : ℝ) * (1 - p) ^ r := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ s.card * (1 - p) ^ r := by
      gcongr
      exact_mod_cast hlargecard
    _ = (2 : ℝ) ^ s.card * (1 - p) ^ (s.card - t + 1) := rfl

/-! ### Prime intervals used for blue labels -/

def primesBetween (a b : ℕ) : Finset ℕ :=
  (Finset.Icc a b).filter Nat.Prime

@[simp] lemma mem_primesBetween {a b p : ℕ} :
    p ∈ primesBetween a b ↔ a ≤ p ∧ p ≤ b ∧ p.Prime := by
  simp [primesBetween, and_assoc]

lemma primesBetween_eq_sdiff (a b : ℕ) (hab : a ≤ b + 1) :
    primesBetween a b = Nat.primesLE b \ Nat.primesLE (a - 1) := by
  ext p
  simp only [mem_primesBetween, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨hap, hpb, hp⟩
    exact ⟨⟨hpb, hp⟩, fun h ↦ by
      have := hp.two_le
      omega⟩
  · rintro ⟨⟨hpb, hp⟩, hpa⟩
    have hap : a ≤ p := by
      by_contra h
      apply hpa
      exact ⟨by omega, hp⟩
    exact ⟨hap, hpb, hp⟩

lemma card_primesBetween (a b : ℕ) (hab : a ≤ b + 1) :
    (primesBetween a b).card = Nat.primeCounting b - Nat.primeCounting (a - 1) := by
  rw [primesBetween_eq_sdiff a b hab,
    Finset.card_sdiff_of_subset (Nat.primesLE_mono (by omega))]
  simp

/-- A coarse Chebyshev consequence: a fixed multiplicative interval contains
linearly many primes up to the unavoidable logarithmic factor.  The generous
factor `16` keeps the proof within Mathlib's explicit Chebyshev bounds. -/
lemma eventually_div_log_le_card_primesBetween :
    ∀ᶠ P : ℕ in atTop,
      (P : ℝ) / Real.log P ≤ ((primesBetween P (16 * P)).card : ℝ) := by
  have hupperR := Chebyshev.eventually_primeCounting_le
    (ε := (1 / 2 : ℝ)) (by norm_num)
  have hupperN := (tendsto_natCast_atTop_atTop (R := ℝ)) hupperR
  filter_upwards [hupperN, eventually_ge_atTop (100 : ℕ)] with P hupper hP
  have hP1 : (1 : ℝ) < P := by exact_mod_cast (show 1 < P by omega)
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have h16Ppos : (0 : ℝ) < 16 * P := by positivity
  have hlog16P : 0 < Real.log (16 * P : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 16 * P by omega)
  have hlog_mon : Real.log (16 : ℝ) ≤ Real.log P := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 16 ≤ P by omega))
  have hlog_den : Real.log (16 * P : ℕ) ≤ 2 * Real.log P := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
      (by positivity : (P : ℝ) ≠ 0)]
    linarith
  have hlog_err : Real.log ((16 * P + 1 : ℕ) : ℝ) ≤ (P : ℝ) := by
    have hraw := Real.log_le_rpow_div
      (show (0 : ℝ) ≤ (((16 * P : ℕ) : ℝ) + 1) by positivity)
      (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)
    have hsqrt_sq : Real.sqrt ((((16 * P : ℕ) : ℝ) + 1)) ^ 2 =
        (((16 * P : ℕ) : ℝ) + 1) := Real.sq_sqrt (by positivity)
    have hsqrt0 : 0 ≤ Real.sqrt ((((16 * P : ℕ) : ℝ) + 1)) := Real.sqrt_nonneg _
    rw [← Real.sqrt_eq_rpow] at hraw
    norm_num [div_eq_mul_inv] at hraw
    push_cast at hsqrt_sq
    have hPR : (100 : ℝ) ≤ P := by exact_mod_cast hP
    have hsq : 4 * ((16 : ℝ) * P + 1) ≤ (P : ℝ) ^ 2 := by
      nlinarith
    have hsqrt_le : 2 * Real.sqrt (((16 * P : ℕ) : ℝ) + 1) ≤ (P : ℝ) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      calc
        (2 * Real.sqrt (((16 * P : ℕ) : ℝ) + 1)) ^ 2 =
            4 * ((16 : ℝ) * P + 1) := by
          push_cast at hsqrt_sq ⊢
          nlinarith
        _ ≤ (P : ℝ) ^ 2 := hsq
    push_cast
    nlinarith
  have hnum : (10 : ℝ) * P ≤
      ((16 * P : ℕ) : ℝ) * Real.log 2 - Real.log ((16 * P + 1 : ℕ) : ℝ) := by
    have hcoef : (11 : ℝ) < 16 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    push_cast at hlog_err ⊢
    nlinarith
  have hlowerQuot : (5 : ℝ) * P / Real.log P ≤
      (((16 * P : ℕ) : ℝ) * Real.log 2 - Real.log ((16 * P + 1 : ℕ) : ℝ)) /
        Real.log ((16 * P : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hlogP hlog16P).2
    have hden0 : 0 ≤ Real.log ((16 * P : ℕ) : ℝ) := hlog16P.le
    have hP0 : (0 : ℝ) ≤ P := by positivity
    nlinarith
  have hlowerPi : (5 : ℝ) * P / Real.log P ≤
      (Nat.primeCounting (16 * P) : ℝ) :=
    hlowerQuot.trans (by simpa only [Nat.cast_add, Nat.cast_one] using
      (Chebyshev.pi_ge (16 * P)))
  have hlog4 : Real.log (4 : ℝ) < 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_lt_d9]
  have hupperPi : (Nat.primeCounting P : ℝ) ≤
      (2 : ℝ) * P / Real.log P := by
    change (Nat.primeCounting ⌊(P : ℝ)⌋₊ : ℝ) ≤
      (Real.log 4 + 1 / 2) * (P : ℝ) / Real.log P at hupper
    rw [Nat.floor_natCast] at hupper
    calc
      (Nat.primeCounting P : ℝ) ≤
          (Real.log 4 + 1 / 2) * P / Real.log P := hupper
      _ ≤ (2 : ℝ) * P / Real.log P := by
        apply div_le_div_of_nonneg_right _ hlogP.le
        nlinarith
  have hsmall : (Nat.primeCounting (P - 1) : ℝ) ≤
      (2 : ℝ) * P / Real.log P := by
    have hm := Nat.monotone_primeCounting (Nat.sub_le P 1)
    exact (by exact_mod_cast hm :
      (Nat.primeCounting (P - 1) : ℝ) ≤ Nat.primeCounting P) |>.trans hupperPi
  have hcountmono : Nat.primeCounting (P - 1) ≤ Nat.primeCounting (16 * P) :=
    Nat.monotone_primeCounting (by omega)
  rw [card_primesBetween P (16 * P) (by omega), Nat.cast_sub hcountmono]
  ring_nf at hlowerPi hsmall ⊢
  nlinarith

private lemma self_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m
  | 0 => by norm_num
  | m + 1 => by
      rw [pow_succ]
      have hm := self_le_two_pow m
      have hpos : 0 < 2 ^ m := by positivity
      omega

/-- A deliberately coarse upper Chebyshev bound, isolated for the elementary
sieve used by the red channels. -/
lemma eventually_primeCounting_le_four_mul_div_log :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤ 4 * (N : ℝ) / Real.log N := by
  have hupperR := Chebyshev.eventually_primeCounting_le
    (ε := (1 : ℝ)) (by norm_num)
  have hupperN := (tendsto_natCast_atTop_atTop (R := ℝ)) hupperR
  filter_upwards [hupperN, eventually_ge_atTop (3 : ℕ)] with N hupper hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlog4 : Real.log (4 : ℝ) < 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_lt_d9]
  change (Nat.primeCounting ⌊(N : ℝ)⌋₊ : ℝ) ≤
    (Real.log 4 + 1) * (N : ℝ) / Real.log N at hupper
  rw [Nat.floor_natCast] at hupper
  calc
    (Nat.primeCounting N : ℝ) ≤
        (Real.log 4 + 1) * N / Real.log N := hupper
    _ ≤ 4 * N / Real.log N := by
      apply div_le_div_of_nonneg_right _ hlogN.le
      have hN0 : (0 : ℝ) ≤ N := by positivity
      nlinarith

/-- On a dyadic prime interval at a sufficiently high exponent, the sum of
reciprocals is at most `16/(e+1)`.  This weak form is enough because the
scale-wide blue envelope has only a fixed number of dyadic levels. -/
lemma eventually_sum_primesBetween_dyadic_inv_le :
    ∀ᶠ e : ℕ in atTop,
      ∑ p ∈ primesBetween (2 ^ e) (2 ^ (e + 1)), (1 / (p : ℝ)) ≤
        16 / (e + 1 : ℝ) := by
  have hupper := eventually_primeCounting_le_four_mul_div_log
  rw [eventually_atTop] at hupper ⊢
  obtain ⟨N₀, hN₀⟩ := hupper
  refine ⟨N₀ + 2, ?_⟩
  intro e he
  have hpowN : N₀ ≤ 2 ^ (e + 1) := by
    calc
      N₀ ≤ 2 ^ N₀ := self_le_two_pow N₀
      _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
  have hpi := hN₀ (2 ^ (e + 1)) hpowN
  have hepos : 0 < (e + 1 : ℝ) := by positivity
  have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogpow : Real.log ((2 ^ (e + 1) : ℕ) : ℝ) =
      (e + 1 : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hdenpos : 0 < Real.log ((2 ^ (e + 1) : ℕ) : ℝ) := by
    rw [hlogpow]
    positivity
  have hcard : ((primesBetween (2 ^ e) (2 ^ (e + 1))).card : ℝ) ≤
      (Nat.primeCounting (2 ^ (e + 1)) : ℝ) := by
    rw [card_primesBetween (2 ^ e) (2 ^ (e + 1)) (by omega)]
    exact_mod_cast Nat.sub_le _ _
  calc
    ∑ p ∈ primesBetween (2 ^ e) (2 ^ (e + 1)), (1 / (p : ℝ)) ≤
        ∑ _p ∈ primesBetween (2 ^ e) (2 ^ (e + 1)),
          (1 / ((2 ^ e : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (mem_primesBetween.mp hp).1
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hp')
    _ = ((primesBetween (2 ^ e) (2 ^ (e + 1))).card : ℝ) /
        ((2 ^ e : ℕ) : ℝ) := by
      simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ (Nat.primeCounting (2 ^ (e + 1)) : ℝ) /
        ((2 ^ e : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right hcard (by positivity)
    _ ≤ (4 * ((2 ^ (e + 1) : ℕ) : ℝ) /
        Real.log ((2 ^ (e + 1) : ℕ) : ℝ)) /
          ((2 ^ e : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right hpi (by positivity)
    _ ≤ 16 / (e + 1 : ℝ) := by
      rw [hlogpow]
      push_cast
      have hpowpos : (0 : ℝ) < 2 ^ e := by positivity
      have hden : 0 < (e + 1 : ℝ) * Real.log 2 := by positivity
      have hpowSucc : (2 : ℝ) ^ (e + 1) = 2 * 2 ^ e := by
        rw [pow_succ]
        ring
      field_simp
      nlinarith

/-! ### Integer macroblocks -/

/-- The base used for target blocks when a summand macroblock has `W` binary
digits.  Target blocks have one additional binary digit per scale. -/
def targetBase (W : ℕ) : ℕ := 2 ^ (W + 1)

def summandBase (W : ℕ) : ℕ := 2 ^ W

def targetBlock (W k : ℕ) : Finset ℕ :=
  Finset.Ico ((targetBase W) ^ k) ((targetBase W) ^ (k + 1))

def targetScale (W n : ℕ) : ℕ := Nat.log (targetBase W) n

/-- The first twenty binary sublevels of a summand macroblock are reserved for
deterministic blue repairs. -/
def blueBlock (W k : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ (W * k)) (2 ^ (W * k + 20))

/-- The remainder of the macroblock carries the untouched Bernoulli red set. -/
def redBlock (W k : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ (W * k + 20)) (2 ^ (W * (k + 1)))

@[simp] lemma mem_targetBlock {W k n : ℕ} :
    n ∈ targetBlock W k ↔ (targetBase W) ^ k ≤ n ∧
      n < (targetBase W) ^ (k + 1) := by
  simp [targetBlock]

@[simp] lemma mem_blueBlock {W k x : ℕ} :
    x ∈ blueBlock W k ↔ 2 ^ (W * k) ≤ x ∧ x < 2 ^ (W * k + 20) := by
  simp [blueBlock]

@[simp] lemma mem_redBlock {W k x : ℕ} :
    x ∈ redBlock W k ↔ 2 ^ (W * k + 20) ≤ x ∧
      x < 2 ^ (W * (k + 1)) := by
  simp [redBlock]

lemma targetBase_one_lt (W : ℕ) : 1 < targetBase W := by
  rw [targetBase]
  exact one_lt_pow₀ (by omega) (by omega)

lemma targetScale_mem_targetBlock {W n : ℕ} (hn : n ≠ 0) :
    n ∈ targetBlock W (targetScale W n) := by
  rw [mem_targetBlock, targetScale]
  exact ⟨Nat.pow_log_le_self _ hn,
    Nat.lt_pow_succ_log_self (targetBase_one_lt W) n⟩

lemma targetScale_tendsto (W : ℕ) : Tendsto (targetScale W) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [eventually_ge_atTop ((targetBase W) ^ K)] with n hn
  exact Nat.le_log_of_pow_le (targetBase_one_lt W) hn

/-- The dynamic blue prime scale.  Division by a point well inside the blue
block makes every label in `[P,16P]` geometrically admissible for large scales. -/
def bluePrimeScale (W k n : ℕ) : ℕ := n / 2 ^ (W * k + 16)

def blueLabels (W k n : ℕ) : Finset ℕ :=
  primesBetween (bluePrimeScale W k n) (16 * bluePrimeScale W k n)

/-- A scale-wide envelope containing every dynamic blue label.  Red lengths
avoid all primes in this envelope, which is what the cross-collision argument
needs. -/
def scaleBluePrimes (W k : ℕ) : Finset ℕ :=
  primesBetween (2 ^ (k - 16)) (2 ^ (k + W + 5))

/-- The scale-wide envelope has asymptotically negligible reciprocal mass.
The proof groups its primes by their binary logarithm and applies the dyadic
Chebyshev estimate above. -/
lemma eventually_sum_scaleBluePrimes_inv_le (W : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ)) ≤ 1 / 2 := by
  have hdyadic := eventually_sum_primesBetween_dyadic_inv_le
  rw [eventually_atTop] at hdyadic ⊢
  obtain ⟨E₀, hE₀⟩ := hdyadic
  refine ⟨E₀ + 16 + 32 * (W + 22) + 16, ?_⟩
  intro k hk
  have hconst : 16 ≤ E₀ + 32 := by omega
  have hpre : 32 * (W + 22) + 16 ≤ E₀ + 16 + 32 * (W + 22) + 16 := by
    calc
      32 * (W + 22) + 16 ≤ 32 * (W + 22) + (E₀ + 32) :=
        Nat.add_le_add_left hconst _
      _ = E₀ + 16 + 32 * (W + 22) + 16 := by ring
  have hadd : 32 * (W + 22) + 16 ≤ k := hpre.trans hk
  have hsub : 32 * (W + 22) ≤ k - 16 := Nat.le_sub_of_add_le hadd
  have hdenNat : 32 * (W + 22) ≤ (k - 16) + 1 := hsub.trans (Nat.le_succ _)
  let levels := Finset.Icc (k - 16) (k + W + 5)
  have hk16 : 16 ≤ k := by omega
  have hlowE : E₀ ≤ k - 16 := by omega
  have hmap : Set.MapsTo (Nat.log 2) (scaleBluePrimes W k : Set ℕ)
      (levels : Set ℕ) := by
    intro p hp
    change Nat.log 2 p ∈ levels
    rw [Finset.mem_Icc]
    have hp' := mem_primesBetween.mp hp
    constructor
    · exact Nat.le_log_of_pow_le (by omega) hp'.1
    · calc
        Nat.log 2 p ≤ Nat.log 2 (2 ^ (k + W + 5)) :=
          Nat.log_monotone hp'.2.1
        _ = k + W + 5 := Nat.log_pow (by omega) _
  have hfiber (e : ℕ) (he : e ∈ levels) :
      ∑ p ∈ scaleBluePrimes W k with Nat.log 2 p = e, (1 / (p : ℝ)) ≤
        16 / (e + 1 : ℝ) := by
    calc
      ∑ p ∈ scaleBluePrimes W k with Nat.log 2 p = e, (1 / (p : ℝ)) ≤
          ∑ p ∈ primesBetween (2 ^ e) (2 ^ (e + 1)), (1 / (p : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hpScale := mem_primesBetween.mp hp.1
          rw [mem_primesBetween]
          have hplow : 2 ^ e ≤ p := by
            rw [← hp.2]
            exact Nat.pow_log_le_self 2 hpScale.2.2.ne_zero
          have hpupper : p ≤ 2 ^ (e + 1) := by
            have hpow := (Nat.lt_pow_succ_log_self (b := 2) (by omega) p).le
            rw [hp.2] at hpow
            simpa only [Nat.succ_eq_add_one] using hpow
          exact ⟨hplow, hpupper, hpScale.2.2⟩
        · intro p _ _
          positivity
      _ ≤ 16 / (e + 1 : ℝ) := by
        apply hE₀
        have := (Finset.mem_Icc.mp he).1
        omega
  have hgroup :
      (∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ))) =
        ∑ e ∈ levels,
          ∑ p ∈ scaleBluePrimes W k with Nat.log 2 p = e, (1 / (p : ℝ)) := by
    exact (Finset.sum_fiberwise_of_maps_to hmap (fun p ↦ (1 / (p : ℝ)))).symm
  rw [hgroup]
  calc
    ∑ e ∈ levels,
        ∑ p ∈ scaleBluePrimes W k with Nat.log 2 p = e, (1 / (p : ℝ)) ≤
        ∑ _e ∈ levels, ((16 : ℝ) / (((k - 16) + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      calc
        ∑ p ∈ scaleBluePrimes W k with Nat.log 2 p = e, (1 / (p : ℝ)) ≤
            16 / (e + 1 : ℝ) := hfiber e he
        _ ≤ (16 : ℝ) / (((k - 16) + 1 : ℕ) : ℝ) := by
          have hloPos : (0 : ℝ) < (((k - 16) + 1 : ℕ) : ℝ) := by positivity
          apply div_le_div_of_nonneg_left (by norm_num) hloPos
          exact_mod_cast Nat.add_le_add_right (Finset.mem_Icc.mp he).1 1
    _ = (W + 22 : ℝ) * ((16 : ℝ) / (((k - 16) + 1 : ℕ) : ℝ)) := by
      have hcardLevels : levels.card = W + 22 := by
        dsimp [levels]
        rw [Nat.card_Icc]
        omega
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [hcardLevels]
      push_cast
      rfl
    _ ≤ 1 / 2 := by
      have hden : (0 : ℝ) < ((k - 16) + 1 : ℕ) := by positivity
      have hdenCast : (32 : ℝ) * (W + 22) ≤ ((k - 16) + 1 : ℕ) := by
        exact_mod_cast hdenNat
      rw [show (W + 22 : ℝ) * ((16 : ℝ) / (((k - 16) + 1 : ℕ) : ℝ)) =
          (16 * (W + 22 : ℝ)) / (((k - 16) + 1 : ℕ) : ℝ) by ring]
      apply (div_le_iff₀ hden).2
      nlinarith only [hdenCast]

/-- Red channels are indexed by their backwards macroblock offset. -/
def redOffsets (W C k : ℕ) : Finset ℕ :=
  Finset.Icc (C * k / W + 2) (2 * C * k / W + 2)

def validRedOffsets (W C k : ℕ) : Finset ℕ :=
  (redOffsets W C k).filter fun d ↦
    d ≤ k ∧ k + W * d + 14 ≤ W * (k - d) + 20

lemma mem_validRedOffsets {W C k d : ℕ} :
    d ∈ validRedOffsets W C k ↔
      d ∈ redOffsets W C k ∧ d ≤ k ∧
        k + W * d + 14 ≤ W * (k - d) + 20 := by
  simp [validRedOffsets, and_assoc]

def redCenterScale (W k d : ℕ) : ℕ :=
  2 ^ (W * (k - d) + W - 5)

def redLengthScale (W k n d : ℕ) : ℕ :=
  n / redCenterScale W k d

/-- Candidate red lengths in a fixed channel, before excluding the blue prime
divisors needed by the rational collision argument. -/
def rawRedLengths (W k n d : ℕ) : Finset ℕ :=
  Finset.Icc (redLengthScale W k n d) (16 * redLengthScale W k n d)

def redLengths (W k n d : ℕ) : Finset ℕ :=
  (rawRedLengths W k n d).filter fun q ↦
    ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q

def badRedLengths (W k n d : ℕ) : Finset ℕ :=
  (rawRedLengths W k n d).filter fun q ↦
    ∃ p ∈ scaleBluePrimes W k, p ∣ q

/-- The same sieved length interval with an arbitrary positive base.  This
parameterized form lets one use many well-separated dyadic subchannels inside
each red macroblock. -/
def sievedLengths (W k P : ℕ) : Finset ℕ :=
  (Finset.Icc P (16 * P)).filter fun q ↦
    ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q

/-- Moving down by five binary digits at a time gives disjoint length scales
while leaving a one-bit gap between the intervals `[P,16P]`. -/
def redSubCenterScale (W k d e : ℕ) : ℕ :=
  2 ^ (W * (k - d) + W - 5 - 5 * e)

def redSubLengthScale (W k n d e : ℕ) : ℕ :=
  n / redSubCenterScale W k d e

def redSubLengths (W k n d e : ℕ) : Finset ℕ :=
  sievedLengths W k (redSubLengthScale W k n d e)

@[simp] lemma mem_redSubLengths {W k n d e q : ℕ} :
    q ∈ redSubLengths W k n d e ↔
      redSubLengthScale W k n d e ≤ q ∧
      q ≤ 16 * redSubLengthScale W k n d e ∧
      ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q := by
  simp [redSubLengths, sievedLengths, and_assoc]

/-- Available red subchannels.  The last two inequalities keep their entire
coordinate support in the red portion of macroblock `k-d`. -/
def validRedSubchannels (W C k : ℕ) : Finset (ℕ × ℕ) :=
  ((redOffsets W C k).product (Finset.range ((W - 50) / 5 + 1))).filter
    fun de ↦ de.1 ≤ k ∧ 5 * de.2 + 50 ≤ W ∧
      k + W * de.1 + 5 * de.2 + 14 ≤ W * (k - de.1) + 20

lemma mem_validRedSubchannels {W C k d e : ℕ} :
    (d, e) ∈ validRedSubchannels W C k ↔
      d ∈ redOffsets W C k ∧ e < (W - 50) / 5 + 1 ∧ d ≤ k ∧
        5 * e + 50 ≤ W ∧
          k + W * d + 5 * e + 14 ≤ W * (k - d) + 20 := by
  simp [validRedSubchannels, and_assoc]

lemma validRedSubchannels_eq_product {W C k : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k) :
    validRedSubchannels W C k =
      (redOffsets W C k).product (Finset.range ((W - 50) / 5 + 1)) := by
  apply Finset.filter_eq_self.mpr
  rintro ⟨d, e⟩ hde
  change (d, e) ∈ (redOffsets W C k ×ˢ
    Finset.range ((W - 50) / 5 + 1)) at hde
  rw [Finset.mem_product] at hde
  change d ≤ k ∧ 5 * e + 50 ≤ W ∧
    k + W * d + 5 * e + 14 ≤ W * (k - d) + 20
  have hdBounds := Finset.mem_Icc.mp hde.1
  have he : e < (W - 50) / 5 + 1 := Finset.mem_range.mp hde.2
  have hWpos : 0 < W := by omega
  have hWd : W * d ≤ 2 * C * k + 2 * W := by
    calc
      W * d ≤ W * (2 * C * k / W + 2) := Nat.mul_le_mul_left W hdBounds.2
      _ = (2 * C * k / W) * W + 2 * W := by ring
      _ ≤ 2 * C * k + 2 * W :=
        Nat.add_le_add_right (Nat.div_mul_le_self (2 * C * k) W) _
  have hWmul := Nat.mul_le_mul_right k hW
  have hdle : d ≤ k := by
    apply Nat.le_of_mul_le_mul_left (c := W) _ hWpos
    calc
      W * d ≤ 2 * C * k + 2 * W := hWd
      _ ≤ W * k := by nlinarith only [hWmul, hk, hW]
  have heDiv : e ≤ (W - 50) / 5 := by omega
  have heW : 5 * e + 50 ≤ W := by
    calc
      5 * e + 50 ≤ 5 * ((W - 50) / 5) + 50 := by gcongr
      _ ≤ (W - 50) + 50 := by
        gcongr
        simpa only [mul_comm] using Nat.div_mul_le_self (W - 50) 5
      _ = W := Nat.sub_add_cancel (by omega)
  have hmulEq : W * (k - d) + W * d = W * k := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hdle]
  have hvalid : k + W * d + 5 * e + 14 ≤ W * (k - d) + 20 := by
    nlinarith only [hWd, heW, hmulEq, hWmul, hk, hW]
  exact ⟨hdle, heW, hvalid⟩

/-- There are linearly many red subchannels, with coefficient proportional to
the scale-separation constant `C`. -/
lemma validRedSubchannels_card_lower {W C k : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k) :
    C * k / 20 ≤ (validRedSubchannels W C k).card := by
  rw [validRedSubchannels_eq_product hC hW hk]
  change C * k / 20 ≤
    #((redOffsets W C k) ×ˢ Finset.range ((W - 50) / 5 + 1))
  rw [Finset.card_product]
  have hWpos : 0 < W := by omega
  let a := C * k / W
  let b := (W - 50) / 5 + 1
  have hlowle : C * k / W + 2 ≤ 2 * C * k / W + 2 := by
    apply Nat.add_le_add_right
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right k (by omega : C ≤ 2 * C)
  have hcardOffsets : (redOffsets W C k).card ≥ a := by
    rw [redOffsets, Nat.card_Icc]
    dsimp [a]
    have htwice : 2 * (C * k / W) ≤ 2 * C * k / W := by
      rw [Nat.le_div_iff_mul_le hWpos]
      calc
        2 * (C * k / W) * W = 2 * ((C * k / W) * W) := by ring
        _ ≤ 2 * (C * k) := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _)
        _ = 2 * C * k := by ring
    omega
  have hbcard : (Finset.range b).card = b := Finset.card_range b
  rw [hbcard]
  have habCard : a * b ≤ (redOffsets W C k).card * b :=
    Nat.mul_le_mul_right b hcardOffsets
  apply (show C * k / 20 ≤ a * b from ?_).trans habCard
  have haUpper : C * k < (a + 1) * W := by
    rw [← Nat.div_lt_iff_lt_mul hWpos]
    dsimp [a]
    omega
  have hCkTwoW : 2 * W ≤ C * k := by
    exact hk.trans (by simpa only [one_mul] using Nat.mul_le_mul_right k hC)
  have hCk_le : C * k ≤ 2 * a * W := by nlinarith
  have hsubDiv : W - 50 < ((W - 50) / 5 + 1) * 5 := by
    rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < 5)]
    omega
  have hWb : W ≤ 10 * b := by
    have hb10 : 10 ≤ (W - 50) / 5 := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 5)]
      omega
    dsimp [b]
    omega
  have htwenty : C * k ≤ 20 * (a * b) := by
    calc
      C * k ≤ 2 * a * W := hCk_le
      _ ≤ 2 * a * (10 * b) := Nat.mul_le_mul_left (2 * a) hWb
      _ = 20 * (a * b) := by ring
  have hdiv := Nat.div_le_div_right htwenty (c := 20)
  simpa [Nat.mul_comm] using hdiv

lemma card_dvd_filter_Icc_le {P p : ℕ} (hP : 0 < P) :
    ((Finset.Icc P (16 * P)).filter fun q ↦ p ∣ q).card ≤ 16 * P / p := by
  calc
    ((Finset.Icc P (16 * P)).filter fun q ↦ p ∣ q).card ≤
        ((Finset.range (16 * P + 1)).filter fun q ↦ q ≠ 0 ∧ p ∣ q).card := by
      apply Finset.card_le_card
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      rw [Finset.mem_Icc] at hq
      exact ⟨by simp; omega, by omega, hq.2⟩
    _ = 16 * P / p := by
      simpa only [Nat.succ_eq_add_one] using Nat.card_multiples' (16 * P) p

lemma card_badRedLengths_le_sum_div {W k n d : ℕ}
    (hP : 0 < redLengthScale W k n d) :
    (badRedLengths W k n d).card ≤
      ∑ p ∈ scaleBluePrimes W k, 16 * redLengthScale W k n d / p := by
  let P := redLengthScale W k n d
  let multiples := fun p : ℕ ↦ (Finset.Icc P (16 * P)).filter fun q ↦ p ∣ q
  have hsubset : badRedLengths W k n d ⊆
      (scaleBluePrimes W k).biUnion multiples := by
    intro q hq
    rw [badRedLengths, Finset.mem_filter] at hq
    rcases hq.2 with ⟨p, hp, hpq⟩
    rw [Finset.mem_biUnion]
    refine ⟨p, hp, ?_⟩
    rw [Finset.mem_filter]
    simpa only [rawRedLengths, P] using ⟨hq.1, hpq⟩
  calc
    (badRedLengths W k n d).card ≤
        ((scaleBluePrimes W k).biUnion multiples).card := Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ scaleBluePrimes W k, (multiples p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ scaleBluePrimes W k, 16 * P / p := by
      apply Finset.sum_le_sum
      intro p _
      exact card_dvd_filter_Icc_le (by simpa only [P] using hP)
    _ = ∑ p ∈ scaleBluePrimes W k, 16 * redLengthScale W k n d / p := by
      rfl

lemma card_badRedLengths_le_eight_mul {W k n d : ℕ}
    (hP : 0 < redLengthScale W k n d)
    (hrecip : ∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ)) ≤ 1 / 2) :
    (badRedLengths W k n d).card ≤ 8 * redLengthScale W k n d := by
  let P := redLengthScale W k n d
  have hnat := card_badRedLengths_le_sum_div (W := W) (k := k) (n := n) (d := d) hP
  have hcast : ((badRedLengths W k n d).card : ℝ) ≤
      ∑ p ∈ scaleBluePrimes W k, ((16 * P / p : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hdiv :
      (∑ p ∈ scaleBluePrimes W k, ((16 * P / p : ℕ) : ℝ)) ≤
        ∑ p ∈ scaleBluePrimes W k, (16 * (P : ℝ)) * (1 / (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p _
    calc
      ((16 * P / p : ℕ) : ℝ) ≤ ((16 * P : ℕ) : ℝ) / (p : ℝ) :=
        Nat.cast_div_le
      _ = (16 * (P : ℝ)) * (1 / (p : ℝ)) := by
        push_cast
        simp [div_eq_mul_inv]
  have hreal : ((badRedLengths W k n d).card : ℝ) ≤ 8 * (P : ℝ) := by
    calc
      ((badRedLengths W k n d).card : ℝ) ≤
          ∑ p ∈ scaleBluePrimes W k, ((16 * P / p : ℕ) : ℝ) := hcast
      _ ≤ ∑ p ∈ scaleBluePrimes W k,
          (16 * (P : ℝ)) * (1 / (p : ℝ)) := hdiv
      _ = (16 * (P : ℝ)) *
          (∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ))) := by
        rw [Finset.mul_sum]
      _ ≤ (16 * (P : ℝ)) * (1 / 2) := by
        gcongr
      _ = 8 * (P : ℝ) := by ring
  exact_mod_cast hreal

lemma redLengths_card_lower {W k n d : ℕ}
    (hP : 0 < redLengthScale W k n d)
    (hrecip : ∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ)) ≤ 1 / 2) :
    7 * redLengthScale W k n d ≤ (redLengths W k n d).card := by
  let P := redLengthScale W k n d
  have hbad := card_badRedLengths_le_eight_mul hP hrecip
  have hraw : (rawRedLengths W k n d).card = 15 * P + 1 := by
    rw [rawRedLengths, Nat.card_Icc]
    dsimp [P]
    omega
  have hpartition : (redLengths W k n d).card + (badRedLengths W k n d).card =
      (rawRedLengths W k n d).card := by
    rw [redLengths, badRedLengths]
    have hbadEq :
        (rawRedLengths W k n d).filter
            (fun q ↦ ∃ p ∈ scaleBluePrimes W k, p ∣ q) =
          (rawRedLengths W k n d).filter
            (fun q ↦ ¬ ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q) := by
      ext q
      simp only [Finset.mem_filter, not_forall, not_not, exists_prop]
    rw [hbadEq]
    exact Finset.card_filter_add_card_filter_not
      (s := rawRedLengths W k n d)
      (fun q ↦ ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q)
  change (badRedLengths W k n d).card ≤ 8 * P at hbad
  have hgoal : 7 * P ≤ (redLengths W k n d).card := by omega
  simpa only [P] using hgoal

/-- At most half of an arbitrary interval `[P,16P]` is removed by the
scale-wide prime sieve. -/
lemma sievedLengths_card_lower {W k P : ℕ}
    (hP : 0 < P)
    (hrecip : ∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ)) ≤ 1 / 2) :
    7 * P ≤ (sievedLengths W k P).card := by
  let bad := (Finset.Icc P (16 * P)).filter fun q ↦
    ∃ p ∈ scaleBluePrimes W k, p ∣ q
  let multiples := fun p : ℕ ↦ (Finset.Icc P (16 * P)).filter fun q ↦ p ∣ q
  have hsubset : bad ⊆ (scaleBluePrimes W k).biUnion multiples := by
    intro q hq
    dsimp only [bad] at hq
    rw [Finset.mem_filter] at hq
    rcases hq.2 with ⟨p, hp, hpq⟩
    rw [Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_filter.mpr ⟨hq.1, hpq⟩⟩
  have hbadNat : bad.card ≤
      ∑ p ∈ scaleBluePrimes W k, 16 * P / p := by
    calc
      bad.card ≤ ((scaleBluePrimes W k).biUnion multiples).card :=
        Finset.card_le_card hsubset
      _ ≤ ∑ p ∈ scaleBluePrimes W k, (multiples p).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ scaleBluePrimes W k, 16 * P / p := by
        apply Finset.sum_le_sum
        intro p _
        exact card_dvd_filter_Icc_le hP
  have hbadReal : (bad.card : ℝ) ≤ 8 * P := by
    have hcast : (bad.card : ℝ) ≤
        ∑ p ∈ scaleBluePrimes W k, ((16 * P / p : ℕ) : ℝ) := by
      exact_mod_cast hbadNat
    calc
      (bad.card : ℝ) ≤
          ∑ p ∈ scaleBluePrimes W k, ((16 * P / p : ℕ) : ℝ) := hcast
      _ ≤ ∑ p ∈ scaleBluePrimes W k,
          (16 * (P : ℝ)) * (1 / (p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p _
        calc
          ((16 * P / p : ℕ) : ℝ) ≤ ((16 * P : ℕ) : ℝ) / (p : ℝ) :=
            Nat.cast_div_le
          _ = (16 * (P : ℝ)) * (1 / (p : ℝ)) := by
            push_cast
            simp [div_eq_mul_inv]
      _ = (16 * (P : ℝ)) *
          (∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ))) := by
        rw [Finset.mul_sum]
      _ ≤ (16 * (P : ℝ)) * (1 / 2) := by gcongr
      _ = 8 * P := by ring
  have hbad : bad.card ≤ 8 * P := by exact_mod_cast hbadReal
  have hraw : (Finset.Icc P (16 * P)).card = 15 * P + 1 := by
    rw [Nat.card_Icc]
    omega
  have hpartition : (sievedLengths W k P).card + bad.card =
      (Finset.Icc P (16 * P)).card := by
    rw [sievedLengths]
    dsimp only [bad]
    have heq : (Finset.Icc P (16 * P)).filter
          (fun q ↦ ∃ p ∈ scaleBluePrimes W k, p ∣ q) =
        (Finset.Icc P (16 * P)).filter
          (fun q ↦ ¬ ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q) := by
      ext q
      simp only [Finset.mem_filter, not_forall, not_not, exists_prop]
    rw [heq]
    exact Finset.card_filter_add_card_filter_not
      (s := Finset.Icc P (16 * P))
      (fun q ↦ ∀ p ∈ scaleBluePrimes W k, ¬p ∣ q)
  omega

lemma redSubLengths_card_lower {W k n d e : ℕ}
    (hP : 0 < redSubLengthScale W k n d e)
    (hrecip : ∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ)) ≤ 1 / 2) :
    7 * redSubLengthScale W k n d e ≤
      (redSubLengths W k n d e).card := by
  exact sievedLengths_card_lower hP hrecip

/-- A narrowed core of a subchannel.  Its one-unit lower margin and sixteen-unit
upper margin survive changing the quotient scale by at most one. -/
def coreRedSubLengths (W k n d e : ℕ) : Finset ℕ :=
  (redSubLengths W k n d e).filter fun q ↦
    redSubLengthScale W k n d e + 1 ≤ q ∧
      q ≤ 16 * (redSubLengthScale W k n d e - 1)

@[simp] lemma mem_coreRedSubLengths {W k n d e q : ℕ} :
    q ∈ coreRedSubLengths W k n d e ↔
      q ∈ redSubLengths W k n d e ∧
      redSubLengthScale W k n d e + 1 ≤ q ∧
      q ≤ 16 * (redSubLengthScale W k n d e - 1) := by
  simp [coreRedSubLengths, and_assoc]

lemma coreRedSubLengths_card_lower {W k n d e : ℕ}
    (hP : 17 ≤ redSubLengthScale W k n d e)
    (hrecip : ∑ p ∈ scaleBluePrimes W k, (1 / (p : ℝ)) ≤ 1 / 2) :
    6 * redSubLengthScale W k n d e ≤
      (coreRedSubLengths W k n d e).card := by
  let P := redSubLengthScale W k n d e
  let s := redSubLengths W k n d e
  let good : ℕ → Prop := fun q ↦ P + 1 ≤ q ∧ q ≤ 16 * (P - 1)
  let excluded := s.filter fun q ↦ ¬good q
  have hsCard : 7 * P ≤ s.card := by
    dsimp [s, P]
    exact redSubLengths_card_lower (by omega) hrecip
  have hexcluded : excluded ⊆ Finset.Icc P P ∪ Finset.Icc (16 * P - 15) (16 * P) := by
    intro q hq
    dsimp only [excluded] at hq
    rw [Finset.mem_filter] at hq
    have hqb := mem_redSubLengths.mp hq.1
    change P ≤ q ∧ q ≤ 16 * P ∧ _ at hqb
    simp only [good, not_and_or, not_le] at hq
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    rcases hq.2 with hlo | hhi
    · left; omega
    · right; omega
  have hIccOne : (Finset.Icc P P).card = 1 := by simp
  have hIccSixteen : (Finset.Icc (16 * P - 15) (16 * P)).card = 16 := by
    rw [Nat.card_Icc]
    have : 15 ≤ 16 * P := by omega
    omega
  have hexcludedCard : excluded.card ≤ 17 := by
    calc
      excluded.card ≤
          (Finset.Icc P P ∪ Finset.Icc (16 * P - 15) (16 * P)).card :=
        Finset.card_le_card hexcluded
      _ ≤ (Finset.Icc P P).card +
          (Finset.Icc (16 * P - 15) (16 * P)).card :=
        Finset.card_union_le _ _
      _ = 17 := by rw [hIccOne, hIccSixteen]
  have hpartition : (coreRedSubLengths W k n d e).card + excluded.card = s.card := by
    change (s.filter good).card + (s.filter fun q ↦ ¬good q).card = s.card
    simpa only [good] using Finset.card_filter_add_card_filter_not
      (s := s) (fun q ↦ P + 1 ≤ q ∧ q ≤ 16 * (P - 1))
  change 6 * P ≤ (coreRedSubLengths W k n d e).card
  omega

private lemma sixteen_mul_pow_two (e : ℕ) : 16 * 2 ^ e = 2 ^ (e + 4) := by
  rw [pow_add]
  norm_num
  ring

lemma bluePrimeScale_lower {W k n : ℕ} (hk : 16 ≤ k)
    (hn : n ∈ targetBlock W k) :
    2 ^ (k - 16) ≤ bluePrimeScale W k n := by
  have hden : 0 < 2 ^ (W * k + 16) := by positivity
  rw [bluePrimeScale, Nat.le_div_iff_mul_le hden]
  calc
    2 ^ (k - 16) * 2 ^ (W * k + 16) = 2 ^ ((W + 1) * k) := by
      rw [← pow_add]
      congr 1
      simp only [Nat.add_mul, one_mul]
      omega
    _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
    _ ≤ n := (mem_targetBlock.mp hn).1

lemma eventually_blueLabels_prime_lower (W : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k,
      (bluePrimeScale W k n : ℝ) / Real.log (bluePrimeScale W k n) ≤
        ((blueLabels W k n).card : ℝ) := by
  have hprime := eventually_div_log_le_card_primesBetween
  rw [eventually_atTop] at hprime ⊢
  obtain ⟨P₀, hP₀⟩ := hprime
  refine ⟨P₀ + 16, ?_⟩
  intro k hk n hn
  apply hP₀
  calc
    P₀ ≤ 2 ^ P₀ := self_le_two_pow P₀
    _ ≤ 2 ^ (k - 16) := Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    _ ≤ bluePrimeScale W k n := bluePrimeScale_lower (by omega) hn

lemma blueLabels_subset_scaleBluePrimes {W k n : ℕ} (hW : 2 ≤ W)
    (hk : W + 16 ≤ k) (hn : n ∈ targetBlock W k) :
    blueLabels W k n ⊆ scaleBluePrimes W k := by
  intro p hp
  rw [scaleBluePrimes, mem_primesBetween]
  have hp' := mem_primesBetween.mp hp
  have hlow := bluePrimeScale_lower (by omega) hn
  have hnBounds := mem_targetBlock.mp hn
  have hden : 0 < 2 ^ (W * k + 16) := by positivity
  have hPUpper : bluePrimeScale W k n < 2 ^ (k + W + 1) := by
    rw [bluePrimeScale, Nat.div_lt_iff_lt_mul hden]
    calc
      n < (targetBase W) ^ (k + 1) := hnBounds.2
      _ = 2 ^ ((W + 1) * (k + 1)) := by simp [targetBase, pow_mul]
      _ ≤ 2 ^ (k + W + 1) * 2 ^ (W * k + 16) := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (n := 2) (by omega)
        simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
        omega
  refine ⟨hlow.trans hp'.1, ?_, hp'.2.2⟩
  exact (calc
    p ≤ 16 * bluePrimeScale W k n := hp'.2.1
    _ < 16 * 2 ^ (k + W + 1) := Nat.mul_lt_mul_of_pos_left hPUpper (by omega)
    _ = 2 ^ (k + W + 5) := by rw [sixteen_mul_pow_two]
    ).le

/-- A convenient deterministic criterion placing every coordinate inspected by
`lengthEvent q n` inside a half-open ambient block. -/
lemma lengthSupport_subset_Ico_of_bounds {L U q n : ℕ} (hq : 0 < q)
    (hleft : L + (q - 1) ≤ n / q)
    (hright : n / q + 5 * q < U) :
    lengthSupport q n ⊆ Finset.Ico L U := by
  intro x hx
  rw [lengthSupport, Finset.mem_Icc] at hx
  rw [Finset.mem_Ico]
  have hsqrt : Nat.sqrt q ≤ q := Nat.sqrt_le_self q
  constructor
  · have hbase : L ≤ baseStart q n := by
      rw [baseStart]
      omega
    exact hbase.trans hx.1
  · have hbase_le : baseStart q n ≤ n / q := by
      rw [baseStart]
      omega
    omega

lemma lengthSupport_subset_Ico_of_divScale {L U D X q n : ℕ}
    (hD : 0 < D) (hP : 0 < n / D) (hq : 0 < q)
    (hqlo : n / D ≤ q) (hqhi : q ≤ 16 * (n / D))
    (hDX : 16 * X ≤ D) (hLX : L + q ≤ X)
    (hU : 2 * D + 5 * q < U) :
    lengthSupport q n ⊆ Finset.Ico L U := by
  have hcenterLow : X ≤ n / q := by
    rw [Nat.le_div_iff_mul_le hq]
    calc
      X * q ≤ X * (16 * (n / D)) := Nat.mul_le_mul_left X hqhi
      _ = (n / D) * (16 * X) := by ring
      _ ≤ (n / D) * D := Nat.mul_le_mul_left _ hDX
      _ ≤ n := Nat.div_mul_le_self n D
  have hnP : n < (n / D + 1) * D := by
    have hmod := Nat.mod_lt n hD
    have hdecomp := Nat.mod_add_div n D
    calc
      n = n % D + D * (n / D) := hdecomp.symm
      _ < D + D * (n / D) := Nat.add_lt_add_right hmod _
      _ = (n / D + 1) * D := by ring
  have hcenterUpper : n / q < 2 * D := by
    have hdivmono : n / q ≤ n / (n / D) := Nat.div_le_div_left hqlo hP
    have hquot : n / (n / D) < 2 * D := by
      rw [Nat.div_lt_iff_lt_mul hP]
      calc
        n < (n / D + 1) * D := hnP
        _ ≤ (2 * D) * (n / D) := by
          calc
            (n / D + 1) * D ≤ (n / D + n / D) * D :=
              Nat.mul_le_mul_right D (by omega)
            _ = (2 * D) * (n / D) := by ring
    omega
  apply lengthSupport_subset_Ico_of_bounds hq
  · omega
  · omega

lemma blueLabel_support_subset {W k n p : ℕ} (hW : 2 ≤ W)
    (hk : W + 16 ≤ k) (hn : n ∈ targetBlock W k)
    (hp : p ∈ blueLabels W k n) :
    lengthSupport p n ⊆ blueBlock W k := by
  let A := 2 ^ (W * k)
  let D := 2 ^ (W * k + 16)
  let P := bluePrimeScale W k n
  have hD : D = 2 ^ (W * k + 16) := rfl
  have hDpos : 0 < D := by positivity
  have hnBounds := mem_targetBlock.mp hn
  have hnLower : 2 ^ ((W + 1) * k) ≤ n := by
    calc
      2 ^ ((W + 1) * k) = (targetBase W) ^ k := by
        simp [targetBase, pow_mul]
      _ ≤ n := hnBounds.1
  have hPLower : 2 ^ (k - 16) ≤ P := by
    dsimp [P, bluePrimeScale]
    rw [Nat.le_div_iff_mul_le hDpos]
    calc
      2 ^ (k - 16) * 2 ^ (W * k + 16) = 2 ^ ((W + 1) * k) := by
        rw [← pow_add]
        congr 1
        simp only [Nat.add_mul, one_mul]
        omega
      _ ≤ n := hnLower
  have hPpos : 0 < P := (pow_pos (by omega) _).trans_le hPLower
  have hPUpper : P < 2 ^ (k + W + 1) := by
    dsimp [P, bluePrimeScale]
    rw [Nat.div_lt_iff_lt_mul hDpos]
    calc
      n < (targetBase W) ^ (k + 1) := hnBounds.2
      _ = 2 ^ ((W + 1) * (k + 1)) := by simp [targetBase, pow_mul]
      _ ≤ 2 ^ (k + W + 1) * 2 ^ (W * k + 16) := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by omega)
        simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
        omega
  have hpBounds := mem_primesBetween.mp hp
  change P ≤ p ∧ p ≤ 16 * P ∧ p.Prime at hpBounds
  have hp0 : 0 < p := hpBounds.2.2.pos
  have hexp : k + W + 5 ≤ W * k := by
    calc
      k + W + 5 ≤ 2 * k := by omega
      _ ≤ W * k := Nat.mul_le_mul_right k hW
  have hpA : p ≤ A := by
    have hpAlt : p < A := calc
      p ≤ 16 * P := hpBounds.2.1
      _ < 16 * 2 ^ (k + W + 1) := Nat.mul_lt_mul_of_pos_left hPUpper (by omega)
      _ = 2 ^ (k + W + 5) := by
        rw [sixteen_mul_pow_two]
      _ ≤ 2 ^ (W * k) := Nat.pow_le_pow_right (n := 2) (by omega) hexp
      _ = A := rfl
    exact hpAlt.le
  have hcenterLow : 2 ^ (W * k + 11) ≤ n / p := by
    rw [Nat.le_div_iff_mul_le hp0]
    calc
      2 ^ (W * k + 11) * p ≤ 2 ^ (W * k + 11) * (16 * P) :=
        Nat.mul_le_mul_left _ hpBounds.2.1
      _ = P * (16 * 2 ^ (W * k + 11)) := by ring
      _ ≤ P * D := by
        gcongr
        rw [hD]
        rw [show 16 = 2 ^ 4 by norm_num, ← pow_add]
        apply Nat.pow_le_pow_right (by omega)
        omega
      _ ≤ n := by
        dsimp [P, bluePrimeScale]
        exact Nat.div_mul_le_self n _
  have hleft : A + (p - 1) ≤ n / p := by
    have hAA : A + A ≤ 2 ^ (W * k + 11) := by
      calc
        A + A = 2 * A := by omega
        _ ≤ 2048 * A := Nat.mul_le_mul_right A (by norm_num)
        _ = 2 ^ (W * k + 11) := by
          dsimp [A]
          rw [pow_add]
          norm_num
          ring
    omega
  have hnP : n < (P + 1) * D := by
    have hmod := Nat.mod_lt n hDpos
    have hdecomp := Nat.mod_add_div n D
    change n < (n / D + 1) * D
    calc
      n = n % D + D * (n / D) := hdecomp.symm
      _ < D + D * (n / D) := Nat.add_lt_add_right hmod _
      _ = (n / D + 1) * D := by ring
  have hcenterUpper : n / p < 2 * D := by
    have hdivmono : n / p ≤ n / P := Nat.div_le_div_left hpBounds.1 hPpos
    have : n / P < 2 * D := by
      rw [Nat.div_lt_iff_lt_mul hPpos]
      calc
        n < (P + 1) * D := hnP
        _ ≤ (2 * D) * P := by
          calc
            (P + 1) * D ≤ (P + P) * D := Nat.mul_le_mul_right D (by omega)
            _ = (2 * D) * P := by ring
    omega
  have hright : n / p + 5 * p < 2 ^ (W * k + 20) := by
    have hDA : D = 2 ^ 16 * A := by
      dsimp [D, A]
      rw [pow_add]
      ring
    have hU : 2 ^ (W * k + 20) = 2 ^ 20 * A := by
      rw [pow_add]
      dsimp [A]
      ring
    calc
      n / p + 5 * p < 2 * D + 5 * p := by omega
      _ ≤ 2 * D + 5 * A := Nat.add_le_add_left (Nat.mul_le_mul_left 5 hpA) _
      _ < 2 ^ (W * k + 20) := by
        rw [hDA, hU]
        have hApos : 0 < A := by positivity
        norm_num
        omega
  simpa only [blueBlock] using
    lengthSupport_subset_Ico_of_bounds hp0 hleft hright

lemma redLength_support_subset {W k n d q : ℕ} (hW : 30 ≤ W)
    (hk : W ≤ k) (hd : d ≤ k)
    (hexp : k + W * d + 14 ≤ W * (k - d) + 20)
    (hn : n ∈ targetBlock W k) (hq : q ∈ redLengths W k n d) :
    lengthSupport q n ⊆ redBlock W (k - d) := by
  let h := k - d
  let A := 2 ^ (W * h + 20)
  let D := redCenterScale W k d
  let P := redLengthScale W k n d
  let X := 2 ^ (W * h + W - 9)
  let U := 2 ^ (W * (h + 1))
  have hDdef : D = 2 ^ (W * h + W - 5) := by
    simp [D, redCenterScale, h]
  have hDpos : 0 < D := by
    rw [hDdef]
    positivity
  have hnBounds := mem_targetBlock.mp hn
  have hD_le_n : D ≤ n := by
    calc
      D = 2 ^ (W * h + W - 5) := hDdef
      _ ≤ 2 ^ ((W + 1) * k) := by
        apply Nat.pow_le_pow_right (n := 2) (by omega)
        have hh_le : h ≤ k := by
          dsimp [h]
          omega
        have hWh : W * h ≤ W * k := Nat.mul_le_mul_left W hh_le
        calc
          W * h + W - 5 ≤ W * h + W := Nat.sub_le _ _
          _ ≤ W * k + W := Nat.add_le_add_right hWh W
          _ ≤ W * k + k := Nat.add_le_add_left hk (W * k)
          _ = (W + 1) * k := by simp only [Nat.add_mul, one_mul]
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := hnBounds.1
  have hPpos : 0 < P := by
    dsimp [P, redLengthScale]
    exact Nat.div_pos hD_le_n hDpos
  have hq' := Finset.mem_filter.mp hq
  have hqBounds := Finset.mem_Icc.mp hq'.1
  change P ≤ q ∧ q ≤ 16 * P at hqBounds
  have hqpos : 0 < q := hPpos.trans_le hqBounds.1
  have hPUpper : P < 2 ^ (k + W * d + 10) := by
    dsimp [P, redLengthScale]
    rw [Nat.div_lt_iff_lt_mul hDpos]
    calc
      n < (targetBase W) ^ (k + 1) := hnBounds.2
      _ = 2 ^ ((W + 1) * (k + 1)) := by simp [targetBase, pow_mul]
      _ ≤ 2 ^ (k + W * d + 10) * D := by
        rw [hDdef, ← pow_add]
        apply Nat.pow_le_pow_right (n := 2) (by omega)
        dsimp [h]
        have hsub : k - d + d = k := Nat.sub_add_cancel hd
        have hmulEq : W * d + W * (k - d) = W * k := by
          rw [← Nat.mul_add]
          congr 1
          omega
        have hExp5 : 5 ≤ W * (k - d) + W := by omega
        have hExpRecover : W * (k - d) + W - 5 + 5 = W * (k - d) + W :=
          Nat.sub_add_cancel hExp5
        simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
        omega
  have hqA : q ≤ A := by
    have hqAlt : q < A := calc
      q ≤ 16 * P := hqBounds.2
      _ < 16 * 2 ^ (k + W * d + 10) :=
        Nat.mul_lt_mul_of_pos_left hPUpper (by omega)
      _ = 2 ^ (k + W * d + 14) := by rw [sixteen_mul_pow_two]
      _ ≤ 2 ^ (W * (k - d) + 20) :=
        Nat.pow_le_pow_right (n := 2) (by omega) hexp
      _ = A := by simp [A, h]
    exact hqAlt.le
  have hDX : 16 * X ≤ D := by
    rw [hDdef]
    dsimp [X, h]
    rw [sixteen_mul_pow_two]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    omega
  have hLX : 2 ^ (W * h + 20) + q ≤ X := by
    have hAA : A + A ≤ X := by
      calc
        A + A = 2 * A := by omega
        _ = 2 ^ (W * h + 21) := by
          dsimp [A]
          rw [show W * h + 21 = (W * h + 20) + 1 by omega, pow_add]
          norm_num
          ring
        _ ≤ 2 ^ (W * h + W - 9) := by
          apply Nat.pow_le_pow_right (n := 2) (by omega)
          omega
        _ = X := rfl
    dsimp [A] at hqA
    omega
  have hUbound : 2 * D + 5 * q < U := by
    have hDU : 16 * D ≤ U := by
      rw [hDdef]
      dsimp [U, h]
      rw [sixteen_mul_pow_two]
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      simp only [Nat.mul_add, mul_one]
      omega
    have hA_D : A ≤ D := by
      rw [hDdef]
      dsimp [A, h]
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      omega
    have hD0 : 0 < D := hDpos
    calc
      2 * D + 5 * q ≤ 2 * D + 5 * A :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 5 hqA) _
      _ ≤ 7 * D := by nlinarith
      _ < 16 * D := by nlinarith
      _ ≤ U := hDU
  simpa only [redBlock, h, U] using
    lengthSupport_subset_Ico_of_divScale hDpos hPpos hqpos
      hqBounds.1 hqBounds.2 hDX hLX hUbound

lemma redLengthScale_pos {W k n d : ℕ} (hW : 5 ≤ W) (hk : W ≤ k)
    (hd : d ≤ k) (hn : n ∈ targetBlock W k) :
    0 < redLengthScale W k n d := by
  let D := redCenterScale W k d
  have hDdef : D = 2 ^ (W * (k - d) + W - 5) := by
    simp [D, redCenterScale]
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hh : k - d ≤ k := Nat.sub_le _ _
  have hWh : W * (k - d) ≤ W * k := Nat.mul_le_mul_left W hh
  have hDle : D ≤ n := by
    calc
      D = 2 ^ (W * (k - d) + W - 5) := hDdef
      _ ≤ 2 ^ ((W + 1) * k) := by
        apply Nat.pow_le_pow_right (n := 2) (by omega)
        calc
          W * (k - d) + W - 5 ≤ W * (k - d) + W := Nat.sub_le _ _
          _ ≤ W * k + W := Nat.add_le_add_right hWh W
          _ ≤ W * k + k := Nat.add_le_add_left hk (W * k)
          _ = (W + 1) * k := by simp only [Nat.add_mul, one_mul]
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  rw [redLengthScale, show redCenterScale W k d = D by rfl]
  exact Nat.div_pos hDle hDpos

lemma redLengthScale_upper {W k n d : ℕ} (hW : 5 ≤ W) (hd : d ≤ k)
    (hn : n ∈ targetBlock W k) :
    redLengthScale W k n d < 2 ^ (k + W * d + 10) := by
  let D := redCenterScale W k d
  have hDdef : D = 2 ^ (W * (k - d) + W - 5) := by
    simp [D, redCenterScale]
  have hDpos : 0 < D := by rw [hDdef]; positivity
  rw [redLengthScale, show redCenterScale W k d = D by rfl,
    Nat.div_lt_iff_lt_mul hDpos]
  calc
    n < (targetBase W) ^ (k + 1) := (mem_targetBlock.mp hn).2
    _ = 2 ^ ((W + 1) * (k + 1)) := by simp [targetBase, pow_mul]
    _ ≤ 2 ^ (k + W * d + 10) * D := by
      rw [hDdef, ← pow_add]
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      have hmulEq : W * d + W * (k - d) = W * k := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have hExp5 : 5 ≤ W * (k - d) + W := by omega
      have hRecover : W * (k - d) + W - 5 + 5 = W * (k - d) + W :=
        Nat.sub_add_cancel hExp5
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
      omega

lemma redLength_lt_globalEnvelope {W C k n d q : ℕ}
    (hW : 5 ≤ W) (hd : d ∈ redOffsets W C k) (hdk : d ≤ k)
    (hn : n ∈ targetBlock W k) (hq : q ∈ redLengths W k n d) :
    q < 2 ^ ((2 * C + 1) * k + 2 * W + 14) := by
  have hP := redLengthScale_upper hW hdk hn
  have hqBounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
  have hdUpper := (Finset.mem_Icc.mp hd).2
  have hWd : W * d ≤ 2 * C * k + 2 * W := by
    calc
      W * d ≤ W * (2 * C * k / W + 2) := Nat.mul_le_mul_left W hdUpper
      _ = (2 * C * k / W) * W + 2 * W := by ring
      _ ≤ 2 * C * k + 2 * W :=
        Nat.add_le_add_right (Nat.div_mul_le_self (2 * C * k) W) _
  calc
    q ≤ 16 * redLengthScale W k n d := hqBounds.2
    _ < 16 * 2 ^ (k + W * d + 10) :=
      Nat.mul_lt_mul_of_pos_left hP (by omega)
    _ = 2 ^ (k + W * d + 14) := by rw [sixteen_mul_pow_two]
    _ ≤ 2 ^ ((2 * C + 1) * k + 2 * W + 14) := by
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      nlinarith

/-! The corresponding bounds for the full family of red subchannels. -/

lemma redSubLengthScale_pos {W k n d e : ℕ}
    (hW : 5 * e + 5 ≤ W) (hk : W ≤ k) (hd : d ≤ k)
    (hn : n ∈ targetBlock W k) :
    0 < redSubLengthScale W k n d e := by
  let D := redSubCenterScale W k d e
  have hDdef : D = 2 ^ (W * (k - d) + W - 5 - 5 * e) := by
    simp [D, redSubCenterScale]
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hWh : W * (k - d) ≤ W * k :=
    Nat.mul_le_mul_left W (Nat.sub_le _ _)
  have hDle : D ≤ n := by
    calc
      D = 2 ^ (W * (k - d) + W - 5 - 5 * e) := hDdef
      _ ≤ 2 ^ ((W + 1) * k) := by
        apply Nat.pow_le_pow_right (n := 2) (by omega)
        calc
          W * (k - d) + W - 5 - 5 * e ≤ W * (k - d) + W :=
            by omega
          _ ≤ W * k + W := Nat.add_le_add_right hWh W
          _ ≤ W * k + k := Nat.add_le_add_left hk _
          _ = (W + 1) * k := by simp only [Nat.add_mul, one_mul]
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  rw [redSubLengthScale, show redSubCenterScale W k d e = D by rfl]
  exact Nat.div_pos hDle hDpos

lemma redSubLengthScale_lower {W k n d e : ℕ}
    (hk : W ≤ k) (hn : n ∈ targetBlock W k) :
    2 ^ (k - W) ≤ redSubLengthScale W k n d e := by
  have hDpos : 0 < redSubCenterScale W k d e := by
    rw [redSubCenterScale]
    positivity
  rw [redSubLengthScale, Nat.le_div_iff_mul_le hDpos]
  have hDle : redSubCenterScale W k d e ≤ 2 ^ (W * k + W) := by
    rw [redSubCenterScale]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    calc
      W * (k - d) + W - 5 - 5 * e ≤ W * (k - d) + W := by omega
      _ ≤ W * k + W := by
        gcongr
        exact Nat.sub_le _ _
  calc
    2 ^ (k - W) * redSubCenterScale W k d e ≤
        2 ^ (k - W) * 2 ^ (W * k + W) := Nat.mul_le_mul_left _ hDle
    _ = 2 ^ ((W + 1) * k) := by
      rw [← pow_add]
      congr 1
      simp only [Nat.add_mul, one_mul]
      omega
    _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
    _ ≤ n := (mem_targetBlock.mp hn).1

lemma redSubLengthScale_lower_strong {W C k n d e : ℕ}
    (hW : 0 < W) (hn : n ∈ targetBlock W k)
    (hde : (d, e) ∈ validRedSubchannels W C k) :
    2 ^ ((C + 1) * k) ≤ redSubLengthScale W k n d e := by
  rcases mem_validRedSubchannels.mp hde with
    ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
  have hdLower := (Finset.mem_Icc.mp hdOff).1
  have hdivUpper : C * k < (C * k / W + 1) * W := by
    rw [← Nat.div_lt_iff_lt_mul hW]
    omega
  have hWdLower : C * k + W ≤ W * d := by
    calc
      C * k + W ≤ W * (C * k / W + 2) := by
        rw [Nat.mul_add]
        nlinarith
      _ ≤ W * d := Nat.mul_le_mul_left W hdLower
  have hDpos : 0 < redSubCenterScale W k d e := by
    rw [redSubCenterScale]
    positivity
  rw [redSubLengthScale, Nat.le_div_iff_mul_le hDpos]
  have hDle : redSubCenterScale W k d e ≤ 2 ^ (W * k - C * k) := by
    rw [redSubCenterScale]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    have hmulEq : W * (k - d) + W * d = W * k := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  calc
    2 ^ ((C + 1) * k) * redSubCenterScale W k d e ≤
        2 ^ ((C + 1) * k) * 2 ^ (W * k - C * k) :=
      Nat.mul_le_mul_left _ hDle
    _ = 2 ^ ((W + 1) * k) := by
      rw [← pow_add]
      congr 1
      have hCk : C * k ≤ W * k := by
        have : C ≤ W := by nlinarith
        exact Nat.mul_le_mul_right k this
      simp only [Nat.add_mul, one_mul]
      omega
    _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
    _ ≤ n := (mem_targetBlock.mp hn).1

lemma div_le_add_one_of_le_add_lt_divisor {x y R D : ℕ}
    (hD : 0 < D) (hR : R < D) (hxy : x ≤ y + R) :
    x / D ≤ y / D + 1 := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hD]
  have hy : y < (y / D + 1) * D := by
    rw [← Nat.div_lt_iff_lt_mul hD]
    omega
  nlinarith

lemma redSubLengthScale_upper {W k n d e : ℕ}
    (hW : 5 * e + 5 ≤ W) (hd : d ≤ k) (hn : n ∈ targetBlock W k) :
    redSubLengthScale W k n d e < 2 ^ (k + W * d + 5 * e + 10) := by
  let D := redSubCenterScale W k d e
  have hDdef : D = 2 ^ (W * (k - d) + W - 5 - 5 * e) := by
    simp [D, redSubCenterScale]
  have hDpos : 0 < D := by rw [hDdef]; positivity
  rw [redSubLengthScale, show redSubCenterScale W k d e = D by rfl,
    Nat.div_lt_iff_lt_mul hDpos]
  calc
    n < (targetBase W) ^ (k + 1) := (mem_targetBlock.mp hn).2
    _ = 2 ^ ((W + 1) * (k + 1)) := by simp [targetBase, pow_mul]
    _ ≤ 2 ^ (k + W * d + 5 * e + 10) * D := by
      rw [hDdef, ← pow_add]
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      have hmulEq : W * d + W * (k - d) = W * k := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have hrecover :
          W * (k - d) + W - 5 - 5 * e + (5 + 5 * e) =
            W * (k - d) + W := by omega
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
      omega

lemma redSubLength_lt_globalEnvelope {W C k n d e q : ℕ}
    (hW : 12 * C + 200 ≤ W) (hde : (d, e) ∈ validRedSubchannels W C k)
    (hn : n ∈ targetBlock W k) (hq : q ∈ redSubLengths W k n d e) :
    q < 2 ^ ((2 * C + 1) * k + 3 * W + 20) := by
  rcases mem_validRedSubchannels.mp hde with
    ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
  have heFive : 5 * e + 5 ≤ W :=
    (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * e)).trans heSafe
  have hP := redSubLengthScale_upper heFive hdle hn
  have hqBounds := mem_redSubLengths.mp hq
  have hdUpper := (Finset.mem_Icc.mp hdOff).2
  have hWd : W * d ≤ 2 * C * k + 2 * W := by
    calc
      W * d ≤ W * (2 * C * k / W + 2) := Nat.mul_le_mul_left W hdUpper
      _ = (2 * C * k / W) * W + 2 * W := by ring
      _ ≤ 2 * C * k + 2 * W :=
        Nat.add_le_add_right (Nat.div_mul_le_self (2 * C * k) W) _
  have heW : 5 * e ≤ W := by omega
  calc
    q ≤ 16 * redSubLengthScale W k n d e := hqBounds.2.1
    _ < 16 * 2 ^ (k + W * d + 5 * e + 10) :=
      Nat.mul_lt_mul_of_pos_left hP (by omega)
    _ = 2 ^ (k + W * d + 5 * e + 14) := by rw [sixteen_mul_pow_two]
    _ ≤ 2 ^ ((2 * C + 1) * k + 3 * W + 20) := by
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      nlinarith

lemma redSubLength_support_subset {W C k n d e q : ℕ}
    (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hn : n ∈ targetBlock W k) (hq : q ∈ redSubLengths W k n d e) :
    lengthSupport q n ⊆ redBlock W (k - d) := by
  let h := k - d
  let A := 2 ^ (W * h + 20)
  let D := redSubCenterScale W k d e
  let P := redSubLengthScale W k n d e
  let X := 2 ^ (W * h + W - 9 - 5 * e)
  let U := 2 ^ (W * (h + 1))
  have hm := mem_validRedSubchannels.mp hde
  have hdle := hm.2.2.1
  have heW := hm.2.2.2.1
  have hvalid := hm.2.2.2.2
  have hDdef : D = 2 ^ (W * h + W - 5 - 5 * e) := by
    simp [D, redSubCenterScale, h]
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hPpos : 0 < P := by
    dsimp [P]
    exact redSubLengthScale_pos (by omega) (by omega) hdle hn
  have hqBounds := mem_redSubLengths.mp hq
  change P ≤ q ∧ q ≤ 16 * P ∧ _ at hqBounds
  have hqpos : 0 < q := hPpos.trans_le hqBounds.1
  have hPUpper : P < 2 ^ (k + W * d + 5 * e + 10) := by
    dsimp [P]
    exact redSubLengthScale_upper (by omega) hdle hn
  have hqA : q ≤ A := by
    have hqAlt : q < A := calc
      q ≤ 16 * P := hqBounds.2.1
      _ < 16 * 2 ^ (k + W * d + 5 * e + 10) :=
        Nat.mul_lt_mul_of_pos_left hPUpper (by omega)
      _ = 2 ^ (k + W * d + 5 * e + 14) := by rw [sixteen_mul_pow_two]
      _ ≤ 2 ^ (W * (k - d) + 20) :=
        Nat.pow_le_pow_right (n := 2) (by omega) hvalid
      _ = A := by simp [A, h]
    exact hqAlt.le
  have hDX : 16 * X ≤ D := by
    rw [hDdef]
    dsimp [X, h]
    rw [sixteen_mul_pow_two]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    omega
  have hLX : 2 ^ (W * h + 20) + q ≤ X := by
    have hAA : A + A ≤ X := by
      calc
        A + A = 2 ^ (W * h + 21) := by
          dsimp [A]
          rw [show W * h + 21 = (W * h + 20) + 1 by omega, pow_add]
          norm_num
          ring
        _ ≤ 2 ^ (W * h + W - 9 - 5 * e) := by
          apply Nat.pow_le_pow_right (n := 2) (by omega)
          omega
        _ = X := rfl
    dsimp [A] at hqA
    omega
  have hUbound : 2 * D + 5 * q < U := by
    have hDU : 16 * D ≤ U := by
      rw [hDdef]
      dsimp [U, h]
      rw [sixteen_mul_pow_two]
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      simp only [Nat.mul_add, mul_one]
      omega
    have hA_D : A ≤ D := by
      rw [hDdef]
      dsimp [A, h]
      apply Nat.pow_le_pow_right (n := 2) (by omega)
      omega
    calc
      2 * D + 5 * q ≤ 2 * D + 5 * A :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 5 hqA) _
      _ ≤ 7 * D := by nlinarith
      _ < 16 * D := by nlinarith [hDpos]
      _ ≤ U := hDU
  simpa only [redBlock, h, U] using
    lengthSupport_subset_Ico_of_divScale hDpos hPpos hqpos
      hqBounds.1 hqBounds.2.1 hDX hLX hUbound

lemma redSubLength_sq_le_target {W C k n d e q : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) (hde : (d, e) ∈ validRedSubchannels W C k)
    (hq : q ∈ redSubLengths W k n d e) : q * (q - 1) ≤ n := by
  let E := (2 * C + 1) * k + 3 * W + 20
  let Q := 2 ^ E
  have hqQ : q < Q := redSubLength_lt_globalEnvelope hW hde hn hq
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 2 * E ≤ (W + 1) * k := by
    dsimp [E]
    nlinarith only [hWmul, hkW, hW]
  have hQsq : Q * Q ≤ n := by
    calc
      Q * Q = 2 ^ (2 * E) := by
        dsimp [Q]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ ((W + 1) * k) := Nat.pow_le_pow_right (n := 2) (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  exact (Nat.mul_le_mul hqQ.le (by omega)).trans hQsq

lemma redSubLength_baseStart_gt_one {W C k n d e q : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) (hde : (d, e) ∈ validRedSubchannels W C k)
    (hq : q ∈ redSubLengths W k n d e) : 1 < baseStart q n := by
  let E := (2 * C + 1) * k + 3 * W + 20
  let Q := 2 ^ E
  have hqQ : q < Q := redSubLength_lt_globalEnvelope hW hde hn hq
  have hqpos : 0 < q := by
    rcases mem_validRedSubchannels.mp hde with ⟨_, _, hdle, heSafe, _⟩
    have heFive : 5 * e + 5 ≤ W :=
      (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * e)).trans heSafe
    have hP := redSubLengthScale_pos heFive (by omega) hdle hn
    exact hP.trans_le (mem_redSubLengths.mp hq).1
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 2 * E + 2 ≤ (W + 1) * k := by
    dsimp [E]
    nlinarith only [hWmul, hkW, hW]
  have hQ : 4 * Q * Q ≤ n := by
    calc
      4 * Q * Q = 2 ^ (2 * E + 2) := by
        dsimp [Q]
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ ((W + 1) * k) := Nat.pow_le_pow_right (n := 2) (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  have hqq : 2 * q * q ≤ n := by
    calc
      2 * q * q ≤ 4 * Q * Q := by nlinarith
      _ ≤ n := hQ
  have hdiv : 2 * q ≤ n / q := by
    rw [Nat.le_div_iff_mul_le hqpos]
    simpa only [mul_assoc] using hqq
  rw [baseStart]
  omega

def redSubRank (W : ℕ) (de : ℕ × ℕ) : ℕ := W * de.1 + 5 * de.2

lemma redSubRank_gap_of_ne {W C k d e d' e' : ℕ}
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hne : (d, e) ≠ (d', e')) :
    redSubRank W (d, e) + 5 ≤ redSubRank W (d', e') ∨
      redSubRank W (d', e') + 5 ≤ redSubRank W (d, e) := by
  rcases mem_validRedSubchannels.mp hde with
    ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
  rcases mem_validRedSubchannels.mp hde' with
    ⟨hdOff', heRange', hdle', heSafe', hvalid'⟩
  dsimp [redSubRank]
  rcases lt_trichotomy d d' with hdd' | hdd' | hdd'
  · left
    have hstep : W * (d + 1) ≤ W * d' := Nat.mul_le_mul_left W hdd'
    calc
      W * d + 5 * e + 5 ≤ W * d + W := by omega
      _ = W * (d + 1) := by ring
      _ ≤ W * d' := hstep
      _ ≤ W * d' + 5 * e' := Nat.le_add_right _ _
  · subst d'
    have heNe : e ≠ e' := by intro heq; exact hne (by simp [heq])
    rcases lt_or_gt_of_ne heNe with hee' | hee'
    · left; omega
    · right; omega
  · right
    have hstep : W * (d' + 1) ≤ W * d := Nat.mul_le_mul_left W hdd'
    calc
      W * d' + 5 * e' + 5 ≤ W * d' + W := by omega
      _ = W * (d' + 1) := by ring
      _ ≤ W * d := hstep
      _ ≤ W * d + 5 * e := Nat.le_add_right _ _

lemma redSubCenterScale_eq_rank {W C k d e : ℕ}
    (hde : (d, e) ∈ validRedSubchannels W C k) :
    redSubCenterScale W k d e =
      2 ^ (W * k + W - 5 - redSubRank W (d, e)) := by
  rcases mem_validRedSubchannels.mp hde with
    ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
  rw [redSubCenterScale]
  congr 1
  dsimp [redSubRank]
  have hmulEq : W * (k - d) + W * d = W * k := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

lemma redSubCenterScale_mul_thirtytwo_le_of_rank_gap
    {W C k d e d' e' : ℕ}
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hgap : redSubRank W (d, e) + 5 ≤ redSubRank W (d', e')) :
    32 * redSubCenterScale W k d' e' ≤ redSubCenterScale W k d e := by
  rw [redSubCenterScale_eq_rank hde, redSubCenterScale_eq_rank hde']
  rw [show 32 = 2 ^ 5 by norm_num, ← pow_add]
  apply Nat.pow_le_pow_right (n := 2) (by omega)
  rcases mem_validRedSubchannels.mp hde' with
    ⟨hdOff', heRange', hdle', heSafe', hvalid'⟩
  dsimp [redSubRank] at hgap ⊢
  have hrank' : W * d' + 5 * e' ≤ W * k + W - 5 := by
    have hWd' : W * d' ≤ W * k := Nat.mul_le_mul_left W hdle'
    omega
  omega

lemma redSubLengthScale_thirtytwo_le_of_rank_gap
    {W C k n d e d' e' : ℕ}
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hgap : redSubRank W (d, e) + 5 ≤ redSubRank W (d', e')) :
    32 * redSubLengthScale W k n d e ≤
      redSubLengthScale W k n d' e' := by
  have hD := redSubCenterScale_mul_thirtytwo_le_of_rank_gap hde hde' hgap
  have hD'pos : 0 < redSubCenterScale W k d' e' := by
    rw [redSubCenterScale]
    positivity
  rw [redSubLengthScale, redSubLengthScale, Nat.le_div_iff_mul_le hD'pos]
  calc
    32 * (n / redSubCenterScale W k d e) * redSubCenterScale W k d' e' =
        (n / redSubCenterScale W k d e) *
          (32 * redSubCenterScale W k d' e') := by ring
    _ ≤ (n / redSubCenterScale W k d e) * redSubCenterScale W k d e :=
      Nat.mul_le_mul_left _ hD
    _ ≤ n := Nat.div_mul_le_self _ _

lemma redSubLengths_lt_of_rank_gap {W C k n d e d' e' q q' : ℕ}
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hP : 0 < redSubLengthScale W k n d e)
    (hgap : redSubRank W (d, e) + 5 ≤ redSubRank W (d', e'))
    (hq : q ∈ redSubLengths W k n d e)
    (hq' : q' ∈ redSubLengths W k n d' e') : q < q' := by
  have hscale := redSubLengthScale_thirtytwo_le_of_rank_gap
    (n := n) hde hde' hgap
  have hqb := mem_redSubLengths.mp hq
  have hqb' := mem_redSubLengths.mp hq'
  calc
    q ≤ 16 * redSubLengthScale W k n d e := hqb.2.1
    _ < 32 * redSubLengthScale W k n d e := by nlinarith
    _ ≤ redSubLengthScale W k n d' e' := hscale
    _ ≤ q' := hqb'.1

lemma redSubLengths_ne_of_channel_ne {W C k n d e d' e' q q' : ℕ}
    (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k)
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hne : (d, e) ≠ (d', e'))
    (hq : q ∈ redSubLengths W k n d e)
    (hq' : q' ∈ redSubLengths W k n d' e') : q ≠ q' := by
  have hP : 0 < redSubLengthScale W k n d e := by
    rcases mem_validRedSubchannels.mp hde with ⟨_, _, hdle, heSafe, _⟩
    exact redSubLengthScale_pos (by omega) (by omega) hdle hn
  have hP' : 0 < redSubLengthScale W k n d' e' := by
    rcases mem_validRedSubchannels.mp hde' with ⟨_, _, hdle, heSafe, _⟩
    exact redSubLengthScale_pos (by omega) (by omega) hdle hn
  rcases redSubRank_gap_of_ne hde hde' hne with hgap | hgap
  · exact (redSubLengths_lt_of_rank_gap hde hde' hP hgap hq hq').ne
  · exact (redSubLengths_lt_of_rank_gap hde' hde hP' hgap hq' hq).ne.symm

/-! ### Arithmetic geometry of support collisions -/

/-- Membership in `lengthSupport q n` locates a coordinate within `q` to the
left and `5q` to the right of the quotient center `n/q`. -/
lemma divCenter_bounds_of_mem_lengthSupport {q n x : ℕ} (hq : 0 < q)
    (hqn : q * (q - 1) ≤ n) (hx : x ∈ lengthSupport q n) :
    n / q ≤ x + q ∧ x ≤ n / q + 5 * q := by
  have hdiv : q - 1 ≤ n / q := by
    rw [Nat.le_div_iff_mul_le hq]
    simpa only [Nat.mul_comm] using hqn
  have hbaseEq : baseStart q n + (q - 1) = n / q := by
    rw [baseStart, Nat.sub_add_cancel hdiv]
  have hsqrt : Nat.sqrt q ≤ q := Nat.sqrt_le_self q
  rw [lengthSupport, Finset.mem_Icc] at hx
  constructor
  · calc
      n / q = baseStart q n + (q - 1) := hbaseEq.symm
      _ ≤ x + (q - 1) := Nat.add_le_add_right hx.1 _
      _ ≤ x + q := Nat.add_le_add_left (Nat.sub_le q 1) x
  · calc
      x ≤ baseStart q n + Nat.sqrt q + 4 * q := hx.2
      _ ≤ n / q + Nat.sqrt q + 4 * q := by
        gcongr
        rw [baseStart]
        exact Nat.sub_le _ _
      _ ≤ n / q + 5 * q := by omega

/-- If two supports meet, their quotient centers differ by at most six times
the sum of their lengths. -/
lemma divCenter_absDiff_le_of_support_inter {q q' n n' : ℕ}
    (hq : 0 < q) (hq' : 0 < q')
    (hqn : q * (q - 1) ≤ n) (hqn' : q' * (q' - 1) ≤ n')
    (hinter : (lengthSupport q n ∩ lengthSupport q' n').Nonempty) :
    (n / q).max (n' / q') - (n / q).min (n' / q') ≤ 6 * (q + q') := by
  obtain ⟨x, hx⟩ := hinter
  rw [Finset.mem_inter] at hx
  rcases hx with ⟨hx, hx'⟩
  have hb := divCenter_bounds_of_mem_lengthSupport hq hqn hx
  have hb' := divCenter_bounds_of_mem_lengthSupport hq' hqn' hx'
  rcases le_total (n / q) (n' / q') with hle | hge
  · simp only [Nat.max_eq_right hle, Nat.min_eq_left hle]
    omega
  · simp only [Nat.max_eq_left hge, Nat.min_eq_right hge]
    omega

/-- The corresponding one-sided form avoids `max/min` in later cross-product
estimates. -/
lemma divCenter_le_add_of_support_inter {q q' n n' : ℕ}
    (hq : 0 < q) (hq' : 0 < q')
    (hqn : q * (q - 1) ≤ n) (hqn' : q' * (q' - 1) ≤ n')
    (hinter : (lengthSupport q n ∩ lengthSupport q' n').Nonempty) :
    n / q ≤ n' / q' + 6 * (q + q') ∧
      n' / q' ≤ n / q + 6 * (q + q') := by
  have h := divCenter_absDiff_le_of_support_inter hq hq' hqn hqn' hinter
  rcases le_total (n / q) (n' / q') with hle | hge
  · simp only [Nat.max_eq_right hle, Nat.min_eq_left hle] at h
    omega
  · simp only [Nat.max_eq_left hge, Nat.min_eq_right hge] at h
    omega

lemma mul_cross_le_add_of_div_le {n n' q q' L : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hcent : n / q ≤ n' / q' + L) :
    n * q' ≤ n' * q + (L + 1) * q * q' := by
  have hnmod := Nat.mod_lt n hq
  have hnEq := Nat.mod_add_div n q
  have hnle : n ≤ (n / q + 1) * q := by
    calc
      n = n % q + q * (n / q) := hnEq.symm
      _ ≤ q + q * (n / q) := Nat.add_le_add_right hnmod.le _
      _ = (n / q + 1) * q := by ring
  have hn'div : (n' / q') * q' ≤ n' := Nat.div_mul_le_self n' q'
  calc
    n * q' ≤ ((n / q + 1) * q) * q' := Nat.mul_le_mul_right q' hnle
    _ ≤ ((n' / q' + L + 1) * q) * q' := by gcongr
    _ = ((n' / q') * q') * q + (L + 1) * q * q' := by ring
    _ ≤ n' * q + (L + 1) * q * q' := by gcongr

def closeRadius (W k : ℕ) : ℕ := 2 ^ (2 * k + 2 * W + 20)

def Close (W k n n' : ℕ) : Prop :=
  n.max n' - n.min n' ≤ closeRadius W k

lemma le_add_closeRadius_of_Close {W k n n' : ℕ} (h : Close W k n n') :
    n ≤ n' + closeRadius W k ∧ n' ≤ n + closeRadius W k := by
  unfold Close at h
  rcases le_total n n' with hle | hge
  · simp only [Nat.max_eq_right hle, Nat.min_eq_left hle] at h
    omega
  · simp only [Nat.max_eq_left hge, Nat.min_eq_right hge] at h
    omega

lemma closeRadius_lt_redSubCenterScale {W C k d e : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hde : (d, e) ∈ validRedSubchannels W C k) :
    closeRadius W k < redSubCenterScale W k d e := by
  rcases mem_validRedSubchannels.mp hde with
    ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
  have hdUpper := (Finset.mem_Icc.mp hdOff).2
  have hWd : W * d ≤ 2 * C * k + 2 * W := by
    calc
      W * d ≤ W * (2 * C * k / W + 2) := Nat.mul_le_mul_left W hdUpper
      _ = (2 * C * k / W) * W + 2 * W := by ring
      _ ≤ 2 * C * k + 2 * W :=
        Nat.add_le_add_right (Nat.div_mul_le_self (2 * C * k) W) _
  have hmulEq : W * (k - d) + W * d = W * k := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hWmul := Nat.mul_le_mul_right k hW
  have hkpos : 0 < k := by omega
  have hCoeff : 2 * C + 5 ≤ W := by omega
  have h4W : 4 * W ≤ 2 * k := by omega
  have hmain : (2 * C + 2) * k + 4 * W < W * k := by
    calc
      (2 * C + 2) * k + 4 * W ≤ (2 * C + 4) * k := by nlinarith
      _ < (2 * C + 5) * k := by nlinarith
      _ ≤ W * k := Nat.mul_le_mul_right k hCoeff
  have he25 : 5 * e + 25 ≤ W := by omega
  have hleft :
      (2 * k + 2 * W + 20) + (5 + 5 * e) + W * d ≤
        ((2 * C + 2) * k + 4 * W) + W := by
    nlinarith only [hWd, he25]
  have hbig :
      (2 * k + 2 * W + 20) + (5 + 5 * e) + W * d < W * k + W :=
    lt_of_le_of_lt hleft (Nat.add_lt_add_right hmain W)
  have htotal :
      (2 * k + 2 * W + 20) + (5 + 5 * e) < W * (k - d) + W := by
    omega
  rw [closeRadius, redSubCenterScale]
  apply Nat.pow_lt_pow_right (by omega)
  omega

lemma redSubLengthScales_close {W C k n n' d e : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hclose : Close W k n n') :
    redSubLengthScale W k n d e ≤ redSubLengthScale W k n' d e + 1 ∧
      redSubLengthScale W k n' d e ≤ redSubLengthScale W k n d e + 1 := by
  have hD : 0 < redSubCenterScale W k d e := by
    rw [redSubCenterScale]
    positivity
  have hR := closeRadius_lt_redSubCenterScale hC hW hk hde
  have hc := le_add_closeRadius_of_Close hclose
  rw [redSubLengthScale, redSubLengthScale]
  exact ⟨div_le_add_one_of_le_add_lt_divisor hD hR hc.1,
    div_le_add_one_of_le_add_lt_divisor hD hR hc.2⟩

lemma coreRedSubLengths_subset_close {W C k n n' d e : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hclose : Close W k n n') :
    coreRedSubLengths W k n d e ⊆ redSubLengths W k n' d e := by
  intro q hq
  have hc := redSubLengthScales_close hC hW hk hde hclose
  have hq' := mem_coreRedSubLengths.mp hq
  rw [mem_redSubLengths]
  have hsieve := (mem_redSubLengths.mp hq'.1).2.2
  refine ⟨?_, ?_, hsieve⟩
  · omega
  · have hPpos : 0 < redSubLengthScale W k n d e := by
      have := hq'.2.1
      omega
    have hsub : redSubLengthScale W k n d e - 1 + 1 =
        redSubLengthScale W k n d e := Nat.sub_add_cancel hPpos
    nlinarith

lemma two_mul_closeRadius_lt_redSubLength {W C k n d e q : ℕ}
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) (hde : (d, e) ∈ validRedSubchannels W C k)
    (hq : q ∈ redSubLengths W k n d e) : 2 * closeRadius W k < q := by
  have hWpos : 0 < W := by omega
  have hP := redSubLengthScale_lower_strong hWpos hn hde
  have hPq := (mem_redSubLengths.mp hq).1
  have hexp : 2 * k + 2 * W + 21 < (C + 1) * k := by
    have hCk := Nat.mul_le_mul_right k hC
    nlinarith only [hCk, hk, hW]
  calc
    2 * closeRadius W k = 2 ^ (2 * k + 2 * W + 21) := by
      rw [closeRadius, mul_comm, ← pow_succ]
    _ < 2 ^ ((C + 1) * k) := Nat.pow_lt_pow_right (by omega) hexp
    _ ≤ redSubLengthScale W k n d e := hP
    _ ≤ q := hPq

lemma absDiff_le_two_closeRadius_of_Close {W k n₀ n n' : ℕ}
    (hn : Close W k n₀ n) (hn' : Close W k n₀ n') :
    n.max n' - n.min n' ≤ 2 * closeRadius W k := by
  have hnBounds := le_add_closeRadius_of_Close hn
  have hn'Bounds := le_add_closeRadius_of_Close hn'
  rcases le_total n n' with hle | hge
  · simp only [Nat.max_eq_right hle, Nat.min_eq_left hle]
    omega
  · simp only [Nat.max_eq_left hge, Nat.min_eq_right hge]
    omega

lemma redLengthEvents_disjoint_of_close_to {W C k n₀ n n' d e q : ℕ}
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) (hn' : n' ∈ targetBlock W k)
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hqn : q ∈ redSubLengths W k n d e)
    (hqn' : q ∈ redSubLengths W k n' d e)
    (hclose : Close W k n₀ n) (hclose' : Close W k n₀ n')
    (hne : n ≠ n') : Disjoint (lengthEvent q n) (lengthEvent q n') := by
  have hC1 : 1 ≤ C := by omega
  apply lengthEvent_disjoint_of_ne_of_absDiff_lt
  · have hP := (mem_redSubLengths.mp hqn).1
    have hPlower := redSubLengthScale_lower_strong (by omega) hn hde
    exact (by positivity : 0 < 2 ^ ((C + 1) * k)).trans_le (hPlower.trans hP)
  · exact redSubLength_baseStart_gt_one hC1 hW hk hn hde hqn
  · exact redSubLength_baseStart_gt_one hC1 hW hk hn' hde hqn'
  · exact hne
  · exact (absDiff_le_two_closeRadius_of_Close hclose hclose').trans_lt
      (two_mul_closeRadius_lt_redSubLength hC hW hk hn hde hqn)

lemma blueLabel_le_envelope {W k n p : ℕ} (hW : 2 ≤ W)
    (hk : W + 16 ≤ k) (hn : n ∈ targetBlock W k)
    (hp : p ∈ blueLabels W k n) :
    p ≤ 2 ^ (k + W + 5) := by
  exact (mem_primesBetween.mp (blueLabels_subset_scaleBluePrimes hW hk hn hp)).2.1

lemma blueLabel_sq_le_target {W k n p : ℕ} (hW : 10 ≤ W)
    (hk : W + 16 ≤ k) (hn : n ∈ targetBlock W k)
    (hp : p ∈ blueLabels W k n) : p * (p - 1) ≤ n := by
  let B := 2 ^ (k + W + 5)
  have hpB : p ≤ B := blueLabel_le_envelope (by omega) hk hn hp
  have hExp : 2 * (k + W + 5) ≤ (W + 1) * k := by
    have hkW : W ≤ k := by omega
    nlinarith [Nat.mul_le_mul_left (W - 1) hkW]
  have hBsq : B * B ≤ n := by
    calc
      B * B = 2 ^ (2 * (k + W + 5)) := by
        dsimp [B]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ ((W + 1) * k) := Nat.pow_le_pow_right (n := 2) (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  calc
    p * (p - 1) ≤ B * B := Nat.mul_le_mul hpB (by omega)
    _ ≤ n := hBsq

private lemma blue_support_disjoint_of_Close_of_lt {W k n n' p p' : ℕ}
    (hW : 10 ≤ W) (hk : W + 16 ≤ k)
    (hn : n ∈ targetBlock W k) (hn' : n' ∈ targetBlock W k)
    (hclose : Close W k n n')
    (hp : p ∈ blueLabels W k n) (hp' : p' ∈ blueLabels W k n')
    (hpp' : p < p') : Disjoint (lengthSupport p n) (lengthSupport p' n') := by
  by_contra hdisj
  have hinter : (lengthSupport p n ∩ lengthSupport p' n').Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp hdisj
  let B := 2 ^ (k + W + 5)
  let R := closeRadius W k
  let L := 6 * (p + p')
  have hpB : p ≤ B := blueLabel_le_envelope (by omega) hk hn hp
  have hp'B : p' ≤ B := blueLabel_le_envelope (by omega) hk hn' hp'
  have hp0 : 0 < p := (mem_primesBetween.mp hp).2.2.pos
  have hp'0 : 0 < p' := (mem_primesBetween.mp hp').2.2.pos
  have hpn := blueLabel_sq_le_target hW hk hn hp
  have hp'n' := blueLabel_sq_le_target hW hk hn' hp'
  have hcent := divCenter_le_add_of_support_inter hp0 hp'0 hpn hp'n' hinter
  have hcross := mul_cross_le_add_of_div_le hp0 hp'0 hcent.1
  change n * p' ≤ n' * p + (L + 1) * p * p' at hcross
  have hn'close := (le_add_closeRadius_of_Close hclose).2
  change n' ≤ n + R at hn'close
  have hlower : n * p + n ≤ n * p' := by
    calc
      n * p + n = n * (p + 1) := by ring
      _ ≤ n * p' := Nat.mul_le_mul_left n (by omega)
  have hnBound : n ≤ R * p + (L + 1) * p * p' := by
    have hn'pmul : n' * p ≤ (n + R) * p := Nat.mul_le_mul_right p hn'close
    have hchain : n * p + n ≤ n * p + (R * p + (L + 1) * p * p') := by
      calc
        n * p + n ≤ n * p' := hlower
        _ ≤ n' * p + (L + 1) * p * p' := hcross
        _ ≤ (n + R) * p + (L + 1) * p * p' :=
          Nat.add_le_add_right hn'pmul _
        _ = n * p + (R * p + (L + 1) * p * p') := by ring
    exact Nat.le_of_add_le_add_left hchain
  have hBpos : 0 < B := by positivity
  have hL : L + 1 ≤ 13 * B := by
    dsimp [L]
    have hsum : p + p' ≤ 2 * B := by omega
    nlinarith
  have hR : R = 1024 * B ^ 2 := by
    dsimp [R, closeRadius, B]
    rw [show 1024 = 2 ^ 10 by norm_num, pow_two, ← pow_add, ← pow_add]
    congr 1
    omega
  have hupper : R * p + (L + 1) * p * p' ≤ 2048 * B ^ 3 := by
    rw [hR]
    calc
      (1024 * B ^ 2) * p + (L + 1) * p * p' ≤
          (1024 * B ^ 2) * B + (13 * B) * B * B := by gcongr
      _ = 1037 * B ^ 3 := by ring
      _ ≤ 2048 * B ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
  have hsmall : 3 * W + 26 < 8 * k := by omega
  have hmul : 8 * k ≤ (W - 2) * k :=
    Nat.mul_le_mul_right k (by omega)
  have hExp : 3 * k + 3 * W + 26 < (W + 1) * k := by
    calc
      3 * k + 3 * W + 26 < 3 * k + 8 * k := by omega
      _ ≤ 3 * k + (W - 2) * k := Nat.add_le_add_left hmul _
      _ = (3 + (W - 2)) * k := by ring
      _ = (W + 1) * k := by
        rw [show 3 + (W - 2) = W + 1 by omega]
  have hpowEq : 2048 * B ^ 3 = 2 ^ (3 * k + 3 * W + 26) := by
    dsimp [B]
    rw [show 2048 = 2 ^ 11 by norm_num, ← pow_mul, ← pow_add]
    rw [show 11 + (k + W + 5) * 3 = 3 * k + 3 * W + 26 by ring]
  have hnLarge : 2048 * B ^ 3 < n := by
    rw [hpowEq]
    calc
      2 ^ (3 * k + 3 * W + 26) < 2 ^ ((W + 1) * k) :=
        Nat.pow_lt_pow_right (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  omega

lemma blue_support_disjoint_of_Close_of_ne {W k n n' p p' : ℕ}
    (hW : 10 ≤ W) (hk : W + 16 ≤ k)
    (hn : n ∈ targetBlock W k) (hn' : n' ∈ targetBlock W k)
    (hclose : Close W k n n')
    (hp : p ∈ blueLabels W k n) (hp' : p' ∈ blueLabels W k n')
    (hpp' : p ≠ p') : Disjoint (lengthSupport p n) (lengthSupport p' n') := by
  rcases lt_or_gt_of_ne hpp' with hlt | hgt
  · exact blue_support_disjoint_of_Close_of_lt hW hk hn hn' hclose hp hp' hlt
  · exact (blue_support_disjoint_of_Close_of_lt hW hk hn' hn
      (by simpa only [Close, max_comm, min_comm] using hclose) hp' hp hgt).symm

lemma target_absDiff_le_of_same_support_inter {q n n' : ℕ}
    (hq : 0 < q) (hqn : q * (q - 1) ≤ n) (hqn' : q * (q - 1) ≤ n')
    (hinter : (lengthSupport q n ∩ lengthSupport q n').Nonempty) :
    n.max n' - n.min n' ≤ (12 * q + 1) * q := by
  have hcent := divCenter_le_add_of_support_inter hq hq hqn hqn' hinter
  have hone (a b : ℕ) (hab : a / q ≤ b / q + 12 * q) :
      a ≤ b + (12 * q + 1) * q := by
    have hamod := Nat.mod_lt a hq
    have haEq := Nat.mod_add_div a q
    have hale : a ≤ (a / q + 1) * q := by
      calc
        a = a % q + q * (a / q) := haEq.symm
        _ ≤ q + q * (a / q) := Nat.add_le_add_right hamod.le _
        _ = (a / q + 1) * q := by ring
    have hbdiv : (b / q) * q ≤ b := Nat.div_mul_le_self b q
    calc
      a ≤ (a / q + 1) * q := hale
      _ ≤ (b / q + 12 * q + 1) * q := Nat.mul_le_mul_right q (by omega)
      _ = (b / q) * q + (12 * q + 1) * q := by ring
      _ ≤ b + (12 * q + 1) * q := Nat.add_le_add_right hbdiv _
  have hnn' : n ≤ n' + (12 * q + 1) * q := hone n n' (by
    simpa only [show 6 * (q + q) = 12 * q by ring] using hcent.1)
  have hn'n : n' ≤ n + (12 * q + 1) * q := hone n' n (by
    simpa only [show 6 * (q + q) = 12 * q by ring] using hcent.2)
  rcases le_total n n' with hle | hge
  · simp only [Nat.max_eq_right hle, Nat.min_eq_left hle]
    omega
  · simp only [Nat.max_eq_left hge, Nat.min_eq_right hge]
    omega

lemma blue_support_disjoint_of_not_Close_same {W k n n' p : ℕ}
    (hW : 10 ≤ W) (hk : W + 16 ≤ k)
    (hn : n ∈ targetBlock W k) (hn' : n' ∈ targetBlock W k)
    (hfar : ¬ Close W k n n')
    (hp : p ∈ blueLabels W k n) (hp' : p ∈ blueLabels W k n') :
    Disjoint (lengthSupport p n) (lengthSupport p n') := by
  by_contra hdisj
  have hinter : (lengthSupport p n ∩ lengthSupport p n').Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp hdisj
  let B := 2 ^ (k + W + 5)
  have hpB : p ≤ B := blueLabel_le_envelope (by omega) hk hn hp
  have hp0 : 0 < p := (mem_primesBetween.mp hp).2.2.pos
  have hpn := blueLabel_sq_le_target hW hk hn hp
  have hpn' := blueLabel_sq_le_target hW hk hn' hp'
  have hdiff := target_absDiff_le_of_same_support_inter hp0 hpn hpn' hinter
  have hsmall : (12 * p + 1) * p ≤ closeRadius W k := by
    have hBpos : 0 < B := by positivity
    calc
      (12 * p + 1) * p ≤ (13 * B) * B := by
        gcongr
        nlinarith
      _ = 13 * B ^ 2 := by ring
      _ ≤ 1024 * B ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
      _ = closeRadius W k := by
        dsimp [B, closeRadius]
        rw [show 1024 = 2 ^ 10 by norm_num, ← pow_mul, ← pow_add]
        rw [show 10 + (k + W + 5) * 2 = 2 * k + 2 * W + 20 by ring]
  apply hfar
  exact hdiff.trans hsmall

lemma redLength_sq_le_target {W C k n d q : ℕ}
    (hC : 1 ≤ C) (hW : 8 * C + 100 ≤ W) (hk : W + 16 ≤ k)
    (hn : n ∈ targetBlock W k) (hd : d ∈ validRedOffsets W C k)
    (hq : q ∈ redLengths W k n d) : q * (q - 1) ≤ n := by
  let E := (2 * C + 1) * k + 2 * W + 14
  let Q := 2 ^ E
  have hd' := mem_validRedOffsets.mp hd
  have hqQ : q < Q := redLength_lt_globalEnvelope (by omega) hd'.1 hd'.2.1 hn hq
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 2 * E ≤ (W + 1) * k := by
    dsimp [E]
    nlinarith
  have hQsq : Q * Q ≤ n := by
    calc
      Q * Q = 2 ^ (2 * E) := by
        dsimp [Q]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ ((W + 1) * k) := Nat.pow_le_pow_right (n := 2) (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  calc
    q * (q - 1) ≤ Q * Q := Nat.mul_le_mul hqQ.le (by omega)
    _ ≤ n := hQsq

private lemma red_support_disjoint_of_close_to_of_lt
    {W C k n₀ n n' d d' q q' : ℕ}
    (hC : 1 ≤ C) (hW : 8 * C + 100 ≤ W) (hk : W + 16 ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hclose : Close W k n₀ n) (hclose' : Close W k n₀ n')
    (hd : d ∈ validRedOffsets W C k) (hd' : d' ∈ validRedOffsets W C k)
    (hq : q ∈ redLengths W k n d) (hq' : q' ∈ redLengths W k n' d')
    (hqq' : q < q') : Disjoint (lengthSupport q n) (lengthSupport q' n') := by
  by_contra hdisj
  have hinter : (lengthSupport q n ∩ lengthSupport q' n').Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp hdisj
  let E := (2 * C + 1) * k + 2 * W + 14
  let Q := 2 ^ E
  let R := closeRadius W k
  let L := 6 * (q + q')
  have hdv := mem_validRedOffsets.mp hd
  have hdv' := mem_validRedOffsets.mp hd'
  have hqQ : q < Q := redLength_lt_globalEnvelope (by omega) hdv.1 hdv.2.1 hn hq
  have hq'Q : q' < Q := redLength_lt_globalEnvelope (by omega) hdv'.1 hdv'.2.1 hn' hq'
  have hq0 : 0 < q := by
    have hP := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1 |>.1
    have hscale : 0 < redLengthScale W k n d :=
      redLengthScale_pos (by omega) (by omega) hdv.2.1 hn
    omega
  have hq'0 : 0 < q' := hq0.trans hqq'
  have hqn := redLength_sq_le_target hC hW hk hn hd hq
  have hqn' := redLength_sq_le_target hC hW hk hn' hd' hq'
  have hcent := divCenter_le_add_of_support_inter hq0 hq'0 hqn hqn' hinter
  have hcross := mul_cross_le_add_of_div_le hq0 hq'0 hcent.1
  change n * q' ≤ n' * q + (L + 1) * q * q' at hcross
  have hn0n := (le_add_closeRadius_of_Close hclose).1
  have hn0n' := (le_add_closeRadius_of_Close hclose').2
  have hn'close : n' ≤ n + 2 * R := by
    change n₀ ≤ n + R at hn0n
    change n' ≤ n₀ + R at hn0n'
    omega
  have hlower : n * q + n ≤ n * q' := by
    calc
      n * q + n = n * (q + 1) := by ring
      _ ≤ n * q' := Nat.mul_le_mul_left n (by omega)
  have hnBound : n ≤ (2 * R) * q + (L + 1) * q * q' := by
    have hn'qmul : n' * q ≤ (n + 2 * R) * q := Nat.mul_le_mul_right q hn'close
    have hchain : n * q + n ≤
        n * q + ((2 * R) * q + (L + 1) * q * q') := by
      calc
        n * q + n ≤ n * q' := hlower
        _ ≤ n' * q + (L + 1) * q * q' := hcross
        _ ≤ (n + 2 * R) * q + (L + 1) * q * q' :=
          Nat.add_le_add_right hn'qmul _
        _ = n * q + ((2 * R) * q + (L + 1) * q * q') := by ring
    exact Nat.le_of_add_le_add_left hchain
  have hQpos : 0 < Q := by positivity
  have hL : L + 1 ≤ 13 * Q := by
    dsimp [L]
    have : q + q' ≤ 2 * Q := by omega
    nlinarith
  have hRQ : R ≤ Q ^ 2 := by
    dsimp [R, closeRadius, Q]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    have hCmul := Nat.mul_le_mul_right k hC
    dsimp [E]
    nlinarith only [hCmul]
  have hupper : (2 * R) * q + (L + 1) * q * q' ≤ 16 * Q ^ 3 := by
    have hfirst : (2 * R) * q ≤ (2 * Q ^ 2) * Q :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hRQ) hqQ.le
    have hsecond : (L + 1) * q * q' ≤ (13 * Q) * Q * Q := by
      exact Nat.mul_le_mul (Nat.mul_le_mul hL hqQ.le) hq'Q.le
    calc
      (2 * R) * q + (L + 1) * q * q' ≤
          (2 * Q ^ 2) * Q + (13 * Q) * Q * Q := Nat.add_le_add hfirst hsecond
      _ = 15 * Q ^ 3 := by ring
      _ ≤ 16 * Q ^ 3 := Nat.mul_le_mul_right (Q ^ 3) (by omega)
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 3 * E + 4 < (W + 1) * k := by
    dsimp [E]
    nlinarith only [hWmul, hkW, hW]
  have hpowEq : 16 * Q ^ 3 = 2 ^ (3 * E + 4) := by
    dsimp [Q]
    rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
    rw [show 4 + E * 3 = 3 * E + 4 by ring]
  have hnLarge : 16 * Q ^ 3 < n := by
    rw [hpowEq]
    calc
      2 ^ (3 * E + 4) < 2 ^ ((W + 1) * k) :=
        Nat.pow_lt_pow_right (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  omega

lemma red_support_disjoint_of_close_to_of_ne
    {W C k n₀ n n' d d' q q' : ℕ}
    (hC : 1 ≤ C) (hW : 8 * C + 100 ≤ W) (hk : W + 16 ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hclose : Close W k n₀ n) (hclose' : Close W k n₀ n')
    (hd : d ∈ validRedOffsets W C k) (hd' : d' ∈ validRedOffsets W C k)
    (hq : q ∈ redLengths W k n d) (hq' : q' ∈ redLengths W k n' d')
    (hqq' : q ≠ q') : Disjoint (lengthSupport q n) (lengthSupport q' n') := by
  rcases lt_or_gt_of_ne hqq' with hlt | hgt
  · exact red_support_disjoint_of_close_to_of_lt hC hW hk hn₀ hn hn'
      hclose hclose' hd hd' hq hq' hlt
  · exact (red_support_disjoint_of_close_to_of_lt hC hW hk hn₀ hn' hn
      hclose' hclose hd' hd hq' hq hgt).symm

private lemma redSub_support_disjoint_of_close_to_of_lt
    {W C k n₀ n n' d e d' e' q q' : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hclose : Close W k n₀ n) (hclose' : Close W k n₀ n')
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hq : q ∈ redSubLengths W k n d e)
    (hq' : q' ∈ redSubLengths W k n' d' e')
    (hqq' : q < q') : Disjoint (lengthSupport q n) (lengthSupport q' n') := by
  by_contra hdisj
  have hinter : (lengthSupport q n ∩ lengthSupport q' n').Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp hdisj
  let E := (2 * C + 1) * k + 3 * W + 20
  let Q := 2 ^ E
  let R := closeRadius W k
  let L := 6 * (q + q')
  have hqQ : q < Q := redSubLength_lt_globalEnvelope hW hde hn hq
  have hq'Q : q' < Q := redSubLength_lt_globalEnvelope hW hde' hn' hq'
  have hq0 : 0 < q := by
    have hlo := (mem_redSubLengths.mp hq).1
    rcases mem_validRedSubchannels.mp hde with ⟨_, _, hdle, heSafe, _⟩
    have heFive : 5 * e + 5 ≤ W :=
      (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * e)).trans heSafe
    have hP := redSubLengthScale_pos heFive (by omega) hdle hn
    omega
  have hq'0 : 0 < q' := hq0.trans hqq'
  have hqn := redSubLength_sq_le_target hC hW hk hn hde hq
  have hqn' := redSubLength_sq_le_target hC hW hk hn' hde' hq'
  have hcent := divCenter_le_add_of_support_inter hq0 hq'0 hqn hqn' hinter
  have hcross := mul_cross_le_add_of_div_le hq0 hq'0 hcent.1
  change n * q' ≤ n' * q + (L + 1) * q * q' at hcross
  have hn0n := (le_add_closeRadius_of_Close hclose).1
  have hn0n' := (le_add_closeRadius_of_Close hclose').2
  have hn'close : n' ≤ n + 2 * R := by
    change n₀ ≤ n + R at hn0n
    change n' ≤ n₀ + R at hn0n'
    omega
  have hlower : n * q + n ≤ n * q' := by
    calc
      n * q + n = n * (q + 1) := by ring
      _ ≤ n * q' := Nat.mul_le_mul_left n (by omega)
  have hnBound : n ≤ (2 * R) * q + (L + 1) * q * q' := by
    have hn'qmul : n' * q ≤ (n + 2 * R) * q := Nat.mul_le_mul_right q hn'close
    have hchain : n * q + n ≤
        n * q + ((2 * R) * q + (L + 1) * q * q') := by
      calc
        n * q + n ≤ n * q' := hlower
        _ ≤ n' * q + (L + 1) * q * q' := hcross
        _ ≤ (n + 2 * R) * q + (L + 1) * q * q' :=
          Nat.add_le_add_right hn'qmul _
        _ = n * q + ((2 * R) * q + (L + 1) * q * q') := by ring
    exact Nat.le_of_add_le_add_left hchain
  have hQpos : 0 < Q := by positivity
  have hL : L + 1 ≤ 13 * Q := by
    dsimp [L]
    have : q + q' ≤ 2 * Q := by omega
    nlinarith
  have hRQ : R ≤ Q ^ 2 := by
    dsimp [R, closeRadius, Q]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    dsimp [E]
    nlinarith
  have hupper : (2 * R) * q + (L + 1) * q * q' ≤ 16 * Q ^ 3 := by
    have hfirst : (2 * R) * q ≤ (2 * Q ^ 2) * Q :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hRQ) hqQ.le
    have hsecond : (L + 1) * q * q' ≤ (13 * Q) * Q * Q :=
      Nat.mul_le_mul (Nat.mul_le_mul hL hqQ.le) hq'Q.le
    calc
      (2 * R) * q + (L + 1) * q * q' ≤
          (2 * Q ^ 2) * Q + (13 * Q) * Q * Q := Nat.add_le_add hfirst hsecond
      _ = 15 * Q ^ 3 := by ring
      _ ≤ 16 * Q ^ 3 := Nat.mul_le_mul_right (Q ^ 3) (by omega)
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 3 * E + 4 < (W + 1) * k := by
    dsimp [E]
    nlinarith only [hWmul, hkW, hW]
  have hpowEq : 16 * Q ^ 3 = 2 ^ (3 * E + 4) := by
    dsimp [Q]
    rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
    rw [show 4 + E * 3 = 3 * E + 4 by ring]
  have hnLarge : 16 * Q ^ 3 < n := by
    rw [hpowEq]
    calc
      2 ^ (3 * E + 4) < 2 ^ ((W + 1) * k) :=
        Nat.pow_lt_pow_right (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n := (mem_targetBlock.mp hn).1
  omega

lemma redSub_support_disjoint_of_close_to_of_ne
    {W C k n₀ n n' d e d' e' q q' : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hclose : Close W k n₀ n) (hclose' : Close W k n₀ n')
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hq : q ∈ redSubLengths W k n d e)
    (hq' : q' ∈ redSubLengths W k n' d' e')
    (hqq' : q ≠ q') : Disjoint (lengthSupport q n) (lengthSupport q' n') := by
  rcases lt_or_gt_of_ne hqq' with hlt | hgt
  · exact redSub_support_disjoint_of_close_to_of_lt hC hW hk hn₀ hn hn'
      hclose hclose' hde hde' hq hq' hlt
  · exact (redSub_support_disjoint_of_close_to_of_lt hC hW hk hn₀ hn' hn
      hclose' hclose hde' hde hq' hq hgt).symm

abbrev RedTrial := Sigma fun _de : ℕ × ℕ ↦ ℕ

noncomputable def redTrials (W C k n : ℕ) : Finset RedTrial :=
  (validRedSubchannels W C k).sigma fun de ↦
    redSubLengths W k n de.1 de.2

@[simp] lemma mem_redTrials {W C k n : ℕ} {a : RedTrial} :
    a ∈ redTrials W C k n ↔
      a.1 ∈ validRedSubchannels W C k ∧
        a.2 ∈ redSubLengths W k n a.1.1 a.1.2 := by
  simp [redTrials]

def redTrialSupport (n : ℕ) (a : RedTrial) : Finset ℕ :=
  lengthSupport a.2 n

def redTrialEvent (n : ℕ) (a : RedTrial) : Set (Set ℕ) :=
  lengthEvent a.2 n

lemma redTrialEvent_supported {n : ℕ} (a : RedTrial) {S T : Set ℕ}
    (hST : S ∩ (redTrialSupport n a : Set ℕ) =
      T ∩ (redTrialSupport n a : Set ℕ)) :
    (S ∈ redTrialEvent n a ↔ T ∈ redTrialEvent n a) := by
  exact lengthEvent_congr_of_inter_support_eq hST

lemma redTrialSupport_disjoint {W C k n : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) {a b : RedTrial}
    (ha : a ∈ redTrials W C k n) (hb : b ∈ redTrials W C k n)
    (hab : a ≠ b) : Disjoint (redTrialSupport n a) (redTrialSupport n b) := by
  have ha' := mem_redTrials.mp ha
  have hb' := mem_redTrials.mp hb
  have hqne : a.2 ≠ b.2 := by
    intro hq
    have hdene : a.1 ≠ b.1 := by
      intro hde
      apply hab
      exact Sigma.ext hde (heq_of_eq hq)
    exact redSubLengths_ne_of_channel_ne hW hk hn ha'.1 hb'.1 hdene
      ha'.2 hb'.2 hq
  have hclose : Close W k n n := by simp [Close]
  exact redSub_support_disjoint_of_close_to_of_ne hC hW hk hn hn hn
    hclose hclose ha'.1 hb'.1 ha'.2 hb'.2 hqne

noncomputable def redMeanCoefficient : ℝ :=
  7 * Real.exp (-1600) / 40960

lemma redMeanCoefficient_pos : 0 < redMeanCoefficient := by
  rw [redMeanCoefficient]
  positivity

lemma eventually_redTrial_probability_lower (W C : ℕ)
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k,
      ∀ a ∈ redTrials W C k n,
        Real.exp (-1600) /
            (1024 * (redSubLengthScale W k n a.1.1 a.1.2 : ℝ)) ≤
          fairBits.real (bitsToSet ⁻¹' redTrialEvent n a) := by
  have hlocal := eventually_lengthEvent_probability_lower
  rw [eventually_atTop] at hlocal ⊢
  obtain ⟨Q₀, hQ₀⟩ := hlocal
  refine ⟨Q₀ + W + 2 * W, ?_⟩
  intro k hk n hn a ha
  have hkW : W ≤ k := by omega
  have ha' := mem_redTrials.mp ha
  rcases mem_validRedSubchannels.mp ha'.1 with
    ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
  let P := redSubLengthScale W k n a.1.1 a.1.2
  have hP : 0 < P := by
    dsimp [P]
    have heFive : 5 * a.1.2 + 5 ≤ W :=
      (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * a.1.2)).trans heSafe
    exact redSubLengthScale_pos heFive hkW hdle hn
  have hqBounds := mem_redSubLengths.mp ha'.2
  change P ≤ a.2 ∧ a.2 ≤ 16 * P ∧ _ at hqBounds
  have hqpos : 0 < a.2 := hP.trans_le hqBounds.1
  have hqQ₀ : Q₀ ≤ a.2 := by
    have hpowLow := redSubLengthScale_lower
      (d := a.1.1) (e := a.1.2) hkW hn
    change 2 ^ (k - W) ≤ P at hpowLow
    calc
      Q₀ ≤ 2 ^ Q₀ := self_le_two_pow Q₀
      _ ≤ 2 ^ (k - W) := Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
      _ ≤ P := hpowLow
      _ ≤ a.2 := hqBounds.1
  have hsq := redSubLength_sq_le_target hC hW (by omega) hn ha'.1 ha'.2
  rw [redTrialEvent, fairBits_real_preimage]
  calc
    Real.exp (-1600) / (1024 * (P : ℝ)) ≤
        Real.exp (-1600) / (64 * (a.2 : ℝ)) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
      exact_mod_cast (calc
        64 * a.2 ≤ 64 * (16 * P) := Nat.mul_le_mul_left 64 hqBounds.2.1
        _ = 1024 * P := by ring)
    _ ≤ fairSetMeasure.real (lengthEvent a.2 n) := hQ₀ _ hqQ₀ n hsq

lemma eventually_redTrial_mean_lower (W C : ℕ)
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k,
      redMeanCoefficient * (C : ℝ) * (k : ℝ) ≤
        ∑ a ∈ redTrials W C k n,
          fairBits.real (bitsToSet ⁻¹' redTrialEvent n a) := by
  have htrial := eventually_redTrial_probability_lower W C hC hW
  have hrecip := eventually_sum_scaleBluePrimes_inv_le W
  filter_upwards [htrial, hrecip, eventually_ge_atTop (2 * W + 40)] with
      k htrial hrecip hk n hn
  have hk2W : 2 * W ≤ k := by omega
  have hchannelCard := validRedSubchannels_card_lower hC hW hk2W
  have hCk40 : 40 ≤ C * k := by
    have : 40 ≤ k := by omega
    exact this.trans (by simpa only [one_mul] using Nat.mul_le_mul_right k hC)
  have hdivlt : C * k < (C * k / 20 + 1) * 20 := by
    rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < 20)]
    omega
  have hfloor : C * k ≤ 40 * (C * k / 20) := by omega
  have hcardReal : (C : ℝ) * k / 40 ≤
      ((validRedSubchannels W C k).card : ℝ) := by
    have hfloorR : ((C * k : ℕ) : ℝ) ≤
        40 * ((C * k / 20 : ℕ) : ℝ) := by exact_mod_cast hfloor
    have hcardR : ((C * k / 20 : ℕ) : ℝ) ≤
        ((validRedSubchannels W C k).card : ℝ) := by
      exact_mod_cast hchannelCard
    push_cast at hfloorR
    nlinarith
  have hfiber : ∀ de ∈ validRedSubchannels W C k,
      7 * Real.exp (-1600) / 1024 ≤
        ∑ q ∈ redSubLengths W k n de.1 de.2,
          fairBits.real
            (bitsToSet ⁻¹' redTrialEvent n (⟨de, q⟩ : RedTrial)) := by
    intro de hde
    let P := redSubLengthScale W k n de.1 de.2
    rcases mem_validRedSubchannels.mp hde with
      ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
    have hP : 0 < P := by
      dsimp [P]
      exact redSubLengthScale_pos (by omega) (by omega) hdle hn
    have hcard := redSubLengths_card_lower (W := W) (k := k)
      (n := n) (d := de.1) (e := de.2) hP hrecip
    let cP := Real.exp (-1600) / (1024 * (P : ℝ))
    have heach : ∀ q ∈ redSubLengths W k n de.1 de.2,
        cP ≤ fairBits.real
          (bitsToSet ⁻¹' redTrialEvent n (⟨de, q⟩ : RedTrial)) := by
      intro q hq
      exact htrial n hn ⟨de, q⟩ (by simp [hde, hq])
    calc
      7 * Real.exp (-1600) / 1024 = (7 * (P : ℝ)) * cP := by
        dsimp [cP]
        field_simp
      _ ≤ ((redSubLengths W k n de.1 de.2).card : ℝ) * cP := by
        gcongr
        exact_mod_cast hcard
      _ = ∑ _q ∈ redSubLengths W k n de.1 de.2, cP := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ redSubLengths W k n de.1 de.2,
          fairBits.real
            (bitsToSet ⁻¹' redTrialEvent n (⟨de, q⟩ : RedTrial)) :=
        Finset.sum_le_sum heach
  calc
    redMeanCoefficient * (C : ℝ) * (k : ℝ) ≤
        ((validRedSubchannels W C k).card : ℝ) *
          (7 * Real.exp (-1600) / 1024) := by
      rw [redMeanCoefficient]
      have hexp : 0 < Real.exp (-1600) := Real.exp_pos _
      nlinarith
    _ = ∑ _de ∈ validRedSubchannels W C k,
        (7 * Real.exp (-1600) / 1024) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ de ∈ validRedSubchannels W C k,
        ∑ q ∈ redSubLengths W k n de.1 de.2,
          fairBits.real
            (bitsToSet ⁻¹' redTrialEvent n (⟨de, q⟩ : RedTrial)) :=
      Finset.sum_le_sum hfiber
    _ = ∑ a ∈ redTrials W C k n,
        fairBits.real (bitsToSet ⁻¹' redTrialEvent n a) := by
      rw [redTrials, Finset.sum_sigma]

def repairCount (D k : ℕ) : ℕ := k / (D + 1)

noncomputable def redCount (W C k n : ℕ) (ω : ℕ → Prop) : ℕ :=
  eventCount (redTrials W C k n).attach
    (fun a ↦ redTrialEvent n a.1) ω

def RedExceptional (W C D k n : ℕ) (ω : ℕ → Prop) : Prop :=
  redCount W C k n ω < repairCount D k

def RedTypical (W C D k n : ℕ) (ω : ℕ → Prop) : Prop :=
  repairCount D k ≤ redCount W C k n ω

lemma redTypical_or_exceptional (W C D k n : ℕ) (ω : ℕ → Prop) :
    RedTypical W C D k n ω ∨ RedExceptional W C D k n ω := by
  unfold RedTypical RedExceptional
  omega

lemma eventually_redExceptional_measure_le (W C D : ℕ)
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k,
      fairBits.real {ω | RedExceptional W C D k n ω} ≤
        Real.exp ((k : ℝ) -
          (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ))) := by
  have hmean := eventually_redTrial_mean_lower W C hC hW
  filter_upwards [hmean, eventually_ge_atTop (2 * W)] with k hmean hk n hn
  let trials := redTrials W C k n
  let ι := ↥trials
  let u : ι → Finset ℕ := fun a ↦ redTrialSupport n a.1
  let E : ι → Set (Set ℕ) := fun a ↦ redTrialEvent n a.1
  have hdisj : ∀ i j : ι, i ≠ j → Disjoint (u i) (u j) := by
    intro i j hij
    apply redTrialSupport_disjoint hC hW hk hn i.property j.property
    exact fun h ↦ hij (Subtype.ext h)
  have hsupp : ∀ i : ι, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i) := by
    intro i S T hST
    exact redTrialEvent_supported i.1 hST
  have htail := independent_event_lower_tail_bound u E trials.attach
    (repairCount D k) hdisj hsupp
  have hsum : redMeanCoefficient * (C : ℝ) * (k : ℝ) ≤
      ∑ a ∈ trials.attach, fairBits.real (bitsToSet ⁻¹' E a) := by
    change redMeanCoefficient * (C : ℝ) * (k : ℝ) ≤
      ∑ a ∈ trials.attach,
        fairBits.real (bitsToSet ⁻¹' redTrialEvent n a.1)
    have hatt :
        (∑ a ∈ trials.attach,
          fairBits.real (bitsToSet ⁻¹' redTrialEvent n a.1)) =
        ∑ a ∈ trials,
          fairBits.real (bitsToSet ⁻¹' redTrialEvent n a) := by
      simpa only using Finset.sum_attach trials
        (fun a ↦ fairBits.real (bitsToSet ⁻¹' redTrialEvent n a))
    rw [hatt]
    exact hmean n hn
  have ht : (repairCount D k : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.div_le_self k (D + 1)
  change fairBits.real {ω | eventCount trials.attach E ω < repairCount D k} ≤ _
  calc
    fairBits.real {ω | eventCount trials.attach E ω < repairCount D k} ≤
        Real.exp ((repairCount D k : ℝ) -
          (1 / 2) * ∑ a ∈ trials.attach,
            fairBits.real (bitsToSet ⁻¹' E a)) := htail
    _ ≤ Real.exp ((k : ℝ) -
        (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-! ### Simultaneous red tails for a close cluster of targets -/

noncomputable def redCoreTrials (W C k n₀ : ℕ) : Finset RedTrial :=
  (validRedSubchannels W C k).sigma fun de ↦
    coreRedSubLengths W k n₀ de.1 de.2

@[simp] lemma mem_redCoreTrials {W C k n₀ : ℕ} {a : RedTrial} :
    a ∈ redCoreTrials W C k n₀ ↔
      a.1 ∈ validRedSubchannels W C k ∧
        a.2 ∈ coreRedSubLengths W k n₀ a.1.1 a.1.2 := by
  simp [redCoreTrials]

noncomputable def redClusterSupport {m : ℕ} (g : Fin m → ℕ)
    (a : RedTrial) : Finset ℕ :=
  Finset.univ.biUnion fun i ↦ lengthSupport a.2 (g i)

def redClusterEvent {m : ℕ} (g : Fin m → ℕ) (a : RedTrial) : Set (Set ℕ) :=
  ⋃ i ∈ (Finset.univ : Finset (Fin m)), lengthEvent a.2 (g i)

lemma redClusterEvent_supported {m : ℕ} (g : Fin m → ℕ) (a : RedTrial)
    {S T : Set ℕ}
    (hST : S ∩ (redClusterSupport g a : Set ℕ) =
      T ∩ (redClusterSupport g a : Set ℕ)) :
    (S ∈ redClusterEvent g a ↔ T ∈ redClusterEvent g a) := by
  classical
  have hone (i : Fin m) :
      S ∩ (lengthSupport a.2 (g i) : Set ℕ) =
        T ∩ (lengthSupport a.2 (g i) : Set ℕ) := by
    ext x
    have hx := Set.ext_iff.mp hST x
    simp only [Set.mem_inter_iff, Finset.mem_coe] at hx ⊢
    have hsub (hxmem : x ∈ lengthSupport a.2 (g i)) :
        x ∈ redClusterSupport g a := by
      rw [redClusterSupport, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, hxmem⟩
    constructor
    · rintro ⟨hxS, hxu⟩
      exact ⟨(hx.mp ⟨hxS, hsub hxu⟩).1, hxu⟩
    · rintro ⟨hxT, hxu⟩
      exact ⟨(hx.mpr ⟨hxT, hsub hxu⟩).1, hxu⟩
  simp only [redClusterEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hiu, hi⟩
    exact ⟨i, hiu, (lengthEvent_congr_of_inter_support_eq (hone i)).mp hi⟩
  · rintro ⟨i, hiu, hi⟩
    exact ⟨i, hiu, (lengthEvent_congr_of_inter_support_eq (hone i)).mpr hi⟩

lemma redCoreTrial_mem_redTrials_of_close {W C k n₀ n : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hclose : Close W k n₀ n) {a : RedTrial}
    (ha : a ∈ redCoreTrials W C k n₀) : a ∈ redTrials W C k n := by
  rw [mem_redCoreTrials] at ha
  rw [mem_redTrials]
  exact ⟨ha.1, coreRedSubLengths_subset_close hC hW hk ha.1 hclose ha.2⟩

lemma redClusterSupport_disjoint {m W C k n₀ : ℕ} {g : Fin m → ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k)
    (hgn : ∀ i, g i ∈ targetBlock W k)
    (hgclose : ∀ i, Close W k n₀ (g i))
    {a b : RedTrial} (ha : a ∈ redCoreTrials W C k n₀)
    (hb : b ∈ redCoreTrials W C k n₀) (hab : a ≠ b) :
    Disjoint (redClusterSupport g a) (redClusterSupport g b) := by
  classical
  have ha' := mem_redCoreTrials.mp ha
  have hb' := mem_redCoreTrials.mp hb
  have haRed := (mem_coreRedSubLengths.mp ha'.2).1
  have hbRed := (mem_coreRedSubLengths.mp hb'.2).1
  have hqne : a.2 ≠ b.2 := by
    intro hq
    have hdene : a.1 ≠ b.1 := by
      intro hde
      apply hab
      exact Sigma.ext hde (heq_of_eq hq)
    exact redSubLengths_ne_of_channel_ne hW hk hn₀ ha'.1 hb'.1 hdene
      haRed hbRed hq
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [redClusterSupport, Finset.mem_biUnion] at hxa hxb
  obtain ⟨i, hiu, hxi⟩ := hxa
  obtain ⟨j, hju, hxj⟩ := hxb
  have hai := redCoreTrial_mem_redTrials_of_close hC hW hk (hgclose i) ha
  have hbj := redCoreTrial_mem_redTrials_of_close hC hW hk (hgclose j) hb
  have hd := redSub_support_disjoint_of_close_to_of_ne hC hW hk hn₀
    (hgn i) (hgn j) (hgclose i) (hgclose j)
    (mem_redTrials.mp hai).1 (mem_redTrials.mp hbj).1
    (mem_redTrials.mp hai).2 (mem_redTrials.mp hbj).2 hqne
  exact (Finset.disjoint_left.mp hd) hxi hxj

lemma fairBits_redClusterEvent_eq_sum {m W C k n₀ : ℕ} {g : Fin m → ℕ}
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hgn : ∀ i, g i ∈ targetBlock W k)
    (hgclose : ∀ i, Close W k n₀ (g i))
    (hginj : Function.Injective g) {a : RedTrial}
    (ha : a ∈ redCoreTrials W C k n₀) :
    fairBits.real (bitsToSet ⁻¹' redClusterEvent g a) =
      ∑ i : Fin m, fairBits.real (bitsToSet ⁻¹' lengthEvent a.2 (g i)) := by
  classical
  have ha' := mem_redCoreTrials.mp ha
  have hqi (i : Fin m) :
      a.2 ∈ redSubLengths W k (g i) a.1.1 a.1.2 :=
    coreRedSubLengths_subset_close (by omega) hW hk ha'.1 (hgclose i) ha'.2
  rw [redClusterEvent, fairBits_real_preimage, measureReal_biUnion_finset]
  · simp only [fairBits_real_preimage]
  · intro i hi j hj hij
    exact redLengthEvents_disjoint_of_close_to hC hW hk (hgn i) (hgn j)
      ha'.1 (hqi i) (hqi j) (hgclose i) (hgclose j)
      (fun heq ↦ hij (hginj heq))
  · intro i hi
    exact measurableSet_lengthEvent _ _

lemma eventCount_attach {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (E : ι → Set (Set ℕ)) (ω : ℕ → Prop) :
    eventCount s.attach (fun i ↦ E i.1) ω = eventCount s E ω := by
  classical
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_eventIndicator_eq_eventCount, ← sum_eventIndicator_eq_eventCount]
  simpa only using Finset.sum_attach s (fun i ↦ eventIndicator (E i) ω)

lemma redCount_eq_eventCount (W C k n : ℕ) (ω : ℕ → Prop) :
    redCount W C k n ω =
      eventCount (redTrials W C k n) (redTrialEvent n) ω := by
  classical
  exact eventCount_attach _ _ _

lemma redClusterCount_lt_of_exceptional {m W C D k n₀ : ℕ}
    (hm : 0 < m) {g : Fin m → ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hgclose : ∀ i, Close W k n₀ (g i)) {ω : ℕ → Prop}
    (hexc : ∀ i, RedExceptional W C D k (g i) ω) :
    eventCount (redCoreTrials W C k n₀) (redClusterEvent g) ω <
      m * repairCount D k := by
  classical
  let core := redCoreTrials W C k n₀
  let good : Fin m → Finset RedTrial := fun i ↦
    core.filter fun a ↦ bitsToSet ω ∈ redTrialEvent (g i) a
  have hcover : core.filter (fun a ↦ bitsToSet ω ∈ redClusterEvent g a) ⊆
      Finset.univ.biUnion good := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_biUnion]
    simp only [redClusterEvent, Set.mem_iUnion] at ha
    obtain ⟨i, hiu, hi⟩ := ha.2
    exact ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ha.1, hi⟩⟩
  have hgood (i : Fin m) : (good i).card < repairCount D k := by
    have hsub : good i ⊆
        (redTrials W C k (g i)).filter
          (fun a ↦ bitsToSet ω ∈ redTrialEvent (g i) a) := by
      intro a ha
      simp only [good, Finset.mem_filter] at ha
      rw [Finset.mem_filter]
      exact ⟨redCoreTrial_mem_redTrials_of_close hC hW hk (hgclose i) ha.1,
        ha.2⟩
    have hle := Finset.card_le_card hsub
    have hex := hexc i
    rw [RedExceptional, redCount_eq_eventCount] at hex
    change ((redTrials W C k (g i)).filter
      (fun a ↦ bitsToSet ω ∈ redTrialEvent (g i) a)).card < repairCount D k at hex
    exact hle.trans_lt hex
  change (core.filter (fun a ↦ bitsToSet ω ∈ redClusterEvent g a)).card < _
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  calc
    (core.filter (fun a ↦ bitsToSet ω ∈ redClusterEvent g a)).card ≤
        (Finset.univ.biUnion good).card := Finset.card_le_card hcover
    _ ≤ ∑ i : Fin m, (good i).card := Finset.card_biUnion_le
    _ < ∑ _i : Fin m, repairCount D k :=
      Finset.sum_lt_sum_of_nonempty huniv (fun i _ ↦ hgood i)
    _ = m * repairCount D k := by simp [nsmul_eq_mul]

noncomputable def redClusterMeanCoefficient : ℝ :=
  3 * Real.exp (-1600) / 40960

lemma redClusterMeanCoefficient_pos : 0 < redClusterMeanCoefficient := by
  rw [redClusterMeanCoefficient]
  positivity

lemma eventually_redCluster_mean_lower (m W C : ℕ)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n₀ ∈ targetBlock W k,
      ∀ g : Fin m → ℕ,
        (∀ i, g i ∈ targetBlock W k) →
        (∀ i, Close W k n₀ (g i)) → Function.Injective g →
        redClusterMeanCoefficient * (m : ℝ) * (C : ℝ) * (k : ℝ) ≤
          ∑ a ∈ redCoreTrials W C k n₀,
            fairBits.real (bitsToSet ⁻¹' redClusterEvent g a) := by
  have htrial := eventually_redTrial_probability_lower W C (by omega) hW
  have hrecip := eventually_sum_scaleBluePrimes_inv_le W
  filter_upwards [htrial, hrecip, eventually_ge_atTop (2 * W + 40)] with
      k htrial hrecip hk n₀ hn₀ g hgn hgclose hginj
  have hk2W : 2 * W ≤ k := by omega
  have hchannelCard := validRedSubchannels_card_lower (by omega : 1 ≤ C) hW hk2W
  have hCk40 : 40 ≤ C * k := by
    have : 40 ≤ k := by omega
    exact this.trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right k (show 1 ≤ C by omega))
  have hdivlt : C * k < (C * k / 20 + 1) * 20 := by
    rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < 20)]
    omega
  have hfloor : C * k ≤ 40 * (C * k / 20) := by omega
  have hcardReal : (C : ℝ) * k / 40 ≤
      ((validRedSubchannels W C k).card : ℝ) := by
    have hfloorR : ((C * k : ℕ) : ℝ) ≤
        40 * ((C * k / 20 : ℕ) : ℝ) := by exact_mod_cast hfloor
    have hcardR : ((C * k / 20 : ℕ) : ℝ) ≤
        ((validRedSubchannels W C k).card : ℝ) := by
      exact_mod_cast hchannelCard
    push_cast at hfloorR
    nlinarith
  have hfiber : ∀ de ∈ validRedSubchannels W C k,
      (m : ℝ) * (3 * Real.exp (-1600) / 1024) ≤
        ∑ q ∈ coreRedSubLengths W k n₀ de.1 de.2,
          fairBits.real
            (bitsToSet ⁻¹' redClusterEvent g (⟨de, q⟩ : RedTrial)) := by
    intro de hde
    let P := redSubLengthScale W k n₀ de.1 de.2
    rcases mem_validRedSubchannels.mp hde with
      ⟨hdOff, heRange, hdle, heSafe, hvalid⟩
    have hP : 17 ≤ P := by
      have hlow := redSubLengthScale_lower (W := W) (k := k)
        (n := n₀) (d := de.1) (e := de.2) (by omega) hn₀
      change 2 ^ (k - W) ≤ P at hlow
      have : 32 ≤ 2 ^ (k - W) := by
        rw [show 32 = 2 ^ 5 by norm_num]
        exact Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
      omega
    have hcard := coreRedSubLengths_card_lower hP hrecip
    let cP := Real.exp (-1600) / (1024 * ((P + 1 : ℕ) : ℝ))
    have hcP : 0 ≤ cP := by dsimp [cP]; positivity
    have heach : ∀ q ∈ coreRedSubLengths W k n₀ de.1 de.2,
        (m : ℝ) * cP ≤ fairBits.real
          (bitsToSet ⁻¹' redClusterEvent g (⟨de, q⟩ : RedTrial)) := by
      intro q hq
      have hcluster := fairBits_redClusterEvent_eq_sum hC hW hk2W hgn
        hgclose hginj (show (⟨de, q⟩ : RedTrial) ∈ redCoreTrials W C k n₀ by
          simp [hde, hq])
      rw [hcluster]
      have hi (i : Fin m) : cP ≤
          fairBits.real (bitsToSet ⁻¹' lengthEvent q (g i)) := by
        have hqi := coreRedSubLengths_subset_close (by omega : 1 ≤ C) hW hk2W
          hde (hgclose i) hq
        have hPscales := redSubLengthScales_close (by omega : 1 ≤ C) hW hk2W
          hde (hgclose i)
        have hPi := hPscales.2
        have hPiPos : 0 < redSubLengthScale W k (g i) de.1 de.2 := by
          dsimp [P] at hP
          omega
        have htriali := htrial (g i) (hgn i) (⟨de, q⟩ : RedTrial) (by
          simp [hde, hqi])
        change Real.exp (-1600) /
            (1024 * (redSubLengthScale W k (g i) de.1 de.2 : ℝ)) ≤
          fairBits.real (bitsToSet ⁻¹' lengthEvent q (g i)) at htriali
        calc
          cP ≤ Real.exp (-1600) /
              (1024 * (redSubLengthScale W k (g i) de.1 de.2 : ℝ)) := by
            apply div_le_div_of_nonneg_left (Real.exp_pos _).le
              (mul_pos (by norm_num) (by exact_mod_cast hPiPos))
            exact_mod_cast Nat.mul_le_mul_left 1024 hPi
          _ ≤ _ := htriali
      calc
        (m : ℝ) * cP = ∑ _i : Fin m, cP := by simp
        _ ≤ ∑ i : Fin m,
            fairBits.real (bitsToSet ⁻¹' lengthEvent q (g i)) :=
          Finset.sum_le_sum fun i _ ↦ hi i
    have hbase : 3 * Real.exp (-1600) / 1024 ≤
        ((6 * P : ℕ) : ℝ) * cP := by
      dsimp [cP]
      have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
      have hexp := Real.exp_pos (-1600)
      push_cast
      field_simp
      nlinarith
    calc
      (m : ℝ) * (3 * Real.exp (-1600) / 1024) ≤
          (m : ℝ) * (((6 * P : ℕ) : ℝ) * cP) := by gcongr
      _ = ((6 * P : ℕ) : ℝ) * ((m : ℝ) * cP) := by ring
      _ ≤ ((coreRedSubLengths W k n₀ de.1 de.2).card : ℝ) *
          ((m : ℝ) * cP) := by
        have hcardR : ((6 * P : ℕ) : ℝ) ≤
            ((coreRedSubLengths W k n₀ de.1 de.2).card : ℝ) := by
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcardR (mul_nonneg (by positivity) hcP)
      _ = ∑ _q ∈ coreRedSubLengths W k n₀ de.1 de.2,
          ((m : ℝ) * cP) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ coreRedSubLengths W k n₀ de.1 de.2,
          fairBits.real
            (bitsToSet ⁻¹' redClusterEvent g (⟨de, q⟩ : RedTrial)) :=
        Finset.sum_le_sum heach
  calc
    redClusterMeanCoefficient * (m : ℝ) * (C : ℝ) * (k : ℝ) ≤
        ((validRedSubchannels W C k).card : ℝ) *
          ((m : ℝ) * (3 * Real.exp (-1600) / 1024)) := by
      rw [redClusterMeanCoefficient]
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have hexp : 0 < Real.exp (-1600) := Real.exp_pos _
      calc
        3 * Real.exp (-1600) / 40960 * (m : ℝ) * (C : ℝ) * (k : ℝ) =
            ((C : ℝ) * k / 40) *
              ((m : ℝ) * (3 * Real.exp (-1600) / 1024)) := by ring
        _ ≤ ((validRedSubchannels W C k).card : ℝ) *
              ((m : ℝ) * (3 * Real.exp (-1600) / 1024)) :=
          mul_le_mul_of_nonneg_right hcardReal
            (mul_nonneg hm0 (by positivity))
    _ = ∑ _de ∈ validRedSubchannels W C k,
        ((m : ℝ) * (3 * Real.exp (-1600) / 1024)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ de ∈ validRedSubchannels W C k,
        ∑ q ∈ coreRedSubLengths W k n₀ de.1 de.2,
          fairBits.real
            (bitsToSet ⁻¹' redClusterEvent g (⟨de, q⟩ : RedTrial)) :=
      Finset.sum_le_sum hfiber
    _ = ∑ a ∈ redCoreTrials W C k n₀,
        fairBits.real (bitsToSet ⁻¹' redClusterEvent g a) := by
      rw [redCoreTrials, Finset.sum_sigma]

lemma eventually_redExceptional_tuple_measure_le (m W C D : ℕ) (hm : 0 < m)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n₀ ∈ targetBlock W k,
      ∀ g : Fin m → ℕ,
        (∀ i, g i ∈ targetBlock W k) →
        (∀ i, Close W k n₀ (g i)) → Function.Injective g →
        fairBits.real {ω | ∀ i, RedExceptional W C D k (g i) ω} ≤
          Real.exp ((m : ℝ) * (k : ℝ) -
            (1 / 2) *
              (redClusterMeanCoefficient * (m : ℝ) * (C : ℝ) * (k : ℝ))) := by
  have hmean := eventually_redCluster_mean_lower m W C hC hW
  filter_upwards [hmean, eventually_ge_atTop (2 * W)] with
      k hmean hk n₀ hn₀ g hgn hgclose hginj
  let trials := redCoreTrials W C k n₀
  let ι := ↥trials
  let u : ι → Finset ℕ := fun a ↦ redClusterSupport g a.1
  let E : ι → Set (Set ℕ) := fun a ↦ redClusterEvent g a.1
  have hdisj : ∀ i j : ι, i ≠ j → Disjoint (u i) (u j) := by
    intro i j hij
    apply redClusterSupport_disjoint (by omega : 1 ≤ C) hW hk hn₀ hgn hgclose
      i.property j.property
    exact fun h ↦ hij (Subtype.ext h)
  have hsupp : ∀ i : ι, ∀ {S T : Set ℕ},
      S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i) := by
    intro i S T hST
    exact redClusterEvent_supported g i.1 hST
  have htail := independent_event_lower_tail_bound u E trials.attach
    (m * repairCount D k) hdisj hsupp
  have hsum : redClusterMeanCoefficient * (m : ℝ) * (C : ℝ) * (k : ℝ) ≤
      ∑ a ∈ trials.attach, fairBits.real (bitsToSet ⁻¹' E a) := by
    change redClusterMeanCoefficient * (m : ℝ) * (C : ℝ) * (k : ℝ) ≤
      ∑ a ∈ trials.attach,
        fairBits.real (bitsToSet ⁻¹' redClusterEvent g a.1)
    have hatt :
        (∑ a ∈ trials.attach,
          fairBits.real (bitsToSet ⁻¹' redClusterEvent g a.1)) =
        ∑ a ∈ trials,
          fairBits.real (bitsToSet ⁻¹' redClusterEvent g a) := by
      simpa only using Finset.sum_attach trials
        (fun a ↦ fairBits.real (bitsToSet ⁻¹' redClusterEvent g a))
    rw [hatt]
    exact hmean n₀ hn₀ g hgn hgclose hginj
  have hsubset : {ω | ∀ i, RedExceptional W C D k (g i) ω} ⊆
      {ω | eventCount trials.attach E ω < m * repairCount D k} := by
    intro ω hω
    have hc := redClusterCount_lt_of_exceptional hm (by omega : 1 ≤ C) hW hk
      hgclose hω
    change eventCount trials.attach (fun a ↦ redClusterEvent g a.1) ω < _
    rw [eventCount_attach]
    exact hc
  calc
    fairBits.real {ω | ∀ i, RedExceptional W C D k (g i) ω} ≤
        fairBits.real {ω | eventCount trials.attach E ω <
          m * repairCount D k} :=
      measureReal_mono hsubset (measure_lt_top fairBits _).ne
    _ ≤ Real.exp (((m * repairCount D k : ℕ) : ℝ) -
        (1 / 2) * ∑ a ∈ trials.attach,
          fairBits.real (bitsToSet ⁻¹' E a)) := htail
    _ ≤ Real.exp ((m : ℝ) * (k : ℝ) -
        (1 / 2) *
          (redClusterMeanCoefficient * (m : ℝ) * (C : ℝ) * (k : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have ht : ((m * repairCount D k : ℕ) : ℝ) ≤ (m : ℝ) * (k : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left m (Nat.div_le_self k (D + 1))
      nlinarith

noncomputable def closeTargets (W k n₀ : ℕ) : Finset ℕ := by
  classical
  exact (targetBlock W k).filter fun n ↦ Close W k n₀ n

@[simp] lemma mem_closeTargets {W k n₀ n : ℕ} :
    n ∈ closeTargets W k n₀ ↔ n ∈ targetBlock W k ∧ Close W k n₀ n := by
  classical
  simp [closeTargets]

lemma closeTargets_card_le (W k n₀ : ℕ) :
    (closeTargets W k n₀).card ≤ 2 * closeRadius W k + 1 := by
  classical
  let I := Finset.Icc (n₀ - closeRadius W k) (n₀ + closeRadius W k)
  have hsub : closeTargets W k n₀ ⊆ I := by
    intro n hn
    rw [mem_closeTargets] at hn
    change n ∈ Finset.Icc (n₀ - closeRadius W k) (n₀ + closeRadius W k)
    rw [Finset.mem_Icc]
    have hb := le_add_closeRadius_of_Close hn.2
    omega
  calc
    (closeTargets W k n₀).card ≤ I.card := Finset.card_le_card hsub
    _ = n₀ + closeRadius W k + 1 - (n₀ - closeRadius W k) := by
      simp [I, Nat.card_Icc]
    _ ≤ 2 * closeRadius W k + 1 := by omega

noncomputable def chooseEnumExact {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hS : S.card = m) : Fin m → α :=
  fun i ↦ ((Fintype.equivFin ↥S).symm
    (Fin.cast (by simp [Fintype.card_coe, hS]) i)).val

lemma chooseEnumExact_injective {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hS : S.card = m) :
    Function.Injective (chooseEnumExact S hS) := by
  intro i j h
  simp only [chooseEnumExact] at h
  exact Fin.cast_injective _
    ((Fintype.equivFin ↥S).symm.injective (Subtype.val_injective h))

lemma chooseEnumExact_mem {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hS : S.card = m) (i : Fin m) :
    chooseEnumExact S hS i ∈ S := by
  exact ((Fintype.equivFin ↥S).symm _).prop

noncomputable def RedClustered (W C D k n₀ : ℕ) (ω : ℕ → Prop) : Prop := by
  classical
  exact D + 1 ≤ ((closeTargets W k n₀).filter
    fun n ↦ RedExceptional W C D k n ω).card

lemma eventually_redClustered_measure_le (W C D : ℕ)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n₀ ∈ targetBlock W k,
      fairBits.real {ω | RedClustered W C D k n₀ ω} ≤
        ((2 * closeRadius W k + 1 : ℕ) : ℝ) ^ (D + 1) *
          Real.exp (((D + 1 : ℕ) : ℝ) * (k : ℝ) -
            (1 / 2) * (redClusterMeanCoefficient *
              ((D + 1 : ℕ) : ℝ) * (C : ℝ) * (k : ℝ))) := by
  classical
  let m := D + 1
  have hm : 0 < m := by dsimp [m]; omega
  have htuple := eventually_redExceptional_tuple_measure_le m W C D hm hC hW
  filter_upwards [htuple] with k htuple n₀ hn₀
  let V := ↥(closeTargets W k n₀)
  let tuples : Finset (Fin m → V) :=
    Finset.univ.filter Function.Injective
  let tupleEvent : (Fin m → V) → Set (ℕ → Prop) := fun g ↦
    {ω | ∀ i, RedExceptional W C D k (g i).1 ω}
  have hsubset : {ω | RedClustered W C D k n₀ ω} ⊆
      ⋃ g ∈ tuples, tupleEvent g := by
    intro ω hω
    change RedClustered W C D k n₀ ω at hω
    let exc := (closeTargets W k n₀).filter
      fun n ↦ RedExceptional W C D k n ω
    have hexccard : m ≤ exc.card := by
      change D + 1 ≤ exc.card
      simpa only [RedClustered, exc] using hω
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hexccard
    let enum : Fin m → ℕ := chooseEnumExact S hScard
    have henumclose (i : Fin m) : enum i ∈ closeTargets W k n₀ := by
      have hiS := chooseEnumExact_mem S hScard i
      have hiExc : enum i ∈ exc := by
        change chooseEnumExact S hScard i ∈ exc
        exact hSsub hiS
      exact (Finset.mem_filter.mp hiExc).1
    let g : Fin m → V := fun i ↦ ⟨enum i, henumclose i⟩
    have hginj : Function.Injective g := by
      intro i j hij
      have hval : (g i).1 = (g j).1 := congrArg Subtype.val hij
      change enum i = enum j at hval
      apply chooseEnumExact_injective S hScard
      change enum i = enum j
      exact hval
    have hgtuple : g ∈ tuples := by
      simp [tuples, hginj]
    rw [Set.mem_iUnion]
    refine ⟨g, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨hgtuple, ?_⟩
    intro i
    have hiS := chooseEnumExact_mem S hScard i
    have hiExc : enum i ∈ exc := by
      change chooseEnumExact S hScard i ∈ exc
      exact hSsub hiS
    exact (Finset.mem_filter.mp hiExc).2
  have heach : ∀ g ∈ tuples,
      fairBits.real (tupleEvent g) ≤
        Real.exp ((m : ℝ) * (k : ℝ) -
          (1 / 2) * (redClusterMeanCoefficient *
            (m : ℝ) * (C : ℝ) * (k : ℝ))) := by
    intro g hg
    have hginj : Function.Injective g := (Finset.mem_filter.mp hg).2
    have hmem (i : Fin m) := (g i).property
    exact htuple n₀ hn₀ (fun i ↦ (g i).1)
      (fun i ↦ (mem_closeTargets.mp (hmem i)).1)
      (fun i ↦ (mem_closeTargets.mp (hmem i)).2)
      (fun i j hij ↦ hginj (Subtype.ext hij))
  have htupleCard : tuples.card ≤ (closeTargets W k n₀).card ^ m := by
    calc
      tuples.card ≤ (Finset.univ : Finset (Fin m → V)).card :=
        Finset.card_filter_le _ _
      _ = (closeTargets W k n₀).card ^ m := by
        simp [V, Fintype.card_fun]
  have hbase0 : (0 : ℝ) ≤ Real.exp ((m : ℝ) * (k : ℝ) -
      (1 / 2) * (redClusterMeanCoefficient *
        (m : ℝ) * (C : ℝ) * (k : ℝ))) := (Real.exp_pos _).le
  calc
    fairBits.real {ω | RedClustered W C D k n₀ ω} ≤
        fairBits.real (⋃ g ∈ tuples, tupleEvent g) :=
      measureReal_mono hsubset (measure_lt_top fairBits _).ne
    _ ≤ ∑ g ∈ tuples, fairBits.real (tupleEvent g) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ tuples, Real.exp ((m : ℝ) * (k : ℝ) -
        (1 / 2) * (redClusterMeanCoefficient *
          (m : ℝ) * (C : ℝ) * (k : ℝ))) := Finset.sum_le_sum heach
    _ = (tuples.card : ℝ) * Real.exp ((m : ℝ) * (k : ℝ) -
        (1 / 2) * (redClusterMeanCoefficient *
          (m : ℝ) * (C : ℝ) * (k : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((closeTargets W k n₀).card ^ m : ℕ) : ℝ) *
        Real.exp ((m : ℝ) * (k : ℝ) -
          (1 / 2) * (redClusterMeanCoefficient *
            (m : ℝ) * (C : ℝ) * (k : ℝ))) := by
      gcongr
    _ ≤ (((2 * closeRadius W k + 1) ^ m : ℕ) : ℝ) *
        Real.exp ((m : ℝ) * (k : ℝ) -
          (1 / 2) * (redClusterMeanCoefficient *
            (m : ℝ) * (C : ℝ) * (k : ℝ))) := by
      gcongr
      exact_mod_cast closeTargets_card_le W k n₀
    _ = ((2 * closeRadius W k + 1 : ℕ) : ℝ) ^ (D + 1) *
        Real.exp (((D + 1 : ℕ) : ℝ) * (k : ℝ) -
          (1 / 2) * (redClusterMeanCoefficient *
            ((D + 1 : ℕ) : ℝ) * (C : ℝ) * (k : ℝ))) := by
      dsimp [m]
      push_cast
      rfl

noncomputable def redTargetSupport (W C k n : ℕ) : Finset ℕ :=
  (redTrials W C k n).biUnion fun a ↦ redTrialSupport n a

def redExceptionalEvent (W C D k n : ℕ) : Set (Set ℕ) :=
  {S | RedExceptional W C D k n S}

lemma redExceptionalEvent_supported (W C D k n : ℕ) {S T : Set ℕ}
    (hST : S ∩ (redTargetSupport W C k n : Set ℕ) =
      T ∩ (redTargetSupport W C k n : Set ℕ)) :
    (S ∈ redExceptionalEvent W C D k n ↔
      T ∈ redExceptionalEvent W C D k n) := by
  classical
  have hone (a : RedTrial) (ha : a ∈ redTrials W C k n) :
      S ∩ (redTrialSupport n a : Set ℕ) =
        T ∩ (redTrialSupport n a : Set ℕ) := by
    ext x
    have hx := Set.ext_iff.mp hST x
    simp only [Set.mem_inter_iff, Finset.mem_coe] at hx ⊢
    have hsub (hxa : x ∈ redTrialSupport n a) :
        x ∈ redTargetSupport W C k n := by
      rw [redTargetSupport, Finset.mem_biUnion]
      exact ⟨a, ha, hxa⟩
    constructor
    · rintro ⟨hxS, hxa⟩
      exact ⟨(hx.mp ⟨hxS, hsub hxa⟩).1, hxa⟩
    · rintro ⟨hxT, hxa⟩
      exact ⟨(hx.mpr ⟨hxT, hsub hxa⟩).1, hxa⟩
  have hfilter :
      (redTrials W C k n).attach.filter
          (fun a ↦ bitsToSet S ∈ redTrialEvent n a.1) =
        (redTrials W C k n).attach.filter
          (fun a ↦ bitsToSet T ∈ redTrialEvent n a.1) := by
    have hbitsS : bitsToSet S = S := by ext x; rfl
    have hbitsT : bitsToSet T = T := by ext x; rfl
    ext a
    simp only [Finset.mem_filter]
    apply and_congr Iff.rfl
    rw [hbitsS, hbitsT]
    exact redTrialEvent_supported a.1 (hone a.1 a.property)
  change
    ((redTrials W C k n).attach.filter
      (fun a ↦ bitsToSet S ∈ redTrialEvent n a.1)).card < repairCount D k ↔
    ((redTrials W C k n).attach.filter
      (fun a ↦ bitsToSet T ∈ redTrialEvent n a.1)).card < repairCount D k
  rw [hfilter]

lemma int_abs_cross_le_of_support_inter {q q' n n' : ℕ}
    (hq : 0 < q) (hq' : 0 < q')
    (hqn : q * (q - 1) ≤ n) (hqn' : q' * (q' - 1) ≤ n')
    (hinter : (lengthSupport q n ∩ lengthSupport q' n').Nonempty) :
    |(n : ℤ) * q' - (n' : ℤ) * q| ≤
      (((6 * (q + q') + 1) * q * q' : ℕ) : ℤ) := by
  have hcent := divCenter_le_add_of_support_inter hq hq' hqn hqn' hinter
  have hab := mul_cross_le_add_of_div_le hq hq' hcent.1
  have hba := mul_cross_le_add_of_div_le hq' hq hcent.2
  have habZ : (n : ℤ) * q' ≤ (n' : ℤ) * q +
      (((6 * (q + q') + 1) * q * q' : ℕ) : ℤ) := by
    exact_mod_cast hab
  have hba' : n' * q ≤ n * q' + (6 * (q + q') + 1) * q * q' := by
    convert hba using 1 <;> ring
  have hbaZ : (n' : ℤ) * q ≤ (n : ℤ) * q' +
      (((6 * (q + q') + 1) * q * q' : ℕ) : ℤ) := by
    exact_mod_cast hba'
  rw [abs_le]
  constructor <;> omega

lemma int_abs_mul_nat_mul_le {z : ℤ} {M a b : ℕ}
    (hz : |z| ≤ (M : ℤ)) :
    |z * (a : ℤ) * (b : ℤ)| ≤ ((M * a * b : ℕ) : ℤ) := by
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (a : ℤ)),
    abs_of_nonneg (by positivity : (0 : ℤ) ≤ (b : ℤ))]
  push_cast
  gcongr

/-- Triangle inequality for the three signed integer error terms used below,
with a natural-number bound already cast to `ℤ`. -/
lemma int_abs_sub_add_le_three {x y z : ℤ} {a b c : ℕ}
    (hx : |x| ≤ (a : ℤ)) (hy : |y| ≤ (b : ℤ)) (hz : |z| ≤ (c : ℤ)) :
    |x - y + z| ≤ ((a + b + c : ℕ) : ℤ) := by
  rw [abs_le] at hx hy hz ⊢
  push_cast
  omega

/-- Convert an integer absolute-value estimate on a natural multiple into the
corresponding estimate involving `Int.natAbs`. -/
lemma nat_mul_natAbs_le_of_int_abs_mul_le {n M : ℕ} {z : ℤ}
    (h : |(n : ℤ) * z| ≤ (M : ℤ)) : n * z.natAbs ≤ M := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (n : ℤ)),
    Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- A uniform cubic bound for the error term furnished by
`int_abs_cross_le_of_support_inter`.  Keeping this elementary estimate outside
the collision argument prevents the nonlinear arithmetic normalizer from
having to inspect that argument's many geometric hypotheses. -/
lemma crossError_le_thirteen_cube {a b Q : ℕ}
    (hQ : 0 < Q) (ha : a ≤ Q) (hb : b ≤ Q) :
    (6 * (a + b) + 1) * a * b ≤ 13 * Q ^ 3 := by
  have hab : a + b ≤ 2 * Q := by omega
  have hcoef : 6 * (a + b) + 1 ≤ 13 * Q := by omega
  calc
    (6 * (a + b) + 1) * a * b ≤ (13 * Q) * Q * Q :=
      Nat.mul_le_mul (Nat.mul_le_mul hcoef ha) hb
    _ = 13 * Q ^ 3 := by ring

/-- Three products of a cubic error by two quantities at most `Q` fit in the
slightly roomier bound `64 * Q^5`. -/
lemma three_crossError_terms_le_sixtyfour_pow_five
    {M₁ M₂ M₃ a₁ a₂ b₁ b₂ c₁ c₂ Q : ℕ}
    (hM₁ : M₁ ≤ 13 * Q ^ 3) (hM₂ : M₂ ≤ 13 * Q ^ 3)
    (hM₃ : M₃ ≤ 13 * Q ^ 3)
    (ha₁ : a₁ ≤ Q) (ha₂ : a₂ ≤ Q)
    (hb₁ : b₁ ≤ Q) (hb₂ : b₂ ≤ Q)
    (hc₁ : c₁ ≤ Q) (hc₂ : c₂ ≤ Q) :
    M₁ * a₁ * a₂ + M₂ * b₁ * b₂ + M₃ * c₁ * c₂ ≤
      64 * Q ^ 5 := by
  have h₁ : M₁ * a₁ * a₂ ≤ 13 * Q ^ 5 := by
    calc
      M₁ * a₁ * a₂ ≤ (13 * Q ^ 3) * Q * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul hM₁ ha₁) ha₂
      _ = 13 * Q ^ 5 := by ring
  have h₂ : M₂ * b₁ * b₂ ≤ 13 * Q ^ 5 := by
    calc
      M₂ * b₁ * b₂ ≤ (13 * Q ^ 3) * Q * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul hM₂ hb₁) hb₂
      _ = 13 * Q ^ 5 := by ring
  have h₃ : M₃ * c₁ * c₂ ≤ 13 * Q ^ 5 := by
    calc
      M₃ * c₁ * c₂ ≤ (13 * Q ^ 3) * Q * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul hM₃ hc₁) hc₂
      _ = 13 * Q ^ 5 := by ring
  calc
    M₁ * a₁ * a₂ + M₂ * b₁ * b₂ + M₃ * c₁ * c₂ ≤
        13 * Q ^ 5 + 13 * Q ^ 5 + 13 * Q ^ 5 := by omega
    _ = 39 * Q ^ 5 := by ring
    _ ≤ 64 * Q ^ 5 := Nat.mul_le_mul_right _ (by norm_num)

lemma red_support_disjoint_of_two_blue_collisions
    {W C k n₀ n n' p₁ p₂ r₁ r₂ d d' q s : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 100 ≤ W) (hk : W + 16 ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hp₁ : p₁ ∈ blueLabels W k n₀) (hp₂ : p₂ ∈ blueLabels W k n)
    (hr₁ : r₁ ∈ blueLabels W k n₀) (hr₂ : r₂ ∈ blueLabels W k n')
    (hpne : p₁ ≠ p₂) (hrne : r₁ ≠ r₂) (hpr : p₁ ≠ r₁)
    (hblue : (lengthSupport p₁ n₀ ∩ lengthSupport p₂ n).Nonempty)
    (hblue' : (lengthSupport r₁ n₀ ∩ lengthSupport r₂ n').Nonempty)
    (hd : d ∈ validRedOffsets W C k) (hd' : d' ∈ validRedOffsets W C k)
    (hq : q ∈ redLengths W k n d) (hs : s ∈ redLengths W k n' d') :
    Disjoint (lengthSupport q n) (lengthSupport s n') := by
  by_contra hdisj
  have hred : (lengthSupport q n ∩ lengthSupport s n').Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp hdisj
  let E := (2 * C + 1) * k + 2 * W + 14
  let Q := 2 ^ E
  have hW8 : 8 * C + 100 ≤ W := by nlinarith
  have hdv := mem_validRedOffsets.mp hd
  have hdv' := mem_validRedOffsets.mp hd'
  have hqQ : q < Q := redLength_lt_globalEnvelope (by omega) hdv.1 hdv.2.1 hn hq
  have hsQ : s < Q := redLength_lt_globalEnvelope (by omega) hdv'.1 hdv'.2.1 hn' hs
  have hq0 : 0 < q := by
    have hscale := redLengthScale_pos (W := W) (k := k) (n := n) (d := d)
      (by omega) (by omega) hdv.2.1 hn
    have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  have hs0 : 0 < s := by
    have hscale := redLengthScale_pos (W := W) (k := k) (n := n') (d := d')
      (by omega) (by omega) hdv'.2.1 hn'
    have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    omega
  have hp₁n := blueLabel_sq_le_target (by omega) hk hn₀ hp₁
  have hp₂n := blueLabel_sq_le_target (by omega) hk hn hp₂
  have hr₁n := blueLabel_sq_le_target (by omega) hk hn₀ hr₁
  have hr₂n := blueLabel_sq_le_target (by omega) hk hn' hr₂
  have hqn := redLength_sq_le_target hC hW8 hk hn hd hq
  have hsn := redLength_sq_le_target hC hW8 hk hn' hd' hs
  have hp₁pos : 0 < p₁ := (mem_primesBetween.mp hp₁).2.2.pos
  have hp₂pos : 0 < p₂ := (mem_primesBetween.mp hp₂).2.2.pos
  have hr₁pos : 0 < r₁ := (mem_primesBetween.mp hr₁).2.2.pos
  have hr₂pos : 0 < r₂ := (mem_primesBetween.mp hr₂).2.2.pos
  have hblueBound := int_abs_cross_le_of_support_inter
    hp₁pos hp₂pos hp₁n hp₂n hblue
  have hblueBound' := int_abs_cross_le_of_support_inter
    hr₁pos hr₂pos hr₁n hr₂n hblue'
  have hredBound := int_abs_cross_le_of_support_inter hq0 hs0 hqn hsn hred
  let A : ℤ := (n₀ : ℤ) * p₂ - (n : ℤ) * p₁
  let B : ℤ := (n₀ : ℤ) * r₂ - (n' : ℤ) * r₁
  let D : ℤ := (n : ℤ) * s - (n' : ℤ) * q
  let MA : ℕ := (6 * (p₁ + p₂) + 1) * p₁ * p₂
  let MB : ℕ := (6 * (r₁ + r₂) + 1) * r₁ * r₂
  let MD : ℕ := (6 * (q + s) + 1) * q * s
  change |A| ≤ (MA : ℤ) at hblueBound
  change |B| ≤ (MB : ℤ) at hblueBound'
  change |D| ≤ (MD : ℤ) at hredBound
  have hBQ : 2 ^ (k + W + 5) ≤ Q := by
    dsimp [Q]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    dsimp [E]
    nlinarith
  have hp₁Q : p₁ ≤ Q := (blueLabel_le_envelope (by omega) hk hn₀ hp₁).trans hBQ
  have hp₂Q : p₂ ≤ Q := (blueLabel_le_envelope (by omega) hk hn hp₂).trans hBQ
  have hr₁Q : r₁ ≤ Q := (blueLabel_le_envelope (by omega) hk hn₀ hr₁).trans hBQ
  have hr₂Q : r₂ ≤ Q := (blueLabel_le_envelope (by omega) hk hn' hr₂).trans hBQ
  have hQpos : 0 < Q := by positivity
  have hMA : MA ≤ 13 * Q ^ 3 := by
    exact crossError_le_thirteen_cube hQpos hp₁Q hp₂Q
  have hMB : MB ≤ 13 * Q ^ 3 := by
    exact crossError_le_thirteen_cube hQpos hr₁Q hr₂Q
  have hMD : MD ≤ 13 * Q ^ 3 := by
    exact crossError_le_thirteen_cube hQpos hqQ.le hsQ.le
  let Z : ℤ := p₂ * s * r₁ - r₂ * q * p₁
  have hidentity : (n₀ : ℤ) * Z =
      A * s * r₁ - B * q * p₁ + D * p₁ * r₁ := by
    dsimp [Z, A, B, D]
    push_cast
    ring
  have hAterm := int_abs_mul_nat_mul_le (a := s) (b := r₁) hblueBound
  have hBterm := int_abs_mul_nat_mul_le (a := q) (b := p₁) hblueBound'
  have hDterm := int_abs_mul_nat_mul_le (a := p₁) (b := r₁) hredBound
  have hsumAbs :
      |A * (s : ℤ) * r₁ - B * (q : ℤ) * p₁ + D * (p₁ : ℤ) * r₁| ≤
        ((MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ : ℕ) : ℤ) := by
    exact int_abs_sub_add_le_three hAterm hBterm hDterm
  have hInt : |(n₀ : ℤ) * Z| ≤
      ((MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ : ℕ) : ℤ) := by
    rw [hidentity]
    exact hsumAbs
  have hNat : n₀ * Z.natAbs ≤
      MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ := by
    exact nat_mul_natAbs_le_of_int_abs_mul_le hInt
  have hterms : MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ ≤
      64 * Q ^ 5 := by
    exact three_crossError_terms_le_sixtyfour_pow_five hMA hMB hMD
      hsQ.le hr₁Q hqQ.le hp₁Q hp₁Q hr₁Q
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 5 * E + 6 < (W + 1) * k := by
    dsimp [E]
    nlinarith only [hWmul, hkW, hW]
  have hpowEq : 64 * Q ^ 5 = 2 ^ (5 * E + 6) := by
    dsimp [Q]
    rw [show 64 = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add]
    rw [show 6 + E * 5 = 5 * E + 6 by ring]
  have hnLarge : 64 * Q ^ 5 < n₀ := by
    rw [hpowEq]
    calc
      2 ^ (5 * E + 6) < 2 ^ ((W + 1) * k) := Nat.pow_lt_pow_right (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n₀ := (mem_targetBlock.mp hn₀).1
  have hZzero : Z = 0 := by
    have habs : Z.natAbs = 0 := by
      by_contra hz
      have hzpos : 0 < Z.natAbs := Nat.pos_of_ne_zero hz
      have : n₀ ≤ n₀ * Z.natAbs := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left n₀ hzpos
      omega
    exact Int.natAbs_eq_zero.mp habs
  have heqInt : (p₂ : ℤ) * s * r₁ = (r₂ : ℤ) * q * p₁ := by
    dsimp [Z] at hZzero
    omega
  have heq : p₂ * s * r₁ = r₂ * q * p₁ := by exact_mod_cast heqInt
  have hp₁prime := (mem_primesBetween.mp hp₁).2.2
  have hp₂prime := (mem_primesBetween.mp hp₂).2.2
  have hr₁prime := (mem_primesBetween.mp hr₁).2.2
  have hp₁scale : p₁ ∈ scaleBluePrimes W k :=
    blueLabels_subset_scaleBluePrimes (by omega) hk hn₀ hp₁
  have hp₁notS : ¬p₁ ∣ s := (Finset.mem_filter.mp hs).2 p₁ hp₁scale
  have hdvdRight : p₁ ∣ r₂ * q * p₁ := by simp
  have hdvdLeft : p₁ ∣ p₂ * s * r₁ := by rw [heq]; exact hdvdRight
  rcases hp₁prime.dvd_or_dvd hdvdLeft with hleft | hright
  · rcases hp₁prime.dvd_or_dvd hleft with hp₂dvd | hsdvd
    · exact hpne ((Nat.prime_dvd_prime_iff_eq hp₁prime hp₂prime).mp hp₂dvd)
    · exact hp₁notS hsdvd
  · exact hpr ((Nat.prime_dvd_prime_iff_eq hp₁prime hr₁prime).mp hright)

/-- The cross-collision lemma for the full family of red subchannels.  This is
the form used in the alteration step. -/
lemma redSub_support_disjoint_of_two_blue_collisions
    {W C k n₀ n n' p₁ p₂ r₁ r₂ d e d' e' q s : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hp₁ : p₁ ∈ blueLabels W k n₀) (hp₂ : p₂ ∈ blueLabels W k n)
    (hr₁ : r₁ ∈ blueLabels W k n₀) (hr₂ : r₂ ∈ blueLabels W k n')
    (hpne : p₁ ≠ p₂) (hrne : r₁ ≠ r₂) (hpr : p₁ ≠ r₁)
    (hblue : (lengthSupport p₁ n₀ ∩ lengthSupport p₂ n).Nonempty)
    (hblue' : (lengthSupport r₁ n₀ ∩ lengthSupport r₂ n').Nonempty)
    (hde : (d, e) ∈ validRedSubchannels W C k)
    (hde' : (d', e') ∈ validRedSubchannels W C k)
    (hq : q ∈ redSubLengths W k n d e)
    (hs : s ∈ redSubLengths W k n' d' e') :
    Disjoint (lengthSupport q n) (lengthSupport s n') := by
  by_contra hdisj
  have hred : (lengthSupport q n ∩ lengthSupport s n').Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp hdisj
  let E := (2 * C + 1) * k + 3 * W + 20
  let Q := 2 ^ E
  have hqQ : q < Q := redSubLength_lt_globalEnvelope hW hde hn hq
  have hsQ : s < Q := redSubLength_lt_globalEnvelope hW hde' hn' hs
  have hq0 : 0 < q := by
    have hlo := (mem_redSubLengths.mp hq).1
    rcases mem_validRedSubchannels.mp hde with ⟨_, _, hdle, heSafe, _⟩
    have heFive : 5 * e + 5 ≤ W :=
      (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * e)).trans heSafe
    have hP := redSubLengthScale_pos heFive (by omega) hdle hn
    exact hP.trans_le hlo
  have hs0 : 0 < s := by
    have hlo := (mem_redSubLengths.mp hs).1
    rcases mem_validRedSubchannels.mp hde' with ⟨_, _, hdle, heSafe, _⟩
    have heFive : 5 * e' + 5 ≤ W :=
      (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * e')).trans heSafe
    have hP := redSubLengthScale_pos heFive (by omega) hdle hn'
    exact hP.trans_le hlo
  have hkBlue : W + 16 ≤ k := by omega
  have hp₁n := blueLabel_sq_le_target (by omega) hkBlue hn₀ hp₁
  have hp₂n := blueLabel_sq_le_target (by omega) hkBlue hn hp₂
  have hr₁n := blueLabel_sq_le_target (by omega) hkBlue hn₀ hr₁
  have hr₂n := blueLabel_sq_le_target (by omega) hkBlue hn' hr₂
  have hqn := redSubLength_sq_le_target hC hW hk hn hde hq
  have hsn := redSubLength_sq_le_target hC hW hk hn' hde' hs
  have hp₁pos : 0 < p₁ := (mem_primesBetween.mp hp₁).2.2.pos
  have hp₂pos : 0 < p₂ := (mem_primesBetween.mp hp₂).2.2.pos
  have hr₁pos : 0 < r₁ := (mem_primesBetween.mp hr₁).2.2.pos
  have hr₂pos : 0 < r₂ := (mem_primesBetween.mp hr₂).2.2.pos
  have hblueBound := int_abs_cross_le_of_support_inter
    hp₁pos hp₂pos hp₁n hp₂n hblue
  have hblueBound' := int_abs_cross_le_of_support_inter
    hr₁pos hr₂pos hr₁n hr₂n hblue'
  have hredBound := int_abs_cross_le_of_support_inter hq0 hs0 hqn hsn hred
  let A : ℤ := (n₀ : ℤ) * p₂ - (n : ℤ) * p₁
  let B : ℤ := (n₀ : ℤ) * r₂ - (n' : ℤ) * r₁
  let D : ℤ := (n : ℤ) * s - (n' : ℤ) * q
  let MA : ℕ := (6 * (p₁ + p₂) + 1) * p₁ * p₂
  let MB : ℕ := (6 * (r₁ + r₂) + 1) * r₁ * r₂
  let MD : ℕ := (6 * (q + s) + 1) * q * s
  change |A| ≤ (MA : ℤ) at hblueBound
  change |B| ≤ (MB : ℤ) at hblueBound'
  change |D| ≤ (MD : ℤ) at hredBound
  have hBQ : 2 ^ (k + W + 5) ≤ Q := by
    dsimp [Q]
    apply Nat.pow_le_pow_right (n := 2) (by omega)
    dsimp [E]
    nlinarith
  have hp₁Q : p₁ ≤ Q :=
    (blueLabel_le_envelope (by omega) hkBlue hn₀ hp₁).trans hBQ
  have hp₂Q : p₂ ≤ Q :=
    (blueLabel_le_envelope (by omega) hkBlue hn hp₂).trans hBQ
  have hr₁Q : r₁ ≤ Q :=
    (blueLabel_le_envelope (by omega) hkBlue hn₀ hr₁).trans hBQ
  have hr₂Q : r₂ ≤ Q :=
    (blueLabel_le_envelope (by omega) hkBlue hn' hr₂).trans hBQ
  have hQpos : 0 < Q := by positivity
  have hMA : MA ≤ 13 * Q ^ 3 :=
    crossError_le_thirteen_cube hQpos hp₁Q hp₂Q
  have hMB : MB ≤ 13 * Q ^ 3 :=
    crossError_le_thirteen_cube hQpos hr₁Q hr₂Q
  have hMD : MD ≤ 13 * Q ^ 3 :=
    crossError_le_thirteen_cube hQpos hqQ.le hsQ.le
  let Z : ℤ := p₂ * s * r₁ - r₂ * q * p₁
  have hidentity : (n₀ : ℤ) * Z =
      A * s * r₁ - B * q * p₁ + D * p₁ * r₁ := by
    dsimp [Z, A, B, D]
    push_cast
    ring
  have hAterm := int_abs_mul_nat_mul_le (a := s) (b := r₁) hblueBound
  have hBterm := int_abs_mul_nat_mul_le (a := q) (b := p₁) hblueBound'
  have hDterm := int_abs_mul_nat_mul_le (a := p₁) (b := r₁) hredBound
  have hsumAbs :
      |A * (s : ℤ) * r₁ - B * (q : ℤ) * p₁ + D * (p₁ : ℤ) * r₁| ≤
        ((MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ : ℕ) : ℤ) :=
    int_abs_sub_add_le_three hAterm hBterm hDterm
  have hInt : |(n₀ : ℤ) * Z| ≤
      ((MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ : ℕ) : ℤ) := by
    rw [hidentity]
    exact hsumAbs
  have hNat : n₀ * Z.natAbs ≤
      MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ :=
    nat_mul_natAbs_le_of_int_abs_mul_le hInt
  have hterms : MA * s * r₁ + MB * q * p₁ + MD * p₁ * r₁ ≤
      64 * Q ^ 5 :=
    three_crossError_terms_le_sixtyfour_pow_five hMA hMB hMD
      hsQ.le hr₁Q hqQ.le hp₁Q hp₁Q hr₁Q
  have hWmul := Nat.mul_le_mul_right k hW
  have hkW : W ≤ k := by omega
  have hExp : 5 * E + 6 < (W + 1) * k := by
    dsimp [E]
    nlinarith only [hWmul, hkW, hW]
  have hpowEq : 64 * Q ^ 5 = 2 ^ (5 * E + 6) := by
    dsimp [Q]
    rw [show 64 = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add]
    rw [show 6 + E * 5 = 5 * E + 6 by ring]
  have hnLarge : 64 * Q ^ 5 < n₀ := by
    rw [hpowEq]
    calc
      2 ^ (5 * E + 6) < 2 ^ ((W + 1) * k) :=
        Nat.pow_lt_pow_right (by omega) hExp
      _ = (targetBase W) ^ k := by simp [targetBase, pow_mul]
      _ ≤ n₀ := (mem_targetBlock.mp hn₀).1
  have hZzero : Z = 0 := by
    have habs : Z.natAbs = 0 := by
      by_contra hz
      have hzpos : 0 < Z.natAbs := Nat.pos_of_ne_zero hz
      have : n₀ ≤ n₀ * Z.natAbs := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left n₀ hzpos
      omega
    exact Int.natAbs_eq_zero.mp habs
  have heqInt : (p₂ : ℤ) * s * r₁ = (r₂ : ℤ) * q * p₁ := by
    dsimp [Z] at hZzero
    omega
  have heq : p₂ * s * r₁ = r₂ * q * p₁ := by exact_mod_cast heqInt
  have hp₁prime := (mem_primesBetween.mp hp₁).2.2
  have hp₂prime := (mem_primesBetween.mp hp₂).2.2
  have hr₁prime := (mem_primesBetween.mp hr₁).2.2
  have hp₁scale : p₁ ∈ scaleBluePrimes W k :=
    blueLabels_subset_scaleBluePrimes (by omega) hkBlue hn₀ hp₁
  have hp₁notS : ¬p₁ ∣ s := (mem_redSubLengths.mp hs).2.2 p₁ hp₁scale
  have hdvdRight : p₁ ∣ r₂ * q * p₁ := by simp
  have hdvdLeft : p₁ ∣ p₂ * s * r₁ := by rw [heq]; exact hdvdRight
  rcases hp₁prime.dvd_or_dvd hdvdLeft with hleft | hright
  · rcases hp₁prime.dvd_or_dvd hleft with hp₂dvd | hsdvd
    · exact hpne ((Nat.prime_dvd_prime_iff_eq hp₁prime hp₂prime).mp hp₂dvd)
    · exact hp₁notS hsdvd
  · exact hpr ((Nat.prime_dvd_prime_iff_eq hp₁prime hr₁prime).mp hright)

lemma redTargetSupport_disjoint_of_two_blue_collisions
    {W C k n₀ n n' p₁ p₂ r₁ r₂ : ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn₀ : n₀ ∈ targetBlock W k) (hn : n ∈ targetBlock W k)
    (hn' : n' ∈ targetBlock W k)
    (hp₁ : p₁ ∈ blueLabels W k n₀) (hp₂ : p₂ ∈ blueLabels W k n)
    (hr₁ : r₁ ∈ blueLabels W k n₀) (hr₂ : r₂ ∈ blueLabels W k n')
    (hpne : p₁ ≠ p₂) (hrne : r₁ ≠ r₂) (hpr : p₁ ≠ r₁)
    (hblue : (lengthSupport p₁ n₀ ∩ lengthSupport p₂ n).Nonempty)
    (hblue' : (lengthSupport r₁ n₀ ∩ lengthSupport r₂ n').Nonempty) :
    Disjoint (redTargetSupport W C k n) (redTargetSupport W C k n') := by
  classical
  rw [Finset.disjoint_left]
  intro x hxn hxn'
  rw [redTargetSupport, Finset.mem_biUnion] at hxn hxn'
  obtain ⟨a, ha, hxa⟩ := hxn
  obtain ⟨b, hb, hxb⟩ := hxn'
  have ha' := mem_redTrials.mp ha
  have hb' := mem_redTrials.mp hb
  have hd := redSub_support_disjoint_of_two_blue_collisions hC hW hk hn₀ hn hn'
    hp₁ hp₂ hr₁ hr₂ hpne hrne hpr hblue hblue'
    ha'.1 hb'.1 ha'.2 hb'.2
  exact (Finset.disjoint_left.mp hd) hxa hxb

noncomputable def blueCollisionTargets (W k n₀ p p₂ : ℕ) : Finset ℕ := by
  classical
  exact (targetBlock W k).filter fun n ↦
    p₂ ∈ blueLabels W k n ∧ ¬Close W k n₀ n ∧
      (lengthSupport p n₀ ∩ lengthSupport p₂ n).Nonempty

@[simp] lemma mem_blueCollisionTargets {W k n₀ p p₂ n : ℕ} :
    n ∈ blueCollisionTargets W k n₀ p p₂ ↔
      n ∈ targetBlock W k ∧ p₂ ∈ blueLabels W k n ∧
        ¬Close W k n₀ n ∧
          (lengthSupport p n₀ ∩ lengthSupport p₂ n).Nonempty := by
  classical
  simp [blueCollisionTargets, and_assoc]

abbrev BlueCollisionData := Sigma fun _p : ℕ ↦ Sigma fun _p₂ : ℕ ↦ ℕ

noncomputable def blueCollisionData (W k n₀ : ℕ) : Finset BlueCollisionData :=
  (blueLabels W k n₀).sigma fun p ↦
    (scaleBluePrimes W k).sigma fun p₂ ↦
      blueCollisionTargets W k n₀ p p₂

@[simp] lemma mem_blueCollisionData {W k n₀ : ℕ} {a : BlueCollisionData} :
    a ∈ blueCollisionData W k n₀ ↔
      a.1 ∈ blueLabels W k n₀ ∧ a.2.1 ∈ scaleBluePrimes W k ∧
        a.2.2 ∈ blueCollisionTargets W k n₀ a.1 a.2.1 := by
  simp [blueCollisionData]

lemma scaleBluePrimes_card_le_envelope (W k : ℕ) :
    (scaleBluePrimes W k).card ≤ 2 ^ (k + W + 5) + 1 := by
  classical
  have hsub : scaleBluePrimes W k ⊆ Finset.range (2 ^ (k + W + 5) + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have := (mem_primesBetween.mp hp).2.1
    omega
  exact (Finset.card_le_card hsub).trans_eq (by simp)

lemma blueLabels_card_le_envelope {W k n : ℕ} (hW : 2 ≤ W)
    (hk : W + 16 ≤ k) (hn : n ∈ targetBlock W k) :
    (blueLabels W k n).card ≤ 2 ^ (k + W + 5) + 1 := by
  exact (Finset.card_le_card (blueLabels_subset_scaleBluePrimes hW hk hn)).trans
    (scaleBluePrimes_card_le_envelope W k)

lemma blueCollisionTargets_card_le {W k n₀ p p₂ : ℕ}
    (hW : 10 ≤ W) (hk : W + 16 ≤ k) (hn₀ : n₀ ∈ targetBlock W k)
    (hp : p ∈ blueLabels W k n₀) :
    (blueCollisionTargets W k n₀ p p₂).card ≤
      26 * (2 ^ (k + W + 5)) ^ 3 + 1 := by
  classical
  let B := 2 ^ (k + W + 5)
  let M := 13 * B ^ 3
  let s := blueCollisionTargets W k n₀ p p₂
  let I := Finset.Icc (n₀ * p₂ - M) (n₀ * p₂ + M)
  have hp0 : 0 < p := (mem_primesBetween.mp hp).2.2.pos
  have hpB : p ≤ B := blueLabel_le_envelope (by omega) hk hn₀ hp
  have himage : s.image (fun n ↦ n * p) ⊆ I := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    have hn' := mem_blueCollisionTargets.mp hn
    have hp₂B : p₂ ≤ B :=
      blueLabel_le_envelope (by omega) hk hn'.1 hn'.2.1
    have hp₂0 : 0 < p₂ := (mem_primesBetween.mp hn'.2.1).2.2.pos
    have hpn := blueLabel_sq_le_target hW hk hn₀ hp
    have hp₂n := blueLabel_sq_le_target hW hk hn'.1 hn'.2.1
    have herr := int_abs_cross_le_of_support_inter hp0 hp₂0 hpn hp₂n hn'.2.2.2
    have hcoef := crossError_le_thirteen_cube (by dsimp [B]; positivity) hpB hp₂B
    have herr' : |(n₀ : ℤ) * p₂ - (n : ℤ) * p| ≤ (M : ℤ) := by
      exact herr.trans (by exact_mod_cast hcoef)
    rw [abs_le] at herr'
    change n * p ∈ Finset.Icc (n₀ * p₂ - M) (n₀ * p₂ + M)
    rw [Finset.mem_Icc]
    have hu : n * p ≤ n₀ * p₂ + M := by
      have huZ : (n : ℤ) * p ≤ (n₀ : ℤ) * p₂ + M := by omega
      exact_mod_cast huZ
    have hl : n₀ * p₂ ≤ n * p + M := by
      have : -((M : ℤ)) ≤ (n₀ : ℤ) * p₂ - (n : ℤ) * p := herr'.1
      push_cast at this
      omega
    omega
  have himageCard : (s.image (fun n ↦ n * p)).card = s.card :=
    Finset.card_image_of_injective s (fun _ _ h ↦ Nat.mul_right_cancel hp0 h)
  have hIcard : I.card ≤ 2 * M + 1 := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  calc
    s.card = (s.image (fun n ↦ n * p)).card := himageCard.symm
    _ ≤ I.card := Finset.card_le_card himage
    _ ≤ 2 * M + 1 := hIcard
    _ = 26 * B ^ 3 + 1 := by dsimp [M]; ring
    _ = 26 * (2 ^ (k + W + 5)) ^ 3 + 1 := rfl

lemma blueCollisionData_card_le {W k n₀ : ℕ}
    (hW : 10 ≤ W) (hk : W + 16 ≤ k) (hn₀ : n₀ ∈ targetBlock W k) :
    (blueCollisionData W k n₀).card ≤
      128 * (2 ^ (k + W + 5)) ^ 5 := by
  classical
  let B := 2 ^ (k + W + 5)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hblue := blueLabels_card_le_envelope (by omega) hk hn₀
  have hscale := scaleBluePrimes_card_le_envelope W k
  have hfiber (p : ℕ) (hp : p ∈ blueLabels W k n₀) :
      ((scaleBluePrimes W k).sigma fun p₂ ↦
        blueCollisionTargets W k n₀ p p₂).card ≤
          (B + 1) * (26 * B ^ 3 + 1) := by
    rw [Finset.card_sigma]
    calc
      (∑ p₂ ∈ scaleBluePrimes W k,
          (blueCollisionTargets W k n₀ p p₂).card) ≤
          ∑ _p₂ ∈ scaleBluePrimes W k, (26 * B ^ 3 + 1) := by
        apply Finset.sum_le_sum
        intro p₂ hp₂
        simpa only [B] using blueCollisionTargets_card_le hW hk hn₀ hp
      _ = (scaleBluePrimes W k).card * (26 * B ^ 3 + 1) := by simp
      _ ≤ (B + 1) * (26 * B ^ 3 + 1) := by gcongr
  rw [blueCollisionData, Finset.card_sigma]
  calc
    (∑ p ∈ blueLabels W k n₀,
        ((scaleBluePrimes W k).sigma fun p₂ ↦
          blueCollisionTargets W k n₀ p p₂).card) ≤
        ∑ _p ∈ blueLabels W k n₀, ((B + 1) * (26 * B ^ 3 + 1)) := by
      exact Finset.sum_le_sum hfiber
    _ = (blueLabels W k n₀).card * ((B + 1) * (26 * B ^ 3 + 1)) := by simp
    _ ≤ (B + 1) * ((B + 1) * (26 * B ^ 3 + 1)) := by gcongr
    _ ≤ (2 * B) * ((2 * B) * (32 * B ^ 3)) := by
      have hBone : B + 1 ≤ 2 * B := by omega
      have hBcubePos : 0 < B ^ 3 := pow_pos hBpos _
      have hBcube : 1 ≤ B ^ 3 := hBcubePos
      have hthird : 26 * B ^ 3 + 1 ≤ 32 * B ^ 3 := by omega
      exact Nat.mul_le_mul hBone (Nat.mul_le_mul hBone hthird)
    _ = 128 * B ^ 5 := by ring
    _ = 128 * (2 ^ (k + W + 5)) ^ 5 := rfl

lemma blueCollision_current_ne_partner {W k n₀ p p₂ n : ℕ}
    (hW : 10 ≤ W) (hk : W + 16 ≤ k) (hn₀ : n₀ ∈ targetBlock W k)
    (hp : p ∈ blueLabels W k n₀)
    (hn : n ∈ blueCollisionTargets W k n₀ p p₂) : p ≠ p₂ := by
  intro heq
  subst p₂
  have hn' := mem_blueCollisionTargets.mp hn
  have hd := blue_support_disjoint_of_not_Close_same hW hk hn₀ hn'.1 hn'.2.2.1
    hp hn'.2.1
  exact (Finset.disjoint_iff_inter_eq_empty.mp hd ▸ hn'.2.2.2).ne_empty rfl

noncomputable def blueBadConfigurations (W k n₀ : ℕ) :
    Finset (Fin k → ↥(blueCollisionData W k n₀)) := by
  classical
  exact Finset.univ.filter fun g ↦
    Function.Injective (fun i ↦ (g i).1.1)

noncomputable def BlueBad (W C D k n₀ : ℕ) (ω : ℕ → Prop) : Prop :=
  ∃ g ∈ blueBadConfigurations W k n₀,
    ∀ i, RedExceptional W C D k (g i).1.2.2 ω

lemma eventually_blueBad_measure_le (W C D : ℕ)
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n₀ ∈ targetBlock W k,
      fairBits.real {ω | BlueBad W C D k n₀ ω} ≤
        (((128 * (2 ^ (k + W + 5)) ^ 5 : ℕ) : ℝ) ^ k) *
          (Real.exp ((k : ℝ) -
            (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ)))) ^ k := by
  have hred := eventually_redExceptional_measure_le W C D hC hW
  filter_upwards [hred, eventually_ge_atTop (2 * W)] with k hred hk n₀ hn₀
  classical
  let data := blueCollisionData W k n₀
  let configs := blueBadConfigurations W k n₀
  let ρ := Real.exp ((k : ℝ) -
    (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ)))
  let configEvent : (Fin k → ↥data) → Set (ℕ → Prop) := fun g ↦
    {ω | ∀ i, RedExceptional W C D k (g i).1.2.2 ω}
  have hkBlue : W + 16 ≤ k := by omega
  have heach : ∀ g ∈ configs, fairBits.real (configEvent g) ≤ ρ ^ k := by
    intro g hg
    have hcurInj : Function.Injective (fun i ↦ (g i).1.1) := by
      exact (Finset.mem_filter.mp hg).2
    let u : Fin k → Finset ℕ := fun i ↦
      redTargetSupport W C k (g i).1.2.2
    let E : Fin k → Set (Set ℕ) := fun i ↦
      redExceptionalEvent W C D k (g i).1.2.2
    have hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (u i) (u j) := by
      intro i j hij
      have hi := mem_blueCollisionData.mp (g i).property
      have hj := mem_blueCollisionData.mp (g j).property
      have hiw := mem_blueCollisionTargets.mp hi.2.2
      have hjw := mem_blueCollisionTargets.mp hj.2.2
      have hpne := blueCollision_current_ne_partner (by omega) hkBlue hn₀ hi.1 hi.2.2
      have hrne := blueCollision_current_ne_partner (by omega) hkBlue hn₀ hj.1 hj.2.2
      have hpr : (g i).1.1 ≠ (g j).1.1 := fun h ↦ hij (hcurInj h)
      exact redTargetSupport_disjoint_of_two_blue_collisions hC hW hk hn₀
        hiw.1 hjw.1 hi.1 hiw.2.1 hj.1 hjw.2.1 hpne hrne hpr
        hiw.2.2.2 hjw.2.2.2
    have hsupp : ∀ i : Fin k, ∀ {S T : Set ℕ},
        S ∩ (u i : Set ℕ) = T ∩ (u i : Set ℕ) → (S ∈ E i ↔ T ∈ E i) := by
      intro i S T hST
      exact redExceptionalEvent_supported W C D k (g i).1.2.2 hST
    have hprod := fairBits_measureReal_biInter_supported_eq_prod u E Finset.univ
      hdisj hsupp
    have hbits (ω : ℕ → Prop) : bitsToSet ω = (ω : Set ℕ) := by
      ext x
      rfl
    have hset : configEvent g =
        ⋂ i ∈ (Finset.univ : Finset (Fin k)), bitsToSet ⁻¹' E i := by
      ext ω
      simp only [configEvent, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ,
        forall_const, Set.mem_preimage]
      constructor
      · intro h i
        change RedExceptional W C D k (g i).1.2.2 (bitsToSet ω)
        rw [hbits]
        exact h i
      · intro h i
        have hi := h i
        change RedExceptional W C D k (g i).1.2.2 (bitsToSet ω) at hi
        rw [hbits] at hi
        exact hi
    rw [hset, hprod]
    calc
      (∏ i : Fin k, fairBits.real (bitsToSet ⁻¹' E i)) ≤
          ∏ _i : Fin k, ρ := by
        apply Finset.prod_le_prod (fun _ _ ↦ measureReal_nonneg)
        intro i hi
        have hmem := (mem_blueCollisionTargets.mp
          (mem_blueCollisionData.mp (g i).property).2.2).1
        have hr := hred (g i).1.2.2 hmem
        have hpre : bitsToSet ⁻¹' E i =
            {ω | RedExceptional W C D k (g i).1.2.2 ω} := by
          ext ω
          change RedExceptional W C D k (g i).1.2.2 (bitsToSet ω) ↔
            RedExceptional W C D k (g i).1.2.2 ω
          rw [hbits]
        rw [hpre]
        exact hr
      _ = ρ ^ k := by simp
  have hconfigsCard : configs.card ≤
      (128 * (2 ^ (k + W + 5)) ^ 5) ^ k := by
    have hdata := blueCollisionData_card_le (by omega) hkBlue hn₀
    calc
      configs.card ≤ (Finset.univ : Finset (Fin k → ↥data)).card :=
        Finset.card_filter_le _ _
      _ = data.card ^ k := by simp [Fintype.card_fun]
      _ ≤ (128 * (2 ^ (k + W + 5)) ^ 5) ^ k :=
        Nat.pow_le_pow_left hdata k
  have hsubset : {ω | BlueBad W C D k n₀ ω} ⊆
      ⋃ g ∈ configs, configEvent g := by
    intro ω hω
    change BlueBad W C D k n₀ ω at hω
    rcases hω with ⟨g, hg, hgi⟩
    rw [Set.mem_iUnion]
    refine ⟨g, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hg, hgi⟩
  calc
    fairBits.real {ω | BlueBad W C D k n₀ ω} ≤
        fairBits.real (⋃ g ∈ configs, configEvent g) :=
      measureReal_mono hsubset (measure_lt_top fairBits _).ne
    _ ≤ ∑ g ∈ configs, fairBits.real (configEvent g) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ configs, ρ ^ k := Finset.sum_le_sum heach
    _ = (configs.card : ℝ) * ρ ^ k := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((128 * (2 ^ (k + W + 5)) ^ 5 : ℕ) : ℝ) ^ k) * ρ ^ k := by
      gcongr
      exact_mod_cast hconfigsCard
    _ = (((128 * (2 ^ (k + W + 5)) ^ 5 : ℕ) : ℝ) ^ k) *
          (Real.exp ((k : ℝ) -
            (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ)))) ^ k := rfl

noncomputable def ScaleBad (W C D k : ℕ) (ω : ℕ → Prop) : Prop :=
  ∃ n ∈ targetBlock W k,
    RedClustered W C D k n ω ∨ BlueBad W C D k n ω

lemma targetBlock_card_le (W k : ℕ) :
    (targetBlock W k).card ≤ (targetBase W) ^ (k + 1) := by
  rw [targetBlock, Nat.card_Ico]
  exact Nat.sub_le _ _

noncomputable def clusterScaleTerm (W C D k : ℕ) : ℝ :=
  ((2 * closeRadius W k + 1 : ℕ) : ℝ) ^ (D + 1) *
    Real.exp (((D + 1 : ℕ) : ℝ) * (k : ℝ) -
      (1 / 2) * (redClusterMeanCoefficient *
        ((D + 1 : ℕ) : ℝ) * (C : ℝ) * (k : ℝ)))

noncomputable def blueScaleTerm (W C k : ℕ) : ℝ :=
  (((128 * (2 ^ (k + W + 5)) ^ 5 : ℕ) : ℝ) ^ k) *
    (Real.exp ((k : ℝ) -
      (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ)))) ^ k

noncomputable def scaleRawBound (W C D k : ℕ) : ℝ :=
  (((targetBase W) ^ (k + 1) : ℕ) : ℝ) *
    (clusterScaleTerm W C D k + blueScaleTerm W C k)

lemma clusterScaleTerm_nonneg (W C D k : ℕ) :
    0 ≤ clusterScaleTerm W C D k := by
  unfold clusterScaleTerm
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le

lemma blueScaleTerm_nonneg (W C k : ℕ) :
    0 ≤ blueScaleTerm W C k := by
  unfold blueScaleTerm
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (pow_nonneg (Real.exp_pos _).le _)

lemma eventually_scaleBad_measure_le_raw (W C D : ℕ)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W) :
    ∀ᶠ k : ℕ in atTop,
      fairBits.real {ω | ScaleBad W C D k ω} ≤ scaleRawBound W C D k := by
  have hcluster := eventually_redClustered_measure_le W C D hC hW
  have hblue := eventually_blueBad_measure_le W C D (by omega) hW
  filter_upwards [hcluster, hblue] with k hcluster hblue
  classical
  let badAt : ℕ → Set (ℕ → Prop) := fun n ↦
    {ω | RedClustered W C D k n ω ∨ BlueBad W C D k n ω}
  have hsubset : {ω | ScaleBad W C D k ω} ⊆
      ⋃ n ∈ targetBlock W k, badAt n := by
    intro ω hω
    change ScaleBad W C D k ω at hω
    rcases hω with ⟨n, hn, hbad⟩
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hn, hbad⟩
  have heach : ∀ n ∈ targetBlock W k,
      fairBits.real (badAt n) ≤
        clusterScaleTerm W C D k + blueScaleTerm W C k := by
    intro n hn
    have hc := hcluster n hn
    have hb := hblue n hn
    change fairBits.real
      ({ω | RedClustered W C D k n ω} ∪ {ω | BlueBad W C D k n ω}) ≤ _
    exact (measureReal_union_le _ _).trans (add_le_add hc hb)
  calc
    fairBits.real {ω | ScaleBad W C D k ω} ≤
        fairBits.real (⋃ n ∈ targetBlock W k, badAt n) :=
      measureReal_mono hsubset (measure_lt_top fairBits _).ne
    _ ≤ ∑ n ∈ targetBlock W k, fairBits.real (badAt n) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _n ∈ targetBlock W k,
        (clusterScaleTerm W C D k + blueScaleTerm W C k) :=
      Finset.sum_le_sum heach
    _ = ((targetBlock W k).card : ℝ) *
        (clusterScaleTerm W C D k + blueScaleTerm W C k) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((targetBase W) ^ (k + 1) : ℕ) : ℝ) *
        (clusterScaleTerm W C D k + blueScaleTerm W C k) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast targetBlock_card_le W k
      · exact add_nonneg (clusterScaleTerm_nonneg W C D k)
          (blueScaleTerm_nonneg W C k)
    _ = scaleRawBound W C D k := rfl

lemma natCast_two_pow_le_exp (N : ℕ) :
    (((2 ^ N : ℕ) : ℝ)) ≤ Real.exp (N : ℝ) := by
  push_cast
  calc
    (2 : ℝ) ^ N ≤ (Real.exp 1) ^ N :=
      pow_le_pow_left₀ (by norm_num) (by
        simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)) N
    _ = Real.exp (N : ℝ) := by
      rw [← Real.exp_nat_mul]
      simp

lemma closeEnvelope_le_two_pow (W k : ℕ) :
    2 * closeRadius W k + 1 ≤ 2 ^ (2 * k + 2 * W + 22) := by
  have hR : 0 < closeRadius W k := by unfold closeRadius; positivity
  calc
    2 * closeRadius W k + 1 ≤ 4 * closeRadius W k := by omega
    _ = 2 ^ (2 * k + 2 * W + 22) := by
      rw [closeRadius, show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega

lemma targetPower_eq_two_pow (W k : ℕ) :
    (targetBase W) ^ (k + 1) = 2 ^ ((W + 1) * (k + 1)) := by
  simp [targetBase, pow_mul]

lemma collisionEnvelope_eq_two_pow (W k : ℕ) :
    128 * (2 ^ (k + W + 5)) ^ 5 = 2 ^ (5 * k + 5 * W + 32) := by
  rw [show 128 = 2 ^ 7 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  ring

noncomputable def clusterScaleExponent (W C D k : ℕ) : ℝ :=
  ((W + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) +
    ((D + 1 : ℕ) : ℝ) * ((2 * k + 2 * W + 22 : ℕ) : ℝ) +
    ((D + 1 : ℕ) : ℝ) * (k : ℝ) -
      (1 / 2) * (redClusterMeanCoefficient *
        ((D + 1 : ℕ) : ℝ) * (C : ℝ) * (k : ℝ))

noncomputable def blueScaleExponent (W C k : ℕ) : ℝ :=
  ((W + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) +
    ((5 * k + 5 * W + 32 : ℕ) : ℝ) * (k : ℝ) +
    ((k : ℝ) -
      (1 / 2) * (redMeanCoefficient * (C : ℝ) * (k : ℝ))) * (k : ℝ)

lemma scaleRawBound_le_exp_add_exp (W C D k : ℕ) :
    scaleRawBound W C D k ≤
      Real.exp (clusterScaleExponent W C D k) +
        Real.exp (blueScaleExponent W C k) := by
  have htarget : (((targetBase W) ^ (k + 1) : ℕ) : ℝ) ≤
      Real.exp ((((W + 1) * (k + 1) : ℕ) : ℝ)) := by
    rw [targetPower_eq_two_pow]
    exact natCast_two_pow_le_exp _
  have hclose : (((2 * closeRadius W k + 1 : ℕ) : ℝ) ^ (D + 1)) ≤
      Real.exp ((((D + 1) * (2 * k + 2 * W + 22) : ℕ) : ℝ)) := by
    calc
      ((2 * closeRadius W k + 1 : ℕ) : ℝ) ^ (D + 1) ≤
          (((2 ^ (2 * k + 2 * W + 22) : ℕ) : ℝ)) ^ (D + 1) := by
        gcongr
        exact_mod_cast closeEnvelope_le_two_pow W k
      _ = (((2 ^ ((D + 1) * (2 * k + 2 * W + 22)) : ℕ) : ℝ)) := by
        push_cast
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ Real.exp ((((D + 1) * (2 * k + 2 * W + 22) : ℕ) : ℝ)) :=
        natCast_two_pow_le_exp _
  have hcollision :
      (((128 * (2 ^ (k + W + 5)) ^ 5 : ℕ) : ℝ) ^ k) ≤
        Real.exp ((((5 * k + 5 * W + 32) * k : ℕ) : ℝ)) := by
    rw [collisionEnvelope_eq_two_pow]
    calc
      (((2 ^ (5 * k + 5 * W + 32) : ℕ) : ℝ)) ^ k =
          (((2 ^ ((5 * k + 5 * W + 32) * k) : ℕ) : ℝ)) := by
        push_cast
        rw [← pow_mul]
      _ ≤ Real.exp ((((5 * k + 5 * W + 32) * k : ℕ) : ℝ)) :=
        natCast_two_pow_le_exp _
  unfold scaleRawBound clusterScaleTerm blueScaleTerm
  rw [mul_add]
  apply add_le_add
  · calc
      (((targetBase W) ^ (k + 1) : ℕ) : ℝ) *
          (((2 * closeRadius W k + 1 : ℕ) : ℝ) ^ (D + 1) *
            Real.exp (((D + 1 : ℕ) : ℝ) * (k : ℝ) -
              1 / 2 * (redClusterMeanCoefficient *
                ((D + 1 : ℕ) : ℝ) * (C : ℝ) * (k : ℝ)))) ≤
          Real.exp ((((W + 1) * (k + 1) : ℕ) : ℝ)) *
            (Real.exp ((((D + 1) * (2 * k + 2 * W + 22) : ℕ) : ℝ)) *
              Real.exp (((D + 1 : ℕ) : ℝ) * (k : ℝ) -
                1 / 2 * (redClusterMeanCoefficient *
                  ((D + 1 : ℕ) : ℝ) * (C : ℝ) * (k : ℝ)))) := by
            gcongr
      _ = Real.exp (clusterScaleExponent W C D k) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold clusterScaleExponent
        push_cast
        ring
  · calc
      (((targetBase W) ^ (k + 1) : ℕ) : ℝ) *
          ((((128 * (2 ^ (k + W + 5)) ^ 5 : ℕ) : ℝ) ^ k) *
            Real.exp ((k : ℝ) -
              1 / 2 * (redMeanCoefficient * (C : ℝ) * (k : ℝ))) ^ k) ≤
          Real.exp ((((W + 1) * (k + 1) : ℕ) : ℝ)) *
            (Real.exp ((((5 * k + 5 * W + 32) * k : ℕ) : ℝ)) *
              Real.exp (((k : ℝ) -
                1 / 2 * (redMeanCoefficient * (C : ℝ) * (k : ℝ))) * k)) := by
            gcongr
            rw [← Real.exp_nat_mul]
            congr 1
            ring_nf
            exact le_rfl
      _ = Real.exp (blueScaleExponent W C k) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold blueScaleExponent
        push_cast
        ring

lemma redMeanCoefficient_eq_cluster :
    redMeanCoefficient = (7 / 3 : ℝ) * redClusterMeanCoefficient := by
  unfold redMeanCoefficient redClusterMeanCoefficient
  ring

lemma eventually_clusterScaleExponent_le_neg (W C D : ℕ)
    (hD : (W + 3 : ℝ) < ((D + 1 : ℕ) : ℝ) *
      (redClusterMeanCoefficient * (C : ℝ) / 2 - 3)) :
    ∀ᶠ k : ℕ in atTop, clusterScaleExponent W C D k ≤ -(k : ℝ) := by
  let c : ℝ := (W + 1 : ℝ) + (D + 1 : ℝ) * (2 * W + 22 : ℝ)
  obtain ⟨K : ℕ, hK⟩ := exists_nat_ge c
  filter_upwards [eventually_ge_atTop K] with k hk
  have hc : c ≤ (k : ℝ) := hK.trans (by exact_mod_cast hk)
  have hcoef : (W + 1 : ℝ) + 3 * (D + 1 : ℝ) -
      redClusterMeanCoefficient * (D + 1 : ℝ) * (C : ℝ) / 2 < -2 := by
    push_cast at hD
    nlinarith
  unfold clusterScaleExponent
  dsimp [c] at hc
  push_cast
  nlinarith

lemma eventually_blueScaleExponent_le_neg (W C : ℕ)
    (hlarge : 20 < redClusterMeanCoefficient * (C : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop, blueScaleExponent W C k ≤ -(k : ℝ) := by
  have halpha : 40 < redMeanCoefficient * (C : ℝ) / 2 := by
    rw [redMeanCoefficient_eq_cluster]
    have hpos := redClusterMeanCoefficient_pos
    have hC0 : (0 : ℝ) ≤ C := by positivity
    nlinarith
  filter_upwards [eventually_ge_atTop (7 * W + 40)] with k hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkW : (W : ℝ) ≤ k := by exact_mod_cast (show W ≤ k by omega)
  have hk34 : (34 : ℝ) ≤ k := by exact_mod_cast (show 34 ≤ k by omega)
  have hlinear : (6 * (W : ℝ) + 34) * (k : ℝ) + (W : ℝ) + 1 ≤
      8 * (k : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkW) hkpos.le,
      mul_nonneg (sub_nonneg.mpr hk34) hkpos.le]
  have hquad : 40 * (k : ℝ) ^ 2 <
      (redMeanCoefficient * (C : ℝ) / 2) * (k : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right halpha (sq_pos_of_pos hkpos)
  unfold blueScaleExponent
  push_cast
  nlinarith

lemma eventually_scaleRawBound_le_two_exp_neg (W C D : ℕ)
    (hlarge : 20 < redClusterMeanCoefficient * (C : ℝ) / 2)
    (hD : (W + 3 : ℝ) < ((D + 1 : ℕ) : ℝ) *
      (redClusterMeanCoefficient * (C : ℝ) / 2 - 3)) :
    ∀ᶠ k : ℕ in atTop,
      scaleRawBound W C D k ≤ 2 * Real.exp (-(k : ℝ)) := by
  have hc := eventually_clusterScaleExponent_le_neg W C D hD
  have hb := eventually_blueScaleExponent_le_neg W C hlarge
  filter_upwards [hc, hb] with k hc hb
  calc
    scaleRawBound W C D k ≤
        Real.exp (clusterScaleExponent W C D k) +
          Real.exp (blueScaleExponent W C k) :=
      scaleRawBound_le_exp_add_exp W C D k
    _ ≤ Real.exp (-(k : ℝ)) + Real.exp (-(k : ℝ)) := by
      gcongr
    _ = 2 * Real.exp (-(k : ℝ)) := by ring

lemma two_exp_neg_nat_le_three_quarters_pow {k : ℕ} (hk : 2 ≤ k) :
    2 * Real.exp (-(k : ℝ)) ≤ (3 / 4 : ℝ) ^ k := by
  have hexp : Real.exp (-1) ≤ (1 / 2 : ℝ) := Real.exp_neg_one_lt_half.le
  have hpow : Real.exp (-1) ^ k ≤ (1 / 2 : ℝ) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos _).le hexp k
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show -((2 + t : ℕ) : ℝ) = ((2 + t : ℕ) : ℝ) * (-1) by ring,
    Real.exp_nat_mul]
  calc
    2 * Real.exp (-1) ^ (2 + t) ≤ 2 * (1 / 2 : ℝ) ^ (2 + t) := by
      gcongr
    _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ t := by
      rw [pow_add]
      norm_num
      ring
    _ ≤ (9 / 16 : ℝ) * (3 / 4 : ℝ) ^ t := by
      have hp : (1 / 2 : ℝ) ^ t ≤ (3 / 4 : ℝ) ^ t :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) t
      have hp0 : 0 ≤ (3 / 4 : ℝ) ^ t := pow_nonneg (by norm_num) _
      nlinarith
    _ = (3 / 4 : ℝ) ^ (2 + t) := by
      rw [pow_add]
      norm_num

lemma eventually_scaleBad_measure_le_geometric (W C D : ℕ)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hlarge : 20 < redClusterMeanCoefficient * (C : ℝ) / 2)
    (hD : (W + 3 : ℝ) < ((D + 1 : ℕ) : ℝ) *
      (redClusterMeanCoefficient * (C : ℝ) / 2 - 3)) :
    ∀ᶠ k : ℕ in atTop,
      fairBits.real {ω | ScaleBad W C D k ω} ≤ (3 / 4 : ℝ) ^ k := by
  have hraw := eventually_scaleBad_measure_le_raw W C D hC hW
  have hdecay := eventually_scaleRawBound_le_two_exp_neg W C D hlarge hD
  filter_upwards [hraw, hdecay, eventually_ge_atTop 2] with k hraw hdecay hk
  exact hraw.trans (hdecay.trans (two_exp_neg_nat_le_three_quarters_pow hk))

lemma scaleBad_tsum_ne_top (W C D : ℕ)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hlarge : 20 < redClusterMeanCoefficient * (C : ℝ) / 2)
    (hD : (W + 3 : ℝ) < ((D + 1 : ℕ) : ℝ) *
      (redClusterMeanCoefficient * (C : ℝ) / 2 - 3)) :
    (∑' k : ℕ, fairBits {ω | ScaleBad W C D k ω}) ≠ ∞ := by
  let μk : ℕ → ℝ≥0 := fun k ↦
    (fairBits {ω | ScaleBad W C D k ω}).toNNReal
  have hgeom : Summable (fun k : ℕ ↦ (3 / 4 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hbound := eventually_scaleBad_measure_le_geometric W C D hC hW hlarge hD
  have hsumReal : Summable (fun k ↦ (μk k : ℝ)) := by
    apply Summable.of_norm_bounded_eventually_nat hgeom
    filter_upwards [hbound] with k hk
    have hfin : fairBits {ω | ScaleBad W C D k ω} ≠ ∞ :=
      measure_ne_top fairBits _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change (fairBits {ω | ScaleBad W C D k ω}).toReal ≤ _
    exact hk
  have hsumNN : Summable μk := NNReal.summable_coe.mp hsumReal
  have hcoe (k : ℕ) : (μk k : ℝ≥0∞) =
      fairBits {ω | ScaleBad W C D k ω} := by
    exact ENNReal.coe_toNNReal (measure_ne_top fairBits _)
  rw [← tsum_congr hcoe]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsumNN

/-- Borel--Cantelli fixes one red Bernoulli configuration for which all sufficiently
large scales are simultaneously free of both kinds of obstruction. -/
lemma exists_eventually_not_scaleBad (W C D : ℕ)
    (hC : 3 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hlarge : 20 < redClusterMeanCoefficient * (C : ℝ) / 2)
    (hD : (W + 3 : ℝ) < ((D + 1 : ℕ) : ℝ) *
      (redClusterMeanCoefficient * (C : ℝ) / 2 - 3)) :
    ∃ ω : ℕ → Prop, ∀ᶠ k : ℕ in atTop, ¬ ScaleBad W C D k ω := by
  have hae : ∀ᵐ ω ∂fairBits,
      ∀ᶠ k : ℕ in atTop, ω ∉ {ω | ScaleBad W C D k ω} :=
    MeasureTheory.ae_eventually_notMem
      (scaleBad_tsum_ne_top W C D hC hW hlarge hD)
  simpa only [Set.mem_setOf_eq] using hae.exists

/-! ### Deterministic blue repairs -/

lemma thirtySix_mul_sq_le_two_pow_sub {k : ℕ} (hk : 64 ≤ k) :
    36 * k ^ 2 ≤ 2 ^ (k - 16) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [show k + 1 - 16 = (k - 16) + 1 by omega, pow_succ]
      have hsquare : 36 * (k + 1) ^ 2 ≤ 2 * (36 * k ^ 2) := by
        nlinarith
      calc
        36 * (k + 1) ^ 2 ≤ 2 * (36 * k ^ 2) := hsquare
        _ ≤ 2 * 2 ^ (k - 16) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k - 16) * 2 := by ring

/-- There are eventually at least `3k` admissible prime lengths for every
target in the `k`-th target block. -/
lemma eventually_blueLabels_card_ge_three_mul (W : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k,
      3 * k ≤ (blueLabels W k n).card := by
  have hprime := eventually_blueLabels_prime_lower W
  filter_upwards [hprime, eventually_ge_atTop 64] with k hprime hk n hn
  let P := bluePrimeScale W k n
  have hPlower : 2 ^ (k - 16) ≤ P := bluePrimeScale_lower (by omega) hn
  have hPsq : 36 * k ^ 2 ≤ P :=
    (thirtySix_mul_sq_le_two_pow_sub hk).trans hPlower
  have hPoneNat : 1 < P := by
    have h48 : 2 ^ 48 ≤ P := by
      exact (Nat.pow_le_pow_right (n := 2) (by omega) (by omega)).trans hPlower
    norm_num at h48
    omega
  have hPnonneg : (0 : ℝ) ≤ P := by positivity
  have hlogpos : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hPoneNat)
  have hlogbound : Real.log (P : ℝ) ≤ 2 * Real.sqrt P := by
    calc
      Real.log (P : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hPnonneg (by norm_num)
      _ = 2 * Real.sqrt P := by
        rw [← Real.sqrt_eq_rpow]
        ring
  have hsqrt : (6 * k : ℝ) ≤ Real.sqrt P := by
    apply Real.le_sqrt_of_sq_le
    have hPsqR : (36 : ℝ) * (k : ℝ) ^ 2 ≤ (P : ℝ) := by
      exact_mod_cast hPsq
    norm_num [pow_two] at hPsqR ⊢
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hratio : (3 * k : ℝ) ≤ (P : ℝ) / Real.log P := by
    rw [le_div_iff₀ hlogpos]
    calc
      (3 * k : ℝ) * Real.log P ≤ (3 * k : ℝ) * (2 * Real.sqrt P) := by
        gcongr
      _ = (6 * k : ℝ) * Real.sqrt P := by ring
      _ ≤ Real.sqrt P * Real.sqrt P := by gcongr
      _ = (P : ℝ) := Real.mul_self_sqrt hPnonneg
  have hcardReal : (3 * k : ℝ) ≤ ((blueLabels W k n).card : ℝ) :=
    hratio.trans (hprime n hn)
  exact_mod_cast hcardReal

lemma blueLabel_baseStart_gt_one {W k n p : ℕ} (hW : 10 ≤ W)
    (hk : W + 16 ≤ k) (hn : n ∈ targetBlock W k)
    (hp : p ∈ blueLabels W k n) :
    1 < baseStart p n := by
  have hmem : baseStart p n ∈ lengthSupport p n := by
    rw [lengthSupport, Finset.mem_Icc]
    omega
  have hblock := blueLabel_support_subset (by omega) hk hn hp hmem
  rw [mem_blueBlock] at hblock
  have hpow : 1 < 2 ^ (W * k) := one_lt_pow₀ (by omega) (by nlinarith)
  exact hpow.trans_le hblock.1

lemma eventually_blue_lengthEvent_nonempty (W : ℕ) (hW : 10 ≤ W) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k, ∀ p ∈ blueLabels W k n,
      (lengthEvent p n).Nonempty := by
  have hlocal := eventually_lengthEvent_probability_lower
  rw [eventually_atTop] at hlocal
  obtain ⟨Q, hQ⟩ := hlocal
  filter_upwards [eventually_ge_atTop (Q + W + 32)] with k hk n hn p hp
  have hkblue : W + 16 ≤ k := by omega
  have hP := bluePrimeScale_lower (by omega) hn
  have hpBounds := mem_primesBetween.mp hp
  have hQp : Q ≤ p := by
    calc
      Q ≤ 2 ^ Q := self_le_two_pow Q
      _ ≤ 2 ^ (k - 16) := Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
      _ ≤ bluePrimeScale W k n := hP
      _ ≤ p := hpBounds.1
  have hp0 : 0 < p := hpBounds.2.2.pos
  have hprob := hQ p hQp n (blueLabel_sq_le_target hW hkblue hn hp)
  have hlower : 0 < Real.exp (-1600) / (64 * (p : ℝ)) := by positivity
  have hmeasure : 0 < fairSetMeasure.real (lengthEvent p n) :=
    hlower.trans_le hprob
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty.mp hempty, measureReal_empty] at hmeasure
  exact lt_irrefl 0 hmeasure

/-- A canonical finite cylinder pattern witnessing `lengthEvent q n`, whenever
that event is nonempty.  Only the inspected coordinates are retained. -/
noncomputable def lengthPattern (q n : ℕ) : Finset ℕ := by
  classical
  exact if h : (lengthEvent q n).Nonempty then
    (lengthSupport q n).filter fun x ↦ x ∈ Classical.choose h
  else ∅

lemma lengthPattern_subset_support (q n : ℕ) :
    lengthPattern q n ⊆ lengthSupport q n := by
  classical
  intro x hx
  by_cases h : (lengthEvent q n).Nonempty
  · rw [lengthPattern, dif_pos h] at hx
    exact (Finset.mem_filter.mp hx).1
  · simp [lengthPattern, h] at hx

lemma lengthPattern_mem_lengthEvent {q n : ℕ}
    (h : (lengthEvent q n).Nonempty) :
    (lengthPattern q n : Set ℕ) ∈ lengthEvent q n := by
  classical
  let S : Set ℕ := Classical.choose h
  have hS : S ∈ lengthEvent q n := Classical.choose_spec h
  have hinter : S ∩ (lengthSupport q n : Set ℕ) =
      (lengthPattern q n : Set ℕ) ∩ (lengthSupport q n : Set ℕ) := by
    ext x
    simp [lengthPattern, h, S, and_left_comm, and_assoc]
  exact (lengthEvent_congr_of_inter_support_eq hinter).mp hS

lemma lengthPattern_gives_representation {q n : ℕ} (hq : 0 < q)
    (hbase : 1 < baseStart q n) (h : (lengthEvent q n).Nonempty) :
    ∃ x y, (x, y) ∈ setIntervalRepresentations (lengthPattern q n : Set ℕ) n ∧
      (setInterval (lengthPattern q n : Set ℕ) x y).card = q :=
  lengthEvent_gives_representation_with_card hq hbase
    (lengthPattern_mem_lengthEvent h)

def supportsCollide (q n q' n' : ℕ) : Prop :=
  (lengthSupport q n ∩ lengthSupport q' n').Nonempty

noncomputable def farBlockedLabels (W k n : ℕ) (T : Finset ℕ)
    (F : ℕ → Finset ℕ) : Finset ℕ := by
  classical
  exact (blueLabels W k n).filter fun p ↦
    ∃ n' ∈ T, ¬Close W k n n' ∧
      ∃ p' ∈ F n', supportsCollide p n p' n'

@[simp] lemma mem_farBlockedLabels {W k n p : ℕ} {T : Finset ℕ}
    {F : ℕ → Finset ℕ} :
    p ∈ farBlockedLabels W k n T F ↔
      p ∈ blueLabels W k n ∧ ∃ n' ∈ T, ¬Close W k n n' ∧
        ∃ p' ∈ F n', supportsCollide p n p' n' := by
  classical
  simp [farBlockedLabels]

/-- If `n` is not blue-bad, fewer than `k` of its labels can be blocked by
already chosen channels belonging to far exceptional targets. -/
lemma farBlockedLabels_card_lt {W C D k n : ℕ} {ω : ℕ → Prop}
    {T : Finset ℕ} {F : ℕ → Finset ℕ}
    (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k)
    (hTtarget : ∀ n' ∈ T, n' ∈ targetBlock W k)
    (hTexc : ∀ n' ∈ T, RedExceptional W C D k n' ω)
    (hFlabel : ∀ n' ∈ T, ∀ p' ∈ F n', p' ∈ blueLabels W k n')
    (hgood : ¬BlueBad W C D k n ω) :
    (farBlockedLabels W k n T F).card < k := by
  classical
  by_contra hnot
  have hkcard : k ≤ (farBlockedLabels W k n T F).card := by omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hkcard
  let enum : Fin k → ℕ := chooseEnumExact S hScard
  have henum (i : Fin k) : enum i ∈ farBlockedLabels W k n T F := by
    exact hSsub (chooseEnumExact_mem S hScard i)
  have hwit (i : Fin k) : ∃ z : ℕ × ℕ,
      z.1 ∈ T ∧ ¬Close W k n z.1 ∧ z.2 ∈ F z.1 ∧
        supportsCollide (enum i) n z.2 z.1 := by
    obtain ⟨n', hn'T, hfar, p', hp'F, hcol⟩ :=
      (mem_farBlockedLabels.mp (henum i)).2
    exact ⟨(n', p'), hn'T, hfar, hp'F, hcol⟩
  let z : Fin k → ℕ × ℕ := fun i ↦ Classical.choose (hwit i)
  have hz (i : Fin k) :
      (z i).1 ∈ T ∧ ¬Close W k n (z i).1 ∧ (z i).2 ∈ F (z i).1 ∧
        supportsCollide (enum i) n (z i).2 (z i).1 :=
    Classical.choose_spec (hwit i)
  have henumLabel (i : Fin k) : enum i ∈ blueLabels W k n :=
    (mem_farBlockedLabels.mp (henum i)).1
  have hkBlue : W + 16 ≤ k := by omega
  have hzData (i : Fin k) :
      (⟨enum i, ⟨(z i).2, (z i).1⟩⟩ : BlueCollisionData) ∈
        blueCollisionData W k n := by
    rw [mem_blueCollisionData]
    refine ⟨henumLabel i,
      blueLabels_subset_scaleBluePrimes (by omega) hkBlue
        (hTtarget (z i).1 (hz i).1)
        (hFlabel (z i).1 (hz i).1 (z i).2 (hz i).2.2.1), ?_⟩
    rw [mem_blueCollisionTargets]
    exact ⟨hTtarget (z i).1 (hz i).1,
      hFlabel (z i).1 (hz i).1 (z i).2 (hz i).2.2.1,
      (hz i).2.1, (hz i).2.2.2⟩
  let g : Fin k → ↥(blueCollisionData W k n) := fun i ↦
    ⟨⟨enum i, ⟨(z i).2, (z i).1⟩⟩, hzData i⟩
  have hginj : Function.Injective (fun i ↦ (g i).1.1) := by
    intro i j hij
    apply chooseEnumExact_injective S hScard
    exact hij
  have hgconfig : g ∈ blueBadConfigurations W k n := by
    simp [blueBadConfigurations, hginj]
  apply hgood
  refine ⟨g, hgconfig, ?_⟩
  intro i
  exact hTexc (z i).1 (hz i).1

def GoodRepairFamily (W D k : ℕ) (T : Finset ℕ)
    (F : ℕ → Finset ℕ) : Prop :=
  (∀ n ∈ T, F n ⊆ blueLabels W k n) ∧
  (∀ n ∈ T, (F n).card = repairCount D k) ∧
  ∀ n ∈ T, ∀ n' ∈ T, ∀ p ∈ F n, ∀ p' ∈ F n',
    (n, p) ≠ (n', p') →
      Disjoint (lengthSupport p n) (lengthSupport p' n')

lemma goodRepairFamily_empty (W D k : ℕ) :
    GoodRepairFamily W D k ∅ (fun _ ↦ ∅) := by
  simp [GoodRepairFamily]

/-- The one-step greedy extension.  Close exceptional targets use at most
`D * repairCount D k` labels; far exceptional targets use fewer than `k`
labels, by `farBlockedLabels_card_lt`. -/
lemma GoodRepairFamily.insert {W C D k n : ℕ} {ω : ℕ → Prop}
    {T : Finset ℕ} {F : ℕ → Finset ℕ}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hnT : n ∉ T) (hn : n ∈ targetBlock W k)
    (hnExc : RedExceptional W C D k n ω)
    (hTtarget : ∀ n' ∈ T, n' ∈ targetBlock W k)
    (hTexc : ∀ n' ∈ T, RedExceptional W C D k n' ω)
    (hfamily : GoodRepairFamily W D k T F)
    (hlabels : 3 * k ≤ (blueLabels W k n).card)
    (hcluster : ¬RedClustered W C D k n ω)
    (hblue : ¬BlueBad W C D k n ω) :
    ∃ F', GoodRepairFamily W D k (insert n T) F' := by
  classical
  let t := repairCount D k
  let closeUsed : Finset ℕ :=
    (T.filter fun n' ↦ Close W k n n').biUnion F
  let farUsed := farBlockedLabels W k n T F
  let blocked := closeUsed ∪ farUsed
  let available := blueLabels W k n \ blocked
  have hcloseTargets : (T.filter fun n' ↦ Close W k n n') ⊆
      (closeTargets W k n).filter fun n' ↦ RedExceptional W C D k n' ω := by
    intro n' hn'
    rw [Finset.mem_filter] at hn' ⊢
    exact ⟨mem_closeTargets.mpr ⟨hTtarget n' hn'.1, hn'.2⟩,
      hTexc n' hn'.1⟩
  have hcloseCard : (T.filter fun n' ↦ Close W k n n').card ≤ D := by
    have hnot : ¬D + 1 ≤ ((closeTargets W k n).filter
        fun n' ↦ RedExceptional W C D k n' ω).card := by
      simpa only [RedClustered] using hcluster
    exact (Finset.card_le_card hcloseTargets).trans (by omega)
  have hcloseUsedCard : closeUsed.card ≤ D * t := by
    calc
      closeUsed.card ≤ (T.filter fun n' ↦ Close W k n n').card * t := by
        apply Finset.card_biUnion_le_card_mul
        intro n' hn'
        exact hfamily.2.1 n' (Finset.mem_filter.mp hn').1 |>.le
      _ ≤ D * t := Nat.mul_le_mul_right t hcloseCard
  have hfarCard : farUsed.card < k := by
    apply farBlockedLabels_card_lt hW hk hn hTtarget hTexc
      (fun n' hn'T p' hp' ↦ hfamily.1 n' hn'T hp') hblue
  have ht : t ≤ k := Nat.div_le_self _ _
  have hDt : D * t ≤ k := by
    have hdiv := Nat.div_mul_le_self k (D + 1)
    dsimp [t, repairCount]
    nlinarith
  have hblockedCard : blocked.card < 2 * k := by
    calc
      blocked.card ≤ closeUsed.card + farUsed.card := Finset.card_union_le _ _
      _ ≤ D * t + farUsed.card := Nat.add_le_add_right hcloseUsedCard _
      _ < 2 * k := by omega
  have hinterCard : (blocked ∩ blueLabels W k n).card < 2 * k :=
    (Finset.card_le_card Finset.inter_subset_left).trans_lt hblockedCard
  have havailableCard : t ≤ available.card := by
    change t ≤ (blueLabels W k n \ blocked).card
    rw [Finset.card_sdiff]
    omega
  obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq havailableCard
  have hGlabel : G ⊆ blueLabels W k n := by
    exact hGsub.trans Finset.sdiff_subset
  have hGnotBlocked {p : ℕ} (hp : p ∈ G) : p ∉ blocked := by
    exact (Finset.mem_sdiff.mp (hGsub hp)).2
  have hnewOld : ∀ p ∈ G, ∀ n' ∈ T, ∀ p' ∈ F n',
      Disjoint (lengthSupport p n) (lengthSupport p' n') := by
    intro p hp n' hn'T p' hp'F
    by_contra hdisj
    have hcol : supportsCollide p n p' n' :=
      Finset.not_disjoint_iff_nonempty_inter.mp hdisj
    by_cases hclose : Close W k n n'
    · have hpeq : p = p' := by
        by_contra hne
        have hd := blue_support_disjoint_of_Close_of_ne (by omega)
          (by omega) hn (hTtarget n' hn'T) hclose (hGlabel hp)
          (hfamily.1 n' hn'T hp'F) hne
        exact hdisj hd
      apply hGnotBlocked hp
      change p ∈ closeUsed ∪ farUsed
      rw [Finset.mem_union]
      left
      change p ∈ (T.filter fun n' ↦ Close W k n n').biUnion F
      rw [Finset.mem_biUnion]
      exact ⟨n', Finset.mem_filter.mpr ⟨hn'T, hclose⟩, hpeq ▸ hp'F⟩
    · apply hGnotBlocked hp
      change p ∈ closeUsed ∪ farUsed
      rw [Finset.mem_union]
      right
      rw [mem_farBlockedLabels]
      exact ⟨hGlabel hp, n', hn'T, hclose, p', hp'F, hcol⟩
  let F' : ℕ → Finset ℕ := fun m ↦ if m = n then G else F m
  refine ⟨F', ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m hm p hp
    rw [Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact hGlabel (by simpa [F'] using hp)
    · have hmn : m ≠ n := fun h ↦ hnT (h ▸ hm)
      exact hfamily.1 m hm (by simpa [F', hmn] using hp)
  · intro m hm
    rw [Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · simpa [F'] using hGcard
    · have hmn : m ≠ n := fun h ↦ hnT (h ▸ hm)
      simpa [F', hmn] using hfamily.2.1 m hm
  · intro a ha b hb p hp p' hp' hpair
    rw [Finset.mem_insert] at ha hb
    rcases ha with haEq | ha <;> rcases hb with hbEq | hb
    · subst a
      subst b
      have hpG : p ∈ G := by simpa [F'] using hp
      have hp'G : p' ∈ G := by simpa [F'] using hp'
      have hpp' : p ≠ p' := by simpa using hpair
      exact blue_support_disjoint_of_Close_of_ne (by omega) (by omega)
        hn hn (by simp [Close]) (hGlabel hpG) (hGlabel hp'G) hpp'
    · subst a
      have hpG : p ∈ G := by simpa [F'] using hp
      have hbn : b ≠ n := fun h ↦ hnT (h ▸ hb)
      have hp'F : p' ∈ F b := by simpa [F', hbn] using hp'
      exact hnewOld p hpG b hb p' hp'F
    · subst b
      have hp'G : p' ∈ G := by simpa [F'] using hp'
      have han : a ≠ n := fun h ↦ hnT (h ▸ ha)
      have hpF : p ∈ F a := by simpa [F', han] using hp
      exact (hnewOld p' hp'G a ha p hpF).symm
    · have han : a ≠ n := fun h ↦ hnT (h ▸ ha)
      have hbn : b ≠ n := fun h ↦ hnT (h ▸ hb)
      exact hfamily.2.2 a ha b hb p (by simpa [F', han] using hp)
        p' (by simpa [F', hbn] using hp') hpair

noncomputable def exceptionalTargets (W C D k : ℕ) (ω : ℕ → Prop) :
    Finset ℕ := by
  classical
  exact (targetBlock W k).filter fun n ↦ RedExceptional W C D k n ω

@[simp] lemma mem_exceptionalTargets {W C D k n : ℕ} {ω : ℕ → Prop} :
    n ∈ exceptionalTargets W C D k ω ↔
      n ∈ targetBlock W k ∧ RedExceptional W C D k n ω := by
  classical
  simp [exceptionalTargets]

lemma exists_goodRepairFamily_of_not_scaleBad {W C D k : ℕ} {ω : ℕ → Prop}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hlabels : ∀ n ∈ targetBlock W k,
      3 * k ≤ (blueLabels W k n).card)
    (hscale : ¬ScaleBad W C D k ω) :
    ∃ F, GoodRepairFamily W D k (exceptionalTargets W C D k ω) F := by
  classical
  let E := exceptionalTargets W C D k ω
  have hgood (n : ℕ) (hn : n ∈ targetBlock W k) :
      ¬RedClustered W C D k n ω ∧ ¬BlueBad W C D k n ω := by
    constructor <;> intro hbad <;> apply hscale
    · exact ⟨n, hn, Or.inl hbad⟩
    · exact ⟨n, hn, Or.inr hbad⟩
  have aux : ∀ T : Finset ℕ, T ⊆ E →
      ∃ F, GoodRepairFamily W D k T F := by
    intro T hTE
    induction T using Finset.induction_on with
    | empty => exact ⟨fun _ ↦ ∅, goodRepairFamily_empty W D k⟩
    | @insert n T hnT ih =>
        have hTsub : T ⊆ E := fun x hx ↦ hTE (Finset.mem_insert_of_mem hx)
        obtain ⟨F, hF⟩ := ih hTsub
        have hnE : n ∈ E := hTE (Finset.mem_insert_self n T)
        have hnData : n ∈ targetBlock W k ∧ RedExceptional W C D k n ω := by
          simpa only [E, mem_exceptionalTargets] using hnE
        exact hF.insert hC hW hk hnT hnData.1 hnData.2
          (fun n' hn'T ↦ (mem_exceptionalTargets.mp (hTsub hn'T)).1)
          (fun n' hn'T ↦ (mem_exceptionalTargets.mp (hTsub hn'T)).2)
          (hlabels n hnData.1) (hgood n hnData.1).1 (hgood n hnData.1).2
  exact aux E (fun _ h ↦ h)

/-- A canonical greedy repair family; it is empty only at scales where the
proved existence theorem does not apply. -/
noncomputable def repairFamily (W C D k : ℕ) (ω : ℕ → Prop) :
    ℕ → Finset ℕ := by
  classical
  exact if h : ∃ F,
      GoodRepairFamily W D k (exceptionalTargets W C D k ω) F then
    Classical.choose h
  else fun _ ↦ ∅

lemma repairFamily_good {W C D k : ℕ} {ω : ℕ → Prop}
    (h : ∃ F, GoodRepairFamily W D k
      (exceptionalTargets W C D k ω) F) :
    GoodRepairFamily W D k (exceptionalTargets W C D k ω)
      (repairFamily W C D k ω) := by
  classical
  rw [repairFamily, dif_pos h]
  exact Classical.choose_spec h

lemma repairFamily_good_of_mem {W C D k n p : ℕ} {ω : ℕ → Prop}
    (hp : p ∈ repairFamily W C D k ω n) :
    GoodRepairFamily W D k (exceptionalTargets W C D k ω)
      (repairFamily W C D k ω) := by
  classical
  by_cases h : ∃ F,
      GoodRepairFamily W D k (exceptionalTargets W C D k ω) F
  · rw [repairFamily, dif_pos h]
    exact Classical.choose_spec h
  · rw [repairFamily, dif_neg h] at hp
    simp at hp

def summandBlock (W k : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ (W * k)) (2 ^ (W * (k + 1)))

@[simp] lemma mem_summandBlock {W k x : ℕ} :
    x ∈ summandBlock W k ↔
      2 ^ (W * k) ≤ x ∧ x < 2 ^ (W * (k + 1)) := by
  simp [summandBlock]

lemma blueBlock_subset_summandBlock {W k : ℕ} (hW : 20 ≤ W) :
    blueBlock W k ⊆ summandBlock W k := by
  intro x hx
  rw [mem_blueBlock] at hx
  rw [mem_summandBlock]
  refine ⟨hx.1, hx.2.trans_le ?_⟩
  apply Nat.pow_le_pow_right (n := 2) (by omega)
  simp only [Nat.mul_add, mul_one]
  omega

lemma redBlock_subset_summandBlock {W k : ℕ} :
    redBlock W k ⊆ summandBlock W k := by
  intro x hx
  rw [mem_redBlock] at hx
  rw [mem_summandBlock]
  exact ⟨(Nat.pow_le_pow_right (n := 2) (by omega) (by omega)).trans hx.1,
    by simpa only [Nat.mul_add, mul_one] using hx.2⟩

lemma summandBlock_disjoint {W k l : ℕ} (hW : 0 < W) (hkl : k ≠ l) :
    Disjoint (summandBlock W k) (summandBlock W l) := by
  rw [Finset.disjoint_left]
  intro x hxk hxl
  rw [mem_summandBlock] at hxk hxl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hexp : W * (k + 1) ≤ W * l := Nat.mul_le_mul_left W (by omega)
    have hpow : 2 ^ (W * (k + 1)) ≤ 2 ^ (W * l) :=
      Nat.pow_le_pow_right (n := 2) (by omega) hexp
    omega
  · have hexp : W * (l + 1) ≤ W * k := Nat.mul_le_mul_left W (by omega)
    have hpow : 2 ^ (W * (l + 1)) ≤ 2 ^ (W * k) :=
      Nat.pow_le_pow_right (n := 2) (by omega) hexp
    omega

lemma blueBlock_disjoint_redBlock {W k l : ℕ} (hW : 20 ≤ W) :
    Disjoint (blueBlock W k) (redBlock W l) := by
  by_cases hkl : k = l
  · subst l
    rw [Finset.disjoint_left]
    intro x hxb hxr
    rw [mem_blueBlock] at hxb
    rw [mem_redBlock] at hxr
    omega
  · exact (summandBlock_disjoint (by omega) hkl).mono
      (blueBlock_subset_summandBlock hW) redBlock_subset_summandBlock

def redRealization (W : ℕ) (ω : ℕ → Prop) : Set ℕ :=
  {x | ∃ k, x ∈ redBlock W k ∧ ω x}

noncomputable def repairSet (W C D : ℕ) (ω : ℕ → Prop) : Set ℕ :=
  {x | ∃ k, 2 * W ≤ k ∧ ∃ n ∈ exceptionalTargets W C D k ω,
    ∃ p ∈ repairFamily W C D k ω n, x ∈ lengthPattern p n}

noncomputable def constructedSet (W C D : ℕ) (ω : ℕ → Prop) : Set ℕ :=
  redRealization W ω ∪ repairSet W C D ω

lemma redRealization_inter_redBlock (W k : ℕ) (ω : ℕ → Prop) :
    redRealization W ω ∩ (redBlock W k : Set ℕ) =
      bitsToSet ω ∩ (redBlock W k : Set ℕ) := by
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe, redRealization,
    Set.mem_setOf_eq, bitsToSet]
  constructor
  · rintro ⟨⟨l, hxl, hω⟩, hxk⟩
    exact ⟨hω, hxk⟩
  · rintro ⟨hω, hxk⟩
    exact ⟨⟨k, hxk, hω⟩, hxk⟩

lemma repairSet_disjoint_redBlock {W C D l : ℕ} {ω : ℕ → Prop}
    (hW : 20 ≤ W) :
    Disjoint (repairSet W C D ω) (redBlock W l : Set ℕ) := by
  rw [Set.disjoint_left]
  intro x hxRepair hxl
  rcases hxRepair with ⟨k, hk, n, hn, p, hp, hxp⟩
  have hpLabel := (repairFamily_good_of_mem hp).1 n hn hp
  have hxSupport := lengthPattern_subset_support p n hxp
  have hxBlue := blueLabel_support_subset (by omega) (by omega)
    (mem_exceptionalTargets.mp hn).1 hpLabel hxSupport
  exact (Finset.disjoint_left.mp (blueBlock_disjoint_redBlock hW)) hxBlue hxl

lemma constructedSet_inter_redBlock {W C D l : ℕ} {ω : ℕ → Prop}
    (hW : 20 ≤ W) :
    constructedSet W C D ω ∩ (redBlock W l : Set ℕ) =
      bitsToSet ω ∩ (redBlock W l : Set ℕ) := by
  rw [constructedSet, Set.union_inter_distrib_right,
    redRealization_inter_redBlock]
  have hd := repairSet_disjoint_redBlock (C := C) (D := D) (l := l)
    (ω := ω) hW
  rw [Set.disjoint_iff_inter_eq_empty.mp hd, Set.union_empty]

lemma repairPattern_support_disjoint {W C D k k' n n' p p' : ℕ}
    {ω : ℕ → Prop} (hW : 20 ≤ W)
    (hk : 2 * W ≤ k) (hk' : 2 * W ≤ k')
    (hn : n ∈ exceptionalTargets W C D k ω)
    (hn' : n' ∈ exceptionalTargets W C D k' ω)
    (hp : p ∈ repairFamily W C D k ω n)
    (hp' : p' ∈ repairFamily W C D k' ω n')
    (hpair : (k, n, p) ≠ (k', n', p')) :
    Disjoint (lengthSupport p n) (lengthSupport p' n') := by
  have hpLabel := (repairFamily_good_of_mem hp).1 n hn hp
  have hp'Label := (repairFamily_good_of_mem hp').1 n' hn' hp'
  have hnTarget := (mem_exceptionalTargets.mp hn).1
  have hn'Target := (mem_exceptionalTargets.mp hn').1
  by_cases hkk' : k = k'
  · subst k'
    have hnp : (n, p) ≠ (n', p') := by
      intro heq
      apply hpair
      simpa using heq
    exact (repairFamily_good_of_mem hp).2.2 n hn n' hn' p hp p' hp' hnp
  · have hsup : lengthSupport p n ⊆ summandBlock W k :=
      (blueLabel_support_subset (by omega) (by omega) hnTarget hpLabel).trans
        (blueBlock_subset_summandBlock hW)
    have hsup' : lengthSupport p' n' ⊆ summandBlock W k' :=
      (blueLabel_support_subset (by omega) (by omega) hn'Target hp'Label).trans
        (blueBlock_subset_summandBlock hW)
    exact (summandBlock_disjoint (by omega) hkk').mono hsup hsup'

/-- On an allocated blue support, the final set is exactly its chosen finite
cylinder pattern. -/
lemma constructedSet_inter_repairSupport {W C D k n p : ℕ}
    {ω : ℕ → Prop} (hW : 20 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ exceptionalTargets W C D k ω)
    (hp : p ∈ repairFamily W C D k ω n) :
    constructedSet W C D ω ∩ (lengthSupport p n : Set ℕ) =
      (lengthPattern p n : Set ℕ) := by
  ext x
  constructor
  · rintro ⟨hxS, hxSupport⟩
    rcases hxS with hxRed | hxRepair
    · rcases hxRed with ⟨l, hxl, hωx⟩
      have hpLabel := (repairFamily_good_of_mem hp).1 n hn hp
      have hxBlue := blueLabel_support_subset (by omega) (by omega)
        (mem_exceptionalTargets.mp hn).1 hpLabel hxSupport
      exact False.elim ((Finset.disjoint_left.mp
        (blueBlock_disjoint_redBlock hW)) hxBlue hxl)
    · rcases hxRepair with ⟨k', hk', n', hn', p', hp', hxp'⟩
      by_cases htriple : (k, n, p) = (k', n', p')
      · have hkk : k = k' := congrArg (fun z ↦ z.1) htriple
        have hnn : n = n' := congrArg (fun z ↦ z.2.1) htriple
        have hpp : p = p' := congrArg (fun z ↦ z.2.2) htriple
        subst k'
        subst n'
        subst p'
        exact hxp'
      · have hxSupport' := lengthPattern_subset_support p' n' hxp'
        have hd := repairPattern_support_disjoint hW hk hk' hn hn' hp hp' htriple
        exact False.elim ((Finset.disjoint_left.mp hd) hxSupport hxSupport')
  · intro hxp
    refine ⟨Or.inr ?_, lengthPattern_subset_support p n hxp⟩
    exact ⟨k, hk, n, hn, p, hp, hxp⟩

lemma constructedSet_mem_lengthEvent_of_repair {W C D k n p : ℕ}
    {ω : ℕ → Prop} (hW : 20 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ exceptionalTargets W C D k ω)
    (hp : p ∈ repairFamily W C D k ω n)
    (hevent : (lengthEvent p n).Nonempty) :
    constructedSet W C D ω ∈ lengthEvent p n := by
  have hpattern := lengthPattern_mem_lengthEvent hevent
  apply (lengthEvent_congr_of_inter_support_eq ?_).mp hpattern
  rw [constructedSet_inter_repairSupport hW hk hn hp]
  exact Set.inter_eq_left.mpr (by
    intro x hx
    exact lengthPattern_subset_support p n hx)

lemma constructedSet_mem_redTrialEvent {W C D k n : ℕ} {ω : ℕ → Prop}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) {a : RedTrial}
    (ha : a ∈ redTrials W C k n)
    (haEvent : bitsToSet ω ∈ redTrialEvent n a) :
    constructedSet W C D ω ∈ redTrialEvent n a := by
  have ha' := mem_redTrials.mp ha
  have hsupport : redTrialSupport n a ⊆ redBlock W (k - a.1.1) :=
    redSubLength_support_subset hW hk ha'.1 hn ha'.2
  have hinter : constructedSet W C D ω ∩ (redTrialSupport n a : Set ℕ) =
      bitsToSet ω ∩ (redTrialSupport n a : Set ℕ) :=
    inter_eq_on_subset hsupport
      (constructedSet_inter_redBlock (C := C) (D := D)
        (l := k - a.1.1) (ω := ω) (by omega))
  exact (redTrialEvent_supported a hinter).mpr haEvent

/-- Distinct members of the red trial family have distinct prescribed
cardinalities. -/
lemma redTrial_length_injective_on {W C k n : ℕ} (hW : 12 * C + 200 ≤ W)
    (hk : 2 * W ≤ k) (hn : n ∈ targetBlock W k) {a b : RedTrial}
    (ha : a ∈ redTrials W C k n) (hb : b ∈ redTrials W C k n)
    (hqab : a.2 = b.2) : a = b := by
  have ha' := mem_redTrials.mp ha
  have hb' := mem_redTrials.mp hb
  have hde : a.1 = b.1 := by
    by_contra hdene
    exact (redSubLengths_ne_of_channel_ne hW hk hn
      ha'.1 hb'.1 hdene ha'.2 hb'.2) hqab
  exact Sigma.ext hde (heq_of_eq hqab)

/-- A finite family of representations whose interval cardinalities are
pairwise distinct can be enumerated injectively. -/
lemma exists_injective_representations_of_distinct_cards
    {ι : Type*} [DecidableEq ι] {S : Set ℕ} {n t : ℕ}
    (R : Finset ι) (hcard : R.card = t) (q : ι → ℕ)
    (hqinj : ∀ {a b}, a ∈ R → b ∈ R → q a = q b → a = b)
    (hrep : ∀ a ∈ R, ∃ x y,
      (x, y) ∈ setIntervalRepresentations S n ∧
        (setInterval S x y).card = q a) :
    ∃ g : Fin t → ℕ × ℕ, Function.Injective g ∧
      ∀ i, g i ∈ setIntervalRepresentations S n := by
  classical
  let e : Fin t → ι := chooseEnumExact R hcard
  have heMem (i : Fin t) : e i ∈ R := chooseEnumExact_mem R hcard i
  have hwit (i : Fin t) : ∃ z : ℕ × ℕ,
      z ∈ setIntervalRepresentations S n ∧
        (setInterval S z.1 z.2).card = q (e i) := by
    obtain ⟨x, y, hxy, hxyCard⟩ := hrep (e i) (heMem i)
    exact ⟨(x, y), hxy, hxyCard⟩
  let g : Fin t → ℕ × ℕ := fun i ↦ Classical.choose (hwit i)
  have hgSpec (i : Fin t) :
      g i ∈ setIntervalRepresentations S n ∧
        (setInterval S (g i).1 (g i).2).card = q (e i) :=
    Classical.choose_spec (hwit i)
  refine ⟨g, ?_, fun i ↦ (hgSpec i).1⟩
  intro i j hij
  have hq : q (e i) = q (e j) := by
    rw [← (hgSpec i).2, ← (hgSpec j).2, hij]
  have heq : e i = e j := hqinj (heMem i) (heMem j) hq
  exact chooseEnumExact_injective R hcard heq

noncomputable def successfulRedTrials (W C k n : ℕ) (ω : ℕ → Prop) :
    Finset RedTrial := by
  classical
  exact (redTrials W C k n).filter fun a ↦
    bitsToSet ω ∈ redTrialEvent n a

@[simp] lemma mem_successfulRedTrials {W C k n : ℕ} {ω : ℕ → Prop}
    {a : RedTrial} :
    a ∈ successfulRedTrials W C k n ω ↔
      a ∈ redTrials W C k n ∧ bitsToSet ω ∈ redTrialEvent n a := by
  classical
  simp [successfulRedTrials]

lemma successfulRedTrials_card (W C k n : ℕ) (ω : ℕ → Prop) :
    (successfulRedTrials W C k n ω).card = redCount W C k n ω := by
  classical
  rw [redCount_eq_eventCount]
  rfl

lemma redTypical_injective_representations {W C D k n : ℕ} {ω : ℕ → Prop}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hn : n ∈ targetBlock W k) (htyp : RedTypical W C D k n ω) :
    ∃ g : Fin (repairCount D k) → ℕ × ℕ, Function.Injective g ∧
      ∀ i, g i ∈ setIntervalRepresentations (constructedSet W C D ω) n := by
  classical
  let R := successfulRedTrials W C k n ω
  have hRcard : repairCount D k ≤ R.card := by
    rw [successfulRedTrials_card]
    exact htyp
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hRcard
  apply exists_injective_representations_of_distinct_cards Q hQcard
    (fun a : RedTrial ↦ a.2)
  · intro a b ha hb hab
    have haR := mem_successfulRedTrials.mp (hQsub ha)
    have hbR := mem_successfulRedTrials.mp (hQsub hb)
    exact redTrial_length_injective_on hW hk hn haR.1 hbR.1 hab
  · intro a ha
    have haR := mem_successfulRedTrials.mp (hQsub ha)
    have ha' := mem_redTrials.mp haR.1
    have hq0 : 0 < a.2 := by
      rcases mem_validRedSubchannels.mp ha'.1 with ⟨_, _, hdle, heSafe, _⟩
      have heFive : 5 * a.1.2 + 5 ≤ W :=
        (Nat.add_le_add_left (by norm_num : 5 ≤ 50) (5 * a.1.2)).trans heSafe
      have hP : 0 < redSubLengthScale W k n a.1.1 a.1.2 :=
        redSubLengthScale_pos heFive (by omega) hdle hn
      exact hP.trans_le (mem_redSubLengths.mp ha'.2).1
    exact lengthEvent_gives_representation_with_card hq0
      (redSubLength_baseStart_gt_one hC hW hk hn ha'.1 ha'.2)
      (constructedSet_mem_redTrialEvent hC hW hk hn haR.1 haR.2)

lemma redExceptional_injective_representations {W C D k n : ℕ}
    {ω : ℕ → Prop} (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hk : 2 * W ≤ k) (hn : n ∈ targetBlock W k)
    (hexc : RedExceptional W C D k n ω)
    (hfamily : ∃ F, GoodRepairFamily W D k
      (exceptionalTargets W C D k ω) F)
    (hevents : ∀ p ∈ blueLabels W k n, (lengthEvent p n).Nonempty) :
    ∃ g : Fin (repairCount D k) → ℕ × ℕ, Function.Injective g ∧
      ∀ i, g i ∈ setIntervalRepresentations (constructedSet W C D ω) n := by
  classical
  let R := repairFamily W C D k ω n
  have hnE : n ∈ exceptionalTargets W C D k ω :=
    mem_exceptionalTargets.mpr ⟨hn, hexc⟩
  have hgood := repairFamily_good hfamily
  have hRcard : R.card = repairCount D k := hgood.2.1 n hnE
  apply exists_injective_representations_of_distinct_cards R hRcard id
  · intro a b ha hb hab
    exact hab
  · intro p hp
    have hpLabel : p ∈ blueLabels W k n := hgood.1 n hnE hp
    have hp0 : 0 < p := (mem_primesBetween.mp hpLabel).2.2.pos
    exact lengthEvent_gives_representation_with_card hp0
      (blueLabel_baseStart_gt_one (by omega) (by omega) hn hpLabel)
      (constructedSet_mem_lengthEvent_of_repair (by omega) hk hnE hp
        (hevents p hpLabel))

lemma goodScale_injective_representations {W C D k : ℕ} {ω : ℕ → Prop}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W) (hk : 2 * W ≤ k)
    (hlabels : ∀ n ∈ targetBlock W k,
      3 * k ≤ (blueLabels W k n).card)
    (hevents : ∀ n ∈ targetBlock W k, ∀ p ∈ blueLabels W k n,
      (lengthEvent p n).Nonempty)
    (hscale : ¬ScaleBad W C D k ω) :
    ∀ n ∈ targetBlock W k,
      ∃ g : Fin (repairCount D k) → ℕ × ℕ, Function.Injective g ∧
        ∀ i, g i ∈ setIntervalRepresentations (constructedSet W C D ω) n := by
  have hfamily := exists_goodRepairFamily_of_not_scaleBad hC hW hk hlabels hscale
  intro n hn
  rcases redTypical_or_exceptional W C D k n ω with htyp | hexc
  · exact redTypical_injective_representations hC hW hk hn htyp
  · exact redExceptional_injective_representations hC hW hk hn hexc hfamily
      (hevents n hn)

lemma eventually_goodScale_injective_representations {W C D : ℕ}
    {ω : ℕ → Prop} (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hscale : ∀ᶠ k : ℕ in atTop, ¬ScaleBad W C D k ω) :
    ∀ᶠ k : ℕ in atTop, ∀ n ∈ targetBlock W k,
      ∃ g : Fin (repairCount D k) → ℕ × ℕ, Function.Injective g ∧
        ∀ i, g i ∈ setIntervalRepresentations (constructedSet W C D ω) n := by
  have hlabels := eventually_blueLabels_card_ge_three_mul W
  have hevents := eventually_blue_lengthEvent_nonempty W (by omega)
  filter_upwards [hscale, hlabels, hevents, eventually_ge_atTop (2 * W)] with
      k hscale hlabels hevents hk
  exact goodScale_injective_representations hC hW hk hlabels hevents hscale

lemma repairCount_tendsto (D : ℕ) :
    Tendsto (repairCount D) atTop atTop := by
  rw [tendsto_atTop]
  intro r
  filter_upwards [eventually_ge_atTop (r * (D + 1))] with k hk
  rw [repairCount, Nat.le_div_iff_mul_le (by omega)]
  simpa only [Nat.mul_comm] using hk

lemma eventually_constructedSet_injective_representations {W C D : ℕ}
    {ω : ℕ → Prop} (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hscale : ∀ᶠ k : ℕ in atTop, ¬ScaleBad W C D k ω) :
    ∀ r : ℕ, ∀ᶠ n : ℕ in atTop,
      ∃ g : Fin r → ℕ × ℕ, Function.Injective g ∧
        ∀ i, g i ∈ setIntervalRepresentations (constructedSet W C D ω) n := by
  have hgood := eventually_goodScale_injective_representations hC hW hscale
  intro r
  have hgoodN := (targetScale_tendsto W).eventually hgood
  have hcount : ∀ᶠ n : ℕ in atTop,
      r ≤ repairCount D (targetScale W n) :=
    ((repairCount_tendsto D).comp (targetScale_tendsto W)).eventually
      (eventually_ge_atTop r)
  filter_upwards [hgoodN, hcount, eventually_gt_atTop (0 : ℕ)] with
      n hgoodN hcount hnpos
  have hnBlock := targetScale_mem_targetBlock (W := W) (n := n) (by omega)
  obtain ⟨g, hg, hgrep⟩ := hgoodN n hnBlock
  let e : Fin r → Fin (repairCount D (targetScale W n)) := fun i ↦
    ⟨i, i.isLt.trans_le hcount⟩
  refine ⟨fun i ↦ g (e i), fun i j hij ↦ ?_, fun i ↦ hgrep (e i)⟩
  have hev : (e i).val = (e j).val := congrArg Fin.val (hg hij)
  exact Fin.ext hev

def finalSet (W C D : ℕ) (ω : ℕ → Prop) : Set ℕ :=
  insert 1 (constructedSet W C D ω)

lemma setInterval_finalSet_eq {W C D x y : ℕ} {ω : ℕ → Prop}
    (hx : 1 < x) :
    setInterval (finalSet W C D ω) x y =
      setInterval (constructedSet W C D ω) x y := by
  ext z
  simp only [mem_setInterval, finalSet, Set.mem_insert_iff]
  constructor
  · rintro ⟨hxz, hzy, hz | hz⟩
    · omega
    · exact ⟨hxz, hzy, hz⟩
  · rintro ⟨hxz, hzy, hz⟩
    exact ⟨hxz, hzy, Or.inr hz⟩

lemma setRepresentation_mem_finalSet {W C D n x y : ℕ} {ω : ℕ → Prop}
    (hxy : (x, y) ∈ setIntervalRepresentations
      (constructedSet W C D ω) n) :
    (x, y) ∈ setIntervalRepresentations (finalSet W C D ω) n := by
  rcases hxy with ⟨hx, hxS, hyS, hxy, hsum⟩
  refine ⟨hx, Or.inr hxS, Or.inr hyS, hxy, ?_⟩
  rw [setInterval_finalSet_eq hx]
  exact hsum

lemma eventually_finalSet_injective_representations {W C D : ℕ}
    {ω : ℕ → Prop} (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hscale : ∀ᶠ k : ℕ in atTop, ¬ScaleBad W C D k ω) :
    ∀ r : ℕ, ∀ᶠ n : ℕ in atTop,
      ∃ g : Fin r → ℕ × ℕ, Function.Injective g ∧
        ∀ i, g i ∈ setIntervalRepresentations (finalSet W C D ω) n := by
  intro r
  filter_upwards [eventually_constructedSet_injective_representations
      hC hW hscale r] with n hn
  obtain ⟨g, hg, hgrep⟩ := hn
  exact ⟨g, hg, fun i ↦ setRepresentation_mem_finalSet (hgrep i)⟩

lemma infinite_of_eventually_setRepresentation_nonempty {S : Set ℕ}
    (hrep : ∀ᶠ n : ℕ in atTop, (setIntervalRepresentations S n).Nonempty) :
    S.Infinite := by
  by_contra hnot
  have hfin : S.Finite := not_not.mp hnot
  let M := ∑ x ∈ hfin.toFinset, x
  obtain ⟨n, hnrep, hnM⟩ :=
    (hrep.and (eventually_gt_atTop M)).exists
  obtain ⟨⟨x, y⟩, hxy⟩ := hnrep
  rcases hxy with ⟨hx, hxS, hyS, hxy, hsum⟩
  have hsub : setInterval S x y ⊆ hfin.toFinset := by
    intro z hz
    exact hfin.mem_toFinset.mpr (mem_setInterval.mp hz).2.2
  have hsumle : (∑ z ∈ setInterval S x y, z) ≤ M := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  omega

lemma finalSet_infinite {W C D : ℕ} {ω : ℕ → Prop}
    (hC : 1 ≤ C) (hW : 12 * C + 200 ≤ W)
    (hscale : ∀ᶠ k : ℕ in atTop, ¬ScaleBad W C D k ω) :
    (finalSet W C D ω).Infinite := by
  apply infinite_of_eventually_setRepresentation_nonempty
  filter_upwards [eventually_finalSet_injective_representations
      hC hW hscale 1] with n hn
  obtain ⟨g, hg, hgrep⟩ := hn
  exact ⟨g ⟨0, by omega⟩, hgrep ⟨0, by omega⟩⟩

lemma exists_construction_parameters :
    ∃ C W D : ℕ, 3 ≤ C ∧ 12 * C + 200 ≤ W ∧
      20 < redClusterMeanCoefficient * (C : ℝ) / 2 ∧
      (W + 3 : ℝ) < ((D + 1 : ℕ) : ℝ) *
        (redClusterMeanCoefficient * (C : ℝ) / 2 - 3) := by
  have hcpos := redClusterMeanCoefficient_pos
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (40 / redClusterMeanCoefficient)
  let C := N + 3
  let W := 12 * C + 200
  let D := W + 3
  have hmul : 40 < redClusterMeanCoefficient * (N : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hcpos).mp hN
  have hlarge : 20 < redClusterMeanCoefficient * (C : ℝ) / 2 := by
    dsimp [C]
    push_cast
    nlinarith
  refine ⟨C, W, D, by dsimp [C]; omega, by rfl, hlarge, ?_⟩
  dsimp [D]
  have hbeta : 1 < redClusterMeanCoefficient * (C : ℝ) / 2 - 3 := by
    nlinarith
  have hWnonneg : (0 : ℝ) ≤ W + 3 := by positivity
  push_cast
  nlinarith [mul_lt_mul_of_pos_left hbeta (by positivity : (0 : ℝ) < W + 4)]

lemma exists_finalSet :
    ∃ S : Set ℕ, S.Infinite ∧ 1 ∈ S ∧
      ∀ r : ℕ, ∀ᶠ n : ℕ in atTop,
        ∃ g : Fin r → ℕ × ℕ, Function.Injective g ∧
          ∀ i, g i ∈ setIntervalRepresentations S n := by
  obtain ⟨C, W, D, hC, hW, hlarge, hD⟩ := exists_construction_parameters
  obtain ⟨ω, hscale⟩ := exists_eventually_not_scaleBad W C D hC hW hlarge hD
  refine ⟨finalSet W C D ω, finalSet_infinite (by omega) hW hscale,
    Set.mem_insert 1 _, ?_⟩
  exact eventually_finalSet_injective_representations (by omega) hW hscale


end Erdos358.Global

namespace Erdos358

/-- The increasing enumeration of the constructed set resolves the first,
stronger part of Erdős Problem 358. -/
theorem exists_strictMono_tendsto_f :
    ∃ A : ℕ → ℕ, StrictMono A ∧ Tendsto (f A) atTop atTop := by
  obtain ⟨S, hS, h1, hrep⟩ := Global.exists_finalSet
  exact ⟨enumerate S, enumerate_strictMono hS,
    tendsto_f_enumerate_of_eventually_set_representations hS h1 hrep⟩

theorem erdos_358 :
    ∃ A, StrictMono A ∧ atTop.Tendsto (Erdos358.f A) atTop := by
  exact Erdos358.exists_strictMono_tendsto_f

theorem erdos_358_part_ii :
    ∃ A, StrictMono A ∧
      ∀ᶠ n in atTop, 2 ≤ Erdos358.f A n := by
  obtain ⟨A, hA, hlim⟩ := Erdos358.exists_strictMono_tendsto_f
  exact ⟨A, hA, hlim.eventually (eventually_ge_atTop 2)⟩

end Erdos358

#print axioms Erdos358.erdos_358
#print axioms Erdos358.erdos_358_part_ii

alias _root_.Erdos358.erdos_358.parts.i := _root_.Erdos358.erdos_358

alias _root_.Erdos358.erdos_358.parts.ii := _root_.Erdos358.erdos_358_part_ii
