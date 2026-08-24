/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 318.
https://www.erdosproblems.com/forum/thread/318

Informal authors:
- Paul Erdős

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos318.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/318.lean
-/
import Mathlib
import Util.Density
import UnitFractions.ErdosProblems
import ErdosProblems.Erdos253

/-!
# Erdős Problem 318

This file uses the exact `P₁` predicate from the Formal Conjectures statement.
The theorem `not_contain_single_even_as_stated` records a boundary defect in
one auxiliary statement from that file: `A = {2}` has exactly one even member,
but has `P₁` vacuously because it admits no nonconstant signing.
-/

open Set Real

namespace Erdos318

/-- Local alias of the shared arithmetic-progression predicate used by nearby files. -/
abbrev Set.IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop := Erdos253.Set.IsAPOfLength s l

/-- The exact property `P₁` used by the upstream statement. -/
def P₁ (A : Set ℕ) : Prop := ∀ (f : ℕ → ℝ),
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) →
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => -1) →
  Set.range f ⊆ {1, -1} →
  ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ A \ {0} ∧ ∑ n ∈ S, f n / n = 0

/-! ## The malformed auxiliary statement -/

/-- A singleton has `P₁` vacuously: every `{±1}`-valued signing is constant. -/
theorem singleton_two_has_P₁ : P₁ ({2} : Set ℕ) := by
  intro f hnotOne hnotNegOne hrange
  have hf2 : f 2 = 1 ∨ f 2 = -1 := by
    simpa using hrange ⟨2, rfl⟩
  rcases hf2 with hf2 | hf2
  · exfalso
    apply hnotOne
    funext x
    have hx : x.1 = 2 := by simpa using x.2.1
    simp [hx, hf2]
  · exfalso
    apply hnotNegOne
    funext x
    have hx : x.1 = 2 := by simpa using x.2.1
    simp [hx, hf2]

theorem singleton_two_even_ncard :
    {n : ℕ | n ∈ ({2} : Set ℕ) ∧ Even n}.ncard = 1 := by
  have hset : {n : ℕ | n ∈ ({2} : Set ℕ) ∧ Even n} = {2} := by
    ext n
    constructor
    · rintro ⟨hn, _⟩
      exact hn
    · intro hn
      refine ⟨hn, ?_⟩
      have : n = 2 := by simpa using hn
      subst n
      exact ⟨1, by norm_num⟩
  rw [hset]
  simp

/-- The literal upstream `contain_single_even` declaration is false. -/
theorem not_contain_single_even_as_stated : ¬ (∀ {A : Set ℕ},
    {n | n ∈ A ∧ Even n}.ncard = 1 → ¬ P₁ A) := by
  intro h
  exact h (A := ({2} : Set ℕ)) singleton_two_even_ncard singleton_two_has_P₁

private lemma sum_odd_recip_ne_inv_even {e : ℕ} {T : Finset ℕ}
    (he0 : e ≠ 0) (he : Even e) (hT : ∀ n ∈ T, Odd n) :
    (∑ n ∈ T, 1 / (n : ℝ)) ≠ 1 / e := by
  intro hsum
  let P : ℕ := ∏ n ∈ T, n
  have odd_prod_local : ∀ U : Finset ℕ, (∀ n ∈ U, Odd n) → Odd (∏ n ∈ U, n) := by
    intro U hU
    induction U using Finset.induction with
    | empty => exact ⟨0, by norm_num⟩
    | @insert a U ha ih =>
        rw [Finset.prod_insert ha]
        exact (hU a (by simp)).mul (ih fun n hn ↦ hU n (by simp [hn]))
  have hPodd : Odd P := odd_prod_local T hT
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0] at hPodd
    norm_num at hPodd
  have hcast : (∑ n ∈ T, ((P / n : ℕ) : ℝ)) =
      (P : ℝ) * ∑ n ∈ T, 1 / (n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnodd := hT n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hnodd
    rw [Nat.cast_div (Finset.dvd_prod_of_mem (fun n : ℕ ↦ n) hn)
      (Nat.cast_ne_zero.mpr hn0)]
    ring
  have hreal : (e : ℝ) * ∑ n ∈ T, ((P / n : ℕ) : ℝ) = P := by
    rw [hcast, hsum]
    field_simp [he0]
  have hnat : e * ∑ n ∈ T, P / n = P := by
    exact_mod_cast hreal
  have hPeven : Even P := by
    rw [← hnat]
    exact Even.mul_right he _
  exact (Nat.not_even_iff_odd.mpr hPodd) hPeven

/-- Correct form of the single-even obstruction for Lean's `ℕ`, which contains `0`:
the unique even member is positive and the set also contains an odd member. -/
theorem contain_single_even_of_positive_and_odd {A : Set ℕ}
    (hcard : {n | n ∈ A ∧ Even n}.ncard = 1)
    (hpositiveEven : ∃ e ∈ A, e ≠ 0 ∧ Even e)
    (hodd : ∃ o ∈ A, Odd o) : ¬ P₁ A := by
  obtain ⟨e, heA, he0, heEven⟩ := hpositiveEven
  obtain ⟨o, hoA, hoOdd⟩ := hodd
  obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp hcard
  have heu : e = u := by
    have heMem : e ∈ {n : ℕ | n ∈ A ∧ Even n} := ⟨heA, heEven⟩
    rw [hu] at heMem
    simpa using heMem
  subst u
  have hunique : ∀ {n : ℕ}, n ∈ A → Even n → n = e := by
    intro n hnA hnEven
    have hnMem : n ∈ {n : ℕ | n ∈ A ∧ Even n} := ⟨hnA, hnEven⟩
    rw [hu] at hnMem
    simpa using hnMem
  have ho0 : o ≠ 0 := by
    rintro rfl
    norm_num at hoOdd
  have hoe : o ≠ e := by
    intro hoe
    subst o
    exact (Nat.not_even_iff_odd.mpr hoOdd) heEven
  simp only [P₁, not_forall, not_exists, not_and]
  let f : ℕ → ℝ := fun n ↦ if Even n then -1 else 1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro hf
    have h := congr_fun hf ⟨e, ⟨heA, by simpa⟩⟩
    norm_num [f, heEven] at h
  · intro hf
    have h := congr_fun hf ⟨o, ⟨hoA, by simpa⟩⟩
    norm_num [f, Nat.not_even_iff_odd.mpr hoOdd] at h
  · rintro _ ⟨n, rfl⟩
    by_cases hn : Even n <;> simp [f, hn]
  · intro S hS hsub
    by_cases heS : e ∈ S
    · intro hzero
      rw [← Finset.sum_erase_add S (fun n ↦ f n / (n : ℝ)) heS] at hzero
      have herase : (∑ n ∈ S.erase e, f n / (n : ℝ)) =
          ∑ n ∈ S.erase e, 1 / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hne : n ≠ e := (Finset.mem_erase.mp hn).1
        have hnA : n ∈ A := (hsub (Finset.mem_of_mem_erase hn)).1
        have hnNotEven : ¬ Even n := fun hnEven ↦ hne (hunique hnA hnEven)
        simp [f, hnNotEven]
      rw [herase] at hzero
      have hrec : (∑ n ∈ S.erase e, 1 / (n : ℝ)) = 1 / e := by
        simp [f, heEven] at hzero
        have hzero' : (∑ n ∈ S.erase e, 1 / (n : ℝ)) + (-1 : ℝ) / e = 0 := by
          simpa [one_div] using hzero
        calc
          (∑ n ∈ S.erase e, 1 / (n : ℝ)) = -((-1 : ℝ) / e) :=
            eq_neg_of_add_eq_zero_left hzero'
          _ = 1 / e := by ring
      exact (sum_odd_recip_ne_inv_even he0 heEven (fun n hn ↦
        Nat.not_even_iff_odd.mp (fun hnEven ↦
          (Finset.mem_erase.mp hn).1
            (hunique (hsub (Finset.mem_of_mem_erase hn)).1 hnEven)))) hrec
    · have hpos : 0 < ∑ n ∈ S, f n / (n : ℝ) := by
        refine Finset.sum_pos (fun n hn ↦ ?_) hS
        have hnA : n ∈ A := (hsub hn).1
        have hn0 : n ≠ 0 := (hsub hn).2
        have hnNotEven : ¬ Even n := fun hnEven ↦ heS ((hunique hnA hnEven) ▸ hn)
        simp [f, hnNotEven]
        positivity
      exact ne_of_gt hpos

/-! ## A positive-density counterexample -/

/-- The odd positive integers together with the single even integer `2`. -/
def densityCounterexample : Set ℕ := {n | Odd n} ∪ {2}

private lemma odd_prod {T : Finset ℕ} (hT : ∀ n ∈ T, Odd n) : Odd (∏ n ∈ T, n) := by
  induction T using Finset.induction with
  | empty => exact ⟨0, by norm_num⟩
  | @insert a T ha ih =>
      rw [Finset.prod_insert ha]
      exact (hT a (by simp)).mul (ih fun n hn ↦ hT n (by simp [hn]))

private lemma sum_odd_recip_ne_half {T : Finset ℕ} (hT : ∀ n ∈ T, Odd n) :
    (∑ n ∈ T, 1 / (n : ℝ)) ≠ 1 / 2 := by
  intro hsum
  let P : ℕ := ∏ n ∈ T, n
  have hPodd : Odd P := by
    exact odd_prod hT
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0] at hPodd
    norm_num at hPodd
  have hcast : (∑ n ∈ T, ((P / n : ℕ) : ℝ)) =
      (P : ℝ) * ∑ n ∈ T, 1 / (n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnodd := hT n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hnodd
    rw [Nat.cast_div (Finset.dvd_prod_of_mem (fun n : ℕ ↦ n) hn)
      (Nat.cast_ne_zero.mpr hn0)]
    ring
  have hreal : (2 : ℝ) * ∑ n ∈ T, ((P / n : ℕ) : ℝ) = P := by
    rw [hcast, hsum]
    ring
  have hnat : 2 * ∑ n ∈ T, P / n = P := by
    exact_mod_cast hreal
  have hPeven : Even P := by
    refine ⟨∑ n ∈ T, P / n, ?_⟩
    omega
  exact (Nat.not_even_iff_odd.mpr hPodd) hPeven

/-- The intended single-even argument, specialized to an actually nontrivial set. -/
theorem densityCounterexample_not_P₁ : ¬ P₁ densityCounterexample := by
  simp only [P₁, not_forall, not_exists, not_and]
  let f : ℕ → ℝ := fun n ↦ if n = 2 then -1 else 1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro hf
    have h := congr_fun hf ⟨2, by simp [densityCounterexample]⟩
    norm_num [f] at h
  · intro hf
    have h := congr_fun hf ⟨1, by
      constructor
      · left
        exact ⟨0, by omega⟩
      · norm_num⟩
    norm_num [f] at h
  · rintro _ ⟨n, rfl⟩
    by_cases hn2 : n = 2 <;> simp [f, hn2]
  · intro S hS hsub
    by_cases h2 : 2 ∈ S
    · intro hzero
      rw [← Finset.sum_erase_add S (fun n ↦ f n / (n : ℝ)) h2] at hzero
      have herase : (∑ n ∈ S.erase 2, f n / (n : ℝ)) =
          ∑ n ∈ S.erase 2, 1 / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn2 : n ≠ 2 := (Finset.mem_erase.mp hn).1
        simp [f, hn2]
      rw [herase] at hzero
      have hrec : (∑ n ∈ S.erase 2, 1 / (n : ℝ)) = 1 / 2 := by
        norm_num [f] at hzero ⊢
        linarith
      apply (sum_odd_recip_ne_half (T := S.erase 2) ?_) hrec
      intro n hn
      have hnS : n ∈ S := Finset.mem_of_mem_erase hn
      have hnA : n ∈ densityCounterexample := (hsub hnS).1
      have hn2 : n ≠ 2 := (Finset.mem_erase.mp hn).1
      rcases hnA with hnodd | hn2'
      · exact hnodd
      · exact (hn2 (by simpa using hn2')).elim
    · have hpos : 0 < ∑ n ∈ S, f n / (n : ℝ) := by
        refine Finset.sum_pos (fun n hn ↦ ?_) hS
        have hnA : n ∈ densityCounterexample := (hsub hn).1
        have hn0 : n ≠ 0 := (hsub hn).2
        have hn2 : n ≠ 2 := fun hn' ↦ h2 (hn' ▸ hn)
        simp [f, hn2]
        positivity
      exact ne_of_gt hpos

private lemma ncard_odd_inter_Iio (N : ℕ) :
    ({n : ℕ | Odd n} ∩ Set.Iio N).ncard = N / 2 := by
  let g : ℕ → ℕ := fun k ↦ 2 * k + 1
  have hg : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    omega
  have hset : {n : ℕ | Odd n} ∩ Set.Iio N = g '' Set.Iio (N / 2) := by
    ext n
    constructor
    · rintro ⟨⟨k, hk⟩, hn⟩
      change n = 2 * k + 1 at hk
      change n < N at hn
      refine ⟨k, ?_, ?_⟩
      · change k < N / 2
        omega
      · dsimp [g]
        omega
    · rintro ⟨k, hk, rfl⟩
      change Odd (g k) ∧ g k < N
      constructor
      · exact ⟨k, by simp [g, two_mul]⟩
      · change k < N / 2 at hk
        dsimp [g]
        omega
  rw [hset, Set.ncard_image_of_injective _ hg, Set.ncard_Iio_nat]

private lemma ncard_densityCounterexample_inter_Iio {N : ℕ} (hN : 3 ≤ N) :
    (densityCounterexample ∩ Set.Iio N).ncard = N / 2 + 1 := by
  have hset : densityCounterexample ∩ Set.Iio N =
      insert 2 ({n : ℕ | Odd n} ∩ Set.Iio N) := by
    ext n
    constructor
    · rintro ⟨hnA, hnN⟩
      rcases hnA with hnodd | hn2
      · exact Or.inr ⟨hnodd, hnN⟩
      · left
        simpa using hn2
    · intro hn
      rcases hn with hn2 | ⟨hnodd, hnN⟩
      · subst n
        constructor
        · exact Or.inr (by simp)
        · change 2 < N
          omega
      · exact ⟨Or.inl hnodd, hnN⟩
  have h2not : 2 ∉ ({n : ℕ | Odd n} ∩ Set.Iio N) := by
    norm_num [Nat.odd_iff]
  rw [hset, Set.ncard_insert_of_notMem h2not, ncard_odd_inter_Iio]

private lemma tendsto_nat_floor_half_ratio :
    Filter.Tendsto (fun N : ℕ ↦ ((N / 2 : ℕ) : ℝ) / N)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hlower : Filter.Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) - 1 / N)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hone : Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / N)
        Filter.atTop (nhds (0 : ℝ)) := tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.sub hone :
      Filter.Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) - 1 / N)
        Filter.atTop (nhds ((1 / 2 : ℝ) - 0)))
  have hupper : Filter.Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hlowNat : N < 2 * (N / 2 + 1) := by omega
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    apply (le_div_iff₀ hNreal).2
    have hlowReal : (N : ℝ) < 2 * ((N / 2 : ℕ) + 1) := by exact_mod_cast hlowNat
    have hid : ((1 / 2 : ℝ) - 1 / N) * N = (N : ℝ) / 2 - 1 := by
      field_simp [ne_of_gt hNreal]
    nlinarith
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have huppNat : 2 * (N / 2) ≤ N := by omega
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    apply (div_le_iff₀ hNreal).2
    have huppReal : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast huppNat
    nlinarith

private lemma tendsto_densityCounterexample_ratio :
    Filter.Tendsto (fun N : ℕ ↦ (((N / 2 + 1 : ℕ) : ℝ) / N))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have h := tendsto_nat_floor_half_ratio.add tendsto_one_div_atTop_nhds_zero_nat
  convert h using 1 <;> norm_num [Nat.cast_add, add_div]

theorem densityCounterexample_hasDensity :
    densityCounterexample.HasDensity (1 / 2 : ℝ) := by
  rw [Set.HasDensity]
  apply tendsto_densityCounterexample_ratio.congr'
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  rw [Set.partialDensity]
  simp only [inter_univ, univ_inter, Set.ncard_Iio_nat]
  rw [ncard_densityCounterexample_inter_Iio hN]

/-- There is a positive-density set without property `P₁`. -/
theorem not_erdos_318 : ∃ A : Set ℕ, A.HasPosDensity ∧ ¬ P₁ A := by
  refine ⟨densityCounterexample, ⟨1 / 2, by norm_num, densityCounterexample_hasDensity⟩,
    densityCounterexample_not_P₁⟩

/-! ## A density lemma for two-colourings of an affine progression -/

private lemma exists_affine_fiber_upper_density_pos (c : ℕ → Bool) :
    ∃ a : Bool, ∀ r m : ℕ, 0 < m →
      0 < UnitFractions.upper_density
        {z : ℕ | ∃ n : ℕ, z = r + m * n ∧ c n = a} := by
  classical
  have hblock : ∀ k : ℕ, ∃ a : Bool,
      k ≤ ((Finset.range (2 * k)).filter fun n ↦ c n = a).card := by
    intro k
    obtain ⟨a, -, ha⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := Finset.range (2 * k)) (t := (Finset.univ : Finset Bool))
        (f := c) (n := k) (fun _ _ ↦ by simp) Finset.univ_nonempty (by simp)
    exact ⟨a, by simpa using ha⟩
  let g : ℕ → Bool := fun k ↦ Classical.choose (hblock k)
  have hg : ∀ k : ℕ,
      k ≤ ((Finset.range (2 * k)).filter fun n ↦ c n = g k).card := by
    intro k
    exact Classical.choose_spec (hblock k)
  obtain ⟨a, haInf⟩ := Finite.exists_infinite_fiber g
  have haInf' : (g ⁻¹' {a}).Infinite := Set.infinite_coe_iff.mp haInf
  let K : Set ℕ := (g ⁻¹' {a}) \ {0}
  have hK : K.Infinite := Set.Infinite.sdiff haInf' (Set.finite_singleton 0)
  refine ⟨a, ?_⟩
  intro r m hm
  let B : Bool → Set ℕ := fun a ↦ {z : ℕ | ∃ n : ℕ, z = r + m * n ∧ c n = a}
  let D : ℕ := r + 2 * m + 1
  have hD : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by simp [D])
  let T : Set ℕ := {N : ℕ | (1 / (D : ℝ)) ≤ UnitFractions.partial_density (B a) N}
  have himage : (fun k : ℕ ↦ D * k) '' K ⊆ T := by
    intro N hN
    rcases hN with ⟨k, hk, rfl⟩
    have hk0 : 0 < k := Nat.pos_iff_ne_zero.mpr (by simpa [K] using hk.2)
    have hka : g k = a := by simpa [K] using hk.1
    let I := (Finset.range (2 * k)).filter fun n ↦ c n = a
    let e : ℕ ↪ ℕ := ⟨fun n ↦ r + m * n, by
      intro x y hxy
      change r + m * x = r + m * y at hxy
      exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_left_cancel hxy)⟩
    have hsub : I.map e ⊆
        (Finset.range (D * k)).filter fun z : ℕ ↦ z ∈ B a := by
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨n, hn, rfl⟩
      have hn' := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [Finset.mem_range]
        have hnk : n < 2 * k := Finset.mem_range.mp hn'.1
        change r + m * n < D * k
        dsimp [D]
        nlinarith
      · exact ⟨n, rfl, hn'.2⟩
    have hkcount : k ≤ I.card := by
      simpa [I, hka] using hg k
    have hcard : k ≤
        ((Finset.range (D * k)).filter fun z : ℕ ↦ z ∈ B a).card := by
      calc
        k ≤ I.card := hkcount
        _ = (I.map e).card := (Finset.card_map e).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hNpos : 0 < (((D * k : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (by simp [D]) hk0
    have hkcast : (k : ℝ) ≤
        (((Finset.range (D * k)).filter fun z : ℕ ↦ z ∈ B a).card : ℝ) := by
      exact_mod_cast hcard
    dsimp [T]
    rw [UnitFractions.partial_density]
    have hfrac : (1 / (D : ℝ)) = (k : ℝ) / (((D * k : ℕ) : ℝ)) := by
      rw [Nat.cast_mul]
      field_simp [ne_of_gt hD, (show (k : ℝ) ≠ 0 by exact_mod_cast hk0.ne')]
    rw [hfrac]
    exact (div_le_div_iff_of_pos_right hNpos).2 hkcast
  have hinj : Set.InjOn (fun k : ℕ ↦ D * k) K := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (by simp [D]) hxy
  have hTinf : T.Infinite := (hK.image hinj).mono himage
  have hfreq : ∃ᶠ N : ℕ in Filter.atTop,
      (1 / (D : ℝ)) ≤ UnitFractions.partial_density (B a) N := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hTinf
  have hupper : (1 / (D : ℝ)) ≤ UnitFractions.upper_density (B a) := by
    exact Filter.le_limsup_of_frequently_le hfreq
      (UnitFractions.is_bounded_under_le_partial_density (A := B a))
  simpa [B] using lt_of_lt_of_le (one_div_pos.mpr hD) hupper

private lemma gcd_lcm_dvd_of_gcd_dvd {a d x y : ℕ}
    (hd : d ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : x.gcd d ∣ a) (hy : y.gcd d ∣ a) :
    (x.lcm y).gcd d ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  have hL0 : x.lcm y ≠ 0 := Nat.lcm_ne_zero hx0 hy0
  have hG0 : (x.lcm y).gcd d ≠ 0 := Nat.gcd_ne_zero_left hL0
  apply (Nat.factorization_le_iff_dvd hG0 ha).mp
  rw [Nat.factorization_gcd hL0 hd, Nat.factorization_lcm hx0 hy0]
  have hxle := (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hx0) ha).mpr hx
  have hyle := (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hy0) ha).mpr hy
  rw [Nat.factorization_gcd hx0 hd] at hxle
  rw [Nat.factorization_gcd hy0 hd] at hyle
  intro p
  specialize hxle p
  specialize hyle p
  simp only [Finsupp.inf_apply, Finsupp.sup_apply] at hxle hyle ⊢
  omega

private lemma exists_lcm_mul_eq_add_mul {a d x y : ℕ}
    (hd : 0 < d) (hx0 : 0 < x) (hy0 : 0 < y)
    (hx : ∃ i : ℕ, x = a + i * d) (hy : ∃ i : ℕ, y = a + i * d) :
    ∃ t k : ℕ, 0 < t ∧ x.lcm y * t = a + k * d := by
  have hgx : x.gcd d ∣ a := by
    rcases hx with ⟨i, hi⟩
    have hmul : x.gcd d ∣ i * d := (Nat.gcd_dvd_right x d).mul_left i
    apply (Nat.dvd_add_iff_left hmul).mpr
    rw [← hi]
    exact Nat.gcd_dvd_left x d
  have hgy : y.gcd d ∣ a := by
    rcases hy with ⟨i, hi⟩
    have hmul : y.gcd d ∣ i * d := (Nat.gcd_dvd_right y d).mul_left i
    apply (Nat.dvd_add_iff_left hmul).mpr
    rw [← hi]
    exact Nat.gcd_dvd_left y d
  let L := x.lcm y
  let G := L.gcd d
  have hG : G ∣ a := by
    exact gcd_lcm_dvd_of_gcd_dvd hd.ne' hx0.ne' hy0.ne' hgx hgy
  rcases hG with ⟨w, hw⟩
  have hbez : (L : ℤ) * Nat.gcdA L d ≡ (G : ℤ) [ZMOD d] := by
    exact Int.gcd_a_modEq L d
  let u : ℤ := Nat.gcdA L d * w
  have hu : (L : ℤ) * u ≡ (a : ℤ) [ZMOD d] := by
    calc
      (L : ℤ) * u = ((L : ℤ) * Nat.gcdA L d) * w := by simp [u]; ring
      _ ≡ (G : ℤ) * w [ZMOD d] := hbez.mul_right w
      _ = a := by exact_mod_cast hw.symm
  obtain ⟨t0, -, ht0⟩ :=
    Int.existsUnique_equiv_nat u (b := (d : ℤ)) (by exact_mod_cast hd)
  let t : ℕ := t0 + d * (a + 1)
  have htmod : (t : ℤ) ≡ u [ZMOD d] := by
    calc
      (t : ℤ) ≡ (t0 : ℤ) [ZMOD d] := by simp [t]
      _ ≡ u [ZMOD d] := ht0
  have hmodInt : ((L * t : ℕ) : ℤ) ≡ (a : ℤ) [ZMOD d] := by
    simpa [Nat.cast_mul] using (htmod.mul_left (L : ℤ)).trans hu
  have hmod : L * t ≡ a [MOD d] := by
    exact_mod_cast hmodInt
  have hL : 0 < L := Nat.lcm_pos hx0 hy0
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hle : a ≤ L * t := by
    dsimp [t]
    nlinarith [Nat.mul_pos hL hd]
  have hdvd : d ∣ L * t - a := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  rcases hdvd with ⟨k, hk⟩
  refine ⟨t, k, ht, ?_⟩
  change L * t = a + k * d
  calc
    L * t = (L * t - a) + a := (Nat.sub_add_cancel hle).symm
    _ = d * k + a := by rw [hk]
    _ = a + k * d := by ac_rfl

private lemma exists_opposite_signs {A : Set ℕ} {f : ℕ → ℝ}
    (hnotOne : f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1))
    (hnotNegOne : f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => -1))
    (hrange : Set.range f ⊆ {1, -1}) :
    ∃ x : (A \ {0} : Set ℕ), f x = 1 ∧
      ∃ y : (A \ {0} : Set ℕ), f y = -1 := by
  have hxne : ∃ x : (A \ {0} : Set ℕ), f x ≠ -1 := by
    by_contra h
    push Not at h
    apply hnotNegOne
    funext x
    exact h x
  have hyne : ∃ y : (A \ {0} : Set ℕ), f y ≠ 1 := by
    by_contra h
    push Not at h
    apply hnotOne
    funext y
    exact h y
  rcases hxne with ⟨x, hx⟩
  rcases hyne with ⟨y, hy⟩
  have hfx : f x = 1 := by
    have := hrange ⟨x, rfl⟩
    rcases this with h | h
    · exact h
    · exact (hx h).elim
  have hfy : f y = -1 := by
    have := hrange ⟨y, rfl⟩
    rcases this with h | h
    · exact (hy h).elim
    · exact h
  exact ⟨x, hfx, y, hfy⟩

private lemma infinite_AP_normal_form {A : Set ℕ} (hA : Set.IsAPOfLength A ⊤) :
    ∃ a d : ℕ, 0 < d ∧ A = Set.range (fun n : ℕ ↦ a + n * d) := by
  rcases hA with ⟨a, d, hcard, hset⟩
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    subst d
    have hsing : A = {a} := by simpa using hset
    rw [hsing] at hcard
    simp at hcard
  refine ⟨a, d, hd, ?_⟩
  rw [hset]
  ext z
  simp

/-- Every infinite arithmetic progression has property `P₁`. -/
theorem erdos_318.variants.infinite_AP {A : Set ℕ}
    (hA : Set.IsAPOfLength A ⊤) : P₁ A := by
  classical
  intro f hnotOne hnotNegOne hrange
  obtain ⟨x, hfx, y, hfy⟩ := exists_opposite_signs hnotOne hnotNegOne hrange
  obtain ⟨a, d, hd, hAeq⟩ := infinite_AP_normal_form hA
  have hxpos : 0 < (x : ℕ) := Nat.pos_iff_ne_zero.mpr x.property.2
  have hypos : 0 < (y : ℕ) := Nat.pos_iff_ne_zero.mpr y.property.2
  obtain ⟨ix, hix⟩ : ∃ i : ℕ, (x : ℕ) = a + i * d := by
    let xv : ℕ := x
    have hxA : xv ∈ A := x.property.1
    have hxA' : xv ∈ Set.range (fun n : ℕ ↦ a + n * d) := by
      rwa [← hAeq]
    rcases hxA' with ⟨i, hi⟩
    exact ⟨i, by simpa [xv] using hi.symm⟩
  obtain ⟨iy, hiy⟩ : ∃ i : ℕ, (y : ℕ) = a + i * d := by
    let yv : ℕ := y
    have hyA : yv ∈ A := y.property.1
    have hyA' : yv ∈ Set.range (fun n : ℕ ↦ a + n * d) := by
      rwa [← hAeq]
    rcases hyA' with ⟨i, hi⟩
    exact ⟨i, by simpa [yv] using hi.symm⟩
  obtain ⟨t, k0, ht, hbase⟩ :=
    exists_lcm_mul_eq_add_mul hd hxpos hypos ⟨ix, hix⟩ ⟨iy, hiy⟩
  let L : ℕ := (x : ℕ).lcm (y : ℕ)
  have hL : 0 < L := Nat.lcm_pos hxpos hypos
  let common : ℕ → ℕ := fun n ↦ L * (t + d * n)
  let c : ℕ → Bool := fun n ↦ decide (f (common n) = 1)
  obtain ⟨sgn, hsgn⟩ := exists_affine_fiber_upper_density_pos c
  let b : ℕ := if sgn then y else x
  let ε : ℝ := if sgn then 1 else -1
  have hbpos : 0 < b := by
    cases sgn <;> simp [b, hxpos, hypos]
  have hfb : f b = -ε := by
    cases sgn <;> simp [b, ε, hfx, hfy]
  have hbA : b ∈ A \ {0} := by
    cases sgn <;> simp [b, x.property, y.property]
  have hbL : b ∣ L := by
    cases sgn
    · simpa [b, L] using Nat.dvd_lcm_left (x : ℕ) (y : ℕ)
    · simpa [b, L] using Nat.dvd_lcm_right (x : ℕ) (y : ℕ)
  let q : ℕ := L / b
  have hbq : b * q = L := by
    dsimp [q]
    rw [Nat.mul_comm, Nat.div_mul_cancel hbL]
  have hq : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, mul_zero] at hbq
    omega
  let B : Set ℕ := {z : ℕ | ∃ n : ℕ,
    z = q * t + q * d * n ∧ c n = sgn}
  have hB : 0 < UnitFractions.upper_density B := by
    simpa [B, mul_assoc] using hsgn (q * t) (q * d) (Nat.mul_pos hq hd)
  let B' : Set ℕ := B \ ({0, 1} : Set ℕ)
  have hpres : UnitFractions.upper_density B = UnitFractions.upper_density B' := by
    simpa [B'] using
      (UnitFractions.upper_density_preserved (A := B) (S := ({0, 1} : Finset ℕ)))
  have hB' : 0 < UnitFractions.upper_density B' := by
    rwa [← hpres]
  obtain ⟨S, hSB, hrecQ⟩ := UnitFractions.unit_fractions_upper_density B' hB'
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hrecQ
    norm_num at hrecQ
  have hrecR : (∑ z ∈ S, 1 / (z : ℝ)) = 1 := by
    have h := congrArg (fun q : ℚ ↦ (q : ℝ)) hrecQ
    push_cast at h
    simpa using h
  have hcSign {n : ℕ} (hn : c n = sgn) : f (common n) = ε := by
    cases hs : sgn
    · have hne : f (common n) ≠ 1 := by
        intro heq
        have : c n = true := by simp [c, heq]
        rw [hn, hs] at this
        contradiction
      have hval := hrange ⟨common n, rfl⟩
      rcases hval with hval | hval
      · exact (hne hval).elim
      · simpa [ε, hs] using hval
    · have : f (common n) = 1 := by
        have : c n = true := by simp [hn, hs]
        simpa [c] using this
      simpa [ε, hs] using this
  have hcommonA (n : ℕ) : common n ∈ A := by
    rw [hAeq]
    refine ⟨k0 + L * n, ?_⟩
    have hbaseL : L * t = a + k0 * d := by simpa [L] using hbase
    dsimp [common]
    calc
      a + (k0 + L * n) * d = (a + k0 * d) + L * d * n := by ring
      _ = L * t + L * d * n := by rw [hbaseL]
      _ = L * (t + d * n) := by ring
  let eb : ℕ ↪ ℕ := ⟨fun z ↦ b * z, by
    intro u v huv
    exact Nat.eq_of_mul_eq_mul_left hbpos huv⟩
  let M : Finset ℕ := S.map eb
  have hbnotM : b ∉ M := by
    intro hbM
    rcases Finset.mem_map.mp hbM with ⟨z, hzS, hz⟩
    have hzB' : z ∈ B' := hSB hzS
    have hz1 : z ≠ 1 := by
      intro hz1
      apply hzB'.2
      simp [hz1]
    apply hz1
    change b * z = b at hz
    apply Nat.eq_of_mul_eq_mul_left hbpos
    simpa using hz
  have hMsub : (M : Set ℕ) ⊆ A \ {0} := by
    intro w hw
    rcases Finset.mem_map.mp hw with ⟨z, hzS, rfl⟩
    have hzB' : z ∈ B' := hSB hzS
    have hzB : z ∈ B := hzB'.1
    rcases hzB with ⟨n, hzn, hcn⟩
    have hden : b * z = common n := by
      dsimp [common]
      rw [hzn, ← hbq]
      ring
    change b * z ∈ A \ {0}
    rw [hden]
    refine ⟨hcommonA n, ?_⟩
    have : 0 < common n := by
      dsimp [common]
      positivity
    exact this.ne'
  have hMsign : ∀ z ∈ S, f (b * z) = ε := by
    intro z hzS
    have hzB' : z ∈ B' := hSB hzS
    rcases hzB'.1 with ⟨n, hzn, hcn⟩
    have hden : b * z = common n := by
      dsimp [common]
      rw [hzn, ← hbq]
      ring
    rw [hden]
    exact hcSign hcn
  have hMsum : (∑ w ∈ M, f w / (w : ℝ)) = ε / b := by
    dsimp [M]
    rw [Finset.sum_map]
    calc
      (∑ z ∈ S, f (b * z) / ((b * z : ℕ) : ℝ)) =
          ∑ z ∈ S, (ε / b) * (1 / (z : ℝ)) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hMsign z hz]
            have hz0 : z ≠ 0 := by
              intro hz0
              apply (hSB hz).2
              simp [hz0]
            push_cast
            field_simp [hbpos.ne', hz0]
      _ = (ε / b) * ∑ z ∈ S, 1 / (z : ℝ) := by rw [Finset.mul_sum]
      _ = ε / b := by rw [hrecR, mul_one]
  refine ⟨insert b M, Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hbA
    · exact hMsub hw
  · rw [Finset.sum_insert hbnotM, hMsum, hfb]
    ring

/-- The natural numbers have property `P₁`. -/
theorem erdos_318.variants.univ : P₁ Set.univ := by
  apply erdos_318.variants.infinite_AP
  refine ⟨0, 1, ?_, ?_⟩
  · simp
  · ext z
    simp

private lemma odd_eq_range :
    {n : ℕ | Odd n} = Set.range (fun k : ℕ ↦ 1 + k * 2) := by
  ext n
  constructor
  · rintro ⟨k, hk⟩
    change n = 2 * k + 1 at hk
    refine ⟨k, ?_⟩
    change 1 + k * 2 = n
    omega
  · rintro ⟨k, rfl⟩
    change Odd (1 + k * 2)
    exact ⟨k, by omega⟩

/-- The odd natural numbers have property `P₁`. -/
theorem erdos_318.variants.odd : P₁ {n : ℕ | Odd n} := by
  apply erdos_318.variants.infinite_AP
  refine ⟨1, 2, ?_, ?_⟩
  · apply ENat.card_eq_top.2
    exact Set.infinite_coe_iff.mpr <| by
      rw [odd_eq_range]
      exact Set.infinite_range_of_injective (by
        intro x y hxy
        change 1 + x * 2 = 1 + y * 2 at hxy
        omega)
  · rw [odd_eq_range]
    ext z
    simp

/-! ## The set of all squares -/

/-- The set of all squares does not have property `P₁`. -/
theorem erdos_318.variants.squares : ¬ P₁ ({n | IsSquare n}) := by
  simp only [P₁, not_forall, not_exists, not_and]
  refine ⟨fun n => if n = 1 then 1 else -1, fun h => ?_, fun h => ?_,
    fun x ⟨y, hy⟩ => ?_, fun S h hs => ?_⟩
  · have : (-1 : ℝ) = 1 := by
      simpa using congr_fun h ⟨4, ⟨⟨2, by grind⟩, by grind⟩⟩
    grind
  · have : 1 = (-1 : ℝ) := by
      simpa using congr_fun h ⟨1, ⟨IsSquare.one, by grind⟩⟩
    grind
  · by_cases x = 1 <;> grind
  by_cases h1 : 1 ∈ S
  · rw [← Finset.sum_erase_add S
      (fun n : ℕ => (if n = 1 then (1 : ℝ) else -1) / n) h1, add_comm,
      Finset.sum_congr rfl
      (g := fun n : ℕ => (-1 : ℝ) / n)]
    · simp only [↓reduceIte, Nat.cast_one, div_self one_ne_zero, ← ne_eq, div_eq_mul_one_div
        (-1 : ℝ), ← Finset.mul_sum, neg_one_mul (∑ x ∈ S.erase 1, 1 / (x : ℝ)),
        ← sub_eq_add_neg]
      apply ne_of_gt
      calc
        0 < 1 - (π ^ 2 / 6 - 1) := by
          have : π ^ 2 < 3.15 ^ 2 := by
            gcongr
            exact Real.pi_lt_d2
          linarith
        _ = 1 - (∑' n : ℕ, 1 / (n : ℝ) ^ 2 - 1) := by
          congr
          exact hasSum_zeta_two.tsum_eq.symm
        _ ≤ 1 - ∑ n ∈ S.erase 1, 1 / (n : ℝ) := by
          gcongr
          have hone : 1 = 1 / ((1 : ℕ) : ℝ) := by norm_num
          nth_rewrite 3 [hone]
          rw [le_sub_iff_add_le, Finset.sum_erase_add S _ h1]
          let S' := S.preimage (· ^ 2) (Function.Injective.injOn
            (Nat.pow_left_injective (by decide)))
          have hS' : S'.map ⟨(· ^ 2), Nat.pow_left_injective (by decide)⟩ = S := by
            apply Finset.coe_injective
            have hrange : (S : Set ℕ) ⊆ Set.range (· ^ 2) :=
              hs.trans (by simp [isSquare_iff_exists_sq, Set.subset_def])
            simpa [S', Set.image_preimage_eq_iff] using hrange
          rw [← hS', Finset.sum_map, Function.Embedding.coeFn_mk]
          simpa [Nat.cast_pow] using
            Summable.sum_le_tsum S' (fun _ _ => by positivity) (by simp)
    · intro _ _
      grind
  · suffices ∑ n ∈ S, (fun n ↦ if n = 1 then 1 else -1) n / (n : ℝ) < 0 by
      linarith
    refine Finset.sum_neg (fun p hp => ?_) h
    have hp1 : p ≠ 1 := by grind
    simp_all [neg_div, zero_lt_iff, (not_iff_not.2 mem_singleton_iff).1 (hs hp).2]

#print axioms singleton_two_has_P₁
#print axioms not_contain_single_even_as_stated
#print axioms contain_single_even_of_positive_and_odd
#print axioms densityCounterexample_hasDensity
#print axioms not_erdos_318
#print axioms erdos_318.variants.infinite_AP
#print axioms erdos_318.variants.univ
#print axioms erdos_318.variants.odd
#print axioms erdos_318.variants.squares

end Erdos318

alias _root_.Erdos318.erdos_318.parts.i := _root_.Erdos318.not_erdos_318
