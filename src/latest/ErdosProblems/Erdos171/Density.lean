import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Uniform density on finite types

This file collects the elementary finite-probability identities used in the
formalization of the density Hales--Jewett theorem.  The definitions take values in
`ℝ`; this is convenient for the density-increment estimates, while the proofs reduce
to exact finite sums.
-/

open scoped BigOperators

namespace Erdos171

section Density

variable {α β : Type*}

/-- The uniform average of a real-valued function on a finite type. -/
noncomputable def average [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

/-- The density of a finset in its ambient finite type, as a real number. -/
noncomputable def density [Fintype α] (A : Finset α) : ℝ :=
  (A.card : ℝ) / Fintype.card α

@[simp]
theorem average_eq_sum_div_card [Fintype α] (f : α → ℝ) :
    average f = (∑ x, f x) / Fintype.card α := by
  simp [average, Fintype.expect_eq_sum_div_card]

@[simp]
theorem density_eq_card_div_card [Fintype α] (A : Finset α) :
    density A = (A.card : ℝ) / Fintype.card α := by
  rfl

theorem density_eq_coe_dens [Fintype α] (A : Finset α) :
    density A = (A.dens : ℝ) := by
  rw [density_eq_card_div_card, Finset.nnratCast_dens]

@[simp]
theorem density_empty [Fintype α] : density (∅ : Finset α) = 0 := by
  simp [density]

@[simp]
theorem density_univ [Fintype α] [Nonempty α] :
    density (Finset.univ : Finset α) = 1 := by
  simp [density]

theorem density_nonneg [Fintype α] (A : Finset α) : 0 ≤ density A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem density_le_one [Fintype α] (A : Finset α) : density A ≤ 1 := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      letI := h
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr h =>
      letI := h
      rw [density, div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_univ A

theorem density_mono [Fintype α] {A B : Finset α} (h : A ⊆ B) :
    density A ≤ density B := by
  unfold density
  gcongr

@[simp]
theorem density_eq_zero [Fintype α] (A : Finset α) :
    density A = 0 ↔ A = ∅ := by
  cases isEmpty_or_nonempty α with
  | inl h =>
      letI := h
      have hA : A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hA]
  | inr h =>
      letI := h
      simp [density]

@[simp]
theorem density_pos [Fintype α] (A : Finset α) :
    0 < density A ↔ A.Nonempty := by
  constructor
  · intro h
    rw [Finset.nonempty_iff_ne_empty]
    intro hA
    simpa [hA] using h
  · intro h
    rw [lt_iff_le_and_ne]
    refine ⟨density_nonneg A, ?_⟩
    intro hd
    exact h.ne_empty ((density_eq_zero A).1 hd.symm)

theorem average_const [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α ↦ c) = c := by
  simp [average, Fintype.expect_const]

theorem average_add [Fintype α] (f g : α → ℝ) :
    average (fun x ↦ f x + g x) = average f + average g := by
  simp [average, Finset.expect_add_distrib]

theorem average_sub [Fintype α] (f g : α → ℝ) :
    average (fun x ↦ f x - g x) = average f - average g := by
  simp [average, Finset.expect_sub_distrib]

theorem average_mul_const [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun x ↦ f x * c) = average f * c := by
  simp [average, Finset.expect_mul]

theorem average_const_mul [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x ↦ c * f x) = c * average f := by
  simp [average, Finset.mul_expect]

/-- Fubini's identity for the uniform average on a finite product. -/
theorem average_product [Fintype α] [Fintype β] (f : α × β → ℝ) :
    average f = average fun a ↦ average fun b ↦ f (a, b) := by
  unfold average
  rw [← Finset.univ_product_univ]
  exact Finset.expect_product Finset.univ Finset.univ f

/-- Uniform finite averages commute. -/
theorem average_comm [Fintype α] [Fintype β] (f : α → β → ℝ) :
    average (fun a ↦ average fun b ↦ f a b) =
      average (fun b ↦ average fun a ↦ f a b) := by
  unfold average
  exact Finset.expect_comm Finset.univ Finset.univ f

/-- The elementary second-moment inequality for a uniform finite average. -/
theorem sq_average_le_average_sq [Fintype α] (f : α → ℝ) :
    (average f) ^ 2 ≤ average fun x ↦ (f x) ^ 2 := by
  simpa only [average_eq_sum_div_card, Finset.card_univ] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ) (f := f))

/-- The average of a function over a specified finite subset. -/
noncomputable def averageOn (A : Finset α) (f : α → ℝ) : ℝ :=
  𝔼 x ∈ A, f x

@[simp]
theorem averageOn_eq_sum_div_card (A : Finset α) (f : α → ℝ) :
    averageOn A f = (∑ x ∈ A, f x) / A.card := by
  simp [averageOn, Finset.expect_eq_sum_div_card]

/-- Some point of a nonempty finite set attains at least the average on that set. -/
theorem exists_averageOn_le {A : Finset α} (hA : A.Nonempty) (f : α → ℝ) :
    ∃ x ∈ A, averageOn A f ≤ f x := by
  by_contra! h
  have hsum : (∑ x ∈ A, f x) < ∑ _x ∈ A, averageOn A f :=
    Finset.sum_lt_sum_of_nonempty hA (fun x hx ↦ h x hx)
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  rw [averageOn_eq_sum_div_card, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcancel : (A.card : ℝ) * ((∑ x ∈ A, f x) / A.card) = ∑ x ∈ A, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

theorem average_mono [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  simp only [average_eq_sum_div_card]
  gcongr with x
  exact h x

theorem average_nonneg [Fintype α] {f : α → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ average f := by
  simpa only [average, Finset.expect_const_zero] using
    average_mono (f := fun _ : α ↦ 0) (g := f) h

theorem average_le_const [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : ∀ x, f x ≤ c) : average f ≤ c := by
  simpa [average_const] using average_mono (f := f) (g := fun _ ↦ c) h

theorem const_le_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : ∀ x, c ≤ f x) : c ≤ average f := by
  simpa [average_const] using average_mono (f := fun _ ↦ c) (g := f) h

/-- Some value of a function is at least its uniform average. -/
theorem exists_average_le [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, average f ≤ f x := by
  by_contra! h
  have hsum : (∑ x, f x) < ∑ _x : α, average f :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ ↦ h x)
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  rw [average_eq_sum_div_card, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hcancel : (Fintype.card α : ℝ) *
      ((∑ x, f x) / Fintype.card α) = ∑ x, f x := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard
  rw [hcancel] at hsum
  exact hsum.false

/-- Some value of a function is at most its uniform average. -/
theorem exists_le_average [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, f x ≤ average f := by
  obtain ⟨x, hx⟩ := exists_average_le (fun x ↦ -f x)
  have hneg : average (fun x ↦ -f x) = -average f := by
    simp [average_eq_sum_div_card]
    ring
  exact ⟨x, by rw [hneg] at hx; linarith⟩

theorem exists_ge_of_le_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : c ≤ average f) : ∃ x, c ≤ f x := by
  obtain ⟨x, hx⟩ := exists_average_le f
  exact ⟨x, h.trans hx⟩

theorem exists_gt_of_lt_average [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : c < average f) : ∃ x, c < f x := by
  obtain ⟨x, hx⟩ := exists_average_le f
  exact ⟨x, h.trans_le hx⟩

/-- A fibre of a subset of a product, with the first coordinate fixed. -/
noncomputable def fiber [Fintype β] (A : Finset (α × β)) (a : α) : Finset β :=
  by
    classical
    exact Finset.univ.filter fun b ↦ (a, b) ∈ A

@[simp]
theorem mem_fiber [Fintype β] (A : Finset (α × β)) (a : α) (b : β) :
    b ∈ fiber A a ↔ (a, b) ∈ A := by
  classical
  simp [fiber]

/-- Exact fibrewise counting for a subset of a product. -/
theorem card_eq_sum_card_fiber [Fintype α] [Fintype β] (A : Finset (α × β)) :
    A.card = ∑ a, (fiber A a).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := A) (t := Finset.univ) (f := Prod.fst) (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 hp
    apply (mem_fiber A a p.2).2
    rw [← hp'.2]
    simpa using hp'.1
  · intro p hp q hq hpq
    apply Prod.ext
    · have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simpa [hp', hq']
    · exact hpq
  · intro b hb
    refine ⟨(a, b), ?_, rfl⟩
    have hb' : (a, b) ∈ A := (mem_fiber A a b).1 hb
    simp [hb']

/-- Uniform density on a product is the average of the densities of its fibres. -/
theorem density_eq_average_fiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    density A = average fun a ↦ density (fiber A a) := by
  cases isEmpty_or_nonempty α with
  | inl hα =>
      letI := hα
      simp [density_eq_card_div_card, average_eq_sum_div_card]
  | inr hα =>
      letI := hα
      cases isEmpty_or_nonempty β with
      | inl hβ =>
          letI := hβ
          simp [density_eq_card_div_card, average_eq_sum_div_card]
      | inr hβ =>
          letI := hβ
          rw [density_eq_card_div_card, average_eq_sum_div_card]
          rw [card_eq_sum_card_fiber]
          simp only [density_eq_card_div_card]
          rw [Fintype.card_prod]
          push_cast
          rw [← Finset.sum_div]
          have ha : (Fintype.card α : ℝ) ≠ 0 := by positivity
          have hb : (Fintype.card β : ℝ) ≠ 0 := by positivity
          field_simp

/-- The indicator of a finset has average equal to its density. -/
theorem average_indicator [Fintype α] [DecidableEq α] (A : Finset α) :
    average (fun x ↦ if x ∈ A then (1 : ℝ) else 0) = density A := by
  classical
  simp [average_eq_sum_div_card, density_eq_card_div_card,
    Finset.sum_boole]

/-- The exact uniform average of a two-valued function. -/
theorem average_piecewise_const [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (a b : ℝ) :
    average (fun x ↦ if x ∈ A then a else b) =
      density A * a + (1 - density A) * b := by
  let ι : α → ℝ := fun x ↦ if x ∈ A then 1 else 0
  have hpoint : (fun x ↦ if x ∈ A then a else b) =
      fun x ↦ ι x * a + (1 - ι x) * b := by
    funext x
    simp only [ι]
    split <;> ring
  rw [hpoint, average_add, average_mul_const, average_mul_const,
    average_sub, average_const, average_indicator]

/-- A pointwise upper bound on and off a set gives the corresponding upper bound
for the uniform average. -/
theorem average_le_density_mul_add [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (a b : ℝ)
    (hA : ∀ x ∈ A, f x ≤ a) (hAc : ∀ x ∉ A, f x ≤ b) :
    average f ≤ density A * a + (1 - density A) * b := by
  rw [← average_piecewise_const A a b]
  apply average_mono
  intro x
  by_cases hx : x ∈ A
  · simpa [hx] using hA x hx
  · simpa [hx] using hAc x hx

/-- A pointwise lower bound on and off a set gives the corresponding lower bound
for the uniform average. -/
theorem density_mul_add_le_average [Fintype α] [Nonempty α] [DecidableEq α]
    (A : Finset α) (f : α → ℝ) (a b : ℝ)
    (hA : ∀ x ∈ A, a ≤ f x) (hAc : ∀ x ∉ A, b ≤ f x) :
    density A * a + (1 - density A) * b ≤ average f := by
  rw [← average_piecewise_const A a b]
  apply average_mono
  intro x
  by_cases hx : x ∈ A
  · simpa [hx] using hA x hx
  · simpa [hx] using hAc x hx

/-- The set on which a real-valued function is at least a given threshold. -/
noncomputable def superlevel [Fintype α] (f : α → ℝ) (c : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter fun x ↦ c ≤ f x

@[simp]
theorem mem_superlevel [Fintype α] (f : α → ℝ) (c : ℝ) (x : α) :
    x ∈ superlevel f c ↔ c ≤ f x := by
  classical
  simp [superlevel]

/-- Quantitative averaging: if `f ≤ B` and its average is at least `μ`, then
the density of the set where `f ≥ c` is at least `(μ-c)/(B-c)`. -/
theorem density_superlevel_ge [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {μ c B : ℝ} (havg : μ ≤ average f)
    (hub : ∀ x, f x ≤ B) (hcB : c < B) :
    (μ - c) / (B - c) ≤ density (superlevel f c) := by
  have havg' : average f ≤ density (superlevel f c) * B +
      (1 - density (superlevel f c)) * c := by
    apply average_le_density_mul_add
    · intro x _
      exact hub x
    · intro x hx
      exact le_of_lt (not_le.1 (by simpa using hx))
  rw [div_le_iff₀ (sub_pos.2 hcB)]
  nlinarith

/-- The particularly useful half-threshold form of quantitative averaging. -/
theorem half_le_density_superlevel [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (havg : δ ≤ average f)
    (hub : ∀ x, f x ≤ 1) :
    δ / 2 ≤ density (superlevel f (δ / 2)) := by
  have havg' : average f ≤ density (superlevel f (δ / 2)) +
      (1 - density (superlevel f (δ / 2))) * (δ / 2) := by
    convert average_le_density_mul_add (superlevel f (δ / 2)) f 1 (δ / 2)
      (fun x _ ↦ hub x) (fun x hx ↦ le_of_lt (not_le.1 (by simpa using hx))) using 1 <;> ring
  have hdle : density (superlevel f (δ / 2)) ≤ 1 := density_le_one _
  have hd0 : 0 ≤ density (superlevel f (δ / 2)) := density_nonneg _
  have hδle : δ ≤ 1 := havg.trans (average_le_const hub)
  nlinarith

/-- Markov's inequality for the finite uniform distribution. -/
theorem density_superlevel_le [Fintype α] [Nonempty α] [DecidableEq α]
    (f : α → ℝ) {μ c : ℝ} (havg : average f ≤ μ)
    (hnonneg : ∀ x, 0 ≤ f x) (hc : 0 < c) :
    density (superlevel f c) ≤ μ / c := by
  have hlower : density (superlevel f c) * c ≤ average f := by
    convert density_mul_add_le_average (superlevel f c) f c 0
      (fun x hx ↦ (mem_superlevel f c x).1 hx)
      (fun x _ ↦ hnonneg x) using 1 <;> ring
  rw [le_div_iff₀ hc]
  exact hlower.trans havg

/-- Turn a set into the finset of all its elements in a finite ambient type. -/
noncomputable def setFinset [Fintype α] (A : Set α) : Finset α := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ A

@[simp]
theorem mem_setFinset [Fintype α] (A : Set α) (x : α) :
    x ∈ setFinset A ↔ x ∈ A := by
  classical
  simp [setFinset]

/-- Uniform density of a set in a finite ambient type. -/
noncomputable def setDensity [Fintype α] (A : Set α) : ℝ :=
  density (setFinset A)

@[simp]
theorem setDensity_empty [Fintype α] : setDensity (∅ : Set α) = 0 := by
  classical
  simp [setDensity, setFinset]

@[simp]
theorem setDensity_univ [Fintype α] [Nonempty α] :
    setDensity (Set.univ : Set α) = 1 := by
  classical
  simp [setDensity, setFinset]

theorem setDensity_nonneg [Fintype α] (A : Set α) : 0 ≤ setDensity A :=
  density_nonneg _

theorem setDensity_le_one [Fintype α] (A : Set α) : setDensity A ≤ 1 :=
  density_le_one _

theorem setDensity_mono [Fintype α] {A B : Set α} (h : A ⊆ B) :
    setDensity A ≤ setDensity B := by
  apply density_mono
  intro x hx
  exact (mem_setFinset B x).2 (h (mem_setFinset A x |>.1 hx))

/-- A fibre of a set in a product. -/
def setFiber (A : Set (α × β)) (a : α) : Set β :=
  {b | (a, b) ∈ A}

@[simp]
theorem mem_setFiber (A : Set (α × β)) (a : α) (b : β) :
    b ∈ setFiber A a ↔ (a, b) ∈ A := Iff.rfl

/-- Set-valued version of the exact product/fibre density identity. -/
theorem setDensity_eq_average_fiber [Fintype α] [Fintype β]
    (A : Set (α × β)) :
    setDensity A = average fun a ↦ setDensity (setFiber A a) := by
  classical
  rw [setDensity, density_eq_average_fiber]
  apply congrArg average
  funext a
  unfold setDensity
  congr 1
  ext b
  simp [setFiber]

/-- Density is preserved by equivalences of finite ambient types. -/
theorem density_map_equiv [Fintype α] [Fintype β] (e : α ≃ β) (A : Finset α) :
    density (A.map e.toEmbedding) = density A := by
  simp [density, Fintype.card_congr e]

/-- The density of a Cartesian product is the product of the two densities. -/
theorem density_product [Fintype α] [Fintype β] (A : Finset α) (B : Finset β) :
    density (A ×ˢ B) = density A * density B := by
  simp [density_eq_card_div_card, Finset.card_product, Fintype.card_prod]
  ring

/-! ## Incidence Fubini identities -/

/-- The column of a finset of pairs at a fixed second coordinate. -/
noncomputable def columnFiber [Fintype α] (A : Finset (α × β)) (b : β) : Finset α := by
  classical
  exact Finset.univ.filter fun a ↦ (a, b) ∈ A

@[simp]
theorem mem_columnFiber [Fintype α] (A : Finset (α × β)) (a : α) (b : β) :
    a ∈ columnFiber A b ↔ (a, b) ∈ A := by
  classical
  simp [columnFiber]

/-- The product-density identity counted by columns rather than rows. -/
theorem density_eq_average_columnFiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    density A = average fun b ↦ density (columnFiber A b) := by
  classical
  let e : α × β ≃ β × α := Equiv.prodComm α β
  let A' : Finset (β × α) := A.map e.toEmbedding
  have hmap : density A' = density A := by
    exact density_map_equiv e A
  have hfiber (b : β) : fiber A' b = columnFiber A b := by
    ext a
    simp [A', e]
  calc
    density A = density A' := hmap.symm
    _ = average (fun b ↦ density (fiber A' b)) := density_eq_average_fiber A'
    _ = average (fun b ↦ density (columnFiber A b)) := by
      apply congrArg average
      funext b
      rw [hfiber]

/-- Double-counting incidences: average row density equals average column density. -/
theorem average_density_fiber_eq_columnFiber [Fintype α] [Fintype β]
    (A : Finset (α × β)) :
    average (fun a ↦ density (fiber A a)) =
      average (fun b ↦ density (columnFiber A b)) := by
  rw [← density_eq_average_fiber, ← density_eq_average_columnFiber]

/-- The row set of a binary relation. -/
def relationRow (R : α → β → Prop) (a : α) : Set β :=
  {b | R a b}

/-- The column set of a binary relation. -/
def relationColumn (R : α → β → Prop) (b : β) : Set α :=
  {a | R a b}

@[simp]
theorem mem_relationRow (R : α → β → Prop) (a : α) (b : β) :
    b ∈ relationRow R a ↔ R a b := Iff.rfl

@[simp]
theorem mem_relationColumn (R : α → β → Prop) (a : α) (b : β) :
    a ∈ relationColumn R b ↔ R a b := Iff.rfl

/-- Predicate/set form of finite incidence double-counting. -/
theorem average_setDensity_relationRow_eq_relationColumn [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    average (fun a ↦ setDensity (relationRow R a)) =
      average (fun b ↦ setDensity (relationColumn R b)) := by
  classical
  let A : Finset (α × β) := setFinset {p | R p.1 p.2}
  have hrow (a : α) : setFinset (relationRow R a) = fiber A a := by
    ext b
    simp [A, relationRow]
  have hcolumn (b : β) : setFinset (relationColumn R b) = columnFiber A b := by
    ext a
    simp [A, relationColumn]
  simpa only [setDensity, hrow, hcolumn] using average_density_fiber_eq_columnFiber A

/-- The average density of pairwise row intersections is the average square of
the column densities.  This is the second-moment form of incidence Fubini. -/
theorem average_pairwise_intersection_relationRow [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    average (fun p : α × α ↦
      setDensity (relationRow R p.1 ∩ relationRow R p.2)) =
      average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) := by
  classical
  let R₂ : α × α → β → Prop := fun p b ↦ R p.1 b ∧ R p.2 b
  have hfubini := average_setDensity_relationRow_eq_relationColumn R₂
  calc
    average (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2)) =
        average (fun p ↦ setDensity (relationRow R₂ p)) := by
      apply congrArg average
      funext p
      congr 1
    _ = average (fun b ↦ setDensity (relationColumn R₂ b)) := hfubini
    _ = average (fun b ↦ setDensity {p : α × α | R p.1 b ∧ R p.2 b}) := by
      apply congrArg average
      funext b
      congr 1
    _ = average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) := by
      apply congrArg average
      funext b
      unfold setDensity
      have hprod : setFinset {p : α × α | R p.1 b ∧ R p.2 b} =
          setFinset (relationColumn R b) ×ˢ setFinset (relationColumn R b) := by
        ext p
        simp [relationColumn]
      rw [hprod, density_product, pow_two]

/-- Nested-average version of `average_pairwise_intersection_relationRow`. -/
theorem average_average_intersection_relationRow [Fintype α] [Fintype β]
    (R : α → β → Prop) :
    average (fun a ↦ average fun a' ↦
      setDensity (relationRow R a ∩ relationRow R a')) =
      average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) := by
  calc
    average (fun a ↦ average fun a' ↦
        setDensity (relationRow R a ∩ relationRow R a')) =
        average (fun p : α × α ↦
          setDensity (relationRow R p.1 ∩ relationRow R p.2)) :=
      (average_product (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2))).symm
    _ = average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) :=
      average_pairwise_intersection_relationRow R

/-- A relation of average row density `δ` has average pairwise-row-intersection
density at least `δ²`. -/
theorem sq_average_relationRow_le_average_pairwise_intersection
    [Fintype α] [Fintype β] (R : α → β → Prop) :
    (average (fun a ↦ setDensity (relationRow R a))) ^ 2 ≤
      average (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2)) := by
  calc
    (average (fun a ↦ setDensity (relationRow R a))) ^ 2 =
        (average (fun b ↦ setDensity (relationColumn R b))) ^ 2 := by
      rw [average_setDensity_relationRow_eq_relationColumn]
    _ ≤ average (fun b ↦ (setDensity (relationColumn R b)) ^ 2) :=
      sq_average_le_average_sq _
    _ = average (fun p : α × α ↦
        setDensity (relationRow R p.1 ∩ relationRow R p.2)) :=
      (average_pairwise_intersection_relationRow R).symm

section Lattice

variable [Fintype α] [DecidableEq α]

theorem density_union_add_density_inter (A B : Finset α) :
    density (A ∪ B) + density (A ∩ B) = density A + density B := by
  simp only [density_eq_coe_dens]
  exact_mod_cast Finset.dens_union_add_dens_inter A B

theorem density_sdiff_add_density_inter (A B : Finset α) :
    density (A \ B) + density (A ∩ B) = density A := by
  simp only [density_eq_coe_dens]
  exact_mod_cast Finset.dens_sdiff_add_dens_inter A B

theorem density_inter_add_density_sdiff (A B : Finset α) :
    density (A ∩ B) + density (A \ B) = density A := by
  rw [add_comm, density_sdiff_add_density_inter]

/-- The elementary union-bound form most useful in density arguments. -/
theorem density_add_sub_one_le_density_inter (A B : Finset α) :
    density A + density B - 1 ≤ density (A ∩ B) := by
  have h := density_union_add_density_inter A B
  have hu := density_le_one (A ∪ B)
  linarith

theorem density_union_le_add (A B : Finset α) :
    density (A ∪ B) ≤ density A + density B := by
  have h := density_union_add_density_inter A B
  have hi := density_nonneg (A ∩ B)
  linarith

theorem density_inter_le_left (A B : Finset α) : density (A ∩ B) ≤ density A :=
  density_mono Finset.inter_subset_left

theorem density_inter_le_right (A B : Finset α) : density (A ∩ B) ≤ density B :=
  density_mono Finset.inter_subset_right

theorem density_compl [Nonempty α] (A : Finset α) :
    density (Finset.univ \ A) = 1 - density A := by
  have h := density_sdiff_add_density_inter Finset.univ A
  simp at h
  unfold density
  linarith

end Lattice

end Density

end Erdos171
