/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Random-forcing facts (F4)–(F6) for the measure-algebra Boolean-valued model.
-/
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.Cylinders
import ErdosProblems.Erdos501.Flypitch4.ForcingRandom

set_option relaxedAutoImplicit true

/-!
# Random forcing over the random algebra: the units (F4) and (F5)

This file starts the proof that `𝔠⁺` random reals force `Erdos501_f` (`Main.lean`,
`erdos501_of_random`) by formalizing the random-forcing facts of the paper *"Erdős Problem 501 after adding ω₂ random reals"* (rev10) in
the form that matches the measure-algebra Boolean-valued model `V (randomAlgebra ι)` of Flypitch.
The paper's formalization plan has the units

* (F1) Theorems 2.1, 2.2 (σ-finite measure theory in ZFC), (F2) Theorems 3.1, 3.2 (the
  forcing-free certificate-to-independent-set theorem), (F3) Theorem 4.3 (Δ-system lemma;
  `DeltaSystem.lean`, proved),
* **(F4)** Theorems 4.1, 4.2 and 4.4: countable support and homogeneous Borel reading —
  Theorems 4.1 and 4.2 are proved **here**, Prop. 4.4 in `HomogeneousReading.lean`;
* **(F5)** Theorem 4.5: the isolated fresh-coordinate forcing argument — proved **here** at the
  level of Boolean values of events read from the generic point (see below);
* (F6) Theorem 5.1: assembly of the forcing data into the certificate interface (not yet).

Everything in this file is proved (no `sorry`).

Throughout, `ι` is an index type, `Ω ι = ι → (ℕ → Bool)` carries the fair-coin product measure
`μ_random ι` and `randomAlgebra ι` is its measure algebra.  A **profile**/**random real** at a
coordinate `α : ι` is `x ↦ x α ∈ 2^ω`; the coordinate blocks `P_α` of the paper are single
coordinates or *petals* `π : ℕ ↪ ι` here (`Ω ι ≅ 2^(ι × ω)`), which loses nothing.  `2^T` denotes
`T → (ℕ → Bool)` for a set of coordinates `T : Set ι`, with the product fair-coin measure
`μ_T = infinitePi (fun _ : T => cantorMeasure)`.

* **(F4) Theorem 4.1 — countable supports and Borel reading of names for reals.**
  `exists_countable_support`: every measurable `A ⊆ Ω ι` depends on countably many coordinates.
  `mkReal F hF` is the name (in `bSet (randomAlgebra ι)`) of the real `{n ∈ ω | F(ĝ) n = 1}`
  read off from the generic point `ĝ` by a measurable `F : Ω ι → 2^ω`, `genericReal α` is the
  generic real at the coordinate `α`; `exists_mkReal_bv_eq` / `exists_mkReal_restrict_bv_eq`:
  **every** name `ẋ` for a subset of `ω` is forced equal to `mkReal (F ∘ (·↾S))` for a countable
  `S ⊆ ι` and a Borel `F : 2^S → 2^ω` (the extensionality principle used,
  `eq_of_forall_of_nat_mem_eq`, holds in any Boolean-valued model).
* **(F4) Theorem 4.2 — factorization.**  For disjoint sets of coordinates `T`, `P` the
  restrictions `x ↦ x↾T` and `x ↦ x↾P` are independent (`indepFun_restrict_restrict`, i.e.
  `𝔹(T ⊔ P) = 𝔹(T) ⊗ 𝔹(P)`), the joint law is the product of the marginals
  (`map_restrict_prod_restrict`), and `x ↦ (x↾T, x↾P)` pulls the product measure algebra of
  `2^T × 2^P` back into the random algebra measure-preservingly (`μ_random_restrict_prod_restrict`);
  the same for a single coordinate `α ∉ T` (`indepFun_restrict_eval`, `map_restrict_prod_eval`,
  `μ_random_restrict_prod_eval`) and for a petal `π : ℕ ↪ ι` avoiding `T` (`map_comp_injective`,
  `indepFun_restrict_comp`, `map_restrict_prod_comp`), together with Fubini for the events
  `{x | (x↾T, Z x) ∈ B}` (`measure_restrict_prod_of_map`, `measure_restrict_prod_eval`,
  `measure_restrict_prod_comp`).
* **(F5) Theorem 4.5 — the isolated fresh-coordinate forcing argument.**  If
  `q = [{x | x↾T ∈ Q}] ≠ ⊥` and `B ⊆ 2^T × 2^P` is a Borel family whose fibres over `Q` have
  measure `≥ ε > 0` (a.s.), then for every coordinate `α ∉ T` (resp. petal `π` avoiding `T`) the
  event "`x↾T ∈ Q` and `(x↾T, x α) ∈ B`" has measure `≥ ε · μ_T(Q) > 0`
  (`measure_pos_of_fiber_pos_of_map`, `measure_pos_of_fiber_pos_ae`), i.e.
  `q ⊓ [{x | (x↾T, x α) ∈ B}] ≠ ⊥` in the random algebra (`bot_lt_inf_mk_of_fiber_pos`,
  `bot_lt_inf_mk_of_fiber_pos_comp`); an uncountable family of pairwise disjoint petals always
  contains one that is fresh over a countable `T` (`exists_mem_not_mem_of_countable`), whence
  `exists_fresh_of_fiber_pos` and `exists_fresh_petal_of_fiber_pos`: no condition can force all
  the profiles `ĝ ∘ π a`, `a ∈ J`, to avoid a set of positive measure coded from its support.  This
  is the Boolean-value computation of Lemma 4.5 (`⊩ ν*(Ż) = 1`).

What is *not* done here: the internal interpretation of Borel sets/codes in
`V (randomAlgebra ι)` — needed to state Lemma 4.5 literally as `⊩ ν*(Ż) = 1` and to identify the
class of the event `{x | (x↾T, ĝ ∘ π) ∈ B}` with the Boolean value `‖ż ∈ Ḃ‖` of a *name* `Ḃ`
for a Borel set — and (F6), Theorem 5.1.
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet
open scoped ENNReal Flypitch

universe u

namespace Flypitch.Erdos501.RandomForcing

variable {ι : Type}

/-! ### (F4a) Countable supports -/

/-- **(F4)** A measurable subset of `Ω ι = ι → 2^ω` depends only on countably many coordinates. -/
theorem exists_countable_support {A : Set (RandomAlgebra.Ω ι)} (hA : MeasurableSet A) :
    ∃ S : Set ι, S.Countable ∧ DependsOn (fun x => x ∈ A) S := by
  obtain ⟨S, t, hS, rfl⟩ := hA.eq_preimage_restrict_countable
  refine ⟨S, hS, fun x y hxy => ?_⟩
  simp only [mem_preimage]
  have : S.domRestrict x = S.domRestrict y := funext fun i => hxy i.1 i.2
  rw [this]

/-- Every element of the random algebra has a representative depending on countably many
coordinates. -/
theorem exists_rep_countable_support (b : randomAlgebra ι) :
    ∃ (A : Set (RandomAlgebra.Ω ι)) (hA : MeasurableSet A) (S : Set ι),
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) A hA = b ∧ S.Countable ∧
      DependsOn (fun x => x ∈ A) S := by
  obtain ⟨A, hA, rfl⟩ := MeasureAlgebra.exists_rep b
  obtain ⟨S, hS, hdep⟩ := exists_countable_support hA
  exact ⟨A, hA, S, rfl, hS, hdep⟩

/-! ### (F4b) Names for reals read off from the generic point -/

lemma measurableSet_bitF {Y : Type*} [MeasurableSpace Y] {F : Y → (ℕ → Bool)} (hF : Measurable F)
    (n : ℕ) : MeasurableSet {y | F y n = true} := by
  have h : Measurable (fun y : Y => F y n) := (measurable_pi_apply n).comp hF
  exact h (measurableSet_singleton true)

/-- The name of the real (subset of `ω`) `{n ∈ ω | F(ĝ) n = 1}` read off from the generic
point `ĝ` of `Ω ι` by the measurable function `F : Ω ι → 2^ω`: its `n`-th bit is the class of
the event `{x | F x n = true}`. -/
-- Definitionally `@set_of_indicator (randomAlgebra ι) _ omega (fun n => …)`; written out and
-- marked reducible so that `(mkReal F hF).type` reduces to `ULift ℕ` at reducible
-- transparency (Lean ≥ 4.34 `simp`), as for `cohen_real.mk` / `random_real.mk`.
@[reducible] noncomputable def mkReal (F : RandomAlgebra.Ω ι → (ℕ → Bool)) (hF : Measurable F) :
    bSet (randomAlgebra ι) :=
  ⟨ULift ℕ, fun n => of_nat n.down,
    fun n => MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | F x n.down = true}
      (measurableSet_bitF hF n.down)⟩

example (F : RandomAlgebra.Ω ι → (ℕ → Bool)) (hF : Measurable F) :
    mkReal F hF = @set_of_indicator (randomAlgebra ι) _ omega
      (fun n => MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | F x n.down = true}
        (measurableSet_bitF hF n.down)) := rfl

variable {F : RandomAlgebra.Ω ι → (ℕ → Bool)} (hF : Measurable F)

@[simp] lemma mkReal_type : (mkReal F hF).type = ULift ℕ := rfl
@[simp] lemma mkReal_func {n} : (mkReal F hF).func n = of_nat n.down := rfl
@[simp] lemma mkReal_bval {n} : (mkReal F hF).bval n =
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | F x n.down = true}
      (measurableSet_bitF hF n.down) := rfl

lemma mkReal_congr {G : RandomAlgebra.Ω ι → (ℕ → Bool)} (hG : Measurable G) (h : F = G) :
    mkReal F hF = mkReal G hG := by subst h; rfl

/-- `mkReal F hF` is (forced to be) a subset of `ω`. -/
lemma mkReal_definite {Γ : randomAlgebra ι} : Γ ≤ mkReal F hF ⊆ᴮ omega := by
  rw [subset_unfold]
  apply le_iInf; intro i
  rw [← deduction]
  simp only [mkReal_bval, mkReal_func]
  exact le_trans inf_le_left (le_trans le_top omega_definite)

/-- The Boolean value of `n ∈ mkReal F hF` is the class of the event `{x | F x n = true}`. -/
lemma mem_mkReal (n : ℕ) : (of_nat n ∈ᴮ mkReal F hF) =
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | F x n = true} (measurableSet_bitF hF n) := by
  rw [mem_unfold]
  apply le_antisymm
  · apply iSup_le; intro k
    by_cases hk : n = k.down
    · subst hk; simp only [mkReal_bval, mkReal_func]; exact inf_le_left
    · simp only [mkReal_bval, mkReal_func, of_nat_inj' hk, inf_bot_eq]; exact bot_le
  · apply le_iSup_of_le (ULift.up n)
    simp only [mkReal_bval, mkReal_func, bv_eq_refl, inf_top_eq, le_refl]

/-- The generic random real at the coordinate `α`: the name `{n ∈ ω | ĝ α n = 1}`. -/
noncomputable def genericReal (α : ι) : bSet (randomAlgebra ι) :=
  mkReal (fun x => x α) (measurable_pi_apply α)

/-- The bits of `genericReal α` are the random bits `χ α n` of `RandomAlgebra.lean`. -/
lemma genericReal_eq (α : ι) :
    genericReal α = @set_of_indicator (randomAlgebra ι) _ omega
      (fun n => RandomAlgebra.χ α n.down) := rfl

/-! ### Extensionality for names of subsets of `ω` (any Boolean algebra) -/

section extensionality

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

lemma mem_omega_eq (z : bSet 𝔹) : (z ∈ᴮ omega) = ⨆ n : ℕ, z =ᴮ of_nat n := by
  rw [mem_unfold]
  simp only [omega_bval, omega_func, top_inf_eq]
  exact le_antisymm (iSup_le fun i => le_iSup_of_le i.down le_rfl)
    (iSup_le fun n => le_iSup_of_le (ULift.up n) le_rfl)

/-- If `x ⊆ ω` and every natural number `n ∈ x` is also in `y`, then `z ∈ x → z ∈ y` for
every `z` (as Boolean values). -/
lemma mem_le_mem_of_subset_omega {x y : bSet 𝔹} (hx : ⊤ ≤ x ⊆ᴮ omega)
    (h : ∀ n : ℕ, (of_nat n ∈ᴮ x) ≤ (of_nat n ∈ᴮ y)) (z : bSet 𝔹) : z ∈ᴮ x ≤ z ∈ᴮ y := by
  have h1 : z ∈ᴮ x ≤ z ∈ᴮ omega := by
    rw [subset_unfold'] at hx
    exact imp_top_iff_le.mp (top_le_iff.mp (le_trans hx (iInf_le _ z)))
  calc z ∈ᴮ x = z ∈ᴮ x ⊓ z ∈ᴮ omega := (inf_eq_left.mpr h1).symm
    _ = z ∈ᴮ x ⊓ ⨆ n : ℕ, z =ᴮ of_nat n := by rw [mem_omega_eq]
    _ = ⨆ n : ℕ, z ∈ᴮ x ⊓ z =ᴮ of_nat n := inf_iSup_eq'
    _ ≤ ⨆ n : ℕ, of_nat n ∈ᴮ x ⊓ z =ᴮ of_nat n := by
        apply iSup_mono; intro n
        exact le_inf (le_trans (le_inf inf_le_right inf_le_left) subst_congr_mem_left) inf_le_right
    _ ≤ ⨆ n : ℕ, of_nat n ∈ᴮ y ⊓ z =ᴮ of_nat n := iSup_mono fun n => inf_le_inf_right _ (h n)
    _ ≤ z ∈ᴮ y := by
        apply iSup_le; intro n
        rw [inf_comm, bv_eq_symm]
        exact subst_congr_mem_left

/-- **Extensionality for subsets of `ω`**: two names for subsets of `ω` with the same Boolean
values of `n ∈ ·` for all `n : ℕ` are forced equal. -/
theorem eq_of_forall_of_nat_mem_eq {x y : bSet 𝔹} (hx : ⊤ ≤ x ⊆ᴮ omega) (hy : ⊤ ≤ y ⊆ᴮ omega)
    (h : ∀ n : ℕ, (of_nat n ∈ᴮ x) = (of_nat n ∈ᴮ y)) : ⊤ ≤ x =ᴮ y := by
  refine le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf; intro z
  apply le_inf
  · exact top_le_iff.mpr (imp_top_iff_le.mpr (mem_le_mem_of_subset_omega hx (fun n => (h n).le) z))
  · exact top_le_iff.mpr (imp_top_iff_le.mpr (mem_le_mem_of_subset_omega hy (fun n => (h n).ge) z))

end extensionality

/-! ### (F4) Borel reading of names for reals -/

/-- **(F4) Borel reading of names for reals.**  Every name `xdot` for a subset of `ω` in the
random-algebra model is forced equal to `mkReal F hF` for a Borel `F : Ω ι → 2^ω` depending on
countably many coordinates. -/
theorem exists_mkReal_bv_eq (xdot : bSet (randomAlgebra ι)) (hxdot : ⊤ ≤ xdot ⊆ᴮ omega) :
    ∃ (F : RandomAlgebra.Ω ι → (ℕ → Bool)) (hF : Measurable F) (S : Set ι),
      S.Countable ∧ DependsOn F S ∧ ⊤ ≤ xdot =ᴮ mkReal F hF := by
  classical
  choose A hA hAeq using fun n : ℕ => MeasureAlgebra.exists_rep (of_nat n ∈ᴮ xdot)
  choose S hS hdep using fun n : ℕ => exists_countable_support (hA n)
  let F : RandomAlgebra.Ω ι → ℕ → Bool := fun x n => if x ∈ A n then true else false
  have hF : Measurable F :=
    measurable_pi_iff.mpr fun n => Measurable.ite (hA n) measurable_const measurable_const
  refine ⟨F, hF, ⋃ n, S n, countable_iUnion hS, ?_, ?_⟩
  · intro x y hxy
    funext n
    have := hdep n (fun i hi => hxy i (mem_iUnion_of_mem n hi))
    simp only [F, this]
  · apply eq_of_forall_of_nat_mem_eq hxdot (mkReal_definite hF)
    intro n
    rw [mem_mkReal, ← hAeq n]
    congr 1
    ext x
    simp [F]

/-- **(F4) Borel reading, in the form of Lemma 4.1 of the paper**: every name `ẋ` for a subset
of `ω` is forced equal to the real read off from the generic point `ĝ` by `F(ĝ↾S)`, for a
*countable* set of coordinates `S ⊆ ι` and a Borel `F : 2^S → 2^ω` (here `2^S = S → (ℕ → Bool)`). -/
theorem exists_mkReal_restrict_bv_eq (xdot : bSet (randomAlgebra ι)) (hx : ⊤ ≤ xdot ⊆ᴮ omega) :
    ∃ (S : Set ι) (F : (S → (ℕ → Bool)) → (ℕ → Bool)) (hF : Measurable F),
      S.Countable ∧ ⊤ ≤ xdot =ᴮ mkReal (F ∘ S.domRestrict) (hF.comp S.measurable_restrict) := by
  classical
  obtain ⟨F, hF, S, hS, hdep, heq⟩ := exists_mkReal_bv_eq xdot hx
  -- extend a point of `2^S` by the constant `false` outside `S`
  let ext : (S → (ℕ → Bool)) → RandomAlgebra.Ω ι :=
    fun t i => if h : i ∈ S then t ⟨i, h⟩ else fun _ => false
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ S
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  have hcomp : (F ∘ ext) ∘ S.domRestrict = F := by
    funext x
    show F (ext (S.domRestrict x)) = F x
    apply hdep
    intro i hi
    simp [ext, hi]
  refine ⟨S, F ∘ ext, hF.comp hext, hS, ?_⟩
  rw [mkReal_congr _ hF hcomp]
  exact heq

/-! ### (F5) Factorization: restrictions to disjoint sets of coordinates are independent -/

variable (T : Set ι) (α : ι)

/-- The marginal of `μ_random ι` on the coordinates in `T` is again a fair-coin product. -/
theorem map_restrict :
    (RandomAlgebra.μ_random ι).map T.domRestrict =
      Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) := by
  unfold RandomAlgebra.μ_random
  exact Measure.infinitePi_map_restrict' _

/-- The marginal of `μ_random ι` on the coordinate `α` is the fair-coin measure on Cantor space. -/
theorem map_eval : (RandomAlgebra.μ_random ι).map (fun x => x α) = RandomAlgebra.cantorMeasure := by
  unfold RandomAlgebra.μ_random
  exact Measure.infinitePi_map_eval _ α

/-- **(F5)** The coordinates of the generic point are mutually independent. -/
theorem iIndepFun_eval : iIndepFun (fun (i : ι) (x : RandomAlgebra.Ω ι) => x i) (RandomAlgebra.μ_random ι) := by
  unfold RandomAlgebra.μ_random
  exact iIndepFun_infinitePi (X := fun (_ : ι) => (id : (ℕ → Bool) → (ℕ → Bool)))
    (fun _ => measurable_id)

/-- The σ-algebra generated by the `T`-restriction is the one generated by the coordinates in
`T` (the sub-σ-algebra `𝔹(T)` of the paper). -/
theorem comap_restrict_eq :
    MeasurableSpace.comap (T.domRestrict (π := fun _ => ℕ → Bool)) MeasurableSpace.pi =
      ⨆ i ∈ T, MeasurableSpace.comap (fun x : RandomAlgebra.Ω ι => x i) MeasurableSpace.pi := by
  unfold MeasurableSpace.pi
  rw [MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  rw [iSup_subtype]
  rfl

/-- **(F5), Lemma 4.2 of the paper.**  For disjoint sets of coordinates `T`, `P`, the
`T`-restriction and the `P`-restriction are independent (`𝔹(T ⊔ P) = 𝔹(T) ⊗ 𝔹(P)`). -/
theorem indepFun_restrict_restrict {T P : Set ι} (hTP : Disjoint T P) :
    IndepFun (T.domRestrict (π := fun _ => ℕ → Bool)) (P.domRestrict (π := fun _ => ℕ → Bool))
      (RandomAlgebra.μ_random ι) := by
  have h := iIndepFun_eval (ι := ι)
  rw [iIndepFun_iff_iIndep] at h
  have h2 := indep_iSup_of_disjoint (h_indep := h)
    (h_le := fun i => (measurable_pi_apply i : Measurable fun x : RandomAlgebra.Ω ι => x i).comap_le)
    (S := T) (T := P) hTP
  rw [IndepFun_iff_Indep]
  convert h2 using 1
  · exact comap_restrict_eq T
  · exact comap_restrict_eq P

/-- **(F5)** For `α ∉ T`, the `T`-restriction and the `α`-th coordinate are independent. -/
theorem indepFun_restrict_eval (hα : α ∉ T) :
    IndepFun (T.domRestrict (π := fun _ => ℕ → Bool)) (fun x : RandomAlgebra.Ω ι => x α)
      (RandomAlgebra.μ_random ι) := by
  have h := iIndepFun_eval (ι := ι)
  rw [iIndepFun_iff_iIndep] at h
  have h2 := indep_iSup_of_disjoint (h_indep := h)
    (h_le := fun i => (measurable_pi_apply i : Measurable fun x : RandomAlgebra.Ω ι => x i).comap_le)
    (S := T) (T := {α}) (disjoint_singleton_right.mpr hα)
  rw [IndepFun_iff_Indep]
  convert h2 using 1
  · exact comap_restrict_eq T
  · rw [iSup_singleton]

/-- **(F5)** The joint law of `(x↾T, x↾P)`, `T ∩ P = ∅`, is the product of the marginals. -/
theorem map_restrict_prod_restrict {T P : Set ι} (hTP : Disjoint T P) :
    (RandomAlgebra.μ_random ι).map (fun x => (T.domRestrict x, P.domRestrict x)) =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod
        (Measure.infinitePi (fun _ : P => RandomAlgebra.cantorMeasure)) := by
  rw [← map_restrict T, ← map_restrict P]
  exact (indepFun_iff_map_prod_eq_prod_map_map (T.measurable_restrict).aemeasurable
    (P.measurable_restrict).aemeasurable).mp (indepFun_restrict_restrict hTP)

/-- **(F5)** The measure of a `(T, P)`-event `{x | (x↾T, x↾P) ∈ B}` is the product measure of `B`;
i.e. pulling back along `x ↦ (x↾T, x↾P)` is a measure-preserving embedding of the measure algebra
of `2^T × 2^P` into the random algebra (Lemma 4.2). -/
theorem μ_random_restrict_prod_restrict {T P : Set ι} (hTP : Disjoint T P)
    {B : Set ((T → (ℕ → Bool)) × (P → (ℕ → Bool)))} (hB : MeasurableSet B) :
    RandomAlgebra.μ_random ι {x | (T.domRestrict x, P.domRestrict x) ∈ B} =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod
        (Measure.infinitePi (fun _ : P => RandomAlgebra.cantorMeasure)) B := by
  have hm : Measurable (fun x : RandomAlgebra.Ω ι => (T.domRestrict x, P.domRestrict x)) :=
    (T.measurable_restrict).prodMk (P.measurable_restrict)
  rw [show {x : RandomAlgebra.Ω ι | (T.domRestrict x, P.domRestrict x) ∈ B} =
      (fun x : RandomAlgebra.Ω ι => (T.domRestrict x, P.domRestrict x)) ⁻¹' B from rfl,
    ← Measure.map_apply hm hB, map_restrict_prod_restrict hTP]

/-- **(F5)** The law of a *petal* `x ↦ (x (π n))ₙ`, `π : ℕ ↪ ι`, is the fair-coin product measure on
`2^ℕ = ℕ → 2^ω` (relabelling of the coordinates along `π`). -/
theorem map_comp_injective {π : ℕ → ι} (hπ : Function.Injective π) :
    (RandomAlgebra.μ_random ι).map (fun x n => x (π n)) =
      Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure) := by
  have h : iIndepFun (fun n (x : RandomAlgebra.Ω ι) => x (π n)) (RandomAlgebra.μ_random ι) :=
    (iIndepFun_eval (ι := ι)).precomp hπ
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun n => measurable_pi_apply (π n))] at h
  refine h.trans ?_
  congr 1
  funext n
  exact map_eval (π n)

/-- **(F5)** For a petal `π : ℕ → ι` avoiding `T`, the `T`-restriction and the petal are
independent. -/
theorem indepFun_restrict_comp {T : Set ι} {π : ℕ → ι} (hπT : ∀ n, π n ∉ T) :
    IndepFun (T.domRestrict (π := fun _ => ℕ → Bool)) (fun x : RandomAlgebra.Ω ι => fun n => x (π n))
      (RandomAlgebra.μ_random ι) := by
  have h := indepFun_restrict_restrict (T := T) (P := Set.range π)
    (Set.disjoint_left.mpr fun t ht ⟨n, hn⟩ => hπT n (by rw [hn]; exact ht))
  have h' := h.comp measurable_id
    (measurable_pi_lambda (fun y : (Set.range π → (ℕ → Bool)) => fun n => y ⟨π n, ⟨n, rfl⟩⟩)
      fun n => measurable_pi_apply _)
  exact h'

/-- **(F5)** The joint law of `(x↾T, (x (π n))ₙ)` for a petal `π : ℕ ↪ ι` avoiding `T` is the
product of the marginals (`𝔹(T ⊔ P_α) = 𝔹(T) ⊗ 𝔹(P_α)`). -/
theorem map_restrict_prod_comp {T : Set ι} {π : ℕ → ι} (hπ : Function.Injective π)
    (hπT : ∀ n, π n ∉ T) :
    (RandomAlgebra.μ_random ι).map (fun x => (T.domRestrict x, fun n => x (π n))) =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod
        (Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)) := by
  rw [← map_restrict T, ← map_comp_injective hπ]
  exact (indepFun_iff_map_prod_eq_prod_map_map (T.measurable_restrict).aemeasurable
    (measurable_pi_lambda _ fun n => measurable_pi_apply (π n)).aemeasurable).mp
    (indepFun_restrict_comp hπT)

/-- **(F5)** The joint law of `(x↾T, x α)` is the product of the marginals. -/
theorem map_restrict_prod_eval (hα : α ∉ T) :
    (RandomAlgebra.μ_random ι).map (fun x => (T.domRestrict x, x α)) =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod
        RandomAlgebra.cantorMeasure := by
  rw [← map_restrict T, ← map_eval α]
  exact (indepFun_iff_map_prod_eq_prod_map_map (T.measurable_restrict).aemeasurable
    (measurable_pi_apply α).aemeasurable).mp (indepFun_restrict_eval T α hα)

/-- **(F5)** The measure of an event `{x | (x↾T, x α) ∈ B}` is the product measure of `B`. -/
theorem μ_random_restrict_prod_eval (hα : α ∉ T)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B) :
    RandomAlgebra.μ_random ι {x | (T.domRestrict x, x α) ∈ B} =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod
        RandomAlgebra.cantorMeasure B := by
  have hm : Measurable (fun x : RandomAlgebra.Ω ι => (T.domRestrict x, x α)) :=
    (T.measurable_restrict).prodMk (measurable_pi_apply α)
  rw [show {x : RandomAlgebra.Ω ι | (T.domRestrict x, x α) ∈ B} =
      (fun x : RandomAlgebra.Ω ι => (T.domRestrict x, x α)) ⁻¹' B from rfl,
    ← Measure.map_apply hm hB, map_restrict_prod_eval T α hα]

/-! ### Fubini and positivity for a `T`-restriction paired with an independent variable -/

section general

variable {W : Type} [MeasurableSpace W] {ν : Measure W} [SFinite ν] {Z : RandomAlgebra.Ω ι → W}

/-- **(F5), Fubini** (general form).  If the joint law of `(x↾T, Z x)` is `μ_T ⊗ ν`, the measure of
`{x | (x↾T, Z x) ∈ B}` is the integral over `t ∈ 2^T` of the `ν`-measure of the fibre `B_t`. -/
theorem measure_restrict_prod_of_map (hZ : Measurable Z)
    (hmap : (RandomAlgebra.μ_random ι).map (fun x => (T.domRestrict x, Z x)) =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod ν)
    {B : Set ((T → (ℕ → Bool)) × W)} (hB : MeasurableSet B) :
    RandomAlgebra.μ_random ι {x | (T.domRestrict x, Z x) ∈ B} =
      ∫⁻ t, ν (Prod.mk t ⁻¹' B)
        ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)) := by
  have hm : Measurable (fun x : RandomAlgebra.Ω ι => (T.domRestrict x, Z x)) :=
    (T.measurable_restrict).prodMk hZ
  rw [show {x : RandomAlgebra.Ω ι | (T.domRestrict x, Z x) ∈ B} =
      (fun x : RandomAlgebra.Ω ι => (T.domRestrict x, Z x)) ⁻¹' B from rfl,
    ← Measure.map_apply hm hB, hmap, Measure.prod_apply hB]

/-- **(F6)/(F5)** (general form).  If the joint law of `(x↾T, Z x)` is `μ_T ⊗ ν`, `Q ⊆ 2^T` has
positive measure and almost every fibre `B_t`, `t ∈ Q`, has `ν`-measure `≥ ε > 0`, then the event
"`x↾T ∈ Q` and `(x↾T, Z x) ∈ B`" has measure `≥ ε · μ_T(Q) > 0`. -/
theorem measure_pos_of_fiber_pos_of_map (hZ : Measurable Z)
    (hmap : (RandomAlgebra.μ_random ι).map (fun x => (T.domRestrict x, Z x)) =
      (Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)).prod ν)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × W)} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ ν (Prod.mk t ⁻¹' B)) :
    0 < RandomAlgebra.μ_random ι {x | T.domRestrict x ∈ Q ∧ (T.domRestrict x, Z x) ∈ B} := by
  set μT := Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) with hμT
  have hset : {x : RandomAlgebra.Ω ι | T.domRestrict x ∈ Q ∧ (T.domRestrict x, Z x) ∈ B} =
      {x : RandomAlgebra.Ω ι | (T.domRestrict x, Z x) ∈ (Q ×ˢ univ) ∩ B} := by
    ext x; simp
  rw [hset, measure_restrict_prod_of_map T hZ hmap ((hQ.prod MeasurableSet.univ).inter hB)]
  -- the fibre over `t` is `B_t` if `t ∈ Q` and `∅` otherwise
  have hfibre : ∀ t, ν (Prod.mk t ⁻¹' ((Q ×ˢ univ) ∩ B)) =
      Q.indicator (fun t => ν (Prod.mk t ⁻¹' B)) t := by
    intro t
    by_cases ht : t ∈ Q
    · rw [indicator_of_mem ht]
      congr 1
      ext z; simp [ht]
    · rw [indicator_of_notMem ht]
      have : Prod.mk t ⁻¹' ((Q ×ˢ univ) ∩ B) = ∅ := by
        ext z; simp [ht]
      rw [this, measure_empty]
  simp_rw [hfibre]
  calc (0 : ℝ≥0∞) < ε * μT Q := ENNReal.mul_pos hε.ne' hQpos.ne'
    _ = ∫⁻ t, Q.indicator (fun _ => ε) t ∂μT := by rw [lintegral_indicator_const hQ, mul_comm]
    _ ≤ ∫⁻ t, Q.indicator (fun t => ν (Prod.mk t ⁻¹' B)) t ∂μT := by
        apply lintegral_mono_ae
        refine hfib.mono fun t ht => ?_
        by_cases htQ : t ∈ Q
        · simp only [indicator_of_mem htQ]; exact ht htQ
        · simp only [indicator_of_notMem htQ, le_refl]

end general

/-- **(F5), Fubini.**  The measure of an event `{x | (x↾T, x α) ∈ B}` is the integral over
`t ∈ 2^T` of the fair-coin measure of the fibre `B_t ⊆ 2^ω`. -/
theorem measure_restrict_prod_eval (hα : α ∉ T)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B) :
    RandomAlgebra.μ_random ι {x | (T.domRestrict x, x α) ∈ B} =
      ∫⁻ t, RandomAlgebra.cantorMeasure (Prod.mk t ⁻¹' B)
        ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)) :=
  measure_restrict_prod_of_map T (measurable_pi_apply α) (map_restrict_prod_eval T α hα) hB

/-- **(F5), Fubini** for a petal `π : ℕ ↪ ι` avoiding `T`. -/
theorem measure_restrict_prod_comp {π : ℕ → ι} (hπ : Function.Injective π) (hπT : ∀ n, π n ∉ T)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))} (hB : MeasurableSet B) :
    RandomAlgebra.μ_random ι {x | (T.domRestrict x, fun n => x (π n)) ∈ B} =
      ∫⁻ t, Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure) (Prod.mk t ⁻¹' B)
        ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)) :=
  measure_restrict_prod_of_map T (measurable_pi_lambda _ fun n => measurable_pi_apply (π n))
    (map_restrict_prod_comp hπ hπT) hB

/-! ### (F5) The isolated fresh-coordinate forcing argument (Theorem 4.5) -/

/-- **(F5)** If `Q ⊆ 2^T` has positive measure and almost every fibre `B_t`, `t ∈ Q`, of the
Borel family `B ⊆ 2^T × 2^ω` has measure `≥ ε > 0`, then for `α ∉ T` the event
"`x↾T ∈ Q` and `(x↾T, x α) ∈ B`" has measure `≥ ε · μ_T(Q) > 0`.  (The a.e. form is the one
matching "`q ⊩ ν(Ḃ) > ε`", which only gives `ν(B_t) > ε` for almost every `t ∈ [q]`.) -/
theorem measure_pos_of_fiber_pos_ae (hα : α ∉ T)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ RandomAlgebra.cantorMeasure (Prod.mk t ⁻¹' B)) :
    0 < RandomAlgebra.μ_random ι {x | T.domRestrict x ∈ Q ∧ (T.domRestrict x, x α) ∈ B} :=
  measure_pos_of_fiber_pos_of_map T (measurable_pi_apply α) (map_restrict_prod_eval T α hα)
    hQ hB hε hQpos hfib

/-- **(F5)**, pointwise form of `measure_pos_of_fiber_pos_ae`. -/
theorem measure_pos_of_fiber_pos (hα : α ∉ T)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ t ∈ Q, ε ≤ RandomAlgebra.cantorMeasure (Prod.mk t ⁻¹' B)) :
    0 < RandomAlgebra.μ_random ι {x | T.domRestrict x ∈ Q ∧ (T.domRestrict x, x α) ∈ B} :=
  measure_pos_of_fiber_pos_ae T α hα hQ hB hε hQpos (Filter.Eventually.of_forall hfib)

/-- **(F5), Boolean-value form.**  Let `q` be the class of an event with support `T` (i.e.
`q = [{x | x↾T ∈ Q}]`) of positive measure, and let `B ⊆ 2^T × 2^ω` be a Borel family whose
fibres over `Q` have measure `≥ ε > 0` (almost surely).  Then for every coordinate `α ∉ T` the
element `q ⊓ [{x | (x↾T, x α) ∈ B}]` of the random algebra is nonzero.  (Once `Ḃ` is the name
for a Borel set read from `B`, the second factor is `‖ĝ α ∈ Ḃ‖`; this is the computation of
Lemma 4.5.) -/
theorem bot_lt_inf_mk_of_fiber_pos (hα : α ∉ T)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ RandomAlgebra.cantorMeasure (Prod.mk t ⁻¹' B)) :
    ⊥ < MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | T.domRestrict x ∈ Q} (T.measurable_restrict hQ) ⊓
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, x α) ∈ B}
        ((T.measurable_restrict.prodMk (measurable_pi_apply α)) hB) := by
  rw [MeasureAlgebra.mk_inf, MeasureAlgebra.bot_lt_iff_meas_pos, MeasureAlgebra.meas_mk]
  exact measure_pos_of_fiber_pos_ae T α hα hQ hB hε hQpos hfib

/-- **(F5), Boolean-value form for a petal** `π : ℕ ↪ ι` avoiding the support `T` (the profile
`ż_α = π_α⁻¹(Ġ↾P_α) ∈ 2^P` of the paper, with `P = ℕ`): `q ⊓ [{x | (x↾T, (x (π n))ₙ) ∈ B}] ≠ ⊥`. -/
theorem bot_lt_inf_mk_of_fiber_pos_comp {π : ℕ → ι} (hπ : Function.Injective π)
    (hπT : ∀ n, π n ∉ T)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure) (Prod.mk t ⁻¹' B)) :
    ⊥ < MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | T.domRestrict x ∈ Q} (T.measurable_restrict hQ) ⊓
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, fun n => x (π n)) ∈ B}
        ((T.measurable_restrict.prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (π n))) hB) := by
  rw [MeasureAlgebra.mk_inf, MeasureAlgebra.bot_lt_iff_meas_pos, MeasureAlgebra.meas_mk]
  exact measure_pos_of_fiber_pos_of_map T (measurable_pi_lambda _ fun n => measurable_pi_apply (π n))
    (map_restrict_prod_comp hπ hπT) hQ hB hε hQpos hfib

/-- **(F6)** In an uncountable index set there is always a coordinate outside a given countable
set of coordinates (a *fresh* coordinate). -/
theorem exists_not_mem_of_countable (hι : ¬ Countable ι) {S : Set ι} (hS : S.Countable) :
    ∃ α : ι, α ∉ S := by
  by_contra h
  apply hι
  have hS' : S = univ := eq_univ_iff_forall.mpr fun α => by_contra fun hα => h ⟨α, hα⟩
  exact countable_univ_iff.mp (hS' ▸ hS)

/-- An uncountable set of coordinates `J` always has an element outside a countable set `T`. -/
theorem exists_mem_not_mem_of_countable {J : Set ι} (hJ : ¬ J.Countable) {T : Set ι}
    (hT : T.Countable) : ∃ α ∈ J, α ∉ T := by
  by_contra h
  apply hJ
  exact hT.mono fun α hα => by_contra fun hαT => h ⟨α, hα, hαT⟩

/-- **(F6), fresh-profile fullness (Lemma 4.5 of the paper), Boolean-value form.**  Let `J ⊆ ι`
be an uncountable set of coordinates (the petals `P_α`, `α ∈ J`), let `q = [{x | x↾T ∈ Q}] ≠ ⊥`
be a condition with countable support `T`, and let `B ⊆ 2^T × 2^ω` be a Borel family whose fibres
over `Q` have measure `≥ ε > 0` (a.s.).  Then some coordinate `α ∈ J` is fresh over `T` and
`q ⊓ [{x | (x↾T, x α) ∈ B}] ≠ ⊥`: no condition `q` can force that all the profiles `ĝ α`,
`α ∈ J`, avoid a set of positive measure coded from `T`. -/
theorem exists_fresh_of_fiber_pos {J : Set ι} (hJ : ¬ J.Countable) {T : Set ι} (hT : T.Countable)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ RandomAlgebra.cantorMeasure (Prod.mk t ⁻¹' B)) :
    ∃ α ∈ J, α ∉ T ∧
      ⊥ < MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | T.domRestrict x ∈ Q}
          (T.measurable_restrict hQ) ⊓
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, x α) ∈ B}
          ((T.measurable_restrict.prodMk (measurable_pi_apply α)) hB) := by
  obtain ⟨α, hαJ, hαT⟩ := exists_mem_not_mem_of_countable hJ hT
  exact ⟨α, hαJ, hαT, bot_lt_inf_mk_of_fiber_pos T α hαT hQ hB hε hQpos hfib⟩

/-- **(F5), Theorem 4.5 (fresh-profile fullness), reading-level form.**  Let `(π a)_{a ∈ J}` be
uncountably many pairwise disjoint petals `π a : ℕ ↪ ι` (the output of the homogeneous reading,
Prop. 4.4), let `q = [{x | x↾T ∈ Q}] ≠ ⊥` be a condition with countable support `T`, and let
`B ⊆ 2^T × 2^ℕ` be a Borel family whose fibres over `Q` have measure `≥ ε > 0` (a.s.).  Then some
petal `π a`, `a ∈ J`, avoids `T` (is *fresh* over `T`) and `q ⊓ [{x | (x↾T, ĝ ∘ π a) ∈ B}] ≠ ⊥`:
no condition can force the profiles `ż_a = ĝ ∘ π a`, `a ∈ J`, to avoid a set of positive
measure coded from its support.  Once names for Borel sets are available, this is exactly
"`⊩ ν*(Ż) = 1`" (Lemma 4.5 of the paper). -/
theorem exists_fresh_petal_of_fiber_pos {A : Type} {J : Set A} (hJ : ¬ J.Countable)
    {π : A → ℕ → ι} (hπ : ∀ a, Function.Injective (π a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b)))
    {T : Set ι} (hT : T.Countable)
    {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q)
    {B : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))} (hB : MeasurableSet B)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hQpos : 0 < Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q)
    (hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure) (Prod.mk t ⁻¹' B)) :
    ∃ a ∈ J, (∀ n, π a n ∉ T) ∧
      ⊥ < MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | T.domRestrict x ∈ Q}
          (T.measurable_restrict hQ) ⊓
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, fun n => x (π a n)) ∈ B}
          ((T.measurable_restrict.prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (π a n)))
            hB) := by
  -- only countably many petals meet the countable set `T`
  have hbad : {a | ∃ n, π a n ∈ T}.Countable := by
    have hsub : {a | ∃ n, π a n ∈ T} ⊆ ⋃ t ∈ T, {a | t ∈ Set.range (π a)} := by
      rintro a ⟨n, hn⟩
      exact Set.mem_biUnion hn ⟨n, rfl⟩
    refine (hT.biUnion fun t _ => ?_).mono hsub
    apply Set.Subsingleton.countable
    intro a ha b hb
    by_contra hab
    exact Set.disjoint_left.mp (hdisj a b hab) ha hb
  obtain ⟨a, haJ, ha⟩ := exists_mem_not_mem_of_countable hJ hbad
  have hπT : ∀ n, π a n ∉ T := fun n hn => ha ⟨n, hn⟩
  exact ⟨a, haJ, hπT, bot_lt_inf_mk_of_fiber_pos_comp T (hπ a) hπT hQ hB hε hQpos hfib⟩

end Flypitch.Erdos501.RandomForcing
