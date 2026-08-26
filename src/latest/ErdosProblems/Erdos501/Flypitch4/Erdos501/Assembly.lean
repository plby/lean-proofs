/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The recursion of Theorem 3.2 on names, part 2 (step S6 of `PLAN.md`): the name `X` of the
infinite independent set and the proof that it is forced to be one.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Recursion

set_option relaxedAutoImplicit true

/-!
# The infinite independent set, as a name (step S6, part 2)

From the recursion of `Recursion.lean` (candidates `cand j k = (m, a) ∈ ℤ × D` and measurable
selectors `sel j` at each stage `j`), we build the name

  `Xname = {testPoint (cand j k).1 (d (cand j k).2) | j k}`, with `‖(j, k)-th element ∈ X‖ = [sel j = k]`,

and prove that it is (forced to be) an infinite subset of `Rdot` which is independent for `A`:

* infinite (`infinite_Xname`), through the name `fname` of the injection `j ↦ x_j`;
* independent (`independent_Xname`): on the piece where `(m, a)` is chosen at stage `i` and
  `(m', a')` at stage `j ≠ i`, the recursion guarantees `xx (t_i) ∉ envSet E (ĝ↾R) t_j`, and the
  homogeneous envelope of `A(testPoint m' (d a'))` is exactly `envSet E (ĝ↾R) t_j` on the cover event
  (P3), so `x_i ∉ A(x_j)` by (P4).

The main theorem `exists_infinite_independent_name` packages this as
`Γ ≤ ⨆ X, X ∈ᴮ 𝒫 Rdot ⊓ (Sem.infinite X ⊓ Sem.independent A X)`.
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice
open scoped ENNReal Flypitch

namespace Flypitch.Erdos501.RandomForcing

open ZFCCore

variable {ι : Type}

section assembly

variable {D : Type} {J : Set D} {π : D → ℕ → ι} {R : Set ι}
  {E : Root R × Prof → ℤ → ℕ → ℝ × ℝ}
  (hE : Measurable E) (hJ : ¬ J.Countable) (hπ : ∀ a, Function.Injective (π a))
  (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b))) (hR : R.Countable)
  {d : D → ι}

/-- The candidates at stage `j`. -/
noncomputable def cand (j : ℕ) : ℕ → ℤ × D :=
  (choiceOf hE hJ hπ hdisj (stage hE hJ hπ hdisj hR j)).1

/-- The selector at stage `j`. -/
noncomputable def sel (j : ℕ) : RandomAlgebra.Ω ι → ℕ :=
  (choiceOf hE hJ hπ hdisj (stage hE hJ hπ hdisj hR j)).2

lemma measurable_sel (j : ℕ) : Measurable (sel hE hJ hπ hdisj hR j) :=
  (choiceOf_spec hE hJ hπ hdisj _).2.1

lemma cand_mem_J (j k : ℕ) : (cand hE hJ hπ hdisj hR j k).2 ∈ J :=
  (choiceOf_spec hE hJ hπ hdisj _).1 k

lemma tj_eq (j : ℕ) (x : RandomAlgebra.Ω ι) :
    tj hE hJ hπ hdisj hR j x =
      ((cand hE hJ hπ hdisj hR j (sel hE hJ hπ hdisj hR j x)).1,
        fun n => x (π (cand hE hJ hπ hdisj hR j (sel hE hJ hπ hdisj hR j x)).2 n)) := rfl

variable (d) in
/-- The `(j, k)`-th candidate test point, as an internal real. -/
noncomputable def tp (j k : ℕ) : bSet (randomAlgebra ι) :=
  testPoint (cand hE hJ hπ hdisj hR j k).1 (d (cand hE hJ hπ hdisj hR j k).2)

/-- The event "the `(j, k)`-th candidate is chosen". -/
def selEvent (j k : ℕ) : Set (RandomAlgebra.Ω ι) := {x | sel hE hJ hπ hdisj hR j x = k}

lemma measurableSet_selEvent (j k : ℕ) : MeasurableSet (selEvent hE hJ hπ hdisj hR j k) :=
  (measurable_sel hE hJ hπ hdisj hR j) (measurableSet_singleton k)

/-- The Boolean value of "the `(j, k)`-th candidate is chosen". -/
noncomputable def selVal (j k : ℕ) : randomAlgebra ι :=
  MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (selEvent hE hJ hπ hdisj hR j k)
    (measurableSet_selEvent hE hJ hπ hdisj hR j k)

variable (d) in
/-- **The name of the independent set** `X = {x_j | j}`, `x_j` the test point chosen at stage `j`. -/
noncomputable def Xname : bSet (randomAlgebra ι) :=
  ⟨ℕ × ℕ, fun jk => tp hE hJ hπ hdisj hR d jk.1 jk.2, fun jk => selVal hE hJ hπ hdisj hR jk.1 jk.2⟩

variable (d) in
/-- The name of the function `j ↦ x_j`. -/
noncomputable def fname : bSet (randomAlgebra ι) :=
  ⟨ℕ × ℕ, fun jk => pair (of_nat jk.1) (tp hE hJ hπ hdisj hR d jk.1 jk.2),
    fun jk => selVal hE hJ hπ hdisj hR jk.1 jk.2⟩

@[simp] lemma Xname_type : (Xname hE hJ hπ hdisj hR d).type = (ℕ × ℕ) := rfl
@[simp] lemma Xname_func (jk : (Xname hE hJ hπ hdisj hR d).type) :
    (Xname hE hJ hπ hdisj hR d).func jk = tp hE hJ hπ hdisj hR d jk.1 jk.2 := rfl
@[simp] lemma Xname_bval (jk : (Xname hE hJ hπ hdisj hR d).type) :
    (Xname hE hJ hπ hdisj hR d).bval jk = selVal hE hJ hπ hdisj hR jk.1 jk.2 := rfl
@[simp] lemma fname_type : (fname hE hJ hπ hdisj hR d).type = (ℕ × ℕ) := rfl
@[simp] lemma fname_func (jk : (fname hE hJ hπ hdisj hR d).type) :
    (fname hE hJ hπ hdisj hR d).func jk = pair (of_nat jk.1) (tp hE hJ hπ hdisj hR d jk.1 jk.2) := rfl
@[simp] lemma fname_bval (jk : (fname hE hJ hπ hdisj hR d).type) :
    (fname hE hJ hπ hdisj hR d).bval jk = selVal hE hJ hπ hdisj hR jk.1 jk.2 := rfl

/-! ### Pointwise facts -/

variable (hπ0 : ∀ a, π a 0 = d a)

include hπ0 in
/-- On the event `sel j x = k`, the reading of the `(j, k)`-th test point is `xx (t_j x)`. -/
lemma reading_tp {j k : ℕ} {x : RandomAlgebra.Ω ι} (hx : sel hE hJ hπ hdisj hR j x = k) :
    ((cand hE hJ hπ hdisj hR j k).1 : ℝ) + binExp (x (d (cand hE hJ hπ hdisj hR j k).2)) =
      xx (tj hE hJ hπ hdisj hR j x) := by
  rw [tj_eq, hx, xx]
  simp only [hπ0]

/-- The good points of the recursion. -/
def good (x : RandomAlgebra.Ω ι) : Prop :=
  ∀ j, μS ((stage hE hJ hπ hdisj hR j).C x) = ∞ ∧
    tj hE hJ hπ hdisj hR j x ∈ QX E (stage hE hJ hπ hdisj hR j).C x

lemma ae_good' : ∀ᵐ x ∂(RandomAlgebra.μ_random ι), good hE hJ hπ hdisj hR x := ae_good hE hJ hπ hdisj hR

/-- For good `x` and `i ≠ j`, `xx (t_i x) ∉ envSet E (x↾R) (t_j x)`. -/
lemma xx_tj_not_mem_envSet {x : RandomAlgebra.Ω ι} (hx : good hE hJ hπ hdisj hR x) {i j : ℕ}
    (hij : i ≠ j) :
    xx (tj hE hJ hπ hdisj hR i x) ∉ envSet E (R.domRestrict x) (tj hE hJ hπ hdisj hR j x) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have := tj_not_mem_removedX hE hJ hπ hdisj hR hx h
    intro hmem
    exact this (Or.inl (Or.inl hmem))
  · have := tj_not_mem_removedX hE hJ hπ hdisj hR hx h
    intro hmem
    exact this (Or.inl (Or.inr hmem))

/-- For good `x` and `i ≠ j`, `xx (t_i x) ≠ xx (t_j x)`. -/
lemma xx_tj_ne {x : RandomAlgebra.Ω ι} (hx : good hE hJ hπ hdisj hR x) {i j : ℕ} (hij : i ≠ j) :
    xx (tj hE hJ hπ hdisj hR i x) ≠ xx (tj hE hJ hπ hdisj hR j x) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have := tj_not_mem_removedX hE hJ hπ hdisj hR hx h
    intro heq
    exact this (Or.inr heq.symm)
  · have := tj_not_mem_removedX hE hJ hπ hdisj hR hx h
    intro heq
    exact this (Or.inr heq)

/-- The cover event of the homogeneous envelopes at `x`, in terms of `aE`/`bE`. -/
lemma coverEvent_env_iff (a : D) (m : ℤ) (x : RandomAlgebra.Ω ι) :
    x ∈ coverEvent (seqFun (envA E hE (π a) m)) (seqFun (envB E hE (π a) m)) ↔
      (R.domRestrict x, fun k => x (π a k)) ∈ coverEvent (aE E m) (bE E m) := Iff.rfl

/-! ### The Boolean-valued properties of `Xname` -/

/-- Every element of `Xname` is a real. -/
lemma Xname_subset_Rdot {Γ : randomAlgebra ι} : Γ ≤ Xname hE hJ hπ hdisj hR d ⊆ᴮ Rdot := by
  rw [subset_unfold]
  refine le_iInf fun jk => ?_
  rw [← deduction]
  exact inf_le_right.trans (by simp only [Xname_func]; exact testPoint_mem_Rdot _ _)

/-- Selection is total: `⨆ k, selVal j k = ⊤`. -/
lemma iSup_selVal (j : ℕ) : (⨆ k, selVal hE hJ hπ hdisj hR j k) = ⊤ := by
  unfold selVal
  rw [MeasureAlgebra.iSup_mk]
  refine mk_eq_top_of_forall _ fun x => ?_
  exact mem_iUnion.mpr ⟨sel hE hJ hπ hdisj hR j x, rfl⟩

/-- Distinct candidates at the same stage are never both chosen. -/
lemma selVal_inf_selVal {j k k' : ℕ} (hkk' : k ≠ k') :
    selVal hE hJ hπ hdisj hR j k ⊓ selVal hE hJ hπ hdisj hR j k' = ⊥ := by
  unfold selVal
  rw [MeasureAlgebra.mk_inf, MeasureAlgebra.bot_def]
  refine MeasureAlgebra.mk_congr ?_
  ext x
  simp only [selEvent, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  exact hkk' (h1.symm.trans h2)

/-- Membership in `Xname`, unfolded. -/
lemma mem_Xname (x : bSet (randomAlgebra ι)) :
    (x ∈ᴮ Xname hE hJ hπ hdisj hR d) =
      ⨆ jk : ℕ × ℕ, selVal hE hJ hπ hdisj hR jk.1 jk.2 ⊓ x =ᴮ tp hE hJ hπ hdisj hR d jk.1 jk.2 := by
  rw [mem_unfold]; rfl

/-- Membership in `fname`, unfolded. -/
lemma mem_fname (y : bSet (randomAlgebra ι)) :
    (y ∈ᴮ fname hE hJ hπ hdisj hR d) =
      ⨆ jk : ℕ × ℕ, selVal hE hJ hπ hdisj hR jk.1 jk.2 ⊓
        y =ᴮ pair (of_nat jk.1) (tp hE hJ hπ hdisj hR d jk.1 jk.2) := by
  rw [mem_unfold]; rfl

/-- The `(j, k)`-th test point is in `Xname` on `selVal j k`. -/
lemma selVal_le_mem_Xname (j k : ℕ) :
    selVal hE hJ hπ hdisj hR j k ≤ tp hE hJ hπ hdisj hR d j k ∈ᴮ Xname hE hJ hπ hdisj hR d := by
  rw [mem_Xname]
  refine le_iSup_of_le (j, k) ?_
  simp only [bv_eq_refl, inf_top_eq, le_refl]

/-- `pair (of_nat j) (tp j k) ∈ fname` on `selVal j k`. -/
lemma selVal_le_app_fname (j k : ℕ) :
    selVal hE hJ hπ hdisj hR j k ≤
      Sem.app (fname hE hJ hπ hdisj hR d) (of_nat j) (tp hE hJ hπ hdisj hR d j k) := by
  rw [Sem.app, mem_fname]
  refine le_iSup_of_le (j, k) ?_
  simp only [bv_eq_refl, inf_top_eq, le_refl]

/-- Elimination of `app fname n u`. -/
lemma app_fname_elim {Γ b : randomAlgebra ι} {n u : bSet (randomAlgebra ι)}
    (h : Γ ≤ Sem.app (fname hE hJ hπ hdisj hR d) n u)
    (H : ∀ (j k : ℕ) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ selVal hE hJ hπ hdisj hR j k →
      Γ' ≤ n =ᴮ of_nat j → Γ' ≤ u =ᴮ tp hE hJ hπ hdisj hR d j k → Γ' ≤ b) : Γ ≤ b := by
  rw [Sem.app, mem_fname] at h
  refine bv_iSup_elim h fun jk Γ' h' hjk => ?_
  have h1 := pair_eq_pair_iff.mp (bv_and_right hjk)
  exact H jk.1 jk.2 Γ' h' (bv_and_left hjk) h1.1 h1.2

include hπ0 in
/-- Two test points chosen at different stages are (forced to be) different reals: the Boolean
value of their equality is disjoint from the selection events. -/
lemma selVal_inf_eq_tp_le_bot {j k j' k' : ℕ} (hjj' : j ≠ j') :
    selVal hE hJ hπ hdisj hR j k ⊓ selVal hE hJ hπ hdisj hR j' k' ⊓
      (tp hE hJ hπ hdisj hR d j k =ᴮ tp hE hJ hπ hdisj hR d j' k') ≤ ⊥ := by
  unfold selVal tp testPoint
  rw [bv_eq_realName, MeasureAlgebra.mk_inf, MeasureAlgebra.mk_inf, MeasureAlgebra.bot_def,
    MeasureAlgebra.mk_le_mk, MeasureAlgebra.ae_le_set_iff_ae_imp]
  filter_upwards [ae_good' hE hJ hπ hdisj hR] with x hx
  rintro ⟨⟨h1, h2⟩, h3⟩
  simp only [selEvent, mem_setOf_eq] at h1 h2 h3
  rw [reading_tp hE hJ hπ hdisj hR hπ0 h1, reading_tp hE hJ hπ hdisj hR hπ0 h2] at h3
  exact absurd h3 (xx_tj_ne hE hJ hπ hdisj hR hx hjj')

include hπ0 in
/-- **`Xname` is infinite**: `ω` injects into it via `fname`. -/
theorem infinite_Xname {Γ : randomAlgebra ι} : Γ ≤ Sem.infinite (Xname hE hJ hπ hdisj hR d) := by
  rw [Sem.infinite]
  refine le_iSup_of_le (fname hE hJ hπ hdisj hR d) (le_inf ?_ ?_)
  · -- `fname : ω → Xname` is a function
    rw [Sem.isFun]
    refine le_iInf fun n => ?_
    rw [bv_imp_iff]; intro Γ₁ _ hn
    rw [mem_omega_eq] at hn
    refine bv_iSup_elim hn fun j Γ₂ h₂ hnj => ?_
    -- split according to the selection at stage `j`
    have htot : Γ₂ ≤ ⨆ k, selVal hE hJ hπ hdisj hR j k := by
      rw [iSup_selVal]; exact le_top
    refine bv_iSup_elim htot fun k Γ₃ h₃ hk => ?_
    refine le_iSup_of_le (tp hE hJ hπ hdisj hR d j k) (le_inf ?_ (le_inf ?_ ?_))
    · exact hk.trans (selVal_le_mem_Xname hE hJ hπ hdisj hR j k)
    · have hnj' : Γ₃ ≤ of_nat j =ᴮ n := by rw [bv_eq_symm]; exact h₃.trans hnj
      exact app_congr_arg hnj' (hk.trans (selVal_le_app_fname hE hJ hπ hdisj hR j k))
    · refine le_iInf fun y' => ?_
      rw [bv_imp_iff]; intro Γ₄ h₄ hy'
      refine app_fname_elim hE hJ hπ hdisj hR hy' fun j' k' Γ₅ h₅ hsel' hnj' hy'' => ?_
      have hjj' : Γ₅ ≤ of_nat j =ᴮ of_nat j' := by
        have := le_inf ((h₅.trans (h₄.trans h₃)).trans hnj) hnj'
        rw [bv_eq_symm (x := n) (y := of_nat j)] at this
        exact this.trans bv_eq_trans
      by_cases hj : j = j'
      · subst hj
        by_cases hk' : k = k'
        · subst hk'; exact hy''
        · have : Γ₅ ≤ ⊥ := by
            have := le_inf ((h₅.trans h₄).trans hk) hsel'
            rw [selVal_inf_selVal hE hJ hπ hdisj hR hk'] at this
            exact this
          exact this.trans bot_le
      · rw [of_nat_inj' hj] at hjj'
        exact hjj'.trans bot_le
  · -- injectivity
    refine le_iInf fun n => ?_
    rw [bv_imp_iff]; intro Γ₁ _ hn
    refine le_iInf fun m => ?_
    rw [bv_imp_iff]; intro Γ₂ h₂ hm
    refine le_iInf fun u => ?_
    rw [bv_imp_iff]; intro Γ₃ h₃ hnu
    rw [bv_imp_iff]; intro Γ₄ h₄ hmu
    refine app_fname_elim hE hJ hπ hdisj hR (h₄.trans hnu) fun j k Γ₅ h₅ hsel hnj hu => ?_
    refine app_fname_elim hE hJ hπ hdisj hR (h₅.trans hmu) fun j' k' Γ₆ h₆ hsel' hmj' hu' => ?_
    by_cases hj : j = j'
    · subst hj
      have := le_inf (h₆.trans hnj) hmj'
      rw [bv_eq_symm (x := m) (y := of_nat j)] at this
      exact this.trans bv_eq_trans
    · -- impossible: `u` would be two different reals
      have h1 : Γ₆ ≤ tp hE hJ hπ hdisj hR d j k =ᴮ tp hE hJ hπ hdisj hR d j' k' := by
        have := le_inf (h₆.trans hu) hu'
        rw [bv_eq_symm (x := u) (y := tp hE hJ hπ hdisj hR d j k)] at this
        exact this.trans bv_eq_trans
      have h2 : Γ₆ ≤ ⊥ :=
        (le_inf (le_inf (h₆.trans hsel) hsel') h1).trans
          (selVal_inf_eq_tp_le_bot hE hJ hπ hdisj hR hπ0 hj)
      exact h2.trans bot_le

include hπ0 in
/-- **`Xname` is independent for `A`**: for `x ≠ y` in `X`, `x ∉ A(y)`.

The hypotheses are the conclusions (P3)/(P4) of `exists_homogeneous_envelopes`: for `a ∈ J` and
`m : ℤ`, the value `A(testPoint m (d a))` is contained in the open set named by the homogeneous
envelopes `envA E hE (π a) m`, `envB E hE (π a) m`, and the corresponding cover event holds. -/
theorem independent_Xname {Γ : randomAlgebra ι} {A : bSet (randomAlgebra ι)}
    (hA1 : Γ ≤ Sem.isFun Rdot (bv_powerset Rdot) A)
    (hP4 : ∀ a ∈ J, ∀ m : ℤ,
      Γ ≤ valSet A (testPoint m (d a)) ⊆ᴮ openName (envA E hE (π a) m) (envB E hE (π a) m))
    (hP3 : ∀ a ∈ J, ∀ m : ℤ, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (coverEvent (seqFun (envA E hE (π a) m)) (seqFun (envB E hE (π a) m)))
      (measurableSet_coverEvent (measurable_seqFun _) (measurable_seqFun _))) :
    Γ ≤ Sem.independent A (Xname hE hJ hπ hdisj hR d) := by
  rw [Sem.independent]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ h₁ hx
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ hy
  rw [bv_imp_iff]; intro Γ₃ h₃ hxy
  refine le_iInf fun Ay => ?_
  rw [bv_imp_iff]; intro Γ₄ h₄ hAy
  rw [mem_Xname] at hx hy
  refine bv_iSup_elim ((h₄.trans (h₃.trans h₂)).trans hx) fun jk Γ₅ h₅ hjk => ?_
  refine bv_iSup_elim ((h₅.trans (h₄.trans h₃)).trans hy) fun j'k' Γ₆ h₆ hj'k' => ?_
  obtain ⟨j, k⟩ := jk
  obtain ⟨j', k'⟩ := j'k'
  dsimp only at hjk hj'k'
  have hΓ : Γ₆ ≤ Γ := h₆.trans (h₅.trans (h₄.trans (h₃.trans (h₂.trans h₁))))
  have hsel : Γ₆ ≤ selVal hE hJ hπ hdisj hR j k := h₆.trans (bv_and_left hjk)
  have hxtp : Γ₆ ≤ x =ᴮ tp hE hJ hπ hdisj hR d j k := h₆.trans (bv_and_right hjk)
  have hsel' : Γ₆ ≤ selVal hE hJ hπ hdisj hR j' k' := bv_and_left hj'k'
  have hytp : Γ₆ ≤ y =ᴮ tp hE hJ hπ hdisj hR d j' k' := bv_and_right hj'k'
  by_cases hj : j = j'
  · subst hj
    by_cases hk : k = k'
    · -- `x = y`: contradicts `x ≠ y`
      subst hk
      have hxy' : Γ₆ ≤ x =ᴮ y := by
        have := le_inf hxtp hytp
        rw [bv_eq_symm (x := y)] at this
        exact this.trans bv_eq_trans
      have : Γ₆ ≤ ⊥ :=
        (le_inf hxy' ((h₆.trans (h₅.trans h₄)).trans hxy)).trans (by rw [inf_compl_eq_bot])
      exact this.trans bot_le
    · -- two different candidates of the same stage are never both chosen
      have : Γ₆ ≤ ⊥ := by
        rw [← selVal_inf_selVal hE hJ hπ hdisj hR hk]; exact le_inf hsel hsel'
      exact this.trans bot_le
  · -- the main case: different stages
    -- `Ay = valSet A (tp j' k')`
    have hAy' : Γ₆ ≤ Sem.app A (tp hE hJ hπ hdisj hR d j' k') Ay :=
      app_congr_arg hytp ((h₆.trans h₅).trans hAy)
    have hval := app_valSet hA1 (x := tp hE hJ hπ hdisj hR d j' k') (testPoint_mem_Rdot _ _)
    have hAyeq : Γ₆ ≤ Ay =ᴮ valSet A (tp hE hJ hπ hdisj hR d j' k') :=
      isFun_unique (hΓ.trans hA1) (testPoint_mem_Rdot _ _) hAy' (hΓ.trans (bv_and_left hval))
    refine le_compl_of_inf_le_bot ?_
    -- on `Γ₆ ⊓ x ∈ᴮ Ay`, `tp j k ∈ᴮ openName (envA (π a') m') (envB (π a') m')`
    have hmem : Γ₆ ⊓ x ∈ᴮ Ay ≤ tp hE hJ hπ hdisj hR d j k ∈ᴮ
        openName (envA E hE (π (cand hE hJ hπ hdisj hR j' k').2) (cand hE hJ hπ hdisj hR j' k').1)
          (envB E hE (π (cand hE hJ hπ hdisj hR j' k').2) (cand hE hJ hπ hdisj hR j' k').1) := by
      have e1 : Γ₆ ⊓ x ∈ᴮ Ay ≤ tp hE hJ hπ hdisj hR d j k ∈ᴮ Ay :=
        subst_congr_mem_left' (inf_le_left.trans hxtp) inf_le_right
      have e2 : Γ₆ ⊓ x ∈ᴮ Ay ≤ tp hE hJ hπ hdisj hR d j k ∈ᴮ
          valSet A (tp hE hJ hπ hdisj hR d j' k') :=
        subst_congr_mem_right' (inf_le_left.trans hAyeq) e1
      exact mem_of_mem_subset (inf_le_left.trans (hΓ.trans
        (hP4 _ (cand_mem_J hE hJ hπ hdisj hR j' k') _))) e2
    have hcov : Γ₆ ⊓ x ∈ᴮ Ay ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        (coverEvent
          (seqFun (envA E hE (π (cand hE hJ hπ hdisj hR j' k').2) (cand hE hJ hπ hdisj hR j' k').1))
          (seqFun (envB E hE (π (cand hE hJ hπ hdisj hR j' k').2) (cand hE hJ hπ hdisj hR j' k').1)))
        (measurableSet_coverEvent (measurable_seqFun _) (measurable_seqFun _)) :=
      inf_le_left.trans (hΓ.trans (hP3 _ (cand_mem_J hE hJ hπ hdisj hR j' k') _))
    unfold tp testPoint at hmem
    rw [mem_openName_realName] at hmem
    have hfin := le_inf (le_inf (le_inf (inf_le_left.trans hsel) (inf_le_left.trans hsel')) hcov) hmem
    refine hfin.trans ?_
    unfold selVal
    rw [MeasureAlgebra.mk_inf, MeasureAlgebra.mk_inf, MeasureAlgebra.mk_inf, MeasureAlgebra.bot_def,
      MeasureAlgebra.mk_le_mk, MeasureAlgebra.ae_le_set_iff_ae_imp]
    filter_upwards [ae_good' hE hJ hπ hdisj hR] with x hx
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exfalso
    simp only [selEvent, mem_setOf_eq] at h1 h2 h4
    obtain ⟨n, h4a, h4b⟩ := h4
    apply xx_tj_not_mem_envSet hE hJ hπ hdisj hR hx hj
    rw [tj_eq hE hJ hπ hdisj hR j' x, h2, ← reading_tp hE hJ hπ hdisj hR hπ0 h1]
    exact (mem_envSet_iff _ _ _).mpr ⟨h3, n, h4a, h4b⟩

include hJ hπ hdisj hR hπ0 in
/-- **Packaging**: the name `Xname` witnesses `∃ X ∈ 𝒫 Rdot, X infinite ∧ X independent for A`. -/
theorem exists_infinite_independent_name {Γ : randomAlgebra ι} {A : bSet (randomAlgebra ι)}
    (hA1 : Γ ≤ Sem.isFun Rdot (bv_powerset Rdot) A)
    (hP4 : ∀ a ∈ J, ∀ m : ℤ,
      Γ ≤ valSet A (testPoint m (d a)) ⊆ᴮ openName (envA E hE (π a) m) (envB E hE (π a) m))
    (hP3 : ∀ a ∈ J, ∀ m : ℤ, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (coverEvent (seqFun (envA E hE (π a) m)) (seqFun (envB E hE (π a) m)))
      (measurableSet_coverEvent (measurable_seqFun _) (measurable_seqFun _))) :
    Γ ≤ ⨆ X : bSet (randomAlgebra ι),
      X ∈ᴮ bv_powerset Rdot ⊓ (Sem.infinite X ⊓ Sem.independent A X) :=
  le_iSup_of_le (Xname hE hJ hπ hdisj hR d)
    (le_inf (bv_powerset_spec.mp (Xname_subset_Rdot hE hJ hπ hdisj hR))
      (le_inf (infinite_Xname hE hJ hπ hdisj hR hπ0)
        (independent_Xname hE hJ hπ hdisj hR hπ0 hA1 hP4 hP3)))

end assembly

/-! ### The Erdős property of `Rdot` -/

open Cardinal in
/-- **Theorem 3.2 in `V^{randomAlgebra ι}`, outer-measure form**: for `𝔠⁺ ≤ #ι` and a function name
`A : Rdot → 𝒫 Rdot` all of whose values have outer measure `< 1` (on `Γ`), there is (on `Γ`) an
infinite independent `X ⊆ Rdot`. -/
theorem exists_infinite_independent_of_omlt1 (hι : Order.succ 𝔠 ≤ #ι) {Γ : randomAlgebra ι}
    {A : bSet (randomAlgebra ι)} (hA1 : Γ ≤ Sem.isFun Rdot (bv_powerset Rdot) A)
    (hA2 : Γ ≤ ⨅ x : bSet (randomAlgebra ι), x ∈ᴮ Rdot ⟹ ⨅ Ax : bSet (randomAlgebra ι),
      Sem.app A x Ax ⟹ Sem.outerMeasureLtOne Rdot plusDot ltDot zeroDot oneDot Ax) :
    Γ ≤ ⨆ X : bSet (randomAlgebra ι),
      X ∈ᴮ bv_powerset Rdot ⊓ (Sem.infinite X ⊓ Sem.independent A X) := by
  -- a set of coordinates of size `𝔠⁺`
  obtain ⟨S, hS⟩ := Cardinal.le_mk_iff_exists_set.mp hι
  obtain ⟨J, R, π, E, hE, hJ, hRc, -, hπinj, hπ0, -, hdisj, hP⟩ :=
    exists_homogeneous_envelopes hA1 hA2 hS Subtype.val_injective (R₀ := ∅) countable_empty
  -- pass to the subtype `J`
  have hJ' : ¬ (Set.univ : Set J).Countable := by
    intro h
    have := Cardinal.mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp h)
    rw [hJ] at this
    exact absurd (this.trans Cardinal.aleph0_le_continuum) (not_le.mpr (Order.lt_succ 𝔠))
  have hπ' : ∀ a : J, Function.Injective (π a.1) := fun a => hπinj a.1 a.2
  have hdisj' : ∀ a b : J, a ≠ b → Disjoint (Set.range (π a.1)) (Set.range (π b.1)) :=
    fun a b hab => hdisj a.1 a.2 b.1 b.2 fun h => hab (Subtype.ext h)
  have hπ0' : ∀ a : J, π a.1 0 = (a.1 : ι) := fun a => hπ0 a.1 a.2
  exact exists_infinite_independent_name hE hJ' hπ' hdisj' hRc (d := fun a : J => (a.1 : ι)) hπ0'
    hA1 (fun a _ m => (hP a.1 a.2 m).1) (fun a _ m => (hP a.1 a.2 m).2)

open Cardinal in
/-- **The internal reals of the random algebra on `𝔠⁺` coordinates have the Erdős property**
(Theorem 3.2 of the paper, in the Boolean-valued model `V^{randomAlgebra ι}`): for every
`A : Rdot → 𝒫 Rdot` with bounded values of outer measure `< 1` there is an infinite independent
`X ⊆ Rdot`. -/
theorem erdosProperty_Rdot (hι : Order.succ 𝔠 ≤ #ι) :
    (⊤ : randomAlgebra ι) ≤ Sem.erdosProperty Rdot plusDot ltDot zeroDot oneDot := by
  rw [Sem.erdosProperty]
  refine le_iInf fun A => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hA1
  rw [bv_imp_iff]; intro Γ h₁ hA2'
  replace hA1 : Γ ≤ Sem.isFun Rdot (bv_powerset Rdot) A := h₁.trans hA1
  -- only the outer-measure part of the hypothesis on the values of `A` is used
  have hA2 : Γ ≤ ⨅ x : bSet (randomAlgebra ι), x ∈ᴮ Rdot ⟹ ⨅ Ax : bSet (randomAlgebra ι),
      Sem.app A x Ax ⟹ Sem.outerMeasureLtOne Rdot plusDot ltDot zeroDot oneDot Ax := by
    refine le_iInf fun x => ?_
    rw [bv_imp_iff]; intro Γ' h' hx
    refine le_iInf fun Ax => ?_
    rw [bv_imp_iff]; intro Γ'' h'' hAx
    have h := bv_mp ((h''.trans (h'.trans hA2')).trans (iInf_le _ x)) (h''.trans hx)
    exact bv_and_right (bv_mp (h.trans (iInf_le _ Ax)) hAx)
  exact exists_infinite_independent_of_omlt1 hι hA1 hA2

open Cardinal in
/-- In `V^{randomAlgebra ι}` with `𝔠⁺ ≤ #ι`, the internal reals `Rdot` (with `plusDot`, `timesDot`,
`ltDot`, `zeroDot`, `oneDot`) form a complete ordered field with the Erdős property. -/
theorem completeOrderedField_and_erdosProperty_Rdot (hι : Order.succ 𝔠 ≤ #ι) :
    (⊤ : randomAlgebra ι) ≤ Sem.completeOrderedField Rdot plusDot timesDot ltDot zeroDot oneDot ⊓
      Sem.erdosProperty Rdot plusDot ltDot zeroDot oneDot :=
  le_inf completeOrderedField_Rdot (erdosProperty_Rdot hι)

end Flypitch.Erdos501.RandomForcing
