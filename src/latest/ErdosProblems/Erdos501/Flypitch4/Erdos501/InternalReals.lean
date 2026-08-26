/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The internal real numbers of the random-algebra model, as names, and the proof that they form
a complete ordered field (in the sense of `Sem.completeOrderedField`).
-/
import Mathlib.Data.Rat.Denumerable
import ErdosProblems.Erdos501.Flypitch4.Erdos501.BorelNames
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Semantics

set_option relaxedAutoImplicit true

/-!
# The internal reals of `V (randomAlgebra ι)` (step S2 of `PLAN.md`)

`Erdos501_f` quantifies over all complete ordered fields.  Its Boolean value was unfolded in
`Semantics.lean`; to *use* it we exhibit **one** internal complete ordered field, built from
canonical names, and prove that it satisfies `Sem.completeOrderedField`.

* A real of the extension is read off from the generic point `ĝ ∈ Ω ι` by a measurable
  `f : Ω ι → ℝ` (`MeasReal ι`); its name is the canonical name `realName f := mkReal (code ∘ f)`
  of the subset of `ω` coding the Dedekind cut of `f(ĝ)` in a fixed enumeration `ratEnum` of `ℚ`
  (`code r n = decide (ratEnum n < r)`).  By `bv_eq_mkReal` and the injectivity of `code`,
  `‖realName f = realName g‖ = [{x | f x = g x}]` (`bv_eq_realName`).
* `Rdot` is the name whose elements are all `realName f` (with Boolean value `⊤`); `ltDot` is the
  set of pairs `(realName f, realName g)` with Boolean value `[{x | f x < g x}]`; `plusDot` and
  `timesDot` are the graphs `((realName f, realName g), realName (f + g))`, resp. `f * g`;
  `zeroDot`, `oneDot` are the names of the constants.
* The membership/application predicates of `Semantics.lean` evaluate on these names to Boolean
  values built from `=ᴮ` to canonical names and events in the measure algebra
  (`mem_Rdot`, `app2_opDot`, `lt_ltDot`), so that every axiom of a complete ordered field
  reduces to the corresponding pointwise fact about `ℝ` (`completeOrderedField_Rdot`).
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice
open scoped ENNReal Flypitch Fol

namespace Flypitch.Erdos501.RandomForcing

variable {ι : Type}

/-! ### Cut codes of reals -/

/-- A fixed enumeration of the rationals. -/
noncomputable def ratEnum : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

/-- The cut code of a real `r`: `code r n = 1` iff the `n`-th rational is `< r`. -/
noncomputable def code (r : ℝ) : ℕ → Bool := fun n => if (ratEnum n : ℝ) < r then true else false

lemma code_apply_eq_true_iff (r : ℝ) (n : ℕ) : code r n = true ↔ (ratEnum n : ℝ) < r := by
  simp [code]

lemma code_injective : Function.Injective code := by
  intro r s hrs
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn h
    have h1 := congrArg (fun c : ℕ → Bool => c (ratEnum.symm q)) hrs
    simp only [code, Equiv.apply_symm_apply] at h1
    rw [if_neg (not_lt.mpr hrq.le), if_pos hqs] at h1
    exact absurd h1 (by decide)
  · obtain ⟨q, hsq, hqr⟩ := exists_rat_btwn h
    have h1 := congrArg (fun c : ℕ → Bool => c (ratEnum.symm q)) hrs
    simp only [code, Equiv.apply_symm_apply] at h1
    rw [if_pos hqr, if_neg (not_lt.mpr hsq.le)] at h1
    exact absurd h1 (by decide)

lemma measurable_code : Measurable code := by
  refine measurable_pi_iff.mpr fun n => ?_
  exact Measurable.ite (p := fun r : ℝ => (ratEnum n : ℝ) < r) measurableSet_Ioi
    measurable_const measurable_const

/-! ### Names for reals read off by real-valued measurable functions -/

/-- Measurable real-valued readings of the generic point. -/
abbrev MeasReal (ι : Type) : Type := {f : RandomAlgebra.Ω ι → ℝ // Measurable f}

/-- The name of the real `f(ĝ)` read off from the generic point `ĝ` by the measurable
`f : Ω ι → ℝ`: the canonical name of the cut code of `f(ĝ)`. -/
noncomputable def realName (f : RandomAlgebra.Ω ι → ℝ) (hf : Measurable f) :
    bSet (randomAlgebra ι) :=
  mkReal (code ∘ f) (measurable_code.comp hf)

variable {f g : RandomAlgebra.Ω ι → ℝ} {hf : Measurable f} {hg : Measurable g}

lemma realName_definite {Γ : randomAlgebra ι} : Γ ≤ realName f hf ⊆ᴮ omega :=
  mkReal_definite (measurable_code.comp hf)

/-- **Equality of names of reals**: `‖realName f = realName g‖ = [{x | f x = g x}]`. -/
theorem bv_eq_realName :
    (realName f hf =ᴮ realName g hg) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | f x = g x} (measurableSet_eq_fun hf hg) := by
  rw [realName, realName, bv_eq_mkReal]
  apply MeasureAlgebra.mk_congr
  ext x
  simp only [mem_setOf_eq, Function.comp]
  exact code_injective.eq_iff

/-- A pointwise-true relation between readings has Boolean value `⊤`. -/
lemma mk_eq_top_of_forall {s : Set (RandomAlgebra.Ω ι)} (hs : MeasurableSet s) (h : ∀ x, x ∈ s) :
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs = ⊤ := by
  rw [MeasureAlgebra.top_def]
  exact MeasureAlgebra.mk_congr (eq_univ_of_forall h)

/-- Monotonicity of `mk` in the set. -/
lemma mk_mono {s t : Set (RandomAlgebra.Ω ι)} {hs : MeasurableSet s} {ht : MeasurableSet t}
    (h : s ⊆ t) : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs ≤
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) t ht :=
  MeasureAlgebra.mk_le_mk.mpr (Filter.Eventually.of_forall h)

lemma bv_eq_realName_of_eq (h : ∀ x, f x = g x) : (realName f hf =ᴮ realName g hg) = ⊤ := by
  rw [bv_eq_realName]; exact mk_eq_top_of_forall _ h

/-! ### The internal reals `Rdot` and their structure -/

/-- The name of the set of all reals of the extension: its elements are the names `realName f`,
`f : Ω ι → ℝ` measurable, each with Boolean value `⊤`. -/
noncomputable def Rdot : bSet (randomAlgebra ι) :=
  ⟨MeasReal ι, fun f => realName f.1 f.2, fun _ => ⊤⟩

@[simp] lemma Rdot_type : (Rdot : bSet (randomAlgebra ι)).type = MeasReal ι := rfl
@[simp] lemma Rdot_func (f : (Rdot : bSet (randomAlgebra ι)).type) :
    (Rdot : bSet (randomAlgebra ι)).func f = realName f.1 f.2 := rfl
@[simp] lemma Rdot_bval (f : (Rdot : bSet (randomAlgebra ι)).type) :
    (Rdot : bSet (randomAlgebra ι)).bval f = ⊤ := rfl

/-- The name of the order relation `<` on `Rdot`: the pairs `(realName f, realName g)` with
Boolean value `[{x | f x < g x}]`. -/
noncomputable def ltDot : bSet (randomAlgebra ι) :=
  ⟨MeasReal ι × MeasReal ι, fun p => pair (realName p.1.1 p.1.2) (realName p.2.1 p.2.2),
    fun p => MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | p.1.1 x < p.2.1 x}
      (measurableSet_lt p.1.2 p.2.2)⟩

@[simp] lemma ltDot_type : (ltDot : bSet (randomAlgebra ι)).type = (MeasReal ι × MeasReal ι) := rfl
@[simp] lemma ltDot_func (p : (ltDot : bSet (randomAlgebra ι)).type) :
    (ltDot : bSet (randomAlgebra ι)).func p = pair (realName p.1.1 p.1.2) (realName p.2.1 p.2.2) := rfl
@[simp] lemma ltDot_bval (p : (ltDot : bSet (randomAlgebra ι)).type) :
    (ltDot : bSet (randomAlgebra ι)).bval p =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | p.1.1 x < p.2.1 x}
        (measurableSet_lt p.1.2 p.2.2) := rfl

/-- `{x | p x ∧ q x}` is measurable, stated with this exact set (not `∩`), for use in statements. -/
lemma measurableSet_setOf_and {X : Type*} [MeasurableSpace X] {p q : X → Prop}
    (hp : MeasurableSet {x | p x}) (hq : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ∧ q x} :=
  hp.inter hq

/-- Measurability of `x ↦ op (f x) (g x)`, stated with this exact type (Lean ≥ 4.34 checks
applications inside `simp`/`rw` at reducible transparency, so the proof terms occurring in
statements must have syntactically the expected types). -/
lemma measurable_op2 {op : ℝ → ℝ → ℝ} (hop : Measurable (Function.uncurry op))
    {f g : RandomAlgebra.Ω ι → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => op (f x) (g x) :=
  hop.comp (hf.prodMk hg)

/-- `Measurable (Function.uncurry (· + ·))` on `ℝ`, with this exact type. -/
lemma measurable_uncurry_add : Measurable (Function.uncurry (HAdd.hAdd : ℝ → ℝ → ℝ)) :=
  measurable_add

/-- `Measurable (Function.uncurry (· * ·))` on `ℝ`, with this exact type. -/
lemma measurable_uncurry_mul : Measurable (Function.uncurry (HMul.hMul : ℝ → ℝ → ℝ)) :=
  measurable_mul

/-- The name of the graph of a binary operation `op` on `ℝ` (measurable in the two arguments):
the triples `((realName f, realName g), realName (fun x => op (f x) (g x)))`. -/
noncomputable def opDot (op : ℝ → ℝ → ℝ) (hop : Measurable (Function.uncurry op)) :
    bSet (randomAlgebra ι) :=
  ⟨MeasReal ι × MeasReal ι,
    fun p => pair (pair (realName p.1.1 p.1.2) (realName p.2.1 p.2.2))
      (realName (fun x => op (p.1.1 x) (p.2.1 x)) (measurable_op2 hop p.1.2 p.2.2)),
    fun _ => ⊤⟩

variable {op : ℝ → ℝ → ℝ} (hop : Measurable (Function.uncurry op))

@[simp] lemma opDot_type : (opDot op hop : bSet (randomAlgebra ι)).type = (MeasReal ι × MeasReal ι) :=
  rfl
@[simp] lemma opDot_func (p : (opDot op hop : bSet (randomAlgebra ι)).type) :
    (opDot op hop : bSet (randomAlgebra ι)).func p =
      pair (pair (realName p.1.1 p.1.2) (realName p.2.1 p.2.2))
        (realName (fun x => op (p.1.1 x) (p.2.1 x)) (measurable_op2 hop p.1.2 p.2.2)) := rfl
@[simp] lemma opDot_bval (p : (opDot op hop : bSet (randomAlgebra ι)).type) :
    (opDot op hop : bSet (randomAlgebra ι)).bval p = ⊤ := rfl

/-- The name of addition on `Rdot`. -/
noncomputable def plusDot : bSet (randomAlgebra ι) := opDot HAdd.hAdd measurable_uncurry_add

/-- The name of multiplication on `Rdot`. -/
noncomputable def timesDot : bSet (randomAlgebra ι) := opDot HMul.hMul measurable_uncurry_mul

/-- The name of `0 ∈ Rdot`. -/
noncomputable def zeroDot : bSet (randomAlgebra ι) := realName (fun _ => (0 : ℝ)) measurable_const

/-- The name of `1 ∈ Rdot`. -/
noncomputable def oneDot : bSet (randomAlgebra ι) := realName (fun _ => (1 : ℝ)) measurable_const

/-! ### Evaluation of the predicates of `Semantics.lean` on these names -/

/-- `‖x ∈ Rdot‖ = ⨆ f, ‖x = realName f‖`. -/
theorem mem_Rdot (x : bSet (randomAlgebra ι)) :
    (x ∈ᴮ (Rdot : bSet (randomAlgebra ι))) = ⨆ f : MeasReal ι, x =ᴮ realName f.1 f.2 := by
  rw [mem_unfold]
  simp only [Rdot_bval, Rdot_func, top_inf_eq]
  rfl

lemma realName_mem_Rdot {Γ : randomAlgebra ι} : Γ ≤ realName f hf ∈ᴮ Rdot := by
  rw [mem_Rdot]
  exact le_trans le_top (le_iSup_of_le ⟨f, hf⟩ (by rw [bv_eq_refl]))

/-- Evaluation of `Sem.app2 (opDot op)` on arbitrary names: `‖op(x, y) = z‖` is the supremum over
readings `f, g` of `‖x = realName f‖ ⊓ ‖y = realName g‖ ⊓ ‖z = realName (op ∘ (f, g))‖`. -/
theorem app2_opDot (x y z : bSet (randomAlgebra ι)) :
    Sem.app2 (opDot op hop) x y z =
      ⨆ p : MeasReal ι × MeasReal ι,
        (x =ᴮ realName p.1.1 p.1.2) ⊓ (y =ᴮ realName p.2.1 p.2.2) ⊓
          (z =ᴮ realName (fun x => op (p.1.1 x) (p.2.1 x)) (measurable_op2 hop p.1.2 p.2.2)) := by
  rw [Sem.app2, mem_unfold]
  simp only [opDot_bval, opDot_func, top_inf_eq]
  apply le_antisymm
  · apply iSup_mono; intro p
    have h := (pair_eq_pair_iff (Γ := pair (pair x y) z =ᴮ
      pair (pair (realName p.1.1 p.1.2) (realName p.2.1 p.2.2))
        (realName (fun x => op (p.1.1 x) (p.2.1 x)) (measurable_op2 hop p.1.2 p.2.2)))).mp le_rfl
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h11, h12⟩ := (pair_eq_pair_iff.mp h1)
    exact le_inf (le_inf h11 h12) h2
  · apply iSup_mono; intro p
    exact pair_eq_pair_iff.mpr ⟨pair_eq_pair_iff.mpr ⟨inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right⟩, inf_le_right⟩

/-- On canonical names, `‖op(realName f, realName g) = z‖ = ‖z = realName (op ∘ (f, g))‖`. -/
theorem app2_opDot_realName (z : bSet (randomAlgebra ι)) :
    Sem.app2 (opDot op hop) (realName f hf) (realName g hg) z =
      z =ᴮ realName (fun x => op (f x) (g x)) (measurable_op2 hop hf hg) := by
  rw [app2_opDot]
  apply le_antisymm
  · apply iSup_le; intro p
    rw [bv_eq_realName, bv_eq_realName]
    calc _ ≤ (z =ᴮ realName (fun x => op (p.1.1 x) (p.2.1 x)) (measurable_op2 hop p.1.2 p.2.2)) ⊓
          (realName (fun x => op (p.1.1 x) (p.2.1 x)) (measurable_op2 hop p.1.2 p.2.2) =ᴮ
            realName (fun x => op (f x) (g x)) (measurable_op2 hop hf hg)) := by
          refine le_inf inf_le_right ?_
          rw [bv_eq_realName]
          refine le_trans inf_le_left ?_
          rw [MeasureAlgebra.mk_inf]
          apply mk_mono
          rintro x ⟨h1, h2⟩
          simp only [mem_setOf_eq] at h1 h2 ⊢
          rw [h1, h2]
      _ ≤ _ := bv_eq_trans
  · refine le_iSup_of_le (⟨f, hf⟩, ⟨g, hg⟩) ?_
    simp only [bv_eq_refl, top_inf_eq, le_refl]

/-- Evaluation of `Sem.lt ltDot` on arbitrary names. -/
theorem lt_ltDot (x y : bSet (randomAlgebra ι)) :
    Sem.lt ltDot x y =
      ⨆ p : MeasReal ι × MeasReal ι,
        (x =ᴮ realName p.1.1 p.1.2) ⊓ (y =ᴮ realName p.2.1 p.2.2) ⊓
          MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | p.1.1 x < p.2.1 x}
            (measurableSet_lt p.1.2 p.2.2) := by
  rw [Sem.lt, mem_unfold]
  simp only [ltDot_bval, ltDot_func]
  apply le_antisymm
  · apply iSup_mono; intro p
    rw [inf_comm]
    refine inf_le_inf_right _ ?_
    exact le_inf (eq_of_eq_pair_left' le_rfl) (eq_of_eq_pair_right' le_rfl)
  · apply iSup_mono; intro p
    rw [inf_comm]
    refine inf_le_inf_left _ ?_
    exact pair_eq_pair_iff.mpr ⟨inf_le_left, inf_le_right⟩

/-- On canonical names, `‖realName f < realName g‖ = [{x | f x < g x}]`. -/
theorem lt_ltDot_realName :
    Sem.lt ltDot (realName f hf) (realName g hg) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | f x < g x} (measurableSet_lt hf hg) := by
  rw [lt_ltDot]
  apply le_antisymm
  · apply iSup_le; intro p
    rw [bv_eq_realName, bv_eq_realName, MeasureAlgebra.mk_inf, MeasureAlgebra.mk_inf]
    apply mk_mono
    rintro x ⟨⟨h1, h2⟩, h3⟩
    simp only [mem_setOf_eq] at h1 h2 h3 ⊢
    rw [h1, h2]; exact h3
  · refine le_iSup_of_le (⟨f, hf⟩, ⟨g, hg⟩) ?_
    simp only [bv_eq_refl, top_inf_eq, le_refl]

/-- On canonical names, `‖realName f ≤ realName g‖ = [{x | f x ≤ g x}]`. -/
theorem le_ltDot_realName :
    Sem.le ltDot (realName f hf) (realName g hg) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | f x ≤ g x} (measurableSet_le hf hg) := by
  rw [Sem.le, lt_ltDot_realName, bv_eq_realName, MeasureAlgebra.mk_sup]
  apply MeasureAlgebra.mk_congr
  ext x
  simp only [mem_union, mem_setOf_eq, le_iff_lt_or_eq]


/-! ### Introduction and elimination rules, in the style of natural deduction on Boolean values -/

section tools

variable {Γ b : randomAlgebra ι} {x y z : bSet (randomAlgebra ι)}

lemma le_mem_Rdot (h : Γ ≤ x =ᴮ realName f hf) : Γ ≤ x ∈ᴮ Rdot := by
  rw [mem_Rdot]; exact le_iSup_of_le ⟨f, hf⟩ h

lemma mem_Rdot_elim (h : Γ ≤ x ∈ᴮ Rdot)
    (H : ∀ (f : MeasReal ι) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ x =ᴮ realName f.1 f.2 →
      Γ' ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [mem_Rdot]
  exact bv_cases_right fun f => H f _ inf_le_left inf_le_right

lemma le_app2_opDot (hx : Γ ≤ x =ᴮ realName f hf) (hy : Γ ≤ y =ᴮ realName g hg)
    (hz : Γ ≤ z =ᴮ realName (fun w => op (f w) (g w)) (measurable_op2 hop hf hg)) :
    Γ ≤ Sem.app2 (opDot op hop) x y z := by
  rw [app2_opDot]
  exact le_iSup_of_le (⟨f, hf⟩, ⟨g, hg⟩) (le_inf (le_inf hx hy) hz)

lemma app2_opDot_elim (h : Γ ≤ Sem.app2 (opDot op hop) x y z)
    (H : ∀ (f g : MeasReal ι) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ x =ᴮ realName f.1 f.2 →
      Γ' ≤ y =ᴮ realName g.1 g.2 →
      Γ' ≤ z =ᴮ realName (fun w => op (f.1 w) (g.1 w)) (measurable_op2 hop f.2 g.2) → Γ' ≤ b) :
    Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [app2_opDot]
  exact bv_cases_right fun p => H p.1 p.2 _ inf_le_left
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)

lemma le_lt_ltDot (hx : Γ ≤ x =ᴮ realName f hf) (hy : Γ ≤ y =ᴮ realName g hg)
    (hfg : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f w < g w}
      (measurableSet_lt hf hg)) :
    Γ ≤ Sem.lt ltDot x y := by
  rw [lt_ltDot]; exact le_iSup_of_le (⟨f, hf⟩, ⟨g, hg⟩) (le_inf (le_inf hx hy) hfg)

lemma lt_ltDot_elim (h : Γ ≤ Sem.lt ltDot x y)
    (H : ∀ (f g : MeasReal ι) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ x =ᴮ realName f.1 f.2 →
      Γ' ≤ y =ᴮ realName g.1 g.2 →
      Γ' ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w < g.1 w}
        (measurableSet_lt f.2 g.2) → Γ' ≤ b) :
    Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [lt_ltDot]
  exact bv_cases_right fun p => H p.1 p.2 _ inf_le_left
    (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)

/-- Two canonical readings of the same name agree (as an event). -/
lemma eq_realName_trans (h1 : Γ ≤ x =ᴮ realName f hf) (h2 : Γ ≤ x =ᴮ realName g hg) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f w = g w}
      (measurableSet_eq_fun hf hg) := by
  rw [← bv_eq_realName (hf := hf) (hg := hg)]
  have h := le_inf h1 h2
  rw [bv_eq_symm (x := x) (y := realName f hf)] at h
  exact h.trans bv_eq_trans

/-- Transport of a name along an a.e. equality of readings. -/
lemma eq_realName_of_eq (h1 : Γ ≤ x =ᴮ realName f hf)
    (h2 : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f w = g w}
      (measurableSet_eq_fun hf hg)) :
    Γ ≤ x =ᴮ realName g hg := by
  rw [← bv_eq_realName (hf := hf) (hg := hg)] at h2
  exact (le_inf h1 h2).trans bv_eq_trans

lemma le_mk_of_forall {s : Set (RandomAlgebra.Ω ι)} {hs : MeasurableSet s} (h : ∀ w, w ∈ s) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs := by
  rw [mk_eq_top_of_forall hs h]; exact le_top

lemma mk_le_of_forall {s t : Set (RandomAlgebra.Ω ι)} {hs : MeasurableSet s}
    {ht : MeasurableSet t} (h : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs)
    (H : ∀ w, w ∈ s → w ∈ t) : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) t ht :=
  h.trans (mk_mono H)

lemma mk_le_of_forall₂ {s₁ s₂ t : Set (RandomAlgebra.Ω ι)} {hs₁ : MeasurableSet s₁}
    {hs₂ : MeasurableSet s₂} {ht : MeasurableSet t}
    (h₁ : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s₁ hs₁)
    (h₂ : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s₂ hs₂)
    (H : ∀ w, w ∈ s₁ → w ∈ s₂ → w ∈ t) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) t ht := by
  have h := le_inf h₁ h₂
  rw [MeasureAlgebra.mk_inf] at h
  exact mk_le_of_forall h fun w hw => H w hw.1 hw.2

lemma mk_le_of_forall₃ {s₁ s₂ s₃ t : Set (RandomAlgebra.Ω ι)} {hs₁ : MeasurableSet s₁}
    {hs₂ : MeasurableSet s₂} {hs₃ : MeasurableSet s₃} {ht : MeasurableSet t}
    (h₁ : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s₁ hs₁)
    (h₂ : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s₂ hs₂)
    (h₃ : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s₃ hs₃)
    (H : ∀ w, w ∈ s₁ → w ∈ s₂ → w ∈ s₃ → w ∈ t) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) t ht := by
  have h := le_inf h₁ (le_inf h₂ h₃)
  rw [MeasureAlgebra.mk_inf, MeasureAlgebra.mk_inf] at h
  exact mk_le_of_forall h fun w hw => H w hw.1 hw.2.1 hw.2.2

lemma le_compl_of_inf_le_bot {a : randomAlgebra ι} (h : Γ ⊓ a ≤ ⊥) : Γ ≤ aᶜ :=
  le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr h)

lemma mk_eq_bot_of_forall_not {s : Set (RandomAlgebra.Ω ι)} (hs : MeasurableSet s)
    (h : ∀ w, w ∉ s) : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs = ⊥ := by
  rw [MeasureAlgebra.bot_def]
  exact MeasureAlgebra.mk_congr (eq_empty_iff_forall_notMem.mpr h)

/-- Case analysis on a Boolean disjunction, in context. -/
lemma bv_or_elim' {a₁ a₂ : randomAlgebra ι} (h : Γ ≤ a₁ ⊔ a₂)
    (H₁ : ∀ Γ' : randomAlgebra ι, Γ' ≤ Γ → Γ' ≤ a₁ → Γ' ≤ b)
    (H₂ : ∀ Γ' : randomAlgebra ι, Γ' ≤ Γ → Γ' ≤ a₂ → Γ' ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [inf_sup_left]
  exact sup_le (H₁ _ inf_le_left inf_le_right) (H₂ _ inf_le_left inf_le_right)

end tools

/-! ### The axioms of a complete ordered field for `Rdot` -/

section axioms

/-- `zeroDot ∈ Rdot`. -/
theorem zeroDot_mem : ⊤ ≤ (zeroDot : bSet (randomAlgebra ι)) ∈ᴮ Rdot := realName_mem_Rdot

/-- `oneDot ∈ Rdot`. -/
theorem oneDot_mem : ⊤ ≤ (oneDot : bSet (randomAlgebra ι)) ∈ᴮ Rdot := realName_mem_Rdot

/-- `zeroDot ≠ oneDot`. -/
theorem zeroDot_ne_oneDot : ⊤ ≤ ((zeroDot : bSet (randomAlgebra ι)) =ᴮ oneDot)ᶜ := by
  rw [zeroDot, oneDot, bv_eq_realName]
  refine le_compl_of_inf_le_bot ?_
  rw [top_inf_eq]
  exact (mk_eq_bot_of_forall_not _ fun w (h : (0 : ℝ) = 1) => zero_ne_one h).le

/-- `opDot op` is a binary operation on `Rdot`. -/
theorem isOp2_opDot : ⊤ ≤ Sem.isOp2 (Rdot : bSet (randomAlgebra ι)) (opDot op hop) := by
  rw [Sem.isOp2]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ hy
  refine mem_Rdot_elim (h₂.trans hx) fun f Γ₃ h₃ hxf => ?_
  refine mem_Rdot_elim (h₃.trans hy) fun g Γ₄ h₄ hyg => ?_
  have hxf' : Γ₄ ≤ x =ᴮ realName f.1 f.2 := h₄.trans hxf
  refine le_iSup_of_le (realName (fun w => op (f.1 w) (g.1 w)) (measurable_op2 hop f.2 g.2)) ?_
  refine le_inf (realName_mem_Rdot) (le_inf ?_ ?_)
  · exact le_app2_opDot hop hxf' hyg (by rw [bv_eq_refl]; exact le_top)
  · refine le_iInf fun z' => ?_
    rw [bv_imp_iff]; intro Γ₅ h₅ hz'
    refine app2_opDot_elim hop hz' fun f' g' Γ₆ h₆ hxf'' hyg' hz'' => ?_
    have e1 := eq_realName_trans hxf'' ((h₆.trans h₅).trans hxf')
    have e2 := eq_realName_trans hyg' ((h₆.trans h₅).trans hyg)
    refine eq_realName_of_eq hz'' ?_
    refine mk_le_of_forall₂ e1 e2 fun w h1 h2 => ?_
    simp only [mem_setOf_eq] at h1 h2 ⊢
    rw [h1, h2]

/-- Two names equal to the same canonical name are equal. -/
lemma bv_eq_of_eq_realName {Γ : randomAlgebra ι} {x y : bSet (randomAlgebra ι)}
    (h1 : Γ ≤ x =ᴮ realName f hf) (h2 : Γ ≤ y =ᴮ realName f hf) : Γ ≤ x =ᴮ y := by
  have h := le_inf h1 h2
  rw [bv_eq_symm (x := y)] at h
  exact h.trans bv_eq_trans

/-- Associativity of `opDot op` on `Rdot`, from associativity of `op`. -/
theorem assoc_opDot (hassoc : ∀ a b c : ℝ, op (op a b) c = op a (op b c)) :
    ⊤ ≤ Sem.assoc (Rdot : bSet (randomAlgebra ι)) (opDot op hop) := by
  rw [Sem.assoc]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun z => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ _
  refine le_iInf fun u => le_iInf fun v => le_iInf fun w => le_iInf fun w' => ?_
  rw [bv_imp_iff]; intro Γ₄ h₄ hxyu
  rw [bv_imp_iff]; intro Γ₅ h₅ huzv
  rw [bv_imp_iff]; intro Γ₆ h₆ hyzw
  rw [bv_imp_iff]; intro Γ₇ h₇ hxww'
  -- read all names canonically
  refine app2_opDot_elim hop (((h₇.trans h₆).trans h₅).trans hxyu) fun f g Γ₈ h₈ hxf hyg hu => ?_
  refine app2_opDot_elim hop ((h₈.trans (h₇.trans h₆)).trans huzv) fun u' h Γ₉ h₉ hu' hzh hv => ?_
  refine app2_opDot_elim hop ((h₉.trans (h₈.trans h₇)).trans hyzw)
    fun g' h' Γ₁₀ h₁₀ hyg' hzh' hw => ?_
  refine app2_opDot_elim hop ((h₁₀.trans h₉).trans (h₈.trans hxww'))
    fun f' w'' Γ₁₁ h₁₁ hxf' hww'' hw' => ?_
  -- transport everything to `Γ₁₁`
  have H₉ : Γ₁₁ ≤ Γ₉ := h₁₁.trans h₁₀
  have H₈ : Γ₁₁ ≤ Γ₈ := H₉.trans h₉
  have e1 := eq_realName_trans (H₈.trans hu) (H₉.trans hu')
  have e2 := eq_realName_trans (H₉.trans hzh) (h₁₁.trans hzh')
  have e3 := eq_realName_trans (H₈.trans hyg) (h₁₁.trans hyg')
  have e4 := eq_realName_trans (H₈.trans hxf) hxf'
  have e5 := eq_realName_trans (h₁₁.trans hw) hww''
  refine bv_eq_of_eq_realName (eq_realName_of_eq (H₉.trans hv) ?_) hw'
  have e := le_inf e1 (le_inf e2 (le_inf e3 (le_inf e4 e5)))
  simp only [MeasureAlgebra.mk_inf] at e
  refine mk_le_of_forall e fun w hw => ?_
  simp only [mem_inter_iff, mem_setOf_eq] at hw ⊢
  obtain ⟨he1, he2, he3, he4, he5⟩ := hw
  rw [← he1, hassoc, he4, he3, he2, ← he5]

/-- Commutativity of `opDot op` on `Rdot`, from commutativity of `op`. -/
theorem comm_opDot (hcomm : ∀ a b : ℝ, op a b = op b a) :
    ⊤ ≤ Sem.comm (Rdot : bSet (randomAlgebra ι)) (opDot op hop) := by
  rw [Sem.comm]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun u => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ hxyu
  refine app2_opDot_elim hop hxyu fun f g Γ₄ h₄ hxf hyg hu => ?_
  refine le_app2_opDot hop hyg hxf (eq_realName_of_eq hu ?_)
  exact le_mk_of_forall fun w => hcomm _ _

/-- `e` is a right identity for `opDot op` on `Rdot` if `ec` is one for `op`. -/
theorem ident_opDot (ec : ℝ) (hid : ∀ a : ℝ, op a ec = a) :
    ⊤ ≤ Sem.ident (Rdot : bSet (randomAlgebra ι)) (opDot op hop)
      (realName (fun _ => ec) measurable_const) := by
  rw [Sem.ident]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine mem_Rdot_elim hx fun f Γ₂ h₂ hxf => ?_
  refine le_app2_opDot hop hxf (by rw [bv_eq_refl]; exact le_top) (eq_realName_of_eq hxf ?_)
  exact le_mk_of_forall fun w => (hid _).symm

/-- Additive inverses in `Rdot`. -/
theorem addInv_plusDot :
    ⊤ ≤ Sem.addInv (Rdot : bSet (randomAlgebra ι)) plusDot zeroDot := by
  rw [Sem.addInv]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine mem_Rdot_elim hx fun f Γ₂ h₂ hxf => ?_
  refine le_iSup_of_le (realName (fun w => -(f.1 w)) f.2.neg) ?_
  refine le_inf (realName_mem_Rdot) ?_
  refine le_app2_opDot measurable_uncurry_add hxf (by rw [bv_eq_refl]; exact le_top) ?_
  rw [zeroDot, bv_eq_realName]
  exact le_mk_of_forall fun w => (add_neg_cancel _).symm

/-- Multiplicative inverses of nonzero elements in `Rdot`. -/
theorem mulInv_timesDot :
    ⊤ ≤ Sem.mulInv (Rdot : bSet (randomAlgebra ι)) timesDot zeroDot oneDot := by
  rw [Sem.mulInv]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  rw [bv_imp_iff]; intro Γ₂ h₂ hx0
  refine mem_Rdot_elim (h₂.trans hx) fun f Γ₃ h₃ hxf => ?_
  refine le_iSup_of_le (realName (fun w => (f.1 w)⁻¹) f.2.inv) ?_
  refine le_inf (realName_mem_Rdot) ?_
  refine le_app2_opDot measurable_uncurry_mul hxf (by rw [bv_eq_refl]; exact le_top) ?_
  -- `f ≠ 0` on `Γ₃`
  have hne : Γ₃ ≤ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w = 0}
      (measurableSet_eq_fun f.2 measurable_const))ᶜ := by
    refine le_compl_of_inf_le_bot ?_
    have h0 : Γ₃ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w = 0}
        (measurableSet_eq_fun f.2 measurable_const) ≤ x =ᴮ zeroDot := by
      rw [zeroDot]
      exact eq_realName_of_eq (inf_le_left.trans hxf) inf_le_right
    have h0' : Γ₃ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w = 0}
        (measurableSet_eq_fun f.2 measurable_const) ≤ (x =ᴮ zeroDot)ᶜ :=
      inf_le_left.trans (h₃.trans hx0)
    exact (le_inf h0 h0').trans (by rw [inf_compl_eq_bot])
  rw [oneDot, bv_eq_realName]
  rw [MeasureAlgebra.mk_compl] at hne
  refine mk_le_of_forall hne fun w hw => ?_
  simp only [mem_compl_iff, mem_setOf_eq] at hw ⊢
  exact (mul_inv_cancel₀ hw).symm

/-- Distributivity in `Rdot`. -/
theorem distrib_Rdot :
    ⊤ ≤ Sem.distrib (Rdot : bSet (randomAlgebra ι)) plusDot timesDot := by
  rw [Sem.distrib]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun z => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ _
  refine le_iInf fun u => le_iInf fun v => le_iInf fun w => le_iInf fun t => le_iInf fun t' => ?_
  rw [bv_imp_iff]; intro Γ₄ h₄ hyzu
  rw [bv_imp_iff]; intro Γ₅ h₅ hxuv
  rw [bv_imp_iff]; intro Γ₆ h₆ hxyw
  rw [bv_imp_iff]; intro Γ₇ h₇ hxzt
  rw [bv_imp_iff]; intro Γ₈ h₈ hwtt'
  refine app2_opDot_elim measurable_uncurry_add ((((h₈.trans h₇).trans h₆).trans h₅).trans hyzu)
    fun g h Γ₉ h₉ hyg hzh hu => ?_
  refine app2_opDot_elim measurable_uncurry_mul ((h₉.trans ((h₈.trans h₇).trans h₆)).trans hxuv)
    fun f u' Γ₁₀ h₁₀ hxf huu' hv => ?_
  refine app2_opDot_elim measurable_uncurry_mul (((h₁₀.trans h₉).trans (h₈.trans h₇)).trans hxyw)
    fun f' g' Γ₁₁ h₁₁ hxf' hyg' hw => ?_
  refine app2_opDot_elim measurable_uncurry_mul ((((h₁₁.trans h₁₀).trans h₉).trans h₈).trans hxzt)
    fun f'' h' Γ₁₂ h₁₂ hxf'' hzh' ht => ?_
  refine app2_opDot_elim measurable_uncurry_add ((((h₁₂.trans h₁₁).trans h₁₀).trans h₉).trans hwtt')
    fun w' t'' Γ₁₃ h₁₃ hww' htt'' ht' => ?_
  -- transport everything to `Γ₁₃`
  have H₁₂ : Γ₁₃ ≤ Γ₁₂ := h₁₃
  have H₁₁ : Γ₁₃ ≤ Γ₁₁ := H₁₂.trans h₁₂
  have H₁₀ : Γ₁₃ ≤ Γ₁₀ := H₁₁.trans h₁₁
  have H₉ : Γ₁₃ ≤ Γ₉ := H₁₀.trans h₁₀
  have e1 := eq_realName_trans (H₉.trans hu) (H₁₀.trans huu')
  have e2 := eq_realName_trans (H₁₀.trans hxf) (H₁₁.trans hxf')
  have e3 := eq_realName_trans (H₁₀.trans hxf) (H₁₂.trans hxf'')
  have e4 := eq_realName_trans (H₉.trans hyg) (H₁₁.trans hyg')
  have e5 := eq_realName_trans (H₉.trans hzh) (H₁₂.trans hzh')
  have e6 := eq_realName_trans (H₁₁.trans hw) hww'
  have e7 := eq_realName_trans (H₁₂.trans ht) htt''
  refine bv_eq_of_eq_realName (eq_realName_of_eq (H₁₀.trans hv) ?_) ht'
  have e := le_inf e1 (le_inf e2 (le_inf e3 (le_inf e4 (le_inf e5 (le_inf e6 e7)))))
  simp only [MeasureAlgebra.mk_inf] at e
  refine mk_le_of_forall e fun w hw => ?_
  simp only [mem_inter_iff, mem_setOf_eq] at hw ⊢
  obtain ⟨he1, he2, he3, he4, he5, he6, he7⟩ := hw
  rw [← he1, ← he6, ← he7, ← he2, ← he3, ← he4, ← he5, mul_add]

/-- Irreflexivity of `ltDot` on `Rdot`. -/
theorem irrefl_ltDot : ⊤ ≤ Sem.irrefl (Rdot : bSet (randomAlgebra ι)) ltDot := by
  rw [Sem.irrefl]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_compl_of_inf_le_bot ?_
  refine lt_ltDot_elim inf_le_right fun f g Γ₂ h₂ hxf hxg hfg => ?_
  have e := eq_realName_trans hxf hxg
  have h := le_inf e hfg
  rw [MeasureAlgebra.mk_inf] at h
  refine h.trans ?_
  rw [MeasureAlgebra.bot_def]
  apply mk_mono
  rintro w ⟨h1, h2⟩
  simp only [mem_setOf_eq] at h1 h2
  exact absurd (h1 ▸ h2) (lt_irrefl _)

/-- Transitivity of `ltDot` on `Rdot`. -/
theorem trans_ltDot : ⊤ ≤ Sem.trans (Rdot : bSet (randomAlgebra ι)) ltDot := by
  rw [Sem.trans]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun z => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ _
  rw [bv_imp_iff]; intro Γ₄ h₄ hxy
  rw [bv_imp_iff]; intro Γ₅ h₅ hyz
  refine lt_ltDot_elim (h₅.trans hxy) fun f g Γ₆ h₆ hxf hyg hfg => ?_
  refine lt_ltDot_elim (h₆.trans hyz) fun g' h Γ₇ h₇ hyg' hzh hgh => ?_
  have e := eq_realName_trans (h₇.trans hyg) hyg'
  refine le_lt_ltDot ((h₇.trans hxf)) hzh ?_
  refine mk_le_of_forall₃ (h₇.trans hfg) e hgh fun w h1 h2 h3 => ?_
  simp only [mem_setOf_eq] at h1 h2 h3 ⊢
  exact lt_trans h1 (h2 ▸ h3)

/-- Totality of `ltDot` on `Rdot`. -/
theorem total_ltDot : ⊤ ≤ Sem.total (Rdot : bSet (randomAlgebra ι)) ltDot := by
  rw [Sem.total]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ hy
  refine mem_Rdot_elim (h₂.trans hx) fun f Γ₃ h₃ hxf => ?_
  refine mem_Rdot_elim (h₃.trans hy) fun g Γ₄ h₄ hyg => ?_
  have hxf' := h₄.trans hxf
  -- trichotomy of the readings, as an event
  have htri : Γ₄ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w < g.1 w}
      (measurableSet_lt f.2 g.2) ⊔
      (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w = g.1 w}
        (measurableSet_eq_fun f.2 g.2) ⊔
       MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | g.1 w < f.1 w}
        (measurableSet_lt g.2 f.2)) := by
    rw [MeasureAlgebra.mk_sup, MeasureAlgebra.mk_sup]
    refine le_mk_of_forall fun w => ?_
    simp only [mem_union, mem_setOf_eq]
    rcases lt_trichotomy (f.1 w) (g.1 w) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine bv_or_elim' htri (fun Γ₅ h₅ hlt => ?_) fun Γ₅ h₅ hrest => ?_
  · exact le_sup_of_le_left (le_lt_ltDot (h₅.trans hxf') (h₅.trans hyg) hlt)
  · refine le_sup_of_le_right ?_
    refine bv_or_elim' hrest (fun Γ₆ h₆ heq => ?_) fun Γ₆ h₆ hgt => ?_
    · refine le_sup_of_le_left ?_
      exact bv_eq_of_eq_realName (eq_realName_of_eq ((h₆.trans h₅).trans hxf') heq)
        ((h₆.trans h₅).trans hyg)
    · exact le_sup_of_le_right (le_lt_ltDot ((h₆.trans h₅).trans hyg) ((h₆.trans h₅).trans hxf') hgt)

/-- Compatibility of `ltDot` with `plusDot`. -/
theorem addCompat_Rdot : ⊤ ≤ Sem.addCompat (Rdot : bSet (randomAlgebra ι)) plusDot ltDot := by
  rw [Sem.addCompat]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun z => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ _
  refine le_iInf fun u => le_iInf fun v => ?_
  rw [bv_imp_iff]; intro Γ₄ h₄ hxy
  rw [bv_imp_iff]; intro Γ₅ h₅ hxzu
  rw [bv_imp_iff]; intro Γ₆ h₆ hyzv
  refine lt_ltDot_elim ((h₆.trans h₅).trans hxy) fun f g Γ₇ h₇ hxf hyg hfg => ?_
  refine app2_opDot_elim measurable_uncurry_add ((h₇.trans h₆).trans hxzu) fun f' h Γ₈ h₈ hxf' hzh hu => ?_
  refine app2_opDot_elim measurable_uncurry_add ((h₈.trans h₇).trans hyzv) fun g' h' Γ₉ h₉ hyg' hzh' hv => ?_
  have H₇ : Γ₉ ≤ Γ₇ := h₉.trans h₈
  have e1 := eq_realName_trans (H₇.trans hxf) (h₉.trans hxf')
  have e2 := eq_realName_trans (H₇.trans hyg) hyg'
  have e3 := eq_realName_trans (h₉.trans hzh) hzh'
  refine le_lt_ltDot (h₉.trans hu) hv ?_
  have e := le_inf (H₇.trans hfg) (le_inf e1 (le_inf e2 e3))
  simp only [MeasureAlgebra.mk_inf] at e
  refine mk_le_of_forall e fun w hw => ?_
  simp only [mem_inter_iff, mem_setOf_eq] at hw ⊢
  obtain ⟨h0, he1, he2, he3⟩ := hw
  rw [← he1, ← he2, ← he3]
  exact add_lt_add_left h0 _

/-- Products of positive elements of `Rdot` are positive. -/
theorem mulPos_Rdot : ⊤ ≤ Sem.mulPos (Rdot : bSet (randomAlgebra ι)) timesDot ltDot zeroDot := by
  rw [Sem.mulPos]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun u => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ h0x
  rw [bv_imp_iff]; intro Γ₄ h₄ h0y
  rw [bv_imp_iff]; intro Γ₅ h₅ hxyu
  refine lt_ltDot_elim ((h₅.trans h₄).trans h0x) fun z f Γ₆ h₆ hz hxf hzf => ?_
  refine lt_ltDot_elim ((h₆.trans h₅).trans h0y) fun z' g Γ₇ h₇ hz' hyg hz'g => ?_
  refine app2_opDot_elim measurable_uncurry_mul ((h₇.trans h₆).trans hxyu) fun f' g' Γ₈ h₈ hxf' hyg' hu => ?_
  have H₆ : Γ₈ ≤ Γ₆ := h₈.trans h₇
  -- the readings of `zeroDot` are `0`
  have hz0 : Γ₈ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | z.1 w = 0}
      (measurableSet_eq_fun z.2 measurable_const) := by
    have := H₆.trans hz
    rw [zeroDot] at this
    exact eq_realName_trans this (by rw [bv_eq_refl]; exact le_top)
  have hz'0 : Γ₈ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | z'.1 w = 0}
      (measurableSet_eq_fun z'.2 measurable_const) := by
    have := h₈.trans hz'
    rw [zeroDot] at this
    exact eq_realName_trans this (by rw [bv_eq_refl]; exact le_top)
  have e1 := eq_realName_trans (H₆.trans hxf) hxf'
  have e2 := eq_realName_trans (h₈.trans hyg) hyg'
  refine le_lt_ltDot (f := fun _ => (0 : ℝ)) (hf := measurable_const) (by rw [zeroDot, bv_eq_refl]; exact le_top) hu ?_
  have e := le_inf (H₆.trans hzf) (le_inf (h₈.trans hz'g) (le_inf hz0 (le_inf hz'0 (le_inf e1 e2))))
  simp only [MeasureAlgebra.mk_inf] at e
  refine mk_le_of_forall e fun w hw => ?_
  simp only [mem_inter_iff, mem_setOf_eq] at hw ⊢
  obtain ⟨h1, h2, h3, h4, he1, he2⟩ := hw
  rw [← he1, ← he2]
  exact mul_pos (h3 ▸ h1) (h4 ▸ h2)

end axioms

/-- The `n`-th rational, as a real. -/
noncomputable abbrev q (n : ℕ) : ℝ := (ratEnum n : ℝ)

section cut

variable {X : Type*}

open Classical in
/-- The supremum (in `EReal`) of the rationals `q n` with `x ∈ A n`. -/
noncomputable def cutSup (A : ℕ → Set X) (x : X) : EReal :=
  ⨆ n, if x ∈ A n then ((q n : ℝ) : EReal) else ⊥

/-- The real number with cut `{q n | x ∈ A n}` (junk if that set is empty or unbounded). -/
noncomputable def cutReal (A : ℕ → Set X) (x : X) : ℝ :=
  (cutSup A x).toReal

lemma measurable_cutReal [MeasurableSpace X] {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    Measurable (cutReal A) := by
  refine Measurable.ereal_toReal ?_
  refine Measurable.iSup fun n => ?_
  exact Measurable.ite (hA n) measurable_const measurable_const

lemma coe_le_cutSup {A : ℕ → Set X} {x : X} {n : ℕ}
    (hn : x ∈ A n) : ((q n : ℝ) : EReal) ≤ cutSup A x :=
  le_iSup_of_le n (by rw [if_pos hn])

lemma cutSup_le {A : ℕ → Set X} {x : X} {M : ℝ}
    (h : ∀ n, x ∈ A n → q n ≤ M) : cutSup A x ≤ (M : EReal) := by
  refine iSup_le fun n => ?_
  split_ifs with hn
  · exact EReal.coe_le_coe_iff.mpr (h n hn)
  · exact bot_le

lemma cutSup_ne_bot {A : ℕ → Set X} {x : X}
    (h : ∃ n, x ∈ A n) : cutSup A x ≠ ⊥ := by
  obtain ⟨n, hn⟩ := h
  exact ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (q n)) (coe_le_cutSup hn))

lemma cutSup_ne_top {A : ℕ → Set X} {x : X}
    (h : ∃ M : ℝ, ∀ n, x ∈ A n → q n ≤ M) : cutSup A x ≠ ⊤ := by
  obtain ⟨M, hM⟩ := h
  exact ne_top_of_le_ne_top (EReal.coe_ne_top M) (cutSup_le hM)

lemma coe_cutReal {A : ℕ → Set X} {x : X}
    (h1 : ∃ n, x ∈ A n) (h2 : ∃ M : ℝ, ∀ n, x ∈ A n → q n ≤ M) :
    ((cutReal A x : ℝ) : EReal) = cutSup A x :=
  EReal.coe_toReal (cutSup_ne_top h2) (cutSup_ne_bot h1)

/-- If every rational below `r` belongs to the cut, then `r ≤ cutReal A x`. -/
lemma le_cutReal {A : ℕ → Set X} {x : X}
    (h1 : ∃ n, x ∈ A n) (h2 : ∃ M : ℝ, ∀ n, x ∈ A n → q n ≤ M) {r : ℝ}
    (h : ∀ n, q n < r → x ∈ A n) : r ≤ cutReal A x := by
  refine le_of_forall_rat_lt_imp_le fun s hs => ?_
  have hs' : q (ratEnum.symm s) < r := by simp only [q, Equiv.apply_symm_apply]; exact hs
  have := coe_le_cutSup (h _ hs')
  rw [← coe_cutReal h1 h2] at this
  simpa [q] using EReal.coe_le_coe_iff.mp this

/-- If every rational of the cut is `< r`, then `cutReal A x ≤ r`. -/
lemma cutReal_le {A : ℕ → Set X} {x : X}
    (h1 : ∃ n, x ∈ A n) {r : ℝ} (h : ∀ n, x ∈ A n → q n < r) : cutReal A x ≤ r := by
  have h2 : ∃ M : ℝ, ∀ n, x ∈ A n → q n ≤ M := ⟨r, fun n hn => (h n hn).le⟩
  have := cutSup_le (M := r) fun n hn => (h n hn).le
  rw [← coe_cutReal h1 h2] at this
  exact EReal.coe_le_coe_iff.mp this

end cut

/-! ### The completeness axiom for `Rdot` -/

/-- The event on which the cut `{qₙ | x ∈ A n}` is nonempty and bounded above. -/
def goodEvent (A : ℕ → Set (RandomAlgebra.Ω ι)) : Set (RandomAlgebra.Ω ι) :=
  {x | (∃ n, x ∈ A n) ∧ ∃ M : ℚ, ∀ n, x ∈ A n → q n ≤ M}

lemma measurableSet_boundedEvent {A : ℕ → Set (RandomAlgebra.Ω ι)}
    (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet {x : RandomAlgebra.Ω ι | ∃ M : ℚ, ∀ n, x ∈ A n → q n ≤ M} := by
  have : {x : RandomAlgebra.Ω ι | ∃ M : ℚ, ∀ n, x ∈ A n → q n ≤ M} =
      ⋃ M : ℚ, ⋂ n, ((A n)ᶜ ∪ {_x | q n ≤ M}) := by
    ext x; simp only [mem_setOf_eq, mem_iUnion, mem_iInter, mem_union, mem_compl_iff]
    simp only [imp_iff_not_or]
  rw [this]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun n =>
    (hA n).compl.union (MeasurableSet.const _)

lemma measurableSet_goodEvent {A : ℕ → Set (RandomAlgebra.Ω ι)} (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (goodEvent A) := by
  have : goodEvent A = (⋃ n, A n) ∩ {x | ∃ M : ℚ, ∀ n, x ∈ A n → q n ≤ M} := by
    ext x; simp [goodEvent]
  rw [this]
  exact (MeasurableSet.iUnion hA).inter (measurableSet_boundedEvent hA)

lemma goodEvent_bdd {A : ℕ → Set (RandomAlgebra.Ω ι)} {x : RandomAlgebra.Ω ι}
    (hx : x ∈ goodEvent A) : ∃ M : ℝ, ∀ n, x ∈ A n → q n ≤ M := by
  obtain ⟨M, hM⟩ := hx.2
  exact ⟨M, hM⟩

section congr

variable {Γ : randomAlgebra ι} {s s' u u' : bSet (randomAlgebra ι)}

lemma le_ltDot_congr_left (h1 : Γ ≤ s =ᴮ s') (h2 : Γ ≤ Sem.le ltDot s' u) :
    Γ ≤ Sem.le ltDot s u := by
  rw [Sem.le] at h2 ⊢
  refine bv_or_elim' h2 (fun Γ' h' hlt => le_sup_of_le_left ?_) fun Γ' h' heq =>
    le_sup_of_le_right ?_
  · rw [Sem.lt] at hlt ⊢
    have hp : Γ' ≤ pair s' u =ᴮ pair s u := by
      refine (h'.trans h1).trans ?_
      rw [bv_eq_symm (x := s)]
      exact subst_congr_pair_left
    exact (le_inf hp hlt).trans subst_congr_mem_left
  · exact (le_inf (h'.trans h1) heq).trans bv_eq_trans

lemma le_ltDot_congr_right (h1 : Γ ≤ u =ᴮ u') (h2 : Γ ≤ Sem.le ltDot s u') :
    Γ ≤ Sem.le ltDot s u := by
  rw [Sem.le] at h2 ⊢
  refine bv_or_elim' h2 (fun Γ' h' hlt => le_sup_of_le_left ?_) fun Γ' h' heq =>
    le_sup_of_le_right ?_
  · rw [Sem.lt] at hlt ⊢
    have hp : Γ' ≤ pair s u' =ᴮ pair s u := by
      refine (h'.trans h1).trans ?_
      rw [bv_eq_symm (x := u)]
      exact subst_congr_pair_right
    exact (le_inf hp hlt).trans subst_congr_mem_left
  · have := le_inf heq (h'.trans h1)
    rw [bv_eq_symm (x := u)] at this
    exact this.trans bv_eq_trans

/-- Modus ponens in context. -/
lemma bv_mp {a c : randomAlgebra ι} (h1 : Γ ≤ a ⟹ c) (h2 : Γ ≤ a) : Γ ≤ c :=
  (le_inf h1 h2).trans bv_imp_elim

/-- A countable family of implications between events, as one event. -/
lemma le_mk_iInter_of_forall {s t : ℕ → Set (RandomAlgebra.Ω ι)} {hs : ∀ n, MeasurableSet (s n)}
    {ht : ∀ n, MeasurableSet (t n)}
    (h : ∀ n, Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (s n) (hs n) ≤
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (t n) (ht n)) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋂ n, (s n)ᶜ ∪ t n)
      (MeasurableSet.iInter fun n => (hs n).compl.union (ht n)) := by
  have e : (⨅ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) ((s n)ᶜ ∪ t n)
      ((hs n).compl.union (ht n))) = MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        (⋂ n, (s n)ᶜ ∪ t n) (MeasurableSet.iInter fun n => (hs n).compl.union (ht n)) :=
    MeasureAlgebra.iInf_mk _ _
  rw [← e]
  refine le_iInf fun n => ?_
  have h' := deduction.mp (h n)
  rw [imp_iff, MeasureAlgebra.mk_compl, MeasureAlgebra.mk_sup] at h'
  exact h'

end congr

/-- **Dedekind completeness of `Rdot`.**  Given a name `S` of a nonempty bounded-above set of
reals, the supremum is read off from the events `‖∃ s ∈ S, qₙ < s‖`, `n ∈ ℕ`. -/
theorem complete_Rdot : ⊤ ≤ Sem.complete (Rdot : bSet (randomAlgebra ι)) ltDot := by
  classical
  rw [Sem.complete]
  refine le_iInf fun S => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hSpow
  rw [bv_imp_iff]; intro Γ₂ h₂ hne
  rw [bv_imp_iff]; intro Γ₃ h₃ hbd
  have hSsub : Γ₁ ≤ S ⊆ᴮ Rdot := bv_powerset_spec.mpr hSpow
  -- the Boolean values `‖∃ s ∈ S, qₙ < s‖` and their representatives `A n`
  obtain ⟨A, hA, hAeq⟩ : ∃ (A : ℕ → Set (RandomAlgebra.Ω ι)) (hA : ∀ n, MeasurableSet (A n)),
      ∀ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (A n) (hA n) =
        ⨆ f : MeasReal ι, (realName f.1 f.2 ∈ᴮ S) ⊓
          MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < f.1 w}
            (measurableSet_lt measurable_const f.2) := by
    choose A hA hAeq using fun n => MeasureAlgebra.exists_rep
      (⨆ f : MeasReal ι, (realName f.1 f.2 ∈ᴮ S) ⊓
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < f.1 w}
          (measurableSet_lt measurable_const f.2))
    exact ⟨A, hA, hAeq⟩
  -- (K1): if `realName f ∈ S` then `‖qₙ < f‖ ≤ [A n]`
  have K1 : ∀ (f : MeasReal ι) (Γ : randomAlgebra ι), Γ ≤ realName f.1 f.2 ∈ᴮ S → ∀ n,
      Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < f.1 w}
        (measurableSet_lt measurable_const f.2) ≤
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (A n) (hA n) := by
    intro f Γ hf n
    rw [hAeq n]
    exact le_iSup_of_le f (inf_le_inf_right _ hf)
  -- (K2): if `realName k` bounds `S` from above then `[A n] ≤ ‖qₙ < k‖`
  have K2 : ∀ (k : MeasReal ι) (Γ : randomAlgebra ι),
      Γ ≤ (⨅ s : bSet (randomAlgebra ι), s ∈ᴮ S ⟹ Sem.le ltDot s (realName k.1 k.2)) → ∀ n,
      Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (A n) (hA n) ≤
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < k.1 w}
          (measurableSet_lt measurable_const k.2) := by
    intro k Γ hk n
    rw [hAeq n]
    refine bv_cases_right fun f => ?_
    have h1 : Γ ⊓ (realName f.1 f.2 ∈ᴮ S) ≤
        Sem.le ltDot (realName f.1 f.2) (realName k.1 k.2) := by
      rw [deduction]; exact hk.trans (iInf_le _ _)
    rw [le_ltDot_realName] at h1
    have h2 : Γ ⊓ ((realName f.1 f.2 ∈ᴮ S) ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {w | q n < f.1 w} (measurableSet_lt measurable_const f.2)) ≤
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | f.1 w ≤ k.1 w}
          (measurableSet_le f.2 k.2) ⊓
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < f.1 w}
          (measurableSet_lt measurable_const f.2) :=
      le_inf (le_trans (le_inf inf_le_left (inf_le_right.trans inf_le_left)) h1)
        (inf_le_right.trans inf_le_right)
    refine h2.trans ?_
    rw [MeasureAlgebra.mk_inf]
    apply mk_mono
    rintro w ⟨hw1, hw2⟩
    simp only [mem_setOf_eq] at hw1 hw2 ⊢
    exact lt_of_lt_of_le hw2 hw1
  -- every element of `S` is a real: `s ∈ S → ∃ f, s = realName f ∧ realName f ∈ S`
  have memS : ∀ (s : bSet (randomAlgebra ι)) (Γ : randomAlgebra ι) (b : randomAlgebra ι),
      Γ ≤ Γ₁ → Γ ≤ s ∈ᴮ S →
      (∀ (f : MeasReal ι) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ s =ᴮ realName f.1 f.2 →
        Γ' ≤ realName f.1 f.2 ∈ᴮ S → Γ' ≤ b) → Γ ≤ b := by
    intro s Γ b hΓ hs H
    have hsR : Γ ≤ s ∈ᴮ Rdot := mem_of_mem_subset (hΓ.trans hSsub) hs
    refine mem_Rdot_elim hsR fun f Γ' h' hsf => ?_
    exact H f Γ' h' hsf (subst_congr_mem_left' hsf (h'.trans hs))
  -- an upper bound `b` of `S` in `R` can be read as `realName k`, and bounds `S`
  have hbd' : ∀ (b : bSet (randomAlgebra ι)) (Γ : randomAlgebra ι), Γ ≤ b ∈ᴮ Rdot →
      Γ ≤ (⨅ s : bSet (randomAlgebra ι), s ∈ᴮ S ⟹ Sem.le ltDot s b) →
      ∀ c : randomAlgebra ι, (∀ (k : MeasReal ι) (Γ' : randomAlgebra ι), Γ' ≤ Γ →
        Γ' ≤ b =ᴮ realName k.1 k.2 →
        Γ' ≤ (⨅ s : bSet (randomAlgebra ι), s ∈ᴮ S ⟹ Sem.le ltDot s (realName k.1 k.2)) →
        Γ' ≤ c) → Γ ≤ c := by
    intro b Γ hbR hub c H
    refine mem_Rdot_elim hbR fun k Γ' h' hbk => ?_
    refine H k Γ' h' hbk ?_
    refine le_iInf fun s => ?_
    rw [bv_imp_iff]; intro Γ'' h'' hs
    have h0 : Γ'' ≤ Sem.le ltDot s b :=
      bv_mp (((h''.trans h').trans hub).trans (iInf_le _ s)) hs
    refine le_ltDot_congr_right ?_ h0
    rw [bv_eq_symm]; exact h''.trans hbk
  -- the good event: the cut is nonempty and bounded above
  have hgood : Γ₃ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (goodEvent A)
      (measurableSet_goodEvent hA) := by
    have hg1 : Γ₃ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋃ n, A n)
        (MeasurableSet.iUnion hA) := by
      have hne' : Γ₂ ≤ ⨆ s : bSet (randomAlgebra ι), s ∈ᴮ S := nonempty_iff_exists_mem.mp hne
      refine (le_inf le_rfl (h₃.trans hne')).trans (bv_cases_right fun s => ?_)
      refine memS s _ _ (inf_le_left.trans (h₃.trans h₂)) inf_le_right fun f Γ' h' _ hfS => ?_
      have e : (⨆ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (A n) (hA n)) =
          MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋃ n, A n) (MeasurableSet.iUnion hA) :=
        MeasureAlgebra.iSup_mk _ _
      rw [← e]
      have htop : (⨆ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < f.1 w}
          (measurableSet_lt measurable_const f.2)) = ⊤ := by
        rw [MeasureAlgebra.iSup_mk]
        refine mk_eq_top_of_forall _ fun w => ?_
        obtain ⟨r, hr⟩ := exists_rat_lt (f.1 w)
        refine mem_iUnion.mpr ⟨ratEnum.symm r, ?_⟩
        simp only [mem_setOf_eq, q, Equiv.apply_symm_apply]; exact hr
      calc Γ' = Γ' ⊓ ⨆ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | q n < f.1 w}
            (measurableSet_lt measurable_const f.2) := by rw [htop, inf_top_eq]
        _ ≤ _ := bv_cases_right fun n => le_iSup_of_le n (K1 f Γ' hfS n)
    have hg2 : Γ₃ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {x | ∃ M : ℚ, ∀ n, x ∈ A n → q n ≤ M} (measurableSet_boundedEvent hA) := by
      refine (le_inf le_rfl hbd).trans (bv_cases_right fun b => ?_)
      refine hbd' b _ (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right) _
        fun k Γ' _ _ hub => ?_
      have h5 := le_mk_iInter_of_forall (K2 k Γ' hub)
      refine mk_le_of_forall h5 fun x hx => ?_
      simp only [mem_iInter, mem_union, mem_compl_iff, mem_setOf_eq] at hx ⊢
      obtain ⟨M, hM⟩ := exists_rat_gt (k.1 x)
      refine ⟨M, fun n hn => ?_⟩
      rcases hx n with h | h
      · exact absurd hn h
      · exact (lt_trans h hM).le
    have h := le_inf hg1 hg2
    rw [MeasureAlgebra.mk_inf] at h
    refine mk_le_of_forall h fun x hx => ?_
    simp only [mem_inter_iff, mem_iUnion] at hx
    exact ⟨hx.1, hx.2⟩
  -- the supremum
  refine le_iSup_of_le (realName (cutReal A) (measurable_cutReal hA)) ?_
  refine le_inf realName_mem_Rdot (le_inf ?_ ?_)
  · -- upper bound
    refine le_iInf fun s => ?_
    rw [bv_imp_iff]; intro Γ' h' hs
    refine memS s Γ' _ (h'.trans (h₃.trans h₂)) hs fun f Γ'' h'' hsf hfS => ?_
    refine le_ltDot_congr_left hsf ?_
    rw [le_ltDot_realName]
    have h4 := le_mk_iInter_of_forall (K1 f Γ'' hfS)
    refine mk_le_of_forall₂ ((h''.trans h').trans hgood) h4 fun x hx1 hx2 => ?_
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_setOf_eq] at hx2 ⊢
    refine le_cutReal hx1.1 (goodEvent_bdd hx1) fun n hn => ?_
    rcases hx2 n with h | h
    · exact absurd hn h
    · exact h
  · -- least upper bound
    refine le_iInf fun v => ?_
    rw [bv_imp_iff]; intro Γ' h' hv
    rw [bv_imp_iff]; intro Γ'' h'' hub
    refine hbd' v Γ'' (h''.trans hv) hub _ fun k Γ₆ h₆ hvk hub' => ?_
    refine le_ltDot_congr_right hvk ?_
    rw [le_ltDot_realName]
    have h5 := le_mk_iInter_of_forall (K2 k Γ₆ hub')
    refine mk_le_of_forall₂ ((h₆.trans (h''.trans h')).trans hgood) h5 fun x hx1 hx2 => ?_
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_setOf_eq] at hx2 ⊢
    refine cutReal_le hx1.1 fun n hn => ?_
    rcases hx2 n with h | h
    · exact absurd hn h
    · exact h


/-! ### Assembly -/

/-- **`Rdot` is a complete ordered field**: the names `Rdot, plusDot, timesDot, ltDot, zeroDot,
oneDot` satisfy (with Boolean value `⊤`) the twenty axioms of `Sem.completeOrderedField`, i.e. the
antecedent of `Erdos501_f` (`Semantics.lean`). -/
theorem completeOrderedField_Rdot :
    ⊤ ≤ Sem.completeOrderedField (Rdot : bSet (randomAlgebra ι)) plusDot timesDot ltDot zeroDot
      oneDot := by
  rw [Sem.completeOrderedField]
  refine le_inf (isOp2_opDot _) (le_inf (isOp2_opDot _) (le_inf zeroDot_mem (le_inf oneDot_mem
    (le_inf (assoc_opDot _ add_assoc) (le_inf (comm_opDot _ add_comm)
    (le_inf (ident_opDot _ 0 add_zero) (le_inf addInv_plusDot (le_inf (assoc_opDot _ mul_assoc)
    (le_inf (comm_opDot _ mul_comm) (le_inf (ident_opDot _ 1 mul_one) (le_inf mulInv_timesDot
    (le_inf zeroDot_ne_oneDot (le_inf distrib_Rdot (le_inf irrefl_ltDot (le_inf trans_ltDot
    (le_inf total_ltDot (le_inf addCompat_Rdot (le_inf mulPos_Rdot complete_Rdot))))))))))))))))))

/-- Consequently, `⊤ ⊩[V (randomAlgebra ι)] Erdos501_f` follows from the Erdős property for the
internal reals `Rdot` **together with** the (internal) uniqueness of complete ordered fields; the
former is the target of the remaining steps S3–S6 of `PLAN.md`, the latter is unit (F8). -/
theorem erdosProperty_Rdot_of_forced {Γ : randomAlgebra ι}
    (h : Γ ⊩[V (randomAlgebra ι)] Erdos501_f) :
    Γ ≤ Sem.erdosProperty (Rdot : bSet (randomAlgebra ι)) plusDot ltDot zeroDot oneDot := by
  rw [forced_Erdos501_f_iff] at h
  exact (le_inf le_rfl (le_top.trans completeOrderedField_Rdot)).trans
    (h Rdot plusDot timesDot ltDot zeroDot oneDot)


end Flypitch.Erdos501.RandomForcing
