/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The internal isomorphism between an arbitrary internal complete ordered field and `Rdot`
(unit (F8), part 2, `PLAN.md` §6).
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.InternalField
import ErdosProblems.Erdos501.Flypitch4.Erdos501.RealReading

set_option relaxedAutoImplicit true

/-!
# The internal isomorphism `F ≅ Rdot` (unit (F8), part 2)

Let `F` be six names in `bSet (randomAlgebra ι)` with `Γ ≤ F.COF`.  For a name `r` (an element of
`F.R` on `Γ`), the Boolean values `‖dyR m k < r‖` of the comparisons with the internal dyadics are
events; choosing representatives `cutSet F r d`, the **reading** of `r` is

  `rd F r x = sup {m/2^k | x ∈ cutSet F r (m, k)}`,

a measurable real function.  The dyadic cut of `r` is (on `Γ`) nonempty, bounded, downward closed and
without maximum (`InternalField.lean`: Archimedean property, `dyR_lt_of_cross`, `dense`), so on the
event `cutGood` the reading is the real with exactly that cut (`mem_iff_lt_dyReal`), and

  `Γ ⊓ ‖dyR d < r‖ = Γ ⊓ [{x | dyVal d < rd F r x}]`      (`lt_dyR_le_mk_rd`, `mk_rd_le_lt_dyR`).

The name `psi F = {(r, realName (rd F r)) | r ∈ F.R}` is then (on `Γ`) a function `F.R → Rdot`
which preserves and reflects `<` (`rd_lt_of_lt`, `lt_of_rd_lt`), is injective (`eq_of_rd_eq`),
additive (`rd_add`), sends `zero, one` to `0, 1` (`rd_zero`, `rd_one`), and is surjective
(`psi_surj`, from the internal completeness of `F` applied to the cut set of a real name).
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice
open scoped ENNReal Flypitch

namespace Flypitch.Erdos501.RandomForcing

/-! ### Dyadic rationals as reals -/

/-- Dyadic indices `(m, k)` for `m / 2^k`. -/
abbrev Dy : Type := ℤ × ℕ

/-- The value `m / 2^k` of a dyadic index. -/
noncomputable def dyVal (d : Dy) : ℝ := (d.1 : ℝ) / 2 ^ d.2

lemma dyVal_lt_iff {d d' : Dy} : dyVal d < dyVal d' ↔ d.1 * 2 ^ d'.2 < d'.1 * 2 ^ d.2 := by
  unfold dyVal
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

lemma dyVal_le_iff {d d' : Dy} : dyVal d ≤ dyVal d' ↔ d.1 * 2 ^ d'.2 ≤ d'.1 * 2 ^ d.2 := by
  unfold dyVal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

lemma dyVal_mk (m : ℤ) (k : ℕ) : dyVal (m, k) = (m : ℝ) / 2 ^ k := rfl

@[simp] lemma dyVal_zero_zero : dyVal (0, 0) = 0 := by simp [dyVal]
@[simp] lemma dyVal_one_zero : dyVal (1, 0) = 1 := by simp [dyVal]

/-- Sum of dyadics, at the common denominator. -/
def dyAdd (d d' : Dy) : Dy := (d.1 * 2 ^ d'.2 + d'.1 * 2 ^ d.2, d.2 + d'.2)

/-- Difference of dyadics, at the common denominator. -/
def dySub (d d' : Dy) : Dy := (d.1 * 2 ^ d'.2 - d'.1 * 2 ^ d.2, d.2 + d'.2)

lemma dyVal_dyAdd (d d' : Dy) : dyVal (dyAdd d d') = dyVal d + dyVal d' := by
  unfold dyVal dyAdd
  simp only
  rw [pow_add, div_add_div _ _ (by positivity) (by positivity)]
  push_cast
  ring

lemma dyVal_dySub (d d' : Dy) : dyVal (dySub d d') = dyVal d - dyVal d' := by
  unfold dyVal dySub
  simp only
  rw [pow_add, div_sub_div _ _ (by positivity) (by positivity)]
  push_cast
  ring

/-- Density of the dyadics in `ℝ`. -/
lemma exists_dyVal_btwn {a b : ℝ} (h : a < b) : ∃ d : Dy, a < dyVal d ∧ dyVal d < b := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr h) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(⌊a * 2 ^ k⌋ + 1, k), ?_, ?_⟩
  · rw [dyVal_mk, lt_div_iff₀ (by positivity)]
    push_cast
    exact Int.lt_floor_add_one _
  · rw [dyVal_mk, div_lt_iff₀ (by positivity)]
    push_cast
    have h1 : (⌊a * 2 ^ k⌋ : ℝ) ≤ a * 2 ^ k := Int.floor_le _
    have h2 : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [one_div_pow]
    rw [h2, div_lt_iff₀ (by positivity)] at hk
    linarith

lemma exists_dyVal_gt (a : ℝ) : ∃ d : Dy, a < dyVal d := by
  obtain ⟨d, hd, _⟩ := exists_dyVal_btwn (lt_add_one a)
  exact ⟨d, hd⟩

lemma exists_dyVal_lt (a : ℝ) : ∃ d : Dy, dyVal d < a := by
  obtain ⟨d, _, hd⟩ := exists_dyVal_btwn (sub_one_lt a)
  exact ⟨d, hd⟩

/-! ### Cuts indexed by dyadics -/

section cut

variable {X : Type*}

open Classical in
/-- The supremum (in `EReal`) of the dyadics `dyVal d` with `x ∈ S d`. -/
noncomputable def dySup (S : Dy → Set X) (x : X) : EReal :=
  ⨆ d, if x ∈ S d then ((dyVal d : ℝ) : EReal) else ⊥

/-- The real number with dyadic cut `{dyVal d | x ∈ S d}` (junk if empty or unbounded). -/
noncomputable def dyReal (S : Dy → Set X) (x : X) : ℝ := (dySup S x).toReal

lemma measurable_dyReal [MeasurableSpace X] {S : Dy → Set X} (hS : ∀ d, MeasurableSet (S d)) :
    Measurable (dyReal S) := by
  refine Measurable.ereal_toReal ?_
  refine Measurable.iSup fun d => ?_
  exact Measurable.ite (hS d) measurable_const measurable_const

lemma coe_le_dySup {S : Dy → Set X} {x : X} {d : Dy} (hd : x ∈ S d) :
    ((dyVal d : ℝ) : EReal) ≤ dySup S x :=
  le_iSup_of_le d (by rw [if_pos hd])

lemma dySup_le {S : Dy → Set X} {x : X} {M : ℝ} (h : ∀ d, x ∈ S d → dyVal d ≤ M) :
    dySup S x ≤ (M : EReal) := by
  refine iSup_le fun d => ?_
  split_ifs with hd
  · exact EReal.coe_le_coe_iff.mpr (h d hd)
  · exact bot_le

lemma dySup_ne_bot {S : Dy → Set X} {x : X} (h : ∃ d, x ∈ S d) : dySup S x ≠ ⊥ := by
  obtain ⟨d, hd⟩ := h
  exact ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (dyVal d)) (coe_le_dySup hd))

lemma dySup_ne_top {S : Dy → Set X} {x : X} (h : ∃ M : ℝ, ∀ d, x ∈ S d → dyVal d ≤ M) :
    dySup S x ≠ ⊤ := by
  obtain ⟨M, hM⟩ := h
  exact ne_top_of_le_ne_top (EReal.coe_ne_top M) (dySup_le hM)

lemma coe_dyReal {S : Dy → Set X} {x : X} (h1 : ∃ d, x ∈ S d)
    (h2 : ∃ M : ℝ, ∀ d, x ∈ S d → dyVal d ≤ M) : ((dyReal S x : ℝ) : EReal) = dySup S x :=
  EReal.coe_toReal (dySup_ne_top h2) (dySup_ne_bot h1)

lemma dyVal_le_dyReal {S : Dy → Set X} {x : X} (h2 : ∃ M : ℝ, ∀ d, x ∈ S d → dyVal d ≤ M) {d : Dy}
    (hd : x ∈ S d) : dyVal d ≤ dyReal S x := by
  have := coe_le_dySup hd
  rw [← coe_dyReal ⟨d, hd⟩ h2] at this
  exact EReal.coe_le_coe_iff.mp this

lemma dyReal_le {S : Dy → Set X} {x : X} (h1 : ∃ d, x ∈ S d) {r : ℝ}
    (h : ∀ d, x ∈ S d → dyVal d ≤ r) : dyReal S x ≤ r := by
  have := dySup_le (M := r) h
  rw [← coe_dyReal h1 ⟨r, h⟩] at this
  exact EReal.coe_le_coe_iff.mp this

lemma exists_of_lt_dyReal {S : Dy → Set X} {x : X} (h1 : ∃ d, x ∈ S d)
    (h2 : ∃ M : ℝ, ∀ d, x ∈ S d → dyVal d ≤ M) {r : ℝ} (h : r < dyReal S x) :
    ∃ d, x ∈ S d ∧ r < dyVal d := by
  by_contra hcon
  push_neg at hcon
  exact absurd h (not_lt.mpr (dyReal_le h1 hcon))

/-- The good points of a family of cut events: the cut is nonempty, bounded, downward closed and
has no maximum. -/
def cutGood (S : Dy → Set X) : Set X :=
  (⋃ d, S d) ∩ ((⋃ d, (S d)ᶜ) ∩
    ((⋂ d, ⋂ d', {x | dyVal d' < dyVal d → x ∈ S d → x ∈ S d'}) ∩
      ⋂ d, {x | x ∈ S d → ∃ d', dyVal d < dyVal d' ∧ x ∈ S d'}))

lemma mem_cutGood {S : Dy → Set X} {x : X} :
    x ∈ cutGood S ↔ (∃ d, x ∈ S d) ∧ (∃ d, x ∉ S d) ∧
      (∀ d d', dyVal d' < dyVal d → x ∈ S d → x ∈ S d') ∧
      (∀ d, x ∈ S d → ∃ d', dyVal d < dyVal d' ∧ x ∈ S d') := by
  simp only [cutGood, mem_inter_iff, mem_iUnion, mem_compl_iff, mem_iInter, mem_setOf_eq]

lemma measurableSet_downClosed [MeasurableSpace X] {S : Dy → Set X} (hS : ∀ d, MeasurableSet (S d))
    (d d' : Dy) : MeasurableSet {x | dyVal d' < dyVal d → x ∈ S d → x ∈ S d'} := by
  have e : {x | dyVal d' < dyVal d → x ∈ S d → x ∈ S d'} =
      {x | dyVal d' < dyVal d}ᶜ ∪ ((S d)ᶜ ∪ S d') := by
    ext x; simp only [mem_setOf_eq, mem_union, Set.mem_compl_iff]; tauto
  rw [e]
  exact (MeasurableSet.const _).compl.union ((hS d).compl.union (hS d'))

lemma measurableSet_noMax [MeasurableSpace X] {S : Dy → Set X} (hS : ∀ d, MeasurableSet (S d))
    (d : Dy) : MeasurableSet {x | x ∈ S d → ∃ d', dyVal d < dyVal d' ∧ x ∈ S d'} := by
  have e : {x | x ∈ S d → ∃ d', dyVal d < dyVal d' ∧ x ∈ S d'} =
      (S d)ᶜ ∪ ⋃ d', {x | dyVal d < dyVal d' ∧ x ∈ S d'} := by
    ext x; simp only [mem_setOf_eq, mem_union, Set.mem_compl_iff, mem_iUnion]; tauto
  rw [e]
  refine (hS d).compl.union (MeasurableSet.iUnion fun d' => ?_)
  have e' : {x | dyVal d < dyVal d' ∧ x ∈ S d'} = {x | dyVal d < dyVal d'} ∩ S d' := rfl
  rw [e']
  exact (MeasurableSet.const _).inter (hS d')

lemma measurableSet_cutGood [MeasurableSpace X] {S : Dy → Set X} (hS : ∀ d, MeasurableSet (S d)) :
    MeasurableSet (cutGood S) :=
  (MeasurableSet.iUnion hS).inter ((MeasurableSet.iUnion fun d => (hS d).compl).inter
    ((MeasurableSet.iInter fun d => MeasurableSet.iInter fun d' => measurableSet_downClosed hS d d').inter
      (MeasurableSet.iInter fun d => measurableSet_noMax hS d)))

lemma cutGood_bdd {S : Dy → Set X} {x : X} (hx : x ∈ cutGood S) :
    ∃ M : ℝ, ∀ d, x ∈ S d → dyVal d ≤ M := by
  rw [mem_cutGood] at hx
  obtain ⟨_, ⟨d₀, hd₀⟩, hdown, _⟩ := hx
  refine ⟨dyVal d₀, fun d hd => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hd₀ (hdown d d₀ hlt hd)

/-- **The reading lemma**: on the good event, `x ∈ S d ↔ dyVal d < dyReal S x`. -/
lemma mem_iff_lt_dyReal {S : Dy → Set X} {x : X} (hx : x ∈ cutGood S) (d : Dy) :
    x ∈ S d ↔ dyVal d < dyReal S x := by
  have hbdd := cutGood_bdd hx
  rw [mem_cutGood] at hx
  obtain ⟨hne, _, hdown, hnomax⟩ := hx
  constructor
  · intro hd
    obtain ⟨d', hdd', hd'⟩ := hnomax d hd
    exact lt_of_lt_of_le hdd' (dyVal_le_dyReal hbdd hd')
  · intro h
    obtain ⟨d', hd', hdd'⟩ := exists_of_lt_dyReal hne hbdd h
    exact hdown d' d hdd' hd'

/-- On the good event, two cut families with the same members give the same real. -/
lemma dyReal_eq_of_forall {S T : Dy → Set X} {x : X} (hS : x ∈ cutGood S) (hT : x ∈ cutGood T)
    (h : ∀ d, x ∈ S d ↔ x ∈ T d) : dyReal S x = dyReal T x := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨d, h1, h2⟩ := exists_dyVal_btwn hlt
    have := (mem_iff_lt_dyReal hT d).mpr h2
    rw [← h] at this
    exact absurd ((mem_iff_lt_dyReal hS d).mp this) (not_lt.mpr h1.le)
  · obtain ⟨d, h1, h2⟩ := exists_dyVal_btwn hlt
    have := (mem_iff_lt_dyReal hS d).mpr h2
    rw [h] at this
    exact absurd ((mem_iff_lt_dyReal hT d).mp this) (not_lt.mpr h1.le)

/-- On the good event, the real is determined by the cut: `∀ d, (dyVal d < a ↔ dyVal d < dyReal S x)`
forces `a = dyReal S x`. -/
lemma eq_dyReal_of_forall {S : Dy → Set X} {x : X} (hS : x ∈ cutGood S) {a : ℝ}
    (h : ∀ d, dyVal d < a ↔ x ∈ S d) : a = dyReal S x := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨d, h1, h2⟩ := exists_dyVal_btwn hlt
    have := (mem_iff_lt_dyReal hS d).mpr h2
    exact absurd ((h d).mpr this) (not_lt.mpr h1.le)
  · obtain ⟨d, h1, h2⟩ := exists_dyVal_btwn hlt
    have := (h d).mp h2
    exact absurd ((mem_iff_lt_dyReal hS d).mp this) (not_lt.mpr h1.le)

end cut

/-! ### Measure-algebra helpers -/

section malg
variable {ι : Type} {Γ : randomAlgebra ι}

/-- `mk` of a countable intersection is the infimum. -/
lemma le_mk_iInter' {κ : Type*} [Countable κ] {s : κ → Set (RandomAlgebra.Ω ι)}
    (hs : ∀ i, MeasurableSet (s i))
    (h : ∀ i, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (s i) (hs i)) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋂ i, s i) (MeasurableSet.iInter hs) := by
  have e := MeasureAlgebra.iInf_mk (μ := RandomAlgebra.μ_random ι) s hs
  rw [← e]
  exact le_iInf h

lemma mk_iUnion_eq {κ : Type*} [Countable κ] (s : κ → Set (RandomAlgebra.Ω ι))
    (hs : ∀ i, MeasurableSet (s i)) :
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋃ i, s i) (MeasurableSet.iUnion hs) =
      ⨆ i, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (s i) (hs i) :=
  (MeasureAlgebra.iSup_mk s hs).symm

/-- `Γ ⊓ [s] ≤ [t]` gives `Γ ≤ [sᶜ ∪ t]`. -/
lemma le_mk_compl_union {s t : Set (RandomAlgebra.Ω ι)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs ≤
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) t ht) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (sᶜ ∪ t) (hs.compl.union ht) := by
  show Γ ≤ imp (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs)
    (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) t ht)
  exact deduction.mp h

lemma le_mk_of_le {s : Set (RandomAlgebra.Ω ι)} {hs : MeasurableSet s} {a : randomAlgebra ι}
    (e : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs = a) (h : Γ ≤ a) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs := e ▸ h

lemma le_bot_of_mk_le {s : Set (RandomAlgebra.Ω ι)} {hs : MeasurableSet s}
    (h : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs) (H : ∀ w, w ∉ s) : Γ ≤ ⊥ := by
  rw [MeasureAlgebra.bot_def]
  exact h.trans (mk_mono fun w hw => absurd hw (H w))

lemma measurableSet_iff_mem (P : Prop) {s : Set (RandomAlgebra.Ω ι)} (hs : MeasurableSet s) :
    MeasurableSet {w | P ↔ w ∈ s} := by
  by_cases hP : P
  · simp only [hP, true_iff, setOf_mem_eq]; exact hs
  · simp only [hP, false_iff]; exact hs.compl

/-- `∀ s ∈ C, φ s` from the indexed form, for `B_ext φ`. -/
lemma le_iInf_mem_imp {C : bSet (randomAlgebra ι)} {φ : bSet (randomAlgebra ι) → randomAlgebra ι}
    (hφ : B_ext φ) (h : ∀ i, Γ ⊓ C.bval i ≤ φ (C.func i)) :
    Γ ≤ ⨅ s : bSet (randomAlgebra ι), s ∈ᴮ C ⟹ φ s := by
  refine le_iInf fun s => ?_
  rw [bv_imp_iff]; intro Γ' h' hs
  rw [mem_unfold] at hs
  refine BV.iSup_elim hs fun i Γ'' h'' hi => ?_
  have h1 : Γ'' ≤ φ (C.func i) := (le_inf (h''.trans h') (bv_and_left hi)).trans (h i)
  exact bv_rw'' (bv_symm (bv_and_right hi)) h1 hφ

lemma B_ext_le (F : Fld (randomAlgebra ι)) (b : bSet (randomAlgebra ι)) :
    B_ext (fun s => F.le s b) :=
  B_ext_sup (h₁ := B_ext_pair_mem_left) (h₂ := B_ext_bv_eq_left)

end malg

/-! ### The reading of a name -/

variable {ι : Type}

section reading

variable (F : Fld (randomAlgebra ι))

/-- A measurable representative of the event `‖dyR d < r‖`. -/
noncomputable def cutSet (r : bSet (randomAlgebra ι)) (d : Dy) : Set (RandomAlgebra.Ω ι) :=
  (MeasureAlgebra.exists_rep (F.lt (F.dyR d.1 d.2) r)).choose

lemma measurableSet_cutSet (r : bSet (randomAlgebra ι)) (d : Dy) :
    MeasurableSet (cutSet F r d) :=
  (MeasureAlgebra.exists_rep (F.lt (F.dyR d.1 d.2) r)).choose_spec.choose

lemma mk_cutSet (r : bSet (randomAlgebra ι)) (d : Dy) :
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (cutSet F r d) (measurableSet_cutSet F r d) =
      F.lt (F.dyR d.1 d.2) r :=
  (MeasureAlgebra.exists_rep (F.lt (F.dyR d.1 d.2) r)).choose_spec.choose_spec

/-- **The reading of `r`**: the real with dyadic cut `{dyVal d | x ∈ ‖dyR d < r‖}`. -/
noncomputable def rd (r : bSet (randomAlgebra ι)) : RandomAlgebra.Ω ι → ℝ := dyReal (cutSet F r)

lemma measurable_rd (r : bSet (randomAlgebra ι)) : Measurable (rd F r) :=
  measurable_dyReal (measurableSet_cutSet F r)

/-- The name of the reading of `r`, an element of `Rdot`. -/
noncomputable def rdName (r : bSet (randomAlgebra ι)) : bSet (randomAlgebra ι) :=
  realName (rd F r) (measurable_rd F r)

lemma rdName_mem_Rdot {Γ : randomAlgebra ι} (r : bSet (randomAlgebra ι)) :
    Γ ≤ rdName F r ∈ᴮ Rdot := realName_mem_Rdot

/-- **The name of the isomorphism** `F.R → Rdot`, `r ↦ rdName F r`. -/
noncomputable def psi : bSet (randomAlgebra ι) :=
  ⟨F.R.type, fun i => pair (F.R.func i) (rdName F (F.R.func i)), F.R.bval⟩

lemma measurableSet_rdEvent (r : bSet (randomAlgebra ι)) (d : Dy) :
    MeasurableSet {x | dyVal d < rd F r x} :=
  measurableSet_lt measurable_const (measurable_rd F r)

variable {F}
variable {Γ : randomAlgebra ι} (hF : Γ ≤ F.COF)
include hF

/-! #### The cut of an element of `R` is a Dedekind cut -/

lemma lt_dyR_dyR_of_val {d d' : Dy} (h : dyVal d < dyVal d') :
    Γ ≤ F.lt (F.dyR d.1 d.2) (F.dyR d'.1 d'.2) :=
  Fld.dyR_lt_of_cross hF (dyVal_lt_iff.mp h)

lemma bot_of_lt_dyR_of_le {d d' : Dy} (h : dyVal d' ≤ dyVal d)
    (hlt : Γ ≤ F.lt (F.dyR d.1 d.2) (F.dyR d'.1 d'.2)) : Γ ≤ ⊥ :=
  BV.bot_of_compl hlt (Fld.not_dyR_lt_of_cross hF (dyVal_le_iff.mp h))

variable {r : bSet (randomAlgebra ι)} (hr : Γ ≤ r ∈ᴮ F.R)
include hr

lemma cut_mono {d d' : Dy} (h : dyVal d' < dyVal d) :
    Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ F.lt (F.dyR d'.1 d'.2) r :=
  Fld.lt_trans (Fld.cof_mono hF inf_le_left) (Fld.dyR_mem (Fld.cof_mono hF inf_le_left) _ _)
    (Fld.dyR_mem (Fld.cof_mono hF inf_le_left) _ _) (inf_le_left.trans hr)
    (lt_dyR_dyR_of_val (Fld.cof_mono hF inf_le_left) h) inf_le_right

lemma cut_dense (d : Dy) :
    Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ ⨆ d' : {d' : Dy // dyVal d < dyVal d'}, F.lt (F.dyR d'.1.1 d'.1.2) r := by
  have H' := Fld.cof_mono hF (inf_le_left : Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ Γ)
  have h1 := Fld.dense H' (Fld.dyR_mem H' _ _) (inf_le_left.trans hr) inf_le_right
  refine BV.iSup_elim h1 fun d' Γ' h' hd' => ?_
  by_cases hv : dyVal d < dyVal d'
  · exact le_iSup_of_le ⟨d', hv⟩ (bv_and_right hd')
  · exact BV.of_bot (bot_of_lt_dyR_of_le (Fld.cof_mono H' h') (not_lt.mp hv) (bv_and_left hd'))

lemma cut_nonempty : Γ ≤ ⨆ d : Dy, F.lt (F.dyR d.1 d.2) r := by
  refine BV.iSup_elim (Fld.arch_neg hF (Fld.cof_one_mem hF) (Fld.zero_lt_one hF) hr)
    fun n Γ' h' hn => ?_
  refine le_iSup_of_le (-(n : ℤ), 0) ?_
  have H' := Fld.cof_mono hF h'
  refine Fld.lt_congr ?_ bv_refl hn
  exact bv_symm (bv_trans (Fld.dyR_neg H' n 0)
    (Fld.neg_congr H' (Fld.dyR_mem H' n 0) (Fld.dyR_natCast H' n 0)))

lemma cut_bdd : Γ ≤ ⨆ d : Dy, (F.lt (F.dyR d.1 d.2) r)ᶜ := by
  refine BV.iSup_elim (Fld.arch hF (Fld.cof_one_mem hF) (Fld.zero_lt_one hF) hr)
    fun n Γ' h' hn => ?_
  refine le_iSup_of_le ((n : ℤ), 0) ?_
  have H' := Fld.cof_mono hF h'
  have h1 : Γ' ≤ F.lt r (F.dyR n 0) := Fld.lt_congr bv_refl (bv_symm (Fld.dyR_natCast H' n 0)) hn
  exact Fld.lt_asymm H' (h'.trans hr) (Fld.dyR_mem H' _ _) h1

/-- On `Γ`, the reading of `r` is taken on the good event. -/
lemma le_mk_cutGood :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (cutGood (cutSet F r))
      (measurableSet_cutGood (measurableSet_cutSet F r)) := by
  show Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋃ d, cutSet F r d)
      (MeasurableSet.iUnion (measurableSet_cutSet F r)) ⊓
    (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋃ d, (cutSet F r d)ᶜ)
      (MeasurableSet.iUnion fun d => (measurableSet_cutSet F r d).compl) ⊓
    (MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (⋂ d, ⋂ d', {x | dyVal d' < dyVal d → x ∈ cutSet F r d → x ∈ cutSet F r d'})
      (MeasurableSet.iInter fun d => MeasurableSet.iInter fun d' =>
        measurableSet_downClosed (measurableSet_cutSet F r) d d') ⊓
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (⋂ d, {x | x ∈ cutSet F r d → ∃ d', dyVal d < dyVal d' ∧ x ∈ cutSet F r d'})
      (MeasurableSet.iInter fun d => measurableSet_noMax (measurableSet_cutSet F r) d)))
  refine le_inf ?_ (le_inf ?_ (le_inf ?_ ?_))
  · refine le_mk_of_le (mk_iUnion_eq (cutSet F r) (measurableSet_cutSet F r)) ?_
    exact (cut_nonempty hF hr).trans (iSup_mono fun d => (mk_cutSet F r d).symm.le)
  · refine le_mk_of_le (mk_iUnion_eq (fun d => (cutSet F r d)ᶜ)
      (fun d => (measurableSet_cutSet F r d).compl)) ?_
    exact (cut_bdd hF hr).trans (iSup_mono fun d => compl_le_compl (mk_cutSet F r d).le)
  · refine le_mk_iInter' (fun d => MeasurableSet.iInter fun d' =>
      measurableSet_downClosed (measurableSet_cutSet F r) d d') fun d =>
      le_mk_iInter' (fun d' => measurableSet_downClosed (measurableSet_cutSet F r) d d') fun d' => ?_
    by_cases hv : dyVal d' < dyVal d
    · have e : {x | dyVal d' < dyVal d → x ∈ cutSet F r d → x ∈ cutSet F r d'} =
          (cutSet F r d)ᶜ ∪ cutSet F r d' := by
        ext x; simp only [mem_setOf_eq, mem_union, Set.mem_compl_iff, hv, true_implies]; tauto
      refine le_mk_of_le (MeasureAlgebra.mk_congr e
        (ht := (measurableSet_cutSet F r d).compl.union (measurableSet_cutSet F r d'))) ?_
      refine le_mk_compl_union (measurableSet_cutSet F r d) (measurableSet_cutSet F r d') ?_
      rw [mk_cutSet, mk_cutSet]
      exact cut_mono hF hr hv
    · have e : {x | dyVal d' < dyVal d → x ∈ cutSet F r d → x ∈ cutSet F r d'} = univ := by
        ext x; simp only [mem_setOf_eq, mem_univ, iff_true]; intro h; exact absurd h hv
      exact le_mk_of_le (MeasureAlgebra.mk_congr e (ht := MeasurableSet.univ)) le_top
  · refine le_mk_iInter' (fun d => measurableSet_noMax (measurableSet_cutSet F r) d) fun d => ?_
    have e : {x | x ∈ cutSet F r d → ∃ d', dyVal d < dyVal d' ∧ x ∈ cutSet F r d'} =
        (cutSet F r d)ᶜ ∪ ⋃ d' : {d' : Dy // dyVal d < dyVal d'}, cutSet F r d'.1 := by
      ext x
      constructor
      · intro hx
        by_cases hd : x ∈ cutSet F r d
        · obtain ⟨d', h1, h2⟩ := hx hd
          exact Or.inr (mem_iUnion.mpr ⟨⟨d', h1⟩, h2⟩)
        · exact Or.inl hd
      · rintro (hx | hx) hd
        · exact absurd hd hx
        · obtain ⟨⟨d', h1⟩, h2⟩ := mem_iUnion.mp hx
          exact ⟨d', h1, h2⟩
    have hB : MeasurableSet ((cutSet F r d)ᶜ ∪ ⋃ d' : {d' : Dy // dyVal d < dyVal d'}, cutSet F r d'.1) :=
      (measurableSet_cutSet F r d).compl.union
        (MeasurableSet.iUnion fun d' => measurableSet_cutSet F r d'.1)
    have hU : MeasurableSet (⋃ d' : {d' : Dy // dyVal d < dyVal d'}, cutSet F r d'.1) :=
      MeasurableSet.iUnion fun d' : {d' : Dy // dyVal d < dyVal d'} => measurableSet_cutSet F r d'.1
    refine le_mk_of_le (MeasureAlgebra.mk_congr e (ht := hB)) ?_
    refine le_mk_compl_union (measurableSet_cutSet F r d) hU ?_
    rw [mk_cutSet]
    refine (cut_dense hF hr d).trans ?_
    have e2 := mk_iUnion_eq (fun d' : {d' : Dy // dyVal d < dyVal d'} => cutSet F r d'.1)
      (fun d' => measurableSet_cutSet F r d'.1)
    refine le_mk_of_le e2 ?_
    exact iSup_mono fun d' => (mk_cutSet F r d'.1).symm.le

/-- **Reading lemma, ⇒**: `Γ ⊓ ‖dyR d < r‖ ≤ [dyVal d < rd r]`. -/
lemma lt_dyR_le_mk_rd (d : Dy) :
    Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | dyVal d < rd F r x} (measurableSet_rdEvent F r d) := by
  have h1 : Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (cutGood (cutSet F r) ∩ cutSet F r d)
      ((measurableSet_cutGood (measurableSet_cutSet F r)).inter (measurableSet_cutSet F r d)) :=
    le_inf (inf_le_left.trans (le_mk_cutGood hF hr))
      (show Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (cutSet F r d)
        (measurableSet_cutSet F r d) by rw [mk_cutSet]; exact inf_le_right)
  refine h1.trans (mk_mono fun x hx => ?_)
  exact (mem_iff_lt_dyReal hx.1 d).mp hx.2

/-- **Reading lemma, ⇐**: `Γ ⊓ [dyVal d < rd r] ≤ ‖dyR d < r‖`. -/
lemma mk_rd_le_lt_dyR (d : Dy) :
    Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | dyVal d < rd F r x} (measurableSet_rdEvent F r d) ≤
      F.lt (F.dyR d.1 d.2) r := by
  rw [← mk_cutSet]
  have h1 : Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | dyVal d < rd F r x}
      (measurableSet_rdEvent F r d) ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (cutGood (cutSet F r) ∩ {x | dyVal d < rd F r x})
      ((measurableSet_cutGood (measurableSet_cutSet F r)).inter (measurableSet_rdEvent F r d)) :=
    le_inf (inf_le_left.trans (le_mk_cutGood hF hr)) inf_le_right
  refine h1.trans (mk_mono fun x hx => ?_)
  exact (mem_iff_lt_dyReal hx.1 d).mpr hx.2

/-- The complement form: `Γ ⊓ ‖dyR d < r‖ᶜ ≤ [rd r ≤ dyVal d]`. -/
lemma not_lt_dyR_le_mk_rd_le (d : Dy) :
    Γ ⊓ (F.lt (F.dyR d.1 d.2) r)ᶜ ≤
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | rd F r x ≤ dyVal d}
        (measurableSet_le (measurable_rd F r) measurable_const) := by
  have h1 := mk_rd_le_lt_dyR hF hr d
  have h2 : Γ ≤ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | dyVal d < rd F r x}
      (measurableSet_rdEvent F r d))ᶜ ⊔ F.lt (F.dyR d.1 d.2) r := by
    show Γ ≤ imp _ _; exact deduction.mp h1
  have h3 : Γ ⊓ (F.lt (F.dyR d.1 d.2) r)ᶜ ≤ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {x | dyVal d < rd F r x} (measurableSet_rdEvent F r d))ᶜ := by
    refine (le_inf (inf_le_left.trans h2) inf_le_right).trans ?_
    rw [inf_sup_right, inf_compl_eq_bot, sup_bot_eq]
    exact inf_le_left
  refine h3.trans ?_
  rw [MeasureAlgebra.mk_compl]
  refine mk_mono fun x hx => ?_
  simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hx ⊢
  exact hx

end reading

/-! ### Congruence and the function `psi` -/

section psi

variable {F : Fld (randomAlgebra ι)} {Γ : randomAlgebra ι} (hF : Γ ≤ F.COF)
include hF

/-- Names with the same dyadic cuts have a.e. the same reading. -/
lemma rd_eq_of_cuts {r r' : bSet (randomAlgebra ι)} (hr : Γ ≤ r ∈ᴮ F.R) (hr' : Γ ≤ r' ∈ᴮ F.R)
    (h : ∀ d : Dy, Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ F.lt (F.dyR d.1 d.2) r' ∧
      Γ ⊓ F.lt (F.dyR d.1 d.2) r' ≤ F.lt (F.dyR d.1 d.2) r) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | rd F r x = rd F r' x}
      (measurableSet_eq_fun (measurable_rd F r) (measurable_rd F r')) := by
  have hg := le_mk_cutGood hF hr
  have hg' := le_mk_cutGood hF hr'
  have hc : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (⋂ d : Dy, ((cutSet F r d)ᶜ ∪ cutSet F r' d) ∩ ((cutSet F r' d)ᶜ ∪ cutSet F r d))
      (MeasurableSet.iInter fun d => ((measurableSet_cutSet F r d).compl.union
        (measurableSet_cutSet F r' d)).inter ((measurableSet_cutSet F r' d).compl.union
          (measurableSet_cutSet F r d))) := by
    refine le_mk_iInter' (fun d => ((measurableSet_cutSet F r d).compl.union
        (measurableSet_cutSet F r' d)).inter ((measurableSet_cutSet F r' d).compl.union
          (measurableSet_cutSet F r d))) fun d => ?_
    show Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) ((cutSet F r d)ᶜ ∪ cutSet F r' d)
        ((measurableSet_cutSet F r d).compl.union (measurableSet_cutSet F r' d)) ⊓
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) ((cutSet F r' d)ᶜ ∪ cutSet F r d)
        ((measurableSet_cutSet F r' d).compl.union (measurableSet_cutSet F r d))
    refine le_inf (le_mk_compl_union (measurableSet_cutSet F r d) (measurableSet_cutSet F r' d) ?_)
      (le_mk_compl_union (measurableSet_cutSet F r' d) (measurableSet_cutSet F r d) ?_)
    · rw [mk_cutSet, mk_cutSet]; exact (h d).1
    · rw [mk_cutSet, mk_cutSet]; exact (h d).2
  have := le_inf hg (le_inf hg' hc)
  simp only [MeasureAlgebra.mk_inf] at this
  refine mk_le_of_forall this fun x hx => ?_
  obtain ⟨hx1, hx2, hx3⟩ := hx
  simp only [mem_iInter, mem_inter_iff, mem_union, Set.mem_compl_iff] at hx3
  refine dyReal_eq_of_forall hx1 hx2 fun d => ?_
  have := hx3 d
  tauto

/-- `r = r'` (on `Γ`) implies `rd r = rd r'` a.e. -/
lemma rd_congr {r r' : bSet (randomAlgebra ι)} (hr : Γ ≤ r ∈ᴮ F.R) (h : Γ ≤ r =ᴮ r') :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | rd F r x = rd F r' x}
      (measurableSet_eq_fun (measurable_rd F r) (measurable_rd F r')) := by
  refine rd_eq_of_cuts hF hr (Fld.mem_congr' h hr) fun d => ⟨?_, ?_⟩
  · exact Fld.lt_congr bv_refl (inf_le_left.trans h) inf_le_right
  · exact Fld.lt_congr bv_refl (inf_le_left.trans (bv_symm h)) inf_le_right

lemma rdName_congr {r r' : bSet (randomAlgebra ι)} (hr : Γ ≤ r ∈ᴮ F.R) (h : Γ ≤ r =ᴮ r') :
    Γ ≤ rdName F r =ᴮ rdName F r' := by
  rw [rdName, rdName, bv_eq_realName]
  exact rd_congr hF hr h

omit hF in
lemma mem_psi (z : bSet (randomAlgebra ι)) :
    (z ∈ᴮ psi F) = ⨆ i, F.R.bval i ⊓ z =ᴮ pair (F.R.func i) (rdName F (F.R.func i)) := by
  rw [mem_unfold]; rfl

omit hF in
lemma app_psi_intro (i : F.R.type) :
    F.R.bval i ≤ Sem.app (psi F) (F.R.func i) (rdName F (F.R.func i)) := by
  rw [Sem.app, mem_psi]
  exact le_iSup_of_le i (by simp only [bv_eq_refl, inf_top_eq, le_refl])

omit hF in
lemma app_psi_elim {x y : bSet (randomAlgebra ι)} {b : randomAlgebra ι}
    (h : Γ ≤ Sem.app (psi F) x y)
    (H : ∀ (i : F.R.type) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ F.R.bval i →
      Γ' ≤ x =ᴮ F.R.func i → Γ' ≤ y =ᴮ rdName F (F.R.func i) → Γ' ≤ b) : Γ ≤ b := by
  rw [Sem.app, mem_psi] at h
  refine BV.iSup_elim h fun i Γ' h' hi => ?_
  have h1 := pair_eq_pair_iff.mp (bv_and_right hi)
  exact H i Γ' h' (bv_and_left hi) h1.1 h1.2

omit hF in
lemma mem_R_elim {x : bSet (randomAlgebra ι)} {b : randomAlgebra ι} (hx : Γ ≤ x ∈ᴮ F.R)
    (H : ∀ (i : F.R.type) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ F.R.bval i →
      Γ' ≤ x =ᴮ F.R.func i → Γ' ≤ b) : Γ ≤ b := by
  rw [mem_unfold] at hx
  exact BV.iSup_elim hx fun i Γ' h' hi => H i Γ' h' (bv_and_left hi) (bv_and_right hi)

/-- **`psi` applied**: on `Γ ⊓ (x ∈ R)`, `psi(x) = y` iff `y = rdName x`. -/
theorem app_psi_of {x y : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R)
    (h : Γ ≤ y =ᴮ rdName F x) : Γ ≤ Sem.app (psi F) x y := by
  refine mem_R_elim hx fun i Γ' h' hi hxi => ?_
  have h1 : Γ' ≤ rdName F x =ᴮ rdName F (F.R.func i) :=
    rdName_congr (Fld.cof_mono hF h') (h'.trans hx) hxi
  have h2 : Γ' ≤ pair x y =ᴮ pair (F.R.func i) (rdName F (F.R.func i)) :=
    pair_congr hxi (bv_trans (h'.trans h) h1)
  exact mem_congr (bv_symm h2) bv_refl (hi.trans (app_psi_intro i))

theorem eq_of_app_psi {x y : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R)
    (h : Γ ≤ Sem.app (psi F) x y) : Γ ≤ y =ᴮ rdName F x := by
  refine app_psi_elim h fun i Γ' h' _ hxi hy => ?_
  exact bv_trans hy (bv_symm (rdName_congr (Fld.cof_mono hF h') (h'.trans hx) hxi))

/-- **`psi` is a function `F.R → Rdot`.** -/
theorem psi_isFun : Γ ≤ Sem.isFun F.R Rdot (psi F) := by
  rw [Sem.isFun]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ' h' hx
  refine le_iSup_of_le (rdName F x) (le_inf (rdName_mem_Rdot F x)
    (le_inf (app_psi_of (Fld.cof_mono hF h') hx bv_refl) (le_iInf fun y' => ?_)))
  rw [bv_imp_iff]; intro Γ'' h'' hy'
  exact eq_of_app_psi (Fld.cof_mono hF (h''.trans h')) (h''.trans hx) hy'

end psi

/-! ### Order -/

section order

variable {F : Fld (randomAlgebra ι)} {Γ : randomAlgebra ι} (hF : Γ ≤ F.COF)
include hF

/-- **`psi` preserves `<`**: `x < y` in `F` implies `rd x < rd y` a.e. -/
theorem rd_lt_of_lt {x y : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ⊓ F.lt x y ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F x w < rd F y w}
      (measurableSet_lt (measurable_rd F x) (measurable_rd F y)) := by
  have hΓ : Γ ⊓ F.lt x y ≤ Γ := inf_le_left
  have H₁ := Fld.cof_mono hF hΓ
  refine BV.iSup_elim (Fld.dense H₁ (hΓ.trans hx) (hΓ.trans hy) inf_le_right) fun d Γ₂ h₂ hd => ?_
  have H₂ := Fld.cof_mono H₁ h₂
  refine BV.iSup_elim (Fld.dense H₂ (Fld.dyR_mem H₂ _ _) ((h₂.trans hΓ).trans hy) (bv_and_right hd))
    fun d' Γ₃ h₃ hd' => ?_
  have H₃ := Fld.cof_mono H₂ h₃
  have hΓ₃ : Γ₃ ≤ Γ := (h₃.trans h₂).trans hΓ
  have h1 : Γ₃ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F x w ≤ dyVal d}
      (measurableSet_le (measurable_rd F x) measurable_const) := by
    have := Fld.lt_asymm H₃ (hΓ₃.trans hx) (Fld.dyR_mem H₃ _ _) (h₃.trans (bv_and_left hd))
    exact (le_inf hΓ₃ this).trans (not_lt_dyR_le_mk_rd_le hF hx d)
  by_cases hv : dyVal d < dyVal d'
  · have h3 : Γ₃ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d' < rd F y w}
        (measurableSet_rdEvent F y d') :=
      (le_inf hΓ₃ (bv_and_right hd')).trans (lt_dyR_le_mk_rd hF hy d')
    have := le_inf h1 h3
    rw [MeasureAlgebra.mk_inf] at this
    refine mk_le_of_forall this fun w hw => ?_
    simp only [mem_inter_iff, mem_setOf_eq] at hw ⊢
    linarith [hw.1, hw.2]
  · exact BV.of_bot (bot_of_lt_dyR_of_le H₃ (not_lt.mp hv) (bv_and_left hd'))

/-- **`psi` reflects `<`**: `rd x < rd y` a.e. implies `x < y`. -/
theorem lt_of_rd_lt {x y : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F x w < rd F y w}
      (measurableSet_lt (measurable_rd F x) (measurable_rd F y)) ≤ F.lt x y := by
  have hΓ : Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F x w < rd F y w}
      (measurableSet_lt (measurable_rd F x) (measurable_rd F y)) ≤ Γ := inf_le_left
  have H₁ := Fld.cof_mono hF hΓ
  refine BV.or_elim (Fld.lt_total H₁ (hΓ.trans hx) (hΓ.trans hy)) (fun Γ' _ h => h) fun Γ' h' h => ?_
  refine BV.or_elim h (fun Γ'' h'' heq => ?_) fun Γ'' h'' hlt => ?_
  · have hΓ'' : Γ'' ≤ Γ := (h''.trans h').trans hΓ
    have h1 := rd_congr (Fld.cof_mono hF hΓ'') (hΓ''.trans hx) heq
    have h2 := le_inf h1 ((h''.trans h').trans inf_le_right)
    rw [MeasureAlgebra.mk_inf] at h2
    refine BV.of_bot (le_bot_of_mk_le h2 fun w hw => ?_)
    simp only [mem_inter_iff, mem_setOf_eq] at hw
    exact absurd hw.2 (by rw [hw.1]; exact lt_irrefl _)
  · have hΓ'' : Γ'' ≤ Γ := (h''.trans h').trans hΓ
    have h1 := (le_inf hΓ'' hlt).trans (rd_lt_of_lt hF hy hx)
    have h2 := le_inf h1 ((h''.trans h').trans inf_le_right)
    rw [MeasureAlgebra.mk_inf] at h2
    refine BV.of_bot (le_bot_of_mk_le h2 fun w hw => ?_)
    simp only [mem_inter_iff, mem_setOf_eq] at hw
    exact absurd hw.2 (not_lt.mpr hw.1.le)

/-- **`psi` is injective**: `rd x = rd y` a.e. implies `x = y`. -/
theorem eq_of_rd_eq {x y : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F x w = rd F y w}
      (measurableSet_eq_fun (measurable_rd F x) (measurable_rd F y)) ≤ x =ᴮ y := by
  have hΓ : Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F x w = rd F y w}
      (measurableSet_eq_fun (measurable_rd F x) (measurable_rd F y)) ≤ Γ := inf_le_left
  have H₁ := Fld.cof_mono hF hΓ
  refine BV.or_elim (Fld.lt_total H₁ (hΓ.trans hx) (hΓ.trans hy)) (fun Γ' h' hlt => ?_) fun Γ' h' h => ?_
  · have hΓ' : Γ' ≤ Γ := h'.trans hΓ
    have h1 := (le_inf hΓ' hlt).trans (rd_lt_of_lt hF hx hy)
    have h2 := le_inf h1 (h'.trans inf_le_right)
    rw [MeasureAlgebra.mk_inf] at h2
    refine BV.of_bot (le_bot_of_mk_le h2 fun w hw => ?_)
    simp only [mem_inter_iff, mem_setOf_eq] at hw
    exact absurd hw.1 (by rw [hw.2]; exact lt_irrefl _)
  · refine BV.or_elim h (fun Γ'' _ heq => heq) fun Γ'' h'' hlt => ?_
    have hΓ'' : Γ'' ≤ Γ := (h''.trans h').trans hΓ
    have h1 := (le_inf hΓ'' hlt).trans (rd_lt_of_lt hF hy hx)
    have h2 := le_inf h1 ((h''.trans h').trans inf_le_right)
    rw [MeasureAlgebra.mk_inf] at h2
    refine BV.of_bot (le_bot_of_mk_le h2 fun w hw => ?_)
    simp only [mem_inter_iff, mem_setOf_eq] at hw
    exact absurd hw.1 (by rw [hw.2]; exact lt_irrefl _)

end order

/-! ### Additivity -/

section add

variable {F : Fld (randomAlgebra ι)} {Γ : randomAlgebra ι} (hF : Γ ≤ F.COF)
include hF

lemma dyR_dyAdd (d d' : Dy) :
    F.add (F.dyR d.1 d.2) (F.dyR d'.1 d'.2) ≡[Γ] F.dyR (dyAdd d d').1 (dyAdd d d').2 := by
  have e1 := Fld.dyR_double_iter hF d.1 d.2 d'.2
  have e2 := Fld.dyR_double_iter hF d'.1 d'.2 d.2
  rw [Nat.add_comm d'.2 d.2] at e2
  refine bv_trans (Fld.add_congr hF (Fld.dyR_mem hF _ _) (Fld.dyR_mem hF _ _) e1 e2) ?_
  exact Fld.dyR_add hF _ _ _

lemma dyR_dySub (d d' : Dy) :
    F.add (F.dyR d.1 d.2) (F.neg (F.dyR d'.1 d'.2)) ≡[Γ] F.dyR (dySub d d').1 (dySub d d').2 := by
  have e1 := Fld.dyR_double_iter hF d.1 d.2 d'.2
  have e2 := Fld.dyR_double_iter hF (-d'.1) d'.2 d.2
  rw [Nat.add_comm d'.2 d.2] at e2
  have e3 : F.neg (F.dyR d'.1 d'.2) ≡[Γ] F.dyR (-d'.1) d'.2 := bv_symm (Fld.dyR_neg hF _ _)
  refine bv_trans (Fld.add_congr hF (Fld.dyR_mem hF _ _) (Fld.neg_mem hF (Fld.dyR_mem hF _ _)) e1
    (bv_trans e3 e2)) ?_
  refine bv_trans (Fld.dyR_add hF _ _ _) ?_
  show F.dyR (d.1 * 2 ^ d'.2 + -d'.1 * 2 ^ d.2) (d.2 + d'.2) ≡[Γ] F.dyR (d.1 * 2 ^ d'.2 - d'.1 * 2 ^ d.2) (d.2 + d'.2)
  rw [neg_mul, ← sub_eq_add_neg]
  exact bv_refl

/-- (A): `dyR d₁ < x`, `dyR d₂ < y` and `x + y = z` give `dyR (d₁ + d₂) < z`. -/
lemma lt_dyR_dyAdd_of {x y z : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hxyz : Γ ≤ Sem.app2 F.plus x y z) (d₁ d₂ : Dy) :
    Γ ⊓ F.lt (F.dyR d₁.1 d₁.2) x ⊓ F.lt (F.dyR d₂.1 d₂.2) y ≤
      F.lt (F.dyR (dyAdd d₁ d₂).1 (dyAdd d₁ d₂).2) z := by
  have hΓ : Γ ⊓ F.lt (F.dyR d₁.1 d₁.2) x ⊓ F.lt (F.dyR d₂.1 d₂.2) y ≤ Γ := inf_le_left.trans inf_le_left
  have H' := Fld.cof_mono hF hΓ
  have h1 := Fld.add_lt_add H' (Fld.dyR_mem H' _ _) (hΓ.trans hx) (Fld.dyR_mem H' _ _) (hΓ.trans hy)
    (inf_le_left.trans inf_le_right) inf_le_right
  have e1 : F.add x y ≡[Γ ⊓ F.lt (F.dyR d₁.1 d₁.2) x ⊓ F.lt (F.dyR d₂.1 d₂.2) y] z :=
    bv_symm (Fld.add_unique H' (hΓ.trans hx) (hΓ.trans hy) (hΓ.trans hxyz))
  exact Fld.lt_congr (dyR_dyAdd H' d₁ d₂) e1 h1

/-- (B): `dyR d < z = x + y` gives `d₁` with `dyR d₁ < x` and `dyR (d - d₁) < y`. -/
lemma exists_split {x y z : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (hxyz : Γ ≤ Sem.app2 F.plus x y z) (d : Dy) :
    Γ ⊓ F.lt (F.dyR d.1 d.2) z ≤
      ⨆ d₁ : Dy, F.lt (F.dyR d₁.1 d₁.2) x ⊓ F.lt (F.dyR (dySub d d₁).1 (dySub d d₁).2) y := by
  have hΓ : Γ ⊓ F.lt (F.dyR d.1 d.2) z ≤ Γ := inf_le_left
  have H' := Fld.cof_mono hF hΓ
  have hx' := hΓ.trans hx
  have hy' := hΓ.trans hy
  have hz' := hΓ.trans hz
  have hdR := Fld.dyR_mem H' d.1 d.2
  have hε := Fld.sub_pos_of_lt H' hdR hz' inf_le_right
  have hεR := Fld.add_mem H' hz' (Fld.neg_mem H' hdR)
  have hlt : Γ ⊓ F.lt (F.dyR d.1 d.2) z ≤ F.lt (F.add x (F.neg (F.add z (F.neg (F.dyR d.1 d.2))))) x := by
    have := Fld.add_lt_add_left H' (Fld.neg_mem H' hεR) (Fld.cof_zero_mem H') hx'
      (Fld.neg_neg_of_pos H' hεR hε)
    exact Fld.lt_congr bv_refl (Fld.add_zero H' hx') this
  refine BV.iSup_elim (Fld.dense H' (Fld.add_mem H' hx' (Fld.neg_mem H' hεR)) hx' hlt)
    fun d₁ Γ'' h'' hd₁ => ?_
  refine le_iSup_of_le d₁ (le_inf (bv_and_right hd₁) ?_)
  have H'' := Fld.cof_mono H' h''
  have hx'' := h''.trans hx'
  have hy'' := h''.trans hy'
  have hz'' := h''.trans hz'
  have hdR'' := Fld.dyR_mem H'' d.1 d.2
  have hd₁R := Fld.dyR_mem H'' d₁.1 d₁.2
  set ε := F.add z (F.neg (F.dyR d.1 d.2)) with hεdef
  have hεR'' : Γ'' ≤ ε ∈ᴮ F.R := h''.trans hεR
  have h1 : Γ'' ≤ F.lt (F.add x (F.neg ε)) (F.dyR d₁.1 d₁.2) := bv_and_left hd₁
  have h2 := Fld.neg_lt_neg H'' (Fld.add_mem H'' hx'' (Fld.neg_mem H'' hεR'')) hd₁R h1
  have h3 := Fld.add_lt_add_left H'' (Fld.neg_mem H'' hd₁R)
    (Fld.neg_mem H'' (Fld.add_mem H'' hx'' (Fld.neg_mem H'' hεR''))) hdR'' h2
  have hnx := Fld.neg_mem H'' hx''
  have hB : Γ'' ≤ F.add (F.neg x) z ∈ᴮ F.R := Fld.add_mem H'' hnx hz''
  have hy_eq : y ≡[Γ''] F.add (F.neg x) z := by
    have e0 : F.add x y ≡[Γ''] z := bv_symm (Fld.add_unique H'' hx'' hy'' (h''.trans (hΓ.trans hxyz)))
    calc y ≡[Γ''] F.add (F.add y x) (F.neg x) := bv_symm (Fld.add_neg_cancel_right H'' hy'' hx'')
      _ ≡[Γ''] F.add (F.add x y) (F.neg x) :=
          Fld.add_congr_left H'' (Fld.add_mem H'' hy'' hx'') hnx (Fld.add_comm H'' hy'' hx'')
      _ ≡[Γ''] F.add z (F.neg x) := Fld.add_congr_left H'' (Fld.add_mem H'' hx'' hy'') hnx e0
      _ ≡[Γ''] F.add (F.neg x) z := Fld.add_comm H'' hz'' hnx
  have e : F.add (F.dyR d.1 d.2) (F.neg (F.add x (F.neg ε))) ≡[Γ''] y := by
    calc F.add (F.dyR d.1 d.2) (F.neg (F.add x (F.neg ε)))
        ≡[Γ''] F.add (F.dyR d.1 d.2) (F.add (F.neg x) (F.neg (F.neg ε))) :=
          Fld.add_congr_right H'' hdR'' (Fld.neg_mem H'' (Fld.add_mem H'' hx'' (Fld.neg_mem H'' hεR'')))
            (Fld.neg_add_rev H'' hx'' (Fld.neg_mem H'' hεR''))
      _ ≡[Γ''] F.add (F.dyR d.1 d.2) (F.add (F.neg x) ε) :=
          Fld.add_congr_right H'' hdR'' (Fld.add_mem H'' hnx (Fld.neg_mem H'' (Fld.neg_mem H'' hεR'')))
            (Fld.add_congr_right H'' hnx (Fld.neg_mem H'' (Fld.neg_mem H'' hεR'')) (Fld.neg_neg H'' hεR''))
      _ ≡[Γ''] F.add (F.dyR d.1 d.2) (F.add (F.add (F.neg x) z) (F.neg (F.dyR d.1 d.2))) :=
          Fld.add_congr_right H'' hdR'' (Fld.add_mem H'' hnx hεR'')
            (bv_symm (Fld.add_assoc H'' hnx hz'' (Fld.neg_mem H'' hdR'')))
      _ ≡[Γ''] F.add (F.add (F.dyR d.1 d.2) (F.add (F.neg x) z)) (F.neg (F.dyR d.1 d.2)) :=
          bv_symm (Fld.add_assoc H'' hdR'' hB (Fld.neg_mem H'' hdR''))
      _ ≡[Γ''] F.add (F.add (F.add (F.neg x) z) (F.dyR d.1 d.2)) (F.neg (F.dyR d.1 d.2)) :=
          Fld.add_congr_left H'' (Fld.add_mem H'' hdR'' hB) (Fld.neg_mem H'' hdR'')
            (Fld.add_comm H'' hdR'' hB)
      _ ≡[Γ''] F.add (F.neg x) z := Fld.add_neg_cancel_right H'' hB hdR''
      _ ≡[Γ''] y := bv_symm hy_eq
  exact Fld.lt_congr (dyR_dySub H'' d d₁) e h3

/-- **`psi` is additive**: `x + y = z` in `F` implies `rd z = rd x + rd y` a.e. -/
theorem rd_add {x y z : bSet (randomAlgebra ι)} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (hxyz : Γ ≤ Sem.app2 F.plus x y z) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F z w = rd F x w + rd F y w}
      (measurableSet_eq_fun (measurable_rd F z) ((measurable_rd F x).add (measurable_rd F y))) := by
  have hgx := le_mk_cutGood hF hx
  have hgy := le_mk_cutGood hF hy
  have hgz := le_mk_cutGood hF hz
  -- (A')
  have hA : ∀ d₁ d₂ : Dy, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (({w | dyVal d₁ < rd F x w} ∩ {w | dyVal d₂ < rd F y w})ᶜ ∪
        {w | dyVal (dyAdd d₁ d₂) < rd F z w})
      (((measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y d₂)).compl.union
        (measurableSet_rdEvent F z _)) := fun d₁ d₂ => by
    refine le_mk_compl_union ((measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y d₂))
      (measurableSet_rdEvent F z _) ?_
    show Γ ⊓ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d₁ < rd F x w}
        (measurableSet_rdEvent F x d₁) ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {w | dyVal d₂ < rd F y w} (measurableSet_rdEvent F y d₂)) ≤ _
    have h1 : Γ ⊓ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d₁ < rd F x w}
        (measurableSet_rdEvent F x d₁) ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {w | dyVal d₂ < rd F y w} (measurableSet_rdEvent F y d₂)) ≤
        Γ ⊓ F.lt (F.dyR d₁.1 d₁.2) x ⊓ F.lt (F.dyR d₂.1 d₂.2) y :=
      le_inf (le_inf inf_le_left
        ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (mk_rd_le_lt_dyR hF hx d₁)))
        ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (mk_rd_le_lt_dyR hF hy d₂))
    have h2 := h1.trans (lt_dyR_dyAdd_of hF hx hy hxyz d₁ d₂)
    exact (le_inf inf_le_left h2).trans (lt_dyR_le_mk_rd hF hz _)
  -- (B')
  have hB : ∀ d : Dy, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      ({w | dyVal d < rd F z w}ᶜ ∪ ⋃ d₁ : Dy, {w | dyVal d₁ < rd F x w} ∩
        {w | dyVal (dySub d d₁) < rd F y w})
      ((measurableSet_rdEvent F z d).compl.union (MeasurableSet.iUnion fun d₁ =>
        (measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y _))) := fun d => by
    refine le_mk_compl_union (measurableSet_rdEvent F z d) (MeasurableSet.iUnion fun d₁ =>
      (measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y _)) ?_
    have h1 : Γ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d < rd F z w}
        (measurableSet_rdEvent F z d) ≤ Γ ⊓ F.lt (F.dyR d.1 d.2) z :=
      le_inf inf_le_left (mk_rd_le_lt_dyR hF hz d)
    have h2 := h1.trans (exists_split hF hx hy hz hxyz d)
    refine le_mk_of_le (mk_iUnion_eq (fun d₁ : Dy => {w | dyVal d₁ < rd F x w} ∩
      {w | dyVal (dySub d d₁) < rd F y w}) (fun d₁ =>
        (measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y _))) ?_
    refine (le_inf inf_le_left h2).trans ?_
    rw [inf_iSup_eq]
    refine iSup_mono fun d₁ => ?_
    show Γ ⊓ _ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d₁ < rd F x w}
      (measurableSet_rdEvent F x d₁) ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {w | dyVal (dySub d d₁) < rd F y w} (measurableSet_rdEvent F y _)
    exact le_inf ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (lt_dyR_le_mk_rd hF hx d₁))
      ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (lt_dyR_le_mk_rd hF hy _))
  have hA' := le_mk_iInter' (fun d₁ => MeasurableSet.iInter fun d₂ =>
      ((measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y d₂)).compl.union
        (measurableSet_rdEvent F z (dyAdd d₁ d₂)))
    fun d₁ => le_mk_iInter' (fun d₂ =>
      ((measurableSet_rdEvent F x d₁).inter (measurableSet_rdEvent F y d₂)).compl.union
        (measurableSet_rdEvent F z (dyAdd d₁ d₂))) fun d₂ => hA d₁ d₂
  have hB' := le_mk_iInter' (fun d => (measurableSet_rdEvent F z d).compl.union
    (MeasurableSet.iUnion fun d₁ => (measurableSet_rdEvent F x d₁).inter
      (measurableSet_rdEvent F y (dySub d d₁)))) hB
  have := le_inf hgx (le_inf hgy (le_inf hgz (le_inf hA' hB')))
  simp only [MeasureAlgebra.mk_inf] at this
  refine mk_le_of_forall this fun w hw => ?_
  obtain ⟨hwx, hwy, hwz, hwA, hwB⟩ := hw
  simp only [mem_iInter, mem_union, Set.mem_compl_iff, mem_inter_iff, mem_setOf_eq,
    mem_iUnion] at hwA hwB
  show rd F z w = rd F x w + rd F y w
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    obtain ⟨d, h1, h2⟩ := exists_dyVal_btwn hlt
    rcases hwB d with h3 | ⟨d₁, h3, h4⟩
    · exact h3 h2
    · rw [dyVal_dySub] at h4
      linarith
  · by_contra hlt
    push_neg at hlt
    obtain ⟨d₁, h1, h2⟩ := exists_dyVal_btwn
      (show rd F x w - (rd F x w + rd F y w - rd F z w) / 2 < rd F x w by linarith)
    obtain ⟨d₂, h3, h4⟩ := exists_dyVal_btwn
      (show rd F y w - (rd F x w + rd F y w - rd F z w) / 2 < rd F y w by linarith)
    rcases hwA d₁ d₂ with h5 | h5
    · exact h5 ⟨h2, h4⟩
    · rw [dyVal_dyAdd] at h5
      linarith

end add

/-! ### Zero and one -/

section zero_one

variable {F : Fld (randomAlgebra ι)} {Γ : randomAlgebra ι} (hF : Γ ≤ F.COF)
include hF

/-- The cut of a name `r` equal to `dyR d₀` (on `Γ`) is `{d | dyVal d < dyVal d₀}`. -/
lemma rd_eq_of_eq_dyR {r : bSet (randomAlgebra ι)} (hr : Γ ≤ r ∈ᴮ F.R) (d₀ : Dy)
    (h : r ≡[Γ] F.dyR d₀.1 d₀.2) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F r w = dyVal d₀}
      (measurableSet_eq_fun (measurable_rd F r) measurable_const) := by
  have hg := le_mk_cutGood hF hr
  have hd : ∀ d : Dy, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {w | dyVal d < dyVal d₀ ↔ w ∈ cutSet F r d}
      (measurableSet_iff_mem _ (measurableSet_cutSet F r d)) := fun d => by
    by_cases hv : dyVal d < dyVal d₀
    · have h1 : Γ ≤ F.lt (F.dyR d.1 d.2) r :=
        Fld.lt_congr bv_refl (bv_symm h) (lt_dyR_dyR_of_val hF hv)
      have e : {w | dyVal d < dyVal d₀ ↔ w ∈ cutSet F r d} = cutSet F r d := by
        ext w; simp only [mem_setOf_eq, hv, true_iff]
      refine le_mk_of_le (MeasureAlgebra.mk_congr e (ht := measurableSet_cutSet F r d)) ?_
      rw [mk_cutSet]; exact h1
    · have h1 : Γ ≤ (F.lt (F.dyR d.1 d.2) r)ᶜ := by
        refine BV.compl_of_inf_le_bot ?_
        have h2 : Γ ⊓ F.lt (F.dyR d.1 d.2) r ≤ F.lt (F.dyR d.1 d.2) (F.dyR d₀.1 d₀.2) :=
          Fld.lt_congr bv_refl (inf_le_left.trans h) inf_le_right
        exact bot_of_lt_dyR_of_le (Fld.cof_mono hF inf_le_left) (not_lt.mp hv) h2
      have e : {w | dyVal d < dyVal d₀ ↔ w ∈ cutSet F r d} = (cutSet F r d)ᶜ := by
        ext w; simp only [mem_setOf_eq, hv, false_iff, Set.mem_compl_iff]
      refine le_mk_of_le (MeasureAlgebra.mk_congr e (ht := (measurableSet_cutSet F r d).compl)) ?_
      show Γ ≤ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (cutSet F r d) (measurableSet_cutSet F r d))ᶜ
      rw [mk_cutSet]; exact h1
  have := le_inf hg (le_mk_iInter' (fun d => measurableSet_iff_mem _ (measurableSet_cutSet F r d)) hd)
  rw [MeasureAlgebra.mk_inf] at this
  refine mk_le_of_forall this fun w hw => ?_
  simp only [mem_inter_iff, mem_iInter, mem_setOf_eq] at hw ⊢
  exact (eq_dyReal_of_forall hw.1 hw.2).symm

/-- `rd zero = 0` a.e. -/
theorem rd_zero : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F F.zero w = 0}
    (measurableSet_eq_fun (measurable_rd F F.zero) measurable_const) := by
  have := rd_eq_of_eq_dyR hF (Fld.cof_zero_mem hF) (0, 0) (bv_symm (Fld.dyR_zero hF 0))
  simpa only [dyVal_zero_zero] using this

/-- `rd one = 1` a.e. -/
theorem rd_one : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F F.one w = 1}
    (measurableSet_eq_fun (measurable_rd F F.one) measurable_const) := by
  have := rd_eq_of_eq_dyR hF (Fld.cof_one_mem hF) (1, 0) (bv_symm (Fld.dyR_one_zero hF))
  simpa only [dyVal_one_zero] using this

end zero_one

/-! ### Surjectivity -/

section surj

variable (F : Fld (randomAlgebra ι))

/-- The name of the cut `{dyR d | dyVal d < g}` of a real name `g` inside `F`. -/
noncomputable def cutName (g : MeasReal ι) : bSet (randomAlgebra ι) :=
  ⟨Dy, fun d => F.dyR d.1 d.2, fun d => MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
    {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2)⟩

variable {F}
variable {Γ : randomAlgebra ι} (hF : Γ ≤ F.COF) (g : MeasReal ι)
include hF

omit hF in
lemma mem_cutName (z : bSet (randomAlgebra ι)) :
    (z ∈ᴮ cutName F g) = ⨆ d : Dy, MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2) ⊓ z =ᴮ F.dyR d.1 d.2 := by
  rw [mem_unfold]; rfl

omit hF in
lemma bval_le_mem_cutName (d : Dy) :
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d < g.1 w}
      (measurableSet_lt measurable_const g.2) ≤ F.dyR d.1 d.2 ∈ᴮ cutName F g :=
  mem_mk' (cutName F g) d

lemma cutName_subset_R : Γ ≤ cutName F g ⊆ᴮ F.R := by
  rw [subset_unfold]
  refine le_iInf fun d => ?_
  rw [← deduction]
  exact inf_le_left.trans (Fld.dyR_mem hF _ _)

lemma cutName_ne_empty : Γ ≤ (cutName F g =ᴮ bSet.empty)ᶜ := by
  refine BV.compl_of_inf_le_bot ?_
  have htop : (⨆ d : Dy, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d < g.1 w}
      (measurableSet_lt measurable_const g.2)) = ⊤ := by
    rw [← mk_iUnion_eq]
    refine mk_eq_top_of_forall _ fun w => ?_
    obtain ⟨d, hd⟩ := exists_dyVal_lt (g.1 w)
    exact mem_iUnion.mpr ⟨d, hd⟩
  have h1 : Γ ⊓ (cutName F g =ᴮ bSet.empty) ≤ ⨆ d : Dy, MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2) ⊓ (cutName F g =ᴮ bSet.empty) := by
    rw [← iSup_inf_eq, htop, top_inf_eq]; exact inf_le_right
  refine h1.trans (iSup_le fun d => ?_)
  exact bot_of_mem_empty (mem_congr bv_refl inf_le_right (inf_le_left.trans (bval_le_mem_cutName g d)))

lemma cutName_bdd :
    Γ ≤ ⨆ b : bSet (randomAlgebra ι), b ∈ᴮ F.R ⊓ ⨅ s : bSet (randomAlgebra ι),
      s ∈ᴮ cutName F g ⟹ F.le s b := by
  have htop : (⨆ d : Dy, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | g.1 w < dyVal d}
      (measurableSet_lt g.2 measurable_const)) = ⊤ := by
    rw [← mk_iUnion_eq]
    refine mk_eq_top_of_forall _ fun w => ?_
    obtain ⟨d, hd⟩ := exists_dyVal_gt (g.1 w)
    exact mem_iUnion.mpr ⟨d, hd⟩
  have h0 : Γ ≤ ⨆ d : Dy, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | g.1 w < dyVal d}
      (measurableSet_lt g.2 measurable_const) := by rw [htop]; exact le_top
  refine BV.iSup_elim h0 fun d₀ Γ' h' hd₀ => ?_
  have H' := Fld.cof_mono hF h'
  refine le_iSup_of_le (F.dyR d₀.1 d₀.2) (le_inf (Fld.dyR_mem H' _ _) (le_iInf fun s => ?_))
  rw [bv_imp_iff]; intro Γ'' h'' hs
  rw [mem_cutName] at hs
  refine BV.iSup_elim hs fun d Γ₃ h₃ hd => ?_
  have H₃ := Fld.cof_mono H' (h₃.trans h'')
  by_cases hv : dyVal d < dyVal d₀
  · exact Fld.le_congr (bv_symm (bv_and_right hd)) bv_refl (Fld.le_of_lt (lt_dyR_dyR_of_val H₃ hv))
  · have h1 := le_inf (bv_and_left hd) ((h₃.trans h'').trans hd₀)
    rw [MeasureAlgebra.mk_inf] at h1
    refine BV.of_bot (le_bot_of_mk_le h1 fun w hw => ?_)
    simp only [mem_inter_iff, mem_setOf_eq] at hw
    exact hv (hw.1.trans hw.2)

/-- **`psi` is surjective onto `Rdot`**: every real name `g` is the reading of some `u ∈ F.R`. -/
theorem psi_surj : Γ ≤ ⨆ u : bSet (randomAlgebra ι), u ∈ᴮ F.R ⊓
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | rd F u w = g.1 w}
      (measurableSet_eq_fun (measurable_rd F u) g.2) := by
  have hc := Fld.cof_complete hF
  rw [Sem.complete] at hc
  have hsup := BV.mp (BV.mp (BV.mp (hc.trans (iInf_le _ (cutName F g)))
    (bv_powerset_spec.mp (cutName_subset_R hF g))) (cutName_ne_empty hF g)) (cutName_bdd hF g)
  refine BV.iSup_elim hsup fun u Γ' h' hu => ?_
  have H' := Fld.cof_mono hF h'
  have huR := bv_and_left hu
  have hu1 := bv_and_left (bv_and_right hu)
  have hu2 := bv_and_right (bv_and_right hu)
  refine le_iSup_of_le u (le_inf huR ?_)
  -- `Γ' ⊓ [dyVal d < g] ≤ ‖dyR d < u‖`
  have h1 : ∀ d : Dy, Γ' ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d < g.1 w}
      (measurableSet_lt measurable_const g.2) ≤ F.lt (F.dyR d.1 d.2) u := fun d => by
    have hden : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d < g.1 w}
        (measurableSet_lt measurable_const g.2) ≤
        ⨆ d' : {d' : Dy // dyVal d < dyVal d'}, MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
          {w | dyVal d'.1 < g.1 w} (measurableSet_lt measurable_const g.2) := by
      rw [← mk_iUnion_eq]
      refine mk_mono fun w hw => ?_
      obtain ⟨d', h1, h2⟩ := exists_dyVal_btwn hw
      exact mem_iUnion.mpr ⟨⟨d', h1⟩, h2⟩
    refine (le_inf inf_le_left (inf_le_right.trans hden)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun d' => ?_
    have H'' : Γ' ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d'.1 < g.1 w}
        (measurableSet_lt measurable_const g.2) ≤ F.COF := inf_le_left.trans H'
    have hmem : Γ' ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d'.1 < g.1 w}
        (measurableSet_lt measurable_const g.2) ≤ F.dyR d'.1.1 d'.1.2 ∈ᴮ cutName F g :=
      inf_le_right.trans (bval_le_mem_cutName g d'.1)
    have hle := BV.mp ((inf_le_left.trans hu1).trans (iInf_le _ (F.dyR d'.1.1 d'.1.2))) hmem
    exact Fld.lt_of_lt_of_le H'' (Fld.dyR_mem H'' _ _) (Fld.dyR_mem H'' _ _) (inf_le_left.trans huR)
      (lt_dyR_dyR_of_val H'' d'.2) hle
  -- `Γ' ⊓ ‖dyR d < u‖ ≤ [dyVal d < g]`
  have h2 : ∀ d : Dy, Γ' ⊓ F.lt (F.dyR d.1 d.2) u ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2) := fun d => by
    refine BV.by_contra ?_
    have hΓ'' : Γ' ⊓ F.lt (F.dyR d.1 d.2) u ⊓ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2))ᶜ ≤ Γ' :=
      inf_le_left.trans inf_le_left
    have H'' := Fld.cof_mono H' hΓ''
    have hub : Γ' ⊓ F.lt (F.dyR d.1 d.2) u ⊓ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2))ᶜ ≤
        ⨅ s : bSet (randomAlgebra ι), s ∈ᴮ cutName F g ⟹ F.le s (F.dyR d.1 d.2) := by
      refine le_iInf_mem_imp (B_ext_le F _) fun d' => ?_
      by_cases hv : dyVal d' < dyVal d
      · exact inf_le_left.trans (Fld.le_of_lt (lt_dyR_dyR_of_val H'' hv))
      · have h3 : Γ' ⊓ F.lt (F.dyR d.1 d.2) u ⊓ (MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
            {w | dyVal d < g.1 w} (measurableSet_lt measurable_const g.2))ᶜ ⊓ (cutName F g).bval d' ≤
            (MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {w | dyVal d < g.1 w}
              (measurableSet_lt measurable_const g.2))ᶜ ⊓ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
              {w | dyVal d' < g.1 w} (measurableSet_lt measurable_const g.2) :=
          le_inf (inf_le_left.trans inf_le_right) inf_le_right
        rw [MeasureAlgebra.mk_compl, MeasureAlgebra.mk_inf] at h3
        refine BV.of_bot (le_bot_of_mk_le h3 fun w hw => ?_)
        simp only [mem_inter_iff, Set.mem_compl_iff, mem_setOf_eq, not_lt] at hw
        exact hv (hw.2.trans_le hw.1)
    have hle := BV.mp (BV.mp ((hΓ''.trans hu2).trans (iInf_le _ (F.dyR d.1 d.2)))
      (Fld.dyR_mem H'' _ _)) hub
    exact BV.bot_of_compl (inf_le_left.trans inf_le_right : _ ≤ F.lt (F.dyR d.1 d.2) u)
      (Fld.not_lt_of_le H'' (hΓ''.trans huR) (Fld.dyR_mem H'' _ _) hle)
  -- combine
  have hg := le_mk_cutGood H' huR
  have hd : ∀ d : Dy, Γ' ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {w | dyVal d < g.1 w ↔ w ∈ cutSet F u d}
      (MeasurableSet.iff (measurableSet_lt measurable_const g.2) (measurableSet_cutSet F u d)) := fun d => by
    have e : {w | dyVal d < g.1 w ↔ w ∈ cutSet F u d} =
        ({w | dyVal d < g.1 w}ᶜ ∪ cutSet F u d) ∩ ((cutSet F u d)ᶜ ∪ {w | dyVal d < g.1 w}) := by
      ext w
      simp only [mem_setOf_eq, mem_inter_iff, mem_union, Set.mem_compl_iff]
      tauto
    refine le_mk_of_le (MeasureAlgebra.mk_congr e
      (ht := ((measurableSet_lt measurable_const g.2).compl.union (measurableSet_cutSet F u d)).inter
        ((measurableSet_cutSet F u d).compl.union (measurableSet_lt measurable_const g.2)))) ?_
    show Γ' ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) ({w | dyVal d < g.1 w}ᶜ ∪ cutSet F u d)
        ((measurableSet_lt measurable_const g.2).compl.union (measurableSet_cutSet F u d)) ⊓
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) ((cutSet F u d)ᶜ ∪ {w | dyVal d < g.1 w})
        ((measurableSet_cutSet F u d).compl.union (measurableSet_lt measurable_const g.2))
    refine le_inf (le_mk_compl_union (measurableSet_lt measurable_const g.2)
      (measurableSet_cutSet F u d) ?_) (le_mk_compl_union (measurableSet_cutSet F u d)
      (measurableSet_lt measurable_const g.2) ?_)
    · rw [mk_cutSet]; exact h1 d
    · rw [mk_cutSet]; exact h2 d
  have := le_inf hg (le_mk_iInter' (fun d => MeasurableSet.iff (measurableSet_lt measurable_const g.2)
    (measurableSet_cutSet F u d)) hd)
  rw [MeasureAlgebra.mk_inf] at this
  refine mk_le_of_forall this fun w hw => ?_
  simp only [mem_inter_iff, mem_iInter, mem_setOf_eq] at hw ⊢
  exact (eq_dyReal_of_forall hw.1 hw.2).symm

/-- Surjectivity in the form of `Sem.app`. -/
theorem psi_surj_app : Γ ≤ ⨆ u : bSet (randomAlgebra ι), u ∈ᴮ F.R ⊓
    Sem.app (psi F) u (realName g.1 g.2) := by
  refine BV.iSup_elim (psi_surj hF g) fun u Γ' h' hu => ?_
  refine le_iSup_of_le u (le_inf (bv_and_left hu) ?_)
  refine app_psi_of (Fld.cof_mono hF h') (bv_and_left hu) ?_
  rw [rdName, bv_eq_realName]
  refine mk_le_of_forall (bv_and_right hu) fun w hw => ?_
  simp only [mem_setOf_eq] at hw ⊢
  exact hw.symm

end surj

end Flypitch.Erdos501.RandomForcing
