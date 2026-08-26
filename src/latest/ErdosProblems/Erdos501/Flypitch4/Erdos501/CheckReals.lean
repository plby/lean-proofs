/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The check-name reals: the ground-model reals as an internal complete ordered field of `V 𝔹`
for Boolean algebras `𝔹` with a dense ω-closed subset (in particular the collapse algebra).
-/
import Mathlib.Data.Rat.Denumerable
import ErdosProblems.Erdos501.Flypitch4.Erdos501.OmegaClosed
import ErdosProblems.Erdos501.Flypitch4.Erdos501.RealsInZFSet

set_option relaxedAutoImplicit true

/-!
# The check-name reals

For an arbitrary nontrivial complete Boolean algebra `𝔹`, the names `rname r = check (codeP r)`
(`r : ℝ`, `codeP r` the `PSet` of codes of the rationals below `r`) are pairwise definitely distinct
(`rname_bv_eq_of_ne : rname r =ᴮ rname s = ⊥` for `r ≠ s`), and the names

* `Rc = {rname r | r ∈ ℝ}`, `plusC`, `timesC` (sets of triples), `ltC` (a set of pairs),
  `zeroC = rname 0`, `oneC = rname 1`

satisfy the nineteen first-order axioms of an ordered field in `V 𝔹` (they are decided by the
corresponding facts about `ℝ`).  Dedekind completeness of `Rc` holds in `V 𝔹` when `𝔹` has a dense
ω-closed subset `D` (`complete_Rc`): the (ω,∞)-distributivity of such algebras — "no new reals" —
is used in the external form of `OmegaClosed.lean`: on a nonzero piece the cut of an internal
subset `S ⊆ Rc` can be decided completely, so that its supremum is a ground real.  Hence
`completeOrderedField_Rc : ⊤ ≤ Sem.completeOrderedField Rc plusC timesC ltC zeroC oneC` for such
`𝔹`, in particular for `𝔹_collapse`.  This is the internal complete ordered field used for Hechler's
counterexample in `Hechler.lean`.
-/

open Fol bSet Flypitch Lattice
open scoped Flypitch

namespace Flypitch.Erdos501

namespace CheckReals

variable {𝔹 : Type} [NontrivialCompleteBooleanAlgebra 𝔹]

/-! ### Codes of reals -/

/-- The `PSet` of the codes of the rationals below `r`. -/
def codeP (r : ℝ) : PSet.{0} :=
  ⟨{q : ℚ // (q : ℝ) < r}, fun q => PSet.ofNat (Encodable.encode q.1)⟩

theorem mk_codeP (r : ℝ) : ZFSet.mk (codeP r) = RealsInZFSet.cutZ r := by
  apply ZFSet.ext
  intro z
  refine Quotient.inductionOn z fun y => ?_
  change ZFSet.mk y ∈ ZFSet.mk (codeP r) ↔ ZFSet.mk y ∈ RealsInZFSet.cutZ r
  rw [ZFSet.mk_mem_iff, RealsInZFSet.cutZ, ZFSet.mem_range, PSet.mem_def]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, (ZFSet.sound hq).symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, ZFSet.exact hq.symm⟩

theorem codeP_equiv_iff {r s : ℝ} : PSet.Equiv (codeP r) (codeP s) ↔ r = s := by
  rw [← ZFSet.eq, mk_codeP, mk_codeP, RealsInZFSet.cutZ_inj]

/-! ### The names -/

/-- The name of the real `r`. -/
def rname (r : ℝ) : bSet 𝔹 := check (codeP r)

theorem rname_bv_eq_of_ne {r s : ℝ} (h : r ≠ s) : (rname r : bSet 𝔹) =ᴮ rname s = ⊥ :=
  check_bv_eq_bot_of_not_equiv fun e => h (codeP_equiv_iff.1 e)

theorem bot_or_eq_of_le_rname_eq {Γ : 𝔹} {r s : ℝ} (h : Γ ≤ (rname r : bSet 𝔹) =ᴮ rname s) :
    Γ ≤ ⊥ ∨ r = s := by
  by_cases hrs : r = s
  · exact Or.inr hrs
  · left
    rwa [rname_bv_eq_of_ne hrs] at h

/-- The set of all (names of) reals. -/
def Rc : bSet 𝔹 := ⟨ℝ, fun r => rname r, fun _ => ⊤⟩

/-- A binary operation on `ℝ`, as a set of triples `((x, y), op x y)`. -/
def opC (op : ℝ → ℝ → ℝ) : bSet 𝔹 :=
  ⟨ℝ × ℝ, fun p => pair (pair (rname p.1) (rname p.2)) (rname (op p.1 p.2)), fun _ => ⊤⟩

/-- Addition. -/
def plusC : bSet 𝔹 := opC (· + ·)

/-- Multiplication. -/
def timesC : bSet 𝔹 := opC (· * ·)

/-- The order, as a set of pairs `(x, y)` with `x < y`. -/
def ltC : bSet 𝔹 := ⟨{p : ℝ × ℝ // p.1 < p.2}, fun p => pair (rname p.1.1) (rname p.1.2), fun _ => ⊤⟩

/-- Zero. -/
def zeroC : bSet 𝔹 := rname 0

/-- One. -/
def oneC : bSet 𝔹 := rname 1

@[simp] lemma Rc_type : (Rc : bSet 𝔹).type = ℝ := rfl
@[simp] lemma Rc_func (r : (Rc : bSet 𝔹).type) : (Rc : bSet 𝔹).func r = rname r := rfl
@[simp] lemma Rc_bval (r : (Rc : bSet 𝔹).type) : (Rc : bSet 𝔹).bval r = ⊤ := rfl
@[simp] lemma opC_type (op : ℝ → ℝ → ℝ) : (opC op : bSet 𝔹).type = (ℝ × ℝ) := rfl
@[simp] lemma opC_func (op : ℝ → ℝ → ℝ) (p : (opC op : bSet 𝔹).type) :
    (opC op : bSet 𝔹).func p = pair (pair (rname p.1) (rname p.2)) (rname (op p.1 p.2)) := rfl
@[simp] lemma opC_bval (op : ℝ → ℝ → ℝ) (p : (opC op : bSet 𝔹).type) :
    (opC op : bSet 𝔹).bval p = ⊤ := rfl
@[simp] lemma ltC_type : (ltC : bSet 𝔹).type = {p : ℝ × ℝ // p.1 < p.2} := rfl
@[simp] lemma ltC_func (p : (ltC : bSet 𝔹).type) :
    (ltC : bSet 𝔹).func p = pair (rname p.1.1) (rname p.1.2) := rfl
@[simp] lemma ltC_bval (p : (ltC : bSet 𝔹).type) : (ltC : bSet 𝔹).bval p = ⊤ := rfl

/-! ### Evaluation lemmas -/

theorem mem_Rc (x : bSet 𝔹) : (x ∈ᴮ (Rc : bSet 𝔹)) = ⨆ r : ℝ, x =ᴮ rname r := by
  rw [mem_unfold]
  simp only [Rc_bval, Rc_func, top_inf_eq]
  rfl

lemma rname_mem_Rc {Γ : 𝔹} (r : ℝ) : Γ ≤ (rname r : bSet 𝔹) ∈ᴮ Rc := by
  rw [mem_Rc]
  exact le_trans le_top (le_iSup_of_le r (by rw [bv_eq_refl]))

lemma le_mem_Rc {Γ : 𝔹} {x : bSet 𝔹} {r : ℝ} (h : Γ ≤ x =ᴮ rname r) : Γ ≤ x ∈ᴮ Rc := by
  rw [mem_Rc]; exact le_iSup_of_le r h

lemma mem_Rc_elim {Γ b : 𝔹} {x : bSet 𝔹} (h : Γ ≤ x ∈ᴮ Rc)
    (H : ∀ (r : ℝ) (Γ' : 𝔹), Γ' ≤ Γ → Γ' ≤ x =ᴮ rname r → Γ' ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [mem_Rc]
  exact bv_cases_right fun r => H r _ inf_le_left inf_le_right

theorem app2_opC (op : ℝ → ℝ → ℝ) (x y z : bSet 𝔹) :
    Sem.app2 (opC op) x y z =
      ⨆ p : ℝ × ℝ, (x =ᴮ rname p.1) ⊓ (y =ᴮ rname p.2) ⊓ (z =ᴮ rname (op p.1 p.2)) := by
  rw [Sem.app2, mem_unfold]
  simp only [opC_bval, opC_func, top_inf_eq]
  apply le_antisymm
  · apply iSup_mono; intro p
    have h := (pair_eq_pair_iff (Γ := pair (pair x y) z =ᴮ
      pair (pair (rname p.1) (rname p.2)) (rname (op p.1 p.2)))).mp le_rfl
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h11, h12⟩ := (pair_eq_pair_iff.mp h1)
    exact le_inf (le_inf h11 h12) h2
  · apply iSup_mono; intro p
    exact pair_eq_pair_iff.mpr ⟨pair_eq_pair_iff.mpr ⟨inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right⟩, inf_le_right⟩

lemma le_app2_opC {op : ℝ → ℝ → ℝ} {Γ : 𝔹} {x y z : bSet 𝔹} {r s : ℝ}
    (hx : Γ ≤ x =ᴮ rname r) (hy : Γ ≤ y =ᴮ rname s) (hz : Γ ≤ z =ᴮ rname (op r s)) :
    Γ ≤ Sem.app2 (opC op) x y z := by
  rw [app2_opC]
  exact le_iSup_of_le (r, s) (le_inf (le_inf hx hy) hz)

lemma app2_opC_elim {op : ℝ → ℝ → ℝ} {Γ b : 𝔹} {x y z : bSet 𝔹}
    (h : Γ ≤ Sem.app2 (opC op) x y z)
    (H : ∀ (r s : ℝ) (Γ' : 𝔹), Γ' ≤ Γ → Γ' ≤ x =ᴮ rname r → Γ' ≤ y =ᴮ rname s →
      Γ' ≤ z =ᴮ rname (op r s) → Γ' ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [app2_opC]
  refine bv_cases_right fun p => ?_
  exact H p.1 p.2 _ inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans (inf_le_left.trans inf_le_right)) (inf_le_right.trans inf_le_right)

theorem lt_ltC (x y : bSet 𝔹) :
    Sem.lt ltC x y = ⨆ p : {p : ℝ × ℝ // p.1 < p.2}, (x =ᴮ rname p.1.1) ⊓ (y =ᴮ rname p.1.2) := by
  rw [Sem.lt, mem_unfold]
  simp only [ltC_bval, ltC_func, top_inf_eq]
  apply le_antisymm
  · apply iSup_mono; intro p
    exact le_inf (eq_of_eq_pair_left' le_rfl) (eq_of_eq_pair_right' le_rfl)
  · apply iSup_mono; intro p
    exact pair_eq_pair_iff.mpr ⟨inf_le_left, inf_le_right⟩

lemma le_lt_ltC {Γ : 𝔹} {x y : bSet 𝔹} {r s : ℝ} (hx : Γ ≤ x =ᴮ rname r)
    (hy : Γ ≤ y =ᴮ rname s) (hrs : r < s) : Γ ≤ Sem.lt ltC x y := by
  rw [lt_ltC]
  exact le_iSup_of_le ⟨(r, s), hrs⟩ (le_inf hx hy)

lemma lt_ltC_elim {Γ b : 𝔹} {x y : bSet 𝔹} (h : Γ ≤ Sem.lt ltC x y)
    (H : ∀ (r s : ℝ) (Γ' : 𝔹), Γ' ≤ Γ → r < s → Γ' ≤ x =ᴮ rname r → Γ' ≤ y =ᴮ rname s →
      Γ' ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [lt_ltC]
  refine bv_cases_right fun p => ?_
  exact H p.1.1 p.1.2 _ inf_le_left p.2 (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right)

/-! ### Transport tools -/

lemma le_of_le_bot {Γ b : 𝔹} (h : Γ ≤ ⊥) : Γ ≤ b := h.trans bot_le

/-- Two readings of the same name agree, or the context is trivial. -/
lemma eq_rname_trans {Γ : 𝔹} {x : bSet 𝔹} {r s : ℝ} (h1 : Γ ≤ x =ᴮ rname r)
    (h2 : Γ ≤ x =ᴮ rname s) : Γ ≤ ⊥ ∨ r = s := by
  apply bot_or_eq_of_le_rname_eq
  rw [bv_eq_symm] at h1
  exact bv_trans h1 h2

/-- Two names equal to the same canonical name are equal. -/
lemma bv_eq_of_eq_rname {Γ : 𝔹} {x y : bSet 𝔹} {r : ℝ} (h1 : Γ ≤ x =ᴮ rname r)
    (h2 : Γ ≤ y =ᴮ rname r) : Γ ≤ x =ᴮ y := by
  rw [bv_eq_symm] at h2
  exact bv_trans h1 h2

lemma le_rname_eq_of_eq {Γ : 𝔹} {r s : ℝ} (h : r = s) : Γ ≤ (rname r : bSet 𝔹) =ᴮ rname s := by
  subst h; exact bv_refl

/-- On canonical names, `<` is decided. -/
lemma lt_ltC_rname {Γ : 𝔹} {r s : ℝ} (h : r < s) : Γ ≤ Sem.lt ltC (rname r : bSet 𝔹) (rname s) :=
  le_lt_ltC bv_refl bv_refl h

lemma lt_ltC_rname_elim {Γ : 𝔹} {r s : ℝ} (h : Γ ≤ Sem.lt ltC (rname r : bSet 𝔹) (rname s)) :
    Γ ≤ ⊥ ∨ r < s := by
  by_cases hrs : r < s
  · exact Or.inr hrs
  · left
    refine lt_ltC_elim h fun r' s' Γ' _ hr's' hr hs => ?_
    rcases bot_or_eq_of_le_rname_eq hr with hb | rfl
    · exact hb
    rcases bot_or_eq_of_le_rname_eq hs with hb | rfl
    · exact hb
    exact absurd hr's' hrs

lemma le_ltC_rname {Γ : 𝔹} {r s : ℝ} (h : r ≤ s) : Γ ≤ Sem.le ltC (rname r : bSet 𝔹) (rname s) := by
  rw [Sem.le]
  rcases h.lt_or_eq with h | h
  · exact le_sup_of_le_left (lt_ltC_rname h)
  · exact le_sup_of_le_right (le_rname_eq_of_eq h)

lemma le_ltC_rname_elim {Γ : 𝔹} {r s : ℝ} (h : Γ ≤ Sem.le ltC (rname r : bSet 𝔹) (rname s)) :
    Γ ≤ ⊥ ∨ r ≤ s := by
  by_cases hrs : r ≤ s
  · exact Or.inr hrs
  · left
    rw [Sem.le, rname_bv_eq_of_ne (fun e => hrs e.le), sup_bot_eq] at h
    rcases lt_ltC_rname_elim h with hb | hlt
    · exact hb
    · exact absurd hlt.le hrs

/-! ### The first-order axioms of an ordered field, for arbitrary `𝔹` -/

theorem zeroC_mem : ⊤ ≤ (zeroC : bSet 𝔹) ∈ᴮ Rc := rname_mem_Rc 0

theorem oneC_mem : ⊤ ≤ (oneC : bSet 𝔹) ∈ᴮ Rc := rname_mem_Rc 1

theorem zeroC_ne_oneC : ⊤ ≤ ((zeroC : bSet 𝔹) =ᴮ oneC)ᶜ := by
  rw [zeroC, oneC, rname_bv_eq_of_ne zero_ne_one, compl_bot]

theorem isOp2_opC (op : ℝ → ℝ → ℝ) : ⊤ ≤ Sem.isOp2 (Rc : bSet 𝔹) (opC op) := by
  rw [Sem.isOp2]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ hy
  refine mem_Rc_elim (h₂.trans hx) fun r Γ₃ h₃ hxr => ?_
  refine mem_Rc_elim (h₃.trans hy) fun s Γ₄ h₄ hys => ?_
  have hxr' : Γ₄ ≤ x =ᴮ rname r := h₄.trans hxr
  refine le_iSup_of_le (rname (op r s)) (le_inf (rname_mem_Rc _) (le_inf ?_ ?_))
  · exact le_app2_opC hxr' hys bv_refl
  · refine le_iInf fun z' => ?_
    rw [bv_imp_iff]; intro Γ₅ h₅ hz'
    refine app2_opC_elim hz' fun r' s' Γ₆ h₆ hxr'' hys' hz'' => ?_
    rcases eq_rname_trans hxr'' ((h₆.trans h₅).trans hxr') with hb | rfl
    · exact le_of_le_bot hb
    rcases eq_rname_trans hys' ((h₆.trans h₅).trans hys) with hb | rfl
    · exact le_of_le_bot hb
    exact hz''

theorem assoc_opC {op : ℝ → ℝ → ℝ} (hassoc : ∀ a b c : ℝ, op (op a b) c = op a (op b c)) :
    ⊤ ≤ Sem.assoc (Rc : bSet 𝔹) (opC op) := by
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
  refine app2_opC_elim (((h₇.trans h₆).trans h₅).trans hxyu) fun a b Γ₈ h₈ hxa hyb hu => ?_
  refine app2_opC_elim ((h₈.trans (h₇.trans h₆)).trans huzv) fun u' c Γ₉ h₉ hu' hzc hv => ?_
  refine app2_opC_elim ((h₉.trans (h₈.trans h₇)).trans hyzw) fun b' c' Γ₁₀ h₁₀ hyb' hzc' hw => ?_
  refine app2_opC_elim ((h₁₀.trans h₉).trans (h₈.trans hxww')) fun a' w'' Γ₁₁ h₁₁ hxa' hww'' hw' => ?_
  have H₉ : Γ₁₁ ≤ Γ₉ := h₁₁.trans h₁₀
  have H₈ : Γ₁₁ ≤ Γ₈ := H₉.trans h₉
  rcases eq_rname_trans (H₈.trans hu) (H₉.trans hu') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₉.trans hzc) (h₁₁.trans hzc') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₈.trans hyb) (h₁₁.trans hyb') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₈.trans hxa) hxa' with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (h₁₁.trans hw) hww'' with hb | rfl
  · exact le_of_le_bot hb
  refine bv_eq_of_eq_rname (H₉.trans hv) ?_
  rw [hassoc]
  exact hw'

theorem comm_opC {op : ℝ → ℝ → ℝ} (hcomm : ∀ a b : ℝ, op a b = op b a) :
    ⊤ ≤ Sem.comm (Rc : bSet 𝔹) (opC op) := by
  rw [Sem.comm]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun u => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ hxyu
  refine app2_opC_elim hxyu fun a b Γ₄ h₄ hxa hyb hu => ?_
  refine le_app2_opC hyb hxa ?_
  rw [hcomm]
  exact hu

theorem ident_opC {op : ℝ → ℝ → ℝ} (e : ℝ) (hid : ∀ a : ℝ, op a e = a) :
    ⊤ ≤ Sem.ident (Rc : bSet 𝔹) (opC op) (rname e) := by
  rw [Sem.ident]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine mem_Rc_elim hx fun a Γ₂ h₂ hxa => ?_
  refine le_app2_opC hxa bv_refl ?_
  rw [hid]
  exact hxa

theorem addInv_plusC : ⊤ ≤ Sem.addInv (Rc : bSet 𝔹) plusC zeroC := by
  rw [Sem.addInv]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine mem_Rc_elim hx fun a Γ₂ h₂ hxa => ?_
  refine le_iSup_of_le (rname (-a)) (le_inf (rname_mem_Rc _) ?_)
  refine le_app2_opC hxa bv_refl ?_
  rw [zeroC, add_neg_cancel]
  exact bv_refl

theorem mulInv_timesC : ⊤ ≤ Sem.mulInv (Rc : bSet 𝔹) timesC zeroC oneC := by
  rw [Sem.mulInv]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  rw [bv_imp_iff]; intro Γ₂ h₂ hne
  refine mem_Rc_elim (h₂.trans hx) fun a Γ₃ h₃ hxa => ?_
  by_cases ha : a = 0
  · -- then `x = 0`, contradicting `hne`
    subst ha
    have h1 : Γ₃ ≤ (x =ᴮ zeroC)ᶜ := h₃.trans hne
    have h2 : Γ₃ ≤ x =ᴮ zeroC := hxa
    exact le_of_le_bot (le_inf h2 h1 |>.trans (by rw [inf_compl_eq_bot]))
  · refine le_iSup_of_le (rname a⁻¹) (le_inf (rname_mem_Rc _) ?_)
    refine le_app2_opC hxa bv_refl ?_
    rw [oneC, mul_inv_cancel₀ ha]
    exact bv_refl

theorem distrib_C : ⊤ ≤ Sem.distrib (Rc : bSet 𝔹) plusC timesC := by
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
  have H₅ : Γ₈ ≤ Γ₅ := (h₈.trans h₇).trans h₆
  have H₄ : Γ₈ ≤ Γ₄ := H₅.trans h₅
  have H₆ : Γ₈ ≤ Γ₆ := h₈.trans h₇
  refine app2_opC_elim (H₄.trans hyzu) fun b c Γ₉ h₉ hyb hzc hu => ?_
  refine app2_opC_elim ((h₉.trans H₅).trans hxuv) fun a u' Γ₁₀ h₁₀ hxa hu' hv => ?_
  refine app2_opC_elim (((h₁₀.trans h₉).trans H₆).trans hxyw)
    fun a' b' Γ₁₁ h₁₁ hxa' hyb' hw => ?_
  refine app2_opC_elim ((((h₁₁.trans h₁₀).trans h₉).trans h₈).trans hxzt)
    fun a'' c' Γ₁₂ h₁₂ hxa'' hzc' ht => ?_
  refine app2_opC_elim ((((h₁₂.trans h₁₁).trans h₁₀).trans h₉).trans hwtt')
    fun w' t'' Γ₁₃ h₁₃ hww' htt'' ht' => ?_
  have H₁₂ : Γ₁₃ ≤ Γ₁₂ := h₁₃
  have H₁₁ : Γ₁₃ ≤ Γ₁₁ := H₁₂.trans h₁₂
  have H₁₀ : Γ₁₃ ≤ Γ₁₀ := H₁₁.trans h₁₁
  have H₉ : Γ₁₃ ≤ Γ₉ := H₁₀.trans h₁₀
  rcases eq_rname_trans (H₉.trans hu) (H₁₀.trans hu') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₁₀.trans hxa) (H₁₁.trans hxa') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₁₁.trans hxa') (H₁₂.trans hxa'') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₉.trans hyb) (H₁₁.trans hyb') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₉.trans hzc) (H₁₂.trans hzc') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₁₁.trans hw) hww' with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (H₁₂.trans ht) htt'' with hb | rfl
  · exact le_of_le_bot hb
  refine bv_eq_of_eq_rname (H₁₀.trans hv) ?_
  rw [mul_add]
  exact ht'

theorem irrefl_ltC : ⊤ ≤ Sem.irrefl (Rc : bSet 𝔹) ltC := by
  rw [Sem.irrefl]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine mem_Rc_elim hx fun a Γ₂ h₂ hxa => ?_
  rw [← imp_bot, bv_imp_iff]; intro Γ₃ h₃ hlt
  refine lt_ltC_elim hlt fun r s Γ₄ h₄ hrs hxr hxs => ?_
  rcases eq_rname_trans hxr hxs with hb | rfl
  · exact hb
  · exact absurd hrs (lt_irrefl r)

theorem trans_ltC : ⊤ ≤ Sem.trans (Rc : bSet 𝔹) ltC := by
  rw [Sem.trans]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun z => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ _
  rw [bv_imp_iff]; intro Γ₄ h₄ hxy
  rw [bv_imp_iff]; intro Γ₅ h₅ hyz
  refine lt_ltC_elim (h₅.trans hxy) fun r s Γ₆ h₆ hrs hxr hys => ?_
  refine lt_ltC_elim (h₆.trans hyz) fun s' t Γ₇ h₇ hst hys' hzt => ?_
  rcases eq_rname_trans (h₇.trans hys) hys' with hb | rfl
  · exact le_of_le_bot hb
  exact le_lt_ltC (h₇.trans hxr) hzt (hrs.trans hst)

theorem total_ltC : ⊤ ≤ Sem.total (Rc : bSet 𝔹) ltC := by
  rw [Sem.total]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hx
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ hy
  refine mem_Rc_elim (h₂.trans hx) fun r Γ₃ h₃ hxr => ?_
  refine mem_Rc_elim (h₃.trans hy) fun s Γ₄ h₄ hys => ?_
  have hxr' : Γ₄ ≤ x =ᴮ rname r := h₄.trans hxr
  rcases lt_trichotomy r s with h | h | h
  · exact le_sup_of_le_left (le_lt_ltC hxr' hys h)
  · subst h
    exact le_sup_of_le_right (le_sup_of_le_left (bv_eq_of_eq_rname hxr' hys))
  · exact le_sup_of_le_right (le_sup_of_le_right (le_lt_ltC hys hxr' h))

theorem addCompat_C : ⊤ ≤ Sem.addCompat (Rc : bSet 𝔹) plusC ltC := by
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
  refine lt_ltC_elim ((h₆.trans h₅).trans hxy) fun r s Γ₇ h₇ hrs hxr hys => ?_
  refine app2_opC_elim ((h₇.trans h₆).trans hxzu) fun r' c Γ₈ h₈ hxr' hzc hu => ?_
  refine app2_opC_elim ((h₈.trans h₇).trans hyzv) fun s' c' Γ₉ h₉ hys' hzc' hv => ?_
  rcases eq_rname_trans ((h₉.trans h₈).trans hxr) (h₉.trans hxr') with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans ((h₉.trans h₈).trans hys) hys' with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (h₉.trans hzc) hzc' with hb | rfl
  · exact le_of_le_bot hb
  exact le_lt_ltC (h₉.trans hu) hv (add_lt_add_left hrs c)

theorem mulPos_C : ⊤ ≤ Sem.mulPos (Rc : bSet 𝔹) timesC ltC zeroC := by
  rw [Sem.mulPos]
  refine le_iInf fun x => ?_
  rw [bv_imp_iff]; intro Γ₁ _ _
  refine le_iInf fun y => ?_
  rw [bv_imp_iff]; intro Γ₂ h₂ _
  refine le_iInf fun u => ?_
  rw [bv_imp_iff]; intro Γ₃ h₃ h0x
  rw [bv_imp_iff]; intro Γ₄ h₄ h0y
  rw [bv_imp_iff]; intro Γ₅ h₅ hxyu
  refine lt_ltC_elim ((h₅.trans h₄).trans h0x) fun z r Γ₆ h₆ hzr h0z hxr => ?_
  refine lt_ltC_elim ((h₆.trans h₅).trans h0y) fun z' s Γ₇ h₇ hz's h0z' hys => ?_
  refine app2_opC_elim ((h₇.trans h₆).trans hxyu) fun r' s' Γ₈ h₈ hxr' hys' hu => ?_
  rcases bot_or_eq_of_le_rname_eq ((h₈.trans h₇).trans h0z) with hb | hz
  · exact le_of_le_bot hb
  rcases bot_or_eq_of_le_rname_eq (h₈.trans h0z') with hb | hz'
  · exact le_of_le_bot hb
  rcases eq_rname_trans ((h₈.trans h₇).trans hxr) hxr' with hb | rfl
  · exact le_of_le_bot hb
  rcases eq_rname_trans (h₈.trans hys) hys' with hb | rfl
  · exact le_of_le_bot hb
  subst hz hz'
  exact le_lt_ltC bv_refl hu (mul_pos hzr hz's)


/-! ### More transport tools -/

lemma le_le_ltC {Γ : 𝔹} {x y : bSet 𝔹} {r s : ℝ} (hx : Γ ≤ x =ᴮ rname r)
    (hy : Γ ≤ y =ᴮ rname s) (h : r ≤ s) : Γ ≤ Sem.le ltC x y := by
  rw [Sem.le]
  rcases h.lt_or_eq with h | rfl
  · exact le_sup_of_le_left (le_lt_ltC hx hy h)
  · exact le_sup_of_le_right (bv_eq_of_eq_rname hx hy)

lemma le_ltC_elim {Γ : 𝔹} {x y : bSet 𝔹} {r s : ℝ} (h : Γ ≤ Sem.le ltC x y)
    (hx : Γ ≤ x =ᴮ rname r) (hy : Γ ≤ y =ᴮ rname s) : Γ ≤ ⊥ ∨ r ≤ s := by
  by_cases hrs : r ≤ s
  · exact Or.inr hrs
  · left
    rw [Sem.le] at h
    -- `Γ ≤ lt x y ⊔ x =ᴮ y`; both disjuncts are `⊥` on `Γ`
    have h1 : Γ ⊓ Sem.lt ltC x y ≤ ⊥ := by
      refine lt_ltC_elim (b := ⊥) inf_le_right fun r' s' Γ' hΓ' hr's' hxr' hys' => ?_
      have hΓ'' : Γ' ≤ Γ := hΓ'.trans inf_le_left
      rcases eq_rname_trans (hΓ''.trans hx) hxr' with hb | rfl
      · exact hb
      rcases eq_rname_trans (hΓ''.trans hy) hys' with hb | rfl
      · exact hb
      exact absurd hr's'.le hrs
    have h2 : Γ ⊓ x =ᴮ y ≤ ⊥ := by
      have e : Γ ⊓ x =ᴮ y ≤ (rname r : bSet 𝔹) =ᴮ rname s := by
        have h3 : Γ ⊓ x =ᴮ y ≤ rname r =ᴮ x := bv_symm (inf_le_left.trans hx)
        have h4 : Γ ⊓ x =ᴮ y ≤ y =ᴮ rname s := inf_le_left.trans hy
        exact bv_trans (bv_trans h3 inf_le_right) h4
      rw [rname_bv_eq_of_ne (fun e => hrs e.le)] at e
      exact e
    calc Γ = Γ ⊓ (Sem.lt ltC x y ⊔ x =ᴮ y) := (inf_eq_left.2 h).symm
      _ = (Γ ⊓ Sem.lt ltC x y) ⊔ (Γ ⊓ x =ᴮ y) := inf_sup_left _ _ _
      _ ≤ ⊥ := sup_le h1 h2

lemma le_of_inf_compl_le_bot {Γ b : 𝔹} (h : Γ ⊓ bᶜ ≤ ⊥) : Γ ≤ b := by
  have : Γ \ b = ⊥ := le_bot_iff.1 (by rwa [sdiff_eq])
  exact sdiff_eq_bot_iff.1 this

/-! ### Dedekind completeness -/

section Complete

/-- An enumeration of the rationals. -/
noncomputable def qe : ℕ → ℚ := fun n => (Denumerable.eqv ℚ).symm n

lemma qe_surjective : Function.Surjective qe := (Denumerable.eqv ℚ).symm.surjective

/-- The cut event `‖∃ s ∈ S, q < s‖`, for a subset `S` of the check reals. -/
def cutEv (S : bSet 𝔹) (q : ℚ) : 𝔹 :=
  ⨆ (r : ℝ) (_ : (q : ℝ) < r), rname r ∈ᴮ S

lemma le_cutEv {Γ : 𝔹} {S : bSet 𝔹} {q : ℚ} {r : ℝ} (hqr : (q : ℝ) < r)
    (h : Γ ≤ (rname r : bSet 𝔹) ∈ᴮ S) : Γ ≤ cutEv S q :=
  le_iSup₂_of_le r hqr h

lemma cutEv_elim {Γ b : 𝔹} {S : bSet 𝔹} {q : ℚ} (h : Γ ≤ cutEv S q)
    (H : ∀ r : ℝ, (q : ℝ) < r → Γ ⊓ (rname r : bSet 𝔹) ∈ᴮ S ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [cutEv, inf_iSup_eq]
  refine iSup_le fun r => ?_
  rw [inf_iSup_eq]
  exact iSup_le fun hqr => H r hqr

variable {D : Set 𝔹} (hD : DenseOmegaClosed D)
include hD

/-- **Dedekind completeness of the check reals**, for a Boolean algebra with a dense ω-closed
subset: every nonempty bounded-above internal subset of `Rc` has a least upper bound (a check
real, since the cut of the subset can be decided completely on a nonzero piece). -/
theorem complete_Rc : ⊤ ≤ Sem.complete (Rc : bSet 𝔹) ltC := by
  rw [Sem.complete]
  refine le_iInf fun S => ?_
  rw [bv_imp_iff]; intro Γ₁ _ hSP
  rw [bv_imp_iff]; intro Γ₂ h₂ hne
  rw [bv_imp_iff]; intro Γ₃ h₃ hbdd
  have hsub : Γ₃ ≤ S ⊆ᴮ Rc := (h₃.trans h₂).trans (bv_powerset_spec.2 hSP)
  -- by contradiction: it suffices to refute a nonzero piece below `Γ₃` forcing "no lub"
  apply le_of_inf_compl_le_bot
  set Γ' := Γ₃ ⊓ (⨆ u : bSet 𝔹, u ∈ᴮ Rc ⊓ ((⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s u) ⊓
    ⨅ v : bSet 𝔹, v ∈ᴮ Rc ⟹ ((⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s v) ⟹ Sem.le ltC u v)))ᶜ
    with hΓ'
  by_contra hpos
  have hΓ'pos : ⊥ < Γ' := bot_lt_iff_ne_bot.2 fun h => hpos (le_of_eq h)
  have hΓ'₃ : Γ' ≤ Γ₃ := inf_le_left
  have hΓ'c : Γ' ≤ (⨆ u : bSet 𝔹, u ∈ᴮ Rc ⊓ ((⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s u) ⊓
    ⨅ v : bSet 𝔹, v ∈ᴮ Rc ⟹ ((⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s v) ⟹ Sem.le ltC u v)))ᶜ :=
    inf_le_right
  -- (a) an element `rname r₀ ∈ S` on a nonzero piece
  have hne' : Γ' ≤ ⨆ i, S.bval i := by
    have this : Γ' ≤ (S =ᴮ (∅ : bSet 𝔹))ᶜ := (hΓ'₃.trans h₃).trans hne
    rwa [eq_empty, compl_compl] at this
  obtain ⟨i₀, hi₀⟩ := nonzero_wit' hΓ'pos hne'
  set Γ₅ := S.bval i₀ ⊓ Γ' with hΓ₅
  have hΓ₅' : Γ₅ ≤ Γ' := inf_le_right
  have hmem₀ : Γ₅ ≤ S.func i₀ ∈ᴮ S := inf_le_left.trans (mem_mk' S i₀)
  have hmemR₀ : Γ₅ ≤ S.func i₀ ∈ᴮ Rc := mem_of_mem_subset ((hΓ₅'.trans hΓ'₃).trans hsub) hmem₀
  rw [mem_Rc] at hmemR₀
  obtain ⟨r₀, hr₀⟩ := nonzero_wit' hi₀ hmemR₀
  set Γ₆ := (S.func i₀ =ᴮ rname r₀) ⊓ Γ₅ with hΓ₆
  have hΓ₆₅ : Γ₆ ≤ Γ₅ := inf_le_right
  have hr₀S : Γ₆ ≤ (rname r₀ : bSet 𝔹) ∈ᴮ S :=
    subst_congr_mem_left' inf_le_left (hΓ₆₅.trans hmem₀)
  -- (b) an upper bound `rname r_b` on a nonzero piece
  have hbdd' : Γ₆ ≤ ⨆ b : bSet 𝔹, b ∈ᴮ Rc ⊓ ⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s b :=
    ((hΓ₆₅.trans hΓ₅').trans hΓ'₃).trans hbdd
  obtain ⟨bn, hbn⟩ := nonzero_wit' hr₀ hbdd'
  set Γ₇ := (bn ∈ᴮ Rc ⊓ ⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s bn) ⊓ Γ₆ with hΓ₇
  have hΓ₇₆ : Γ₇ ≤ Γ₆ := inf_le_right
  have hbnR : Γ₇ ≤ bn ∈ᴮ Rc := inf_le_left.trans inf_le_left
  have hbnub : Γ₇ ≤ ⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s bn := inf_le_left.trans inf_le_right
  rw [mem_Rc] at hbnR
  obtain ⟨rb, hrb⟩ := nonzero_wit' hbn hbnR
  set Γ₈ := (bn =ᴮ rname rb) ⊓ Γ₇ with hΓ₈
  have hΓ₈₇ : Γ₈ ≤ Γ₇ := inf_le_right
  have hbnrb : Γ₈ ≤ bn =ᴮ rname rb := inf_le_left
  -- the upper-bound property, read on check reals
  have hub : ∀ (r : ℝ) (Γ'' : 𝔹), Γ'' ≤ Γ₈ → Γ'' ≤ (rname r : bSet 𝔹) ∈ᴮ S → Γ'' ≤ ⊥ ∨ r ≤ rb := by
    intro r Γ'' hΓ'' hrS
    have h1 : Γ'' ≤ Sem.le ltC (rname r) bn := by
      have := (hΓ''.trans hΓ₈₇).trans hbnub
      exact (bv_imp_iff.1 (iInf_le _ (rname r) |> le_trans this) le_rfl hrS)
    exact le_ltC_elim h1 bv_refl (hΓ''.trans hbnrb)
  -- (c) decide the cut on a nonzero piece
  obtain ⟨Γ₉, c, hΓ₉pos, hΓ₉₈, hc⟩ := exists_decide_of_denseOmegaClosed hD hrb
    (fun n => cutEv S (qe n))
  have hΓ₉₆ : Γ₉ ≤ Γ₆ := (hΓ₉₈.trans hΓ₈₇).trans hΓ₇₆
  set C : Set ℝ := {x | ∃ n, c n = true ∧ x = ((qe n : ℚ) : ℝ)} with hC
  have hc_true : ∀ n, Γ₉ ≤ cutEv S (qe n) → c n = true := by
    intro n hn
    by_contra hf
    have hf' : c n = false := by simpa using hf
    have := le_inf hn ((hc n).2 hf')
    rw [inf_compl_eq_bot] at this
    exact absurd (lt_of_lt_of_le hΓ₉pos this) (lt_irrefl _)
  have hCne : C.Nonempty := by
    obtain ⟨q, hq⟩ := exists_rat_lt r₀
    obtain ⟨n, hn⟩ := qe_surjective q
    refine ⟨((qe n : ℚ) : ℝ), n, ?_, rfl⟩
    apply hc_true
    exact le_cutEv (by rw [hn]; exact hq) (hΓ₉₆.trans hr₀S)
  have hCbdd : BddAbove C := by
    refine ⟨rb, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 : Γ₉ ≤ cutEv S (qe n) := (hc n).1 hn
    have h2 : Γ₉ ≤ ⊥ := by
      refine cutEv_elim h1 fun r hqr => ?_
      rcases hub r _ (inf_le_left.trans hΓ₉₈) inf_le_right with hb | hle
      · exact hb
      · exact absurd (hlt.trans hqr) (not_lt.2 hle)
    exact absurd (lt_of_lt_of_le hΓ₉pos h2) (lt_irrefl _)
  set u : ℝ := sSup C with hu
  -- (d) `rname u` is the least upper bound of `S` on `Γ₉`
  have hlub : Γ₉ ≤ ⨆ u : bSet 𝔹, u ∈ᴮ Rc ⊓ ((⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s u) ⊓
      ⨅ v : bSet 𝔹, v ∈ᴮ Rc ⟹ ((⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s v) ⟹ Sem.le ltC u v)) := by
    refine le_iSup_of_le (rname u) (le_inf (rname_mem_Rc u) (le_inf ?_ ?_))
    · -- upper bound
      refine le_iInf fun s => ?_
      rw [bv_imp_iff]; intro Γ₁₀ h₁₀ hs
      have hsR : Γ₁₀ ≤ s ∈ᴮ Rc :=
        mem_of_mem_subset ((((h₁₀.trans hΓ₉₆).trans hΓ₆₅).trans hΓ₅').trans (hΓ'₃.trans hsub)) hs
      refine mem_Rc_elim hsR fun r Γ₁₁ h₁₁ hsr => ?_
      rcases le_or_gt r u with hru | hur
      · exact le_le_ltC hsr bv_refl hru
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hur
        obtain ⟨n, hn⟩ := qe_surjective q
        have hcn : c n = false := by
          by_contra hf
          have hf' : c n = true := by simpa using hf
          have : ((qe n : ℚ) : ℝ) ∈ C := ⟨n, hf', rfl⟩
          have := le_csSup hCbdd this
          rw [hn] at this
          exact absurd (lt_of_le_of_lt this hq1) (lt_irrefl _)
        have h1 : Γ₁₁ ≤ cutEv S (qe n) :=
          le_cutEv (by rw [hn]; exact hq2) (subst_congr_mem_left' hsr (h₁₁.trans hs))
        have h2 : Γ₁₁ ≤ (cutEv S (qe n))ᶜ := (h₁₁.trans h₁₀).trans ((hc n).2 hcn)
        exact le_of_le_bot ((le_inf h1 h2).trans (by rw [inf_compl_eq_bot]))
    · -- least
      refine le_iInf fun v => ?_
      rw [bv_imp_iff]; intro Γ₁₀ h₁₀ hv
      rw [bv_imp_iff]; intro Γ₁₁ h₁₁ hvub
      refine mem_Rc_elim (h₁₁.trans hv) fun rv Γ₁₂ h₁₂ hvr => ?_
      rcases le_or_gt u rv with huv | hvu
      · exact le_le_ltC bv_refl hvr huv
      · obtain ⟨x, ⟨n, hn, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hCne hvu
        have h1 : Γ₁₂ ≤ cutEv S (qe n) := ((h₁₂.trans h₁₁).trans h₁₀).trans ((hc n).1 hn)
        refine le_of_le_bot (cutEv_elim h1 fun r hqr => ?_)
        have h3 : Γ₁₂ ⊓ (rname r : bSet 𝔹) ∈ᴮ S ≤ Sem.le ltC (rname r) v := by
          have h4 : Γ₁₂ ⊓ (rname r : bSet 𝔹) ∈ᴮ S ≤ ⨅ s : bSet 𝔹, s ∈ᴮ S ⟹ Sem.le ltC s v :=
            (inf_le_left.trans h₁₂).trans hvub
          exact bv_imp_iff.1 (iInf_le _ (rname r) |> le_trans h4) le_rfl inf_le_right
        rcases le_ltC_elim h3 bv_refl (inf_le_left.trans hvr) with hb | hle
        · exact hb
        · exact absurd (hx.trans hqr) (not_lt.2 hle)
  -- (e) contradiction
  have h1 : Γ₉ ≤ ⊥ := (le_inf hlub ((hΓ₉₆.trans hΓ₆₅).trans (hΓ₅'.trans hΓ'c))).trans
    (by rw [inf_compl_eq_bot])
  exact absurd (lt_of_lt_of_le hΓ₉pos h1) (lt_irrefl _)

/-- **The check reals form a complete ordered field** in `V 𝔹`, for `𝔹` with a dense ω-closed
subset. -/
theorem completeOrderedField_Rc :
    ⊤ ≤ Sem.completeOrderedField (Rc : bSet 𝔹) plusC timesC ltC zeroC oneC := by
  rw [Sem.completeOrderedField]
  refine le_inf (isOp2_opC _) (le_inf (isOp2_opC _) (le_inf zeroC_mem (le_inf oneC_mem
    (le_inf (assoc_opC add_assoc) (le_inf (comm_opC add_comm) (le_inf (ident_opC 0 add_zero)
    (le_inf addInv_plusC (le_inf (assoc_opC mul_assoc) (le_inf (comm_opC mul_comm)
    (le_inf (ident_opC 1 mul_one) (le_inf mulInv_timesC (le_inf zeroC_ne_oneC (le_inf distrib_C
    (le_inf irrefl_ltC (le_inf trans_ltC (le_inf total_ltC (le_inf addCompat_C
    (le_inf mulPos_C (complete_Rc hD)))))))))))))))))))

end Complete

/-! ### The collapse algebra -/

/-- The check reals form a complete ordered field in `V 𝔹_collapse`. -/
theorem completeOrderedField_Rc_collapse :
    ⊤ ≤ Sem.completeOrderedField (Rc : bSet collapse_algebra.𝔹_collapse) plusC timesC ltC
      zeroC oneC :=
  completeOrderedField_Rc Collapse.denseOmegaClosed_D_col

end CheckReals

end Flypitch.Erdos501
