/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Internal complete ordered fields: the Boolean-valued toolkit for unit (F8) (`PLAN.md` §6).
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Semantics

set_option relaxedAutoImplicit true

/-!
# Internal complete ordered fields (unit (F8), part 1)

Let `F = (R, plus, times, ltR, zero, one)` be six names in `bSet β` and `Γ ≤ F.COF` (`F` is a complete
ordered field on `Γ`, `Sem.completeOrderedField`).  This file develops, at the level of Boolean
values, the elementary theory of `F` needed to build the internal isomorphism `F ≅ Rdot`:

* names for the operations by the maximum principle (`opN`, `Fld.add`, `Fld.mul`, `Fld.neg`,
  `Fld.inv`) and their characterizing properties (`add_app2`, `add_unique`, congruence);
* the ordered abelian group laws (`add_assoc`, `add_comm`, `add_zero`, `add_neg`, cancellation,
  `add_lt_add_right`, …), `zero_lt_one`, halving (`half_add_half`);
* the internal naturals `mulN n x = x + ⋯ + x`, the halves `hR k = 1/2^k`, the dyadics
  `dyR m k = m / 2^k`, their order and additive arithmetic;
* the **Archimedean property** (`arch`, from Dedekind completeness) and the **density of the
  dyadics** (`dense`).

Everything is generic in the Boolean algebra `β`.  Statements are Γ-style (`Γ ≤ …`); the relation
`x ≡[Γ] y := Γ ≤ x =ᴮ y` is an equivalence usable in `calc` blocks.
-/

open Flypitch bSet Lattice
open scoped Flypitch

namespace Flypitch.Erdos501

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-! ### Generic Γ-style tools -/

namespace BV

lemma mp {Γ a c : β} (h1 : Γ ≤ a ⟹ c) (h2 : Γ ≤ a) : Γ ≤ c :=
  (le_inf h1 h2).trans bv_imp_elim

lemma iSup_elim {α : Type*} {Γ c : β} {s : α → β} (h : Γ ≤ ⨆ i, s i)
    (H : ∀ (i : α) (Γ' : β), Γ' ≤ Γ → Γ' ≤ s i → Γ' ≤ c) : Γ ≤ c :=
  (le_inf le_rfl h).trans (bv_cases_right fun i => H i _ inf_le_left inf_le_right)

lemma or_elim {Γ a₁ a₂ b : β} (h : Γ ≤ a₁ ⊔ a₂)
    (H₁ : ∀ Γ' : β, Γ' ≤ Γ → Γ' ≤ a₁ → Γ' ≤ b)
    (H₂ : ∀ Γ' : β, Γ' ≤ Γ → Γ' ≤ a₂ → Γ' ≤ b) : Γ ≤ b := by
  refine (le_inf le_rfl h).trans ?_
  rw [inf_sup_left]
  exact sup_le (H₁ _ inf_le_left inf_le_right) (H₂ _ inf_le_left inf_le_right)

lemma compl_of_inf_le_bot {Γ a : β} (h : Γ ⊓ a ≤ ⊥) : Γ ≤ aᶜ :=
  le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr h)

lemma bot_of_compl {Γ a : β} (h1 : Γ ≤ a) (h2 : Γ ≤ aᶜ) : Γ ≤ ⊥ :=
  (le_inf h1 h2).trans (by rw [inf_compl_eq_bot])

lemma of_bot {Γ a : β} (h : Γ ≤ ⊥) : Γ ≤ a := h.trans bot_le

/-- Proof by contradiction: to show `Γ ≤ a`, show `Γ ⊓ aᶜ ≤ ⊥`. -/
lemma by_contra {Γ a : β} (h : Γ ⊓ aᶜ ≤ ⊥) : Γ ≤ a := by
  have := compl_of_inf_le_bot h
  rwa [compl_compl] at this

end BV

/-- `x ≡[Γ] y` is `Γ ≤ x =ᴮ y`. -/
notation:50 x " ≡[" Γ "] " y => bSet.bv_eq' Γ x y

instance bv_eq'_trans {Γ : β} : @Trans (bSet β) (bSet β) (bSet β) (bv_eq' Γ) (bv_eq' Γ) (bv_eq' Γ) :=
  ⟨fun h1 h2 => bv_trans h1 h2⟩

/-! ### The data of an internal ordered field -/

/-- Six names: the carrier `R`, the operations `plus`, `times` (sets of triples `((x, y), z)`), the
order `ltR` (a set of pairs), and the constants `zero`, `one`. -/
structure Fld (β : Type) [NontrivialCompleteBooleanAlgebra β] where
  R : bSet β
  plus : bSet β
  times : bSet β
  ltR : bSet β
  zero : bSet β
  one : bSet β

namespace Fld

variable (F : Fld β)

/-- The Boolean value of "`F` is a complete ordered field". -/
def COF : β := Sem.completeOrderedField F.R F.plus F.times F.ltR F.zero F.one

/-- `x < y` in `F`. -/
abbrev lt (x y : bSet β) : β := Sem.lt F.ltR x y

/-- `x ≤ y` in `F`. -/
abbrev le (x y : bSet β) : β := Sem.le F.ltR x y

/-! #### Names for the operations, by the maximum principle -/

/-- A name for `op(x, y)`: the maximum-principle witness of `⨆ z, app2 op x y z`. -/
noncomputable def opN (op x y : bSet β) : bSet β :=
  Classical.choose (maximum_principle (fun z => Sem.app2 op x y z) B_ext_pair_mem_right)

lemma opN_spec (op x y : bSet β) :
    (⨆ z : bSet β, Sem.app2 op x y z) = Sem.app2 op x y (opN op x y) :=
  Classical.choose_spec (maximum_principle (fun z => Sem.app2 op x y z) B_ext_pair_mem_right)

/-- A name for `x + y`. -/
noncomputable def add (x y : bSet β) : bSet β := opN F.plus x y

/-- A name for `x · y`. -/
noncomputable def mul (x y : bSet β) : bSet β := opN F.times x y

lemma B_ext_neg_pred (x : bSet β) :
    B_ext (fun y : bSet β => y ∈ᴮ F.R ⊓ Sem.app2 F.plus x y F.zero) :=
  B_ext_inf B_ext_mem_left
    (B_ext_pair_right (ϕ := fun w => pair w F.zero ∈ᴮ F.plus) B_ext_pair_mem_left)

/-- A name for `-x`: the maximum-principle witness of `⨆ y, y ∈ R ⊓ x + y = 0`. -/
noncomputable def neg (x : bSet β) : bSet β :=
  Classical.choose (maximum_principle _ (F.B_ext_neg_pred x))

lemma neg_spec (x : bSet β) :
    (⨆ y : bSet β, y ∈ᴮ F.R ⊓ Sem.app2 F.plus x y F.zero) =
      (F.neg x ∈ᴮ F.R ⊓ Sem.app2 F.plus x (F.neg x) F.zero) :=
  Classical.choose_spec (maximum_principle _ (F.B_ext_neg_pred x))

lemma B_ext_inv_pred (x : bSet β) :
    B_ext (fun y : bSet β => y ∈ᴮ F.R ⊓ Sem.app2 F.times x y F.one) :=
  B_ext_inf B_ext_mem_left
    (B_ext_pair_right (ϕ := fun w => pair w F.one ∈ᴮ F.times) B_ext_pair_mem_left)

/-- A name for `x⁻¹`. -/
noncomputable def inv (x : bSet β) : bSet β :=
  Classical.choose (maximum_principle _ (F.B_ext_inv_pred x))

lemma inv_spec (x : bSet β) :
    (⨆ y : bSet β, y ∈ᴮ F.R ⊓ Sem.app2 F.times x y F.one) =
      (F.inv x ∈ᴮ F.R ⊓ Sem.app2 F.times x (F.inv x) F.one) :=
  Classical.choose_spec (maximum_principle _ (F.B_ext_inv_pred x))

variable {F}
variable {Γ : β}

/-! #### Projections of the twenty axioms -/

section proj
variable (H : Γ ≤ F.COF)
include H

lemma cof_isOp2_plus : Γ ≤ Sem.isOp2 F.R F.plus := bv_and_left H
lemma cof_isOp2_times : Γ ≤ Sem.isOp2 F.R F.times := bv_and_left (bv_and_right H)
lemma cof_zero_mem : Γ ≤ F.zero ∈ᴮ F.R := bv_and_left (bv_and_right (bv_and_right H))
lemma cof_one_mem : Γ ≤ F.one ∈ᴮ F.R :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right H)))
lemma cof_add_assoc : Γ ≤ Sem.assoc F.R F.plus :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right H))))
lemma cof_add_comm : Γ ≤ Sem.comm F.R F.plus :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right H)))))
lemma cof_add_ident : Γ ≤ Sem.ident F.R F.plus F.zero :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right H))))))
lemma cof_addInv : Γ ≤ Sem.addInv F.R F.plus F.zero :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right H)))))))
lemma cof_mul_assoc : Γ ≤ Sem.assoc F.R F.times :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right H))))))))
lemma cof_mul_comm : Γ ≤ Sem.comm F.R F.times :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right H)))))))))
lemma cof_mul_ident : Γ ≤ Sem.ident F.R F.times F.one :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right H))))))))))
lemma cof_mulInv : Γ ≤ Sem.mulInv F.R F.times F.zero F.one :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right H)))))))))))
lemma cof_zero_ne_one : Γ ≤ (F.zero =ᴮ F.one)ᶜ :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right H))))))))))))
lemma cof_distrib : Γ ≤ Sem.distrib F.R F.plus F.times :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right H)))))))))))))
lemma cof_irrefl : Γ ≤ Sem.irrefl F.R F.ltR :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right H))))))))))))))
lemma cof_trans : Γ ≤ Sem.trans F.R F.ltR :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right H)))))))))))))))
lemma cof_total : Γ ≤ Sem.total F.R F.ltR :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right H))))))))))))))))
lemma cof_addCompat : Γ ≤ Sem.addCompat F.R F.plus F.ltR :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right H)))))))))))))))))
lemma cof_mulPos : Γ ≤ Sem.mulPos F.R F.times F.ltR F.zero :=
  bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right H))))))))))))))))))
lemma cof_complete : Γ ≤ Sem.complete F.R F.ltR :=
  bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right H))))))))))))))))))

end proj

lemma cof_mono {Γ' : β} (H : Γ ≤ F.COF) (h : Γ' ≤ Γ) : Γ' ≤ F.COF := h.trans H

/-! #### Congruence of the atomic predicates -/

lemma app2_congr {op x x' y y' z z' : bSet β} (hx : x ≡[Γ] x') (hy : y ≡[Γ] y') (hz : z ≡[Γ] z')
    (h : Γ ≤ Sem.app2 op x y z) : Γ ≤ Sem.app2 op x' y' z' :=
  mem_congr (pair_congr (pair_congr hx hy) hz) bv_refl h

lemma lt_congr {x x' y y' : bSet β} (hx : x ≡[Γ] x') (hy : y ≡[Γ] y') (h : Γ ≤ F.lt x y) :
    Γ ≤ F.lt x' y' :=
  mem_congr (pair_congr hx hy) bv_refl h

lemma mem_congr' {x x' : bSet β} (hx : x ≡[Γ] x') (h : Γ ≤ x ∈ᴮ F.R) : Γ ≤ x' ∈ᴮ F.R :=
  mem_congr hx bv_refl h

/-! #### Binary operations -/

section op
variable {op : bSet β} (hop : Γ ≤ Sem.isOp2 F.R op)
include hop

lemma isOp2_elim {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ≤ ⨆ z : bSet β, z ∈ᴮ F.R ⊓
      (Sem.app2 op x y z ⊓ ⨅ z' : bSet β, Sem.app2 op x y z' ⟹ z' =ᴮ z) :=
  BV.mp ((BV.mp (hop.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy

lemma opN_app2 {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ≤ Sem.app2 op x y (opN op x y) := by
  rw [← opN_spec]
  refine (isOp2_elim hop hx hy).trans (iSup_le fun z => ?_)
  exact le_iSup_of_le z (inf_le_right.trans inf_le_left)

lemma opN_unique {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ Sem.app2 op x y z) : z ≡[Γ] opN op x y := by
  refine BV.iSup_elim (isOp2_elim hop hx hy) fun w Γ' h' hw => ?_
  have h1 : Γ' ≤ z =ᴮ w :=
    BV.mp ((bv_and_right (bv_and_right hw)).trans (iInf_le _ z)) (h'.trans hz)
  have h2 : Γ' ≤ opN op x y =ᴮ w :=
    BV.mp ((bv_and_right (bv_and_right hw)).trans (iInf_le _ (opN op x y)))
      (h'.trans (opN_app2 hop hx hy))
  exact bv_trans h1 (bv_symm h2)

lemma opN_mem {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ≤ opN op x y ∈ᴮ F.R := by
  refine BV.iSup_elim (isOp2_elim hop hx hy) fun w Γ' h' hw => ?_
  have h2 : Γ' ≤ opN op x y =ᴮ w :=
    BV.mp ((bv_and_right (bv_and_right hw)).trans (iInf_le _ (opN op x y)))
      (h'.trans (opN_app2 hop hx hy))
  exact mem_congr' (F := F) (bv_symm h2) (bv_and_left hw)

lemma opN_congr {x x' y y' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hxx' : x ≡[Γ] x') (hyy' : y ≡[Γ] y') : opN op x y ≡[Γ] opN op x' y' :=
  opN_unique hop (mem_congr' hxx' hx) (mem_congr' hyy' hy)
    (app2_congr hxx' hyy' bv_refl (opN_app2 hop hx hy))

/-- If `app2 op x y z` and `app2 op x y z'` then `z = z'`. -/
lemma app2_unique {x y z z' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ Sem.app2 op x y z) (hz' : Γ ≤ Sem.app2 op x y z') : z ≡[Γ] z' :=
  bv_trans (opN_unique hop hx hy hz) (bv_symm (opN_unique hop hx hy hz'))

end op

/-! #### Addition -/

section add
variable (H : Γ ≤ F.COF)
include H

lemma add_mem {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) : Γ ≤ F.add x y ∈ᴮ F.R :=
  opN_mem (cof_isOp2_plus H) hx hy

lemma add_app2 {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ≤ Sem.app2 F.plus x y (F.add x y) :=
  opN_app2 (cof_isOp2_plus H) hx hy

lemma add_unique {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ Sem.app2 F.plus x y z) : z ≡[Γ] F.add x y :=
  opN_unique (cof_isOp2_plus H) hx hy hz

lemma add_congr {x x' y y' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hxx' : x ≡[Γ] x') (hyy' : y ≡[Γ] y') : F.add x y ≡[Γ] F.add x' y' :=
  opN_congr (cof_isOp2_plus H) hx hy hxx' hyy'

lemma add_congr_left {x x' y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hxx' : x ≡[Γ] x') : F.add x y ≡[Γ] F.add x' y :=
  add_congr H hx hy hxx' bv_refl

lemma add_congr_right {x y y' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hyy' : y ≡[Γ] y') : F.add x y ≡[Γ] F.add x y' :=
  add_congr H hx hy bv_refl hyy'

lemma add_assoc {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (hz : Γ ≤ z ∈ᴮ F.R) :
    F.add (F.add x y) z ≡[Γ] F.add x (F.add y z) := by
  have h := cof_add_assoc H
  rw [Sem.assoc] at h
  have h1 := BV.mp (h.trans (iInf_le _ x)) hx
  have h2 := BV.mp (h1.trans (iInf_le _ y)) hy
  have h3 := BV.mp (h2.trans (iInf_le _ z)) hz
  have h4 := h3.trans (iInf_le _ (F.add x y)) |>.trans (iInf_le _ (F.add (F.add x y) z))
    |>.trans (iInf_le _ (F.add y z)) |>.trans (iInf_le _ (F.add x (F.add y z)))
  exact BV.mp (BV.mp (BV.mp (BV.mp h4 (add_app2 H hx hy)) (add_app2 H (add_mem H hx hy) hz))
    (add_app2 H hy hz)) (add_app2 H hx (add_mem H hy hz))

lemma add_comm {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    F.add x y ≡[Γ] F.add y x := by
  have h := cof_add_comm H
  rw [Sem.comm] at h
  have h1 := BV.mp ((BV.mp (h.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy
  have h2 := BV.mp (h1.trans (iInf_le _ (F.add x y))) (add_app2 H hx hy)
  exact add_unique H hy hx h2

lemma add_zero {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.add x F.zero ≡[Γ] x := by
  have h := cof_add_ident H
  rw [Sem.ident] at h
  exact bv_symm (add_unique H hx (cof_zero_mem H) (BV.mp (h.trans (iInf_le _ x)) hx))

lemma zero_add {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.add F.zero x ≡[Γ] x :=
  bv_trans (add_comm H (cof_zero_mem H) hx) (add_zero H hx)

lemma neg_mem_and_app2 {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) :
    Γ ≤ F.neg x ∈ᴮ F.R ⊓ Sem.app2 F.plus x (F.neg x) F.zero := by
  rw [← neg_spec]
  have h := cof_addInv H
  rw [Sem.addInv] at h
  exact BV.mp (h.trans (iInf_le _ x)) hx

lemma neg_mem {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : Γ ≤ F.neg x ∈ᴮ F.R :=
  bv_and_left (neg_mem_and_app2 H hx)

lemma add_neg {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.add x (F.neg x) ≡[Γ] F.zero :=
  bv_symm (add_unique H hx (neg_mem H hx) (bv_and_right (neg_mem_and_app2 H hx)))

lemma neg_add {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.add (F.neg x) x ≡[Γ] F.zero :=
  bv_trans (add_comm H (neg_mem H hx) hx) (add_neg H hx)

lemma add_left_cancel {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : F.add z x ≡[Γ] F.add z y) : x ≡[Γ] y := by
  have hnz := neg_mem H hz
  calc x ≡[Γ] F.add F.zero x := bv_symm (zero_add H hx)
    _ ≡[Γ] F.add (F.add (F.neg z) z) x := add_congr_left H (cof_zero_mem H) hx (bv_symm (neg_add H hz))
    _ ≡[Γ] F.add (F.neg z) (F.add z x) := add_assoc H hnz hz hx
    _ ≡[Γ] F.add (F.neg z) (F.add z y) := add_congr_right H hnz (add_mem H hz hx) h
    _ ≡[Γ] F.add (F.add (F.neg z) z) y := bv_symm (add_assoc H hnz hz hy)
    _ ≡[Γ] F.add F.zero y := add_congr_left H (add_mem H hnz hz) hy (neg_add H hz)
    _ ≡[Γ] y := zero_add H hy

lemma add_right_cancel {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : F.add x z ≡[Γ] F.add y z) : x ≡[Γ] y :=
  add_left_cancel H hx hy hz
    (bv_trans (add_comm H hz hx) (bv_trans h (add_comm H hy hz)))

/-- Uniqueness of the additive inverse. -/
lemma neg_unique {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : F.add x y ≡[Γ] F.zero) : y ≡[Γ] F.neg x :=
  add_left_cancel H hy (neg_mem H hx) hx (bv_trans h (bv_symm (add_neg H hx)))

lemma neg_congr {x x' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hxx' : x ≡[Γ] x') :
    F.neg x ≡[Γ] F.neg x' :=
  neg_unique H (mem_congr' hxx' hx) (neg_mem H hx)
    (bv_trans (add_congr_left H (mem_congr' hxx' hx) (neg_mem H hx) (bv_symm hxx')) (add_neg H hx))

lemma neg_neg {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.neg (F.neg x) ≡[Γ] x :=
  bv_symm (neg_unique H (neg_mem H hx) hx (neg_add H hx))

lemma neg_zero : F.neg F.zero ≡[Γ] F.zero :=
  bv_symm (neg_unique H (cof_zero_mem H) (cof_zero_mem H) (add_zero H (cof_zero_mem H)))

lemma neg_add_rev {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    F.neg (F.add x y) ≡[Γ] F.add (F.neg x) (F.neg y) := by
  have hnx := neg_mem H hx
  have hny := neg_mem H hy
  refine bv_symm (neg_unique H (add_mem H hx hy) (add_mem H hnx hny) ?_)
  calc F.add (F.add x y) (F.add (F.neg x) (F.neg y))
      ≡[Γ] F.add (F.add y x) (F.add (F.neg x) (F.neg y)) :=
        add_congr_left H (add_mem H hx hy) (add_mem H hnx hny) (add_comm H hx hy)
    _ ≡[Γ] F.add y (F.add x (F.add (F.neg x) (F.neg y))) := add_assoc H hy hx (add_mem H hnx hny)
    _ ≡[Γ] F.add y (F.add (F.add x (F.neg x)) (F.neg y)) :=
        add_congr_right H hy (add_mem H hx (add_mem H hnx hny)) (bv_symm (add_assoc H hx hnx hny))
    _ ≡[Γ] F.add y (F.add F.zero (F.neg y)) :=
        add_congr_right H hy (add_mem H (add_mem H hx hnx) hny)
          (add_congr_left H (add_mem H hx hnx) hny (add_neg H hx))
    _ ≡[Γ] F.add y (F.neg y) := add_congr_right H hy (add_mem H (cof_zero_mem H) hny) (zero_add H hny)
    _ ≡[Γ] F.zero := add_neg H hy

/-- `(x + y) + (-y) = x`. -/
lemma add_neg_cancel_right {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    F.add (F.add x y) (F.neg y) ≡[Γ] x :=
  calc F.add (F.add x y) (F.neg y) ≡[Γ] F.add x (F.add y (F.neg y)) := add_assoc H hx hy (neg_mem H hy)
    _ ≡[Γ] F.add x F.zero := add_congr_right H hx (add_mem H hy (neg_mem H hy)) (add_neg H hy)
    _ ≡[Γ] x := add_zero H hx

/-- `(x + (-y)) + y = x`. -/
lemma add_neg_cancel_right' {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    F.add (F.add x (F.neg y)) y ≡[Γ] x :=
  calc F.add (F.add x (F.neg y)) y ≡[Γ] F.add x (F.add (F.neg y) y) := add_assoc H hx (neg_mem H hy) hy
    _ ≡[Γ] F.add x F.zero := add_congr_right H hx (add_mem H (neg_mem H hy) hy) (neg_add H hy)
    _ ≡[Γ] x := add_zero H hx

/-- Rearrangement `(a + b) + (c + d) = (a + c) + (b + d)`. -/
lemma add_add_add_comm {a b c d : bSet β} (ha : Γ ≤ a ∈ᴮ F.R) (hb : Γ ≤ b ∈ᴮ F.R)
    (hc : Γ ≤ c ∈ᴮ F.R) (hd : Γ ≤ d ∈ᴮ F.R) :
    F.add (F.add a b) (F.add c d) ≡[Γ] F.add (F.add a c) (F.add b d) := by
  calc F.add (F.add a b) (F.add c d) ≡[Γ] F.add a (F.add b (F.add c d)) :=
        add_assoc H ha hb (add_mem H hc hd)
    _ ≡[Γ] F.add a (F.add (F.add b c) d) :=
        add_congr_right H ha (add_mem H hb (add_mem H hc hd)) (bv_symm (add_assoc H hb hc hd))
    _ ≡[Γ] F.add a (F.add (F.add c b) d) :=
        add_congr_right H ha (add_mem H (add_mem H hb hc) hd)
          (add_congr_left H (add_mem H hb hc) hd (add_comm H hb hc))
    _ ≡[Γ] F.add a (F.add c (F.add b d)) :=
        add_congr_right H ha (add_mem H (add_mem H hc hb) hd) (add_assoc H hc hb hd)
    _ ≡[Γ] F.add (F.add a c) (F.add b d) := bv_symm (add_assoc H ha hc (add_mem H hb hd))

end add

/-! #### `≤` (no axioms needed) -/

lemma le_of_lt {x y : bSet β} (h : Γ ≤ F.lt x y) : Γ ≤ F.le x y := h.trans le_sup_left

lemma le_of_eq {x y : bSet β} (h : x ≡[Γ] y) : Γ ≤ F.le x y := h.trans le_sup_right

lemma le_refl' (x : bSet β) : Γ ≤ F.le x x := le_of_eq (F := F) bv_refl

lemma le_elim {x y : bSet β} {b : β} (h : Γ ≤ F.le x y)
    (H₁ : ∀ Γ' : β, Γ' ≤ Γ → Γ' ≤ F.lt x y → Γ' ≤ b)
    (H₂ : ∀ Γ' : β, Γ' ≤ Γ → (x ≡[Γ'] y) → Γ' ≤ b) : Γ ≤ b :=
  BV.or_elim h H₁ H₂

lemma le_congr {x x' y y' : bSet β} (hx : x ≡[Γ] x') (hy : y ≡[Γ] y') (h : Γ ≤ F.le x y) :
    Γ ≤ F.le x' y' :=
  le_elim h (fun Γ' (h' : Γ' ≤ Γ) hlt => le_of_lt (lt_congr (h'.trans hx) (h'.trans hy) hlt))
    fun Γ' (h' : Γ' ≤ Γ) heq =>
      le_of_eq (bv_trans (bv_symm (h'.trans hx)) (bv_trans heq (h'.trans hy)))

/-! #### Order -/

section order
variable (H : Γ ≤ F.COF)
include H

lemma lt_irrefl {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : Γ ≤ (F.lt x x)ᶜ := by
  have h := cof_irrefl H
  rw [Sem.irrefl] at h
  exact BV.mp (h.trans (iInf_le _ x)) hx

lemma lt_trans {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (hz : Γ ≤ z ∈ᴮ F.R)
    (h1 : Γ ≤ F.lt x y) (h2 : Γ ≤ F.lt y z) : Γ ≤ F.lt x z := by
  have h := cof_trans H
  rw [Sem.trans] at h
  have h' := BV.mp ((BV.mp ((BV.mp (h.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy).trans
    (iInf_le _ z)) hz
  exact BV.mp (BV.mp h' h1) h2

lemma lt_total {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ≤ F.lt x y ⊔ (x =ᴮ y ⊔ F.lt y x) := by
  have h := cof_total H
  rw [Sem.total] at h
  exact BV.mp ((BV.mp (h.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy

lemma lt_asymm {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (h1 : Γ ≤ F.lt x y) :
    Γ ≤ (F.lt y x)ᶜ := by
  refine BV.compl_of_inf_le_bot ?_
  have H' := cof_mono H (inf_le_left : Γ ⊓ F.lt y x ≤ Γ)
  exact BV.bot_of_compl
    (lt_trans H' (inf_le_left.trans hx) (inf_le_left.trans hy) (inf_le_left.trans hx)
      (inf_le_left.trans h1) inf_le_right)
    (lt_irrefl H' (inf_le_left.trans hx))

/-- `x < y → x ≠ y`. -/
lemma ne_of_lt {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h1 : Γ ≤ F.lt x y) : Γ ≤ (x =ᴮ y)ᶜ := by
  refine BV.compl_of_inf_le_bot ?_
  have H' := cof_mono H (inf_le_left : Γ ⊓ x =ᴮ y ≤ Γ)
  exact BV.bot_of_compl (lt_congr bv_refl (bv_symm inf_le_right) (inf_le_left.trans h1))
    (lt_irrefl H' (inf_le_left.trans hx))

lemma bot_of_lt_of_eq {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h1 : Γ ≤ F.lt x y) (h2 : x ≡[Γ] y) :
    Γ ≤ ⊥ :=
  BV.bot_of_compl h2 (ne_of_lt H hx h1)

lemma bot_of_lt_of_lt {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h1 : Γ ≤ F.lt x y) (h2 : Γ ≤ F.lt y x) : Γ ≤ ⊥ :=
  BV.bot_of_compl h2 (lt_asymm H hx hy h1)

lemma add_lt_add_right {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.lt x y) : Γ ≤ F.lt (F.add x z) (F.add y z) := by
  have hc := cof_addCompat H
  rw [Sem.addCompat] at hc
  have h' := BV.mp ((BV.mp ((BV.mp (hc.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy).trans
    (iInf_le _ z)) hz
  have h'' := h'.trans (iInf_le _ (F.add x z)) |>.trans (iInf_le _ (F.add y z))
  exact BV.mp (BV.mp (BV.mp h'' h) (add_app2 H hx hz)) (add_app2 H hy hz)

lemma add_lt_add_left {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.lt x y) : Γ ≤ F.lt (F.add z x) (F.add z y) :=
  lt_congr (add_comm H hx hz) (add_comm H hy hz) (add_lt_add_right H hx hy hz h)

lemma lt_of_add_lt_add_right {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.lt (F.add x z) (F.add y z)) : Γ ≤ F.lt x y := by
  have := add_lt_add_right H (add_mem H hx hz) (add_mem H hy hz) (neg_mem H hz) h
  exact lt_congr (add_neg_cancel_right H hx hz) (add_neg_cancel_right H hy hz) this

lemma lt_of_add_lt_add_left {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.lt (F.add z x) (F.add z y)) : Γ ≤ F.lt x y :=
  lt_of_add_lt_add_right H hx hy hz (lt_congr (add_comm H hz hx) (add_comm H hz hy) h)

lemma add_lt_add {a b c d : bSet β} (ha : Γ ≤ a ∈ᴮ F.R) (hb : Γ ≤ b ∈ᴮ F.R) (hc : Γ ≤ c ∈ᴮ F.R)
    (hd : Γ ≤ d ∈ᴮ F.R) (h1 : Γ ≤ F.lt a b) (h2 : Γ ≤ F.lt c d) :
    Γ ≤ F.lt (F.add a c) (F.add b d) :=
  lt_trans H (add_mem H ha hc) (add_mem H hb hc) (add_mem H hb hd)
    (add_lt_add_right H ha hb hc h1) (add_lt_add_left H hc hd hb h2)

lemma neg_lt_neg {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (h : Γ ≤ F.lt x y) :
    Γ ≤ F.lt (F.neg y) (F.neg x) := by
  have hnx := neg_mem H hx
  have hny := neg_mem H hy
  have h1 := add_lt_add_right H hx hy (add_mem H hnx hny) h
  refine lt_congr ?_ ?_ h1
  · calc F.add x (F.add (F.neg x) (F.neg y)) ≡[Γ] F.add (F.add x (F.neg x)) (F.neg y) :=
          bv_symm (add_assoc H hx hnx hny)
      _ ≡[Γ] F.add F.zero (F.neg y) := add_congr_left H (add_mem H hx hnx) hny (add_neg H hx)
      _ ≡[Γ] F.neg y := zero_add H hny
  · calc F.add y (F.add (F.neg x) (F.neg y)) ≡[Γ] F.add y (F.add (F.neg y) (F.neg x)) :=
          add_congr_right H hy (add_mem H hnx hny) (add_comm H hnx hny)
      _ ≡[Γ] F.add (F.add y (F.neg y)) (F.neg x) := bv_symm (add_assoc H hy hny hnx)
      _ ≡[Γ] F.add F.zero (F.neg x) := add_congr_left H (add_mem H hy hny) hnx (add_neg H hy)
      _ ≡[Γ] F.neg x := zero_add H hnx

lemma sub_pos_of_lt {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (h : Γ ≤ F.lt x y) :
    Γ ≤ F.lt F.zero (F.add y (F.neg x)) :=
  lt_congr (add_neg H hx) bv_refl (add_lt_add_right H hx hy (neg_mem H hx) h)

lemma lt_of_sub_pos {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : Γ ≤ F.lt F.zero (F.add y (F.neg x))) : Γ ≤ F.lt x y := by
  have := add_lt_add_right H (cof_zero_mem H) (add_mem H hy (neg_mem H hx)) hx h
  exact lt_congr (zero_add H hx) (add_neg_cancel_right' H hy hx) this

lemma neg_pos_of_neg {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h : Γ ≤ F.lt x F.zero) :
    Γ ≤ F.lt F.zero (F.neg x) :=
  lt_congr (neg_zero H) bv_refl (neg_lt_neg H hx (cof_zero_mem H) h)

lemma neg_neg_of_pos {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h : Γ ≤ F.lt F.zero x) :
    Γ ≤ F.lt (F.neg x) F.zero :=
  lt_congr bv_refl (neg_zero H) (neg_lt_neg H (cof_zero_mem H) hx h)

lemma lt_of_lt_of_le {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (hz : Γ ≤ z ∈ᴮ F.R)
    (h1 : Γ ≤ F.lt x y) (h2 : Γ ≤ F.le y z) : Γ ≤ F.lt x z :=
  le_elim h2
    (fun Γ' h' hlt => lt_trans (cof_mono H h') (h'.trans hx) (h'.trans hy) (h'.trans hz)
      (h'.trans h1) hlt)
    fun Γ' h' heq => lt_congr bv_refl heq (h'.trans h1)

lemma lt_of_le_of_lt {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (hz : Γ ≤ z ∈ᴮ F.R)
    (h1 : Γ ≤ F.le x y) (h2 : Γ ≤ F.lt y z) : Γ ≤ F.lt x z :=
  le_elim h1
    (fun Γ' h' hlt => lt_trans (cof_mono H h') (h'.trans hx) (h'.trans hy) (h'.trans hz)
      hlt (h'.trans h2))
    fun Γ' h' heq => lt_congr (bv_symm heq) bv_refl (h'.trans h2)

lemma le_trans' {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (hz : Γ ≤ z ∈ᴮ F.R)
    (h1 : Γ ≤ F.le x y) (h2 : Γ ≤ F.le y z) : Γ ≤ F.le x z :=
  le_elim h1
    (fun Γ' h' hlt => le_of_lt (lt_of_lt_of_le (cof_mono H h') (h'.trans hx) (h'.trans hy)
      (h'.trans hz) hlt (h'.trans h2)))
    fun Γ' h' heq => le_congr (bv_symm heq) bv_refl (h'.trans h2)

lemma le_of_not_lt {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : Γ ≤ (F.lt y x)ᶜ) : Γ ≤ F.le x y := by
  refine BV.or_elim (lt_total H hx hy) (fun Γ' h' hlt => le_of_lt hlt) fun Γ' h' h2 => ?_
  refine BV.or_elim h2 (fun Γ'' h'' heq => le_of_eq heq) fun Γ'' h'' hlt => ?_
  exact BV.of_bot (BV.bot_of_compl hlt ((h''.trans h').trans h))

lemma not_lt_of_le {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : Γ ≤ F.le x y) : Γ ≤ (F.lt y x)ᶜ := by
  refine BV.compl_of_inf_le_bot ?_
  have H' := cof_mono H (inf_le_left : Γ ⊓ F.lt y x ≤ Γ)
  have h1 : Γ ⊓ F.lt y x ≤ F.lt y y :=
    lt_of_lt_of_le H' (inf_le_left.trans hy) (inf_le_left.trans hx) (inf_le_left.trans hy)
      inf_le_right (inf_le_left.trans h)
  exact BV.bot_of_compl h1 (lt_irrefl H' (inf_le_left.trans hy))

lemma le_of_lt_or_le {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : Γ ≤ (F.lt y x)ᶜ) : Γ ≤ F.le x y := le_of_not_lt H hx hy h

lemma add_le_add_right {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.le x y) : Γ ≤ F.le (F.add x z) (F.add y z) :=
  le_elim h
    (fun Γ' h' hlt => le_of_lt (add_lt_add_right (cof_mono H h') (h'.trans hx) (h'.trans hy)
      (h'.trans hz) hlt))
    fun Γ' h' heq => le_of_eq (add_congr_left (cof_mono H h') (h'.trans hx) (h'.trans hz) heq)

lemma add_le_add_left {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.le x y) : Γ ≤ F.le (F.add z x) (F.add z y) :=
  le_congr (add_comm H hx hz) (add_comm H hy hz) (add_le_add_right H hx hy hz h)

lemma le_of_add_le_add_right {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ z ∈ᴮ F.R) (h : Γ ≤ F.le (F.add x z) (F.add y z)) : Γ ≤ F.le x y := by
  have := add_le_add_right H (add_mem H hx hz) (add_mem H hy hz) (neg_mem H hz) h
  exact le_congr (add_neg_cancel_right H hx hz) (add_neg_cancel_right H hy hz) this

/-- `x + z < y + z'` from `x < y` and `z ≤ z'`. -/
lemma add_lt_add_of_lt_of_le {a b c d : bSet β} (ha : Γ ≤ a ∈ᴮ F.R) (hb : Γ ≤ b ∈ᴮ F.R)
    (hc : Γ ≤ c ∈ᴮ F.R) (hd : Γ ≤ d ∈ᴮ F.R) (h1 : Γ ≤ F.lt a b) (h2 : Γ ≤ F.le c d) :
    Γ ≤ F.lt (F.add a c) (F.add b d) :=
  lt_of_lt_of_le H (add_mem H ha hc) (add_mem H hb hc) (add_mem H hb hd)
    (add_lt_add_right H ha hb hc h1) (add_le_add_left H hc hd hb h2)

lemma add_lt_add_of_le_of_lt {a b c d : bSet β} (ha : Γ ≤ a ∈ᴮ F.R) (hb : Γ ≤ b ∈ᴮ F.R)
    (hc : Γ ≤ c ∈ᴮ F.R) (hd : Γ ≤ d ∈ᴮ F.R) (h1 : Γ ≤ F.le a b) (h2 : Γ ≤ F.lt c d) :
    Γ ≤ F.lt (F.add a c) (F.add b d) :=
  lt_of_le_of_lt H (add_mem H ha hc) (add_mem H hb hc) (add_mem H hb hd)
    (add_le_add_right H ha hb hc h1) (add_lt_add_left H hc hd hb h2)

end order

/-! #### Multiplication (only what is needed: `0 < 1` and halving) -/

section mul
variable (H : Γ ≤ F.COF)
include H

lemma mul_mem {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) : Γ ≤ F.mul x y ∈ᴮ F.R :=
  opN_mem (cof_isOp2_times H) hx hy

lemma mul_app2 {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    Γ ≤ Sem.app2 F.times x y (F.mul x y) :=
  opN_app2 (cof_isOp2_times H) hx hy

lemma mul_unique {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hz : Γ ≤ Sem.app2 F.times x y z) : z ≡[Γ] F.mul x y :=
  opN_unique (cof_isOp2_times H) hx hy hz

lemma mul_congr {x x' y y' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (hxx' : x ≡[Γ] x') (hyy' : y ≡[Γ] y') : F.mul x y ≡[Γ] F.mul x' y' :=
  opN_congr (cof_isOp2_times H) hx hy hxx' hyy'

lemma mul_comm {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    F.mul x y ≡[Γ] F.mul y x := by
  have h := cof_mul_comm H
  rw [Sem.comm] at h
  have h1 := BV.mp ((BV.mp (h.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy
  exact mul_unique H hy hx (BV.mp (h1.trans (iInf_le _ (F.mul x y))) (mul_app2 H hx hy))

lemma mul_one {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.mul x F.one ≡[Γ] x := by
  have h := cof_mul_ident H
  rw [Sem.ident] at h
  exact bv_symm (mul_unique H hx (cof_one_mem H) (BV.mp (h.trans (iInf_le _ x)) hx))

lemma one_mul {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.mul F.one x ≡[Γ] x :=
  bv_trans (mul_comm H (cof_one_mem H) hx) (mul_one H hx)

/-- `x · (y + z) = x · y + x · z`. -/
lemma mul_add {x y z : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (hz : Γ ≤ z ∈ᴮ F.R) :
    F.mul x (F.add y z) ≡[Γ] F.add (F.mul x y) (F.mul x z) := by
  have h := cof_distrib H
  rw [Sem.distrib] at h
  have h1 := BV.mp ((BV.mp ((BV.mp (h.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy).trans
    (iInf_le _ z)) hz
  have h2 := h1.trans (iInf_le _ (F.add y z)) |>.trans (iInf_le _ (F.mul x (F.add y z)))
    |>.trans (iInf_le _ (F.mul x y)) |>.trans (iInf_le _ (F.mul x z))
    |>.trans (iInf_le _ (F.add (F.mul x y) (F.mul x z)))
  exact BV.mp (BV.mp (BV.mp (BV.mp (BV.mp h2 (add_app2 H hy hz))
    (mul_app2 H hx (add_mem H hy hz))) (mul_app2 H hx hy)) (mul_app2 H hx hz))
    (add_app2 H (mul_mem H hx hy) (mul_mem H hx hz))

lemma mul_zero {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.mul x F.zero ≡[Γ] F.zero := by
  have h0 := cof_zero_mem H
  have hm := mul_mem H hx h0
  have e : F.add (F.mul x F.zero) F.zero ≡[Γ] F.add (F.mul x F.zero) (F.mul x F.zero) :=
    calc F.add (F.mul x F.zero) F.zero ≡[Γ] F.mul x F.zero := add_zero H hm
      _ ≡[Γ] F.mul x (F.add F.zero F.zero) := mul_congr H hx h0 bv_refl (bv_symm (add_zero H h0))
      _ ≡[Γ] F.add (F.mul x F.zero) (F.mul x F.zero) := mul_add H hx h0 h0
  exact bv_symm (add_left_cancel H h0 hm hm e)

lemma inv_mem_and_app2 {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hne : Γ ≤ (x =ᴮ F.zero)ᶜ) :
    Γ ≤ F.inv x ∈ᴮ F.R ⊓ Sem.app2 F.times x (F.inv x) F.one := by
  rw [← inv_spec]
  have h := cof_mulInv H
  rw [Sem.mulInv] at h
  exact BV.mp (BV.mp (h.trans (iInf_le _ x)) hx) hne

lemma inv_mem {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hne : Γ ≤ (x =ᴮ F.zero)ᶜ) :
    Γ ≤ F.inv x ∈ᴮ F.R :=
  bv_and_left (inv_mem_and_app2 H hx hne)

lemma mul_inv {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hne : Γ ≤ (x =ᴮ F.zero)ᶜ) :
    F.mul x (F.inv x) ≡[Γ] F.one :=
  bv_symm (mul_unique H hx (inv_mem H hx hne) (bv_and_right (inv_mem_and_app2 H hx hne)))

lemma mul_pos {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) (h1 : Γ ≤ F.lt F.zero x)
    (h2 : Γ ≤ F.lt F.zero y) : Γ ≤ F.lt F.zero (F.mul x y) := by
  have h := cof_mulPos H
  rw [Sem.mulPos] at h
  have h' := (BV.mp ((BV.mp (h.trans (iInf_le _ x)) hx).trans (iInf_le _ y)) hy).trans
    (iInf_le _ (F.mul x y))
  exact BV.mp (BV.mp (BV.mp h' h1) h2) (mul_app2 H hx hy)

/-- **`0 < 1`.** -/
lemma zero_lt_one : Γ ≤ F.lt F.zero F.one := by
  have h0 := cof_zero_mem H
  have h1 := cof_one_mem H
  refine BV.or_elim (lt_total H h0 h1) (fun Γ' _ h => h) fun Γ' h' h => ?_
  refine BV.or_elim h
    (fun Γ'' h'' heq => BV.of_bot (BV.bot_of_compl heq ((h''.trans h').trans (cof_zero_ne_one H))))
    fun Γ'' h'' hlt => ?_
  have hΓ : Γ'' ≤ Γ := h''.trans h'
  have H'' := cof_mono H hΓ
  have h0'' := hΓ.trans h0
  have h1'' := hΓ.trans h1
  have hn1 := neg_mem H'' h1''
  -- `0 < -1`
  have hneg : Γ'' ≤ F.lt F.zero (F.neg F.one) :=
    lt_congr (add_neg H'' h1'') (zero_add H'' hn1) (add_lt_add_right H'' h1'' h0'' hn1 hlt)
  -- `(-1)(-1) = 1`
  have hsq : F.mul (F.neg F.one) (F.neg F.one) ≡[Γ''] F.one := by
    have e1 : F.add (F.mul (F.neg F.one) (F.neg F.one)) (F.neg F.one) ≡[Γ''] F.zero :=
      calc F.add (F.mul (F.neg F.one) (F.neg F.one)) (F.neg F.one)
          ≡[Γ''] F.add (F.mul (F.neg F.one) (F.neg F.one)) (F.mul (F.neg F.one) F.one) :=
            add_congr_right H'' (mul_mem H'' hn1 hn1) hn1 (bv_symm (mul_one H'' hn1))
        _ ≡[Γ''] F.mul (F.neg F.one) (F.add (F.neg F.one) F.one) := bv_symm (mul_add H'' hn1 hn1 h1'')
        _ ≡[Γ''] F.mul (F.neg F.one) F.zero := mul_congr H'' hn1 (add_mem H'' hn1 h1'') bv_refl (neg_add H'' h1'')
        _ ≡[Γ''] F.zero := mul_zero H'' hn1
    have e2 : F.neg F.one ≡[Γ''] F.neg (F.mul (F.neg F.one) (F.neg F.one)) :=
      neg_unique H'' (mul_mem H'' hn1 hn1) hn1 e1
    calc F.mul (F.neg F.one) (F.neg F.one)
        ≡[Γ''] F.neg (F.neg (F.mul (F.neg F.one) (F.neg F.one))) := bv_symm (neg_neg H'' (mul_mem H'' hn1 hn1))
      _ ≡[Γ''] F.neg (F.neg F.one) := neg_congr H'' (neg_mem H'' (mul_mem H'' hn1 hn1)) (bv_symm e2)
      _ ≡[Γ''] F.one := neg_neg H'' h1''
  have hpos : Γ'' ≤ F.lt F.zero F.one := lt_congr bv_refl hsq (mul_pos H'' hn1 hn1 hneg hneg)
  exact BV.of_bot (bot_of_lt_of_lt H'' h0'' h1'' hpos hlt)

/-- `2 = 1 + 1`. -/
noncomputable def two (F : Fld β) : bSet β := F.add F.one F.one

omit H in
lemma two_def : F.two = F.add F.one F.one := rfl

lemma two_mem : Γ ≤ F.two ∈ᴮ F.R := add_mem H (cof_one_mem H) (cof_one_mem H)

lemma zero_lt_two : Γ ≤ F.lt F.zero F.two := by
  have h0 := cof_zero_mem H
  have h1 := cof_one_mem H
  have := add_lt_add_right H h0 h1 h1 (zero_lt_one H)
  exact lt_trans H h0 h1 (two_mem H) (zero_lt_one H) (lt_congr (zero_add H h1) bv_refl this)

lemma two_ne_zero : Γ ≤ (F.two =ᴮ F.zero)ᶜ := by
  refine BV.compl_of_inf_le_bot ?_
  have H' := cof_mono H (inf_le_left : Γ ⊓ F.two =ᴮ F.zero ≤ Γ)
  exact bot_of_lt_of_eq H' (inf_le_left.trans (cof_zero_mem H))
    (inf_le_left.trans (zero_lt_two H)) (bv_symm inf_le_right)

/-- `x / 2 = x · 2⁻¹`. -/
noncomputable def half (F : Fld β) (x : bSet β) : bSet β := F.mul x (F.inv F.two)

lemma inv_two_mem : Γ ≤ F.inv F.two ∈ᴮ F.R := inv_mem H (two_mem H) (two_ne_zero H)

lemma half_mem {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : Γ ≤ F.half x ∈ᴮ F.R :=
  mul_mem H hx (inv_two_mem H)

lemma inv_two_add_inv_two : F.add (F.inv F.two) (F.inv F.two) ≡[Γ] F.one := by
  have hi := inv_two_mem H
  have h1 := cof_one_mem H
  calc F.add (F.inv F.two) (F.inv F.two)
      ≡[Γ] F.add (F.mul (F.inv F.two) F.one) (F.mul (F.inv F.two) F.one) :=
        add_congr H hi hi (bv_symm (mul_one H hi)) (bv_symm (mul_one H hi))
    _ ≡[Γ] F.mul (F.inv F.two) (F.add F.one F.one) := bv_symm (mul_add H hi h1 h1)
    _ ≡[Γ] F.mul F.two (F.inv F.two) := mul_comm H hi (two_mem H)
    _ ≡[Γ] F.one := mul_inv H (two_mem H) (two_ne_zero H)

/-- `x/2 + x/2 = x`. -/
lemma half_add_half {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.add (F.half x) (F.half x) ≡[Γ] x := by
  have hi := inv_two_mem H
  calc F.add (F.half x) (F.half x) ≡[Γ] F.mul x (F.add (F.inv F.two) (F.inv F.two)) :=
        bv_symm (mul_add H hx hi hi)
    _ ≡[Γ] F.mul x F.one := mul_congr H hx (add_mem H hi hi) bv_refl (inv_two_add_inv_two H)
    _ ≡[Γ] x := mul_one H hx

lemma half_congr {x x' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hxx' : x ≡[Γ] x') :
    F.half x ≡[Γ] F.half x' :=
  mul_congr H hx (inv_two_mem H) hxx' bv_refl

/-- If `y + y > 0` then `y > 0`. -/
lemma pos_of_add_self_pos {y : bSet β} (hy : Γ ≤ y ∈ᴮ F.R) (h : Γ ≤ F.lt F.zero (F.add y y)) :
    Γ ≤ F.lt F.zero y := by
  have h0 := cof_zero_mem H
  refine BV.or_elim (lt_total H h0 hy) (fun Γ' _ h => h) fun Γ' h' h2 => ?_
  refine BV.or_elim h2 (fun Γ'' h'' heq => ?_) fun Γ'' h'' hlt => ?_
  · -- `y = 0`, so `y + y = 0`
    have hΓ : Γ'' ≤ Γ := h''.trans h'
    have H'' := cof_mono H hΓ
    have e : F.add y y ≡[Γ''] F.zero :=
      bv_trans (add_congr H'' (hΓ.trans hy) (hΓ.trans hy) (bv_symm heq) (bv_symm heq))
        (add_zero H'' (hΓ.trans h0))
    exact BV.of_bot (bot_of_lt_of_eq H'' (hΓ.trans h0) (hΓ.trans h) (bv_symm e))
  · -- `y < 0`, so `y + y < 0`
    have hΓ : Γ'' ≤ Γ := h''.trans h'
    have H'' := cof_mono H hΓ
    have hy'' := hΓ.trans hy
    have h0'' := hΓ.trans h0
    have h3 : Γ'' ≤ F.lt (F.add y y) F.zero :=
      lt_congr bv_refl (add_zero H'' h0'') (add_lt_add H'' hy'' h0'' hy'' h0'' hlt hlt)
    exact BV.of_bot (bot_of_lt_of_lt H'' h0'' (add_mem H'' hy'' hy'') (hΓ.trans h) h3)

lemma half_pos {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h : Γ ≤ F.lt F.zero x) :
    Γ ≤ F.lt F.zero (F.half x) :=
  pos_of_add_self_pos H (half_mem H hx) (lt_congr bv_refl (bv_symm (half_add_half H hx)) h)

end mul

/-! #### Internal naturals, halves and dyadics -/

/-- `n · x = x + ⋯ + x` (`n` times). -/
noncomputable def mulN (F : Fld β) : ℕ → bSet β → bSet β
  | 0, _ => F.zero
  | n + 1, x => F.add (F.mulN n x) x

/-- `hR k = 1 / 2^k`. -/
noncomputable def hR (F : Fld β) : ℕ → bSet β
  | 0 => F.one
  | k + 1 => F.half (F.hR k)

/-- `dyR' a b k = (a - b) / 2^k` for naturals `a b`. -/
noncomputable def dyR' (F : Fld β) (a b k : ℕ) : bSet β :=
  F.add (F.mulN a (F.hR k)) (F.neg (F.mulN b (F.hR k)))

/-- The dyadic `dyR m k = m / 2^k` (`m : ℤ`). -/
noncomputable def dyR (F : Fld β) (m : ℤ) (k : ℕ) : bSet β := F.dyR' m.toNat (-m).toNat k

@[simp] lemma mulN_zero (x : bSet β) : F.mulN 0 x = F.zero := rfl
@[simp] lemma mulN_succ (n : ℕ) (x : bSet β) : F.mulN (n + 1) x = F.add (F.mulN n x) x := rfl
@[simp] lemma hR_zero : F.hR 0 = F.one := rfl
@[simp] lemma hR_succ (k : ℕ) : F.hR (k + 1) = F.half (F.hR k) := rfl
lemma dyR_def (m : ℤ) (k : ℕ) : F.dyR m k = F.dyR' m.toNat (-m).toNat k := rfl

/-- The name of a sequence `{f n | n ∈ ℕ}` (all Boolean values `⊤`). -/
def seqName (f : ℕ → bSet β) : bSet β := ⟨ℕ, f, fun _ => ⊤⟩

lemma mem_seqName (f : ℕ → bSet β) (x : bSet β) : (x ∈ᴮ seqName f) = ⨆ n, x =ᴮ f n := by
  rw [mem_unfold]
  show (⨆ i : ℕ, ⊤ ⊓ x =ᴮ f i) = _
  simp only [top_inf_eq]

lemma seqName_mem (f : ℕ → bSet β) (n : ℕ) : Γ ≤ f n ∈ᴮ seqName f := by
  rw [mem_seqName]; exact le_iSup_of_le n bv_refl

section nat
variable (H : Γ ≤ F.COF)
include H

lemma mulN_mem {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : ∀ n, Γ ≤ F.mulN n x ∈ᴮ F.R
  | 0 => cof_zero_mem H
  | n + 1 => add_mem H (mulN_mem hx n) hx

lemma mulN_congr {x x' : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hxx' : x ≡[Γ] x') :
    ∀ n, F.mulN n x ≡[Γ] F.mulN n x'
  | 0 => bv_refl
  | n + 1 => add_congr H (mulN_mem H hx n) hx (mulN_congr hx hxx' n) hxx'

lemma mulN_one_apply {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) : F.mulN 1 x ≡[Γ] x := zero_add H hx

lemma mulN_add {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (a : ℕ) :
    ∀ b, F.mulN (a + b) x ≡[Γ] F.add (F.mulN a x) (F.mulN b x)
  | 0 => bv_symm (add_zero H (mulN_mem H hx a))
  | b + 1 => by
      show F.add (F.mulN (a + b) x) x ≡[Γ] F.add (F.mulN a x) (F.add (F.mulN b x) x)
      calc F.add (F.mulN (a + b) x) x ≡[Γ] F.add (F.add (F.mulN a x) (F.mulN b x)) x :=
            add_congr_left H (mulN_mem H hx _) hx (mulN_add hx a b)
        _ ≡[Γ] F.add (F.mulN a x) (F.add (F.mulN b x) x) :=
            add_assoc H (mulN_mem H hx a) (mulN_mem H hx b) hx

lemma mulN_add_apply {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R) :
    ∀ n, F.mulN n (F.add x y) ≡[Γ] F.add (F.mulN n x) (F.mulN n y)
  | 0 => bv_symm (add_zero H (cof_zero_mem H))
  | n + 1 => by
      show F.add (F.mulN n (F.add x y)) (F.add x y) ≡[Γ] F.add (F.add (F.mulN n x) x) (F.add (F.mulN n y) y)
      calc F.add (F.mulN n (F.add x y)) (F.add x y)
          ≡[Γ] F.add (F.add (F.mulN n x) (F.mulN n y)) (F.add x y) :=
            add_congr_left H (mulN_mem H (add_mem H hx hy) n) (add_mem H hx hy) (mulN_add_apply hx hy n)
        _ ≡[Γ] F.add (F.add (F.mulN n x) x) (F.add (F.mulN n y) y) :=
            add_add_add_comm H (mulN_mem H hx n) (mulN_mem H hy n) hx hy

lemma mulN_double {y : bSet β} (hy : Γ ≤ y ∈ᴮ F.R) :
    ∀ n, F.mulN (2 * n) y ≡[Γ] F.mulN n (F.add y y)
  | 0 => bv_refl
  | n + 1 => by
      show F.add (F.add (F.mulN (2 * n) y) y) y ≡[Γ] F.add (F.mulN n (F.add y y)) (F.add y y)
      calc F.add (F.add (F.mulN (2 * n) y) y) y ≡[Γ] F.add (F.mulN (2 * n) y) (F.add y y) :=
            add_assoc H (mulN_mem H hy _) hy hy
        _ ≡[Γ] F.add (F.mulN n (F.add y y)) (F.add y y) :=
            add_congr_left H (mulN_mem H hy _) (add_mem H hy hy) (mulN_double hy n)

lemma mulN_pos {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h : Γ ≤ F.lt F.zero x) :
    ∀ n, 0 < n → Γ ≤ F.lt F.zero (F.mulN n x)
  | 0, h0 => absurd h0 (Nat.lt_irrefl 0)
  | 1, _ => lt_congr bv_refl (bv_symm (mulN_one_apply H hx)) h
  | n + 2, _ => by
      have h1 := mulN_pos hx h (n + 1) n.succ_pos
      have := add_lt_add H (cof_zero_mem H) (mulN_mem H hx (n+1)) (cof_zero_mem H) hx h1 h
      exact lt_congr (add_zero H (cof_zero_mem H)) bv_refl this

lemma mulN_lt_mulN_left {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h : Γ ≤ F.lt F.zero x) {a b : ℕ}
    (hab : a < b) : Γ ≤ F.lt (F.mulN a x) (F.mulN b x) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + (c + 1) := ⟨b - a - 1, by omega⟩
  have h1 := mulN_pos H hx h (c + 1) c.succ_pos
  have h2 := add_lt_add_left H (cof_zero_mem H) (mulN_mem H hx (c+1)) (mulN_mem H hx a) h1
  exact lt_congr (add_zero H (mulN_mem H hx a)) (bv_symm (mulN_add H hx a (c+1))) h2

lemma mulN_le_mulN_left {x : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (h : Γ ≤ F.lt F.zero x) {a b : ℕ}
    (hab : a ≤ b) : Γ ≤ F.le (F.mulN a x) (F.mulN b x) := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact le_of_lt (mulN_lt_mulN_left H hx h hlt)
  · exact le_refl' _

lemma mulN_lt_mulN_right {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : Γ ≤ F.lt x y) : ∀ n, 0 < n → Γ ≤ F.lt (F.mulN n x) (F.mulN n y)
  | 0, h0 => absurd h0 (Nat.lt_irrefl 0)
  | 1, _ => lt_congr (bv_symm (mulN_one_apply H hx)) (bv_symm (mulN_one_apply H hy)) h
  | n + 2, _ =>
      add_lt_add H (mulN_mem H hx (n+1)) (mulN_mem H hy (n+1)) hx hy
        (mulN_lt_mulN_right hx hy h (n + 1) n.succ_pos) h

lemma mulN_le_mulN_right {x y : bSet β} (hx : Γ ≤ x ∈ᴮ F.R) (hy : Γ ≤ y ∈ᴮ F.R)
    (h : Γ ≤ F.le x y) : ∀ n, Γ ≤ F.le (F.mulN n x) (F.mulN n y)
  | 0 => le_refl' _
  | n + 1 =>
      le_elim (mulN_le_mulN_right hx hy h n)
        (fun Γ' h' hlt => le_of_lt (add_lt_add_of_lt_of_le (cof_mono H h')
          (h'.trans (mulN_mem H hx n)) (h'.trans (mulN_mem H hy n)) (h'.trans hx) (h'.trans hy)
          hlt (h'.trans h)))
        fun Γ' h' heq =>
          add_le_add_left (cof_mono H h') (h'.trans hx) (h'.trans hy) (h'.trans (mulN_mem H hy n))
            (h'.trans h) |> le_congr (add_congr_left (cof_mono H h') (h'.trans (mulN_mem H hy n))
              (h'.trans hx) (bv_symm heq)) bv_refl

lemma hR_mem : ∀ k, Γ ≤ F.hR k ∈ᴮ F.R
  | 0 => cof_one_mem H
  | k + 1 => half_mem H (hR_mem k)

lemma hR_pos : ∀ k, Γ ≤ F.lt F.zero (F.hR k)
  | 0 => zero_lt_one H
  | k + 1 => half_pos H (hR_mem H k) (hR_pos k)

lemma hR_succ_add (k : ℕ) : F.add (F.hR (k + 1)) (F.hR (k + 1)) ≡[Γ] F.hR k :=
  half_add_half H (hR_mem H k)

lemma mulN_pow_hR : ∀ k, F.mulN (2 ^ k) (F.hR k) ≡[Γ] F.one
  | 0 => zero_add H (cof_one_mem H)
  | k + 1 => by
      rw [pow_succ']
      calc F.mulN (2 * 2 ^ k) (F.hR (k + 1)) ≡[Γ] F.mulN (2 ^ k) (F.add (F.hR (k+1)) (F.hR (k+1))) :=
            mulN_double H (hR_mem H (k+1)) _
        _ ≡[Γ] F.mulN (2 ^ k) (F.hR k) := mulN_congr H (add_mem H (hR_mem H _) (hR_mem H _)) (hR_succ_add H k) _
        _ ≡[Γ] F.one := mulN_pow_hR k

/-! dyadics -/

lemma dyR'_mem (a b k : ℕ) : Γ ≤ F.dyR' a b k ∈ᴮ F.R :=
  add_mem H (mulN_mem H (hR_mem H k) a) (neg_mem H (mulN_mem H (hR_mem H k) b))

lemma dyR_mem (m : ℤ) (k : ℕ) : Γ ≤ F.dyR m k ∈ᴮ F.R := dyR'_mem H _ _ k

lemma dyR'_add (a b a' b' k : ℕ) :
    F.add (F.dyR' a b k) (F.dyR' a' b' k) ≡[Γ] F.dyR' (a + a') (b + b') k := by
  have hh := hR_mem H k
  have hA := mulN_mem H hh a; have hB := mulN_mem H hh b
  have hA' := mulN_mem H hh a'; have hB' := mulN_mem H hh b'
  calc F.add (F.dyR' a b k) (F.dyR' a' b' k)
      ≡[Γ] F.add (F.add (F.mulN a (F.hR k)) (F.mulN a' (F.hR k)))
        (F.add (F.neg (F.mulN b (F.hR k))) (F.neg (F.mulN b' (F.hR k)))) :=
        add_add_add_comm H hA (neg_mem H hB) hA' (neg_mem H hB')
    _ ≡[Γ] F.add (F.mulN (a + a') (F.hR k)) (F.neg (F.mulN (b + b') (F.hR k))) :=
        add_congr H (add_mem H hA hA') (add_mem H (neg_mem H hB) (neg_mem H hB'))
          (bv_symm (mulN_add H hh a a'))
          (bv_trans (bv_symm (neg_add_rev H hB hB'))
            (neg_congr H (add_mem H hB hB') (bv_symm (mulN_add H hh b b'))))

lemma dyR'_congr {a b a' b' : ℕ} (k : ℕ) (h : a + b' = a' + b) :
    F.dyR' a b k ≡[Γ] F.dyR' a' b' k := by
  have hh := hR_mem H k
  have hA := mulN_mem H hh a; have hB := mulN_mem H hh b
  have hA' := mulN_mem H hh a'; have hB' := mulN_mem H hh b'
  have e : F.add (F.mulN a (F.hR k)) (F.mulN b' (F.hR k)) ≡[Γ]
      F.add (F.mulN a' (F.hR k)) (F.mulN b (F.hR k)) :=
    bv_trans (bv_symm (mulN_add H hh a b')) (bv_trans (by rw [h]; exact bv_refl) (mulN_add H hh a' b))
  calc F.dyR' a b k ≡[Γ] F.add (F.dyR' a b k) F.zero := bv_symm (add_zero H (dyR'_mem H a b k))
    _ ≡[Γ] F.add (F.dyR' a b k) (F.add (F.mulN b' (F.hR k)) (F.neg (F.mulN b' (F.hR k)))) :=
        add_congr_right H (dyR'_mem H a b k) (cof_zero_mem H) (bv_symm (add_neg H hB'))
    _ ≡[Γ] F.add (F.add (F.mulN a (F.hR k)) (F.mulN b' (F.hR k)))
        (F.add (F.neg (F.mulN b (F.hR k))) (F.neg (F.mulN b' (F.hR k)))) :=
        add_add_add_comm H hA (neg_mem H hB) hB' (neg_mem H hB')
    _ ≡[Γ] F.add (F.add (F.mulN a' (F.hR k)) (F.mulN b (F.hR k)))
        (F.add (F.neg (F.mulN b' (F.hR k))) (F.neg (F.mulN b (F.hR k)))) :=
        add_congr H (add_mem H hA hB') (add_mem H (neg_mem H hB) (neg_mem H hB')) e
          (add_comm H (neg_mem H hB) (neg_mem H hB'))
    _ ≡[Γ] F.add (F.add (F.mulN a' (F.hR k)) (F.neg (F.mulN b' (F.hR k))))
        (F.add (F.mulN b (F.hR k)) (F.neg (F.mulN b (F.hR k)))) :=
        add_add_add_comm H hA' hB (neg_mem H hB') (neg_mem H hB)
    _ ≡[Γ] F.add (F.dyR' a' b' k) F.zero :=
        add_congr_right H (dyR'_mem H a' b' k) (add_mem H hB (neg_mem H hB)) (add_neg H hB)
    _ ≡[Γ] F.dyR' a' b' k := add_zero H (dyR'_mem H a' b' k)

lemma dyR'_double (a b k : ℕ) : F.dyR' a b k ≡[Γ] F.dyR' (2 * a) (2 * b) (k + 1) := by
  have hh := hR_mem H k
  have hh1 := hR_mem H (k + 1)
  have e : ∀ c, F.mulN c (F.hR k) ≡[Γ] F.mulN (2 * c) (F.hR (k + 1)) := fun c =>
    bv_trans (mulN_congr H hh (bv_symm (hR_succ_add H k)) c) (bv_symm (mulN_double H hh1 c))
  exact add_congr H (mulN_mem H hh a) (neg_mem H (mulN_mem H hh b)) (e a)
    (neg_congr H (mulN_mem H hh b) (e b))

lemma dyR'_pos {a : ℕ} (ha : 0 < a) (k : ℕ) : Γ ≤ F.lt F.zero (F.dyR' a 0 k) := by
  have hh := hR_mem H k
  have e : F.dyR' a 0 k ≡[Γ] F.mulN a (F.hR k) :=
    calc F.dyR' a 0 k ≡[Γ] F.add (F.mulN a (F.hR k)) F.zero :=
          add_congr_right H (mulN_mem H hh a) (neg_mem H (cof_zero_mem H)) (neg_zero H)
      _ ≡[Γ] F.mulN a (F.hR k) := add_zero H (mulN_mem H hh a)
  exact lt_congr bv_refl (bv_symm e) (mulN_pos H hh (hR_pos H k) a ha)

lemma dyR_add (m m' : ℤ) (k : ℕ) : F.add (F.dyR m k) (F.dyR m' k) ≡[Γ] F.dyR (m + m') k := by
  rw [dyR_def, dyR_def, dyR_def]
  refine bv_trans (dyR'_add H _ _ _ _ k) (dyR'_congr H k ?_)
  omega

lemma dyR_pos {m : ℤ} (hm : 0 < m) (k : ℕ) : Γ ≤ F.lt F.zero (F.dyR m k) := by
  rw [dyR_def, show (-m).toNat = 0 by omega]
  exact dyR'_pos H (by omega) k

lemma dyR_lt {m m' : ℤ} (h : m < m') (k : ℕ) : Γ ≤ F.lt (F.dyR m k) (F.dyR m' k) := by
  have h1 := dyR_pos H (sub_pos.mpr h) k
  have h2 := add_lt_add_left H (cof_zero_mem H) (dyR_mem H (m' - m) k) (dyR_mem H m k) h1
  refine lt_congr (add_zero H (dyR_mem H m k)) ?_ h2
  have := dyR_add H m (m' - m) k
  rwa [show m + (m' - m) = m' by omega] at this

lemma dyR_le {m m' : ℤ} (h : m ≤ m') (k : ℕ) : Γ ≤ F.le (F.dyR m k) (F.dyR m' k) := by
  rcases h.lt_or_eq with hlt | rfl
  · exact le_of_lt (dyR_lt H hlt k)
  · exact le_refl' _

lemma dyR_double (m : ℤ) (k : ℕ) : F.dyR m k ≡[Γ] F.dyR (2 * m) (k + 1) := by
  rw [dyR_def, dyR_def]
  refine bv_trans (dyR'_double H _ _ k) (dyR'_congr H (k+1) ?_)
  omega

lemma dyR_double_iter (m : ℤ) (k : ℕ) : ∀ j, F.dyR m k ≡[Γ] F.dyR (m * 2 ^ j) (k + j)
  | 0 => by simp only [pow_zero, _root_.mul_one, Nat.add_zero]; exact bv_refl
  | j + 1 => by
      refine bv_trans (dyR_double_iter m k j) ?_
      rw [show m * 2 ^ (j + 1) = 2 * (m * 2 ^ j) by
          rw [pow_succ, ← _root_.mul_assoc, _root_.mul_comm],
        show k + (j + 1) = (k + j) + 1 from rfl]
      exact dyR_double H _ _

/-- Comparison of dyadics with different denominators, in terms of the cross-multiplied
numerators. -/
lemma dyR_lt_of_cross {m m' : ℤ} {k k' : ℕ} (h : m * 2 ^ k' < m' * 2 ^ k) :
    Γ ≤ F.lt (F.dyR m k) (F.dyR m' k') := by
  have e1 := dyR_double_iter H m k k'
  have e2 := dyR_double_iter H m' k' k
  rw [Nat.add_comm k' k] at e2
  exact lt_congr (bv_symm e1) (bv_symm e2) (dyR_lt H h (k + k'))

lemma dyR_eq_of_cross {m m' : ℤ} {k k' : ℕ} (h : m * 2 ^ k' = m' * 2 ^ k) :
    F.dyR m k ≡[Γ] F.dyR m' k' := by
  have e1 := dyR_double_iter H m k k'
  have e2 := dyR_double_iter H m' k' k
  rw [Nat.add_comm k' k] at e2
  rw [h] at e1
  exact bv_trans e1 (bv_symm e2)

lemma dyR_le_of_cross {m m' : ℤ} {k k' : ℕ} (h : m * 2 ^ k' ≤ m' * 2 ^ k) :
    Γ ≤ F.le (F.dyR m k) (F.dyR m' k') := by
  rcases h.lt_or_eq with hlt | heq
  · exact le_of_lt (dyR_lt_of_cross H hlt)
  · exact le_of_eq (dyR_eq_of_cross H heq)

lemma not_dyR_lt_of_cross {m m' : ℤ} {k k' : ℕ} (h : m' * 2 ^ k ≤ m * 2 ^ k') :
    Γ ≤ (F.lt (F.dyR m k) (F.dyR m' k'))ᶜ :=
  not_lt_of_le H (dyR_mem H m' k') (dyR_mem H m k) (dyR_le_of_cross H h)

lemma dyR_zero (k : ℕ) : F.dyR 0 k ≡[Γ] F.zero := by
  rw [dyR_def]
  simp only [Int.toNat_zero, dyR', mulN_zero]
  exact bv_trans (add_congr_right H (cof_zero_mem H) (neg_mem H (cof_zero_mem H)) (neg_zero H))
    (add_zero H (cof_zero_mem H))

lemma dyR_one (k : ℕ) : F.dyR 1 k ≡[Γ] F.hR k := by
  rw [dyR_def, show ((1 : ℤ)).toNat = 1 from rfl, show ((-1 : ℤ)).toNat = 0 from rfl]
  simp only [dyR', mulN_zero]
  refine bv_trans (add_congr_right H (mulN_mem H (hR_mem H k) 1) (neg_mem H (cof_zero_mem H))
    (neg_zero H)) (bv_trans (add_zero H (mulN_mem H (hR_mem H k) 1)) (mulN_one_apply H (hR_mem H k)))

lemma dyR_one_zero : F.dyR 1 0 ≡[Γ] F.one := dyR_one H 0

lemma dyR_neg (m : ℤ) (k : ℕ) : F.dyR (-m) k ≡[Γ] F.neg (F.dyR m k) := by
  refine neg_unique H (dyR_mem H m k) (dyR_mem H (-m) k) ?_
  exact bv_trans (dyR_add H m (-m) k) (by rw [add_neg_cancel]; exact dyR_zero H k)

lemma dyR_natCast (n k : ℕ) : F.dyR n k ≡[Γ] F.mulN n (F.hR k) := by
  rw [dyR_def]
  simp only [Int.toNat_natCast, Int.toNat_neg_natCast, dyR', mulN_zero]
  exact bv_trans (add_congr_right H (mulN_mem H (hR_mem H k) n) (neg_mem H (cof_zero_mem H))
    (neg_zero H)) (add_zero H (mulN_mem H (hR_mem H k) n))

end nat

/-! #### The Archimedean property and density of the dyadics -/

section arch
variable (H : Γ ≤ F.COF)
include H

/-- **Archimedean property**: for `ε > 0` and any `r`, some multiple `n · ε` exceeds `r`. -/
theorem arch {ε r : bSet β} (hεR : Γ ≤ ε ∈ᴮ F.R) (hε : Γ ≤ F.lt F.zero ε) (hr : Γ ≤ r ∈ᴮ F.R) :
    Γ ≤ ⨆ n : ℕ, F.lt r (F.mulN n ε) := by
  refine BV.by_contra ?_
  set Γ' := Γ ⊓ (⨆ n : ℕ, F.lt r (F.mulN n ε))ᶜ with hΓ'
  have hΓ : Γ' ≤ Γ := inf_le_left
  have H' := cof_mono H hΓ
  have hεR' := hΓ.trans hεR
  have hr' := hΓ.trans hr
  -- on `Γ'`, every `n · ε` is `≤ r`
  have hub : ∀ n, Γ' ≤ F.le (F.mulN n ε) r := fun n => by
    refine le_of_not_lt H' (mulN_mem H' hεR' n) hr' ?_
    have h1 : Γ' ≤ (⨆ n : ℕ, F.lt r (F.mulN n ε))ᶜ := inf_le_right
    rw [compl_iSup] at h1
    exact h1.trans (iInf_le _ n)
  -- the set `N = {n · ε}`
  set N : bSet β := seqName (fun n => F.mulN n ε) with hN
  have hNsub : Γ' ≤ N ⊆ᴮ F.R := by
    rw [subset_unfold]
    refine le_iInf fun n => ?_
    rw [← deduction]
    exact inf_le_left.trans (mulN_mem H' hεR' n)
  have hNP : Γ' ≤ N ∈ᴮ bv_powerset F.R := bv_powerset_spec.mp hNsub
  have hNne : Γ' ≤ (N =ᴮ bSet.empty)ᶜ := by
    refine BV.compl_of_inf_le_bot ?_
    have h1 : Γ' ⊓ N =ᴮ bSet.empty ≤ F.zero ∈ᴮ N := seqName_mem (fun n => F.mulN n ε) 0
    exact bot_of_mem_empty (mem_congr bv_refl inf_le_right h1)
  have hbdd : Γ' ≤ ⨆ b : bSet β, b ∈ᴮ F.R ⊓ ⨅ s : bSet β, s ∈ᴮ N ⟹ F.le s b := by
    refine le_iSup_of_le r (le_inf hr' (le_iInf fun s => ?_))
    rw [bv_imp_iff]; intro Γ'' h'' hs
    rw [hN, mem_seqName] at hs
    refine BV.iSup_elim hs fun n Γ₃ h₃ hsn => ?_
    exact le_congr (bv_symm hsn) bv_refl ((h₃.trans h'').trans (hub n))
  have hc := cof_complete H'
  rw [Sem.complete] at hc
  have hsup := BV.mp (BV.mp (BV.mp (hc.trans (iInf_le _ N)) hNP) hNne) hbdd
  refine BV.iSup_elim hsup fun u Γ'' h'' hu => ?_
  have H'' := cof_mono H' h''
  have huR := bv_and_left hu
  have hu1 := bv_and_left (bv_and_right hu)
  have hu2 := bv_and_right (bv_and_right hu)
  have hεR'' := h''.trans hεR'
  -- `v = u - ε` is an upper bound of `N`
  set v := F.add u (F.neg ε) with hv
  have hvR : Γ'' ≤ v ∈ᴮ F.R := add_mem H'' huR (neg_mem H'' hεR'')
  have hvub : Γ'' ≤ ⨅ s : bSet β, s ∈ᴮ N ⟹ F.le s v := by
    refine le_iInf fun s => ?_
    rw [bv_imp_iff]; intro Γ₃ h₃ hs
    rw [hN, mem_seqName] at hs
    refine BV.iSup_elim hs fun n Γ₄ h₄ hsn => ?_
    have hΓ₄ : Γ₄ ≤ Γ'' := h₄.trans h₃
    have H₄ := cof_mono H'' hΓ₄
    have hε₄ := hΓ₄.trans hεR''
    have h1 : Γ₄ ≤ F.le (F.mulN (n + 1) ε) u :=
      BV.mp ((hΓ₄.trans hu1).trans (iInf_le _ (F.mulN (n + 1) ε)))
        (seqName_mem (fun n => F.mulN n ε) (n + 1))
    have h2 := add_le_add_right H₄ (mulN_mem H₄ hε₄ (n + 1)) (hΓ₄.trans huR) (neg_mem H₄ hε₄) h1
    have h3 : Γ₄ ≤ F.le (F.mulN n ε) v :=
      le_congr (add_neg_cancel_right H₄ (mulN_mem H₄ hε₄ n) hε₄) bv_refl h2
    exact le_congr (bv_symm hsn) bv_refl h3
  have hle : Γ'' ≤ F.le u v := BV.mp (BV.mp (hu2.trans (iInf_le _ v)) hvR) hvub
  have hlt : Γ'' ≤ F.lt v u := by
    have hnε := neg_neg_of_pos H'' hεR'' ((h''.trans hΓ).trans hε)
    have := add_lt_add_left H'' (neg_mem H'' hεR'') (cof_zero_mem H'') huR hnε
    exact lt_congr bv_refl (add_zero H'' huR) this
  exact BV.bot_of_compl hlt (not_lt_of_le H'' huR hvR hle)

lemma arch_neg {ε r : bSet β} (hεR : Γ ≤ ε ∈ᴮ F.R) (hε : Γ ≤ F.lt F.zero ε) (hr : Γ ≤ r ∈ᴮ F.R) :
    Γ ≤ ⨆ n : ℕ, F.lt (F.neg (F.mulN n ε)) r := by
  refine BV.iSup_elim (arch H hεR hε (neg_mem H hr)) fun n Γ' h' hn => ?_
  refine le_iSup_of_le n ?_
  have H' := cof_mono H h'
  have := neg_lt_neg H' (neg_mem H' (h'.trans hr)) (mulN_mem H' (h'.trans hεR) n) hn
  exact lt_congr bv_refl (neg_neg H' (h'.trans hr)) this

/-- Some `1/2^k` is below any positive `ε`. -/
lemma exists_hR_lt {ε : bSet β} (hεR : Γ ≤ ε ∈ᴮ F.R) (hε : Γ ≤ F.lt F.zero ε) :
    Γ ≤ ⨆ k : ℕ, F.lt (F.hR k) ε := by
  refine BV.iSup_elim (arch H hεR hε (cof_one_mem H)) fun n Γ' h' hn => ?_
  refine le_iSup_of_le n ?_
  have H' := cof_mono H h'
  have hεR' := h'.trans hεR
  have hε' := h'.trans hε
  have h2 : Γ' ≤ F.lt F.one (F.mulN (2 ^ n) ε) :=
    lt_of_lt_of_le H' (cof_one_mem H') (mulN_mem H' hεR' n) (mulN_mem H' hεR' (2 ^ n)) hn
      (mulN_le_mulN_left H' hεR' hε' Nat.lt_two_pow_self.le)
  have h3 := mulN_pow_hR H' n
  refine BV.or_elim (lt_total H' (hR_mem H' n) hεR') (fun Γ'' _ h => h) fun Γ'' h'' h => ?_
  refine BV.or_elim h (fun Γ₃ h₃ heq => ?_) fun Γ₃ h₃ hlt => ?_
  · have hΓ₃ : Γ₃ ≤ Γ' := h₃.trans h''
    have H₃ := cof_mono H' hΓ₃
    have e : F.mulN (2 ^ n) ε ≡[Γ₃] F.one :=
      bv_trans (mulN_congr H₃ (hΓ₃.trans hεR') (bv_symm heq) _) (hΓ₃.trans h3)
    exact BV.of_bot (bot_of_lt_of_eq H₃ (cof_one_mem H₃) (hΓ₃.trans h2) (bv_symm e))
  · have hΓ₃ : Γ₃ ≤ Γ' := h₃.trans h''
    have H₃ := cof_mono H' hΓ₃
    have h4 : Γ₃ ≤ F.lt (F.mulN (2 ^ n) ε) F.one :=
      lt_congr bv_refl (hΓ₃.trans h3)
        (mulN_lt_mulN_right H₃ (hΓ₃.trans hεR') (hR_mem H₃ n) hlt (2 ^ n) (Nat.two_pow_pos n))
    exact BV.of_bot (bot_of_lt_of_lt H₃ (cof_one_mem H₃) (mulN_mem H₃ (hΓ₃.trans hεR') _)
      (hΓ₃.trans h2) h4)

omit H in
/-- The finite chain: between a dyadic `≤ r` and one `> r` there is a "floor". -/
lemma floor_chain {r : bSet β} (k : ℕ) (a : ℤ) :
    ∀ (j : ℕ) {Γ : β}, Γ ≤ F.COF → Γ ≤ r ∈ᴮ F.R → Γ ≤ F.le (F.dyR a k) r →
      Γ ≤ F.lt r (F.dyR (a + j + 1) k) →
      Γ ≤ ⨆ m : ℤ, F.le (F.dyR m k) r ⊓ F.lt r (F.dyR (m + 1) k)
  | 0, Γ, _, _, h1, h2 => le_iSup_of_le a (le_inf h1 (by simpa using h2))
  | j + 1, Γ, H, hr, h1, h2 => by
      have h2' : Γ ≤ F.lt r (F.dyR (a + j + 1 + 1) k) := by
        have e : a + ((j + 1 : ℕ) : ℤ) + 1 = a + j + 1 + 1 := by push_cast; omega
        rwa [e] at h2
      refine BV.or_elim (lt_total H (dyR_mem H (a + j + 1) k) hr) (fun Γ' h' hlt => ?_)
        fun Γ' h' h => ?_
      · exact le_iSup_of_le (a + j + 1) (le_inf (le_of_lt hlt) (h'.trans h2'))
      · refine BV.or_elim h (fun Γ'' h'' heq => ?_) fun Γ'' h'' hlt => ?_
        · exact le_iSup_of_le (a + j + 1) (le_inf (le_of_eq heq) ((h''.trans h').trans h2'))
        · exact floor_chain k a j (cof_mono H (h''.trans h')) ((h''.trans h').trans hr)
            ((h''.trans h').trans h1) hlt

/-- **Floor**: for every `r` and `k` there is `m` with `m/2^k ≤ r < (m+1)/2^k`. -/
lemma exists_floor {r : bSet β} (hr : Γ ≤ r ∈ᴮ F.R) (k : ℕ) :
    Γ ≤ ⨆ m : ℤ, F.le (F.dyR m k) r ⊓ F.lt r (F.dyR (m + 1) k) := by
  have hh := hR_mem H k
  have hhp := hR_pos H k
  refine BV.iSup_elim (arch H hh hhp hr) fun n Γ' h' hn => ?_
  have H' := cof_mono H h'
  refine BV.iSup_elim (arch_neg H' (h'.trans hh) (h'.trans hhp) (h'.trans hr)) fun n' Γ'' h'' hn' => ?_
  have H'' := cof_mono H' h''
  have hr'' := (h''.trans h').trans hr
  have h1 : Γ'' ≤ F.le (F.dyR (-(n' : ℤ)) k) r := by
    refine le_of_lt (lt_congr ?_ bv_refl hn')
    exact bv_symm (bv_trans (dyR_neg H'' n' k) (neg_congr H'' (dyR_mem H'' n' k) (dyR_natCast H'' n' k)))
  have h2 : Γ'' ≤ F.lt r (F.dyR (-(n' : ℤ) + (n + n' : ℕ) + 1) k) := by
    have e : (-(n' : ℤ) + ((n + n' : ℕ) : ℤ) + 1) = (n : ℤ) + 1 := by push_cast; omega
    rw [e]
    have h3 : Γ'' ≤ F.lt r (F.dyR n k) :=
      lt_congr bv_refl (bv_symm (dyR_natCast H'' n k)) (h''.trans hn)
    exact lt_trans H'' hr'' (dyR_mem H'' n k) (dyR_mem H'' (n + 1) k) h3 (dyR_lt H'' (by omega) k)
  exact floor_chain k (-(n' : ℤ)) (n + n') H'' hr'' h1 h2

/-- **Density of the dyadics**: `r < r'` implies there is a dyadic strictly between. -/
theorem dense {r r' : bSet β} (hr : Γ ≤ r ∈ᴮ F.R) (hr' : Γ ≤ r' ∈ᴮ F.R) (h : Γ ≤ F.lt r r') :
    Γ ≤ ⨆ d : ℤ × ℕ, F.lt r (F.dyR d.1 d.2) ⊓ F.lt (F.dyR d.1 d.2) r' := by
  have hε := sub_pos_of_lt H hr hr' h
  have hεR := add_mem H hr' (neg_mem H hr)
  refine BV.iSup_elim (exists_hR_lt H hεR hε) fun k Γ' h' hk => ?_
  have H' := cof_mono H h'
  refine BV.iSup_elim (exists_floor H' (h'.trans hr) k) fun m Γ'' h'' hm => ?_
  refine le_iSup_of_le (m + 1, k) (le_inf (bv_and_right hm) ?_)
  have hΓ : Γ'' ≤ Γ := h''.trans h'
  have H'' := cof_mono H hΓ
  have hr'' := hΓ.trans hr
  have hr''' := hΓ.trans hr'
  have hh := hR_mem H'' k
  have e1 : F.dyR (m + 1) k ≡[Γ''] F.add (F.dyR m k) (F.hR k) :=
    bv_symm (bv_trans (add_congr_right H'' (dyR_mem H'' m k) hh (bv_symm (dyR_one H'' k)))
      (dyR_add H'' m 1 k))
  have h2 : Γ'' ≤ F.lt (F.add (F.dyR m k) (F.hR k)) (F.add r (F.add r' (F.neg r))) :=
    add_lt_add_of_le_of_lt H'' (dyR_mem H'' m k) hr'' hh (hΓ.trans hεR) (bv_and_left hm)
      (h''.trans hk)
  have e2 : F.add r (F.add r' (F.neg r)) ≡[Γ''] r' :=
    calc F.add r (F.add r' (F.neg r)) ≡[Γ''] F.add r (F.add (F.neg r) r') :=
          add_congr_right H'' hr'' (add_mem H'' hr''' (neg_mem H'' hr'')) (add_comm H'' hr''' (neg_mem H'' hr''))
      _ ≡[Γ''] F.add (F.add r (F.neg r)) r' := bv_symm (add_assoc H'' hr'' (neg_mem H'' hr'') hr''')
      _ ≡[Γ''] F.add F.zero r' := add_congr_left H'' (add_mem H'' hr'' (neg_mem H'' hr'')) hr''' (add_neg H'' hr'')
      _ ≡[Γ''] r' := zero_add H'' hr'''
  exact lt_congr (bv_symm e1) e2 h2

end arch

end Fld

end Flypitch.Erdos501
