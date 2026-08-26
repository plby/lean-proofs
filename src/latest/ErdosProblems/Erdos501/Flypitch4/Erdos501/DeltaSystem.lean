/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

(F3) The Δ-system lemma for `𝔠⁺` countable sets (Theorem 4.3 of the paper).
-/
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.Zorn

set_option relaxedAutoImplicit true

/-!
# (F3) The Δ-system lemma for `𝔠⁺` countable sets

`delta_system_countable`: any family of `𝔠⁺` countable sets has a Δ-subsystem of size `𝔠⁺`.

This is Theorem 4.3 of the paper *"Erdős Problem 501 after adding ω₂ random reals"* (rev10),
unit **(F3)** of its formalization plan ("`ZFC + CH` combinatorics").  In the paper the index
cardinal is `ω₂` and `CH` is used to get `ℵ₁^{ℵ₀} = ℵ₁ < ℵ₂`; here the index cardinal is `𝔠⁺`
(= `ω₂` of the collapse extension, see `ColRandom.lean`), and the corresponding hypothesis
`𝔠^{ℵ₀} = 𝔠 < 𝔠⁺` is a theorem of `ZFC` — so no `CH` is needed in this form.

## The proof

Write `κ = 𝔠⁺` (a regular cardinal `> 𝔠`), and call a family `F` of indices *disjoint outside*
a set `Y` of coordinates if the sets `S a \ Y`, `a ∈ F`, are pairwise disjoint.

* **Good case** (`exists_delta_of_disjOutside`): if `#Y ≤ 𝔠` and `F` is disjoint outside `Y` with
  `#F = κ`, then the traces `S a ∩ Y` (`a ∈ F`) are countable subsets of `Y`, of which there are
  only `≤ 𝔠^{ℵ₀} = 𝔠`; by the pigeonhole principle (`κ` regular) `κ` of them coincide, and this
  common trace `R` is the root of a Δ-system: `S a ∩ S b = (S a ∩ Y) ∩ (S b ∩ Y) = R`.
* Otherwise every family disjoint outside a small `Y` is small.  Let `maxFam Y` be a maximal
  family disjoint outside `Y` (Zorn) consisting of sets not contained in `Y`, and
  `Ynext Y = Y ∪ ⋃_{a ∈ maxFam Y} S a` (again small).  By maximality every `S a ⊄ Y` **meets**
  `Ynext Y \ Y` (`meets_of_maximal`).
* Iterate `ω₁` times (`chain`, a well-founded recursion on `W = ω₁`, i.e. on
  `(ℵ₁).ord.ToType`): `X w = Ynext (⋃_{v < w} X v)`, `X_∞ = ⋃_w X w`, all of size `≤ 𝔠`.  Some
  `S a ⊄ X_∞` (else `κ` sets would be contained in the small set `X_∞`, giving `κ` equal sets — a
  Δ-system).  But `S a ∩ X_∞` is countable, hence contained in some `X w₀` (`ω₁` has uncountable
  cofinality), and for `w₁ > w₀` the set `S a ⊄ ⋃_{v < w₁} X v` must meet `X w₁ \ ⋃_{v<w₁} X v`,
  which is disjoint from `X w₀ ⊇ S a ∩ X_∞` — a contradiction (`chain_contradiction`).

This is the classical argument (Kunen, *Set Theory*, II.1.6, in its "closure" form) with the
order-type bookkeeping replaced by maximal disjoint families.
-/

open Cardinal Set
open scoped Ordinal

namespace Flypitch.Erdos501

section DeltaSystem

variable {A ι : Type} (S : A → Set ι)

/-- A family `F` of indices is *disjoint outside `Y`* if the sets `S a \ Y`, `a ∈ F`, are
pairwise disjoint. -/
def DisjOutside (Y : Set ι) (F : Set A) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, a ≠ b → Disjoint (S a \ Y) (S b \ Y)

/-- There are at most `𝔠` countable subsets of a set of size `≤ 𝔠`. -/
lemma card_countable_subsets_le {Y : Set ι} (hY : #Y ≤ 𝔠) : #{t : Set Y // #t ≤ ℵ₀} ≤ 𝔠 :=
  calc #{t : Set Y // #t ≤ ℵ₀} ≤ max #Y ℵ₀ ^ ℵ₀ := Cardinal.mk_bounded_set_le Y ℵ₀
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right (max_le hY aleph0_le_continuum)
    _ = 𝔠 := Cardinal.continuum_power_aleph0

/-- **The good case**: a family of more than `𝔠` indices whose sets are pairwise disjoint outside
a set `Y` of size `≤ 𝔠` contains a Δ-system of size `𝔠⁺` (its root is the common trace on `Y`). -/
lemma exists_delta_of_disjOutside (hS : ∀ a, (S a).Countable) (hA : #A = Order.succ 𝔠)
    {Y : Set ι} (hY : #Y ≤ 𝔠) {F : Set A} (hF : ¬ #F ≤ 𝔠) (hdisj : DisjOutside S Y F) :
    ∃ (J : Set A) (R : Set ι), #J = Order.succ 𝔠 ∧ (∀ a ∈ J, R ⊆ S a) ∧
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R := by
  have hℵ₀ : ℵ₀ ≤ Order.succ 𝔠 := aleph0_le_continuum.trans (Order.le_succ _)
  have hFκ : Order.succ 𝔠 ≤ #F := Order.succ_le_of_lt (not_le.mp hF)
  -- the trace map `a ↦ S a ∩ Y`, into the `≤ 𝔠` countable subsets of `Y`
  let tr : F → {t : Set Y // #t ≤ ℵ₀} := fun a =>
    ⟨Subtype.val ⁻¹' S a.1,
      Cardinal.mk_le_aleph0_iff.mpr ((hS a.1).preimage Subtype.val_injective).to_subtype⟩
  obtain ⟨⟨R', hR'⟩, J, hJF, ⟨hJcard, hJtr⟩⟩ := Cardinal.infinite_pigeonhole_set (s := F) tr
    (Order.succ 𝔠) hFκ hℵ₀ (by
      rw [(Cardinal.isRegular_succ aleph0_le_continuum).cof_ord]
      exact (card_countable_subsets_le hY).trans_lt (Order.lt_succ _))
  have htr : ∀ a ∈ J, (Subtype.val ⁻¹' S a : Set Y) = R' := fun a ha =>
    congrArg Subtype.val (hJtr ha)
  let R : Set ι := Subtype.val '' R'
  have hR : ∀ a ∈ J, S a ∩ Y = R := by
    intro a ha
    ext x
    constructor
    · rintro ⟨hxa, hxY⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      rw [← htr a ha]
      exact hxa
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (Subtype.val ⁻¹' S a : Set Y) := by rw [htr a ha]; exact hy
      exact ⟨hy', y.2⟩
  refine ⟨J, R, le_antisymm ((Cardinal.mk_set_le J).trans hA.le) hJcard, ?_, ?_⟩
  · intro a ha
    rw [← hR a ha]
    exact inter_subset_left
  · intro a ha b hb hab
    apply subset_antisymm
    · rintro x ⟨hxa, hxb⟩
      by_cases hxY : x ∈ Y
      · rw [← hR a ha]; exact ⟨hxa, hxY⟩
      · exact (Set.disjoint_left.mp (hdisj a (hJF ha) b (hJF hb) hab) ⟨hxa, hxY⟩ ⟨hxb, hxY⟩).elim
    · intro x hx
      have h1 : x ∈ S a ∩ Y := by rw [hR a ha]; exact hx
      have h2 : x ∈ S b ∩ Y := by rw [hR b hb]; exact hx
      exact ⟨h1.1, h2.1⟩

/-- The families disjoint outside `Y` consisting of sets not contained in `Y`. -/
def Fam (Y : Set ι) : Set (Set A) := {F | (∀ a ∈ F, ¬ S a ⊆ Y) ∧ DisjOutside S Y F}

/-- Maximal families exist (Zorn's lemma). -/
lemma exists_maximal_fam (Y : Set ι) : ∃ F, Maximal (· ∈ Fam S Y) F := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
  · rintro a ⟨F, hF, haF⟩
    exact (hc hF).1 a haF
  · rintro a ⟨F, hF, haF⟩ b ⟨G, hG, hbG⟩ hab
    rcases hchain.total hF hG with h | h
    · exact (hc hG).2 a (h haF) b hbG hab
    · exact (hc hF).2 a haF b (h hbG) hab

/-- The next set of the closure: `Y ∪ ⋃_{a ∈ maxFam Y} S a`. -/
def Ynext (maxFam : Set ι → Set A) (Y : Set ι) : Set ι := Y ∪ ⋃ a ∈ maxFam Y, S a

/-- **Meeting property.**  If `F` is a maximal family disjoint outside `Y`, every set `S a ⊄ Y`
meets `(Y ∪ ⋃_{b ∈ F} S b) \ Y`. -/
lemma meets_of_maximal {Y : Set ι} {F : Set A} (hmax : Maximal (· ∈ Fam S Y) F) (a : A)
    (ha : ¬ S a ⊆ Y) : (S a ∩ ((Y ∪ ⋃ b ∈ F, S b) \ Y)).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hmem : ∀ x, x ∈ S a → x ∉ Y → x ∉ ⋃ b ∈ F, S b := by
    intro x hxa hxY hx
    have : x ∈ S a ∩ ((Y ∪ ⋃ b ∈ F, S b) \ Y) := ⟨hxa, Or.inr hx, hxY⟩
    rw [hcon] at this
    exact this
  have haF : a ∉ F := by
    intro haF
    obtain ⟨x, hxa, hxY⟩ := Set.not_subset.mp ha
    exact hmem x hxa hxY (mem_biUnion haF hxa)
  have hdisj_a : ∀ b ∈ F, Disjoint (S a \ Y) (S b \ Y) := by
    intro b hb
    rw [Set.disjoint_left]
    rintro x ⟨hxa, hxY⟩ ⟨hxb, -⟩
    exact hmem x hxa hxY (mem_biUnion hb hxb)
  have hins : insert a F ∈ Fam S Y := by
    refine ⟨?_, ?_⟩
    · intro c hc
      rcases mem_insert_iff.mp hc with rfl | hcF
      · exact ha
      · exact hmax.prop.1 c hcF
    · intro c hc d hd hcd
      rcases mem_insert_iff.mp hc with rfl | hcF <;> rcases mem_insert_iff.mp hd with rfl | hdF
      · exact absurd rfl hcd
      · exact hdisj_a d hdF
      · exact (hdisj_a c hcF).symm
      · exact hmax.prop.2 c hcF d hdF hcd
  exact haF (hmax.mem_of_prop_insert hins)

/-- Size bound for `Ynext`. -/
lemma card_Ynext_le (hS : ∀ a, (S a).Countable) {maxFam : Set ι → Set A} {Y : Set ι}
    (hY : #Y ≤ 𝔠) (hF : #(maxFam Y) ≤ 𝔠) : #(Ynext S maxFam Y) ≤ 𝔠 := by
  have h1 : #(⋃ a ∈ maxFam Y, S a) ≤ 𝔠 :=
    calc #(⋃ a ∈ maxFam Y, S a) ≤ #(maxFam Y) * ⨆ a : maxFam Y, #(S a.1) :=
          Cardinal.mk_biUnion_le S (maxFam Y)
      _ ≤ 𝔠 * 𝔠 := mul_le_mul' hF (ciSup_le' fun a =>
          (Cardinal.mk_le_aleph0_iff.mpr (hS a.1).to_subtype).trans aleph0_le_continuum)
      _ = 𝔠 := Cardinal.mul_eq_self aleph0_le_continuum
  calc #(Ynext S maxFam Y) ≤ #Y + #(⋃ a ∈ maxFam Y, S a) := Cardinal.mk_union_le _ _
    _ ≤ 𝔠 + 𝔠 := add_le_add hY h1
    _ = 𝔠 := Cardinal.add_eq_self aleph0_le_continuum

/-! ### The closure chain of length `ω₁` -/

section chain

variable {W : Type} [LinearOrder W] [WellFoundedLT W]

/-- The closure chain `X w = Ynext (⋃_{v < w} X v)`. -/
noncomputable def chain (maxFam : Set ι → Set A) : W → Set ι :=
  WellFounded.fix wellFounded_lt fun w rec => Ynext S maxFam (⋃ v : Iio w, rec v.1 v.2)

lemma chain_eq (maxFam : Set ι → Set A) (w : W) :
    chain S maxFam w = Ynext S maxFam (⋃ v : Iio w, chain S maxFam v.1) := by
  unfold chain
  rw [WellFounded.fix_eq]

lemma chain_mono (maxFam : Set ι → Set A) {v w : W} (hvw : v ≤ w) :
    chain S maxFam v ⊆ chain S maxFam w := by
  rcases hvw.lt_or_eq with h | rfl
  · rw [chain_eq S maxFam w]
    exact (subset_iUnion (fun v : Iio w => chain S maxFam v.1) ⟨v, h⟩).trans subset_union_left
  · exact subset_refl _

omit [WellFoundedLT W] in
/-- Countable subsets of an uncountable well-order with countable initial segments are bounded. -/
lemma exists_upper_bound_of_countable (hW : ¬ Countable W) (hIio : ∀ w : W, (Iio w).Countable)
    {s : Set W} (hs : s.Countable) : ∃ w₀, ∀ w ∈ s, w ≤ w₀ := by
  by_contra h
  apply hW
  have hsub : (univ : Set W) ⊆ ⋃ w ∈ s, Iio w := by
    intro w₀ _
    obtain ⟨w, hw, hlt⟩ : ∃ w ∈ s, ¬ w ≤ w₀ := by
      by_contra h'
      exact h ⟨w₀, fun w hw => by_contra fun hle => h' ⟨w, hw, hle⟩⟩
    exact mem_biUnion hw (not_le.mp hlt)
  exact countable_univ_iff.mp ((hs.biUnion fun w _ => hIio w).mono hsub)

omit [WellFoundedLT W] in
lemma exists_gt_of_uncountable (hW : ¬ Countable W) (hIio : ∀ w : W, (Iio w).Countable) (w₀ : W) :
    ∃ w₁, w₀ < w₁ := by
  by_contra h
  apply hW
  have hsub : (univ : Set W) ⊆ insert w₀ (Iio w₀) := by
    intro w _
    rcases (not_lt.mp fun hlt => h ⟨w, hlt⟩).lt_or_eq with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl heq
  exact countable_univ_iff.mp (((hIio w₀).insert w₀).mono hsub)

variable (hS : ∀ a, (S a).Countable) (hIio : ∀ w : W, (Iio w).Countable)
  {maxFam : Set ι → Set A} (hsmall : ∀ Y : Set ι, #Y ≤ 𝔠 → #(maxFam Y) ≤ 𝔠)

include hS hIio hsmall in
lemma card_chain_le (w : W) : #(chain S maxFam w) ≤ 𝔠 := by
  refine WellFoundedLT.induction (motive := fun w : W => #(chain S maxFam w) ≤ 𝔠) w
    fun w ih => ?_
  show #(chain S maxFam w) ≤ 𝔠
  rw [chain_eq]
  have hY : #(⋃ v : Iio w, chain S maxFam v.1) ≤ 𝔠 :=
    calc #(⋃ v : Iio w, chain S maxFam v.1) ≤ #(Iio w) * ⨆ v : Iio w, #(chain S maxFam v.1) :=
          Cardinal.mk_iUnion_le _
      _ ≤ 𝔠 * 𝔠 := mul_le_mul'
          ((Cardinal.mk_le_aleph0_iff.mpr (hIio w).to_subtype).trans aleph0_le_continuum)
          (ciSup_le' fun v => ih v.1 v.2)
      _ = 𝔠 := Cardinal.mul_eq_self aleph0_le_continuum
  exact card_Ynext_le S hS hY (hsmall _ hY)

include hS hIio hsmall in
lemma card_iUnion_chain_le (hWc : #W ≤ 𝔠) : #(⋃ w : W, chain S maxFam w) ≤ 𝔠 :=
  calc #(⋃ w : W, chain S maxFam w) ≤ #W * ⨆ w, #(chain S maxFam w) := Cardinal.mk_iUnion_le _
    _ ≤ 𝔠 * 𝔠 := mul_le_mul' hWc (ciSup_le' fun w => card_chain_le S (W := W) hS hIio hsmall w)
    _ = 𝔠 := Cardinal.mul_eq_self aleph0_le_continuum

include hS hIio hsmall in
/-- **The closure argument.**  If every `S a ⊄ Y` meets `Ynext Y \ Y` (for small `Y`), then every
`S a` is contained in `X_∞ = ⋃_w chain w`. -/
lemma chain_contradiction (hW : ¬ Countable W)
    (hmeets : ∀ Y : Set ι, #Y ≤ 𝔠 → ∀ a, ¬ S a ⊆ Y → (S a ∩ (Ynext S maxFam Y \ Y)).Nonempty)
    (a : A) (ha : ¬ S a ⊆ ⋃ w : W, chain S maxFam w) : False := by
  classical
  -- `S a ∩ X_∞` is countable, hence contained in some `chain w₀`
  have hcnt : (S a ∩ ⋃ w : W, chain S maxFam w).Countable := (hS a).mono inter_subset_left
  haveI := hcnt.to_subtype
  have hex : ∀ e : ↥(S a ∩ ⋃ w : W, chain S maxFam w), ∃ w, (e : ι) ∈ chain S maxFam w :=
    fun e => mem_iUnion.mp e.2.2
  choose wf hwf using hex
  obtain ⟨w₀, hw₀⟩ := exists_upper_bound_of_countable (W := W) hW hIio (countable_range wf)
  have hsub : S a ∩ ⋃ w : W, chain S maxFam w ⊆ chain S maxFam w₀ := fun e he =>
    chain_mono S maxFam (hw₀ _ ⟨⟨e, he⟩, rfl⟩) (hwf ⟨e, he⟩)
  -- pick `w₁ > w₀`; then `S a ⊄ Y w₁ := ⋃_{v < w₁} chain v ⊇ chain w₀`
  obtain ⟨w₁, hw₁⟩ := exists_gt_of_uncountable (W := W) hW hIio w₀
  have hY₀ : chain S maxFam w₀ ⊆ ⋃ v : Iio w₁, chain S maxFam v.1 :=
    subset_iUnion (fun v : Iio w₁ => chain S maxFam v.1) ⟨w₀, hw₁⟩
  have hYX : (⋃ v : Iio w₁, chain S maxFam v.1) ⊆ ⋃ w : W, chain S maxFam w :=
    iUnion_subset fun v => subset_iUnion (fun w => chain S maxFam w) v.1
  have hnot : ¬ S a ⊆ ⋃ v : Iio w₁, chain S maxFam v.1 := fun h => ha (h.trans hYX)
  have hYc : #(⋃ v : Iio w₁, chain S maxFam v.1) ≤ 𝔠 :=
    calc #(⋃ v : Iio w₁, chain S maxFam v.1) ≤ #(Iio w₁) * ⨆ v : Iio w₁, #(chain S maxFam v.1) :=
          Cardinal.mk_iUnion_le _
      _ ≤ 𝔠 * 𝔠 := mul_le_mul'
          ((Cardinal.mk_le_aleph0_iff.mpr (hIio w₁).to_subtype).trans aleph0_le_continuum)
          (ciSup_le' fun v => card_chain_le S (W := W) hS hIio hsmall v.1)
      _ = 𝔠 := Cardinal.mul_eq_self aleph0_le_continuum
  -- the meeting property at `Y w₁` produces `e ∈ S a ∩ chain w₁` with `e ∉ Y w₁`;
  -- but `e ∈ S a ∩ X_∞ ⊆ chain w₀ ⊆ Y w₁`
  obtain ⟨e, heS, heX, heY⟩ := hmeets _ hYc a hnot
  have heX' : e ∈ ⋃ w : W, chain S maxFam w := by
    rw [mem_iUnion]
    exact ⟨w₁, by rw [chain_eq]; exact heX⟩
  exact heY (hY₀ (hsub ⟨heS, heX'⟩))

end chain

/-- `ω₁` as a type: `(ℵ₁).ord.ToType`, uncountable, with countable initial segments. -/
lemma omega1_facts :
    ¬ Countable (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType ∧
      (∀ w : (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType, (Iio w).Countable) ∧
      #(Cardinal.aleph 1 : Cardinal.{0}).ord.ToType ≤ 𝔠 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : #(Cardinal.aleph 1 : Cardinal.{0}).ord.ToType ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr h
    rw [Cardinal.mk_ord_toType] at h1
    exact (Cardinal.aleph0_lt_aleph_one).not_ge h1
  · intro w
    have h1 : #(Iio w) < #(Cardinal.aleph 1 : Cardinal.{0}).ord.ToType :=
      Cardinal.mk_Iio_lt w (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
    rw [Cardinal.mk_ord_toType, Cardinal.lt_aleph_one_iff] at h1
    exact Set.countable_coe_iff.mp (Cardinal.mk_le_aleph0_iff.mp h1)
  · rw [Cardinal.mk_ord_toType]
    exact Cardinal.aleph_one_le_continuum

/-- **(F3) The Δ-system lemma for `𝔠⁺` countable sets** (Theorem 4.3).  If `S : A → Set ι` is a
family of countable sets indexed by a type of cardinality `𝔠⁺`, there are a subfamily `J` of
cardinality `𝔠⁺` and a *root* `R` with `S a ∩ S b = R` for all distinct `a, b ∈ J`
(and `R ⊆ S a` for `a ∈ J`). -/
theorem delta_system_countable (hS : ∀ a, (S a).Countable) (hA : #A = Order.succ 𝔠) :
    ∃ (J : Set A) (R : Set ι), #J = Order.succ 𝔠 ∧ (∀ a ∈ J, R ⊆ S a) ∧
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → S a ∩ S b = R := by
  classical
  by_contra hno
  -- (a) every family disjoint outside a small `Y` is small
  have hsmall' : ∀ Y : Set ι, #Y ≤ 𝔠 → ∀ F : Set A, DisjOutside S Y F → #F ≤ 𝔠 := by
    intro Y hY F hF
    by_contra h
    exact hno (exists_delta_of_disjOutside S hS hA hY h hF)
  -- (b) maximal families
  choose maxFam hmax using exists_maximal_fam S
  have hsmall : ∀ Y : Set ι, #Y ≤ 𝔠 → #(maxFam Y) ≤ 𝔠 := fun Y hY =>
    hsmall' Y hY _ (hmax Y).prop.2
  have hmeets : ∀ Y : Set ι, #Y ≤ 𝔠 → ∀ a, ¬ S a ⊆ Y →
      (S a ∩ (Ynext S maxFam Y \ Y)).Nonempty := fun Y _ a ha =>
    meets_of_maximal S (hmax Y) a ha
  -- (c) the closure chain along `ω₁`
  obtain ⟨hW, hIio, hWc⟩ := omega1_facts
  have hXc := card_iUnion_chain_le S hS hIio hsmall hWc
  -- some `S a` is not contained in `X_∞`: otherwise `A` is a family disjoint outside `X_∞`
  have hex : ∃ a, ¬ S a ⊆ ⋃ w : (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType, chain S maxFam w := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hdisj : DisjOutside S
        (⋃ w : (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType, chain S maxFam w) univ := by
      intro a _ b _ _
      rw [Set.diff_eq_empty.mpr (h a)]
      exact disjoint_bot_left
    have := hsmall' _ hXc univ hdisj
    rw [Cardinal.mk_univ, hA] at this
    exact (Order.lt_succ 𝔠).not_ge this
  obtain ⟨a, ha⟩ := hex
  exact chain_contradiction S hS hIio hsmall hW hmeets a ha

end DeltaSystem

end Flypitch.Erdos501
