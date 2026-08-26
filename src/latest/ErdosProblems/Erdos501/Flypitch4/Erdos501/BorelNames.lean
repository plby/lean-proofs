/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Names for Borel sets in the random-algebra model, and Theorem 4.5 (`⊩ ν*(Ż) = 1`) with names.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import ErdosProblems.Erdos501.Flypitch4.Erdos501.RandomForcing

set_option relaxedAutoImplicit true

/-!
# Names for Borel sets of reals in `V (randomAlgebra ι)`

This file provides the *names* for Borel sets that the units (F5) and (F6) of the paper's plan
speak about, and restates Theorem 4.5 (unit (F5), "fresh-profile fullness", `⊩ ν*(Ż) = 1`) in
terms of them.

## Design

In the measure-algebra model every name for a real (subset of `ω`) is forced equal to a
*canonical* name `mkReal F hF` for a measurable `F : Ω ι → 2^ω` (Theorem 4.1,
`exists_mkReal_bv_eq`).  A Borel set of reals *in the extension* is read from the generic point:
given a set of coordinates `T` and a Borel `B ⊆ 2^T × 2^ω`, the set `Ḃ = {r ∈ 2^ω | (ĝ↾T, r) ∈ B}`
("`B` with the parameter `ĝ↾T` plugged in").  Its name `borelName T B hB` is the `bSet` whose
elements are the canonical names `mkReal F` of all reals, `mkReal F` belonging to `Ḃ` with Boolean
value the class of the event `{x | (x↾T, F x) ∈ B}`.  The basic facts are

* `bv_eq_mkReal`: `‖mkReal G = mkReal F‖ = [{x | G x = F x}]` — two canonical names are equal
  exactly on the event where the readings agree;
* `mem_borelName_mkReal`: `‖mkReal G ∈ Ḃ‖ = [{x | (x↾T, G x) ∈ B}]` — evaluation of the name at
  a canonical name, hence at every name for a real (`mem_borelName`);
* `mem_borelName_le_subset_omega`: `Ḃ` is (forced to be) a set of reals.

Profiles `z ∈ 2^P` (`P = ℕ`, `2^P = ℕ → 2^ω`) are coded as reals by `codeP` (pairing);
`profileName π` is the name of the profile `ż = ĝ ∘ π` of a petal `π : ℕ ↪ ι`, and
`borelNameP T B'` the name of the Borel set of profiles `{z | (ĝ↾T, z) ∈ B'}` for
`B' ⊆ 2^T × 2^P`, with `mem_borelNameP_profileName : ‖ż ∈ Ḃ‖ = [{x | (x↾T, ĝ ∘ π) ∈ B'}]`.

Finally `measGtP T hB' ε` is the Boolean value of "`ν(Ḃ) > ε`" for `Ḃ = borelNameP T B'`
(the class of `{x | ε < ν(B'_{x↾T})}`, `B'_t` the fibre of `B'` over `t`, `ν` the fair-coin product
measure on `2^P` — this is what "`q ⊩ ν(Ḃ) > ε`" unpacks to in the measure-algebra model, see the
paper's proof of Lemma 4.5), and

* **`fullness` (Theorem 4.5, with names)**: for uncountably many pairwise disjoint petals
  `(π a)_{a ∈ J}` (the output of Prop. 4.4), every countable `T`, Borel `B' ⊆ 2^T × 2^P` and
  `ε > 0`: `‖ν(Ḃ) > ε‖ ≤ ⨆ a ∈ J, ‖ż_a ∈ Ḃ‖`, i.e. `⊩ (ν(Ḃ) > ε → Ḃ ∩ Ż ≠ ∅)` for the name
  `Ż = {ż_a | a ∈ J}` (`profilesName`) — which is `⊩ ν*(Ż) = 1` once one knows (Borel reading of
  codes, not formalized) that every name for a Borel set of profiles is of the form
  `borelNameP T B'` for a countable `T`.
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet
open scoped ENNReal Flypitch

namespace Flypitch.MeasureAlgebra

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- `mk` respects equality of sets (as sets, not only almost everywhere). -/
theorem mk_congr {s t : Set X} (h : s = t) {hs : MeasurableSet s} {ht : MeasurableSet t} :
    mk μ s hs = mk μ t ht := by
  subst h; rfl

end Flypitch.MeasureAlgebra

namespace Flypitch.Erdos501.RandomForcing

variable {ι : Type}

/-! ### The Boolean value of the equality of two canonical names for reals -/

lemma measurableSet_eqF {G F : RandomAlgebra.Ω ι → (ℕ → Bool)} (hG : Measurable G)
    (hF : Measurable F) : MeasurableSet {x | G x = F x} := by
  have h : {x | G x = F x} = ⋂ n, {x | G x n = F x n} := by
    ext x; simp [funext_iff]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    measurableSet_eq_fun ((measurable_pi_apply n).comp hG) ((measurable_pi_apply n).comp hF)

/-- **Equality of canonical names.**  Two canonical names for reals are equal (as a Boolean value)
exactly on the event where the readings agree: `‖mkReal G = mkReal F‖ = [{x | G x = F x}]`. -/
theorem bv_eq_mkReal {G F : RandomAlgebra.Ω ι → (ℕ → Bool)} (hG : Measurable G)
    (hF : Measurable F) :
    (mkReal G hG =ᴮ mkReal F hF) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | G x = F x} (measurableSet_eqF hG hF) := by
  rw [bv_eq_unfold]
  simp only [mkReal_bval, mkReal_func, mem_mkReal, imp_iff, MeasureAlgebra.mk_compl,
    MeasureAlgebra.mk_sup]
  rw [MeasureAlgebra.iInf_mk, MeasureAlgebra.iInf_mk, MeasureAlgebra.mk_inf]
  apply MeasureAlgebra.mk_congr
  ext x
  simp only [mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq, funext_iff]
  constructor
  · rintro ⟨h1, h2⟩ n
    rcases h1 ⟨n⟩ with h | h <;> rcases h2 ⟨n⟩ with h' | h' <;> simp_all
  · intro h
    refine ⟨fun n => ?_, fun n => ?_⟩
    · rw [h n.down]; exact (em _).symm
    · rw [h n.down]; exact (em _).symm

/-! ### Names for Borel sets of reals -/

/-- Codes of reals: the measurable functions `Ω ι → 2^ω`; `F` codes the canonical name
`mkReal F` of the real `{n | F(ĝ) n = 1}`. -/
abbrev RealCode (ι : Type) : Type := {F : RandomAlgebra.Ω ι → (ℕ → Bool) // Measurable F}

/-- **The name `Ḃ`** of the Borel set of reals `{r ∈ 2^ω | (ĝ↾T, r) ∈ B}` read from a Borel
`B ⊆ 2^T × 2^ω` and the `T`-part `ĝ↾T` of the generic point: its elements are the canonical names
`mkReal F` of reals, `mkReal F` belonging to `Ḃ` with Boolean value the class of the event
`{x | (x↾T, F x) ∈ B}`. -/
noncomputable def borelName (T : Set ι) (B : Set ((T → (ℕ → Bool)) × (ℕ → Bool)))
    (hB : MeasurableSet B) : bSet (randomAlgebra ι) :=
  ⟨RealCode ι, fun F => mkReal F.1 F.2,
    fun F => MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, F.1 x) ∈ B}
      (hB.preimage (T.measurable_restrict.prodMk F.2))⟩

variable (T : Set ι) {B : Set ((T → (ℕ → Bool)) × (ℕ → Bool))} (hB : MeasurableSet B)

@[simp] lemma borelName_type : (borelName T B hB).type = RealCode ι := rfl
@[simp] lemma borelName_func (F : (borelName T B hB).type) :
    (borelName T B hB).func F = mkReal F.1 F.2 := rfl
@[simp] lemma borelName_bval (F : (borelName T B hB).type) : (borelName T B hB).bval F =
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, F.1 x) ∈ B}
      (hB.preimage (T.measurable_restrict.prodMk F.2)) := rfl

/-- **Evaluation of `Ḃ` at a canonical name**: `‖mkReal G ∈ Ḃ‖ = [{x | (x↾T, G x) ∈ B}]`. -/
theorem mem_borelName_mkReal {G : RandomAlgebra.Ω ι → (ℕ → Bool)} (hG : Measurable G) :
    (mkReal G hG ∈ᴮ borelName T B hB) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, G x) ∈ B}
        (hB.preimage (T.measurable_restrict.prodMk hG)) := by
  rw [mem_unfold]
  simp only [borelName_bval, borelName_func]
  apply le_antisymm
  · apply iSup_le
    intro F
    rw [bv_eq_mkReal, MeasureAlgebra.mk_inf, MeasureAlgebra.mk_le_mk,
      MeasureAlgebra.ae_le_set_iff_ae_imp]
    refine Filter.Eventually.of_forall fun x hx => ?_
    obtain ⟨hxB, hxeq⟩ := hx
    show (T.domRestrict x, G x) ∈ B
    rw [hxeq]
    exact hxB
  · refine le_iSup_of_le ⟨G, hG⟩ ?_
    have h : (mkReal G hG =ᴮ mkReal (⟨G, hG⟩ : RealCode ι).1 (⟨G, hG⟩ : RealCode ι).2) = ⊤ :=
      bv_eq_refl _
    rw [h, inf_top_eq]

/-- Every element of `Ḃ` is (forced to be) a real: `‖y ∈ Ḃ‖ ≤ ‖y ⊆ ω‖`. -/
theorem mem_borelName_le_subset_omega (y : bSet (randomAlgebra ι)) :
    y ∈ᴮ borelName T B hB ≤ y ⊆ᴮ omega := by
  rw [mem_unfold]
  apply iSup_le
  intro F
  simp only [borelName_bval, borelName_func]
  calc _ ≤ (mkReal F.1 F.2 ⊆ᴮ omega) ⊓ (y =ᴮ mkReal F.1 F.2) :=
        inf_le_inf_right _ (le_trans le_top (mkReal_definite F.2))
    _ ≤ y ⊆ᴮ omega := subst_congr_subset_left

/-- **Evaluation of `Ḃ` at an arbitrary name for a real** (via the Borel reading, Theorem 4.1):
for every `y` with `⊤ ≤ y ⊆ᴮ ω` there is a canonical name `mkReal G` forced equal to `y` with
`‖y ∈ Ḃ‖ = [{x | (x↾T, G x) ∈ B}]`. -/
theorem mem_borelName (y : bSet (randomAlgebra ι)) (hy : ⊤ ≤ y ⊆ᴮ omega) :
    ∃ (G : RandomAlgebra.Ω ι → (ℕ → Bool)) (hG : Measurable G),
      ⊤ ≤ y =ᴮ mkReal G hG ∧ (y ∈ᴮ borelName T B hB) =
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, G x) ∈ B}
          (hB.preimage (T.measurable_restrict.prodMk hG)) := by
  obtain ⟨G, hG, -, -, -, heq⟩ := exists_mkReal_bv_eq y hy
  refine ⟨G, hG, heq, ?_⟩
  rw [← mem_borelName_mkReal T hB hG]
  apply le_antisymm
  · calc y ∈ᴮ borelName T B hB = (y =ᴮ mkReal G hG) ⊓ (y ∈ᴮ borelName T B hB) := by
          rw [top_le_iff.mp heq, top_inf_eq]
      _ ≤ _ := subst_congr_mem_left
  · calc mkReal G hG ∈ᴮ borelName T B hB
        = (mkReal G hG =ᴮ y) ⊓ (mkReal G hG ∈ᴮ borelName T B hB) := by
          rw [bv_eq_symm, top_le_iff.mp heq, top_inf_eq]
      _ ≤ _ := subst_congr_mem_left

/-! ### Profiles as reals, and names for Borel sets of profiles -/

/-- Coding of a profile `z ∈ 2^P = ℕ → 2^ω` as a real, via `Nat.pair`. -/
def codeP (z : ℕ → (ℕ → Bool)) : ℕ → Bool := fun m => z (Nat.unpair m).1 (Nat.unpair m).2

/-- Decoding of a real as a profile. -/
def decodeP (r : ℕ → Bool) : ℕ → (ℕ → Bool) := fun n k => r (Nat.pair n k)

@[simp] lemma decodeP_codeP (z : ℕ → (ℕ → Bool)) : decodeP (codeP z) = z := by
  funext n k
  simp [decodeP, codeP]

lemma measurable_codeP : Measurable codeP :=
  measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma measurable_decodeP : Measurable decodeP :=
  measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The name `ż` of the profile `ĝ ∘ π ∈ 2^P` of a petal `π : ℕ → ι` (as a real, via `codeP`). -/
noncomputable def profileName (π : ℕ → ι) : bSet (randomAlgebra ι) :=
  mkReal (fun x => codeP (fun n => x (π n)))
    (measurable_codeP.comp (measurable_pi_lambda _ fun n => measurable_pi_apply (π n)))

/-- The name `Ż = {ż_a | a ∈ J}` of the set of profiles of a family of petals. -/
noncomputable def profilesName {A : Type} (J : Set A) (π : A → ℕ → ι) : bSet (randomAlgebra ι) :=
  ⟨J, fun a => profileName (π a), fun _ => ⊤⟩

@[simp] lemma profilesName_type {A : Type} (J : Set A) (π : A → ℕ → ι) :
    (profilesName J π).type = J := rfl
@[simp] lemma profilesName_func {A : Type} (J : Set A) (π : A → ℕ → ι)
    (a : (profilesName J π).type) : (profilesName J π).func a = profileName (π a.1) := rfl
@[simp] lemma profilesName_bval {A : Type} (J : Set A) (π : A → ℕ → ι)
    (a : (profilesName J π).type) : (profilesName J π).bval a = ⊤ := rfl

/-- **`‖Ḃ ∩ Ż ≠ ∅‖ = ⨆ a ∈ J, ‖ż_a ∈ Ḃ‖`**: the Boolean value of "some element of `Ż` lies in
`Ḃ`" (for any name `Ḃ`) is the supremum of the Boolean values `‖ż_a ∈ Ḃ‖`. -/
theorem iSup_mem_profilesName {A : Type} (J : Set A) (π : A → ℕ → ι)
    (Bdot : bSet (randomAlgebra ι)) :
    (⨆ z : bSet (randomAlgebra ι), z ∈ᴮ profilesName J π ⊓ z ∈ᴮ Bdot) =
      ⨆ a : J, (profileName (π a) ∈ᴮ Bdot) := by
  apply le_antisymm
  · apply iSup_le
    intro z
    rw [mem_unfold, iSup_inf_eq]
    apply iSup_mono
    intro a
    simp only [profilesName_bval, profilesName_func, top_inf_eq]
    exact subst_congr_mem_left
  · apply iSup_le
    intro a
    apply le_iSup_of_le (profileName (π a))
    refine le_inf (le_trans le_top ?_) le_rfl
    rw [mem_unfold]
    apply le_iSup_of_le a
    exact le_inf le_rfl (le_of_eq (bv_eq_refl _).symm)

variable {B' : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))}

lemma measurableSet_decodeP_preimage (hB' : MeasurableSet B') :
    MeasurableSet {p : (T → (ℕ → Bool)) × (ℕ → Bool) | (p.1, decodeP p.2) ∈ B'} :=
  hB'.preimage (measurable_fst.prodMk (measurable_decodeP.comp measurable_snd))

/-- The name `Ḃ` of the Borel set of profiles `{z ∈ 2^P | (ĝ↾T, z) ∈ B'}` read from a Borel
`B' ⊆ 2^T × 2^P`. -/
noncomputable def borelNameP (hB' : MeasurableSet B') : bSet (randomAlgebra ι) :=
  borelName T {p | (p.1, decodeP p.2) ∈ B'} (measurableSet_decodeP_preimage T hB')

/-- **`‖ż ∈ Ḃ‖ = [{x | (x↾T, ĝ ∘ π) ∈ B'}]`**: the Boolean value of "the profile of the petal `π`
belongs to the Borel set of profiles read from `B'`" is the class of the event
`{x | (x↾T, (x (π n))ₙ) ∈ B'}` — the identification used in the proof of Lemma 4.5. -/
theorem mem_borelNameP_profileName (hB' : MeasurableSet B') (π : ℕ → ι) :
    (profileName π ∈ᴮ borelNameP T hB') =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (T.domRestrict x, fun n => x (π n)) ∈ B'}
        (hB'.preimage
          (T.measurable_restrict.prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (π n)))) := by
  unfold profileName borelNameP
  rw [mem_borelName_mkReal]
  apply MeasureAlgebra.mk_congr
  ext x
  simp

/-- The Boolean value of "`ν(Ḃ) > ε`" for `Ḃ = borelNameP T B'`: the class of the event
`{x | ε < ν(B'_{x↾T})}`, where `B'_t = {z | (t, z) ∈ B'}` and `ν` is the fair-coin product measure
on `2^P`.  (In the measure-algebra model, "`q ⊩ ν(Ḃ) > ε`" means exactly that `ν(B'_{x↾T}) > ε`
for almost every `x ∈ [q]`; the internal statement is not formalized, this is its Boolean value.) -/
noncomputable def measGtP (hB' : MeasurableSet B') (ε : ℝ≥0∞) : randomAlgebra ι :=
  MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
    {x | ε < Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
      (Prod.mk (T.domRestrict x) ⁻¹' B')}
    (measurableSet_lt measurable_const
      ((measurable_measure_prodMk_left hB').comp T.measurable_restrict))

/-! ### Supports of events -/

open Classical in
/-- Extension of a point of `2^T` to a point of `Ω ι` (by `false` outside `T`). -/
noncomputable def extT (T : Set ι) (t : T → (ℕ → Bool)) : RandomAlgebra.Ω ι :=
  fun i => if h : i ∈ T then t ⟨i, h⟩ else fun _ => false

lemma measurable_extT : Measurable (extT T) := by
  classical
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ T
  · simp only [extT, h, dite_true]; exact measurable_pi_apply _
  · simp only [extT, h, dite_false]; exact measurable_const

@[simp] lemma restrict_extT (t : T → (ℕ → Bool)) : T.domRestrict (extT T t) = t := by
  funext s
  simp [extT, s.2]

/-- Every measurable event is a `T`-event `{x | x↾T ∈ Q}` for a countable `T` and a *measurable*
`Q ⊆ 2^T` (Theorem 4.1, countable supports, with a measurable trace). -/
theorem exists_countable_restrict_preimage {A : Set (RandomAlgebra.Ω ι)} (hA : MeasurableSet A) :
    ∃ T : Set ι, T.Countable ∧
      ∃ Q : Set (T → (ℕ → Bool)), MeasurableSet Q ∧ A = T.domRestrict ⁻¹' Q := by
  obtain ⟨T, t, hT, hAt⟩ := hA.eq_preimage_restrict_countable
  refine ⟨T, hT, extT T ⁻¹' A, measurable_extT T hA, ?_⟩
  ext x
  simp only [mem_preimage]
  rw [hAt]
  simp only [mem_preimage, restrict_extT]

/-- The measure of a `T`-event is the `μ_T`-measure of its trace. -/
theorem μ_random_restrict_preimage {Q : Set (T → (ℕ → Bool))} (hQ : MeasurableSet Q) :
    RandomAlgebra.μ_random ι (T.domRestrict ⁻¹' Q) =
      Measure.infinitePi (fun _ : T => RandomAlgebra.cantorMeasure) Q := by
  rw [← map_restrict T, Measure.map_apply T.measurable_restrict hQ]

/-! ### (F5) Theorem 4.5 with names: `⊩ ν(Ḃ) > ε → Ḃ ∩ Ż ≠ ∅` -/

/-- **Theorem 4.5 (fresh-profile fullness), Boolean-value form with names.**  Let `(π a)_{a ∈ J}`
be uncountably many pairwise disjoint petals (the output of the homogeneous reading, Prop. 4.4),
`Ż = {ż_a | a ∈ J}` the name of the set of their profiles, `T` a countable set of coordinates,
`B' ⊆ 2^T × 2^P` Borel and `Ḃ = borelNameP T B'` the name of the Borel set of profiles read from
`B'`, and `ε > 0`.  Then

    ‖ν(Ḃ) > ε‖ ≤ ⨆ a ∈ J, ‖ż_a ∈ Ḃ‖   (= ‖Ḃ ∩ Ż ≠ ∅‖),

i.e. no condition can force "`ν(Ḃ) > ε` and `Ḃ ∩ Ż = ∅`".  Since (by the Borel reading of codes)
every name for a Borel set of profiles is of this form for a countable `T`, this is
`⊩ ν*(Ż) = 1`. -/
theorem fullness (hB' : MeasurableSet B') {A : Type} {J : Set A} (hJ : ¬ J.Countable)
    {π : A → ℕ → ι} (hπ : ∀ a, Function.Injective (π a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b)))
    (hT : T.Countable) {ε : ℝ≥0∞} (hε : 0 < ε) :
    measGtP T hB' ε ≤ ⨆ a : J, (profileName (π a) ∈ᴮ borelNameP T hB') := by
  classical
  by_contra hlt
  set c : randomAlgebra ι := ⨆ a : J, (profileName (π a) ∈ᴮ borelNameP T hB') with hc
  -- the condition `q = ‖ν(Ḃ) > ε‖ ⊓ ‖Ḃ ∩ Ż = ∅‖` would be nonzero
  have hq : ⊥ < measGtP T hB' ε ⊓ cᶜ := by
    rw [bot_lt_iff_ne_bot, ← @sdiff_eq (randomAlgebra ι) _ _ _]
    exact fun h => hlt (sdiff_eq_bot_iff.mp h)
  -- write `q` as a `T'`-event for a countable `T' ⊇ T`
  obtain ⟨Aq, hAq, hAq_eq⟩ := MeasureAlgebra.exists_rep (measGtP T hB' ε ⊓ cᶜ)
  obtain ⟨S, hS, Q₀, hQ₀, hAqS⟩ := exists_countable_restrict_preimage hAq
  have hTT' : T ⊆ T ∪ S := subset_union_left
  have hST' : S ⊆ T ∪ S := subset_union_right
  have hT'c : (T ∪ S).Countable := hT.union hS
  let resT : ((T ∪ S : Set ι) → (ℕ → Bool)) → (T → (ℕ → Bool)) := fun t s => t ⟨s, hTT' s.2⟩
  let resS : ((T ∪ S : Set ι) → (ℕ → Bool)) → (S → (ℕ → Bool)) := fun t s => t ⟨s, hST' s.2⟩
  have hresT : Measurable resT := measurable_pi_lambda _ fun s => measurable_pi_apply _
  have hresS : Measurable resS := measurable_pi_lambda _ fun s => measurable_pi_apply _
  let Q : Set ((T ∪ S : Set ι) → (ℕ → Bool)) := resS ⁻¹' Q₀
  have hQ : MeasurableSet Q := hresS hQ₀
  have hAqQ : Aq = (T ∪ S).domRestrict ⁻¹' Q := by
    rw [hAqS]; rfl
  let B'' : Set (((T ∪ S : Set ι) → (ℕ → Bool)) × (ℕ → (ℕ → Bool))) := {p | (resT p.1, p.2) ∈ B'}
  have hB'' : MeasurableSet B'' := hB'.preimage ((hresT.comp measurable_fst).prodMk measurable_snd)
  -- (i) the trace `Q` has positive measure
  have hQpos : 0 < Measure.infinitePi (fun _ : (T ∪ S : Set ι) => RandomAlgebra.cantorMeasure) Q := by
    rw [← hAq_eq, MeasureAlgebra.bot_lt_iff_meas_pos, MeasureAlgebra.meas_mk, hAqQ,
      μ_random_restrict_preimage _ hQ] at hq
    exact hq
  -- (ii) almost every fibre over `Q` has measure `> ε`, since `q ≤ ‖ν(Ḃ) > ε‖`
  have hfib : ∀ᵐ t ∂(Measure.infinitePi (fun _ : (T ∪ S : Set ι) => RandomAlgebra.cantorMeasure)),
      t ∈ Q → ε ≤ Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
        (Prod.mk t ⁻¹' B'') := by
    have hle : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) Aq hAq ≤ measGtP T hB' ε := by
      rw [hAq_eq]; exact inf_le_left
    unfold measGtP at hle
    rw [MeasureAlgebra.mk_le_mk, MeasureAlgebra.ae_le_set_iff_ae_imp] at hle
    rw [← map_restrict (T ∪ S)]
    refine (ae_map_iff (μ := RandomAlgebra.μ_random ι)
      ((T ∪ S).measurable_restrict (X := fun _ : ι => ℕ → Bool)).aemeasurable
      (p := fun t => t ∈ Q → ε ≤ Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
        (Prod.mk t ⁻¹' B''))
      (hQ.imp (measurableSet_le measurable_const (measurable_measure_prodMk_left hB'')))).mpr ?_
    refine hle.mono fun x hx hxQ => ?_
    have hxA : x ∈ Aq := by rw [hAqQ]; exact hxQ
    exact (hx hxA).le
  -- (iii) a fresh petal meets `B'` inside `q`
  obtain ⟨a, haJ, -, hpos⟩ :=
    exists_fresh_petal_of_fiber_pos hJ hπ hdisj hT'c hQ hB'' hε hQpos hfib
  -- (iv) but `q ⊓ ‖ż_a ∈ Ḃ‖ ≤ cᶜ ⊓ c = ⊥`
  refine absurd (lt_of_lt_of_le hpos ?_) (lt_irrefl _)
  calc _ ≤ cᶜ ⊓ c := inf_le_inf ?_ ?_
    _ = ⊥ := compl_inf_eq_bot
  · refine (MeasureAlgebra.mk_congr hAqQ.symm (ht := hAq)).trans_le ?_
    rw [hAq_eq]
    exact inf_le_right
  · have h1 : (profileName (π a) ∈ᴮ borelNameP T hB') ≤ c :=
      le_iSup (fun a : J => profileName (π a) ∈ᴮ borelNameP T hB') ⟨a, haJ⟩
    rw [mem_borelNameP_profileName] at h1
    exact h1

end Flypitch.Erdos501.RandomForcing
