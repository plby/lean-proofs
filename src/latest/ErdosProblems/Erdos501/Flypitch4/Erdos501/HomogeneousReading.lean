/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

(F4) Homogeneous Borel reading of `𝔠⁺` names for reals (Prop. 4.4 of the paper).
-/
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Logic.Denumerable
import ErdosProblems.Erdos501.Flypitch4.Erdos501.RandomForcing
import ErdosProblems.Erdos501.Flypitch4.Erdos501.DeltaSystem

set_option relaxedAutoImplicit true

/-!
# (F4) Homogeneous reading (Prop. 4.4)

The last part of unit (F4) of the paper's plan ("countable support and homogeneous Borel
reading"): `homogeneous_reading`.

Given `𝔠⁺` names `ẋ_a` (`a : A`, `#A = 𝔠⁺`) for subsets of `ω` in the random-algebra model
`V (randomAlgebra ι)`, together with an injective choice `d a : ι` of a *profile coordinate* for
each name (the block `D_α` of the paper) and a countable set `R₀` of coordinates (the support of
a condition `p`), there are

* a set `J ⊆ A` of indices with `#J = 𝔠⁺`,
* a countable *root* `R ⊇ R₀`,
* pairwise disjoint *petals* `π a : ℕ ↪ ι` (`a ∈ J`) avoiding `R`, with `π a 0 = d a`
  (the paper's `π_α : P → P_α` with `π_α[D] = D_α`; here `P = ℕ`, `D = {0}`), and
* a **single** Borel `F : 2^R × 2^ℕ → 2^ω`

such that every `ẋ_a`, `a ∈ J`, is forced equal to `F(ĝ↾R, ĝ ∘ π a)` — the same Borel function
of the root part `ĝ↾R` of the generic and of the profile `ż_a = ĝ ∘ π a`.

Ingredients: the Borel reading `exists_mkReal_restrict_bv_eq` (Lemma 4.1, `RandomForcing.lean`),
the Δ-system lemma `delta_system_countable` (Theorem 4.3, unit (F3), `DeltaSystem.lean`), and the
count `card_measurable_le_continuum`: there are at most `𝔠` Borel
functions `2^R × 2^ℕ → 2^ω` (the paper's "only `ℵ₁` Borel codes under `CH`"; with `𝔠⁺` names the
pigeonhole needs no `CH`).
-/

open MeasureTheory Set Flypitch bSet Cardinal
open scoped ENNReal Flypitch

namespace Flypitch.Erdos501.RandomForcing

/-! ### Counting Borel sets and Borel functions -/

/-- A countably generated σ-algebra has at most `𝔠` measurable sets. -/
theorem card_measurableSet_le_continuum (Y : Type) [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] : #{s : Set Y | MeasurableSet s} ≤ 𝔠 := by
  have h := MeasurableSpace.cardinal_measurableSet_le_continuum
    (s := MeasurableSpace.countableGeneratingSet Y)
    ((Cardinal.mk_le_aleph0_iff.mpr
      (MeasurableSpace.countable_countableGeneratingSet (α := Y)).to_subtype).trans
      Cardinal.aleph0_le_continuum)
  rwa [MeasurableSpace.generateFrom_countableGeneratingSet] at h

/-- There are at most `𝔠` measurable functions from a countably generated measurable space to
`2^ω` ("only `𝔠` Borel codes"). -/
theorem card_measurable_le_continuum (Y : Type) [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] : #{f : Y → (ℕ → Bool) // Measurable f} ≤ 𝔠 := by
  let Φ : {f : Y → (ℕ → Bool) // Measurable f} → (ℕ → {s : Set Y | MeasurableSet s}) :=
    fun f n => ⟨{y | f.1 y n = true}, measurableSet_bitF f.2 n⟩
  have hΦ : Function.Injective Φ := by
    intro f g h
    apply Subtype.ext
    funext y n
    have h1 : {y | f.1 y n = true} = {y | g.1 y n = true} := congrArg (fun φ => (φ n).1) h
    exact Bool.eq_iff_iff.mpr (Set.ext_iff.mp h1 y)
  calc #{f : Y → (ℕ → Bool) // Measurable f}
      ≤ #(ℕ → {s : Set Y | MeasurableSet s}) := Cardinal.mk_le_of_injective hΦ
    _ = #{s : Set Y | MeasurableSet s} ^ ℵ₀ := by rw [← Cardinal.power_def, Cardinal.mk_nat]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right (card_measurableSet_le_continuum Y)
    _ = 𝔠 := Cardinal.continuum_power_aleph0

/-! ### (F4) Homogeneous reading -/

variable {ι : Type}

/-- **(F4) Homogeneous reading (Prop. 4.4 of the paper).**  Let `ẋ_a` (`a : A`, `#A = 𝔠⁺`) be
names for subsets of `ω` in `V (randomAlgebra ι)`, `d : A ↪ ι` a choice of profile coordinates and
`R₀ ⊆ ι` countable (the support of a condition).  Then there are `J ⊆ A` with `#J = 𝔠⁺`, a
countable root `R ⊇ R₀`, pairwise disjoint petals `π a : ℕ ↪ ι` (`a ∈ J`) avoiding `R` with
`π a 0 = d a`, and a single Borel `F : 2^R × 2^ℕ → 2^ω` with
`⊤ ≤ ẋ_a =ᴮ mkReal (fun ĝ => F (ĝ↾R, ĝ ∘ π a))` for all `a ∈ J`. -/
theorem homogeneous_reading {A : Type} (hA : #A = Order.succ 𝔠) {d : A → ι}
    (hd : Function.Injective d) (xdot : A → bSet (randomAlgebra ι))
    (hx : ∀ a, ⊤ ≤ xdot a ⊆ᴮ omega) {R₀ : Set ι} (hR₀ : R₀.Countable) :
    ∃ (J : Set A) (R : Set ι) (π : A → ℕ → ι)
      (F : (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → (ℕ → Bool)) (hF : Measurable F),
      #J = Order.succ 𝔠 ∧ R.Countable ∧ R₀ ⊆ R ∧
      (∀ a ∈ J, Function.Injective (π a)) ∧ (∀ a ∈ J, π a 0 = d a) ∧
      (∀ a ∈ J, ∀ n, π a n ∉ R) ∧
      (∀ a ∈ J, ∀ b ∈ J, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b))) ∧
      ∀ a ∈ J, ⊤ ≤ xdot a =ᴮ mkReal (fun x => F (R.domRestrict x, fun n => x (π a n)))
        (hF.comp (R.measurable_restrict.prodMk
          (measurable_pi_lambda _ fun n => measurable_pi_apply (π a n)))) := by
  classical
  have hℵ₀ : ℵ₀ ≤ Order.succ 𝔠 := aleph0_le_continuum.trans (Order.le_succ _)
  -- (1) Borel readings with countable supports (Lemma 4.1)
  choose S₀ F₀ hF₀ hS₀ heq using fun a => exists_mkReal_restrict_bv_eq (xdot a) (hx a)
  -- (2) pairwise disjoint countably infinite sets `E a ⊆ ι`, used to pad the petals
  have hAι : #(A × ℕ) ≤ #ι := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_nat, hA,
      Cardinal.mul_eq_left hℵ₀ hℵ₀ Cardinal.aleph0_ne_zero, ← hA]
    exact Cardinal.mk_le_of_injective hd
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hAι
  let E : A → Set ι := fun a => Set.range fun n => e (a, n)
  have hE_inf : ∀ a, (E a).Infinite := fun a =>
    Set.infinite_range_of_injective fun n m h => (Prod.mk.inj (e.injective h)).2
  have hE_disj : ∀ a b, a ≠ b → Disjoint (E a) (E b) := by
    intro a b hab
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ ⟨m, hm⟩
    exact hab (Prod.mk.inj (e.injective hm)).1.symm
  -- (3) the enlarged supports
  let S : A → Set ι := fun a => S₀ a ∪ R₀ ∪ {d a} ∪ E a
  have hS : ∀ a, (S a).Countable := fun a =>
    (((hS₀ a).union hR₀).union (Set.countable_singleton _)).union (Set.countable_range _)
  have hd_mem : ∀ a, d a ∈ S a := fun a => by simp [S]
  have hE_sub : ∀ a, E a ⊆ S a := fun a => Set.subset_union_right
  have hS₀_sub : ∀ a, S₀ a ⊆ S a := fun a s hs => by simp [S, hs]
  -- (4) the Δ-system lemma (F3)
  obtain ⟨J₀, R, hJ₀, hRS, hΔ⟩ := delta_system_countable S hS hA
  have hJ₀ne : J₀.Nonempty := by
    rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hJ₀]
    exact (zero_le.trans_lt (Order.lt_succ 𝔠)).ne'
  obtain ⟨a₀, ha₀⟩ := hJ₀ne
  have hR : R.Countable := (hS a₀).mono (hRS a₀ ha₀)
  have hR₀R : R₀ ⊆ R := by
    have hnt : Nontrivial J₀ := Cardinal.one_lt_iff_nontrivial.mp
      (by rw [hJ₀]; exact one_lt_aleph0.trans_le hℵ₀)
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hnt.exists_pair_ne
    have hab' : a ≠ b := fun h => hab (Subtype.ext h)
    rw [← hΔ a ha b hb hab']
    intro r hr
    exact ⟨by simp [S, hr], by simp [S, hr]⟩
  -- (5) discard the countably many indices whose profile coordinate or padding meets the root
  let bad : Set A := {a | d a ∈ R ∨ (E a ∩ R).Nonempty}
  have hbad : bad.Countable := by
    have h1 : {a | d a ∈ R}.Countable := hR.preimage hd
    have h2 : {a | (E a ∩ R).Nonempty}.Countable := by
      have hsub : {a | (E a ∩ R).Nonempty} ⊆ ⋃ r ∈ R, {a | r ∈ E a} := by
        rintro a ⟨r, hrE, hrR⟩
        exact Set.mem_biUnion hrR hrE
      refine (hR.biUnion fun r _ => ?_).mono hsub
      apply Set.Subsingleton.countable
      intro a ha b hb
      by_contra hab
      exact Set.disjoint_left.mp (hE_disj a b hab) ha hb
    exact (h1.union h2).mono fun a ha => ha
  let J₁ : Set A := J₀ \ bad
  have hJ₁ : #J₁ = Order.succ 𝔠 := by
    apply le_antisymm ((Cardinal.mk_le_mk_of_subset Set.diff_subset).trans hJ₀.le)
    by_contra hlt
    rw [not_le, Order.lt_succ_iff] at hlt
    have h1 : #J₀ ≤ #J₁ + #bad :=
      (Cardinal.mk_le_mk_of_subset (Set.subset_diff_union J₀ bad)).trans (Cardinal.mk_union_le _ _)
    have h2 : #bad ≤ 𝔠 :=
      (Cardinal.mk_le_aleph0_iff.mpr hbad.to_subtype).trans aleph0_le_continuum
    have h3 : #J₀ ≤ 𝔠 :=
      h1.trans ((add_le_add hlt h2).trans (Cardinal.add_eq_self aleph0_le_continuum).le)
    rw [hJ₀] at h3
    exact (Order.lt_succ 𝔠).not_ge h3
  -- (6) for `a ∈ J₁` the petal `S a \ R` is countably infinite and contains `d a`;
  --     enumerate it as `π a : ℕ ≃ S a \ R` with `π a 0 = d a`
  have hpetal : ∀ a, ∃ π : ℕ → ι, a ∈ J₁ →
      Function.Injective π ∧ Set.range π = S a \ R ∧ π 0 = d a := by
    intro a
    by_cases ha : a ∈ J₁
    · have hnotbad : a ∉ bad := ha.2
      have hdR : d a ∉ R := fun h => hnotbad (Or.inl h)
      have hER : Disjoint (E a) R := Set.disjoint_iff_inter_eq_empty.mpr
        (Set.not_nonempty_iff_eq_empty.mp fun h => hnotbad (Or.inr h))
      have hinf : (S a \ R).Infinite :=
        (hE_inf a).mono (Set.subset_diff.mpr ⟨hE_sub a, hER⟩)
      have hcnt : (S a \ R).Countable := (hS a).mono Set.diff_subset
      have : Countable ↥(S a \ R) := hcnt.to_subtype
      have : Infinite ↥(S a \ R) := hinf.to_subtype
      obtain ⟨D⟩ : Nonempty (Denumerable ↥(S a \ R)) :=
        nonempty_denumerable_iff.mpr ⟨inferInstance, inferInstance⟩
      let e' : ℕ ≃ ↥(S a \ R) := (Denumerable.eqv _).symm
      let k : ℕ := e'.symm ⟨d a, hd_mem a, hdR⟩
      refine ⟨fun n => (e' (Equiv.swap 0 k n)).1, fun _ => ⟨?_, ?_, ?_⟩⟩
      · exact Subtype.val_injective.comp (e'.injective.comp (Equiv.swap 0 k).injective)
      · ext y
        constructor
        · rintro ⟨n, rfl⟩
          exact (e' (Equiv.swap 0 k n)).2
        · intro hy
          refine ⟨Equiv.swap 0 k (e'.symm ⟨y, hy⟩), ?_⟩
          simp
      · simp [k]
    · exact ⟨fun _ => d a, fun h => absurd h ha⟩
  choose π hπ using hpetal
  -- (7) glue the readings to the common domain `2^R × 2^ℕ`
  let glue : ∀ a, (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → (S₀ a → (ℕ → Bool)) :=
    fun a tz s => if h : (s : ι) ∈ R then tz.1 ⟨s, h⟩ else tz.2 (Function.invFun (π a) s)
  have hglue : ∀ a, Measurable (glue a) := by
    intro a
    refine measurable_pi_lambda _ fun s => ?_
    by_cases h : (s : ι) ∈ R
    · simp only [glue, h, dite_true]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [glue, h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  let G : ∀ a, (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → (ℕ → Bool) := fun a => F₀ a ∘ glue a
  have hG : ∀ a, Measurable (G a) := fun a => (hF₀ a).comp (hglue a)
  have hGread : ∀ a ∈ J₁, ∀ x : RandomAlgebra.Ω ι,
      G a (R.domRestrict x, fun n => x (π a n)) = F₀ a ((S₀ a).domRestrict x) := by
    intro a ha x
    obtain ⟨-, hπrange, -⟩ := hπ a ha
    show F₀ a (glue a (R.domRestrict x, fun n => x (π a n))) = F₀ a ((S₀ a).domRestrict x)
    congr 1
    funext s
    by_cases h : (s : ι) ∈ R
    · simp [glue, h]
    · simp only [glue, h, dite_false]
      have hs : (s : ι) ∈ Set.range (π a) := by
        rw [hπrange]
        exact ⟨hS₀_sub a s.2, h⟩
      show x (π a (Function.invFun (π a) s)) = x s
      rw [Function.invFun_eq hs]
  have hread : ∀ a ∈ J₁,
      ∀ H : {G : (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → (ℕ → Bool) // Measurable G},
      H = ⟨G a, hG a⟩ →
      ⊤ ≤ xdot a =ᴮ mkReal (fun x => H.1 (R.domRestrict x, fun n => x (π a n)))
        (H.2.comp (R.measurable_restrict.prodMk
          (measurable_pi_lambda _ fun n => measurable_pi_apply (π a n)))) := by
    intro a ha H hH
    subst hH
    dsimp only
    rw [mkReal_congr _ ((hF₀ a).comp (S₀ a).measurable_restrict) (funext (hGread a ha))]
    exact heq a
  -- (8) pigeonhole: there are only `𝔠` Borel functions `2^R × 2^ℕ → 2^ω`
  have : Countable ↥R := hR.to_subtype
  let Codes := {G : (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → (ℕ → Bool) // Measurable G}
  have hCodes : #Codes ≤ 𝔠 := card_measurable_le_continuum _
  obtain ⟨⟨F, hF⟩, J, hJJ₁, hJcard, hJF⟩ := Cardinal.infinite_pigeonhole_set (s := J₁)
    (fun a => (⟨G a, hG a⟩ : Codes)) (Order.succ 𝔠) hJ₁.ge hℵ₀
    (by
      rw [(Cardinal.isRegular_succ aleph0_le_continuum).cof_ord]
      exact hCodes.trans_lt (Order.lt_succ _))
  -- (9) conclusion
  refine ⟨J, R, π, F, hF, ?_, hR, hR₀R, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_antisymm
      ((Cardinal.mk_le_mk_of_subset (hJJ₁.trans Set.diff_subset)).trans hJ₀.le) hJcard
  · exact fun a ha => (hπ a (hJJ₁ ha)).1
  · exact fun a ha => (hπ a (hJJ₁ ha)).2.2
  · intro a ha n hn
    have hmem : π a n ∈ S a \ R := by
      rw [← (hπ a (hJJ₁ ha)).2.1]
      exact ⟨n, rfl⟩
    exact hmem.2 hn
  · intro a ha b hb hab
    rw [(hπ a (hJJ₁ ha)).2.1, (hπ b (hJJ₁ hb)).2.1, Set.disjoint_left]
    rintro y ⟨hya, hyR⟩ ⟨hyb, -⟩
    apply hyR
    rw [← hΔ a (hJJ₁ ha).1 b (hJJ₁ hb).1 hab]
    exact ⟨hya, hyb⟩
  · intro a ha
    exact hread a (hJJ₁ ha) ⟨F, hF⟩ (hJF ha).symm

end Flypitch.Erdos501.RandomForcing
