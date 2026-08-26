/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Reading internal reals, internal sequences of reals and the internal outer-measure hypothesis of
`Erdos501_f` as ground-model Borel data (step S3 of `PLAN.md`).
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.InternalReals

set_option relaxedAutoImplicit true

/-!
# Reading internal reals, sequences and covers (step S3)

The Erdős property `Sem.erdosProperty Rdot plusDot ltDot zeroDot oneDot` (`Semantics.lean`) is
stated for names: its hypothesis says that for every `x ∈ Rdot` the value `A(x)` is bounded and
has *internal* outer measure `< 1` (`Sem.outerMeasureLtOne Rdot … (A x)`: internal sequences
`a, b, s : ω → Rdot` of endpoints and partial sums).  To use it, this file reads such internal
data as ground-model Borel data:

* **Every internal real is canonical** (`realName_of_mem_Rdot`): if `Γ ≤ y ∈ᴮ Rdot` then
  `Γ ≤ y =ᴮ realName g` for a *single* measurable `g : Ω ι → ℝ` (a Γ-version of Theorem 4.1
  followed by decoding of cut codes, `decode`); no mixing is needed since the Borel reading of a
  name for a subset of `ω` is built bit by bit.
* **Internal sequences of reals are sequences of readings** (`exists_seq_of_isFun`): a name `F`
  with `Γ ≤ Sem.isFun ω Rdot F` has values `F(ň) =ᴮ realName (f n)`, `f : ℕ → MeasReal ι`, on `Γ`.
* **The maximum principle** for the existential quantifiers of `Sem.outerMeasureLtOne`
  (`outerMeasureLtOne_elim`), obtained from Flypitch's `maximum_principle` and the fact that
  every `Sem.*` predicate is the realization of a formula, hence extensional (`B_ext_realize`).
* **The reading of the outer-measure hypothesis** (`outerMeasureLtOne_reading`): if
  `Γ ≤ Sem.outerMeasureLtOne Rdot plusDot ltDot zeroDot oneDot S` (and `S ⊆ᴮ Rdot`), there are
  `a b : ℕ → MeasReal ι` and `r : MeasReal ι` such that, on `Γ`: `aₙ < bₙ` for all `n`,
  `∑_{n<N} (bₙ - aₙ) ≤ r < 1` for all `N`, and `S ⊆ᴮ openName a b`, where `openName a b` is the
  name of the open set `⋃ₙ (aₙ(ĝ), bₙ(ĝ))` of the extension.  In particular (ground model)
  `λ(⋃ₙ (aₙ x, bₙ x)) ≤ r x < 1` for a.e. `x ∈ Γ` (`volume_iUnion_Ioo_le`).
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice
open scoped ENNReal Flypitch Fol

namespace Flypitch.Erdos501.RandomForcing

variable {ι : Type}

/-! ### Extensionality for subsets of `ω`, in context -/

section extensionality

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Γ-version of `mem_le_mem_of_subset_omega`. -/
lemma mem_le_mem_of_subset_omega' {Γ : 𝔹} {x y : bSet 𝔹} (hx : Γ ≤ x ⊆ᴮ omega)
    (h : ∀ n : ℕ, Γ ⊓ (of_nat n ∈ᴮ x) ≤ of_nat n ∈ᴮ y) (z : bSet 𝔹) :
    Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ y := by
  have h1 : Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ omega := mem_of_mem_subset (inf_le_left.trans hx) inf_le_right
  calc Γ ⊓ z ∈ᴮ x = (Γ ⊓ z ∈ᴮ x) ⊓ z ∈ᴮ omega := (inf_eq_left.mpr h1).symm
    _ = (Γ ⊓ z ∈ᴮ x) ⊓ ⨆ n : ℕ, z =ᴮ of_nat n := by rw [mem_omega_eq]
    _ ≤ ⨆ n : ℕ, (Γ ⊓ of_nat n ∈ᴮ x) ⊓ z =ᴮ of_nat n := by
        refine bv_cases_right fun n => le_iSup_of_le n ?_
        refine le_inf (le_inf (inf_le_left.trans inf_le_left) ?_) inf_le_right
        exact le_trans (le_inf inf_le_right (inf_le_left.trans inf_le_right)) subst_congr_mem_left
    _ ≤ ⨆ n : ℕ, of_nat n ∈ᴮ y ⊓ z =ᴮ of_nat n := iSup_mono fun n => inf_le_inf_right _ (h n)
    _ ≤ z ∈ᴮ y := by
        apply iSup_le; intro n
        rw [inf_comm, bv_eq_symm]
        exact subst_congr_mem_left

/-- **Extensionality for subsets of `ω`, in context**: two names for subsets of `ω` with the same
natural numbers as elements (on `Γ`) are equal on `Γ`. -/
theorem eq_of_forall_of_nat_mem_eq' {Γ : 𝔹} {x y : bSet 𝔹} (hx : Γ ≤ x ⊆ᴮ omega)
    (hy : Γ ≤ y ⊆ᴮ omega) (h₁ : ∀ n : ℕ, Γ ⊓ (of_nat n ∈ᴮ x) ≤ of_nat n ∈ᴮ y)
    (h₂ : ∀ n : ℕ, Γ ⊓ (of_nat n ∈ᴮ y) ≤ of_nat n ∈ᴮ x) : Γ ≤ x =ᴮ y := by
  refine le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf; intro z
  apply le_inf
  · rw [← deduction]; exact mem_le_mem_of_subset_omega' hx h₁ z
  · rw [← deduction]; exact mem_le_mem_of_subset_omega' hy h₂ z

/-- The elements of `set_of_indicator (u := omega) χ`. -/
lemma of_nat_mem_set_of_indicator_omega (χ : (omega : bSet 𝔹).type → 𝔹) (n : ℕ) :
    (of_nat n ∈ᴮ @set_of_indicator 𝔹 _ omega χ) = χ (ULift.up n) := by
  rw [mem_unfold]
  apply le_antisymm
  · apply iSup_le; intro k
    change χ k ⊓ (of_nat n =ᴮ of_nat k.down) ≤ χ (ULift.up n)
    by_cases hk : n = k.down
    · subst hk; exact inf_le_left
    · rw [of_nat_inj' hk, inf_bot_eq]; exact bot_le
  · apply le_iSup_of_le (ULift.up n)
    change χ (ULift.up n) ≤ χ (ULift.up n) ⊓ (of_nat n =ᴮ of_nat n)
    rw [bv_eq_refl, inf_top_eq]

end extensionality

/-! ### Borel reading of names for subsets of `ω`, in context -/

/-- **Theorem 4.1 in context**: for every name `y`, there is a Borel `G : Ω ι → 2^ω` with
`‖y ⊆ ω‖ ≤ ‖y = mkReal G‖`. -/
theorem exists_mkReal_of_subset_omega (y : bSet (randomAlgebra ι)) :
    ∃ (G : RandomAlgebra.Ω ι → (ℕ → Bool)) (hG : Measurable G),
      (y ⊆ᴮ omega) ≤ y =ᴮ mkReal G hG := by
  classical
  choose A hA hAeq using fun n : ℕ => MeasureAlgebra.exists_rep (of_nat n ∈ᴮ y)
  let G : RandomAlgebra.Ω ι → ℕ → Bool := fun x n => if x ∈ A n then true else false
  have hG : Measurable G :=
    measurable_pi_iff.mpr fun n => Measurable.ite (hA n) measurable_const measurable_const
  refine ⟨G, hG, ?_⟩
  have hmem : ∀ n, (of_nat n ∈ᴮ mkReal G hG) = of_nat n ∈ᴮ y := by
    intro n
    rw [mem_mkReal, ← hAeq n]
    congr 1
    ext x
    simp [G]
  refine eq_of_forall_of_nat_mem_eq' le_rfl (mkReal_definite hG) ?_ ?_
  · intro n; rw [hmem n]; exact inf_le_right
  · intro n; rw [hmem n]; exact inf_le_right

/-! ### Decoding cut codes -/

/-- Decoding of a cut code: the real whose cut is `{qₙ | c n = 1}` (junk if that is not a proper
cut). -/
noncomputable def decode : (ℕ → Bool) → ℝ := cutReal (fun n => {c : ℕ → Bool | c n = true})

lemma measurable_decode : Measurable decode :=
  measurable_cutReal fun n =>
    (measurable_pi_apply (X := fun _ : ℕ => Bool) n) (measurableSet_singleton true)

/-- `decode` inverts `code`. -/
lemma decode_code (r : ℝ) : decode (code r) = r := by
  have h1 : ∃ n, code r ∈ {c : ℕ → Bool | c n = true} := by
    obtain ⟨s, hs⟩ := exists_rat_lt r
    refine ⟨ratEnum.symm s, ?_⟩
    simp only [mem_setOf_eq, code_apply_eq_true_iff, Equiv.apply_symm_apply]; exact hs
  have h2 : ∃ M : ℝ, ∀ n, code r ∈ {c : ℕ → Bool | c n = true} → q n ≤ M :=
    ⟨r, fun n hn => ((code_apply_eq_true_iff r n).mp hn).le⟩
  apply le_antisymm
  · exact cutReal_le h1 fun n hn => (code_apply_eq_true_iff r n).mp hn
  · exact le_cutReal h1 h2 fun n hn => (code_apply_eq_true_iff r n).mpr hn

/-- **Every internal real is canonical**: if `Γ ≤ y ∈ᴮ Rdot` then `Γ ≤ y =ᴮ realName g` for a
single measurable `g`. -/
theorem realName_of_mem_Rdot {Γ : randomAlgebra ι} {y : bSet (randomAlgebra ι)}
    (h : Γ ≤ y ∈ᴮ Rdot) : ∃ (g : RandomAlgebra.Ω ι → ℝ) (hg : Measurable g),
      Γ ≤ y =ᴮ realName g hg := by
  obtain ⟨G, hG, hyG⟩ := exists_mkReal_of_subset_omega y
  refine ⟨decode ∘ G, measurable_decode.comp hG, ?_⟩
  refine mem_Rdot_elim h fun f Γ' h' hyf => ?_
  -- on `Γ'`, `y = realName f`, hence `mkReal G = realName f` and `G = code ∘ f` a.e.
  have hyω : Γ' ≤ y ⊆ᴮ omega :=
    (le_inf (realName_definite (Γ := Γ')) hyf).trans subst_congr_subset_left
  have h1 : Γ' ≤ y =ᴮ mkReal G hG := hyω.trans hyG
  have h2 : Γ' ≤ mkReal G hG =ᴮ realName f.1 f.2 := by
    have := le_inf h1 hyf
    rw [bv_eq_symm (x := y) (y := mkReal G hG)] at this
    exact this.trans bv_eq_trans
  rw [realName, bv_eq_mkReal] at h2
  have h3 : Γ' ≤ mkReal G hG =ᴮ realName (decode ∘ G) (measurable_decode.comp hG) := by
    rw [realName, bv_eq_mkReal]
    refine mk_le_of_forall h2 fun w hw => ?_
    simp only [mem_setOf_eq, Function.comp] at hw ⊢
    rw [hw, decode_code]
  exact (le_inf h1 h3).trans bv_eq_trans

/-! ### Names for functions `ω → Rdot` -/

section functions

variable {Γ : randomAlgebra ι} {F n n' u u' D C : bSet (randomAlgebra ι)}

/-- Congruence of `Sem.app` in the argument. -/
lemma app_congr_arg (h1 : Γ ≤ n' =ᴮ n) (h2 : Γ ≤ Sem.app F n' u) : Γ ≤ Sem.app F n u := by
  rw [Sem.app] at h2 ⊢
  have hp : Γ ≤ pair n' u =ᴮ pair n u := h1.trans subst_congr_pair_left
  exact (le_inf hp h2).trans subst_congr_mem_left

/-- Congruence of `Sem.app` in the value. -/
lemma app_congr_val (h1 : Γ ≤ u =ᴮ u') (h2 : Γ ≤ Sem.app F n u) : Γ ≤ Sem.app F n u' := by
  rw [Sem.app] at h2 ⊢
  have hp : Γ ≤ pair n u =ᴮ pair n u' := h1.trans subst_congr_pair_right
  exact (le_inf hp h2).trans subst_congr_mem_left

/-- Single-valuedness of a function name. -/
lemma isFun_unique (hF : Γ ≤ Sem.isFun D C F) (hn : Γ ≤ n ∈ᴮ D) (h1 : Γ ≤ Sem.app F n u)
    (h2 : Γ ≤ Sem.app F n u') : Γ ≤ u =ᴮ u' := by
  rw [Sem.isFun] at hF
  have h := bv_mp (hF.trans (iInf_le _ n)) hn
  refine (le_inf le_rfl h).trans (bv_cases_right fun y => ?_)
  have hy1 : Γ ⊓ (y ∈ᴮ C ⊓ (Sem.app F n y ⊓ ⨅ y', Sem.app F n y' ⟹ y' =ᴮ y)) ≤ u =ᴮ y :=
    bv_mp ((inf_le_right.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ u))
      (inf_le_left.trans h1)
  have hy2 : Γ ⊓ (y ∈ᴮ C ⊓ (Sem.app F n y ⊓ ⨅ y', Sem.app F n y' ⟹ y' =ᴮ y)) ≤ u' =ᴮ y :=
    bv_mp ((inf_le_right.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ u'))
      (inf_le_left.trans h2)
  have := le_inf hy1 hy2
  rw [bv_eq_symm (x := u') (y := y)] at this
  exact this.trans bv_eq_trans

/-- The value of a function name `F` at `n`, as the name of the union of all values: a subset of
`ω` whenever the value is one. -/
noncomputable def valName (F n : bSet (randomAlgebra ι)) : bSet (randomAlgebra ι) :=
  @set_of_indicator (randomAlgebra ι) _ omega
    (fun m => ⨆ y : bSet (randomAlgebra ι), Sem.app F n y ⊓ of_nat m.down ∈ᴮ y)

lemma valName_subset_omega : Γ ≤ valName F n ⊆ᴮ omega :=
  set_of_indicator_subset fun _ => le_top

lemma of_nat_mem_valName (m : ℕ) :
    (of_nat m ∈ᴮ valName F n) = ⨆ y : bSet (randomAlgebra ι), Sem.app F n y ⊓ of_nat m ∈ᴮ y :=
  of_nat_mem_set_of_indicator_omega _ m

/-- If `F : ω → Rdot` is a function name then `valName F ň` is its value at `ň`, and a real. -/
theorem app_valName (hF : Γ ≤ Sem.isFun omega Rdot F) (k : ℕ) :
    Γ ≤ Sem.app F (of_nat k) (valName F (of_nat k)) ⊓ (valName F (of_nat k) ∈ᴮ Rdot) := by
  rw [Sem.isFun] at hF
  have h := bv_mp (hF.trans (iInf_le _ (of_nat k))) (of_nat_mem_omega (Γ := Γ))
  refine (le_inf le_rfl h).trans (bv_cases_right fun y => ?_)
  -- on `Γ' := Γ ⊓ (y ∈ Rdot ⊓ (F(k) = y ⊓ uniqueness))`, `y = valName F k`
  set Γ' := Γ ⊓ (y ∈ᴮ Rdot ⊓ (Sem.app F (of_nat k) y ⊓
    ⨅ y', Sem.app F (of_nat k) y' ⟹ y' =ᴮ y)) with hΓ'
  have hyR : Γ' ≤ y ∈ᴮ Rdot := inf_le_right.trans inf_le_left
  have hFy : Γ' ≤ Sem.app F (of_nat k) y := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have huniq : Γ' ≤ ⨅ y', Sem.app F (of_nat k) y' ⟹ y' =ᴮ y :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hyω : Γ' ≤ y ⊆ᴮ omega := by
    refine mem_Rdot_elim hyR fun f Γ'' h'' hyf => ?_
    exact (le_inf (realName_definite (Γ := Γ'')) hyf).trans subst_congr_subset_left
  have heq : Γ' ≤ y =ᴮ valName F (of_nat k) := by
    refine eq_of_forall_of_nat_mem_eq' hyω valName_subset_omega ?_ ?_
    · intro m
      rw [of_nat_mem_valName]
      exact le_iSup_of_le y (le_inf (inf_le_left.trans hFy) inf_le_right)
    · intro m
      rw [of_nat_mem_valName]
      refine bv_cases_right fun y' => ?_
      have h1 : Γ' ⊓ (Sem.app F (of_nat k) y' ⊓ of_nat m ∈ᴮ y') ≤ y' =ᴮ y :=
        bv_mp ((inf_le_left.trans huniq).trans (iInf_le _ y')) (inf_le_right.trans inf_le_left)
      exact (le_inf h1 (inf_le_right.trans inf_le_right)).trans subst_congr_mem_right
  exact le_inf (app_congr_val heq hFy) (subst_congr_mem_left' heq hyR)

/-- **Internal sequences of reals are sequences of readings**: if `Γ ≤ Sem.isFun ω Rdot F` then
there is `f : ℕ → MeasReal ι` with `Γ ≤ ‖F(ň) = realName (f n)‖` for all `n`. -/
theorem exists_seq_of_isFun (hF : Γ ≤ Sem.isFun omega Rdot F) :
    ∃ f : ℕ → MeasReal ι, ∀ n, Γ ≤ Sem.app F (of_nat n) (realName (f n).1 (f n).2) := by
  have h : ∀ n : ℕ, ∃ f : MeasReal ι, Γ ≤ Sem.app F (of_nat n) (realName f.1 f.2) := by
    intro n
    have h1 := app_valName hF n
    obtain ⟨g, hg, hvg⟩ := realName_of_mem_Rdot (bv_and_right h1)
    exact ⟨⟨g, hg⟩, app_congr_val hvg (bv_and_left h1)⟩
  choose f hf using h
  exact ⟨f, hf⟩

end functions


/-! ### Extensionality of realizations, and the maximum principle for the outer-measure witnesses -/

section maximum

open Fol

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-- The Boolean realization of a formula is extensional in each free variable. -/
theorem B_ext_realize {n : ℕ} (v : DVec (V β) n) (f : bounded_formula L_ZFC (n + 1)) :
    B_ext (fun a : bSet β => boolean_realize_bounded_formula (DVec.cons a v) f DVec.nil) := by
  intro a a'
  refine le_trans (inf_le_inf_right _ ?_)
    (boolean_realize_bounded_formula_congr ⟨bSet.empty⟩ (DVec.cons a v) (DVec.cons a' v) f DVec.nil)
  refine le_iInf fun m => ?_
  rcases m with ⟨k, hk⟩
  cases k with
  | zero => exact le_rfl
  | succ k =>
    show a =ᴮ a' ≤ (DVec.nth v k _ =ᴮ DVec.nth v k _)
    rw [bv_eq_refl]; exact le_top

/-- The body of `Sem.outerMeasureLtOne`, with the three witnesses as arguments. -/
def Sem.omBody (R plus ltR zero one S a b s : bSet β) : β :=
  Sem.isFun bSet.omega R a ⊓
  (Sem.isFun bSet.omega R b ⊓
  (Sem.isFun bSet.omega R s ⊓
  (Sem.nondegenerate ltR a b ⊓
  (Sem.covers ltR S a b ⊓
  (Sem.app s bSet.empty zero ⊓
  (Sem.partialSums plus a b s ⊓
  Sem.sumsBounded R ltR one s))))))

lemma Sem.outerMeasureLtOne_eq (R plus ltR zero one S : bSet β) :
    Sem.outerMeasureLtOne R plus ltR zero one S =
      ⨆ a : bSet β, ⨆ b : bSet β, ⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s := rfl

/-- The syntactic body of `OuterMeasureLtOneF`, as a function of the levels of `a, b, s`. -/
def omBodyF (R plus lt zero one S : Tm) (a b s : ℕ) : Fm :=
  andsF [
    isFunF omT R (varT a),
    isFunF omT R (varT b),
    isFunF omT R (varT s),
    allIn omT fun n => allF fun u => allF fun v =>
      appF (varT a) (varT n) (varT u) ⟶ appF (varT b) (varT n) (varT v) ⟶ ltF lt (varT u) (varT v),
    allIn S fun y => exIn omT fun n => exF fun u => exF fun v =>
      appF (varT a) (varT n) (varT u) ⋀ appF (varT b) (varT n) (varT v) ⋀
      ltF lt (varT u) (varT y) ⋀ ltF lt (varT y) (varT v),
    appF (varT s) empT zero,
    allIn omT fun n => allF fun m => succF (varT n) (varT m) ⟶
      allF fun u => allF fun v => allF fun w => allF fun w' => allF fun t => allF fun t' =>
        appF (varT a) (varT n) (varT u) ⟶ appF (varT b) (varT n) (varT v) ⟶
        appF (varT s) (varT n) (varT w) ⟶ appF (varT s) (varT m) (varT w') ⟶
        app2F plus (varT w') (varT u) (varT t) ⟶ app2F plus (varT w) (varT v) (varT t') ⟶
        eqF (varT t) (varT t'),
    exIn R fun r => ltF lt (varT r) one ⋀
      allIn omT fun n => allF fun w => appF (varT s) (varT n) (varT w) ⟶ leF lt (varT w) (varT r)
  ]

lemma OuterMeasureLtOneF_eq (R plus lt zero one S : Tm) :
    OuterMeasureLtOneF R plus lt zero one S =
      exF fun a => exF fun b => exF fun s => omBodyF R plus lt zero one S a b s := rfl

/-- The context `[S, one, zero, lt, plus, R]` (innermost first). -/
def omCtx (R plus ltR zero one S : bSet β) : DVec (V β) 6 :=
  DVec.cons S (DVec.cons one (DVec.cons zero (DVec.cons ltR (DVec.cons plus (DVec.cons R DVec.nil)))))

lemma realize_omBody₁ (R plus ltR zero one S a : bSet β) :
    boolean_realize_bounded_formula (DVec.cons a (omCtx R plus ltR zero one S))
      ((exF fun b => exF fun s => omBodyF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) 6 b s) 7)
      DVec.nil =
    ⨆ b : bSet β, ⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s := by
  simp only [omCtx, omBodyF, exF, allF, allIn, exIn, andF, orF, impF, iffF, memF, eqF, varT,
    pairT, omT, empT, ltF, leF, appF, app2F, isFunF, succF, andsF,
    boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_or, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term, DVec.nth, V_forall,
    V_exists, V_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.omBody, Sem.isFun, Sem.nondegenerate, Sem.covers, Sem.partialSums,
    Sem.sumsBounded, Sem.succ, Sem.lt, Sem.le, Sem.app, Sem.app2]

lemma realize_omBody₂ (R plus ltR zero one S a b : bSet β) :
    boolean_realize_bounded_formula (DVec.cons b (DVec.cons a (omCtx R plus ltR zero one S)))
      ((exF fun s => omBodyF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) 6 7 s) 8)
      DVec.nil =
    ⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s := by
  simp only [omCtx, omBodyF, exF, allF, allIn, exIn, andF, orF, impF, iffF, memF, eqF, varT,
    pairT, omT, empT, ltF, leF, appF, app2F, isFunF, succF, andsF,
    boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_or, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term, DVec.nth, V_forall,
    V_exists, V_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.omBody, Sem.isFun, Sem.nondegenerate, Sem.covers, Sem.partialSums,
    Sem.sumsBounded, Sem.succ, Sem.lt, Sem.le, Sem.app, Sem.app2]

lemma realize_omBody₃ (R plus ltR zero one S a b s : bSet β) :
    boolean_realize_bounded_formula
      (DVec.cons s (DVec.cons b (DVec.cons a (omCtx R plus ltR zero one S))))
      (omBodyF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) 6 7 8 9) DVec.nil =
    Sem.omBody R plus ltR zero one S a b s := by
  simp only [omCtx, omBodyF, exF, allF, allIn, exIn, andF, orF, impF, iffF, memF, eqF, varT,
    pairT, omT, empT, ltF, leF, appF, app2F, isFunF, succF, andsF,
    boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_or, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_omega',
    boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term, DVec.nth, V_forall,
    V_exists, V_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.omBody, Sem.isFun, Sem.nondegenerate, Sem.covers, Sem.partialSums,
    Sem.sumsBounded, Sem.succ, Sem.lt, Sem.le, Sem.app, Sem.app2]

/-- **The maximum principle for the witnesses of `Sem.outerMeasureLtOne`**: if
`Γ ≤ Sem.outerMeasureLtOne R plus lt zero one S`, then there are *single* names `a b s` with
`Γ ≤ Sem.omBody R plus lt zero one S a b s`. -/
theorem outerMeasureLtOne_elim {Γ : β} {R plus ltR zero one S : bSet β}
    (h : Γ ≤ Sem.outerMeasureLtOne R plus ltR zero one S) :
    ∃ a b s : bSet β, Γ ≤ Sem.omBody R plus ltR zero one S a b s := by
  rw [Sem.outerMeasureLtOne_eq] at h
  have e₁ : ∀ a : bSet β, (⨆ b : bSet β, ⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s) =
      boolean_realize_bounded_formula (DVec.cons a (omCtx R plus ltR zero one S))
        ((exF fun b => exF fun s =>
          omBodyF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) 6 b s) 7) DVec.nil :=
    fun a => (realize_omBody₁ R plus ltR zero one S a).symm
  obtain ⟨a, ha⟩ := maximum_principle
    (fun a : bSet β => ⨆ b : bSet β, ⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s)
    (by simp only [e₁]; exact B_ext_realize _ _)
  rw [ha] at h
  have e₂ : ∀ b : bSet β, (⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s) =
      boolean_realize_bounded_formula (DVec.cons b (DVec.cons a (omCtx R plus ltR zero one S)))
        ((exF fun s => omBodyF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) 6 7 s) 8)
        DVec.nil :=
    fun b => (realize_omBody₂ R plus ltR zero one S a b).symm
  obtain ⟨b, hb⟩ := maximum_principle
    (fun b : bSet β => ⨆ s : bSet β, Sem.omBody R plus ltR zero one S a b s)
    (by simp only [e₂]; exact B_ext_realize _ _)
  rw [hb] at h
  have e₃ : ∀ s : bSet β, Sem.omBody R plus ltR zero one S a b s =
      boolean_realize_bounded_formula
        (DVec.cons s (DVec.cons b (DVec.cons a (omCtx R plus ltR zero one S))))
        (omBodyF (varT 0) (varT 1) (varT 2) (varT 3) (varT 4) (varT 5) 6 7 8 9) DVec.nil :=
    fun s => (realize_omBody₃ R plus ltR zero one S a b s).symm
  obtain ⟨s, hs⟩ := maximum_principle
    (fun s : bSet β => Sem.omBody R plus ltR zero one S a b s)
    (by simp only [e₃]; exact B_ext_realize _ _)
  rw [hs] at h
  exact ⟨a, b, s, h⟩

end maximum


/-! ### Names for open sets given by sequences of intervals -/

lemma measurableSet_openSet (a b : ℕ → MeasReal ι) {g : RandomAlgebra.Ω ι → ℝ}
    (hg : Measurable g) : MeasurableSet {x | ∃ n, (a n).1 x < g x ∧ g x < (b n).1 x} := by
  have : {x | ∃ n, (a n).1 x < g x ∧ g x < (b n).1 x} =
      ⋃ n, {x | (a n).1 x < g x} ∩ {x | g x < (b n).1 x} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun n => (measurableSet_lt (a n).2 hg).inter (measurableSet_lt hg (b n).2)

/-- The name of the open set `⋃ₙ (aₙ(ĝ), bₙ(ĝ))` of the extension, for sequences of readings
`a b : ℕ → MeasReal ι`: its elements are the canonical names of all reals, `realName g` belonging
to it with Boolean value `[{x | ∃ n, aₙ x < g x < bₙ x}]`. -/
noncomputable def openName (a b : ℕ → MeasReal ι) : bSet (randomAlgebra ι) :=
  ⟨MeasReal ι, fun g => realName g.1 g.2,
    fun g => MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {x | ∃ n, (a n).1 x < g.1 x ∧ g.1 x < (b n).1 x} (measurableSet_openSet a b g.2)⟩

variable {a b : ℕ → MeasReal ι}

@[simp] lemma openName_type : (openName a b).type = MeasReal ι := rfl
@[simp] lemma openName_func (g : (openName a b).type) :
    (openName a b).func g = realName g.1 g.2 := rfl
@[simp] lemma openName_bval (g : (openName a b).type) : (openName a b).bval g =
    MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | ∃ n, (a n).1 x < g.1 x ∧ g.1 x < (b n).1 x}
      (measurableSet_openSet a b g.2) := rfl

/-- `‖realName g ∈ openName a b‖ = [{x | ∃ n, aₙ x < g x < bₙ x}]`. -/
theorem mem_openName_realName {g : RandomAlgebra.Ω ι → ℝ} (hg : Measurable g) :
    (realName g hg ∈ᴮ openName a b) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | ∃ n, (a n).1 x < g x ∧ g x < (b n).1 x}
        (measurableSet_openSet a b hg) := by
  rw [mem_unfold]
  simp only [openName_bval, openName_func]
  apply le_antisymm
  · apply iSup_le; intro g'
    rw [bv_eq_realName, MeasureAlgebra.mk_inf]
    apply mk_mono
    rintro x ⟨⟨n, h1, h2⟩, h3⟩
    simp only [mem_setOf_eq] at h3
    exact ⟨n, h3 ▸ h1, h3 ▸ h2⟩
  · refine le_iSup_of_le ⟨g, hg⟩ ?_
    simp only [bv_eq_refl, inf_top_eq, le_refl]

theorem openName_subset_Rdot {Γ : randomAlgebra ι} : Γ ≤ openName a b ⊆ᴮ Rdot := by
  rw [subset_unfold]
  refine le_iInf fun g => ?_
  rw [← deduction]
  exact inf_le_right.trans (by simp only [openName_func]; exact realName_mem_Rdot)

/-! ### Small facts about `of_nat` and `Sem.succ`, and congruence of `Sem.lt` -/

lemma of_nat_zero_eq : (of_nat 0 : bSet (randomAlgebra ι)) = bSet.empty := by
  show check (PSet.ofNat 0) = bSet.empty
  rw [show PSet.ofNat 0 = ∅ from rfl]
  exact check_empty_eq_empty

lemma mem_of_nat_succ (z : bSet (randomAlgebra ι)) (n : ℕ) :
    (z ∈ᴮ of_nat (n + 1)) = (z ∈ᴮ of_nat n ⊔ z =ᴮ of_nat n) := by
  show z ∈ᴮ check (PSet.insert (PSet.ofNat n) (PSet.ofNat n)) = _
  rw [check_insert]
  show z ∈ᴮ insert (check (PSet.ofNat n)) (check (PSet.ofNat n)) = _
  rw [mem_insert1, sup_comm]

/-- `of_nat (n+1)` is the successor of `of_nat n` in the sense of `Sem.succ`. -/
lemma succ_of_nat {Γ : randomAlgebra ι} (n : ℕ) :
    Γ ≤ Sem.succ (of_nat n : bSet (randomAlgebra ι)) (of_nat (n + 1)) := by
  rw [Sem.succ]
  refine le_iInf fun z => ?_
  rw [mem_of_nat_succ, bihimp_self]
  exact le_top

section ltcongr

variable {Γ : randomAlgebra ι} {x x' y y' : bSet (randomAlgebra ι)}

lemma lt_ltDot_congr_left (h1 : Γ ≤ x =ᴮ x') (h2 : Γ ≤ Sem.lt ltDot x' y) :
    Γ ≤ Sem.lt ltDot x y := by
  rw [Sem.lt] at h2 ⊢
  have hp : Γ ≤ pair x' y =ᴮ pair x y := by
    rw [bv_eq_symm (x := x)] at h1
    exact h1.trans subst_congr_pair_left
  exact (le_inf hp h2).trans subst_congr_mem_left

lemma lt_ltDot_congr_right (h1 : Γ ≤ y =ᴮ y') (h2 : Γ ≤ Sem.lt ltDot x y') :
    Γ ≤ Sem.lt ltDot x y := by
  rw [Sem.lt] at h2 ⊢
  have hp : Γ ≤ pair x y' =ᴮ pair x y := by
    rw [bv_eq_symm (x := y)] at h1
    exact h1.trans subst_congr_pair_right
  exact (le_inf hp h2).trans subst_congr_mem_left

/-- Countably many events, as one event. -/
lemma le_mk_iInter {s : ℕ → Set (RandomAlgebra.Ω ι)} {hs : ∀ n, MeasurableSet (s n)}
    (h : ∀ n, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (s n) (hs n)) :
    Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋂ n, s n) (MeasurableSet.iInter hs) := by
  have e : (⨅ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (s n) (hs n)) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋂ n, s n) (MeasurableSet.iInter hs) :=
    MeasureAlgebra.iInf_mk _ _
  rw [← e]
  exact le_iInf h

end ltcongr


/-! ### Reading the internal outer-measure hypothesis -/

section reading

variable {Γ : randomAlgebra ι}

/-- Elimination of a Boolean existential, in context. -/
lemma bv_iSup_elim {α : Type*} {s : α → randomAlgebra ι} {c : randomAlgebra ι} (h : Γ ≤ ⨆ i, s i)
    (H : ∀ (i : α) (Γ' : randomAlgebra ι), Γ' ≤ Γ → Γ' ≤ s i → Γ' ≤ c) : Γ ≤ c :=
  (le_inf le_rfl h).trans (bv_cases_right fun i => H i _ inf_le_left inf_le_right)

end reading

/-! ### Interval sequences: partial sums, the bound, and the cover event (over any type) -/

section cover

variable {Y : Type*}

/-- The partial sums `∑_{n<N} (bₙ - aₙ)`. -/
noncomputable def partialSum (a b : ℕ → Y → ℝ) (N : ℕ) (y : Y) : ℝ :=
  ∑ n ∈ Finset.range N, (b n y - a n y)

/-- The supremum of the partial sums (junk where unbounded). -/
noncomputable def sumBound (a b : ℕ → Y → ℝ) (y : Y) : ℝ :=
  ⨆ N, partialSum a b N y

/-- The event "the intervals are nondegenerate, the partial sums are bounded by `sumBound < 1`". -/
def coverEvent (a b : ℕ → Y → ℝ) : Set Y :=
  {y | (∀ n, a n y < b n y) ∧ sumBound a b y < 1 ∧ ∀ N, partialSum a b N y ≤ sumBound a b y}

variable [MeasurableSpace Y] {a b : ℕ → Y → ℝ}

lemma measurable_partialSum (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n)) (N : ℕ) :
    Measurable (partialSum a b N) :=
  Finset.measurable_sum _ fun n _ => (hb n).sub (ha n)

lemma measurable_sumBound (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n)) :
    Measurable (sumBound a b) :=
  Measurable.iSup fun N => measurable_partialSum ha hb N

lemma measurableSet_coverEvent (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n)) :
    MeasurableSet (coverEvent a b) := by
  have e : coverEvent a b = (⋂ n, {y | a n y < b n y}) ∩
      ({y | sumBound a b y < 1} ∩ ⋂ N, {y | partialSum a b N y ≤ sumBound a b y}) := by
    ext y; simp [coverEvent]
  rw [e]
  exact (MeasurableSet.iInter fun n => measurableSet_lt (ha n) (hb n)).inter
    ((measurableSet_lt (measurable_sumBound ha hb) measurable_const).inter
      (MeasurableSet.iInter fun N => measurableSet_le (measurable_partialSum ha hb N)
        (measurable_sumBound ha hb)))

omit [MeasurableSpace Y] in
/-- On the cover event, the open set `⋃ₙ (aₙ y, bₙ y)` has Lebesgue measure at most
`sumBound a b y`. -/
theorem volume_iUnion_Ioo_le {y : Y} (hy : y ∈ coverEvent a b) :
    volume (⋃ n, Ioo (a n y) (b n y)) ≤ ENNReal.ofReal (sumBound a b y) := by
  obtain ⟨hlt, _, hle⟩ := hy
  have hnn : ∀ n, 0 ≤ b n y - a n y := fun n => sub_nonneg.mpr (hlt n).le
  have hsumm : Summable fun n => b n y - a n y := summable_of_sum_range_le hnn hle
  calc volume (⋃ n, Ioo (a n y) (b n y))
      ≤ ∑' n, volume (Ioo (a n y) (b n y)) := measure_iUnion_le _
    _ = ∑' n, ENNReal.ofReal (b n y - a n y) := by simp only [Real.volume_Ioo]
    _ = ENNReal.ofReal (∑' n, (b n y - a n y)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hsumm).symm
    _ ≤ ENNReal.ofReal (sumBound a b y) :=
        ENNReal.ofReal_le_ofReal (Real.tsum_le_of_sum_range_le hnn hle)

omit [MeasurableSpace Y] in
/-- On the cover event, the open set `⋃ₙ (aₙ y, bₙ y)` has Lebesgue measure `< 1`. -/
theorem volume_iUnion_Ioo_lt_one {y : Y} (hy : y ∈ coverEvent a b) :
    volume (⋃ n, Ioo (a n y) (b n y)) < 1 :=
  lt_of_le_of_lt (volume_iUnion_Ioo_le hy) (ENNReal.ofReal_lt_one.mpr hy.2.1)

omit [MeasurableSpace Y] in
/-- The cover event only depends on the values of the sequences. -/
lemma coverEvent_congr {a' b' : ℕ → Y → ℝ} {y : Y} (ha : ∀ n, a n y = a' n y)
    (hb : ∀ n, b n y = b' n y) : y ∈ coverEvent a b ↔ y ∈ coverEvent a' b' := by
  have h1 : ∀ N, partialSum a b N y = partialSum a' b' N y := fun N => by
    simp only [partialSum, ha, hb]
  have h2 : sumBound a b y = sumBound a' b' y := by simp only [sumBound, h1]
  simp only [coverEvent, mem_setOf_eq, ha, hb, h1, h2]

end cover

section reading

variable {Γ : randomAlgebra ι}

/-- The underlying functions of a sequence of readings. -/
abbrev seqFun (a : ℕ → MeasReal ι) : ℕ → RandomAlgebra.Ω ι → ℝ := fun n => (a n).1

lemma measurable_seqFun (a : ℕ → MeasReal ι) : ∀ n, Measurable (seqFun a n) := fun n => (a n).2

/-- **Reading the internal outer-measure hypothesis.**  If `Γ ≤ Sem.outerMeasureLtOne Rdot … S`
(and `S ⊆ Rdot`), then there are sequences of readings `a b : ℕ → MeasReal ι` such that, on `Γ`,
the intervals `(aₙ, bₙ)` are nondegenerate with total length `∑ (bₙ - aₙ) ≤ sumBound a b < 1`
(`coverEvent`), and `S ⊆ᴮ openName a b`. -/
theorem outerMeasureLtOne_reading {S : bSet (randomAlgebra ι)} (hS : Γ ≤ S ⊆ᴮ Rdot)
    (h : Γ ≤ Sem.outerMeasureLtOne Rdot plusDot ltDot zeroDot oneDot S) :
    ∃ a b : ℕ → MeasReal ι,
      Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (coverEvent (seqFun a) (seqFun b))
        (measurableSet_coverEvent (measurable_seqFun a) (measurable_seqFun b)) ∧
      Γ ≤ S ⊆ᴮ openName a b := by
  obtain ⟨aN, bN, sN, hbody⟩ := outerMeasureLtOne_elim h
  rw [Sem.omBody] at hbody
  have hfa := bv_and_left hbody
  have hfb := bv_and_left (bv_and_right hbody)
  have hfs := bv_and_left (bv_and_right (bv_and_right hbody))
  have hnd := bv_and_left (bv_and_right (bv_and_right (bv_and_right hbody)))
  have hcov := bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right hbody))))
  have hs0 := bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right hbody)))))
  have hps := bv_and_left (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right hbody))))))
  have hsb := bv_and_right (bv_and_right (bv_and_right (bv_and_right (bv_and_right
    (bv_and_right (bv_and_right hbody))))))
  obtain ⟨a, ha⟩ := exists_seq_of_isFun hfa
  obtain ⟨b, hb⟩ := exists_seq_of_isFun hfb
  obtain ⟨s, hs⟩ := exists_seq_of_isFun hfs
  refine ⟨a, b, ?_, ?_⟩
  · -- the cover event
    -- (i) nondegenerate intervals
    have hlt : ∀ n, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (a n).1 x < (b n).1 x}
        (measurableSet_lt (a n).2 (b n).2) := by
      intro n
      rw [Sem.nondegenerate] at hnd
      have h1 := bv_mp (hnd.trans (iInf_le _ (of_nat n))) of_nat_mem_omega
      have h2 := bv_mp (bv_mp ((h1.trans (iInf_le _ (realName (a n).1 (a n).2))).trans
        (iInf_le _ (realName (b n).1 (b n).2))) (ha n)) (hb n)
      rwa [lt_ltDot_realName] at h2
    -- (ii) the partial-sums recursion: `s 0 = 0`, `s (n+1) + aₙ = s n + bₙ`
    have hs0' : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (s 0).1 x = 0}
        (measurableSet_eq_fun (s 0).2 measurable_const) := by
      have h1 : Γ ≤ Sem.app sN (of_nat 0) zeroDot := by rw [of_nat_zero_eq]; exact hs0
      have h2 := isFun_unique hfs of_nat_mem_omega (hs 0) h1
      rw [zeroDot, bv_eq_realName] at h2
      exact h2
    have hrec : ∀ n, Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {x | (s (n + 1)).1 x + (a n).1 x = (s n).1 x + (b n).1 x}
        (measurableSet_eq_fun ((s (n+1)).2.add (a n).2) ((s n).2.add (b n).2)) := by
      intro n
      rw [Sem.partialSums] at hps
      have h1 := bv_mp (hps.trans (iInf_le _ (of_nat n))) of_nat_mem_omega
      have h2 := bv_mp (h1.trans (iInf_le _ (of_nat (n + 1)))) (succ_of_nat n)
      have h3 := (((((h2.trans (iInf_le _ (realName (a n).1 (a n).2))).trans
        (iInf_le _ (realName (b n).1 (b n).2))).trans
        (iInf_le _ (realName (s n).1 (s n).2))).trans
        (iInf_le _ (realName (s (n + 1)).1 (s (n + 1)).2))).trans
        (iInf_le _ (realName (fun x => (s (n + 1)).1 x + (a n).1 x)
          ((s (n + 1)).2.add (a n).2)))).trans
        (iInf_le _ (realName (fun x => (s n).1 x + (b n).1 x) ((s n).2.add (b n).2)))
      have hp1 : Γ ≤ Sem.app2 plusDot (realName (s (n + 1)).1 (s (n + 1)).2)
          (realName (a n).1 (a n).2)
          (realName (fun x => (s (n + 1)).1 x + (a n).1 x) ((s (n + 1)).2.add (a n).2)) :=
        le_app2_opDot measurable_add (le_top.trans (le_of_eq (bv_eq_refl _).symm))
          (le_top.trans (le_of_eq (bv_eq_refl _).symm)) (le_top.trans (le_of_eq (bv_eq_refl _).symm))
      have hp2 : Γ ≤ Sem.app2 plusDot (realName (s n).1 (s n).2) (realName (b n).1 (b n).2)
          (realName (fun x => (s n).1 x + (b n).1 x) ((s n).2.add (b n).2)) :=
        le_app2_opDot measurable_add (le_top.trans (le_of_eq (bv_eq_refl _).symm))
          (le_top.trans (le_of_eq (bv_eq_refl _).symm)) (le_top.trans (le_of_eq (bv_eq_refl _).symm))
      have h4 := bv_mp (bv_mp (bv_mp (bv_mp (bv_mp (bv_mp h3 (ha n)) (hb n)) (hs n))
        (hs (n + 1))) hp1) hp2
      rw [bv_eq_realName] at h4
      exact h4
    have hsum : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        (⋂ N, {x | (s N).1 x = partialSum (seqFun a) (seqFun b) N x})
        (MeasurableSet.iInter fun N => measurableSet_eq_fun (s N).2
          (measurable_partialSum (measurable_seqFun a) (measurable_seqFun b) N)) := by
      have h1 := le_inf hs0' (le_mk_iInter hrec)
      rw [MeasureAlgebra.mk_inf] at h1
      refine mk_le_of_forall h1 fun x hx => ?_
      simp only [mem_inter_iff, mem_iInter, mem_setOf_eq] at hx ⊢
      obtain ⟨h0, hr⟩ := hx
      intro N
      induction N with
      | zero => simp [partialSum, h0]
      | succ N ih =>
        simp only [partialSum, seqFun, Finset.sum_range_succ] at ih ⊢
        rw [← ih]; linarith [hr N]
    -- (iii) the bound `r < 1` on the partial sums
    have hbdd : Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        {x | BddAbove (range fun N => partialSum (seqFun a) (seqFun b) N x) ∧
          sumBound (seqFun a) (seqFun b) x < 1}
        (measurableSet_setOf_and (measurableSet_bddAbove_range fun N =>
            measurable_partialSum (measurable_seqFun a) (measurable_seqFun b) N)
          (measurableSet_lt (measurable_sumBound (measurable_seqFun a) (measurable_seqFun b))
            measurable_const)) := by
      rw [Sem.sumsBounded] at hsb
      refine bv_iSup_elim hsb fun r' Γ' h' hr' => ?_
      obtain ⟨k, hk, hr'k⟩ := realName_of_mem_Rdot (bv_and_left hr')
      -- `k < 1`
      have hk1 : Γ' ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | k x < 1}
          (measurableSet_lt hk measurable_const) := by
        have h1 : Γ' ≤ Sem.lt ltDot r' oneDot := bv_and_left (bv_and_right hr')
        have h2 : Γ' ≤ Sem.lt ltDot (realName k hk) oneDot := by
          refine lt_ltDot_congr_left ?_ h1
          rw [bv_eq_symm]; exact hr'k
        rw [oneDot, lt_ltDot_realName] at h2
        exact h2
      -- `s n ≤ k` for all `n`
      have hkn : ∀ n, Γ' ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | (s n).1 x ≤ k x}
          (measurableSet_le (s n).2 hk) := by
        intro n
        have h1 : Γ' ≤ ⨅ n', n' ∈ᴮ omega ⟹ ⨅ w, Sem.app sN n' w ⟹ Sem.le ltDot w r' :=
          bv_and_right (bv_and_right hr')
        have h2 := bv_mp (bv_mp (h1.trans (iInf_le _ (of_nat n))) of_nat_mem_omega |>.trans
          (iInf_le _ (realName (s n).1 (s n).2))) (h'.trans (hs n))
        have h3 : Γ' ≤ Sem.le ltDot (realName (s n).1 (s n).2) (realName k hk) :=
          le_ltDot_congr_right (by rw [bv_eq_symm]; exact hr'k) h2
        rw [le_ltDot_realName] at h3
        exact h3
      have h := le_inf (h'.trans hsum) (le_inf hk1 (le_mk_iInter hkn))
      simp only [MeasureAlgebra.mk_inf] at h
      refine mk_le_of_forall h fun x hx => ?_
      simp only [mem_inter_iff, mem_iInter, mem_setOf_eq] at hx ⊢
      obtain ⟨hsumx, hk1x, hknx⟩ := hx
      have hb : BddAbove (range fun N => partialSum (seqFun a) (seqFun b) N x) := by
        refine ⟨k x, ?_⟩
        rintro _ ⟨N, rfl⟩
        show partialSum (seqFun a) (seqFun b) N x ≤ k x
        rw [← hsumx N]; exact hknx N
      refine ⟨hb, lt_of_le_of_lt (ciSup_le fun N => ?_) hk1x⟩
      show partialSum (seqFun a) (seqFun b) N x ≤ k x
      rw [← hsumx N]; exact hknx N
    have h := le_inf (le_mk_iInter hlt) hbdd
    rw [MeasureAlgebra.mk_inf] at h
    refine mk_le_of_forall h fun x hx => ?_
    simp only [mem_inter_iff, mem_iInter, mem_setOf_eq] at hx
    obtain ⟨hltx, hbx, hsx⟩ := hx
    exact ⟨hltx, hsx, fun N => le_ciSup hbx N⟩
  · -- `S ⊆ openName a b`
    rw [subset_unfold']
    refine le_iInf fun y => ?_
    rw [bv_imp_iff]; intro Γ' h' hyS
    have hyR : Γ' ≤ y ∈ᴮ Rdot := mem_of_mem_subset (h'.trans hS) hyS
    obtain ⟨g, hg, hyg⟩ := realName_of_mem_Rdot hyR
    rw [Sem.covers] at hcov
    have h1 := bv_mp ((h'.trans hcov).trans (iInf_le _ y)) hyS
    refine bv_iSup_elim h1 fun n' Γ₂ h₂ hn' => ?_
    have hn'ω : Γ₂ ≤ ⨆ k, n' =ᴮ of_nat k := by rw [← mem_omega_eq]; exact bv_and_left hn'
    refine bv_iSup_elim hn'ω fun k Γ₃ h₃ hnk => ?_
    refine bv_iSup_elim (h₃.trans (bv_and_right hn')) fun u Γ₄ h₄ hu => ?_
    refine bv_iSup_elim hu fun v Γ₅ h₅ huv => ?_
    have H₃ : Γ₅ ≤ Γ₃ := h₅.trans h₄
    have H₂ : Γ₅ ≤ Γ₂ := H₃.trans h₃
    have HΓ : Γ₅ ≤ Γ := (H₂.trans h₂).trans h'
    have hau : Γ₅ ≤ Sem.app aN (of_nat k) u := app_congr_arg (H₃.trans hnk) (bv_and_left huv)
    have hbv : Γ₅ ≤ Sem.app bN (of_nat k) v :=
      app_congr_arg (H₃.trans hnk) (bv_and_left (bv_and_right huv))
    have hu' : Γ₅ ≤ u =ᴮ realName (a k).1 (a k).2 :=
      isFun_unique (HΓ.trans hfa) of_nat_mem_omega hau (HΓ.trans (ha k))
    have hv' : Γ₅ ≤ v =ᴮ realName (b k).1 (b k).2 :=
      isFun_unique (HΓ.trans hfb) of_nat_mem_omega hbv (HΓ.trans (hb k))
    have hyg' : Γ₅ ≤ y =ᴮ realName g hg := (H₂.trans h₂).trans hyg
    have hlt1 : Γ₅ ≤ Sem.lt ltDot (realName (a k).1 (a k).2) (realName g hg) := by
      refine lt_ltDot_congr_left (by rw [bv_eq_symm]; exact hu') ?_
      refine lt_ltDot_congr_right (by rw [bv_eq_symm]; exact hyg') ?_
      exact bv_and_left (bv_and_right (bv_and_right huv))
    have hlt2 : Γ₅ ≤ Sem.lt ltDot (realName g hg) (realName (b k).1 (b k).2) := by
      refine lt_ltDot_congr_left (by rw [bv_eq_symm]; exact hyg') ?_
      refine lt_ltDot_congr_right (by rw [bv_eq_symm]; exact hv') ?_
      exact bv_and_right (bv_and_right (bv_and_right huv))
    rw [lt_ltDot_realName] at hlt1 hlt2
    refine subst_congr_mem_left' (by rw [bv_eq_symm]; exact hyg') ?_
    rw [mem_openName_realName]
    exact mk_le_of_forall₂ hlt1 hlt2 fun x hx1 hx2 => ⟨k, hx1, hx2⟩

end reading

end Flypitch.Erdos501.RandomForcing
