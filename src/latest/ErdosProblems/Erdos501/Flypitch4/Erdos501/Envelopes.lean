/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The envelopes of the values `A(x_{m,α})` of the given family at the profile test points, read
homogeneously (step S4 of `PLAN.md`): (5.4)–(5.8) of the paper.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.RealReading
import ErdosProblems.Erdos501.Flypitch4.Erdos501.HomogeneousReading
import ErdosProblems.Erdos501.Flypitch4.Erdos501.BinaryExpansion

set_option relaxedAutoImplicit true

/-!
# Homogeneous envelopes (step S4)

Fix a name `A` for a function `Rdot → 𝒫(Rdot)` all of whose values have internal outer measure
`< 1` (the hypothesis of `Sem.erdosProperty Rdot …`, in context `Γ`).  For a coordinate `α : ι`
and `m : ℤ`, the **profile test point** is the internal real `testPoint m α = m + binExp (ĝ α)`
(its law is Lebesgue measure on `[m, m+1)`, `map_profileTest_binExp`).  The value `A(testPoint m α)`
is the name `valSet A (testPoint m α)` (the union of all values, `app_valSet`), and by
`outerMeasureLtOne_reading` it is contained in the name of an open set `⋃ₙ (aₙ, bₙ)` of measure
`< 1`, for sequences of readings `aₙ, bₙ` depending on `(m, α)`.

**Homogeneous reading.**  Coding all these endpoint sequences (for the given `α`) into one name
for a subset of `ω` (`encodeFam`) and applying the homogeneous reading `homogeneous_reading` to
`𝔠⁺` coordinates `α = d a`, we obtain `J` (`#J = 𝔠⁺`), a countable root `R`, pairwise disjoint
petals `π a : ℕ ↪ ι` (`a ∈ J`) with `π a 0 = d a` and a **single** Borel map
`E : 2^R × 2^ℕ → (ℤ → ℕ → ℝ × ℝ)` such that for all `a ∈ J` and `m : ℤ`, on `Γ`:

* `A(testPoint m (d a)) ⊆ᴮ openName (envA E R (π a) m) (envB E R (π a) m)`, where the endpoints
  `envA … n = (E (ĝ↾R, ĝ ∘ π a) m n).1`, `envB … n = (E (ĝ↾R, ĝ ∘ π a) m n).2` are read
  from the root and the petal only (`exists_homogeneous_envelopes`);
* the cover event holds: `λ(⋃ₙ (envA n, envB n)) < 1`.

This is the paper's (5.4)–(5.8): the envelope codes `ċ_{m,a} = F_m(ĝ↾R, ż_a)`.
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice Cardinal
open scoped ENNReal Flypitch Fol Cardinal

namespace Flypitch.Erdos501.RandomForcing

variable {ι : Type}

/-! ### Extensionality for subsets of `Rdot`, in context, and the value of a function name -/

section values

variable {Γ : randomAlgebra ι} {x y : bSet (randomAlgebra ι)}

/-- Γ-version of `mem_le_mem_of_subset_omega` for subsets of `Rdot`. -/
lemma mem_le_mem_of_subset_Rdot' (hx : Γ ≤ x ⊆ᴮ Rdot)
    (h : ∀ f : MeasReal ι, Γ ⊓ (realName f.1 f.2 ∈ᴮ x) ≤ realName f.1 f.2 ∈ᴮ y)
    (z : bSet (randomAlgebra ι)) : Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ y := by
  have h1 : Γ ⊓ z ∈ᴮ x ≤ z ∈ᴮ Rdot := mem_of_mem_subset (inf_le_left.trans hx) inf_le_right
  calc Γ ⊓ z ∈ᴮ x = (Γ ⊓ z ∈ᴮ x) ⊓ z ∈ᴮ Rdot := (inf_eq_left.mpr h1).symm
    _ = (Γ ⊓ z ∈ᴮ x) ⊓ ⨆ f : MeasReal ι, z =ᴮ realName f.1 f.2 := by rw [mem_Rdot]
    _ ≤ ⨆ f : MeasReal ι, (Γ ⊓ realName f.1 f.2 ∈ᴮ x) ⊓ z =ᴮ realName f.1 f.2 := by
        refine bv_cases_right fun f => le_iSup_of_le f ?_
        refine le_inf (le_inf (inf_le_left.trans inf_le_left) ?_) inf_le_right
        exact le_trans (le_inf inf_le_right (inf_le_left.trans inf_le_right)) subst_congr_mem_left
    _ ≤ ⨆ f : MeasReal ι, realName f.1 f.2 ∈ᴮ y ⊓ z =ᴮ realName f.1 f.2 :=
        iSup_mono fun f => inf_le_inf_right _ (h f)
    _ ≤ z ∈ᴮ y := by
        apply iSup_le; intro f
        rw [inf_comm, bv_eq_symm]
        exact subst_congr_mem_left

/-- **Extensionality for subsets of `Rdot`, in context.** -/
theorem eq_of_forall_realName_mem_eq' (hx : Γ ≤ x ⊆ᴮ Rdot) (hy : Γ ≤ y ⊆ᴮ Rdot)
    (h₁ : ∀ f : MeasReal ι, Γ ⊓ (realName f.1 f.2 ∈ᴮ x) ≤ realName f.1 f.2 ∈ᴮ y)
    (h₂ : ∀ f : MeasReal ι, Γ ⊓ (realName f.1 f.2 ∈ᴮ y) ≤ realName f.1 f.2 ∈ᴮ x) :
    Γ ≤ x =ᴮ y := by
  refine le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf; intro z
  apply le_inf
  · rw [← deduction]; exact mem_le_mem_of_subset_Rdot' hx h₁ z
  · rw [← deduction]; exact mem_le_mem_of_subset_Rdot' hy h₂ z

/-- The value of a function name `A : Rdot → 𝒫(Rdot)` at `x`: the name of the union of all
values (a subset of `Rdot`). -/
noncomputable def valSet (A x : bSet (randomAlgebra ι)) : bSet (randomAlgebra ι) :=
  ⟨MeasReal ι, fun f => realName f.1 f.2,
    fun f => ⨆ y : bSet (randomAlgebra ι), Sem.app A x y ⊓ realName f.1 f.2 ∈ᴮ y⟩

variable {A : bSet (randomAlgebra ι)}

@[simp] lemma valSet_type : (valSet A x).type = MeasReal ι := rfl
@[simp] lemma valSet_func (f : (valSet A x).type) : (valSet A x).func f = realName f.1 f.2 := rfl
@[simp] lemma valSet_bval (f : (valSet A x).type) : (valSet A x).bval f =
    ⨆ y : bSet (randomAlgebra ι), Sem.app A x y ⊓ realName f.1 f.2 ∈ᴮ y := rfl

lemma valSet_subset_Rdot : Γ ≤ valSet A x ⊆ᴮ Rdot := by
  rw [subset_unfold]
  refine le_iInf fun f => ?_
  rw [← deduction]
  exact inf_le_right.trans (by simp only [valSet_func]; exact realName_mem_Rdot)

lemma realName_mem_valSet (f : MeasReal ι) :
    (realName f.1 f.2 ∈ᴮ valSet A x) =
      ⨆ y : bSet (randomAlgebra ι), Sem.app A x y ⊓ realName f.1 f.2 ∈ᴮ y := by
  rw [mem_unfold]
  simp only [valSet_bval, valSet_func]
  apply le_antisymm
  · apply iSup_le; intro f'
    refine bv_cases_left fun y => le_iSup_of_le y ?_
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    refine le_trans (le_inf inf_le_right (inf_le_left.trans inf_le_right)) ?_
    rw [bv_eq_symm (x := realName f.1 f.2)]
    exact subst_congr_mem_left
  · refine le_iSup_of_le f ?_
    simp only [bv_eq_refl, inf_top_eq, le_refl]

/-- If `A : Rdot → 𝒫(Rdot)` is a function name and `x ∈ Rdot`, then `valSet A x` is the value
of `A` at `x`, and a subset of `Rdot`. -/
theorem app_valSet (hA : Γ ≤ Sem.isFun Rdot (bv_powerset Rdot) A) (hx : Γ ≤ x ∈ᴮ Rdot) :
    Γ ≤ Sem.app A x (valSet A x) ⊓ (valSet A x ⊆ᴮ Rdot) := by
  refine le_inf ?_ valSet_subset_Rdot
  rw [Sem.isFun] at hA
  have h := bv_mp (hA.trans (iInf_le _ x)) hx
  refine bv_iSup_elim h fun y Γ' h' hy => ?_
  have hyP : Γ' ≤ y ⊆ᴮ Rdot := bv_powerset_spec.mpr (bv_and_left hy)
  have hAy : Γ' ≤ Sem.app A x y := bv_and_left (bv_and_right hy)
  have huniq : Γ' ≤ ⨅ y', Sem.app A x y' ⟹ y' =ᴮ y := bv_and_right (bv_and_right hy)
  have heq : Γ' ≤ y =ᴮ valSet A x := by
    refine eq_of_forall_realName_mem_eq' hyP valSet_subset_Rdot ?_ ?_
    · intro f
      rw [realName_mem_valSet]
      exact le_iSup_of_le y (le_inf (inf_le_left.trans hAy) inf_le_right)
    · intro f
      rw [realName_mem_valSet]
      refine bv_cases_right fun y' => ?_
      have h1 : Γ' ⊓ (Sem.app A x y' ⊓ realName f.1 f.2 ∈ᴮ y') ≤ y' =ᴮ y :=
        bv_mp ((inf_le_left.trans huniq).trans (iInf_le _ y')) (inf_le_right.trans inf_le_left)
      exact (le_inf h1 (inf_le_right.trans inf_le_right)).trans subst_congr_mem_right
  exact app_congr_val heq hAy

end values

/-! ### Coding families of reals `ℤ → ℕ → ℝ × ℝ` as subsets of `ω` -/

/-- A fixed enumeration `ℕ ≃ ℤ × ℕ × ℕ`. -/
noncomputable def famEnum : ℕ ≃ ℤ × ℕ × ℕ := (Denumerable.eqv (ℤ × ℕ × ℕ)).symm

/-- The real selected by an index `(m, n, j)`: the left endpoint for `j = 0`, the right one
otherwise. -/
def famPick (f : ℤ → ℕ → ℝ × ℝ) (i : ℤ × ℕ × ℕ) : ℝ :=
  if i.2.2 = 0 then (f i.1 i.2.1).1 else (f i.1 i.2.1).2

lemma measurable_famPick (i : ℤ × ℕ × ℕ) : Measurable fun f : ℤ → ℕ → ℝ × ℝ => famPick f i := by
  unfold famPick
  split_ifs
  · exact measurable_fst.comp ((measurable_pi_apply i.2.1).comp (measurable_pi_apply i.1))
  · exact measurable_snd.comp ((measurable_pi_apply i.2.1).comp (measurable_pi_apply i.1))

/-- Coding of a family `f : ℤ → ℕ → ℝ × ℝ` of pairs of reals as one subset of `ω`. -/
noncomputable def encodeFam (f : ℤ → ℕ → ℝ × ℝ) : ℕ → Bool :=
  codeP fun k => code (famPick f (famEnum k))

/-- Decoding of a subset of `ω` as a family `ℤ → ℕ → ℝ × ℝ`. -/
noncomputable def decodeFam (c : ℕ → Bool) : ℤ → ℕ → ℝ × ℝ := fun m n =>
  (decode (decodeP c (famEnum.symm (m, n, 0))), decode (decodeP c (famEnum.symm (m, n, 1))))

lemma measurable_encodeFam : Measurable encodeFam :=
  measurable_codeP.comp (measurable_pi_lambda _ fun _ => measurable_code.comp (measurable_famPick _))

lemma measurable_decodeFam : Measurable decodeFam := by
  refine measurable_pi_lambda _ fun m => measurable_pi_lambda _ fun n => Measurable.prodMk ?_ ?_
  · exact measurable_decode.comp ((measurable_pi_apply _).comp measurable_decodeP)
  · exact measurable_decode.comp ((measurable_pi_apply _).comp measurable_decodeP)

@[simp] lemma decodeFam_encodeFam (f : ℤ → ℕ → ℝ × ℝ) : decodeFam (encodeFam f) = f := by
  funext m n
  simp only [decodeFam, encodeFam, decodeP_codeP, Equiv.apply_symm_apply, famPick, decode_code,
    if_true, one_ne_zero, if_false]

/-! ### The profile test points and the homogeneous envelope data -/

/-- The profile test point `m + binExp (ĝ α)`, as an internal real. -/
noncomputable def testPoint (m : ℤ) (α : ι) : bSet (randomAlgebra ι) :=
  realName (fun x => (m : ℝ) + ZFCCore.binExp (x α))
    (measurable_const.add (ZFCCore.measurable_binExp.comp (measurable_pi_apply α)))

lemma testPoint_mem_Rdot {Γ : randomAlgebra ι} (m : ℤ) (α : ι) : Γ ≤ testPoint m α ∈ᴮ Rdot :=
  realName_mem_Rdot

/-- The homogeneous envelope endpoints read from the root `R` and the petal `π`. -/
noncomputable def envA {R : Set ι} (E : (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → ℤ → ℕ → ℝ × ℝ)
    (hE : Measurable E) (π : ℕ → ι) (m : ℤ) (n : ℕ) : MeasReal ι :=
  ⟨fun x => (E (R.domRestrict x, fun k => x (π k)) m n).1,
    measurable_fst.comp (((measurable_pi_apply n).comp ((measurable_pi_apply m).comp hE)).comp
      (R.measurable_restrict.prodMk (measurable_pi_lambda _ fun k => measurable_pi_apply (π k))))⟩

noncomputable def envB {R : Set ι} (E : (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → ℤ → ℕ → ℝ × ℝ)
    (hE : Measurable E) (π : ℕ → ι) (m : ℤ) (n : ℕ) : MeasReal ι :=
  ⟨fun x => (E (R.domRestrict x, fun k => x (π k)) m n).2,
    measurable_snd.comp (((measurable_pi_apply n).comp ((measurable_pi_apply m).comp hE)).comp
      (R.measurable_restrict.prodMk (measurable_pi_lambda _ fun k => measurable_pi_apply (π k))))⟩

/-- Events of Boolean value `⊤` hold almost everywhere. -/
lemma ae_of_mk_eq_top {s : Set (RandomAlgebra.Ω ι)} {hs : MeasurableSet s}
    (h : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) s hs = ⊤) :
    ∀ᵐ x ∂(RandomAlgebra.μ_random ι), x ∈ s := by
  rw [MeasureAlgebra.top_def, MeasureAlgebra.mk_eq_mk] at h
  exact ae_eq_univ.mp h

/-- Names of open sets with a.e. equal endpoint sequences are equal. -/
lemma openName_congr_ae {a b a' b' : ℕ → MeasReal ι}
    (h : ∀ᵐ x ∂(RandomAlgebra.μ_random ι), ∀ n, (a n).1 x = (a' n).1 x ∧ (b n).1 x = (b' n).1 x) :
    ⊤ ≤ openName a b =ᴮ openName a' b' := by
  refine eq_of_forall_realName_mem_eq' openName_subset_Rdot openName_subset_Rdot ?_ ?_
  · intro f
    rw [top_inf_eq, mem_openName_realName, mem_openName_realName, MeasureAlgebra.mk_le_mk,
      MeasureAlgebra.ae_le_set_iff_ae_imp]
    filter_upwards [h] with x hx hf
    obtain ⟨n, h1, h2⟩ := hf
    exact ⟨n, (hx n).1 ▸ h1, (hx n).2 ▸ h2⟩
  · intro f
    rw [top_inf_eq, mem_openName_realName, mem_openName_realName, MeasureAlgebra.mk_le_mk,
      MeasureAlgebra.ae_le_set_iff_ae_imp]
    filter_upwards [h] with x hx hf
    obtain ⟨n, h1, h2⟩ := hf
    exact ⟨n, (hx n).1.symm ▸ h1, (hx n).2.symm ▸ h2⟩

/-- **Homogeneous envelopes (5.4)–(5.8).**  Given a function name `A : Rdot → 𝒫(Rdot)` all of
whose values have internal outer measure `< 1` (on `Γ`), `𝔠⁺` coordinates `d a` and a countable
`R₀`, there are `J` with `#J = 𝔠⁺`, a countable root `R ⊇ R₀`, pairwise disjoint petals
`π a : ℕ ↪ ι` (`a ∈ J`) avoiding `R` with `π a 0 = d a`, and one Borel
`E : 2^R × 2^ℕ → (ℤ → ℕ → ℝ × ℝ)` such that for all `a ∈ J` and `m : ℤ`, on `Γ`, the value
`A(testPoint m (d a))` is contained in the open set with endpoints `E(ĝ↾R, ĝ ∘ π a) m`, and the
cover event holds for these endpoints (so the open set has Lebesgue measure `< 1`). -/
theorem exists_homogeneous_envelopes {Γ : randomAlgebra ι} {A : bSet (randomAlgebra ι)}
    (hA1 : Γ ≤ Sem.isFun Rdot (bv_powerset Rdot) A)
    (hA2 : Γ ≤ ⨅ x : bSet (randomAlgebra ι), x ∈ᴮ Rdot ⟹ ⨅ Ax : bSet (randomAlgebra ι),
      Sem.app A x Ax ⟹ Sem.outerMeasureLtOne Rdot plusDot ltDot zeroDot oneDot Ax)
    {D : Type} (hD : #D = Order.succ 𝔠) {d : D → ι} (hd : Function.Injective d)
    {R₀ : Set ι} (hR₀ : R₀.Countable) :
    ∃ (J : Set D) (R : Set ι) (π : D → ℕ → ι)
      (E : (R → (ℕ → Bool)) × (ℕ → (ℕ → Bool)) → ℤ → ℕ → ℝ × ℝ) (hE : Measurable E),
      #J = Order.succ 𝔠 ∧ R.Countable ∧ R₀ ⊆ R ∧
      (∀ a ∈ J, Function.Injective (π a)) ∧ (∀ a ∈ J, π a 0 = d a) ∧
      (∀ a ∈ J, ∀ n, π a n ∉ R) ∧
      (∀ a ∈ J, ∀ b ∈ J, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b))) ∧
      ∀ a ∈ J, ∀ m : ℤ,
        Γ ≤ valSet A (testPoint m (d a)) ⊆ᴮ openName (envA E hE (π a) m) (envB E hE (π a) m) ∧
        Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
          (coverEvent (seqFun (envA E hE (π a) m)) (seqFun (envB E hE (π a) m)))
          (measurableSet_coverEvent (measurable_seqFun _) (measurable_seqFun _)) := by
  classical
  -- (1) for each coordinate `d a` and `m`, an open cover of `A(testPoint m (d a))` of measure `< 1`
  have hcov : ∀ (a : D) (m : ℤ), ∃ as bs : ℕ → MeasReal ι,
      Γ ≤ MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (coverEvent (seqFun as) (seqFun bs))
        (measurableSet_coverEvent (measurable_seqFun as) (measurable_seqFun bs)) ∧
      Γ ≤ valSet A (testPoint m (d a)) ⊆ᴮ openName as bs := by
    intro a m
    have hval := app_valSet hA1 (testPoint_mem_Rdot m (d a))
    have h1 := bv_mp (bv_mp (hA2.trans (iInf_le _ (testPoint m (d a)))) (testPoint_mem_Rdot m (d a))
      |>.trans (iInf_le _ (valSet A (testPoint m (d a))))) (bv_and_left hval)
    exact outerMeasureLtOne_reading (bv_and_right hval) h1
  choose as bs hcovE hsub using hcov
  -- (2) code the endpoint sequences of the coordinate `d a` as one name for a subset of `ω`
  let fam : D → RandomAlgebra.Ω ι → ℤ → ℕ → ℝ × ℝ := fun a x m n => ((as a m n).1 x, (bs a m n).1 x)
  have hfam : ∀ a, Measurable (fam a) := fun a =>
    measurable_pi_lambda _ fun m => measurable_pi_lambda _ fun n =>
      (as a m n).2.prodMk (bs a m n).2
  let codeName : D → bSet (randomAlgebra ι) := fun a =>
    mkReal (fun x => encodeFam (fam a x)) (measurable_encodeFam.comp (hfam a))
  -- (3) the homogeneous reading of these `𝔠⁺` names
  obtain ⟨J, R, π, F, hF, hJ, hR, hR₀R, hπinj, hπ0, hπR, hdisj, hread⟩ :=
    homogeneous_reading hD hd codeName (fun a => mkReal_definite _) hR₀
  refine ⟨J, R, π, fun p => decodeFam (F p), measurable_decodeFam.comp hF, hJ, hR, hR₀R, hπinj,
    hπ0, hπR, hdisj, fun a ha m => ?_⟩
  -- (4) for `a ∈ J`, the endpoint sequences agree a.e. with the homogeneous reading
  have hae : ∀ᵐ x ∂(RandomAlgebra.μ_random ι), ∀ m n,
      (as a m n).1 x = (envA (fun p => decodeFam (F p)) (measurable_decodeFam.comp hF) (π a) m n).1 x ∧
      (bs a m n).1 x = (envB (fun p => decodeFam (F p)) (measurable_decodeFam.comp hF) (π a) m n).1 x := by
    have h := hread a ha
    rw [bv_eq_mkReal] at h
    have h' := ae_of_mk_eq_top (top_le_iff.mp h)
    filter_upwards [h'] with x hx m n
    have hx' : encodeFam (fam a x) = F (R.domRestrict x, fun n => x (π a n)) := hx
    simp only [envA, envB]
    rw [← hx', decodeFam_encodeFam]
    exact ⟨rfl, rfl⟩
  have hae' : ∀ᵐ x ∂(RandomAlgebra.μ_random ι), ∀ n,
      (as a m n).1 x = (envA (fun p => decodeFam (F p)) (measurable_decodeFam.comp hF) (π a) m n).1 x ∧
      (bs a m n).1 x = (envB (fun p => decodeFam (F p)) (measurable_decodeFam.comp hF) (π a) m n).1 x := by
    filter_upwards [hae] with x hx
    exact hx m
  refine ⟨?_, ?_⟩
  · -- transport `⊆ᴮ` along the equality of the open-set names
    have heq := openName_congr_ae hae'
    exact (le_inf (hsub a m) (le_top.trans heq)).trans subst_congr_subset_right
  · -- the cover events agree a.e.
    refine (hcovE a m).trans (MeasureAlgebra.mk_le_mk.mpr ?_)
    rw [MeasureAlgebra.ae_le_set_iff_ae_imp]
    filter_upwards [hae'] with x hx hcx
    exact (coverEvent_congr (fun n => (hx n).1) (fun n => (hx n).2)).mp hcx

end Flypitch.Erdos501.RandomForcing
