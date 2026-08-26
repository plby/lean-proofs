/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.ProductGadget
import ErdosProblems.Erdos330.Stage

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Concrete CRT gadget wrapper for Erdős Problem 330

This file connects the product-coordinate gadget to the abstract `CRTGadget`
interface used by the stage construction.  The finite set equations and subset
fields are supplied by `ProductGadget`; the remaining input is the cardinality
formula for the translated private slice.
-/

namespace Erdos330

open scoped Pointwise

abbrev NonselectedIndex (P : Finset ℕ) (a : ℕ) := {b // b ∈ P.erase a}

theorem exists_crtProduct_CRTGadget_of_card_formula {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (m : ℕ → ℕ) (M a : ℕ)
    (p0 : ℕ) [NeZero M] [Fact p0.Prime] [NeZero p0]
    (hp0_eq : p0 = m a)
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (hφnat : ∀ n : ℕ, (φ (n : ZMod M)).1 = (n : ZMod p0))
    (ha1 : (φ (a : ZMod M)).1 = α)
    (he : e = affineNormalize p β (φ (a : ZMod M)).2)
    (hDnat :
      ∀ c ∈ P, ∀ n : ℕ,
        (n : ZMod M) ∈ crtProductAllowedFinset M p0 p φ α β →
          (n : ZMod (m c)) ≠ (c : ZMod (m c)))
    (hcard : ∀ h : ZMod p0,
      ((crtProductPstarFinset M p0 p φ (a : ZMod M) β e h).card : ℝ) / (M : ℝ) =
        (1 : ℝ) / (m a : ℝ) *
          (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ))) :
    ∃ h u1 u2 : ZMod p0,
      ∃ G : CRTGadget P m M a (crtProductAllowedFinset M p0 p φ α β),
        G.T = crtProductTFinset M p0 p φ β e data h u1 u2 ∧
        G.Pstar = crtProductPstarFinset M p0 p φ (a : ZMod M) β e h ∧
        G.Tbase = crtProductTbaseFinset M p0 p φ β h u1 u2 := by
  subst p0
  obtain ⟨h, u1, u2, hbase_sub, hT_sub, hP_sub, hpriv_ne, hDbase, hTT, hDT⟩ :=
    exists_crtProduct_gadget_core M (m a) p hp7 hp0_3 hp0_23 φ (a : ZMod M) α β e data
      ha1 he
  have hα : α = (a : ZMod (m a)) := by
    rw [← ha1]
    exact hφnat a
  refine ⟨h, u1, u2, ?_⟩
  refine ⟨{
    T := crtProductTFinset M (m a) p φ β e data h u1 u2
    Pstar := crtProductPstarFinset M (m a) p φ (a : ZMod M) β e h
    Tbase := crtProductTbaseFinset M (m a) p φ β h u1 u2
    Tbase_subset_T := hbase_sub
    T_subset_D := hT_sub
    Pstar_subset_D := hP_sub
    D_add_Tbase_full := hDbase
    selectedCoord := fun z => (φ z).1
    selectedCoord_natCast := hφnat
    privateResidue := h + h - α
    privateResidue_ne_active := by simpa [hα] using hpriv_ne
    T_selected_avoid := by
      intro t ht
      simpa [hα] using crtProductAllowed_selected_ne M (m a) p φ α β (hT_sub ht)
    Pstar_selected := by
      intro r hr
      exact crtProductPstar_selected_eq M (m a) p φ (a : ZMod M) α β e h ha1 hr
    D_nat_avoid := by
      simpa using hDnat
    T_add_T_compl_private := hTT
    D_add_T_full := hDT
    Pstar_card_formula := hcard h
  }, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

theorem exists_crtProduct_CRTGadget_of_subtype_product_index
    (P : Finset ℕ) (m : ℕ → ℕ) (M a : ℕ)
    [NeZero M] [Fact (Nat.Prime (m a))] [NeZero (m a)]
    [(i : NonselectedIndex P a) → Fact (Nat.Prime (m (i : ℕ)))]
    [(i : NonselectedIndex P a) → Fintype (ZMod (m (i : ℕ)))]
    (hma23 : 23 ≤ m a) (hma3 : m a % 4 = 3)
    (hm_ge7 : ∀ i : NonselectedIndex P a, 7 ≤ m (i : ℕ))
    (hm_pos : ∀ i : NonselectedIndex P a, 0 < m (i : ℕ))
    (hM : M = m a * ∏ i : NonselectedIndex P a, m (i : ℕ))
    (φ : ZMod M ≃+ ProductSpace (m a) (fun i : NonselectedIndex P a => m (i : ℕ)))
    (α : ZMod (m a))
    (β e : ∀ i : NonselectedIndex P a, ZMod (m (i : ℕ)))
    (data : ∀ i : NonselectedIndex P a, SafePairData (ZMod (m (i : ℕ))) (e i))
    (hβ : ∀ i : NonselectedIndex P a, β i = ((i : ℕ) : ZMod (m (i : ℕ))))
    (hφnat : ∀ n : ℕ, (φ (n : ZMod M)).1 = (n : ZMod (m a)))
    (hφsnd : ∀ n : ℕ, ∀ i : NonselectedIndex P a,
      (φ (n : ZMod M)).2 i = (n : ZMod (m (i : ℕ))))
    (ha1 : (φ (a : ZMod M)).1 = α)
    (he : e = affineNormalize (fun i : NonselectedIndex P a => m (i : ℕ)) β
      (φ (a : ZMod M)).2) :
    ∃ h u1 u2 : ZMod (m a),
      ∃ G : CRTGadget P m M a
          (crtProductAllowedFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
            φ α β),
        G.T = crtProductTFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          φ β e data h u1 u2 ∧
        G.Pstar = crtProductPstarFinset M (m a)
          (fun i : NonselectedIndex P a => m (i : ℕ)) φ (a : ZMod M) β e h ∧
        G.Tbase = crtProductTbaseFinset M (m a)
          (fun i : NonselectedIndex P a => m (i : ℕ)) φ β h u1 u2 := by
  refine exists_crtProduct_CRTGadget_of_card_formula P m M a (m a)
    rfl (fun i : NonselectedIndex P a => m (i : ℕ)) hm_ge7 hma3 hma23 φ α β e data
    hφnat ha1 he ?_ ?_
  · intro c hc n hn
    by_cases hca : c = a
    · subst c
      have hα : α = (a : ZMod (m a)) := by
        rw [← ha1]
        exact hφnat a
      have hne := crtProductAllowed_selected_ne M (m a)
        (fun i : NonselectedIndex P a => m (i : ℕ)) φ α β hn
      simpa [hφnat n, hα] using hne
    · let i : NonselectedIndex P a := ⟨c, Finset.mem_erase.mpr ⟨hca, hc⟩⟩
      have hmem := hn
      change (n : ZMod M) ∈
        (crtProductAllowedFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          φ α β : Finset (ZMod M)) at hmem
      simp [crtProductAllowedFinset, addEquivPreimageFinset, productAllowed] at hmem
      have hne : (φ (n : ZMod M)).2 i ≠ β i := hmem.2 i
      have hsnd := hφsnd n i
      simpa [i, hsnd, hβ i] using hne
  intro h
  calc
    ((crtProductPstarFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          φ (a : ZMod M) β e h).card : ℝ) / (M : ℝ) =
        (1 : ℝ) / (m a : ℝ) *
          ∏ i : NonselectedIndex P a, (1 - (1 : ℝ) / (m (i : ℕ) : ℝ)) := by
      exact crtProductPstarFinset_card_real_formula M (m a)
        (fun i : NonselectedIndex P a => m (i : ℕ)) φ (a : ZMod M) β e h
        (show 0 < m a from (Fact.out : Nat.Prime (m a)).pos) hm_pos hM
    _ = (1 : ℝ) / (m a : ℝ) *
          (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ)) := by
      congr 1
      rw [← Finset.prod_subtype (s := P.erase a) (p := fun b => b ∈ P.erase a)
        (f := fun b => 1 - (1 : ℝ) / (m b : ℝ))]
      intro b
      rfl

theorem exists_crtProduct_CRTGadget_for_exact_product
    (P : Finset ℕ) (m : ℕ → ℕ) (a : ℕ)
    [Fact (Nat.Prime (m a))] [NeZero (m a)]
    [NeZero (m a * ∏ i : NonselectedIndex P a, m (i : ℕ))]
    [(i : NonselectedIndex P a) → Fact (Nat.Prime (m (i : ℕ)))]
    [(i : NonselectedIndex P a) → Fintype (ZMod (m (i : ℕ)))]
    (hma23 : 23 ≤ m a) (hma3 : m a % 4 = 3)
    (hm_ge7 : ∀ i : NonselectedIndex P a, 7 ≤ m (i : ℕ))
    (hcop0 : Nat.Coprime (m a) (∏ i : NonselectedIndex P a, m (i : ℕ)))
    (hcop : Pairwise fun i j : NonselectedIndex P a => Nat.Coprime (m (i : ℕ)) (m (j : ℕ))) :
    ∃ h u1 u2 : ZMod (m a),
      ∃ G : CRTGadget P m (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) a
          (crtProductAllowedFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) (m a)
            (fun i : NonselectedIndex P a => m (i : ℕ))
            (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
            (a : ZMod (m a))
            (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))),
        G.T = crtProductTFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) (m a)
          (fun i : NonselectedIndex P a => m (i : ℕ))
          (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
          (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))
          (fun i : NonselectedIndex P a => (a : ZMod (m (i : ℕ))) -
            ((i : ℕ) : ZMod (m (i : ℕ))))
          (fun i : NonselectedIndex P a =>
            safePairDataZMod (m (i : ℕ)) (hm_ge7 i)
              ((a : ZMod (m (i : ℕ))) - ((i : ℕ) : ZMod (m (i : ℕ)))))
          h u1 u2 ∧
        G.Pstar = crtProductPstarFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ))
          (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
          (a : ZMod (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)))
          (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))
          (fun i : NonselectedIndex P a => (a : ZMod (m (i : ℕ))) -
            ((i : ℕ) : ZMod (m (i : ℕ)))) h ∧
        G.Tbase = crtProductTbaseFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ))
          (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
          (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ)))) h u1 u2 := by
  refine exists_crtProduct_CRTGadget_of_subtype_product_index P m
    (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) a hma23 hma3 hm_ge7 ?_ rfl
    (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
    (a : ZMod (m a))
    (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))
    (fun i : NonselectedIndex P a => (a : ZMod (m (i : ℕ))) -
      ((i : ℕ) : ZMod (m (i : ℕ))))
    (fun i : NonselectedIndex P a =>
      safePairDataZMod (m (i : ℕ)) (hm_ge7 i)
        ((a : ZMod (m (i : ℕ))) - ((i : ℕ) : ZMod (m (i : ℕ)))))
    (fun i => rfl)
    (fun n => productCRTAddEquiv_fst_natCast (m a)
      (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop n)
    (fun n i => productCRTAddEquiv_snd_natCast (m a)
      (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop n i) ?_ ?_
  · intro i
    have h7 := hm_ge7 i
    omega
  · exact productCRTAddEquiv_fst_natCast (m a)
      (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop a
  · funext i
    dsimp [affineNormalize]
    have hsnd := productCRTAddEquiv_snd_natCast (m a)
      (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop a i
    simpa using hsnd.symm

theorem prod_eq_selected_mul_nonselected (P : Finset ℕ) (m : ℕ → ℕ) {a : ℕ}
    (ha : a ∈ P) :
    P.prod m = m a * ∏ i : NonselectedIndex P a, m (i : ℕ) := by
  classical
  rw [← Finset.mul_prod_erase _ _ ha]
  congr 1
  rw [← Finset.prod_subtype (s := P.erase a) (p := fun b => b ∈ P.erase a) (f := m)]
  intro b
  rfl

lemma stage_M_eq_selected_mul_nonselected (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    st.M = st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ) := by
  rw [st.M_def, prod_eq_selected_mul_nonselected st.P st.m ha]

lemma stage_selected_coprime_nonselected_prod (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    Nat.Coprime (st.m a) (∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) := by
  classical
  rw [Nat.coprime_fintype_prod_right_iff]
  intro i
  rcases Finset.mem_erase.mp i.property with ⟨hia, hiP⟩
  exact st.m_pairwise_coprime ha hiP hia.symm

lemma stage_pairwise_coprime_nonselected (st : StageState) {a : ℕ} :
    Pairwise fun i j : NonselectedIndex st.P a =>
      Nat.Coprime (st.m (i : ℕ)) (st.m (j : ℕ)) := by
  intro i j hij
  rcases Finset.mem_erase.mp i.property with ⟨_hia, hiP⟩
  rcases Finset.mem_erase.mp j.property with ⟨_hja, hjP⟩
  exact st.m_pairwise_coprime hiP hjP (fun hijNat => hij (Subtype.ext hijNat))

lemma stage_nonselected_product_pos (st : StageState) {a : ℕ} :
    0 < ∏ i : NonselectedIndex st.P a, st.m (i : ℕ) := by
  classical
  exact Finset.prod_pos fun i _hi =>
    st.modulus_pos ((Finset.mem_erase.mp i.property).2)

lemma stage_exact_product_pos (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    0 < st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ) := by
  exact Nat.mul_pos (st.modulus_pos ha) (stage_nonselected_product_pos st)

lemma stage_M_pos (st : StageState) {a : ℕ} (ha : a ∈ st.P) : 0 < st.M := by
  rw [stage_M_eq_selected_mul_nonselected st ha]
  exact stage_exact_product_pos st ha

noncomputable def stageCRTProductEquiv (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) ≃+
      ProductSpace (st.m a) (fun i : NonselectedIndex st.P a => st.m (i : ℕ)) :=
  productCRTAddEquiv (st.m a) (fun i : NonselectedIndex st.P a => st.m (i : ℕ))
    (stage_selected_coprime_nonselected_prod st ha)
    (stage_pairwise_coprime_nonselected st (a := a))

theorem stageCRTProductEquiv_fst_natCast (st : StageState) {a n : ℕ} (ha : a ∈ st.P) :
    ((stageCRTProductEquiv st ha)
      (n : ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)))).1 =
      (n : ZMod (st.m a)) := by
  unfold stageCRTProductEquiv
  exact productCRTAddEquiv_fst_natCast (st.m a)
    (fun i : NonselectedIndex st.P a => st.m (i : ℕ))
    (stage_selected_coprime_nonselected_prod st ha)
    (stage_pairwise_coprime_nonselected st (a := a)) n

theorem stageCRTProductEquiv_snd_natCast (st : StageState) {a n : ℕ} (ha : a ∈ st.P)
    (i : NonselectedIndex st.P a) :
    ((stageCRTProductEquiv st ha)
      (n : ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)))).2 i =
      (n : ZMod (st.m (i : ℕ))) := by
  unfold stageCRTProductEquiv
  exact productCRTAddEquiv_snd_natCast (st.m a)
    (fun i : NonselectedIndex st.P a => st.m (i : ℕ))
    (stage_selected_coprime_nonselected_prod st ha)
    (stage_pairwise_coprime_nonselected st (a := a)) n i

noncomputable def stageCRTAllowedFinset (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    Finset (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))) := by
  classical
  letI : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  exact crtProductAllowedFinset
    (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) (st.m a)
    (fun i : NonselectedIndex st.P a => st.m (i : ℕ)) (stageCRTProductEquiv st ha)
    (a : ZMod (st.m a))
    (fun i : NonselectedIndex st.P a => ((i : ℕ) : ZMod (st.m (i : ℕ))))

noncomputable def stageShiftedQRDelete (st : StageState) {a : ℕ} (ha : a ∈ st.P)
    (h u1 u2 : ZMod (st.m a)) : Finset (ZMod (st.m a)) := by
  letI : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  exact shiftedQRDelete (st.m a) h ({u1, u2} : Finset (ZMod (st.m a)))

noncomputable def stageCRTTbaseFinset (st : StageState) {a : ℕ} (ha : a ∈ st.P)
    (h u1 u2 : ZMod (st.m a)) :
    Finset (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))) := by
  classical
  letI : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  letI : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  exact crtProductTbaseFinset
    (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) (st.m a)
    (fun i : NonselectedIndex st.P a => st.m (i : ℕ)) (stageCRTProductEquiv st ha)
    (fun i : NonselectedIndex st.P a => ((i : ℕ) : ZMod (st.m (i : ℕ))))
    h u1 u2

theorem natCast_mem_stageCRTTbaseFinset_iff (st : StageState) {a n : ℕ}
    (ha : a ∈ st.P) (h u1 u2 : ZMod (st.m a)) :
    (n : ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))) ∈
        stageCRTTbaseFinset st ha h u1 u2 ↔
      (n : ZMod (st.m a)) ∈ stageShiftedQRDelete st ha h u1 u2 ∧
        ∀ i : NonselectedIndex st.P a,
          (n : ZMod (st.m (i : ℕ))) ≠ ((i : ℕ) : ZMod (st.m (i : ℕ))) := by
  classical
  let : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  let : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  unfold stageCRTTbaseFinset stageShiftedQRDelete crtProductTbaseFinset productBase
    shiftedNonzeroBox
  simp only [addEquivPreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  constructor
  · intro ht
    constructor
    · have hsel := ht.1
      rw [stageCRTProductEquiv_fst_natCast st ha] at hsel
      exact hsel
    · intro i hbad
      exact ht.2 i (by rw [stageCRTProductEquiv_snd_natCast st ha i, hbad])
  · intro ht
    constructor
    · rw [stageCRTProductEquiv_fst_natCast st ha]
      exact ht.1
    · intro i hbad
      exact ht.2 i (by rw [← stageCRTProductEquiv_snd_natCast st ha i, hbad])

theorem natCast_mem_stageCRTAllowedFinset_iff (st : StageState) {a n : ℕ}
    (ha : a ∈ st.P) :
    (n : ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))) ∈
        stageCRTAllowedFinset st ha ↔
      (n : ZMod (st.m a)) ≠ (a : ZMod (st.m a)) ∧
        ∀ i : NonselectedIndex st.P a,
          (n : ZMod (st.m (i : ℕ))) ≠ ((i : ℕ) : ZMod (st.m (i : ℕ))) := by
  classical
  let : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  unfold stageCRTAllowedFinset crtProductAllowedFinset productAllowed shiftedNonzeroBox
  simp only [addEquivPreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  constructor
  · intro hallowed
    constructor
    · intro hbad
      exact hallowed.1 (by rw [stageCRTProductEquiv_fst_natCast st ha, hbad])
    · intro i hbad
      exact hallowed.2 i (by rw [stageCRTProductEquiv_snd_natCast st ha i, hbad])
  · intro hallowed
    constructor
    · intro hbad
      exact hallowed.1 (by rw [← stageCRTProductEquiv_fst_natCast st ha, hbad])
    · intro i hbad
      exact hallowed.2 i (by rw [← stageCRTProductEquiv_snd_natCast st ha i, hbad])

theorem exists_stage_exact_product_CRTGadget_on_allowed (st : StageState) {a : ℕ}
    (ha : a ∈ st.P) :
    Nonempty (CRTGadget st.P st.m
      (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) a
      (stageCRTAllowedFinset st ha)) := by
  classical
  let : Fact (Nat.Prime (st.m a)) := ⟨st.m_prime a ha⟩
  let : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  let : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  let : (i : NonselectedIndex st.P a) → Fact (Nat.Prime (st.m (i : ℕ))) := fun i =>
    ⟨st.m_prime (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex st.P a) → NeZero (st.m (i : ℕ)) := fun i =>
    NeZero.of_pos (st.modulus_pos ((Finset.mem_erase.mp i.property).2))
  let : (i : NonselectedIndex st.P a) → Fintype (ZMod (st.m (i : ℕ))) := fun _ =>
    inferInstance
  obtain ⟨_, _, _, G, _⟩ :=
    exists_crtProduct_CRTGadget_for_exact_product st.P st.m a
      (st.m_ge23 a ha) (st.m_mod4 a ha)
      (fun i => by
        have h23 := st.m_ge23 (i : ℕ) ((Finset.mem_erase.mp i.property).2)
        omega)
      (stage_selected_coprime_nonselected_prod st ha)
      (stage_pairwise_coprime_nonselected st (a := a))
  exact ⟨G⟩

theorem exists_stage_exact_product_CRTGadget (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    ∃ D : Finset (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))),
      Nonempty (CRTGadget st.P st.m
        (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) a D) :=
  ⟨stageCRTAllowedFinset st ha, exists_stage_exact_product_CRTGadget_on_allowed st ha⟩

noncomputable def stageCRTAllowedFinsetAtM (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    Finset (ZMod st.M) :=
  Eq.mp (congrArg (fun M => Finset (ZMod M))
    (stage_M_eq_selected_mul_nonselected st ha).symm) (stageCRTAllowedFinset st ha)

noncomputable def stageCRTTbaseFinsetAtM (st : StageState) {a : ℕ} (ha : a ∈ st.P)
    (h u1 u2 : ZMod (st.m a)) : Finset (ZMod st.M) :=
  Eq.mp (congrArg (fun M => Finset (ZMod M))
    (stage_M_eq_selected_mul_nonselected st ha).symm)
    (stageCRTTbaseFinset st ha h u1 u2)

theorem natCast_mem_stageZmodFinsetCast_iff {M M' : ℕ} (hM : M = M')
    (D : Finset (ZMod M')) (n : ℕ) :
    (n : ZMod M) ∈ Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) D ↔
      (n : ZMod M') ∈ D := by
  cases hM
  simp

theorem natCast_mem_stageCRTAllowedFinsetAtM_iff (st : StageState) {a n : ℕ}
    (ha : a ∈ st.P) :
    (n : ZMod st.M) ∈ stageCRTAllowedFinsetAtM st ha ↔
      (n : ZMod (st.m a)) ≠ (a : ZMod (st.m a)) ∧
        ∀ i : NonselectedIndex st.P a,
          (n : ZMod (st.m (i : ℕ))) ≠ ((i : ℕ) : ZMod (st.m (i : ℕ))) := by
  rw [stageCRTAllowedFinsetAtM]
  rw [natCast_mem_stageZmodFinsetCast_iff (stage_M_eq_selected_mul_nonselected st ha)]
  exact natCast_mem_stageCRTAllowedFinset_iff st ha

theorem natCast_mem_stageCRTAllowedFinsetAtM_iff_active (st : StageState)
    {a n : ℕ} (ha : a ∈ st.P) :
    (n : ZMod st.M) ∈ stageCRTAllowedFinsetAtM st ha ↔
      ∀ c ∈ st.P, (n : ZMod (st.m c)) ≠ (c : ZMod (st.m c)) := by
  rw [natCast_mem_stageCRTAllowedFinsetAtM_iff st ha]
  constructor
  · intro h c hc
    by_cases hca : c = a
    · subst c
      exact h.1
    · let i : NonselectedIndex st.P a := ⟨c, Finset.mem_erase.mpr ⟨hca, hc⟩⟩
      exact h.2 i
  · intro h
    refine ⟨h a ha, ?_⟩
    intro i
    exact h (i : ℕ) (Finset.mem_erase.mp i.property).2

theorem natCast_mem_stageCRTTbaseFinsetAtM_iff (st : StageState) {a n : ℕ}
    (ha : a ∈ st.P) (h u1 u2 : ZMod (st.m a)) :
    (n : ZMod st.M) ∈ stageCRTTbaseFinsetAtM st ha h u1 u2 ↔
      (n : ZMod (st.m a)) ∈ stageShiftedQRDelete st ha h u1 u2 ∧
        ∀ i : NonselectedIndex st.P a,
          (n : ZMod (st.m (i : ℕ))) ≠ ((i : ℕ) : ZMod (st.m (i : ℕ))) := by
  rw [stageCRTTbaseFinsetAtM]
  rw [natCast_mem_stageZmodFinsetCast_iff (stage_M_eq_selected_mul_nonselected st ha)]
  exact natCast_mem_stageCRTTbaseFinset_iff st ha h u1 u2

theorem exists_stage_CRTGadget_on_allowedAtM (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    Nonempty (CRTGadget st.P st.m st.M a (stageCRTAllowedFinsetAtM st ha)) := by
  convert exists_stage_exact_product_CRTGadget_on_allowed st ha
  · exact stage_M_eq_selected_mul_nonselected st ha
  · unfold stageCRTAllowedFinsetAtM
    simp

def StageState.HasCanonicalD (st : StageState) : Prop :=
  ∀ a (ha : a ∈ st.P), st.D = stageCRTAllowedFinsetAtM st ha

theorem exists_stage_CRTGadget_on_D_of_canonical (st : StageState)
    (hD : st.HasCanonicalD) {a : ℕ} (ha : a ∈ st.P) :
    Nonempty (CRTGadget st.P st.m st.M a st.D) := by
  rw [hD a ha]
  exact exists_stage_CRTGadget_on_allowedAtM st ha

theorem zmodFinsetCast_add_self_eq_univ {M M' : ℕ} (hM : M = M')
    (D : Finset (ZMod M'))
    (hD : ((D : Set (ZMod M')) + (D : Set (ZMod M'))) = Set.univ) :
    let Dm : Finset (ZMod M) := Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) D
    ((Dm : Set (ZMod M)) + (Dm : Set (ZMod M))) = Set.univ := by
  cases hM
  simpa using hD

theorem zmodFinsetCast_add_eq_univ {M M' : ℕ} (hM : M = M')
    (D T : Finset (ZMod M'))
    (hDT : ((D : Set (ZMod M')) + (T : Set (ZMod M'))) = Set.univ) :
    let Dm : Finset (ZMod M) := Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) D
    let Tm : Finset (ZMod M) := Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) T
    ((Dm : Set (ZMod M)) + (Tm : Set (ZMod M))) = Set.univ := by
  cases hM
  simpa using hDT

theorem stageCRTAllowedFinset_add_self_eq_univ (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    ((stageCRTAllowedFinset st ha : Set
        (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)))) +
      (stageCRTAllowedFinset st ha : Set
        (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))))) = Set.univ := by
  classical
  let : Fact (Nat.Prime (st.m a)) := ⟨st.m_prime a ha⟩
  let : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  let : (i : NonselectedIndex st.P a) → Fact (Nat.Prime (st.m (i : ℕ))) := fun i =>
    ⟨st.m_prime (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  unfold stageCRTAllowedFinset
  simpa using
    (crtProduct_allowed_add_allowed_eq_univ
      (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) (st.m a)
      (fun i : NonselectedIndex st.P a => st.m (i : ℕ))
      (le_trans (by norm_num : 7 ≤ 23) (st.m_ge23 a ha))
      (fun i => le_trans (by norm_num : 7 ≤ 23)
          (st.m_ge23 (i : ℕ) ((Finset.mem_erase.mp i.property).2)))
      (stageCRTProductEquiv st ha) (a : ZMod (st.m a))
      (fun i : NonselectedIndex st.P a => ((i : ℕ) : ZMod (st.m (i : ℕ)))))

theorem stageCRTAllowedFinset_add_Tbase_eq_univ (st : StageState) {a : ℕ}
    (ha : a ∈ st.P) (h u1 u2 : ZMod (st.m a)) :
    ((stageCRTAllowedFinset st ha : Set
        (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)))) +
      (stageCRTTbaseFinset st ha h u1 u2 : Set
        (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))))) = Set.univ := by
  classical
  let : Fact (Nat.Prime (st.m a)) := ⟨st.m_prime a ha⟩
  let : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  let : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  let : (i : NonselectedIndex st.P a) → Fact (Nat.Prime (st.m (i : ℕ))) := fun i =>
    ⟨st.m_prime (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  unfold stageCRTAllowedFinset stageCRTTbaseFinset
  simpa using
    (crtProduct_allowed_add_Tbase_eq_univ
      (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) (st.m a)
      (fun i : NonselectedIndex st.P a => st.m (i : ℕ))
      (fun i => le_trans (by norm_num : 7 ≤ 23)
          (st.m_ge23 (i : ℕ) ((Finset.mem_erase.mp i.property).2)))
      (st.m_mod4 a ha) (st.m_ge23 a ha)
      (stageCRTProductEquiv st ha) (a : ZMod (st.m a)) h u1 u2
      (fun i : NonselectedIndex st.P a => ((i : ℕ) : ZMod (st.m (i : ℕ)))))

theorem stageCRTAllowedFinsetAtM_add_self_eq_univ (st : StageState) {a : ℕ}
    (ha : a ∈ st.P) :
    ((stageCRTAllowedFinsetAtM st ha : Set (ZMod st.M)) +
      (stageCRTAllowedFinsetAtM st ha : Set (ZMod st.M))) = Set.univ :=
  zmodFinsetCast_add_self_eq_univ (stage_M_eq_selected_mul_nonselected st ha)
    (stageCRTAllowedFinset st ha) (stageCRTAllowedFinset_add_self_eq_univ st ha)

theorem stageCRTAllowedFinsetAtM_add_Tbase_eq_univ (st : StageState) {a : ℕ}
    (ha : a ∈ st.P) (h u1 u2 : ZMod (st.m a)) :
    ((stageCRTAllowedFinsetAtM st ha : Set (ZMod st.M)) +
      (stageCRTTbaseFinsetAtM st ha h u1 u2 : Set (ZMod st.M))) = Set.univ :=
  zmodFinsetCast_add_eq_univ (stage_M_eq_selected_mul_nonselected st ha)
    (stageCRTAllowedFinset st ha) (stageCRTTbaseFinset st ha h u1 u2)
    (stageCRTAllowedFinset_add_Tbase_eq_univ st ha h u1 u2)

theorem stage_D_add_D_eq_univ_of_canonical (st : StageState)
    (hD : st.HasCanonicalD) {a : ℕ} (ha : a ∈ st.P) :
    ((st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M))) = Set.univ := by
  rw [hD a ha]
  exact stageCRTAllowedFinsetAtM_add_self_eq_univ st ha

theorem canonicalD_middle_residueBlock_cover (st : StageState) (hD : st.HasCanonicalD)
    {a N L n : ℕ} (ha : a ∈ st.P)
    (hML : st.M ≤ L) (hnlo : 2 * N + st.M ≤ n)
    (hnhi : n ≤ 2 * N + 2 * L - st.M) :
    n ∈ twoFoldFinset (residueBlockFinset st.M st.D N (N + L)) := by
  let : NeZero st.M := NeZero.of_pos (stage_M_pos st ha)
  have hres : (n : ZMod st.M) ∈
      (st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M)) := by
    rw [stage_D_add_D_eq_univ_of_canonical st hD ha]
    exact Set.mem_univ _
  exact residueBlockFinset_middle_mem_twoFold_self (M := st.M) (N := N) (L := L)
    (n := n) hML hnlo hnhi hres

theorem exists_stage_CRTGadget (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    ∃ D : Finset (ZMod st.M), Nonempty (CRTGadget st.P st.m st.M a D) :=
  ⟨stageCRTAllowedFinsetAtM st ha, exists_stage_CRTGadget_on_allowedAtM st ha⟩

end Erdos330
