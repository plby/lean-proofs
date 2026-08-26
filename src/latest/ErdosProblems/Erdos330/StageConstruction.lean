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
import ErdosProblems.Erdos330.PrimeSupply
import ErdosProblems.Erdos330.StageCoverage

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
# Stage-construction data for Erdős Problem 330

This file starts the concrete one-stage construction layer.  The first part is
the fresh-prime package used when activating a dormant element.
-/

namespace Erdos330

open scoped Pointwise

structure FreshPrimeData (st : StageState) (p : ℕ) where
  X_lt_p : st.X < p
  M_lt_p : st.M < p
  ge23 : 23 ≤ p
  prime : Nat.Prime p
  mod4 : p % 4 = 3
  coprime_old : ∀ a ∈ st.P, Nat.Coprime p (st.m a)

theorem exists_freshPrimeData_ge (st : StageState) (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ FreshPrimeData st p := by
  obtain ⟨p, hpge, hpprime, hpmod⟩ :=
    exists_prime_three_mod_four_ge (max (max (max (st.X + 1) (st.M + 1)) 23) N)
  refine ⟨p, by omega, ?_⟩
  exact {
    X_lt_p := by omega
    M_lt_p := by omega
    ge23 := by omega
    prime := hpprime
    mod4 := hpmod
    coprime_old := by
      intro a ha
      have hmpos : 0 < st.m a := st.modulus_pos ha
      have hprod_pos : 0 < st.P.prod st.m := by
        exact Finset.prod_pos (fun b hb => st.modulus_pos hb)
      have hMpos : 0 < st.M := by
        rw [st.M_def]
        exact hprod_pos
      have hdvd : st.m a ∣ st.M := by
        rw [st.M_def]
        exact Finset.dvd_prod_of_mem st.m ha
      have hm_le_M : st.m a ≤ st.M := Nat.le_of_dvd hMpos hdvd
      have hm_lt_p : st.m a < p := lt_of_le_of_lt hm_le_M (by omega)
      exact Nat.coprime_of_lt_prime (Nat.ne_of_gt hmpos) hm_lt_p hpprime
  }

theorem exists_freshPrimeData (st : StageState) : ∃ p : ℕ, FreshPrimeData st p := by
  obtain ⟨p, _hpN, hp⟩ := exists_freshPrimeData_ge st 0
  exact ⟨p, hp⟩

theorem FreshPrimeData.eq_of_zmod_eq_of_old {st : StageState} {p u v : ℕ}
    (hp : FreshPrimeData st p) (hu : u ≤ st.X) (hv : v ≤ st.X)
    (huv : (u : ZMod p) = (v : ZMod p)) :
    u = v :=
  nat_eq_of_zmod_eq_of_le_lt hu hv hp.X_lt_p huv

/-- The active set after activating a dormant element. -/
def activatedActiveSet (st : StageState) (b : ℕ) : Finset ℕ :=
  insert b st.P

/-- The modulus assignment after activating `b` with fresh modulus `p`. -/
def activatedModulus (st : StageState) (b p : ℕ) : ℕ → ℕ :=
  fun c => if c = b then p else st.m c

/-- The active modulus product after activating `b`. -/
def activatedM (st : StageState) (b p : ℕ) : ℕ :=
  (activatedActiveSet st b).prod (activatedModulus st b p)

theorem activatedModulus_new (st : StageState) (b p : ℕ) :
    activatedModulus st b p b = p := by
  simp [activatedModulus]

theorem activatedModulus_old_of_ne (st : StageState) {b p c : ℕ} (hcb : c ≠ b) :
    activatedModulus st b p c = st.m c := by
  simp [activatedModulus, hcb]

theorem activatedModulus_old_of_mem (st : StageState) {b p c : ℕ}
    (hbDormant : b ∉ st.P) (hc : c ∈ st.P) :
    activatedModulus st b p c = st.m c := by
  exact activatedModulus_old_of_ne st (fun hcb => hbDormant (hcb ▸ hc))

theorem activated_m_prime (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ c ∈ activatedActiveSet st b, Nat.Prime (activatedModulus st b p c) := by
  intro c hc
  rw [activatedActiveSet] at hc
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · simpa [activatedModulus_new] using hp.prime
  · rw [activatedModulus_old_of_mem st hbDormant hcP]
    exact st.m_prime c hcP

theorem activated_m_ge23 (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ c ∈ activatedActiveSet st b, 23 ≤ activatedModulus st b p c := by
  intro c hc
  rw [activatedActiveSet] at hc
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · simpa [activatedModulus_new] using hp.ge23
  · rw [activatedModulus_old_of_mem st hbDormant hcP]
    exact st.m_ge23 c hcP

theorem activated_m_mod4 (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ c ∈ activatedActiveSet st b, activatedModulus st b p c % 4 = 3 := by
  intro c hc
  rw [activatedActiveSet] at hc
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · simpa [activatedModulus_new] using hp.mod4
  · rw [activatedModulus_old_of_mem st hbDormant hcP]
    exact st.m_mod4 c hcP

theorem activated_m_pairwise_coprime (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ ⦃c⦄, c ∈ activatedActiveSet st b →
      ∀ ⦃d⦄, d ∈ activatedActiveSet st b → c ≠ d →
        Nat.Coprime (activatedModulus st b p c) (activatedModulus st b p d) := by
  intro c hc d hd hcd
  rw [activatedActiveSet] at hc hd
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · rcases Finset.mem_insert.mp hd with hdb | hdP
    · exact (hcd hdb.symm).elim
    · simpa [activatedModulus_new, activatedModulus_old_of_mem st hbDormant hdP]
        using hp.coprime_old d hdP
  · rcases Finset.mem_insert.mp hd with rfl | hdP
    · simpa [activatedModulus_new, activatedModulus_old_of_mem st hbDormant hcP]
        using (hp.coprime_old c hcP).symm
    · rw [activatedModulus_old_of_mem st hbDormant hcP,
        activatedModulus_old_of_mem st hbDormant hdP]
      exact st.m_pairwise_coprime hcP hdP hcd

theorem activatedM_eq (st : StageState) {b p : ℕ} (hbDormant : b ∉ st.P) :
    activatedM st b p = p * st.M := by
  classical
  unfold activatedM activatedActiveSet
  rw [Finset.prod_insert hbDormant, activatedModulus_new, st.M_def]
  congr 1
  exact Finset.prod_congr rfl fun c hc =>
    activatedModulus_old_of_mem st hbDormant hc

theorem activatedM_pos (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    0 < activatedM st b p := by
  rw [activatedM_eq st hbDormant]
  have hMpos : 0 < st.M := by
    rw [st.M_def]
    exact Finset.prod_pos fun c hc => st.modulus_pos hc
  exact Nat.mul_pos hp.prime.pos hMpos

theorem activatedModulus_dvd_M (st : StageState) {b p c : ℕ}
    (hc : c ∈ activatedActiveSet st b) :
    activatedModulus st b p c ∣ activatedM st b p := by
  rw [activatedM]
  exact Finset.dvd_prod_of_mem (activatedModulus st b p) hc

theorem activatedFreshModulus_dvd_M (st : StageState) (b p : ℕ) :
    p ∣ activatedM st b p := by
  have hb : b ∈ activatedActiveSet st b := by
    simp [activatedActiveSet]
  simpa [activatedModulus_new] using
    (activatedModulus_dvd_M st (b := b) (p := p) hb)

theorem activatedOldM_dvd_M (st : StageState) {b p : ℕ} (hbDormant : b ∉ st.P) :
    st.M ∣ activatedM st b p := by
  rw [activatedM_eq st hbDormant]
  exact ⟨p, by rw [Nat.mul_comm]⟩

def activatedFreshProjection (st : StageState) (b p : ℕ)
    (γ : ZMod (activatedM st b p)) : ZMod p :=
  ZMod.castHom (activatedFreshModulus_dvd_M st b p) (ZMod p) γ

def activatedOldProjection (st : StageState) {b p : ℕ} (hbDormant : b ∉ st.P)
    (γ : ZMod (activatedM st b p)) : ZMod st.M :=
  ZMod.castHom (activatedOldM_dvd_M st hbDormant) (ZMod st.M) γ

theorem activatedFreshProjection_natCast (st : StageState) (b p n : ℕ) :
    activatedFreshProjection st b p (n : ZMod (activatedM st b p)) =
      (n : ZMod p) := by
  simp [activatedFreshProjection]

theorem activatedOldProjection_natCast (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (n : ℕ) :
    activatedOldProjection st hbDormant (n : ZMod (activatedM st b p)) =
      (n : ZMod st.M) := by
  simp [activatedOldProjection]

theorem activatedFreshProjection_sub_natCast (st : StageState) (b p u : ℕ)
    (γ : ZMod (activatedM st b p)) :
    activatedFreshProjection st b p (γ - (u : ZMod (activatedM st b p))) =
      activatedFreshProjection st b p γ - (u : ZMod p) := by
  rw [activatedFreshProjection]
  change (ZMod.cast (γ - (u : ZMod (activatedM st b p))) : ZMod p) =
    (ZMod.cast γ : ZMod p) - (u : ZMod p)
  rw [ZMod.cast_sub (activatedFreshModulus_dvd_M st b p) γ
    (u : ZMod (activatedM st b p))]
  rw [ZMod.cast_natCast (activatedFreshModulus_dvd_M st b p) u]

theorem activatedOldProjection_sub_natCast (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (u : ℕ) (γ : ZMod (activatedM st b p)) :
    activatedOldProjection st hbDormant (γ - (u : ZMod (activatedM st b p))) =
      activatedOldProjection st hbDormant γ - (u : ZMod st.M) := by
  rw [activatedOldProjection]
  change (ZMod.cast (γ - (u : ZMod (activatedM st b p))) : ZMod st.M) =
    (ZMod.cast γ : ZMod st.M) - (u : ZMod st.M)
  rw [ZMod.cast_sub (activatedOldM_dvd_M st hbDormant) γ
    (u : ZMod (activatedM st b p))]
  rw [ZMod.cast_natCast (activatedOldM_dvd_M st hbDormant) u]

theorem activated_active_mem_old (st : StageState) {a b : ℕ} (ha : a ∈ st.P) :
    a ∈ activatedActiveSet st b := by
  exact Finset.mem_insert_of_mem ha

theorem activatedM_eq_selected_mul_nonselected (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) :
    activatedM st b p =
      activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ) := by
  rw [activatedM]
  exact prod_eq_selected_mul_nonselected (activatedActiveSet st b)
    (activatedModulus st b p) (activated_active_mem_old st ha)

lemma activated_selected_coprime_nonselected_prod (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    Nat.Coprime (activatedModulus st b p a)
      (∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) := by
  classical
  rw [Nat.coprime_fintype_prod_right_iff]
  intro i
  rcases Finset.mem_erase.mp i.property with ⟨hia, hiP⟩
  exact activated_m_pairwise_coprime st hbDormant hp (activated_active_mem_old st ha)
    hiP hia.symm

lemma activated_pairwise_coprime_nonselected (st : StageState) {a b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    Pairwise fun i j : NonselectedIndex (activatedActiveSet st b) a =>
      Nat.Coprime (activatedModulus st b p (i : ℕ))
        (activatedModulus st b p (j : ℕ)) := by
  intro i j hij
  rcases Finset.mem_erase.mp i.property with ⟨_hia, hiP⟩
  rcases Finset.mem_erase.mp j.property with ⟨_hja, hjP⟩
  exact activated_m_pairwise_coprime st hbDormant hp hiP hjP
    (fun hijNat => hij (Subtype.ext hijNat))

lemma activated_nonselected_product_pos (st : StageState) {a b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    0 < ∏ i : NonselectedIndex (activatedActiveSet st b) a,
      activatedModulus st b p (i : ℕ) := by
  classical
  exact Finset.prod_pos fun i _hi =>
    (activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)).pos

lemma activated_exact_product_pos (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    0 < activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ) := by
  exact Nat.mul_pos
    ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
    (activated_nonselected_product_pos st hbDormant hp)

noncomputable def activatedCRTProductEquiv (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ZMod (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ)) ≃+
      ProductSpace (activatedModulus st b p a)
        (fun i : NonselectedIndex (activatedActiveSet st b) a =>
          activatedModulus st b p (i : ℕ)) :=
  productCRTAddEquiv (activatedModulus st b p a)
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      activatedModulus st b p (i : ℕ))
    (activated_selected_coprime_nonselected_prod st ha hbDormant hp)
    (activated_pairwise_coprime_nonselected st hbDormant hp)

theorem activatedCRTProductEquiv_fst_natCast (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ((activatedCRTProductEquiv st ha hbDormant hp)
      (n : ZMod (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ)))).1 =
      (n : ZMod (activatedModulus st b p a)) := by
  unfold activatedCRTProductEquiv
  exact productCRTAddEquiv_fst_natCast (activatedModulus st b p a)
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      activatedModulus st b p (i : ℕ))
    (activated_selected_coprime_nonselected_prod st ha hbDormant hp)
    (activated_pairwise_coprime_nonselected st hbDormant hp) n

theorem activatedCRTProductEquiv_snd_natCast (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (i : NonselectedIndex (activatedActiveSet st b) a) :
    ((activatedCRTProductEquiv st ha hbDormant hp)
      (n : ZMod (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ)))).2 i =
      (n : ZMod (activatedModulus st b p (i : ℕ))) := by
  unfold activatedCRTProductEquiv
  exact productCRTAddEquiv_snd_natCast (activatedModulus st b p a)
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      activatedModulus st b p (i : ℕ))
    (activated_selected_coprime_nonselected_prod st ha hbDormant hp)
    (activated_pairwise_coprime_nonselected st hbDormant hp) n i

noncomputable def activatedCRTAllowedFinsetExact (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    Finset (ZMod (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))) := by
  classical
  letI : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  exact crtProductAllowedFinset
    (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))
    (activatedModulus st b p a)
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      activatedModulus st b p (i : ℕ))
    (activatedCRTProductEquiv st ha hbDormant hp)
    (a : ZMod (activatedModulus st b p a))
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))))

noncomputable def activatedCRTAllowedFinsetAtM (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    Finset (ZMod (activatedM st b p)) :=
  Eq.mp (congrArg (fun M => Finset (ZMod M))
    (activatedM_eq_selected_mul_nonselected st ha).symm)
    (activatedCRTAllowedFinsetExact st ha hbDormant hp)

theorem natCast_mem_eqMp_zmodFinset_iff {M M' : ℕ} (hM : M = M')
    (D : Finset (ZMod M')) (n : ℕ) :
    (n : ZMod M) ∈ Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) D ↔
      (n : ZMod M') ∈ D := by
  cases hM
  simp

theorem natCast_mem_activatedCRTAllowedFinsetExact_iff (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    (n : ZMod (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))) ∈
        activatedCRTAllowedFinsetExact st ha hbDormant hp ↔
      (n : ZMod (activatedModulus st b p a)) ≠
          (a : ZMod (activatedModulus st b p a)) ∧
        ∀ i : NonselectedIndex (activatedActiveSet st b) a,
          (n : ZMod (activatedModulus st b p (i : ℕ))) ≠
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))) := by
  classical
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  unfold activatedCRTAllowedFinsetExact crtProductAllowedFinset productAllowed shiftedNonzeroBox
  simp only [addEquivPreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    constructor
    · intro hbad
      exact h.1 (by rw [activatedCRTProductEquiv_fst_natCast st ha hbDormant hp, hbad])
    · intro i hbad
      exact h.2 i
        (by rw [activatedCRTProductEquiv_snd_natCast st ha hbDormant hp i, hbad])
  · intro h
    constructor
    · intro hbad
      exact h.1
        (by rw [← activatedCRTProductEquiv_fst_natCast st ha hbDormant hp, hbad])
    · intro i hbad
      exact h.2 i
        (by rw [← activatedCRTProductEquiv_snd_natCast st ha hbDormant hp i, hbad])

theorem natCast_mem_activatedCRTAllowedFinsetAtM_iff (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    (n : ZMod (activatedM st b p)) ∈ activatedCRTAllowedFinsetAtM st ha hbDormant hp ↔
      (n : ZMod (activatedModulus st b p a)) ≠
          (a : ZMod (activatedModulus st b p a)) ∧
        ∀ i : NonselectedIndex (activatedActiveSet st b) a,
          (n : ZMod (activatedModulus st b p (i : ℕ))) ≠
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))) := by
  rw [activatedCRTAllowedFinsetAtM]
  rw [natCast_mem_eqMp_zmodFinset_iff
    (activatedM_eq_selected_mul_nonselected (a := a) (b := b) (p := p) st ha)]
  exact natCast_mem_activatedCRTAllowedFinsetExact_iff st ha hbDormant hp

theorem natCast_mem_activatedCRTAllowedFinsetAtM_iff_active (st : StageState)
    {a b p n : ℕ} (ha : a ∈ st.P) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p) :
    (n : ZMod (activatedM st b p)) ∈ activatedCRTAllowedFinsetAtM st ha hbDormant hp ↔
      ∀ c ∈ activatedActiveSet st b,
        (n : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)) := by
  rw [natCast_mem_activatedCRTAllowedFinsetAtM_iff st ha hbDormant hp]
  constructor
  · intro h c hc
    by_cases hca : c = a
    · subst c
      exact h.1
    · let i : NonselectedIndex (activatedActiveSet st b) a :=
        ⟨c, Finset.mem_erase.mpr ⟨hca, hc⟩⟩
      exact h.2 i
  · intro h
    refine ⟨h a (activated_active_mem_old st ha), ?_⟩
    intro i
    exact h (i : ℕ) (Finset.mem_erase.mp i.property).2

theorem activatedCRTAllowedFinsetAtM_projection_lift (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ y : ZMod (activatedM st b p),
      activatedOldProjection st hbDormant y ∈ st.D →
        activatedFreshProjection st b p y ≠ (b : ZMod p) →
          y ∈ activatedCRTAllowedFinsetAtM st ha hbDormant hp := by
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  intro y hyOld hyFresh
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective y
  have hnOld : (n : ZMod st.M) ∈ st.D := by
    simpa [activatedOldProjection_natCast] using hyOld
  have hnFresh : (n : ZMod p) ≠ (b : ZMod p) := by
    simpa [activatedFreshProjection_natCast] using hyFresh
  rw [natCast_mem_activatedCRTAllowedFinsetAtM_iff st ha hbDormant hp]
  constructor
  · rw [activatedModulus_old_of_mem st hbDormant ha]
    exact st.D_nat_avoid a ha n hnOld
  · intro i
    rcases Finset.mem_erase.mp i.property with ⟨_hia, hiActive⟩
    simp [activatedActiveSet] at hiActive
    rcases hiActive with hib | hiP
    · rw [hib, activatedModulus_new]
      exact hnFresh
    · rw [activatedModulus_old_of_mem st hbDormant hiP]
      exact st.D_nat_avoid (i : ℕ) hiP n hnOld

noncomputable def activatedShiftedQRDelete (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (activatedModulus st b p a)) :
    Finset (ZMod (activatedModulus st b p a)) := by
  letI : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  exact shiftedQRDelete (activatedModulus st b p a) h
    ({u1, u2} : Finset (ZMod (activatedModulus st b p a)))

noncomputable def activatedCRTTbaseFinsetExact (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (activatedModulus st b p a)) :
    Finset (ZMod (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))) := by
  classical
  letI : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  letI : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  exact crtProductTbaseFinset
    (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))
    (activatedModulus st b p a)
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      activatedModulus st b p (i : ℕ))
    (activatedCRTProductEquiv st ha hbDormant hp)
    (fun i : NonselectedIndex (activatedActiveSet st b) a =>
      ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))))
    h u1 u2

noncomputable def activatedCRTTbaseFinsetAtM (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (activatedModulus st b p a)) :
    Finset (ZMod (activatedM st b p)) :=
  Eq.mp (congrArg (fun M => Finset (ZMod M))
    (activatedM_eq_selected_mul_nonselected st ha).symm)
    (activatedCRTTbaseFinsetExact st ha hbDormant hp h u1 u2)

theorem natCast_mem_activatedCRTTbaseFinsetExact_iff (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (activatedModulus st b p a)) :
    (n : ZMod (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))) ∈
        activatedCRTTbaseFinsetExact st ha hbDormant hp h u1 u2 ↔
      (n : ZMod (activatedModulus st b p a)) ∈
          activatedShiftedQRDelete st ha hbDormant hp h u1 u2 ∧
        ∀ i : NonselectedIndex (activatedActiveSet st b) a,
          (n : ZMod (activatedModulus st b p (i : ℕ))) ≠
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))) := by
  classical
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  unfold activatedCRTTbaseFinsetExact activatedShiftedQRDelete crtProductTbaseFinset
    productBase shiftedNonzeroBox
  simp only [addEquivPreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  constructor
  · intro ht
    constructor
    · have hsel := ht.1
      rw [activatedCRTProductEquiv_fst_natCast st ha hbDormant hp] at hsel
      exact hsel
    · intro i hbad
      exact ht.2 i
        (by rw [activatedCRTProductEquiv_snd_natCast st ha hbDormant hp i, hbad])
  · intro ht
    constructor
    · rw [activatedCRTProductEquiv_fst_natCast st ha hbDormant hp]
      exact ht.1
    · intro i hbad
      exact ht.2 i
        (by rw [← activatedCRTProductEquiv_snd_natCast st ha hbDormant hp i, hbad])

theorem natCast_mem_activatedCRTTbaseFinsetAtM_iff (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (activatedModulus st b p a)) :
    (n : ZMod (activatedM st b p)) ∈
        activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 ↔
      (n : ZMod (activatedModulus st b p a)) ∈
          activatedShiftedQRDelete st ha hbDormant hp h u1 u2 ∧
        ∀ i : NonselectedIndex (activatedActiveSet st b) a,
          (n : ZMod (activatedModulus st b p (i : ℕ))) ≠
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))) := by
  rw [activatedCRTTbaseFinsetAtM]
  rw [natCast_mem_eqMp_zmodFinset_iff
    (activatedM_eq_selected_mul_nonselected (a := a) (b := b) (p := p) st ha)]
  exact natCast_mem_activatedCRTTbaseFinsetExact_iff st ha hbDormant hp h u1 u2

def activatedSelectedOfOld (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (x : ZMod (st.m a)) :
    ZMod (activatedModulus st b p a) :=
  Eq.mp (congrArg ZMod (activatedModulus_old_of_mem st (p := p) hbDormant ha).symm) x

def oldSelectedOfActivated (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P)
    (x : ZMod (activatedModulus st b p a)) : ZMod (st.m a) :=
  Eq.mp (congrArg ZMod (activatedModulus_old_of_mem st (p := p) hbDormant ha)) x

theorem zmod_eqMp_symm_eq {M M' : ℕ} (hM : M = M') (x : ZMod M) :
    Eq.mp (congrArg ZMod hM.symm) (Eq.mp (congrArg ZMod hM) x) = x := by
  cases hM
  rfl

theorem activatedSelectedOfOld_oldSelectedOfActivated (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P)
    (x : ZMod (activatedModulus st b p a)) :
    activatedSelectedOfOld st ha hbDormant (oldSelectedOfActivated st ha hbDormant x) = x := by
  dsimp [activatedSelectedOfOld, oldSelectedOfActivated]
  exact zmod_eqMp_symm_eq (activatedModulus_old_of_mem st (p := p) hbDormant ha) x

theorem shiftedQRDelete_cast_mem {M M' n : ℕ} (hM : M = M')
    [NeZero M] [NeZero M'] (h u1 u2 : ZMod M') :
    (n : ZMod M') ∈ shiftedQRDelete M' h ({u1, u2} : Finset (ZMod M')) →
      (n : ZMod M) ∈ shiftedQRDelete M
        (Eq.mp (congrArg ZMod hM.symm) h)
        ({Eq.mp (congrArg ZMod hM.symm) u1,
          Eq.mp (congrArg ZMod hM.symm) u2} : Finset (ZMod M)) := by
  cases hM
  simp

theorem activatedShiftedQRDelete_mem_of_stage (st : StageState) {a b p n : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (st.m a)) :
    (n : ZMod (st.m a)) ∈ stageShiftedQRDelete st ha h u1 u2 →
      (n : ZMod (activatedModulus st b p a)) ∈
        activatedShiftedQRDelete st ha hbDormant hp
          (activatedSelectedOfOld st ha hbDormant h)
          (activatedSelectedOfOld st ha hbDormant u1)
          (activatedSelectedOfOld st ha hbDormant u2) := by
  intro hn
  dsimp [activatedShiftedQRDelete, stageShiftedQRDelete, activatedSelectedOfOld] at hn ⊢
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  exact shiftedQRDelete_cast_mem
    (activatedModulus_old_of_mem st (p := p) hbDormant ha) h u1 u2 hn

theorem activatedTbase_projection_lift_of_stageTbase (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (st.m a)) :
    ∀ y : ZMod (activatedM st b p),
      activatedOldProjection st hbDormant y ∈ stageCRTTbaseFinsetAtM st ha h u1 u2 →
        activatedFreshProjection st b p y ≠ (b : ZMod p) →
          y ∈ activatedCRTTbaseFinsetAtM st ha hbDormant hp
            (activatedSelectedOfOld st ha hbDormant h)
            (activatedSelectedOfOld st ha hbDormant u1)
            (activatedSelectedOfOld st ha hbDormant u2) := by
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  intro y hyOld hyFresh
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective y
  have hnOld : (n : ZMod st.M) ∈ stageCRTTbaseFinsetAtM st ha h u1 u2 := by
    simpa [activatedOldProjection_natCast] using hyOld
  have hnFresh : (n : ZMod p) ≠ (b : ZMod p) := by
    simpa [activatedFreshProjection_natCast] using hyFresh
  rw [natCast_mem_stageCRTTbaseFinsetAtM_iff st ha h u1 u2] at hnOld
  rw [natCast_mem_activatedCRTTbaseFinsetAtM_iff st ha hbDormant hp]
  constructor
  · exact activatedShiftedQRDelete_mem_of_stage st ha hbDormant hp h u1 u2 hnOld.1
  · intro i
    rcases Finset.mem_erase.mp i.property with ⟨hia, hiActive⟩
    simp [activatedActiveSet] at hiActive
    rcases hiActive with hib | hiP
    · rw [hib, activatedModulus_new]
      exact hnFresh
    · let j : NonselectedIndex st.P a := ⟨(i : ℕ), Finset.mem_erase.mpr ⟨hia, hiP⟩⟩
      have hj := hnOld.2 j
      rw [activatedModulus_old_of_mem st hbDormant hiP]
      exact hj

theorem activatedCRTAllowedFinsetExact_add_self_eq_univ (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ((activatedCRTAllowedFinsetExact st ha hbDormant hp : Set
        (ZMod (activatedModulus st b p a *
          ∏ i : NonselectedIndex (activatedActiveSet st b) a,
            activatedModulus st b p (i : ℕ)))) +
      (activatedCRTAllowedFinsetExact st ha hbDormant hp : Set
        (ZMod (activatedModulus st b p a *
          ∏ i : NonselectedIndex (activatedActiveSet st b) a,
            activatedModulus st b p (i : ℕ))))) = Set.univ := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  unfold activatedCRTAllowedFinsetExact
  simpa using
    (crtProduct_allowed_add_allowed_eq_univ
      (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ))
      (activatedModulus st b p a)
      (fun i : NonselectedIndex (activatedActiveSet st b) a =>
        activatedModulus st b p (i : ℕ))
      (le_trans (by norm_num : 7 ≤ 23)
        (activated_m_ge23 st hbDormant hp a (activated_active_mem_old st ha)))
      (fun i => le_trans (by norm_num : 7 ≤ 23)
        (activated_m_ge23 st hbDormant hp (i : ℕ)
          ((Finset.mem_erase.mp i.property).2)))
      (activatedCRTProductEquiv st ha hbDormant hp)
      (a : ZMod (activatedModulus st b p a))
      (fun i : NonselectedIndex (activatedActiveSet st b) a =>
        ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ)))))

theorem activatedCRTAllowedFinsetAtM_add_self_eq_univ (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ((activatedCRTAllowedFinsetAtM st ha hbDormant hp : Set (ZMod (activatedM st b p))) +
      (activatedCRTAllowedFinsetAtM st ha hbDormant hp : Set (ZMod (activatedM st b p)))) =
        Set.univ :=
  zmodFinsetCast_add_self_eq_univ (activatedM_eq_selected_mul_nonselected st ha)
    (activatedCRTAllowedFinsetExact st ha hbDormant hp)
    (activatedCRTAllowedFinsetExact_add_self_eq_univ st ha hbDormant hp)

theorem exists_activated_exact_product_CRTGadget_on_allowed_with_eqs (st : StageState)
    {a b p : ℕ} (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    [Fact (Nat.Prime (activatedModulus st b p a))]
    [NeZero (activatedModulus st b p a)]
    [NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ))]
    [(i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ)))]
    [(i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ)))] :
    ∃ h u1 u2 : ZMod (activatedModulus st b p a),
      ∃ G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
          (activatedModulus st b p a *
            ∏ i : NonselectedIndex (activatedActiveSet st b) a,
              activatedModulus st b p (i : ℕ))
          a (activatedCRTAllowedFinsetExact st ha hbDormant hp),
        G.T = crtProductTFinset
          (activatedModulus st b p a *
            ∏ i : NonselectedIndex (activatedActiveSet st b) a,
              activatedModulus st b p (i : ℕ))
          (activatedModulus st b p a)
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            activatedModulus st b p (i : ℕ))
          (activatedCRTProductEquiv st ha hbDormant hp)
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))))
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            (a : ZMod (activatedModulus st b p (i : ℕ))) -
              ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))))
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            safePairDataZMod (activatedModulus st b p (i : ℕ))
              (by
                have h23 := activated_m_ge23 st hbDormant hp (i : ℕ)
                  ((Finset.mem_erase.mp i.property).2)
                omega)
              ((a : ZMod (activatedModulus st b p (i : ℕ))) -
                ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ)))))
          h u1 u2 ∧
        G.Pstar = crtProductPstarFinset
          (activatedModulus st b p a *
            ∏ i : NonselectedIndex (activatedActiveSet st b) a,
              activatedModulus st b p (i : ℕ))
          (activatedModulus st b p a)
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            activatedModulus st b p (i : ℕ))
          (activatedCRTProductEquiv st ha hbDormant hp)
          (a : ZMod (activatedModulus st b p a *
            ∏ i : NonselectedIndex (activatedActiveSet st b) a,
              activatedModulus st b p (i : ℕ)))
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))))
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            (a : ZMod (activatedModulus st b p (i : ℕ))) -
              ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ)))) h ∧
        G.Tbase = crtProductTbaseFinset
          (activatedModulus st b p a *
            ∏ i : NonselectedIndex (activatedActiveSet st b) a,
              activatedModulus st b p (i : ℕ))
          (activatedModulus st b p a)
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            activatedModulus st b p (i : ℕ))
          (activatedCRTProductEquiv st ha hbDormant hp)
          (fun i : NonselectedIndex (activatedActiveSet st b) a =>
            ((i : ℕ) : ZMod (activatedModulus st b p (i : ℕ))))
          h u1 u2 := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      NeZero (activatedModulus st b p (i : ℕ)) := fun i =>
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)).pos)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  exact
    exists_crtProduct_CRTGadget_for_exact_product (activatedActiveSet st b)
      (activatedModulus st b p) a
      (activated_m_ge23 st hbDormant hp a (activated_active_mem_old st ha))
      (activated_m_mod4 st hbDormant hp a (activated_active_mem_old st ha))
      (fun i => by
        have h23 := activated_m_ge23 st hbDormant hp (i : ℕ)
          ((Finset.mem_erase.mp i.property).2)
        omega)
      (activated_selected_coprime_nonselected_prod st ha hbDormant hp)
      (activated_pairwise_coprime_nonselected st hbDormant hp)

theorem exists_activated_exact_product_CRTGadget_on_allowed (st : StageState)
    {a b p : ℕ} (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    Nonempty (CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ))
      a (activatedCRTAllowedFinsetExact st ha hbDormant hp)) := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  obtain ⟨_, _, _, G, _⟩ :=
    exists_activated_exact_product_CRTGadget_on_allowed_with_eqs st ha hbDormant hp
  exact ⟨G⟩

noncomputable def CRTGadget.castModulus {P : Finset ℕ} {m : ℕ → ℕ} {M M' a : ℕ}
    {D : Finset (ZMod M')} (hM : M = M') (G : CRTGadget P m M' a D) :
    CRTGadget P m M a (Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) D) := by
  cases hM
  simpa using G

theorem CRTGadget.castModulus_Tbase {P : Finset ℕ} {m : ℕ → ℕ} {M M' a : ℕ}
    {D : Finset (ZMod M')} (hM : M = M') (G : CRTGadget P m M' a D) :
    (CRTGadget.castModulus hM G).Tbase =
      Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) G.Tbase := by
  cases hM
  rfl

theorem eqMp_zmodFinset_eq_of_eq {M M' : ℕ} (h1 h2 : M = M')
    (D : Finset (ZMod M')) :
    Eq.mp (congrArg (fun q => Finset (ZMod q)) h1.symm) D =
      Eq.mp (congrArg (fun q => Finset (ZMod q)) h2.symm) D := by
  cases h1
  rfl

theorem CRTGadget.cast_modulus {P : Finset ℕ} {m : ℕ → ℕ} {M M' a : ℕ}
    {D : Finset (ZMod M')} (hM : M = M')
    (hG : Nonempty (CRTGadget P m M' a D)) :
    Nonempty (CRTGadget P m M a
      (Eq.mp (congrArg (fun q => Finset (ZMod q)) hM.symm) D)) := by
  exact hG.elim fun G => ⟨CRTGadget.castModulus hM G⟩

theorem exists_activated_CRTGadget_on_allowedAtM (st : StageState)
    {a b p : ℕ} (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    Nonempty (CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedM st b p) a (activatedCRTAllowedFinsetAtM st ha hbDormant hp)) := by
  have hM :
      activatedM st b p =
        activatedModulus st b p a *
          ∏ i : NonselectedIndex (activatedActiveSet st b) a,
            activatedModulus st b p (i : ℕ) :=
    activatedM_eq_selected_mul_nonselected (a := a) (b := b) (p := p) st ha
  simpa [activatedCRTAllowedFinsetAtM] using
    (CRTGadget.cast_modulus (P := activatedActiveSet st b) (m := activatedModulus st b p)
      (a := a) hM
      (exists_activated_exact_product_CRTGadget_on_allowed st ha hbDormant hp))

/--
Concrete numeric and CRT choices for one service-and-tail stage after activating
`b`.  The inequality fields are intentionally added only as later lemmas need
them; this structure starts by naming the three new finite blocks.
-/
structure StageParams (st : StageState) (a b p : ℕ) where
  Dplus : Finset (ZMod (activatedM st b p))
  G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
    (activatedM st b p) a Dplus
  N : ℕ
  L : ℕ
  LZ : ℕ

noncomputable def canonicalStageParams (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (N L LZ : ℕ) : StageParams st a b p :=
  {
    Dplus := activatedCRTAllowedFinsetAtM st ha hbDormant hp
    G := Classical.choice (exists_activated_CRTGadget_on_allowedAtM st ha hbDormant hp)
    N := N
    L := L
    LZ := LZ
  }

noncomputable def stageParamsOfActivatedExactGadget (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ))
      a (activatedCRTAllowedFinsetExact st ha hbDormant hp))
    (N L LZ : ℕ) : StageParams st a b p :=
  let hM : activatedM st b p =
      activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ) :=
    activatedM_eq_selected_mul_nonselected (a := a) (b := b) (p := p) st ha
  {
    Dplus := activatedCRTAllowedFinsetAtM st ha hbDormant hp
    G := CRTGadget.castModulus hM G
    N := N
    L := L
    LZ := LZ
  }

theorem stageParamsOfActivatedExactGadget_Dplus_eq (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ))
      a (activatedCRTAllowedFinsetExact st ha hbDormant hp))
    (N L LZ : ℕ) :
    (stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ).Dplus =
      activatedCRTAllowedFinsetAtM st ha hbDormant hp := by
  rfl

theorem stageParamsOfActivatedExactGadget_Tbase_eq (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
      (activatedModulus st b p a *
        ∏ i : NonselectedIndex (activatedActiveSet st b) a,
          activatedModulus st b p (i : ℕ))
      a (activatedCRTAllowedFinsetExact st ha hbDormant hp))
    (N L LZ : ℕ) (h u1 u2 : ZMod (activatedModulus st b p a))
    (hG : G.Tbase = activatedCRTTbaseFinsetExact st ha hbDormant hp h u1 u2) :
    (stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ).G.Tbase =
      activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 := by
  dsimp [stageParamsOfActivatedExactGadget, activatedCRTTbaseFinsetAtM]
  rw [CRTGadget.castModulus_Tbase, hG]
  exact eqMp_zmodFinset_eq_of_eq
    (activatedM_eq_selected_mul_nonselected (a := a) (b := b) (p := p) st ha)
    (activatedM_eq_selected_mul_nonselected (a := a) (b := b) (p := p) st ha)
    (activatedCRTTbaseFinsetExact st ha hbDormant hp h u1 u2)

theorem exists_stageParams_with_activated_Tbase_eq (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (N L LZ : ℕ) :
    ∃ h u1 u2 : ZMod (activatedModulus st b p a),
      ∃ params : StageParams st a b p,
        params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp ∧
        params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2 := by
  classical
  let : Fact (Nat.Prime (activatedModulus st b p a)) :=
    ⟨activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)⟩
  let : NeZero (activatedModulus st b p a) :=
    NeZero.of_pos
      ((activated_m_prime st hbDormant hp a (activated_active_mem_old st ha)).pos)
  let : NeZero (activatedModulus st b p a *
      ∏ i : NonselectedIndex (activatedActiveSet st b) a,
        activatedModulus st b p (i : ℕ)) :=
    NeZero.of_pos (activated_exact_product_pos st ha hbDormant hp)
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fact (Nat.Prime (activatedModulus st b p (i : ℕ))) := fun i =>
    ⟨activated_m_prime st hbDormant hp (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  let : (i : NonselectedIndex (activatedActiveSet st b) a) →
      Fintype (ZMod (activatedModulus st b p (i : ℕ))) := fun _ =>
    inferInstance
  obtain ⟨h, u1, u2, G, _hT, _hPstar, hTbase⟩ :=
    exists_activated_exact_product_CRTGadget_on_allowed_with_eqs st ha hbDormant hp
  let params := stageParamsOfActivatedExactGadget st ha hbDormant hp G N L LZ
  refine ⟨h, u1, u2, params, ?_, ?_⟩
  · exact stageParamsOfActivatedExactGadget_Dplus_eq st ha hbDormant hp G N L LZ
  · exact stageParamsOfActivatedExactGadget_Tbase_eq st ha hbDormant hp G N L LZ
      h u1 u2 hTbase

theorem canonicalStageParams_Dplus_add_self_eq_univ (st : StageState) {a b p : ℕ}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (N L LZ : ℕ) :
    let params := canonicalStageParams st ha hbDormant hp N L LZ
    ((params.Dplus : Set (ZMod (activatedM st b p))) +
      (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ := by
  dsimp [canonicalStageParams]
  exact activatedCRTAllowedFinsetAtM_add_self_eq_univ st ha hbDormant hp

namespace StageParams

def Mplus {st : StageState} {a b p : ℕ} (_params : StageParams st a b p) : ℕ :=
  activatedM st b p

/-- Endpoint reached after the service block and private block. -/
def serviceR {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  2 * params.N + 2 * params.L - params.Mplus

/-- Endpoint of the protected private sums, before the tail starts. -/
def protectedEndpoint {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  params.serviceR - st.X

/-- Lower endpoint of the next tail reservoir. -/
def K {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  params.protectedEndpoint + 1

def nextX {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  params.K + params.LZ

def nextR {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  2 * params.K + 2 * params.LZ - params.Mplus

/-- The service block using the CRT gadget's `T` residues. -/
def lowerBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  residueBlockFinset params.Mplus params.G.T params.N (params.N + params.L)

/-- The private-partner block whose translate by `a` is protected. -/
def privateBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  residueBlockFinset params.Mplus params.G.Pstar
    (2 * params.N + params.Mplus - a) (params.serviceR - a)

/-- The tail reservoir for the next stage. -/
def tailBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  residueBlockFinset params.Mplus params.Dplus params.K params.nextX

/-- The finite set after adding all three new blocks. -/
def nextS {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  ((st.S ∪ params.lowerBlock) ∪ params.privateBlock) ∪ params.tailBlock

theorem old_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    st.S ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem lowerBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.lowerBlock ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem privateBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.privateBlock ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem tailBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.tailBlock ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem old_union_lowerBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    st.S ∪ params.lowerBlock ⊆ params.nextS := by
  intro n hn
  rw [Finset.mem_union] at hn
  rcases hn with hnS | hnLower
  · exact params.old_subset_nextS hnS
  · exact params.lowerBlock_subset_nextS hnLower

theorem old_union_tailBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    st.S ∪ params.tailBlock ⊆ params.nextS := by
  intro n hn
  rw [Finset.mem_union] at hn
  rcases hn with hnS | hnTail
  · exact params.old_subset_nextS hnS
  · exact params.tailBlock_subset_nextS hnTail

theorem mem_lowerBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.lowerBlock ↔
      params.N ≤ n ∧ n ≤ params.N + params.L ∧ (n : ZMod params.Mplus) ∈ params.G.T := by
  simp [lowerBlock, mem_residueBlockFinset]

theorem mem_privateBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.privateBlock ↔
      2 * params.N + params.Mplus - a ≤ n ∧ n ≤ params.serviceR - a ∧
        (n : ZMod params.Mplus) ∈ params.G.Pstar := by
  simp [privateBlock, mem_residueBlockFinset]

theorem mem_tailBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.tailBlock ↔
      params.K ≤ n ∧ n ≤ params.nextX ∧ (n : ZMod params.Mplus) ∈ params.Dplus := by
  simp [tailBlock, mem_residueBlockFinset, nextX]

theorem privateBlock_lo_gt_X {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) (ha : a ∈ st.P) (hN : st.X < params.N) :
    st.X < 2 * params.N + params.Mplus - a := by
  have haX : a ≤ st.X := st.active_le_X ha
  omega

theorem nextS_new_elements_above_old_X {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) (ha : a ∈ st.P)
    (hN : st.X < params.N) (hK : st.X < params.K) :
    ∀ n ∈ params.nextS, n ∉ st.S → st.X < n := by
  classical
  intro n hn hnotS
  simp [nextS] at hn
  rcases hn with hnS | hnLower | hnPrivate | hnTail
  · exact (hnotS hnS).elim
  · rw [mem_lowerBlock] at hnLower
    exact lt_of_lt_of_le hN hnLower.1
  · rw [mem_privateBlock] at hnPrivate
    exact lt_of_lt_of_le (params.privateBlock_lo_gt_X ha hN) hnPrivate.1
  · rw [mem_tailBlock] at hnTail
    exact lt_of_lt_of_le hK hnTail.1

theorem nextS_new_elements_avoid_active {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
      (s : ZMod (activatedModulus st b p c)) ≠
        (c : ZMod (activatedModulus st b p c)) := by
  classical
  intro c hc s hs hnotS
  simp [nextS] at hs
  rcases hs with hsOld | hsLower | hsPrivate | hsTail
  · exact (hnotS hsOld).elim
  · rw [mem_lowerBlock] at hsLower
    exact params.G.D_nat_avoid c hc s
      (params.G.T_subset_D (by simpa [StageParams.Mplus] using hsLower.2.2))
  · rw [mem_privateBlock] at hsPrivate
    exact params.G.D_nat_avoid c hc s
      (params.G.Pstar_subset_D (by simpa [StageParams.Mplus] using hsPrivate.2.2))
  · rw [mem_tailBlock] at hsTail
    exact params.G.D_nat_avoid c hc s (by simpa [StageParams.Mplus] using hsTail.2.2)

theorem nextS_le_nextX {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (hX : st.X ≤ params.nextX)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate : params.serviceR ≤ params.nextX) :
    ∀ n ∈ params.nextS, n ≤ params.nextX := by
  classical
  intro n hn
  simp [nextS] at hn
  rcases hn with hnS | hnLower | hnPrivate | hnTail
  · exact (st.S_le_X n hnS).trans hX
  · rw [mem_lowerBlock] at hnLower
    exact hnLower.2.1.trans hlower
  · rw [mem_privateBlock] at hnPrivate
    omega
  · rw [mem_tailBlock] at hnTail
    exact hnTail.2.1

/--
Partners in the private block whose translated sums lie in the permanent
protected core: above the lower service range and below `protectedEndpoint`.
-/
def protectedPartnerBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  params.privateBlock.filter fun q =>
    st.X + params.N + params.L < a + q ∧ a + q < params.protectedEndpoint

/-- The protected sums `a + q` generated by the protected partner core. -/
def protectedSumBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  params.protectedPartnerBlock.image fun q => a + q

theorem mem_protectedPartnerBlock {st : StageState} {a b p q : ℕ}
    {params : StageParams st a b p} :
    q ∈ params.protectedPartnerBlock ↔
      q ∈ params.privateBlock ∧
        st.X + params.N + params.L < a + q ∧ a + q < params.protectedEndpoint := by
  classical
  simp [protectedPartnerBlock]

theorem mem_protectedSumBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.protectedSumBlock ↔
      ∃ q ∈ params.privateBlock,
        st.X + params.N + params.L < a + q ∧
          a + q < params.protectedEndpoint ∧ n = a + q := by
  classical
  rw [protectedSumBlock]
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
    rw [mem_protectedPartnerBlock] at hq
    exact ⟨q, hq.1, hq.2.1, hq.2.2, rfl⟩
  · rintro ⟨q, hqPrivate, hqLower, hqUpper, rfl⟩
    exact Finset.mem_image.mpr ⟨q, (mem_protectedPartnerBlock.mpr
      ⟨hqPrivate, hqLower, hqUpper⟩), rfl⟩

theorem protectedSumBlock_lt_endpoint {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} (hn : n ∈ params.protectedSumBlock) :
    n < params.protectedEndpoint := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q, _hq, _hlo, hhi, rfl⟩
  exact hhi

theorem protectedSumBlock_le_endpoint {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} (hn : n ∈ params.protectedSumBlock) :
    n ≤ params.protectedEndpoint :=
  (protectedSumBlock_lt_endpoint hn).le

theorem protectedSumBlock_mem_twoFold_nextS {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} (haS : a ∈ st.S)
    (hn : n ∈ params.protectedSumBlock) :
    n ∈ twoFoldFinset params.nextS := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q, hqPrivate, _hlo, _hhi, rfl⟩
  exact ⟨a, params.old_subset_nextS haS, q, params.privateBlock_subset_nextS hqPrivate, rfl⟩

theorem protectedSumBlock_ne_old_add_old {st : StageState} {a b p n x y : ℕ}
    {params : StageParams st a b p} (hN : st.X < params.N)
    (hn : n ∈ params.protectedSumBlock) (hx : x ∈ st.S) (hy : y ∈ st.S) :
    x + y ≠ n := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q, _hq, hlo, _hhi, rfl⟩
  have hxX := st.S_le_X x hx
  have hyX := st.S_le_X y hy
  omega

theorem protectedSumBlock_ne_old_add_lower {st : StageState} {a b p n x y : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hx : x ∈ st.S) (hy : y ∈ params.lowerBlock) :
    x + y ≠ n := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q, _hq, hlo, _hhi, rfl⟩
  rw [mem_lowerBlock] at hy
  have hxX := st.S_le_X x hx
  omega

theorem protectedSumBlock_ne_lower_add_old {st : StageState} {a b p n x y : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hx : x ∈ params.lowerBlock) (hy : y ∈ st.S) :
    x + y ≠ n := by
  intro hxy
  exact protectedSumBlock_ne_old_add_lower (params := params) hn hy hx (by omega)

theorem protectedSumBlock_lt_tail {st : StageState} {a b p n z : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hz : z ∈ params.tailBlock) :
    n < z := by
  have hnlt := protectedSumBlock_lt_endpoint (params := params) hn
  rw [mem_tailBlock] at hz
  dsimp [K] at hz
  omega

theorem protectedSumBlock_ne_tail_add_any {st : StageState} {a b p n x y : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hx : x ∈ params.tailBlock) :
    x + y ≠ n := by
  have hlt : n < x := protectedSumBlock_lt_tail (params := params) hn hx
  omega

theorem protectedSumBlock_ne_any_add_tail {st : StageState} {a b p n x y : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hy : y ∈ params.tailBlock) :
    x + y ≠ n := by
  have hlt : n < y := protectedSumBlock_lt_tail (params := params) hn hy
  omega

theorem protectedSumBlock_ne_lower_add_lower {st : StageState} {a b p n x y : ℕ}
    {params : StageParams st a b p} [NeZero (activatedM st b p)]
    (hn : n ∈ params.protectedSumBlock) (hx : x ∈ params.lowerBlock)
    (hy : y ∈ params.lowerBlock) :
    x + y ≠ n := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q, hqPrivate, _hlo, _hhi, rfl⟩
  rw [mem_privateBlock] at hqPrivate
  have hprivateSlice : ((a + q : ℕ) : ZMod (activatedM st b p)) ∈
      ((fun z : ZMod (activatedM st b p) => (a : ZMod (activatedM st b p)) + z) ''
        (params.G.Pstar : Set (ZMod (activatedM st b p)))) := by
    refine ⟨(q : ZMod (activatedM st b p)), ?_, ?_⟩
    · simpa [StageParams.Mplus] using hqPrivate.2.2
    · simp [Nat.cast_add]
  rw [mem_lowerBlock] at hx hy
  intro hxy
  have hsum_mem : ((a + q : ℕ) : ZMod (activatedM st b p)) ∈
      (params.G.T : Set (ZMod (activatedM st b p))) +
        (params.G.T : Set (ZMod (activatedM st b p))) := by
    refine ⟨(x : ZMod (activatedM st b p)), ?_, (y : ZMod (activatedM st b p)), ?_, ?_⟩
    · simpa [StageParams.Mplus] using hx.2.2
    · simpa [StageParams.Mplus] using hy.2.2
    · rw [← hxy]
      simp [Nat.cast_add]
  rw [params.G.T_add_T_compl_private] at hsum_mem
  exact hsum_mem.2 hprivateSlice

theorem privateBlock_selectedCoord {st : StageState} {a b p q : ℕ}
    {params : StageParams st a b p} (hq : q ∈ params.privateBlock) :
    (q : ZMod (activatedModulus st b p a)) = params.G.privateResidue := by
  rw [mem_privateBlock] at hq
  rw [← params.G.selectedCoord_natCast q]
  exact params.G.Pstar_selected (q : ZMod (activatedM st b p))
    (by simpa [StageParams.Mplus] using hq.2.2)

theorem lowerBlock_selectedCoord_ne_active {st : StageState} {a b p x : ℕ}
    {params : StageParams st a b p} (hx : x ∈ params.lowerBlock) :
    (x : ZMod (activatedModulus st b p a)) ≠ (a : ZMod (activatedModulus st b p a)) := by
  rw [mem_lowerBlock] at hx
  rw [← params.G.selectedCoord_natCast x]
  exact params.G.T_selected_avoid (x : ZMod (activatedM st b p))
    (by simpa [StageParams.Mplus] using hx.2.2)

theorem protectedSumBlock_ne_old_add_private {st : StageState} {a b p n s q : ℕ}
    {params : StageParams st a b p}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P)
    (hn : n ∈ params.protectedSumBlock) (hs : s ∈ st.S) (hs_ne : s ≠ a)
    (hq : q ∈ params.privateBlock) :
    s + q ≠ n := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q₀, hq₀, _hlo, _hhi, rfl⟩
  intro hsum
  have hqsel := privateBlock_selectedCoord (params := params) hq
  have hq₀sel := privateBlock_selectedCoord (params := params) hq₀
  have hselected :
      (s : ZMod (activatedModulus st b p a)) =
        (a : ZMod (activatedModulus st b p a)) := by
    have hcast : ((s + q : ℕ) : ZMod (activatedModulus st b p a)) =
        ((a + q₀ : ℕ) : ZMod (activatedModulus st b p a)) := by
      rw [hsum]
    rw [Nat.cast_add, Nat.cast_add, hqsel, hq₀sel] at hcast
    linear_combination hcast
  have hselected_old : (s : ZMod (st.m a)) = (a : ZMod (st.m a)) := by
    rwa [activatedModulus_old_of_mem st hbDormant ha] at hselected
  exact hs_ne (st.isolated a ha s hs hselected_old)

theorem protectedSumBlock_ne_private_add_old {st : StageState} {a b p n q s : ℕ}
    {params : StageParams st a b p}
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P)
    (hn : n ∈ params.protectedSumBlock) (hq : q ∈ params.privateBlock)
    (hs : s ∈ st.S) (hs_ne : s ≠ a) :
    q + s ≠ n := by
  intro hsum
  exact protectedSumBlock_ne_old_add_private (params := params) ha hbDormant hn hs hs_ne hq
    (by omega)

theorem protectedSumBlock_ne_lower_add_private {st : StageState} {a b p n x q : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hx : x ∈ params.lowerBlock)
    (hq : q ∈ params.privateBlock) :
    x + q ≠ n := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q₀, hq₀, _hlo, _hhi, rfl⟩
  intro hsum
  have hqsel := privateBlock_selectedCoord (params := params) hq
  have hq₀sel := privateBlock_selectedCoord (params := params) hq₀
  have hselected :
      (x : ZMod (activatedModulus st b p a)) =
        (a : ZMod (activatedModulus st b p a)) := by
    have hcast : ((x + q : ℕ) : ZMod (activatedModulus st b p a)) =
        ((a + q₀ : ℕ) : ZMod (activatedModulus st b p a)) := by
      rw [hsum]
    rw [Nat.cast_add, Nat.cast_add, hqsel, hq₀sel] at hcast
    linear_combination hcast
  exact (lowerBlock_selectedCoord_ne_active (params := params) hx) hselected

theorem protectedSumBlock_ne_private_add_lower {st : StageState} {a b p n q x : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hq : q ∈ params.privateBlock)
    (hx : x ∈ params.lowerBlock) :
    q + x ≠ n := by
  intro hsum
  exact protectedSumBlock_ne_lower_add_private (params := params) hn hx hq (by omega)

theorem protectedSumBlock_ne_private_add_private {st : StageState} {a b p n q₁ q₂ : ℕ}
    {params : StageParams st a b p}
    (hn : n ∈ params.protectedSumBlock) (hq₁ : q₁ ∈ params.privateBlock)
    (hq₂ : q₂ ∈ params.privateBlock) :
    q₁ + q₂ ≠ n := by
  rw [mem_protectedSumBlock] at hn
  rcases hn with ⟨q₀, hq₀, _hlo, _hhi, rfl⟩
  intro hsum
  have hq₁sel := privateBlock_selectedCoord (params := params) hq₁
  have hq₂sel := privateBlock_selectedCoord (params := params) hq₂
  have hq₀sel := privateBlock_selectedCoord (params := params) hq₀
  have hbad :
      params.G.privateResidue = (a : ZMod (activatedModulus st b p a)) := by
    have hcast : ((q₁ + q₂ : ℕ) : ZMod (activatedModulus st b p a)) =
        ((a + q₀ : ℕ) : ZMod (activatedModulus st b p a)) := by
      rw [hsum]
    rw [Nat.cast_add, Nat.cast_add, hq₁sel, hq₂sel, hq₀sel] at hcast
    linear_combination hcast
  exact params.G.privateResidue_ne_active hbad

theorem protectedSumBlock_card_eq_partner {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.protectedSumBlock.card = params.protectedPartnerBlock.card := by
  classical
  rw [protectedSumBlock]
  exact Finset.card_image_of_injective _ (fun x y hxy => Nat.add_left_cancel hxy)

theorem protectedSumBlock_density_of_partner_density {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) {densityNumerator densityDenominator : ℕ}
    (hpartner :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * params.protectedPartnerBlock.card) :
    densityNumerator * params.protectedEndpoint ≤
      densityDenominator * params.protectedSumBlock.card := by
  rwa [protectedSumBlock_card_eq_partner params]

theorem protectedResidueSubblock_subset_partner {st : StageState} {a b p lo hi : ℕ}
    (params : StageParams st a b p)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint) :
    residueBlockFinset params.Mplus params.G.Pstar lo hi ⊆ params.protectedPartnerBlock := by
  intro q hq
  rw [mem_residueBlockFinset] at hq
  rw [mem_protectedPartnerBlock]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_privateBlock]
    exact ⟨hlo_private.trans hq.1, hq.2.1.trans hhi_private, hq.2.2⟩
  · omega
  · omega

theorem protectedPartnerBlock_card_lower_of_residue_subblock {st : StageState}
    {a b p lo hi : ℕ} (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint) :
    params.G.Pstar.card * ((hi - lo) / params.Mplus) ≤ params.protectedPartnerBlock.card := by
  let : NeZero params.Mplus := (inferInstance : NeZero (activatedM st b p))
  have hsub := protectedResidueSubblock_subset_partner (params := params) (lo := lo) (hi := hi)
    hlo_private hhi_private hlo_sum hhi_sum
  have hcount : params.G.Pstar.card * ((hi - lo) / params.Mplus) ≤
      (residueBlockFinset params.Mplus params.G.Pstar lo hi).card :=
    residueBlockFinset_card_lower_of_le params.Mplus params.G.Pstar hlohi
  exact hcount.trans (Finset.card_le_card hsub)

theorem protectedSumBlock_density_of_residue_subblock {st : StageState}
    {a b p lo hi densityNumerator densityDenominator : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    densityNumerator * params.protectedEndpoint ≤
      densityDenominator * params.protectedSumBlock.card := by
  have hpartner_lower :=
    protectedPartnerBlock_card_lower_of_residue_subblock (params := params) (lo := lo) (hi := hi)
      hlohi hlo_private hhi_private hlo_sum hhi_sum
  have hpartner_density : densityNumerator * params.protectedEndpoint ≤
      densityDenominator * params.protectedPartnerBlock.card := by
    exact harith.trans (Nat.mul_le_mul_left densityDenominator hpartner_lower)
  exact protectedSumBlock_density_of_partner_density params hpartner_density

theorem protectedSumBlock_private_of_pair_exclusions {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (haS : a ∈ st.S) (hN : st.X < params.N)
    (hold_private :
      ∀ n ∈ params.protectedSumBlock, ∀ s ∈ st.S, s ≠ a →
        ∀ q ∈ params.privateBlock, s + q ≠ n)
    (hprivate_old :
      ∀ n ∈ params.protectedSumBlock, ∀ q ∈ params.privateBlock,
        ∀ s ∈ st.S, s ≠ a → q + s ≠ n)
    (hlower_private :
      ∀ n ∈ params.protectedSumBlock, ∀ x ∈ params.lowerBlock,
        ∀ q ∈ params.privateBlock, x + q ≠ n)
    (hprivate_lower :
      ∀ n ∈ params.protectedSumBlock, ∀ q ∈ params.privateBlock,
        ∀ x ∈ params.lowerBlock, q + x ≠ n)
    (hprivate_private :
      ∀ n ∈ params.protectedSumBlock, ∀ q₁ ∈ params.privateBlock,
        ∀ q₂ ∈ params.privateBlock, q₁ + q₂ ≠ n) :
    ∀ n ∈ params.protectedSumBlock, n ∈ privateSet {x : ℕ | x ∈ params.nextS} a := by
  classical
  intro n hn
  refine ⟨protectedSumBlock_mem_twoFold_nextS haS hn, ?_⟩
  intro hwithout
  rcases hwithout with ⟨x, hx, y, hy, hxy⟩
  have hx_ne : x ≠ a := by
    intro hxa
    exact hx.2 (by simp [hxa])
  have hy_ne : y ≠ a := by
    intro hya
    exact hy.2 (by simp [hya])
  have hxNext := hx.1
  have hyNext := hy.1
  simp [StageParams.nextS] at hxNext hyNext
  rcases hxNext with hxOld | hxLower | hxPrivate | hxTail
  · rcases hyNext with hyOld | hyLower | hyPrivate | hyTail
    · exact (protectedSumBlock_ne_old_add_old (params := params) hN hn hxOld hyOld) hxy
    · exact (protectedSumBlock_ne_old_add_lower (params := params) hn hxOld hyLower) hxy
    · exact (hold_private n hn x hxOld hx_ne y hyPrivate) hxy
    · exact (protectedSumBlock_ne_any_add_tail (params := params) hn hyTail) hxy
  · rcases hyNext with hyOld | hyLower | hyPrivate | hyTail
    · exact (protectedSumBlock_ne_lower_add_old (params := params) hn hxLower hyOld) hxy
    · exact (protectedSumBlock_ne_lower_add_lower (params := params) hn hxLower hyLower) hxy
    · exact (hlower_private n hn x hxLower y hyPrivate) hxy
    · exact (protectedSumBlock_ne_any_add_tail (params := params) hn hyTail) hxy
  · rcases hyNext with hyOld | hyLower | hyPrivate | hyTail
    · exact (hprivate_old n hn x hxPrivate y hyOld hy_ne) hxy
    · exact (hprivate_lower n hn x hxPrivate y hyLower) hxy
    · exact (hprivate_private n hn x hxPrivate y hyPrivate) hxy
    · exact (protectedSumBlock_ne_any_add_tail (params := params) hn hyTail) hxy
  · exact (protectedSumBlock_ne_tail_add_any (params := params) hn hxTail) hxy

theorem protectedSumBlock_private {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hN : st.X < params.N) :
    ∀ n ∈ params.protectedSumBlock, n ∈ privateSet {x : ℕ | x ∈ params.nextS} a := by
  refine params.protectedSumBlock_private_of_pair_exclusions (st.active_mem_state ha) hN
    ?_ ?_ ?_ ?_ ?_
  · intro n hn s hs hs_ne q hq
    exact protectedSumBlock_ne_old_add_private (params := params) ha hbDormant hn hs hs_ne hq
  · intro n hn q hq s hs hs_ne
    exact protectedSumBlock_ne_private_add_old (params := params) ha hbDormant hn hq hs hs_ne
  · intro n hn x hx q hq
    exact protectedSumBlock_ne_lower_add_private (params := params) hn hx hq
  · intro n hn q hq x hx
    exact protectedSumBlock_ne_private_add_lower (params := params) hn hq hx
  · intro n hn q₁ hq₁ q₂ hq₂
    exact protectedSumBlock_ne_private_add_private (params := params) hn hq₁ hq₂

def protectedBlockCertificate_of_sumBlock {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) {densityNumerator densityDenominator : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hprivate :
      ∀ n ∈ params.protectedSumBlock, n ∈ privateSet {x : ℕ | x ∈ params.nextS} a)
    (hdensity :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * params.protectedSumBlock.card) :
    ProtectedBlockCertificate params.nextS a params.protectedEndpoint := by
  exact {
    block := params.protectedSumBlock
    block_subset_private := hprivate
    block_le_endpoint := fun n hn => protectedSumBlock_le_endpoint hn
    block_lt_endpoint := fun n hn => protectedSumBlock_lt_endpoint hn
    densityNumerator := densityNumerator
    densityDenominator := densityDenominator
    densityDenominator_pos := hdensityDenominator_pos
    block_density_lower := hdensity
  }

end StageParams

theorem stageExtension_of_stageParams_next_state {st st' : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (hS : st'.S = params.nextS)
    (hP : st'.P = activatedActiveSet st b)
    (hm_old : ∀ c ∈ st.P, st'.m c = st.m c)
    (hcoverStart : st'.coverStart = st.coverStart)
    (hX : st.X ≤ st'.X) (hR : st.R ≤ st'.R)
    (ha : a ∈ st.P) (hN : st.X < params.N) (hK : st.X < params.K) :
    StageExtension st st' := by
  refine {
    S_subset := ?_
    P_subset := ?_
    m_eq_on_old := hm_old
    coverStart_eq := hcoverStart
    X_mono := hX
    R_mono := hR
    new_elements_above_old_X := ?_
  }
  · intro n hn
    rw [hS]
    exact params.old_subset_nextS hn
  · intro n hn
    rw [hP]
    exact Finset.mem_insert_of_mem hn
  · intro n hn hnotS
    rw [hS] at hn
    exact params.nextS_new_elements_above_old_X ha hN hK n hn hnotS

theorem stageParams_nextS_coverage_of_piecewise {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (lower_cover :
      ∀ n : ℕ, st.R < n → n < 2 * params.N + params.Mplus →
        n ∈ twoFoldFinset params.nextS)
    (middle_cover :
      ∀ n : ℕ, 2 * params.N + params.Mplus ≤ n → n ≤ params.serviceR →
        n ∈ twoFoldFinset params.nextS)
    (tail_cover :
      ∀ n : ℕ, params.serviceR < n → n < 2 * params.K + params.Mplus →
        n ∈ twoFoldFinset params.nextS)
    (tail_middle_cover :
      ∀ n : ℕ, 2 * params.K + params.Mplus ≤ n → n ≤ params.nextR →
        n ∈ twoFoldFinset params.nextS) :
    ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS := by
  intro n hn_start hn_end
  by_cases hn_old : n ≤ st.R
  · exact twoFoldFinset_mono params.old_subset_nextS (st.coverage n hn_start hn_old)
  have hn_R_lt : st.R < n := by omega
  by_cases hn_lower : n < 2 * params.N + params.Mplus
  · exact lower_cover n hn_R_lt hn_lower
  have hn_middle_start : 2 * params.N + params.Mplus ≤ n := by omega
  by_cases hn_middle : n ≤ params.serviceR
  · exact middle_cover n hn_middle_start hn_middle
  have hn_service_lt : params.serviceR < n := by omega
  by_cases hn_tail : n < 2 * params.K + params.Mplus
  · exact tail_cover n hn_service_lt hn_tail
  have hn_tail_middle_start : 2 * params.K + params.Mplus ≤ n := by omega
  exact tail_middle_cover n hn_tail_middle_start hn_end

theorem CRTGadget.T_middle_residueBlock_cover {P : Finset ℕ} {m : ℕ → ℕ}
    {M a : ℕ} {D : Finset (ZMod M)} [NeZero M]
    (G : CRTGadget P m M a D) {N L n : ℕ}
    (hML : M ≤ L) (hnlo : 2 * N + M ≤ n)
    (hnhi : n ≤ 2 * N + 2 * L - M)
    (hnot_private : (n : ZMod M) ∉
      ((fun x : ZMod M => (a : ZMod M) + x) '' (G.Pstar : Set (ZMod M)))) :
    n ∈ twoFoldFinset (residueBlockFinset M G.T N (N + L)) := by
  have hres : (n : ZMod M) ∈
      (G.T : Set (ZMod M)) + (G.T : Set (ZMod M)) := by
    rw [G.T_add_T_compl_private]
    exact ⟨Set.mem_univ _, hnot_private⟩
  exact residueBlockFinset_middle_mem_twoFold_self (M := M) (N := N) (L := L)
    (n := n) hML hnlo hnhi hres

theorem stageParams_middle_cover {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hN : st.X < params.N) (hML : params.Mplus ≤ params.L) :
    ∀ n : ℕ, 2 * params.N + params.Mplus ≤ n → n ≤ params.serviceR →
      n ∈ twoFoldFinset params.nextS := by
  intro n hnlo hnhi
  by_cases hprivate : (n : ZMod (activatedM st b p)) ∈
      ((fun x : ZMod (activatedM st b p) => (a : ZMod (activatedM st b p)) + x) ''
        (params.G.Pstar : Set (ZMod (activatedM st b p))))
  · rcases hprivate with ⟨ρ, hρ, hsum⟩
    have ha_le_n : a ≤ n := by
      have haX : a ≤ st.X := st.active_le_X ha
      omega
    have hρ_sub : ((n - a : ℕ) : ZMod (activatedM st b p)) = ρ := by
      calc
        ((n - a : ℕ) : ZMod (activatedM st b p)) =
            (n : ZMod (activatedM st b p)) - (a : ZMod (activatedM st b p)) := by
          exact Nat.cast_sub ha_le_n
        _ = ((a : ZMod (activatedM st b p)) + ρ) -
            (a : ZMod (activatedM st b p)) := by
          rw [← hsum]
        _ = ρ := by abel
    have hpartner : n - a ∈ params.privateBlock := by
      rw [StageParams.mem_privateBlock]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · omega
      · simpa [StageParams.Mplus, hρ_sub] using hρ
    refine ⟨a, params.old_subset_nextS (st.active_mem_state ha), n - a,
      params.privateBlock_subset_nextS hpartner, ?_⟩
    omega
  · have hBB : n ∈ twoFoldFinset params.lowerBlock :=
      params.G.T_middle_residueBlock_cover hML hnlo hnhi hprivate
    exact twoFoldFinset_mono params.lowerBlock_subset_nextS hBB

theorem residueBlock_middle_cover_of_add_univ {M N L n : ℕ} [NeZero M]
    (Ω : Finset (ZMod M))
    (hΩ : ((Ω : Set (ZMod M)) + (Ω : Set (ZMod M))) = Set.univ)
    (hML : M ≤ L) (hnlo : 2 * N + M ≤ n)
    (hnhi : n ≤ 2 * N + 2 * L - M) :
    n ∈ twoFoldFinset (residueBlockFinset M Ω N (N + L)) := by
  have hres : (n : ZMod M) ∈ (Ω : Set (ZMod M)) + (Ω : Set (ZMod M)) := by
    rw [hΩ]
    exact Set.mem_univ _
  exact residueBlockFinset_middle_mem_twoFold_self (M := M) (N := N) (L := L)
    (n := n) hML hnlo hnhi hres

theorem exists_two_in_residueBlock_triple_window (M Jlo : ℕ) [NeZero M]
    (ρ : ZMod M) :
    ∃ u ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) Jlo (Jlo + 3 * M),
      ∃ v ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) Jlo (Jlo + 3 * M),
        u ≠ v := by
  obtain ⟨u, hu_lo, hu_hi, huρ⟩ := exists_natCast_eq_zmod_in_Icc_len M Jlo ρ
  refine ⟨u, ?_, u + M, ?_, ?_⟩
  · rw [mem_residueBlockFinset]
    exact ⟨hu_lo, by omega, by simpa using huρ⟩
  · rw [mem_residueBlockFinset]
    refine ⟨by omega, ?_, ?_⟩
    · omega
    · have hyρ : ((u + M : ℕ) : ZMod M) = ρ := by
        calc
        ((u + M : ℕ) : ZMod M) = (u : ZMod M) + (M : ZMod M) := by
          exact Nat.cast_add u M
        _ = ρ := by simp [huρ]
      simpa using hyρ
  · have hMpos : 0 < M := NeZero.pos M
    omega

theorem stageParams_tail_middle_cover {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hDplus_add :
      ((params.Dplus : Set (ZMod (activatedM st b p))) +
        (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ)
    (hMLZ : params.Mplus ≤ params.LZ) :
    ∀ n : ℕ, 2 * params.K + params.Mplus ≤ n → n ≤ params.nextR →
      n ∈ twoFoldFinset params.nextS := by
  intro n hnlo hnhi
  have hZZ : n ∈ twoFoldFinset
      (residueBlockFinset (activatedM st b p) params.Dplus params.K (params.K + params.LZ)) :=
    residueBlock_middle_cover_of_add_univ params.Dplus hDplus_add hMLZ hnlo hnhi
  have htail : n ∈ twoFoldFinset params.tailBlock := by
    simpa [StageParams.tailBlock, StageParams.nextX, StageParams.Mplus] using hZZ
  exact twoFoldFinset_mono params.tailBlock_subset_nextS htail

theorem stageParams_tail_reservoir_multiplicity {st : StageState} {a b p Jlo : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (hJlo : params.K ≤ Jlo) (hJhi : Jlo + 3 * params.Mplus ≤ params.nextX)
    (ρ : ZMod (activatedM st b p)) (hρ : ρ ∈ params.Dplus) :
    ∃ u ∈ residueBlockFinset params.Mplus ({ρ} : Finset (ZMod params.Mplus))
        Jlo (Jlo + 3 * params.Mplus),
      ∃ v ∈ residueBlockFinset params.Mplus ({ρ} : Finset (ZMod params.Mplus))
          Jlo (Jlo + 3 * params.Mplus),
        u ≠ v ∧ u ∈ params.nextS ∧ v ∈ params.nextS := by
  obtain ⟨u, hu, v, hv, huv⟩ :=
    exists_two_in_residueBlock_triple_window (activatedM st b p) Jlo ρ
  have hu_tail : u ∈ params.tailBlock := by
    rw [StageParams.mem_tailBlock]
    rw [mem_residueBlockFinset] at hu
    have huρ : (u : ZMod (activatedM st b p)) = ρ := by simpa using hu.2.2
    refine ⟨hJlo.trans hu.1, hu.2.1.trans hJhi, ?_⟩
    change (u : ZMod (activatedM st b p)) ∈ params.Dplus
    simpa [huρ] using hρ
  have hv_tail : v ∈ params.tailBlock := by
    rw [StageParams.mem_tailBlock]
    rw [mem_residueBlockFinset] at hv
    have hvρ : (v : ZMod (activatedM st b p)) = ρ := by simpa using hv.2.2
    refine ⟨hJlo.trans hv.1, hv.2.1.trans hJhi, ?_⟩
    change (v : ZMod (activatedM st b p)) ∈ params.Dplus
    simpa [hvρ] using hρ
  refine ⟨u, by simpa [StageParams.Mplus] using hu, v, by simpa [StageParams.Mplus] using hv,
    huv, params.tailBlock_subset_nextS hu_tail, params.tailBlock_subset_nextS hv_tail⟩

theorem stageParams_lower_helper_cover {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (hhelper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T)
    (hCL : 3 * st.M ≤ params.L)
    (hstart : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hend : 2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1) :
    ∀ n : ℕ, st.R < n → n < 2 * params.N + params.Mplus →
      n ∈ twoFoldFinset params.nextS := by
  intro n hnR hnmid
  have hcover : n ∈ twoFoldFinset (st.S ∪ params.lowerBlock) := by
    have hnlo : st.H + params.N + 3 * st.M ≤ n := by omega
    have hnhi : n + 3 * st.M ≤ st.X + params.N + params.L := by omega
    simpa [StageParams.lowerBlock, StageParams.Mplus] using
      (residueBlock_helper_cover (M := activatedM st b p) (H := st.H) (X := st.X)
        (N := params.N) (L := params.L) (C := 3 * st.M) (Ω := params.G.T)
        (S := st.S) hhelper st.reservoir_long hCL hnlo hnhi)
  exact twoFoldFinset_mono params.old_union_lowerBlock_subset_nextS hcover

theorem stageParams_tail_helper_cover {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (hhelper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (hstart : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (hend : 2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1) :
    ∀ n : ℕ, params.serviceR < n → n < 2 * params.K + params.Mplus →
      n ∈ twoFoldFinset params.nextS := by
  intro n hnR hnmid
  have hcover : n ∈ twoFoldFinset (st.S ∪ params.tailBlock) := by
    have hnlo : st.H + params.K + 3 * st.M ≤ n := by
      omega
    have hnhi : n + 3 * st.M ≤ st.X + params.K + params.LZ := by omega
    simpa [StageParams.tailBlock, StageParams.nextX, StageParams.Mplus] using
      (residueBlock_helper_cover (M := activatedM st b p) (H := st.H) (X := st.X)
        (N := params.K) (L := params.LZ) (C := 3 * st.M) (Ω := params.Dplus)
        (S := st.S) hhelper st.reservoir_long hCLZ hnlo hnhi)
  exact twoFoldFinset_mono params.old_union_tailBlock_subset_nextS hcover

theorem activated_helper_of_old_residue_lift {st : StageState} {b p : ℕ}
    (hp : FreshPrimeData st p)
    (Ω : Finset (ZMod (activatedM st b p)))
    (hchoose : ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ Ω) :
    ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ Ω := by
  let : NeZero p := NeZero.of_pos hp.prime.pos
  intro Jlo hJlo hJhi γ
  exact exists_reservoir_helper_for_target_from_old_residue_lift st Ω hJlo hJhi
    hp.X_lt_p (fun γ => activatedFreshProjection st b p γ - (b : ZMod p))
    hchoose γ

theorem stageParams_T_helper_of_old_residue_lift {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) (hp : FreshPrimeData st p)
    (hchoose : ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T) :
    ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T :=
  activated_helper_of_old_residue_lift hp params.G.T hchoose

theorem stageParams_D_helper_of_old_residue_lift {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) (hp : FreshPrimeData st p)
    (hchoose : ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus) :
    ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus :=
  activated_helper_of_old_residue_lift hp params.Dplus hchoose

theorem stageParams_D_lift_of_oldD_add_and_projection_lift {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p) (hbDormant : b ∉ st.P)
    (hD_add : ((st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M))) = Set.univ)
    (hmem : ∀ y : ZMod (activatedM st b p),
      activatedOldProjection st hbDormant y ∈ st.D →
        activatedFreshProjection st b p y ≠ (b : ZMod p) → y ∈ params.Dplus) :
    ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus := by
  intro γ
  have hγ : activatedOldProjection st hbDormant γ ∈
      (st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M)) := by
    rw [hD_add]
    exact Set.mem_univ _
  rcases hγ with ⟨ρ, hρ, d, hd, hsum⟩
  refine ⟨ρ, hρ, ?_⟩
  intro u huρ huFresh
  let y : ZMod (activatedM st b p) := γ - (u : ZMod (activatedM st b p))
  have hyOld : activatedOldProjection st hbDormant y ∈ st.D := by
    have hyOldEq : activatedOldProjection st hbDormant y = d := by
      dsimp [y]
      rw [activatedOldProjection_sub_natCast, huρ]
      rw [← hsum]
      simp [sub_eq_add_neg, add_assoc]
    simpa [hyOldEq] using hd
  have hyFresh : activatedFreshProjection st b p y ≠ (b : ZMod p) := by
    dsimp [y]
    rw [activatedFreshProjection_sub_natCast]
    intro hy
    apply huFresh
    calc
      (u : ZMod p) =
          activatedFreshProjection st b p γ -
            (activatedFreshProjection st b p γ - (u : ZMod p)) := by abel
      _ = activatedFreshProjection st b p γ - (b : ZMod p) := by rw [hy]
  exact hmem y hyOld hyFresh

theorem stageParams_D_lift_of_oldD_add_canonicalDplus {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (hD_add : ((st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M))) = Set.univ) :
    ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus := by
  refine stageParams_D_lift_of_oldD_add_and_projection_lift params hbDormant hD_add ?_
  intro y hyOld hyFresh
  rw [hDplus]
  exact activatedCRTAllowedFinsetAtM_projection_lift st ha hbDormant hp y hyOld hyFresh

theorem stageParams_T_lift_of_oldD_add_oldSet_and_projection_lift {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p) (hbDormant : b ∉ st.P)
    (Ωold : Finset (ZMod st.M))
    (hcover : ((st.D : Set (ZMod st.M)) + (Ωold : Set (ZMod st.M))) = Set.univ)
    (hmem : ∀ y : ZMod (activatedM st b p),
      activatedOldProjection st hbDormant y ∈ Ωold →
        activatedFreshProjection st b p y ≠ (b : ZMod p) → y ∈ params.G.T) :
    ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T := by
  intro γ
  have hγ : activatedOldProjection st hbDormant γ ∈
      (st.D : Set (ZMod st.M)) + (Ωold : Set (ZMod st.M)) := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hγ with ⟨ρ, hρ, θ, hθ, hsum⟩
  refine ⟨ρ, hρ, ?_⟩
  intro u huρ huFresh
  let y : ZMod (activatedM st b p) := γ - (u : ZMod (activatedM st b p))
  have hyOld : activatedOldProjection st hbDormant y ∈ Ωold := by
    have hyOldEq : activatedOldProjection st hbDormant y = θ := by
      dsimp [y]
      rw [activatedOldProjection_sub_natCast, huρ]
      rw [← hsum]
      simp [sub_eq_add_neg, add_assoc]
    simpa [hyOldEq] using hθ
  have hyFresh : activatedFreshProjection st b p y ≠ (b : ZMod p) := by
    dsimp [y]
    rw [activatedFreshProjection_sub_natCast]
    intro hy
    apply huFresh
    calc
      (u : ZMod p) =
          activatedFreshProjection st b p γ -
            (activatedFreshProjection st b p γ - (u : ZMod p)) := by abel
      _ = activatedFreshProjection st b p γ - (b : ZMod p) := by rw [hy]
  exact hmem y hyOld hyFresh

theorem stageParams_T_projection_lift_of_stageTbase_eq {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (st.m a))
    (hTbase :
      params.G.Tbase =
        activatedCRTTbaseFinsetAtM st ha hbDormant hp
          (activatedSelectedOfOld st ha hbDormant h)
          (activatedSelectedOfOld st ha hbDormant u1)
          (activatedSelectedOfOld st ha hbDormant u2)) :
    ∀ y : ZMod (activatedM st b p),
      activatedOldProjection st hbDormant y ∈ stageCRTTbaseFinsetAtM st ha h u1 u2 →
        activatedFreshProjection st b p y ≠ (b : ZMod p) → y ∈ params.G.T := by
  intro y hyOld hyFresh
  have hyBase :
      y ∈ activatedCRTTbaseFinsetAtM st ha hbDormant hp
        (activatedSelectedOfOld st ha hbDormant h)
        (activatedSelectedOfOld st ha hbDormant u1)
        (activatedSelectedOfOld st ha hbDormant u2) :=
    activatedTbase_projection_lift_of_stageTbase st ha hbDormant hp h u1 u2
      y hyOld hyFresh
  exact params.G.Tbase_subset_T (by
    rw [hTbase]
    exact hyBase)

theorem stageParams_T_lift_of_stageTbase_eq {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (st.m a))
    (hcover :
      ((st.D : Set (ZMod st.M)) +
        (stageCRTTbaseFinsetAtM st ha h u1 u2 : Set (ZMod st.M))) = Set.univ)
    (hTbase :
      params.G.Tbase =
        activatedCRTTbaseFinsetAtM st ha hbDormant hp
          (activatedSelectedOfOld st ha hbDormant h)
          (activatedSelectedOfOld st ha hbDormant u1)
          (activatedSelectedOfOld st ha hbDormant u2)) :
    ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T := by
  exact stageParams_T_lift_of_oldD_add_oldSet_and_projection_lift params hbDormant
    (stageCRTTbaseFinsetAtM st ha h u1 u2) hcover
    (stageParams_T_projection_lift_of_stageTbase_eq params ha hbDormant hp h u1 u2 hTbase)

theorem stageParams_T_lift_of_stageTbase_eq_activated {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hcover :
      ((st.D : Set (ZMod st.M)) +
        (stageCRTTbaseFinsetAtM st ha
          (oldSelectedOfActivated st ha hbDormant h)
          (oldSelectedOfActivated st ha hbDormant u1)
          (oldSelectedOfActivated st ha hbDormant u2) : Set (ZMod st.M))) = Set.univ)
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2) :
    ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T := by
  refine stageParams_T_lift_of_stageTbase_eq params ha hbDormant hp
    (oldSelectedOfActivated st ha hbDormant h)
    (oldSelectedOfActivated st ha hbDormant u1)
    (oldSelectedOfActivated st ha hbDormant u2) hcover ?_
  rw [activatedSelectedOfOld_oldSelectedOfActivated st ha hbDormant h,
    activatedSelectedOfOld_oldSelectedOfActivated st ha hbDormant u1,
    activatedSelectedOfOld_oldSelectedOfActivated st ha hbDormant u2]
  exact hTbase

theorem stageParams_T_lift_of_canonicalD_stageTbase_eq_activated {st : StageState}
    {a b p : ℕ} (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (hD : st.D = stageCRTAllowedFinsetAtM st ha)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2) :
    ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T := by
  refine stageParams_T_lift_of_stageTbase_eq_activated params ha hbDormant hp h u1 u2 ?_
    hTbase
  rw [hD]
  exact stageCRTAllowedFinsetAtM_add_Tbase_eq_univ st ha
    (oldSelectedOfActivated st ha hbDormant h)
    (oldSelectedOfActivated st ha hbDormant u1)
    (oldSelectedOfActivated st ha hbDormant u2)

theorem stageParams_nextS_coverage_of_helpers {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hN : st.X < params.N)
    (T_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T)
    (D_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus)
    (hDplus_add :
      ((params.Dplus : Set (ZMod (activatedM st b p))) +
        (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ) :
    ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS := by
  exact stageParams_nextS_coverage_of_piecewise params
    (stageParams_lower_helper_cover params T_helper hCL hlower_start hlower_end)
    (stageParams_middle_cover params ha hN hML)
    (stageParams_tail_helper_cover params D_helper hCLZ htail_start htail_end)
    (stageParams_tail_middle_cover params hDplus_add hMLZ)

theorem stageParams_isolated_of_new_avoid {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (hbS : b ∈ st.S) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c))) :
    ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS,
      (s : ZMod (activatedModulus st b p c)) =
        (c : ZMod (activatedModulus st b p c)) → s = c := by
  intro c hc s hs hcong
  by_cases hs_old : s ∈ st.S
  · rw [activatedActiveSet] at hc
    have hbX : b ≤ st.X := st.S_le_X b hbS
    rcases Finset.mem_insert.mp hc with rfl | hcP
    · rw [activatedModulus_new] at hcong
      exact hp.eq_of_zmod_eq_of_old (st.S_le_X s hs_old) hbX hcong
    · rw [activatedModulus_old_of_mem st hbDormant hcP] at hcong
      exact st.isolated c hcP s hs_old hcong
  · exact (hnew_avoid c hc s hs hs_old hcong).elim

noncomputable def nextStageStateOfParams (st : StageState) {a b p : ℕ}
    (params : StageParams st a b p)
    (hbS : b ∈ st.S) (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p)
    (hS_le : ∀ n ∈ params.nextS, n ≤ params.nextX)
    (hisolated :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS,
        (s : ZMod (activatedModulus st b p c)) =
          (c : ZMod (activatedModulus st b p c)) → s = c)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b) :
    StageState := by
  classical
  letI : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  exact {
    S := params.nextS
    P := activatedActiveSet st b
    m := activatedModulus st b p
    M := activatedM st b p
    D := params.Dplus
    H := params.K
    X := params.nextX
    R := params.nextR
    coverStart := st.coverStart
    P_subset_S := by
      intro c hc
      rw [activatedActiveSet] at hc
      rcases Finset.mem_insert.mp hc with rfl | hcP
      · exact params.old_subset_nextS hbS
      · exact params.old_subset_nextS (st.active_mem_state hcP)
    S_le_X := hS_le
    m_prime := activated_m_prime st hbDormant hp
    m_ge23 := activated_m_ge23 st hbDormant hp
    m_mod4 := activated_m_mod4 st hbDormant hp
    m_pairwise_coprime := activated_m_pairwise_coprime st hbDormant hp
    M_def := rfl
    isolated := hisolated
    reservoir_subset := by
      intro n hn
      simpa [StageParams.tailBlock, StageParams.Mplus] using
        (params.tailBlock_subset_nextS hn)
    reservoir_multiplicity := by
      intro Jlo hJlo hJhi ρ hρ
      simpa [StageParams.Mplus] using
        (stageParams_tail_reservoir_multiplicity params hJlo hJhi ρ hρ)
    reservoir_long := hreservoir_long
    headroom := hheadroom
    coverage := hcoverage
    exists_dormant := hexists_dormant
  }

theorem nextStageStateOfParams_hasCanonicalD {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hS_le : ∀ n ∈ params.nextS, n ≤ params.nextX)
    (hisolated :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS,
        (s : ZMod (activatedModulus st b p c)) =
          (c : ZMod (activatedModulus st b p c)) → s = c)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp) :
    (nextStageStateOfParams st params hbS hbDormant hp hS_le hisolated hreservoir_long
      hheadroom hcoverage hexists_dormant).HasCanonicalD := by
  classical
  let : NeZero (activatedM st b p) := NeZero.of_pos (activatedM_pos st hbDormant hp)
  let st' := nextStageStateOfParams st params hbS hbDormant hp hS_le hisolated
    hreservoir_long hheadroom hcoverage hexists_dormant
  intro c hc
  change params.Dplus = stageCRTAllowedFinsetAtM st' hc
  rw [hDplus]
  ext z
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [natCast_mem_activatedCRTAllowedFinsetAtM_iff_active st ha hbDormant hp]
  rw [natCast_mem_stageCRTAllowedFinsetAtM_iff_active st' hc]
  simp [st', nextStageStateOfParams]

theorem exists_stageExtension_of_params {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b) :
    ∃ st' : StageState,
      StageExtension st st' ∧
        st'.S = params.nextS ∧ st'.P = activatedActiveSet st b ∧
          st'.m = activatedModulus st b p ∧ st'.M = activatedM st b p ∧
            st'.H = params.K ∧ st'.X = params.nextX ∧
              st'.R = params.nextR ∧ st'.coverStart = st.coverStart := by
  let st' := nextStageStateOfParams st params hbS hbDormant hp
    (params.nextS_le_nextX hX_next hlower hprivate)
    (stageParams_isolated_of_new_avoid params hbS hbDormant hp hnew_avoid)
    hreservoir_long hheadroom hcoverage hexists_dormant
  refine ⟨st', ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine stageExtension_of_stageParams_next_state params (st' := st') rfl rfl ?_ rfl
    hX_next hR_next ha hN hK
  intro c hc
  exact activatedModulus_old_of_mem st hbDormant hc

theorem exists_stageExtension_of_params_hasCanonicalD {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b) :
    ∃ st' : StageState,
      StageExtension st st' ∧ st'.HasCanonicalD ∧
        st'.S = params.nextS ∧ st'.P = activatedActiveSet st b ∧
          st'.m = activatedModulus st b p ∧ st'.M = activatedM st b p ∧
            st'.H = params.K ∧ st'.X = params.nextX ∧
              st'.R = params.nextR ∧ st'.coverStart = st.coverStart := by
  let hS_le := params.nextS_le_nextX hX_next hlower hprivate
  let hisolated := stageParams_isolated_of_new_avoid params hbS hbDormant hp hnew_avoid
  let st' := nextStageStateOfParams st params hbS hbDormant hp hS_le hisolated
    hreservoir_long hheadroom hcoverage hexists_dormant
  refine ⟨st', ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine stageExtension_of_stageParams_next_state params (st' := st') rfl rfl ?_ rfl
      hX_next hR_next ha hN hK
    intro c hc
    exact activatedModulus_old_of_mem st hbDormant hc
  · exact nextStageStateOfParams_hasCanonicalD params ha hbS hbDormant hp hS_le hisolated
      hreservoir_long hheadroom hcoverage hexists_dormant hDplus

noncomputable def serviceExtensionOfParams {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    {densityNumerator densityDenominator : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hcore_private :
      ∀ n ∈ params.protectedSumBlock, n ∈ privateSet {x : ℕ | x ∈ params.nextS} a)
    (hcore_density :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * params.protectedSumBlock.card) :
    Σ st' : StageState, ServiceExtension st st' a := by
  let st' := nextStageStateOfParams st params hbS hbDormant hp
    (params.nextS_le_nextX hX_next hlower hprivate_height)
    (stageParams_isolated_of_new_avoid params hbS hbDormant hp hnew_avoid)
    hreservoir_long hheadroom hcoverage hexists_dormant
  let ext : StageExtension st st' :=
    stageExtension_of_stageParams_next_state params (st' := st') rfl rfl
      (by
        intro c hc
        exact activatedModulus_old_of_mem st hbDormant hc)
      rfl hX_next hR_next ha hN hK
  let cert : ProtectedBlockCertificate st'.S a params.protectedEndpoint :=
    params.protectedBlockCertificate_of_sumBlock hdensityDenominator_pos hcore_private
      hcore_density
  exact ⟨st', {
    toStageExtension := ext
    served_active := ha
    protectedEndpoint := params.protectedEndpoint
    protectedEndpoint_le_X := hendpoint_le_nextX
    protectedBlock := cert
  }⟩

/-- A service step together with the canonical-residue invariant for its target state. -/
structure CanonicalServiceExtension (st : StageState) (a : ℕ) where
  next : StageState
  service : ServiceExtension st next a
  canonicalD : next.HasCanonicalD

noncomputable def serviceExtensionOfParamsWithCanonicalD {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p)
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    {densityNumerator densityDenominator : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hcore_private :
      ∀ n ∈ params.protectedSumBlock, n ∈ privateSet {x : ℕ | x ∈ params.nextS} a)
    (hcore_density :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * params.protectedSumBlock.card) :
    CanonicalServiceExtension st a := by
  let hS_le := params.nextS_le_nextX hX_next hlower hprivate_height
  let hisolated := stageParams_isolated_of_new_avoid params hbS hbDormant hp hnew_avoid
  let st' := nextStageStateOfParams st params hbS hbDormant hp hS_le hisolated
    hreservoir_long hheadroom hcoverage hexists_dormant
  let ext : StageExtension st st' :=
    stageExtension_of_stageParams_next_state params (st' := st') rfl rfl
      (by
        intro c hc
        exact activatedModulus_old_of_mem st hbDormant hc)
      rfl hX_next hR_next ha hN hK
  let cert : ProtectedBlockCertificate st'.S a params.protectedEndpoint :=
    params.protectedBlockCertificate_of_sumBlock hdensityDenominator_pos hcore_private
      hcore_density
  exact {
    next := st'
    service := {
      toStageExtension := ext
      served_active := ha
      protectedEndpoint := params.protectedEndpoint
      protectedEndpoint_le_X := hendpoint_le_nextX
      protectedBlock := cert
    }
    canonicalD := nextStageStateOfParams_hasCanonicalD params ha hbS hbDormant hp hS_le hisolated
      hreservoir_long hheadroom hcoverage hexists_dormant hDplus
  }

noncomputable def serviceExtensionOfParamsFromPairExclusions {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    {densityNumerator densityDenominator : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hold_private :
      ∀ n ∈ params.protectedSumBlock, ∀ s ∈ st.S, s ≠ a →
        ∀ q ∈ params.privateBlock, s + q ≠ n)
    (hprivate_old :
      ∀ n ∈ params.protectedSumBlock, ∀ q ∈ params.privateBlock,
        ∀ s ∈ st.S, s ≠ a → q + s ≠ n)
    (hlower_private :
      ∀ n ∈ params.protectedSumBlock, ∀ x ∈ params.lowerBlock,
        ∀ q ∈ params.privateBlock, x + q ≠ n)
    (hprivate_lower :
      ∀ n ∈ params.protectedSumBlock, ∀ q ∈ params.privateBlock,
        ∀ x ∈ params.lowerBlock, q + x ≠ n)
    (hprivate_private :
      ∀ n ∈ params.protectedSumBlock, ∀ q₁ ∈ params.privateBlock,
        ∀ q₂ ∈ params.privateBlock, q₁ + q₂ ≠ n)
    (hcore_density :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * params.protectedSumBlock.card) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParams params ha hbS hbDormant hp hN hK hX_next hR_next hlower
    hprivate_height hnew_avoid hreservoir_long hheadroom hcoverage hexists_dormant
    hendpoint_le_nextX hdensityDenominator_pos
    (params.protectedSumBlock_private_of_pair_exclusions (st.active_mem_state ha) hN
      hold_private hprivate_old hlower_private hprivate_lower hprivate_private)
    hcore_density

noncomputable def serviceExtensionOfParamsWithProtectedCore {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    {densityNumerator densityDenominator : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hcore_density :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * params.protectedSumBlock.card) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParams params ha hbS hbDormant hp hN hK hX_next hR_next hlower
    hprivate_height hnew_avoid hreservoir_long hheadroom hcoverage hexists_dormant
    hendpoint_le_nextX hdensityDenominator_pos
    (params.protectedSumBlock_private ha hbDormant hN)
    hcore_density

noncomputable def serviceExtensionOfParamsWithResidueDensity {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hcoverage :
      ∀ n : ℕ, st.coverStart ≤ n → n ≤ params.nextR → n ∈ twoFoldFinset params.nextS)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParamsWithProtectedCore params ha hbS hbDormant hp hN hK hX_next
    hR_next hlower hprivate_height hnew_avoid hreservoir_long hheadroom hcoverage
    hexists_dormant hendpoint_le_nextX hdensityDenominator_pos
    (params.protectedSumBlock_density_of_residue_subblock (lo := lo) (hi := hi)
      hlohi hlo_private hhi_private hlo_sum hhi_sum harith)

noncomputable def serviceExtensionOfParamsFromHelpers {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower_height : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hnew_avoid :
      ∀ c ∈ activatedActiveSet st b, ∀ s ∈ params.nextS, s ∉ st.S →
        (s : ZMod (activatedModulus st b p c)) ≠
          (c : ZMod (activatedModulus st b p c)))
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    (T_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T)
    (D_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus)
    (hDplus_add :
      ((params.Dplus : Set (ZMod (activatedM st b p))) +
        (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParamsWithResidueDensity params ha hbS hbDormant hp hN hK hX_next
    hR_next hlower_height hprivate_height hnew_avoid hreservoir_long hheadroom
    (stageParams_nextS_coverage_of_helpers params ha hN T_helper D_helper hDplus_add hCL
      hlower_start hlower_end hML hCLZ htail_start htail_end hMLZ)
    hexists_dormant hendpoint_le_nextX hdensityDenominator_pos hlohi hlo_private
    hhi_private hlo_sum hhi_sum harith

noncomputable def serviceExtensionOfParamsFromHelpersAndAllowedAvoidance
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower_height : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    (T_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T)
    (D_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus)
    (hDplus_add :
      ((params.Dplus : Set (ZMod (activatedM st b p))) +
        (params.Dplus : Set (ZMod (activatedM st b p)))) = Set.univ)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParamsFromHelpers params ha hbS hbDormant hp hN hK hX_next
    hR_next hlower_height hprivate_height params.nextS_new_elements_avoid_active
    hreservoir_long hheadroom hexists_dormant hendpoint_le_nextX T_helper D_helper
    hDplus_add hCL hlower_start hlower_end hML hCLZ htail_start htail_end hMLZ
    hdensityDenominator_pos hlohi hlo_private hhi_private hlo_sum hhi_sum harith

noncomputable def serviceExtensionOfParamsFromCanonicalDplusAndHelpers
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower_height : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    (T_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T)
    (D_helper : ∀ Jlo, st.H ≤ Jlo → Jlo + 3 * st.M ≤ st.X →
      ∀ γ : ZMod (activatedM st b p),
        ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParamsFromHelpersAndAllowedAvoidance params ha hbS hbDormant hp
    hN hK hX_next hR_next hlower_height hprivate_height hreservoir_long hheadroom
    hexists_dormant hendpoint_le_nextX T_helper D_helper
    (by
      rw [hDplus]
      exact activatedCRTAllowedFinsetAtM_add_self_eq_univ st ha hbDormant hp)
    hCL hlower_start hlower_end hML hCLZ htail_start htail_end hMLZ
    hdensityDenominator_pos hlohi hlo_private hhi_private hlo_sum hhi_sum harith

noncomputable def serviceExtensionOfParamsFromCanonicalDplusAndResidueLifts
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower_height : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    (T_lift : ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.G.T)
    (D_lift : ∀ γ : ZMod (activatedM st b p), ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ →
        (u : ZMod p) ≠ activatedFreshProjection st b p γ - (b : ZMod p) →
          γ - (u : ZMod (activatedM st b p)) ∈ params.Dplus)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParamsFromCanonicalDplusAndHelpers params ha hbS hbDormant hp
    hDplus hN hK hX_next hR_next hlower_height hprivate_height hreservoir_long
    hheadroom hexists_dormant hendpoint_le_nextX
    (stageParams_T_helper_of_old_residue_lift params hp T_lift)
    (stageParams_D_helper_of_old_residue_lift params hp D_lift)
    hCL hlower_start hlower_end hML hCLZ htail_start htail_end hMLZ
    hdensityDenominator_pos hlohi hlo_private hhi_private hlo_sum hhi_sum harith

noncomputable def serviceExtensionOfParamsFromCanonicalDAndTbaseEq
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hD : st.D = stageCRTAllowedFinsetAtM st ha)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (h u1 u2 : ZMod (activatedModulus st b p a))
    (hTbase : params.G.Tbase = activatedCRTTbaseFinsetAtM st ha hbDormant hp h u1 u2)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower_height : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a := by
  have hD_add :
      ((st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M))) = Set.univ := by
    rw [hD]
    exact stageCRTAllowedFinsetAtM_add_self_eq_univ st ha
  exact serviceExtensionOfParamsFromCanonicalDplusAndResidueLifts params ha hbS
    hbDormant hp hDplus hN hK hX_next hR_next hlower_height hprivate_height
    hreservoir_long hheadroom hexists_dormant hendpoint_le_nextX
    (stageParams_T_lift_of_canonicalD_stageTbase_eq_activated params ha hbDormant hp
      hD h u1 u2 hTbase)
    (stageParams_D_lift_of_oldD_add_canonicalDplus params ha hbDormant hp hDplus hD_add)
    hCL hlower_start hlower_end hML hCLZ htail_start htail_end hMLZ
    hdensityDenominator_pos hlohi hlo_private hhi_private hlo_sum hhi_sum harith

noncomputable def serviceExtensionOfParamsFromOldProjectionLifts
    {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) [NeZero (activatedM st b p)]
    (oldG : CRTGadget st.P st.m st.M a st.D)
    (ha : a ∈ st.P) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (hp : FreshPrimeData st p)
    (hDplus : params.Dplus = activatedCRTAllowedFinsetAtM st ha hbDormant hp)
    (hDold_add :
      ((st.D : Set (ZMod st.M)) + (st.D : Set (ZMod st.M))) = Set.univ)
    (T_projection_lift : ∀ y : ZMod (activatedM st b p),
      activatedOldProjection st hbDormant y ∈ oldG.Tbase →
        activatedFreshProjection st b p y ≠ (b : ZMod p) → y ∈ params.G.T)
    (hN : st.X < params.N) (hK : st.X < params.K)
    (hX_next : st.X ≤ params.nextX) (hR_next : st.R ≤ params.nextR)
    (hlower_height : params.N + params.L ≤ params.nextX)
    (hprivate_height : params.serviceR ≤ params.nextX)
    (hreservoir_long : params.K + 3 * params.Mplus ≤ params.nextX)
    (hheadroom : params.K + params.nextX + 3 * params.Mplus ≤ params.nextR)
    (hexists_dormant : ∃ c ∈ params.nextS, c ∉ activatedActiveSet st b)
    (hendpoint_le_nextX : params.protectedEndpoint ≤ params.nextX)
    (hCL : 3 * st.M ≤ params.L)
    (hlower_start : st.H + params.N + 3 * st.M ≤ st.R + 1)
    (hlower_end :
      2 * params.N + params.Mplus + 3 * st.M ≤ st.X + params.N + params.L + 1)
    (hML : params.Mplus ≤ params.L)
    (hCLZ : 3 * st.M ≤ params.LZ)
    (htail_start : st.H + params.K + 3 * st.M ≤ params.serviceR + 1)
    (htail_end :
      2 * params.K + params.Mplus + 3 * st.M ≤ st.X + params.K + params.LZ + 1)
    (hMLZ : params.Mplus ≤ params.LZ)
    {densityNumerator densityDenominator lo hi : ℕ}
    (hdensityDenominator_pos : 0 < densityDenominator)
    (hlohi : lo ≤ hi)
    (hlo_private : 2 * params.N + params.Mplus - a ≤ lo)
    (hhi_private : hi ≤ params.serviceR - a)
    (hlo_sum : st.X + params.N + params.L < a + lo)
    (hhi_sum : a + hi < params.protectedEndpoint)
    (harith :
      densityNumerator * params.protectedEndpoint ≤
        densityDenominator * (params.G.Pstar.card * ((hi - lo) / params.Mplus))) :
    Σ st' : StageState, ServiceExtension st st' a :=
  serviceExtensionOfParamsFromCanonicalDplusAndResidueLifts params ha hbS hbDormant hp
    hDplus hN hK hX_next hR_next hlower_height hprivate_height hreservoir_long
    hheadroom hexists_dormant hendpoint_le_nextX
    (stageParams_T_lift_of_oldD_add_oldSet_and_projection_lift params hbDormant
      oldG.Tbase oldG.D_add_Tbase_full T_projection_lift)
    (stageParams_D_lift_of_oldD_add_canonicalDplus params ha hbDormant hp hDplus hDold_add)
    hCL hlower_start hlower_end hML hCLZ htail_start htail_end hMLZ
    hdensityDenominator_pos hlohi hlo_private hhi_private hlo_sum hhi_sum harith

end Erdos330
