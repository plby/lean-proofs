/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos154

open Filter Finset
open scoped Pointwise

namespace Erdos154

/-- FC-style Sidon predicate: pairwise sums are unique up to commutativity. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ i₁, i₁ ∈ A → ∀ j₁, j₁ ∈ A → ∀ i₂, i₂ ∈ A → ∀ j₂, j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

lemma isSidonSetNat_of_isSidon {A : Set ℕ} (hA : IsSidon A) : IsSidonSetNat A := by
  intro a ha b hb c hc d hd hab hcd hsum
  rcases hA a ha c hc b hb d hd hsum with h | h
  · exact h
  · rcases h with ⟨had, hbc⟩
    have hba : b ≤ a := by simpa [← hbc, ← had] using hcd
    have hab_eq : a = b := le_antisymm hab hba
    subst b
    subst c
    subst d
    exact ⟨rfl, rfl⟩

private def sym2Add : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨fun a b : ℕ => a + b, fun a b => Nat.add_comm a b⟩

@[simp]
private lemma sym2Add_mk (a b : ℕ) : sym2Add s(a, b) = a + b := rfl

private def residueCount (A : Finset ℕ) (m : ℕ) (r : ZMod m) : ℕ :=
  (A.filter (fun a : ℕ => (a : ZMod m) = r)).card

private lemma filter_zmod_eq_filter_mod (A : Finset ℕ) {m : ℕ} [NeZero m] (r : ZMod m) :
    A.filter (fun a : ℕ => (a : ZMod m) = r) = A.filter (fun a => a % m = r.val) := by
  ext a
  simp only [mem_filter]
  constructor
  · intro h
    exact ⟨h.1, by simpa [ZMod.val_natCast] using congr_arg ZMod.val h.2⟩
  · intro h
    refine ⟨h.1, ?_⟩
    apply ZMod.val_injective m
    simpa [ZMod.val_natCast] using h.2

private lemma orderedPairCount_eq_sum_residueCount
    (A : Finset ℕ) {m : ℕ} [NeZero m] (i : ZMod m) :
    ((A.product A).filter
        (fun p : ℕ × ℕ => ((p.1 + p.2 : ℕ) : ZMod m) = i)).card =
      ∑ r : ZMod m, residueCount A m r * residueCount A m (i - r) := by
  let fiber : ZMod m → Finset (ℕ × ℕ) := fun r =>
    (A.filter (fun a : ℕ => (a : ZMod m) = r)).product
      (A.filter (fun b : ℕ => (b : ZMod m) = i - r))
  have hdisj : ((Finset.univ : Finset (ZMod m)) : Set (ZMod m)).PairwiseDisjoint fiber := by
    intro r _ s _ hrs
    change Disjoint (fiber r) (fiber s)
    rw [Finset.disjoint_left]
    intro p hp hq
    have hr : (p.1 : ZMod m) = r := (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2
    have hs : (p.1 : ZMod m) = s := (Finset.mem_filter.1 (Finset.mem_product.1 hq).1).2
    exact hrs (hr.symm.trans hs)
  have hunion :
      (Finset.univ : Finset (ZMod m)).disjiUnion fiber hdisj =
        (A.product A).filter
          (fun p : ℕ × ℕ => ((p.1 + p.2 : ℕ) : ZMod m) = i) := by
    ext p
    rcases p with ⟨a, b⟩
    constructor
    · intro hp
      rcases Finset.mem_disjiUnion.1 hp with ⟨r, _, hp⟩
      rcases Finset.mem_product.1 hp with ⟨ha, hb⟩
      rcases Finset.mem_filter.1 ha with ⟨haA, har⟩
      rcases Finset.mem_filter.1 hb with ⟨hbA, hbr⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_product.2 ⟨haA, hbA⟩
      · rw [Nat.cast_add, har, hbr]
        abel
    · intro hp
      rw [Finset.mem_filter] at hp
      rcases hp with ⟨hpA, hsum⟩
      rcases Finset.mem_product.1 hpA with ⟨ha, hb⟩
      rw [Finset.mem_disjiUnion]
      refine ⟨(a : ZMod m), Finset.mem_univ _, ?_⟩
      change (a, b) ∈ (A.filter (fun x : ℕ => (x : ZMod m) = (a : ZMod m))).product
        (A.filter (fun y : ℕ => (y : ZMod m) = i - (a : ZMod m)))
      refine Finset.mem_product.2 ⟨?_, ?_⟩
      · exact Finset.mem_filter.2 ⟨ha, rfl⟩
      · refine Finset.mem_filter.2 ⟨hb, ?_⟩
        rw [Nat.cast_add] at hsum
        rw [← hsum]
        abel
  rw [← hunion, Finset.card_disjiUnion]
  simp [fiber, residueCount, Finset.card_product]

private lemma orderedPairCount_mod_eq_sum_residueCount
    (A : Finset ℕ) {m i : ℕ} [NeZero m] (hi : i < m) :
    ((A.product A).filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card =
      ∑ r : ZMod m, residueCount A m r * residueCount A m ((i : ZMod m) - r) := by
  have hfilter :
      (A.product A).filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i) =
        (A.product A).filter
          (fun p : ℕ × ℕ => ((p.1 + p.2 : ℕ) : ZMod m) = (i : ZMod m)) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      rw [ZMod.natCast_eq_natCast_iff']
      simpa [Nat.mod_eq_of_lt hi] using h.2
    · intro h
      refine ⟨h.1, ?_⟩
      have hmod := (ZMod.natCast_eq_natCast_iff' (p.1 + p.2) i m).1 h.2
      simpa [Nat.mod_eq_of_lt hi] using hmod
  rw [hfilter]
  exact orderedPairCount_eq_sum_residueCount A (i : ZMod m)

private lemma eventually_sqrt_pos {N : ℕ → ℕ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) :
    ∀ᶠ k in atTop, 0 < Real.sqrt (N k) := by
  filter_upwards [hN.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  exact Real.sqrt_pos_of_pos hk

private lemma eventually_card_pos_of_tendsto_card_div_sqrt
    {N : ℕ → ℕ} {A : ℕ → Finset ℕ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hcard : Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1)) :
    ∀ᶠ k in atTop, 0 < (A k).card := by
  have hsqrt_pos := eventually_sqrt_pos hN
  have hhalf : ∀ᶠ k in atTop, (1 / 2 : ℝ) <
      ((A k).card : ℝ) / Real.sqrt (N k) :=
    hcard.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hsqrt_pos, hhalf] with k hsqrt hhalf
  have hdiv_pos : 0 < ((A k).card : ℝ) / Real.sqrt (N k) := by
    linarith
  have hmul_pos : 0 <
      (((A k).card : ℝ) / Real.sqrt (N k)) * Real.sqrt (N k) :=
    mul_pos hdiv_pos hsqrt
  rw [div_mul_cancel₀ _ hsqrt.ne'] at hmul_pos
  exact_mod_cast hmul_pos

private lemma tendsto_residueCount_div_card
    {m : ℕ} [NeZero m] (r : ZMod m) {N : ℕ → ℕ} {A : ℕ → Finset ℕ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hcard : Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1))
    (hres : Tendsto
      (fun k => (((A k).filter (fun a => a % m = r.val)).card : ℝ) / Real.sqrt (N k))
      atTop (nhds (1 / (m : ℝ)))) :
    Tendsto (fun k => (residueCount (A k) m r : ℝ) / ((A k).card : ℝ))
      atTop (nhds (1 / (m : ℝ))) := by
  have hsqrt_pos := eventually_sqrt_pos hN
  have hA_pos := eventually_card_pos_of_tendsto_card_div_sqrt hN hcard
  have hquot := hres.div hcard (by norm_num : (1 : ℝ) ≠ 0)
  refine Tendsto.congr' ?_ (by simpa using hquot)
  filter_upwards [hsqrt_pos, hA_pos] with k hsqrt hA
  rw [residueCount, filter_zmod_eq_filter_mod (A k) r]
  have hA_ne : ((A k).card : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  change (((((A k).filter (fun a => a % m = r.val)).card : ℝ) / Real.sqrt (N k)) /
      (((A k).card : ℝ) / Real.sqrt (N k))) =
    ((((A k).filter (fun a => a % m = r.val)).card : ℝ) / ((A k).card : ℝ))
  field_simp [hsqrt.ne', hA_ne]

private lemma tendsto_orderedPairCount_mod_div_card_sq
    {m i : ℕ} [NeZero m] (hi : i < m) {N : ℕ → ℕ} {A : ℕ → Finset ℕ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hcard : Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1))
    (hres : ∀ r : ZMod m,
      Tendsto (fun k => (residueCount (A k) m r : ℝ) / ((A k).card : ℝ))
        atTop (nhds (1 / (m : ℝ)))) :
    Tendsto
      (fun k => ((((A k).product (A k)).filter
        (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card : ℝ) / (((A k).card : ℝ) ^ 2))
      atTop (nhds (1 / (m : ℝ))) := by
  have hA_pos := eventually_card_pos_of_tendsto_card_div_sqrt hN hcard
  have hsum : Tendsto
      (fun k => ∑ r : ZMod m,
        ((residueCount (A k) m r : ℝ) / ((A k).card : ℝ)) *
          ((residueCount (A k) m ((i : ZMod m) - r) : ℝ) / ((A k).card : ℝ)))
      atTop (nhds (∑ _r : ZMod m, (1 / (m : ℝ)) * (1 / (m : ℝ)))) := by
    refine tendsto_finset_sum (Finset.univ : Finset (ZMod m)) ?_
    intro r _
    exact (hres r).mul (hres ((i : ZMod m) - r))
  have hlimit : (∑ _r : ZMod m, (1 / (m : ℝ)) * (1 / (m : ℝ))) = 1 / (m : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
    simp [nsmul_eq_mul, hm_ne]
  have hsum' : Tendsto
      (fun k => ∑ r : ZMod m,
        ((residueCount (A k) m r : ℝ) / ((A k).card : ℝ)) *
          ((residueCount (A k) m ((i : ZMod m) - r) : ℝ) / ((A k).card : ℝ)))
      atTop (nhds (1 / (m : ℝ))) := by
    rwa [hlimit] at hsum
  refine Tendsto.congr' ?_ hsum'
  filter_upwards [hA_pos] with k hA
  rw [orderedPairCount_mod_eq_sum_residueCount (A k) hi]
  have hA_ne : ((A k).card : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  symm
  calc
    ((↑(∑ r : ZMod m,
          residueCount (A k) m r * residueCount (A k) m ((i : ZMod m) - r)) : ℝ) /
        ((A k).card : ℝ) ^ 2)
        = (∑ r : ZMod m,
            (residueCount (A k) m r : ℝ) *
              (residueCount (A k) m ((i : ZMod m) - r) : ℝ)) /
          ((A k).card : ℝ) ^ 2 := by
            simp [Nat.cast_sum, Nat.cast_mul]
    _ = ∑ r : ZMod m,
        ((residueCount (A k) m r : ℝ) *
          (residueCount (A k) m ((i : ZMod m) - r) : ℝ)) / ((A k).card : ℝ) ^ 2 := by
          rw [Finset.sum_div]
    _ = ∑ r : ZMod m,
        ((residueCount (A k) m r : ℝ) / ((A k).card : ℝ)) *
          ((residueCount (A k) m ((i : ZMod m) - r) : ℝ) / ((A k).card : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          field_simp [hA_ne]

private lemma tendsto_card_atTop_of_tendsto_card_div_sqrt
    {N : ℕ → ℕ} {A : ℕ → Finset ℕ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hcard : Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1)) :
    Tendsto (fun k => ((A k).card : ℝ)) atTop atTop := by
  have hsqrt_top : Tendsto (fun k => Real.sqrt (N k)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hprod := Filter.Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hsqrt_top hcard
  refine Tendsto.congr' ?_ hprod
  filter_upwards [eventually_sqrt_pos hN] with k hsqrt
  field_simp [hsqrt.ne']

private lemma tendsto_diagCount_div_card_sq_zero
    (m i : ℕ) {N : ℕ → ℕ} {A : ℕ → Finset ℕ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hcard : Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1)) :
    Tendsto
      (fun k => (((A k).filter (fun a => (2 * a) % m = i)).card : ℝ) /
        (((A k).card : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hA_top := tendsto_card_atTop_of_tendsto_card_div_sqrt hN hcard
  have hinv : Tendsto (fun k => (((A k).card : ℝ))⁻¹) atTop (nhds 0) :=
    hA_top.inv_tendsto_atTop
  refine squeeze_zero ?_ ?_ hinv
  · intro k
    positivity
  · intro k
    by_cases hA_zero : (A k).card = 0
    · have hfilter_zero : ((A k).filter (fun a => (2 * a) % m = i)).card = 0 := by
        exact Nat.eq_zero_of_le_zero ((card_filter_le (A k) (fun a => (2 * a) % m = i)).trans
          (le_of_eq hA_zero))
      simp [hA_zero, hfilter_zero]
    · have hA_pos : 0 < (A k).card := Nat.pos_of_ne_zero hA_zero
      have hA_real_pos : 0 < ((A k).card : ℝ) := by exact_mod_cast hA_pos
      have hfilter_le : (((A k).filter (fun a => (2 * a) % m = i)).card : ℝ) ≤
          ((A k).card : ℝ) := by
        exact_mod_cast card_filter_le (A k) (fun a => (2 * a) % m = i)
      calc
        (((A k).filter (fun a => (2 * a) % m = i)).card : ℝ) / (((A k).card : ℝ) ^ 2)
            ≤ ((A k).card : ℝ) / (((A k).card : ℝ) ^ 2) := by
              gcongr
        _ = (((A k).card : ℝ))⁻¹ := by
              field_simp [hA_real_pos.ne']

private lemma sidon_injOn_sym2Add {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    Set.InjOn sym2Add (A.sym2 : Set (Sym2 ℕ)) := by
  intro x hx y hy hxy
  induction x using Sym2.ind with
  | h a b =>
    induction y using Sym2.ind with
    | h c d =>
      rw [sym2Add_mk, sym2Add_mk] at hxy
      have hab : a ∈ A ∧ b ∈ A :=
        (Finset.mk_mem_sym2_iff (s := A) (a := a) (b := b)).1 hx
      have hcd : c ∈ A ∧ d ∈ A :=
        (Finset.mk_mem_sym2_iff (s := A) (a := c) (b := d)).1 hy
      rcases hA a hab.1 c hcd.1 b hab.2 d hcd.2 hxy with h | h
      · rw [Sym2.eq_iff]
        exact Or.inl ⟨h.1, h.2⟩
      · rw [Sym2.eq_iff]
        exact Or.inr ⟨h.1, h.2⟩

private lemma image_sym2Add_sym2 (A : Finset ℕ) :
    A.sym2.image sym2Add = A + A := by
  rw [Finset.sym2_eq_image]
  rw [Finset.image_image]
  exact Finset.image_add_product

lemma card_sumset_sidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    2 * (A + A).card = A.card * A.card + A.card := by
  rw [← image_sym2Add_sym2 A]
  rw [Finset.card_image_of_injOn (sidon_injOn_sym2Add (A := A) hA)]
  rw [Finset.card_sym2]
  have h : (A.card + 1) * A.card = Nat.choose (A.card + 1) 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq A.card 1
  rw [Nat.mul_comm 2]
  rw [← h]
  ring

lemma card_sumset_filter_sidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (m i : ℕ) :
    ((A + A).filter (fun s => s % m = i)).card =
      (A.sym2.filter (fun z => sym2Add z % m = i)).card := by
  rw [← image_sym2Add_sym2 A]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  exact sidon_injOn_sym2Add (A := A) hA (by exact (Finset.mem_filter.1 hx).1)
    (by exact (Finset.mem_filter.1 hy).1) hxy

private lemma two_mul_card_image_mk_offDiag_filter (A : Finset ℕ) (m i : ℕ) :
    2 * (((A.offDiag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).image
      Sym2.mk.uncurry).card) =
      (A.offDiag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card := by
  let T : Finset (ℕ × ℕ) := A.offDiag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)
  have hsum := Finset.card_eq_sum_card_image (Sym2.mk.uncurry) T
  have hfiber : ∀ z ∈ T.image Sym2.mk.uncurry,
      (T.filter fun p => Sym2.mk.uncurry p = z).card = 2 := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨p, hpT, rfl⟩
    rcases p with ⟨a, b⟩
    have hp := Finset.mem_filter.1 hpT
    have hpOff := Finset.mem_offDiag.1 hp.1
    have hQ : (a + b) % m = i := hp.2
    have hswapT : (b, a) ∈ T := by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_offDiag]
        exact ⟨hpOff.2.1, hpOff.1, hpOff.2.2.symm⟩
      · simpa [Nat.add_comm] using hQ
    have hfiber_eq : (T.filter fun p : ℕ × ℕ => Sym2.mk.uncurry p = s(a, b)) =
        {(a, b), (b, a)} := by
      ext q
      rcases q with ⟨c, d⟩
      constructor
      · intro hq
        rw [Finset.mem_filter] at hq
        have hmk : s(c, d) = s(a, b) := by
          simpa [Function.uncurry] using hq.2
        rw [Sym2.eq_iff] at hmk
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        exact hmk
      · intro hq
        rw [Finset.mem_filter]
        constructor
        · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
          rcases hq with hq | hq
          · rcases hq with ⟨rfl, rfl⟩
            exact hpT
          · rcases hq with ⟨rfl, rfl⟩
            exact hswapT
        · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
          rcases hq with hq | hq
          · rcases hq with ⟨rfl, rfl⟩
            rfl
          · rcases hq with ⟨rfl, rfl⟩
            change s(c, d) = s(d, c)
            rw [Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
    change (T.filter fun p : ℕ × ℕ => Sym2.mk.uncurry p = s(a, b)).card = 2
    rw [hfiber_eq]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp [hpOff.2.2]
  have hsum_const : ∑ z ∈ T.image Sym2.mk.uncurry,
      (T.filter fun p => Sym2.mk.uncurry p = z).card =
      (T.image Sym2.mk.uncurry).card * 2 := by
    exact Finset.sum_const_nat hfiber
  rw [hsum_const] at hsum
  rw [hsum, Nat.mul_comm]

private lemma card_diag_filter (A : Finset ℕ) (m i : ℕ) :
    (A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card =
      (A.filter (fun a => (2 * a) % m = i)).card := by
  rw [← Finset.card_image_of_injOn
    (s := A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i))
    (f := fun p : ℕ × ℕ => p.1)]
  · congr 1
    ext a
    simp [two_mul]
  · intro p hp q hq hpq
    change p ∈ A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i) at hp
    change q ∈ A.diag.filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i) at hq
    rw [Finset.mem_filter] at hp hq
    have hpdiag := Finset.mem_diag.1 hp.1
    have hqdiag := Finset.mem_diag.1 hq.1
    ext
    · exact hpq
    · simpa [hpdiag.2, hqdiag.2] using hpq

lemma two_mul_card_sym2_filter_eq_ordered_pair_count_add_diag
    (A : Finset ℕ) (m i : ℕ) :
    2 * (A.sym2.filter (fun z => sym2Add z % m = i)).card =
      ((A.product A).filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card
        + (A.filter (fun a => (2 * a) % m = i)).card := by
  let Q : ℕ × ℕ → Prop := fun p => (p.1 + p.2) % m = i
  have hsym : A.sym2.filter (fun z => sym2Add z % m = i) =
      ((A.product A).filter Q).image Sym2.mk.uncurry := by
    rw [Finset.sym2_eq_image]
    rw [Finset.filter_image]
    rfl
  rw [hsym]
  have hprod : A.product A = A.diag ∪ A.offDiag := by
    rw [Finset.product_eq_sprod]
    exact (Finset.diag_union_offDiag A).symm
  rw [hprod]
  rw [Finset.filter_union]
  have hdisj : Disjoint (A.diag.filter Q) (A.offDiag.filter Q) := by
    exact Disjoint.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1)
      (by intro x hx; exact (Finset.mem_filter.1 hx).1) (Finset.disjoint_diag_offDiag (s := A))
  rw [Finset.card_union_of_disjoint hdisj]
  have himage_union : ((A.diag.filter Q ∪ A.offDiag.filter Q).image Sym2.mk.uncurry).card =
      ((A.diag.filter Q).image Sym2.mk.uncurry).card +
        ((A.offDiag.filter Q).image Sym2.mk.uncurry).card := by
    rw [Finset.image_union]
    rw [Finset.card_union_of_disjoint]
    rw [Finset.disjoint_iff_ne]
    intro z hz1 w hz2 hzw
    rw [Finset.mem_image] at hz1 hz2
    rcases hz1 with ⟨p, hp, hpz⟩
    rcases hz2 with ⟨q, hq, hqw⟩
    have hmk : Sym2.mk.uncurry p = Sym2.mk.uncurry q := by rw [hpz, hzw, hqw]
    have hpdiag := Finset.mem_diag.1 (Finset.mem_filter.1 hp).1
    have hqoff := Finset.mem_offDiag.1 (Finset.mem_filter.1 hq).1
    rcases p with ⟨a, b⟩
    rcases q with ⟨c, d⟩
    simp only at hpdiag hqoff
    have hmk' : s(a, b) = s(c, d) := by
      simpa [Function.uncurry] using hmk
    rw [Sym2.eq_iff] at hmk'
    rcases hmk' with hmk | hmk <;> simp_all
  rw [himage_union]
  have hdiag_card : ((A.diag.filter Q).image Sym2.mk.uncurry).card =
      (A.filter (fun a => (2 * a) % m = i)).card := by
    rw [Finset.card_image_of_injOn]
    · exact card_diag_filter A m i
    · intro p hp q hq hpq
      change p ∈ A.diag.filter Q at hp
      change q ∈ A.diag.filter Q at hq
      have hpq' : p = q ∨ p = q.swap :=
        Sym2.mk_eq_mk_iff.1 (by simpa [Function.uncurry] using hpq)
      have hpdiag := Finset.mem_diag.1 (Finset.mem_filter.1 hp).1
      have hqdiag := Finset.mem_diag.1 (Finset.mem_filter.1 hq).1
      rcases hpq' with hpq | hpq
      · rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        simp_all
      · rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        simp_all
  have hoff_card : 2 * ((A.offDiag.filter Q).image Sym2.mk.uncurry).card =
      (A.offDiag.filter Q).card := by
    simpa [Q] using two_mul_card_image_mk_offDiag_filter A m i
  have hdiag_filter : (A.diag.filter Q).card =
      (A.filter (fun a => (2 * a) % m = i)).card := by
    simpa [Q] using card_diag_filter A m i
  rw [hdiag_card]
  rw [Nat.mul_add]
  rw [hoff_card, hdiag_filter]
  omega

private lemma lindstrom_implies_sumset_distribution :
    (∀ (m : ℕ) (_hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt (N k))
        atTop (nhds (1 / m))) →
    ∀ (m : ℕ) (_hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k + A k).filter (fun s => s % m = i)).card : ℝ) / ((A k + A k).card : ℝ))
        atTop (nhds (1 / m)) := by
  intro hlindstrom m hm N A hN hA_bound hA_sidon hcard i hi
  haveI : NeZero m := ⟨by omega⟩
  have hres : ∀ r : ZMod m,
      Tendsto (fun k => (residueCount (A k) m r : ℝ) / ((A k).card : ℝ))
        atTop (nhds (1 / (m : ℝ))) := by
    intro r
    refine tendsto_residueCount_div_card r hN hcard ?_
    exact hlindstrom m hm N A hN hA_bound hA_sidon hcard r.val (ZMod.val_lt r)
  have hordered :=
    tendsto_orderedPairCount_mod_div_card_sq (A := A) (N := N) hi hN hcard hres
  have hdiag := tendsto_diagCount_div_card_sq_zero m i hN hcard
  have hA_pos := eventually_card_pos_of_tendsto_card_div_sqrt hN hcard
  have hlimit : Tendsto
      (fun k =>
        let c : ℝ := ((A k).card : ℝ)
        let o : ℝ := ((((A k).product (A k)).filter
          (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card : ℝ)
        let d : ℝ := (((A k).filter (fun a => (2 * a) % m = i)).card : ℝ)
        ((o / c ^ 2 + d / c ^ 2) / (1 + c⁻¹)))
      atTop (nhds (1 / (m : ℝ))) := by
    have hden : Tendsto (fun k => 1 + (((A k).card : ℝ))⁻¹) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add
        (tendsto_card_atTop_of_tendsto_card_div_sqrt hN hcard).inv_tendsto_atTop
    have hnum := hordered.add hdiag
    have hquot := hnum.div hden (by norm_num : (1 + 0 : ℝ) ≠ 0)
    simpa using hquot
  refine Tendsto.congr' ?_ hlimit
  filter_upwards [hA_pos] with k hA
  let C : ℝ := ((A k).card : ℝ)
  let O : ℝ := ((((A k).product (A k)).filter
    (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card : ℝ)
  let D : ℝ := (((A k).filter (fun a => (2 * a) % m = i)).card : ℝ)
  let F : ℝ := (((A k + A k).filter (fun s => s % m = i)).card : ℝ)
  let T : ℝ := ((A k + A k).card : ℝ)
  have hC_pos : 0 < C := by
    dsimp [C]
    exact_mod_cast hA
  have hC_ne : C ≠ 0 := hC_pos.ne'
  have hnum_nat :
      2 * ((A k + A k).filter (fun s => s % m = i)).card =
        (((A k).product (A k)).filter (fun p : ℕ × ℕ => (p.1 + p.2) % m = i)).card +
          ((A k).filter (fun a => (2 * a) % m = i)).card := by
    rw [card_sumset_filter_sidon (hA_sidon k) m i]
    exact two_mul_card_sym2_filter_eq_ordered_pair_count_add_diag (A k) m i
  have hnum_real : (2 : ℝ) * F = O + D := by
    dsimp [F, O, D]
    exact_mod_cast hnum_nat
  have hden_nat : 2 * (A k + A k).card = (A k).card * (A k).card + (A k).card :=
    card_sumset_sidon (hA_sidon k)
  have hden_real : (2 : ℝ) * T = C ^ 2 + C := by
    dsimp [T, C]
    simpa [pow_two] using (by exact_mod_cast hden_nat :
      (2 : ℝ) * ((A k + A k).card : ℝ) =
        ((A k).card : ℝ) * ((A k).card : ℝ) + ((A k).card : ℝ))
  have hT_pos : 0 < T := by
    dsimp [T]
    have hsum_pos : 0 < (A k + A k).card := by
      by_contra hnot
      have hzero : (A k + A k).card = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hden_nat
      omega
    exact_mod_cast hsum_pos
  have hT_ne : T ≠ 0 := hT_pos.ne'
  have hC_sq_add_ne : C ^ 2 + C ≠ 0 := by
    have hpos : 0 < C ^ 2 + C := by nlinarith [sq_pos_of_pos hC_pos]
    exact hpos.ne'
  have hC_add_one_ne : C + 1 ≠ 0 := by positivity
  change ((O / C ^ 2 + D / C ^ 2) / (1 + C⁻¹)) = F / T
  symm
  calc
    F / T = ((2 : ℝ) * F) / ((2 : ℝ) * T) := by
      field_simp [hT_ne]
    _ = (O + D) / (C ^ 2 + C) := by
      rw [hnum_real, hden_real]
    _ = ((O / C ^ 2 + D / C ^ 2) / (1 + C⁻¹)) := by
      field_simp [hC_ne, hC_sq_add_ne, hC_add_one_ne]


/-- Erdős 154 sumset distribution, proved from Lindström's theorem and the Sidon property. -/
theorem erdos_154_sumset :
    ∀ (m : ℕ) (_hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
      Tendsto (fun k => (N k : ℝ)) atTop atTop →
      (∀ k, ∀ x ∈ A k, x ≤ N k) →
      (∀ k, IsSidon (A k : Set ℕ)) →
      Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
      ∀ i < m, Tendsto
        (fun k => (((A k + A k).filter (fun s => s % m = i)).card : ℝ) / ((A k + A k).card : ℝ))
        atTop (nhds (1 / m)) := by
  refine lindstrom_implies_sumset_distribution ?_
  intro m hm N A hN hA_bound hA_sidon hcard
  exact sidon_density_limit m hm N A hN hA_bound
    (fun k => isSidonSetNat_of_isSidon (hA_sidon k)) hcard

#print axioms erdos_154_sumset

end Erdos154
