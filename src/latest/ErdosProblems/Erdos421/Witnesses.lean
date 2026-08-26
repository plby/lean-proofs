import ErdosProblems.Erdos421.Blocks

/-!
# Cancellation to separated witnesses

This formalizes the cancellation used in Lemma 3.1 of the selected paper.
-/

namespace Erdos421

theorem IsBlock.sdiff {A B C : Finset ℕ} (hB : IsBlock A B) (hC : IsBlock A C)
    (hBC : (B \ C).Nonempty) (hCB : (C \ B).Nonempty) : IsBlock A (B \ C) := by
  refine ⟨hBC, fun _ hx ↦ hB.subset (Finset.mem_sdiff.mp hx).1, ?_⟩
  intro a b x ha hb hx hax hxb
  rcases Finset.mem_sdiff.mp ha with ⟨haB, haC⟩
  rcases Finset.mem_sdiff.mp hb with ⟨hbB, hbC⟩
  refine Finset.mem_sdiff.mpr ⟨hB.convex haB hbB hx hax hxb, ?_⟩
  intro hxC
  obtain ⟨c, hc⟩ := hCB
  rcases Finset.mem_sdiff.mp hc with ⟨hcC, hcB⟩
  by_cases hca : c ≤ a
  · exact haC (hC.convex hcC hxC (hB.subset haB) hca hax)
  · have hbc : b < c := by
      by_contra h
      exact hcB (hB.convex haB hbB (hC.subset hcC) (by omega) (by omega))
    exact hbC (hC.convex hxC hcC (hB.subset hbB) hxb hbc.le)

theorem sdiff_separated_of_lt {A B C : Finset ℕ} (hB : IsBlock A B) (hC : IsBlock A C)
    {b c : ℕ} (hb : b ∈ B \ C) (hc : c ∈ C \ B) (hbc : b < c) :
    ∀ x ∈ B \ C, ∀ y ∈ C \ B, x < y := by
  intro x hx y hy
  rcases Finset.mem_sdiff.mp hb with ⟨hbB, hbC⟩
  rcases Finset.mem_sdiff.mp hc with ⟨hcC, _⟩
  rcases Finset.mem_sdiff.mp hx with ⟨hxB, _⟩
  rcases Finset.mem_sdiff.mp hy with ⟨hyC, hyB⟩
  by_contra hxy
  have hyb : y < b := by
    by_contra h
    exact hyB (hB.convex hbB hxB (hC.subset hyC) (by omega) (by omega))
  exact hbC (hC.convex hyC hcC (hB.subset hbB) hyb.le hbc.le)

/-- Every failure of distinct block products has a separated, nonempty witness. -/
theorem exists_separated_collision {A : Finset ℕ} (htwo : ∀ a ∈ A, 2 ≤ a)
    (hbad : ¬ CollisionFree A) :
    ∃ E R : Finset ℕ, IsBlock A E ∧ IsBlock A R ∧
      (∀ e ∈ E, ∀ r ∈ R, e < r) ∧ E.prod id = R.prod id ∧ R.card < E.card := by
  classical
  unfold CollisionFree at hbad
  push Not at hbad
  obtain ⟨B, C, hB, hC, hprod, hne⟩ := hbad
  have hBC : (B \ C).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro h
    exact hne (eq_of_subset_of_prod_eq h (fun c hc ↦ htwo c (hC.subset hc)) hprod)
  have hCB : (C \ B).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro h
    exact hne (eq_of_subset_of_prod_eq h (fun b hb ↦ htwo b (hB.subset hb)) hprod.symm).symm
  have hposB : ∀ b ∈ B, 0 < b := by
    intro b hb
    have := htwo b (hB.subset hb)
    omega
  have heq := prod_sdiff_eq_of_prod_eq hposB hprod
  have hblockBC := hB.sdiff hC hBC hCB
  have hblockCB := hC.sdiff hB hCB hBC
  obtain ⟨b, hb⟩ := hBC
  obtain ⟨c, hc⟩ := hCB
  have hbne : b ≠ c := by
    intro heq
    subst c
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp hc).1
  rcases lt_or_gt_of_ne hbne with hbc | hcb
  · have hsep := sdiff_separated_of_lt hB hC hb hc hbc
    refine ⟨B \ C, C \ B, hblockBC, hblockCB, hsep, heq, ?_⟩
    exact earlier_card_gt hblockBC.nonempty hblockCB.nonempty
      (fun a ha ↦ hposB a (Finset.mem_sdiff.mp ha).1) hsep heq
  · have hsep := sdiff_separated_of_lt hC hB hc hb hcb
    refine ⟨C \ B, B \ C, hblockCB, hblockBC, hsep, heq.symm, ?_⟩
    apply earlier_card_gt hblockCB.nonempty hblockBC.nonempty _ hsep heq.symm
    intro a ha
    have := htwo a (hblockCB.subset ha)
    omega

/-- A rejected tentative gap has a later witness that is an ordinary interval
strictly between the boundary primes. -/
theorem canonical_rejection {A : Finset ℕ} {p q : ℕ}
    (hA : CollisionFree A) (hbound : ∀ a ∈ A, 2 ≤ a ∧ a ≤ p)
    (hpA : p ∈ A) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hbad : ¬ CollisionFree (A ∪ Finset.Ioc p q)) :
    ∃ (E : Finset ℕ) (m n : ℕ),
      p < m ∧ m ≤ n ∧ n < q ∧ IsBlock (A ∪ Finset.Ioc p q) E ∧
      (∀ e ∈ E, e < m) ∧ E.prod id = (Finset.Icc m n).prod id ∧
      n - m + 1 < E.card := by
  have htwo : ∀ a ∈ A ∪ Finset.Ioc p q, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hbound a ha).1
    · have := (Finset.mem_Ioc.mp ha).1
      have := hp.two_le
      omega
  have hmax : ∀ a ∈ A ∪ Finset.Ioc p q, a ≤ q := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hbound a ha).2.trans hpq.le
    · exact (Finset.mem_Ioc.mp ha).2
  obtain ⟨E, R, hE, hR, hsep, hprod, hcard⟩ := exists_separated_collision htwo hbad
  have hpos : ∀ e ∈ E, 0 < e := by
    intro e he
    have := htwo e (hE.subset he)
    omega
  have hnoprime : ∀ r ∈ R, ¬ r.Prime :=
    fun _ hr ↦ not_prime_mem_later hpos hsep hprod hr
  have hRold : ¬ R ⊆ A := by
    intro hRA
    have hEA : E ⊆ A := by
      intro e he
      rcases Finset.mem_union.mp (hE.subset he) with heA | heNew
      · exact heA
      · obtain ⟨r, hr⟩ := hR.nonempty
        have := (hbound r (hRA hr)).2
        have := hsep e he r hr
        have := (Finset.mem_Ioc.mp heNew).1
        omega
    have heq := hA E R
      (hE.restrict Finset.subset_union_left hEA)
      (hR.restrict Finset.subset_union_left hRA) hprod
    obtain ⟨e, he⟩ := hE.nonempty
    have hr : e ∈ R := heq ▸ he
    exact (lt_irrefl e) (hsep e he e hr)
  obtain ⟨r, hr, hrA⟩ := Finset.not_subset.mp hRold
  have hpr : p < r := by
    rcases Finset.mem_union.mp (hR.subset hr) with h | h
    · exact False.elim (hrA h)
    · exact (Finset.mem_Ioc.mp h).1
  have hRlower : ∀ x ∈ R, p < x := by
    intro x hx
    by_contra hpx
    have hpR := hR.convex hx hr (Finset.mem_union_left _ hpA) (by omega) hpr.le
    exact hnoprime p hpR hp
  have hRupper : ∀ x ∈ R, x < q := by
    intro x hx
    have hxq := hmax x (hR.subset hx)
    have hxne : x ≠ q := by intro heq; subst x; exact hnoprime q hx hq
    omega
  let m := R.min' hR.nonempty
  let n := R.max' hR.nonempty
  have hm : m ∈ R := R.min'_mem hR.nonempty
  have hn : n ∈ R := R.max'_mem hR.nonempty
  have hmn : m ≤ n := R.min'_le n hn
  have hReq : R = Finset.Icc m n := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_Icc.mpr ⟨R.min'_le x hx, R.le_max' x hx⟩
    · intro hx
      rcases Finset.mem_Icc.mp hx with ⟨hmx, hxn⟩
      apply hR.convex hm hn _ hmx hxn
      apply Finset.mem_union_right
      exact Finset.mem_Ioc.mpr ⟨(hRlower m hm).trans_le hmx,
        hxn.trans (hRupper n hn).le⟩
  refine ⟨E, m, n, hRlower m hm, hmn, hRupper n hn, hE,
    fun e he ↦ hsep e he m hm, hprod.trans (congrArg (Finset.prod · id) hReq), ?_⟩
  rw [hReq, Nat.card_Icc] at hcard
  omega

/-- There is no multiple of a prime strictly between it and its double. -/
theorem not_dvd_gap_prod {p m n : ℕ} (hp : p.Prime) (hpm : p < m) (hnp : n < 2 * p) :
    ¬ p ∣ (Finset.Icc m n).prod id := by
  intro h
  obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finsetProd_iff id).mp h
  obtain ⟨j, rfl⟩ := hpx
  have hx' := Finset.mem_Icc.mp hx
  have hj : 2 ≤ j := by
    by_contra h
    have := Nat.mul_le_mul_left p (show j ≤ 1 by omega)
    simp only [mul_one] at this
    omega
  have := Nat.mul_le_mul_left p hj
  nlinarith

/-- The earlier canonical witness cannot straddle the old boundary prime.
If it is new, it too is a full numerical interval. -/
theorem earlier_block_location {A E : Finset ℕ} {p q m n : ℕ}
    (hp : p.Prime) (hpA : p ∈ A)
    (hq2 : q ≤ 2 * p) (hpm : p < m) (hnq : n < q)
    (hE : IsBlock (A ∪ Finset.Ioc p q) E)
    (hsep : ∀ e ∈ E, e < m) (hprod : E.prod id = (Finset.Icc m n).prod id) :
    E ⊆ A ∨ ∃ a b, p < a ∧ a ≤ b ∧ b < m ∧ E = Finset.Icc a b := by
  have hpE : p ∉ E := by
    intro hpE
    apply not_dvd_gap_prod hp hpm (hnq.trans_le hq2)
    rw [← hprod]
    exact Finset.dvd_prod_of_mem id hpE
  by_cases hEA : E ⊆ A
  · exact Or.inl hEA
  · right
    obtain ⟨e, he, heA⟩ := Finset.not_subset.mp hEA
    have hpe : p < e := by
      rcases Finset.mem_union.mp (hE.subset he) with h | h
      · exact False.elim (heA h)
      · exact (Finset.mem_Ioc.mp h).1
    have hEnew : ∀ x ∈ E, p < x := by
      intro x hx
      by_contra hpx
      exact hpE (hE.convex hx he (Finset.mem_union_left _ hpA) (by omega) hpe.le)
    let a := E.min' hE.nonempty
    let b := E.max' hE.nonempty
    have ha : a ∈ E := E.min'_mem hE.nonempty
    have hb : b ∈ E := E.max'_mem hE.nonempty
    have hbm := hsep b hb
    have hmn : m ≤ n := by
      by_contra h
      have hempty : Finset.Icc m n = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      have htwo := two_le_prod hE.nonempty (by
        intro x hx
        have := hEnew x hx
        have := hp.two_le
        omega)
      rw [hempty, Finset.prod_empty] at hprod
      omega
    refine ⟨a, b, hEnew a ha, E.min'_le b hb, hbm, ?_⟩
    ext x
    constructor
    · intro hx
      exact Finset.mem_Icc.mpr ⟨E.min'_le x hx, E.le_max' x hx⟩
    · intro hx
      rcases Finset.mem_Icc.mp hx with ⟨hax, hxb⟩
      apply hE.convex ha hb _ hax hxb
      apply Finset.mem_union_right
      exact Finset.mem_Ioc.mpr ⟨(hEnew a ha).trans_le hax,
        hxb.trans (hbm.trans_le (hmn.trans hnq.le)).le⟩

end Erdos421
