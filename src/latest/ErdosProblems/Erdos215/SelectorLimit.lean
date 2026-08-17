/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.Selector

/-!
The denominator-chain/direct-limit part of the Jackson--Mauldin selector.

This file deliberately assumes the still-separate finite theorem saying that
every separated selector has a literal separated extension across each prime.
From that hypothesis it derives extension across every positive multiplier,
forces the new points into a rich pool without changing old points, and takes
the direct limit.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The exact finite input needed by the direct-limit construction. -/
def LiteralPrimeExtensionHypothesis : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), ∀ {d : ℕ}, d ≠ 0 → ∀ (s : LiftData d),
    s.Separated → ∃ t : LiftData (p * d), PrimeExtends p hp.pos s t ∧ t.Separated

/-- Literal extension, with no primality restriction on the multiplier. -/
def MultExtends (m : ℕ) (hm : 0 < m) {d : ℕ}
    (s : LiftData d) (t : LiftData (m * d)) : Prop :=
  PrimeExtends m hm s t

def LiftData.cast {d e : ℕ} (h : d = e) (s : LiftData d) : LiftData e :=
  h ▸ s

@[simp] lemma LiftData.cast_rfl {d : ℕ} (s : LiftData d) : s.cast rfl = s := rfl

@[simp] lemma LiftData.cast_k {d e : ℕ} (h : d = e) (s : LiftData d) (i j : Fin e) :
    (s.cast h).k i j = s.k (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

@[simp] lemma LiftData.cast_l {d e : ℕ} (h : d = e) (s : LiftData d) (i j : Fin e) :
    (s.cast h).l i j = s.l (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

lemma LiftData.separated_cast {d e : ℕ} (h : d = e) (s : LiftData d)
    (hs : s.Separated) : (s.cast h).Separated := by
  subst e
  exact hs

lemma multExtends_one {d : ℕ} (s : LiftData d) :
    MultExtends 1 (by omega) s (s.cast (by simp)) := by
  intro i j
  simpa [MultExtends, oldIndex]

lemma oldIndex_comp (m n : ℕ) (hm : 0 < m) (hn : 0 < n) {d : ℕ} (i : Fin d) :
    Fin.cast (by simp [Nat.mul_assoc] : n * (m * d) = (n * m) * d)
      (oldIndex n hn (oldIndex m hm i)) =
        oldIndex (n * m) (Nat.mul_pos hn hm) i := by
  apply Fin.ext
  simp [oldIndex, Nat.mul_assoc]

lemma multExtends_comp (m n : ℕ) (hm : 0 < m) (hn : 0 < n) {d : ℕ}
    {s : LiftData d} {t : LiftData (m * d)} {u : LiftData (n * (m * d))}
    (hst : MultExtends m hm s t) (htu : MultExtends n hn t u) :
    MultExtends (n * m) (Nat.mul_pos hn hm) s
      (u.cast (by simp [Nat.mul_assoc] : n * (m * d) = (n * m) * d)) := by
  intro i j
  have hst' := hst i j
  have htu' := htu (oldIndex m hm i) (oldIndex m hm j)
  have hi :
      Fin.cast (by simp [Nat.mul_assoc] : (n * m) * d = n * (m * d))
          (oldIndex (n * m) (Nat.mul_pos hn hm) i) =
        oldIndex n hn (oldIndex m hm i) := by
    apply Fin.ext
    simp [oldIndex, Nat.mul_assoc]
  have hj :
      Fin.cast (by simp [Nat.mul_assoc] : (n * m) * d = n * (m * d))
          (oldIndex (n * m) (Nat.mul_pos hn hm) j) =
        oldIndex n hn (oldIndex m hm j) := by
    apply Fin.ext
    simp [oldIndex, Nat.mul_assoc]
  rw [LiftData.cast_k, LiftData.cast_l, hi, hj]
  exact ⟨htu'.1.trans hst'.1, htu'.2.trans hst'.2⟩

/-- Prime extensions compose to give an extension across any positive natural
multiplier. -/
theorem exists_multExtension (hprime : LiteralPrimeExtensionHypothesis)
    (m : ℕ) (hm : 0 < m) {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (hs : s.Separated) :
    ∃ t : LiftData (m * d), MultExtends m hm s t ∧ t.Separated := by
  induction m using Nat.strong_induction_on generalizing d with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        exact ⟨s.cast (by simp), multExtends_one s,
          s.separated_cast (by simp) hs⟩
      · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
        let q := m / p
        have hp0 : 0 < p := hp.pos
        have hq0 : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hpm) hp0
        have hmq : p * q = m := Nat.mul_div_cancel' hpm
        have hqm : q < m := Nat.div_lt_self hm hp.one_lt
        obtain ⟨t, hst, ht⟩ := ih q hqm hq0 hd s hs
        obtain ⟨u, htu, hu⟩ := hprime p hp (Nat.mul_ne_zero (Nat.ne_of_gt hq0) hd) t ht
        have hden : p * (q * d) = m * d := by rw [← hmq]; simp [Nat.mul_assoc]
        let u' : LiftData (m * d) := u.cast hden
        refine ⟨u', ?_, u.separated_cast hden hu⟩
        intro i j
        have hst' := hst i j
        have htu' := htu (oldIndex q hq0 i) (oldIndex q hq0 j)
        have hi : Fin.cast hden.symm (oldIndex m hm i) =
            oldIndex p hp0 (oldIndex q hq0 i) := by
          apply Fin.ext
          change m * (i : ℕ) = p * (q * (i : ℕ))
          rw [← hmq]
          simp [Nat.mul_assoc]
        have hj : Fin.cast hden.symm (oldIndex m hm j) =
            oldIndex p hp0 (oldIndex q hq0 j) := by
          apply Fin.ext
          change m * (j : ℕ) = p * (q * (j : ℕ))
          rw [← hmq]
          simp [Nat.mul_assoc]
        dsimp only [u']
        rw [LiftData.cast_k, LiftData.cast_l, hi, hj]
        exact ⟨htu'.1.trans hst'.1, htu'.2.trans hst'.2⟩

/-- Force only the genuinely new residues of a literal extension into a rich
pool.  The old lifts are left definitionally equal to the previous lifts. -/
theorem multExtension_in_rich_pool (P : Set RatPoint) (hP : Rich P)
    (m : ℕ) (hm : 0 < m) {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (hsP : ∀ i j, s.point i j ∈ P) {t : LiftData (m * d)}
    (hst : MultExtends m hm s t) (ht : t.Separated) :
    ∃ u : LiftData (m * d), MultExtends m hm s u ∧ u.Separated ∧
      ∀ i j, u.point i j ∈ P := by
  have hmd : m * d ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hm) hd
  have havail : ∀ i j, ∃ k l a b : ℤ,
      k = t.k i j + (m * d) * a ∧ l = t.l i j + (m * d) * b ∧
      liftedPoint (m * d) i j k l ∈ P ∧
      ∀ i₀ j₀, i = oldIndex m hm i₀ → j = oldIndex m hm j₀ →
        k = s.k i₀ j₀ ∧ l = s.l i₀ j₀ := by
    intro i j
    by_cases hold : ∃ i₀ j₀, i = oldIndex m hm i₀ ∧ j = oldIndex m hm j₀
    · rcases hold with ⟨i₀, j₀, rfl, rfl⟩
      have heq := hst i₀ j₀
      refine ⟨t.k (oldIndex m hm i₀) (oldIndex m hm j₀),
        t.l (oldIndex m hm i₀) (oldIndex m hm j₀), 0, 0, by simp, by simp, ?_, ?_⟩
      · change t.point (oldIndex m hm i₀) (oldIndex m hm j₀) ∈ P
        rw [point_oldIndex_of_primeExtends m hm hd hst i₀ j₀]
        exact hsP i₀ j₀
      · intro i₁ j₁ hi hj
        have hii : i₁ = i₀ := oldIndex_injective m hm (hi.symm)
        have hjj : j₁ = j₀ := oldIndex_injective m hm (hj.symm)
        subst i₁
        subst j₁
        exact heq
    · rcases (hP (m * d) hmd i j (t.k i j) (t.l i j)).nonempty with ⟨x, hx⟩
      rcases hx with ⟨k, l, rfl, hk, hl, hp⟩
      rcases Int.modEq_iff_add_fac.mp hk with ⟨a, ha⟩
      rcases Int.modEq_iff_add_fac.mp hl with ⟨b, hb⟩
      refine ⟨k, l, a, b, ha, hb, hp, ?_⟩
      intro i₀ j₀ hi hj
      exact (hold ⟨i₀, j₀, hi, hj⟩).elim
  choose k l a b hk hl hp hold using havail
  let u : LiftData (m * d) := ⟨k, l⟩
  have htu : t.Congruent u := by
    intro i j
    exact ⟨a i j, b i j, hk i j, hl i j⟩
  refine ⟨u, ?_, LiftData.separated_of_congruent ht htu, ?_⟩
  · intro i j
    exact hold (oldIndex m hm i) (oldIndex m hm j) i j rfl rfl
  · intro i j
    exact hp i j

/-- The rich-pool version of extension across any positive multiplier. -/
theorem exists_multExtension_in_rich_pool (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) (m : ℕ) (hm : 0 < m)
    {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (hs : s.Separated)
    (hsP : ∀ i j, s.point i j ∈ P) :
    ∃ t : LiftData (m * d), MultExtends m hm s t ∧ t.Separated ∧
      ∀ i j, t.point i j ∈ P := by
  obtain ⟨t, hst, ht⟩ := exists_multExtension hprime m hm hd s hs
  exact multExtension_in_rich_pool P hP m hm hd s hsP hst ht

/-- A cofinal denominator chain.  Its closed form is `(n+1)! * d₀`. -/
def chainDenom (d₀ : ℕ) : ℕ → ℕ
  | 0 => d₀
  | n + 1 => (n + 2) * chainDenom d₀ n

lemma chainDenom_ne_zero {d₀ : ℕ} (hd₀ : d₀ ≠ 0) (n : ℕ) :
    chainDenom d₀ n ≠ 0 := by
  induction n with
  | zero => exact hd₀
  | succ n ih => exact Nat.mul_ne_zero (by omega) ih

lemma chainDenom_eq_factorial (d₀ n : ℕ) :
    chainDenom d₀ n = (n + 1).factorial * d₀ := by
  induction n with
  | zero => simp [chainDenom]
  | succ n ih =>
      rw [chainDenom, ih]
      change (n + 2) * ((n + 1).factorial * d₀) = (n + 2).factorial * d₀
      have hf : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
        convert Nat.factorial_succ (n + 1) using 1 <;> omega
      rw [hf]
      ring

lemma dvd_chainDenom (d₀ e : ℕ) (he : 0 < e) : e ∣ chainDenom d₀ e := by
  rw [chainDenom_eq_factorial]
  exact dvd_mul_of_dvd_left (Nat.dvd_factorial he (by omega)) d₀

/-- A separated finite selector all of whose points lie in `P`. -/
structure PoolStage (P : Set RatPoint) (d : ℕ) where
  selector : LiftData d
  separated : selector.Separated
  mem_pool : ∀ i j, selector.point i j ∈ P

noncomputable def nextPoolStage (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d : ℕ} (hd : d ≠ 0) (n : ℕ)
    (s : PoolStage P d) : PoolStage P ((n + 2) * d) := by
  let h := exists_multExtension_in_rich_pool hprime P hP (n + 2) (by omega) hd
    s.selector s.separated s.mem_pool
  exact ⟨Classical.choose h, (Classical.choose_spec h).2.1,
    (Classical.choose_spec h).2.2⟩

lemma nextPoolStage_extends (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d : ℕ} (hd : d ≠ 0) (n : ℕ)
    (s : PoolStage P d) :
    MultExtends (n + 2) (by omega) s.selector
      (nextPoolStage hprime P hP hd n s).selector := by
  exact (Classical.choose_spec (exists_multExtension_in_rich_pool hprime P hP
    (n + 2) (by omega) hd s.selector s.separated s.mem_pool)).1

noncomputable def poolChain (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) : (n : ℕ) → PoolStage P (chainDenom d₀ n)
  | 0 => s₀
  | n + 1 => nextPoolStage hprime P hP (chainDenom_ne_zero hd₀ n) n
      (poolChain hprime P hP hd₀ s₀ n)

lemma poolChain_extends (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) (n : ℕ) :
    MultExtends (n + 2) (by omega)
      (poolChain hprime P hP hd₀ s₀ n).selector
      (poolChain hprime P hP hd₀ s₀ (n + 1)).selector := by
  change MultExtends (n + 2) (by omega)
    (poolChain hprime P hP hd₀ s₀ n).selector
    (nextPoolStage hprime P hP (chainDenom_ne_zero hd₀ n) n
      (poolChain hprime P hP hd₀ s₀ n)).selector
  exact nextPoolStage_extends hprime P hP (chainDenom_ne_zero hd₀ n) n _

def stageRange {d : ℕ} (s : LiftData d) : Set RatPoint :=
  Set.range (fun ij : Fin d × Fin d ↦ s.point ij.1 ij.2)

lemma stageRange_subset_of_multExtends (m : ℕ) (hm : 0 < m) {d : ℕ}
    (hd : d ≠ 0) {s : LiftData d} {t : LiftData (m * d)}
    (hst : MultExtends m hm s t) : stageRange s ⊆ stageRange t := by
  rintro x ⟨⟨i, j⟩, rfl⟩
  refine ⟨⟨oldIndex m hm i, oldIndex m hm j⟩, ?_⟩
  exact point_oldIndex_of_primeExtends m hm hd hst i j

lemma poolChain_stageRange_monotone (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    Monotone (fun n ↦ stageRange (poolChain hprime P hP hd₀ s₀ n).selector) := by
  apply monotone_nat_of_le_succ
  intro n
  exact stageRange_subset_of_multExtends (n + 2) (by omega)
    (chainDenom_ne_zero hd₀ n) (poolChain_extends hprime P hP hd₀ s₀ n)

def limitSelector (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) : Set RatPoint :=
  ⋃ n, stageRange (poolChain hprime P hP hd₀ s₀ n).selector

lemma limitSelector_subset (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    limitSelector hprime P hP hd₀ s₀ ⊆ P := by
  rintro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, ⟨⟨i, j⟩, rfl⟩⟩
  exact (poolChain hprime P hP hd₀ s₀ n).mem_pool i j

lemma limitSelector_isPartial (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    IsPartial (limitSelector hprime P hP hd₀ s₀) := by
  intro x hx y hy hxy
  rcases Set.mem_iUnion.mp hx with ⟨a, hxa⟩
  rcases Set.mem_iUnion.mp hy with ⟨b, hyb⟩
  let N := max a b
  have hmono := poolChain_stageRange_monotone hprime P hP hd₀ s₀
  have hxN := hmono (le_max_left a b) hxa
  have hyN := hmono (le_max_right a b) hyb
  rcases hxN with ⟨⟨i₁, j₁⟩, rfl⟩
  rcases hyN with ⟨⟨i₂, j₂⟩, rfl⟩
  have hne : (i₁, j₁) ≠ (i₂, j₂) := by
    intro h
    exact hxy (congrArg
      (fun ij : Fin (chainDenom d₀ N) × Fin (chainDenom d₀ N) ↦
        (poolChain hprime P hP hd₀ s₀ N).selector.point ij.1 ij.2) h)
  exact (LiftData.separated_iff_sqDist_not_int (chainDenom_ne_zero hd₀ N)
    (poolChain hprime P hP hd₀ s₀ N).selector).mp
      (poolChain hprime P hP hd₀ s₀ N).separated i₁ j₁ i₂ j₂ hne

lemma residue_liftedPoint_eq (d : ℕ) (hd : d ≠ 0) (i j : Fin d)
    (k₁ l₁ k₂ l₂ : ℤ) :
    residue (liftedPoint d i j k₁ l₁) = residue (liftedPoint d i j k₂ l₂) := by
  apply Prod.ext
  · apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simp only [liftedPoint, residue, Prod.fst_sub, AddSubgroup.mem_zmultiples_iff]
    refine ⟨k₁ - k₂, ?_⟩
    push_cast
    field_simp [hd]
    ring
  · apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simp only [liftedPoint, residue, Prod.snd_sub, AddSubgroup.mem_zmultiples_iff]
    refine ⟨l₁ - l₂, ?_⟩
    push_cast
    field_simp [hd]
    ring

lemma rat_eq_residue_lift (q : ℚ) (D : ℕ) (hD : 0 < D) (hden : q.den ∣ D) :
    ∃ i : Fin D, ∃ k : ℤ, q = (i : ℚ) / D + k := by
  rcases hden with ⟨c, hc⟩
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    subst c
    simp at hc
    omega
  let N : ℤ := q.num * c
  let r : ℤ := N % (D : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg N (by exact_mod_cast hD.ne')
  have hrD : r < (D : ℤ) := Int.emod_lt_of_pos N (by exact_mod_cast hD)
  let i : Fin D := ⟨r.toNat, (Int.toNat_lt hr0).2 hrD⟩
  let k : ℤ := N / (D : ℤ)
  refine ⟨i, k, ?_⟩
  have hir : ((i : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
  have hsplit : r + (D : ℤ) * k = N := Int.emod_add_mul_ediv N D
  rw [← q.num_div_den]
  push_cast
  field_simp [q.den_ne_zero, hD.ne']
  have hirQ : ((i : ℕ) : ℚ) = (r : ℚ) := by
    calc
      ((i : ℕ) : ℚ) = ((((i : ℕ) : ℤ)) : ℚ) := by norm_num
      _ = (r : ℚ) := congrArg (fun z : ℤ ↦ (z : ℚ)) hir
  have hsplitQ : (r : ℚ) + D * k = N := by exact_mod_cast hsplit
  rw [hirQ, hsplitQ]
  dsimp only [N]
  rw [hc]
  push_cast
  ring

lemma ratPoint_eq_liftedPoint (x : RatPoint) (D : ℕ) (hD : 0 < D)
    (hden₁ : x.1.den ∣ D) (hden₂ : x.2.den ∣ D) :
    ∃ i j : Fin D, ∃ k l : ℤ, x = liftedPoint D i j k l := by
  obtain ⟨i, k, hi⟩ := rat_eq_residue_lift x.1 D hD hden₁
  obtain ⟨j, l, hj⟩ := rat_eq_residue_lift x.2 D hD hden₂
  exact ⟨i, j, k, l, Prod.ext hi hj⟩

lemma limitSelector_hits (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    HitsEveryIntegerTranslate (limitSelector hprime P hP hd₀ s₀) := by
  intro x
  let e := x.1.den * x.2.den
  have he : 0 < e := Nat.mul_pos x.1.den_pos x.2.den_pos
  have heD : e ∣ chainDenom d₀ e := dvd_chainDenom d₀ e he
  have hden₁ : x.1.den ∣ chainDenom d₀ e :=
    (dvd_mul_right x.1.den x.2.den).trans heD
  have hden₂ : x.2.den ∣ chainDenom d₀ e :=
    (dvd_mul_left x.2.den x.1.den).trans heD
  obtain ⟨i, j, k, l, hx⟩ := ratPoint_eq_liftedPoint x (chainDenom d₀ e)
    (Nat.pos_of_ne_zero (chainDenom_ne_zero hd₀ e)) hden₁ hden₂
  let y := (poolChain hprime P hP hd₀ s₀ e).selector.point i j
  refine ⟨y, ?_, ?_⟩
  · apply Set.mem_iUnion.mpr
    exact ⟨e, ⟨(i, j), rfl⟩⟩
  · rw [hx]
    exact residue_liftedPoint_eq (chainDenom d₀ e) (chainDenom_ne_zero hd₀ e)
      i j _ _ k l

/-- Direct-limit assembly from one finite separated selector already lying in
the rich pool.  The last clause records that every base-stage point survives
literally in the limit. -/
theorem exists_rich_selector_from_base (hprime : LiteralPrimeExtensionHypothesis)
    (P : Set RatPoint) (hP : Rich P) {d₀ : ℕ} (hd₀ : d₀ ≠ 0)
    (s₀ : PoolStage P d₀) :
    ∃ T : Set RatPoint, T ⊆ P ∧ IsPartial T ∧ HitsEveryIntegerTranslate T ∧
      stageRange s₀.selector ⊆ T := by
  refine ⟨limitSelector hprime P hP hd₀ s₀,
    limitSelector_subset hprime P hP hd₀ s₀,
    limitSelector_isPartial hprime P hP hd₀ s₀,
    limitSelector_hits hprime P hP hd₀ s₀, ?_⟩
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

/-- Translate all integral lifts by the same integer vector. -/
def translateLift {d : ℕ} (s : LiftData d) (a b : ℤ) : LiftData d where
  k i j := s.k i j + a
  l i j := s.l i j + b

lemma translateLift_separated {d : ℕ} (s : LiftData d) (a b : ℤ)
    (hs : s.Separated) : (translateLift s a b).Separated := by
  intro i₁ j₁ i₂ j₂ hne hdiv
  apply hs i₁ j₁ i₂ j₂ hne
  have heq :
      conflictNumerator d i₁ j₁ i₂ j₂
          ((translateLift s a b).k i₁ j₁) ((translateLift s a b).l i₁ j₁)
          ((translateLift s a b).k i₂ j₂) ((translateLift s a b).l i₂ j₂) =
        conflictNumerator d i₁ j₁ i₂ j₂
          (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂) := by
    simp only [translateLift, conflictNumerator]
    ring
  rwa [heq] at hdiv

lemma translateLift_point_eq {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (i j : Fin d) (k l : ℤ) :
    (translateLift s (k - s.k i j) (l - s.l i j)).point i j =
      liftedPoint d i j k l := by
  simp only [LiftData.point, translateLift, liftedPoint]
  congr <;> ring

/-- Force a finite selector into a rich pool while reserving one prescribed
selected point literally. -/
theorem finiteSelector_in_rich_pool_through {d : ℕ} (hd : d ≠ 0)
    (s : LiftData d) (P : Set RatPoint) (hP : Rich P) (hs : s.Separated)
    (i₀ j₀ : Fin d) (hbase : s.point i₀ j₀ ∈ P) :
    ∃ t : LiftData d, t.Separated ∧ (∀ i j, t.point i j ∈ P) ∧
      t.point i₀ j₀ = s.point i₀ j₀ := by
  have havail : ∀ i j, ∃ k l a b : ℤ,
      k = s.k i j + d * a ∧ l = s.l i j + d * b ∧
      liftedPoint d i j k l ∈ P ∧
      ((i, j) = (i₀, j₀) → k = s.k i₀ j₀ ∧ l = s.l i₀ j₀) := by
    intro i j
    by_cases hij : (i, j) = (i₀, j₀)
    · have hi : i = i₀ := congrArg Prod.fst hij
      have hj : j = j₀ := congrArg Prod.snd hij
      refine ⟨s.k i j, s.l i j, 0, 0, by simp, by simp, ?_, ?_⟩
      · change s.point i j ∈ P
        simpa [hi, hj] using hbase
      · intro hij'
        have hi' : i = i₀ := congrArg Prod.fst hij'
        have hj' : j = j₀ := congrArg Prod.snd hij'
        simp [hi', hj']
    · rcases (hP d hd i j (s.k i j) (s.l i j)).nonempty with ⟨x, hx⟩
      rcases hx with ⟨k, l, rfl, hk, hl, hp⟩
      rcases Int.modEq_iff_add_fac.mp hk with ⟨a, ha⟩
      rcases Int.modEq_iff_add_fac.mp hl with ⟨b, hb⟩
      exact ⟨k, l, a, b, ha, hb, hp, fun h ↦ (hij h).elim⟩
  choose k l a b hk hl hp hkeep using havail
  let t : LiftData d := ⟨k, l⟩
  have hst : s.Congruent t := by
    intro i j
    exact ⟨a i j, b i j, hk i j, hl i j⟩
  refine ⟨t, LiftData.separated_of_congruent hs hst, hp, ?_⟩
  rcases hkeep i₀ j₀ rfl with ⟨hk₀, hl₀⟩
  simp only [LiftData.point, t, hk₀, hl₀]

/-- Coordinate-level rich selector, including an optional prescribed point.
The only finite arithmetic input is `LiteralPrimeExtensionHypothesis`: every
separated finite selector extends literally and separatedly across every
prime. -/
theorem rich_selector_of_literal_prime_extensions
    (hprime : LiteralPrimeExtensionHypothesis) (P : Set RatPoint) (hP : Rich P)
    (w : Option RatPoint) (hw : ∀ x, x ∈ w → x ∈ P) :
    ∃ T : Set RatPoint, T ⊆ P ∧ IsPartial T ∧ HitsEveryIntegerTranslate T ∧
      ∀ x, x ∈ w → x ∈ T := by
  cases w with
  | none =>
      obtain ⟨s, hs, hsP⟩ := finiteSelector_in_rich_pool (by omega)
        LiftData.initialTwo P hP LiftData.initialTwo_separated
      let s₀ : PoolStage P 2 := ⟨s, hs, hsP⟩
      obtain ⟨T, hTP, hpartial, hhits, -⟩ :=
        exists_rich_selector_from_base hprime P hP (by omega) s₀
      exact ⟨T, hTP, hpartial, hhits, by simp⟩
  | some w =>
      let m := w.1.den * w.2.den
      have hm : 0 < m := Nat.mul_pos w.1.den_pos w.2.den_pos
      obtain ⟨s, -, hs⟩ := exists_multExtension hprime m hm (by omega)
        LiftData.initialTwo LiftData.initialTwo_separated
      have hD : 0 < m * 2 := Nat.mul_pos hm (by omega)
      have hden₁ : w.1.den ∣ m * 2 :=
        (dvd_mul_right w.1.den w.2.den).trans (dvd_mul_right m 2)
      have hden₂ : w.2.den ∣ m * 2 :=
        (dvd_mul_left w.2.den w.1.den).trans (dvd_mul_right m 2)
      obtain ⟨i, j, k, l, hwrep⟩ :=
        ratPoint_eq_liftedPoint w (m * 2) hD hden₁ hden₂
      let s' := translateLift s (k - s.k i j) (l - s.l i j)
      have hs' : s'.Separated := translateLift_separated s _ _ hs
      have hpoint : s'.point i j = w := by
        exact (translateLift_point_eq hD.ne' s i j k l).trans hwrep.symm
      have hwp : w ∈ P := hw w (by simp)
      obtain ⟨t, ht, htP, htpoint⟩ := finiteSelector_in_rich_pool_through hD.ne'
        s' P hP hs' i j (hpoint.symm ▸ hwp)
      let s₀ : PoolStage P (m * 2) := ⟨t, ht, htP⟩
      obtain ⟨T, hTP, hpartial, hhits, hbase⟩ :=
        exists_rich_selector_from_base hprime P hP hD.ne' s₀
      have hwT : w ∈ T := hbase ⟨(i, j), htpoint.trans hpoint⟩
      refine ⟨T, hTP, hpartial, hhits, ?_⟩
      intro x hx
      have hwx : w = x := by simpa using hx
      have hxw : x = w := hwx.symm
      simpa [hxw] using hwT

end

end Erdos215.Selector
