/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos13.Erdos13Additive
import ErdosProblems.Erdos1211.External.Erdos587Core.Main
import ErdosProblems.Erdos697.Erdos697Bernoulli

/-!
# Erdős Problem 344

The mathematical proof and the formal dependency map are in `tex/344.tex`.
-/

/-!
The original development imported the full proof of Erdős 360 only for the
small finite-group almost-period package below.  Keeping that package here
makes the formal proof of Problem 344 depend only on its actual ingredients.
-/

namespace Erdos360

open Function MulAction
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- Translations which add at most `e` points to a finite set. -/
def almostPeriods {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) : Finset G :=
  Finset.univ.filter fun x ↦
    (T ∪ Erdos587.addTranslate x T).card ≤ T.card + e

lemma mem_almostPeriods_iff {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] {T : Finset G} {e : ℕ} {x : G} :
    x ∈ almostPeriods T e ↔
      (T ∪ Erdos587.addTranslate x T).card ≤ T.card + e := by
  simp [almostPeriods]

lemma card_sub_le_card_inter_translate_of_mem_almostPeriods
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e : ℕ} {x : G} (hx : x ∈ almostPeriods T e) :
    T.card - e ≤ (T ∩ Erdos587.addTranslate x T).card := by
  have hunion := mem_almostPeriods_iff.mp hx
  have hcard := Finset.card_inter_add_card_union
    T (Erdos587.addTranslate x T)
  rw [Erdos587.card_addTranslate] at hcard
  omega

def almostPeriodIncidences
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) : Finset (Σ _x : G, G) :=
  (almostPeriods T e).sigma fun x ↦
    T ∩ Erdos587.addTranslate x T

lemma almostPeriodIncidence_encode_injective
    {G : Type*} [AddCommGroup G] :
    Function.Injective
      (fun p : Σ _x : G, G ↦ (p.2, -p.1 + p.2)) := by
  rintro ⟨x, z⟩ ⟨y, w⟩ hp
  have hzw : z = w := congrArg Prod.fst hp
  have hsecond : -x + z = -y + w := congrArg Prod.snd hp
  subst w
  have hneg : -x = -y := add_right_cancel hsecond
  have hxy : x = y := neg_injective hneg
  subst y
  rfl

lemma card_sub_mul_card_almostPeriods_le_sq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) :
    (T.card - e) * (almostPeriods T e).card ≤ T.card ^ 2 := by
  classical
  let I := almostPeriodIncidences T e
  let enc : (Σ _x : G, G) → G × G :=
    fun p ↦ (p.2, -p.1 + p.2)
  have hLower : (T.card - e) * (almostPeriods T e).card ≤ I.card := by
    change (T.card - e) * (almostPeriods T e).card ≤
      ((almostPeriods T e).sigma fun x ↦
        T ∩ Erdos587.addTranslate x T).card
    rw [Finset.card_sigma]
    calc
      (T.card - e) * (almostPeriods T e).card =
          ∑ _x ∈ almostPeriods T e, (T.card - e) := by
        simp [mul_comm]
      _ ≤ ∑ x ∈ almostPeriods T e,
          (T ∩ Erdos587.addTranslate x T).card := by
        exact Finset.sum_le_sum fun x hx ↦
          card_sub_le_card_inter_translate_of_mem_almostPeriods hx
  have hMaps : Set.MapsTo enc (I : Set (Σ _x : G, G))
      ((T ×ˢ T : Finset (G × G)) : Set (G × G)) := by
    intro p hp
    rw [Finset.mem_coe, show I = almostPeriodIncidences T e by rfl,
      almostPeriodIncidences, Finset.mem_sigma] at hp
    obtain ⟨_hx, hz⟩ := hp
    rw [Finset.mem_inter] at hz
    change enc p ∈ (T ×ˢ T : Finset (G × G))
    rw [Finset.mem_product]
    exact ⟨hz.1, Erdos587.mem_addTranslate.mp hz.2⟩
  have hInjective : (I : Set (Σ _x : G, G)).InjOn enc :=
    (almostPeriodIncidence_encode_injective : Function.Injective enc).injOn
  have hUpper : I.card ≤ (T ×ˢ T).card :=
    Finset.card_le_card_of_injOn enc hMaps hInjective
  calc
    (T.card - e) * (almostPeriods T e).card ≤ I.card := hLower
    _ ≤ (T ×ˢ T).card := hUpper
    _ = T.card ^ 2 := by simp [pow_two]

/-- Points introduced by translating `T` by `x`. -/
def translationNew {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T : Finset G) (x : G) : Finset G :=
  Erdos587.addTranslate x T \ T

lemma mem_almostPeriods_iff_card_translationNew_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e : ℕ} {x : G} :
    x ∈ almostPeriods T e ↔ (translationNew T x).card ≤ e := by
  rw [mem_almostPeriods_iff]
  have hcard := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x T) T
  rw [Finset.union_comm] at hcard
  simp only [translationNew]
  omega

lemma card_translationNew_add_le
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T : Finset G) (x y : G) :
    (translationNew T (x + y)).card ≤
      (translationNew T x).card + (translationNew T y).card := by
  classical
  let D := Erdos587.addTranslate x (Erdos587.addTranslate y T) \
    Erdos587.addTranslate x T
  have hsubset : translationNew T (x + y) ⊆ D ∪ translationNew T x := by
    intro z hz
    rw [translationNew, Finset.mem_sdiff] at hz
    rw [Finset.mem_union]
    by_cases hzx : z ∈ Erdos587.addTranslate x T
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hzx, hz.2⟩)
    · apply Or.inl
      rw [Finset.mem_sdiff]
      refine ⟨?_, hzx⟩
      rw [Erdos587.addTranslate_add]
      exact hz.1
  have hD : D.card ≤ (translationNew T y).card := by
    let f : G → G := fun z ↦ -x + z
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      rw [Finset.mem_coe, show D =
        Erdos587.addTranslate x (Erdos587.addTranslate y T) \
          Erdos587.addTranslate x T by rfl,
        Finset.mem_sdiff] at hz
      rw [Finset.mem_coe, translationNew, Finset.mem_sdiff]
      exact ⟨Erdos587.mem_addTranslate.mp hz.1,
        fun hzT ↦ hz.2 (Erdos587.mem_addTranslate.mpr hzT)⟩
    · exact fun _ _ _ _ h ↦ add_left_cancel h
  calc
    (translationNew T (x + y)).card ≤
        (D ∪ translationNew T x).card := Finset.card_le_card hsubset
    _ ≤ D.card + (translationNew T x).card := Finset.card_union_le _ _
    _ ≤ (translationNew T y).card + (translationNew T x).card :=
      Nat.add_le_add_right hD _
    _ = (translationNew T x).card + (translationNew T y).card := by omega

lemma add_mem_almostPeriods
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T : Finset G} {e d : ℕ} {x y : G}
    (hx : x ∈ almostPeriods T e) (hy : y ∈ almostPeriods T d) :
    x + y ∈ almostPeriods T (e + d) := by
  rw [mem_almostPeriods_iff_card_translationNew_le] at hx hy ⊢
  exact (card_translationNew_add_le T x y).trans (Nat.add_le_add hx hy)

@[simp] lemma zero_mem_almostPeriods
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (e : ℕ) : 0 ∈ almostPeriods T e := by
  rw [mem_almostPeriods_iff_card_translationNew_le]
  simp [translationNew]

def EscapesProperStabilizerCosets
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) : Prop :=
  ∀ C : Finset G, C.Nonempty → C ≠ Finset.univ →
    ∀ a ∈ A, ∃ b ∈ A, b ∉ a +ᵥ C.addStab

def NotContainedInProperCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) : Prop :=
  ∀ H : AddSubgroup G, H ≠ ⊤ → ∀ a : G,
    ¬(A : Set G) ⊆ a +ᵥ (H : Set G)

lemma escapesProperStabilizerCosets_of_notContainedInProperCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hcoset : NotContainedInProperCoset A) :
    EscapesProperStabilizerCosets A := by
  intro C hC hCproper a ha
  have hCstab := hC
  have hCwitness := hC
  let H : AddSubgroup G := AddAction.stabilizer G (C : Set G)
  have hHproper : H ≠ ⊤ := by
    intro hHtop
    apply hCproper
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨c, hc⟩ := hCwitness
    have hxStab : x - c ∈ C.addStab := by
      rw [← Finset.mem_coe, Finset.coe_addStab hCstab]
      change x - c ∈ H
      rw [hHtop]
      trivial
    have hxC := (Finset.mem_addStab' hCstab).mp hxStab hc
    simpa using hxC
  by_contra hnone
  push Not at hnone
  have hfin : A ⊆ a +ᵥ C.addStab := fun b hb ↦ hnone b hb
  have hset : (A : Set G) ⊆ a +ᵥ (H : Set G) := by
    intro b hb
    have hbfin := hfin (by simpa using hb)
    rw [Finset.mem_vadd_finset] at hbfin
    obtain ⟨y, hy, hsum⟩ := hbfin
    refine ⟨y, ?_, hsum⟩
    have hyset : y ∈ (C.addStab : Set G) := hy
    rw [Finset.coe_addStab hCstab] at hyset
    exact hyset
  exact hcoset H hHproper a hset

lemma two_mul_card_addStab_le_card_add
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A C : Finset G} (hA : A.Nonempty)
    (hesc : EscapesProperStabilizerCosets A)
    (hC : C.Nonempty) (hCproper : C ≠ Finset.univ) :
    2 * C.addStab.card ≤ (A + C.addStab).card := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hbA, hbcoset⟩ := hesc C hC hCproper a ha
  have hcosetSubset : a +ᵥ C.addStab ⊆ A + C.addStab :=
    Finset.vadd_finset_subset_add ha
  have hbSum : b ∈ A + C.addStab :=
    Finset.subset_add_left A (Finset.zero_mem_addStab.mpr hC) hbA
  have hstrict : a +ᵥ C.addStab ⊂ A + C.addStab := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hcosetSubset, ?_⟩
    intro heq
    exact hbcoset (heq ▸ hbSum)
  have hlt : C.addStab.card < (A + C.addStab).card := by
    rw [← Finset.card_vadd_finset a C.addStab]
    exact Finset.card_lt_card hstrict
  have hdvd : C.addStab.card ∣ (A + C.addStab).card :=
    Finset.card_addStab_dvd_card_add_addStab A C
  obtain ⟨q, hq⟩ := hdvd
  have hHpos : 0 < C.addStab.card := hC.addStab.card_pos
  rw [hq] at hlt ⊢
  have hq2 : 2 ≤ q := by
    by_contra hqnot
    interval_cases q <;> simp_all
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right C.addStab.card hq2

lemma two_mul_card_add_le_of_escape
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (hesc : EscapesProperStabilizerCosets A)
    (hproper : S + A ≠ Finset.univ) :
    2 * S.card + A.card ≤ 2 * (S + A).card := by
  let C := S + A
  have hC : C.Nonempty := hS.add hA
  have hHnonempty : C.addStab.Nonempty := hC.addStab
  have hHtwo : 2 * C.addStab.card ≤ (A + C.addStab).card :=
    two_mul_card_addStab_le_card_add hA hesc hC hproper
  have hAcard : A.card ≤ (A + C.addStab).card :=
    Finset.card_le_card_add_right hHnonempty
  have hSCard : S.card ≤ (S + C.addStab).card :=
    Finset.card_le_card_add_right hHnonempty
  have hK := Finset.add_kneser S A
  change (S + C.addStab).card + (A + C.addStab).card ≤
    C.card + C.addStab.card at hK
  change 2 * S.card + A.card ≤ 2 * C.card
  omega

def iteratedFinsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) : ℕ → Finset G
  | 0 => {0}
  | k + 1 => iteratedFinsetSum A k + A

@[simp] lemma iteratedFinsetSum_succ
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (k : ℕ) :
    iteratedFinsetSum A (k + 1) = iteratedFinsetSum A k + A := rfl

lemma iteratedFinsetSum_nonempty
    {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    (hA : A.Nonempty) (k : ℕ) : (iteratedFinsetSum A k).Nonempty := by
  induction k with
  | zero => simp [iteratedFinsetSum]
  | succ k ih => exact ih.add hA

lemma min_group_card_iteratedFinsetSum_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty)
    (hesc : EscapesProperStabilizerCosets A) :
    ∀ k : ℕ, 1 ≤ k →
      min (2 * Fintype.card G) ((k + 1) * A.card) ≤
        2 * (iteratedFinsetSum A k).card := by
  intro k hk
  induction k using Nat.case_strong_induction_on with
  | hz => omega
  | hi k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [iteratedFinsetSum]
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have ih' := ih k (Nat.le_refl k) hkpos
        let S := iteratedFinsetSum A k
        let C := S + A
        have hS : S.Nonempty := iteratedFinsetSum_nonempty hA k
        by_cases hCuniv : C = Finset.univ
        · rw [iteratedFinsetSum_succ]
          change min (2 * Fintype.card G) ((k + 1 + 1) * A.card) ≤
            2 * C.card
          rw [hCuniv, Finset.card_univ]
          exact min_le_left _ _
        · have hgrowth : 2 * S.card + A.card ≤ 2 * C.card :=
            two_mul_card_add_le_of_escape hA hS hesc hCuniv
          have ihMain : (k + 1) * A.card ≤ 2 * S.card := by
            rcases le_total (2 * Fintype.card G) ((k + 1) * A.card) with
                hgroup | htarget
            · have hfullLower : 2 * Fintype.card G ≤ 2 * S.card := by
                simpa [min_eq_left hgroup] using ih'
              have hfullUpper : 2 * S.card ≤ 2 * Fintype.card G := by
                exact Nat.mul_le_mul_left 2 (Finset.card_le_univ S)
              have hScard : S.card = Fintype.card G := by omega
              have hSuniv : S = Finset.univ :=
                Finset.eq_univ_of_card S hScard
              exfalso
              apply hCuniv
              dsimp [C]
              rw [hSuniv]
              ext x
              simp only [Finset.mem_add, Finset.mem_univ]
              obtain ⟨a, ha⟩ := hA
              constructor
              · intro _
                trivial
              · intro _
                exact ⟨x - a, trivial, a, ha, by abel⟩
            · simpa [min_eq_right htarget] using ih'
          change min (2 * Fintype.card G) ((k + 1 + 1) * A.card) ≤
            2 * C.card
          apply (min_le_right _ _).trans
          calc
            (k + 1 + 1) * A.card = (k + 1) * A.card + A.card := by ring
            _ ≤ 2 * S.card + A.card := Nat.add_le_add_right ihMain _
            _ ≤ 2 * C.card := hgrowth

theorem min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty)
    (hcoset : NotContainedInProperCoset A) (k : ℕ) (hk : 1 ≤ k) :
    min (2 * Fintype.card G) ((k + 1) * A.card) ≤
      2 * (iteratedFinsetSum A k).card :=
  min_group_card_iteratedFinsetSum_lower hA
    (escapesProperStabilizerCosets_of_notContainedInProperCoset hcoset) k hk

end Erdos360

namespace Erdos344

universe u

open BigOperators Filter Set
open scoped Pointwise Topology

attribute [local instance] Classical.propDecidable
noncomputable local instance (A : Set ℕ) : DecidablePred A := Classical.decPred A

/-- Finite subset sums of a set of natural numbers. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ b ∈ B, b}

/-- The number of members of `A` in the positive initial interval `[1, N]`. -/
noncomputable def counting (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- The literal eventual square-root density condition in Problem 344. -/
def SqrtDense (C : ℝ) (A : Set ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, C * Real.sqrt (N : ℝ) ≤ (counting A N : ℝ)

/-- `S` contains a nonconstant finite arithmetic progression of length `k`. -/
def ContainsFiniteAP (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- `S` contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, a + i * d ∈ S

/-- A set has arbitrarily long finite progressions with one fixed positive
common difference. -/
def HasFixedStepProgressions (S : Set ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ, ∃ a : ℕ, ∀ i < k, a + i * d ∈ S

/-- An additive `q`-net with width `K`: every interval
`[n*q, (n+K)*q]` contains a member of `S` divisible by `q`. -/
def IsAddNet (q K : ℕ) (S : Set ℕ) : Prop :=
  0 < q ∧ ∀ n : ℕ, ∃ s ∈ S, q ∣ s ∧ n * q ≤ s ∧ s ≤ (n + K) * q

lemma sqrtDense_mono_constant {A : Set ℕ} {c C : ℝ} (hcC : c ≤ C)
    (hC : SqrtDense C A) : SqrtDense c A := by
  filter_upwards [hC] with N hN
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_right hcC hsqrt).trans hN

lemma subsetSums_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  rintro n ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans hAB, rfl⟩

@[simp] lemma zero_mem_subsetSums (A : Set ℕ) : 0 ∈ subsetSums A := by
  exact ⟨∅, by simp, by simp⟩

lemma singleton_mem_subsetSums {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  exact ⟨{a}, by simpa, by simp⟩

lemma add_mem_subsetSums_of_disjoint {A B : Set ℕ} (hAB : Disjoint A B)
    {x y : ℕ} (hx : x ∈ subsetSums A) (hy : y ∈ subsetSums B) :
    x + y ∈ subsetSums (A ∪ B) := by
  obtain ⟨X, hXA, rfl⟩ := hx
  obtain ⟨Y, hYB, rfl⟩ := hy
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    exact Set.disjoint_left.1 hAB (hXA hzX) (hYB hzY)
  refine ⟨X ∪ Y, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_union] at hz
    exact hz.elim (fun h ↦ Or.inl (hXA h)) (fun h ↦ Or.inr (hYB h))
  · rw [Finset.sum_union hXY]

lemma subsetSums_union_subset_add {A B : Set ℕ} (hAB : Disjoint A B) :
    subsetSums A + subsetSums B ⊆ subsetSums (A ∪ B) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact add_mem_subsetSums_of_disjoint hAB hx hy

lemma mul_mem_subsetSum_of_scaled_mem
    {A Z : Finset ℕ} {d x : ℕ} (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ A) (hx : x ∈ Z.subsetSum) :
    d * x ∈ A.subsetSum := by
  obtain ⟨S, hSZ, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨S.image (fun z ↦ d * z), ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact hscale z (hSZ hz)
  · rw [Finset.sum_image]
    · rw [← Finset.mul_sum]
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hd hab

lemma containsFiniteAP_scaled_subsetSum
    {A Z : Finset ℕ} {d k : ℕ} (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ A)
    (hAP : ContainsFiniteAP (Z.subsetSum : Set ℕ) k) :
    ContainsFiniteAP (A.subsetSum : Set ℕ) k := by
  obtain ⟨a, q, hq, hprog⟩ := hAP
  refine ⟨d * a, d * q, Nat.mul_pos hd hq, ?_⟩
  intro i hi
  have hmem := mul_mem_subsetSum_of_scaled_mem hd hscale (hprog i hi)
  simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmem

lemma containsFiniteAP_mono {S T : Set ℕ} (hST : S ⊆ T) {k : ℕ}
    (hS : ContainsFiniteAP S k) : ContainsFiniteAP T k := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i hi ↦ hST (h i hi)⟩

lemma containsFiniteAP_of_le {S : Set ℕ} {k l : ℕ} (hkl : k ≤ l)
    (hS : ContainsFiniteAP S l) : ContainsFiniteAP S k := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i hi ↦ h i (hi.trans_le hkl)⟩

lemma containsInfiniteAP_mono {S T : Set ℕ} (hST : S ⊆ T)
    (hS : ContainsInfiniteAP S) : ContainsInfiniteAP T := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i ↦ hST (h i)⟩

/-! ### Counting and increasing enumerations -/

lemma counting_eq_count {A : Set ℕ} (hApos : A ⊆ Set.Ici 1) (N : ℕ) :
    counting A N = Nat.count (· ∈ A) (N + 1) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  simp only [counting]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨hx1, hxN⟩, hxA⟩
    exact ⟨by omega, hxA⟩
  · rintro ⟨hxN, hxA⟩
    exact ⟨⟨hApos hxA, by omega⟩, hxA⟩

lemma counting_nth {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    (hAinf : A.Infinite) (m : ℕ) :
    counting A (Nat.nth (· ∈ A) m) = m + 1 := by
  rw [counting_eq_count hApos]
  exact Nat.count_nth_succ_of_infinite hAinf m

lemma nth_mem {A : Set ℕ} (hAinf : A.Infinite) (m : ℕ) :
    Nat.nth (· ∈ A) m ∈ A := by
  exact Nat.nth_mem_of_infinite hAinf m

lemma nth_strictMono {A : Set ℕ} (hAinf : A.Infinite) :
    StrictMono (Nat.nth (· ∈ A)) := by
  exact Nat.nth_strictMono hAinf

lemma counting_le_ncard {A : Set ℕ} (hAfin : A.Finite) (N : ℕ) :
    counting A N ≤ A.ncard := by
  classical
  rw [counting, Set.ncard_eq_toFinset_card A hAfin]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact hAfin.mem_toFinset.mpr hx.2

lemma infinite_of_sqrtDense {A : Set ℕ} {C : ℝ} (hC : 0 < C)
    (hdense : SqrtDense C A) : A.Infinite := by
  intro hAfin
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ ↦ C * Real.sqrt (N : ℝ)) atTop atTop :=
    hsqrt.const_mul_atTop hC
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (A.ncard : ℝ) + 1 ≤ C * Real.sqrt (N : ℝ) :=
    hscale.eventually (eventually_ge_atTop ((A.ncard : ℝ) + 1))
  obtain ⟨N, hdenseN, hlargeN⟩ := (hdense.and hlarge).exists
  have hcount : (counting A N : ℝ) ≤ A.ncard := by
    exact_mod_cast counting_le_ncard hAfin N
  linarith

lemma counting_le_counting_sdiff_add_ncard {A F : Set ℕ}
    (hFfin : F.Finite) (N : ℕ) :
    counting A N ≤ counting (A \ F) N + F.ncard := by
  let X := (Finset.Icc 1 N).filter (· ∈ A)
  let Y := (Finset.Icc 1 N).filter (· ∈ A \ F)
  have hsub : X ⊆ Y ∪ hFfin.toFinset := by
    intro x hx
    simp only [X, Y, Finset.mem_filter, Finset.mem_union,
      hFfin.mem_toFinset, Set.mem_sdiff] at hx ⊢
    by_cases hxF : x ∈ F
    · exact Or.inr hxF
    · exact Or.inl ⟨hx.1, hx.2, hxF⟩
  have hcardY : Y.card = counting (A \ F) N := by
    unfold counting
    apply congrArg Finset.card
    ext x
    simp only [Y, Finset.mem_filter, Finset.mem_Icc]
  calc
    counting A N = X.card := rfl
    _ ≤ (Y ∪ hFfin.toFinset).card := Finset.card_le_card hsub
    _ ≤ Y.card + hFfin.toFinset.card := Finset.card_union_le Y hFfin.toFinset
    _ = counting (A \ F) N + F.ncard := by
      rw [hcardY, Set.ncard_eq_toFinset_card F hFfin]

lemma sqrtDense_sdiff_finite {A F : Set ℕ} {c C : ℝ}
    (hcC : c < C) (hFfin : F.Finite) (hdense : SqrtDense C A) :
    SqrtDense c (A \ F) := by
  have hgap : 0 < C - c := sub_pos.mpr hcC
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ ↦ (C - c) * Real.sqrt (N : ℝ))
      atTop atTop := hsqrt.const_mul_atTop hgap
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (F.ncard : ℝ) ≤ (C - c) * Real.sqrt (N : ℝ) :=
    hscale.eventually (eventually_ge_atTop (F.ncard : ℝ))
  filter_upwards [hdense, hlarge] with N hN hlargeN
  have hcountNat := counting_le_counting_sdiff_add_ncard (A := A) hFfin N
  have hcount : (counting A N : ℝ) ≤
      counting (A \ F) N + F.ncard := by exact_mod_cast hcountNat
  nlinarith

/-- The elements in one parity class of their zero-based rank in `A`. -/
def rankPart (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {x ∈ A | Nat.count (· ∈ A) x % 2 = r}

lemma nth_mem_rankPart {A : Set ℕ} (hAinf : A.Infinite) (j : ℕ) :
    Nat.nth (· ∈ A) j ∈ rankPart A (j % 2) := by
  refine ⟨nth_mem hAinf j, ?_⟩
  rw [Nat.count_nth_of_infinite (p := fun x ↦ x ∈ A) hAinf]

lemma rankPart_subset (A : Set ℕ) (r : ℕ) : rankPart A r ⊆ A :=
  fun _ hx ↦ hx.1

lemma rankPart_disjoint (A : Set ℕ) : Disjoint (rankPart A 0) (rankPart A 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx0⟩ ⟨-, hx1⟩
  omega

lemma rankPart_zero_union_one {A : Set ℕ} :
    rankPart A 0 ∪ rankPart A 1 = A := by
  ext x
  constructor
  · rintro (hx | hx) <;> exact hx.1
  · intro hx
    have hmod : Nat.count (· ∈ A) x % 2 = 0 ∨ Nat.count (· ∈ A) x % 2 = 1 := by
      omega
    rcases hmod with hmod | hmod
    · exact Or.inl ⟨hx, hmod⟩
    · exact Or.inr ⟨hx, hmod⟩

lemma half_counting_le_rankPart {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    (hAinf : A.Infinite) {r : ℕ} (hr : r < 2) (N : ℕ) :
    counting A N / 2 ≤ counting (rankPart A r) N := by
  let k := counting A N
  let I := Finset.range (k / 2)
  let f : ℕ → ℕ := fun i ↦ Nat.nth (· ∈ A) (2 * i + r)
  have hcountEq : Nat.count (· ∈ A) (N + 1) = k := by
    symm
    exact counting_eq_count hApos N
  have himage : I.image f ⊆ (Finset.Icc 1 N).filter (· ∈ rankPart A r) := by
    intro x hx
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hx
    have hi : i < k / 2 := Finset.mem_range.mp hiI
    have hij : 2 * i + r < k := by omega
    have hlt : f i < N + 1 := by
      apply Nat.nth_lt_of_lt_count
      simpa [hcountEq] using hij
    have hfA : f i ∈ A := nth_mem hAinf _
    have hfpos : 1 ≤ f i := hApos hfA
    have hfrank : f i ∈ rankPart A r := by
      refine ⟨hfA, ?_⟩
      dsimp [f]
      rw [Nat.count_nth_of_infinite (p := fun x ↦ x ∈ A) hAinf]
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hfpos, by omega⟩, hfrank⟩
  have hfinj : Function.Injective f := (nth_strictMono hAinf).injective.comp
    (fun _ _ h ↦ by omega)
  calc
    counting A N / 2 = I.card := by simp [I, k]
    _ = (I.image f).card := (Finset.card_image_iff.mpr hfinj.injOn).symm
    _ ≤ ((Finset.Icc 1 N).filter (· ∈ rankPart A r)).card :=
      Finset.card_le_card himage
    _ = counting (rankPart A r) N := rfl

lemma sqrtDense_rankPart {A : Set ℕ} {c C : ℝ}
    (hApos : A ⊆ Set.Ici 1) (hc : 0 < c) (hgap : c < C / 2)
    (hdense : SqrtDense C A) {r : ℕ} (hr : r < 2) :
    SqrtDense c (rankPart A r) := by
  have hCpos : 0 < C := by linarith
  have hAinf := infinite_of_sqrtDense hCpos hdense
  have hmargin : 0 < C / 2 - c := sub_pos.mpr hgap
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      1 ≤ (C / 2 - c) * Real.sqrt (N : ℝ) :=
    (hsqrt.const_mul_atTop hmargin).eventually (eventually_ge_atTop 1)
  filter_upwards [hdense, hlarge] with N hN hlargeN
  have hhalfNat := half_counting_le_rankPart hApos hAinf hr N
  have hhalf : (counting A N / 2 : ℕ) ≤ counting (rankPart A r) N := hhalfNat
  have hfloor : (counting A N : ℝ) / 2 - 1 ≤ (counting A N / 2 : ℕ) := by
    have hkNat : counting A N ≤ 2 * (counting A N / 2) + 1 := by omega
    have hkReal : (counting A N : ℝ) ≤
        2 * ((counting A N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hkNat
    linarith
  have hhalfReal : (counting A N / 2 : ℕ) ≤
      (counting (rankPart A r) N : ℝ) := by exact_mod_cast hhalf
  nlinarith

lemma eventually_density_inversion {A : Set ℕ} {C : ℝ}
    (hApos : A ⊆ Set.Ici 1) (hC : 0 < C) (hdense : SqrtDense C A) :
    ∀ᶠ m : ℕ in atTop,
      C ^ 2 * (Nat.nth (· ∈ A) m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
  have hAinf : A.Infinite := infinite_of_sqrtDense hC hdense
  have hnthTop : Tendsto (Nat.nth (· ∈ A)) atTop atTop :=
    (nth_strictMono hAinf).tendsto_atTop
  have hdenseNth : ∀ᶠ m : ℕ in atTop,
      C * Real.sqrt (Nat.nth (· ∈ A) m : ℝ) ≤
        (counting A (Nat.nth (· ∈ A) m) : ℝ) :=
    hnthTop.eventually hdense
  filter_upwards [hdenseNth] with m hm
  rw [counting_nth hApos hAinf] at hm
  have hleft : 0 ≤ C * Real.sqrt (Nat.nth (· ∈ A) m : ℝ) :=
    mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hsquare := (sq_le_sq₀ hleft (by positivity)).2 hm
  calc
    C ^ 2 * (Nat.nth (· ∈ A) m : ℝ) =
        (C * Real.sqrt (Nat.nth (· ∈ A) m : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt]
      positivity
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := hsquare

lemma addNet_add_finiteAP {S T : Set ℕ} {q K a : ℕ}
    (hnet : IsAddNet q K T)
    (hAP : ∀ i < K + 1, a + i * q ∈ S) :
    ContainsInfiniteAP (S + T) := by
  refine ⟨a + K * q, q, hnet.1, ?_⟩
  intro n
  obtain ⟨s, hsT, hq, hlo, hhi⟩ := hnet.2 n
  obtain ⟨t, rfl⟩ := hq
  have hnle : n ≤ t := by
    rw [Nat.mul_comm n q] at hlo
    exact Nat.le_of_mul_le_mul_left hlo hnet.1
  have htle : t ≤ n + K := by
    rw [Nat.mul_comm (n + K) q] at hhi
    exact Nat.le_of_mul_le_mul_left hhi hnet.1
  let i := n + K - t
  have hiK : i ≤ K := by
    dsimp [i]
    omega
  have hi : i < K + 1 := by omega
  have hit : i + t = n + K := by
    dsimp [i]
    omega
  have hsum : (a + i * q) + q * t = (a + K * q) + n * q := by
    calc
      (a + i * q) + q * t = a + (i + t) * q := by ring
      _ = a + (n + K) * q := by rw [hit]
      _ = (a + K * q) + n * q := by ring
  rw [← hsum]
  exact ⟨a + i * q, hAP i hi, q * t, hsT, rfl⟩

/-! ### Lowering a finite progression's common difference -/

/-- Explicit membership form of common-difference lowering. -/
lemma lowerStep_of_residue_translates_mem {S U : Set ℕ}
    {a q M L Z : ℕ} (hq : 0 < q) (hM : 0 < M)
    (hAP : ∀ j < L, a + j * (q * M) ∈ S)
    (hres : ∀ i < M, ∃ u ∈ U, ∃ z ≤ Z, u = i * q + (q * M) * z) :
    ∀ n < M * (L - Z),
      (a + (q * M) * Z) + n * q ∈ S + U := by
  intro n hn
  let i := n % M
  let k := n / M
  have hi : i < M := Nat.mod_lt n hM
  obtain ⟨u, huU, z, hzZ, rfl⟩ := hres i hi
  let j := Z + k - z
  have hk : k < L - Z := by
    apply (Nat.div_lt_iff_lt_mul hM).2
    simpa [Nat.mul_comm] using hn
  have hzsum : z ≤ Z + k := hzZ.trans (Nat.le_add_right Z k)
  have hjEq : j + z = Z + k := by
    dsimp [j]
    omega
  have hsubpos : 0 < L - Z := (Nat.zero_le k).trans_lt hk
  have hZL : Z ≤ L := (Nat.sub_pos_iff_lt.mp hsubpos).le
  have hsubadd : L - Z + Z = L := Nat.sub_add_cancel hZL
  have hjL : j < L := by
    dsimp [j]
    omega
  have hnDecomp : n = k * M + i := by
    simpa [k, i] using (Nat.div_add_mod' n M).symm
  have hsum :
      (a + j * (q * M)) + (i * q + (q * M) * z) =
        (a + (q * M) * Z) + n * q := by
    calc
      (a + j * (q * M)) + (i * q + (q * M) * z) =
          a + (j + z) * (q * M) + i * q := by ring
      _ = a + (Z + k) * (q * M) + i * q := by rw [hjEq]
      _ = (a + (q * M) * Z) + (k * M + i) * q := by ring
      _ = (a + (q * M) * Z) + n * q := by rw [← hnDecomp]
  rw [← hsum]
  exact ⟨a + j * (q * M), hAP j hjL,
    i * q + (q * M) * z, huU, rfl⟩

/-- If `U` supplies a bounded translate in every residue class modulo `M`,
then adding `U` to a long `q*M` progression produces a `q` progression. -/
lemma lowerStep_of_residue_translates {S U : Set ℕ}
    {a q M L Z : ℕ} (hq : 0 < q) (hM : 0 < M)
    (hAP : ∀ j < L, a + j * (q * M) ∈ S)
    (hres : ∀ i < M, ∃ u ∈ U, ∃ z ≤ Z, u = i * q + (q * M) * z) :
    ContainsFiniteAP (S + U) (M * (L - Z)) := by
  exact ⟨a + (q * M) * Z, q, hq,
    lowerStep_of_residue_translates_mem hq hM hAP hres⟩

lemma fixedStep_addNet_of_disjoint {B C : Set ℕ} (hBC : Disjoint B C)
    {d K : ℕ}
    (hlong : ∀ k : ℕ, ∃ a : ℕ, ∀ i < k, a + i * d ∈ subsetSums B)
    (hnet : IsAddNet d K (subsetSums C)) :
    ContainsInfiniteAP (subsetSums (B ∪ C)) := by
  obtain ⟨a, ha⟩ := hlong (K + 1)
  have hsum : ContainsInfiniteAP (subsetSums B + subsetSums C) :=
    addNet_add_finiteAP hnet ha
  exact containsInfiniteAP_mono (subsetSums_union_subset_add hBC) hsum

/-! ### Graham's bounded-gap argument, in a finite coverage form -/

private def prefixSum (y : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, y i

private lemma prefixSum_succ (y : ℕ → ℕ) (n : ℕ) :
    prefixSum y (n + 1) = prefixSum y n + y n := by
  simp only [prefixSum, Finset.sum_range_succ]

private lemma twice_triangular_le_prefixSum (y : ℕ → ℕ)
    (hy : StrictMono y) (hypos : ∀ i, 0 < y i) :
    ∀ n, n * (n + 1) ≤ 2 * prefixSum y n := by
  intro n
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      have hyn : n + 1 ≤ y n := by
        have hstep : n + y 0 ≤ y n := by
          simpa using hy.add_le_nat n 0
        have hyzero : 1 ≤ y 0 := hypos 0
        omega
      calc
        (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
        _ ≤ 2 * prefixSum y n + 2 * y n :=
          Nat.add_le_add ih (Nat.mul_le_mul_left 2 hyn)
        _ = 2 * prefixSum y (n + 1) := by rw [prefixSum_succ]; ring

/-- Above the constant `3`, square-root density forces the eventual growth
condition in Graham's bounded-gap argument. -/
lemma eventually_nth_le_prefixSum {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    (hdense : SqrtDense 3 A) :
    ∀ᶠ m : ℕ in atTop,
      Nat.nth (· ∈ A) m ≤ prefixSum (Nat.nth (· ∈ A)) m := by
  have hAinf : A.Infinite := infinite_of_sqrtDense (by norm_num) hdense
  have hinv := eventually_density_inversion hApos (by norm_num : (0 : ℝ) < 3) hdense
  filter_upwards [hinv, eventually_ge_atTop 1] with m hinv hm
  have hlower := twice_triangular_le_prefixSum
    (Nat.nth (· ∈ A)) (nth_strictMono hAinf)
    (fun i ↦ hApos (nth_mem hAinf i)) m
  have hlowerReal :
      (m : ℝ) * (m + 1) ≤
        2 * (prefixSum (Nat.nth (· ∈ A)) m : ℝ) := by
    exact_mod_cast hlower
  have hresult :
      (Nat.nth (· ∈ A) m : ℝ) ≤
        (prefixSum (Nat.nth (· ∈ A)) m : ℝ) := by
    norm_num at hinv
    have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hcompare : 2 * ((m : ℝ) + 1) ^ 2 ≤ 9 * m * (m + 1) := by
      nlinarith
    nlinarith
  exact_mod_cast hresult

/-- If every new term is at most the sum of its predecessors, subset sums of
each sufficiently long prefix cover that prefix's total interval with a fixed
additive error. -/
private lemma exists_prefix_subsetSum_near (y : ℕ → ℕ) (m₀ : ℕ)
    (hgrowth : ∀ m, m₀ ≤ m → y m ≤ prefixSum y m) :
    ∀ n, m₀ ≤ n → ∀ x ≤ prefixSum y n,
      ∃ F : Finset ℕ, F ⊆ Finset.range n ∧
        (∑ i ∈ F, y i) ≤ x ∧ x ≤ (∑ i ∈ F, y i) + prefixSum y m₀ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro x hx
      exact ⟨∅, by simp, by simp, by simpa using hx⟩
  | succ n hn ih =>
      intro x hx
      by_cases hsmall : x ≤ prefixSum y n
      · obtain ⟨F, hF, hFlo, hFhi⟩ := ih x hsmall
        exact ⟨F, hF.trans (by simp), hFlo, hFhi⟩
      · have hyn : y n ≤ prefixSum y n := hgrowth n hn
        have hyx : y n ≤ x := hyn.trans (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
        have hsub : x - y n ≤ prefixSum y n := by
          rw [prefixSum_succ] at hx
          omega
        obtain ⟨F, hF, hFlo, hFhi⟩ := ih (x - y n) hsub
        have hnF : n ∉ F := fun h ↦ by
          have := hF h
          simp at this
        refine ⟨insert n F, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · exact Finset.mem_range.mpr ((Finset.mem_range.mp (hF hi)).trans
              (Nat.lt_succ_self n))
        · rw [Finset.sum_insert hnF]
          omega
        · rw [Finset.sum_insert hnF]
          omega

private lemma id_le_prefixSum (y : ℕ → ℕ) (hy : ∀ i, 0 < y i) (n : ℕ) :
    n ≤ prefixSum y n := by
  calc
    n = ∑ _i ∈ Finset.range n, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range n, y i := by
      exact Finset.sum_le_sum fun i _ ↦ hy i
    _ = prefixSum y n := rfl

/-- A strictly enumerated positive sequence satisfying Graham's growth
condition and lying in one residue subgroup has a subset-sum additive net. -/
theorem exists_addNet_subsetSums_of_sequence {C : Set ℕ} {q : ℕ}
    (hqpos : 0 < q) (y : ℕ → ℕ) (hyinj : Function.Injective y)
    (hypos : ∀ i, 0 < y i) (hyC : ∀ i, y i ∈ C)
    (hyq : ∀ i, q ∣ y i)
    (hgrowth : ∃ m₀, ∀ m, m₀ ≤ m → y m ≤ prefixSum y m) :
    ∃ K : ℕ, IsAddNet q K (subsetSums C) := by
  obtain ⟨m₀, hgrowth⟩ := hgrowth
  let K := prefixSum y m₀
  refine ⟨K, hqpos, ?_⟩
  intro n
  let x := (n + K) * q
  let N := max m₀ x
  have hmN : m₀ ≤ N := le_max_left _ _
  have hxN : x ≤ N := le_max_right _ _
  have hxsum : x ≤ prefixSum y N :=
    hxN.trans (id_le_prefixSum y hypos N)
  obtain ⟨F, hFN, hFlo, hFhi⟩ :=
    exists_prefix_subsetSum_near y m₀ hgrowth N hmN x hxsum
  let G := F.image y
  have hsum : ∑ z ∈ G, z = ∑ i ∈ F, y i := by
    dsimp [G]
    rw [Finset.sum_image hyinj.injOn]
  have hGC : ↑G ⊆ C := by
    intro z hz
    rw [Finset.mem_coe] at hz
    change z ∈ F.image y at hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact hyC i
  have hmem : (∑ z ∈ G, z) ∈ subsetSums C :=
    ⟨G, hGC, rfl⟩
  have hdiv : q ∣ ∑ z ∈ G, z := by
    rw [hsum]
    exact Finset.dvd_sum fun i _ ↦ hyq i
  have hKq : K ≤ K * q := by
    have : 1 ≤ q := hqpos
    nlinarith
  refine ⟨∑ z ∈ G, z, hmem, hdiv, ?_, ?_⟩
  · rw [hsum]
    have hFhi' : x ≤ (∑ i ∈ F, y i) + K * q := by
      exact hFhi.trans (Nat.add_le_add_left (by simpa [K] using hKq) _)
    dsimp [x] at hFhi'
    rw [Nat.add_mul] at hFhi'
    exact Nat.le_of_add_le_add_right hFhi'
  · rw [hsum]
    exact hFlo

/-- Graham's argument specialized to a square-root-dense set in one
divisibility class. -/
theorem exists_addNet_subsetSums_of_sqrtDense {C : Set ℕ} {q : ℕ}
    (hCpos : C ⊆ Set.Ici 1) (hdense : SqrtDense 3 C)
    (hqpos : 0 < q) (hq : ∀ c ∈ C, q ∣ c) :
    ∃ K : ℕ, IsAddNet q K (subsetSums C) := by
  have hCinf : C.Infinite := infinite_of_sqrtDense (by norm_num) hdense
  let y : ℕ → ℕ := Nat.nth (· ∈ C)
  have hyinj : Function.Injective y := (nth_strictMono hCinf).injective
  have hypos : ∀ i, 0 < y i := fun i ↦ hCpos (nth_mem hCinf i)
  have hyC : ∀ i, y i ∈ C := nth_mem hCinf
  have hyq : ∀ i, q ∣ y i := fun i ↦ hq _ (hyC i)
  obtain ⟨m₀, hm₀⟩ := (eventually_atTop.1 (eventually_nth_le_prefixSum hCpos hdense))
  exact exists_addNet_subsetSums_of_sequence hqpos y hyinj hypos hyC hyq ⟨m₀, hm₀⟩

/-! ### Subgroups of a finite cyclic group -/

/-- Every additive subgroup of `ZMod d` consists exactly of the multiples
of a positive divisor `q` of `d`.  The formulation records the two directions
needed for the residue-stabilization argument below. -/
lemma exists_generator_modulus {d : ℕ} (hd : 0 < d)
    (K : AddSubgroup (ZMod d)) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧
      (∀ x : ZMod d, x ∈ K → q ∣ x.val) ∧
      (∀ i : ℕ, (i * q : ZMod d) ∈ K) := by
  letI : NeZero d := ⟨hd.ne'⟩
  let V := Finset.univ.filter fun x : ZMod d ↦ x ∈ K ∧ x ≠ 0
  by_cases hV : V.Nonempty
  · obtain ⟨g, hgV, hgmin⟩ := Finset.exists_min_image V ZMod.val hV
    have hgK : g ∈ K := (Finset.mem_filter.mp hgV).2.1
    have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgV).2.2
    let q := g.val
    have hqpos : 0 < q :=
      Nat.pos_of_ne_zero (fun h ↦ hg0 ((ZMod.val_eq_zero g).mp h))
    have hqd : q < d := g.val_lt
    have hmin : ∀ x : ZMod d, x ∈ K → x ≠ 0 → q ≤ x.val := by
      intro x hxK hx0
      exact hgmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hx0⟩)
    have hcastg : (q : ZMod d) = g := ZMod.natCast_zmod_val g
    have hqdvd : q ∣ d := by
      let r := d % q
      have hrq : r < q := Nat.mod_lt d hqpos
      have hrd : r < d := hrq.trans hqd
      have hsumZ : ((d / q * q : ℕ) : ZMod d) + (r : ZMod d) = 0 := by
        have hsum := congrArg (fun n : ℕ ↦ (n : ZMod d)) (Nat.div_add_mod' d q)
        push_cast at hsum
        simpa [r] using hsum
      have hcast : (r : ZMod d) = -((d / q : ℕ) • g) := by
        rw [← hcastg]
        simp only [nsmul_eq_mul, Nat.cast_mul]
        apply (eq_neg_iff_add_eq_zero).2
        simpa [add_comm] using hsumZ
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.neg_mem (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    refine ⟨q, hqpos, hqdvd, ?_, ?_⟩
    · intro x hxK
      let r := x.val % q
      have hrq : r < q := Nat.mod_lt x.val hqpos
      have hrd : r < d := hrq.trans hqd
      have hmul : x.val / q * q ≤ x.val := by
        simpa [mul_comm] using Nat.mul_div_le x.val q
      have hdecomp : x.val % q + x.val / q * q = x.val := by
        simpa [mul_comm] using Nat.mod_add_div x.val q
      have hsub : x.val - x.val / q * q = r := by
        dsimp [r]
        omega
      have hcast : (r : ZMod d) = x - (x.val / q : ℕ) • g := by
        calc
          (r : ZMod d) = ((x.val - x.val / q * q : ℕ) : ZMod d) := by rw [hsub]
          _ = (x.val : ZMod d) - (x.val / q * q : ℕ) := by
            rw [Nat.cast_sub hmul]
          _ = x - (x.val / q : ℕ) • g := by
            rw [ZMod.natCast_zmod_val x, Nat.cast_mul, hcastg]
            simp [nsmul_eq_mul]
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.sub_mem hxK (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    · intro i
      have hi : (i * q : ZMod d) = i • g := by
        rw [← hcastg]
        simp [nsmul_eq_mul]
      rw [hi]
      exact K.nsmul_mem hgK i
  · refine ⟨d, hd, dvd_rfl, ?_, ?_⟩
    · intro x hxK
      have hx0 : x = 0 := by
        by_contra hxne
        exact hV ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hxne⟩⟩
      rw [hx0]
      simp
    · intro i
      simp

/-- The two membership directions supplied by `exists_generator_modulus`
identify the subgroup with the usual cyclic subgroup generated by `q`. -/
lemma subgroup_eq_zmultiples_of_generator_modulus
    {d q : ℕ} [NeZero d] (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    H = AddSubgroup.zmultiples (q : ZMod d) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := hHdiv x hx
    rw [← ZMod.natCast_zmod_val x, hi, Nat.cast_mul]
    change ((q : ZMod d) * (i : ZMod d)) ∈
      AddSubgroup.zmultiples (q : ZMod d)
    rw [mul_comm]
    simpa [nsmul_eq_mul] using
      ((AddSubgroup.zmultiples (q : ZMod d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q : ZMod d)) i)
  · intro x hx
    obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    cases i with
    | ofNat i =>
        simpa [nsmul_eq_mul, mul_comm] using hmult i
    | negSucc i =>
        have hi : (i + 1) • (q : ZMod d) ∈ H := by
          simpa [nsmul_eq_mul, mul_comm] using hmult (i + 1)
        have hneg := H.neg_mem hi
        convert hneg using 1 <;> simp [nsmul_eq_mul] <;> ring

/-- Cardinality of the subgroup of multiples of `q` in `ZMod d`. -/
lemma natCard_subgroup_of_generator_modulus
    {d q : ℕ} (hd : 0 < d) (_hq : 0 < q) (hqd : q ∣ d)
    (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    Nat.card H = d / q := by
  letI : NeZero d := ⟨hd.ne'⟩
  rw [subgroup_eq_zmultiples_of_generator_modulus H hHdiv hmult,
    Nat.card_zmultiples, ZMod.addOrderOf_coe q hd.ne']
  have hgcd : d.gcd q = q := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left_iff_dvd.mpr hqd
  rw [hgcd]

lemma ncard_addSubgroup_eq_natCard {G : Type*} [AddGroup G]
    (H : AddSubgroup G) : (H : Set G).ncard = Nat.card H := by
  rw [← Set.ncard_univ H]
  apply Set.ncard_congr (fun x hx => (⟨x, hx⟩ : H))
  · simp
  · intro a b ha hb hab
    exact congrArg Subtype.val hab
  · intro b _
    exact ⟨b.1, b.2, Subtype.ext rfl⟩

/-- Set-cardinality form used for normalized coset fibres. -/
lemma ncard_subgroup_of_generator_modulus
    {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (hqd : q ∣ d)
    (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    (H : Set (ZMod d)).ncard = d / q := by
  rw [ncard_addSubgroup_eq_natCard H]
  exact natCard_subgroup_of_generator_modulus hd hq hqd H hHdiv hmult

/-! ### Divisor-sensitive modular completeness -/

/-- A homomorphism sends the subset sums of a list onto the subset sums of
the mapped list. -/
lemma image_listSubsetSums_map {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
    (f : G →+ H) (A : List G) :
    (Erdos587.listSubsetSums A).image f =
      Erdos587.listSubsetSums (A.map f) := by
  have image_addTranslate (a : G) (S : Finset G) :
      (Erdos587.addTranslate a S).image f =
        Erdos587.addTranslate (f a) (S.image f) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      rw [Erdos587.mem_addTranslate] at hx ⊢
      apply Finset.mem_image.mpr
      refine ⟨-a + x, hx, ?_⟩
      rw [map_add, map_neg, hxy]
    · intro hy
      rw [Erdos587.mem_addTranslate] at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨a + x, ?_, ?_⟩
      · rw [Erdos587.mem_addTranslate]
        simpa
      · rw [map_add, hxy]
        abel
  induction A with
  | nil => simp [Erdos587.listSubsetSums]
  | cons a A ih =>
      simp only [Erdos587.listSubsetSums_cons, List.map_cons,
        Finset.image_union, ih]
      rw [image_addTranslate, ih]

lemma zmod_castHom_eq_zero_iff_val_dvd {q d : ℕ} [NeZero q]
    (hdq : d ∣ q) (x : ZMod q) :
    ZMod.castHom hdq (ZMod d) x = 0 ↔ d ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- If a surjective homomorphism has exactly the translation stabilizer of
`S` as its kernel, the image of `S` has trivial translation stabilizer. -/
lemma image_stabilizer_eq_bot {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (S : Finset G)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    Erdos587.finsetAddStabilizer (S.image f) = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have hy' : Erdos587.addTranslate (f x) (S.image f) = S.image f := hy
  have hxsub : Erdos587.addTranslate x S ⊆ S := by
    intro z hz
    have hs : -x + z ∈ S := Erdos587.mem_addTranslate.mp hz
    have hfs : f (-x + z) ∈ S.image f :=
      Finset.mem_image.mpr ⟨_, hs, rfl⟩
    have hfztrans : f z ∈ Erdos587.addTranslate (f x) (S.image f) := by
      apply Finset.mem_image.mpr
      refine ⟨f (-x + z), hfs, ?_⟩
      simp only [map_add, map_neg]
      abel
    rw [hy'] at hfztrans
    obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfztrans
    have hzero : f (z - t) = 0 := by
      rw [map_sub, hft]
      simp
    have hstab : z - t ∈ Erdos587.finsetAddStabilizer S :=
      (hker _).mp hzero
    have hmem : (z - t) + t ∈ Erdos587.addTranslate (z - t) S := by
      apply Finset.mem_image.mpr
      exact ⟨t, ht, rfl⟩
    rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
    simpa using hmem
  have hxstab : Erdos587.addTranslate x S = S := by
    exact Finset.eq_of_subset_of_card_le hxsub (by
      rw [Erdos587.card_addTranslate])
  have hxker : f x = 0 := (hker x).mpr hxstab
  simpa [hxker]

/-- Under the same kernel hypothesis, a proper set has proper image. -/
lemma image_ne_univ_of_stabilizer_kernel {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (S : Finset G) (hSproper : S ≠ Finset.univ)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    S.image f ≠ Finset.univ := by
  intro himage
  apply hSproper
  apply Finset.eq_univ_of_forall
  intro x
  have hfx : f x ∈ S.image f := by rw [himage]; simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfx
  have hzero : f (x - t) = 0 := by rw [map_sub, hft]; simp
  have hstab : x - t ∈ Erdos587.finsetAddStabilizer S :=
    (hker _).mp hzero
  have hmem : (x - t) + t ∈ Erdos587.addTranslate (x - t) S := by
    apply Finset.mem_image.mpr
    exact ⟨t, ht, rfl⟩
  rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
  simpa using hmem

/-- If the final subset-sum stabilizer is trivial and the subset sums are
proper, fewer than `|G|-1` list occurrences are nonzero. -/
lemma nonzero_length_add_one_lt_card_of_stabilizer_bot
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : List G)
    (hproper : Erdos587.listSubsetSums A ≠ Finset.univ)
    (hstab : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums A) = ⊥) :
    (A.filter fun a => a ≠ 0).length + 1 < Fintype.card G := by
  have hstable :
      (Erdos587.subsetSumStableTerms A).filter (fun a => a ≠ 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have haStab : a ∈ Erdos587.finsetAddStabilizer
        (Erdos587.listSubsetSums A) :=
      Erdos587.mem_stable_stabilizes_listSubsetSums ha
    rw [hstab] at haStab
    simpa using haStab
  have hperm :=
    (Erdos587.stable_append_growth_perm A).filter (fun a => a ≠ 0)
  have hlen :
      (A.filter fun a => a ≠ 0).length ≤
        (Erdos587.subsetSumGrowthTerms A).length := by
    rw [← hperm.length_eq, List.filter_append, hstable]
    exact List.length_filter_le _ _
  have hcardlt : (Erdos587.listSubsetSums A).card < Fintype.card G := by
    have hss : Erdos587.listSubsetSums A ⊂ (Finset.univ : Finset G) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩
    exact Finset.card_lt_card hss
  have hgrowth := Erdos587.growth_length_add_one_le_card_listSubsetSums A
  omega

lemma length_filter_zmod_castHom_ne_zero
    {q d : ℕ} [NeZero q] [NeZero d] (hdq : d ∣ q) (A : List ℕ) :
    ((A.map fun a : ℕ => ZMod.castHom hdq (ZMod d) (a : ZMod q)).filter
      fun x => x ≠ 0).length =
      (A.filter fun a => ¬ d ∣ a).length := by
  induction A with
  | nil => simp
  | cons a A ih =>
      simp only [List.map_cons, map_natCast]
      have ih' :
          ((A.map fun a : ℕ => (a : ZMod d)).filter fun x => x ≠ 0).length =
            (A.filter fun a => ¬ d ∣ a).length := by
        simpa only [map_natCast] using ih
      by_cases ha : d ∣ a
      · have ha0 : (a : ZMod d) = 0 :=
          (ZMod.natCast_eq_zero_iff a d).mpr ha
        rw [List.filter_cons_of_neg (by simpa using ha0),
          List.filter_cons_of_neg (by simpa using ha)]
        exact ih'
      · have ha0 : (a : ZMod d) ≠ 0 :=
          fun h => ha ((ZMod.natCast_eq_zero_iff a d).mp h)
        rw [List.filter_cons_of_pos (by simp [ha0]),
          List.filter_cons_of_pos (by simp [ha]),
          List.length_cons, List.length_cons, ih']

/-- A divisor-diverse list is complete modulo `q`.  This is the
Conlon--Fox--Pham modular completeness criterion: for every divisor `d > 1`
of `q`, `d - 1` nonmultiples force all residues to occur as subset sums. -/
theorem listSubsetSums_mod_eq_univ_of_divisor_diverse
    {q : ℕ} [NeZero q] (hq : 0 < q) (A : List ℕ)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ (A.filter fun a => ¬ d ∣ a).length) :
    Erdos587.listSubsetSums (A.map fun a : ℕ => (a : ZMod q)) =
      Finset.univ := by
  let M : List (ZMod q) := A.map fun a : ℕ => (a : ZMod q)
  let S : Finset (ZMod q) := Erdos587.listSubsetSums M
  by_contra hproper
  have hproperS : S ≠ Finset.univ := by simpa [S, M] using hproper
  let K : AddSubgroup (ZMod q) := Erdos587.finsetAddStabilizer S
  have hKproper : K ≠ ⊤ :=
    Erdos587.finsetAddStabilizer_ne_top
      (by simpa [S] using Erdos587.zero_mem_listSubsetSums M) hproperS
  obtain ⟨d, hdpos, hdq, hKdiv, hmultK⟩ := exists_generator_modulus hq K
  have hdgt : 1 < d := by
    by_contra hnot
    have hd1 : d = 1 := by omega
    apply hKproper
    apply top_unique
    intro x _
    rw [← ZMod.natCast_zmod_val x]
    simpa [hd1] using hmultK x.val
  letI : NeZero d := ⟨hdpos.ne'⟩
  let f : ZMod q →+ ZMod d :=
    (ZMod.castHom hdq (ZMod d)).toAddMonoidHom
  have hfsurj : Function.Surjective f := by
    intro y
    refine ⟨(y.val : ZMod q), ?_⟩
    have hdqle : d ≤ q := Nat.le_of_dvd hq hdq
    have hyq : y.val < q := y.val_lt.trans_le hdqle
    dsimp [f]
    rw [ZMod.cast_eq_val, ZMod.val_natCast, Nat.mod_eq_of_lt hyq]
    exact ZMod.natCast_zmod_val y
  have hker : ∀ x : ZMod q,
      f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S := by
    intro x
    constructor
    · intro hx
      have hdval : d ∣ x.val :=
        (zmod_castHom_eq_zero_iff_val_dvd hdq x).mp (by
          simpa [f] using hx)
      obtain ⟨i, hi⟩ := hdval
      have hxrepr : x = (i * d : ℕ) := by
        calc
          x = (x.val : ZMod q) := (ZMod.natCast_zmod_val x).symm
          _ = (d * i : ℕ) := by rw [hi]
          _ = (i * d : ℕ) := by rw [mul_comm]
      rw [hxrepr]
      change ((i * d : ℕ) : ZMod q) ∈ K
      simpa only [Nat.cast_mul] using hmultK i
    · intro hx
      apply (zmod_castHom_eq_zero_iff_val_dvd hdq x).mpr
      exact hKdiv x hx
  let B : List (ZMod d) := M.map f
  have himage : S.image f = Erdos587.listSubsetSums B := by
    simpa [S, B] using image_listSubsetSums_map f M
  have hproperB : Erdos587.listSubsetSums B ≠ Finset.univ := by
    intro hall
    have himageProper := image_ne_univ_of_stabilizer_kernel
      f S hproperS hker
    apply himageProper
    rw [himage, hall]
  have hstabB : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums B) = ⊥ := by
    have hstab := image_stabilizer_eq_bot f hfsurj S hker
    rwa [himage] at hstab
  have hfew := nonzero_length_add_one_lt_card_of_stabilizer_bot
    B hproperB hstabB
  have hfew' : (B.filter fun a => a ≠ 0).length + 1 < d := by
    simpa [ZMod.card] using hfew
  have hfilter :
      (B.filter fun a => a ≠ 0).length =
        (A.filter fun a => ¬ d ∣ a).length := by
    simpa [B, M, f, List.map_map, Function.comp_def] using
      length_filter_zmod_castHom_ne_zero hdq A
  rw [hfilter] at hfew'
  have hlower := hdiverse d hdgt hdq
  omega

/-! ### The unsaturated modular-growth step -/

/-- A finite set containing zero and generating the ambient finite group is
not contained in a coset of a proper subgroup. -/
lemma notContainedInProperCoset_of_zero_mem_closure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} (hzero : 0 ∈ P)
    (hclosure : AddSubgroup.closure (P : Set G) = ⊤) :
    Erdos360.NotContainedInProperCoset P := by
  intro H hH a hsub
  have hPa : ∀ x ∈ P, ∃ y : G, y ∈ H ∧ a + y = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hsub (by simpa using hx)
    exact ⟨y, by simpa using hy, by simpa using hxy⟩
  obtain ⟨y0, hy0, hay0⟩ := hPa 0 hzero
  have hPsub : (P : Set G) ⊆ H := by
    intro x hx
    obtain ⟨y, hy, hay⟩ := hPa x (by simpa using hx)
    have haH : a ∈ H := by
      have hneg : -y0 ∈ H := H.neg_mem hy0
      have haeq : a = -y0 := by
        rw [← add_left_inj y0]
        simpa [add_comm] using hay0
      simpa [haeq] using hneg
    have hsum : a + y ∈ H := H.add_mem haH hy
    simpa [hay] using hsum
  have htop_le : (⊤ : AddSubgroup G) ≤ H := by
    rw [← hclosure, AddSubgroup.closure_le]
    exact hPsub
  exact hH (top_unique htop_le)

/-- Iterated sums of shifts which each add at most `e` points add at most
`k*e` points. -/
lemma iteratedFinsetSum_almostPeriods_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (U : Finset G) (e k : ℕ) :
    Erdos360.iteratedFinsetSum (Erdos360.almostPeriods U e) k ⊆
      Erdos360.almostPeriods U (k * e) := by
  induction k with
  | zero => simp [Erdos360.iteratedFinsetSum]
  | succ k ih =>
      intro x hx
      rw [Erdos360.iteratedFinsetSum_succ, Finset.mem_add] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have ha' := ih ha
      have hab := Erdos360.add_mem_almostPeriods ha' hb
      simpa [Nat.succ_mul, Nat.add_comm] using hab

/-- CFP's unsaturated-phase estimate.  If `X` generates a finite abelian
group and `U` lies below one quarter of that group but above one quarter of
`X`, some translate by a member of `X` adds at least `|X|/16` new points. -/
lemma exists_translationNew_large_of_closure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {U X : Finset G} (hU : U.Nonempty) (hX : X.Nonempty)
    (hXU : X.card < 4 * U.card)
    (hUG : 4 * U.card < Fintype.card G)
    (hclosure : AddSubgroup.closure (X : Set G) = ⊤) :
    ∃ x ∈ X, X.card ≤ 16 * (Erdos360.translationNew U x).card := by
  classical
  by_contra hnone
  push Not at hnone
  let e := X.card / 16
  let k := 4 * U.card / X.card
  let P := Erdos360.almostPeriods U e
  have hXpos : 0 < X.card := Finset.card_pos.mpr hX
  have hUP : 0 < U.card := Finset.card_pos.mpr hU
  have hXP : X ⊆ P := by
    intro x hx
    rw [Erdos360.mem_almostPeriods_iff_card_translationNew_le]
    have hsmall := hnone x hx
    dsimp [e]
    omega
  have hzeroP : 0 ∈ P := by simp [P]
  have hclosureP : AddSubgroup.closure (P : Set G) = ⊤ := by
    apply top_unique
    rw [← hclosure]
    apply AddSubgroup.closure_mono
    exact_mod_cast hXP
  have hPcoset : Erdos360.NotContainedInProperCoset P :=
    notContainedInProperCoset_of_zero_mem_closure_eq_top hzeroP hclosureP
  have hkpos : 1 ≤ k := by
    dsimp [k]
    rw [Nat.le_div_iff_mul_le hXpos]
    omega
  have hke : 2 * (k * e) ≤ U.card := by
    have he : 16 * e ≤ X.card := by
      dsimp [e]
      exact Nat.mul_div_le _ _
    have hkX : k * X.card ≤ 4 * U.card := by
      dsimp [k]
      exact Nat.div_mul_le_self _ _
    nlinarith
  have hiterSub : Erdos360.iteratedFinsetSum P k ⊆
      Erdos360.almostPeriods U (k * e) := by
    simpa [P] using iteratedFinsetSum_almostPeriods_subset U e k
  have hAPbound := Erdos360.card_sub_mul_card_almostPeriods_le_sq U (k * e)
  have hden : U.card ≤ 2 * (U.card - k * e) := by omega
  have hAPcard : (Erdos360.almostPeriods U (k * e)).card ≤ 2 * U.card := by
    have hmul : U.card * (Erdos360.almostPeriods U (k * e)).card ≤
        U.card * (2 * U.card) := by
      calc
        U.card * (Erdos360.almostPeriods U (k * e)).card ≤
            2 * ((U.card - k * e) *
              (Erdos360.almostPeriods U (k * e)).card) := by nlinarith
        _ ≤ 2 * U.card ^ 2 := Nat.mul_le_mul_left 2 hAPbound
        _ = U.card * (2 * U.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hUP
  have hiterCard : (Erdos360.iteratedFinsetSum P k).card ≤ 2 * U.card :=
    (Finset.card_le_card hiterSub).trans hAPcard
  have hlower :=
    Erdos360.min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroP⟩ hPcoset k hkpos
  have hiter4 : 2 * (Erdos360.iteratedFinsetSum P k).card ≤
      4 * U.card := by omega
  have htarget : (k + 1) * P.card ≤ 4 * U.card := by
    rcases le_total (2 * Fintype.card G) ((k + 1) * P.card) with hle | hle
    · have hgroup : 2 * Fintype.card G ≤
          2 * (Erdos360.iteratedFinsetSum P k).card := by
        simpa [min_eq_left hle] using hlower
      have : 2 * Fintype.card G ≤ 4 * U.card := hgroup.trans hiter4
      omega
    · have hmain : (k + 1) * P.card ≤
          2 * (Erdos360.iteratedFinsetSum P k).card := by
        simpa [min_eq_right hle] using hlower
      exact hmain.trans hiter4
  have hXcardP : X.card ≤ P.card := Finset.card_le_card hXP
  have hupper : (k + 1) * X.card ≤ 4 * U.card :=
    (Nat.mul_le_mul_left (k + 1) hXcardP).trans htarget
  have hstrict : 4 * U.card < X.card * (k + 1) := by
    dsimp [k]
    exact Nat.lt_mul_div_succ (4 * U.card) hXpos
  nlinarith [hupper]

/-- The quantitative choice used in a CFP growth phase: if the current
internal subset-sum set has fewer than half as many points as the remaining
set, one remaining shift grows it by a factor of at least `3/2`. -/
lemma exists_three_halves_growth
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T X : Finset G} (hT : T.Nonempty) (_hX : X.Nonempty)
    (hsmall : 2 * T.card < X.card) :
    ∃ x ∈ X,
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  let e := T.card / 2
  let P := Erdos360.almostPeriods T e
  have hTpos : 0 < T.card := Finset.card_pos.mpr hT
  have hden : T.card ≤ 2 * (T.card - e) := by
    dsimp [e]
    omega
  have hAPbound := Erdos360.card_sub_mul_card_almostPeriods_le_sq T e
  have hPcard : P.card ≤ 2 * T.card := by
    have hmul : T.card * P.card ≤ T.card * (2 * T.card) := by
      calc
        T.card * P.card ≤ 2 * ((T.card - e) * P.card) := by nlinarith
        _ ≤ 2 * T.card ^ 2 := by
          exact Nat.mul_le_mul_left 2 (by simpa [P] using hAPbound)
        _ = T.card * (2 * T.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hTpos
  have hnot : ¬ X ⊆ P := by
    intro hXP
    have := (Finset.card_le_card hXP).trans hPcard
    omega
  obtain ⟨x, hxX, hxP⟩ := Finset.not_subset.mp hnot
  refine ⟨x, hxX, ?_⟩
  have hnew : e < (Erdos360.translationNew T x).card := by
    contrapose! hxP
    exact Erdos360.mem_almostPeriods_iff_card_translationNew_le.mpr hxP
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x T) T
  have hunion : (T ∪ Erdos587.addTranslate x T).card =
      T.card + (Erdos360.translationNew T x).card := by
    dsimp [Erdos360.translationNew] at hsdiff ⊢
    rw [Finset.union_comm] at hsdiff
    omega
  rw [hunion]
  dsimp [e] at hnew
  omega

/-- The remaining elements of a modular phase, regarded inside the subgroup
which they generate. -/
noncomputable def liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (X : Finset G) :
    Finset (AddSubgroup.closure (X : Set G)) := by
  classical
  letI : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) => x.1)
      Subtype.val_injective
  exact Finset.univ.filter fun x => x.1 ∈ X

@[simp] lemma mem_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {X : Finset G} {x : AddSubgroup.closure (X : Set G)} :
    x ∈ liftFinsetToClosure X ↔ x.1 ∈ X := by
  letI : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) => x.1)
      Subtype.val_injective
  simp [liftFinsetToClosure]

lemma card_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) : (liftFinsetToClosure X).card = X.card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  have himage : (liftFinsetToClosure X).image (fun x : H => x.1) = X := by
    ext x
    simp only [Finset.mem_image, mem_liftFinsetToClosure]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_liftFinsetToClosure.mp hy
    · intro hx
      exact ⟨⟨x, AddSubgroup.subset_closure hx⟩,
        mem_liftFinsetToClosure.mpr hx, rfl⟩
  calc
    (liftFinsetToClosure X).card =
        ((liftFinsetToClosure X).image (fun x : H => x.1)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = X.card := by rw [himage]

lemma closure_liftFinsetToClosure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) :
    AddSubgroup.closure ((liftFinsetToClosure X :
      Finset (AddSubgroup.closure (X : Set G))) :
        Set (AddSubgroup.closure (X : Set G))) = ⊤ := by
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  have hset : ((liftFinsetToClosure X : Finset H) : Set H) =
      H.subtype ⁻¹' (X : Set G) := by
    ext x
    simp [H]
  rw [hset]
  exact AddSubgroup.closure_preimage_eq_top (X : Set G)

/-- A coset fibre of `S`, translated back into its subgroup. -/
noncomputable def normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G) (u : G) : Finset H := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  exact Finset.univ.filter fun h => u + h.1 ∈ S

@[simp] lemma mem_normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {S : Finset G} {u : G} {h : H} :
    h ∈ normalizedCosetFiber H S u ↔ u + h.1 ∈ S := by
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  simp [normalizedCosetFiber]

lemma card_translationNew_normalizedCosetFiber_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G) (u : G) (x : H) :
    (Erdos360.translationNew (normalizedCosetFiber H S u) x).card ≤
      (Erdos360.translationNew S x.1).card := by
  classical
  let f : H → G := fun h => u + h.1
  apply Finset.card_le_card_of_injOn f
  · intro h hh
    rw [Finset.mem_coe, Erdos360.translationNew, Finset.mem_sdiff] at hh
    rw [Finset.mem_coe, Erdos360.translationNew, Finset.mem_sdiff]
    constructor
    · rw [Erdos587.mem_addTranslate] at hh ⊢
      simpa [f, add_assoc, add_left_comm, add_comm] using hh.1
    · simpa [f] using hh.2
  · intro a _ b _ hab
    apply Subtype.ext
    exact add_left_cancel hab

/-- Unsaturated growth in one coset implies the same quantitative growth of
the entire modular subset-sum set. -/
lemma exists_translationNew_large_of_normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S X : Finset G} {u : G}
    (hU : (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).Nonempty)
    (hX : X.Nonempty)
    (hXU : X.card < 4 *
      (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).card)
    (hUG : 4 *
      (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).card <
        (AddSubgroup.closure (X : Set G) : Set G).ncard) :
    ∃ x ∈ X, X.card ≤ 16 * (Erdos360.translationNew S x).card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  let XH : Finset H := liftFinsetToClosure X
  let U : Finset H := normalizedCosetFiber H S u
  have hXH : XH.Nonempty := by
    apply Finset.card_pos.mp
    rw [show XH.card = X.card by exact card_liftFinsetToClosure X]
    exact Finset.card_pos.mpr hX
  have hXcard : XH.card = X.card := card_liftFinsetToClosure X
  have hUG' : 4 * U.card < Fintype.card H := by
    have hcardH : Fintype.card H = (H : Set G).ncard := by
      exact Set.fintypeCard_eq_ncard (H : Set G)
    rw [hcardH]
    simpa [U, H] using hUG
  obtain ⟨x, hxXH, hxlarge⟩ :=
    exists_translationNew_large_of_closure_eq_top hU hXH
      (by simpa [U, hXcard] using hXU)
      hUG'
      (closure_liftFinsetToClosure_eq_top X)
  refine ⟨x.1, (mem_liftFinsetToClosure.mp hxXH), ?_⟩
  have hle := card_translationNew_normalizedCosetFiber_le H S u x
  rw [← hXcard]
  exact hxlarge.trans (Nat.mul_le_mul_left 16 hle)

/-! ### Coset fibres of ordinary finite subset sums -/

/-- Adjoining a genuinely new group element replaces the finite subset-sum
set by its union with one translate. -/
lemma subsetSum_insert_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (a : G) (haA : a ∉ A) :
    (insert a A).subsetSum =
      A.subsetSum ∪ Erdos587.addTranslate a A.subsetSum := by
  ext x
  simp only [Finset.mem_subsetSum_iff, Finset.mem_union]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases ha : a ∈ B
    · right
      rw [Erdos587.mem_addTranslate, Finset.mem_subsetSum_iff]
      refine ⟨B.erase a, ?_, ?_⟩
      · intro y hy
        have hy' := Finset.mem_erase.mp hy
        exact (Finset.mem_insert.mp (hB hy'.2)).resolve_left
          (fun h => hy'.1 h)
      · have he := Finset.sum_erase_add B id ha
        simp only [id_eq] at he
        rw [← he]
        abel
    · left
      exact ⟨B, fun y hy => (Finset.mem_insert.mp (hB hy)).resolve_left
        (fun h => ha (h ▸ hy)), rfl⟩
  · rintro (⟨B, hB, rfl⟩ | hx)
    · exact ⟨B, hB.trans (Finset.subset_insert a A), rfl⟩
    · rw [Erdos587.mem_addTranslate] at hx
      obtain ⟨B, hB, hsum⟩ := Finset.mem_subsetSum_iff.mp hx
      have ha : a ∉ B := fun haB => haA (hB haB)
      refine ⟨insert a B, Finset.insert_subset_insert a hB, ?_⟩
      rw [Finset.sum_insert ha, hsum]
      abel

lemma listSubsetSums_eq_of_perm
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : List G} (h : A.Perm B) :
    Erdos587.listSubsetSums A = Erdos587.listSubsetSums B := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Erdos587.listSubsetSums_cons, ih]
  | swap a b l =>
      simp only [Erdos587.listSubsetSums_cons,
        Erdos587.addTranslate_union, Erdos587.addTranslate_add]
      rw [add_comm a b]
      ac_rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Mathlib's finite-set subset sums and the occurrence-list recursion agree
when the list is the duplicate-free list of a finset. -/
lemma listSubsetSums_toList_eq_subsetSum
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    Erdos587.listSubsetSums A.toList = A.subsetSum := by
  induction A using Finset.induction with
  | empty =>
      simp [Erdos587.listSubsetSums_nil, Finset.subsetSum]
  | @insert a A ha ih =>
      rw [listSubsetSums_eq_of_perm (Finset.toList_insert ha)]
      simp only [Erdos587.listSubsetSums_cons, ih]
      symm
      exact subsetSum_insert_eq A a ha

/-- The elements of a finite ambient set which lie in a subgroup, lifted to
the subgroup subtype. -/
noncomputable def elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) : Finset H := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  exact Finset.univ.filter fun h => h.1 ∈ A

@[simp] lemma mem_elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {A : Finset G} {h : H} :
    h ∈ elementsInSubgroup H A ↔ h.1 ∈ A := by
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  simp [elementsInSubgroup]

lemma exists_finset_sum_val_of_mem_subsetSum_elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {A : Finset G} {t : H}
    (ht : t ∈ (elementsInSubgroup H A).subsetSum) :
    ∃ U : Finset G, U ⊆ A ∧ (∀ x ∈ U, x ∈ H) ∧
      ∑ x ∈ U, x = t.1 := by
  rw [Finset.mem_subsetSum_iff] at ht
  obtain ⟨T, hT, hsum⟩ := ht
  let U : Finset G := T.image fun h : H => h.1
  have hU : U ⊆ A := by
    intro x hx
    obtain ⟨h, hhT, rfl⟩ := Finset.mem_image.mp hx
    exact mem_elementsInSubgroup.mp (hT hhT)
  refine ⟨U, hU, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx
    exact h.2
  · change ∑ x ∈ T.image (fun h : H => h.1), x = t.1
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    have he := congrArg Subtype.val hsum
    simpa using he

/-- CFP Lemma 5.11: every occupied subgroup coset of a subset-sum set
contains at least as many points as the subset sums made only from elements
of that subgroup. -/
lemma subsetSum_fiber_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (u : G)
    (hU : (normalizedCosetFiber H A.subsetSum u).Nonempty) :
    (elementsInSubgroup H A).subsetSum.card ≤
      (normalizedCosetFiber H A.subsetSum u).card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  obtain ⟨h₀, hh₀⟩ := hU
  have hy : u + h₀.1 ∈ A.subsetSum :=
    mem_normalizedCosetFiber.mp hh₀
  rw [Finset.mem_subsetSum_iff] at hy
  obtain ⟨B, hBA, hBsum⟩ := hy
  let B₀ := B.filter fun x => x ∉ H
  let B₁ := B.filter fun x => x ∈ H
  let y := ∑ x ∈ B₀, x
  have hBsplit : B₀ ∪ B₁ = B := by
    ext x
    by_cases hx : x ∈ H <;> simp [B₀, B₁, hx]
  have hBdisj : Disjoint B₀ B₁ := by
    rw [Finset.disjoint_left]
    intro x hx₀ hx₁
    exact (Finset.mem_filter.mp hx₀).2 (Finset.mem_filter.mp hx₁).2
  have hysum : y + ∑ x ∈ B₁, x = u + h₀.1 := by
    rw [← Finset.sum_union hBdisj, hBsplit, hBsum]
  have hB₁H : ∑ x ∈ B₁, x ∈ H := by
    apply H.sum_mem
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hycoset : -u + y ∈ H := by
    have heq : -u + y = h₀.1 - ∑ x ∈ B₁, x := by
      calc
        -u + y = (-u + (y + ∑ x ∈ B₁, x)) - ∑ x ∈ B₁, x := by abel
        _ = (-u + (u + h₀.1)) - ∑ x ∈ B₁, x := by rw [hysum]
        _ = h₀.1 - ∑ x ∈ B₁, x := by abel
    rw [heq]
    exact H.sub_mem h₀.2 hB₁H
  let base : H := ⟨-u + y, hycoset⟩
  let f : H → H := fun t => base + t
  apply Finset.card_le_card_of_injOn f
  · intro t ht
    rw [Finset.mem_coe, mem_normalizedCosetFiber]
    obtain ⟨T, hTA, hTH, hTsum⟩ :=
      exists_finset_sum_val_of_mem_subsetSum_elementsInSubgroup ht
    rw [Finset.mem_subsetSum_iff]
    have hBT : Disjoint B₀ T := by
      rw [Finset.disjoint_left]
      intro x hxB hxT
      exact (Finset.mem_filter.mp hxB).2 (hTH x hxT)
    refine ⟨B₀ ∪ T, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union] at hx
      exact hx.elim
        (fun h => hBA (Finset.filter_subset _ _ h))
        (fun h => hTA h)
    · rw [Finset.sum_union hBT, hTsum]
      change y + t.1 = u + (base + t).1
      dsimp [base]
      abel
  · intro a _ b _ hab
    exact add_left_cancel hab

/-- Seeded form of CFP Lemma 5.11.  This is the form used in Lemma 6.2,
where the seed contributes exactly one summand and subsequent phases adjoin
ordinary subset sums. -/
lemma seededSubsetSum_fiber_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (E A : Finset G) (u : G)
    (hU : (normalizedCosetFiber H (E + A.subsetSum) u).Nonempty) :
    (elementsInSubgroup H A).subsetSum.card ≤
      (normalizedCosetFiber H (E + A.subsetSum) u).card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  obtain ⟨h₀, hh₀⟩ := hU
  have hsum : u + h₀.1 ∈ E + A.subsetSum :=
    mem_normalizedCosetFiber.mp hh₀
  rw [Finset.mem_add] at hsum
  obtain ⟨e, he, x, hx, hex⟩ := hsum
  have hxcoset : -(u - e) + x ∈ H := by
    have heq : -(u - e) + x = h₀.1 := by
      calc
        -(u - e) + x = -u + (e + x) := by abel
        _ = -u + (u + h₀.1) := by rw [hex]
        _ = h₀.1 := by abel
    rw [heq]
    exact h₀.2
  let hxH : H := ⟨-(u - e) + x, hxcoset⟩
  have hxEq : (u - e) + hxH.1 = x := by
    dsimp [hxH]
    abel
  have hfiberA :
      (normalizedCosetFiber H A.subsetSum (u - e)).Nonempty := by
    refine ⟨hxH, ?_⟩
    rw [mem_normalizedCosetFiber, hxEq]
    exact hx
  have hcard := subsetSum_fiber_lower H A (u - e) hfiberA
  exact hcard.trans (Finset.card_le_card (by
    intro h hh
    rw [mem_normalizedCosetFiber] at hh ⊢
    rw [Finset.mem_add]
    refine ⟨e, he, (u - e) + h.1, hh, ?_⟩
    abel))

/-! ### The cyclic modulus attached to a remaining phase set -/

/-- The positive divisor `q ∣ b` for which the subgroup generated by `R`
is the subgroup of multiples of `q`. -/
noncomputable def closureModulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : ℕ :=
  Classical.choose (exists_generator_modulus hb
    (AddSubgroup.closure (R : Set (ZMod b))))

lemma closureModulus_spec {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    0 < closureModulus hb R ∧ closureModulus hb R ∣ b ∧
      (∀ x : ZMod b, x ∈ AddSubgroup.closure (R : Set (ZMod b)) →
        closureModulus hb R ∣ x.val) ∧
      (∀ i : ℕ, (i * closureModulus hb R : ZMod b) ∈
        AddSubgroup.closure (R : Set (ZMod b))) :=
  Classical.choose_spec (exists_generator_modulus hb
    (AddSubgroup.closure (R : Set (ZMod b))))

lemma closureModulus_pos {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : 0 < closureModulus hb R :=
  (closureModulus_spec hb R).1

lemma closureModulus_dvd {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : closureModulus hb R ∣ b :=
  (closureModulus_spec hb R).2.1

lemma closure_eq_zmultiples_modulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    AddSubgroup.closure (R : Set (ZMod b)) =
      AddSubgroup.zmultiples (closureModulus hb R : ZMod b) :=
  subgroup_eq_zmultiples_of_generator_modulus _
    (closureModulus_spec hb R).2.2.1
    (closureModulus_spec hb R).2.2.2

lemma mem_closure_iff_modulus_dvd_val {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) (x : ZMod b) :
    x ∈ AddSubgroup.closure (R : Set (ZMod b)) ↔
      closureModulus hb R ∣ x.val := by
  constructor
  · exact (closureModulus_spec hb R).2.2.1 x
  · rintro ⟨i, hi⟩
    have hmultiple := (closureModulus_spec hb R).2.2.2 i
    have hx : x = (i * closureModulus hb R : ℕ) := by
      calc
        x = (x.val : ZMod b) := (ZMod.natCast_zmod_val x).symm
        _ = (closureModulus hb R * i : ℕ) := by rw [hi]
        _ = (i * closureModulus hb R : ℕ) := by rw [mul_comm]
    rw [hx]
    simpa only [Nat.cast_mul] using hmultiple

lemma ncard_closure_eq_div_modulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard =
      b / closureModulus hb R :=
  ncard_subgroup_of_generator_modulus hb (closureModulus_pos hb R)
    (closureModulus_dvd hb R) _
    (closureModulus_spec hb R).2.2.1
    (closureModulus_spec hb R).2.2.2

lemma card_elementsInSubgroup_of_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (hAH : (A : Set G) ⊆ H) :
    (elementsInSubgroup H A).card = A.card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  have himage : (elementsInSubgroup H A).image (fun h : H => h.1) = A := by
    ext x
    simp only [Finset.mem_image, mem_elementsInSubgroup]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hx
      exact ⟨⟨x, hAH hx⟩, hx, rfl⟩
  calc
    (elementsInSubgroup H A).card =
        ((elementsInSubgroup H A).image (fun h : H => h.1)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := by rw [himage]

/-- The remaining residue set injects into its closure, so the defining
modulus times the number of remaining residues is at most `b`. -/
lemma closureModulus_mul_card_le {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : closureModulus hb R * R.card ≤ b := by
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  have hRcard : R.card ≤ Fintype.card H := by
    rw [← card_elementsInSubgroup_of_subset H R
      (fun _ hx => AddSubgroup.subset_closure hx)]
    exact Finset.card_le_univ _
  have hHcard : Fintype.card H = b / closureModulus hb R := by
    rw [show Fintype.card H = (H : Set (ZMod b)).ncard by
      exact Set.fintypeCard_eq_ncard (H : Set (ZMod b))]
    exact ncard_closure_eq_div_modulus hb R
  rw [hHcard] at hRcard
  calc
    closureModulus hb R * R.card ≤
        closureModulus hb R * (b / closureModulus hb R) :=
      Nat.mul_le_mul_left _ hRcard
    _ = b := Nat.mul_div_cancel' (closureModulus_dvd hb R)

/-- Shrinking the remaining set can only enlarge its cyclic modulus. -/
lemma closureModulus_dvd_of_subset {b : ℕ} [NeZero b] (hb : 0 < b)
    {R T : Finset (ZMod b)} (hTR : T ⊆ R) :
    closureModulus hb R ∣ closureModulus hb T := by
  let q := closureModulus hb R
  let r := closureModulus hb T
  have hrb : r ∣ b := closureModulus_dvd hb T
  have hrle : r ≤ b := Nat.le_of_dvd hb hrb
  by_cases hrEq : r = b
  · change q ∣ r
    rw [hrEq]
    exact closureModulus_dvd hb R
  · have hrlt : r < b := lt_of_le_of_ne hrle hrEq
    have hmemT : (r : ZMod b) ∈ AddSubgroup.closure (T : Set (ZMod b)) := by
      have := (closureModulus_spec hb T).2.2.2 1
      simpa [r] using this
    have hmemR : (r : ZMod b) ∈ AddSubgroup.closure (R : Set (ZMod b)) := by
      apply AddSubgroup.closure_mono (by exact_mod_cast hTR)
      exact hmemT
    have hqval := (closureModulus_spec hb R).2.2.1 (r : ZMod b) hmemR
    simpa [q, r, ZMod.val_natCast, Nat.mod_eq_of_lt hrlt] using hqval

/-- Divisor diversity in an original residue set implies that, after a
remaining set `R` has been set aside, the already-used elements represent
every coset of the subgroup generated by `R`.  Adding any nonempty seed
therefore makes every normalized subgroup fibre nonempty. -/
lemma normalizedCosetFiber_nonempty_of_diverse_used
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    ∀ u : ZMod b,
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + (R₀ \ R).subsetSum) u).Nonempty := by
  classical
  let q := closureModulus hb R
  have hq : 0 < q := closureModulus_pos hb R
  letI : NeZero q := ⟨hq.ne'⟩
  let U := R₀ \ R
  let f : ZMod b →+ ZMod q :=
    (ZMod.castHom (closureModulus_dvd hb R) (ZMod q)).toAddMonoidHom
  have hUdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ ((U.toList.map fun x : ZMod b => x.val).filter
        fun a => ¬d ∣ a).length := by
    intro d hd hdq
    have hnonmult : R₀.filter (fun x => ¬d ∣ x.val) ⊆
        U.filter (fun x => ¬d ∣ x.val) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      refine ⟨?_, hx.2⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hx.1, ?_⟩
      intro hxR
      have hqval : q ∣ x.val :=
        (closureModulus_spec hb R).2.2.1 x
          (AddSubgroup.subset_closure hxR)
      exact hx.2 (hdq.trans hqval)
    have hcard := Finset.card_le_card hnonmult
    have hlen : ((U.toList.map fun x : ZMod b => x.val).filter
        fun a => ¬d ∣ a).length =
        (U.filter fun x => ¬d ∣ x.val).card := by
      rw [List.filter_map]
      rw [List.length_map]
      rw [← List.toFinset_card_of_nodup (U.nodup_toList.filter _)]
      rw [List.toFinset_filter]
      simp [Function.comp_def]
    rw [hlen]
    exact (hdiverse d hd (by simpa [q] using hdq)).trans hcard
  have hallVal : Erdos587.listSubsetSums
      ((U.toList.map fun x : ZMod b => x.val).map
        fun a : ℕ => (a : ZMod q)) = Finset.univ :=
    listSubsetSums_mod_eq_univ_of_divisor_diverse hq _ hUdiverse
  have hmap : U.toList.map f =
      (U.toList.map fun x : ZMod b => x.val).map
        fun a : ℕ => (a : ZMod q) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp [f, ZMod.castHom_apply]
  have hall : (U.subsetSum.image f) = Finset.univ := by
    rw [← listSubsetSums_toList_eq_subsetSum]
    rw [image_listSubsetSums_map, hmap, hallVal]
  intro u
  obtain ⟨e, he⟩ := hE
  have htarget : f (u - e) ∈ U.subsetSum.image f := by
    rw [hall]
    simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp htarget
  let H := AddSubgroup.closure (R : Set (ZMod b))
  have hker : e + t - u ∈ H := by
    apply (mem_closure_iff_modulus_dvd_val hb R (e + t - u)).2
    apply (zmod_castHom_eq_zero_iff_val_dvd
      (closureModulus_dvd hb R) (e + t - u)).mp
    change f (e + t - u) = 0
    rw [map_sub, map_add, hft]
    simp [map_sub]
  refine ⟨⟨e + t - u, hker⟩, ?_⟩
  rw [mem_normalizedCosetFiber]
  rw [Finset.mem_add]
  refine ⟨e, he, t, ht, ?_⟩
  simp [sub_eq_add_neg]

/-- If every coset of a nonzero finite subgroup is occupied and every fibre
contains at least one quarter of that subgroup, then the whole set occupies
at least one quarter of the ambient group. -/
lemma card_le_four_mul_card_of_all_coset_fibers_large
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G)
    (hlarge : ∀ u : G,
      (H : Set G).ncard ≤ 4 * (normalizedCosetFiber H S u).card) :
    Fintype.card G ≤ 4 * S.card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  let I : Finset (Σ _u : G, H) :=
    (Finset.univ : Finset G).sigma fun u => normalizedCosetFiber H S u
  let J : Finset (G × H) := S ×ˢ (Finset.univ : Finset H)
  have hIJ : I.card = J.card := by
    apply Finset.card_bij'
        (fun p _ => (p.1 + p.2.1, p.2))
        (fun p _ => ⟨p.1 - p.2.1, p.2⟩)
    · rintro ⟨u, h⟩ hp
      simp [sub_eq_add_neg]
    · rintro ⟨s, h⟩ hp
      simp [sub_eq_add_neg]
    · intro p hp
      dsimp only [J]
      rw [Finset.mem_product]
      dsimp only [I] at hp
      have hpFiber := (Finset.mem_sigma.mp hp).2
      exact ⟨mem_normalizedCosetFiber.mp hpFiber, Finset.mem_univ _⟩
    · intro p hp
      dsimp only [I]
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_normalizedCosetFiber]
      dsimp only [J] at hp
      rw [Finset.mem_product] at hp
      simpa [sub_eq_add_neg] using hp.1
  have hsum : Fintype.card G * (H : Set G).ncard ≤ 4 * I.card := by
    calc
      Fintype.card G * (H : Set G).ncard =
          ∑ _u : G, (H : Set G).ncard := by simp
      _ ≤ ∑ u : G, 4 * (normalizedCosetFiber H S u).card := by
        exact Finset.sum_le_sum fun u _ => hlarge u
      _ = 4 * I.card := by
        simp only [I, Finset.card_sigma]
        simp [Finset.mul_sum]
  have hHcard : (H : Set G).ncard = Fintype.card H := by
    exact (Set.fintypeCard_eq_ncard (H : Set G)).symm
  have hHpos : 0 < (H : Set G).ncard := by
    rw [hHcard]
    exact Fintype.card_pos
  have hIcard : I.card = S.card * (H : Set G).ncard := by
    simp only [hIJ, J, Finset.card_product, Finset.card_univ, hHcard]
  rw [hIcard] at hsum
  have hmul : Fintype.card G * (H : Set G).ncard ≤
      (4 * S.card) * (H : Set G).ncard := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  exact Nat.le_of_mul_le_mul_right hmul hHpos

/-- The modular subset-sum set after adjoining one unused element is the
old set together with one translate. -/
lemma seededSubsetSum_insert_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (E A : Finset G) (x : G) (hx : x ∉ A) :
    E + (insert x A).subsetSum =
      (E + A.subsetSum) ∪
        Erdos587.addTranslate x (E + A.subsetSum) := by
  rw [subsetSum_insert_eq A x hx, Finset.add_union]
  congr 1
  ext z
  constructor
  · intro hz
    obtain ⟨e, he, t, ht, hzt⟩ := Finset.mem_add.mp hz
    rw [Erdos587.mem_addTranslate]
    apply Finset.mem_add.mpr
    refine ⟨e, he, -x + t, ?_, ?_⟩
    · exact Erdos587.mem_addTranslate.mp ht
    · calc
        e + (-x + t) = -x + (e + t) := by abel
        _ = -x + z := by rw [hzt]
  · intro hz
    rw [Erdos587.mem_addTranslate] at hz
    obtain ⟨e, he, t, ht, hzt⟩ := Finset.mem_add.mp hz
    apply Finset.mem_add.mpr
    refine ⟨e, he, x + t, ?_, ?_⟩
    · rw [Erdos587.mem_addTranslate]
      simpa using ht
    · calc
        e + (x + t) = x + (e + t) := by abel
        _ = x + (-x + z) := by rw [hzt]
        _ = z := by abel

lemma sdiff_erase_eq_insert_sdiff
    {α : Type*} [DecidableEq α] {R₀ R : Finset α} {x : α}
    (hxR : x ∈ R) (hR : R ⊆ R₀) :
    R₀ \ R.erase x = insert x (R₀ \ R) := by
  ext y
  by_cases hyx : y = x
  · subst y
    simp [hxR, hR hxR]
  · simp [hyx]

/-- A growth phase is witnessed by a coset fibre no larger than one quarter
of the remaining residue set. -/
def IsModularGrowthPhase {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) : Prop :=
  ∃ u : ZMod b,
    4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) u).card ≤ R.card

/-- An unsaturated fibre has less than one quarter of its subgroup. -/
def HasUnsaturatedFiber {b : ℕ} [NeZero b] (R₀ R E : Finset (ZMod b)) :
    Prop :=
  ∃ u : ZMod b,
    4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) u).card <
        (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard

lemma exists_internal_growth_of_modularGrowthPhase
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hRne : R.Nonempty) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hgrowth : IsModularGrowthPhase hb R₀ R E) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    ∃ x : H, x.1 ∈ R ∧
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X := liftFinsetToClosure R
  obtain ⟨u, huSmall⟩ := hgrowth
  have huNe := normalizedCosetFiber_nonempty_of_diverse_used
    hb R₀ R E hE hdiverse u
  have hTle : T.card ≤ (normalizedCosetFiber H
      (E + (R₀ \ R).subsetSum) u).card := by
    exact seededSubsetSum_fiber_lower H E (R₀ \ R) u huNe
  have hTne : T.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp only [T]
    rw [Finset.mem_subsetSum_iff]
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  have hXne : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hRne
  have hsmall : 2 * T.card < X.card := by
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    have : 4 * T.card ≤ R.card :=
      (Nat.mul_le_mul_left 4 hTle).trans huSmall
    omega
  obtain ⟨x, hx, hxGrowth⟩ := exists_three_halves_growth hTne hXne hsmall
  exact ⟨x, mem_liftFinsetToClosure.mp hx, hxGrowth⟩

lemma exists_large_step_of_unsaturatedFiber
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hRne : R.Nonempty) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hnotGrowth : ¬IsModularGrowthPhase hb R₀ R E)
    (hunsat : HasUnsaturatedFiber R₀ R E) :
    ∃ x ∈ R, R.card ≤ 16 *
      (Erdos360.translationNew (E + (R₀ \ R).subsetSum) x).card := by
  classical
  obtain ⟨u, huSmall⟩ := hunsat
  have huNe := normalizedCosetFiber_nonempty_of_diverse_used
    hb R₀ R E hE hdiverse u
  have hlarge : R.card < 4 *
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + (R₀ \ R).subsetSum) u).card := by
    by_contra hnot
    apply hnotGrowth
    exact ⟨u, by omega⟩
  exact exists_translationNew_large_of_normalizedCosetFiber
    huNe hRne hlarge huSmall

lemma saturated_modularPhase_card
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hsaturated : ¬HasUnsaturatedFiber R₀ R E) :
    b ≤ 4 * (E + (R₀ \ R).subsetSum).card := by
  have hlarge : ∀ u : ZMod b,
      (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard ≤
        4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
          (E + (R₀ \ R).subsetSum) u).card := by
    intro u
    have huNe := normalizedCosetFiber_nonempty_of_diverse_used
      hb R₀ R E hE hdiverse u
    by_contra hnot
    apply hsaturated
    exact ⟨u, by omega⟩
  simpa [ZMod.card] using
    (card_le_four_mul_card_of_all_coset_fibers_large
      (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) hlarge)

/-! ### The deterministic modular phase recursion -/

/-- Diversity only where it can be used by a phase whose remainder still
contains at least half of the original residues. -/
def PhaseDiverse {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ : Finset (ZMod b)) : Prop :=
  ∀ R : Finset (ZMod b), R₀.card ≤ 2 * R.card →
    ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card

lemma phaseDiverse_of_bounded
    {b : ℕ} [NeZero b] (hb : 0 < b) (R₀ : Finset (ZMod b))
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d * R₀.card ≤ 2 * b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    PhaseDiverse hb R₀ := by
  intro R hwide d hd hdq
  apply hdiverse d hd (hdq.trans (closureModulus_dvd hb R))
  have hdle : d ≤ closureModulus hb R :=
    Nat.le_of_dvd (closureModulus_pos hb R) hdq
  have hclosure := closureModulus_mul_card_le hb R
  nlinarith

/-- A canonical choice for the next phase.  In a growth phase it uses the
internal multiplicative-growth witness; in an unsaturated phase it uses the
large-translation witness; otherwise it removes an arbitrary remaining
element. -/
noncomputable def modularPhasePick
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hR : R.Nonempty
  · by_cases hwide : R₀.card ≤ 2 * R.card
    · by_cases hg : IsModularGrowthPhase hb R₀ R E
      · exact (Classical.choose
          (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
            (hdiverse R hwide) hg)).1
      · by_cases hu : HasUnsaturatedFiber R₀ R E
        · exact Classical.choose
            (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
              (hdiverse R hwide) hg hu)
        · exact hR.choose
    · exact hR.choose
  · exact 0

lemma modularPhasePick_mem
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty) :
    modularPhasePick hb R₀ E hE hdiverse R ∈ R := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR]
  by_cases hwide : R₀.card ≤ 2 * R.card
  · rw [dif_pos hwide]
    by_cases hg : IsModularGrowthPhase hb R₀ R E
    · rw [dif_pos hg]
      exact (Classical.choose_spec
          (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
            (hdiverse R hwide) hg)).1
    · rw [dif_neg hg]
      by_cases hu : HasUnsaturatedFiber R₀ R E
      · rw [dif_pos hu]
        exact (Classical.choose_spec
          (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
            (hdiverse R hwide) hg hu)).1
      · rw [dif_neg hu]
        exact hR.choose_spec
  · rw [dif_neg hwide]
    exact hR.choose_spec

lemma modularPhasePick_internal_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hwide : R₀.card ≤ 2 * R.card)
    (hg : IsModularGrowthPhase hb R₀ R E) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    3 * T.card ≤ 2 *
      (T ∪ Erdos587.addTranslate
        (⟨modularPhasePick hb R₀ E hE hdiverse R,
          AddSubgroup.subset_closure
            (modularPhasePick_mem hb R₀ E hE hdiverse R hR)⟩ : H) T).card := by
  classical
  dsimp only
  let hex := exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
    (hdiverse R hwide) hg
  let x := Classical.choose hex
  have hxSpec := (Classical.choose_spec hex).2
  have hpick : modularPhasePick hb R₀ E hE hdiverse R = x.1 := by
    simp only [modularPhasePick, dif_pos hR, dif_pos hwide, dif_pos hg, hex, x]
  have hsubtype :
      (⟨modularPhasePick hb R₀ E hE hdiverse R,
        AddSubgroup.subset_closure
          (modularPhasePick_mem hb R₀ E hE hdiverse R hR)⟩ :
          AddSubgroup.closure (R : Set (ZMod b))) = x := by
    exact Subtype.ext hpick
  rw [hsubtype]
  exact hxSpec

lemma modularPhasePick_unsaturated_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hwide : R₀.card ≤ 2 * R.card)
    (hg : ¬IsModularGrowthPhase hb R₀ R E)
    (hu : HasUnsaturatedFiber R₀ R E) :
    R.card ≤ 16 * (Erdos360.translationNew
      (E + (R₀ \ R).subsetSum)
      (modularPhasePick hb R₀ E hE hdiverse R)).card := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR, dif_pos hwide, dif_neg hg, dif_pos hu]
  exact (Classical.choose_spec
    (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
      (hdiverse R hwide) hg hu)).2

noncomputable def modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    ℕ → Finset (ZMod b)
  | 0 => R₀
  | i + 1 =>
      let R := modularRemainder hb R₀ E hE hdiverse i
      if R.Nonempty then
        R.erase (modularPhasePick hb R₀ E hE hdiverse R)
      else R

noncomputable def modularPhaseSums
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) : Finset (ZMod b) :=
  E + (R₀ \ modularRemainder hb R₀ E hE hdiverse i).subsetSum

@[simp] lemma modularRemainder_zero
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    modularRemainder hb R₀ E hE hdiverse 0 = R₀ := rfl

lemma modularRemainder_succ_of_nonempty
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) (hne : (modularRemainder hb R₀ E hE hdiverse i).Nonempty) :
    modularRemainder hb R₀ E hE hdiverse (i + 1) =
      (modularRemainder hb R₀ E hE hdiverse i).erase
        (modularPhasePick hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse i)) := by
  change (if (modularRemainder hb R₀ E hE hdiverse i).Nonempty then
      (modularRemainder hb R₀ E hE hdiverse i).erase
        (modularPhasePick hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse i))
    else modularRemainder hb R₀ E hE hdiverse i) = _
  rw [if_pos hne]

lemma modularRemainder_succ_subset
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    modularRemainder hb R₀ E hE hdiverse (i + 1) ⊆
      modularRemainder hb R₀ E hE hdiverse i := by
  let R := modularRemainder hb R₀ E hE hdiverse i
  change (if R.Nonempty then
      R.erase (modularPhasePick hb R₀ E hE hdiverse R) else R) ⊆ R
  split_ifs
  · exact Finset.erase_subset _ _
  · exact fun _ hx => hx

lemma modularRemainder_subset_initial
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    ∀ i : ℕ, modularRemainder hb R₀ E hE hdiverse i ⊆ R₀ := by
  intro i
  induction i with
  | zero => exact fun _ hx => hx
  | succ i ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse i).trans ih

lemma card_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (modularRemainder hb R₀ E hE hdiverse i).card = R₀.card - i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i ≤ R₀.card := by omega
      have hcard := ih hi'
      have hne : (modularRemainder hb R₀ E hE hdiverse i).Nonempty := by
        apply Finset.card_pos.mp
        rw [hcard]
        omega
      rw [modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hne]
      rw [Finset.card_erase_of_mem
        (modularPhasePick_mem hb R₀ E hE hdiverse _ hne)]
      omega

lemma card_used_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (R₀ \ modularRemainder hb R₀ E hE hdiverse i).card = i := by
  rw [Finset.card_sdiff_of_subset
    (modularRemainder_subset_initial hb R₀ E hE hdiverse i)]
  rw [card_modularRemainder hb R₀ E hE hdiverse hi]
  omega

lemma modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card) :
    modularPhaseSums hb R₀ E hE hdiverse (i + 1) =
      modularPhaseSums hb R₀ E hE hdiverse i ∪
        Erdos587.addTranslate
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))
          (modularPhaseSums hb R₀ E hE hdiverse i) := by
  let R := modularRemainder hb R₀ E hE hdiverse i
  have hcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hRsub : R ⊆ R₀ :=
    modularRemainder_subset_initial hb R₀ E hE hdiverse i
  have hxR := modularPhasePick_mem hb R₀ E hE hdiverse R hRne
  have hxNot : modularPhasePick hb R₀ E hE hdiverse R ∉ R₀ \ R := by
    simp only [Finset.mem_sdiff]
    exact fun h => h.2 hxR
  rw [modularPhaseSums, modularPhaseSums]
  rw [modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hRne]
  rw [sdiff_erase_eq_insert_sdiff hxR hRsub]
  exact seededSubsetSum_insert_eq E (R₀ \ R)
    (modularPhasePick hb R₀ E hE hdiverse R) hxNot

/-- The numerical size of the subset sums made from already-used elements
which lie in the subgroup generated by the current remainder. -/
noncomputable def modularInternalCard
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) : ℕ :=
  let H := AddSubgroup.closure (R : Set (ZMod b))
  (elementsInSubgroup H (R₀ \ R)).subsetSum.card

lemma elementsInSubgroup_mono
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) {A B : Finset G} (hAB : A ⊆ B) :
    elementsInSubgroup H A ⊆ elementsInSubgroup H B := by
  intro x hx
  rw [mem_elementsInSubgroup] at hx ⊢
  exact hAB hx

lemma modularInternalCard_mono_of_subset_of_closure_eq
    {b : ℕ} [NeZero b] (R₀ : Finset (ZMod b))
    {R T : Finset (ZMod b)} (hTR : T ⊆ R)
    (hclosure : AddSubgroup.closure (T : Set (ZMod b)) =
      AddSubgroup.closure (R : Set (ZMod b))) :
    modularInternalCard R₀ R ≤ modularInternalCard R₀ T := by
  classical
  let HR := AddSubgroup.closure (R : Set (ZMod b))
  let HT := AddSubgroup.closure (T : Set (ZMod b))
  have hused : R₀ \ R ⊆ R₀ \ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun hxT => hx.2 (hTR hxT)⟩
  have hsub : elementsInSubgroup HR (R₀ \ R) ⊆
      elementsInSubgroup HR (R₀ \ T) :=
    elementsInSubgroup_mono HR hused
  have hsums := Finset.subsetSum_mono hsub
  have hcard := Finset.card_le_card hsums
  dsimp only [modularInternalCard]
  rw [hclosure]
  exact hcard

lemma closure_eq_of_closureModulus_eq
    {b : ℕ} [NeZero b] (hb : 0 < b) {R T : Finset (ZMod b)}
    (hmod : closureModulus hb R = closureModulus hb T) :
    AddSubgroup.closure (R : Set (ZMod b)) =
      AddSubgroup.closure (T : Set (ZMod b)) := by
  rw [closure_eq_zmultiples_modulus hb R,
    closure_eq_zmultiples_modulus hb T, hmod]

lemma modularRemainder_antitone
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j) :
    modularRemainder hb R₀ E hE hdiverse j ⊆
      modularRemainder hb R₀ E hE hdiverse i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse (i + k)).trans
        (ih (by omega))

lemma modularInternalCard_mono_of_modulus_eq
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j)
    (hmod : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse j)) :
    modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse i) ≤
      modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse j) := by
  apply modularInternalCard_mono_of_subset_of_closure_eq R₀
    (modularRemainder_antitone hb R₀ E hE hdiverse hij)
  exact (closure_eq_of_closureModulus_eq hb hmod).symm

lemma elementsInSubgroup_insert
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (x : H) (hx : x.1 ∉ A) :
    elementsInSubgroup H (insert x.1 A) =
      insert x (elementsInSubgroup H A) := by
  ext y
  simp only [mem_elementsInSubgroup, Finset.mem_insert, Subtype.coe_inj]

lemma modularInternalCard_growth_step
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card)
    (hwide : R₀.card ≤ 2 *
      (modularRemainder hb R₀ E hE hdiverse i).card)
    (hg : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E)
    (hmod : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse (i + 1))) :
    3 * modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse i) ≤
      2 * modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
  classical
  let R := modularRemainder hb R₀ E hE hdiverse i
  let T := modularRemainder hb R₀ E hE hdiverse (i + 1)
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := R₀ \ R
  let x := modularPhasePick hb R₀ E hE hdiverse R
  have hRcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hxR : x ∈ R := modularPhasePick_mem hb R₀ E hE hdiverse R hRne
  have hxU : x ∉ U := by
    simp only [U, Finset.mem_sdiff]
    exact fun h => h.2 hxR
  have hT : T = R.erase x := by
    exact modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hRne
  have hused : R₀ \ T = insert x U := by
    rw [hT]
    exact sdiff_erase_eq_insert_sdiff hxR
      (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
  let xH : H := ⟨x, AddSubgroup.subset_closure hxR⟩
  have hgrowth := modularPhasePick_internal_growth
    hb R₀ E hE hdiverse R hRne hwide hg
  have hclosure : AddSubgroup.closure (T : Set (ZMod b)) = H := by
    exact (closure_eq_of_closureModulus_eq hb hmod).symm
  have hnext : elementsInSubgroup H (R₀ \ T) =
      insert xH (elementsInSubgroup H U) := by
    rw [hused]
    exact elementsInSubgroup_insert H U xH hxU
  have hsumNext : (elementsInSubgroup H (R₀ \ T)).subsetSum =
      (elementsInSubgroup H U).subsetSum ∪
        Erdos587.addTranslate xH (elementsInSubgroup H U).subsetSum := by
    rw [hnext]
    exact subsetSum_insert_eq _ _ (by
      rw [mem_elementsInSubgroup]
      exact hxU)
  dsimp only [modularInternalCard]
  rw [show AddSubgroup.closure (T : Set (ZMod b)) = H by exact hclosure]
  rw [hsumNext]
  exact hgrowth

lemma log_two_lt_of_double_le {a c : ℕ} (ha : 0 < a)
    (hac : 2 * a ≤ c) : Nat.log 2 a < Nat.log 2 c := by
  have hstep : Nat.log 2 a < Nat.log 2 (a * 2) := by
    rw [Nat.log_mul_base (by omega) ha.ne']
    omega
  exact hstep.trans_le (Nat.log_mono_right (by simpa [mul_comm] using hac))

lemma eq_of_dvd_of_log_two_eq {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hac : a ∣ c) (hlog : Nat.log 2 a = Nat.log 2 c) : a = c := by
  obtain ⟨r, rfl⟩ := hac
  have hr : 0 < r := by
    by_contra h
    have : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    simp at hc
  by_contra hne
  have hrne : r ≠ 1 := by
    intro hrone
    subst r
    simp at hne
  have hr2 : 2 ≤ r := by
    omega
  have hdouble : 2 * a ≤ a * r := by
    nlinarith
  exact (Nat.ne_of_lt (log_two_lt_of_double_le ha hdouble)) hlog

lemma modularInternalCard_pos
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) :
    0 < modularInternalCard R₀ R := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨0, Finset.zero_mem_subsetSum⟩

lemma modularInternalCard_le
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) :
    modularInternalCard R₀ R ≤ b := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  calc
    modularInternalCard R₀ R =
        (elementsInSubgroup H (R₀ \ R)).subsetSum.card := rfl
    _ ≤ Fintype.card H := Finset.card_le_univ _
    _ ≤ Fintype.card (ZMod b) :=
      Fintype.card_le_of_injective (fun h : H => h.1) Subtype.val_injective
    _ = b := ZMod.card b

lemma closureModulus_eq_between
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i t j : ℕ} (hit : i ≤ t) (htj : t ≤ j)
    (hij : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse j)) :
    closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse t) := by
  apply Nat.dvd_antisymm
  · exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hit)
  · rw [hij]
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse htj)

/-- The phase indices at which the selector invokes the internal
multiplicative-growth alternative. -/
noncomputable def modularGrowthIndices
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i =>
    IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E

/-- Binary logarithms of the current subgroup modulus and its internal
subset-sum cardinality.  Both coordinates lie between zero and `log₂ b`. -/
noncomputable def modularGrowthCode
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) : Fin (Nat.log 2 b + 1) × Fin (Nat.log 2 b + 1) :=
  (⟨Nat.log 2 (closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse i)), by
      have hle : closureModulus hb
          (modularRemainder hb R₀ E hE hdiverse i) ≤ b :=
        Nat.le_of_dvd hb (closureModulus_dvd hb _)
      exact Nat.lt_succ_of_le (Nat.log_mono_right hle)⟩,
   ⟨Nat.log 2 (modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse i)), by
      exact Nat.lt_succ_of_le (Nat.log_mono_right
        (modularInternalCard_le R₀ _))⟩)

lemma exists_three_ordered_of_two_lt_card {S : Finset ℕ}
    (hS : 2 < S.card) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i < j ∧ j < k := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hS
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨a, ha, b, hb, c, hc, hab', hbc'⟩
      · exact ⟨a, ha, c, hc, b, hb, hac', hcb'⟩
    · exact ⟨c, hc, a, ha, b, hb, hca', hab'⟩
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · exact ⟨b, hb, a, ha, c, hc, hba', hac'⟩
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨b, hb, c, hc, a, ha, hbc', hca'⟩
      · exact ⟨c, hc, b, hb, a, ha, hcb', hba'⟩

lemma modularGrowthCode_not_three
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hk : 2 * (k + 1) ≤ R₀.card)
    (hgi : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E)
    (hgj : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse j) E)
    (hcodeIJ : modularGrowthCode hb R₀ E hE hdiverse i =
      modularGrowthCode hb R₀ E hE hdiverse j)
    (hcodeJK : modularGrowthCode hb R₀ E hE hdiverse j =
      modularGrowthCode hb R₀ E hE hdiverse k) : False := by
  let Ri := modularRemainder hb R₀ E hE hdiverse i
  let Rj := modularRemainder hb R₀ E hE hdiverse j
  let Rk := modularRemainder hb R₀ E hE hdiverse k
  let qi := closureModulus hb Ri
  let qj := closureModulus hb Rj
  let qk := closureModulus hb Rk
  let ci := modularInternalCard R₀ Ri
  let cj := modularInternalCard R₀ Rj
  let ck := modularInternalCard R₀ Rk
  have hqLogIJ : Nat.log 2 qi = Nat.log 2 qj :=
    congrArg (fun z => z.1.val) hcodeIJ
  have hqLogJK : Nat.log 2 qj = Nat.log 2 qk :=
    congrArg (fun z => z.1.val) hcodeJK
  have hcLogIJ : Nat.log 2 ci = Nat.log 2 cj :=
    congrArg (fun z => z.2.val) hcodeIJ
  have hcLogJK : Nat.log 2 cj = Nat.log 2 ck :=
    congrArg (fun z => z.2.val) hcodeJK
  have hqDivIJ : qi ∣ qj := by
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hij.le)
  have hqDivJK : qj ∣ qk := by
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hjk.le)
  have hqEqIJ : qi = qj :=
    eq_of_dvd_of_log_two_eq (closureModulus_pos hb Ri)
      (closureModulus_pos hb Rj) hqDivIJ hqLogIJ
  have hqEqJK : qj = qk :=
    eq_of_dvd_of_log_two_eq (closureModulus_pos hb Rj)
      (closureModulus_pos hb Rk) hqDivJK hqLogJK
  have hqiSucc : closureModulus hb Ri = closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqIJ
  have hqjSucc : closureModulus hb Rj = closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqJK
  have hgrowI : 3 * ci ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) (by
        rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
        omega) hgi hqiSucc
  have hmonoIJ : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) ≤ cj := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqiSucc.symm.trans hqEqIJ
  have hgrowJ : 3 * cj ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) (by
        rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
        omega) hgj hqjSucc
  have hmonoJK : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) ≤ ck := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqjSucc.symm.trans hqEqJK
  have hthreeI : 3 * ci ≤ 2 * cj := hgrowI.trans (Nat.mul_le_mul_left 2 hmonoIJ)
  have hthreeJ : 3 * cj ≤ 2 * ck := hgrowJ.trans (Nat.mul_le_mul_left 2 hmonoJK)
  have hdouble : 2 * ci ≤ ck := by
    have hcipos : 0 < ci := modularInternalCard_pos R₀ Ri
    omega
  have hloglt : Nat.log 2 ci < Nat.log 2 ck :=
    log_two_lt_of_double_le (modularInternalCard_pos R₀ Ri) hdouble
  exact (Nat.ne_of_lt hloglt) (hcLogIJ.trans hcLogJK)

theorem card_modularGrowthIndices_le
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card) :
    (modularGrowthIndices hb R₀ E hE hdiverse k).card ≤
      2 * (Nat.log 2 b + 1) ^ 2 := by
  classical
  let G := modularGrowthIndices hb R₀ E hE hdiverse k
  let C := Fin (Nat.log 2 b + 1) × Fin (Nat.log 2 b + 1)
  let f : ℕ → C := modularGrowthCode hb R₀ E hE hdiverse
  by_contra hnot
  have hlarge : (Finset.univ : Finset C).card * 2 < G.card := by
    simp only [Finset.card_univ, C, Fintype.card_prod, Fintype.card_fin]
    dsimp only [G] at hnot ⊢
    have hgt : 2 * (Nat.log 2 b + 1) ^ 2 <
        (modularGrowthIndices hb R₀ E hE hdiverse k).card :=
      Nat.lt_of_not_ge hnot
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hgt
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G) (t := Finset.univ) (f := f)
      (n := 2) (fun _ _ => Finset.mem_univ _) hlarge
  let S := G.filter fun i => f i = y
  have hScard : 2 < S.card := by
    simpa only [S] using hy
  obtain ⟨i, hiS, j, hjS, q, hqS, hij, hjq⟩ :=
    exists_three_ordered_of_two_lt_card hScard
  have hiG : i ∈ G := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ G := (Finset.mem_filter.mp hjS).1
  have hqG : q ∈ G := (Finset.mem_filter.mp hqS).1
  have hfi : f i = y := (Finset.mem_filter.mp hiS).2
  have hfj : f j = y := (Finset.mem_filter.mp hjS).2
  have hfq : f q = y := (Finset.mem_filter.mp hqS).2
  have hiData := Finset.mem_filter.mp hiG
  have hjData := Finset.mem_filter.mp hjG
  have hqData := Finset.mem_filter.mp hqG
  exact modularGrowthCode_not_three hb R₀ E hE hdiverse hij hjq
    (by
      have hqk : q < k := Finset.mem_range.mp hqData.1
      omega)
    hiData.2 hjData.2 (hfi.trans hfj.symm) (hfj.trans hfq.symm)

lemma card_union_addTranslate_eq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (x : G) :
    (S ∪ Erdos587.addTranslate x S).card =
      S.card + (Erdos360.translationNew S x).card := by
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x S) S
  dsimp only [Erdos360.translationNew] at hsdiff ⊢
  rw [Finset.union_comm] at hsdiff
  omega

lemma card_modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card) :
    (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card =
      (modularPhaseSums hb R₀ E hE hdiverse i).card +
        (Erdos360.translationNew
          (modularPhaseSums hb R₀ E hE hdiverse i)
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))).card := by
  rw [modularPhaseSums_succ hb R₀ E hE hdiverse hi]
  exact card_union_addTranslate_eq _ _

lemma card_modularGrowthIndices_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse (i + 1)).card =
      if IsModularGrowthPhase hb R₀
          (modularRemainder hb R₀ E hE hdiverse i) E then
        (modularGrowthIndices hb R₀ E hE hdiverse i).card + 1
      else (modularGrowthIndices hb R₀ E hE hdiverse i).card := by
  classical
  by_cases hg : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E <;>
    simp [modularGrowthIndices, Finset.range_add_one, Finset.filter_insert, hg]

lemma card_modularGrowthIndices_le_index
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse i).card ≤ i := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range i)

lemma mul_pred_potential_le (u r : ℕ) (hr : 0 < r) :
    (u + 1) * (r - 1) ≤ u * r + r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp only [Nat.succ_sub_one]
  nlinarith

/-- If no saturated phase occurs, every nongrowth phase contributes a
linear number of genuinely new residues.  This potential packages all those
increments while allowing the remainder to shrink. -/
theorem unsaturated_modularPhase_potential
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card)
    (hu : ∀ i < k, HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E) :
    (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
        (R₀.card - k) ≤
      16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < R₀.card := by omega
      have hkprev : k ≤ R₀.card := hklt.le
      have hhalfPrev : 2 * k ≤ R₀.card := by omega
      have huPrev : ∀ i < k, HasUnsaturatedFiber R₀
          (modularRemainder hb R₀ E hE hdiverse i) E := by
        intro i hi
        exact hu i (by omega)
      have hIH := ih hhalfPrev huPrev
      let R := modularRemainder hb R₀ E hE hdiverse k
      let S := modularPhaseSums hb R₀ E hE hdiverse k
      let x := modularPhasePick hb R₀ E hE hdiverse R
      let D := Erdos360.translationNew S x
      have hRcard : R.card = R₀.card - k :=
        card_modularRemainder hb R₀ E hE hdiverse hkprev
      have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
      have hwide : R₀.card ≤ 2 * R.card := by rw [hRcard]; omega
      have huK : HasUnsaturatedFiber R₀ R E := hu k (by omega)
      have hScard :
          (modularPhaseSums hb R₀ E hE hdiverse (k + 1)).card =
            S.card + D.card := by
        exact card_modularPhaseSums_succ hb R₀ E hE hdiverse hklt
      by_cases hg : IsModularGrowthPhase hb R₀ R E
      · have hGcard := card_modularGrowthIndices_succ
          hb R₀ E hE hdiverse k
        rw [if_pos hg] at hGcard
        rw [hGcard, hScard]
        have hGle := card_modularGrowthIndices_le_index
          hb R₀ E hE hdiverse k
        have hrem : R₀.card - (k + 1) ≤ R₀.card - k := by omega
        have hleft :
            (k + 1 - ((modularGrowthIndices hb R₀ E hE hdiverse k).card + 1)) *
                (R₀.card - (k + 1)) ≤
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
                (R₀.card - k) := by
          apply Nat.mul_le_mul
          · omega
          · exact hrem
        exact hleft.trans (hIH.trans (Nat.mul_le_mul_left 16
          (Nat.le_add_right S.card D.card)))
      · have hGcard := card_modularGrowthIndices_succ
          hb R₀ E hE hdiverse k
        rw [if_neg hg] at hGcard
        have hnew : R.card ≤ 16 * D.card := by
          exact modularPhasePick_unsaturated_growth
            hb R₀ E hE hdiverse R hRne hwide hg huK
        rw [hGcard, hScard]
        have hGle := card_modularGrowthIndices_le_index
          hb R₀ E hE hdiverse k
        have hremSucc : R₀.card - (k + 1) = (R₀.card - k) - 1 := by
          omega
        have hphaseSucc :
            k + 1 - (modularGrowthIndices hb R₀ E hE hdiverse k).card =
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) + 1 := by
          omega
        rw [hremSucc, hphaseSucc]
        calc
          ((k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) + 1) *
                ((R₀.card - k) - 1) ≤
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
                (R₀.card - k) + R.card := by
            rw [hRcard]
            exact mul_pred_potential_le _ _ (by omega)
          _ ≤ 16 * S.card + 16 * D.card := Nat.add_le_add hIH hnew
          _ = 16 * (S.card + D.card) := by ring

lemma modularPhaseSums_mono
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j) :
    modularPhaseSums hb R₀ E hE hdiverse i ⊆
      modularPhaseSums hb R₀ E hE hdiverse j := by
  rw [modularPhaseSums, modularPhaseSums]
  apply Finset.add_subset_add_left
  apply Finset.subsetSum_mono
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hx.1, ?_⟩
  intro hxj
  exact hx.2 (modularRemainder_antitone hb R₀ E hE hdiverse hij hxj)

/-- Exact output of the deterministic modular phase machine: either one
phase has already filled a quarter of the cyclic group, or the accumulated
unsaturated phases satisfy the quantitative potential bound. -/
theorem modularPhase_dichotomy
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
          (R₀.card - k) ≤
        16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  classical
  by_cases hu : ∀ i < k, HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E
  · exact Or.inr (unsaturated_modularPhase_potential
      hb R₀ E hE hdiverse hhalf hu)
  · push Not at hu
    obtain ⟨i, hi, hsat⟩ := hu
    left
    have hiCard : i ≤ R₀.card := by omega
    have hwide : R₀.card ≤ 2 *
        (modularRemainder hb R₀ E hE hdiverse i).card := by
      rw [card_modularRemainder hb R₀ E hE hdiverse hiCard]
      omega
    have hquarter := saturated_modularPhase_card hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E hE
      (hdiverse _ hwide) hsat
    exact hquarter.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card
      (modularPhaseSums_mono hb R₀ E hE hdiverse hi.le)))

/-- Bounded modular subset-sum growth with explicit, deliberately coarse
constants.  Once the number of exposed phases dominates the logarithmic
growth count and no more than half the residues have been used, either a
quarter of the group is filled or the sumset has quadratic-size growth. -/
theorem bounded_modular_subsetSum_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hlog : 4 * (Nat.log 2 b + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      k * R₀.card ≤
        64 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  have hk : k ≤ R₀.card := by omega
  rcases modularPhase_dichotomy hb R₀ E hE hdiverse hhalf with hfill | hpot
  · exact Or.inl hfill
  · right
    let g := (modularGrowthIndices hb R₀ E hE hdiverse k).card
    have hg := card_modularGrowthIndices_le hb R₀ E hE hdiverse hhalf
    have hgk : 2 * g ≤ k := by
      dsimp only [g]
      nlinarith
    have hg_le : g ≤ k := by omega
    have hkleft : k ≤ 2 * (k - g) := by omega
    have hmright : R₀.card ≤ 2 * (R₀.card - k) := by omega
    have hprod : k * R₀.card ≤
        4 * ((k - g) * (R₀.card - k)) := by
      calc
        k * R₀.card ≤ (2 * (k - g)) * (2 * (R₀.card - k)) :=
          Nat.mul_le_mul hkleft hmright
        _ = 4 * ((k - g) * (R₀.card - k)) := by ring
    calc
      k * R₀.card ≤ 4 * ((k - g) * (R₀.card - k)) := hprod
      _ ≤ 4 * (16 * (modularPhaseSums hb R₀ E hE hdiverse k).card) :=
        Nat.mul_le_mul_left 4 hpot
      _ = 64 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by ring

/-! ### Common-divisor extraction -/

noncomputable def divideMultiples (Y : Finset ℕ) (e : ℕ) : Finset ℕ :=
  (Y.filter fun y => e ∣ y).image fun y => y / e

lemma mem_divideMultiples_iff {Y : Finset ℕ} {e y : ℕ} (he : 0 < e) :
    y ∈ divideMultiples Y e ↔ e * y ∈ Y := by
  classical
  rw [divideMultiples, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    simpa [Nat.mul_div_cancel' hx.2] using hx.1
  · intro hy
    refine ⟨e * y, Finset.mem_filter.mpr ⟨hy, dvd_mul_right e y⟩, ?_⟩
    exact Nat.mul_div_right y he

lemma card_divideMultiples {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    (divideMultiples Y e).card = (Y.filter fun y => e ∣ y).card := by
  classical
  rw [divideMultiples, Finset.card_image_iff]
  intro x hx y hy hxy
  have hx' : x ∈ Y ∧ e ∣ x := Finset.mem_filter.mp hx
  have hy' : y ∈ Y ∧ e ∣ y := Finset.mem_filter.mp hy
  have hxmul : e * (x / e) = x := by
    simpa [mul_comm] using Nat.mul_div_cancel' hx'.2
  have hymul : e * (y / e) = y := by
    simpa [mul_comm] using Nat.mul_div_cancel' hy'.2
  change x / e = y / e at hxy
  rw [← hxmul, ← hymul]
  exact congrArg (fun z => e * z) hxy

lemma card_sub_card_divideMultiples {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    Y.card - (divideMultiples Y e).card =
      (Y.filter fun y => ¬e ∣ y).card := by
  rw [card_divideMultiples he]
  have hpartition : (Y.filter fun y => e ∣ y) ∪
      (Y.filter fun y => ¬e ∣ y) = Y := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint (Y.filter fun y => e ∣ y)
      (Y.filter fun y => ¬e ∣ y) := by
    rw [Finset.disjoint_left]
    intro y hy hny
    simp only [Finset.mem_filter] at hy hny
    exact hny.2 hy.2
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hpartition] at hcard
  omega

lemma divideMultiples_subset_Icc {Y : Finset ℕ} {e n : ℕ} (he : 0 < e)
    (hY : Y ⊆ Finset.Icc 1 n) :
    divideMultiples Y e ⊆ Finset.Icc 1 (n / e) := by
  intro y hy
  rw [mem_divideMultiples_iff he] at hy
  have hmem := Finset.mem_Icc.mp (hY hy)
  rw [Finset.mem_Icc]
  constructor
  · by_contra h
    have : y = 0 := Nat.eq_zero_of_not_pos h
    subst y
    simp at hmem
  · exact (Nat.le_div_iff_mul_le he).2 (by simpa [mul_comm] using hmem.2)

lemma divideMultiples_scaled_subset {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    ∀ y ∈ divideMultiples Y e, e * y ∈ Y := by
  intro y hy
  exact (mem_divideMultiples_iff he).mp hy

/-- Finite descent which repeatedly discards the exceptional nonmultiples
and divides by their common divisor.  The returned list records every
division, making the total loss auditable. -/
theorem exists_divisorExtractionAux
    (B L K d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧
      (∀ z ∈ Z, q * z ∈ Y) ∧
      Y.card - Z.card ≤ L * factors.length + K * factors.sum ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e ≤ (Z.filter fun z => ¬e ∣ z).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          (Y.filter fun y => ¬e ∣ y).card < L + K * e
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := divideMultiples Y e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, factors, hq, hqprod, hfactors, hdqB,
            hscale, hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' rfl
        refine ⟨e * q, Z, e :: factors, Nat.mul_pos hepos hq, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun h => h ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · intro z hz
          have hzY' : q * z ∈ Y' := hscale z hz
          have := divideMultiples_scaled_subset hepos (q * z) hzY'
          simpa [mul_assoc] using this
        · have hY'le : Y'.card ≤ Y.card := by
            dsimp only [Y']
            rw [card_divideMultiples hepos]
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have hZle : Z.card ≤ Y'.card := by
            apply Finset.card_le_card_of_injOn (fun z => q * z)
            · intro z hz
              exact hscale z hz
            · intro x hx y hy hxy
              exact Nat.eq_of_mul_eq_mul_left hq hxy
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          rw [hsplit]
          have hfirst : Y.card - Y'.card ≤ L + K * e := by
            dsimp only [Y']
            rw [card_sub_card_divideMultiples hepos]
            exact hsmall.le
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e) +
                  (L * factors.length + K * factors.sum) :=
              Nat.add_le_add hfirst hloss
            _ = L * (e :: factors).length + K * (e :: factors).sum := by
              simp only [List.length_cons, List.sum_cons]
              ring
        · intro a ha hbound
          convert hdiverse a ha (by simpa [mul_assoc] using hbound) using 1 <;>
            simp [mul_assoc]
      · refine ⟨1, Y, [], by omega, by simp, by simp, ?_, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using (Nat.lt_of_not_ge hnot)

lemma prod_pos_of_one_lt : ∀ factors : List ℕ,
    (∀ e ∈ factors, 1 < e) → 0 < factors.prod
  | [], _ => by simp
  | e :: factors, h => by
      simp only [List.prod_cons]
      exact Nat.mul_pos (by have := h e (by simp); omega)
        (prod_pos_of_one_lt factors (by
          intro a ha
          exact h a (by simp [ha])))

lemma sum_le_prod_of_one_lt : ∀ factors : List ℕ,
    (∀ e ∈ factors, 1 < e) → factors.sum ≤ factors.prod
  | [], _ => by simp
  | [e], h => by simp
  | e :: f :: factors, h => by
      have he : 2 ≤ e := h e (by simp)
      have htail : ∀ a ∈ f :: factors, 1 < a := by
        intro a ha
        exact h a (by simp [ha])
      have hfprod : 2 ≤ (f :: factors).prod := by
        have hf : 2 ≤ f := htail f (by simp)
        simp only [List.prod_cons]
        exact hf.trans (Nat.le_mul_of_pos_right f
          (prod_pos_of_one_lt factors (by
            intro a ha
            exact htail a (by simp [ha]))))
      have ih := sum_le_prod_of_one_lt (f :: factors) htail
      simp only [List.sum_cons, List.prod_cons]
      calc
        e + (f :: factors).sum ≤ e + (f :: factors).prod :=
          Nat.add_le_add_left ih e
        _ ≤ e * (f :: factors).prod := by nlinarith

lemma length_le_log_prod_of_one_lt (factors : List ℕ)
    (h : ∀ e ∈ factors, 1 < e) :
    factors.length ≤ Nat.log 2 factors.prod := by
  apply Nat.le_log_of_pow_le (by omega)
  induction factors with
  | nil => simp
  | cons e factors ih =>
      have he : 2 ≤ e := h e (by simp)
      have htail : ∀ a ∈ factors, 1 < a := by
        intro a ha
        exact h a (by simp [ha])
      simp only [List.length_cons, List.prod_cons, pow_succ]
      simpa [mul_comm] using Nat.mul_le_mul (ih htail) he

/-- Usable corollary of the descent: the output is diverse up to the global
divisor budget and loses only a logarithmic term plus a term linear in that
budget. -/
theorem exists_divisorExtraction
    (B L K : ℕ) (hB : 0 < B) (Y : Finset ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ℕ,
      0 < d ∧ d ≤ B ∧
      (∀ z ∈ Z, d * z ∈ Y) ∧
      Y.card - Z.card ≤ L * Nat.log 2 B + K * B ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun z => ¬e ∣ z).card := by
  obtain ⟨d, Z, factors, hd, hdprod, hfactors, hdB,
      hscale, hloss, hdiverse⟩ :=
    exists_divisorExtractionAux B L K 1 (by omega) hB Y
  refine ⟨d, Z, hd, by simpa using hdB, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤ L * factors.length + K * factors.sum := hloss
      _ ≤ L * Nat.log 2 B + K * B := by
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_left
          exact (length_le_log_prod_of_one_lt factors hfactors).trans
            (Nat.log_mono_right (by simpa [hdprod] using hdB))
        · apply Nat.mul_le_mul_left
          exact (sum_le_prod_of_one_lt factors hfactors).trans
            (by simpa [hdprod] using hdB)
  · intro e he hde
    exact hdiverse e he (by simpa using hde)

/-! The finite completion needs a lower pool whose elements are all smaller
than a reserved pivot pool.  The reserve required after division by `d` is
only `P / d`; charging that geometrically decreasing quantity during the
divisor descent avoids an erroneous extra logarithmic factor. -/

noncomputable def lowerPart (Y : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (Finset.range (Y.card - r)).attach.image fun i ↦
    Y.orderEmbOfFin rfl ⟨i.1, by
      have hi := Finset.mem_range.mp i.2
      omega⟩

lemma card_lowerPart (Y : Finset ℕ) (r : ℕ) :
    (lowerPart Y r).card = Y.card - r := by
  classical
  rw [lowerPart, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Subtype.ext
    have hij' :
        (⟨i.1, by
          have hi := Finset.mem_range.mp i.2
          omega⟩ : Fin Y.card) =
        ⟨j.1, by
          have hj := Finset.mem_range.mp j.2
          omega⟩ :=
      (Y.orderEmbOfFin rfl).injective hij
    exact congrArg Fin.val hij'

lemma lowerPart_subset (Y : Finset ℕ) (r : ℕ) : lowerPart Y r ⊆ Y := by
  classical
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  exact Y.orderEmbOfFin_mem rfl _

lemma card_sdiff_lowerPart (Y : Finset ℕ) (r : ℕ) :
    (Y \ lowerPart Y r).card = min r Y.card := by
  rw [Finset.card_sdiff_of_subset (lowerPart_subset Y r), card_lowerPart]
  omega

lemma card_sdiff_lowerPart_le (Y : Finset ℕ) (r : ℕ) :
    (Y \ lowerPart Y r).card ≤ r := by
  rw [card_sdiff_lowerPart]
  exact min_le_left _ _

lemma lowerPart_lt_sdiff {Y : Finset ℕ} {r x y : ℕ}
    (hx : x ∈ lowerPart Y r) (hy : y ∈ Y \ lowerPart Y r) : x < y := by
  classical
  obtain ⟨i, hiRange, hix⟩ := Finset.mem_image.mp hx
  have hi : i.1 < Y.card - r := Finset.mem_range.mp i.2
  have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
  let jy : Fin Y.card := (Y.orderIsoOfFin rfl).symm ⟨y, hyY⟩
  have hjLarge : Y.card - r ≤ jy.val := by
    by_contra hnot
    have hj : jy.val ∈ Finset.range (Y.card - r) := by
      rw [Finset.mem_range]
      omega
    apply (Finset.mem_sdiff.mp hy).2
    apply Finset.mem_image.mpr
    refine ⟨⟨jy.val, hj⟩, by simp, ?_⟩
    have hinv := (Y.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyY⟩
    exact congrArg Subtype.val hinv
  have hfin : (⟨i.1, by omega⟩ : Fin Y.card) < jy := by
    exact Fin.mk_lt_mk.mpr (hi.trans_le hjLarge)
  have hlt := (Y.orderEmbOfFin rfl).strictMono hfin
  have hinv := (Y.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyY⟩
  have hjy : Y.orderEmbOfFin rfl jy = y := congrArg Subtype.val hinv
  rw [hix, hjy] at hlt
  exact hlt

lemma card_filter_le_lowerPart_add (Y : Finset ℕ) (r : ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    (Y.filter P).card ≤ ((lowerPart Y r).filter P).card + r := by
  classical
  let L := lowerPart Y r
  let U := Y \ L
  have hsub : Y.filter P ⊆ L.filter P ∪ U := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_cases hyL : y ∈ L
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyL, hy.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy.1, hyL⟩)
  calc
    (Y.filter P).card ≤ (L.filter P ∪ U).card := Finset.card_le_card hsub
    _ ≤ (L.filter P).card + U.card := Finset.card_union_le _ _
    _ ≤ (L.filter P).card + r :=
      Nat.add_le_add_left (card_sdiff_lowerPart_le Y r) _

lemma two_mul_div_le_self {x e : ℕ} (he : 2 ≤ e) : 2 * (x / e) ≤ x := by
  calc
    2 * (x / e) ≤ e * (x / e) := Nat.mul_le_mul_right (x / e) he
    _ = (x / e) * e := by ring
    _ ≤ x := Nat.div_mul_le_self _ _

/-- Divisor descent with a geometrically shrinking ordered reserve.  At scale
`d`, the largest `P / d` labels may be reserved as future pivots; diversity is
required only in the remaining lower pool. -/
theorem exists_orderedDivisorExtractionAux
    (B L K P S d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧
      (∀ z ∈ Z, q * z ∈ Y) ∧
      Y.card - Z.card ≤
        (L + S) * factors.length + K * factors.sum + 2 * (P / d) ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e ≤ ((lowerPart Z (P / (d * q) + S)).filter
          fun z => ¬e ∣ z).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          (((lowerPart Y (P / d + S)).filter fun y => ¬e ∣ y).card <
            L + K * e)
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := divideMultiples Y e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, factors, hq, hqprod, hfactors, hdqB,
            hscale, hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' rfl
        refine ⟨e * q, Z, e :: factors, Nat.mul_pos hepos hq,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun h => h ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · intro z hz
          have hzY' : q * z ∈ Y' := hscale z hz
          have hzY := divideMultiples_scaled_subset hepos (q * z) hzY'
          simpa [mul_assoc] using hzY
        · have hY'le : Y'.card ≤ Y.card := by
            dsimp only [Y']
            rw [card_divideMultiples hepos]
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have hZle : Z.card ≤ Y'.card := by
            apply Finset.card_le_card_of_injOn (fun z => q * z)
            · intro z hz
              exact hscale z hz
            · intro x hx y hy hxy
              exact Nat.eq_of_mul_eq_mul_left hq hxy
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          rw [hsplit]
          have hfirst : Y.card - Y'.card ≤ L + K * e + (P / d + S) := by
            dsimp only [Y']
            rw [card_sub_card_divideMultiples hepos]
            calc
              (Y.filter fun y => ¬e ∣ y).card ≤
                  (((lowerPart Y (P / d + S)).filter fun y => ¬e ∣ y).card) +
                    (P / d + S) :=
                card_filter_le_lowerPart_add Y (P / d + S) (fun y => ¬e ∣ y)
              _ ≤ L + K * e + (P / d + S) :=
                Nat.add_le_add_right hsmall.le _
          have hassoc : P / (d * e) = (P / d) / e := by
            exact (Nat.div_div_eq_div_mul P d e).symm
          have hgeom : P / d + 2 * (P / (d * e)) ≤ 2 * (P / d) := by
            rw [hassoc]
            have hhalf := two_mul_div_le_self (x := P / d) (e := e) (by omega)
            omega
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e + (P / d + S)) +
                  ((L + S) * factors.length + K * factors.sum +
                    2 * (P / (d * e))) := Nat.add_le_add hfirst hloss
            _ ≤ (L + S) * (e :: factors).length + K * (e :: factors).sum +
                  2 * (P / d) := by
              simp only [List.length_cons, List.sum_cons]
              nlinarith
        · intro a ha hbound
          have hdv := hdiverse a ha (by simpa only [mul_assoc] using hbound)
          simpa only [mul_assoc] using hdv
      · refine ⟨1, Y, [], by omega, by simp, by simp, ?_, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using (Nat.lt_of_not_ge hnot)

/-- Ordered common-divisor extraction.  The terminal lower part is diverse,
the complementary upper part has at most `P / d` elements, and the whole
descent loses only `2P` in addition to the logarithmic and divisor charges. -/
theorem exists_orderedDivisorExtraction
    (B L K P S : ℕ) (hB : 0 < B) (Y : Finset ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ℕ,
      0 < d ∧ d ≤ B ∧
      (∀ z ∈ Z, d * z ∈ Y) ∧
      Y.card - Z.card ≤ (L + S) * Nat.log 2 B + K * B + 2 * P ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ ((lowerPart Z (P / d + S)).filter
          fun z => ¬e ∣ z).card := by
  obtain ⟨d, Z, factors, hd, hdprod, hfactors, hdB,
      hscale, hloss, hdiverse⟩ :=
    exists_orderedDivisorExtractionAux B L K P S 1 (by omega) hB Y
  refine ⟨d, Z, hd, by simpa using hdB, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤
          (L + S) * factors.length + K * factors.sum + 2 * (P / 1) := hloss
      _ ≤ (L + S) * Nat.log 2 B + K * B + 2 * P := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · apply Nat.mul_le_mul_left
            exact (length_le_log_prod_of_one_lt factors hfactors).trans
              (Nat.log_mono_right (by simpa [hdprod] using hdB))
          · apply Nat.mul_le_mul_left
            exact (sum_le_prod_of_one_lt factors hfactors).trans
              (by simpa [hdprod] using hdB)
        · simp
  · intro e he hde
    simpa [mul_assoc] using hdiverse e he (by simpa [mul_assoc] using hde)

/-! A second form of the descent pays for a scale-dependent collision
budget.  After division by the accumulated divisor `d`, the possible number
of representatives of one residue is proportional to `Q / d`.  These terms
form a geometric series along the descent, so their total cost is at most
`2 * Q`, rather than acquiring an extra logarithm. -/

theorem exists_collisionDivisorExtractionAux
    (B L K Q d : ℕ) (hd : 0 < d) (hdB : d ≤ B) (Y : Finset ℕ) :
    ∃ q : ℕ, ∃ Z : Finset ℕ, ∃ factors : List ℕ,
      0 < q ∧ q = factors.prod ∧
      (∀ e ∈ factors, 1 < e) ∧ d * q ≤ B ∧
      (∀ z ∈ Z, q * z ∈ Y) ∧
      Y.card - Z.card ≤
        L * factors.length + K * factors.sum + 2 * (Q / d) ∧
      ∀ e : ℕ, 1 < e → d * q * e ≤ B →
        L + K * e + Q / (d * q) ≤
          (Z.filter fun z => ¬e ∣ z).card := by
  classical
  generalize hr : B - d = r
  induction r using Nat.strong_induction_on generalizing d Y with
  | h r ih =>
      by_cases hbad : ∃ e : ℕ, 1 < e ∧ d * e ≤ B ∧
          ((Y.filter fun y => ¬e ∣ y).card < L + K * e + Q / d)
      · obtain ⟨e, he, hdeB, hsmall⟩ := hbad
        let Y' := divideMultiples Y e
        have hepos : 0 < e := by omega
        have hdepos : 0 < d * e := Nat.mul_pos hd hepos
        have hmeasure : B - d * e < r := by
          rw [← hr]
          have hdlt : d < d * e := by nlinarith
          omega
        obtain ⟨q, Z, factors, hq, hqprod, hfactors, hdqB,
            hscale, hloss, hdiverse⟩ :=
          ih (B - d * e) hmeasure (d * e) hdepos hdeB Y' rfl
        refine ⟨e * q, Z, e :: factors, Nat.mul_pos hepos hq,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.prod_cons, hqprod]
        · intro a ha
          simp only [List.mem_cons] at ha
          exact ha.elim (fun hEq => hEq ▸ he) (hfactors a)
        · simpa [mul_assoc] using hdqB
        · intro z hz
          have hzY' : q * z ∈ Y' := hscale z hz
          have hzY := divideMultiples_scaled_subset hepos (q * z) hzY'
          simpa [mul_assoc] using hzY
        · have hY'le : Y'.card ≤ Y.card := by
            dsimp only [Y']
            rw [card_divideMultiples hepos]
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have hZle : Z.card ≤ Y'.card := by
            apply Finset.card_le_card_of_injOn (fun z => q * z)
            · intro z hz
              exact hscale z hz
            · intro x hx y hy hxy
              exact Nat.eq_of_mul_eq_mul_left hq hxy
          have hsplit : Y.card - Z.card =
              (Y.card - Y'.card) + (Y'.card - Z.card) := by omega
          rw [hsplit]
          have hfirst : Y.card - Y'.card ≤ L + K * e + Q / d := by
            dsimp only [Y']
            rw [card_sub_card_divideMultiples hepos]
            exact hsmall.le
          have hassoc : Q / (d * e) = (Q / d) / e := by
            exact (Nat.div_div_eq_div_mul Q d e).symm
          have hgeom : Q / d + 2 * (Q / (d * e)) ≤ 2 * (Q / d) := by
            rw [hassoc]
            have hhalf := two_mul_div_le_self (x := Q / d) (e := e) (by omega)
            omega
          calc
            (Y.card - Y'.card) + (Y'.card - Z.card) ≤
                (L + K * e + Q / d) +
                  (L * factors.length + K * factors.sum +
                    2 * (Q / (d * e))) := Nat.add_le_add hfirst hloss
            _ ≤ L * (e :: factors).length + K * (e :: factors).sum +
                  2 * (Q / d) := by
              simp only [List.length_cons, List.sum_cons]
              nlinarith
        · intro a ha hbound
          have hdv := hdiverse a ha (by simpa only [mul_assoc] using hbound)
          simpa only [mul_assoc] using hdv
      · refine ⟨1, Y, [], by omega, by simp, by simp, ?_, by simp, by simp, ?_⟩
        · simpa using hdB
        · intro e he hde
          by_contra hnot
          apply hbad
          refine ⟨e, he, by simpa using hde, ?_⟩
          simpa using (Nat.lt_of_not_ge hnot)

/-- Common-divisor extraction with a geometrically charged collision budget. -/
theorem exists_collisionDivisorExtraction
    (B L K Q : ℕ) (hB : 0 < B) (Y : Finset ℕ) :
    ∃ d : ℕ, ∃ Z : Finset ℕ,
      0 < d ∧ d ≤ B ∧
      (∀ z ∈ Z, d * z ∈ Y) ∧
      Y.card - Z.card ≤ L * Nat.log 2 B + K * B + 2 * Q ∧
      ∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e + Q / d ≤ (Z.filter fun z => ¬e ∣ z).card := by
  obtain ⟨d, Z, factors, hd, hdprod, hfactors, hdB,
      hscale, hloss, hdiverse⟩ :=
    exists_collisionDivisorExtractionAux B L K Q 1 (by omega) hB Y
  refine ⟨d, Z, hd, by simpa using hdB, hscale, ?_, ?_⟩
  · calc
      Y.card - Z.card ≤
          L * factors.length + K * factors.sum + 2 * (Q / 1) := hloss
      _ ≤ L * Nat.log 2 B + K * B + 2 * Q := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · apply Nat.mul_le_mul_left
            exact (length_le_log_prod_of_one_lt factors hfactors).trans
              (Nat.log_mono_right (by simpa [hdprod] using hdB))
          · apply Nat.mul_le_mul_left
            exact (sum_le_prod_of_one_lt factors hfactors).trans
              (by simpa [hdprod] using hdB)
        · simp
  · intro e he hde
    simpa [mul_assoc] using hdiverse e he (by simpa [mul_assoc] using hde)

/-! ### A finite simultaneous-balancing lemma -/

open Erdos697.Bernoulli in
lemma bernoulliHalf_weight {ι : Type*} [DecidableEq ι]
    (s T : Finset ι) (hT : T ⊆ s) :
    weight s (fun _ ↦ (2 : ℝ)⁻¹) T = (2 : ℝ)⁻¹ ^ s.card := by
  rw [weight]
  simp only [Finset.prod_const]
  rw [show 1 - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by norm_num, ← pow_add]
  congr 1
  have hle := Finset.card_le_card hT
  rw [Finset.card_sdiff_of_subset hT]
  omega

lemma card_powerset_filter_inter {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (P : Finset ι → Prop)
    [DecidablePred P] :
    (s.powerset.filter fun T ↦ P (T ∩ F)).card =
      (F.powerset.filter P).card * 2 ^ (s \ F).card := by
  let A := F.powerset.filter P
  let D := (s \ F).powerset
  have hfamily : s.powerset.filter (fun T ↦ P (T ∩ F)) =
      Finset.image₂ (· ∪ ·) A D := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image₂,
      A, D]
    constructor
    · rintro ⟨hTs, hP⟩
      refine ⟨T ∩ F, ⟨Finset.inter_subset_right, hP⟩,
        T \ F, ?_, ?_⟩
      · exact Finset.sdiff_subset_sdiff hTs (by rfl)
      · simpa [Finset.union_comm] using Finset.sdiff_union_inter T F
    · rintro ⟨U, ⟨hUF, hPU⟩, V, hVD, rfl⟩
      have hVs : V ⊆ s := hVD.trans Finset.sdiff_subset
      have hVnot : ∀ x ∈ V, x ∉ F := by
        intro x hxV hxF
        exact (Finset.mem_sdiff.mp (hVD hxV)).2 hxF
      have hinter : (U ∪ V) ∩ F = U := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxU | hxV, hxF⟩
          · exact hxU
          · exact (hVnot x hxV hxF).elim
        · intro hxU
          exact ⟨Or.inl hxU, hUF hxU⟩
      refine ⟨Finset.union_subset (hUF.trans hF) hVs, ?_⟩
      rw [hinter]
      exact hPU
  rw [hfamily]
  have hinj : ((A : Set (Finset ι)) ×ˢ (D : Set (Finset ι))).InjOn
      (fun x ↦ x.1 ∪ x.2) := by
    rintro ⟨U, V⟩ ⟨hUA, hVDmem⟩ ⟨U', V'⟩ ⟨hU'A, hV'Dmem⟩ huv
    have hUF : U ⊆ F := (Finset.mem_filter.mp hUA).1
      |> Finset.mem_powerset.mp
    have hU'F : U' ⊆ F := (Finset.mem_filter.mp hU'A).1
      |> Finset.mem_powerset.mp
    have hVD : V ⊆ s \ F := Finset.mem_powerset.mp hVDmem
    have hV'D : V' ⊆ s \ F := Finset.mem_powerset.mp hV'Dmem
    change U ∪ V = U' ∪ V' at huv
    have hU : U = U' := by
      ext x
      constructor
      · intro hxU
        have hx : x ∈ U' ∪ V' := by
          rw [← huv]
          exact Finset.mem_union_left V hxU
        rcases Finset.mem_union.mp hx with hxU' | hxV'
        · exact hxU'
        · exact ((Finset.mem_sdiff.mp (hV'D hxV')).2 (hUF hxU)).elim
      · intro hxU'
        have hx : x ∈ U ∪ V := by
          rw [huv]
          exact Finset.mem_union_left V' hxU'
        rcases Finset.mem_union.mp hx with hxU | hxV
        · exact hxU
        · exact ((Finset.mem_sdiff.mp (hVD hxV)).2 (hU'F hxU')).elim
    subst U'
    change U ∪ V = U ∪ V' at huv
    have hV : V = V' := by
      ext x
      constructor
      · intro hxV
        have hx : x ∈ U ∪ V' := by
          rw [← huv]
          exact Finset.mem_union_right U hxV
        rcases Finset.mem_union.mp hx with hxU | hxV'
        · exact ((Finset.mem_sdiff.mp (hVD hxV)).2 (hUF hxU)).elim
        · exact hxV'
      · intro hxV'
        have hx : x ∈ U ∪ V := by
          rw [huv]
          exact Finset.mem_union_right U hxV'
        rcases Finset.mem_union.mp hx with hxU | hxV
        · exact ((Finset.mem_sdiff.mp (hV'D hxV')).2 (hUF hxU)).elim
        · exact hxV
    subst V'
    rfl
  rw [Finset.card_image₂_iff.mpr hinj]
  simp [A, D]

open Erdos697.Bernoulli in
lemma sum_bernoulliHalf_filter_inter {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (P : Finset ι → Prop)
    [DecidablePred P] :
    (∑ T ∈ s.powerset.filter (fun T ↦ P (T ∩ F)),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) =
      ∑ U ∈ F.powerset.filter P, weight F (fun _ ↦ (2 : ℝ)⁻¹) U := by
  rw [show (∑ T ∈ s.powerset.filter (fun T ↦ P (T ∩ F)),
      weight s (fun _ ↦ (2 : ℝ)⁻¹) T) =
      ((s.powerset.filter fun T ↦ P (T ∩ F)).card : ℝ) *
        (2 : ℝ)⁻¹ ^ s.card by
    calc
      _ = ∑ _T ∈ s.powerset.filter (fun T ↦ P (T ∩ F)),
          (2 : ℝ)⁻¹ ^ s.card := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [bernoulliHalf_weight s T
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)]
      _ = _ := by simp]
  rw [show (∑ U ∈ F.powerset.filter P,
      weight F (fun _ ↦ (2 : ℝ)⁻¹) U) =
      ((F.powerset.filter P).card : ℝ) * (2 : ℝ)⁻¹ ^ F.card by
    calc
      _ = ∑ _U ∈ F.powerset.filter P, (2 : ℝ)⁻¹ ^ F.card := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [bernoulliHalf_weight F U
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1)]
      _ = _ := by simp]
  rw [card_powerset_filter_inter s F hF P, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  have hcard : F.card + (s \ F).card = s.card := by
    have hle := Finset.card_le_card hF
    rw [Finset.card_sdiff_of_subset hF]
    omega
  rw [← hcard, pow_add]
  have hpow : (2 : ℝ) ^ (s \ F).card * (2 : ℝ)⁻¹ ^ (s \ F).card = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((F.powerset.filter P).card : ℝ) * (2 : ℝ) ^ (s \ F).card *
          ((2 : ℝ)⁻¹ ^ F.card * (2 : ℝ)⁻¹ ^ (s \ F).card) =
        ((F.powerset.filter P).card : ℝ) * (2 : ℝ)⁻¹ ^ F.card *
          ((2 : ℝ) ^ (s \ F).card * (2 : ℝ)⁻¹ ^ (s \ F).card) := by ring
    _ = ((F.powerset.filter P).card : ℝ) * (2 : ℝ)⁻¹ ^ F.card := by
      rw [hpow]
      ring

open Erdos697.Bernoulli in
lemma bernoulliHalf_lower_inter {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ) (hK : 4 * K ≤ F.card) :
    (∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ F).card < K),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 24)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ U.card < K)]
  have htail := lower_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (1 : ℝ) / 2)
    (by simp; ring) (by norm_num) (by norm_num) (by
      have hKr : (4 * K : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  convert htail using 1 <;> norm_num <;> ring

open Erdos697.Bernoulli in
lemma bernoulliHalf_upper_inter {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ)
    (hK : 3 * F.card ≤ 4 * K) :
    (∑ T ∈ s.powerset.filter (fun T ↦ K ≤ (T ∩ F).card),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 40)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ K ≤ U.card)]
  have htail := upper_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (3 : ℝ) / 2)
    (by simp; ring) (by norm_num) (by
      have hKr : (3 * F.card : ℝ) ≤ (4 * K : ℝ) := by exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  convert htail using 1 <;> norm_num <;> ring

open Erdos697.Bernoulli in
lemma bernoulliHalf_lower_two_fifths {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ) (hK : 5 * K ≤ 2 * F.card) :
    (∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ F).card < K),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 180)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ U.card < K)]
  have htail := lower_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (4 : ℝ) / 5)
    (by simp; ring) (by norm_num) (by norm_num) (by
      have hKr : (5 * K : ℝ) ≤ (2 * F.card : ℕ) := by exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  convert htail using 1 <;> norm_num <;> ring

open Erdos697.Bernoulli in
lemma bernoulliHalf_upper_three_fifths {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ)
    (hK : 3 * F.card ≤ 5 * K) :
    (∑ T ∈ s.powerset.filter (fun T ↦ K ≤ (T ∩ F).card),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 220)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ K ≤ U.card)]
  have htail := upper_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (6 : ℝ) / 5)
    (by simp; ring) (by norm_num) (by
      have hKr : (3 * F.card : ℝ) ≤ (5 * K : ℕ) := by exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  convert htail using 1 <;> norm_num <;> ring

open Erdos697.Bernoulli in
lemma bernoulliHalf_lower_nine_twentieths {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ) (hK : 20 * K ≤ 9 * F.card) :
    (∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ F).card < K),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 1000)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ U.card < K)]
  have htail := lower_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (9 : ℝ) / 10)
    (by simp; ring) (by norm_num) (by norm_num) (by
      have hKr : (20 * K : ℝ) ≤ (9 * F.card : ℕ) := by
        exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  calc
    _ ≤ Real.exp (-((F.card : ℝ) / 760)) := by
      convert htail using 1 <;> norm_num <;> ring
    _ ≤ Real.exp (-((F.card : ℝ) / 1000)) := by
      apply Real.exp_le_exp.mpr
      have hcard : (0 : ℝ) ≤ F.card := by positivity
      nlinarith

open Erdos697.Bernoulli in
lemma bernoulliHalf_upper_eleven_twentieths {ι : Type*} [DecidableEq ι]
    (s F : Finset ι) (hF : F ⊆ s) (K : ℕ)
    (hK : 11 * F.card ≤ 20 * K) :
    (∑ T ∈ s.powerset.filter (fun T ↦ K ≤ (T ∩ F).card),
        weight s (fun _ ↦ (2 : ℝ)⁻¹) T) ≤
      Real.exp (-((F.card : ℝ) / 1000)) := by
  rw [sum_bernoulliHalf_filter_inter s F hF
    (fun U ↦ K ≤ U.card)]
  have htail := upper_tail_chernoff F (fun _ ↦ (2 : ℝ)⁻¹)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)
    (K := K) (EW := (F.card : ℝ) / 2) (r := (11 : ℝ) / 10)
    (by simp; ring) (by norm_num) (by
      have hKr : (11 * F.card : ℝ) ≤ (20 * K : ℕ) := by
        exact_mod_cast hK
      push_cast at hKr
      nlinarith)
  calc
    _ ≤ Real.exp (-((F.card : ℝ) / 840)) := by
      convert htail using 1 <;> norm_num <;> ring
    _ ≤ Real.exp (-((F.card : ℝ) / 1000)) := by
      apply Real.exp_le_exp.mpr
      have hcard : (0 : ℝ) ≤ F.card := by positivity
      nlinarith

lemma two_mul_exp_neg_log_bound (r : ℕ) :
    (2 * r : ℝ) * Real.exp
      (-((Nat.log 2 (2 * r + 1) + 1 : ℕ) : ℝ)) < 1 := by
  let L := Nat.log 2 (2 * r + 1) + 1
  have hnat : 2 * r < 2 ^ L := by
    calc
      2 * r < 2 * r + 1 := by omega
      _ < 2 ^ (Nat.log 2 (2 * r + 1)).succ :=
        Nat.lt_pow_succ_log_self (by omega) _
      _ = 2 ^ L := by simp [L]
  have hcast : (2 * r : ℝ) < (2 : ℝ) ^ L := by
    exact_mod_cast hnat
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp 1 using 1 <;> norm_num
  have hpow : (2 : ℝ) ^ L ≤ Real.exp (L : ℝ) := by
    calc
      (2 : ℝ) ^ L ≤ (Real.exp 1) ^ L :=
        pow_le_pow_left₀ (by norm_num) he2 _
      _ = Real.exp (L : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have hinv : Real.exp (-((L : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ L)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) hpow
  calc
    (2 * r : ℝ) * Real.exp
        (-((Nat.log 2 (2 * r + 1) + 1 : ℕ) : ℝ)) =
        (2 * r : ℝ) * Real.exp (-((L : ℕ) : ℝ)) := by rfl
    _ ≤ (2 * r : ℝ) * ((2 : ℝ) ^ L)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ < 1 := by
      simpa [div_eq_mul_inv] using
        ((div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)).2 hcast)

open Erdos697.Bernoulli in
lemma sum_bernoulliHalf_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : Finset (Finset ι)) (hE : E ⊆ s.powerset) :
    (∑ T ∈ E, weight s (fun _ ↦ (2 : ℝ)⁻¹) T) =
      (E.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
  calc
    _ = ∑ _T ∈ E, (2 : ℝ)⁻¹ ^ s.card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [bernoulliHalf_weight s T (Finset.mem_powerset.mp (hE hT))]
    _ = _ := by simp

/-- One Bernoulli bisection simultaneously balances every member of a finite
family.  The logarithmic size threshold is what permits this lemma to be
iterated while retaining divisor and dyadic-bin constraints. -/
theorem exists_simultaneously_balanced_subset
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (family : Finset (Finset ι))
    (hsub : ∀ F ∈ family, F ⊆ s)
    (hlarge : ∀ F ∈ family,
      220 * (Nat.log 2 (2 * family.card + 1) + 1) ≤ F.card) :
    ∃ T : Finset ι, T ⊆ s ∧ ∀ F ∈ family,
      2 * F.card / 5 ≤ (T ∩ F).card ∧
        (T ∩ F).card < 3 * F.card / 5 + 1 := by
  let L := Nat.log 2 (2 * family.card + 1) + 1
  let low : Finset ι → Finset (Finset ι) := fun F ↦
    s.powerset.filter fun T ↦ (T ∩ F).card < 2 * F.card / 5
  let high : Finset ι → Finset (Finset ι) := fun F ↦
    s.powerset.filter fun T ↦ 3 * F.card / 5 + 1 ≤ (T ∩ F).card
  let bad : Finset ι → Finset (Finset ι) := fun F ↦ low F ∪ high F
  let Bad := family.biUnion bad
  have hlowSub (F : Finset ι) : low F ⊆ s.powerset := by
    exact Finset.filter_subset _ _
  have hhighSub (F : Finset ι) : high F ⊆ s.powerset := by
    exact Finset.filter_subset _ _
  have hbadSub (F : Finset ι) : bad F ⊆ s.powerset := by
    exact Finset.union_subset (hlowSub F) (hhighSub F)
  have hBadSub : Bad ⊆ s.powerset := by
    intro T hT
    change T ∈ family.biUnion bad at hT
    rw [Finset.mem_biUnion] at hT
    obtain ⟨F, hF, hTF⟩ := hT
    exact hbadSub F hTF
  have hlow (F : Finset ι) (hF : F ∈ family) :
      ((low F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        Real.exp (-((L : ℕ) : ℝ)) := by
    have htail := bernoulliHalf_lower_two_fifths s F (hsub F hF)
      (2 * F.card / 5) (by omega)
    rw [sum_bernoulliHalf_finset s (low F) (hlowSub F)] at htail
    have hcard : 220 * L ≤ F.card := hlarge F hF
    have hcast : (L : ℝ) ≤ (F.card : ℝ) / 220 := by
      have hcardR : (220 * L : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hcard
      push_cast at hcardR
      nlinarith
    exact htail.trans (Real.exp_le_exp.mpr (by
      have hFnonneg : (0 : ℝ) ≤ F.card := by positivity
      nlinarith))
  have hhigh (F : Finset ι) (hF : F ∈ family) :
      ((high F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        Real.exp (-((L : ℕ) : ℝ)) := by
    have htail := bernoulliHalf_upper_three_fifths s F (hsub F hF)
      (3 * F.card / 5 + 1) (by omega)
    rw [sum_bernoulliHalf_finset s (high F) (hhighSub F)] at htail
    have hcard : 220 * L ≤ F.card := hlarge F hF
    have hcast : (L : ℝ) ≤ (F.card : ℝ) / 220 := by
      have hcardR : (220 * L : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hcard
      push_cast at hcardR
      nlinarith
    exact htail.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hbad (F : Finset ι) (hF : F ∈ family) :
      ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        2 * Real.exp (-((L : ℕ) : ℝ)) := by
    have hcard := Finset.card_union_le (low F) (high F)
    have hcardR : ((bad F).card : ℝ) ≤
        (low F).card + (high F).card := by
      exact_mod_cast hcard
    have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ s.card := by positivity
    calc
      ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
          (((low F).card : ℝ) + ((high F).card : ℝ)) *
            (2 : ℝ)⁻¹ ^ s.card :=
        mul_le_mul_of_nonneg_right hcardR hpnonneg
      _ = ((low F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card +
          ((high F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
        push_cast
        ring
      _ ≤ Real.exp (-((L : ℕ) : ℝ)) +
          Real.exp (-((L : ℕ) : ℝ)) :=
        add_le_add (hlow F hF) (hhigh F hF)
      _ = 2 * Real.exp (-((L : ℕ) : ℝ)) := by ring
  have hBadCard := Finset.card_biUnion_le
    (s := family) (t := bad)
  have hBadCardR : (Bad.card : ℝ) ≤
      ∑ F ∈ family, ((bad F).card : ℝ) := by
    exact_mod_cast hBadCard
  have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ s.card := by positivity
  have hBadProb : (Bad.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card < 1 := by
    calc
      (Bad.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
          (∑ F ∈ family, ((bad F).card : ℝ)) *
            (2 : ℝ)⁻¹ ^ s.card :=
        mul_le_mul_of_nonneg_right hBadCardR hpnonneg
      _ = ∑ F ∈ family,
          ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
        rw [Finset.sum_mul]
      _ ≤ ∑ _F ∈ family, 2 * Real.exp (-((L : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro F hF
        exact hbad F hF
      _ = (2 * family.card : ℝ) * Real.exp (-((L : ℕ) : ℝ)) := by
        simp
        ring
      _ < 1 := by
        simpa [L] using two_mul_exp_neg_log_bound family.card
  have hwhole : (s.powerset.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card = 1 := by
    simpa using (Erdos697.Bernoulli.sum_weight_powerset s
      (fun _ ↦ (2 : ℝ)⁻¹)).trans (sum_bernoulliHalf_finset s s.powerset
        (Subset.refl _))
  have hcardltR : (Bad.card : ℝ) < s.powerset.card := by
    have hp : 0 < (2 : ℝ)⁻¹ ^ s.card := by positivity
    nlinarith
  have hcardlt : Bad.card < s.powerset.card := by exact_mod_cast hcardltR
  obtain ⟨T, hT⟩ := Finset.sdiff_nonempty_of_card_lt_card hcardlt
  rw [Finset.mem_sdiff] at hT
  refine ⟨T, Finset.mem_powerset.mp hT.1, ?_⟩
  intro F hF
  have hnotBad : T ∉ bad F := by
    intro hTF
    exact hT.2 (Finset.mem_biUnion.mpr ⟨F, hF, hTF⟩)
  change T ∉ low F ∪ high F at hnotBad
  rw [Finset.mem_union, not_or] at hnotBad
  constructor
  · have := hnotBad.1
    change T ∉ s.powerset.filter
      (fun T ↦ (T ∩ F).card < 2 * F.card / 5) at this
    rw [Finset.mem_filter, not_and_or] at this
    exact le_of_not_gt (this.resolve_left (by simpa using hT.1))
  · have := hnotBad.2
    change T ∉ s.powerset.filter
      (fun T ↦ 3 * F.card / 5 + 1 ≤ (T ∩ F).card) at this
    rw [Finset.mem_filter, not_and_or] at this
    exact lt_of_not_ge (this.resolve_left (by simpa using hT.1))

theorem exists_simultaneously_balanced_subset_indexed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      220 * (Nat.log 2 (2 * J.card + 1) + 1) ≤ (F j).card) :
    ∃ T : Finset ι, T ⊆ s ∧ ∀ j ∈ J,
      2 * (F j).card / 5 ≤ (T ∩ F j).card ∧
        (T ∩ F j).card < 3 * (F j).card / 5 + 1 := by
  let family := J.image F
  have hfamilyCard : family.card ≤ J.card := Finset.card_image_le
  have hlog : Nat.log 2 (2 * family.card + 1) ≤
      Nat.log 2 (2 * J.card + 1) := by
    apply Nat.log_mono_right
    omega
  have hfamilySub : ∀ G ∈ family, G ⊆ s := by
    intro G hG
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
    exact hsub j hj
  have hfamilyLarge : ∀ G ∈ family,
      220 * (Nat.log 2 (2 * family.card + 1) + 1) ≤ G.card := by
    intro G hG
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
    exact (Nat.mul_le_mul_left 220 (Nat.add_le_add_right hlog 1)).trans
      (hlarge j hj)
  obtain ⟨T, hTs, hT⟩ := exists_simultaneously_balanced_subset
    s family hfamilySub hfamilyLarge
  refine ⟨T, hTs, ?_⟩
  intro j hj
  exact hT (F j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

/-- Indexed simultaneous bisection, with the same two-fifths/three-fifths
bounds for both complementary children. -/
theorem exists_balanced_bipartition_indexed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      220 * (Nat.log 2 (2 * J.card + 1) + 1) ≤ (F j).card) :
    ∃ T U : Finset ι, Disjoint T U ∧ T ∪ U = s ∧
      ∀ j ∈ J,
        (2 * (F j).card / 5 ≤ (T ∩ F j).card ∧
          (T ∩ F j).card < 3 * (F j).card / 5 + 2) ∧
        (2 * (F j).card / 5 ≤ (U ∩ F j).card ∧
          (U ∩ F j).card < 3 * (F j).card / 5 + 2) := by
  obtain ⟨T, hTs, hT⟩ := exists_simultaneously_balanced_subset_indexed
    s J F hsub hlarge
  let U := s \ T
  refine ⟨T, U, Finset.disjoint_sdiff, ?_, ?_⟩
  · exact Finset.union_sdiff_of_subset hTs
  · intro j hj
    refine ⟨⟨(hT j hj).1, (hT j hj).2.trans_le (by omega)⟩, ?_⟩
    have hEq : U ∩ F j = F j \ (T ∩ F j) := by
      ext x
      simp only [U, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxs, hxT⟩, hxF⟩
        exact ⟨hxF, fun hx ↦ hxT hx.1⟩
      · rintro ⟨hxF, hxnot⟩
        exact ⟨⟨hsub j hj hxF, fun hxT ↦ hxnot ⟨hxT, hxF⟩⟩, hxF⟩
    have hinter : T ∩ F j ⊆ F j := Finset.inter_subset_right
    have hcard : (U ∩ F j).card =
        (F j).card - (T ∩ F j).card := by
      rw [hEq, Finset.card_sdiff_of_subset hinter]
    have hsumle : 2 * (F j).card / 5 + 3 * (F j).card / 5 ≤
        (F j).card := by
      calc
        2 * (F j).card / 5 + 3 * (F j).card / 5 ≤
            (2 * (F j).card + 3 * (F j).card) / 5 :=
          Nat.div_add_div_le_add_div
        _ = (F j).card := by omega
    have hsumge : (F j).card ≤
        2 * (F j).card / 5 + 3 * (F j).card / 5 + 1 := by
      have h := Nat.add_div_le_div_add_div_add_one
        (2 * (F j).card) (3 * (F j).card) 5
      have hleft : (2 * (F j).card + 3 * (F j).card) / 5 =
          (F j).card := by omega
      rw [hleft] at h
      exact h
    have hlo := (hT j hj).1
    have hhi := (hT j hj).2
    rw [hcard]
    constructor <;> omega

/-- A much tighter simultaneous bisection.  The weaker exponential constant
is harmless, while the nine-twentieths/eleven-twentieths window remains tight
enough after fifteen recursive levels for the finite filling argument. -/
theorem exists_simultaneously_balanced_subset_tight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (family : Finset (Finset ι))
    (hsub : ∀ F ∈ family, F ⊆ s)
    (hlarge : ∀ F ∈ family,
      1000 * (Nat.log 2 (2 * family.card + 1) + 1) ≤ F.card) :
    ∃ T : Finset ι, T ⊆ s ∧ ∀ F ∈ family,
      9 * F.card / 20 ≤ (T ∩ F).card ∧
        (T ∩ F).card < 11 * F.card / 20 + 1 := by
  let L := Nat.log 2 (2 * family.card + 1) + 1
  let low : Finset ι → Finset (Finset ι) := fun F ↦
    s.powerset.filter fun T ↦ (T ∩ F).card < 9 * F.card / 20
  let high : Finset ι → Finset (Finset ι) := fun F ↦
    s.powerset.filter fun T ↦ 11 * F.card / 20 + 1 ≤ (T ∩ F).card
  let bad : Finset ι → Finset (Finset ι) := fun F ↦ low F ∪ high F
  let Bad := family.biUnion bad
  have hlowSub (F : Finset ι) : low F ⊆ s.powerset :=
    Finset.filter_subset _ _
  have hhighSub (F : Finset ι) : high F ⊆ s.powerset :=
    Finset.filter_subset _ _
  have hbadSub (F : Finset ι) : bad F ⊆ s.powerset :=
    Finset.union_subset (hlowSub F) (hhighSub F)
  have hBadSub : Bad ⊆ s.powerset := by
    intro T hT
    change T ∈ family.biUnion bad at hT
    obtain ⟨F, hF, hTF⟩ := Finset.mem_biUnion.mp hT
    exact hbadSub F hTF
  have hlow (F : Finset ι) (hF : F ∈ family) :
      ((low F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        Real.exp (-((L : ℕ) : ℝ)) := by
    have htail := bernoulliHalf_lower_nine_twentieths s F (hsub F hF)
      (9 * F.card / 20) (by omega)
    rw [sum_bernoulliHalf_finset s (low F) (hlowSub F)] at htail
    have hcard : 1000 * L ≤ F.card := hlarge F hF
    have hcast : (L : ℝ) ≤ (F.card : ℝ) / 1000 := by
      have hcardR : (1000 * L : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast hcard
      push_cast at hcardR
      nlinarith
    exact htail.trans (Real.exp_le_exp.mpr (by
      have hFnonneg : (0 : ℝ) ≤ F.card := by positivity
      nlinarith))
  have hhigh (F : Finset ι) (hF : F ∈ family) :
      ((high F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        Real.exp (-((L : ℕ) : ℝ)) := by
    have htail := bernoulliHalf_upper_eleven_twentieths s F (hsub F hF)
      (11 * F.card / 20 + 1) (by omega)
    rw [sum_bernoulliHalf_finset s (high F) (hhighSub F)] at htail
    have hcard : 1000 * L ≤ F.card := hlarge F hF
    have hcast : (L : ℝ) ≤ (F.card : ℝ) / 1000 := by
      have hcardR : (1000 * L : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast hcard
      push_cast at hcardR
      nlinarith
    exact htail.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hbad (F : Finset ι) (hF : F ∈ family) :
      ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
        2 * Real.exp (-((L : ℕ) : ℝ)) := by
    have hcard := Finset.card_union_le (low F) (high F)
    have hcardR : ((bad F).card : ℝ) ≤
        (low F).card + (high F).card := by
      exact_mod_cast hcard
    have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ s.card := by positivity
    calc
      ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
          (((low F).card : ℝ) + ((high F).card : ℝ)) *
            (2 : ℝ)⁻¹ ^ s.card :=
        mul_le_mul_of_nonneg_right hcardR hpnonneg
      _ = ((low F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card +
          ((high F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
        push_cast
        ring
      _ ≤ Real.exp (-((L : ℕ) : ℝ)) +
          Real.exp (-((L : ℕ) : ℝ)) :=
        add_le_add (hlow F hF) (hhigh F hF)
      _ = 2 * Real.exp (-((L : ℕ) : ℝ)) := by ring
  have hBadCard := Finset.card_biUnion_le (s := family) (t := bad)
  have hBadCardR : (Bad.card : ℝ) ≤
      ∑ F ∈ family, ((bad F).card : ℝ) := by
    exact_mod_cast hBadCard
  have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ s.card := by positivity
  have hBadProb : (Bad.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card < 1 := by
    calc
      (Bad.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card ≤
          (∑ F ∈ family, ((bad F).card : ℝ)) *
            (2 : ℝ)⁻¹ ^ s.card :=
        mul_le_mul_of_nonneg_right hBadCardR hpnonneg
      _ = ∑ F ∈ family,
          ((bad F).card : ℝ) * (2 : ℝ)⁻¹ ^ s.card := by
        rw [Finset.sum_mul]
      _ ≤ ∑ _F ∈ family, 2 * Real.exp (-((L : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro F hF
        exact hbad F hF
      _ = (2 * family.card : ℝ) * Real.exp (-((L : ℕ) : ℝ)) := by
        simp
        ring
      _ < 1 := by
        simpa [L] using two_mul_exp_neg_log_bound family.card
  have hwhole : (s.powerset.card : ℝ) * (2 : ℝ)⁻¹ ^ s.card = 1 := by
    simpa using (Erdos697.Bernoulli.sum_weight_powerset s
      (fun _ ↦ (2 : ℝ)⁻¹)).trans (sum_bernoulliHalf_finset s s.powerset
        (Subset.refl _))
  have hcardltR : (Bad.card : ℝ) < s.powerset.card := by
    have hp : 0 < (2 : ℝ)⁻¹ ^ s.card := by positivity
    nlinarith
  have hcardlt : Bad.card < s.powerset.card := by exact_mod_cast hcardltR
  obtain ⟨T, hT⟩ := Finset.sdiff_nonempty_of_card_lt_card hcardlt
  rw [Finset.mem_sdiff] at hT
  refine ⟨T, Finset.mem_powerset.mp hT.1, ?_⟩
  intro F hF
  have hnotBad : T ∉ bad F := by
    intro hTF
    exact hT.2 (Finset.mem_biUnion.mpr ⟨F, hF, hTF⟩)
  change T ∉ low F ∪ high F at hnotBad
  rw [Finset.mem_union, not_or] at hnotBad
  constructor
  · have h := hnotBad.1
    change T ∉ s.powerset.filter
      (fun T ↦ (T ∩ F).card < 9 * F.card / 20) at h
    rw [Finset.mem_filter, not_and_or] at h
    exact le_of_not_gt (h.resolve_left (by simpa using hT.1))
  · have h := hnotBad.2
    change T ∉ s.powerset.filter
      (fun T ↦ 11 * F.card / 20 + 1 ≤ (T ∩ F).card) at h
    rw [Finset.mem_filter, not_and_or] at h
    exact lt_of_not_ge (h.resolve_left (by simpa using hT.1))

theorem exists_simultaneously_balanced_subset_tight_indexed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      1000 * (Nat.log 2 (2 * J.card + 1) + 1) ≤ (F j).card) :
    ∃ T : Finset ι, T ⊆ s ∧ ∀ j ∈ J,
      9 * (F j).card / 20 ≤ (T ∩ F j).card ∧
        (T ∩ F j).card < 11 * (F j).card / 20 + 1 := by
  let family := J.image F
  have hfamilyCard : family.card ≤ J.card := Finset.card_image_le
  have hlog : Nat.log 2 (2 * family.card + 1) ≤
      Nat.log 2 (2 * J.card + 1) := by
    apply Nat.log_mono_right
    omega
  have hfamilySub : ∀ G ∈ family, G ⊆ s := by
    intro G hG
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
    exact hsub j hj
  have hfamilyLarge : ∀ G ∈ family,
      1000 * (Nat.log 2 (2 * family.card + 1) + 1) ≤ G.card := by
    intro G hG
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
    exact (Nat.mul_le_mul_left 1000 (Nat.add_le_add_right hlog 1)).trans
      (hlarge j hj)
  obtain ⟨T, hTs, hT⟩ := exists_simultaneously_balanced_subset_tight
    s family hfamilySub hfamilyLarge
  refine ⟨T, hTs, ?_⟩
  intro j hj
  exact hT (F j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

theorem exists_balanced_bipartition_tight_indexed
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      1000 * (Nat.log 2 (2 * J.card + 1) + 1) ≤ (F j).card) :
    ∃ T U : Finset ι, Disjoint T U ∧ T ∪ U = s ∧
      ∀ j ∈ J,
        (9 * (F j).card / 20 ≤ (T ∩ F j).card ∧
          (T ∩ F j).card < 11 * (F j).card / 20 + 2) ∧
        (9 * (F j).card / 20 ≤ (U ∩ F j).card ∧
          (U ∩ F j).card < 11 * (F j).card / 20 + 2) := by
  obtain ⟨T, hTs, hT⟩ := exists_simultaneously_balanced_subset_tight_indexed
    s J F hsub hlarge
  let U := s \ T
  refine ⟨T, U, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hTs, ?_⟩
  intro j hj
  refine ⟨⟨(hT j hj).1, (hT j hj).2.trans_le (by omega)⟩, ?_⟩
  have hEq : U ∩ F j = F j \ (T ∩ F j) := by
    ext x
    simp only [U, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxs, hxT⟩, hxF⟩
      exact ⟨hxF, fun hx ↦ hxT hx.1⟩
    · rintro ⟨hxF, hxnot⟩
      exact ⟨⟨hsub j hj hxF, fun hxT ↦ hxnot ⟨hxT, hxF⟩⟩, hxF⟩
  have hinter : T ∩ F j ⊆ F j := Finset.inter_subset_right
  have hcard : (U ∩ F j).card =
      (F j).card - (T ∩ F j).card := by
    rw [hEq, Finset.card_sdiff_of_subset hinter]
  have hsumle : 9 * (F j).card / 20 + 11 * (F j).card / 20 ≤
      (F j).card := by
    calc
      9 * (F j).card / 20 + 11 * (F j).card / 20 ≤
          (9 * (F j).card + 11 * (F j).card) / 20 :=
        Nat.div_add_div_le_add_div
      _ = (F j).card := by omega
  have hsumge : (F j).card ≤
      9 * (F j).card / 20 + 11 * (F j).card / 20 + 1 := by
    have h := Nat.add_div_le_div_add_div_add_one
      (9 * (F j).card) (11 * (F j).card) 20
    have hleft : (9 * (F j).card + 11 * (F j).card) / 20 =
        (F j).card := by omega
    rw [hleft] at h
    exact h
  have hlo := (hT j hj).1
  have hhi := (hT j hj).2
  rw [hcard]
  constructor <;> omega

/-! ### Recursive simultaneous balancing -/

/-- A perfect binary tree of natural-number sumsets.  It is declared here
because the partition machinery below maps its leaves into such a tree. -/
inductive SumTree : ℕ → Type
  | leaf (S : Finset ℕ) : SumTree 0
  | node {t : ℕ} (left right : SumTree t) : SumTree (t + 1)

namespace SumTree

def carrier : {t : ℕ} → SumTree t → Finset ℕ
  | 0, leaf S => S
  | _ + 1, node left right => carrier left + carrier right

def AllLeaves (P : Finset ℕ → Prop) : {t : ℕ} → SumTree t → Prop
  | 0, leaf S => P S
  | _ + 1, node left right => AllLeaves P left ∧ AllLeaves P right

/-- Cardinality forced at depth `t` if every additive merge keeps growing. -/
def growthLower (k : ℕ) : ℕ → ℕ
  | 0 => k
  | t + 1 => 3 * growthLower k t - 3

lemma growthLower_ge {k : ℕ} (hk : 2 ≤ k) :
    ∀ t, k ≤ growthLower k t := by
  intro t
  induction t with
  | zero => simp [growthLower]
  | succ t ih =>
      rw [growthLower]
      have htwo : 2 ≤ growthLower k t := hk.trans ih
      omega

end SumTree

/-- A perfect binary tree whose leaves are finsets.  Unlike `SumTree`, its
internal operation is union; it records a genuine disjoint partition of the
original labelled set. -/
inductive PartitionTree (ι : Type u) : ℕ → Type u
  | leaf (S : Finset ι) : PartitionTree ι 0
  | node {t : ℕ} (left right : PartitionTree ι t) : PartitionTree ι (t + 1)

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

def carrier : {t : ℕ} → PartitionTree ι t → Finset ι
  | 0, leaf S => S
  | _ + 1, node left right => carrier left ∪ carrier right

def AllLeaves (P : Finset ι → Prop) : {t : ℕ} → PartitionTree ι t → Prop
  | 0, leaf S => P S
  | _ + 1, node left right => AllLeaves P left ∧ AllLeaves P right

def PairwiseDisjoint : {t : ℕ} → PartitionTree ι t → Prop
  | 0, leaf _ => True
  | _ + 1, node left right =>
      PairwiseDisjoint left ∧ PairwiseDisjoint right ∧
        Disjoint left.carrier right.carrier

lemma AllLeaves.mono {t : ℕ} {T : PartitionTree ι t}
    {P Q : Finset ι → Prop} (h : T.AllLeaves P)
    (hPQ : ∀ S, P S → Q S) : T.AllLeaves Q := by
  induction T with
  | leaf S => exact hPQ S h
  | node left right ihl ihr =>
      exact ⟨ihl h.1, ihr h.2⟩

lemma AllLeaves.and {t : ℕ} {T : PartitionTree ι t}
    {P Q : Finset ι → Prop} (hP : T.AllLeaves P)
    (hQ : T.AllLeaves Q) : T.AllLeaves fun S ↦ P S ∧ Q S := by
  induction T with
  | leaf S => exact ⟨hP, hQ⟩
  | node left right ihl ihr =>
      exact ⟨ihl hP.1 hQ.1, ihr hP.2 hQ.2⟩

lemma allLeaves_subset_carrier {t : ℕ} (T : PartitionTree ι t) :
    T.AllLeaves fun S ↦ S ⊆ T.carrier := by
  induction T with
  | leaf S => exact fun _ h ↦ h
  | node left right ihl ihr =>
      exact ⟨
        ihl.mono fun S hS x hx ↦ Finset.mem_union_left _ (hS hx),
        ihr.mono fun S hS x hx ↦ Finset.mem_union_right _ (hS hx)⟩

lemma tight_split_card_ratios {p c : ℕ} (hp : 200 ≤ p)
    (hlow : 9 * p / 20 ≤ c) (hhigh : c < 11 * p / 20 + 2) :
    89 * p ≤ 200 * c ∧ 200 * c ≤ 111 * p := by
  constructor <;> omega

private lemma balancing_threshold_pos (r : ℕ) :
    0 < 1000 * (Nat.log 2 (2 * r + 1) + 1) := by positivity

private lemma balancing_threshold_ge_two_hundred (r : ℕ) :
    200 ≤ 1000 * (Nat.log 2 (2 * r + 1) + 1) := by
  have : 1 ≤ Nat.log 2 (2 * r + 1) + 1 := by omega
  nlinarith

/-- Iterating the tight Bernoulli split produces a perfect disjoint partition.
Every tracked subset has, in every leaf, between the displayed fixed powers
of its ideal share.  The hypothesis is written in multiplication form so it
can be propagated without any floor or divisibility assumptions. -/
theorem exists_tight_partition
    {κ : Type*} [DecidableEq κ]
    (t : ℕ) (s : Finset ι) (J : Finset κ) (F : κ → Finset ι)
    (hsub : ∀ j ∈ J, F j ⊆ s)
    (hlarge : ∀ j ∈ J,
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
        89 ^ t * (F j).card) :
    ∃ T : PartitionTree ι t,
      T.carrier = s ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦ ∀ j ∈ J,
        89 ^ t * (F j).card ≤ 200 ^ t * (C ∩ F j).card ∧
        200 ^ t * (C ∩ F j).card ≤ 111 ^ t * (F j).card := by
  induction t generalizing s F with
  | zero =>
      refine ⟨.leaf s, rfl, trivial, ?_⟩
      intro j hj
      have hinter : s ∩ F j = F j := Finset.inter_eq_right.mpr (hsub j hj)
      simp [hinter]
  | succ t ih =>
      let Q := 1000 * (Nat.log 2 (2 * J.card + 1) + 1)
      have hQpos : 0 < Q := balancing_threshold_pos J.card
      have hQ200 : 200 ≤ Q := balancing_threshold_ge_two_hundred J.card
      have hlargeSplit : ∀ j ∈ J, Q ≤ (F j).card := by
        intro j hj
        have hp89 : 89 ^ (t + 1) ≤ 200 ^ (t + 1) := by
          exact Nat.pow_le_pow_left (by omega : 89 ≤ 200) (t + 1)
        have hmul : 200 ^ (t + 1) * Q ≤
            200 ^ (t + 1) * (F j).card := by
          calc
            200 ^ (t + 1) * Q = Q * 200 ^ (t + 1) := by ring
            _ ≤ 89 ^ (t + 1) * (F j).card := hlarge j hj
            _ ≤ 200 ^ (t + 1) * (F j).card :=
              Nat.mul_le_mul_right (F j).card hp89
        exact Nat.le_of_mul_le_mul_left hmul (pow_pos (by omega) _)
      obtain ⟨u, v, huv, huvUnion, hsplit⟩ :=
        exists_balanced_bipartition_tight_indexed s J F hsub (by
          intro j hj
          simpa [Q] using hlargeSplit j hj)
      have hratioU : ∀ j ∈ J,
          89 * (F j).card ≤ 200 * (u ∩ F j).card ∧
            200 * (u ∩ F j).card ≤ 111 * (F j).card := by
        intro j hj
        exact tight_split_card_ratios
          (hQ200.trans (hlargeSplit j hj)) (hsplit j hj).1.1
            (hsplit j hj).1.2
      have hratioV : ∀ j ∈ J,
          89 * (F j).card ≤ 200 * (v ∩ F j).card ∧
            200 * (v ∩ F j).card ≤ 111 * (F j).card := by
        intro j hj
        exact tight_split_card_ratios
          (hQ200.trans (hlargeSplit j hj)) (hsplit j hj).2.1
            (hsplit j hj).2.2
      let Fu : κ → Finset ι := fun j ↦ u ∩ F j
      let Fv : κ → Finset ι := fun j ↦ v ∩ F j
      have hsubU : ∀ j ∈ J, Fu j ⊆ u := by
        intro j hj
        exact Finset.inter_subset_left
      have hsubV : ∀ j ∈ J, Fv j ⊆ v := by
        intro j hj
        exact Finset.inter_subset_left
      have hlargeU : ∀ j ∈ J, Q * 200 ^ t ≤
          89 ^ t * (Fu j).card := by
        intro j hj
        have hmul : 200 * (Q * 200 ^ t) ≤
            200 * (89 ^ t * (Fu j).card) := by
          calc
            200 * (Q * 200 ^ t) = Q * 200 ^ (t + 1) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ (t + 1) * (F j).card := hlarge j hj
            _ = 89 ^ t * (89 * (F j).card) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ t * (200 * (Fu j).card) :=
              Nat.mul_le_mul_left _ (hratioU j hj).1
            _ = 200 * (89 ^ t * (Fu j).card) := by ring
        exact Nat.le_of_mul_le_mul_left hmul (by omega)
      have hlargeV : ∀ j ∈ J, Q * 200 ^ t ≤
          89 ^ t * (Fv j).card := by
        intro j hj
        have hmul : 200 * (Q * 200 ^ t) ≤
            200 * (89 ^ t * (Fv j).card) := by
          calc
            200 * (Q * 200 ^ t) = Q * 200 ^ (t + 1) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ (t + 1) * (F j).card := hlarge j hj
            _ = 89 ^ t * (89 * (F j).card) := by
              rw [pow_succ]
              ring
            _ ≤ 89 ^ t * (200 * (Fv j).card) :=
              Nat.mul_le_mul_left _ (hratioV j hj).1
            _ = 200 * (89 ^ t * (Fv j).card) := by ring
        exact Nat.le_of_mul_le_mul_left hmul (by omega)
      obtain ⟨Tu, hTuCarrier, hTuDisj, hTuLeaves⟩ :=
        ih u Fu hsubU (by simpa [Q] using hlargeU)
      obtain ⟨Tv, hTvCarrier, hTvDisj, hTvLeaves⟩ :=
        ih v Fv hsubV (by simpa [Q] using hlargeV)
      let T : PartitionTree ι (t + 1) := .node Tu Tv
      refine ⟨T, ?_, ?_, ?_⟩
      · change Tu.carrier ∪ Tv.carrier = s
        rw [hTuCarrier, hTvCarrier, huvUnion]
      · exact ⟨hTuDisj, hTvDisj, by simpa [hTuCarrier, hTvCarrier] using huv⟩
      · constructor
        · refine (hTuLeaves.and (allLeaves_subset_carrier Tu)).mono ?_
          rintro C ⟨hC, hCsubTu⟩ j hj
          have hCsub : C ⊆ u := by simpa [hTuCarrier] using hCsubTu
          have hinter : C ∩ Fu j = C ∩ F j := by
            ext x
            simp only [Fu, Finset.mem_inter]
            tauto
          have hCj := hC j hj
          rw [hinter] at hCj
          refine ⟨?_, ?_⟩
          · calc
              89 ^ (t + 1) * (F j).card =
                  89 ^ t * (89 * (F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 89 ^ t * (200 * (Fu j).card) :=
                Nat.mul_le_mul_left _ (hratioU j hj).1
              _ = 200 * (89 ^ t * (Fu j).card) := by ring
              _ ≤ 200 * (200 ^ t * (C ∩ F j).card) :=
                Nat.mul_le_mul_left 200 hCj.1
              _ = 200 ^ (t + 1) * (C ∩ F j).card := by
                rw [pow_succ]
                ring
          · calc
              200 ^ (t + 1) * (C ∩ F j).card =
                  200 * (200 ^ t * (C ∩ F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 200 * (111 ^ t * (Fu j).card) :=
                Nat.mul_le_mul_left 200 hCj.2
              _ = 111 ^ t * (200 * (Fu j).card) := by ring
              _ ≤ 111 ^ t * (111 * (F j).card) :=
                Nat.mul_le_mul_left _ (hratioU j hj).2
              _ = 111 ^ (t + 1) * (F j).card := by
                rw [pow_succ]
                ring
        · refine (hTvLeaves.and (allLeaves_subset_carrier Tv)).mono ?_
          rintro C ⟨hC, hCsubTv⟩ j hj
          have hCsub : C ⊆ v := by simpa [hTvCarrier] using hCsubTv
          have hinter : C ∩ Fv j = C ∩ F j := by
            ext x
            simp only [Fv, Finset.mem_inter]
            tauto
          have hCj := hC j hj
          rw [hinter] at hCj
          refine ⟨?_, ?_⟩
          · calc
              89 ^ (t + 1) * (F j).card =
                  89 ^ t * (89 * (F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 89 ^ t * (200 * (Fv j).card) :=
                Nat.mul_le_mul_left _ (hratioV j hj).1
              _ = 200 * (89 ^ t * (Fv j).card) := by ring
              _ ≤ 200 * (200 ^ t * (C ∩ F j).card) :=
                Nat.mul_le_mul_left 200 hCj.1
              _ = 200 ^ (t + 1) * (C ∩ F j).card := by
                rw [pow_succ]
                ring
          · calc
              200 ^ (t + 1) * (C ∩ F j).card =
                  200 * (200 ^ t * (C ∩ F j).card) := by
                    rw [pow_succ]
                    ring
              _ ≤ 200 * (111 ^ t * (Fv j).card) :=
                Nat.mul_le_mul_left 200 hCj.2
              _ = 111 ^ t * (200 * (Fv j).card) := by ring
              _ ≤ 111 ^ t * (111 * (F j).card) :=
                Nat.mul_le_mul_left _ (hratioV j hj).2
              _ = 111 ^ (t + 1) * (F j).card := by
                rw [pow_succ]
                ring

end PartitionTree

/-- Pair two elements at a time, placing the larger of each pair on the
currently lighter side.  This gives a cardinally balanced split whose two
weight sums differ by at most the largest individual weight. -/
theorem exists_weightBalanced_bipartition
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℕ) (M : ℕ)
    (hw : ∀ x ∈ s, w x ≤ M) :
    ∃ T U : Finset ι, Disjoint T U ∧ T ∪ U = s ∧
      T.card ≤ U.card + 1 ∧ U.card ≤ T.card + 1 ∧
      (∑ x ∈ T, w x) ≤ (∑ x ∈ U, w x) + M ∧
      (∑ x ∈ U, w x) ≤ (∑ x ∈ T, w x) + M := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      by_cases hs : s.Nonempty
      · let a := hs.choose
        have haS : a ∈ s := hs.choose_spec
        let s₁ := s.erase a
        by_cases hs₁ : s₁.Nonempty
        · let b := hs₁.choose
          have hbS₁ : b ∈ s₁ := hs₁.choose_spec
          have hbS : b ∈ s := Finset.mem_of_mem_erase hbS₁
          have hba : b ≠ a := (Finset.mem_erase.mp hbS₁).1
          let R := s₁.erase b
          have hRs : R ⊂ s := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
            intro hEq
            have haR : a ∈ R := by simpa [hEq] using haS
            exact (by simpa [R, s₁] using haR)
          have hwR : ∀ x ∈ R, w x ≤ M := by
            intro x hx
            exact hw x (hRs.subset hx)
          obtain ⟨T, U, hTU, hTUR, hcardTU, hcardUT, hsumTU, hsumUT⟩ :=
            ih R hRs hwR
          have hTR : T ⊆ R := by
            intro x hx
            rw [← hTUR]
            exact Finset.mem_union_left U hx
          have hUR : U ⊆ R := by
            intro x hx
            rw [← hTUR]
            exact Finset.mem_union_right T hx
          have haR : a ∉ R := by simp [R, s₁]
          have hbR : b ∉ R := by simp [R]
          have haT : a ∉ T := fun h ↦ haR (hTR h)
          have haU : a ∉ U := fun h ↦ haR (hUR h)
          have hbT : b ∉ T := fun h ↦ hbR (hTR h)
          have hbU : b ∉ U := fun h ↦ hbR (hUR h)
          have hrecoverAB : insert a (insert b R) = s := by
            rw [Finset.insert_erase hbS₁]
            exact Finset.insert_erase haS
          have hrecoverBA : insert b (insert a R) = s := by
            rw [Finset.insert_comm, hrecoverAB]
          have hfinish (x y : ι)
              (hxy : x ≠ y) (hxT : x ∉ T) (hxU : x ∉ U)
              (hyT : y ∉ T) (hyU : y ∉ U)
              (hrecover : insert x (insert y R) = s)
              (hweightTU : (∑ z ∈ T, w z) + w x ≤
                (∑ z ∈ U, w z) + w y + M)
              (hweightUT : (∑ z ∈ U, w z) + w y ≤
                (∑ z ∈ T, w z) + w x + M) :
              ∃ T' U' : Finset ι, Disjoint T' U' ∧ T' ∪ U' = s ∧
                T'.card ≤ U'.card + 1 ∧ U'.card ≤ T'.card + 1 ∧
                (∑ z ∈ T', w z) ≤ (∑ z ∈ U', w z) + M ∧
                (∑ z ∈ U', w z) ≤ (∑ z ∈ T', w z) + M := by
            refine ⟨insert x T, insert y U, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [Finset.disjoint_left]
              intro z hzT hzU
              simp only [Finset.mem_insert] at hzT hzU
              rcases hzT with rfl | hzT
              · rcases hzU with hxy' | hxU'
                · exact hxy hxy'
                · exact hxU hxU'
              · rcases hzU with rfl | hzU
                · exact hyT hzT
                · exact Finset.disjoint_left.mp hTU hzT hzU
            · calc
                insert x T ∪ insert y U = insert x (insert y (T ∪ U)) := by
                  ext z
                  simp only [Finset.mem_union, Finset.mem_insert]
                  tauto
                _ = s := by rw [hTUR, hrecover]
            · simp only [Finset.card_insert_of_notMem hxT,
                Finset.card_insert_of_notMem hyU]
              omega
            · simp only [Finset.card_insert_of_notMem hxT,
                Finset.card_insert_of_notMem hyU]
              omega
            · simpa [Finset.sum_insert, hxT, hyU, add_comm, add_left_comm,
                add_assoc] using hweightTU
            · simpa [Finset.sum_insert, hxT, hyU, add_comm, add_left_comm,
                add_assoc] using hweightUT
          have haM := hw a haS
          have hbM := hw b hbS
          by_cases hsum : (∑ x ∈ T, w x) ≤ ∑ x ∈ U, w x
          · by_cases hwab : w b ≤ w a
            · apply hfinish a b hba.symm haT haU hbT hbU hrecoverAB <;> omega
            · apply hfinish b a hba hbT hbU haT haU hrecoverBA <;> omega
          · have hsum' : (∑ x ∈ U, w x) ≤ ∑ x ∈ T, w x := by omega
            by_cases hwab : w b ≤ w a
            · apply hfinish b a hba hbT hbU haT haU hrecoverBA <;> omega
            · apply hfinish a b hba.symm haT haU hbT hbU hrecoverAB <;> omega
        · have hs₁empty : s₁ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs₁
          have hsEq : s = {a} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨haS, ?_⟩
            intro x hx
            by_contra hxa
            have : x ∈ s₁ := Finset.mem_erase.mpr ⟨hxa, hx⟩
            simpa [hs₁empty] using this
          refine ⟨{a}, ∅, by simp, by simpa using hsEq.symm,
            by simp, by simp, ?_, by simp⟩
          simpa using hw a haS
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        exact ⟨∅, ∅, by simp, by simpa using hsEmpty.symm, by simp⟩

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

/-- Recursive cardinal-and-weight balancing.  Each level contributes at most
one unit of cardinal discrepancy and at most one largest weight; hence the
geometric error `2^t - 1` at a leaf. -/
theorem exists_weightBalanced_partition
    (t : ℕ) (s : Finset ι) (w : ι → ℕ) (M : ℕ)
    (hw : ∀ x ∈ s, w x ≤ M) :
    ∃ T : PartitionTree ι t,
      T.carrier = s ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦
        s.card ≤ 2 ^ t * C.card + (2 ^ t - 1) ∧
        2 ^ t * C.card ≤ s.card + (2 ^ t - 1) ∧
        (∑ x ∈ s, w x) ≤ 2 ^ t * (∑ x ∈ C, w x) + (2 ^ t - 1) * M ∧
        2 ^ t * (∑ x ∈ C, w x) ≤
          (∑ x ∈ s, w x) + (2 ^ t - 1) * M := by
  induction t generalizing s with
  | zero =>
      refine ⟨.leaf s, rfl, trivial, ?_⟩
      simp [AllLeaves]
  | succ t ih =>
      obtain ⟨u, v, huv, huvUnion, hcardUV, hcardVU,
          hsumUV, hsumVU⟩ := exists_weightBalanced_bipartition s w M hw
      have hus : u ⊆ s := by
        intro x hx
        rw [← huvUnion]
        exact Finset.mem_union_left v hx
      have hvs : v ⊆ s := by
        intro x hx
        rw [← huvUnion]
        exact Finset.mem_union_right u hx
      have hwu : ∀ x ∈ u, w x ≤ M := fun x hx ↦ hw x (hus hx)
      have hwv : ∀ x ∈ v, w x ≤ M := fun x hx ↦ hw x (hvs hx)
      obtain ⟨Tu, hTuCarrier, hTuDisj, hTuLeaves⟩ := ih u hwu
      obtain ⟨Tv, hTvCarrier, hTvDisj, hTvLeaves⟩ := ih v hwv
      have hcardS : s.card = u.card + v.card := by
        rw [← huvUnion, Finset.card_union_of_disjoint huv]
      have hsumS : (∑ x ∈ s, w x) =
          (∑ x ∈ u, w x) + ∑ x ∈ v, w x := by
        rw [← huvUnion, Finset.sum_union huv]
      have hcardLowerU : s.card ≤ 2 * u.card + 1 := by omega
      have hcardUpperU : 2 * u.card ≤ s.card + 1 := by omega
      have hcardLowerV : s.card ≤ 2 * v.card + 1 := by omega
      have hcardUpperV : 2 * v.card ≤ s.card + 1 := by omega
      have hsumLowerU : (∑ x ∈ s, w x) ≤
          2 * (∑ x ∈ u, w x) + M := by omega
      have hsumUpperU : 2 * (∑ x ∈ u, w x) ≤
          (∑ x ∈ s, w x) + M := by omega
      have hsumLowerV : (∑ x ∈ s, w x) ≤
          2 * (∑ x ∈ v, w x) + M := by omega
      have hsumUpperV : 2 * (∑ x ∈ v, w x) ≤
          (∑ x ∈ s, w x) + M := by omega
      let T : PartitionTree ι (t + 1) := .node Tu Tv
      refine ⟨T, ?_, ?_, ?_⟩
      · change Tu.carrier ∪ Tv.carrier = s
        rw [hTuCarrier, hTvCarrier, huvUnion]
      · exact ⟨hTuDisj, hTvDisj, by simpa [hTuCarrier, hTvCarrier] using huv⟩
      · constructor
        · refine hTuLeaves.mono ?_
          intro C hC
          have hp : 0 < 2 ^ t := pow_pos (by omega) _
          have hsub : 2 ^ t - 1 + 1 = 2 ^ t := Nat.sub_add_cancel (by omega)
          have herr : 2 * (2 ^ t - 1) + 1 = 2 ^ t * 2 - 1 := by omega
          have herrM : 2 * ((2 ^ t - 1) * M) + M =
              (2 ^ t * 2 - 1) * M := by
            calc
              2 * ((2 ^ t - 1) * M) + M =
                  (2 * (2 ^ t - 1) + 1) * M := by ring
              _ = (2 ^ t * 2 - 1) * M := by rw [herr]
          simp only [pow_succ]
          refine ⟨?_, ?_, ?_, ?_⟩
          · calc
              s.card ≤ 2 * u.card + 1 := hcardLowerU
              _ ≤ 2 * (2 ^ t * C.card + (2 ^ t - 1)) + 1 :=
                Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC.1) 1
              _ = 2 ^ t * 2 * C.card + (2 ^ t * 2 - 1) := by
                calc
                  2 * (2 ^ t * C.card + (2 ^ t - 1)) + 1 =
                      2 * (2 ^ t * C.card) +
                        (2 * (2 ^ t - 1) + 1) := by ring
                  _ = 2 * (2 ^ t * C.card) + (2 ^ t * 2 - 1) := by rw [herr]
                  _ = 2 ^ t * 2 * C.card + (2 ^ t * 2 - 1) := by ring
          · calc
              2 ^ t * 2 * C.card = 2 * (2 ^ t * C.card) := by ring
              _ ≤ 2 * (u.card + (2 ^ t - 1)) :=
                Nat.mul_le_mul_left 2 hC.2.1
              _ = 2 * u.card + 2 * (2 ^ t - 1) := by ring
              _ ≤ (s.card + 1) + 2 * (2 ^ t - 1) :=
                Nat.add_le_add_right hcardUpperU _
              _ = s.card + (2 ^ t * 2 - 1) := by omega
          · calc
              (∑ x ∈ s, w x) ≤ 2 * (∑ x ∈ u, w x) + M := hsumLowerU
              _ ≤ 2 * (2 ^ t * (∑ x ∈ C, w x) +
                    (2 ^ t - 1) * M) + M :=
                Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC.2.2.1) M
              _ = 2 ^ t * 2 * (∑ x ∈ C, w x) +
                    (2 ^ t * 2 - 1) * M := by
                calc
                  2 * (2 ^ t * (∑ x ∈ C, w x) +
                      (2 ^ t - 1) * M) + M =
                      2 * (2 ^ t * (∑ x ∈ C, w x)) +
                        (2 * ((2 ^ t - 1) * M) + M) := by ring
                  _ = 2 * (2 ^ t * (∑ x ∈ C, w x)) +
                        (2 ^ t * 2 - 1) * M := by rw [herrM]
                  _ = 2 ^ t * 2 * (∑ x ∈ C, w x) +
                        (2 ^ t * 2 - 1) * M := by ring
          · calc
              2 ^ t * 2 * (∑ x ∈ C, w x) =
                  2 * (2 ^ t * (∑ x ∈ C, w x)) := by ring
              _ ≤ 2 * ((∑ x ∈ u, w x) + (2 ^ t - 1) * M) :=
                Nat.mul_le_mul_left 2 hC.2.2.2
              _ = 2 * (∑ x ∈ u, w x) +
                    2 * ((2 ^ t - 1) * M) := by ring
              _ ≤ ((∑ x ∈ s, w x) + M) +
                    2 * ((2 ^ t - 1) * M) :=
                Nat.add_le_add_right hsumUpperU _
              _ = (∑ x ∈ s, w x) + (2 ^ t * 2 - 1) * M := by
                calc
                  (∑ x ∈ s, w x) + M + 2 * ((2 ^ t - 1) * M) =
                      (∑ x ∈ s, w x) +
                        (2 * ((2 ^ t - 1) * M) + M) := by omega
                  _ = (∑ x ∈ s, w x) + (2 ^ t * 2 - 1) * M := by
                    rw [herrM]
        · refine hTvLeaves.mono ?_
          intro C hC
          have hp : 0 < 2 ^ t := pow_pos (by omega) _
          have hsub : 2 ^ t - 1 + 1 = 2 ^ t := Nat.sub_add_cancel (by omega)
          have herr : 2 * (2 ^ t - 1) + 1 = 2 ^ t * 2 - 1 := by omega
          have herrM : 2 * ((2 ^ t - 1) * M) + M =
              (2 ^ t * 2 - 1) * M := by
            calc
              2 * ((2 ^ t - 1) * M) + M =
                  (2 * (2 ^ t - 1) + 1) * M := by ring
              _ = (2 ^ t * 2 - 1) * M := by rw [herr]
          simp only [pow_succ]
          refine ⟨?_, ?_, ?_, ?_⟩
          · calc
              s.card ≤ 2 * v.card + 1 := hcardLowerV
              _ ≤ 2 * (2 ^ t * C.card + (2 ^ t - 1)) + 1 :=
                Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC.1) 1
              _ = 2 ^ t * 2 * C.card + (2 ^ t * 2 - 1) := by
                calc
                  2 * (2 ^ t * C.card + (2 ^ t - 1)) + 1 =
                      2 * (2 ^ t * C.card) +
                        (2 * (2 ^ t - 1) + 1) := by ring
                  _ = 2 * (2 ^ t * C.card) + (2 ^ t * 2 - 1) := by rw [herr]
                  _ = 2 ^ t * 2 * C.card + (2 ^ t * 2 - 1) := by ring
          · calc
              2 ^ t * 2 * C.card = 2 * (2 ^ t * C.card) := by ring
              _ ≤ 2 * (v.card + (2 ^ t - 1)) :=
                Nat.mul_le_mul_left 2 hC.2.1
              _ = 2 * v.card + 2 * (2 ^ t - 1) := by ring
              _ ≤ (s.card + 1) + 2 * (2 ^ t - 1) :=
                Nat.add_le_add_right hcardUpperV _
              _ = s.card + (2 ^ t * 2 - 1) := by omega
          · calc
              (∑ x ∈ s, w x) ≤ 2 * (∑ x ∈ v, w x) + M := hsumLowerV
              _ ≤ 2 * (2 ^ t * (∑ x ∈ C, w x) +
                    (2 ^ t - 1) * M) + M :=
                Nat.add_le_add_right (Nat.mul_le_mul_left 2 hC.2.2.1) M
              _ = 2 ^ t * 2 * (∑ x ∈ C, w x) +
                    (2 ^ t * 2 - 1) * M := by
                calc
                  2 * (2 ^ t * (∑ x ∈ C, w x) +
                      (2 ^ t - 1) * M) + M =
                      2 * (2 ^ t * (∑ x ∈ C, w x)) +
                        (2 * ((2 ^ t - 1) * M) + M) := by ring
                  _ = 2 * (2 ^ t * (∑ x ∈ C, w x)) +
                        (2 ^ t * 2 - 1) * M := by rw [herrM]
                  _ = 2 ^ t * 2 * (∑ x ∈ C, w x) +
                        (2 ^ t * 2 - 1) * M := by ring
          · calc
              2 ^ t * 2 * (∑ x ∈ C, w x) =
                  2 * (2 ^ t * (∑ x ∈ C, w x)) := by ring
              _ ≤ 2 * ((∑ x ∈ v, w x) + (2 ^ t - 1) * M) :=
                Nat.mul_le_mul_left 2 hC.2.2.2
              _ = 2 * (∑ x ∈ v, w x) +
                    2 * ((2 ^ t - 1) * M) := by ring
              _ ≤ ((∑ x ∈ s, w x) + M) +
                    2 * ((2 ^ t - 1) * M) :=
                Nat.add_le_add_right hsumUpperV _
              _ = (∑ x ∈ s, w x) + (2 ^ t * 2 - 1) * M := by
                calc
                  (∑ x ∈ s, w x) + M + 2 * ((2 ^ t - 1) * M) =
                      (∑ x ∈ s, w x) +
                        (2 * ((2 ^ t - 1) * M) + M) := by omega
                  _ = (∑ x ∈ s, w x) + (2 ^ t * 2 - 1) * M := by
                    rw [herrM]

end PartitionTree

/-! ### Bounded integer subset sums and modular pivots -/

noncomputable def boundedSubsetSum (C : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (C.powerset.filter fun H ↦ H.card ≤ k).image fun H ↦ ∑ h ∈ H, h

lemma mem_boundedSubsetSum_iff {C : Finset ℕ} {k u : ℕ} :
    u ∈ boundedSubsetSum C k ↔
      ∃ H : Finset ℕ, H ⊆ C ∧ H.card ≤ k ∧ u = ∑ h ∈ H, h := by
  classical
  simp only [boundedSubsetSum, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨H, ⟨hHC, hHk⟩, rfl⟩
    exact ⟨H, hHC, hHk, rfl⟩
  · rintro ⟨H, hHC, hHk, rfl⟩
    exact ⟨H, ⟨hHC, hHk⟩, rfl⟩

@[simp] lemma zero_mem_boundedSubsetSum (C : Finset ℕ) (k : ℕ) :
    0 ∈ boundedSubsetSum C k := by
  rw [mem_boundedSubsetSum_iff]
  exact ⟨∅, by simp⟩

lemma boundedSubsetSum_subset_subsetSum (C : Finset ℕ) (k : ℕ) :
    boundedSubsetSum C k ⊆ C.subsetSum := by
  intro u hu
  obtain ⟨H, hHC, hHk, rfl⟩ := mem_boundedSubsetSum_iff.mp hu
  exact Finset.mem_subsetSum_iff.mpr ⟨H, hHC, rfl⟩

lemma boundedSubsetSum_subset_Icc_sum (C : Finset ℕ) (k : ℕ) :
    boundedSubsetSum C k ⊆ Finset.Icc 0 (∑ c ∈ C, c) := by
  intro u hu
  obtain ⟨H, hHC, hHk, rfl⟩ := mem_boundedSubsetSum_iff.mp hu
  rw [Finset.mem_Icc]
  exact ⟨Nat.zero_le _, Finset.sum_le_sum_of_subset hHC⟩

lemma boundedSubsetSum_le_sum_pivots
    {C P : Finset ℕ} {k u : ℕ}
    (hP : P.Nonempty) (hk : k ≤ P.card)
    (horder : ∀ c ∈ C, ∀ p ∈ P, c ≤ p)
    (hu : u ∈ boundedSubsetSum C k) : u ≤ ∑ p ∈ P, p := by
  obtain ⟨H, hHC, hHk, rfl⟩ := mem_boundedSubsetSum_iff.mp hu
  let p₀ := P.min' hP
  have hp₀ : p₀ ∈ P := P.min'_mem hP
  have hsumH : (∑ h ∈ H, h) ≤ H.card * p₀ := by
    calc
      (∑ h ∈ H, h) ≤ ∑ _h ∈ H, p₀ := by
        apply Finset.sum_le_sum
        intro h hh
        exact horder h (hHC hh) p₀ hp₀
      _ = H.card * p₀ := by simp
  have hsumP : P.card * p₀ ≤ ∑ p ∈ P, p := by
    calc
      P.card * p₀ = ∑ _p ∈ P, p₀ := by simp
      _ ≤ ∑ p ∈ P, p := by
        apply Finset.sum_le_sum
        intro p hp
        exact P.min'_le p hp
  exact hsumH.trans ((Nat.mul_le_mul_right p₀ (hHk.trans hk)).trans hsumP)

lemma exists_preimage_finset_of_subset_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset α) (f : α → β) (hinj : Set.InjOn f C)
    (G : Finset β) (hG : G ⊆ C.image f) :
    ∃ H : Finset α, H ⊆ C ∧ H.card = G.card ∧ H.image f = G := by
  let H := C.filter fun c ↦ f c ∈ G
  have hHC : H ⊆ C := Finset.filter_subset _ _
  have himage : H.image f = G := by
    ext g
    simp only [H, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨c, ⟨hcC, hfcG⟩, rfl⟩
      exact hfcG
    · intro hg
      obtain ⟨c, hcC, hcg⟩ := Finset.mem_image.mp (hG hg)
      exact ⟨c, ⟨hcC, hcg ▸ hg⟩, hcg⟩
  refine ⟨H, hHC, ?_, himage⟩
  rw [← himage, Finset.card_image_iff.mpr (hinj.mono hHC)]

/-- A finite subset of an image has a set of pairwise distinct representatives.
No injectivity hypothesis on the original map is needed: one representative
is chosen when each new image point is inserted. -/
lemma exists_preimage_finset_of_subset_image'
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset α) (f : α → β) (G : Finset β)
    (hG : G ⊆ C.image f) :
    ∃ H : Finset α, H ⊆ C ∧ H.card = G.card ∧ H.image f = G := by
  classical
  induction G using Finset.induction with
  | empty => exact ⟨∅, by simp⟩
  | @insert g G hg ih =>
      have hGsub : G ⊆ C.image f :=
        fun x hx ↦ hG (Finset.mem_insert_of_mem hx)
      obtain ⟨H, hHC, hHcard, hHimage⟩ := ih hGsub
      obtain ⟨c, hcC, hfc⟩ := Finset.mem_image.mp
        (hG (Finset.mem_insert_self g G))
      have hcH : c ∉ H := by
        intro hc
        apply hg
        rw [← hHimage]
        exact Finset.mem_image.mpr ⟨c, hc, hfc⟩
      refine ⟨insert c H, Finset.insert_subset hcC hHC, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hcH, hHcard,
          Finset.card_insert_of_notMem hg]
      · rw [Finset.image_insert, hfc, hHimage]

lemma natCast_zmod_injOn_of_lt {b : ℕ} [NeZero b] {C : Finset ℕ}
    (hC : ∀ c ∈ C, c < b) : Set.InjOn (fun c : ℕ ↦ (c : ZMod b)) C := by
  intro x hx y hy hxy
  have hmod := (ZMod.natCast_eq_natCast_iff' x y b).mp hxy
  simpa [Nat.mod_eq_of_lt (hC x hx), Nat.mod_eq_of_lt (hC y hy)] using hmod

/-- Reduction modulo `p`, together with the quotient by `p`, is injective on
an interval.  Consequently every occupied residue has at most `N / p + 1`
representatives in `[1,N]`. -/
lemma card_le_div_add_one_mul_card_image_zmod
    {C : Finset ℕ} {N p : ℕ} [NeZero p] (hp : 0 < p)
    (hC : C ⊆ Finset.Icc 1 N) :
    C.card ≤ (N / p + 1) *
      (C.image fun c : ℕ ↦ (c : ZMod p)).card := by
  classical
  let R := C.image fun c : ℕ ↦ (c : ZMod p)
  let T := (Finset.range (N / p + 1)).product R
  let f : ℕ → ℕ × ZMod p := fun c ↦ (c / p, (c : ZMod p))
  have hmaps : ∀ c ∈ C, f c ∈ T := by
    intro c hc
    have hcN := (Finset.mem_Icc.mp (hC hc)).2
    rw [show T = (Finset.range (N / p + 1)) ×ˢ R from rfl,
      Finset.mem_product]
    constructor
    · rw [Finset.mem_range]
      have hq : c / p ≤ N / p := Nat.div_le_div_right hcN
      simpa [f] using Nat.lt_succ_of_le hq
    · change (c : ZMod p) ∈ C.image fun c : ℕ ↦ (c : ZMod p)
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hinj : Set.InjOn f C := by
    intro x hx y hy hxy
    have hdiv : x / p = y / p := congrArg Prod.fst hxy
    have hcast : (x : ZMod p) = (y : ZMod p) := congrArg Prod.snd hxy
    have hmod : x % p = y % p := by
      simpa [ZMod.val_natCast] using congrArg ZMod.val hcast
    calc
      x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
      _ = y % p + p * (y / p) := by rw [hmod, hdiv]
      _ = y := Nat.mod_add_div y p
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [T, R] using hcard

/-- The same quotient--residue injection, restricted to elements not
divisible by a divisor of the modulus. -/
lemma card_filter_not_dvd_le_mul_card_image_filter
    {C : Finset ℕ} {N p e : ℕ} [NeZero p] (hp : 0 < p)
    (hC : C ⊆ Finset.Icc 1 N) (hep : e ∣ p) :
    (C.filter fun c ↦ ¬e ∣ c).card ≤
      (N / p + 1) *
        ((C.image fun c : ℕ ↦ (c : ZMod p)).filter
          fun r ↦ ¬e ∣ r.val).card := by
  classical
  let D := C.filter fun c ↦ ¬e ∣ c
  let R := (C.image fun c : ℕ ↦ (c : ZMod p)).filter
    fun r ↦ ¬e ∣ r.val
  let T := (Finset.range (N / p + 1)).product R
  let f : ℕ → ℕ × ZMod p := fun c ↦ (c / p, (c : ZMod p))
  have hmaps : ∀ c ∈ D, f c ∈ T := by
    intro c hc
    have hc' := Finset.mem_filter.mp hc
    have hcN := (Finset.mem_Icc.mp (hC hc'.1)).2
    rw [show T = (Finset.range (N / p + 1)) ×ˢ R from rfl,
      Finset.mem_product]
    constructor
    · rw [Finset.mem_range]
      have hq : c / p ≤ N / p := Nat.div_le_div_right hcN
      simpa [f] using Nat.lt_succ_of_le hq
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · change (c : ZMod p) ∈ C.image fun c : ℕ ↦ (c : ZMod p)
        exact Finset.mem_image.mpr ⟨c, hc'.1, rfl⟩
      · intro heval
        apply hc'.2
        have hemod : e ∣ c % p := by
          simpa [f, ZMod.val_natCast] using heval
        rw [← Nat.mod_add_div c p]
        exact Nat.dvd_add hemod (dvd_mul_of_dvd_left hep _)
  have hinj : Set.InjOn f D := by
    intro x hx y hy hxy
    have hdiv : x / p = y / p := congrArg Prod.fst hxy
    have hcast : (x : ZMod p) = (y : ZMod p) := congrArg Prod.snd hxy
    have hmod : x % p = y % p := by
      simpa [ZMod.val_natCast] using congrArg ZMod.val hcast
    calc
      x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
      _ = y % p + p * (y / p) := by rw [hmod, hdiv]
      _ = y := Nat.mod_add_div y p
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [T, R, D] using hcard

lemma card_filter_core_le_card_image_filter
    {D C : Finset ℕ} {p e : ℕ} [NeZero p]
    (hDC : D ⊆ C) (hDlt : ∀ d ∈ D, d < p) (hep : e ∣ p) :
    (D.filter fun d ↦ ¬e ∣ d).card ≤
      ((C.image fun c : ℕ ↦ (c : ZMod p)).filter
        fun r ↦ ¬e ∣ r.val).card := by
  classical
  let D' := D.filter fun d ↦ ¬e ∣ d
  let R := (C.image fun c : ℕ ↦ (c : ZMod p)).filter
    fun r ↦ ¬e ∣ r.val
  have hmaps : ∀ d ∈ D', (d : ZMod p) ∈ R := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    rw [show R = (C.image fun c : ℕ ↦ (c : ZMod p)).filter
      (fun r ↦ ¬e ∣ r.val) from rfl, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨d, hDC hd'.1, rfl⟩, ?_⟩
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hDlt d hd'.1)] using hd'.2
  have hinj : Set.InjOn (fun d : ℕ ↦ (d : ZMod p)) D' :=
    (natCast_zmod_injOn_of_lt hDlt).mono (Finset.filter_subset _ _)
  have hcard := Finset.card_le_card_of_injOn
    (fun d : ℕ ↦ (d : ZMod p)) hmaps hinj
  simpa [D', R] using hcard

/-- A lower collision-free pool and an upper collision-controlled pool can
jointly certify every divisor inequality required by the modular phase
machine. -/
lemma phaseDiverse_of_split_witnesses
    {D U : Finset ℕ} {N p : ℕ} [NeZero p] (hp : 0 < p)
    (hDlt : ∀ d ∈ D, d < p) (hU : U ⊆ Finset.Icc 1 N)
    (hwitness : ∀ e : ℕ, 1 < e → e ∣ p →
      e * ((D ∪ U).image fun c : ℕ ↦ (c : ZMod p)).card ≤ 2 * p →
      e - 1 ≤ (D.filter fun d ↦ ¬e ∣ d).card ∨
        (N / p + 1) * (e - 1) ≤
          (U.filter fun u ↦ ¬e ∣ u).card) :
    PhaseDiverse hp ((D ∪ U).image fun c : ℕ ↦ (c : ZMod p)) := by
  classical
  apply phaseDiverse_of_bounded hp
  intro e he hep hecard
  rcases hwitness e he hep hecard with hlow | hupp
  · exact hlow.trans (card_filter_core_le_card_image_filter
      (Finset.subset_union_left (s₁ := D) (s₂ := U)) hDlt hep)
  · have hcollision := card_filter_not_dvd_le_mul_card_image_filter hp hU hep
    let RU := (U.image fun u : ℕ ↦ (u : ZMod p)).filter
      fun r ↦ ¬e ∣ r.val
    let R := ((D ∪ U).image fun c : ℕ ↦ (c : ZMod p)).filter
      fun r ↦ ¬e ∣ r.val
    have hRU : RU ⊆ R := by
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      rw [show R = ((D ∪ U).image fun c : ℕ ↦ (c : ZMod p)).filter
        (fun r ↦ ¬e ∣ r.val) from rfl, Finset.mem_filter]
      refine ⟨?_, hr'.2⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr'.1
      exact Finset.mem_image.mpr
        ⟨u, Finset.mem_union_right D hu, rfl⟩
    have hqpos : 0 < N / p + 1 := Nat.succ_pos _
    have hmul : (N / p + 1) * (e - 1) ≤
        (N / p + 1) * R.card := by
      calc
        (N / p + 1) * (e - 1) ≤
            (U.filter fun u ↦ ¬e ∣ u).card := hupp
        _ ≤ (N / p + 1) * RU.card := by simpa [RU] using hcollision
        _ ≤ (N / p + 1) * R.card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hRU)
    exact Nat.le_of_mul_le_mul_left hmul hqpos

/-- A collision-free core below the modulus gives a direct lower bound for
the number of occupied residues of a larger base set. -/
lemma card_core_le_card_image_zmod
    {D C : Finset ℕ} {p : ℕ} [NeZero p]
    (hDC : D ⊆ C) (hDlt : ∀ d ∈ D, d < p) :
    D.card ≤ (C.image fun c : ℕ ↦ (c : ZMod p)).card := by
  have hinj := natCast_zmod_injOn_of_lt hDlt
  calc
    D.card = (D.image fun d : ℕ ↦ (d : ZMod p)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (C.image fun c : ℕ ↦ (c : ZMod p)).card :=
      Finset.card_le_card (Finset.image_subset_image hDC)

/-- Every residue produced after `k` modular phases has an integer witness
using at most `k` members of the original collision-free lower pool. -/
lemma modularPhaseSums_subset_bounded_image
    {b : ℕ} [NeZero b] (hb : 0 < b) (C : Finset ℕ)
    (hC : ∀ c ∈ C, c < b)
    (R₀ : Finset (ZMod b)) (hR₀ : R₀ = C.image fun c : ℕ ↦ (c : ZMod b))
    (hdiverse : PhaseDiverse hb R₀) {k : ℕ} (hk : k ≤ R₀.card) :
    modularPhaseSums hb R₀ {0} (by simp) hdiverse k ⊆
      (boundedSubsetSum C k).image fun u : ℕ ↦ (u : ZMod b) := by
  classical
  intro z hz
  rw [modularPhaseSums, Finset.mem_add] at hz
  obtain ⟨z₀, hz₀, v, hv, hzEq⟩ := hz
  have hz₀eq : z₀ = 0 := by simpa using hz₀
  subst z₀
  simp only [zero_add] at hzEq
  rw [Finset.mem_subsetSum_iff] at hv
  obtain ⟨G, hGused, hGsum⟩ := hv
  have hGR₀ : G ⊆ R₀ := hGused.trans Finset.sdiff_subset
  have hinj := natCast_zmod_injOn_of_lt hC
  obtain ⟨H, hHC, hHcard, hHimage⟩ :=
    exists_preimage_finset_of_subset_image C
      (fun c : ℕ ↦ (c : ZMod b)) hinj G (by simpa [hR₀] using hGR₀)
  have husedCard :
      (R₀ \ modularRemainder hb R₀ {0} (by simp) hdiverse k).card = k :=
    card_used_modularRemainder hb R₀ {0} (by simp) hdiverse hk
  have hHk : H.card ≤ k := by
    rw [hHcard, ← husedCard]
    exact Finset.card_le_card hGused
  let u := ∑ h ∈ H, h
  have huBounded : u ∈ boundedSubsetSum C k :=
    mem_boundedSubsetSum_iff.mpr ⟨H, hHC, hHk, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨u, huBounded, ?_⟩
  rw [← hzEq, ← hGsum, ← hHimage]
  simp only [u]
  rw [Finset.sum_image (hinj.mono hHC)]
  push_cast
  rfl

/-- The witness-lifting statement above remains valid when several integers
have the same residue.  The modular recursion uses each residue at most once,
so choosing one representative of every used residue preserves the bound on
the number of summands. -/
lemma modularPhaseSums_subset_bounded_image'
    {b : ℕ} [NeZero b] (hb : 0 < b) (C : Finset ℕ)
    (R₀ : Finset (ZMod b)) (hR₀ : R₀ = C.image fun c : ℕ ↦ (c : ZMod b))
    (hdiverse : PhaseDiverse hb R₀) {k : ℕ} (hk : k ≤ R₀.card) :
    modularPhaseSums hb R₀ {0} (by simp) hdiverse k ⊆
      (boundedSubsetSum C k).image fun u : ℕ ↦ (u : ZMod b) := by
  classical
  intro z hz
  rw [modularPhaseSums, Finset.mem_add] at hz
  obtain ⟨z₀, hz₀, v, hv, hzEq⟩ := hz
  have hz₀eq : z₀ = 0 := by simpa using hz₀
  subst z₀
  simp only [zero_add] at hzEq
  rw [Finset.mem_subsetSum_iff] at hv
  obtain ⟨G, hGused, hGsum⟩ := hv
  have hGR₀ : G ⊆ R₀ := hGused.trans Finset.sdiff_subset
  obtain ⟨H, hHC, hHcard, hHimage⟩ :=
    exists_preimage_finset_of_subset_image' C
      (fun c : ℕ ↦ (c : ZMod b)) G (by simpa [hR₀] using hGR₀)
  have husedCard :
      (R₀ \ modularRemainder hb R₀ {0} (by simp) hdiverse k).card = k :=
    card_used_modularRemainder hb R₀ {0} (by simp) hdiverse hk
  have hHk : H.card ≤ k := by
    rw [hHcard, ← husedCard]
    exact Finset.card_le_card hGused
  let u := ∑ h ∈ H, h
  have huBounded : u ∈ boundedSubsetSum C k :=
    mem_boundedSubsetSum_iff.mpr ⟨H, hHC, hHk, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨u, huBounded, ?_⟩
  rw [← hzEq, ← hGsum, ← hHimage]
  simp only [u]
  have hinjH : Set.InjOn (fun c : ℕ ↦ (c : ZMod b)) H := by
    apply Finset.card_image_iff.mp
    rw [hHimage, hHcard]
  rw [Finset.sum_image hinjH]
  push_cast
  rfl

noncomputable def natAddTranslate (b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x ↦ x + b

lemma card_union_natAddTranslate (b : ℕ) (S : Finset ℕ) :
    (S ∪ natAddTranslate b S).card =
      S.card + (natAddTranslate b S \ S).card := by
  have h := Finset.card_sdiff_add_card (natAddTranslate b S) S
  rw [Finset.union_comm] at h
  omega

/-- Adding the integer modulus creates at least one new sum in every residue
class already occupied by `S`. -/
lemma card_add_modulus_growth {b : ℕ} [NeZero b] (hb : 0 < b)
    (S : Finset ℕ) :
    S.card + (S.image fun x : ℕ ↦ (x : ZMod b)).card ≤
      (S ∪ natAddTranslate b S).card := by
  classical
  let R : Finset (ZMod b) := S.image fun x : ℕ ↦ (x : ZMod b)
  let fiber : R → Finset ℕ := fun r ↦
    Finset.filter (fun x : ℕ ↦ (x : ZMod b) = r.1) S
  have hfiber (r : R) : (fiber r).Nonempty := by
    obtain ⟨x, hxS, hxr⟩ := Finset.mem_image.mp r.2
    refine ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩⟩
    exact hxr
  let pick (r : R) := (fiber r).max' (hfiber r)
  let f : R → ℕ := fun r ↦ pick r + b
  have hmaps : ∀ r ∈ R.attach, f r ∈ natAddTranslate b S \ S := by
    intro r hr
    have hpickFiber : pick r ∈ fiber r := (fiber r).max'_mem (hfiber r)
    have hpickS : pick r ∈ S := (Finset.mem_filter.mp hpickFiber).1
    have hpickCast : (pick r : ZMod b) = r.1 :=
      (Finset.mem_filter.mp hpickFiber).2
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_image.mpr ⟨pick r, hpickS, rfl⟩
    · intro hnewS
      have hcast : ((pick r + b : ℕ) : ZMod b) = r.1 := by
        simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using hpickCast
      have hnewFiber : pick r + b ∈ fiber r :=
        Finset.mem_filter.mpr ⟨hnewS, hcast⟩
      have hle := (fiber r).le_max' (pick r + b) hnewFiber
      have hle' : pick r + b ≤ pick r := by simpa [pick] using hle
      omega
  have hinj : Set.InjOn f R.attach := by
    intro r hr q hq heq
    apply Subtype.ext
    have hpickEq : pick r = pick q := Nat.add_right_cancel heq
    have hrmem := (Finset.mem_filter.mp ((fiber r).max'_mem (hfiber r))).2
    have hqmem := (Finset.mem_filter.mp ((fiber q).max'_mem (hfiber q))).2
    calc
      r.1 = (pick r : ZMod b) := hrmem.symm
      _ = (pick q : ZMod b) := by rw [hpickEq]
      _ = q.1 := hqmem
  have hnew : R.card ≤ (natAddTranslate b S \ S).card := by
    rw [← Finset.card_attach]
    exact Finset.card_le_card_of_injOn f hmaps hinj
  rw [card_union_natAddTranslate]
  exact Nat.add_le_add_left hnew S.card

lemma nat_subsetSum_insert_eq (P : Finset ℕ) (b : ℕ) (hbP : b ∉ P) :
    (insert b P).subsetSum =
      P.subsetSum ∪ natAddTranslate b P.subsetSum := by
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hQ, hsum⟩ := Finset.mem_subsetSum_iff.mp hx
    by_cases hbQ : b ∈ Q
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨∑ q ∈ Q.erase b, q, ?_, ?_⟩
      · apply Finset.mem_subsetSum_iff.mpr
        refine ⟨Q.erase b, ?_, rfl⟩
        intro q hq
        exact (Finset.mem_insert.mp (hQ (Finset.mem_of_mem_erase hq))).resolve_left
          (fun h ↦ (Finset.mem_erase.mp hq).1 h)
      · have hsumErase := Finset.sum_erase_add Q id hbQ
        simp only [id_eq] at hsumErase
        omega
    · apply Finset.mem_union_left
      apply Finset.mem_subsetSum_iff.mpr
      refine ⟨Q, ?_, hsum⟩
      intro q hq
      exact (Finset.mem_insert.mp (hQ hq)).resolve_left (fun h ↦ hbQ (h ▸ hq))
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨Q, hQP, hsum⟩ := Finset.mem_subsetSum_iff.mp hx
      apply Finset.mem_subsetSum_iff.mpr
      exact ⟨Q, hQP.trans (Finset.subset_insert b P), hsum⟩
    · obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
      obtain ⟨Q, hQP, hsum⟩ := Finset.mem_subsetSum_iff.mp hu
      have hbQ : b ∉ Q := fun hbQ ↦ hbP (hQP hbQ)
      apply Finset.mem_subsetSum_iff.mpr
      refine ⟨insert b Q, Finset.insert_subset_insert b hQP, ?_⟩
      rw [Finset.sum_insert hbQ]
      omega

noncomputable def pivotExtended (S P : Finset ℕ) : Finset ℕ :=
  S + P.subsetSum

lemma pivotExtended_empty (S : Finset ℕ) : pivotExtended S ∅ = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, z, hz, hsum⟩ := Finset.mem_add.mp hx
    obtain ⟨Q, hQ, hQsum⟩ := Finset.mem_subsetSum_iff.mp hz
    have hQempty : Q = ∅ := by
      exact Finset.Subset.antisymm hQ (Finset.empty_subset Q)
    have hz0 : z = 0 := by
      subst Q
      simpa using hQsum.symm
    have hsx : s = x := by omega
    simpa [hsx] using hs
  · intro hx
    apply Finset.mem_add.mpr
    exact ⟨x, hx, 0, Finset.zero_mem_subsetSum, by omega⟩

lemma pivotExtended_insert (S P : Finset ℕ) (b : ℕ) (hbP : b ∉ P) :
    pivotExtended S (insert b P) =
      pivotExtended S P ∪ natAddTranslate b (pivotExtended S P) := by
  rw [pivotExtended, nat_subsetSum_insert_eq P b hbP, Finset.add_union]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, u, hu, hsum⟩ := Finset.mem_add.mp hx
    obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp hu
    apply Finset.mem_image.mpr
    refine ⟨s + v, Finset.mem_add.mpr ⟨s, hs, v, hv, rfl⟩, ?_⟩
    omega
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨s, hs, v, hv, hsv⟩ := Finset.mem_add.mp hy
    apply Finset.mem_add.mpr
    refine ⟨s, hs, v + b, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨v, hv, rfl⟩
    · omega

lemma subset_pivotExtended_left (S P : Finset ℕ) : S ⊆ pivotExtended S P := by
  intro s hs
  exact Finset.mem_add.mpr ⟨s, hs, 0, Finset.zero_mem_subsetSum, by omega⟩

/-- Repeatedly adjoining positive pivots adds at least the sum of the occupied
residue counts of the fixed base set. -/
lemma card_pivotExtended_lower
    (S P : Finset ℕ) (hPpos : ∀ b ∈ P, 0 < b)
    (hcover : ∀ b ∈ P,
      b ≤ 4 * (S.image fun x : ℕ ↦ (x : ZMod b)).card) :
    S.card + ∑ b ∈ P, b / 4 ≤ (pivotExtended S P).card := by
  classical
  induction P using Finset.induction with
  | empty => simp [pivotExtended_empty]
  | @insert b P hbP ih =>
      have hb : 0 < b := hPpos b (Finset.mem_insert_self _ _)
      letI : NeZero b := ⟨hb.ne'⟩
      have hposP : ∀ a ∈ P, 0 < a := by
        intro a ha
        exact hPpos a (Finset.mem_insert_of_mem ha)
      have hcoverP : ∀ a ∈ P,
          a ≤ 4 * (S.image fun x : ℕ ↦ (x : ZMod a)).card := by
        intro a ha
        exact hcover a (Finset.mem_insert_of_mem ha)
      have hIH := ih hposP hcoverP
      let T := pivotExtended S P
      have hSsubT : S ⊆ T := subset_pivotExtended_left S P
      have hres : (S.image fun x : ℕ ↦ (x : ZMod b)).card ≤
          (T.image fun x : ℕ ↦ (x : ZMod b)).card := by
        apply Finset.card_le_card
        exact Finset.image_subset_image hSsubT
      have hquarter : b / 4 ≤
          (T.image fun x : ℕ ↦ (x : ZMod b)).card := by
        have := hcover b (Finset.mem_insert_self _ _)
        omega
      have hgrowth := card_add_modulus_growth hb T
      rw [pivotExtended_insert S P b hbP]
      rw [Finset.sum_insert hbP]
      change S.card + (b / 4 + ∑ p ∈ P, p / 4) ≤
        (T ∪ natAddTranslate b T).card
      calc
        S.card + (b / 4 + ∑ p ∈ P, p / 4) =
            (S.card + ∑ p ∈ P, p / 4) + b / 4 := by ring
        _ ≤ T.card + b / 4 := Nat.add_le_add_right hIH _
        _ ≤ T.card + (T.image fun x : ℕ ↦ (x : ZMod b)).card :=
          Nat.add_le_add_left hquarter _
        _ ≤ (T ∪ natAddTranslate b T).card := hgrowth

lemma sum_le_eight_sum_div_four (P : Finset ℕ)
    (hlarge : 8 * P.card ≤ ∑ p ∈ P, p) :
    (∑ p ∈ P, p) ≤ 8 * ∑ p ∈ P, p / 4 := by
  have hterm : ∀ p ∈ P, p ≤ 4 * (p / 4) + 4 := by
    intro p hp
    omega
  have hsum : (∑ p ∈ P, p) ≤
      ∑ p ∈ P, (4 * (p / 4) + 4) :=
    Finset.sum_le_sum hterm
  have hsum' : (∑ p ∈ P, p) ≤
      4 * (∑ p ∈ P, p / 4) + 4 * P.card := by
    calc
      (∑ p ∈ P, p) ≤
          ∑ p ∈ P, (4 * (p / 4) + 4) := hsum
      _ = 4 * (∑ p ∈ P, p / 4) + 4 * P.card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        change 4 * (∑ p ∈ P, p / 4) + P.card * 4 =
          4 * (∑ p ∈ P, p / 4) + 4 * P.card
        ring
  omega

lemma card_pivotExtended_ge_sum_div_eight
    (S P : Finset ℕ) (hPpos : ∀ b ∈ P, 0 < b)
    (hcover : ∀ b ∈ P,
      b ≤ 4 * (S.image fun x : ℕ ↦ (x : ZMod b)).card)
    (hlarge : 8 * P.card ≤ ∑ p ∈ P, p) :
    (∑ p ∈ P, p) ≤ 8 * (pivotExtended S P).card := by
  have hcard := card_pivotExtended_lower S P hPpos hcover
  have hsum := sum_le_eight_sum_div_four P hlarge
  omega

lemma pivotExtended_subset_subsetSum_union
    {C P S : Finset ℕ} (hCP : Disjoint C P)
    (hS : S ⊆ C.subsetSum) :
    pivotExtended S P ⊆ (C ∪ P).subsetSum := by
  intro x hx
  obtain ⟨s, hs, p, hp, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨H, hHC, hHsum⟩ := Finset.mem_subsetSum_iff.mp (hS hs)
  obtain ⟨Q, hQP, hQsum⟩ := Finset.mem_subsetSum_iff.mp hp
  have hHQ : Disjoint H Q := hCP.mono hHC hQP
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨H ∪ Q, Finset.union_subset_union hHC hQP, ?_⟩
  rw [Finset.sum_union hHQ, hHsum, hQsum]

lemma pivotExtended_boundedSubsetSum_subset_Icc
    (C P : Finset ℕ) (k : ℕ) :
    pivotExtended (boundedSubsetSum C k) P ⊆
      Finset.Icc 0 ((∑ c ∈ C, c) + ∑ p ∈ P, p) := by
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
  have hu' := Finset.mem_Icc.mp
    (boundedSubsetSum_subset_Icc_sum C k hu)
  have hvle : v ≤ ∑ p ∈ P, p := by
    obtain ⟨Q, hQP, rfl⟩ := Finset.mem_subsetSum_iff.mp hv
    exact Finset.sum_le_sum_of_subset hQP
  rw [Finset.mem_Icc]
  omega

lemma pivotExtended_subset_Icc_of_order
    {C P S : Finset ℕ} {k : ℕ}
    (hP : P.Nonempty) (hk : k ≤ P.card)
    (horder : ∀ c ∈ C, ∀ p ∈ P, c ≤ p)
    (hS : S ⊆ boundedSubsetSum C k) :
    pivotExtended S P ⊆ Finset.Icc 0 (2 * ∑ p ∈ P, p) := by
  intro x hx
  obtain ⟨s, hs, q, hq, rfl⟩ := Finset.mem_add.mp hx
  have hsle := boundedSubsetSum_le_sum_pivots hP hk horder (hS hs)
  have hqle : q ≤ ∑ p ∈ P, p := by
    obtain ⟨Q, hQP, rfl⟩ := Finset.mem_subsetSum_iff.mp hq
    exact Finset.sum_le_sum_of_subset hQP
  rw [Finset.mem_Icc]
  omega

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

def zipUnion : {t : ℕ} → PartitionTree ι t → PartitionTree ι t →
    PartitionTree ι t
  | 0, .leaf A, .leaf B => .leaf (A ∪ B)
  | _ + 1, .node A₁ A₂, .node B₁ B₂ =>
      .node (zipUnion A₁ B₁) (zipUnion A₂ B₂)

lemma carrier_zipUnion {t : ℕ} (A B : PartitionTree ι t) :
    (zipUnion A B).carrier = A.carrier ∪ B.carrier := by
  induction A with
  | leaf A => cases B; rfl
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          simp only [zipUnion, carrier, ih₁, ih₂]
          ext x
          simp only [Finset.mem_union]
          tauto

lemma pairwiseDisjoint_zipUnion {t : ℕ} {A B : PartitionTree ι t}
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier) :
    (zipUnion A B).PairwiseDisjoint := by
  induction A with
  | leaf A => cases B; trivial
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          rcases hA with ⟨hA₁, hA₂, hA12⟩
          rcases hB with ⟨hB₁, hB₂, hB12⟩
          have hA₁B₁ : Disjoint A₁.carrier B₁.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_left _ hx)
              (fun x hx ↦ Finset.mem_union_left _ hx)
          have hA₂B₂ : Disjoint A₂.carrier B₂.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_right _ hx)
              (fun x hx ↦ Finset.mem_union_right _ hx)
          refine ⟨ih₁ hA₁ hB₁ hA₁B₁, ih₂ hA₂ hB₂ hA₂B₂, ?_⟩
          rw [carrier_zipUnion, carrier_zipUnion, Finset.disjoint_left]
          intro x hxLeft hxRight
          rw [Finset.mem_union] at hxLeft hxRight
          rcases hxLeft with hxA₁ | hxB₁ <;>
            rcases hxRight with hxA₂ | hxB₂
          · exact Finset.disjoint_left.mp hA12 hxA₁ hxA₂
          · exact Finset.disjoint_left.mp hAB
              (Finset.mem_union_left _ hxA₁) (Finset.mem_union_right _ hxB₂)
          · exact Finset.disjoint_left.mp hAB
              (Finset.mem_union_right _ hxA₂) (Finset.mem_union_left _ hxB₁)
          · exact Finset.disjoint_left.mp hB12 hxB₁ hxB₂

def mapSumTree (f : Finset ι → Finset ℕ) :
    {t : ℕ} → PartitionTree ι t → SumTree t
  | 0, .leaf A => .leaf (f A)
  | _ + 1, .node A B => .node (mapSumTree f A) (mapSumTree f B)

lemma allLeaves_mapSumTree {t : ℕ} (f : Finset ι → Finset ℕ)
    (T : PartitionTree ι t) (P : Finset ℕ → Prop) :
    (mapSumTree f T).AllLeaves P ↔ T.AllLeaves fun C ↦ P (f C) := by
  induction T with
  | leaf C => rfl
  | node A B ihA ihB =>
      simp only [mapSumTree, SumTree.AllLeaves, AllLeaves, ihA, ihB]

lemma subsetSum_add_subset_union {A B : Finset ℕ} (hAB : Disjoint A B) :
    A.subsetSum + B.subsetSum ⊆ (A ∪ B).subsetSum := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨P, hPA, rfl⟩ := Finset.mem_subsetSum_iff.mp ha
  obtain ⟨Q, hQB, rfl⟩ := Finset.mem_subsetSum_iff.mp hb
  have hPQ := hAB.mono hPA hQB
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨P ∪ Q, Finset.union_subset_union hPA hQB, ?_⟩
  rw [Finset.sum_union hPQ]

lemma carrier_mapSumTree_subset_subsetSum {t : ℕ}
    (f : Finset ℕ → Finset ℕ) (T : PartitionTree ℕ t)
    (hdisj : T.PairwiseDisjoint)
    (hleaf : ∀ C, f C ⊆ C.subsetSum) :
    (mapSumTree f T).carrier ⊆ T.carrier.subsetSum := by
  induction T with
  | leaf C => exact hleaf C
  | node A B ihA ihB =>
      rcases hdisj with ⟨hA, hB, hAB⟩
      exact (Finset.add_subset_add (ihA hA) (ihB hB)).trans
        (subsetSum_add_subset_union hAB)

end PartitionTree

lemma growthLower_ge_pow_mul {k : ℕ} (hk : 2 ≤ k) :
    ∀ t, 3 ^ t * (k - 2) + 2 ≤ SumTree.growthLower k t := by
  intro t
  induction t with
  | zero => simp only [pow_zero, one_mul, SumTree.growthLower]; omega
  | succ t ih =>
    rw [SumTree.growthLower, pow_succ]
    have hmul := Nat.mul_le_mul_left 3 ih
    have hge := SumTree.growthLower_ge hk t
    rw [show 3 ^ t * 3 * (k - 2) = 3 * (3 ^ t * (k - 2)) by ring]
    omega

/-! The eventual estimates in the finite theorem are kept elementary.  The
only analytic-looking error is polylogarithmic; the next two lemmas dominate
it by the integer square root once the binary logarithm is at least `64`. -/

lemma add_one_pow_six_le_two_pow {r : ℕ} (hr : 64 ≤ r) :
    (r + 1) ^ 6 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hratio : 9 * (r + 2) ≤ 10 * (r + 1) := by omega
      have hpow := Nat.pow_le_pow_left hratio 6
      have hcoeff : 10 ^ 6 ≤ 2 * 9 ^ 6 := by norm_num
      have hscaled : 9 ^ 6 * (r + 2) ^ 6 ≤
          9 ^ 6 * (2 * (r + 1) ^ 6) := by
        calc
          9 ^ 6 * (r + 2) ^ 6 = (9 * (r + 2)) ^ 6 := by ring
          _ ≤ (10 * (r + 1)) ^ 6 := hpow
          _ = 10 ^ 6 * (r + 1) ^ 6 := by ring
          _ ≤ (2 * 9 ^ 6) * (r + 1) ^ 6 :=
            Nat.mul_le_mul_right _ hcoeff
          _ = 9 ^ 6 * (2 * (r + 1) ^ 6) := by ring
      have hstep : (r + 2) ^ 6 ≤ 2 * (r + 1) ^ 6 :=
        Nat.le_of_mul_le_mul_left hscaled (by positivity)
      rw [pow_succ]
      calc
        (r + 2) ^ 6 ≤ 2 * (r + 1) ^ 6 := hstep
        _ ≤ 2 * 2 ^ r := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ r * 2 := by ring

lemma log_cube_le_sqrt {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (Nat.log 2 n + 1) ^ 3 ≤ Nat.sqrt n := by
  have hn0 : n ≠ 0 := by positivity
  have hlog : 64 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by omega) hn
  apply Nat.le_sqrt'.mpr
  calc
    ((Nat.log 2 n + 1) ^ 3) ^ 2 = (Nat.log 2 n + 1) ^ 6 := by ring
    _ ≤ 2 ^ Nat.log 2 n := add_one_pow_six_le_two_pow hlog
    _ ≤ n := Nat.pow_log_le_self 2 hn0

/-! Fixed numerical parameters for the finite completion.  The large density
constant is intentionally very wasteful: it pays simultaneously for divisor
descent, dyadic pruning, forty-nine balanced splitting levels, and all integer
rounding errors. -/

def finiteDepth : ℕ := 48

def partitionAmplifier : ℕ := 200 ^ (finiteDepth + 1)

def coreAmplifier : ℕ := 4 * 200 ^ finiteDepth

def finiteDensityConstant : ℕ :=
  1000000000 * partitionAmplifier * coreAmplifier

/-- The published theorem only asks for some absolute constant.  Squaring the
bookkeeping constant leaves ample room for all integer roundings in the final
assembly. -/
def svDensityConstant : ℕ := finiteDensityConstant ^ 2

lemma finiteDepth_eq : finiteDepth = 48 := rfl

lemma partitionAmplifier_eq : partitionAmplifier = 200 ^ 49 := rfl

lemma coreAmplifier_eq : coreAmplifier = 4 * 200 ^ 48 := rfl

lemma finiteDensityConstant_pos : 0 < finiteDensityConstant := by
  unfold finiteDensityConstant partitionAmplifier coreAmplifier finiteDepth
  positivity

lemma svDensityConstant_pos : 0 < svDensityConstant := by
  unfold svDensityConstant
  exact pow_pos finiteDensityConstant_pos _

lemma two_pow_sixtyFour_le_svDensityConstant_sq :
    2 ^ 64 ≤ svDensityConstant ^ 2 := by
  norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
    coreAmplifier, finiteDepth]

lemma nat_square_bound_of_real_sqrt
    {H n m : ℕ}
    (h : (H : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)) :
    H ^ 2 * n ≤ m ^ 2 := by
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hleft : 0 ≤ (H : ℝ) * Real.sqrt (n : ℝ) :=
    mul_nonneg (by positivity) hsqrt
  have hprod : 0 ≤
      ((m : ℝ) - (H : ℝ) * Real.sqrt (n : ℝ)) *
        ((m : ℝ) + (H : ℝ) * Real.sqrt (n : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr h) (add_nonneg (by positivity) hleft)
  have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hreal : ((H : ℝ) ^ 2) * (n : ℝ) ≤ ((m : ℝ) ^ 2) := by
    nlinarith
  exact_mod_cast hreal

lemma scaled_nat_sqrt_le_of_square_bound
    {H n m : ℕ} (h : H ^ 2 * n ≤ m ^ 2) :
    H * Nat.sqrt n ≤ m := by
  have hsqrt : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  have hsq : (H * Nat.sqrt n) ^ 2 ≤ m ^ 2 := by
    calc
      (H * Nat.sqrt n) ^ 2 = H ^ 2 * (Nat.sqrt n) ^ 2 := by ring
      _ ≤ H ^ 2 * n := Nat.mul_le_mul_left _ hsqrt
      _ ≤ m ^ 2 := h
  exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hsq

lemma ambient_large_of_square_bound
    {H n m : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (h : H ^ 2 * n ≤ m ^ 2) : H ^ 2 ≤ n := by
  have hmSq : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn 2
  apply Nat.le_of_mul_le_mul_right (c := n) ?_ hn
  calc
    H ^ 2 * n ≤ m ^ 2 := h
    _ ≤ n ^ 2 := hmSq
    _ = n * n := by ring

lemma coefficient_mul_div_add_one_le
    {E H n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (hHs : H * Nat.sqrt n ≤ m) (hcoef : 8 * E ≤ H ^ 2) :
    E * (n / m + 1) ≤ m := by
  let s := Nat.sqrt n
  have hspos : 0 < s := by simpa [s, Nat.sqrt_pos] using hn
  have hnlt : n < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' n
  have hn4 : n ≤ 4 * s ^ 2 := by
    have hsone : 1 ≤ s := hspos
    nlinarith
  have hquot : (n / m + 1) * m ≤ n + m := by
    calc
      (n / m + 1) * m = (n / m) * m + m := by ring
      _ ≤ n + m := Nat.add_le_add_right (Nat.div_mul_le_self n m) m
  have hquot8 : (n / m + 1) * m ≤ 8 * s ^ 2 := by
    calc
      (n / m + 1) * m ≤ n + m := hquot
      _ ≤ 2 * n := by omega
      _ ≤ 8 * s ^ 2 := by nlinarith
  have hscaled : E * (n / m + 1) * m ≤ H ^ 2 * s ^ 2 := by
    calc
      E * (n / m + 1) * m = E * ((n / m + 1) * m) := by ring
      _ ≤ E * (8 * s ^ 2) := Nat.mul_le_mul_left E hquot8
      _ = (8 * E) * s ^ 2 := by ring
      _ ≤ H ^ 2 * s ^ 2 := Nat.mul_le_mul_right (s ^ 2) hcoef
  have hrootSq : H ^ 2 * s ^ 2 ≤ m ^ 2 := by
    calc
      H ^ 2 * s ^ 2 = (H * s) ^ 2 := by ring
      _ ≤ m ^ 2 := Nat.pow_le_pow_left hHs 2
  apply Nat.le_of_mul_le_mul_right (c := m) ?_ hm
  calc
    E * (n / m + 1) * m ≤ H ^ 2 * s ^ 2 := hscaled
    _ ≤ m ^ 2 := hrootSq
    _ = m * m := by ring

lemma coefficient_mul_log_cube_le
    {E H n m : ℕ} (hn : 2 ^ 64 ≤ n)
    (hEH : E ≤ H) (hHs : H * Nat.sqrt n ≤ m) :
    E * (Nat.log 2 n + 1) ^ 3 ≤ m := by
  calc
    E * (Nat.log 2 n + 1) ^ 3 ≤
        E * Nat.sqrt n := Nat.mul_le_mul_left E (log_cube_le_sqrt hn)
    _ ≤ H * Nat.sqrt n := Nat.mul_le_mul_right _ hEH
    _ ≤ m := hHs

def divisorCutoff (n m : ℕ) : ℕ :=
  2 * coreAmplifier * (n / m + 1)

def trackingThreshold (n : ℕ) : ℕ :=
  4000 * partitionAmplifier * (Nat.log 2 n + 1)

def extractionLinearCharge (n : ℕ) : ℕ :=
  (6 * (Nat.log 2 n + 1) + 2) * trackingThreshold n

def extractionCollisionCharge (n m : ℕ) : ℕ :=
  2 * partitionAmplifier * divisorCutoff n m

def modularPhaseLength (n m : ℕ) : ℕ :=
  16 * coreAmplifier * (n / m + 1) +
    4 * (Nat.log 2 n + 1) ^ 2

def leafCardTarget (M : ℕ) : ℕ :=
  89 ^ 49 * ((M / partitionAmplifier) / 16)

def leafBoxBound (M : ℕ) : ℕ :=
  40 * 111 ^ 49 * (M / partitionAmplifier + 1)

lemma leaf_parameters_of_mass
    {n m M : ℕ} (hn : 0 < n)
    (hdensity : svDensityConstant ^ 2 * n ≤ m ^ 2)
    (hmass : m ^ 2 ≤ 16 * M) :
    32 ≤ M / partitionAmplifier ∧
      n ≤ 2 * leafCardTarget M - 1 := by
  have hcoef : 512 * partitionAmplifier ≤ svDensityConstant ^ 2 := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hscaled : 512 * partitionAmplifier * n ≤ 16 * M := by
    calc
      512 * partitionAmplifier * n ≤ svDensityConstant ^ 2 * n :=
        Nat.mul_le_mul_right n hcoef
      _ ≤ m ^ 2 := hdensity
      _ ≤ 16 * M := hmass
  have hPn : 32 * partitionAmplifier * n ≤ M := by
    have h := Nat.le_of_mul_le_mul_left
      (show 16 * (32 * partitionAmplifier * n) ≤ 16 * M by
        convert hscaled using 1 <;> ring)
      (by norm_num : 0 < 16)
    exact h
  have hq : 32 ≤ M / partitionAmplifier := by
    have hPpos : 0 < partitionAmplifier := by
      unfold partitionAmplifier finiteDepth
      positivity
    apply (Nat.le_div_iff_mul_le hPpos).2
    calc
      32 * partitionAmplifier ≤ 32 * partitionAmplifier * n := by
        calc
          32 * partitionAmplifier = (32 * partitionAmplifier) * 1 := by ring
          _ ≤ (32 * partitionAmplifier) * n :=
            Nat.mul_le_mul_left _ hn
          _ = 32 * partitionAmplifier * n := by ring
      _ ≤ M := hPn
  have hr : n + 1 ≤ (M / partitionAmplifier) / 16 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
    have hPpos : 0 < partitionAmplifier := by
      unfold partitionAmplifier finiteDepth
      positivity
    apply (Nat.le_div_iff_mul_le hPpos).2
    calc
      (n + 1) * 16 * partitionAmplifier ≤
          32 * partitionAmplifier * n := by
        have hn2 : n + 1 ≤ 2 * n := by omega
        calc
          (n + 1) * 16 * partitionAmplifier =
              (16 * partitionAmplifier) * (n + 1) := by ring
          _ ≤ (16 * partitionAmplifier) * (2 * n) :=
            Nat.mul_le_mul_left _ hn2
          _ = 32 * partitionAmplifier * n := by ring
      _ ≤ M := hPn
  constructor
  · exact hq
  · unfold leafCardTarget
    have htarget : n + 1 ≤ 89 ^ 49 *
        ((M / partitionAmplifier) / 16) := by
      exact hr.trans (Nat.le_mul_of_pos_left _ (by positivity))
    omega

lemma trackingThreshold_pos (n : ℕ) : 0 < trackingThreshold n := by
  unfold trackingThreshold partitionAmplifier finiteDepth
  positivity

lemma divisorCutoff_pos (n m : ℕ) : 0 < divisorCutoff n m := by
  unfold divisorCutoff coreAmplifier finiteDepth
  positivity

lemma partitionAmplifier_pos : 0 < partitionAmplifier := by
  unfold partitionAmplifier finiteDepth
  positivity

/-- Divisor extraction and the dyadic-pruning budget together discard at
most one eighth of the original set.  This is the only place where the deliberately
large numerical density constant is spent. -/
lemma finite_extraction_pruning_loss
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (hroot : svDensityConstant * Nat.sqrt n ≤ m)
    (hn64 : 2 ^ 64 ≤ n) :
    8 * (extractionLinearCharge n * Nat.log 2 (divisorCutoff n m) +
        6 * partitionAmplifier * divisorCutoff n m +
        6 * (Nat.log 2 n + 1) * trackingThreshold n) ≤ m := by
  let l := Nat.log 2 n + 1
  have hl : 1 ≤ l := by simp [l]
  have hBcoef : 8 * (2 * coreAmplifier) ≤ svDensityConstant ^ 2 := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hBm : divisorCutoff n m ≤ m := by
    simpa [divisorCutoff] using
      (coefficient_mul_div_add_one_le hn hm hmn hroot hBcoef)
  have hBn : divisorCutoff n m ≤ n := hBm.trans hmn
  have hlogB : Nat.log 2 (divisorCutoff n m) ≤ Nat.log 2 n :=
    Nat.log_mono_right hBn
  have hlinear : extractionLinearCharge n *
      Nat.log 2 (divisorCutoff n m) ≤
        32000 * partitionAmplifier * l ^ 3 := by
    change ((6 * l + 2) * (4000 * partitionAmplifier * l)) *
        Nat.log 2 (divisorCutoff n m) ≤
      32000 * partitionAmplifier * l ^ 3
    calc
      ((6 * l + 2) * (4000 * partitionAmplifier * l)) *
          Nat.log 2 (divisorCutoff n m) ≤
          ((8 * l) * (4000 * partitionAmplifier * l)) * l := by
            apply Nat.mul_le_mul
            · exact Nat.mul_le_mul_right _ (by omega)
            · exact hlogB.trans (by omega)
      _ = 32000 * partitionAmplifier * l ^ 3 := by ring
  have hprune : 6 * l * trackingThreshold n ≤
      24000 * partitionAmplifier * l ^ 3 := by
    change 6 * l * (4000 * partitionAmplifier * l) ≤
      24000 * partitionAmplifier * l ^ 3
    have hsq : l ^ 2 ≤ l ^ 3 := by
      calc
        l ^ 2 = l ^ 2 * 1 := by simp
        _ ≤ l ^ 2 * l := Nat.mul_le_mul_left _ hl
        _ = l ^ 3 := by ring
    nlinarith
  have hpoly : extractionLinearCharge n *
        Nat.log 2 (divisorCutoff n m) +
      6 * l * trackingThreshold n ≤
        56000 * partitionAmplifier * l ^ 3 := by
    calc
      extractionLinearCharge n * Nat.log 2 (divisorCutoff n m) +
          6 * l * trackingThreshold n ≤
          32000 * partitionAmplifier * l ^ 3 +
            24000 * partitionAmplifier * l ^ 3 :=
        Nat.add_le_add hlinear hprune
      _ = 56000 * partitionAmplifier * l ^ 3 := by ring
  have hpolyCoef : 896000 * partitionAmplifier ≤ svDensityConstant := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hpolyBudget := coefficient_mul_log_cube_le hn64 hpolyCoef hroot
  have hpoly16 : 16 * (extractionLinearCharge n *
        Nat.log 2 (divisorCutoff n m) +
      6 * l * trackingThreshold n) ≤ m := by
    calc
      16 * (extractionLinearCharge n * Nat.log 2 (divisorCutoff n m) +
          6 * l * trackingThreshold n) ≤
          896000 * partitionAmplifier * l ^ 3 := by
            have h := Nat.mul_le_mul_left 16 hpoly
            convert h using 1 <;> ring
      _ ≤ m := by simpa [l] using hpolyBudget
  have hquotCoef : 8 * (192 * partitionAmplifier * coreAmplifier) ≤
      svDensityConstant ^ 2 := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hquotBudget := coefficient_mul_div_add_one_le hn hm hmn hroot hquotCoef
  have hquot16 : 16 * (6 * partitionAmplifier * divisorCutoff n m) ≤ m := by
    calc
      16 * (6 * partitionAmplifier * divisorCutoff n m) =
          (192 * partitionAmplifier * coreAmplifier) * (n / m + 1) := by
            simp only [divisorCutoff]
            ring
      _ ≤ m := hquotBudget
  change 8 * (extractionLinearCharge n * Nat.log 2 (divisorCutoff n m) +
      6 * partitionAmplifier * divisorCutoff n m +
      6 * l * trackingThreshold n) ≤ m
  omega

lemma trackingThreshold_sixteen_le
    {n m : ℕ} (hn64 : 2 ^ 64 ≤ n)
    (hroot : svDensityConstant * Nat.sqrt n ≤ m) :
    16 * trackingThreshold n ≤ m := by
  let l := Nat.log 2 n + 1
  have hl : 1 ≤ l := by simp [l]
  have hcoef : 64000 * partitionAmplifier ≤ svDensityConstant := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hbudget := coefficient_mul_log_cube_le hn64 hcoef hroot
  calc
    16 * trackingThreshold n = 64000 * partitionAmplifier * l := by
      simp [trackingThreshold, l]
      ring
    _ ≤ 64000 * partitionAmplifier * l ^ 3 := by
      apply Nat.mul_le_mul_left
      have hl3 : l ≤ l ^ 3 := by
        calc
          l = l * 1 * 1 := by simp
          _ ≤ l * l * l := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left l hl) hl
          _ = l ^ 3 := by ring
      exact hl3
    _ ≤ m := by simpa [l] using hbudget

lemma modularPhaseLength_leaf_bounds
    {n m N r : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (hNn : N ≤ n) (hn64 : 2 ^ 64 ≤ n)
    (hroot : svDensityConstant * Nat.sqrt n ≤ m)
    (hcore : m ≤ coreAmplifier * r) :
    2 * modularPhaseLength n m ≤ r ∧
      16 * N ≤ modularPhaseLength n m * r := by
  let l := Nat.log 2 n + 1
  have hl : 1 ≤ l := by simp [l]
  have hdivCoef : 8 * (64 * coreAmplifier ^ 2) ≤
      svDensityConstant ^ 2 := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hdiv := coefficient_mul_div_add_one_le
    hn hm hmn hroot hdivCoef
  have hlogCoef : 16 * coreAmplifier ≤ svDensityConstant := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hlog0 := coefficient_mul_log_cube_le hn64 hlogCoef hroot
  have hlog : 16 * coreAmplifier * l ^ 2 ≤ m := by
    calc
      16 * coreAmplifier * l ^ 2 ≤ 16 * coreAmplifier * l ^ 3 := by
        apply Nat.mul_le_mul_left
        calc
          l ^ 2 = l ^ 2 * 1 := by simp
          _ ≤ l ^ 2 * l := Nat.mul_le_mul_left _ hl
          _ = l ^ 3 := by ring
      _ ≤ m := by simpa [l] using hlog0
  have htwice : 2 * (2 * coreAmplifier * modularPhaseLength n m) ≤
      2 * m := by
    have hdiv' : 64 * coreAmplifier ^ 2 * (n / m + 1) ≤ m := hdiv
    change 2 * (2 * coreAmplifier *
      (16 * coreAmplifier * (n / m + 1) + 4 * l ^ 2)) ≤ 2 * m
    have hsum := Nat.add_le_add hdiv' hlog
    convert hsum using 1 <;> ring
  have hphaseCore : 2 * coreAmplifier * modularPhaseLength n m ≤ m := by
    omega
  have hhalfScaled : coreAmplifier * (2 * modularPhaseLength n m) ≤
      coreAmplifier * r := by
    calc
      coreAmplifier * (2 * modularPhaseLength n m) =
          2 * coreAmplifier * modularPhaseLength n m := by ring
      _ ≤ m := hphaseCore
      _ ≤ coreAmplifier * r := hcore
  have hhalf : 2 * modularPhaseLength n m ≤ r :=
    Nat.le_of_mul_le_mul_left hhalfScaled (by
      unfold coreAmplifier finiteDepth
      positivity)
  have hnq : n ≤ (n / m + 1) * m := by
    calc
      n = n / m * m + n % m := by
        simpa [mul_comm] using (Nat.div_add_mod n m).symm
      _ ≤ n / m * m + m :=
        Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hm)) _
      _ = (n / m + 1) * m := by ring
  have hmass : 16 * N ≤ modularPhaseLength n m * r := by
    calc
      16 * N ≤ 16 * n := Nat.mul_le_mul_left 16 hNn
      _ ≤ 16 * ((n / m + 1) * m) := Nat.mul_le_mul_left 16 hnq
      _ ≤ 16 * ((n / m + 1) * (coreAmplifier * r)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcore)
      _ = (16 * coreAmplifier * (n / m + 1)) * r := by ring
      _ ≤ modularPhaseLength n m * r := by
        apply Nat.mul_le_mul_right
        unfold modularPhaseLength
        omega
  exact ⟨hhalf, hmass⟩

lemma card_le_of_lt_bound {S : Finset ℕ} {p : ℕ}
    (hS : ∀ s ∈ S, s < p) : S.card ≤ p := by
  have hsub : S ⊆ Finset.range p := by
    intro s hs
    exact Finset.mem_range.mpr (hS s hs)
  simpa using Finset.card_le_card hsub

lemma card_mul_card_le_sum_of_lt
    {L H : Finset ℕ} (horder : ∀ l ∈ L, ∀ h ∈ H, l < h) :
    L.card * H.card ≤ ∑ h ∈ H, h := by
  calc
    L.card * H.card = ∑ _h ∈ H, L.card := by simp [mul_comm]
    _ ≤ ∑ h ∈ H, h := by
      apply Finset.sum_le_sum
      intro h hh
      exact card_le_of_lt_bound (fun l hl ↦ horder l hl h hh)

lemma sum_le_four_sum_of_order
    {L H : Finset ℕ} (hH : H.Nonempty)
    (hcard : L.card ≤ 4 * H.card)
    (horder : ∀ l ∈ L, ∀ h ∈ H, l < h) :
    (∑ l ∈ L, l) ≤ 4 * ∑ h ∈ H, h := by
  let p := H.min' hH
  have hp : p ∈ H := H.min'_mem hH
  have hLsum : (∑ l ∈ L, l) ≤ L.card * p := by
    calc
      (∑ l ∈ L, l) ≤ ∑ _l ∈ L, p := by
        apply Finset.sum_le_sum
        intro l hl
        exact (horder l hl p hp).le
      _ = L.card * p := by simp
  have hHsum : H.card * p ≤ ∑ h ∈ H, h := by
    calc
      H.card * p = ∑ _h ∈ H, p := by simp
      _ ≤ ∑ h ∈ H, h := by
        apply Finset.sum_le_sum
        intro h hh
        exact H.min'_le h hh
  calc
    (∑ l ∈ L, l) ≤ L.card * p := hLsum
    _ ≤ (4 * H.card) * p := Nat.mul_le_mul_right p hcard
    _ = 4 * (H.card * p) := by ring
    _ ≤ 4 * ∑ h ∈ H, h := Nat.mul_le_mul_left 4 hHsum

lemma quotient_le_divisor_budget
    {G n m d N p : ℕ} (hG : 4 ≤ G) (hm : 0 < m) (hd : 0 < d)
    (hpN : p ≤ N) (hdN : d * N ≤ n) (hmp : m ≤ 4 * p) :
    N / p + 1 ≤ (2 * G * (n / m + 1)) / d := by
  have hqp : (N / p + 1) * p ≤ 2 * N := by
    calc
      (N / p + 1) * p = N / p * p + p := by ring
      _ ≤ N + p := Nat.add_le_add_right (Nat.div_mul_le_self N p) p
      _ ≤ 2 * N := by omega
  have hdmul : d * (N / p + 1) * m ≤
      (2 * G * (n / m + 1)) * m := by
    calc
      d * (N / p + 1) * m ≤ d * (N / p + 1) * (4 * p) :=
        Nat.mul_le_mul_left _ hmp
      _ = 4 * d * ((N / p + 1) * p) := by ring
      _ ≤ 4 * d * (2 * N) := Nat.mul_le_mul_left _ hqp
      _ = 8 * (d * N) := by ring
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 hdN
      _ ≤ 2 * G * n := by nlinarith
      _ ≤ (2 * G * (n / m + 1)) * m := by
        have hn : n ≤ (n / m + 1) * m := by
          calc
            n = n / m * m + n % m := by
              simpa [mul_comm] using (Nat.div_add_mod n m).symm
            _ ≤ n / m * m + m :=
              Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hm)) _
            _ = (n / m + 1) * m := by ring
        have h := Nat.mul_le_mul_left (2 * G) hn
        simpa [mul_assoc] using h
  have hdle : d * (N / p + 1) ≤ 2 * G * (n / m + 1) :=
    Nat.le_of_mul_le_mul_right hdmul hm
  exact (Nat.le_div_iff_mul_le hd).2 (by simpa [mul_comm] using hdle)

lemma phase_quotient_bound
    {D : Finset ℕ} {G n m d B N p e : ℕ} (hm : 0 < m) (hd : 0 < d)
    (he : 1 < e) (hpN : p ≤ N)
    (hdN : d * N ≤ n) (hB : 2 * G * (n / m + 1) ≤ B)
    (hcore : m ≤ G * D.card)
    (heD : e * D.card ≤ 2 * p) :
    (N / p + 1) * (e - 1) ≤ e + 2 * (B / d) := by
  have hqp : (N / p + 1) * p ≤ 2 * N := by
    calc
      (N / p + 1) * p = N / p * p + p := by ring
      _ ≤ N + p := Nat.add_le_add_right (Nat.div_mul_le_self N p) p
      _ ≤ 2 * N := by omega
  have hem : e * m ≤ 2 * G * p := by
    calc
      e * m ≤ e * (G * D.card) := Nat.mul_le_mul_left e hcore
      _ = G * (e * D.card) := by ring
      _ ≤ G * (2 * p) := Nat.mul_le_mul_left G heD
      _ = 2 * G * p := by ring
  have hscaled : d * ((N / p + 1) * e) * m ≤ 2 * B * m := by
    calc
      d * ((N / p + 1) * e) * m =
          d * (N / p + 1) * (e * m) := by ring
      _ ≤ d * (N / p + 1) * (2 * G * p) :=
        Nat.mul_le_mul_left _ hem
      _ = 2 * G * d * ((N / p + 1) * p) := by ring
      _ ≤ 2 * G * d * (2 * N) := Nat.mul_le_mul_left _ hqp
      _ = 4 * G * (d * N) := by ring
      _ ≤ 4 * G * n := Nat.mul_le_mul_left _ hdN
      _ ≤ (4 * G * (n / m + 1)) * m := by
        have hn : n ≤ (n / m + 1) * m := by
          calc
            n = n / m * m + n % m := by
              simpa [mul_comm] using (Nat.div_add_mod n m).symm
            _ ≤ n / m * m + m :=
              Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hm)) _
            _ = (n / m + 1) * m := by ring
        have h := Nat.mul_le_mul_left (4 * G) hn
        simpa [mul_assoc] using h
      _ ≤ 2 * B * m := by
        have h := Nat.mul_le_mul_left 2 hB
        have hm' := Nat.mul_le_mul_right m h
        convert hm' using 1 <;> ring
  have hdqe : d * ((N / p + 1) * e) ≤ 2 * B :=
    Nat.le_of_mul_le_mul_right hscaled hm
  have hqediv : (N / p + 1) * e ≤ (2 * B) / d :=
    (Nat.le_div_iff_mul_le hd).2 (by simpa [mul_comm] using hdqe)
  have hround : (2 * B) / d ≤ 2 * (B / d) + 1 := by
    have h := Nat.add_div_le_div_add_div_add_one B B d
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  calc
    (N / p + 1) * (e - 1) ≤ (N / p + 1) * e :=
      Nat.mul_le_mul_left _ (Nat.sub_le e 1)
    _ ≤ (2 * B) / d := hqediv
    _ ≤ 2 * (B / d) + 1 := hround
    _ ≤ e + 2 * (B / d) := by omega

lemma lower_tag_gives_leaf_witness
    {L D : Finset ℕ} {T e : ℕ} (hDL : D ⊆ L)
    (htag : T + partitionAmplifier * e ≤
      (L.filter fun z ↦ ¬e ∣ z).card)
    (hratio : 89 ^ 48 * (L.filter fun z ↦ ¬e ∣ z).card ≤
      200 ^ 48 * (D ∩ (L.filter fun z ↦ ¬e ∣ z)).card) :
    e - 1 ≤ (D.filter fun z ↦ ¬e ∣ z).card := by
  have hinter : D ∩ (L.filter fun z ↦ ¬e ∣ z) =
      D.filter fun z ↦ ¬e ∣ z := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter]
    aesop
  rw [hinter] at hratio
  have hscale : 200 ^ 48 * e ≤
      200 ^ 48 * (D.filter fun z ↦ ¬e ∣ z).card := by
    calc
      200 ^ 48 * e ≤ 89 ^ 48 * (partitionAmplifier * e) := by
        rw [partitionAmplifier_eq]
        have hcoef : 200 ^ 48 ≤ 89 ^ 48 * 200 ^ 49 := by
          have : 1 ≤ 89 ^ 48 * 200 := by norm_num
          nlinarith
        have hmul := Nat.mul_le_mul_right e hcoef
        convert hmul using 1 <;> ring
      _ ≤ 89 ^ 48 * (L.filter fun z ↦ ¬e ∣ z).card := by
        apply Nat.mul_le_mul_left
        exact (Nat.le_add_left _ T).trans htag
      _ ≤ 200 ^ 48 * (D.filter fun z ↦ ¬e ∣ z).card := hratio
  have he : e ≤ (D.filter fun z ↦ ¬e ∣ z).card :=
    Nat.le_of_mul_le_mul_left hscale (by positivity)
  omega

lemma upper_tag_gives_leaf_witness
    {H U : Finset ℕ} {T B d e q : ℕ} (hUH : U ⊆ H)
    (hq : q * (e - 1) ≤ e + 2 * (B / d))
    (htag : T + partitionAmplifier * e +
        2 * partitionAmplifier * (B / d) ≤
      (H.filter fun z ↦ ¬e ∣ z).card)
    (hratio : 89 ^ 49 * (H.filter fun z ↦ ¬e ∣ z).card ≤
      200 ^ 49 * (U ∩ (H.filter fun z ↦ ¬e ∣ z)).card) :
    q * (e - 1) ≤ (U.filter fun z ↦ ¬e ∣ z).card := by
  have hinter : U ∩ (H.filter fun z ↦ ¬e ∣ z) =
      U.filter fun z ↦ ¬e ∣ z := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter]
    aesop
  rw [hinter] at hratio
  have hscale : 200 ^ 49 * (e + 2 * (B / d)) ≤
      200 ^ 49 * (U.filter fun z ↦ ¬e ∣ z).card := by
    calc
      200 ^ 49 * (e + 2 * (B / d)) ≤
          89 ^ 49 * (partitionAmplifier * e +
            2 * partitionAmplifier * (B / d)) := by
        rw [partitionAmplifier_eq]
        have hcoef : 200 ^ 49 ≤ 89 ^ 49 * 200 ^ 49 := by
          have : 1 ≤ 89 ^ 49 := by norm_num
          nlinarith
        have hmul := Nat.mul_le_mul_right (e + 2 * (B / d)) hcoef
        convert hmul using 1 <;> ring
      _ ≤ 89 ^ 49 * (H.filter fun z ↦ ¬e ∣ z).card := by
        apply Nat.mul_le_mul_left
        omega
      _ ≤ 200 ^ 49 * (U.filter fun z ↦ ¬e ∣ z).card := hratio
  have hBe : e + 2 * (B / d) ≤
      (U.filter fun z ↦ ¬e ∣ z).card :=
    Nat.le_of_mul_le_mul_left hscale (by positivity)
  exact hq.trans hBe

lemma eight_leafCardTarget_le
    {M s : ℕ}
    (hweight : 89 ^ 49 * M ≤ 2 * partitionAmplifier * s) :
    8 * leafCardTarget M ≤ s := by
  have hPpos : 0 < partitionAmplifier := partitionAmplifier_pos
  have hround : partitionAmplifier *
      (16 * ((M / partitionAmplifier) / 16)) ≤ M := by
    calc
      partitionAmplifier * (16 * ((M / partitionAmplifier) / 16)) ≤
          partitionAmplifier * (M / partitionAmplifier) := by
        apply Nat.mul_le_mul_left
        simpa [mul_comm] using Nat.div_mul_le_self (M / partitionAmplifier) 16
      _ ≤ M := Nat.mul_div_le _ _
  have hscaled : (2 * partitionAmplifier) *
      (8 * leafCardTarget M) ≤ (2 * partitionAmplifier) * s := by
    calc
      (2 * partitionAmplifier) * (8 * leafCardTarget M) =
          89 ^ 49 * (partitionAmplifier *
            (16 * ((M / partitionAmplifier) / 16))) := by
        simp only [leafCardTarget]
        ring
      _ ≤ 89 ^ 49 * M := Nat.mul_le_mul_left _ hround
      _ ≤ 2 * partitionAmplifier * s := hweight
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

lemma leaf_box_bound_of_weights
    {M sD sU sP : ℕ}
    (hD : 200 ^ 48 * sD ≤ 8 * 111 ^ 48 * M)
    (hU : partitionAmplifier * sU ≤ 2 * 111 ^ 49 * M)
    (hP : partitionAmplifier * sP ≤ 2 * 111 ^ 49 * M) :
    sD + sU + sP ≤ leafBoxBound M := by
  have hPamp : partitionAmplifier = 200 * 200 ^ 48 := by
    rw [partitionAmplifier_eq]
    ring
  have hD' : partitionAmplifier * sD ≤ 1600 * 111 ^ 48 * M := by
    rw [hPamp]
    calc
      200 * 200 ^ 48 * sD = 200 * (200 ^ 48 * sD) := by ring
      _ ≤ 200 * (8 * 111 ^ 48 * M) := Nat.mul_le_mul_left 200 hD
      _ = 1600 * 111 ^ 48 * M := by ring
  have hsum : partitionAmplifier * (sD + sU + sP) ≤
      40 * 111 ^ 49 * M := by
    calc
      partitionAmplifier * (sD + sU + sP) =
          partitionAmplifier * sD + partitionAmplifier * sU +
            partitionAmplifier * sP := by ring
      _ ≤ 1600 * 111 ^ 48 * M + 2 * 111 ^ 49 * M +
            2 * 111 ^ 49 * M := by omega
      _ ≤ 40 * 111 ^ 49 * M := by
        have hcoef : 1600 * 111 ^ 48 + 4 * 111 ^ 49 ≤ 40 * 111 ^ 49 := by
          have hpos : 0 < 111 ^ 48 := by positivity
          nlinarith
        have := Nat.mul_le_mul_right M hcoef
        convert this using 1 <;> ring
  have hround : M ≤ partitionAmplifier * (M / partitionAmplifier + 1) := by
    have hmod := Nat.mod_lt M partitionAmplifier_pos
    calc
      M = M / partitionAmplifier * partitionAmplifier +
          M % partitionAmplifier := by
        simpa [mul_comm] using (Nat.div_add_mod M partitionAmplifier).symm
      _ ≤ M / partitionAmplifier * partitionAmplifier + partitionAmplifier :=
        Nat.add_le_add_left (Nat.le_of_lt hmod) _
      _ = partitionAmplifier * (M / partitionAmplifier + 1) := by ring
  have hscaled : partitionAmplifier * (sD + sU + sP) ≤
      partitionAmplifier * leafBoxBound M := by
    calc
      partitionAmplifier * (sD + sU + sP) ≤
          40 * 111 ^ 49 * M := hsum
      _ ≤ 40 * 111 ^ 49 *
          (partitionAmplifier * (M / partitionAmplifier + 1)) :=
        Nat.mul_le_mul_left _ hround
      _ = partitionAmplifier * leafBoxBound M := by
        simp only [leafBoxBound]
        ring
  exact Nat.le_of_mul_le_mul_left hscaled partitionAmplifier_pos

lemma depth_fortyEight_growth
    {q : ℕ} (hq : 32 ≤ q) :
    2 ^ 48 * (40 * 111 ^ 49 * (q + 1)) + 1 <
      SumTree.growthLower (89 ^ 49 * (q / 16)) 48 := by
  have hr : 2 ≤ q / 16 := by omega
  have hk : 2 ≤ 89 ^ 49 * (q / 16) := by
    have : 1 ≤ 89 ^ 49 := one_le_pow₀ (by omega)
    nlinarith
  have hgrowth := growthLower_ge_pow_mul hk 48
  have hqround : q + 1 ≤ 24 * (q / 16) := by omega
  have hcoef :
      2 ^ 48 * (40 * 111 ^ 49) * 24 <
        3 ^ 48 * (89 ^ 49 - 1) := by norm_num
  have hminus :
      (89 ^ 49 - 1) * (q / 16) ≤
        89 ^ 49 * (q / 16) - 2 := by
    calc
      (89 ^ 49 - 1) * (q / 16) =
          89 ^ 49 * (q / 16) - 1 * (q / 16) := by
            rw [Nat.sub_mul]
      _ = 89 ^ 49 * (q / 16) - q / 16 := by simp
      _ ≤ 89 ^ 49 * (q / 16) - 2 :=
        Nat.sub_le_sub_left hr _
  have hstrict :
      2 ^ 48 * (40 * 111 ^ 49 * (q + 1)) + 1 <
        3 ^ 48 * (89 ^ 49 * (q / 16) - 2) + 2 := by
    calc
      2 ^ 48 * (40 * 111 ^ 49 * (q + 1)) + 1 ≤
          (2 ^ 48 * (40 * 111 ^ 49) * 24) * (q / 16) + 1 := by
            have hscaled := Nat.mul_le_mul_left
              (2 ^ 48 * (40 * 111 ^ 49)) hqround
            have hadd := Nat.add_le_add_right hscaled 1
            convert hadd using 1 <;> ring
      _ < (3 ^ 48 * (89 ^ 49 - 1)) * (q / 16) + 2 := by
            have hpos : 0 < q / 16 := by omega
            have hmul := Nat.mul_lt_mul_of_pos_right hcoef hpos
            omega
      _ ≤ 3 ^ 48 * (89 ^ 49 * (q / 16) - 2) + 2 := by
            have hadd := Nat.add_le_add_right
              (Nat.mul_le_mul_left (3 ^ 48) hminus) 2
            convert hadd using 1 <;> ring
  exact hstrict.trans_le hgrowth

/-! ### Dyadic pruning and weighted balance

The finite assembly partitions a set many times.  Cardinal balance alone is
not enough: a leaf could receive all of the very large elements.  We first
discard the occupied dyadic value classes that are too small, then track every
remaining class through the simultaneous partition.  The next definitions
and lemmas turn the resulting classwise cardinal estimates into estimates for
the sums of the elements. -/

noncomputable def dyadicBin (Y : Finset ℕ) (j : ℕ) : Finset ℕ :=
  Y.filter fun y ↦ Nat.log 2 y = j

def dyadicRange (N : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 N + 1)

noncomputable def largeDyadicIndices
    (Y : Finset ℕ) (N Q : ℕ) : Finset ℕ :=
  (dyadicRange N).filter fun j ↦ Q ≤ (dyadicBin Y j).card

noncomputable def dyadicPrune (Y : Finset ℕ) (N Q : ℕ) : Finset ℕ :=
  (largeDyadicIndices Y N Q).biUnion fun j ↦ dyadicBin Y j

lemma dyadicBin_subset (Y : Finset ℕ) (j : ℕ) :
    dyadicBin Y j ⊆ Y :=
  Finset.filter_subset _ _

lemma log_mem_dyadicRange {Y : Finset ℕ} {N y : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) (hy : y ∈ Y) :
    Nat.log 2 y ∈ dyadicRange N := by
  rw [dyadicRange, Finset.mem_range]
  have hyN := (Finset.mem_Icc.mp (hY hy)).2
  exact Nat.lt_succ_of_le (Nat.log_mono_right hyN)

lemma biUnion_dyadicBin_eq {Y : Finset ℕ} {N : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) :
    (dyadicRange N).biUnion (dyadicBin Y) = Y := by
  apply Finset.biUnion_filter_eq_of_maps_to
  intro y hy
  exact log_mem_dyadicRange hY hy

lemma pairwiseDisjoint_dyadicBin (Y : Finset ℕ) (J : Finset ℕ) :
    Set.PairwiseDisjoint (J : Set ℕ) (dyadicBin Y) := by
  change Set.PairwiseDisjoint (J : Set ℕ)
    (fun j ↦ Y.filter fun y ↦ Nat.log 2 y = j)
  exact Set.pairwiseDisjoint_filter
    (fun y : ℕ ↦ Nat.log 2 y) (J : Set ℕ) Y

lemma dyadicPrune_subset (Y : Finset ℕ) (N Q : ℕ) :
    dyadicPrune Y N Q ⊆ Y := by
  intro y hy
  obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
  exact dyadicBin_subset Y j hyj

lemma dyadicPrune_subset_Icc {Y : Finset ℕ} {N Q : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) :
    dyadicPrune Y N Q ⊆ Finset.Icc 1 N :=
  (dyadicPrune_subset Y N Q).trans hY

lemma dyadicBin_card_lt_of_mem_sdiff_prune
    {Y : Finset ℕ} {N Q y : ℕ} (hY : Y ⊆ Finset.Icc 1 N)
    (hy : y ∈ Y \ dyadicPrune Y N Q) :
    (dyadicBin Y (Nat.log 2 y)).card < Q := by
  have hj : Nat.log 2 y ∈ dyadicRange N :=
    log_mem_dyadicRange hY (Finset.mem_sdiff.mp hy).1
  by_contra hnot
  have hjLarge : Nat.log 2 y ∈ largeDyadicIndices Y N Q := by
    exact Finset.mem_filter.mpr ⟨hj, Nat.le_of_not_gt hnot⟩
  apply (Finset.mem_sdiff.mp hy).2
  apply Finset.mem_biUnion.mpr
  refine ⟨Nat.log 2 y, hjLarge, ?_⟩
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy).1, rfl⟩

lemma card_sdiff_dyadicPrune_le {Y : Finset ℕ} {N Q : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) :
    (Y \ dyadicPrune Y N Q).card ≤
      (Nat.log 2 N + 1) * Q := by
  classical
  let Jsmall := (dyadicRange N).filter fun j ↦ (dyadicBin Y j).card < Q
  let U := Jsmall.biUnion fun j ↦ dyadicBin Y j
  have hsub : Y \ dyadicPrune Y N Q ⊆ U := by
    intro y hy
    have hyY := (Finset.mem_sdiff.mp hy).1
    let j := Nat.log 2 y
    have hjR : j ∈ dyadicRange N := log_mem_dyadicRange hY hyY
    have hyBin : y ∈ dyadicBin Y j := by
      exact Finset.mem_filter.mpr ⟨hyY, rfl⟩
    have hjSmall : (dyadicBin Y j).card < Q := by
      by_contra hnot
      have hjLarge : j ∈ largeDyadicIndices Y N Q := by
        rw [largeDyadicIndices, Finset.mem_filter]
        exact ⟨hjR, Nat.le_of_not_gt hnot⟩
      exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_biUnion.mpr ⟨j, hjLarge, hyBin⟩)
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_filter.mpr ⟨hjR, hjSmall⟩, hyBin⟩
  have hUcard : U.card ≤ ∑ j ∈ Jsmall, (dyadicBin Y j).card := by
    exact Finset.card_biUnion_le
  have hsum : (∑ j ∈ Jsmall, (dyadicBin Y j).card) ≤ Jsmall.card * Q := by
    calc
      (∑ j ∈ Jsmall, (dyadicBin Y j).card) ≤ ∑ _j ∈ Jsmall, Q := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.mem_filter.mp hj).2.le
      _ = Jsmall.card * Q := by simp
  have hJcard : Jsmall.card ≤ Nat.log 2 N + 1 := by
    calc
      Jsmall.card ≤ (dyadicRange N).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.log 2 N + 1 := by simp [dyadicRange]
  calc
    (Y \ dyadicPrune Y N Q).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Jsmall, (dyadicBin Y j).card := hUcard
    _ ≤ Jsmall.card * Q := hsum
    _ ≤ (Nat.log 2 N + 1) * Q := Nat.mul_le_mul_right Q hJcard

lemma card_filter_le_pruned_filter_add_loss
    {X S : Finset ℕ} (hS : S ⊆ X) (P : ℕ → Prop) [DecidablePred P] :
    (X.filter P).card ≤ (S.filter P).card + (X \ S).card := by
  have hsub : X.filter P ⊆ S.filter P ∪ (X \ S) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxS, hx'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx'.1, hxS⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma dyadicBin_dyadicPrune_eq {Y : Finset ℕ} {N Q j : ℕ}
    (hj : j ∈ largeDyadicIndices Y N Q) :
    dyadicBin (dyadicPrune Y N Q) j = dyadicBin Y j := by
  classical
  ext y
  simp only [dyadicBin, Finset.mem_filter]
  constructor
  · rintro ⟨hy, hjy⟩
    exact ⟨dyadicPrune_subset Y N Q hy, hjy⟩
  · rintro ⟨hyY, hjy⟩
    refine ⟨Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩, hjy⟩
    exact Finset.mem_filter.mpr ⟨hyY, hjy⟩

lemma dyadicBin_dyadicPrune_eq_empty {Y : Finset ℕ} {N Q j : ℕ}
    (hj : j ∈ dyadicRange N)
    (hsmall : (dyadicBin Y j).card < Q) :
    dyadicBin (dyadicPrune Y N Q) j = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨y, hy⟩
  have hy' := (Finset.mem_filter.mp hy).1
  obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy'
  have hilog := (Finset.mem_filter.mp hyi).2
  have hjlog := (Finset.mem_filter.mp hy).2
  have hij : i = j := by omega
  have hiLarge : Q ≤ (dyadicBin Y i).card :=
    (Finset.mem_filter.mp hi).2
  rw [hij] at hiLarge
  exact (Nat.not_le_of_gt hsmall) hiLarge

lemma dyadicBin_dyadicPrune_large_or_empty
    {Y : Finset ℕ} {N Q j : ℕ} (hj : j ∈ dyadicRange N) :
    dyadicBin (dyadicPrune Y N Q) j = ∅ ∨
      Q ≤ (dyadicBin (dyadicPrune Y N Q) j).card := by
  classical
  by_cases hlarge : Q ≤ (dyadicBin Y j).card
  · right
    have hj' : j ∈ largeDyadicIndices Y N Q := by
      exact Finset.mem_filter.mpr ⟨hj, hlarge⟩
    rw [dyadicBin_dyadicPrune_eq hj']
    exact hlarge
  · left
    exact dyadicBin_dyadicPrune_eq_empty hj (Nat.lt_of_not_ge hlarge)

lemma dyadicBin_prune_large_of_largeIndex_one
    {Y : Finset ℕ} {N Q j : ℕ}
    (hj : j ∈ largeDyadicIndices (dyadicPrune Y N Q) N 1) :
    Q ≤ (dyadicBin (dyadicPrune Y N Q) j).card := by
  have hjpos : 1 ≤ (dyadicBin (dyadicPrune Y N Q) j).card :=
    (Finset.mem_filter.mp hj).2
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega :
    0 < (dyadicBin (dyadicPrune Y N Q) j).card)
  have hyPrune := (Finset.mem_filter.mp hy).1
  obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hyPrune
  have hij : i = j := by
    have hiLog := (Finset.mem_filter.mp hyi).2
    have hjLog := (Finset.mem_filter.mp hy).2
    omega
  subst i
  rw [dyadicBin_dyadicPrune_eq hi]
  exact (Finset.mem_filter.mp hi).2

lemma inter_dyadicBin_eq {S Y : Finset ℕ} {j : ℕ} (hSY : S ⊆ Y) :
    S ∩ dyadicBin Y j = dyadicBin S j := by
  classical
  ext y
  simp only [dyadicBin, Finset.mem_inter, Finset.mem_filter]
  tauto

lemma largeDyadicIndices_card (Y : Finset ℕ) (N Q : ℕ) :
    (largeDyadicIndices Y N Q).card ≤ Nat.log 2 N + 1 := by
  calc
    (largeDyadicIndices Y N Q).card ≤ (dyadicRange N).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Nat.log 2 N + 1 := by simp [dyadicRange]

lemma balancing_threshold_le_tracking
    {n N t : ℕ} {S E : Finset ℕ}
    (hn : 2 ≤ n) (hN : N ≤ n) (ht : t ≤ 49) (hE : E.card ≤ n) :
    (1000 * (Nat.log 2
        (2 * (1 + E.card + (largeDyadicIndices S N 1).card) + 1) + 1)) *
        200 ^ t ≤ trackingThreshold n := by
  have hlogN : Nat.log 2 N ≤ Nat.log 2 n := Nat.log_mono_right hN
  have hbins := largeDyadicIndices_card S N 1
  have harg :
      2 * (1 + E.card + (largeDyadicIndices S N 1).card) + 1 ≤ 8 * n := by
    have hlogself := Nat.log_le_self 2 n
    omega
  have hnpos : 0 < n := by omega
  have hlogEight : Nat.log 2 (8 * n) ≤ Nat.log 2 n + 3 := by
    have heq : Nat.log 2 (8 * n) = Nat.log 2 n + 3 := by
      rw [show 8 * n = ((n * 2) * 2) * 2 by ring]
      rw [Nat.log_mul_base (by omega) (by positivity : 0 < (n * 2) * 2).ne']
      rw [Nat.log_mul_base (by omega) (by positivity : 0 < n * 2).ne']
      rw [Nat.log_mul_base (by omega) hnpos.ne']
    exact heq.le
  have hlogArg : Nat.log 2
      (2 * (1 + E.card + (largeDyadicIndices S N 1).card) + 1) + 1 ≤
        4 * (Nat.log 2 n + 1) := by
    have := (Nat.log_mono_right harg).trans hlogEight
    omega
  have hpow : 200 ^ t ≤ partitionAmplifier := by
    rw [partitionAmplifier_eq]
    exact Nat.pow_le_pow_right (by omega) ht
  calc
    (1000 * (Nat.log 2
        (2 * (1 + E.card + (largeDyadicIndices S N 1).card) + 1) + 1)) *
          200 ^ t ≤
        (1000 * (4 * (Nat.log 2 n + 1))) * partitionAmplifier :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hlogArg) hpow
    _ = trackingThreshold n := by
      simp only [trackingThreshold]
      ring

structure PreparedPools (A : Finset ℕ) (n m : ℕ) where
  d : ℕ
  N : ℕ
  lower : Finset ℕ
  upper : Finset ℕ
  lowerTags : Finset ℕ
  upperTags : Finset ℕ
  d_pos : 0 < d
  N_eq : N = n / d
  scale_mem : ∀ z ∈ lower ∪ upper, d * z ∈ A
  lower_box : lower ⊆ Finset.Icc 1 N
  upper_box : upper ⊆ Finset.Icc 1 N
  disjoint : Disjoint lower upper
  ordered : ∀ l ∈ lower, ∀ u ∈ upper, l < u
  lower_large : m ≤ 4 * lower.card
  upper_large : m ≤ 4 * upper.card
  lowerTags_card : lowerTags.card ≤ n
  upperTags_card : upperTags.card ≤ n
  tags_cover : ∀ e : ℕ, 1 < e → d * e ≤ divisorCutoff n m →
    e ∈ lowerTags ∨ e ∈ upperTags
  lower_tag : ∀ e ∈ lowerTags,
    trackingThreshold n + partitionAmplifier * e ≤
      (lower.filter fun z ↦ ¬e ∣ z).card
  upper_tag : ∀ e ∈ upperTags,
    trackingThreshold n + partitionAmplifier * e +
        2 * partitionAmplifier * (divisorCutoff n m / d) ≤
      (upper.filter fun z ↦ ¬e ∣ z).card
  lower_bins : ∀ j ∈ largeDyadicIndices lower N 1,
    trackingThreshold n ≤ (dyadicBin lower j).card
  upper_bins : ∀ j ∈ largeDyadicIndices upper N 1,
    trackingThreshold n ≤ (dyadicBin upper j).card

theorem exists_preparedPools
    {A : Finset ℕ} {n m : ℕ} (hn : 0 < n) (hm32 : 32 ≤ m)
    (hcard : A.card = m) (hA : A ⊆ Finset.Icc 1 n)
    (hroot : svDensityConstant * Nat.sqrt n ≤ m)
    (hn64 : 2 ^ 64 ≤ n) :
    Nonempty (PreparedPools A n m) := by
  classical
  have hm : 0 < m := by omega
  have hmn : m ≤ n := by
    rw [← hcard]
    exact (Finset.card_le_card hA).trans (by simp)
  let B := divisorCutoff n m
  let T := trackingThreshold n
  have hBpos : 0 < B := by simpa [B] using divisorCutoff_pos n m
  obtain ⟨d, Z, hd, hdB, hscale, hloss, hdiverse⟩ :=
    exists_collisionDivisorExtraction B (extractionLinearCharge n)
      (2 * partitionAmplifier) (extractionCollisionCharge n m) hBpos A
  let N := n / d
  let r := Z.card / 2
  let L₀ := lowerPart Z r
  let H₀ := Z \ L₀
  let L := dyadicPrune L₀ N T
  let H := dyadicPrune H₀ N T
  let E := Finset.Icc 2 (B / d)
  let EL := E.filter fun e ↦
    T + partitionAmplifier * e ≤ (L.filter fun z ↦ ¬e ∣ z).card
  let EH := E \ EL
  have hZbox : Z ⊆ Finset.Icc 1 N := by
    intro z hz
    have hzA := hscale z hz
    have hzI := Finset.mem_Icc.mp (hA hzA)
    rw [Finset.mem_Icc]
    constructor
    · by_contra hz0
      have : z = 0 := Nat.eq_zero_of_not_pos hz0
      subst z
      simp at hzI
    · exact (Nat.le_div_iff_mul_le hd).2 (by simpa [mul_comm] using hzI.2)
  have hZle : Z.card ≤ m := by
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun z ↦ d * z)
    · exact hscale
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hd hxy
  have hExtract : m - Z.card ≤
      extractionLinearCharge n * Nat.log 2 B +
        6 * partitionAmplifier * B := by
    rw [← hcard]
    calc
      A.card - Z.card ≤ extractionLinearCharge n * Nat.log 2 B +
          (2 * partitionAmplifier) * B +
            2 * extractionCollisionCharge n m := hloss
      _ = extractionLinearCharge n * Nat.log 2 B +
          6 * partitionAmplifier * B := by
        simp only [extractionCollisionCharge, B]
        ring
  have hNn : N ≤ n := by
    dsimp only [N]
    exact Nat.div_le_self n d
  have hL₀box : L₀ ⊆ Finset.Icc 1 N :=
    (lowerPart_subset Z r).trans hZbox
  have hH₀box : H₀ ⊆ Finset.Icc 1 N :=
    (Finset.sdiff_subset).trans hZbox
  have hLsub : L ⊆ L₀ := dyadicPrune_subset L₀ N T
  have hHsub : H ⊆ H₀ := dyadicPrune_subset H₀ N T
  have hLbox : L ⊆ Finset.Icc 1 N := hLsub.trans hL₀box
  have hHbox : H ⊆ Finset.Icc 1 N := hHsub.trans hH₀box
  have hlogN : Nat.log 2 N + 1 ≤ Nat.log 2 n + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hNn) 1
  have hLloss : (L₀ \ L).card ≤ (Nat.log 2 n + 1) * T := by
    calc
      (L₀ \ L).card ≤ (Nat.log 2 N + 1) * T := by
        simpa [L] using card_sdiff_dyadicPrune_le hL₀box
      _ ≤ (Nat.log 2 n + 1) * T := Nat.mul_le_mul_right T hlogN
  have hHloss : (H₀ \ H).card ≤ (Nat.log 2 n + 1) * T := by
    calc
      (H₀ \ H).card ≤ (Nat.log 2 N + 1) * T := by
        simpa [H] using card_sdiff_dyadicPrune_le hH₀box
      _ ≤ (Nat.log 2 n + 1) * T := Nat.mul_le_mul_right T hlogN
  have hbudget0 := finite_extraction_pruning_loss hn hm hmn hroot hn64
  have hbudget : 8 * ((m - Z.card) + (L₀ \ L).card +
      (H₀ \ H).card) ≤ m := by
    calc
      8 * ((m - Z.card) + (L₀ \ L).card + (H₀ \ H).card) ≤
          8 * (extractionLinearCharge n * Nat.log 2 B +
            6 * partitionAmplifier * B +
            6 * (Nat.log 2 n + 1) * T) := by
        apply Nat.mul_le_mul_left
        have hp := Nat.add_le_add hLloss hHloss
        calc
          (m - Z.card) + (L₀ \ L).card + (H₀ \ H).card ≤
              (extractionLinearCharge n * Nat.log 2 B +
                6 * partitionAmplifier * B) +
                  ((L₀ \ L).card + (H₀ \ H).card) := by
            simpa [Nat.add_assoc] using
              Nat.add_le_add_right hExtract ((L₀ \ L).card + (H₀ \ H).card)
          _ ≤ (extractionLinearCharge n * Nat.log 2 B +
                6 * partitionAmplifier * B) +
                  2 * ((Nat.log 2 n + 1) * T) := by
            have hp' : (L₀ \ L).card + (H₀ \ H).card ≤
                2 * ((Nat.log 2 n + 1) * T) := by
              convert hp using 1 <;> ring
            exact Nat.add_le_add_left hp' _
          _ ≤ extractionLinearCharge n * Nat.log 2 B +
                6 * partitionAmplifier * B +
                  6 * (Nat.log 2 n + 1) * T := by
            have htwo : 2 * ((Nat.log 2 n + 1) * T) ≤
                6 * (Nat.log 2 n + 1) * T := by
              have := Nat.mul_le_mul_right ((Nat.log 2 n + 1) * T)
                (by omega : 2 ≤ 6)
              convert this using 1 <;> ring
            exact Nat.add_le_add_left htwo _
      _ ≤ m := by simpa [B, T] using hbudget0
  have hLcardEq : (L₀ \ L).card + L.card = L₀.card :=
    Finset.card_sdiff_add_card_eq_card hLsub
  have hHcardEq : (H₀ \ H).card + H.card = H₀.card :=
    Finset.card_sdiff_add_card_eq_card hHsub
  have hL₀card : L₀.card = Z.card - r := by
    simpa [L₀] using card_lowerPart Z r
  have hH₀card : H₀.card = r := by
    dsimp only [H₀]
    rw [card_sdiff_lowerPart]
    exact min_eq_left (Nat.div_le_self _ _)
  have hLlarge : m ≤ 4 * L.card := by
    dsimp only [r] at hL₀card hH₀card
    omega
  have hHlarge : m ≤ 4 * H.card := by
    dsimp only [r] at hL₀card hH₀card
    omega
  have hLHdisj : Disjoint L H := by
    exact (Finset.disjoint_sdiff.mono hLsub hHsub)
  have horder : ∀ l ∈ L, ∀ u ∈ H, l < u := by
    intro l hl u hu
    exact lowerPart_lt_sdiff (hLsub hl) (hHsub hu)
  have hscaleLH : ∀ z ∈ L ∪ H, d * z ∈ A := by
    intro z hz
    rw [Finset.mem_union] at hz
    exact hz.elim
      (fun h ↦ hscale z (lowerPart_subset Z r (hLsub h)))
      (fun h ↦ hscale z (Finset.sdiff_subset (hHsub h)))
  have htagStrong (e : ℕ) (he : e ∈ E) :
      e ∈ EL ∨
        (e ∈ EH ∧ T + partitionAmplifier * e +
          2 * partitionAmplifier * (B / d) ≤
            (H.filter fun z ↦ ¬e ∣ z).card) := by
    by_cases heL : e ∈ EL
    · exact Or.inl heL
    · right
      refine ⟨Finset.mem_sdiff.mpr ⟨he, heL⟩, ?_⟩
      have hZsplit : (Z.filter fun z ↦ ¬e ∣ z).card =
          (L₀.filter fun z ↦ ¬e ∣ z).card +
            (H₀.filter fun z ↦ ¬e ∣ z).card := by
        have hUnion : L₀ ∪ H₀ = Z :=
          Finset.union_sdiff_of_subset (lowerPart_subset Z r)
        have hDisj : Disjoint L₀ H₀ := Finset.disjoint_sdiff
        rw [← Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter hDisj)]
        congr 1
        ext z
        simp only [Finset.mem_union, Finset.mem_filter]
        rw [← hUnion]
        simp only [Finset.mem_union]
        tauto
      have hZupper : (Z.filter fun z ↦ ¬e ∣ z).card ≤
          (L.filter fun z ↦ ¬e ∣ z).card +
            (H.filter fun z ↦ ¬e ∣ z).card +
              (L₀ \ L).card + (H₀ \ H).card := by
        rw [hZsplit]
        have h₁ := card_filter_le_pruned_filter_add_loss hLsub
          (fun z ↦ ¬e ∣ z)
        have h₂ := card_filter_le_pruned_filter_add_loss hHsub
          (fun z ↦ ¬e ∣ z)
        omega
      have heBounds := Finset.mem_Icc.mp he
      have hdeB : d * e ≤ B :=
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).1 heBounds.2
      have hdiv := hdiverse e (by omega) hdeB
      have hlinear : 2 * T + (L₀ \ L).card + (H₀ \ H).card ≤
          extractionLinearCharge n := by
        change 2 * T + (L₀ \ L).card + (H₀ \ H).card ≤
          (6 * (Nat.log 2 n + 1) + 2) * T
        have hp := Nat.add_le_add hLloss hHloss
        calc
          2 * T + (L₀ \ L).card + (H₀ \ H).card ≤
              2 * T + 2 * ((Nat.log 2 n + 1) * T) :=
            by
              have hp' : (L₀ \ L).card + (H₀ \ H).card ≤
                  2 * ((Nat.log 2 n + 1) * T) := by
                convert hp using 1 <;> ring
              simpa [Nat.add_assoc] using Nat.add_le_add_left hp' (2 * T)
          _ = (2 * (Nat.log 2 n + 1) + 2) * T := by ring
          _ ≤ (6 * (Nat.log 2 n + 1) + 2) * T := by
            apply Nat.mul_le_mul_right
            omega
      have hcollision : 2 * partitionAmplifier * (B / d) ≤
          extractionCollisionCharge n m / d := by
        apply (Nat.le_div_iff_mul_le hd).2
        calc
          (2 * partitionAmplifier * (B / d)) * d =
              2 * partitionAmplifier * (d * (B / d)) := by ring
          _ ≤ 2 * partitionAmplifier * B := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_div_le B d
          _ = extractionCollisionCharge n m := by
            simp [extractionCollisionCharge, B]
      have hdiv' : extractionLinearCharge n +
          2 * partitionAmplifier * e + extractionCollisionCharge n m / d ≤
            (Z.filter fun z ↦ ¬e ∣ z).card := by
        simpa [Nat.add_assoc] using hdiv
      have hremain : 2 * T + 2 * partitionAmplifier * e +
          2 * partitionAmplifier * (B / d) ≤
            (L.filter fun z ↦ ¬e ∣ z).card +
              (H.filter fun z ↦ ¬e ∣ z).card := by
        have hleft : 2 * T + 2 * partitionAmplifier * e +
              2 * partitionAmplifier * (B / d) +
              ((L₀ \ L).card + (H₀ \ H).card) ≤
            extractionLinearCharge n + 2 * partitionAmplifier * e +
              extractionCollisionCharge n m / d := by
          calc
            2 * T + 2 * partitionAmplifier * e +
                2 * partitionAmplifier * (B / d) +
                ((L₀ \ L).card + (H₀ \ H).card) =
                (2 * T + (L₀ \ L).card + (H₀ \ H).card) +
                  2 * partitionAmplifier * e +
                    2 * partitionAmplifier * (B / d) := by ring
            _ ≤ extractionLinearCharge n +
                  2 * partitionAmplifier * e +
                    extractionCollisionCharge n m / d := by
              exact Nat.add_le_add
                (Nat.add_le_add_right hlinear _)
                hcollision
        have hright : extractionLinearCharge n +
              2 * partitionAmplifier * e + extractionCollisionCharge n m / d ≤
            (L.filter fun z ↦ ¬e ∣ z).card +
              (H.filter fun z ↦ ¬e ∣ z).card +
                ((L₀ \ L).card + (H₀ \ H).card) := by
          exact hdiv'.trans (by
            have := hZupper
            omega)
        omega
      have hnot : ¬ T + partitionAmplifier * e ≤
          (L.filter fun z ↦ ¬e ∣ z).card := by
        simpa [EL, Finset.mem_filter, he] using heL
      rw [show 2 * partitionAmplifier * e =
        2 * (partitionAmplifier * e) by ring] at hremain
      omega
  have htagCover : ∀ e : ℕ, 1 < e → d * e ≤ B →
      e ∈ EL ∨ e ∈ EH := by
    intro e he hde
    have heE : e ∈ E := by
      change e ∈ Finset.Icc 2 (B / d)
      rw [Finset.mem_Icc]
      exact ⟨by omega, (Nat.le_div_iff_mul_le hd).2 (by simpa [mul_comm] using hde)⟩
    rcases htagStrong e heE with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  have hELtag : ∀ e ∈ EL, T + partitionAmplifier * e ≤
      (L.filter fun z ↦ ¬e ∣ z).card := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hEHtag : ∀ e ∈ EH, T + partitionAmplifier * e +
        2 * partitionAmplifier * (B / d) ≤
      (H.filter fun z ↦ ¬e ∣ z).card := by
    intro e he
    have heE := (Finset.mem_sdiff.mp he).1
    exact (htagStrong e heE).resolve_left (Finset.mem_sdiff.mp he).2 |>.2
  have hBcoef : 8 * (2 * coreAmplifier) ≤ svDensityConstant ^ 2 := by
    norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
      coreAmplifier, finiteDepth]
  have hBm : B ≤ m := by
    simpa [B, divisorCutoff] using
      (coefficient_mul_div_add_one_le hn hm hmn hroot hBcoef)
  have hEcard : E.card ≤ n := by
    have hBd : B / d ≤ n := (Nat.div_le_self B d).trans (hBm.trans hmn)
    have hcardI : (Finset.Icc 2 (B / d)).card ≤ n := by
      simp
      omega
    simpa [E] using hcardI
  have hELcard : EL.card ≤ n := by
    have hsub : EL ⊆ E := by
      intro e he
      exact (Finset.mem_filter.mp he).1
    exact (Finset.card_le_card hsub).trans hEcard
  have hEHcard : EH.card ≤ n := by
    have := (Finset.card_le_card (Finset.sdiff_subset : E \ EL ⊆ E)).trans hEcard
    simpa [EH] using this
  have hLbins : ∀ j ∈ largeDyadicIndices L N 1,
      T ≤ (dyadicBin L j).card := by
    intro j hj
    simpa [L] using dyadicBin_prune_large_of_largeIndex_one hj
  have hHbins : ∀ j ∈ largeDyadicIndices H N 1,
      T ≤ (dyadicBin H j).card := by
    intro j hj
    simpa [H] using dyadicBin_prune_large_of_largeIndex_one hj
  exact ⟨{
    d := d
    N := N
    lower := L
    upper := H
    lowerTags := EL
    upperTags := EH
    d_pos := hd
    N_eq := rfl
    scale_mem := hscaleLH
    lower_box := hLbox
    upper_box := hHbox
    disjoint := hLHdisj
    ordered := horder
    lower_large := hLlarge
    upper_large := hHlarge
    lowerTags_card := hELcard
    upperTags_card := hEHcard
    tags_cover := by simpa [B] using htagCover
    lower_tag := by simpa [T] using hELtag
    upper_tag := by simpa [B, T] using hEHtag
    lower_bins := by simpa [T] using hLbins
    upper_bins := by simpa [T] using hHbins }⟩

lemma upperPart_sum_dominates {Y : Finset ℕ} (hYcard : 2 ≤ Y.card) :
    let r := Y.card / 2
    let L := lowerPart Y r
    let U := Y \ L
    (∑ y ∈ Y, y) ≤ 3 * ∑ y ∈ U, y := by
  classical
  dsimp only
  let r := Y.card / 2
  let L := lowerPart Y r
  let U := Y \ L
  have hr : 0 < r := by dsimp [r]; omega
  have hUcard : U.card = r := by
    dsimp only [U, L]
    rw [card_sdiff_lowerPart]
    exact min_eq_left (Nat.div_le_self _ _)
  have hUne : U.Nonempty := Finset.card_pos.mp (by simpa [hUcard] using hr)
  let p := U.min' hUne
  have hpU : p ∈ U := U.min'_mem hUne
  have hLsum : (∑ y ∈ L, y) ≤ L.card * p := by
    calc
      (∑ y ∈ L, y) ≤ ∑ _y ∈ L, p := by
        apply Finset.sum_le_sum
        intro y hy
        exact (lowerPart_lt_sdiff hy hpU).le
      _ = L.card * p := by simp
  have hUsum : U.card * p ≤ ∑ y ∈ U, y := by
    calc
      U.card * p = ∑ _y ∈ U, p := by simp
      _ ≤ ∑ y ∈ U, y := by
        apply Finset.sum_le_sum
        intro y hy
        exact U.min'_le y hy
  have hLcard : L.card ≤ 2 * U.card := by
    rw [hUcard]
    dsimp only [L, r]
    rw [card_lowerPart]
    omega
  have hLsum' : (∑ y ∈ L, y) ≤ 2 * ∑ y ∈ U, y := by
    calc
      (∑ y ∈ L, y) ≤ L.card * p := hLsum
      _ ≤ (2 * U.card) * p := Nat.mul_le_mul_right p hLcard
      _ = 2 * (U.card * p) := by ring
      _ ≤ 2 * ∑ y ∈ U, y := Nat.mul_le_mul_left 2 hUsum
  have hLU : L ∪ U = Y := by
    exact Finset.union_sdiff_of_subset (lowerPart_subset Y r)
  have hdisj : Disjoint L U := Finset.disjoint_sdiff
  calc
    (∑ y ∈ Y, y) = ∑ y ∈ L ∪ U, y := by rw [hLU]
    _ = (∑ y ∈ L, y) + ∑ y ∈ U, y := Finset.sum_union hdisj
    _ ≤ 3 * ∑ y ∈ U, y := by omega

/-- If all occupied dyadic classes of `Y` are large, pruning the upper half
again at the smaller threshold loses at most a constant fraction of its
weight.  The only classes that can be lost from the upper half meet the lower
half; order then forces all of them to be the same boundary class. -/
lemma upperPart_prune_sum_dominates
    {Y : Finset ℕ} {N Q : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) (hQ : 0 < Q)
    (hYcard : 4 * Q ≤ Y.card)
    (hbins : ∀ j ∈ dyadicRange N,
      dyadicBin Y j = ∅ ∨ 4 * Q ≤ (dyadicBin Y j).card) :
    let r := Y.card / 2
    let L := lowerPart Y r
    let H := Y \ L
    let P := dyadicPrune H N Q
    (∑ y ∈ H, y) ≤ 3 * ∑ y ∈ P, y := by
  classical
  dsimp only
  let r := Y.card / 2
  let L := lowerPart Y r
  let H := Y \ L
  let P := dyadicPrune H N Q
  let E := H \ P
  change (∑ y ∈ H, y) ≤ 3 * ∑ y ∈ P, y
  have hLY : L ⊆ Y := lowerPart_subset Y r
  have hHY : H ⊆ Y := Finset.sdiff_subset
  have hHBox : H ⊆ Finset.Icc 1 N := hHY.trans hY
  have hPY : P ⊆ H := dyadicPrune_subset H N Q
  have hHcard : H.card = r := by
    dsimp only [H, L]
    rw [card_sdiff_lowerPart]
    exact min_eq_left (Nat.div_le_self _ _)
  have hHlarge : 2 * Q ≤ H.card := by
    rw [hHcard]
    dsimp only [r]
    omega
  have hLU : L ∪ H = Y :=
    Finset.union_sdiff_of_subset (lowerPart_subset Y r)
  have hLH : Disjoint L H := Finset.disjoint_sdiff
  have hboundary (y : ℕ) (hy : y ∈ E) :
      ∃ x ∈ L, Nat.log 2 x = Nat.log 2 y := by
    have hyH : y ∈ H := (Finset.mem_sdiff.mp hy).1
    have hyY : y ∈ Y := hHY hyH
    let j := Nat.log 2 y
    have hjR : j ∈ dyadicRange N := log_mem_dyadicRange hY hyY
    have hyBinY : y ∈ dyadicBin Y j :=
      Finset.mem_filter.mpr ⟨hyY, rfl⟩
    have hbinYne : dyadicBin Y j ≠ ∅ := by
      exact Finset.nonempty_iff_ne_empty.mp ⟨y, hyBinY⟩
    have hbinYlarge : 4 * Q ≤ (dyadicBin Y j).card :=
      (hbins j hjR).resolve_left hbinYne
    have hyE' : y ∈ H \ dyadicPrune H N Q := hy
    have hbinHsmall : (dyadicBin H j).card < Q := by
      simpa [j] using dyadicBin_card_lt_of_mem_sdiff_prune hHBox hyE'
    have hcardlt : (dyadicBin H j).card < (dyadicBin Y j).card := by
      omega
    obtain ⟨x, hxYbin, hxnotHbin⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hcardlt
    have hxY : x ∈ Y := dyadicBin_subset Y j hxYbin
    have hxnotH : x ∉ H := by
      intro hxH
      exact hxnotHbin (Finset.mem_filter.mpr
        ⟨hxH, (Finset.mem_filter.mp hxYbin).2⟩)
    have hxL : x ∈ L := by
      rw [← hLU] at hxY
      exact (Finset.mem_union.mp hxY).resolve_right hxnotH
    exact ⟨x, hxL, (Finset.mem_filter.mp hxYbin).2⟩
  by_cases hEne : E.Nonempty
  · let y₀ := E.min' hEne
    have hy₀E : y₀ ∈ E := E.min'_mem hEne
    obtain ⟨x₀, hx₀L, hx₀log⟩ := hboundary y₀ hy₀E
    have hsameLog : ∀ y ∈ E, Nat.log 2 y = Nat.log 2 y₀ := by
      intro y hyE
      obtain ⟨x, hxL, hxlog⟩ := hboundary y hyE
      have hyH : y ∈ H := (Finset.mem_sdiff.mp hyE).1
      have hy₀H : y₀ ∈ H := (Finset.mem_sdiff.mp hy₀E).1
      have hxy₀ : x < y₀ := lowerPart_lt_sdiff hxL hy₀H
      have hx₀y : x₀ < y := lowerPart_lt_sdiff hx₀L hyH
      have hle₁ := Nat.log_mono_right (b := 2) (Nat.le_of_lt hxy₀)
      have hle₂ := Nat.log_mono_right (b := 2) (Nat.le_of_lt hx₀y)
      omega
    have hEsubBin : E ⊆ dyadicBin H (Nat.log 2 y₀) := by
      intro y hyE
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hyE).1, hsameLog y hyE⟩
    have hEcard : E.card < Q := by
      have hsmall := dyadicBin_card_lt_of_mem_sdiff_prune hHBox hy₀E
      exact (Finset.card_le_card hEsubBin).trans_lt hsmall
    have hsplit : H.card = E.card + P.card := by
      have hEP : E ∪ P = H := by
        dsimp only [E]
        exact Finset.sdiff_union_of_subset hPY
      have hdisjEP : Disjoint E P := Finset.sdiff_disjoint
      rw [← hEP, Finset.card_union_of_disjoint hdisjEP]
    have hPcard : E.card ≤ P.card := by
      omega
    have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
    let p := P.min' hPne
    have hpP : p ∈ P := P.min'_mem hPne
    have hpH : p ∈ H := hPY hpP
    have hx₀p : x₀ < p := lowerPart_lt_sdiff hx₀L hpH
    have hlogle : Nat.log 2 y₀ ≤ Nat.log 2 p := by
      rw [← hx₀log]
      exact Nat.log_mono_right (Nat.le_of_lt hx₀p)
    have hpoint : ∀ y ∈ E, y ≤ 2 * p := by
      intro y hyE
      have hyUpper₀ := Nat.lt_pow_succ_log_self (by omega : 1 < 2) y
      have hyUpper : y < 2 * 2 ^ Nat.log 2 y₀ := by
        rw [hsameLog y hyE, pow_succ] at hyUpper₀
        simpa [mul_comm] using hyUpper₀
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) hlogle
      have hpLower := Nat.pow_log_le_self 2
        (by have := (Finset.mem_Icc.mp (hHBox hpH)).1; omega : p ≠ 0)
      calc
        y ≤ 2 * 2 ^ Nat.log 2 y₀ := hyUpper.le
        _ ≤ 2 * 2 ^ Nat.log 2 p := Nat.mul_le_mul_left 2 hpow
        _ ≤ 2 * p := Nat.mul_le_mul_left 2 hpLower
    have hEsum : (∑ y ∈ E, y) ≤ 2 * ∑ y ∈ P, y := by
      calc
        (∑ y ∈ E, y) ≤ ∑ _y ∈ E, 2 * p := by
          apply Finset.sum_le_sum
          intro y hy
          exact hpoint y hy
        _ = E.card * (2 * p) := by simp
        _ ≤ P.card * (2 * p) := Nat.mul_le_mul_right (2 * p) hPcard
        _ = 2 * (P.card * p) := by ring
        _ ≤ 2 * ∑ y ∈ P, y := by
          apply Nat.mul_le_mul_left
          calc
            P.card * p = ∑ _y ∈ P, p := by simp
            _ ≤ ∑ y ∈ P, y := by
              apply Finset.sum_le_sum
              intro y hy
              exact P.min'_le y hy
    have hEP : E ∪ P = H := by
      dsimp only [E]
      exact Finset.sdiff_union_of_subset hPY
    have hdisjEP : Disjoint E P := Finset.sdiff_disjoint
    calc
      (∑ y ∈ H, y) = (∑ y ∈ E, y) + ∑ y ∈ P, y := by
        rw [← Finset.sum_union hdisjEP, hEP]
      _ ≤ 3 * ∑ y ∈ P, y := by omega
  · have hEempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEne
    have hHP : H = P := by
      apply Finset.Subset.antisymm
      · intro y hyH
        by_contra hyP
        have : y ∈ E := Finset.mem_sdiff.mpr ⟨hyH, hyP⟩
        simpa [hEempty] using this
      · exact hPY
    rw [hHP]
    omega

lemma dyadicBin_lower {Y : Finset ℕ} {j y : ℕ}
    (hy : y ∈ dyadicBin Y j) (hypos : 0 < y) : 2 ^ j ≤ y := by
  have hlog := Nat.pow_log_le_self 2 hypos.ne'
  simpa [(Finset.mem_filter.mp hy).2] using hlog

lemma dyadicBin_upper {Y : Finset ℕ} {j y : ℕ}
    (hy : y ∈ dyadicBin Y j) : y < 2 * 2 ^ j := by
  have hj := (Finset.mem_filter.mp hy).2
  have h := Nat.lt_pow_succ_log_self (by omega : 1 < 2) y
  rw [hj, pow_succ] at h
  simpa [mul_comm] using h

lemma card_mul_pow_le_sum_dyadicBin (Y : Finset ℕ) (j : ℕ)
    (hYpos : ∀ y ∈ Y, 0 < y) :
    (dyadicBin Y j).card * 2 ^ j ≤ ∑ y ∈ dyadicBin Y j, y := by
  calc
    (dyadicBin Y j).card * 2 ^ j = ∑ _y ∈ dyadicBin Y j, 2 ^ j := by simp
    _ ≤ ∑ y ∈ dyadicBin Y j, y := by
      apply Finset.sum_le_sum
      intro y hy
      exact dyadicBin_lower hy (hYpos y (dyadicBin_subset Y j hy))

lemma sum_dyadicBin_le_two_mul (Y : Finset ℕ) (j : ℕ) :
    (∑ y ∈ dyadicBin Y j, y) ≤
      2 * ((dyadicBin Y j).card * 2 ^ j) := by
  calc
    (∑ y ∈ dyadicBin Y j, y) ≤
        ∑ _y ∈ dyadicBin Y j, (2 * 2 ^ j) := by
      apply Finset.sum_le_sum
      intro y hy
      exact (dyadicBin_upper hy).le
    _ = 2 * ((dyadicBin Y j).card * 2 ^ j) := by simp; ring

lemma sum_dyadicBins {Y : Finset ℕ} {N : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) :
    (∑ j ∈ dyadicRange N, ∑ y ∈ dyadicBin Y j, y) = ∑ y ∈ Y, y := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_dyadicBin Y (dyadicRange N)),
    biUnion_dyadicBin_eq hY]

/-- Classwise balance on all occupied dyadic classes implies weight balance.
The factors `2` are the width of a dyadic class. -/
lemma dyadic_weight_balance
    {Y S : Finset ℕ} {N a b c : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) (hS : S ⊆ Y)
    (hclasses : ∀ j ∈ dyadicRange N,
      a * (dyadicBin Y j).card ≤ b * (dyadicBin S j).card ∧
      b * (dyadicBin S j).card ≤ c * (dyadicBin Y j).card) :
    a * (∑ y ∈ Y, y) ≤ 2 * b * (∑ y ∈ S, y) ∧
      b * (∑ y ∈ S, y) ≤ 2 * c * (∑ y ∈ Y, y) := by
  have hSbox : S ⊆ Finset.Icc 1 N := hS.trans hY
  rw [← sum_dyadicBins hY, ← sum_dyadicBins hSbox]
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hYupper := sum_dyadicBin_le_two_mul Y j
    have hSlower := card_mul_pow_le_sum_dyadicBin S j (fun y hy ↦
      (Finset.mem_Icc.mp (hSbox hy)).1)
    calc
      a * (∑ y ∈ dyadicBin Y j, y) ≤
          a * (2 * ((dyadicBin Y j).card * 2 ^ j)) :=
        Nat.mul_le_mul_left a hYupper
      _ = 2 * (a * (dyadicBin Y j).card) * 2 ^ j := by ring
      _ ≤ 2 * (b * (dyadicBin S j).card) * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j)
          (Nat.mul_le_mul_left 2 (hclasses j hj).1)
      _ = 2 * b * ((dyadicBin S j).card * 2 ^ j) := by ring
      _ ≤ 2 * b * (∑ y ∈ dyadicBin S j, y) :=
        Nat.mul_le_mul_left (2 * b) hSlower
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hSupper := sum_dyadicBin_le_two_mul S j
    have hYlower := card_mul_pow_le_sum_dyadicBin Y j (fun y hy ↦
      (Finset.mem_Icc.mp (hY hy)).1)
    calc
      b * (∑ y ∈ dyadicBin S j, y) ≤
          b * (2 * ((dyadicBin S j).card * 2 ^ j)) :=
        Nat.mul_le_mul_left b hSupper
      _ = 2 * (b * (dyadicBin S j).card) * 2 ^ j := by ring
      _ ≤ 2 * (c * (dyadicBin Y j).card) * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j)
          (Nat.mul_le_mul_left 2 (hclasses j hj).2)
      _ = 2 * c * ((dyadicBin Y j).card * 2 ^ j) := by ring
      _ ≤ 2 * c * (∑ y ∈ dyadicBin Y j, y) :=
        Nat.mul_le_mul_left (2 * c) hYlower

lemma dyadic_weight_balance_of_large_indices
    {Y C : Finset ℕ} {N a b c : ℕ}
    (hY : Y ⊆ Finset.Icc 1 N) (hC : C ⊆ Y)
    (hclasses : ∀ j ∈ largeDyadicIndices Y N 1,
      a * (dyadicBin Y j).card ≤
          b * (C ∩ dyadicBin Y j).card ∧
      b * (C ∩ dyadicBin Y j).card ≤
          c * (dyadicBin Y j).card) :
    a * (∑ y ∈ Y, y) ≤ 2 * b * (∑ y ∈ C, y) ∧
      b * (∑ y ∈ C, y) ≤ 2 * c * (∑ y ∈ Y, y) := by
  apply dyadic_weight_balance hY hC
  intro j hj
  by_cases hne : dyadicBin Y j = ∅
  · have hCempty : dyadicBin C j = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨y, hy⟩
      have hyY : y ∈ dyadicBin Y j :=
        Finset.mem_filter.mpr
          ⟨hC (dyadicBin_subset C j hy), (Finset.mem_filter.mp hy).2⟩
      simpa [hne] using hyY
    rw [hne, hCempty]
    simp
  · have hjLarge : j ∈ largeDyadicIndices Y N 1 := by
      rw [largeDyadicIndices, Finset.mem_filter]
      refine ⟨hj, ?_⟩
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    simpa [inter_dyadicBin_eq hC] using hclasses j hjLarge

lemma dyadic_weight_balance_pruned
    {X C : Finset ℕ} {N Q a b c : ℕ}
    (hX : X ⊆ Finset.Icc 1 N)
    (hC : C ⊆ dyadicPrune X N Q)
    (hclasses : ∀ j ∈ largeDyadicIndices X N Q,
      a * (dyadicBin (dyadicPrune X N Q) j).card ≤
          b * (C ∩ dyadicBin (dyadicPrune X N Q) j).card ∧
      b * (C ∩ dyadicBin (dyadicPrune X N Q) j).card ≤
          c * (dyadicBin (dyadicPrune X N Q) j).card) :
    a * (∑ y ∈ dyadicPrune X N Q, y) ≤ 2 * b * (∑ y ∈ C, y) ∧
      b * (∑ y ∈ C, y) ≤
        2 * c * (∑ y ∈ dyadicPrune X N Q, y) := by
  apply dyadic_weight_balance (dyadicPrune_subset_Icc hX) hC
  intro j hj
  by_cases hjLarge : j ∈ largeDyadicIndices X N Q
  · simpa [inter_dyadicBin_eq hC] using hclasses j hjLarge
  · have hsmall : (dyadicBin X j).card < Q := by
      have hjNot : ¬(j ∈ dyadicRange N ∧ Q ≤ (dyadicBin X j).card) := by
        simpa [largeDyadicIndices, Finset.mem_filter] using hjLarge
      exact Nat.lt_of_not_ge (fun h ↦ hjNot ⟨hj, h⟩)
    have hempty := dyadicBin_dyadicPrune_eq_empty hj hsmall
    have hCempty : dyadicBin C j = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨y, hy⟩
      have hy' := (dyadicBin_subset C j hy)
      have hyPrune := hC hy'
      have : y ∈ dyadicBin (dyadicPrune X N Q) j :=
        Finset.mem_filter.mpr ⟨hyPrune, (Finset.mem_filter.mp hy).2⟩
      simpa [hempty] using this
    rw [hempty, hCempty]
    simp

/-- A reusable partition package tracking the whole carrier, specified
divisor-witness sets, and all occupied dyadic classes. -/
theorem PartitionTree.exists_dyadic_diverse_partition
    (t : ℕ) (S : Finset ℕ) (N Q : ℕ) (E : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 N)
    (hwhole : Q ≤ S.card)
    (hdiv : ∀ e ∈ E, Q ≤ (S.filter fun x ↦ ¬e ∣ x).card)
    (hbin : ∀ j ∈ largeDyadicIndices S N 1,
      Q ≤ (dyadicBin S j).card)
    (hQ : (1000 * (Nat.log 2
        (2 * (1 + E.card + (largeDyadicIndices S N 1).card) + 1) + 1)) *
        200 ^ t ≤ Q) :
    ∃ T : PartitionTree ℕ t,
      T.carrier = S ∧ T.PairwiseDisjoint ∧
      T.AllLeaves fun C ↦
        (89 ^ t * S.card ≤ 200 ^ t * C.card ∧
          200 ^ t * C.card ≤ 111 ^ t * S.card) ∧
        (∀ e ∈ E,
          89 ^ t * (S.filter fun x ↦ ¬e ∣ x).card ≤
              200 ^ t * (C ∩ (S.filter fun x ↦ ¬e ∣ x)).card ∧
          200 ^ t * (C ∩ (S.filter fun x ↦ ¬e ∣ x)).card ≤
              111 ^ t * (S.filter fun x ↦ ¬e ∣ x).card) ∧
        (∀ j ∈ largeDyadicIndices S N 1,
          89 ^ t * (dyadicBin S j).card ≤
              200 ^ t * (C ∩ dyadicBin S j).card ∧
          200 ^ t * (C ∩ dyadicBin S j).card ≤
              111 ^ t * (dyadicBin S j).card) := by
  classical
  let κ := Unit ⊕ (ℕ ⊕ ℕ)
  let Jwhole : Finset κ := {Sum.inl ()}
  let Jdiv : Finset κ := E.image fun e ↦ Sum.inr (Sum.inl e)
  let Jbin : Finset κ :=
    (largeDyadicIndices S N 1).image fun j ↦ Sum.inr (Sum.inr j)
  let J := Jwhole ∪ Jdiv ∪ Jbin
  let F : κ → Finset ℕ
    | Sum.inl _ => S
    | Sum.inr (Sum.inl e) => S.filter fun x ↦ ¬e ∣ x
    | Sum.inr (Sum.inr j) => dyadicBin S j
  have hJcard : J.card ≤
      1 + E.card + (largeDyadicIndices S N 1).card := by
    calc
      J.card ≤ (Jwhole ∪ Jdiv).card + Jbin.card := Finset.card_union_le _ _
      _ ≤ (Jwhole.card + Jdiv.card) + Jbin.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 1 + E.card + (largeDyadicIndices S N 1).card := by
        have hdivCard : Jdiv.card ≤ E.card := by
          dsimp only [Jdiv]
          exact Finset.card_image_le
        have hbinCard : Jbin.card ≤ (largeDyadicIndices S N 1).card := by
          dsimp only [Jbin]
          exact Finset.card_image_le
        simp only [Jwhole, Finset.card_singleton]
        omega
  have hlog : Nat.log 2 (2 * J.card + 1) ≤
      Nat.log 2
        (2 * (1 + E.card + (largeDyadicIndices S N 1).card) + 1) := by
    apply Nat.log_mono_right
    omega
  have hsub : ∀ z ∈ J, F z ⊆ S := by
    intro z hz
    rcases z with _ | z
    · exact Finset.Subset.rfl
    · rcases z with e | j
      · exact Finset.filter_subset _ _
      · exact dyadicBin_subset S j
  have hlarge : ∀ z ∈ J,
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
        89 ^ t * (F z).card := by
    intro z hz
    have hthreshold :
        (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤ Q := by
      calc
        (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤
            (1000 * (Nat.log 2
              (2 * (1 + E.card +
                (largeDyadicIndices S N 1).card) + 1) + 1)) * 200 ^ t := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          exact Nat.add_le_add_right hlog 1
        _ ≤ Q := hQ
    have hFQ : Q ≤ (F z).card := by
      rcases z with z | z
      · simpa [F] using hwhole
      · rcases z with e | j
        · have hzdiv : Sum.inr (Sum.inl e) ∈ Jdiv := by
            have hz' : Sum.inr (Sum.inl e) ∈ Jwhole ∪ Jdiv ∨
                Sum.inr (Sum.inl e) ∈ Jbin := Finset.mem_union.mp hz
            rcases hz' with hz' | hzbin
            · exact (Finset.mem_union.mp hz').resolve_left (by simp [Jwhole])
            · exfalso
              simpa [Jbin] using hzbin
          have he : e ∈ E := by simpa [Jdiv] using hzdiv
          simpa [F] using hdiv e he
        · have hzbin : Sum.inr (Sum.inr j) ∈ Jbin := by
            have hz' : Sum.inr (Sum.inr j) ∈ Jwhole ∪ Jdiv ∨
                Sum.inr (Sum.inr j) ∈ Jbin := Finset.mem_union.mp hz
            exact hz'.resolve_left (by
              intro h
              rcases Finset.mem_union.mp h with hw | hd
              · simpa [Jwhole] using hw
              · simpa [Jdiv] using hd)
          have hj : j ∈ largeDyadicIndices S N 1 := by
            simpa [Jbin] using hzbin
          simpa [F] using hbin j hj
    calc
      (1000 * (Nat.log 2 (2 * J.card + 1) + 1)) * 200 ^ t ≤ Q := hthreshold
      _ ≤ (F z).card := hFQ
      _ = 1 * (F z).card := by simp
      _ ≤ 89 ^ t * (F z).card :=
        Nat.mul_le_mul_right (F z).card (one_le_pow₀ (by omega))
  obtain ⟨T, hTcarrier, hTdisj, hTleaves⟩ :=
    PartitionTree.exists_tight_partition t S J F hsub hlarge
  refine ⟨T, hTcarrier, hTdisj, ?_⟩
  refine (hTleaves.and (PartitionTree.allLeaves_subset_carrier T)).mono ?_
  rintro C ⟨hC, hCsub⟩
  have hCS : C ⊆ S := by simpa [hTcarrier] using hCsub
  have hwholeMem : Sum.inl () ∈ J := by simp [J, Jwhole]
  have hwholeRatio := hC (Sum.inl ()) hwholeMem
  have hwholeInter : C ∩ S = C := Finset.inter_eq_left.mpr hCS
  refine ⟨by simpa [F, hwholeInter] using hwholeRatio, ?_, ?_⟩
  · intro e he
    have hz : Sum.inr (Sum.inl e) ∈ J := by
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    simpa [F] using hC (Sum.inr (Sum.inl e)) hz
  · intro j hj
    have hz : Sum.inr (Sum.inr j) ∈ J := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa [F] using hC (Sum.inr (Sum.inr j)) hz

/-- A collision-free lower pool satisfying the phase diversity inequalities
occupies at least a quarter of every pivot modulus after `k` bounded subset
sum steps. -/
lemma boundedSubsetSum_quarter_modulus
    {C : Finset ℕ} {p k : ℕ} (hp : 0 < p)
    (hClt : ∀ c ∈ C, c < p)
    (hdiverse : ∀ e : ℕ, 1 < e → e ∣ p → e * C.card ≤ 2 * p →
      e - 1 ≤ (C.filter fun c ↦ ¬e ∣ c).card)
    (hlog : 4 * (Nat.log 2 p + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ C.card)
    (hmass : 16 * p ≤ k * C.card) :
    p ≤ 4 * ((boundedSubsetSum C k).image
      (fun u : ℕ ↦ (u : ZMod p))).card := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  let R₀ := C.image fun c : ℕ ↦ (c : ZMod p)
  have hinj := natCast_zmod_injOn_of_lt hClt
  have hRcard : R₀.card = C.card :=
    Finset.card_image_iff.mpr hinj
  have hfilter (e : ℕ) (hep : e ∣ p) :
      (R₀.filter fun x => ¬e ∣ x.val).card =
        (C.filter fun c => ¬e ∣ c).card := by
    have heq : R₀.filter (fun x => ¬e ∣ x.val) =
        (C.filter fun c => ¬e ∣ c).image fun c : ℕ ↦ (c : ZMod p) := by
      ext x
      simp only [R₀, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨c, hcC, rfl⟩, hcdiv⟩
        refine ⟨c, ⟨hcC, ?_⟩, rfl⟩
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hClt c hcC)] using hcdiv
      · rintro ⟨c, ⟨hcC, hcdiv⟩, rfl⟩
        refine ⟨⟨c, hcC, rfl⟩, ?_⟩
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hClt c hcC)] using hcdiv
    rw [heq, Finset.card_image_iff.mpr (hinj.mono (Finset.filter_subset _ _))]
  have hphase : PhaseDiverse hp R₀ := by
    apply phaseDiverse_of_bounded hp R₀
    intro e he hep hecard
    rw [hfilter e hep]
    apply hdiverse e he hep
    simpa [hRcard] using hecard
  let E : Finset (ZMod p) := {0}
  have hE : E.Nonempty := by simp [E]
  have halt := bounded_modular_subsetSum_growth hp R₀ E hE hphase
    (by simpa [hRcard] using hlog) (by simpa [hRcard] using hhalf)
  have hlift := modularPhaseSums_subset_bounded_image hp C hClt R₀ rfl hphase
    (by simpa [hRcard] using (show k ≤ C.card by omega))
  have hcardLift :
      (modularPhaseSums hp R₀ E hE hphase k).card ≤
        ((boundedSubsetSum C k).image fun u : ℕ ↦ (u : ZMod p)).card :=
    Finset.card_le_card (by simpa [E] using hlift)
  rcases halt with hfill | hgrowth
  · exact hfill.trans (Nat.mul_le_mul_left 4 hcardLift)
  · have hphaseMass : p ≤ 4 *
        (modularPhaseSums hp R₀ E hE hphase k).card := by
      rw [hRcard] at hgrowth
      omega
    exact hphaseMass.trans (Nat.mul_le_mul_left 4 hcardLift)

/-- Collision-tolerant form of `boundedSubsetSum_quarter_modulus`.  Its
hypotheses are stated directly for the occupied residue set.  The preceding
representative lemma then lifts every modular sum to distinct integers even
when the original reduction map is not injective. -/
lemma boundedSubsetSum_quarter_modulus_of_phase
    {C : Finset ℕ} {p k : ℕ} [NeZero p] (hp : 0 < p)
    (R₀ : Finset (ZMod p))
    (hR₀ : R₀ = C.image fun c : ℕ ↦ (c : ZMod p))
    (hphase : PhaseDiverse hp R₀)
    (hlog : 4 * (Nat.log 2 p + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ R₀.card)
    (hmass : 16 * p ≤ k * R₀.card) :
    p ≤ 4 * ((boundedSubsetSum C k).image
      (fun u : ℕ ↦ (u : ZMod p))).card := by
  classical
  let E : Finset (ZMod p) := {0}
  have hE : E.Nonempty := by simp [E]
  have halt := bounded_modular_subsetSum_growth hp R₀ E hE hphase
    hlog hhalf
  have hk : k ≤ R₀.card := by omega
  have hlift := modularPhaseSums_subset_bounded_image' hp C R₀ hR₀ hphase hk
  have hcardLift :
      (modularPhaseSums hp R₀ E hE hphase k).card ≤
        ((boundedSubsetSum C k).image fun u : ℕ ↦ (u : ZMod p)).card :=
    Finset.card_le_card (by simpa [E] using hlift)
  rcases halt with hfill | hgrowth
  · exact hfill.trans (Nat.mul_le_mul_left 4 hcardLift)
  · have hphaseMass : p ≤ 4 *
        (modularPhaseSums hp R₀ E hE hphase k).card := by
      omega
    exact hphaseMass.trans (Nat.mul_le_mul_left 4 hcardLift)

lemma pivot_modular_cover_of_split
    {D U : Finset ℕ} {G n m d B N p k : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hp : 0 < p)
    (hDN : D ⊆ Finset.Icc 1 N) (hUN : U ⊆ Finset.Icc 1 N)
    (hpN : p ≤ N) (hdN : d * N ≤ n)
    (hB : 2 * G * (n / m + 1) ≤ B)
    (hcore : m ≤ G * D.card)
    (hDlt : ∀ z ∈ D, z < p)
    (hdiv : ∀ e : ℕ, 1 < e → d * e ≤ B →
      e * D.card ≤ 2 * p →
      e - 1 ≤ (D.filter fun z ↦ ¬e ∣ z).card ∨
        (N / p + 1) * (e - 1) ≤
          (U.filter fun z ↦ ¬e ∣ z).card)
    (hlog : 4 * (Nat.log 2 p + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ D.card)
    (hmass : 16 * N ≤ k * D.card) :
    p ≤ 4 * ((boundedSubsetSum (D ∪ U) k).image
      (fun u : ℕ ↦ (u : ZMod p))).card := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  let R₀ := (D ∪ U).image fun z : ℕ ↦ (z : ZMod p)
  have hDcard : D.card ≤ R₀.card := by
    apply card_core_le_card_image_zmod
      (Finset.subset_union_left (s₁ := D) (s₂ := U))
    exact hDlt
  have hphase : PhaseDiverse hp R₀ := by
    apply phaseDiverse_of_split_witnesses hp hDlt hUN
    intro e he hep heR
    have heD : e * D.card ≤ 2 * p := by
      exact (Nat.mul_le_mul_left e hDcard).trans heR
    apply hdiv e he
    have hemp : e * m ≤ 2 * G * p := by
      calc
        e * m ≤ e * (G * D.card) :=
          Nat.mul_le_mul_left e hcore
        _ = G * (e * D.card) := by ring
        _ ≤ G * (2 * p) := Nat.mul_le_mul_left _ heD
        _ = 2 * G * p := by ring
    have hdem : d * e * m ≤ B * m := by
      calc
        d * e * m = d * (e * m) := by ring
        _ ≤ d * (2 * G * p) := Nat.mul_le_mul_left d hemp
        _ ≤ 2 * G * (d * N) := by
          have h := Nat.mul_le_mul_left (2 * G * d) hpN
          convert h using 1 <;> ring
        _ ≤ 2 * G * n := Nat.mul_le_mul_left _ hdN
        _ ≤ (2 * G * (n / m + 1)) * m := by
          have hn : n ≤ (n / m + 1) * m := by
            calc
              n = n / m * m + n % m := by
                simpa [mul_comm] using (Nat.div_add_mod n m).symm
              _ ≤ n / m * m + m :=
                Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hm)) _
              _ = (n / m + 1) * m := by ring
          simpa [mul_assoc] using Nat.mul_le_mul_left (2 * G) hn
        _ ≤ B * m := Nat.mul_le_mul_right m hB
    · exact Nat.le_of_mul_le_mul_right hdem hm
    · exact heD
  have hhalfR : 2 * k ≤ R₀.card := hhalf.trans hDcard
  have hmassR : 16 * p ≤ k * R₀.card := by
    calc
      16 * p ≤ 16 * N := Nat.mul_le_mul_left 16 hpN
      _ ≤ k * D.card := hmass
      _ ≤ k * R₀.card := Nat.mul_le_mul_left k hDcard
  exact boundedSubsetSum_quarter_modulus_of_phase hp R₀ rfl hphase
    hlog hhalfR hmassR

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

noncomputable def pairedPivotSumTree (k : ℕ) :
    {t : ℕ} → PartitionTree ℕ t → PartitionTree ℕ t → SumTree t
  | 0, .leaf C, .leaf P => .leaf (pivotExtended (boundedSubsetSum C k) P)
  | _ + 1, .node C₁ C₂, .node P₁ P₂ =>
      .node (pairedPivotSumTree k C₁ P₁) (pairedPivotSumTree k C₂ P₂)

def AllLeafPairs (Q : Finset ℕ → Finset ℕ → Prop) :
    {t : ℕ} → PartitionTree ℕ t → PartitionTree ℕ t → Prop
  | 0, .leaf C, .leaf P => Q C P
  | _ + 1, .node C₁ C₂, .node P₁ P₂ =>
      AllLeafPairs Q C₁ P₁ ∧ AllLeafPairs Q C₂ P₂

lemma AllLeafPairs.mono {t : ℕ} {A B : PartitionTree ℕ t}
    {P Q : Finset ℕ → Finset ℕ → Prop} (h : AllLeafPairs P A B)
    (hPQ : ∀ C D, P C D → Q C D) : AllLeafPairs Q A B := by
  induction A with
  | leaf C =>
      cases B with
      | leaf D => exact hPQ C D h
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

lemma allLeaves_zipUnion {t : ℕ}
    {A B : PartitionTree ℕ t} {P : Finset ℕ → Finset ℕ → Prop}
    (hP : AllLeafPairs P A B) {Q : Finset ℕ → Prop}
    (hQ : ∀ C D, P C D → Q (C ∪ D)) :
    (zipUnion A B).AllLeaves Q := by
  induction A with
  | leaf C =>
      cases B with
      | leaf D => exact hQ C D hP
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ => exact ⟨ih₁ hP.1, ih₂ hP.2⟩

lemma allLeafPairs_of_allLeaves {t : ℕ}
    {A B : PartitionTree ℕ t} {PA PB : Finset ℕ → Prop}
    (hA : A.AllLeaves PA) (hB : B.AllLeaves PB)
    {Q : Finset ℕ → Finset ℕ → Prop}
    (hQ : ∀ C P, PA C → PB P → Q C P) :
    AllLeafPairs Q A B := by
  induction A with
  | leaf C =>
      cases B with
      | leaf P => exact hQ C P hA hB
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          exact ⟨ih₁ hA.1 hB.1, ih₂ hA.2 hB.2⟩

lemma allLeaves_pairedPivotSumTree_iff {t k : ℕ}
    (A B : PartitionTree ℕ t) (Q : Finset ℕ → Prop) :
    (pairedPivotSumTree k A B).AllLeaves Q ↔
      AllLeafPairs (fun C P ↦ Q (pivotExtended (boundedSubsetSum C k) P)) A B := by
  induction A with
  | leaf C => cases B; rfl
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          simp only [pairedPivotSumTree, SumTree.AllLeaves, AllLeafPairs,
            ih₁, ih₂]

lemma carrier_pairedPivotSumTree_subset_subsetSum {t k : ℕ}
    (A B : PartitionTree ℕ t)
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier) :
    (pairedPivotSumTree k A B).carrier ⊆
      (A.carrier ∪ B.carrier).subsetSum := by
  induction A with
  | leaf C =>
      cases B with
      | leaf P =>
          exact pivotExtended_subset_subsetSum_union hAB
            (boundedSubsetSum_subset_subsetSum C k)
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          rcases hA with ⟨hA₁, hA₂, hA12⟩
          rcases hB with ⟨hB₁, hB₂, hB12⟩
          have hA₁B₁ : Disjoint A₁.carrier B₁.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_left _ hx)
              (fun x hx ↦ Finset.mem_union_left _ hx)
          have hA₂B₂ : Disjoint A₂.carrier B₂.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_right _ hx)
              (fun x hx ↦ Finset.mem_union_right _ hx)
          have hsupport : Disjoint
              (A₁.carrier ∪ B₁.carrier) (A₂.carrier ∪ B₂.carrier) := by
            rw [Finset.disjoint_left]
            intro x hx₁ hx₂
            rw [Finset.mem_union] at hx₁ hx₂
            rcases hx₁ with hxA₁ | hxB₁ <;> rcases hx₂ with hxA₂ | hxB₂
            · exact Finset.disjoint_left.mp hA12 hxA₁ hxA₂
            · exact Finset.disjoint_left.mp hAB
                (Finset.mem_union_left _ hxA₁) (Finset.mem_union_right _ hxB₂)
            · exact Finset.disjoint_left.mp hAB
                (Finset.mem_union_right _ hxA₂) (Finset.mem_union_left _ hxB₁)
            · exact Finset.disjoint_left.mp hB12 hxB₁ hxB₂
          have hsub := (Finset.add_subset_add (ih₁ B₁ hA₁ hB₁ hA₁B₁)
            (ih₂ B₂ hA₂ hB₂ hA₂B₂)).trans
              (subsetSum_add_subset_union hsupport)
          simpa only [pairedPivotSumTree, SumTree.carrier, carrier,
            Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
            using hsub

end PartitionTree

/-! ### Stabilization of finite subset-sum residues -/

/-- All residues modulo `d` represented by finite subset sums of the increasing
enumeration of `A`. -/
noncomputable def residueSubsetSums (A : Set ℕ) (d : ℕ) [NeZero d] :
    Finset (ZMod d) :=
  Finset.univ.filter fun z ↦
    ∃ I : Finset ℕ, (∑ i ∈ I, (Nat.nth (· ∈ A) i : ZMod d)) = z

lemma mem_residueSubsetSums_iff {A : Set ℕ} {d : ℕ} [NeZero d]
    {z : ZMod d} :
    z ∈ residueSubsetSums A d ↔
      ∃ I : Finset ℕ,
        (∑ i ∈ I, (Nat.nth (· ∈ A) i : ZMod d)) = z := by
  simp [residueSubsetSums]

noncomputable def residueWitness (A : Set ℕ) (d : ℕ) [NeZero d]
    (z : residueSubsetSums A d) : Finset ℕ :=
  Classical.choose (mem_residueSubsetSums_iff.mp z.property)

lemma residueWitness_spec (A : Set ℕ) (d : ℕ) [NeZero d]
    (z : residueSubsetSums A d) :
    (∑ i ∈ residueWitness A d z,
      (Nat.nth (· ∈ A) i : ZMod d)) = z :=
  Classical.choose_spec (mem_residueSubsetSums_iff.mp z.property)

noncomputable def residueSupport (A : Set ℕ) (d : ℕ) [NeZero d] : Finset ℕ :=
  (residueSubsetSums A d).attach.biUnion (residueWitness A d)

lemma residueWitness_subset_support (A : Set ℕ) (d : ℕ) [NeZero d]
    (z : residueSubsetSums A d) :
    residueWitness A d z ⊆ residueSupport A d := by
  intro i hi
  rw [residueSupport, Finset.mem_biUnion]
  exact ⟨z, Finset.mem_attach _ _, hi⟩

lemma zero_mem_residueSubsetSums (A : Set ℕ) (d : ℕ) [NeZero d] :
    (0 : ZMod d) ∈ residueSubsetSums A d := by
  rw [mem_residueSubsetSums_iff]
  exact ⟨∅, by simp⟩

/-- Once every chosen residue witness is supported below an index, every later
term translates the finite residue set into itself and hence stabilizes it. -/
lemma eventual_cast_mem_residue_stabilizer (A : Set ℕ) (d : ℕ) [NeZero d] :
    ∀ j, (residueSupport A d).sup id < j →
      (Nat.nth (· ∈ A) j : ZMod d) ∈
        AddAction.stabilizer (ZMod d) (residueSubsetSums A d) := by
  intro j hj
  rw [AddAction.mem_stabilizer_finset']
  intro z hz
  let z' : residueSubsetSums A d := ⟨z, hz⟩
  let I := residueWitness A d z'
  have hjI : j ∉ I := by
    intro hjI
    have hjsupp : j ∈ residueSupport A d :=
      residueWitness_subset_support A d z' hjI
    have := Finset.le_sup (f := id) hjsupp
    exact (not_le_of_gt hj) (by simpa using this)
  rw [mem_residueSubsetSums_iff]
  refine ⟨insert j I, ?_⟩
  rw [Finset.sum_insert hjI]
  change (Nat.nth (· ∈ A) j : ZMod d) +
      (∑ i ∈ I, (Nat.nth (· ∈ A) i : ZMod d)) = _
  rw [residueWitness_spec A d z']
  rfl

lemma residue_stabilizer_subset (A : Set ℕ) (d : ℕ) [NeZero d] :
    (AddAction.stabilizer (ZMod d) (residueSubsetSums A d) : Set (ZMod d)) ⊆
      residueSubsetSums A d := by
  intro z hz
  have hzero := zero_mem_residueSubsetSums A d
  have := (AddAction.mem_stabilizer_finset'.mp hz) hzero
  simpa using this

/-- Residue stabilization.  Modulo any positive `d`, a finite initial part of
an infinite set supplies every multiple of a divisor `q ∣ d`, while every
remaining element is divisible by `q`. -/
theorem exists_residue_stabilization {A : Set ℕ} (hAinf : A.Infinite)
    {d : ℕ} (hd : 0 < d) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧ ∃ F : Finset ℕ,
      (↑F : Set ℕ) ⊆ A ∧
      (∀ a ∈ A \ (↑F : Set ℕ), q ∣ a) ∧
      (∀ i < d / q, ∃ u ∈ subsetSums (↑F : Set ℕ),
        (u : ZMod d) = (i * q : ZMod d)) := by
  letI : NeZero d := ⟨hd.ne'⟩
  let K := AddAction.stabilizer (ZMod d) (residueSubsetSums A d)
  obtain ⟨q, hqpos, hqd, hKdiv, hmultK⟩ := exists_generator_modulus hd K
  let n₀ := (residueSupport A d).sup id + 1
  let y : ℕ → ℕ := Nat.nth (· ∈ A)
  let F := (Finset.range n₀).image y
  refine ⟨q, hqpos, hqd, F, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_image] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact nth_mem hAinf j
  · intro a ha
    let j := Nat.count (· ∈ A) a
    have hyj : y j = a := by
      exact Nat.nth_count ha.1
    have hjlarge : (residueSupport A d).sup id < j := by
      by_contra hnot
      have hjrange : j ∈ Finset.range n₀ := by
        rw [Finset.mem_range]
        dsimp [n₀]
        omega
      have haF : a ∈ F := by
        change a ∈ (Finset.range n₀).image y
        rw [Finset.mem_image]
        exact ⟨j, hjrange, hyj⟩
      exact ha.2 haF
    have hjK : (y j : ZMod d) ∈ K :=
      eventual_cast_mem_residue_stabilizer A d j hjlarge
    have hqmod : q ∣ (y j : ZMod d).val := hKdiv _ hjK
    have hqrem : q ∣ y j % d := by
      simpa [ZMod.val_natCast] using hqmod
    have hqdpart : q ∣ d * (y j / d) := dvd_mul_of_dvd_left hqd _
    rw [← hyj]
    rw [← Nat.mod_add_div (y j) d]
    exact dvd_add hqrem hqdpart
  · intro i hi
    have hiK : (i * q : ZMod d) ∈ K := hmultK i
    have hiH : (i * q : ZMod d) ∈ residueSubsetSums A d :=
      residue_stabilizer_subset A d hiK
    let z : residueSubsetSums A d := ⟨(i * q : ZMod d), hiH⟩
    let I := residueWitness A d z
    let G := I.image y
    have hIrange : I ⊆ Finset.range n₀ := by
      intro j hjI
      have hjsupp : j ∈ residueSupport A d :=
        residueWitness_subset_support A d z hjI
      have hjle := Finset.le_sup (f := id) hjsupp
      rw [Finset.mem_range]
      dsimp [n₀]
      simpa using Nat.lt_succ_of_le (by simpa using hjle)
    have hGF : G ⊆ F := by
      change I.image y ⊆ (Finset.range n₀).image y
      intro g hg
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_image.mpr ⟨j, hIrange hj, rfl⟩
    have hsum : ∑ g ∈ G, g = ∑ j ∈ I, y j := by
      change ∑ g ∈ I.image y, g = ∑ j ∈ I, y j
      rw [Finset.sum_image (nth_strictMono hAinf).injective.injOn]
    refine ⟨∑ g ∈ G, g, ?_, ?_⟩
    · exact ⟨G, fun g hg ↦ hGF hg, rfl⟩
    · rw [hsum]
      simpa [I, y, z] using residueWitness_spec A d z

lemma subsetSum_le_sum {F : Finset ℕ} {u : ℕ}
    (hu : u ∈ subsetSums (↑F : Set ℕ)) : u ≤ ∑ f ∈ F, f := by
  obtain ⟨G, hGF, rfl⟩ := hu
  exact Finset.sum_le_sum_of_subset hGF

lemma exists_eq_add_mul_of_zmod_eq {u r d : ℕ} (_hd : 0 < d) (hr : r < d)
    (h : (u : ZMod d) = (r : ZMod d)) :
    ∃ z : ℕ, u = r + d * z := by
  letI : NeZero d := ⟨_hd.ne'⟩
  have hmod : u % d = r := by
    have := (ZMod.natCast_eq_natCast_iff' u r d).mp h
    simpa [Nat.mod_eq_of_lt hr] using this
  refine ⟨u / d, ?_⟩
  calc
    u = u % d + d * (u / d) := (Nat.mod_add_div u d).symm
    _ = r + d * (u / d) := by rw [hmod]

/-- The endgame used in Szemerédi--Vu's infinite argument.  One dense part
provides arbitrarily long progressions of a fixed step.  The other part
stabilizes its subset-sum residues, lowers that step, and provides the
additive net that extends the resulting finite progression forever. -/
theorem fixedStep_and_dense_residue_part
    {A B R : Set ℕ}
    (hRpos : R ⊆ Set.Ici 1) (hRdense : SqrtDense 4 R)
    (hBR : Disjoint B R) (hunion : B ∪ R = A)
    (hfixed : HasFixedStepProgressions (subsetSums B)) :
    ContainsInfiniteAP (subsetSums A) := by
  have hRinf : R.Infinite := infinite_of_sqrtDense (by norm_num) hRdense
  obtain ⟨d, hd, hlong⟩ := hfixed
  obtain ⟨q, hqpos, hqd, F, hFR, htailq, hresmod⟩ :=
    exists_residue_stabilization hRinf hd
  let C : Set ℕ := R \ (↑F : Set ℕ)
  have hCpos : C ⊆ Set.Ici 1 := fun _ hx ↦ hRpos hx.1
  have hCdense : SqrtDense 3 C := by
    exact sqrtDense_sdiff_finite (by norm_num : (3 : ℝ) < 4)
      F.finite_toSet hRdense
  obtain ⟨K, hnet⟩ := exists_addNet_subsetSums_of_sqrtDense
    hCpos hCdense hqpos htailq
  let M := d / q
  have hqle : q ≤ d := Nat.le_of_dvd hd hqd
  have hMpos : 0 < M := Nat.div_pos hqle hqpos
  have hdEq : q * M = d := Nat.mul_div_cancel' hqd
  let Z := ∑ f ∈ F, f
  let L := Z + (K + 1)
  obtain ⟨a, ha⟩ := hlong L
  have hAP : ∀ j < L, a + j * (q * M) ∈ subsetSums B := by
    simpa [hdEq] using ha
  have hres : ∀ i < M, ∃ u ∈ subsetSums (↑F : Set ℕ),
      ∃ z ≤ Z, u = i * q + (q * M) * z := by
    intro i hi
    obtain ⟨u, huF, hucong⟩ := hresmod i (by simpa [M] using hi)
    have hiqd : i * q < d := by
      rw [← hdEq]
      nlinarith
    have hucong' : (u : ZMod d) = (i * q : ℕ) := by
      simpa only [Nat.cast_mul] using hucong
    obtain ⟨z, huz⟩ := exists_eq_add_mul_of_zmod_eq hd hiqd hucong'
    have hz : z ≤ Z := by
      have hdz : z ≤ d * z := Nat.le_mul_of_pos_left z hd
      have hdzu : d * z ≤ u := by omega
      have hzu : z ≤ u := hdz.trans hdzu
      simpa [Z] using hzu.trans (subsetSum_le_sum huF)
    refine ⟨u, huF, z, hz, ?_⟩
    simpa [hdEq, mul_comm] using huz
  have hLsub : L - Z = K + 1 := by simp [L]
  have hlength : K + 1 ≤ M * (L - Z) := by
    rw [hLsub]
    nlinarith
  have hlowered : ∀ n < M * (L - Z),
      (a + (q * M) * Z) + n * q ∈
        subsetSums B + subsetSums (↑F : Set ℕ) :=
    lowerStep_of_residue_translates_mem hqpos hMpos hAP hres
  let D : Set ℕ := B ∪ (↑F : Set ℕ)
  have hBF : Disjoint B (↑F : Set ℕ) := hBR.mono_right hFR
  have hAPD : ∀ n < K + 1,
      (a + (q * M) * Z) + n * q ∈ subsetSums D := by
    intro n hn
    apply subsetSums_union_subset_add hBF
    exact hlowered n (hn.trans_le hlength)
  have hDC : Disjoint D C := by
    rw [Set.disjoint_left]
    rintro x (hxB | hxF) ⟨hxR, hxnotF⟩
    · exact Set.disjoint_left.1 hBR hxB hxR
    · exact hxnotF hxF
  have hinfSum : ContainsInfiniteAP (subsetSums D + subsetSums C) :=
    addNet_add_finiteAP hnet hAPD
  have hinfDU : ContainsInfiniteAP (subsetSums (D ∪ C)) :=
    containsInfiniteAP_mono (subsetSums_union_subset_add hDC) hinfSum
  have hDU : D ∪ C = A := by
    change (B ∪ (↑F : Set ℕ)) ∪ (R \ (↑F : Set ℕ)) = A
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Finset.mem_coe]
    constructor
    · rintro ((hxB | hxF) | ⟨hxR, -⟩)
      · exact hunion ▸ Or.inl hxB
      · exact hunion ▸ Or.inr (hFR hxF)
      · exact hunion ▸ Or.inr hxR
    · intro hxA
      have hxBR : x ∈ B ∨ x ∈ R := by
        have : x ∈ B ∪ R := by
          rw [hunion]
          exact hxA
        simpa only [Set.mem_union] using this
      rcases hxBR with hxB | hxR
      · exact Or.inl (Or.inl hxB)
      · by_cases hxF : x ∈ F
        · exact Or.inl (Or.inr hxF)
        · exact Or.inr ⟨hxR, hxF⟩
  rw [hDU] at hinfDU
  exact hinfDU

/-! ### Merging progressions while decreasing the common difference -/

lemma coprime_AP_residues {q M r : ℕ}
    (_hq : 0 < q) (hM : 0 < M) (hr : 0 < r) (hcop : M.Coprime r) :
    ∀ i < M, ∃ t < M, ∃ z ≤ r,
      t * (q * r) = i * q + (q * M) * z := by
  letI : NeZero M := ⟨hM.ne'⟩
  let ur : (ZMod M)ˣ := ZMod.unitOfCoprime r hcop.symm
  intro i hi
  let x : ZMod M := (i : ZMod M) * (ur⁻¹ : (ZMod M)ˣ)
  let t := x.val
  have htM : t < M := x.val_lt
  have htrCast : (t * r : ZMod M) = (i : ZMod M) := by
    change (x.val : ZMod M) * (r : ZMod M) = (i : ZMod M)
    rw [ZMod.natCast_zmod_val x]
    change ((i : ZMod M) * (↑(ur⁻¹) : ZMod M)) * (r : ZMod M) = i
    have hur : (r : ZMod M) = (ur : ZMod M) := rfl
    rw [hur]
    simp [mul_assoc]
  obtain ⟨z, htr⟩ := exists_eq_add_mul_of_zmod_eq
    (u := t * r) (r := i) (d := M) hM hi (by
      simpa only [Nat.cast_mul] using htrCast)
  have hz : z ≤ r := by
    have htz : M * z ≤ t * r := by omega
    have htrlt : t * r < M * r := (Nat.mul_lt_mul_right hr).2 htM
    have hmz : M * z < M * r := htz.trans_lt htrlt
    exact ((Nat.mul_lt_mul_left hM).mp hmz).le
  refine ⟨t, htM, z, hz, ?_⟩
  calc
    t * (q * r) = q * (t * r) := by ring
    _ = q * (i + M * z) := by rw [htr]
    _ = i * q + (q * M) * z := by ring

/-- The sum of a `q*M` progression and a sufficiently long `q*r`
progression contains a long `q` progression when `M` and `r` are coprime. -/
lemma merge_AP_by_gcd {S U : Set ℕ}
    {a b q M r LS LU : ℕ}
    (hq : 0 < q) (hM : 0 < M) (hr : 0 < r) (hcop : M.Coprime r)
    (hMU : M ≤ LU)
    (hS : ∀ j < LS, a + j * (q * M) ∈ S)
    (hU : ∀ t < LU, b + t * (q * r) ∈ U) :
    ∀ n < M * (LS - r),
      (a + b + (q * M) * r) + n * q ∈ S + U := by
  let U₀ : Set ℕ := {u | b + u ∈ U}
  have hres : ∀ i < M, ∃ u ∈ U₀, ∃ z ≤ r,
      u = i * q + (q * M) * z := by
    intro i hi
    obtain ⟨t, htM, z, hzr, heq⟩ := coprime_AP_residues hq hM hr hcop i hi
    refine ⟨t * (q * r), ?_, z, hzr, heq⟩
    exact hU t (htM.trans_le hMU)
  intro n hn
  have hx := lowerStep_of_residue_translates_mem hq hM hS hres n hn
  obtain ⟨s, hs, u, hu, hsum⟩ := hx
  change s + u = (a + (q * M) * r) + n * q at hsum
  refine ⟨s, hs, b + u, hu, ?_⟩
  calc
    s + (b + u) = b + (s + u) := by omega
    _ = b + ((a + (q * M) * r) + n * q) := by rw [hsum]
    _ = (a + b + (q * M) * r) + n * q := by omega

/-- Rank-two geometry in the form used by the finite Szemerédi--Vu proof.
The Minkowski sum of two sufficiently long progressions whose normalized
steps are coprime contains a progression with their gcd as common step. -/
lemma containsFiniteAP_add_of_coprime_steps {S U : Set ℕ}
    {a b q M r LS LU : ℕ}
    (hq : 0 < q) (hM : 0 < M) (hr : 0 < r) (hcop : M.Coprime r)
    (hMU : M ≤ LU)
    (hS : ∀ j < LS, a + j * (q * M) ∈ S)
    (hU : ∀ t < LU, b + t * (q * r) ∈ U) :
    ContainsFiniteAP (S + U) (M * (LS - r)) := by
  refine ⟨a + b + (q * M) * r, q, hq, ?_⟩
  intro n hn
  simpa [mul_comm] using
    merge_AP_by_gcd hq hM hr hcop hMU hS hU n hn

/-! ### A binary-tree filling lemma -/

namespace SumTree

lemma zero_mem_carrier {t : ℕ} {T : SumTree t}
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S) : 0 ∈ T.carrier := by
  induction T with
  | leaf S => exact hzero
  | node left right ihl ihr =>
      exact Finset.add_mem_add (ihl hzero.1) (ihr hzero.2)

lemma carrier_subset_Icc {t m : ℕ} {T : SumTree t}
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m) :
    T.carrier ⊆ Finset.Icc 0 (2 ^ t * m) := by
  induction T with
  | leaf S => simpa [carrier, AllLeaves] using hbox
  | @node t left right ihl ihr =>
      intro z hz
      rw [carrier, Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hx' := Finset.mem_Icc.mp (ihl hbox.1 hx)
      have hy' := Finset.mem_Icc.mp (ihr hbox.2 hy)
      apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.zero_le _
      · calc
          x + y ≤ 2 ^ t * m + 2 ^ t * m := Nat.add_le_add hx'.2 hy'.2
          _ = 2 ^ t * 2 * m := by ring
          _ = 2 ^ (t + 1) * m := by rw [pow_succ]

lemma card_carrier_le {t m : ℕ} {T : SumTree t}
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m) :
    T.carrier.card ≤ 2 ^ t * m + 1 := by
  have hsub := carrier_subset_Icc hbox
  have hcard := Finset.card_le_card hsub
  simpa using hcard

private lemma left_subset_carrier {t : ℕ} (left right : SumTree t)
    (hzero : 0 ∈ right.carrier) :
    (left.carrier : Set ℕ) ⊆ ((SumTree.node left right).carrier : Finset ℕ) := by
  intro x hx
  exact Finset.add_mem_add hx hzero

private lemma right_subset_carrier {t : ℕ} (left right : SumTree t)
    (hzero : 0 ∈ left.carrier) :
    (right.carrier : Set ℕ) ⊆ ((SumTree.node left right).carrier : Finset ℕ) := by
  intro x hx
  change x ∈ left.carrier + right.carrier
  simpa using Finset.add_mem_add hzero hx

/-- Tree alternative behind the rank-one filling argument: either a merge
has already produced a progression of the initial target length, or all
merges grow and the root has the corresponding recursively forced size. -/
lemma containsAP_or_card_growth {t k : ℕ} {T : SumTree t} (hk : 2 ≤ k)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ k ≤ S.card) :
    ContainsFiniteAP (T.carrier : Set ℕ) (2 * k - 1) ∨
      growthLower k t ≤ T.carrier.card := by
  induction T with
  | leaf S =>
      right
      simpa [carrier, AllLeaves, growthLower] using hcard
  | @node t left right ihl ihr =>
      rcases ihl hzero.1 hcard.1 with hAP | hleft
      · left
        exact containsFiniteAP_mono
          (left_subset_carrier left right (zero_mem_carrier hzero.2)) hAP
      rcases ihr hzero.2 hcard.2 with hAP | hright
      · left
        exact containsFiniteAP_mono
          (right_subset_carrier left right (zero_mem_carrier hzero.1)) hAP
      have hleftne : left.carrier.Nonempty := ⟨0, zero_mem_carrier hzero.1⟩
      have hrightne : right.carrier.Nonempty := ⟨0, zero_mem_carrier hzero.2⟩
      rcases Erdos13Additive.growth_or_long_AP hleftne hrightne with hgrow | hprog
      · right
        rw [growthLower]
        have hmin : growthLower k t ≤
            min left.carrier.card right.carrier.card := by
          exact le_min hleft hright
        have hsum : 3 * growthLower k t ≤
            left.carrier.card + right.carrier.card +
              min left.carrier.card right.carrier.card := by
          omega
        have hroot : left.carrier + right.carrier =
            (SumTree.node left right).carrier := rfl
        rw [hroot] at hgrow
        omega
      · left
        obtain ⟨a, d, hd, hprog, -⟩ := hprog
        refine ⟨a, d, hd, ?_⟩
        intro i hi
        apply hprog
        rw [Erdos13Additive.mem_natAP]
        refine ⟨i, ?_, ?_⟩
        · have hkleft : k ≤ left.carrier.card :=
            (growthLower_ge hk t).trans hleft
          have hkright : k ≤ right.carrier.card :=
            (growthLower_ge hk t).trans hright
          omega
        · simp [mul_comm]

/-- Quantitative rank-one filling lemma.  If a perfect family of dense
one-dimensional leaves is deep enough that perpetual growth would exceed the
ambient interval, its iterated sum contains a long arithmetic progression. -/
theorem containsFiniteAP_of_growth_exceeds_diameter
    {t k m : ℕ} {T : SumTree t} (hk : 2 ≤ k)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ k ≤ S.card)
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m)
    (hexceed : 2 ^ t * m + 1 < growthLower k t) :
    ContainsFiniteAP (T.carrier : Set ℕ) (2 * k - 1) := by
  rcases containsAP_or_card_growth hk hzero hcard with hAP | hgrowth
  · exact hAP
  · have hupp := card_carrier_le hbox
    omega

end SumTree

/-- Final rank-one wrapper for a pair of aligned partition trees.  The leaf
hypothesis records precisely the modular coverage, pivot mass, target mass,
and diameter facts used by the sum-tree argument. -/
theorem containsFiniteAP_of_paired_pivots
    {t phase K box : ℕ} (A B : PartitionTree ℕ t)
    (hK : 2 ≤ K)
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier)
    (hleaf : PartitionTree.AllLeafPairs (fun C P ↦
      (∀ p ∈ P, 0 < p) ∧
      (∀ p ∈ P, p ≤ 4 * ((boundedSubsetSum C phase).image
        (fun u : ℕ ↦ (u : ZMod p))).card) ∧
      8 * P.card ≤ ∑ p ∈ P, p ∧
      8 * K ≤ ∑ p ∈ P, p ∧
      pivotExtended (boundedSubsetSum C phase) P ⊆ Finset.Icc 0 box) A B)
    (hexceed : 2 ^ t * box + 1 < SumTree.growthLower K t) :
    ContainsFiniteAP ((A.carrier ∪ B.carrier).subsetSum : Set ℕ)
      (2 * K - 1) := by
  let T := PartitionTree.pairedPivotSumTree phase A B
  have hzero : T.AllLeaves fun S ↦ 0 ∈ S := by
    rw [PartitionTree.allLeaves_pairedPivotSumTree_iff]
    refine hleaf.mono ?_
    intro C P _
    exact Finset.mem_add.mpr
      ⟨0, zero_mem_boundedSubsetSum C phase,
        0, Finset.zero_mem_subsetSum, by omega⟩
  have hcard : T.AllLeaves fun S ↦ K ≤ S.card := by
    rw [PartitionTree.allLeaves_pairedPivotSumTree_iff]
    refine hleaf.mono ?_
    intro C P h
    have hpivot := card_pivotExtended_ge_sum_div_eight
      (boundedSubsetSum C phase) P h.1 h.2.1 h.2.2.1
    omega
  have hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 box := by
    rw [PartitionTree.allLeaves_pairedPivotSumTree_iff]
    exact hleaf.mono fun C P h ↦ h.2.2.2.2
  have hAP := SumTree.containsFiniteAP_of_growth_exceeds_diameter
    hK hzero hcard hbox hexceed
  exact containsFiniteAP_mono
    (PartitionTree.carrier_pairedPivotSumTree_subset_subsetSum
      A B hA hB hAB) hAP

/-! ### The small-doubling rank-one containment step -/

/-- Integer-ratio form of the Lev--Smelianski step needed in the filling
argument.  Equal-size sets with sumset at most `2.1` times their size lie in
an arithmetic progression of at most `1.1 m + 1` terms.  This ordered-diameter
form is the algebraic core; the symmetric wrapper follows below. -/
private lemma small_sumset_contained_AP_of_diameter_le
    {S T : Finset ℕ} {m : ℕ}
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hScard : S.card = m) (hTcard : T.card = m) (hm : 30 ≤ m)
    (hsmall : 10 * (S + T).card ≤ 21 * m)
    (hdiam : S.max' hSne - S.min' hSne ≤ T.max' hTne - T.min' hTne) :
    ∃ a b d L : ℕ, 0 < d ∧ 10 * L ≤ 11 * m + 10 ∧
      S ⊆ Erdos13Additive.natAP a d L ∧
      T ⊆ Erdos13Additive.natAP b d L := by
  let s := S.min' hSne
  let t := T.min' hTne
  let sM := S.max' hSne
  let tM := T.max' hTne
  let u := sM - s
  let v := tM - t
  have hsS : s ∈ S := S.min'_mem hSne
  have htT : t ∈ T := T.min'_mem hTne
  have hsMS : sM ∈ S := S.max'_mem hSne
  have htMT : tM ∈ T := T.max'_mem hTne
  have hSmin : ∀ x ∈ S, s ≤ x := fun x hx ↦ S.min'_le x hx
  have hTmin : ∀ x ∈ T, t ≤ x := fun x hx ↦ T.min'_le x hx
  have hSmax : ∀ x ∈ S, x ≤ sM := fun x hx ↦ S.le_max' x hx
  have hTmax : ∀ x ∈ T, x ≤ tM := fun x hx ↦ T.le_max' x hx
  have huv : u ≤ v := by simpa [u, v, s, t, sM, tM] using hdiam
  have hvpos : 0 < v := by
    by_contra hv
    have hvzero : v = 0 := Nat.eq_zero_of_not_pos hv
    have hTeq : T = {t} := by
      ext x
      constructor
      · intro hx
        have hxmin := hTmin x hx
        have hxmax := hTmax x hx
        have htMt : tM = t := by dsimp [v] at hvzero; omega
        simp only [Finset.mem_singleton]
        omega
      · intro hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact htT
    have : T.card = 1 := by simp [hTeq]
    omega
  let S₁ := Erdos13Additive.normalizeNat S s 1
  let T₁ := Erdos13Additive.normalizeNat T t 1
  let W := S₁ ∪ T₁
  let d := W.gcd (fun n : ℕ ↦ n)
  have huS₁ : u ∈ S₁ := by
    have h := Erdos13Additive.top_mem_normalizeNat (m := s) (d := 1) hsMS
    simpa [S₁, u, sM, s] using h
  have hvT₁ : v ∈ T₁ := by
    have h := Erdos13Additive.top_mem_normalizeNat (m := t) (d := 1) htMT
    simpa [T₁, v, tM, t] using h
  have hvW : v ∈ W := Finset.mem_union_right S₁ hvT₁
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hz := (Finset.gcd_eq_zero_iff.mp hd) v hvW
    omega
  have hSdiv : ∀ x ∈ S, d ∣ x - s := by
    intro x hx
    apply Finset.gcd_dvd
    apply Finset.mem_union_left T₁
    apply Erdos13Additive.mem_normalizeNat.mpr
    exact ⟨x, hx, by simp⟩
  have hTdiv : ∀ x ∈ T, d ∣ x - t := by
    intro x hx
    apply Finset.gcd_dvd
    apply Finset.mem_union_right S₁
    apply Erdos13Additive.mem_normalizeNat.mpr
    exact ⟨x, hx, by simp⟩
  have hdv : d ∣ v := Finset.gcd_dvd hvW
  have hdvle : d ≤ v := Nat.le_of_dvd hvpos hdv
  have hvqpos : 0 < v / d := Nat.div_pos hdvle hdpos
  let A := Erdos13Additive.normalizeNat S s d
  let B := Erdos13Additive.normalizeNat T t d
  have hAint : A ⊆ Finset.Icc 0 (u / d) := by
    apply Erdos13Additive.normalizeNat_subset_Icc
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hSmin x hx, hSmax x hx⟩
  have hBint : B ⊆ Finset.Icc 0 (v / d) := by
    apply Erdos13Additive.normalizeNat_subset_Icc
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hTmin x hx, hTmax x hx⟩
  have hAzero : 0 ∈ A := Erdos13Additive.zero_mem_normalizeNat hsS
  have hBzero : 0 ∈ B := Erdos13Additive.zero_mem_normalizeNat htT
  have hAtop : u / d ∈ A := by
    simpa [A, u, sM, s] using
      (Erdos13Additive.top_mem_normalizeNat (m := s) (d := d) hsMS)
  have hBtop : v / d ∈ B := by
    simpa [B, v, tM, t] using
      (Erdos13Additive.top_mem_normalizeNat (m := t) (d := d) htMT)
  have hqorder : u / d ≤ v / d := Nat.div_le_div_right huv
  have hABW : A ∪ B = W.image (fun z ↦ z / d) := by
    ext q
    simp only [A, B, W, S₁, T₁, Erdos13Additive.normalizeNat,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact ⟨x - s, Or.inl ⟨x, hx, by simp⟩, rfl⟩
      · exact ⟨y - t, Or.inr ⟨y, hy, by simp⟩, rfl⟩
    · rintro ⟨z, (⟨x, hx, hxz⟩ | ⟨y, hy, hyz⟩), rfl⟩
      · left
        refine ⟨x, hx, ?_⟩
        simpa using congrArg (fun n ↦ n / d) hxz
      · right
        refine ⟨y, hy, ?_⟩
        simpa using congrArg (fun n ↦ n / d) hyz
  have hWgcd : W.gcd (fun z ↦ z / d) = 1 := by
    exact Finset.gcd_div_id_eq_one hvW hvpos.ne'
  have hABgcdNat : (A ∪ B).gcd (fun n : ℕ ↦ n) = 1 := by
    rw [hABW, Finset.gcd_image]
    exact hWgcd
  have hABgcdInt : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1 := by
    rw [Erdos13Additive.nat_int_finset_gcd, hABgcdNat]
    norm_num
  have hAcard : A.card = m := by
    rw [Erdos13Additive.card_normalizeNat hdpos hSmin hSdiv, hScard]
  have hBcard : B.card = m := by
    rw [Erdos13Additive.card_normalizeNat hdpos hTmin hTdiv, hTcard]
  have hsumcard : (A + B).card = (S + T).card := by
    symm
    exact Erdos13Additive.card_sumset_eq_card_normalized
      hdpos hSmin hTmin hSdiv hTdiv
  have hruzsa := Erdos13Additive.ruzsa_normalized_diameter_bound
    hAint hBint hqorder hvqpos hAzero hAtop hBzero hBtop hABgcdInt
  have hthree : (A + B).card < 3 * m - 3 := by
    rw [hsumcard]
    omega
  have hdiameter : m + v / d ≤ (A + B).card := by
    rw [hAcard, hBcard] at hruzsa
    by_contra hnot
    have hfirst : (A + B).card < m + v / d := Nat.lt_of_not_ge hnot
    have hminlt : (A + B).card <
        min (m + v / d) (m + m + min m m - 3) := by
      apply lt_min
      · exact hfirst
      · have heq : m + m + min m m - 3 = 3 * m - 3 := by
          simp only [min_self]
          omega
        simpa only [heq] using hthree
    exact (not_lt_of_ge hruzsa) hminlt
  have hvbound : 10 * (v / d + 1) ≤ 11 * m + 10 := by
    rw [hsumcard] at hdiameter
    omega
  refine ⟨s, t, d, v / d + 1, hdpos, hvbound, ?_, ?_⟩
  · intro x hx
    have hqmem : (x - s) / d ∈ A :=
      Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hqle : (x - s) / d ≤ v / d :=
      (Finset.mem_Icc.mp (hAint hqmem)).2.trans hqorder
    apply Erdos13Additive.mem_natAP.mpr
    refine ⟨(x - s) / d, by omega, ?_⟩
    have hsx : s ≤ x := hSmin x hx
    calc
      s + d * ((x - s) / d) = s + (x - s) := by
        rw [Nat.mul_div_cancel' (hSdiv x hx)]
      _ = x := Nat.add_sub_of_le hsx
  · intro x hx
    have hqmem : (x - t) / d ∈ B :=
      Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hqle : (x - t) / d ≤ v / d :=
      (Finset.mem_Icc.mp (hBint hqmem)).2
    apply Erdos13Additive.mem_natAP.mpr
    refine ⟨(x - t) / d, by omega, ?_⟩
    have htx : t ≤ x := hTmin x hx
    calc
      t + d * ((x - t) / d) = t + (x - t) := by
        rw [Nat.mul_div_cancel' (hTdiv x hx)]
      _ = x := Nat.add_sub_of_le htx

/-- Symmetric small-doubling containment lemma. -/
lemma small_sumset_contained_AP
    {S T : Finset ℕ} {m : ℕ}
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hScard : S.card = m) (hTcard : T.card = m) (hm : 30 ≤ m)
    (hsmall : 10 * (S + T).card ≤ 21 * m) :
    ∃ a d L : ℕ, 0 < d ∧ 10 * L ≤ 11 * m + 10 ∧
      S ⊆ Erdos13Additive.natAP a d L := by
  rcases le_total (S.max' hSne - S.min' hSne) (T.max' hTne - T.min' hTne) with h | h
  · obtain ⟨a, -, d, L, hd, hL, hS, -⟩ :=
      small_sumset_contained_AP_of_diameter_le
        hSne hTne hScard hTcard hm hsmall h
    exact ⟨a, d, L, hd, hL, hS⟩
  · obtain ⟨-, a, d, L, hd, hL, -, hS⟩ :=
      small_sumset_contained_AP_of_diameter_le
        hTne hSne hTcard hScard hm (by simpa [add_comm] using hsmall) h
    exact ⟨a, d, L, hd, hL, hS⟩

/-! ### Dyadic blocks and a fixed progression difference -/

private def blockScale (m i : ℕ) : ℕ := 2 ^ i * m

private lemma blockScale_succ (m i : ℕ) :
    blockScale m (i + 1) = 2 * blockScale m i := by
  simp [blockScale, pow_succ]
  ring

noncomputable def svBlock (A : Set ℕ) (H m i : ℕ) : Finset ℕ :=
  (Finset.Ico (H * blockScale m i) (H * blockScale m (i + 1))).image
    (Nat.nth (· ∈ A))

noncomputable def svUsed (A : Set ℕ) (H m i : ℕ) : Finset ℕ :=
  (Finset.Ico (H * m) (H * blockScale m (i + 1))).image
    (Nat.nth (· ∈ A))

lemma card_svBlock {A : Set ℕ} (hAinf : A.Infinite) (H m i : ℕ) :
    (svBlock A H m i).card = H * blockScale m i := by
  rw [svBlock, Finset.card_image_iff.mpr (nth_strictMono hAinf).injective.injOn]
  rw [Nat.card_Ico]
  rw [blockScale_succ]
  have heq : H * (2 * blockScale m i) = 2 * (H * blockScale m i) := by ring
  rw [heq]
  omega

lemma svBlock_subset {A : Set ℕ} (hAinf : A.Infinite) (H m i : ℕ) :
    (↑(svBlock A H m i) : Set ℕ) ⊆ A := by
  intro a ha
  rw [Finset.mem_coe, svBlock, Finset.mem_image] at ha
  obtain ⟨j, -, rfl⟩ := ha
  exact nth_mem hAinf j

lemma svUsed_subset {A : Set ℕ} (hAinf : A.Infinite) (H m i : ℕ) :
    (↑(svUsed A H m i) : Set ℕ) ⊆ A := by
  intro a ha
  rw [Finset.mem_coe, svUsed, Finset.mem_image] at ha
  obtain ⟨j, -, rfl⟩ := ha
  exact nth_mem hAinf j

private lemma index_le_pow_two (i : ℕ) : i ≤ 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ i := pow_pos (by omega) _
      omega

lemma index_le_half_blockScale_sq {m i : ℕ} (hm : 2 ≤ m) :
    i ≤ blockScale m i ^ 2 / 2 := by
  have hie : i ≤ blockScale m i := by
    calc
      i ≤ 2 ^ i := index_le_pow_two i
      _ ≤ 2 ^ i * m := Nat.le_mul_of_pos_right _ (by omega)
      _ = blockScale m i := rfl
  have he2 : 2 ≤ blockScale m i := by
    calc
      2 ≤ m := hm
      _ ≤ blockScale m i :=
        Nat.le_mul_of_pos_left m (pow_pos (by omega) _)
  apply (Nat.le_div_iff_mul_le (by omega)).2
  calc
    i * 2 ≤ blockScale m i * 2 := Nat.mul_le_mul_right 2 hie
    _ ≤ blockScale m i * blockScale m i :=
      Nat.mul_le_mul_left _ he2
    _ = blockScale m i ^ 2 := by ring

lemma svUsed_zero (A : Set ℕ) (H m : ℕ) :
    svUsed A H m 0 = svBlock A H m 0 := by
  unfold svUsed svBlock
  congr 1
  ext j
  simp [blockScale]

lemma svUsed_succ (A : Set ℕ) (H m i : ℕ) :
    svUsed A H m (i + 1) = svUsed A H m i ∪ svBlock A H m (i + 1) := by
  rw [svUsed, svUsed, svBlock, ← Finset.image_union]
  congr 1
  symm
  apply Finset.Ico_union_Ico_eq_Ico
  · have : m ≤ blockScale m (i + 1) := by
      exact Nat.le_mul_of_pos_left m (pow_pos (by omega) _)
    exact Nat.mul_le_mul_left H this
  · apply Nat.mul_le_mul_left H
    calc
      blockScale m (i + 1) ≤ 2 * blockScale m (i + 1) := by omega
      _ = blockScale m ((i + 1) + 1) := (blockScale_succ m (i + 1)).symm

lemma disjoint_svUsed_svBlock {A : Set ℕ} (hAinf : A.Infinite)
    (H m i : ℕ) :
    Disjoint (svUsed A H m i) (svBlock A H m (i + 1)) := by
  rw [Finset.disjoint_left]
  intro a haU haB
  rw [svUsed, Finset.mem_image] at haU
  rw [svBlock, Finset.mem_image] at haB
  obtain ⟨j, hj, hja⟩ := haU
  obtain ⟨k, hk, hka⟩ := haB
  have hjk : j = k := (nth_strictMono hAinf).injective (hja.trans hka.symm)
  subst k
  simp only [Finset.mem_Ico] at hj hk
  exact (not_lt_of_ge hk.1) hj.2

lemma subsetSums_coe_finset (F : Finset ℕ) :
    subsetSums (↑F : Set ℕ) = (F.subsetSum : Set ℕ) := by
  ext u
  rw [Finset.mem_coe, Finset.mem_subsetSum_iff]
  constructor
  · rintro ⟨G, hGF, rfl⟩
    exact ⟨G, hGF, rfl⟩
  · rintro ⟨G, hGF, rfl⟩
    exact ⟨G, hGF, rfl⟩

lemma subsetSum_le_card_mul {F : Finset ℕ} {N u : ℕ}
    (hFN : F ⊆ Finset.Icc 1 N) (hu : u ∈ F.subsetSum) :
    u ≤ F.card * N := by
  rw [Finset.mem_subsetSum_iff] at hu
  obtain ⟨G, hGF, rfl⟩ := hu
  calc
    ∑ g ∈ G, g ≤ ∑ _g ∈ G, N := by
      apply Finset.sum_le_sum
      intro g hg
      exact (Finset.mem_Icc.mp (hFN (hGF hg))).2
    _ = G.card * N := by simp
    _ ≤ F.card * N := Nat.mul_le_mul_right N (Finset.card_le_card hGF)

lemma AP_step_le_two_card {F : Finset ℕ} {N a d : ℕ}
    (hN : 2 ≤ N) (hFN : F ⊆ Finset.Icc 1 N)
    (hAP : ∀ j < N, a + j * d ∈ (F.subsetSum : Set ℕ)) :
    d ≤ 2 * F.card := by
  have hlast := subsetSum_le_card_mul hFN (hAP (N - 1) (by omega))
  have hprod : (N - 1) * d ≤ (N - 1) * (2 * F.card) := by
    calc
      (N - 1) * d ≤ a + (N - 1) * d := Nat.le_add_left _ _
      _ ≤ F.card * N := hlast
      _ ≤ F.card * (2 * (N - 1)) :=
        Nat.mul_le_mul_left F.card (by omega)
      _ = (2 * F.card) * (N - 1) := by ring
      _ = (N - 1) * (2 * F.card) := by ring
  exact Nat.le_of_mul_le_mul_left hprod (by omega)

lemma svBlock_subset_Icc_of_inversion {A : Set ℕ} {H m : ℕ}
    (hAinf : A.Infinite) (hApos : A ⊆ Set.Ici 1)
    (hH : 0 < H) (hm : 0 < m)
    (hinv : ∀ j, H * m ≤ j →
      (8 * (H : ℝ)) ^ 2 * (Nat.nth (· ∈ A) j : ℝ) ≤
        (((j + 1 : ℕ) : ℝ)) ^ 2) :
    ∀ i, svBlock A H m i ⊆ Finset.Icc 1 (blockScale m i ^ 2) := by
  intro i a ha
  rw [svBlock, Finset.mem_image] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  rw [Finset.mem_Icc]
  refine ⟨hApos (nth_mem hAinf j), ?_⟩
  have hscale : m ≤ blockScale m i :=
    Nat.le_mul_of_pos_left m (pow_pos (by omega) _)
  have hjlower : H * m ≤ j := by
    exact (Nat.mul_le_mul_left H hscale).trans (Finset.mem_Ico.mp hj).1
  have hjupper : j + 1 ≤ 2 * H * blockScale m i := by
    have hjlt := (Finset.mem_Ico.mp hj).2
    rw [blockScale_succ] at hjlt
    nlinarith
  have hinvJ := hinv j hjlower
  have hjupperR : (((j + 1 : ℕ) : ℝ)) ≤
      2 * (H : ℝ) * (blockScale m i : ℝ) := by
    exact_mod_cast hjupper
  have hsq : (((j + 1 : ℕ) : ℝ)) ^ 2 ≤
      (2 * (H : ℝ) * (blockScale m i : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hjupperR
  have hboundR : (Nat.nth (· ∈ A) j : ℝ) ≤
      ((blockScale m i ^ 2 : ℕ) : ℝ) := by
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    push_cast
    by_contra hnot
    have hlt : (blockScale m i : ℝ) ^ 2 <
        (Nat.nth (· ∈ A) j : ℝ) := lt_of_not_ge hnot
    have hprod : 0 < (H : ℝ) ^ 2 *
        ((Nat.nth (· ∈ A) j : ℝ) - (blockScale m i : ℝ) ^ 2) :=
      mul_pos (sq_pos_of_pos hHr) (sub_pos.mpr hlt)
    nlinarith
  exact_mod_cast hboundR

lemma exists_svBlock_AP
    {A : Set ℕ} {c : ℝ} {H m : ℕ}
    (hfinite : ∀ n : ℕ, 0 < n → ∀ F : Finset ℕ,
      F ⊆ Finset.Icc 1 n →
      c * Real.sqrt (n : ℝ) ≤ (F.card : ℝ) →
      ContainsFiniteAP (F.subsetSum : Set ℕ) n)
    (hcH : c ≤ H) (hAinf : A.Infinite) (hm : 2 ≤ m)
    (hblocks : ∀ i, svBlock A H m i ⊆
      Finset.Icc 1 (blockScale m i ^ 2)) :
    ∀ i, ∃ a d : ℕ, 0 < d ∧ d ≤ 2 * H * blockScale m i ∧
      ∀ j < blockScale m i ^ 2,
        a + j * d ∈ subsetSums (↑(svBlock A H m i) : Set ℕ) := by
  intro i
  let e := blockScale m i
  have he : 2 ≤ e := hm.trans (Nat.le_mul_of_pos_left m (pow_pos (by omega) _))
  have hcard : (svBlock A H m i).card = H * e := card_svBlock hAinf H m i
  have hsqrt : Real.sqrt ((e ^ 2 : ℕ) : ℝ) = e := by
    push_cast
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hdense : c * Real.sqrt ((e ^ 2 : ℕ) : ℝ) ≤
      ((svBlock A H m i).card : ℝ) := by
    rw [hsqrt, hcard]
    exact_mod_cast mul_le_mul_of_nonneg_right hcH (Nat.cast_nonneg e)
  obtain ⟨a, d, hd, hAP⟩ := hfinite (e ^ 2) (by positivity)
    (svBlock A H m i) (hblocks i) hdense
  have hdBound : d ≤ 2 * H * e := by
    have := AP_step_le_two_card (F := svBlock A H m i) (N := e ^ 2)
      (a := a) (d := d) (by nlinarith) (hblocks i) hAP
    rw [hcard] at this
    nlinarith
  refine ⟨a, d, hd, hdBound, ?_⟩
  simpa [subsetSums_coe_finset] using hAP

lemma exists_merged_block_AP
    {A : Set ℕ} {H m : ℕ} (hAinf : A.Infinite)
    (hH : 0 < H) (hmLarge : 8 * H ≤ m)
    (hblockAP : ∀ i, ∃ a d : ℕ, 0 < d ∧
      d ≤ 2 * H * blockScale m i ∧
      ∀ j < blockScale m i ^ 2,
        a + j * d ∈ subsetSums (↑(svBlock A H m i) : Set ℕ)) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 2 * H * m ∧
      ∀ i, ∃ a d : ℕ, 0 < d ∧ d ∣ D ∧
        ∀ j < blockScale m i ^ 2 / 2,
          a + j * d ∈ subsetSums (↑(svUsed A H m i) : Set ℕ) := by
  obtain ⟨a₀, D, hD, hDbound, hAP₀⟩ := hblockAP 0
  refine ⟨D, hD, ?_, ?_⟩
  · simpa [blockScale] using hDbound
  · intro i
    induction i with
    | zero =>
        refine ⟨a₀, D, hD, dvd_rfl, ?_⟩
        rw [svUsed_zero]
        exact fun j hj ↦ hAP₀ j (hj.trans_le (Nat.div_le_self _ _))
    | succ i ih =>
        obtain ⟨aOld, dOld, hdOld, hdOldD, hOld⟩ := ih
        obtain ⟨aNew, dNew, hdNew, hdNewBound, hNew⟩ := hblockAP (i + 1)
        let q := Nat.gcd dNew dOld
        let M := dNew / q
        let r := dOld / q
        have hq : 0 < q := Nat.gcd_pos_of_pos_left dOld hdNew
        have hqdNew : q ∣ dNew := Nat.gcd_dvd_left _ _
        have hqdOld : q ∣ dOld := Nat.gcd_dvd_right _ _
        have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hdNew hqdNew) hq
        have hr : 0 < r := Nat.div_pos (Nat.le_of_dvd hdOld hqdOld) hq
        have hdNewEq : q * M = dNew := Nat.mul_div_cancel' hqdNew
        have hdOldEq : q * r = dOld := Nat.mul_div_cancel' hqdOld
        have hcop : M.Coprime r := Nat.coprime_div_gcd_div_gcd hq
        let e := blockScale m i
        let e' := blockScale m (i + 1)
        have heEq : e' = 2 * e := blockScale_succ m i
        have hme : m ≤ e :=
          Nat.le_mul_of_pos_left m (pow_pos (by omega) _)
        have heLarge : 8 * H ≤ e := hmLarge.trans hme
        have hMleNew : M ≤ dNew := Nat.div_le_self _ _
        have hNewOldLen : 2 * H * e' ≤ e ^ 2 / 2 := by
          apply (Nat.le_div_iff_mul_le (by omega)).2
          rw [heEq]
          nlinarith
        have hMU : M ≤ e ^ 2 / 2 :=
          hMleNew.trans (hdNewBound.trans hNewOldLen)
        have hdOldLeD : dOld ≤ D := Nat.le_of_dvd hD hdOldD
        have hDhalf : D ≤ e' ^ 2 / 2 := by
          have hDb : D ≤ 2 * H * m := by simpa [blockScale] using hDbound
          apply (Nat.le_div_iff_mul_le (by omega)).2
          nlinarith [hme]
        have hrHalf : r ≤ e' ^ 2 / 2 :=
          (Nat.div_le_self _ _).trans (hdOldLeD.trans hDhalf)
        have hsub : e' ^ 2 / 2 ≤ e' ^ 2 - r := by omega
        have htarget : e' ^ 2 / 2 ≤ M * (e' ^ 2 - r) := by
          exact hsub.trans (Nat.le_mul_of_pos_left _ hM)
        have hmerge : ∀ n < M * (e' ^ 2 - r),
            (aNew + aOld + (q * M) * r) + n * q ∈
              subsetSums (↑(svBlock A H m (i + 1)) : Set ℕ) +
                subsetSums (↑(svUsed A H m i) : Set ℕ) := by
          apply merge_AP_by_gcd hq hM hr hcop hMU
          · simpa [e', hdNewEq] using hNew
          · simpa [e, hdOldEq] using hOld
        have hdisj : Disjoint (svBlock A H m (i + 1)) (svUsed A H m i) :=
          (disjoint_svUsed_svBlock hAinf H m i).symm
        refine ⟨aNew + aOld + (q * M) * r, q, hq,
          hqdOld.trans hdOldD, ?_⟩
        intro n hn
        have hx := hmerge n (hn.trans_le htarget)
        have hx' := subsetSums_union_subset_add
          (A := (↑(svBlock A H m (i + 1)) : Set ℕ))
          (B := (↑(svUsed A H m i) : Set ℕ))
          (by exact_mod_cast hdisj) hx
        rw [Set.union_comm, ← Finset.coe_union, ← svUsed_succ] at hx'
        exact hx'

lemma fixedStep_of_merged_blocks
    {A : Set ℕ} {H m D : ℕ} (hAinf : A.Infinite) (hm : 2 ≤ m)
    (hD : 0 < D)
    (hmerged : ∀ i, ∃ a d : ℕ, 0 < d ∧ d ∣ D ∧
      ∀ j < blockScale m i ^ 2 / 2,
        a + j * d ∈ subsetSums (↑(svUsed A H m i) : Set ℕ)) :
    HasFixedStepProgressions (subsetSums A) := by
  let aa : ℕ → ℕ := fun i ↦ (hmerged i).choose
  let dd : ℕ → ℕ := fun i ↦ (hmerged i).choose_spec.choose
  have hspec (i : ℕ) : 0 < dd i ∧ dd i ∣ D ∧
      ∀ j < blockScale m i ^ 2 / 2,
        aa i + j * dd i ∈ subsetSums (↑(svUsed A H m i) : Set ℕ) :=
    (hmerged i).choose_spec.choose_spec
  have hddle (i : ℕ) : dd i ≤ D := Nat.le_of_dvd hD (hspec i).2.1
  let f : ℕ → Fin (D + 1) := fun i ↦ ⟨dd i, Nat.lt_succ_of_le (hddle i)⟩
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber f
  have hvset : (f ⁻¹' {v}).Infinite := Set.infinite_coe_iff.mp hv
  have hvpos : 0 < v.val := by
    obtain ⟨i, hi, -⟩ := hvset.exists_gt 0
    have hfi : f i = v := by simpa using hi
    have hval := congrArg (fun x : Fin (D + 1) ↦ x.val) hfi
    change dd i = v.val at hval
    simpa [← hval] using (hspec i).1
  refine ⟨v.val, hvpos, ?_⟩
  intro k
  obtain ⟨i, hiFiber, hki⟩ := hvset.exists_gt k
  have hfi : f i = v := by simpa using hiFiber
  have hval := congrArg (fun x : Fin (D + 1) ↦ x.val) hfi
  change dd i = v.val at hval
  refine ⟨aa i, ?_⟩
  intro j hj
  apply subsetSums_mono (svUsed_subset hAinf H m i)
  rw [← hval]
  exact (hspec i).2.2 j (hj.trans_le <|
    (Nat.le_of_lt hki).trans (index_le_half_blockScale_sq hm))

theorem fixedStepProgressions_of_finiteSV
    {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    {c : ℝ} (hc : 0 < c)
    (hfinite : ∀ n : ℕ, 0 < n → ∀ F : Finset ℕ,
      F ⊆ Finset.Icc 1 n →
      c * Real.sqrt (n : ℝ) ≤ (F.card : ℝ) →
      ContainsFiniteAP (F.subsetSum : Set ℕ) n)
    (hdense : SqrtDense (8 * (Nat.ceil c : ℝ)) A) :
    HasFixedStepProgressions (subsetSums A) := by
  let H := Nat.ceil c
  have hH : 0 < H := Nat.ceil_pos.mpr hc
  have hcH : c ≤ (H : ℝ) := Nat.le_ceil c
  have hC : (0 : ℝ) < 8 * H := by positivity
  have hAinf := infinite_of_sqrtDense hC hdense
  have hinvEventually := eventually_density_inversion hApos hC hdense
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hinvEventually
  let m := max (8 * H) (max 2 j₀)
  have hm2 : 2 ≤ m := le_max_of_le_right (le_max_left _ _)
  have hmLarge : 8 * H ≤ m := le_max_left _ _
  have hj₀Hm : j₀ ≤ H * m := by
    have hjm : j₀ ≤ m := le_max_of_le_right (le_max_right _ _)
    exact hjm.trans (Nat.le_mul_of_pos_left m hH)
  have hinv : ∀ j, H * m ≤ j →
      (8 * (H : ℝ)) ^ 2 * (Nat.nth (· ∈ A) j : ℝ) ≤
        (((j + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j hj
    exact hj₀ j (hj₀Hm.trans hj)
  have hblocks := svBlock_subset_Icc_of_inversion hAinf hApos hH
    (by omega : 0 < m) hinv
  have hblockAP := exists_svBlock_AP hfinite hcH hAinf hm2 hblocks
  obtain ⟨D, hD, -, hmerged⟩ :=
    exists_merged_block_AP hAinf hH hmLarge hblockAP
  exact fixedStep_of_merged_blocks hAinf hm2 hD hmerged

theorem finiteSzemerediVu_nat
    {n : ℕ} (hn : 0 < n) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n)
    (hroot : svDensityConstant * Nat.sqrt n ≤ A.card)
    (hdensity : svDensityConstant ^ 2 * n ≤ A.card ^ 2) :
    ContainsFiniteAP (A.subsetSum : Set ℕ) n := by
  classical
  let m := A.card
  have hm : 0 < m := by
    by_contra hm0
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
    have hsqrt : 0 < Nat.sqrt n := by simpa [Nat.sqrt_pos] using hn
    have hconst : 0 < svDensityConstant * Nat.sqrt n :=
      Nat.mul_pos svDensityConstant_pos hsqrt
    omega
  have hmn : m ≤ n := by
    dsimp only [m]
    exact (Finset.card_le_card hA).trans (by simp)
  have hnlarge : svDensityConstant ^ 2 ≤ n :=
    ambient_large_of_square_bound hn hmn hdensity
  have hn64 : 2 ^ 64 ≤ n :=
    two_pow_sixtyFour_le_svDensityConstant_sq.trans hnlarge
  have hsqrt1 : 1 ≤ Nat.sqrt n := by
    have hsqrt : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
    omega
  have hm32 : 32 ≤ m := by
    have h32 : 32 ≤ svDensityConstant := by
      norm_num [svDensityConstant, finiteDensityConstant, partitionAmplifier,
        coreAmplifier, finiteDepth]
    have : svDensityConstant ≤ svDensityConstant * Nat.sqrt n := by
      simpa using Nat.mul_le_mul_left svDensityConstant hsqrt1
    exact h32.trans (this.trans hroot)
  obtain ⟨P⟩ := exists_preparedPools hn hm32 rfl hA hroot hn64
  have hNn : P.N ≤ n := by
    rw [P.N_eq]
    exact Nat.div_le_self _ _
  have hn2 : 2 ≤ n := by omega
  have hthreshold := trackingThreshold_sixteen_le hn64 hroot
  change 16 * trackingThreshold n ≤ m at hthreshold
  have hwholeL : trackingThreshold n ≤ P.lower.card := by
    have hs : 4 * (4 * trackingThreshold n) ≤ 4 * P.lower.card := by
      have hs0 := hthreshold.trans P.lower_large
      rw [show 4 * (4 * trackingThreshold n) =
        16 * trackingThreshold n by omega]
      exact hs0
    have h4 : 4 * trackingThreshold n ≤ P.lower.card :=
      Nat.le_of_mul_le_mul_left hs (by norm_num : 0 < 4)
    exact (show trackingThreshold n ≤ 4 * trackingThreshold n by
      have := Nat.mul_le_mul_left (trackingThreshold n) (by omega : 1 ≤ 4)
      simpa [mul_comm] using this).trans h4
  have hwholeH : trackingThreshold n ≤ P.upper.card := by
    have hs : 4 * (4 * trackingThreshold n) ≤ 4 * P.upper.card := by
      have hs0 := hthreshold.trans P.upper_large
      rw [show 4 * (4 * trackingThreshold n) =
        16 * trackingThreshold n by omega]
      exact hs0
    have h4 : 4 * trackingThreshold n ≤ P.upper.card :=
      Nat.le_of_mul_le_mul_left hs (by norm_num : 0 < 4)
    exact (show trackingThreshold n ≤ 4 * trackingThreshold n by
      have := Nat.mul_le_mul_left (trackingThreshold n) (by omega : 1 ≤ 4)
      simpa [mul_comm] using this).trans h4
  have hdivL : ∀ e ∈ P.lowerTags,
      trackingThreshold n ≤ (P.lower.filter fun z ↦ ¬e ∣ z).card := by
    intro e he
    exact (Nat.le_add_right _ (partitionAmplifier * e)).trans
      (P.lower_tag e he)
  have hdivH : ∀ e ∈ P.upperTags,
      trackingThreshold n ≤ (P.upper.filter fun z ↦ ¬e ∣ z).card := by
    intro e he
    exact (Nat.le_add_right _
      (partitionAmplifier * e +
        2 * partitionAmplifier * (divisorCutoff n m / P.d))).trans
      (by simpa [Nat.add_assoc] using P.upper_tag e he)
  have hQL : (1000 * (Nat.log 2
      (2 * (1 + P.lowerTags.card +
        (largeDyadicIndices P.lower P.N 1).card) + 1) + 1)) *
      200 ^ 48 ≤ trackingThreshold n :=
    balancing_threshold_le_tracking hn2 hNn (by omega)
      P.lowerTags_card
  obtain ⟨TL, hTLcarrier, hTLdisj, hTLleaf⟩ :=
    PartitionTree.exists_dyadic_diverse_partition 48 P.lower P.N
      (trackingThreshold n) P.lowerTags P.lower_box hwholeL hdivL
      P.lower_bins hQL
  have hQH : (1000 * (Nat.log 2
      (2 * (1 + P.upperTags.card +
        (largeDyadicIndices P.upper P.N 1).card) + 1) + 1)) *
      200 ^ 49 ≤ trackingThreshold n :=
    balancing_threshold_le_tracking hn2 hNn (by omega)
      P.upperTags_card
  obtain ⟨TH, hTHcarrier, hTHdisj, hTHleaf⟩ :=
    PartitionTree.exists_dyadic_diverse_partition 49 P.upper P.N
      (trackingThreshold n) P.upperTags P.upper_box hwholeH hdivH
      P.upper_bins hQH
  cases TH with
  | node TU TP =>
    rcases hTHdisj with ⟨hTUdisj, hTPdisj, hTUTP⟩
    rcases hTHleaf with ⟨hTUleaf, hTPleaf⟩
    have hTUupper : TU.carrier ⊆ P.upper := by
      rw [← hTHcarrier]
      exact Finset.subset_union_left
    have hTPupper : TP.carrier ⊆ P.upper := by
      rw [← hTHcarrier]
      exact Finset.subset_union_right
    let LowerLeaf : Finset ℕ → Prop := fun D ↦
      (89 ^ 48 * P.lower.card ≤ 200 ^ 48 * D.card ∧
        200 ^ 48 * D.card ≤ 111 ^ 48 * P.lower.card) ∧
      (∀ e ∈ P.lowerTags,
        89 ^ 48 * (P.lower.filter fun z ↦ ¬e ∣ z).card ≤
            200 ^ 48 * (D ∩ (P.lower.filter fun z ↦ ¬e ∣ z)).card ∧
        200 ^ 48 * (D ∩ (P.lower.filter fun z ↦ ¬e ∣ z)).card ≤
            111 ^ 48 * (P.lower.filter fun z ↦ ¬e ∣ z).card) ∧
      (∀ j ∈ largeDyadicIndices P.lower P.N 1,
        89 ^ 48 * (dyadicBin P.lower j).card ≤
            200 ^ 48 * (D ∩ dyadicBin P.lower j).card ∧
        200 ^ 48 * (D ∩ dyadicBin P.lower j).card ≤
            111 ^ 48 * (dyadicBin P.lower j).card)
    let UpperLeaf : Finset ℕ → Prop := fun U ↦
      (89 ^ 49 * P.upper.card ≤ 200 ^ 49 * U.card ∧
        200 ^ 49 * U.card ≤ 111 ^ 49 * P.upper.card) ∧
      (∀ e ∈ P.upperTags,
        89 ^ 49 * (P.upper.filter fun z ↦ ¬e ∣ z).card ≤
            200 ^ 49 * (U ∩ (P.upper.filter fun z ↦ ¬e ∣ z)).card ∧
        200 ^ 49 * (U ∩ (P.upper.filter fun z ↦ ¬e ∣ z)).card ≤
            111 ^ 49 * (P.upper.filter fun z ↦ ¬e ∣ z).card) ∧
      (∀ j ∈ largeDyadicIndices P.upper P.N 1,
        89 ^ 49 * (dyadicBin P.upper j).card ≤
            200 ^ 49 * (U ∩ dyadicBin P.upper j).card ∧
        200 ^ 49 * (U ∩ dyadicBin P.upper j).card ≤
            111 ^ 49 * (dyadicBin P.upper j).card)
    have hTLleaf' : TL.AllLeaves LowerLeaf := by
      simpa [LowerLeaf] using hTLleaf
    have hTUleaf' : TU.AllLeaves UpperLeaf := by
      simpa [UpperLeaf] using hTUleaf
    have hTPleaf' : TP.AllLeaves UpperLeaf := by
      simpa [UpperLeaf] using hTPleaf
    have hTLfull : TL.AllLeaves fun D ↦ LowerLeaf D ∧ D ⊆ P.lower := by
      refine hTLleaf'.and ((PartitionTree.allLeaves_subset_carrier TL).mono ?_)
      intro D hD
      exact hD.trans (by simpa [hTLcarrier])
    have hTUfull : TU.AllLeaves fun U ↦ UpperLeaf U ∧ U ⊆ P.upper := by
      refine hTUleaf'.and ((PartitionTree.allLeaves_subset_carrier TU).mono ?_)
      intro U hU
      exact hU.trans hTUupper
    have hTPfull : TP.AllLeaves fun Q ↦ UpperLeaf Q ∧ Q ⊆ P.upper := by
      refine hTPleaf'.and ((PartitionTree.allLeaves_subset_carrier TP).mono ?_)
      intro Q hQ
      exact hQ.trans hTPupper
    let Base := PartitionTree.zipUnion TL TU
    have hDUpairs : PartitionTree.AllLeafPairs (fun D U ↦
        (LowerLeaf D ∧ D ⊆ P.lower) ∧
          (UpperLeaf U ∧ U ⊆ P.upper)) TL TU :=
      PartitionTree.allLeafPairs_of_allLeaves hTLfull hTUfull
        (fun _ _ hD hU ↦ ⟨hD, hU⟩)
    have hBaseLeaves : Base.AllLeaves (fun C ↦
        ∃ D U, C = D ∪ U ∧
          (LowerLeaf D ∧ D ⊆ P.lower) ∧
          (UpperLeaf U ∧ U ⊆ P.upper)) := by
      apply PartitionTree.allLeaves_zipUnion hDUpairs
      intro D U hDU
      exact ⟨D, U, rfl, hDU⟩
    have hraw : PartitionTree.AllLeafPairs (fun C Q ↦
        (∃ D U, C = D ∪ U ∧
          (LowerLeaf D ∧ D ⊆ P.lower) ∧
          (UpperLeaf U ∧ U ⊆ P.upper)) ∧
        (UpperLeaf Q ∧ Q ⊆ P.upper)) Base TP :=
      PartitionTree.allLeafPairs_of_allLeaves hBaseLeaves hTPfull
        (fun _ _ hC hQ ↦ ⟨hC, hQ⟩)
    have hLowerCardM : P.lower.card ≤ m := by
      change P.lower.card ≤ A.card
      apply Finset.card_le_card_of_injOn (fun z ↦ P.d * z)
      · intro z hz
        exact P.scale_mem z (Finset.mem_union_left _ hz)
      · intro x _ y _ hxy
        exact Nat.eq_of_mul_eq_mul_left P.d_pos hxy
    have hUpperNe : P.upper.Nonempty := by
      apply Finset.card_pos.mp
      omega
    have hLowerSum : (∑ z ∈ P.lower, z) ≤
        4 * ∑ z ∈ P.upper, z := by
      apply sum_le_four_sum_of_order hUpperNe
      · exact hLowerCardM.trans P.upper_large
      · exact P.ordered
    let M := ∑ z ∈ P.upper, z
    have hmass0 := card_mul_card_le_sum_of_lt P.ordered
    have hmass : m ^ 2 ≤ 16 * M := by
      have hcards := Nat.mul_le_mul P.lower_large P.upper_large
      calc
        m ^ 2 = m * m := by ring
        _ ≤ (4 * P.lower.card) * (4 * P.upper.card) := hcards
        _ = 16 * (P.lower.card * P.upper.card) := by ring
        _ ≤ 16 * M := Nat.mul_le_mul_left 16 hmass0
    have hparams := leaf_parameters_of_mass hn hdensity hmass
    let K := leafCardTarget M
    let phase := modularPhaseLength n m
    let box := leafBoxBound M
    have hleaf : PartitionTree.AllLeafPairs (fun C Q ↦
        (∀ q ∈ Q, 0 < q) ∧
        (∀ q ∈ Q, q ≤ 4 * ((boundedSubsetSum C phase).image
          (fun u : ℕ ↦ (u : ZMod q))).card) ∧
        8 * Q.card ≤ ∑ q ∈ Q, q ∧
        8 * K ≤ ∑ q ∈ Q, q ∧
        pivotExtended (boundedSubsetSum C phase) Q ⊆
          Finset.Icc 0 box) Base TP := by
      refine hraw.mono ?_
      intro C Q hCQ
      obtain ⟨⟨D, U, rfl, hD, hU⟩, hQ⟩ := hCQ
      have hDspec := hD.1
      have hDsub := hD.2
      have hUspec := hU.1
      have hUsub := hU.2
      have hQspec := hQ.1
      have hQsub := hQ.2
      dsimp only [LowerLeaf] at hDspec
      dsimp only [UpperLeaf] at hUspec hQspec
      have hcore : m ≤ coreAmplifier * D.card := by
        calc
          m ≤ 4 * P.lower.card := P.lower_large
          _ ≤ 4 * (200 ^ 48 * D.card) := by
            apply Nat.mul_le_mul_left
            calc
              P.lower.card ≤ 89 ^ 48 * P.lower.card :=
                Nat.le_mul_of_pos_left _ (by positivity)
              _ ≤ 200 ^ 48 * D.card := hDspec.1.1
          _ = coreAmplifier * D.card := by rw [coreAmplifier_eq]; ring
      have hphaseBounds := modularPhaseLength_leaf_bounds
        hn hm hmn hNn hn64 hroot hcore
      have hDbox : D ⊆ Finset.Icc 1 P.N := hDsub.trans P.lower_box
      have hUbox : U ⊆ Finset.Icc 1 P.N := hUsub.trans P.upper_box
      have hQbox : Q ⊆ Finset.Icc 1 P.N := hQsub.trans P.upper_box
      have hQpos : ∀ q ∈ Q, 0 < q := by
        intro q hq
        exact (Finset.mem_Icc.mp (hQbox hq)).1
      have hcover : ∀ q ∈ Q, q ≤ 4 *
          ((boundedSubsetSum (D ∪ U) phase).image
            (fun u : ℕ ↦ (u : ZMod q))).card := by
        intro q hq
        have hqpos := hQpos q hq
        have hqN := (Finset.mem_Icc.mp (hQbox hq)).2
        have hDlt : ∀ z ∈ D, z < q := by
          intro z hz
          exact P.ordered z (hDsub hz) q (hQsub hq)
        have hlogq : 4 * (Nat.log 2 q + 1) ^ 2 ≤ phase := by
          have hlogle : Nat.log 2 q + 1 ≤ Nat.log 2 n + 1 := by
            exact Nat.add_le_add_right
              (Nat.log_mono_right (hqN.trans hNn)) 1
          have hsq := Nat.pow_le_pow_left hlogle 2
          dsimp only [phase]
          unfold modularPhaseLength
          exact (Nat.mul_le_mul_left 4 hsq).trans
            (Nat.le_add_left _ _)
        apply pivot_modular_cover_of_split
          (G := coreAmplifier) (n := n) (m := m) (d := P.d)
          (B := divisorCutoff n m) (N := P.N) (p := q) (k := phase)
          hm P.d_pos hqpos hDbox hUbox
          hqN (by rw [P.N_eq]; simpa [mul_comm] using Nat.div_mul_le_self n P.d)
          (by rfl) hcore hDlt
        · intro e he hde heD
          rcases P.tags_cover e he hde with heL | heH
          · left
            exact lower_tag_gives_leaf_witness hDsub
              (P.lower_tag e heL) (hDspec.2.1 e heL).1
          · right
            have hqbound := phase_quotient_bound
              (D := D) (G := coreAmplifier) (n := n) (m := m)
              (d := P.d) (B := divisorCutoff n m) (N := P.N)
              (p := q) (e := e) hm P.d_pos he hqN
              (by rw [P.N_eq]; simpa [mul_comm] using Nat.div_mul_le_self n P.d)
              (by rfl) hcore heD
            exact upper_tag_gives_leaf_witness
              (T := trackingThreshold n) (B := divisorCutoff n m)
              (d := P.d) (e := e) (q := P.N / q + 1)
              hUsub hqbound
              (P.upper_tag e heH) (hUspec.2.1 e heH).1
        · exact hlogq
        · exact hphaseBounds.1
        · exact hphaseBounds.2
      have hLcard8 : 8 ≤ P.lower.card := by omega
      have hlarge : 8 * Q.card ≤ ∑ q ∈ Q, q := by
        calc
          8 * Q.card = ∑ _q ∈ Q, 8 := by simp [mul_comm]
          _ ≤ ∑ q ∈ Q, q := by
            apply Finset.sum_le_sum
            intro q hq
            exact hLcard8.trans (card_le_of_lt_bound
              (fun z hz ↦ P.ordered z hz q (hQsub hq)))
      have hDweight : 200 ^ 48 * (∑ z ∈ D, z) ≤ 8 * 111 ^ 48 * M := by
        have hw := (dyadic_weight_balance_of_large_indices P.lower_box hDsub
          (hDspec.2.2)).2
        calc
          200 ^ 48 * (∑ z ∈ D, z) ≤
              2 * 111 ^ 48 * (∑ z ∈ P.lower, z) := hw
          _ ≤ 2 * 111 ^ 48 * (4 * M) :=
            Nat.mul_le_mul_left _ (by simpa [M] using hLowerSum)
          _ = 8 * 111 ^ 48 * M := by ring
      have hUweight : partitionAmplifier * (∑ z ∈ U, z) ≤
          2 * 111 ^ 49 * M := by
        simpa [partitionAmplifier_eq, M] using
          (dyadic_weight_balance_of_large_indices P.upper_box hUsub
            (hUspec.2.2)).2
      have hQweight : partitionAmplifier * (∑ z ∈ Q, z) ≤
          2 * 111 ^ 49 * M := by
        simpa [partitionAmplifier_eq, M] using
          (dyadic_weight_balance_of_large_indices P.upper_box hQsub
            (hQspec.2.2)).2
      have hQweightLower : 89 ^ 49 * M ≤
          2 * partitionAmplifier * (∑ z ∈ Q, z) := by
        simpa [partitionAmplifier_eq, M] using
          (dyadic_weight_balance_of_large_indices P.upper_box hQsub
            (hQspec.2.2)).1
      have htarget : 8 * K ≤ ∑ z ∈ Q, z := by
        simpa [K] using eight_leafCardTarget_le hQweightLower
      have hDUdisj : Disjoint D U := P.disjoint.mono hDsub hUsub
      have hsumDU : (∑ z ∈ D ∪ U, z) =
          (∑ z ∈ D, z) + ∑ z ∈ U, z := Finset.sum_union hDUdisj
      have hboxEnd : (∑ z ∈ D ∪ U, z) + ∑ z ∈ Q, z ≤ box := by
        rw [hsumDU]
        simpa [box] using leaf_box_bound_of_weights hDweight hUweight hQweight
      have hboxLeaf : pivotExtended (boundedSubsetSum (D ∪ U) phase) Q ⊆
          Finset.Icc 0 box := by
        intro x hx
        have hx' := Finset.mem_Icc.mp
          (pivotExtended_boundedSubsetSum_subset_Icc (D ∪ U) Q phase hx)
        exact Finset.mem_Icc.mpr ⟨hx'.1, hx'.2.trans hboxEnd⟩
      exact ⟨hQpos, hcover, hlarge, htarget, hboxLeaf⟩
    have hL_TU : Disjoint TL.carrier TU.carrier := by
      apply P.disjoint.mono
      · simpa [hTLcarrier]
      · exact hTUupper
    have hBaseDisj : Base.PairwiseDisjoint :=
      PartitionTree.pairwiseDisjoint_zipUnion hTLdisj hTUdisj hL_TU
    have hBaseTP : Disjoint Base.carrier TP.carrier := by
      rw [show Base.carrier = TL.carrier ∪ TU.carrier by
        exact PartitionTree.carrier_zipUnion TL TU]
      rw [Finset.disjoint_left]
      intro z hz hzp
      rw [Finset.mem_union] at hz
      rcases hz with hzL | hzU
      · exact Finset.disjoint_left.mp P.disjoint
          (by rw [← hTLcarrier]; exact hzL) (hTPupper hzp)
      · exact Finset.disjoint_left.mp hTUTP hzU hzp
    have hgrowth : 2 ^ 48 * box + 1 < SumTree.growthLower K 48 := by
      simpa [box, K, M, leafBoxBound, leafCardTarget] using
        depth_fortyEight_growth hparams.1
    have hAP := containsFiniteAP_of_paired_pivots Base TP
      (by
        dsimp only [K]
        have hr : 2 ≤ (M / partitionAmplifier) / 16 := by omega
        have hone : 1 ≤ 89 ^ 49 := by norm_num
        calc
          2 ≤ (M / partitionAmplifier) / 16 := hr
          _ = 1 * ((M / partitionAmplifier) / 16) := by simp
          _ ≤ 89 ^ 49 * ((M / partitionAmplifier) / 16) :=
            Nat.mul_le_mul_right _ hone)
      hBaseDisj hTPdisj hBaseTP hleaf hgrowth
    have hscaled : ∀ z ∈ Base.carrier ∪ TP.carrier, P.d * z ∈ A := by
      intro z hz
      apply P.scale_mem z
      rw [show Base.carrier = TL.carrier ∪ TU.carrier by
        exact PartitionTree.carrier_zipUnion TL TU] at hz
      rw [Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases Finset.mem_union.mp hz with hzL | hzU
        · exact Or.inl (by rw [← hTLcarrier]; exact hzL)
        · exact Or.inr (hTUupper hzU)
      · exact Or.inr (hTPupper hz)
    exact containsFiniteAP_scaled_subsetSum P.d_pos hscaled
      (containsFiniteAP_of_le hparams.2 hAP)

/-- Exact finite input proved by Szemerédi and Vu.  This is a proposition,
not an assumption in the final theorem. -/
def FiniteSzemerediVu : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ A : Finset ℕ,
    A ⊆ Finset.Icc 1 n →
    c * Real.sqrt (n : ℝ) ≤ (A.card : ℝ) →
    ContainsFiniteAP (A.subsetSum : Set ℕ) n

/-- The finite Szemerédi--Vu theorem, with the explicit bookkeeping constant
used by the formal construction above. -/
theorem finiteSzemerediVu : FiniteSzemerediVu := by
  refine ⟨(svDensityConstant : ℝ), ?_, ?_⟩
  · exact_mod_cast svDensityConstant_pos
  · intro n hn A hA hdense
    have hsquare : svDensityConstant ^ 2 * n ≤ A.card ^ 2 :=
      nat_square_bound_of_real_sqrt hdense
    have hroot : svDensityConstant * Nat.sqrt n ≤ A.card :=
      scaled_nat_sqrt_le_of_square_bound hsquare
    exact finiteSzemerediVu_nat hn A hA hroot hsquare

/-! ### Assembly of the infinite theorem from the finite theorem -/

lemma counting_inter_Ici_one (A : Set ℕ) (N : ℕ) :
    counting (A ∩ Set.Ici 1) N = counting A N := by
  unfold counting
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
    Set.mem_Ici]
  aesop

lemma sqrtDense_positive_part {A : Set ℕ} {C : ℝ}
    (hA : SqrtDense C A) : SqrtDense C (A ∩ Set.Ici 1) := by
  filter_upwards [hA] with N hN
  rwa [counting_inter_Ici_one]

/-- The completely formal Section 6 deduction.  Its sole remaining input is
the finite theorem `FiniteSzemerediVu`. -/
theorem erdos344_of_finiteSzemerediVu (hSV : FiniteSzemerediVu) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ,
      SqrtDense C A → ContainsInfiniteAP (subsetSums A) := by
  obtain ⟨c, hc, hfinite⟩ := hSV
  let H := Nat.ceil c
  have hH : 0 < H := Nat.ceil_pos.mpr hc
  refine ⟨20 * (H : ℝ), by positivity, ?_⟩
  intro A hAdense
  let Apos : Set ℕ := A ∩ Set.Ici 1
  have hApos : Apos ⊆ Set.Ici 1 := fun _ hx ↦ hx.2
  have hAposA : Apos ⊆ A := fun _ hx ↦ hx.1
  have hAposDense : SqrtDense (20 * (H : ℝ)) Apos := by
    exact sqrtDense_positive_part hAdense
  let B := rankPart Apos 0
  let R := rankPart Apos 1
  have hBdense : SqrtDense (8 * (H : ℝ)) B := by
    apply sqrtDense_rankPart hApos (by positivity)
      (C := 20 * (H : ℝ)) (r := 0) (hr := by omega)
      (hdense := hAposDense)
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    nlinarith
  have hRdense : SqrtDense 4 R := by
    apply sqrtDense_rankPart hApos (by norm_num)
      (C := 20 * (H : ℝ)) (r := 1) (hr := by omega)
      (hdense := hAposDense)
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  have hBpos : B ⊆ Set.Ici 1 :=
    (rankPart_subset Apos 0).trans hApos
  have hRpos : R ⊆ Set.Ici 1 :=
    (rankPart_subset Apos 1).trans hApos
  have hfixed : HasFixedStepProgressions (subsetSums B) := by
    have hceil : Nat.ceil c = H := rfl
    simpa [hceil] using
      (fixedStepProgressions_of_finiteSV hBpos hc hfinite hBdense)
  have hsubcompletePos : ContainsInfiniteAP (subsetSums Apos) := by
    apply fixedStep_and_dense_residue_part hRpos hRdense
      (rankPart_disjoint Apos) (rankPart_zero_union_one (A := Apos)) hfixed
  exact containsInfiniteAP_mono (subsetSums_mono hAposA) hsubcompletePos

/-- Erdős Problem 344: every set whose counting function is bounded below by
a positive constant times the square root is subcomplete. -/
theorem erdos_344 :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ,
      SqrtDense C A → ContainsInfiniteAP (subsetSums A) :=
  erdos344_of_finiteSzemerediVu finiteSzemerediVu

#print axioms finiteSzemerediVu
#print axioms erdos_344

end Erdos344
