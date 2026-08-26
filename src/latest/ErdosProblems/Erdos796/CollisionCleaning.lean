import ErdosProblems.Erdos796.MultiplicativeSidon
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite collision cleaning

This file formalizes the collision-cleaning argument in the structural
reduction.  If distinct fibres have ordered product convolution at most two,
then a fixed nontrivial unordered product collision can occur in at most one
fibre.  Choosing one participating value from every collision and deleting
the corresponding tagged value therefore makes every fibre multiplicatively
Sidon.  The number of tagged deletions is at most the fourth power of the
ambient cofactor range.
-/

namespace Erdos796

open scoped BigOperators

namespace CollisionCleaning

/-- Four entries encoding two canonically ordered unordered pairs. -/
structure CollisionData where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

/-- The data encode two distinct unordered pairs with the same product. -/
def IsCollision (e : CollisionData) : Prop :=
  e.a ≤ e.b ∧ e.c ≤ e.d ∧ (e.a, e.b) ≠ (e.c, e.d) ∧ e.a * e.b = e.c * e.d

/-- A collision occurs in a finite set when all four displayed entries lie
in that set. -/
def OccursIn (e : CollisionData) (A : Finset ℕ) : Prop :=
  IsCollision e ∧ e.a ∈ A ∧ e.b ∈ A ∧ e.c ∈ A ∧ e.d ∈ A

/-- Ordered convolution compatibility between distinct fibres in `Q`. -/
def CrossCompatibleOn (Q : Finset ℕ) (T : ℕ → Finset ℕ) : Prop :=
  ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → ∀ m : ℕ,
    productRepCount (T i) (T j) m ≤ 2

/-- Three distinct ordered solutions in a rectangular product force the
ordered convolution count to be at least three. -/
theorem three_rectangular_solutions_le_productRepCount
    {A B : Finset ℕ} {m : ℕ} {x₁ x₂ x₃ : ℕ × ℕ}
    (h₁ : x₁.1 ∈ A ∧ x₁.2 ∈ B ∧ x₁.1 * x₁.2 = m)
    (h₂ : x₂.1 ∈ A ∧ x₂.2 ∈ B ∧ x₂.1 * x₂.2 = m)
    (h₃ : x₃.1 ∈ A ∧ x₃.2 ∈ B ∧ x₃.1 * x₃.2 = m)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) :
    3 ≤ productRepCount A B m := by
  let S : Finset (ℕ × ℕ) := {x₁, x₂, x₃}
  have hcard : S.card = 3 := by
    simp [S, h₁₂, h₁₃, h₂₃]
  have hsub : S ⊆ (A ×ˢ B).filter (fun uv => uv.1 * uv.2 = m) := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₁.1, h₁.2.1⟩, h₁.2.2⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₂.1, h₂.2.1⟩, h₂.2.2⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h₃.1, h₃.2.1⟩, h₃.2.2⟩
  rw [productRepCount, ← hcard]
  exact Finset.card_le_card hsub

/-- If one canonical collision occurs in two fibres, the rectangular
convolution between those fibres has at least three solutions. -/
theorem three_le_cross_count_of_collision
    {e : CollisionData} {A B : Finset ℕ}
    (heA : OccursIn e A) (heB : OccursIn e B) :
    3 ≤ productRepCount A B (e.a * e.b) := by
  rcases heA with ⟨he, haA, hbA, hcA, hdA⟩
  rcases heB with ⟨_, haB, hbB, hcB, hdB⟩
  rcases he with ⟨hab, hcd, hpairs, hprod⟩
  by_cases hne : e.a ≠ e.b
  · apply three_rectangular_solutions_le_productRepCount
      (x₁ := (e.a, e.b)) (x₂ := (e.b, e.a)) (x₃ := (e.c, e.d))
    · exact ⟨haA, hbB, rfl⟩
    · exact ⟨hbA, haB, Nat.mul_comm _ _⟩
    · exact ⟨hcA, hdB, hprod.symm⟩
    · intro h
      exact hne (congrArg Prod.fst h)
    · exact hpairs
    · intro h
      have hbc : e.b = e.c := congrArg Prod.fst h
      have had : e.a = e.d := congrArg Prod.snd h
      have hba : e.b ≤ e.a := by simpa [hbc, had] using! hcd
      exact hne (Nat.le_antisymm hab hba)
  · have haa : e.a = e.b := not_ne_iff.mp hne
    have hcdne : e.c ≠ e.d := by
      intro hcc
      have hsq : e.a * e.a = e.c * e.c := by simpa [haa, hcc] using! hprod
      have hac : e.a = e.c := by
        exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hsq
      apply hpairs
      exact Prod.ext hac (haa.symm.trans (hac.trans hcc))
    apply three_rectangular_solutions_le_productRepCount
      (x₁ := (e.a, e.a)) (x₂ := (e.c, e.d)) (x₃ := (e.d, e.c))
    · exact ⟨haA, haB, by simp [haa]⟩
    · exact ⟨hcA, hdB, hprod.symm.trans (by simp [haa])⟩
    · exact ⟨hdA, hcB, by simpa [Nat.mul_comm, haa] using! hprod.symm⟩
    · intro h
      have hac : e.a = e.c := congrArg Prod.fst h
      have had : e.a = e.d := congrArg Prod.snd h
      exact hcdne (hac.symm.trans had)
    · intro h
      have had : e.a = e.d := congrArg Prod.fst h
      have hac : e.a = e.c := congrArg Prod.snd h
      exact hcdne (hac.symm.trans had)
    · intro h
      exact hcdne (congrArg Prod.fst h)

/-- Under cross-compatibility, a fixed collision occurs in at most one
indexed fibre. -/
theorem collision_occurs_in_at_most_one_fiber
    {Q : Finset ℕ} {T : ℕ → Finset ℕ}
    (hcross : CrossCompatibleOn Q T) {e : CollisionData}
    {i j : ℕ} (hi : i ∈ Q) (hj : j ∈ Q)
    (hei : OccursIn e (T i)) (hej : OccursIn e (T j)) :
    i = j := by
  by_contra hij
  have hlower := three_le_cross_count_of_collision hei hej
  have hupper := hcross i hi j hj hij (e.a * e.b)
  omega

/-- Uniqueness of unordered products conversely bounds the ordered
convolution by two. -/
theorem conv_le_two_of_unorderedProductUnique {A : Finset ℕ}
    (hunique : UnorderedProductUnique A) (m : ℕ) :
    productRepCount A A m ≤ 2 := by
  rw [productRepCount]
  let S := (A ×ˢ A).filter fun uv => uv.1 * uv.2 = m
  by_cases hS : S = ∅
  · simp [S, hS]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hpdata : p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 * p.2 = m := by
      have hp' := Finset.mem_filter.mp hp
      have hpA := Finset.mem_product.mp hp'.1
      exact ⟨hpA.1, hpA.2, hp'.2⟩
    have hsub : S ⊆ {p, (p.2, p.1)} := by
      intro q hq
      have hqdata : q.1 ∈ A ∧ q.2 ∈ A ∧ q.1 * q.2 = m := by
        have hq' := Finset.mem_filter.mp hq
        have hqA := Finset.mem_product.mp hq'.1
        exact ⟨hqA.1, hqA.2, hq'.2⟩
      have hprod : q.1 * q.2 = p.1 * p.2 := hqdata.2.2.trans hpdata.2.2.symm
      rcases hunique hqdata.1 hqdata.2.1 hpdata.1 hpdata.2.1 hprod with h | h
      · have : q = p := Prod.ext h.1 h.2
        simp [this]
      · have : q = (p.2, p.1) := Prod.ext h.1 h.2
        simp [this]
    change S.card ≤ 2
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- A set with no canonical collision has unique unordered products. -/
theorem unorderedProductUnique_of_no_collision {A : Finset ℕ}
    (hno : ∀ e : CollisionData, ¬ OccursIn e A) :
    UnorderedProductUnique A := by
  intro a b c d ha hb hc hd hprod
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · by_cases hp : (a, b) = (c, d)
      · exact Or.inl ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
      · exact False.elim (hno ⟨a, b, c, d⟩ ⟨⟨hab, hcd, hp, hprod⟩,
          ha, hb, hc, hd⟩)
    · have hdc : d ≤ c := Nat.le_of_lt (lt_of_not_ge hcd)
      by_cases hp : (a, b) = (d, c)
      · exact Or.inr ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
      · exact False.elim (hno ⟨a, b, d, c⟩ ⟨⟨hab, hdc, hp,
          by simpa [Nat.mul_comm] using! hprod⟩, ha, hb, hd, hc⟩)
  · have hba : b ≤ a := Nat.le_of_lt (lt_of_not_ge hab)
    by_cases hcd : c ≤ d
    · by_cases hp : (b, a) = (c, d)
      · exact Or.inr ⟨congrArg Prod.snd hp, congrArg Prod.fst hp⟩
      · exact False.elim (hno ⟨b, a, c, d⟩ ⟨⟨hba, hcd, hp,
          by simpa [Nat.mul_comm] using! hprod⟩, hb, ha, hc, hd⟩)
    · have hdc : d ≤ c := Nat.le_of_lt (lt_of_not_ge hcd)
      by_cases hp : (b, a) = (d, c)
      · exact Or.inl ⟨congrArg Prod.snd hp, congrArg Prod.fst hp⟩
      · exact False.elim (hno ⟨b, a, d, c⟩ ⟨⟨hba, hdc, hp,
          by simpa [Nat.mul_comm] using! hprod⟩, hb, ha, hd, hc⟩)

/-- All quadruples in the positive ambient interval. -/
def collisionUniverse (R : ℕ) : Finset CollisionData :=
  ((positiveIcc R ×ˢ positiveIcc R) ×ˢ
      (positiveIcc R ×ˢ positiveIcc R)).image
    fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩

@[simp]
theorem mem_collisionUniverse {R : ℕ} {e : CollisionData} :
    e ∈ collisionUniverse R ↔
      e.a ∈ positiveIcc R ∧ e.b ∈ positiveIcc R ∧
        e.c ∈ positiveIcc R ∧ e.d ∈ positiveIcc R := by
  constructor
  · intro he
    rw [collisionUniverse] at he
    rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    have hp₁ := Finset.mem_product.mp hp'.1
    have hp₂ := Finset.mem_product.mp hp'.2
    exact ⟨hp₁.1, hp₁.2, hp₂.1, hp₂.2⟩
  · rintro ⟨ha, hb, hc, hd⟩
    rw [collisionUniverse]
    exact Finset.mem_image.mpr
      ⟨((e.a, e.b), (e.c, e.d)),
        Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
            Finset.mem_product.mpr ⟨hc, hd⟩⟩, rfl⟩

theorem card_collisionUniverse (R : ℕ) :
    (collisionUniverse R).card = R ^ 4 := by
  let f : (ℕ × ℕ) × (ℕ × ℕ) → CollisionData :=
    fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases q with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
    simp only [f, CollisionData.mk.injEq] at hpq
    simp only [Prod.mk.injEq]
    exact ⟨⟨hpq.1, hpq.2.1⟩, hpq.2.2.1, hpq.2.2.2⟩
  rw [collisionUniverse, Finset.card_image_of_injective _ hf]
  simp [positiveIcc]
  ring

/-- Collision types which occur in at least one displayed fibre. -/
noncomputable def occurringCollisions
    (R : ℕ) (Q : Finset ℕ) (T : ℕ → Finset ℕ) :
    Finset CollisionData := by
  classical
  exact (collisionUniverse R).filter fun e =>
    ∃ q ∈ Q, OccursIn e (T q)

theorem mem_occurringCollisions {R : ℕ} {Q : Finset ℕ}
    {T : ℕ → Finset ℕ} {e : CollisionData} :
    e ∈ occurringCollisions R Q T ↔
      e ∈ collisionUniverse R ∧ ∃ q ∈ Q, OccursIn e (T q) := by
  classical
  simp [occurringCollisions]

/-- The unique fibre selected for an occurring collision. -/
noncomputable def selectedFiber
    (Q : Finset ℕ) (T : ℕ → Finset ℕ) (e : CollisionData) : ℕ := by
  classical
  exact if h : ∃ q ∈ Q, OccursIn e (T q) then Classical.choose h else 0

theorem selectedFiber_spec {Q : Finset ℕ} {T : ℕ → Finset ℕ}
    {e : CollisionData} (he : ∃ q ∈ Q, OccursIn e (T q)) :
    selectedFiber Q T e ∈ Q ∧ OccursIn e (T (selectedFiber Q T e)) := by
  classical
  rw [selectedFiber, dif_pos he]
  exact Classical.choose_spec he

/-- One tagged value is selected from every occurring collision. -/
noncomputable def deletionPairs
    (R : ℕ) (Q : Finset ℕ) (T : ℕ → Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (occurringCollisions R Q T).image fun e =>
    (selectedFiber Q T e, e.a)

theorem card_deletionPairs_le {R : ℕ} {Q : Finset ℕ}
    {T : ℕ → Finset ℕ} :
    (deletionPairs R Q T).card ≤ R ^ 4 := by
  classical
  calc
    (deletionPairs R Q T).card ≤ (occurringCollisions R Q T).card := by
      exact Finset.card_image_le
    _ ≤ (collisionUniverse R).card := by
      exact Finset.card_filter_le _ _
    _ = R ^ 4 := card_collisionUniverse R

theorem deletionPair_supported {R : ℕ} {Q : Finset ℕ}
    {T : ℕ → Finset ℕ} {qx : ℕ × ℕ}
    (hqx : qx ∈ deletionPairs R Q T) :
    qx.1 ∈ Q ∧ qx.2 ∈ T qx.1 := by
  classical
  rcases Finset.mem_image.mp hqx with ⟨e, he, rfl⟩
  have hex := (mem_occurringCollisions.mp he).2
  have hspec := selectedFiber_spec hex
  exact ⟨hspec.1, hspec.2.2.1⟩

/-- Delete precisely the values whose tagged copies were chosen. -/
noncomputable def cleanedFiber
    (R : ℕ) (Q : Finset ℕ) (T : ℕ → Finset ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact (T q).filter fun x => (q, x) ∉ deletionPairs R Q T

theorem cleanedFiber_subset {R : ℕ} {Q : Finset ℕ}
    {T : ℕ → Finset ℕ} (q : ℕ) :
    cleanedFiber R Q T q ⊆ T q := by
  classical
  exact Finset.filter_subset _ _

/-- Values deleted from one tagged fibre. -/
noncomputable def removedFromFiber
    (R : ℕ) (Q : Finset ℕ) (T : ℕ → Finset ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact (T q).filter fun x => (q, x) ∈ deletionPairs R Q T

theorem card_sub_cleanedFiber_eq_removedFromFiber
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ} (q : ℕ) :
    (T q).card - (cleanedFiber R Q T q).card =
      (removedFromFiber R Q T q).card := by
  classical
  have hpartition := (T q).card_filter_add_card_filter_not
    (fun x => (q, x) ∈ deletionPairs R Q T)
  change (removedFromFiber R Q T q).card +
      (cleanedFiber R Q T q).card = (T q).card at hpartition
  omega

/-- Summing the deleted values over fibres counts the tagged deletion pairs
exactly once. -/
theorem sum_card_removedFromFiber_eq_card_deletionPairs
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ} :
    ∑ q ∈ Q, (removedFromFiber R Q T q).card =
      (deletionPairs R Q T).card := by
  classical
  let D := deletionPairs R Q T
  have hmap : Set.MapsTo Prod.fst (D : Set (ℕ × ℕ)) (Q : Set ℕ) := by
    intro qx hqx
    exact (deletionPair_supported hqx).1
  have hfiber (q : ℕ) (hq : q ∈ Q) :
      (D.filter fun qx => qx.1 = q).card =
        (removedFromFiber R Q T q).card := by
    refine Finset.card_bij (fun qx _ => qx.2) ?_ ?_ ?_
    · intro qx hqx
      have hqx' := Finset.mem_filter.mp hqx
      have hfirst : qx.1 = q := hqx'.2
      have hsupp := deletionPair_supported hqx'.1
      apply Finset.mem_filter.mpr
      constructor
      · simpa [hfirst] using! hsupp.2
      · have hpair : qx = (q, qx.2) := Prod.ext hfirst rfl
        change (q, qx.2) ∈ D
        rw [← hpair]
        exact hqx'.1
    · intro x hx y hy hxy
      apply Prod.ext
      · exact (Finset.mem_filter.mp hx).2.trans
          (Finset.mem_filter.mp hy).2.symm
      · exact hxy
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      refine ⟨(q, x), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      simpa [D] using! hx'.2
  calc
    ∑ q ∈ Q, (removedFromFiber R Q T q).card =
        ∑ q ∈ Q, (D.filter fun qx => qx.1 = q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (hfiber q hq).symm
    _ = D.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise hmap
    _ = (deletionPairs R Q T).card := rfl

/-- At most `R⁴` tagged values are deleted in total. -/
theorem total_cleaning_cost_le_fourth_power
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ} :
    ∑ q ∈ Q, ((T q).card - (cleanedFiber R Q T q).card) ≤ R ^ 4 := by
  calc
    ∑ q ∈ Q, ((T q).card - (cleanedFiber R Q T q).card) =
        ∑ q ∈ Q, (removedFromFiber R Q T q).card := by
      apply Finset.sum_congr rfl
      intro q _
      exact card_sub_cleanedFiber_eq_removedFromFiber q
    _ = (deletionPairs R Q T).card :=
      sum_card_removedFromFiber_eq_card_deletionPairs
    _ ≤ R ^ 4 := card_deletionPairs_le

/-- Product convolution is monotone under shrinking either factor set. -/
theorem productRepCount_mono {A A' B B' : Finset ℕ} {m : ℕ}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    productRepCount A' B' m ≤ productRepCount A B m := by
  rw [productRepCount, productRepCount]
  apply Finset.card_le_card
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpAB := Finset.mem_product.mp hp'.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hA hpAB.1, hB hpAB.2⟩, hp'.2⟩

/-- No canonical collision survives in a cleaned fibre. -/
theorem no_collision_cleanedFiber
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ Q, T q ⊆ positiveIcc R)
    (hcross : CrossCompatibleOn Q T)
    {q : ℕ} (hq : q ∈ Q) (e : CollisionData) :
    ¬OccursIn e (cleanedFiber R Q T q) := by
  classical
  intro heclean
  have heT : OccursIn e (T q) := by
    exact ⟨heclean.1,
      cleanedFiber_subset q heclean.2.1,
      cleanedFiber_subset q heclean.2.2.1,
      cleanedFiber_subset q heclean.2.2.2.1,
      cleanedFiber_subset q heclean.2.2.2.2⟩
  have heUniv : e ∈ collisionUniverse R := by
    rw [mem_collisionUniverse]
    exact ⟨hrange q hq heT.2.1, hrange q hq heT.2.2.1,
      hrange q hq heT.2.2.2.1, hrange q hq heT.2.2.2.2⟩
  have heOcc : e ∈ occurringCollisions R Q T :=
    mem_occurringCollisions.mpr ⟨heUniv, ⟨q, hq, heT⟩⟩
  have hspec := selectedFiber_spec
    (show ∃ i ∈ Q, OccursIn e (T i) from ⟨q, hq, heT⟩)
  have hselected : selectedFiber Q T e = q :=
    collision_occurs_in_at_most_one_fiber hcross hspec.1 hq hspec.2 heT
  have hdeleted : (q, e.a) ∈ deletionPairs R Q T := by
    rw [deletionPairs]
    apply Finset.mem_image.mpr
    exact ⟨e, heOcc, by simp [hselected]⟩
  have heaClean := heclean.2.1
  exact (Finset.mem_filter.mp heaClean).2 hdeleted

/-- Every cleaned fibre has ordered self-convolution at most two. -/
theorem cleanedFiber_self_compatible
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ Q, T q ⊆ positiveIcc R)
    (hcross : CrossCompatibleOn Q T)
    {q : ℕ} (hq : q ∈ Q) (m : ℕ) :
    productRepCount (cleanedFiber R Q T q) (cleanedFiber R Q T q) m ≤ 2 := by
  apply conv_le_two_of_unorderedProductUnique
  apply unorderedProductUnique_of_no_collision
  exact no_collision_cleanedFiber hrange hcross hq

/-- The entire cleaned family is compatible on the displayed index set,
including equal indices. -/
theorem cleanedFiber_compatible_on
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ Q, T q ⊆ positiveIcc R)
    (hcross : CrossCompatibleOn Q T) :
    ∀ i ∈ Q, ∀ j ∈ Q, ∀ m : ℕ,
      productRepCount (cleanedFiber R Q T i)
        (cleanedFiber R Q T j) m ≤ 2 := by
  intro i hi j hj m
  by_cases hij : i = j
  · subst j
    exact cleanedFiber_self_compatible hrange hcross hi m
  · exact (productRepCount_mono (cleanedFiber_subset i) (cleanedFiber_subset j)).trans
      (hcross i hi j hj hij m)

/-- Packaged finite collision-cleaning lemma used by the structural
reduction. -/
theorem exists_compatible_cleaning
    {R : ℕ} {Q : Finset ℕ} {T : ℕ → Finset ℕ}
    (hrange : ∀ q ∈ Q, T q ⊆ positiveIcc R)
    (hcross : CrossCompatibleOn Q T) :
    ∃ S : ℕ → Finset ℕ,
      (∀ q ∈ Q, S q ⊆ T q) ∧
      (∀ i ∈ Q, ∀ j ∈ Q, ∀ m : ℕ,
        productRepCount (S i) (S j) m ≤ 2) ∧
      (∑ q ∈ Q, ((T q).card - (S q).card) ≤ R ^ 4) := by
  refine ⟨cleanedFiber R Q T, ?_, ?_, ?_⟩
  · intro q _
    exact cleanedFiber_subset q
  · exact cleanedFiber_compatible_on hrange hcross
  · exact total_cleaning_cost_le_fourth_power

end CollisionCleaning

end Erdos796
