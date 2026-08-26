import ErdosProblems.Erdos117.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Elementary compression of conjugacy classes

The first input to the upper-bound argument is a polynomial bound for every
conjugacy class. We work with the equivalent index of its centralizer.
-/

namespace Erdos117

open Finset

variable {G : Type*} [Group G]

/-- A finite bound on clique sizes is attained, even when the group is infinite. -/
theorem exists_maximum_noncommuting_set {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ s : Finset G, (s : Set G).Pairwise (fun x y => ¬ Commute x y) ∧
      ∀ t : Finset G, (t : Set G).Pairwise (fun x y => ¬ Commute x y) → t.card ≤ s.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ s : Finset G,
    (s : Set G).Pairwise (fun x y => ¬ Commute x y) ∧ s.card = k
  have hzero : P 0 := ⟨∅, by simp, rfl⟩
  obtain ⟨s, hs, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le n) hzero
  refine ⟨s, hs, fun t ht => ?_⟩
  rw [hcard]
  exact Nat.le_findGreatest (hn t ht) ⟨t, ht, rfl⟩

private theorem commute_of_mul_left {a x y : G} (ha : Commute a y)
    (h : Commute (a * x) y) : Commute x y := by
  simpa only [inv_mul_cancel_left] using ha.inv_left.mul_left h

/-- The common centralizer of a maximum noncommuting set is the center.
The proof enlarges a clique by multiplying selected vertices by an element
of its centralizer. No finiteness assumption on the group is needed. -/
theorem centralizer_eq_center_of_maximum {s : Finset G}
    (hs : (s : Set G).Pairwise (fun x y => ¬ Commute x y))
    (hmax : ∀ t : Finset G, (t : Set G).Pairwise (fun x y => ¬ Commute x y) →
      t.card ≤ s.card) :
    Subgroup.centralizer (s : Set G) = Subgroup.center G := by
  classical
  apply le_antisymm _ (Subgroup.center_le_centralizer _)
  intro a ha
  apply Subgroup.mem_center_iff.mpr
  intro b
  by_contra hab
  have hab' : ¬ Commute a b := fun h => hab h.symm.eq
  have has : ∀ x ∈ s, Commute a x := fun x hx => (ha x hx).symm
  let f : G → G := fun x => if Commute x b then a * x else x
  have haf : ∀ x ∈ s, Commute a (f x) := by
    intro x hx
    dsimp [f]
    split_ifs
    · exact (Commute.refl a).mul_right (has x hx)
    · exact has x hx
  have hcancel : ∀ x ∈ s, ∀ y ∈ s, Commute (f x) (f y) → Commute x y := by
    intro x hx y hy h
    have hxy : Commute x (f y) := by
      by_cases hxb : Commute x b
      · have hfx : f x = a * x := if_pos hxb
        rw [hfx] at h
        exact commute_of_mul_left (haf y hy) h
      · have hfx : f x = x := if_neg hxb
        rwa [hfx] at h
    by_cases hyb : Commute y b
    · have h' : Commute (a * y) x := by simpa only [f, if_pos hyb] using hxy.symm
      exact (commute_of_mul_left (has x hx) h').symm
    · simpa only [f, if_neg hyb] using hxy
  have hinj : Set.InjOn f s := by
    intro x hx y hy hxy
    by_contra hne
    exact hs hx hy hne (hcancel x hx y hy (hxy ▸ Commute.refl (f x)))
  have hfb : ∀ x ∈ s, ¬ Commute (f x) b := by
    intro x hx h
    by_cases hxb : Commute x b
    · have h' : Commute (a * x) b := by simpa only [f, if_pos hxb] using h
      exact hab' (by simpa only [mul_inv_cancel_right] using h'.mul_left hxb.inv_left)
    · exact hxb (by simpa only [f, if_neg hxb] using h)
  have hp : ((s.image f : Finset G) : Set G).Pairwise (fun x y => ¬ Commute x y) := by
    intro x hx y hy hne hcomm
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    exact hs hu hv (fun h => hne (congrArg f h)) (hcancel u hu v hv hcomm)
  have hb : b ∉ s.image f := by
    rintro hb
    obtain ⟨x, hx, hxb⟩ := mem_image.mp hb
    exact hfb x hx (hxb ▸ Commute.refl b)
  have hp' : ((insert b (s.image f) : Finset G) : Set G).Pairwise
      (fun x y => ¬ Commute x y) := by
    rw [coe_insert, Set.pairwise_insert_of_notMem hb]
    refine ⟨hp, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact ⟨fun h => hfb y hy h.symm, hfb y hy⟩
  have hm := hmax _ hp'
  rw [card_insert_of_notMem hb, card_image_of_injOn hinj] at hm
  omega

/-- A maximal noncommuting set dominates the commuting relation on a finite set. -/
theorem exists_commuting_dominating_set (X : Finset G) :
    ∃ s : Finset G, s ⊆ X ∧
      (s : Set G).Pairwise (fun x y => ¬ Commute x y) ∧
      ∀ x ∈ X, ∃ y ∈ s, Commute x y := by
  classical
  let C := X.powerset.filter
    (fun s : Finset G => (s : Set G).Pairwise (fun x y => ¬ Commute x y))
  have hC : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨s, hs, hmax⟩ := C.exists_max_image Finset.card hC
  obtain ⟨hsX, hsp⟩ := mem_filter.mp hs
  have hsX' := mem_powerset.mp hsX
  refine ⟨s, hsX', hsp, ?_⟩
  intro x hx
  by_contra hn
  have hnc : ∀ y ∈ s, ¬ Commute x y := by simpa using hn
  have hxs : x ∉ s := fun h => hnc x h (Commute.refl x)
  have hp : ((insert x s : Finset G) : Set G).Pairwise (fun a b => ¬ Commute a b) := by
    rw [coe_insert, Set.pairwise_insert_of_notMem hxs]
    exact ⟨hsp, fun y hy => ⟨hnc y hy, fun h => hnc y hy h.symm⟩⟩
  have hi : insert x s ∈ C := by
    exact mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx hsX'), hp⟩
  have hm := hmax (insert x s) hi
  rw [card_insert_of_notMem hxs] at hm
  omega

/-- The index of the centralizer of one element. -/
noncomputable def centralizerIndex (x : G) : ℕ := (Subgroup.centralizer {x}).index

theorem centralizerIndex_mul_le [Finite G] (x y : G) :
    centralizerIndex (x * y) ≤ centralizerIndex x * centralizerIndex y := by
  have hle : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ≤
      Subgroup.centralizer {x * y} := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at *
    have hx : Commute z x := (Subgroup.mem_centralizer_singleton_iff.mp hz.1)
    have hy : Commute z y := (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
    exact (hx.mul_right hy).eq
  exact (Subgroup.index_antitone hle).trans Subgroup.index_inf_le

theorem centralizerIndex_inv (x : G) : centralizerIndex x⁻¹ = centralizerIndex x := by
  unfold centralizerIndex
  congr 1
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  change Commute z x⁻¹ ↔ Commute z x
  exact ⟨fun h => by simpa using h.inv_right, fun h => h.inv_right⟩

section Finite

variable [Fintype G]

private noncomputable def centralizerFinset (x : G) : Finset G :=
  @Finset.filter _ (fun y => Commute y x) (Classical.decPred _) Finset.univ

private theorem centralizerIndex_mul_card (x : G) :
    centralizerIndex x * (centralizerFinset x).card = Fintype.card G := by
  classical
  let : Fintype (Subgroup.centralizer ({x} : Set G)) := Fintype.ofFinite _
  have hc : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      (centralizerFinset x).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp only [centralizerFinset, mem_filter, mem_univ, true_and]
    exact Subgroup.mem_centralizer_singleton_iff
  rw [centralizerIndex, ← hc, Subgroup.index_mul_card, Nat.card_eq_fintype_card]

private theorem card_le_sum_centralizers (X : Finset G) (s : Finset G)
    (h : ∀ x ∈ X, ∃ y ∈ s, Commute x y) :
    X.card ≤ ∑ y ∈ s, (centralizerFinset y).card := by
  classical
  have hs : X ⊆ s.biUnion centralizerFinset := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h x hx
    exact mem_biUnion.mpr ⟨y, hy, by simp [centralizerFinset, hxy]⟩
  exact (card_le_card hs).trans (card_biUnion_le)

private theorem majority_small_centralizerIndex {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ Y : Finset G, Fintype.card G < 2 * Y.card ∧
      ∀ y ∈ Y, centralizerIndex y ≤ 2 * n := by
  classical
  let X := univ.filter (fun x : G => 2 * n < centralizerIndex x)
  let Y := univ.filter (fun x : G => centralizerIndex x ≤ 2 * n)
  obtain ⟨s, hsX, hsp, hdom⟩ := exists_commuting_dominating_set X
  have hs : s.card ≤ n := hn s hsp
  have hc := card_le_sum_centralizers X s hdom
  have hb : (2 * n + 1) * X.card ≤ n * Fintype.card G := by
    calc
      (2 * n + 1) * X.card ≤ (2 * n + 1) * ∑ y ∈ s, (centralizerFinset y).card :=
        Nat.mul_le_mul_left _ hc
      _ = ∑ y ∈ s, (2 * n + 1) * (centralizerFinset y).card := mul_sum _ _ _
      _ ≤ ∑ _y ∈ s, Fintype.card G := by
        apply sum_le_sum
        intro y hy
        have hyX : 2 * n < centralizerIndex y := (mem_filter.mp (hsX hy)).2
        exact (Nat.mul_le_mul_right _ hyX).trans_eq (centralizerIndex_mul_card y)
      _ = s.card * Fintype.card G := by simp
      _ ≤ n * Fintype.card G := Nat.mul_le_mul_right _ hs
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have hx : 2 * X.card < Fintype.card G := by nlinarith
  have hsum : X.card + Y.card = Fintype.card G := by
    simpa only [X, Y, not_lt, card_univ] using
      card_filter_add_card_filter_not (s := univ) (fun x : G => 2 * n < centralizerIndex x)
  refine ⟨Y, by omega, fun y hy => (mem_filter.mp hy).2⟩

private theorem exists_div_of_majority (Y : Finset G)
    (hY : Fintype.card G < 2 * Y.card) (g : G) :
    ∃ u ∈ Y, ∃ v ∈ Y, g = u * v⁻¹ := by
  classical
  let T := Y.image (fun v => g * v)
  have hT : T.card = Y.card := card_image_of_injective _ (mul_right_injective g)
  have hsum := card_union_add_card_inter Y T
  have hu : (Y ∪ T).card ≤ Fintype.card G := card_le_univ _
  have hi : 0 < (Y ∩ T).card := by omega
  obtain ⟨u, hu⟩ := card_pos.mp hi
  obtain ⟨huY, huT⟩ := mem_inter.mp hu
  obtain ⟨v, hv, huv⟩ := mem_image.mp huT
  refine ⟨u, huY, v, hv, ?_⟩
  rw [← huv, mul_assoc, mul_inv_cancel, mul_one]

end Finite

/-- Polynomial BFC bound: every conjugacy class has size at most `4*n^2`.
This proves the first compression input, rather than assuming it from Pyber. -/
theorem centralizerIndex_le [Finite G] {n : ℕ} (hn : NoncommutingBound G n) (g : G) :
    centralizerIndex g ≤ (2 * n) ^ 2 := by
  let := Fintype.ofFinite G
  obtain ⟨Y, hY, hsmall⟩ := majority_small_centralizerIndex hn
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_div_of_majority Y hY g
  calc
    centralizerIndex (u * v⁻¹) ≤ centralizerIndex u * centralizerIndex v⁻¹ :=
      centralizerIndex_mul_le u v⁻¹
    _ = centralizerIndex u * centralizerIndex v := by rw [centralizerIndex_inv]
    _ ≤ (2 * n) * (2 * n) := Nat.mul_le_mul (hsmall u hu) (hsmall v hv)
    _ = (2 * n) ^ 2 := (pow_two _).symm

/-- A bound for the center index from a bound for every conjugacy class. -/
theorem centerIndex_le_of_centralizerIndex_le {n B : ℕ}
    (hn : NoncommutingBound G n) (hB : 0 < B)
    (hb : ∀ x : G, centralizerIndex x ≤ B) :
    (Subgroup.center G).index ≤ B ^ n := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximum_noncommuting_set hn
  have heq : (⨅ x : s, Subgroup.centralizer ({(x : G)} : Set G)) = Subgroup.center G := by
    rw [← centralizer_eq_center_of_maximum hs hmax]
    ext g
    simp only [Subgroup.mem_iInf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, Subtype.forall, mem_coe]
  calc
    (Subgroup.center G).index =
        (⨅ x : s, Subgroup.centralizer ({(x : G)} : Set G)).index := congrArg _ heq.symm
    _ ≤ ∏ x : s, centralizerIndex (x : G) := Subgroup.index_iInf_le _
    _ ≤ ∏ _x : s, B := prod_le_prod' (fun x _ => hb x)
    _ = B ^ s.card := by simp
    _ ≤ B ^ n := Nat.pow_le_pow_right hB (hn s hs)

/-- Elementary quantitative center bound. Its logarithm is `O(n log(n+2))`,
which suffices for the coset-extension step without invoking Pyber's theorem. -/
theorem centerIndex_le [Finite G] {n : ℕ} (hn : NoncommutingBound G n) :
    (Subgroup.center G).index ≤ ((2 * n) ^ 2) ^ n := by
  have hnpos := one_le_of_noncommutingBound hn
  exact centerIndex_le_of_centralizerIndex_le hn (by positivity) (centralizerIndex_le hn)

end Erdos117
