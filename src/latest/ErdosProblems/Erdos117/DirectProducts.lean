import ErdosProblems.Erdos117.Compression
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Nilpotent

/-!
# Covers and cliques in direct products

Abelian covers multiply, and products of actual noncommuting families are
noncommuting families. These statements use the true factor clique sizes,
not a common upper bound for all factors.
-/

namespace Erdos117

open scoped BigOperators

theorem hasAbelianCover_one {G : Type*} [Group G] [IsMulCommutative G] :
    HasAbelianCover G 1 := by
  refine ⟨fun _ => ⊤, fun _ => inferInstance, fun x => ⟨0, ?_⟩⟩
  trivial

theorem class_two_subgroup {G : Type*} [Group G]
    (hG : commutator G ≤ Subgroup.center G) (H : Subgroup G) :
    commutator H ≤ Subgroup.center H := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp
    (hG (Subgroup.commutator_mem_commutator (Subgroup.mem_top (x : G))
      (Subgroup.mem_top (y : G)))) (z : G)

theorem isNilpotent_of_class_two {G : Type*} [Group G]
    (hG : commutator G ≤ Subgroup.center G) : Group.IsNilpotent G := by
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨2, ?_⟩
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one,
    Subgroup.commutator_top_right_eq_bot_iff_le_center]
  exact hG

theorem commutator_subgroup_card_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (commutator H) ≤ Nat.card (commutator G) := by
  have hmap : (commutator H).map H.subtype ≤ commutator G := by
    rw [H.map_subtype_commutator]
    exact Subgroup.commutator_mono le_top le_top
  let f : commutator H → commutator G := fun x =>
    ⟨(x.val : G), hmap ⟨x.val, x.2, rfl⟩⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  have hval : (x.val : G) = (y.val : G) := congrArg (fun z : commutator G => z.val) h
  exact Subtype.ext (Subtype.ext hval)

/-- A finite clique bound is attained by an indexed family. -/
theorem exists_exact_clique_bound {G : Type*} [Group G] {n : ℕ}
    (hn : NoncommutingBound G n) :
    ∃ k ≤ n, NoncommutingBound G k ∧
      ∃ a : Fin k → G, ∀ i j, i ≠ j → ¬Commute (a i) (a j) := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximum_noncommuting_set hn
  let e : s ≃ Fin s.card := s.equivFin
  refine ⟨s.card, hn s hs, hmax, fun i => (e.symm i).val, ?_⟩
  intro i j hij hc
  exact hs (e.symm i).2 (e.symm j).2
    (fun h => hij (e.symm.injective (Subtype.ext h))) hc

/-- The product of abelian covers is an abelian cover of the direct product. -/
theorem hasAbelianCover_pi {ι : Type*} [Fintype ι]
    {G : ι → Type*} [∀ i, Group (G i)] {k : ι → ℕ}
    (hk : ∀ i, HasAbelianCover (G i) (k i)) :
    HasAbelianCover (∀ i, G i) (∏ i, k i) := by
  classical
  choose c hc using fun i => (hasAbelianCover_iff_coloring (k i)).mp (hk i)
  let e : (∀ i, Fin (k i)) ≃ Fin (∏ i, k i) := Fintype.equivFinOfCardEq (by simp)
  apply (hasAbelianCover_iff_coloring _).mpr
  refine ⟨fun x => e (fun i => c i (x i)), ?_⟩
  intro x y hxy
  have h := e.injective hxy
  exact funext (fun i => (hc i (x i) (y i) (congrFun h i)).eq)

/-- Distinct tuples differ in a coordinate whose entries do not commute. -/
theorem pi_noncommuting_family {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    {k : ι → ℕ} (a : ∀ i, Fin (k i) → G i)
    (ha : ∀ i u v, u ≠ v → ¬Commute (a i u) (a i v)) :
    ∀ u v : (∀ i, Fin (k i)), u ≠ v →
      ¬Commute (fun i => a i (u i)) (fun i => a i (v i)) := by
  intro u v huv hc
  apply huv
  funext i
  by_contra hne
  exact ha i (u i) (v i) hne (congrFun hc.eq i)

/-- A clique bound on the direct product bounds the product of the factor
clique cardinalities. No graph-product equality is assumed. -/
theorem product_clique_card_le {ι : Type*} [Fintype ι]
    {G : ι → Type*} [∀ i, Group (G i)] {n : ℕ}
    (hn : NoncommutingBound (∀ i, G i) n) {k : ι → ℕ}
    (a : ∀ i, Fin (k i) → G i)
    (ha : ∀ i u v, u ≠ v → ¬Commute (a i u) (a i v)) :
    (∏ i, k i) ≤ n := by
  classical
  simpa using hn.card_le (pi_noncommuting_family a ha)

/-- A nonabelian group has a three-element noncommuting family, namely
`x`, `y`, and `x*y` for any noncommuting pair. -/
theorem three_le_of_nonabelian {G : Type*} [Group G] {n : ℕ}
    (hn : NoncommutingBound G n) (hG : ¬IsMulCommutative G) : 3 ≤ n := by
  classical
  obtain ⟨x, y, hxy⟩ : ∃ x y : G, ¬Commute x y := by
    by_contra h
    apply hG
    apply IsMulCommutative.of_comm
    intro x y
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  have hxxy : ¬Commute x (x * y) := by
    intro h
    apply hxy
    simpa only [inv_mul_cancel_left] using (Commute.refl x).inv_right.mul_right h
  have hyxy : ¬Commute y (x * y) := by
    intro h
    apply hxy
    have h' : Commute y x := by
      simpa only [mul_inv_cancel_right] using h.mul_right (Commute.refl y).inv_right
    exact h'.symm
  let a : Fin 3 → G := ![x, y, x * y]
  have ha : ∀ i j, i ≠ j → ¬Commute (a i) (a j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hxy
    · exact hxxy
    · exact fun h => hxy h.symm
    · exact (hij rfl).elim
    · exact hyxy
    · exact fun h => hxxy h.symm
    · exact fun h => hyxy h.symm
    · exact (hij rfl).elim
  simpa using hn.card_le ha

/-- The exact factor clique bounds have product at most the ambient bound. -/
theorem exists_factor_clique_bounds {ι : Type*} [Fintype ι]
    {G : ι → Type*} [∀ i, Group (G i)] {n : ℕ}
    (hn : NoncommutingBound (∀ i, G i) n) :
    ∃ k : ι → ℕ, (∀ i, NoncommutingBound (G i) (k i)) ∧
      (∀ i, 1 ≤ k i) ∧ (∀ i, ¬IsMulCommutative (G i) → 3 ≤ k i) ∧ (∏ i, k i) ≤ n := by
  classical
  have hfactor (i : ι) : NoncommutingBound (G i) n :=
    noncommutingBound_of_surjective (fun x : ∀ i, G i => x i)
      (fun x => ⟨Function.update 1 i x, by simp⟩)
      (fun _ _ h => congrFun h.eq i) hn
  choose k hkn hk a ha using fun i => exists_exact_clique_bound (hfactor i)
  exact ⟨k, hk, fun i => one_le_of_noncommutingBound (hk i),
    fun i => three_le_of_nonabelian (hk i), product_clique_card_le hn a ha⟩

/-- Evaluation at the unique Sylow subgroup removes the redundant inner
product from Mathlib's nilpotent-group decomposition. -/
noncomputable def nilpotentSylowEquiv {G : Type*} [Group G] [Finite G]
    [Group.IsNilpotent G] :
    (∀ p : (Nat.card G).primeFactors, (default : Sylow p.val G)) ≃* G := by
  let e := Sylow.directProductOfNormal (G := G) (fun {p} hp P => inferInstance)
  let e' : (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p.val G, P) ≃*
      (∀ p : (Nat.card G).primeFactors, (default : Sylow p.val G)) :=
    MulEquiv.piCongrRight (fun p => by
      letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      letI := Sylow.unique_of_normal (default : Sylow p.val G) inferInstance
      exact MulEquiv.piUnique (fun P : Sylow p.val G => P))
  exact e'.symm.trans e

end Erdos117
