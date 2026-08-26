import ErdosProblems.Erdos118.BoundedNeighborhoods
import ErdosProblems.Erdos118.Imported591.ExactOuterLevels

/-!
The local triangle-free product bound and the final root-block assembly.
These proofs do not assume a positive endpoint partition theorem. The final
assembly requires an explicitly supplied full-type set with red global pairs;
constructing such a set from triangle-freeness is still missing.
-/

open Set Ordinal

namespace Erdos118.RootAssembly

open Schipperus.K4Core BoundedNeighborhoods
open Negative Negative.Exact

/-- A neighborhood already supplies the target, or the proved small-neighborhood
fusion supplies it in the product. -/
theorem independent_of_triangleFree_product {Y X : Type}
    [LinearOrder Y] [WellFoundedLT Y] [Nonempty Y] [Countable Y]
    [LinearOrder X] [WellFoundedLT X]
    (hind : FinitelyIndivisible Y)
    (hinit : ∀ a : Y, ¬ Large Y (Set.Iic a))
    (habsorb : (ω : Ordinal) * typeLT Y = typeLT Y)
    (hprod : (typeLT Y) * typeLT Y = typeLT X)
    (B : SimpleGraph X) (hB : B.CliqueFree 3) :
    ∃ S : Set X, B.IsIndepSet S ∧ typeLT S = typeLT Y := by
  classical
  by_contra hno
  have hsmall (x : X) : ¬ Large Y {z | B.Adj x z} := by
    rintro ⟨f⟩
    let e : Y ↪o X := f.trans (OrderEmbedding.subtype {z | B.Adj x z})
    apply hno
    refine ⟨Set.range e, ?_, ?_⟩
    · intro a ha b hb hab
      obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      exact B.isIndepSet_neighborSet_of_triangleFree hB x (f u).2 (f v).2 hab
    · exact (OrderIso.ordinalType_congr e.orderIso).symm
  obtain ⟨S, htype, hfree⟩ := exists_independent_of_small_neighborhoods
    hind hinit B hsmall (blocks_of_type_mul hprod)
  exact hno ⟨S, hfree, htype.trans habsorb⟩

theorem reservoir_eq_theta_pow (r : ℕ) : reservoir r = (ω ^ ω : Ordinal) ^ r := by
  rw [reservoir, Ordinal.opow_mul, Ordinal.opow_natCast]

theorem reservoir_mul_self (r : ℕ) : reservoir r * reservoir r = reservoir (2 * r) := by
  rw [reservoir_eq_theta_pow, reservoir_eq_theta_pow, two_mul, pow_add]

theorem omega_mul_reservoir (r : ℕ) (hr : 0 < r) :
    (ω : Ordinal) * reservoir r = reservoir r := by
  have he : (1 : Ordinal) + ω * (r : Ordinal) = ω * (r : Ordinal) := by
    have hr' : (1 : Ordinal) ≤ (r : Ordinal) := by exact_mod_cast hr
    have hω : (ω : Ordinal) ≤ ω * (r : Ordinal) := by
      simpa only [mul_one] using (mul_le_mul_right hr' (ω : Ordinal))
    exact Ordinal.one_add_of_omega0_le hω
  rw [reservoir, ← Ordinal.opow_one_add, he]

/-- The local relation needed in each root fiber is derived, not postulated. -/
theorem local_three (r : ℕ) (hr : 0 < r) :
    Partition (reservoir (2 * r)) (reservoir r) 3 := by
  apply (partition_iff _ _ _).mpr
  intro B hB
  let Y := (reservoir r).ToType
  let : Nonempty Y := Ordinal.nonempty_toType_iff.mpr
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
  let : Countable Y := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Cardinal.mk_toType, reservoir, Ordinal.card_omega0_opow]
    · apply max_le le_rfl
      rw [Ordinal.card_mul, Ordinal.card_omega0, Ordinal.card_nat,
        Cardinal.aleph0_mul_nat (Nat.ne_of_gt hr)]
    · exact mul_ne_zero Ordinal.omega0_ne_zero (by exact_mod_cast Nat.ne_of_gt hr))
  have hind : FinitelyIndivisible Y :=
    Schipperus.PieceIndiv.omegaPower_finitelyIndivisible_of_le
      Erdos590.erdos_590 (ω * (r : Ordinal)) r (Ordinal.type_toType _) le_rfl
  have hlim : Order.IsSuccLimit (typeLT Y) := by
    rw [Ordinal.type_toType]
    exact Ordinal.isSuccLimit_opow Ordinal.one_lt_omega0
      (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast hr))
  have habsorb : (ω : Ordinal) * typeLT Y = typeLT Y := by
    simpa only [Y, Ordinal.type_toType] using omega_mul_reservoir r hr
  have hprod : (typeLT Y) * typeLT Y = typeLT (reservoir (2 * r)).ToType := by
    simpa only [Y, Ordinal.type_toType] using reservoir_mul_self r
  obtain ⟨S, hfree, htype⟩ := independent_of_triangleFree_product hind
    (Schipperus.PieceIndiv.not_large_Iic_of_isSuccLimit hlim) habsorb hprod B hB
  exact ⟨S, hfree, by simpa only [Y, Ordinal.type_toType] using htype⟩

/-- Transport the proved local relation into an arbitrary ordered subset. -/
theorem local_independent_subset (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (V : Set G) (r : ℕ) (hr : 0 < r)
    (hsize : reservoir (2 * r) ≤ typeLT V) :
    ∃ S ⊆ V, B.IsIndepSet S ∧ typeLT S = reservoir r := by
  have htype : typeLT (reservoir (2 * r)).ToType ≤ typeLT V := by
    simpa only [Ordinal.type_toType] using hsize
  obtain ⟨f⟩ := Ordinal.type_le_iff'.mp htype
  let intoV : (reservoir (2 * r)).ToType ↪o V :=
    OrderEmbedding.ofStrictMono f (fun _ _ h ↦ f.map_rel_iff.mpr h)
  let e := intoV.trans (OrderEmbedding.subtype V)
  obtain ⟨g, hg⟩ := (partition_iff_orderEmbedding _ _ _).mp (local_three r hr)
    (B.comap e) (cliqueFree_comap B hB e.toEmbedding)
  let finalMap : (reservoir r).ToType ↪o G := g.trans e
  refine ⟨Set.range finalMap, ?_, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact (intoV (g a)).2
  · intro x hx y hy hxy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact hg a b (fun h ↦ hxy (congrArg finalMap h))
  · rw [type_range, Ordinal.type_toType]

/-- The local targets are cofinal in the exact endpoint ordinal. -/
theorem lambda_le_of_reservoir_bounds (a : Ordinal.{0})
    (h : ∀ r : ℕ, reservoir (r + 1) ≤ a) : lambda ≤ a := by
  rw [lambda_eq_natural_inner_power, ← thetaOmega_eq]
  apply (Ordinal.opow_le_of_isSuccLimit
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero) Ordinal.isSuccLimit_omega0).mpr
  intro b hb
  obtain ⟨r, rfl⟩ := Ordinal.lt_omega0.mp hb
  rw [Ordinal.opow_natCast]
  have hr := Negative.OuterLevels.theta_pow_strictMono (Nat.lt_succ_self r)
  change (ω ^ ω : Ordinal) ^ r < (ω ^ ω : Ordinal) ^ (r + 1) at hr
  rw [← reservoir_eq_theta_pow (r + 1)] at hr
  exact hr.le.trans (h r)

/-- Choose strictly increasing root fibers with enough local order type. -/
theorem increasing_large_roots (W : Set G) (hW : typeLT W = lambda) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      ∀ r, reservoir (2 * (r + 1)) ≤ typeLT (OuterLevels.Fiber W (m r)) := by
  classical
  have hlarge (r M : ℕ) : ∃ m, M < m ∧
      reservoir (2 * (r + 1)) ≤ typeLT (OuterLevels.Fiber W m) := by
    rw [reservoir_eq_theta_pow]
    exact OuterLevels.exists_large_fiber_above_pow W
      (hW.trans lambda_eq_natural_inner_power) M (2 * (r + 1))
  choose next hnext using hlarge
  let m : ℕ → ℕ := fun r ↦ Nat.rec (next 0 0) (fun i prev ↦ next (i + 1) prev) r
  have hm0 : m 0 = next 0 0 := rfl
  have hmsucc (r : ℕ) : m (r + 1) = next (r + 1) (m r) := rfl
  refine ⟨m, strictMono_nat_of_lt_succ (fun r ↦ ?_), ?_⟩
  · rw [hmsucc]
    exact (hnext (r + 1) (m r)).1
  · intro r
    cases r with
    | zero => rw [hm0]; exact (hnext 0 0).2
    | succ r => rw [hmsucc]; exact (hnext (r + 1) (m r)).2

/-- This closes the local-to-global assembly once a full-type family with
red pairs between distinct roots has been constructed. That family is not
assumed to follow from triangle-freeness in this declaration. -/
theorem independent_of_red_global_pairs (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (W : Set G) (hW : typeLT W = lambda)
    (hglobal : ∀ s ∈ W, ∀ t ∈ W, s.1.length ≠ t.1.length → ¬ B.Adj s t) :
    ∃ S ⊆ W, B.IsIndepSet S ∧ typeLT S = lambda := by
  classical
  obtain ⟨m, hm, hsize⟩ := increasing_large_roots W hW
  have hlocal (r : ℕ) : ∃ S ⊆ OuterLevels.Fiber W (m r),
      B.IsIndepSet S ∧ typeLT S = reservoir (r + 1) :=
    local_independent_subset B hB _ (r + 1) (Nat.zero_lt_succ r) (hsize r)
  choose I hIfiber hIind hItype using hlocal
  let S : Set G := ⋃ r : ℕ, I r
  have hIS (r : ℕ) : I r ⊆ S := Set.subset_iUnion I r
  have hSW : S ⊆ W := by
    intro x hx
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    exact (hIfiber r hr).1
  refine ⟨S, hSW, ?_, le_antisymm ?_ ?_⟩
  · intro x hx y hy hxy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
    by_cases hrs : r = s
    · subst s
      exact hIind r hr hs hxy
    · apply hglobal x (hIfiber r hr).1 y (hIfiber s hs).1
      rw [(hIfiber r hr).2, (hIfiber s hs).2]
      exact fun h ↦ hrs (hm.injective h)
  · exact (Ordinal.type_set_le S).trans_eq (type_G.trans lambda_eq_natural_inner_power.symm)
  · apply lambda_le_of_reservoir_bounds
    intro r
    rw [← hItype r]
    exact LexPrefix.typeLT_mono_set (hIS r)

end Erdos118.RootAssembly
