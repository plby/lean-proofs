import Wikipedia.NoExoticSixSphere.UnorderedSphereDoublePoints

/-!
# Exact counting for cancellation of two simple double values

The fiber condition concerns the original map, not a formal count. Removing
pairs preserves this condition. At two distinct simple double values the
removed set consists of exactly four ordered pairs, so the actual quotient
by sheet interchange loses exactly two elements.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.DegreeCollapse.DoublePointCounting

open NoExoticSixSphere SphereSelfIntersections

variable {M : Type*} {f g : Sphere 3 → M}

def HasOnlyDoubleFibers (f : Sphere 3 → M) : Prop :=
  ∀ x y, x ≠ y → f x = f y → ∀ z, f z = f x → z = x ∨ z = y

theorem onlyDoubleFibers_of_pairs_subset (hf : HasOnlyDoubleFibers f)
    (hsub : pairs g ⊆ pairs f) : HasOnlyDoubleFibers g := by
  intro x y hxy hgy z hgz
  by_cases hzx : z = x
  · exact Or.inl hzx
  have hfy : f x = f y := (hsub (a := (x, y)) ⟨hxy, hgy⟩).2
  have hfz : f z = f x := (hsub (a := (z, x)) ⟨hzx, hgz⟩).2
  exact hf x y hxy hfy z hfz

theorem pairs_at_simple_value {x y : Sphere 3} (hxy : x ≠ y) (hc : f x = f y)
    (hfib : ∀ z, f z = f x → z = x ∨ z = y) :
    pairs f ∩ {p : Sphere 3 × Sphere 3 | f p.1 = f x} = {(x, y), (y, x)} := by
  ext p
  rcases p with ⟨a, b⟩
  constructor
  · rintro ⟨⟨hab, he⟩, ha⟩
    have hb : f b = f x := he.symm.trans ha
    rcases hfib a ha with rfl | rfl <;> rcases hfib b hb with rfl | rfl
    · exact (hab rfl).elim
    · simp
    · simp
    · exact (hab rfl).elim
  · intro hp
    rcases hp with hp | hp
    · cases hp
      exact ⟨⟨hxy, hc⟩, rfl⟩
    · cases hp
      exact ⟨⟨hxy.symm, hc.symm⟩, hc.symm⟩

theorem pairs_at_two_simple_values {x₀ y₀ x₁ y₁ : Sphere 3}
    (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁) (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁) :
    pairs f ∩ {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)} =
      {(x₀, y₀), (y₀, x₀)} ∪ {(x₁, y₁), (y₁, x₁)} := by
  rw [← pairs_at_simple_value h₀ hc₀ hfib₀, ← pairs_at_simple_value h₁ hc₁ hfib₁,
    ← inter_union_distrib_left]
  rfl

theorem ncard_pairs_at_two_simple_values {x₀ y₀ x₁ y₁ : Sphere 3}
    (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁) (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hv : f x₀ ≠ f x₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁) :
    (pairs f ∩ {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)}).ncard = 4 := by
  have hd : Disjoint
      (pairs f ∩ {p : Sphere 3 × Sphere 3 | f p.1 = f x₀})
      (pairs f ∩ {p : Sphere 3 × Sphere 3 | f p.1 = f x₁}) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact hv (hp.2.symm.trans hq.2)
  rw [pairs_at_simple_value h₀ hc₀ hfib₀, pairs_at_simple_value h₁ hc₁ hfib₁] at hd
  have hp₀ : (x₀, y₀) ≠ (y₀, x₀) := fun h ↦ h₀ (congrArg Prod.fst h)
  have hp₁ : (x₁, y₁) ≠ (y₁, x₁) := fun h ↦ h₁ (congrArg Prod.fst h)
  rw [pairs_at_two_simple_values h₀ h₁ hc₀ hc₁ hfib₀ hfib₁, ncard_union_eq hd]
  simp [hp₀, hp₁]

theorem unordered_card_after_two_value_removal (hfin : (pairs f).Finite)
    {x₀ y₀ x₁ y₁ : Sphere 3}
    (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁) (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hv : f x₀ ≠ f x₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁)
    (hpairs : pairs g = pairs f \
      {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)}) :
    Nat.card (Unordered g) + 2 = Nat.card (Unordered f) := by
  have hgfin : (pairs g).Finite := hpairs ▸ hfin.sdiff
  have hc := ncard_inter_add_ncard_sdiff_eq_ncard (pairs f)
    {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)} hfin
  rw [ncard_pairs_at_two_simple_values h₀ h₁ hc₀ hc₁ hv hfib₀ hfib₁, ← hpairs,
    ordered_ncard_eq_twice_unordered f hfin,
    ordered_ncard_eq_twice_unordered g hgfin] at hc
  omega

theorem unorderedParity_eq_of_card_drop_two
    (h : Nat.card (Unordered g) + 2 = Nat.card (Unordered f)) :
    unorderedParity g = unorderedParity f := by
  unfold unorderedParity
  rw [← h, Nat.cast_add, ZMod.natCast_self, add_zero]

theorem unorderedProj_eq_of_same_value (hf : HasOnlyDoubleFibers f)
    (p q : pairs f) (hv : f p.val.1 = f q.val.1) :
    unorderedProj f p = unorderedProj f q := by
  have h₁ := hf p.val.1 p.val.2 p.property.1 p.property.2 q.val.1 hv.symm
  have h₂ := hf p.val.1 p.val.2 p.property.1 p.property.2 q.val.2
    (q.property.2.symm.trans hv.symm)
  apply (unorderedProj_eq_iff f p q).mpr
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact (q.property.1 (h₁.trans h₂.symm)).elim
  · exact Or.inl (Subtype.ext (Prod.ext h₁.symm h₂.symm))
  · exact Or.inr (Subtype.ext (Prod.ext h₁.symm h₂.symm))
  · exact (q.property.1 (h₁.trans h₂.symm)).elim

theorem exists_distinct_double_values (hf : HasOnlyDoubleFibers f)
    (hfin : (pairs f).Finite) (hcard : 1 < Nat.card (Unordered f)) :
    ∃ p q : pairs f, f p.val.1 ≠ f q.val.1 := by
  let : Finite (Unordered f) := finite_unordered f hfin
  let : Fintype (Unordered f) := Fintype.ofFinite (Unordered f)
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective b
  exact ⟨p, q, fun hv ↦ hab (unorderedProj_eq_of_same_value hf p q hv)⟩

theorem injective_of_unordered_card_zero (hfin : (pairs f).Finite)
    (hcard : Nat.card (Unordered f) = 0) : Injective f := by
  have hzero : (pairs f).ncard = 0 := by
    rw [ordered_ncard_eq_twice_unordered f hfin, hcard, mul_zero]
  have hempty : pairs f = ∅ := (ncard_eq_zero hfin).mp hzero
  intro x y hxy
  by_contra hne
  have hp : (x, y) ∈ pairs f := ⟨hne, hxy⟩
  rw [hempty] at hp
  exact hp

theorem injective_of_small_even_unordered_card (hfin : (pairs f).Finite)
    (hcard : Nat.card (Unordered f) ≤ 1) (hparity : unorderedParity f = 0) :
    Injective f := by
  have heven : Even (Nat.card (Unordered f)) := ZMod.natCast_eq_zero_iff_even.mp hparity
  obtain ⟨k, hk⟩ := heven
  apply injective_of_unordered_card_zero hfin
  omega

end Wikipedia.HopfProblem.DegreeCollapse.DoublePointCounting
