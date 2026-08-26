import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card

/-!
# Basic parameters for Erdős problem 117

The group is not assumed finite. The clique bound quantifies over all finite
sets of pairwise noncommuting elements, and covers consist of actual abelian
subgroups, not cosets.
-/

namespace Erdos117

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Every finite pairwise noncommuting subset has at most `n` elements. -/
def NoncommutingBound (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ s : Finset G, (s : Set G).Pairwise (fun x y => ¬ Commute x y) → s.card ≤ n

/-- An abelian cover indexed by a finite type. -/
def AbelianCover (G : Type*) [Group G] (ι : Type*) (A : ι → Subgroup G) : Prop :=
  (∀ i, IsMulCommutative (A i)) ∧ ∀ x : G, ∃ i, x ∈ A i

/-- Existence of a cover by at most `k` abelian subgroups. -/
def HasAbelianCover (G : Type*) [Group G] (k : ℕ) : Prop :=
  ∃ A : Fin k → Subgroup G, AbelianCover G (Fin k) A

/-- The finite-set formulation retains the original quantification over all
subsets, including infinite subsets. -/
theorem noncommutingBound_iff_subsets (n : ℕ) :
    NoncommutingBound G n ↔
      ∀ S : Set G, (n : ℕ∞) < S.encard →
        ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ Commute x y := by
  classical
  constructor
  · intro h S hS
    by_contra hn
    have hpair : S.Pairwise (fun x y => ¬ Commute x y) := by
      intro x hx y hy hxy hcomm
      exact hn ⟨x, hx, y, hy, hxy, hcomm⟩
    by_cases hfin : S.Finite
    · have hc := h hfin.toFinset (by simpa using hpair)
      have henc : S.encard ≤ (n : ℕ∞) := by
        rw [hfin.encard_eq_coe_toFinset_card]
        exact_mod_cast hc
      exact (not_lt_of_ge henc) hS
    · obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin (n + 1)
      have hc := h s (hpair.mono hs)
      omega
  · intro h s hs
    by_contra hn
    have hcard : (n : ℕ∞) < (s : Set G).encard := by
      simpa using (show (n : ℕ∞) < (s.card : ℕ∞) from by exact_mod_cast Nat.lt_of_not_ge hn)
    obtain ⟨x, hx, y, hy, hxy, hcomm⟩ := h s hcard
    exact hs hx hy hxy hcomm

theorem noncommutingBound_mono {n m : ℕ} (h : NoncommutingBound G n)
    (hnm : n ≤ m) : NoncommutingBound G m :=
  fun s hs => (h s hs).trans hnm

theorem one_le_of_noncommutingBound {n : ℕ} (h : NoncommutingBound G n) : 1 ≤ n := by
  classical
  simpa using h {1} (by simp)

theorem NoncommutingBound.card_le {n : ℕ} (h : NoncommutingBound G n)
    {ι : Type*} [Fintype ι] {a : ι → G}
    (ha : ∀ i j, i ≠ j → ¬Commute (a i) (a j)) : Fintype.card ι ≤ n := by
  classical
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact ha i j hne (hij ▸ Commute.refl _)
  have hs := h (Finset.univ.image a) (by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact ha i j (fun h => hxy (congrArg a h)))
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hs

theorem NoncommutingBound.subgroup {n : ℕ} (h : NoncommutingBound G n) (H : Subgroup G) :
    NoncommutingBound H n := by
  classical
  intro s hs
  have hfamily : ∀ x y : s, x ≠ y → ¬Commute (x.val : G) (y.val : G) := by
    intro x y hxy hc
    exact hs x.2 y.2 (fun h => hxy (Subtype.ext h)) (Subtype.ext hc.eq)
  have hc := h.card_le hfamily
  simpa using hc

theorem abelianCover_of_commuting_coloring {ι : Type*} (c : G → ι)
    (hc : ∀ x y, c x = c y → Commute x y) :
    AbelianCover G ι (fun i => Subgroup.closure {x | c x = i}) := by
  constructor
  · intro i
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy
    exact (hc x y (hx.trans hy.symm)).eq
  · intro x
    exact ⟨c x, Subgroup.subset_closure rfl⟩

theorem commuting_coloring_of_abelianCover {ι : Type*} {A : ι → Subgroup G}
    (h : AbelianCover G ι A) :
    ∃ c : G → ι, ∀ x y, c x = c y → Commute x y := by
  classical
  choose c hc using h.2
  refine ⟨c, fun x y hxy => ?_⟩
  have := h.1 (c x)
  have hy : y ∈ A (c x) := hxy ▸ hc y
  exact congrArg Subtype.val (mul_comm' (⟨x, hc x⟩ : A (c x)) ⟨y, hy⟩)

theorem hasAbelianCover_iff_coloring (k : ℕ) :
    HasAbelianCover G k ↔
      ∃ c : G → Fin k, ∀ x y, c x = c y → Commute x y := by
  constructor
  · rintro ⟨A, hA⟩
    exact commuting_coloring_of_abelianCover hA
  · rintro ⟨c, hc⟩
    exact ⟨_, abelianCover_of_commuting_coloring c hc⟩

theorem hasAbelianCover_mono {k l : ℕ} (h : HasAbelianCover G k) (hkl : k ≤ l) :
    HasAbelianCover G l := by
  obtain ⟨c, hc⟩ := (hasAbelianCover_iff_coloring k).mp h
  apply (hasAbelianCover_iff_coloring l).mpr
  exact ⟨fun x => Fin.castLE hkl (c x), fun x y hxy =>
    hc x y (Fin.castLE_injective hkl hxy)⟩

/-- Pull back a cover through any map that reflects commutation. -/
theorem hasAbelianCover_of_commute_reflecting {H : Type*} [Group H] (f : G → H)
    (hf : ∀ x y, Commute (f x) (f y) → Commute x y) {k : ℕ}
    (h : HasAbelianCover H k) : HasAbelianCover G k := by
  obtain ⟨c, hc⟩ := (hasAbelianCover_iff_coloring k).mp h
  apply (hasAbelianCover_iff_coloring k).mpr
  exact ⟨c ∘ f, fun x y hxy => hf x y (hc _ _ hxy)⟩

/-- A commutation-reflecting map cannot decrease the clique bound. -/
theorem noncommutingBound_of_commute_reflecting {H : Type*} [Group H] (f : G → H)
    (hf : ∀ x y, Commute (f x) (f y) → Commute x y) {n : ℕ}
    (h : NoncommutingBound H n) : NoncommutingBound G n := by
  classical
  intro s hs
  have hinj : Set.InjOn f s := by
    intro x hx y hy hxy
    by_contra hne
    exact hs hx hy hne (hf x y (hxy ▸ Commute.refl (f x)))
  have hp : ((s.image f : Finset H) : Set H).Pairwise (fun x y => ¬ Commute x y) := by
    intro x hx y hy hne hcomm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact hs hu hv (fun h => hne (congrArg f h)) (hf u v hcomm)
  simpa only [Finset.card_image_of_injOn hinj] using h _ hp

/-- A surjective commutation-preserving map transports every clique bound. -/
theorem noncommutingBound_of_surjective {H : Type*} [Group H] (f : G → H)
    (hs : Function.Surjective f) (hf : ∀ x y, Commute x y → Commute (f x) (f y))
    {n : ℕ} (h : NoncommutingBound G n) : NoncommutingBound H n := by
  classical
  choose g hg using hs
  exact noncommutingBound_of_commute_reflecting g (fun x y hc => by
    simpa only [hg] using hf (g x) (g y) hc) h

/-- A surjective commutation-preserving map also transports abelian covers. -/
theorem hasAbelianCover_of_surjective {H : Type*} [Group H] (f : G → H)
    (hs : Function.Surjective f) (hf : ∀ x y, Commute x y → Commute (f x) (f y))
    {k : ℕ} (h : HasAbelianCover G k) : HasAbelianCover H k := by
  classical
  choose g hg using hs
  exact hasAbelianCover_of_commute_reflecting g (fun x y hc => by
    simpa only [hg] using hf (g x) (g y) hc) h

theorem commute_mulEquiv_iff {H : Type*} [Group H] (e : G ≃* H) (x y : G) :
    Commute (e x) (e y) ↔ Commute x y := by
  rw [commute_iff_eq, commute_iff_eq, ← e.map_mul, ← e.map_mul, e.injective.eq_iff]

theorem noncommutingBound_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    {n : ℕ} (h : NoncommutingBound G n) : NoncommutingBound H n := by
  classical
  intro s hs
  have hp : ((s.image e.symm : Finset G) : Set G).Pairwise
      (fun x y => ¬ Commute x y) := by
    intro x hx y hy hxy hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hs ha hb (fun h => hxy (congrArg e.symm h))
      ((commute_mulEquiv_iff e.symm a b).mp hc)
  simpa only [Finset.card_image_of_injective _ e.symm.injective] using h _ hp

theorem hasAbelianCover_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    {k : ℕ} (h : HasAbelianCover G k) : HasAbelianCover H k := by
  obtain ⟨c, hc⟩ := (hasAbelianCover_iff_coloring k).mp h
  apply (hasAbelianCover_iff_coloring k).mpr
  exact ⟨fun x => c (e.symm x), fun x y hxy =>
    (commute_mulEquiv_iff e.symm x y).mp (hc _ _ hxy)⟩

theorem noncommutingBound_of_abelianCover {k : ℕ} (h : HasAbelianCover G k) :
    NoncommutingBound G k := by
  classical
  obtain ⟨c, hc⟩ := (hasAbelianCover_iff_coloring k).mp h
  intro s hs
  have hi : Set.InjOn c s := by
    intro x hx y hy hxy
    by_contra hn
    exact hs hx hy hn (hc x y hxy)
  calc
    s.card = (s.image c).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ Fintype.card (Fin k) := Finset.card_le_univ _
    _ = k := Fintype.card_fin k

theorem card_le_sum_card_of_cover [Fintype G] {ι : Type*} [Fintype ι]
    (A : ι → Subgroup G) [∀ i, Fintype (A i)]
    (h : ∀ x : G, ∃ i, x ∈ A i) :
    Fintype.card G ≤ ∑ i, Fintype.card (A i) := by
  let f : (Σ i, A i) → G := fun a => a.2
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := h x
    exact ⟨⟨i, x, hi⟩, rfl⟩
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_surjective f hf

end Erdos117
