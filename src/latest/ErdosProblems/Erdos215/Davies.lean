import Mathlib

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Davies decompositions for countably many finitary operations

This file isolates the set-theoretic closure interface used in the proof of
Erdős Problem 215.  A `SkolemFamily` is a countable list of operations on
finite lists.  `SkolemFamily.Hull s` is the least set containing `s` and
closed under all those operations.

The eventual Davies decomposition is expressed using terminal, countable
layers and finitely many predecessor guards.  The guard formulation is the
part of the classical iterated-hull proof that later geometric arguments
actually use.
-/

namespace Erdos215

open Set Cardinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

/-- A countable family of Skolem operations of arbitrary finite arity. -/
abbrev SkolemFamily (U : Type u) := ℕ → List U → U

namespace SkolemFamily

variable {U : Type u} (sk : SkolemFamily U)

/-- One application of a Skolem operation to parameters from `s`. -/
def Step (s : Set U) : Set U :=
  s ∪ {y | ∃ (n : ℕ) (xs : List U), (∀ x ∈ xs, x ∈ s) ∧ sk n xs = y}

/-- The closure obtained after finitely many rounds of Skolem operations. -/
def Hull (s : Set U) : Set U :=
  ⋃ k : ℕ, (Step sk)^[k] s

@[simp]
theorem subset_step (s : Set U) : s ⊆ sk.Step s := by
  intro x hx
  exact Or.inl hx

theorem step_mono : Monotone sk.Step := by
  intro s t hst x hx
  rcases hx with hx | ⟨n, xs, hxs, rfl⟩
  · exact Or.inl (hst hx)
  · exact Or.inr ⟨n, xs, fun y hy ↦ hst (hxs y hy), rfl⟩

theorem iterate_subset_iterate_succ (s : Set U) (k : ℕ) :
    (sk.Step)^[k] s ⊆ (sk.Step)^[k + 1] s := by
  rw [Function.iterate_succ_apply']
  exact sk.subset_step _

theorem iterate_subset_of_le (s : Set U) {k l : ℕ} (hkl : k ≤ l) :
    (sk.Step)^[k] s ⊆ (sk.Step)^[l] s := by
  induction l, hkl using Nat.le_induction with
  | base => exact Subset.rfl
  | succ l hkl ih =>
      exact ih.trans (sk.iterate_subset_iterate_succ s l)

theorem subset_hull (s : Set U) : s ⊆ sk.Hull s := by
  intro x hx
  exact mem_iUnion.2 ⟨0, hx⟩

theorem hull_mono : Monotone sk.Hull := by
  intro s t hst x hx
  rcases mem_iUnion.1 hx with ⟨k, hk⟩
  refine mem_iUnion.2 ⟨k, ?_⟩
  exact (sk.step_mono.iterate k) hst hk

theorem step_subset_hull (s : Set U) : sk.Step (sk.Hull s) ⊆ sk.Hull s := by
  intro y hy
  rcases hy with hy | ⟨n, xs, hxs, rfl⟩
  · exact hy
  · have hex : ∃ k : ℕ, ∀ x ∈ xs, x ∈ (sk.Step)^[k] s := by
      induction xs with
      | nil => exact ⟨0, by simp⟩
      | cons a xs ih =>
          obtain ⟨ka, hka⟩ := mem_iUnion.1 (hxs a (by simp))
          obtain ⟨kl, hkl⟩ := ih (fun x hx ↦ hxs x (by simp [hx]))
          refine ⟨max ka kl, ?_⟩
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact sk.iterate_subset_of_le s (Nat.le_max_left _ _) hka
          · exact sk.iterate_subset_of_le s (Nat.le_max_right _ _) (hkl x hx)
    rcases hex with ⟨k, hk⟩
    refine mem_iUnion.2 ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    exact (Or.inr ⟨n, xs, hk, rfl⟩ : sk n xs ∈ sk.Step ((sk.Step)^[k] s))

/-- A set is closed under the selected Skolem operations. -/
def Closed (s : Set U) : Prop :=
  ∀ (n : ℕ) (xs : List U), (∀ x ∈ xs, x ∈ s) → sk n xs ∈ s

theorem closed_hull (s : Set U) : sk.Closed (sk.Hull s) := by
  intro n xs hxs
  exact sk.step_subset_hull s (Or.inr ⟨n, xs, hxs, rfl⟩)

theorem hull_min {s t : Set U} (hst : s ⊆ t) (ht : sk.Closed t) : sk.Hull s ⊆ t := by
  intro x hx
  rcases mem_iUnion.1 hx with ⟨k, hk⟩
  have hiter : ∀ m : ℕ, (sk.Step)^[m] s ⊆ t := by
    intro m
    induction m with
    | zero => exact hst
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        rintro y (hy | ⟨n, xs, hxs, rfl⟩)
        · exact ih hy
        · exact ht n xs (fun z hz ↦ ih (hxs z hz))
  exact hiter k hk

theorem countable_step {s : Set U} (hs : s.Countable) : (sk.Step s).Countable := by
  classical
  let : Countable s := hs.to_subtype
  let values : ℕ × List s → U := fun p ↦ sk p.1 (p.2.map Subtype.val)
  have liftList : ∀ (xs : List U), (∀ x ∈ xs, x ∈ s) →
      ∃ ys : List s, ys.map Subtype.val = xs := by
    intro xs
    induction xs with
    | nil => exact fun _ ↦ ⟨[], rfl⟩
    | cons x xs ih =>
        intro hxs
        obtain ⟨ys, hys⟩ := ih (fun y hy ↦ hxs y (by simp [hy]))
        refine ⟨⟨x, hxs x (by simp)⟩ :: ys, ?_⟩
        simp [hys]
  apply hs.union
  refine (countable_range values).mono ?_
  rintro y ⟨n, xs, hxs, rfl⟩
  obtain ⟨ys, hys⟩ := liftList xs hxs
  exact ⟨(n, ys), by simp only [values, hys]⟩

theorem countable_iterate {s : Set U} (hs : s.Countable) (k : ℕ) :
    ((sk.Step)^[k] s).Countable := by
  induction k with
  | zero => exact hs
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact sk.countable_step ih

/-- Countably many finitary operations generate only countably many points
from a countable set of parameters. -/
theorem countable_hull {s : Set U} (hs : s.Countable) : (sk.Hull s).Countable := by
  exact countable_iUnion (sk.countable_iterate hs)

/-- One Skolem round does not increase an infinite cardinal bound. -/
theorem mk_step_le_max (s : Set U) :
    #(sk.Step s) ≤ max ℵ₀ (Cardinal.mk s) := by
  classical
  let code : s ⊕ (ℕ × List s) → U
    | Sum.inl x => x.1
    | Sum.inr p => sk p.1 (p.2.map Subtype.val)
  have hsub : sk.Step s ⊆ Set.range code := by
    rintro y (hy | ⟨n, xs, hxs, rfl⟩)
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · have liftList : ∃ ys : List s, ys.map Subtype.val = xs := by
        induction xs with
        | nil => exact ⟨[], rfl⟩
        | cons x xs ih =>
            obtain ⟨ys, hys⟩ := ih (fun y hy ↦ hxs y (by simp [hy]))
            exact ⟨⟨x, hxs x (by simp)⟩ :: ys, by simp [hys]⟩
      obtain ⟨ys, hys⟩ := liftList
      refine ⟨Sum.inr (n, ys), ?_⟩
      change sk n (ys.map Subtype.val) = sk n xs
      rw [hys]
  let K : Cardinal := max ℵ₀ (Cardinal.mk s)
  have hK : ℵ₀ ≤ K := le_max_left _ _
  calc
    #(sk.Step s) ≤ #(Set.range code) := Cardinal.mk_subtype_mono (fun _ hx ↦ hsub hx)
    _ ≤ #(s ⊕ (ℕ × List s)) := Cardinal.mk_range_le
    _ = #s + ℵ₀ * #(List s) := by simp
    _ ≤ K + K * K := by
      exact add_le_add (le_max_right _ _) <|
        mul_le_mul' (le_max_left _ _) (Cardinal.mk_list_le_max _)
    _ = K := by
      rw [Cardinal.mul_eq_self hK]
      exact Cardinal.add_eq_left hK le_rfl

theorem mk_iterate_le_max (s : Set U) (k : ℕ) :
    #((sk.Step)^[k] s) ≤ max ℵ₀ (Cardinal.mk s) := by
  let K : Cardinal := max ℵ₀ (Cardinal.mk s)
  have hK : ℵ₀ ≤ K := le_max_left _ _
  induction k with
  | zero => exact le_max_right _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (sk.mk_step_le_max _).trans <| max_le hK ih

/-- Cardinal form of the downward Löwenheim--Skolem estimate for this coded
Skolem language.  It is valid without any regularity assumption on the
ambient cardinal. -/
theorem mk_hull_le_max (s : Set U) :
    #(sk.Hull s) ≤ max ℵ₀ (Cardinal.mk s) := by
  let K : Cardinal := max ℵ₀ (Cardinal.mk s)
  have hK : ℵ₀ ≤ K := le_max_left _ _
  calc
    #(sk.Hull s) ≤ (ℵ₀ : Cardinal.{u}) * ⨆ k : ℕ, #((sk.Step)^[k] s) := by
      simpa [Hull] using
        (Cardinal.mk_iUnion_le_lift (fun k : ℕ ↦ (sk.Step)^[k] s))
    _ ≤ K * K := by
      refine mul_le_mul' ?_ ?_
      · simpa using hK
      · exact ciSup_le' (sk.mk_iterate_le_max s)
    _ = K := Cardinal.mul_eq_self hK

end SkolemFamily

namespace DaviesSplit

variable {U : Type u} (sk : SkolemFamily U)

/-- The initial ordinal of the cardinality of a region. -/
abbrev Stage (N : Set U) := (Cardinal.mk N).ord.ToType

/-- A fixed enumeration of a region in initial-ordinal order. -/
noncomputable def enumerate (N : Set U) : Stage N ≃ N :=
  Classical.choice <| Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk N))

/-- Parameters enumerated no later than stage `i`. -/
def seed (N : Set U) (i : Stage N) : Set U :=
  Set.range fun j : Set.Iic i ↦ (enumerate N j.1).1

/-- Parameters enumerated strictly before stage `i`. -/
def strictSeed (N : Set U) (i : Stage N) : Set U :=
  Set.range fun j : Set.Iio i ↦ (enumerate N j.1).1

/-- The upper relative hull at `i`; it contains the `i`-th enumerated point. -/
def upper (N : Set U) (i : Stage N) : Set U :=
  N ∩ sk.Hull (seed N i)

/-- The continuous lower boundary at `i`, namely the union of all earlier
upper relative hulls.  Defining the zeroth boundary this way makes it empty,
as required in the Davies construction even when the Skolem language has
constants. -/
def lower (N : Set U) (i : Stage N) : Set U :=
  ⋃ j : Set.Iio i, upper sk N j.1

/-- The successor-difference region at `i`. -/
def difference (N : Set U) (i : Stage N) : Set U :=
  upper sk N i \ lower sk N i

theorem strictSeed_subset_seed (N : Set U) (i : Stage N) :
    strictSeed N i ⊆ seed N i := by
  rintro x ⟨j, rfl⟩
  refine ⟨⟨j.1, ?_⟩, rfl⟩
  simpa only [Set.mem_Iic] using j.2.le

theorem lower_subset_upper (N : Set U) (i : Stage N) :
    lower sk N i ⊆ upper sk N i := by
  rintro x hx
  rcases mem_iUnion.1 hx with ⟨j, hxj⟩
  refine inter_subset_inter_right N (sk.hull_mono ?_) hxj
  rintro y ⟨k, rfl⟩
  refine ⟨⟨k.1, ?_⟩, rfl⟩
  have hkj : k.1 ≤ j.1 := by simpa only [Set.mem_Iic] using k.2
  have hji : j.1 < i := by simpa only [Set.mem_Iio] using j.2
  simpa only [Set.mem_Iic] using hkj.trans hji.le

theorem enumerate_mem_upper (N : Set U) (i : Stage N) :
    (enumerate N i).1 ∈ upper sk N i := by
  refine ⟨(enumerate N i).2, sk.subset_hull _ ?_⟩
  refine ⟨⟨i, ?_⟩, rfl⟩
  simp

theorem seed_mono {N : Set U} {i j : Stage N} (hij : i < j) :
    seed N i ⊆ strictSeed N j := by
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k.1, k.2.trans_lt hij⟩, rfl⟩

theorem seed_mono_le {N : Set U} {i j : Stage N} (hij : i ≤ j) :
    seed N i ⊆ seed N j := by
  rintro x ⟨k, rfl⟩
  refine ⟨⟨k.1, ?_⟩, rfl⟩
  have hki : k.1 ≤ i := by simpa only [Set.mem_Iic] using k.2
  simpa only [Set.mem_Iic] using hki.trans hij

theorem upper_mono {N : Set U} {i j : Stage N} (hij : i ≤ j) :
    upper sk N i ⊆ upper sk N j :=
  inter_subset_inter_right N <| sk.hull_mono (seed_mono_le hij)

theorem upper_subset_lower {N : Set U} {i j : Stage N} (hij : i < j) :
    upper sk N i ⊆ lower sk N j := by
  intro x hx
  exact mem_iUnion.2 ⟨⟨i, hij⟩, hx⟩

theorem iUnion_difference_eq (N : Set U) :
    ⋃ i, difference sk N i = N := by
  apply Set.Subset.antisymm
  · rintro x hx
    rcases mem_iUnion.1 hx with ⟨i, hxi⟩
    exact hxi.1.1
  · intro x hxN
    let A : Set (Stage N) := {i | x ∈ upper sk N i}
    have hA : A.Nonempty := by
      let i := (enumerate N).symm ⟨x, hxN⟩
      refine ⟨i, ?_⟩
      have he : (enumerate N i).1 = x := congrArg Subtype.val ((enumerate N).apply_symm_apply ⟨x, hxN⟩)
      simpa [A, he] using enumerate_mem_upper sk N i
    obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min A hA
    refine mem_iUnion.2 ⟨i, hi, ?_⟩
    intro hlow
    rcases mem_iUnion.1 hlow with ⟨j, hxj⟩
    exact hmin j.1 hxj j.2

theorem difference_pairwise_disjoint (N : Set U) :
    Pairwise fun i j : Stage N ↦ Disjoint (difference sk N i) (difference sk N j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    exact hxj.2 ((upper_subset_lower sk hij) hxi.1)
  · refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    exact hxi.2 ((upper_subset_lower sk hji) hxj.1)

theorem mk_seed_lt (N : Set U) (i : Stage N) (hN : ℵ₀ < Cardinal.mk N) :
    Cardinal.mk (seed N i) < Cardinal.mk N := by
  refine (Cardinal.mk_range_le.trans_lt ?_)
  have hstage : ℵ₀ ≤ Cardinal.mk (Stage N) := by
    simpa [Stage] using hN.le
  simpa [Stage] using Cardinal.mk_Iic_lt i (by simp) hstage

/-- Every child difference has cardinality strictly below that of an
uncountable parent region.  This is the termination measure for the Davies
tree, and uses no regularity of the parent cardinal. -/
theorem mk_difference_lt (N : Set U) (i : Stage N) (hN : ℵ₀ < Cardinal.mk N) :
    Cardinal.mk (difference sk N i) < Cardinal.mk N := by
  have hseed : Cardinal.mk (seed N i) < Cardinal.mk N := mk_seed_lt N i hN
  calc
    Cardinal.mk (difference sk N i) ≤ Cardinal.mk (sk.Hull (seed N i)) :=
      Cardinal.mk_subtype_mono fun _ hx ↦ hx.1.2
    _ ≤ max ℵ₀ (Cardinal.mk (seed N i)) := sk.mk_hull_le_max _
    _ < Cardinal.mk N := max_lt hN hseed

end DaviesSplit

/-- Operations applied to parameters from `N` stay in the region `B ∪ N`. -/
def LocallyClosed {U : Type u} (sk : SkolemFamily U) (B N : Set U) : Prop :=
  ∀ n xs, (∀ x ∈ xs, x ∈ N) → sk n xs ∈ B ∪ N

/-- A finite family of predecessor guards, each of which forces Skolem values
into `B`, and whose union is exactly `B`. -/
def IsGuardBase {U : Type u} (sk : SkolemFamily U) (B : Set U)
    (G : Finset (Set U)) : Prop :=
  B = ⋃ g ∈ G, g ∧
    ∀ g ∈ G, ∀ n xs, (∀ x ∈ xs, x ∈ g) → sk n xs ∈ B

namespace DaviesSplit

variable {U : Type u} (sk : SkolemFamily U)

theorem upper_subset_parent (B N : Set U) (i : Stage N) :
    upper sk N i ⊆ B ∪ N := fun _ hx ↦ Or.inr hx.1

theorem lower_subset_parent (B N : Set U) (i : Stage N) :
    lower sk N i ⊆ B ∪ N := fun _ hx ↦ Or.inr ((lower_subset_upper sk N i hx).1)

/-- A finite list of points in a nonempty lower boundary is contained in one
earlier upper hull. -/
theorem list_bounded_in_lower {N : Set U} {i : Stage N}
    (hne : (lower sk N i).Nonempty) (xs : List U)
    (hxs : ∀ x ∈ xs, x ∈ lower sk N i) :
    ∃ j : Stage N, j < i ∧ ∀ x ∈ xs, x ∈ upper sk N j := by
  obtain ⟨z, hz⟩ := hne
  rcases mem_iUnion.1 hz with ⟨j0, hz0⟩
  have hj0 : j0.1 < i := by simpa only [Set.mem_Iio] using j0.2
  induction xs with
  | nil => exact ⟨j0.1, hj0, by simp⟩
  | cons x xs ih =>
      rcases mem_iUnion.1 (hxs x (by simp)) with ⟨jx, hxj⟩
      have hjx : jx.1 < i := by simpa only [Set.mem_Iio] using jx.2
      obtain ⟨jt, hjt, htail⟩ := ih (fun y hy ↦ hxs y (by simp [hy]))
      refine ⟨max jx.1 jt, max_lt hjx hjt, ?_⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact upper_mono sk (le_max_left _ _) hxj
      · exact upper_mono sk (le_max_right _ _) (htail y hy)

/-- `(D6)` for a nonempty lower relative piece. -/
theorem skolem_mem_base_union_lower {B N : Set U} {i : Stage N}
    (hlocal : LocallyClosed sk B N) (hne : (lower sk N i).Nonempty)
    (n : ℕ) (xs : List U) (hxs : ∀ x ∈ xs, x ∈ lower sk N i) :
    sk n xs ∈ B ∪ lower sk N i := by
  obtain ⟨j, hj, hupper⟩ := list_bounded_in_lower sk hne xs hxs
  have hparent : sk n xs ∈ B ∪ N :=
    hlocal n xs (fun x hx ↦ (lower_subset_upper sk N i (hxs x hx)).1)
  have hhull : sk n xs ∈ sk.Hull (seed N j) :=
    sk.closed_hull _ n xs (fun x hx ↦ (hupper x hx).2)
  rcases hparent with hB | hN
  · exact Or.inl hB
  · exact Or.inr <| mem_iUnion.2 ⟨⟨j, hj⟩, hN, hhull⟩

/-- The child successor difference is locally closed over the enlarged base
`B ∪ lower i`. -/
theorem difference_locallyClosed {B N : Set U} (hlocal : LocallyClosed sk B N)
    (i : Stage N) :
    LocallyClosed sk (B ∪ lower sk N i) (difference sk N i) := by
  intro n xs hxs
  have hparent : sk n xs ∈ B ∪ N :=
    hlocal n xs (fun x hx ↦ (hxs x hx).1.1)
  have hhull : sk n xs ∈ sk.Hull (seed N i) :=
    sk.closed_hull _ n xs (fun x hx ↦ (hxs x hx).1.2)
  rcases hparent with hB | hN
  · exact Or.inl (Or.inl hB)
  · have hu : sk n xs ∈ upper sk N i := ⟨hN, hhull⟩
    by_cases hl : sk n xs ∈ lower sk N i
    · exact Or.inl (Or.inr hl)
    · exact Or.inr ⟨hu, hl⟩

theorem prior_differences_eq_lower (N : Set U) (i : Stage N) :
    {x | ∃ j, j < i ∧ x ∈ difference sk N j} = lower sk N i := by
  apply Set.Subset.antisymm
  · rintro x ⟨j, hji, hxj⟩
    exact mem_iUnion.2 ⟨⟨j, hji⟩, hxj.1⟩
  · intro x hx
    rcases mem_iUnion.1 hx with ⟨j, hxj⟩
    have hji : j.1 < i := by simpa only [Set.mem_Iio] using j.2
    have hxN : x ∈ N := hxj.1
    have hall : x ∈ ⋃ k, difference sk N k := by
      rw [iUnion_difference_eq sk N]
      exact hxN
    rcases mem_iUnion.1 hall with ⟨k, hxk⟩
    refine ⟨k, ?_, hxk⟩
    by_contra hki
    have hik : i ≤ k := le_of_not_gt hki
    have hjk : j.1 < k := hji.trans_le hik
    exact hxk.2 ((upper_subset_lower sk hjk) hxj)
    

end DaviesSplit

/-- A Davies decomposition relative to an already constructed predecessor
region `B`.  The finite guard family at a terminal stage covers `B` together
with all earlier terminal layers. -/
structure RelativeDavies {U : Type u} (sk : SkolemFamily U)
    (B N : Set U) where
  Index : Type u
  lt : Index → Index → Prop
  isWellOrder : IsWellOrder Index lt
  layer : Index → Set U
  layer_countable : ∀ i, (layer i).Countable
  layer_disjoint : Pairwise fun i j ↦ Disjoint (layer i) (layer j)
  layer_cover : ⋃ i, layer i = N
  guards : Index → Finset (Set U)
  guards_cover : ∀ i,
    B ∪ {x | ∃ j, lt j i ∧ x ∈ layer j} = ⋃ g ∈ guards i, g
  guard_closed : ∀ i g, g ∈ guards i → ∀ n xs,
    (∀ x ∈ xs, x ∈ g) →
      sk n xs ∈ B ∪ {x | ∃ j, lt j i ∧ x ∈ layer j}
  layer_closed : ∀ i n xs, (∀ x ∈ xs, x ∈ layer i) →
    sk n xs ∈
      (B ∪ {x | ∃ j, lt j i ∧ x ∈ layer j}) ∪ layer i

namespace RelativeDavies

variable {U : Type u} {sk : SkolemFamily U} {B N : Set U}

theorem layer_subset_region (D : RelativeDavies sk B N) (i : D.Index) :
    D.layer i ⊆ N := by
  intro x hx
  have hx' : x ∈ ⋃ j, D.layer j := mem_iUnion.2 ⟨i, hx⟩
  rw [D.layer_cover] at hx'
  exact hx'

noncomputable def childGuards (sk : SkolemFamily U) (G : Finset (Set U))
    (i : DaviesSplit.Stage N) :
    Finset (Set U) := by
  classical
  exact if (DaviesSplit.lower sk N i).Nonempty then
      insert (DaviesSplit.lower sk N i) G
    else G

theorem childGuards_valid (G : Finset (Set U)) (hG : IsGuardBase sk B G)
    (hlocal : LocallyClosed sk B N) (i : DaviesSplit.Stage N) :
    IsGuardBase sk (B ∪ DaviesSplit.lower sk N i) (childGuards sk G i) := by
  classical
  by_cases hne : (DaviesSplit.lower sk N i).Nonempty
  · rw [childGuards, if_pos hne]
    constructor
    · rw [hG.1]
      simp only [Finset.mem_insert, iUnion_iUnion_eq_left]
      ext x
      simp [or_comm, or_left_comm]
    · intro g hg n xs hxs
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · exact DaviesSplit.skolem_mem_base_union_lower sk hlocal hne n xs hxs
      · exact Or.inl (hG.2 g hg n xs hxs)
  · have hempty : DaviesSplit.lower sk N i = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [childGuards, if_neg hne, hempty, union_empty]
    exact hG

/-- The countable base case of the cardinal recursion. -/
def ofCountable (G : Finset (Set U)) (hG : IsGuardBase sk B G)
    (hN : N.Countable) (hlocal : LocallyClosed sk B N) :
    RelativeDavies sk B N where
  Index := ULift.{u} (Fin 1)
  lt := (fun i j ↦ i < j)
  isWellOrder := inferInstance
  layer := fun _ ↦ N
  layer_countable := fun _ ↦ hN
  layer_disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  layer_cover := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨i, hxi⟩
      exact hxi
    · intro x hx
      exact mem_iUnion.2 ⟨ULift.up (0 : Fin 1), hx⟩
  guards := fun _ ↦ G
  guards_cover := by
    intro i
    have hempty : {x | ∃ j, j < i ∧ x ∈ N} = (∅ : Set U) := by
      ext x
      constructor
      · rintro ⟨j, hji, hx⟩
        have hji' : i < i := by simpa [Subsingleton.elim j i] using hji
        exact (lt_irrefl i hji').elim
      · simp
    rw [hempty, union_empty]
    exact hG.1
  guard_closed := by
    intro i g hg n xs hxs
    exact Or.inl (hG.2 g hg n xs hxs)
  layer_closed := by
    intro i n xs hxs
    rcases hlocal n xs hxs with hB | hN
    · exact Or.inl (Or.inl hB)
    · exact Or.inr hN

theorem lex_before_eq (hlocal : LocallyClosed sk B N)
    (child : ∀ i : DaviesSplit.Stage N,
      RelativeDavies sk (B ∪ DaviesSplit.lower sk N i) (DaviesSplit.difference sk N i))
    (i : DaviesSplit.Stage N) (a : (child i).Index) :
    {x | ∃ q : Σ j, (child j).Index,
      Sigma.Lex (fun x y : DaviesSplit.Stage N ↦ x < y) (fun j ↦ (child j).lt) q ⟨i, a⟩ ∧
        x ∈ (child q.1).layer q.2} =
      DaviesSplit.lower sk N i ∪
        {x | ∃ b, (child i).lt b a ∧ x ∈ (child i).layer b} := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, hxq⟩
    rcases q with ⟨j, b⟩
    cases hq with
    | left _ _ hji =>
        apply Or.inl
        rw [← DaviesSplit.prior_differences_eq_lower sk N i]
        exact ⟨j, hji, (child j).layer_subset_region b hxq⟩
    | right _ _ hba =>
        exact Or.inr ⟨b, hba, hxq⟩
  · rintro x (hx | hx)
    · rw [← DaviesSplit.prior_differences_eq_lower sk N i] at hx
      rcases hx with ⟨j, hji, hxj⟩
      have hxcover : x ∈ ⋃ b, (child j).layer b := by
        rw [(child j).layer_cover]
        exact hxj
      rcases mem_iUnion.1 hxcover with ⟨b, hxb⟩
      exact ⟨⟨j, b⟩, Sigma.Lex.left _ _ hji, hxb⟩
    · rcases hx with ⟨b, hba, hxb⟩
      exact ⟨⟨i, b⟩, Sigma.Lex.right _ _ hba, hxb⟩

/-- Assemble the recursively decomposed successor differences in
lexicographic order. -/
def combine (hlocal : LocallyClosed sk B N)
    (child : ∀ i : DaviesSplit.Stage N,
      RelativeDavies sk (B ∪ DaviesSplit.lower sk N i) (DaviesSplit.difference sk N i)) :
    RelativeDavies sk B N where
  Index := Σ i : DaviesSplit.Stage N, (child i).Index
  lt := Sigma.Lex (fun i j : DaviesSplit.Stage N ↦ i < j) (fun i ↦ (child i).lt)
  isWellOrder := {
    wf := by
      let e := (Equiv.psigmaEquivSigma (fun i : DaviesSplit.Stage N ↦ (child i).Index)).symm
      have hp : WellFounded
          (PSigma.Lex (fun i j : DaviesSplit.Stage N ↦ i < j) (fun i ↦ (child i).lt)) :=
        wellFounded_lt.psigma_lex fun i ↦ (child i).isWellOrder.wf
      have he : WellFounded (Function.onFun
          (PSigma.Lex (fun i j : DaviesSplit.Stage N ↦ i < j) (fun i ↦ (child i).lt)) e) :=
        hp.onFun
      apply he.mono
      intro x y hxy
      cases hxy with
      | left a b hij => exact PSigma.Lex.left _ _ hij
      | right a b hab => exact PSigma.Lex.right _ hab
    trichotomous := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hnij hnji
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (hnij (Sigma.Lex.left _ _ hij)).elim
      · have hab : a = b := (child i).isWellOrder.trichotomous a b
            (fun h ↦ hnij (Sigma.Lex.right _ _ h))
            (fun h ↦ hnji (Sigma.Lex.right _ _ h))
        cases hab
        rfl
      · exact (hnji (Sigma.Lex.left _ _ hji)).elim
    }
  layer := fun q ↦ (child q.1).layer q.2
  layer_countable := fun q ↦ (child q.1).layer_countable q.2
  layer_disjoint := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hne
    by_cases hij : i = j
    · subst j
      apply (child i).layer_disjoint
      intro hab
      apply hne
      cases hab
      rfl
    · exact (DaviesSplit.difference_pairwise_disjoint sk N hij).mono
        ((child i).layer_subset_region a) ((child j).layer_subset_region b)
  layer_cover := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases mem_iUnion.1 hx with ⟨q, hxq⟩
      have hd : x ∈ DaviesSplit.difference sk N q.1 :=
        (child q.1).layer_subset_region q.2 hxq
      have hall : x ∈ ⋃ i, DaviesSplit.difference sk N i := mem_iUnion.2 ⟨q.1, hd⟩
      rw [DaviesSplit.iUnion_difference_eq sk N] at hall
      exact hall
    · intro x hx
      have hall : x ∈ ⋃ i, DaviesSplit.difference sk N i := by
        rw [DaviesSplit.iUnion_difference_eq sk N]
        exact hx
      rcases mem_iUnion.1 hall with ⟨i, hxi⟩
      have hc : x ∈ ⋃ a, (child i).layer a := by
        rw [(child i).layer_cover]
        exact hxi
      rcases mem_iUnion.1 hc with ⟨a, hxa⟩
      exact mem_iUnion.2 ⟨⟨i, a⟩, hxa⟩
  guards := fun q ↦ (child q.1).guards q.2
  guards_cover := by
    rintro ⟨i, a⟩
    rw [lex_before_eq hlocal child i a, ← union_assoc]
    exact (child i).guards_cover a
  guard_closed := by
    rintro ⟨i, a⟩ g hg n xs hxs
    have h := (child i).guard_closed a g hg n xs hxs
    rw [lex_before_eq hlocal child i a, ← union_assoc]
    exact h
  layer_closed := by
    rintro ⟨i, a⟩ n xs hxs
    have h := (child i).layer_closed a n xs hxs
    rw [lex_before_eq hlocal child i a, ← union_assoc]
    exact h

/-- The relative Davies decomposition, proved by well-founded recursion on
the cardinality of the current successor-difference region. -/
theorem exists_relative (G : Finset (Set U)) (hG : IsGuardBase sk B G)
    (hlocal : LocallyClosed sk B N) :
    Nonempty (RelativeDavies sk B N) := by
  let P : Cardinal.{u} → Prop := fun κ ↦
    ∀ (B' N' : Set U) (G' : Finset (Set U)),
      IsGuardBase sk B' G' → LocallyClosed sk B' N' → Cardinal.mk N' = κ →
        Nonempty (RelativeDavies sk B' N')
  have build : ∀ κ, P κ := by
    intro κ
    exact Cardinal.lt_wf.induction κ (fun κ ih ↦ by
      dsimp only [P]
      intro B' N' G' hG' hlocal' hcard
      by_cases hc : N'.Countable
      · exact ⟨ofCountable G' hG' hc hlocal'⟩
      · have hunc : ℵ₀ < Cardinal.mk N' := by
          apply lt_of_not_ge
          intro hle
          exact hc (Cardinal.mk_le_aleph0_iff.mp hle)
        have child_exists : ∀ i : DaviesSplit.Stage N',
            Nonempty (RelativeDavies sk
              (B' ∪ DaviesSplit.lower sk N' i) (DaviesSplit.difference sk N' i)) := by
          intro i
          have hlt : Cardinal.mk (DaviesSplit.difference sk N' i) < κ :=
            (DaviesSplit.mk_difference_lt sk N' i hunc).trans_eq hcard
          exact ih _ hlt
            (B' ∪ DaviesSplit.lower sk N' i) (DaviesSplit.difference sk N' i)
            (childGuards sk G' i) (childGuards_valid G' hG' hlocal' i)
            (DaviesSplit.difference_locallyClosed sk hlocal' i) rfl
        let child : ∀ i : DaviesSplit.Stage N',
            RelativeDavies sk
              (B' ∪ DaviesSplit.lower sk N' i) (DaviesSplit.difference sk N' i) :=
          fun i ↦ Classical.choice (child_exists i)
        exact ⟨combine hlocal' child⟩)
  exact build (Cardinal.mk N) B N G hG hlocal rfl

end RelativeDavies

/-- The part of a Davies tree used by the geometric recursion.

`layer i` is the countable terminal difference at stage `i`.  Earlier layers
are covered by the finitely many sets in `guards i`.  A Skolem value whose
parameters lie in one guard is forced back into the predecessor cut, while a
Skolem value whose parameters all lie in the current layer cannot jump past
that layer. -/
structure DaviesDecomposition {U : Type u} (sk : SkolemFamily U) where
  Index : Type u
  lt : Index → Index → Prop
  isWellOrder : IsWellOrder Index lt
  layer : Index → Set U
  layer_countable : ∀ i, (layer i).Countable
  layer_disjoint : Pairwise fun i j ↦ Disjoint (layer i) (layer j)
  layer_cover : ⋃ i, layer i = Set.univ
  guards : Index → Finset (Set U)
  guards_cover : ∀ i,
    {x | ∃ j, lt j i ∧ x ∈ layer j} = ⋃ g ∈ guards i, g
  guard_closed : ∀ i g, g ∈ guards i → ∀ n xs,
    (∀ x ∈ xs, x ∈ g) → sk n xs ∈ {x | ∃ j, lt j i ∧ x ∈ layer j}
  layer_closed : ∀ i n xs, (∀ x ∈ xs, x ∈ layer i) →
    sk n xs ∈ {x | ∃ j, lt j i ∧ x ∈ layer j} ∪ layer i

/-- Davies' finite-predecessor decomposition for a countable family of
finitary operations.  No continuum-hypothesis or regularity assumption is
used. -/
theorem exists_daviesDecomposition {U : Type u} (sk : SkolemFamily U) :
    Nonempty (DaviesDecomposition sk) := by
  have hguard : IsGuardBase sk (∅ : Set U) ∅ := by
    constructor
    · simp
    · simp
  have hlocal : LocallyClosed sk (∅ : Set U) Set.univ := by
    intro n xs hxs
    exact Or.inr (Set.mem_univ _)
  obtain ⟨R⟩ := RelativeDavies.exists_relative (∅ : Finset (Set U)) hguard hlocal
  exact ⟨{
    Index := R.Index
    lt := R.lt
    isWellOrder := R.isWellOrder
    layer := R.layer
    layer_countable := R.layer_countable
    layer_disjoint := R.layer_disjoint
    layer_cover := R.layer_cover
    guards := R.guards
    guards_cover := by
      intro i
      simpa using R.guards_cover i
    guard_closed := by
      intro i g hg n xs hxs
      simpa using R.guard_closed i g hg n xs hxs
    layer_closed := by
      intro i n xs hxs
      simpa using R.layer_closed i n xs hxs
    }⟩

/-- Short public name used by the global construction. -/
theorem exists_decomposition {U : Type u} (sk : SkolemFamily U) :
    Nonempty (DaviesDecomposition sk) :=
  exists_daviesDecomposition sk

/-- A chosen Davies decomposition. -/
noncomputable def daviesDecomposition {U : Type u} (sk : SkolemFamily U) :
    DaviesDecomposition sk :=
  Classical.choice (exists_daviesDecomposition sk)

namespace DaviesDecomposition

variable {U : Type u} {sk : SkolemFamily U} (D : DaviesDecomposition sk)

/-- The union of all layers before `i`. -/
def before (i : D.Index) : Set U :=
  {x | ∃ j, D.lt j i ∧ x ∈ D.layer j}

theorem before_eq_guards (i : D.Index) :
    D.before i = ⋃ g ∈ D.guards i, g :=
  D.guards_cover i

theorem mem_before_of_guard {i : D.Index} {g : Set U}
    (hg : g ∈ D.guards i) : g ⊆ D.before i := by
  rw [D.before_eq_guards i]
  intro x hx
  exact mem_iUnion.2 ⟨g, mem_iUnion.2 ⟨hg, hx⟩⟩

/-- Abstract `(D6)`: a named uniquely-defining operation applied inside one
predecessor guard has its value in the predecessor cut. -/
theorem skolem_mem_before {i : D.Index} {g : Set U} (hg : g ∈ D.guards i)
    (n : ℕ) (xs : List U) (hxs : ∀ x ∈ xs, x ∈ g) :
    sk n xs ∈ D.before i :=
  D.guard_closed i g hg n xs hxs

theorem skolem_mem_before_or_layer (i : D.Index) (n : ℕ) (xs : List U)
    (hxs : ∀ x ∈ xs, x ∈ D.layer i) :
    sk n xs ∈ D.before i ∪ D.layer i :=
  D.layer_closed i n xs hxs

theorem exists_guard_of_mem_before {i : D.Index} {x : U} (hx : x ∈ D.before i) :
    ∃ g ∈ D.guards i, x ∈ g := by
  rw [D.before_eq_guards i] at hx
  rcases mem_iUnion.1 hx with ⟨g, hx⟩
  rcases mem_iUnion.1 hx with ⟨hg, hxg⟩
  exact ⟨g, hg, hxg⟩

end DaviesDecomposition

end

end Erdos215
