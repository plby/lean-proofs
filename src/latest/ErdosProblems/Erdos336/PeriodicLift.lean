import Mathlib
import ErdosProblems.Erdos336.Basic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lifting exact finite-cyclic representations to periodic asymptotic bases
-/

namespace Erdos336

/-- The set of naturals whose residue modulo `g` belongs to `E`. -/
def PeriodicLift {g : ℕ} (E : Set (ZMod g)) : Set ℕ :=
  {n | (n : ZMod g) ∈ E}

private lemma cast_sum_map_val {g : ℕ} [NeZero g]
    (ys : List (ZMod g)) :
    (((ys.map ZMod.val).sum : ℕ) : ZMod g) = ys.sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      rw [ZMod.natCast_zmod_val]

private lemma sum_map_val_le {g : ℕ} [NeZero g]
    (ys : List (ZMod g)) :
    (ys.map ZMod.val).sum ≤ ys.length * g := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hy : y.val ≤ g := Nat.le_of_lt (ZMod.val_lt y)
      calc
        y.val + (ys.map ZMod.val).sum ≤ g + ys.length * g :=
          Nat.add_le_add hy ih
        _ = (ys.length + 1) * g := by ring
        _ = (Nat.succ ys.length) * g := by simp [Nat.succ_eq_add_one]

/-- A nonempty exact cyclic representation lifts to an exact representation
of every sufficiently large natural in the corresponding periodic set. -/
theorem natRep_of_groupRep_periodic_of_large
    {g k n : ℕ} (hg : 0 < g) (hk : 0 < k)
    {E : Set (ZMod g)}
    (hn : k * g ≤ n)
    (hrep : GroupRepExactly E k (n : ZMod g)) :
    RepresentsExactly (PeriodicLift E) k n := by
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  obtain ⟨ys, hlen, hymem, hysum⟩ := hrep
  have hysne : ys ≠ [] := by
    intro he
    subst ys
    simp at hlen
    omega
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hysne
  let tailVals : List ℕ := ys.map ZMod.val
  let s : ℕ := y.val + tailVals.sum
  have hs_cast : (s : ZMod g) = (n : ZMod g) := by
    calc
      (s : ZMod g) =
          (((List.map ZMod.val (y :: ys)).sum : ℕ) : ZMod g) := by
            simp [s, tailVals]
      _ = (y :: ys).sum := cast_sum_map_val (g := g) (y :: ys)
      _ = (n : ZMod g) := hysum
  have hs_bound : s ≤ k * g := by
    have hbound := sum_map_val_le (g := g) (y :: ys)
    rw [hlen] at hbound
    exact hbound
  have hsn : s ≤ n := hs_bound.trans hn
  have hsmod : s ≡ n [MOD g] :=
    (ZMod.natCast_eq_natCast_iff s n g).mp hs_cast
  obtain ⟨t, hnt⟩ := (Nat.modEq_iff_exists_eq_add hsn).mp hsmod
  let xs : List ℕ := (y.val + g * t) :: tailVals
  refine ⟨xs, ?_, ?_, ?_⟩
  · dsimp [xs, tailVals]
    simp only [List.length_cons, List.length_map]
    simpa using hlen
  · intro a ha
    simp only [xs, List.mem_cons] at ha
    rcases ha with rfl | ha
    · change ((y.val + g * t : ℕ) : ZMod g) ∈ E
      have hyE : y ∈ E := hymem y (by simp)
      simpa [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self] using hyE
    · change (a : ZMod g) ∈ E
      simp only [tailVals, List.mem_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      simpa using hymem z (by simp [hz])
  · dsimp [xs, s, tailVals] at hnt ⊢
    omega

/-- Uniform exact cyclic coverage lifts to eventual exact coverage of the
periodic set. -/
theorem eventuallyExactly_periodic_of_all_groupRep
    {g k : ℕ} (hg : 0 < g) (hk : 0 < k) {E : Set (ZMod g)}
    (hall : ∀ y : ZMod g, GroupRepExactly E k y) :
    EventuallyExactly (PeriodicLift E) k := by
  refine ⟨k * g, ?_⟩
  intro n hn
  exact natRep_of_groupRep_periodic_of_large hg hk hn (hall (n : ZMod g))

private lemma cast_sum_nat_list {R : Type*} [AddCommMonoidWithOne R]
    (xs : List ℕ) :
    (List.map (fun a : ℕ => (a : R)) xs).sum = (xs.sum : R) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

/-- A uniform positive-diameter bound in the finite cyclic group lifts to
an eventual at-most bound for the periodic set. -/
theorem eventuallyAtMost_periodic_of_groupRepAtMost
    {g h : ℕ} (hg : 0 < g) {E : Set (ZMod g)}
    (hall : ∀ y : ZMod g, ∃ k : ℕ,
      0 < k ∧ k ≤ h ∧ GroupRepExactly E k y) :
    EventuallyAtMost (PeriodicLift E) h := by
  refine ⟨h * g, ?_⟩
  intro n hn
  obtain ⟨k, hkpos, hkh, hkrep⟩ := hall (n : ZMod g)
  refine ⟨k, hkh, ?_⟩
  apply natRep_of_groupRep_periodic_of_large hg hkpos
  · exact (Nat.mul_le_mul_right g hkh).trans hn
  · exact hkrep

/-- Projecting a natural representation of a periodic lift gives a
representation of its residue in the finite cyclic group. -/
theorem groupRep_of_natRep_periodic
    {g k n : ℕ} {E : Set (ZMod g)}
    (hrep : RepresentsExactly (PeriodicLift E) k n) :
    GroupRepExactly E k (n : ZMod g) := by
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hrep
  refine ⟨List.map (fun a : ℕ => (a : ZMod g)) xs, by simp [hlen], ?_, ?_⟩
  · intro y hy
    obtain ⟨a : ℕ, ha, hay⟩ := List.mem_map.mp hy
    subst y
    exact hxmem a ha
  · rw [← hxsum]
    exact cast_sum_nat_list xs

/-- A residue missing from an exact cyclic power prevents eventual exact
coverage by the corresponding periodic set. -/
theorem not_eventuallyExactly_periodic_of_missing
    {g k : ℕ} (hg : 0 < g) {E : Set (ZMod g)}
    (hmiss : ∃ y : ZMod g, ¬ GroupRepExactly E k y) :
    ¬ EventuallyExactly (PeriodicLift E) k := by
  rintro ⟨N, hN⟩
  obtain ⟨y, hy⟩ := hmiss
  letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  let t : ℕ := N + 1
  let n : ℕ := y.val + t * g
  have hNn : N ≤ n := by
    dsimp [n, t]
    nlinarith
  have hncast : (n : ZMod g) = y := by
    dsimp [n]
    simp [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
      ZMod.natCast_zmod_val]
  apply hy
  rw [← hncast]
  exact groupRep_of_natRep_periodic (hN n hNn)

end Erdos336
