import Mathlib

namespace Erdos707

/-- A Sidon set `A` is a set where all pairwise sums `i + j` are unique,
up to swapping the addends. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ ⦃i₁ i₂ j₁ j₂ : α⦄, i₁ ∈ A → i₂ ∈ A → j₁ ∈ A → j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- `B` is a perfect difference set modulo `v` if there is a bijection between
non-zero residues mod `v` and distinct differences `a - b`, where `a, b ∈ B`. -/
def IsPerfectDifferenceSetModulo (B : Set ℤ) (v : ℕ) : Prop :=
  B.offDiag.BijOn (fun (a, b) => (a - b : ZMod v)) {x : ZMod v | x ≠ 0}

/-
END DEFINITIONS

We begin by proving some "consistency check" results on our definitions,
to make sure they have not gone wrong.

After these results, the definition of Sidon set isn't actually used
until the very end of the file, when giving concrete counterexamples.
-/
/-- Differences are injective on `A.offDiag`. -/
def IsSidonSubtractive' {α : Type*} [AddGroup α] (A : Set α) : Prop :=
  (A.offDiag).InjOn (fun (p : α × α) => p.1 - p.2)

/-- An (additive) Sidon set implies "subtractive Sidon":
equality of differences on `A.offDiag` forces equality of ordered pairs. -/
lemma IsSidon.isSidonSubtractive'
    {α : Type*} [AddCommGroup α] {A : Set α}
    (hA : IsSidon (A := A)) :
    IsSidonSubtractive' A := by
  -- Unfold the goal: injectivity on `A.offDiag` for the difference map.
  intro p hp q hq hdiff
  rcases p with ⟨a₁, a₂⟩
  rcases q with ⟨b₁, b₂⟩
  -- Decode membership in `offDiag`.
  have hpa : a₁ ∈ A ∧ a₂ ∈ A ∧ a₁ ≠ a₂ := by
    simpa [Set.offDiag, Set.mem_setOf] using hp
  have hqb : b₁ ∈ A ∧ b₂ ∈ A ∧ b₁ ≠ b₂ := by
    simpa [Set.offDiag, Set.mem_setOf] using hq
  -- From `a₁ - a₂ = b₁ - b₂`, derive `a₁ + b₂ = b₁ + a₂`.
  have hsum : a₁ + b₂ = b₁ + a₂ := by
    have := congrArg (fun t => t + a₂ + b₂) hdiff
    -- simplify both sides
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Apply the Sidon property to the pairs `(a₁,b₂)` and `(b₁,a₂)`.
  have h := hA (i₁ := a₁) (i₂ := b₂) (j₁ := b₁) (j₂ := a₂)
                hpa.1 hqb.2.1 hqb.1 hpa.2.1 hsum
  -- Only the non-swapped case can occur; the swapped case contradicts `offDiag`.
  cases h with
  | inl hpair =>
      -- `a₁ = b₁` and `b₂ = a₂` ⇒ pairs are equal.
      apply Prod.ext
      · exact hpair.left
      · simpa using hpair.right.symm
  | inr hswap =>
      -- Swapped would force `a₁ = a₂`, contradicting `a₁ ≠ a₂`.
      exact (hpa.2.2 hswap.left).elim

/-- "Subtractive Sidon" implies (additive) Sidon.
If differences are injective on `A.offDiag`, then equal sums force equality
of addend pairs up to swapping. -/
lemma IsSidonSubtractive'.isSidon
    {α : Type*} [AddCommGroup α] {A : Set α}
    (hA : IsSidonSubtractive' (A := A)) :
    IsSidon (A := A) := by
  intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ hsum
  by_cases h₁ : i₁ = j₁
  · have : i₁ + i₂ = i₁ + j₂ := by simpa [h₁] using hsum
    have hj : i₂ = j₂ := by simpa using add_left_cancel this
    exact Or.inl ⟨h₁, hj⟩
  by_cases h₂ : i₂ = j₂
  · have : i₁ + i₂ = j₁ + i₂ := by simpa [h₂] using hsum
    have hi : i₁ = j₁ := by simpa using add_right_cancel this
    exact Or.inl ⟨hi, h₂⟩
  -- now `h₁ : i₁ ≠ j₁` and `h₂ : i₂ ≠ j₂`
  have hdiff : i₁ - j₁ = j₂ - i₂ := by
    have t := congrArg (fun t => t + (-j₁) + (-i₂)) hsum
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using t
  -- offDiag memberships
  have hi_off : (i₁, j₁) ∈ A.offDiag := by
    -- ⟨i₁∈A, j₁∈A, i₁ ≠ j₁⟩
    simpa [Set.offDiag, Set.mem_setOf] using And.intro hi₁ (And.intro hj₁ h₁)
  have h₂' : j₂ ≠ i₂ := fun h => h₂ h.symm
  have hj_off : (j₂, i₂) ∈ A.offDiag := by
    -- ⟨j₂∈A, i₂∈A, j₂ ≠ i₂⟩
    simpa [Set.offDiag, Set.mem_setOf] using And.intro hj₂ (And.intro hi₂ h₂')
  -- Injectivity of differences on offDiag
  have := hA hi_off hj_off hdiff
  rcases Prod.ext_iff.mp this with ⟨hij, hji⟩
  exact Or.inr ⟨hij, hji.symm⟩

/-- A perfect difference set modulo `v` is (integer) subtractive Sidon. -/
lemma IsPerfectDifferenceSetModulo.isSidonSubtractive_int
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (h : IsPerfectDifferenceSetModulo B v) :
    IsSidonSubtractive' (A := B) := by
  -- We need: injective (on `B.offDiag`) for `(a,b) ↦ (a - b : ℤ)`.
  -- From the `BijOn`, we have injectivity for `(a,b) ↦ (a - b : ZMod v)`.
  intro p hp q hq hdiff
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have hinj : (B.offDiag).InjOn (fun (p : ℤ × ℤ) => (p.1 - p.2 : ZMod v)) :=
    h.injOn
  -- Cast the integer equality of differences into `ZMod v`.
  have hmod : ((a - b : ℤ) : ZMod v) = ((c - d : ℤ) : ZMod v) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod v)) hdiff
  -- Apply injectivity on `B.offDiag` for the `ZMod v`-valued difference map.
  have : (fun p : ℤ × ℤ => (p.1 - p.2 : ZMod v)) (a, b)
        = (fun p : ℤ × ℤ => (p.1 - p.2 : ZMod v)) (c, d) := by
    simpa using hmod
  exact hinj hp hq this

/-- **Perfect difference set ⇒ additive Sidon (over `ℤ`)**. -/
lemma IsPerfectDifferenceSetModulo.isSidon_int
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (h : IsPerfectDifferenceSetModulo B v) :
    IsSidon (A := B) := by
  -- Chain PDS ⇒ subtractive Sidon ⇒ additive Sidon.
  exact
    (IsSidonSubtractive'.isSidon (A := B)
      (IsPerfectDifferenceSetModulo.isSidonSubtractive_int (B := B) (v := v) h))

/-
From here until the main theorems, we just prove a lot of stuff about
perfect difference sets, basically building up a lot of structure as
cyclic projective planes.
-/

lemma card_zmod (v : ℕ) [NeZero v] :
    Fintype.card (ZMod v) = v := by
  simp

/-- If a finite set `S` has cardinality `v` and contains `0`,
then removing `0` drops the cardinality by one. -/
lemma ncard_diff_singleton_zero
  {α : Type*} [Zero α]
  {S : Set α} {v : ℕ}
  (hfin : S.Finite) (hcard : S.ncard = v) (h0 : (0 : α) ∈ S) :
  (S \ {0}).ncard = v - 1 := by
  -- From mathlib: (S \ {0}).ncard + 1 = S.ncard
  have hplus :
      (S \ {0}).ncard + 1 = S.ncard := by
    simpa using
      (Set.ncard_diff_singleton_add_one (s := S) (a := (0 : α)) (hs := hfin) h0)
  -- Subtract 1 on both sides
  have : (S \ {0}).ncard = S.ncard - 1 := by
    simpa [Nat.add_sub_cancel] using congrArg (fun n => n - 1) hplus
  -- Replace `S.ncard` with `v`
  simpa [hcard] using this

/-- Same statement, written with a set-builder predicate `{x ∈ S | x ≠ 0}`. -/
lemma ncard_subset_ne_zero
  {α : Type*} [Zero α] [DecidableEq α]
  {S : Set α} {v : ℕ}
  (hfin : S.Finite) (hcard : S.ncard = v) (h0 : (0 : α) ∈ S) :
  ({x : α | x ∈ S ∧ x ≠ 0}).ncard = v - 1 := by
  classical
  -- Identify `{x ∈ S | x ≠ 0}` with `S \ {0}`
  have hEq : ({x : α | x ∈ S ∧ x ≠ 0} : Set α) = (S \ {0}) := by
    ext x; constructor <;> intro hx
    · rcases hx with ⟨hxS, hx0⟩
      exact ⟨hxS, by simpa [Set.mem_singleton_iff]⟩
    · rcases hx with ⟨hxS, hxnot⟩
      exact ⟨hxS, by simpa [Set.mem_singleton_iff] using hxnot⟩
  -- Now apply the “remove 0 drops cardinality by 1” lemma
  have h := ncard_diff_singleton_zero (α := α) (S := S) (v := v) hfin hcard h0
  simpa [hEq] using h

/-- Over `ZMod v` with `v ≠ 0`, the set of nonzero residues has cardinality `v - 1`. -/
lemma ncard_nonzero_zmod (v : ℕ) [NeZero v] :
    ({x : ZMod v | x ≠ 0} : Set (ZMod v)).ncard = v - 1 := by
  classical
  -- Use the general “remove 0 drops cardinality by 1” lemma on `S = univ`.
  have hfin  : (Set.univ : Set (ZMod v)).Finite := Set.finite_univ
  have hcard : (Set.univ : Set (ZMod v)).ncard = v := by
    -- `(univ).ncard = Fintype.card`, and `Fintype.card (ZMod v) = v` for `v ≠ 0`.
    simp
  have h0 : (0 : ZMod v) ∈ (Set.univ : Set (ZMod v)) := by simp
  -- Apply the set-builder version with `S = univ`, then simplify `{x ∈ univ | x ≠ 0}`.
  simpa [Set.mem_univ, true_and] using
    (ncard_subset_ne_zero (α := ZMod v) (S := (Set.univ : Set (ZMod v))) (v := v) hfin hcard h0)

/-- If `B` is infinite, then `B.offDiag` is infinite. -/
lemma infinite_offDiag_of_infinite
  {α : Type*} [DecidableEq α] {B : Set α} (hB : B.Infinite) :
  (B.offDiag).Infinite := by
  classical
  -- pick a point b₀ ∈ B
  obtain ⟨b0, hb0⟩ := hB.nonempty
  -- removing a finite set `{b0}` from an infinite set keeps it infinite
  have hInfDiff : (B \ {b0}).Infinite :=
    hB.diff (Set.finite_singleton b0)

  -- injective map sending x ↦ (x, b0)
  let f : α → α × α := fun x => (x, b0)
  have hf : Set.InjOn f (B \ {b0}) := by
    intro x hx y hy hxy
    -- equality of ordered pairs gives equality of first components
    exact congrArg Prod.fst hxy

  -- the image of an infinite set under an injective map is infinite
  have himg : (f '' (B \ {b0})).Infinite := hInfDiff.image hf

  -- this image sits inside B.offDiag
  have hsub : f '' (B \ {b0}) ⊆ B.offDiag := by
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    rcases hx with ⟨hxB, hxne⟩
    have hb0B : b0 ∈ B := hb0
    have hx_ne_b0 : x ≠ b0 := by
      -- from x ∉ {b0}
      simpa [Set.mem_singleton_iff] using hxne
    -- unpack offDiag definition: p.1 ∈ B ∧ p.2 ∈ B ∧ p.1 ≠ p.2
    exact ⟨hxB, hb0B, by simpa using hx_ne_b0⟩

  -- a superset of an infinite set is infinite
  exact himg.mono hsub

/-- If `v ≠ 0`, then the set of nonzero residues in `ZMod v` is finite. -/
lemma finite_nonzero_zmod (v : ℕ) [NeZero v] :
  ({x : ZMod v | x ≠ 0} : Set (ZMod v)).Finite := by
  classical
  -- `ZMod v` is a finite type under `[NeZero v]`, so `univ` is finite
  have hUniv : (Set.univ : Set (ZMod v)).Finite := Set.finite_univ
  -- Any subset of a finite set is finite
  exact hUniv.subset (by intro x hx; trivial)

/-- If `B` is infinite and `S` is finite, there cannot be a bijection (in the `BijOn` sense)
from `B.offDiag` to `S`. -/
lemma no_bijOn_offDiag_to_finite_of_infinite
  {α β : Type*} {B : Set α} {S : Set β}
  (hB : B.Infinite) (hS : S.Finite) (f : α × α → β) :
  ¬ (B.offDiag).BijOn f S := by
  classical
  intro hBij
  -- `B.offDiag` is infinite.
  have hOffInf : (B.offDiag).Infinite :=
    infinite_offDiag_of_infinite (B := B) hB
  -- Injective image of an infinite set is infinite.
  have hImgInf : (f '' B.offDiag).Infinite :=
    hOffInf.image hBij.injOn
  -- But the image equals `S`, which is finite.
  have hImgFin : (f '' B.offDiag).Finite := by
    simpa [hBij.image_eq] using hS
  -- Finish via option (C): `Infinite` is (defeq) `¬ Finite` in many mathlib versions.
  change ¬ (f '' B.offDiag).Finite at hImgInf
  exact hImgInf hImgFin

/-- If `B` is a perfect difference set modulo `v` and `v ≠ 0`, then `B` is finite. -/
lemma IsPerfectDifferenceSetModulo.finite
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v) :
  B.Finite := by
  classical
  -- Either `B` is finite (done) or infinite (derive a contradiction).
  rcases Set.finite_or_infinite (s := B) with hfin | hinf
  · exact hfin
  -- If `B` were infinite, there cannot be a `BijOn` from `B.offDiag` to a finite set.
  · have hNo :
        ¬ (B.offDiag).BijOn
            (fun ab : ℤ × ℤ => (ab.1 : ZMod v) - (ab.2 : ZMod v))
            ({x : ZMod v | x ≠ 0} : Set (ZMod v)) :=
      no_bijOn_offDiag_to_finite_of_infinite
        (B := B) (S := ({x : ZMod v | x ≠ 0} : Set (ZMod v)))
        hinf (finite_nonzero_zmod v)
        (fun ab => (ab.1 : ZMod v) - (ab.2 : ZMod v))
    -- But `h` is exactly such a bijection, contradiction.
    exact (hNo h).elim

/-- Seemingly an extremely useful lemma? -/
lemma ncard_toFinset
  {α : Type*} [DecidableEq α] {S : Set α}
  (hS : S.Finite) :
  S.ncard = hS.toFinset.card := by
  classical
  simpa using (Set.ncard_eq_toFinset_card (s := S) (hs := hS))

/-- If a finset `T` has cardinality `x`, then `T.offDiag` has cardinality `x*x - x`
(= `x * (x - 1)`). -/
lemma card_offDiag_of_card
  {α : Type*} [DecidableEq α] {T : Finset α} {x : ℕ}
  (hx : T.card = x) :
  T.offDiag.card = x * x - x := by
  classical
  calc
    T.offDiag.card = T.card * T.card - T.card := Finset.offDiag_card (s := T)
    _                = x * x - x               := by simp [hx]

/-- As sets, `(↑T : Set α).offDiag = ↑(T.offDiag)`. -/
lemma coe_offDiag_finset
  {α : Type*} [DecidableEq α] (T : Finset α) :
  ((↑T : Set α).offDiag : Set (α × α)) = (↑(T.offDiag) : Set (α × α)) := by
  classical
  ext p
  rcases p with ⟨a, b⟩
  -- LHS: `(a,b) ∈ (↑T).offDiag` ↔ `a ∈ T ∧ b ∈ T ∧ a ≠ b`
  -- RHS: `(a,b) ∈ ↑(T.offDiag)` ↔ `(a,b) ∈ (T.product T).filter (fun p => p.fst ≠ p.snd)`
  --     ↔ `a ∈ T ∧ b ∈ T ∧ a ≠ b`
  simp [Set.offDiag, Finset.offDiag, Finset.mem_coe,
        Finset.mem_product, and_left_comm, and_comm]

/-- If `B` is finite with cardinality `x`, then `B.offDiag` has cardinality `x*x - x`
(= `x * (x - 1)`). -/
lemma ncard_offDiag_of_card
  {α : Type*} [DecidableEq α]
  {B : Set α} {x : ℕ}
  (hfin : B.Finite) (hcard : B.ncard = x) :
  (B.offDiag).ncard = x * x - x := by
  classical
  -- Turn `B` into a finset
  let T : Finset α := hfin.toFinset

  -- `B.ncard = T.card`, hence `T.card = x`
  have hBn : B.ncard = T.card := by
    simpa [Set.ncard_eq_toFinset_card, T]
      using (Set.ncard_eq_toFinset_card (s := B) (hs := hfin))
  have hT : T.card = x := by simpa [hBn] using hcard

  -- Replace `B` by `↑T` and then use the finset lemma
  have hBcoe : (↑T : Set α) = B := by
    ext a; simp [T]

  -- As sets, `(↑T).offDiag = ↑(T.offDiag)`
  have hOffEq :
      (B.offDiag : Set (α × α)) = (↑(T.offDiag) : Set (α × α)) := by
    simp [hBcoe]

  calc
    (B.offDiag).ncard
        = ((↑(T.offDiag) : Set (α × α))).ncard := by
            simp [hOffEq]
    _   = T.offDiag.card := by
            -- `ncard` of a coerced finset equals its `card`
            simpa using (Set.ncard_coe_finset (s := T.offDiag))
    _   = x * x - x := by
            -- your finset lemma
            simp [hT]

/-- If `B` is finite with cardinality `q + 1`, then `B.offDiag` has cardinality `q*q + q`. -/
lemma ncard_offDiag_of_card_succ
  {α : Type*} [DecidableEq α]
  {B : Set α} {q : ℕ}
  (hfin : B.Finite) (hcard : B.ncard = q + 1) :
  (B.offDiag).ncard = q*q + q := by
  classical
  -- Start from the general `x*x - x` lemma with `x = q + 1`
  have h := ncard_offDiag_of_card (α := α) (B := B) (x := q + 1) hfin hcard
  -- Now simplify `(q+1)*(q+1) - (q+1)` to `q*q + q`
  calc
    (B.offDiag).ncard
        = (q + 1) * (q + 1) - (q + 1) := by simpa using h
    _   = ((q + 1) * q + (q + 1) * 1) - (q + 1) := by
            simp [Nat.mul_add]
    _   = (((q*q) + (1*q)) + (q + 1)) - (q + 1) := by
            simp [Nat.add_mul]
    _   = q*q + q := by
            -- turn `1*q` into `q`, reassociate, then cancel `+(q+1)` with `-(q+1)`
            simpa [Nat.one_mul, Nat.add_assoc] using
              (Nat.add_sub_cancel (q*q + q) (q + 1))

/-- If `B` is a perfect difference set modulo `v`, `v ≠ 0`, and `B.ncard = q + 1`,
then `q*q + q + 1 = v`. -/
lemma IsPerfectDifferenceSetModulo.card_param_eq_succ
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) :
  q*q + q + 1 = v := by
  classical
  -- Target set of the bijection
  set S : Set (ZMod v) := {x : ZMod v | x ≠ 0}

  -- Left side via your `(q+1)` lemma
  have hLHS : (B.offDiag).ncard = q*q + q :=
    ncard_offDiag_of_card_succ (α := ℤ) (B := B) (q := q) hfin hcard

  -- Finiteness witnesses and finsets
  have hOffFin : (B.offDiag).Finite :=
    (hfin.prod hfin).subset (by intro p hp; exact ⟨hp.1, hp.2.1⟩)
  let s : Finset (ℤ × ℤ) := hOffFin.toFinset
  let t : Finset (ZMod v) := (finite_nonzero_zmod v).toFinset

  have hs : (↑s : Set (ℤ × ℤ)) = B.offDiag := by
    ext p; simp [s]
  have ht : (↑t : Set (ZMod v)) = S := by
    ext x; simp [t, S]

  -- Transport the bijection to finset-underlying sets; deduce equal cards
  have hBij' :
      (↑s : Set (ℤ × ℤ)).BijOn (fun (a,b) => (a - b : ZMod v)) (↑t : Set (ZMod v)) := by
    simpa [hs, ht, IsPerfectDifferenceSetModulo, S] using h
  have hCards : s.card = t.card := hBij'.finsetCard_eq

  -- Convert `card` ↔ `ncard`
  have hnDom : (B.offDiag).ncard = s.card := by
    simpa [hs] using (Set.ncard_coe_finset (s := s))
  have hnCod : S.ncard = t.card := by
    simpa [ht] using (Set.ncard_coe_finset (s := t))

  -- Thus `(B.offDiag).ncard = S.ncard`
  have hEqNC : (B.offDiag).ncard = S.ncard := by
    simpa [hnDom, hnCod] using hCards

  -- Right side via your `ZMod` lemma
  have hRHS : S.ncard = v - 1 := by
    simpa [S] using (ncard_nonzero_zmod v)

  -- First get `q*q + q = v - 1`
  have hEq : q*q + q = v - 1 := by
    calc
      q*q + q = (B.offDiag).ncard := by simp [hLHS]
      _       = S.ncard            := hEqNC
      _       = v - 1              := hRHS

  -- Then add 1 to both sides
  have hv0 : v ≠ 0 := (inferInstance : NeZero v).out
  have hv  : 1 ≤ v := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0)
  calc
    q*q + q + 1 = (v - 1) + 1 := by simp [hEq]
    _           = v           := Nat.sub_add_cancel hv

/-- From `q*q + q + 1 = v`, deduce `v % 2 = 1` by a case split on `q % 2`. -/
lemma IsPerfectDifferenceSetModulo.mod_two_eq_one
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) :
  v % 2 = 1 := by
  classical
  -- From the previous lemma we have the exact value of `v`.
  have hv : q*q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ
      (B := B) (v := v) (q := q) h hfin hcard

  -- Split on `q % 2`.
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · -- Case `q % 2 = 0`
    have hq2 : (q*q) % 2 = 0 := by
      -- (q*q) % 2 = ((q%2)*(q%2)) % 2 = (0*0) % 2 = 0
      simpa [hq] using (Nat.mul_mod q q 2)
    have hsum0 : (q*q + q) % 2 = 0 := by
      calc
        (q*q + q) % 2
            = ((q*q) % 2 + q % 2) % 2 := by
                simp [Nat.add_mod]
        _   = (0 + 0) % 2 := by simp [hq2, hq]
        _   = 0 := by simp
    calc
      v % 2 = (q*q + q + 1) % 2 := by simp [hv]
      _     = ((q*q + q) % 2 + (1 % 2)) % 2 := by
                simp [Nat.add_mod]
      _     = (0 + 1) % 2 := by simp [hsum0]
      _     = 1 := by simp
  · -- Case `q % 2 = 1`
    have hq2 : (q*q) % 2 = 1 := by
      -- (q*q) % 2 = ((q%2)*(q%2)) % 2 = (1*1) % 2 = 1
      simpa [hq] using (Nat.mul_mod q q 2)
    have hsum0 : (q*q + q) % 2 = 0 := by
      calc
        (q*q + q) % 2
            = ((q*q) % 2 + q % 2) % 2 := by
                simp [Nat.add_mod]
        _   = (1 + 1) % 2 := by simp [hq2, hq]
        _   = 0 := by simp
    calc
      v % 2 = (q*q + q + 1) % 2 := by simp [hv]
      _     = ((q*q + q) % 2 + (1 % 2)) % 2 := by
                simp [Nat.add_mod]
      _     = (0 + 1) % 2 := by simp [hsum0]
      _     = 1 := by simp

/- Start building up projective plane stuff. -/

/-- The translate of `B` by `x : ZMod v`, viewed as a subset of points `ZMod v`. -/
def pdsLine (B : Set ℤ) (v : ℕ) (x : ZMod v) : Set (ZMod v) :=
  {y | ∃ b ∈ B, y = ((b : ZMod v) + x)}

/-- Incidence: a point `p : ZMod v` is on the line indexed by `ℓ : ZMod v`
iff `p ∈ pdsLine B v ℓ`. -/
def pdsMembership (B : Set ℤ) (v : ℕ) : Membership (ZMod v) (ZMod v) :=
  ⟨fun p ℓ => p ∈ pdsLine B v ℓ⟩

/-- Incidence: a point `p : ZMod v` is on the line indexed by `ℓ : ZMod v`
iff `p ∈ pdsLine B v ℓ`.  Except the order of the arguments is flipped.
I do not understand why this is helpful yet alone seemingly necessary. -/
def pdsMembershipFlipped (B : Set ℤ) (v : ℕ) : Membership (ZMod v) (ZMod v) :=
  ⟨fun ℓ p => p ∈ pdsLine B v ℓ⟩

/-- Membership in a translate as a “difference” test:
`s ∈ (B + t)` iff `s - t` is the residue of some `b ∈ B`. -/
lemma mem_pdsLine_iff_sub_coe_mem
    (B : Set ℤ) (v : ℕ) (s t : ZMod v) :
    s ∈ pdsLine B v t ↔ ∃ b ∈ B, (s - t : ZMod v) = (b : ZMod v) := by
  classical
  constructor
  · intro h
    rcases h with ⟨b, hbB, hs⟩
    refine ⟨b, hbB, ?_⟩
    -- from `s = b + t` deduce `s - t = b`
    simp [hs, sub_eq_add_neg, add_comm, add_assoc]
  · intro h
    rcases h with ⟨b, hbB, hst⟩
    -- from `s - t = b` deduce `s = b + t`
    have := congrArg (fun z => z + t) hst
    -- close the goal `s = (b : ZMod v) + t`
    refine ⟨b, hbB, ?_⟩
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

/-- Same statement phrased as membership in the image of `B` under the coercion `ℕ → ZMod v`. -/
lemma mem_pdsLine_iff_sub_mem_image
    (B : Set ℤ) (v : ℕ) (s t : ZMod v) :
    s ∈ pdsLine B v t ↔
      (s - t : ZMod v) ∈ (Set.image (fun b : ℤ => (b : ZMod v)) B) := by
  classical
  constructor
  · intro h
    rcases (mem_pdsLine_iff_sub_coe_mem B v s t).1 h with ⟨b, hb, hst⟩
    -- `Set.mem_image`: x ∈ f '' B ↔ ∃ b ∈ B, f b = x
    exact ⟨b, hb, hst.symm⟩
  · intro h
    rcases h with ⟨b, hb, hst⟩
    -- convert `↑b = s - t` to `s - t = ↑b`
    exact (mem_pdsLine_iff_sub_coe_mem B v s t).2 ⟨b, hb, hst.symm⟩

/-- If `B` is a perfect difference set modulo `v` and `v ≥ 3`, then
for every translate `x : ZMod v` there exists a point not on the line `pdsLine B v x`.

*Proof idea:* if `0,1,2` were all on the line `x`, then
`(1-x) - (0-x) = (2-x) - (1-x) = 1`, giving two distinct pairs from `B.offDiag`
mapping to the same nonzero residue `1` under the PDS bijection. -/
lemma exists_point_not_on_pdsLine
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v) (hv : 3 ≤ v) :
  ∀ x : ZMod v, ∃ y : ZMod v, y ∉ pdsLine B v x := by
  classical
  -- nontriviality of `ZMod v` (needed to use `zero_ne_one`)
  haveI : Fact (1 < v) := ⟨lt_of_lt_of_le (by decide : 1 < 3) hv⟩
  intro x
  -- assume all points are on the line (contradiction)
  by_contra hAll
  have hAll' : ∀ y : ZMod v, y ∈ pdsLine B v x := by
    intro y
    -- from `¬ ∃ y, y ∉ L` get `∀ y, ¬ (y ∉ L)`, then remove double negation
    exact not_not.mp ((not_exists.mp hAll) y)

  have hx0 : (0 : ZMod v) ∈ pdsLine B v x := hAll' 0
  have hx1 : (1 : ZMod v) ∈ pdsLine B v x := hAll' 1
  have hx2 : (2 : ZMod v) ∈ pdsLine B v x := hAll' 2

  -- pick preimages in `B` for `0-x`, `1-x`, `2-x`
  rcases (mem_pdsLine_iff_sub_coe_mem B v (0 : ZMod v) x).1 hx0 with ⟨b0, hb0B, h0⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v (1 : ZMod v) x).1 hx1 with ⟨b1, hb1B, h1⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v (2 : ZMod v) x).1 hx2 with ⟨b2, hb2B, h2⟩

  -- (1 - x) - (0 - x) = 1
  have diff10 : ((b1 : ZMod v) - (b0 : ZMod v)) = 1 := by
    -- First cancel `x` on both sides to get `(1 - 0)`
    have hsub :
        ((1 : ZMod v) - x) - ((0 : ZMod v) - x)
          = (1 : ZMod v) - 0 := by
      simp [sub_eq_add_neg, add_comm]
    -- Then `(1 - 0) = 1`
    have : ((1 : ZMod v) - x) - ((0 : ZMod v) - x) = 1 := by
      simp
    -- Substitute the witnesses `h1, h0`
    simpa [h1, h0] using this

  -- (2 - x) - (1 - x) = 1
  have diff21 : ((b2 : ZMod v) - (b1 : ZMod v)) = 1 := by
    -- First cancel `x` on both sides to get `(2 - 1)`
    have hsub :
        ((2 : ZMod v) - x) - ((1 : ZMod v) - x)
          = (2 : ZMod v) - 1 := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    -- Then `(2 - 1) = 1`
    have : ((2 : ZMod v) - x) - ((1 : ZMod v) - x) = 1 := by
      -- turn the RHS `(2 - 1)` into `1`
      simpa using hsub.trans (by
        -- `norm_num` proves `((2 : ZMod v) - (1 : ZMod v)) = 1`
        norm_num)
    -- Substitute the witnesses `h2, h1`
    simpa [h2, h1] using this

  -- show the two ordered pairs are in `B.offDiag`
  have hb10ne : b1 ≠ b0 := by
    intro hEq
    -- then `((b1:ZMod v) - (b0:ZMod v)) = 0`, contradicting `= 1`
    have : ((b1 : ZMod v) - (b0 : ZMod v)) = 0 := by simp [hEq]
    have : (1 : ZMod v) = 0 := by simpa [this] using diff10.symm
    exact (one_ne_zero : (1 : ZMod v) ≠ 0) this
  have hb21ne : b2 ≠ b1 := by
    intro hEq
    have : ((b2 : ZMod v) - (b1 : ZMod v)) = 0 := by simp [hEq]
    have : (1 : ZMod v) = 0 := by simpa [this] using diff21.symm
    exact (one_ne_zero : (1 : ZMod v) ≠ 0) this

  have hp10 : (b1, b0) ∈ B.offDiag := by exact ⟨hb1B, hb0B, hb10ne⟩
  have hp21 : (b2, b1) ∈ B.offDiag := by exact ⟨hb2B, hb1B, hb21ne⟩

  -- injectivity on `B.offDiag` (from the PDS bijection)
  rcases h with ⟨hMaps, hInj, hSurj⟩
  have : (b1, b0) = (b2, b1) := by
    -- both pairs map to `1`, so injectivity forces equality
    apply hInj hp10 hp21
    simp [diff10, diff21]
  -- but then `b0 = b1`, contradicting `hb10ne`
  exact hb10ne (by cases this; rfl)

/-- If `B` is a perfect difference set modulo `v` and `v ≥ 3`, then
for every point `p : ZMod v` there exists a line (some translate `ℓ : ZMod v`)
that does **not** contain `p`.

*Proof idea:* Consider the three lines indexed by `0,1,2`. If a point `p`
lay on all three, then `(p-0), (p-1), (p-2)` are residues of elements of `B`,
and
`(p-0) - (p-1) = 1 = (p-1) - (p-2)`, giving two distinct pairs of `B.offDiag`
that map to the same nonzero residue `1`, contradicting injectivity of the PDS bijection. -/
lemma exists_line_not_through_point
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v) (hv : 3 ≤ v) :
  ∀ p : ZMod v, ∃ ℓ : ZMod v, p ∉ pdsLine B v ℓ := by
  classical
  -- ensure `1 ≠ 0` in `ZMod v`
  haveI : Fact (1 < v) := ⟨lt_of_lt_of_le (by decide : 1 < 3) hv⟩
  intro p
  -- Suppose, towards a contradiction, that `p` lies on every line.
  by_contra hAll
  have hAll' : ∀ ℓ : ZMod v, p ∈ pdsLine B v ℓ := by
    intro ℓ
    exact not_not.mp ((not_exists.mp hAll) ℓ)

  -- Membership on the three lines 0,1,2
  have hp0 : p ∈ pdsLine B v (0 : ZMod v) := hAll' 0
  have hp1 : p ∈ pdsLine B v (1 : ZMod v) := hAll' 1
  have hp2 : p ∈ pdsLine B v (2 : ZMod v) := hAll' 2

  -- Choose preimages in `B`:
  rcases (mem_pdsLine_iff_sub_coe_mem B v p 0).1 hp0 with ⟨b0, hb0B, h0⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v p 1).1 hp1 with ⟨b1, hb1B, h1⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v p 2).1 hp2 with ⟨b2, hb2B, h2⟩

  -- Differences are both `1`:
  have diff01 : ((b0 : ZMod v) - (b1 : ZMod v)) = 1 := by
    have : ((p : ZMod v) - 0) - (p - 1) = (1 : ZMod v) := by
      simp [sub_eq_add_neg, add_comm]
    simpa [h0, h1] using this
  -- (p - 1) - (p - 2) = 1
  have diff12 : ((b1 : ZMod v) - (b2 : ZMod v)) = 1 := by
    -- cancel `p` on both sides to get `(-1) + 2`
    have hsub :
        (p - 1) - (p - 2) = ((-1 : ZMod v) + 2) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    -- then `(-1) + 2 = 1`
    have : (p - 1) - (p - 2) = 1 := by
      simpa using hsub.trans (by norm_num)
    -- Substitute the witnesses `h1, h2`
    simpa [h1, h2] using this

  -- Show these pairs are in `B.offDiag`
  have hb01ne : b0 ≠ b1 := by
    intro hEq; have : ((b0 : ZMod v) - (b1 : ZMod v)) = 0 := by simp [hEq]
    have : (1 : ZMod v) = 0 := by simpa [this] using diff01.symm
    exact (one_ne_zero : (1 : ZMod v) ≠ 0) this
  have hb12ne : b1 ≠ b2 := by
    intro hEq; have : ((b1 : ZMod v) - (b2 : ZMod v)) = 0 := by simp [hEq]
    have : (1 : ZMod v) = 0 := by simpa [this] using diff12.symm
    exact (one_ne_zero : (1 : ZMod v) ≠ 0) this

  have hp01 : (b0, b1) ∈ B.offDiag := ⟨hb0B, hb1B, hb01ne⟩
  have hp12 : (b1, b2) ∈ B.offDiag := ⟨hb1B, hb2B, hb12ne⟩

  -- Injectivity of the PDS map on `B.offDiag` gives a contradiction
  rcases h with ⟨_maps, inj, _surj⟩
  have : (b0, b1) = (b1, b2) := by
    apply inj hp01 hp12
    -- both images are `1`
    simp [diff01, diff12]
  -- then `b0 = b1`, contradicting `hb01ne`
  exact hb01ne (by cases this; rfl)

/-- (PDS analog of “if two points lie on two lines, then either the points coincide
or the lines coincide”.) -/
lemma pds_points_lines_collapse
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  {p₁ p₂ l₁ l₂ : ZMod v}
  (hp1l1 : p₁ ∈ pdsLine B v l₁)
  (hp2l1 : p₂ ∈ pdsLine B v l₁)
  (hp1l2 : p₁ ∈ pdsLine B v l₂)
  (hp2l2 : p₂ ∈ pdsLine B v l₂) :
  p₁ = p₂ ∨ l₁ = l₂ := by
  classical
  by_cases hp : p₁ = p₂
  · exact Or.inl hp
  · -- We will show `l₁ = l₂`.
    -- Pick the witnesses in `B` for the four memberships.
    rcases (mem_pdsLine_iff_sub_coe_mem B v p₁ l₁).1 hp1l1 with ⟨b11, hb11B, h11⟩
    rcases (mem_pdsLine_iff_sub_coe_mem B v p₂ l₁).1 hp2l1 with ⟨b21, hb21B, h21⟩
    rcases (mem_pdsLine_iff_sub_coe_mem B v p₁ l₂).1 hp1l2 with ⟨b12, hb12B, h12⟩
    rcases (mem_pdsLine_iff_sub_coe_mem B v p₂ l₂).1 hp2l2 with ⟨b22, hb22B, h22⟩

    -- The two off-diagonal pairs we will compare:
    have hb11_ne_b21 : b11 ≠ b21 := by
      intro hEq
      -- then `(p₁ - l₁) - (p₂ - l₁) = 0` ⇒ `p₁ - p₂ = 0` ⇒ `p₁ = p₂`
      have h0 : ((p₁ - l₁) - (p₂ - l₁) : ZMod v) = 0 := by
        simp [h11, h21, hEq]
      have : (p₁ - p₂ : ZMod v) = 0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h0
      exact hp (sub_eq_zero.mp this)
    have hb12_ne_b22 : b12 ≠ b22 := by
      intro hEq
      have h0 : ((p₁ - l₂) - (p₂ - l₂) : ZMod v) = 0 := by
        simp [h12, h22, hEq]
      have : (p₁ - p₂ : ZMod v) = 0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h0
      exact hp (sub_eq_zero.mp this)

    have hpair1 : (b11, b21) ∈ B.offDiag := ⟨hb11B, hb21B, hb11_ne_b21⟩
    have hpair2 : (b12, b22) ∈ B.offDiag := ⟨hb12B, hb22B, hb12_ne_b22⟩

    -- Under the PDS map, both pairs land at the same residue `(p₁ - p₂)`.
    have him1 :
        ((b11 : ZMod v) - (b21 : ZMod v)) = (p₁ - p₂ : ZMod v) := by
      -- `((p₁ - l₁) - (p₂ - l₁)) = (p₁ - p₂)`
      have : ((p₁ - l₁) - (p₂ - l₁) : ZMod v) = (p₁ - p₂) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      simpa [h11, h21] using this
    have him2 :
        ((b12 : ZMod v) - (b22 : ZMod v)) = (p₁ - p₂ : ZMod v) := by
      have : ((p₁ - l₂) - (p₂ - l₂) : ZMod v) = (p₁ - p₂) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      simpa [h12, h22] using this
    have himEq :
        ((b11 : ZMod v) - (b21 : ZMod v)) = ((b12 : ZMod v) - (b22 : ZMod v)) :=
      him1.trans him2.symm

    -- Use injectivity on `B.offDiag`
    rcases h with ⟨_maps, hinj, _surj⟩
    have hPairsEq : (b11, b21) = (b12, b22) := by
      apply hinj hpair1 hpair2
      simpa using himEq

    -- From equality of pairs we had `(p₁ - l₁) = (p₁ - l₂)`. Cancel `p₁` on the left.
    have hpl : (p₁ - l₁ : ZMod v) = p₁ - l₂ := by
      cases hPairsEq
      simp [h11, h12]
    -- Add `-p₁` to both sides: `-p₁ + (p₁ - l₁) = -p₁ + (p₁ - l₂)`
    have hneg :
        (-p₁ + (p₁ - l₁) : ZMod v) = -p₁ + (p₁ - l₂) :=
      congrArg (fun z : ZMod v => -p₁ + z) hpl
    -- This simplifies to `-l₁ = -l₂`
    have hneg' : (-l₁ : ZMod v) = -l₂ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    -- Hence `l₁ = l₂`
    have hl : l₁ = l₂ := by
      simpa using (neg_injective hneg')
    exact Or.inr hl

/-- If `B` is a perfect difference set modulo `v` and `x₁ ≠ x₂`, then there exists
a `y : ZMod v` lying on both `pdsLine B v x₁` and `pdsLine B v x₂`. -/
lemma exists_point_on_both_pdsLines
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  {x₁ x₂ : ZMod v} (hneq : x₁ ≠ x₂) :
  ∃ y : ZMod v, y ∈ pdsLine B v x₁ ∧ y ∈ pdsLine B v x₂ := by
  classical
  rcases h with ⟨_maps, hinj, hsurj⟩
  -- `x₂ - x₁` is a nonzero residue (since `x₁ ≠ x₂`)
  have hxne : (x₂ - x₁ : ZMod v) ≠ 0 := by
    intro h0
    -- add `x₁` to both sides
    have := congrArg (fun z : ZMod v => z + x₁) h0
    -- we got `x₂ = x₁`; flip it to contradict `hneq : x₁ ≠ x₂`
    exact hneq (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm)
  have hxmem : (x₂ - x₁ : ZMod v) ∈ {x : ZMod v | x ≠ 0} := by simpa using hxne

  -- Surjectivity gives a pair `(a,b) ∈ B.offDiag` with `a - b = x₂ - x₁`
  rcases hsurj hxmem with ⟨⟨a, b⟩, hpair, hdiff⟩
  rcases hpair with ⟨haB, hbB, hneab⟩

  -- Define the common point
  let y : ZMod v := (b : ZMod v) + x₂

  -- Show `y` lies on the `x₂`-line (witness `b`)
  have hy₂ : y ∈ pdsLine B v x₂ := by
    exact ⟨b, hbB, rfl⟩

  -- Show `y` lies on the `x₁`-line (witness `a`)
  have hy₁ : y ∈ pdsLine B v x₁ := by
    -- compute `y - x₁ = b + (x₂ - x₁) = b + (a - b) = a`
    have : (y - x₁ : ZMod v) = (a : ZMod v) := by
      -- first expand `y - x₁` to `b + (x₂ - x₁)`
      have hyx1 : (y - x₁ : ZMod v) = (b : ZMod v) + (x₂ - x₁) := by
        simp [y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      -- rewrite `x₂ - x₁` using `hdiff : (a - b) = (x₂ - x₁)`
      have hyx1' : (y - x₁ : ZMod v) = (b : ZMod v) + ((a : ZMod v) - (b : ZMod v)) := by
        simpa [hdiff] using hyx1
      -- simplify `b + (a - b)` to `a`
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hyx1'
    exact (mem_pdsLine_iff_sub_coe_mem B v y x₁).2 ⟨a, haB, this⟩

  exact ⟨y, hy₁, hy₂⟩

noncomputable def pdsCommonPoint
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (x₁ x₂ : ZMod v) (hneq : x₁ ≠ x₂) : ZMod v :=
  Classical.choose (exists_point_on_both_pdsLines (B := B) (v := v) h (x₁ := x₁) (x₂ := x₂) hneq)

/-- The chosen point lies on both lines. -/
lemma pdsCommonPoint_mem_both
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  {x₁ x₂ : ZMod v} (hneq : x₁ ≠ x₂) :
  pdsCommonPoint (B := B) (v := v) h x₁ x₂ hneq ∈ pdsLine B v x₁ ∧
  pdsCommonPoint (B := B) (v := v) h x₁ x₂ hneq ∈ pdsLine B v x₂ := by
  classical
  -- Unpack the witnesses from `exists_point_on_both_pdsLines`
  simpa [pdsCommonPoint] using
    Classical.choose_spec (exists_point_on_both_pdsLines
      (B := B) (v := v) h (x₁ := x₁) (x₂ := x₂) hneq)

/-- If `B` is a perfect difference set modulo `v` and `x₁ ≠ x₂` are points in `ZMod v`,
then there exists a line (some translate `y : ZMod v`) containing both points. -/
lemma exists_pdsLine_through_two_points
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  {x₁ x₂ : ZMod v} (hneq : x₁ ≠ x₂) :
  ∃ y : ZMod v, x₁ ∈ pdsLine B v y ∧ x₂ ∈ pdsLine B v y := by
  classical
  rcases h with ⟨_maps, _inj, hsurj⟩
  -- `x₁ - x₂` is nonzero
  have hxne : (x₁ - x₂ : ZMod v) ≠ 0 := by
    intro h0
    -- add `x₂` to both sides; this gives `x₁ = x₂`
    have := congrArg (fun z : ZMod v => z + x₂) h0
    exact hneq (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
  have hxmem : (x₁ - x₂ : ZMod v) ∈ {x : ZMod v | x ≠ 0} := by simpa using hxne

  -- Surjectivity: pick `(a,b) ∈ B.offDiag` with `a - b = x₁ - x₂`
  rcases hsurj hxmem with ⟨⟨a, b⟩, hpair, hdiff⟩
  rcases hpair with ⟨haB, hbB, _hneab⟩

  -- Define the line index
  let y : ZMod v := (x₂ : ZMod v) - (b : ZMod v)

  -- Show `x₂` lies on `pdsLine B v y` (witness `b`)
  have hx2 : x₂ ∈ pdsLine B v y := by
    -- since `(x₂ - y) = b`
    refine (mem_pdsLine_iff_sub_coe_mem B v x₂ y).2 ?_
    have : (x₂ - y : ZMod v) = (b : ZMod v) := by
      simp [y, sub_eq_add_neg]
    exact ⟨b, hbB, this⟩

  -- Show `x₁` lies on `pdsLine B v y` (witness `a`)
  have hx1 : x₁ ∈ pdsLine B v y := by
    -- compute `(x₁ - y) = b + (x₁ - x₂) = b + (a - b) = a`
    refine (mem_pdsLine_iff_sub_coe_mem B v x₁ y).2 ?_
    have hstep : (x₁ - y : ZMod v) = (b : ZMod v) + (x₁ - x₂) := by
      simp [y, sub_eq_add_neg, add_left_comm]
    have hstep' :
        (x₁ - y : ZMod v) = (b : ZMod v) + ((a : ZMod v) - (b : ZMod v)) := by
      simpa [hdiff] using hstep
    have : (x₁ - y : ZMod v) = (a : ZMod v) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstep'
    exact ⟨a, haB, this⟩

  exact ⟨y, hx1, hx2⟩

/-- A chosen common line through two distinct points `x₁, x₂`:
we pick `y` from the existence lemma with `x₁, x₂ ∈ pdsLine B v y`. -/
noncomputable def pdsCommonLine
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (x₁ x₂ : ZMod v) (hneq : x₁ ≠ x₂) : ZMod v :=
  Classical.choose (exists_pdsLine_through_two_points
    (B := B) (v := v) h (x₁ := x₁) (x₂ := x₂) hneq)

/-- The chosen common line contains both points. -/
lemma pdsCommonLine_mem_both
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  {x₁ x₂ : ZMod v} (hneq : x₁ ≠ x₂) :
  x₁ ∈ pdsLine B v (pdsCommonLine (B := B) (v := v) h x₁ x₂ hneq) ∧
  x₂ ∈ pdsLine B v (pdsCommonLine (B := B) (v := v) h x₁ x₂ hneq) := by
  classical
  -- Directly unpack the witnesses from the existence lemma.
  simpa [pdsCommonLine] using
    Classical.choose_spec
      (exists_pdsLine_through_two_points (B := B) (v := v) h (x₁ := x₁) (x₂ := x₂) hneq)

/-- In a PDS, the coercion `ℕ → ZMod v` is injective on `B`. -/
lemma coe_injOn_of_pds {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v) :
  Set.InjOn (fun b : ℤ => (b : ZMod v)) B := by
  classical
  intro b1 hb1 b2 hb2 hcoe
  by_contra hneq
  rcases h with ⟨hMaps, _hinj, _hsurj⟩
  have hpair : (b1, b2) ∈ B.offDiag := ⟨hb1, hb2, hneq⟩
  -- image of (b1,b2) is nonzero
  have hx : (↑b1 - ↑b2 : ZMod v) ∈ {x : ZMod v | x ≠ 0} := hMaps hpair
  have hne0 : (↑b1 - ↑b2 : ZMod v) ≠ 0 := by simpa using hx
  -- but equal residues give zero difference
  have heq0 : (↑b1 - ↑b2 : ZMod v) = 0 := by simp [hcoe]
  exact hne0 heq0

/-- Each line has exactly `q+1` points (and hence at least three when `q ≥ 2`). -/
lemma ncard_pdsLine_of_card
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1)
  (ℓ : ZMod v) :
  (pdsLine B v ℓ).ncard = q + 1 := by
  classical
  -- 1) `pdsLine` is the image of `B` by translation `b ↦ ↑b + ℓ`.
  have himg : pdsLine B v ℓ = (fun b : ℤ => (b : ZMod v) + ℓ) '' B := by
    ext y; constructor
    · rintro ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩
    · rintro ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩

  -- 2) Translation is injective on `B`.
  have hinj : Set.InjOn (fun b : ℤ => (b : ZMod v) + ℓ) B := by
    intro b1 hb1 b2 hb2 hsum
    have : (b1 : ZMod v) = (b2 : ZMod v) := by
      have := congrArg (fun z : ZMod v => z - ℓ) hsum
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact (coe_injOn_of_pds (B := B) (v := v) h) hb1 hb2 this

  -- 3) A `BijOn` between `B` and `pdsLine B v ℓ`.
  have hbij : B.BijOn (fun b : ℤ => (b : ZMod v) + ℓ) (pdsLine B v ℓ) := by
    refine ⟨?maps, hinj, ?surj⟩
    · intro b hbB; exact ⟨b, hbB, rfl⟩
    · intro y hy; rcases hy with ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩

  -- 4) Pass to finsets and compare `card`s.
  have hfinLine : (pdsLine B v ℓ).Finite := by
    simpa [himg] using hfin.image (fun b : ℤ => (b : ZMod v) + ℓ)

  set s : Finset ℤ := hfin.toFinset
  set t : Finset (ZMod v) := hfinLine.toFinset

  have hB_coe : (↑s : Set ℤ) = B := hfin.coe_toFinset
  have hL_coe : (↑t : Set (ZMod v)) = pdsLine B v ℓ := hfinLine.coe_toFinset

  -- Transport the bijection to the coerced finsets.
  have hbij' :
      (↑s : Set ℤ).BijOn (fun b : ℤ => (b : ZMod v) + ℓ) (↑t : Set (ZMod v)) := by
    simpa [hB_coe, hL_coe] using hbij

  -- Equal `card`s of those finsets (correct usage of `finsetCard_eq`).
  have hcards : s.card = t.card :=
    Set.BijOn.finsetCard_eq
      (e  := fun b : ℤ => (b : ZMod v) + ℓ)
      (he := hbij')

  /- 5) Convert back to `ncard` explicitly (avoid brittle `simpa`). -/
  -- For the line:
  have h_line_ncard : (pdsLine B v ℓ).ncard = t.card := by
    -- First do it for `↑t`, then rewrite using `hL_coe`.
    have : (↑t : Set (ZMod v)).ncard = t.card := by
      simp [Set.ncard_eq_toFinset_card]
    simpa [hL_coe] using this

  -- For `B`:
  have h_B_ncard : B.ncard = s.card := by
    -- First do it for `↑s`, then rewrite using `hB_coe`.
    have : (↑s : Set ℤ).ncard = s.card := by
      simp [Set.ncard_eq_toFinset_card]
    simpa [hB_coe] using this

  -- Now `(pdsLine …).ncard = s.card` and hence equals `B.ncard`.
  have hEq : (pdsLine B v ℓ).ncard = B.ncard := by
    have : (pdsLine B v ℓ).ncard = s.card := by
      simpa [hcards] using h_line_ncard
    simpa [h_B_ncard] using this

  -- Conclude with `B.ncard = q+1`.
  simpa [hEq] using hcard

/-- In a PDS, no line contains the three points `0, 1, 2` (provided `v ≥ 3`). -/
lemma not012_on_same_pdsLine
  {B : Set ℤ} {v : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v) (hv : 3 ≤ v) (ℓ : ZMod v) :
  ¬ ((0 : ZMod v) ∈ pdsLine B v ℓ ∧
     (1 : ZMod v) ∈ pdsLine B v ℓ ∧
     (2 : ZMod v) ∈ pdsLine B v ℓ) := by
  classical
  -- ensure `1 ≠ 0` in `ZMod v`
  haveI : Fact (1 < v) := ⟨lt_of_lt_of_le (by decide : 1 < 3) hv⟩
  rcases h with ⟨_maps, hinj, _surj⟩
  intro h012
  rcases h012 with ⟨h0, h1, h2⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v (0 : ZMod v) ℓ).1 h0 with ⟨b0, hb0B, h0eq⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v (1 : ZMod v) ℓ).1 h1 with ⟨b1, hb1B, h1eq⟩
  rcases (mem_pdsLine_iff_sub_coe_mem B v (2 : ZMod v) ℓ).1 h2 with ⟨b2, hb2B, h2eq⟩
  -- (1 - ℓ) - (0 - ℓ) = 1  ⇒  (b1 - b0) = 1
  have diff10 : ((b1 : ZMod v) - (b0 : ZMod v)) = 1 := by
    have : ((1 : ZMod v) - ℓ) - ((0 : ZMod v) - ℓ) = 1 := by
      have hsub : ((1 : ZMod v) - ℓ) - ((0 : ZMod v) - ℓ) = (1 : ZMod v) - 0 := by
        simp [sub_eq_add_neg, add_comm]
      simp
    simpa [h1eq, h0eq] using this
  -- (2 - ℓ) - (1 - ℓ) = 1  ⇒  (b2 - b1) = 1
  have diff21 : ((b2 : ZMod v) - (b1 : ZMod v)) = 1 := by
    have hsub : ((2 : ZMod v) - ℓ) - ((1 : ZMod v) - ℓ) = (2 : ZMod v) - 1 := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have : ((2 : ZMod v) - ℓ) - ((1 : ZMod v) - ℓ) = 1 := by
      simpa using hsub.trans (by norm_num)
    simpa [h2eq, h1eq] using this
  -- So both pairs are in `B.offDiag`
  have hb10ne : b1 ≠ b0 := by
    intro hEq
    have : ((b1 : ZMod v) - (b0 : ZMod v)) = 0 := by simp [hEq]
    have : (1 : ZMod v) = 0 := by simpa [this] using diff10.symm
    exact (one_ne_zero : (1 : ZMod v) ≠ 0) this
  have hb21ne : b2 ≠ b1 := by
    intro hEq
    have : ((b2 : ZMod v) - (b1 : ZMod v)) = 0 := by simp [hEq]
    have : (1 : ZMod v) = 0 := by simpa [this] using diff21.symm
    exact (one_ne_zero : (1 : ZMod v) ≠ 0) this
  have hp10 : (b1, b0) ∈ B.offDiag := ⟨hb1B, hb0B, hb10ne⟩
  have hp21 : (b2, b1) ∈ B.offDiag := ⟨hb2B, hb1B, hb21ne⟩
  -- Injectivity of the PDS map forces these ordered pairs equal,
  -- contradicting `b1 ≠ b0`.
  have : (b1, b0) = (b2, b1) := by
    apply hinj hp10 hp21
    simp [diff10, diff21]
  exact hb10ne (by cases this; rfl)

/-- If a PDS has `|B| = q+1 ≥ 3`, then any line containing both `0` and `1`
contains a third point different from `0` and `1`. -/
lemma exists_third_point_on_line_with_0_1
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
  {ℓ : ZMod v}
  (h0 : (0 : ZMod v) ∈ pdsLine B v ℓ)
  (h1 : (1 : ZMod v) ∈ pdsLine B v ℓ) :
  ∃ p : ZMod v, p ∈ pdsLine B v ℓ ∧ p ≠ 0 ∧ p ≠ 1 := by
  classical
  -- The line is finite (image of a finite set).
  have hfinL : (pdsLine B v ℓ).Finite := by
    -- one way: `pdsLine` is an image of `B` under `b ↦ (b : ZMod v) + ℓ`
    have : pdsLine B v ℓ = (fun b : ℤ => (b : ZMod v) + ℓ) '' B := by
      ext y; constructor
      · rintro ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩
      · rintro ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩
    simpa [this] using hfin.image (fun b : ℤ => (b : ZMod v) + ℓ)

  -- Work with the finset of that line.
  let T : Finset (ZMod v) := hfinL.toFinset
  have hTset : (↑T : Set (ZMod v)) = pdsLine B v ℓ := hfinL.coe_toFinset

  -- >>> FIXED PART: turn the `ncard` statement into `T.card = q+1`.
  have hTcard : T.card = q + 1 := by
    have hline : (pdsLine B v ℓ).ncard = q + 1 :=
      ncard_pdsLine_of_card (B := B) (v := v) (q := q) h hfin hcard ℓ
    -- rewrite to the coerced finset-set, then use `ncard_eq_toFinset_card`
    have : ((↑T : Set (ZMod v))).ncard = q + 1 := by
      simpa [hTset] using hline
    simpa [Set.ncard_eq_toFinset_card] using this
  -- <<<

  -- 0 and 1 are in the finset `T` (coercion-to-set then `Finset.mem_coe`)
  have h0T : (0 : ZMod v) ∈ T := by
    have : (0 : ZMod v) ∈ (↑T : Set (ZMod v)) := by simpa [hTset] using h0
    simpa using this
  have h1T : (1 : ZMod v) ∈ T := by
    have : (1 : ZMod v) ∈ (↑T : Set (ZMod v)) := by simpa [hTset] using h1
    simpa using this

  -- From `hTcard : T.card = q+1` and `hq3 : 3 ≤ q+1` we get `3 ≤ T.card`.
  have hT_ge3 : 3 ≤ T.card := by simpa [hTcard] using hq3

  -- Case split on `1 = 0`.
  by_cases h10 : (1 : ZMod v) = 0
  · -- Then `1 = 0`. Since `T.card ≥ 3`, `T.erase 0` has at least 2 elements.
    have hU : (T.erase 0).card + 1 = T.card := T.card_erase_add_one h0T
    have hU_ge2 : 2 ≤ (T.erase 0).card := by
      -- 3 ≤ T.card = (T.erase 0).card + 1  ⇒  2 ≤ (T.erase 0).card
      have : 3 ≤ (T.erase 0).card + 1 := by simpa [hU] using hT_ge3
      exact (Nat.succ_le_succ_iff.mp this)
    -- hence nonempty; pick p ∈ T.erase 0
    have hU_pos : 0 < (T.erase 0).card := lt_of_lt_of_le (by decide : 0 < 2) hU_ge2
    obtain ⟨p, hpU⟩ := Finset.card_pos.mp hU_pos
    have hpT   : p ∈ T := (Finset.mem_erase.mp hpU).2
    have hp_ne0 : p ≠ 0 := (Finset.mem_erase.mp hpU).1
    refine ⟨p, ?_, hp_ne0, ?_⟩
    · -- turn `p ∈ T` into `p ∈ (↑T : Set _)`, then rewrite by `hTset`
      have hpT_set : p ∈ (↑T : Set (ZMod v)) := by simpa using hpT
      simpa [hTset] using hpT_set
    · -- since `1 = 0`, `p ≠ 1` as well
      simpa [h10] using hp_ne0

  · -- Now the main case: `1 ≠ 0`. Then both are distinct elements of `T`.
    have h10' : (1 : ZMod v) ≠ 0 := h10
    -- First erase 0: still at least 2 elements.
    have hU : (T.erase 0).card + 1 = T.card := T.card_erase_add_one h0T
    have hU_ge2 : 2 ≤ (T.erase 0).card := by
      have : 3 ≤ (T.erase 0).card + 1 := by simpa [hU] using hT_ge3
      exact (Nat.succ_le_succ_iff.mp this)
    -- 1 is still in `T.erase 0` since `1 ≠ 0`.
    have h1_in_U : (1 : ZMod v) ∈ T.erase 0 := by
      simp [Finset.mem_erase, h10', h1T]
    -- Erase 1 too: now at least 1 element remains because T.card ≥ 3.
    have hV : ((T.erase 0).erase 1).card + 1 = (T.erase 0).card :=
      (T.erase 0).card_erase_add_one h1_in_U

    have hV_pos : 0 < ((T.erase 0).erase 1).card := by
      -- from `2 ≤ (T.erase 0).card` and `hV` we get `2 ≤ ((T.erase 0).erase 1).card + 1`
      have h2 : 2 ≤ ((T.erase 0).erase 1).card + 1 := by
        simpa [hV] using hU_ge2
      -- strip one `succ` on both sides: `1 ≤ ((T.erase 0).erase 1).card`
      have hge1 : 1 ≤ ((T.erase 0).erase 1).card :=
        (Nat.succ_le_succ_iff).mp (by simpa using h2)
      -- then `0 < …` via `Nat.succ_le.mp`
      exact Nat.succ_le.mp hge1
    -- Pick p from that remainder; p ≠ 0 and p ≠ 1 and p ∈ T.
    obtain ⟨p, hpV⟩ := Finset.card_pos.mp hV_pos
    have hpU  : p ∈ T.erase 0 := (Finset.mem_erase.mp hpV).2
    have hpT  : p ∈ T := (Finset.mem_erase.mp hpU).2
    have hp_ne1 : p ≠ 1 := (Finset.mem_erase.mp hpV).1
    have hp_ne0 : p ≠ 0 := (Finset.mem_erase.mp hpU).1
    refine ⟨p, ?_, hp_ne0, hp_ne1⟩
      -- turn `p ∈ T` into `p ∈ (↑T : Set _)`, then rewrite via `hTset`
    · have hpT_set : p ∈ (↑T : Set (ZMod v)) := by
        simpa using hpT            -- uses `Finset.mem_coe`
      simpa [hTset] using hpT_set  -- now `p ∈ pdsLine B v ℓ`


/-- If a PDS has `|B| = q+1 ≥ 3`, then **for any two distinct points** `p₁ ≠ p₂`
there is a line through them that contains a third point different from both. -/
lemma exists_third_point_on_line_with_two_points
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (h : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
  {p₁ p₂ : ZMod v} (hneq : p₁ ≠ p₂) :
  ∃ ℓ p, p ∈ pdsLine B v ℓ ∧
          p₁ ∈ pdsLine B v ℓ ∧
          p₂ ∈ pdsLine B v ℓ ∧
          p ≠ p₁ ∧ p ≠ p₂ := by
  classical
  -- Pick a line through p₁ and p₂.
  obtain ⟨ℓ, hp1ℓ, hp2ℓ⟩ :=
    exists_pdsLine_through_two_points (B := B) (v := v) h hneq

  -- The line is finite (image of a finite set).
  have hfinL : (pdsLine B v ℓ).Finite := by
    have : pdsLine B v ℓ = (fun b : ℤ => (b : ZMod v) + ℓ) '' B := by
      ext y; constructor
      · rintro ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩
      · rintro ⟨b, hbB, rfl⟩; exact ⟨b, hbB, rfl⟩
    simpa [this] using hfin.image (fun b : ℤ => (b : ZMod v) + ℓ)

  -- Work with the finset of the line.
  let T : Finset (ZMod v) := hfinL.toFinset
  have hTset : (↑T : Set (ZMod v)) = pdsLine B v ℓ := hfinL.coe_toFinset

  -- Card of the line is q+1.
  have hTcard : T.card = q + 1 := by
    have hline : (pdsLine B v ℓ).ncard = q + 1 :=
      ncard_pdsLine_of_card (B := B) (v := v) (q := q) h hfin hcard ℓ
    have : ((↑T : Set (ZMod v))).ncard = q + 1 := by
      simpa [hTset] using hline
    simpa [Set.ncard_eq_toFinset_card] using this

  -- p₁,p₂ are in that finset.
  have hp1T : p₁ ∈ T := by
    have : p₁ ∈ (↑T : Set (ZMod v)) := by simpa [hTset] using hp1ℓ
    simpa using this
  have hp2T : p₂ ∈ T := by
    have : p₂ ∈ (↑T : Set (ZMod v)) := by simpa [hTset] using hp2ℓ
    simpa using this

  -- From `hTcard` and `hq3` we get `3 ≤ T.card`.
  have hT_ge3 : 3 ≤ T.card := by simpa [hTcard] using hq3

  -- Erase p₁: still at least 2 elements.
  have hU : (T.erase p₁).card + 1 = T.card := T.card_erase_add_one hp1T
  have hU_ge2 : 2 ≤ (T.erase p₁).card := by
    have : 3 ≤ (T.erase p₁).card + 1 := by simpa [hU] using hT_ge3
    exact (Nat.succ_le_succ_iff).mp this

  -- p₂ is still in `T.erase p₁` (since `p₂ ≠ p₁`).
  have hp2_ne_p1 : p₂ ≠ p₁ := fun h => hneq h.symm
  have hp2_in_U : p₂ ∈ T.erase p₁ := by
    simp [Finset.mem_erase, hp2_ne_p1, hp2T]

  -- Erase p₂ as well: now at least one element remains.
  have hV : ((T.erase p₁).erase p₂).card + 1 = (T.erase p₁).card :=
    (T.erase p₁).card_erase_add_one hp2_in_U
  have hV_pos : 0 < ((T.erase p₁).erase p₂).card := by
    -- From `2 ≤ (T.erase p₁).card` and `hV`, get `1 ≤ ((T.erase p₁).erase p₂).card`
    have h2 : 2 ≤ ((T.erase p₁).erase p₂).card + 1 := by
      simpa [hV] using hU_ge2
    have hge1 : 1 ≤ ((T.erase p₁).erase p₂).card :=
      (Nat.succ_le_succ_iff).mp (by simpa using h2)
    exact Nat.succ_le.mp hge1

  -- Pick a third point p in the remainder; it’s ≠ p₁, ≠ p₂, and lies in the line.
  obtain ⟨p, hpV⟩ := Finset.card_pos.mp hV_pos
  have hpU  : p ∈ T.erase p₁ := (Finset.mem_erase.mp hpV).2
  have hpT  : p ∈ T := (Finset.mem_erase.mp hpU).2
  have hp_ne2 : p ≠ p₂ := (Finset.mem_erase.mp hpV).1
  have hp_ne1 : p ≠ p₁ := (Finset.mem_erase.mp hpU).1
  -- convert back to set-membership on the line
  have hpT_set : p ∈ (↑T : Set (ZMod v)) := by simpa using hpT
  have hpLine  : p ∈ pdsLine B v ℓ := by simpa [hTset] using hpT_set

  exact ⟨ℓ, p, hpLine, hp1ℓ, hp2ℓ, hp_ne1, hp_ne2⟩

/-- If `0 ≤ a < b < v` (naturals), then `a % v ≠ b % v`. -/
lemma mod_ne_of_lt_chain {a b v : ℕ}
    --(h0a : 0 ≤ a)
    (hab : a < b) (hbv : b < v) :
    a % v ≠ b % v := by
  -- From `a < b < v` we also have `a < v`
  have hav : a < v := lt_trans hab hbv
  -- Reduce both remainders since they are already below `v`
  have hmod_a : a % v = a := Nat.mod_eq_of_lt hav
  have hmod_b : b % v = b := Nat.mod_eq_of_lt hbv
  intro h
  -- If remainders were equal, the numbers would be equal
  have : a = b := by simpa [hmod_a, hmod_b] using h
  exact (ne_of_lt hab) this

/-- If `a < b` and `b < v`, then `(a : ZMod v) ≠ (b : ZMod v)`. -/
lemma zmod_coe_ne_of_lt_chain {a b v : ℕ} [NeZero v]
    (hab : a < b) (hbv : b < v) :
    (a : ZMod v) ≠ (b : ZMod v) := by
  -- From the chain we also have `a < v`
  have hav : a < v := lt_trans hab hbv
  -- If the casts were equal in `ZMod v`, their `val`s (remainders) would be equal.
  intro h
  have hval : (ZMod.val (a : ZMod v)) = ZMod.val (b : ZMod v) :=
    congrArg ZMod.val h
  -- But `ZMod.val` of a natural cast is exactly the remainder modulo `v`.
  -- With `a,b < v`, those remainders are just `a` and `b`.
  have : a % v = b % v := by
    -- these are standard simp lemmas:
    -- `ZMod.natCast_self`-style simp for `val` of a nat into `ZMod`,
    -- and `Nat.mod_eq_of_lt` because `a,b < v`.
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hval
  -- Contradict the modular inequality you already have.
  exact (mod_ne_of_lt_chain hab hbv) this

/-- If `v ≥ 3`, then `0` and `1` are distinct in `ZMod v`. -/
lemma zero_ne_one_zmod_of_three_le {v : ℕ} (hv : 3 ≤ v) :
    (0 : ZMod v) ≠ (1 : ZMod v) := by
  -- `1 < v` follows from `3 ≤ v`
  haveI : Fact (1 < v) := ⟨lt_of_lt_of_le (by decide : 1 < 3) hv⟩
  -- In a nontrivial type like `ZMod v` (when `1 < v`), we have `1 ≠ 0`
  -- and hence `0 ≠ 1`.
  simp

/-- If `v ≥ 3`, then `(1 : ZMod v) ≠ 2`. -/
lemma one_ne_two_zmod_of_three_le {v : ℕ} (hv : 3 ≤ v) :
    (1 : ZMod v) ≠ (2 : ZMod v) := by
  -- make `ZMod v` nontrivial
  haveI : Fact (1 < v) := ⟨lt_of_lt_of_le (by decide : 1 < 3) hv⟩
  -- we’ll contradict `0 ≠ 1`
  have h01 : (0 : ZMod v) ≠ (1 : ZMod v) := by simp
  -- assume `1 = 2`, subtract `1` on both sides to get `0 = 1`
  intro h12
  have h' := congrArg (fun z : ZMod v => z - (1 : ZMod v)) h12
  -- `h' : (1 - 1) = (2 - 1)`
  have h'' : (0 : ZMod v) = ((2 : ZMod v) - 1) := by
    simpa [sub_eq_add_neg] using h'
  -- compute `(2 : ZMod v) - 1 = 1`
  have h2sub1 : (2 : ZMod v) - 1 = (1 : ZMod v) := by
    norm_num
  -- contradiction: `0 = 1`
  exact h01 (by simp [h2sub1] at h'')

/-- If `v ≥ 3`, then `(0 : ZMod v) ≠ (2 : ZMod v)`. -/
lemma zero_ne_two_zmod_of_three_le {v : ℕ} (hv : 3 ≤ v) :
    (0 : ZMod v) ≠ (2 : ZMod v) := by
  intro h
  -- First rewrite the equality so it matches `ZMod.natCast_eq_natCast_iff`.
  have h' : ((0 : ℕ) : ZMod v) = (2 : ℕ) := by simpa using h
  -- Equality of casts ↔ congruence mod `v`
  have hmod : 0 ≡ 2 [MOD v] := (ZMod.natCast_eq_natCast_iff 0 2 v).1 h'
  -- From `0 ≡ 2 [MOD v]` we get `2 % v = 0`, hence `v ∣ 2`.
  have hv_mod : 2 % v = 0 := by
    -- `Nat.ModEq v a b` is definitionally `a % v = b % v`
    simpa [Nat.ModEq, Nat.zero_mod] using hmod.symm
  have hv_dvd2 : v ∣ 2 := Nat.dvd_of_mod_eq_zero hv_mod
  -- But `v ≥ 3` makes that impossible.
  have : 3 ≤ 2 := le_trans hv (Nat.le_of_dvd (by decide : 0 < 2) hv_dvd2)
  exact (Nat.not_succ_le_self 2) this

/-- Build the configuration with lines `ℓ01, ℓ02, ℓ12`, a third point `p` on `ℓ01`,
then a line `ℓ2p` through `2` and `p`, and a third point `q` on `ℓ2p`. -/
lemma exists_config_012_p_q
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (hv : 3 ≤ v)
  (h : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1) :
  ∃ ℓ01 ℓ02 ℓ12 ℓ2p p q : ZMod v,
      (0 : ZMod v) ∈ pdsLine B v ℓ01 ∧ (1 : ZMod v) ∈ pdsLine B v ℓ01 ∧
      (0 : ZMod v) ∈ pdsLine B v ℓ02 ∧ (2 : ZMod v) ∈ pdsLine B v ℓ02 ∧
      (1 : ZMod v) ∈ pdsLine B v ℓ12 ∧ (2 : ZMod v) ∈ pdsLine B v ℓ12 ∧
      p ∈ pdsLine B v ℓ01 ∧ p ≠ 0 ∧ p ≠ 1 ∧
      (2 : ZMod v) ∈ pdsLine B v ℓ2p ∧ p ∈ pdsLine B v ℓ2p ∧
      q ∈ pdsLine B v ℓ2p ∧ q ≠ (2 : ZMod v) ∧ q ≠ p := by
  classical
  -- Pairwise distinctness of 0,1,2 from `v ≥ 3`
  have h01 : (0 : ZMod v) ≠ (1 : ZMod v) := zero_ne_one_zmod_of_three_le hv
  have h02 : (0 : ZMod v) ≠ (2 : ZMod v) := zero_ne_two_zmod_of_three_le hv
  have h12 : (1 : ZMod v) ≠ (2 : ZMod v) := one_ne_two_zmod_of_three_le hv

  -- Lines through the pairs (0,1), (0,2), (1,2)
  obtain ⟨ℓ01, h0ℓ01, h1ℓ01⟩ :=
    exists_pdsLine_through_two_points (B := B) (v := v) h (x₁ := (0 : ZMod v)) (x₂ := 1) h01
  obtain ⟨ℓ02, h0ℓ02, h2ℓ02⟩ :=
    exists_pdsLine_through_two_points (B := B) (v := v) h (x₁ := (0 : ZMod v)) (x₂ := 2) h02
  obtain ⟨ℓ12, h1ℓ12, h2ℓ12⟩ :=
    exists_pdsLine_through_two_points (B := B) (v := v) h (x₁ := (1 : ZMod v)) (x₂ := 2) h12

  -- A third point `p` on ℓ01, different from 0 and 1
  obtain ⟨p, hpℓ01, hp0, hp1⟩ :=
    exists_third_point_on_line_with_0_1
      (B := B) (v := v) (q := q) h hfin hcard hq3 h0ℓ01 h1ℓ01

  -- Show `p ≠ 2` using "no 0,1,2 on the same line"
  have h2_not_on_ℓ01 : (2 : ZMod v) ∉ pdsLine B v ℓ01 := by
    have hNo := not012_on_same_pdsLine (B := B) (v := v) h hv ℓ01
    exact fun h2 => (hNo ⟨h0ℓ01, h1ℓ01, h2⟩).elim
  have hp2 : p ≠ (2 : ZMod v) := by
    intro hpeq
    have : (2 : ZMod v) ∈ pdsLine B v ℓ01 := by simpa [hpeq] using hpℓ01
    exact h2_not_on_ℓ01 this

  -- The line through {2,p}
  obtain ⟨ℓ2p, h2ℓ2p, hpℓ2p⟩ :=
    exists_pdsLine_through_two_points (B := B) (v := v) h (x₁ := (2 : ZMod v)) (x₂ := p) (by
      exact ne_comm.mp hp2)

  -- On that line, get a third point `q ≠ 2,p`.
  obtain ⟨ℓ', q, hqℓ', h2ℓ', hpℓ', hq2, hqp⟩ :=
    exists_third_point_on_line_with_two_points
      (B := B) (v := v) (q := q) h hfin hcard hq3
      (p₁ := (2 : ZMod v)) (p₂ := p) (by exact ne_comm.mp hp2)

  -- Uniqueness: `ℓ' = ℓ2p`, so `q ∈ pdsLine B v ℓ2p`.
  have : ℓ' = ℓ2p := by
    have hcollapse :=
      pds_points_lines_collapse (B := B) (v := v) h
        (p₁ := (2 : ZMod v)) (p₂ := p) (l₁ := ℓ') (l₂ := ℓ2p)
        h2ℓ' hpℓ' h2ℓ2p hpℓ2p
    rcases hcollapse with hEq | hEq
    · exact (hp2 (by simpa using hEq.symm)).elim
    · exact hEq
  have hqℓ2p : q ∈ pdsLine B v ℓ2p := by simpa [this] using hqℓ'

  -- Package everything
  exact ⟨ℓ01, ℓ02, ℓ12, ℓ2p, p, q,
    h0ℓ01, h1ℓ01, h0ℓ02, h2ℓ02, h1ℓ12, h2ℓ12,
    hpℓ01, hp0, hp1,
    h2ℓ2p, hpℓ2p,
    hqℓ2p, hq2, hqp⟩

/-- Using the configuration, produce
`p₁ = q`, `p₂ = 1`, `p₃ = p` and `l₁ = ℓ02`, `l₂ = ℓ01`, `l₃ = ℓ12`
with the required incidences. -/
lemma exists_pattern_from_config
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (hv : 3 ≤ v)
  (h : IsPerfectDifferenceSetModulo B v)
  (hf : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1) :
  ∃ (p₁ p₂ p₃ : ZMod v) (l₁ l₂ l₃ : ZMod v),
    p₁ ∉ pdsLine B v l₂ ∧ p₁ ∉ pdsLine B v l₃ ∧
    p₂ ∉ pdsLine B v l₁ ∧ p₂ ∈ pdsLine B v l₂ ∧ p₂ ∈ pdsLine B v l₃ ∧
    p₃ ∉ pdsLine B v l₁ ∧ p₃ ∈ pdsLine B v l₂ ∧ p₃ ∉ pdsLine B v l₃ := by
  classical
  rcases exists_config_012_p_q (B := B) (v := v) (q := q) hv h hf hcard hq3 with
    ⟨ℓ01, ℓ02, ℓ12, ℓ2p, p, q, h0ℓ01, h1ℓ01, h0ℓ02, h2ℓ02, h1ℓ12, h2ℓ12,
      hpℓ01, hp0, hp1, h2ℓ2p, hpℓ2p, hqℓ2p, hq2, hqp⟩
  -- We target the assignment:
  --   p₁ := q,  p₂ := 1,  p₃ := p,
  --   l₁ := ℓ02, l₂ := ℓ01, l₃ := ℓ12.
  refine ⟨q, (1 : ZMod v), p, ℓ02, ℓ01, ℓ12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- p₁ ∉ l₂ :  q ∉ ℓ01
    -- If `q ∈ ℓ01`, collapsing on the pair `{p,q}` forces `ℓ01 = ℓ2p`,
    -- hence `2 ∈ ℓ01`, contradicting `not012_on_same_pdsLine`.
    intro hqℓ01
    -- collapse for points p,q on lines ℓ01 and ℓ2p
    have hcollapse :=
      pds_points_lines_collapse (B := B) (v := v) h
        (p₁ := p) (p₂ := q) (l₁ := ℓ01) (l₂ := ℓ2p)
        hpℓ01 hqℓ01 hpℓ2p hqℓ2p
    -- from the collapse, the `p = q` branch contradicts `hqp`, so we get `ℓ01 = ℓ2p`
    have hℓeq : ℓ01 = ℓ2p := by
      rcases hcollapse with hpeq | hleq
      · exact (False.elim (hqp hpeq.symm))
      · exact hleq
    -- therefore 2 ∈ ℓ01
    have h2ℓ01 : (2 : ZMod v) ∈ pdsLine B v ℓ01 := by
      simpa [hℓeq] using h2ℓ2p
    -- contradict the "no 0,1,2 on the same line" lemma
    have hNo := not012_on_same_pdsLine (B := B) (v := v) h hv ℓ01
    exact (hNo ⟨h0ℓ01, h1ℓ01, h2ℓ01⟩).elim
  · -- p₁ ∉ l₃ :  q ∉ ℓ12
    -- If `q ∈ ℓ12`, collapse on `{2,q}` across `ℓ12` and `ℓ2p` to get `ℓ12 = ℓ2p`
    -- (since `q ≠ 2`). Then `1 ∈ ℓ2p`; collapsing `{1,p}` across `ℓ01` and `ℓ2p`
    -- forces `ℓ01 = ℓ2p` (since `p ≠ 1`), hence `2 ∈ ℓ01`, contradicting `not012_on_same_pdsLine`.
    intro hqℓ12
    have hcollapse :=
      pds_points_lines_collapse (B := B) (v := v) h
        (p₁ := (2 : ZMod v)) (p₂ := q) (l₁ := ℓ12) (l₂ := ℓ2p)
        h2ℓ12 hqℓ12 h2ℓ2p hqℓ2p
    have hℓeq : ℓ12 = ℓ2p := by
      rcases hcollapse with h2q | hlin
      · exact (hq2 h2q.symm).elim
      · exact hlin
    have h1ℓ2p : (1 : ZMod v) ∈ pdsLine B v ℓ2p := by
      simpa [hℓeq] using h1ℓ12

    -- Now collapse on `{1,p}` across `ℓ01` and `ℓ2p`.
    have hcollapse' :=
      pds_points_lines_collapse (B := B) (v := v) h
        (p₁ := (1 : ZMod v)) (p₂ := p) (l₁ := ℓ01) (l₂ := ℓ2p)
        h1ℓ01 hpℓ01 h1ℓ2p hpℓ2p
    have hℓ01eqℓ2p : ℓ01 = ℓ2p := by
      rcases hcollapse' with h1p | hlin
      · exact (hp1 h1p.symm).elim
      · exact hlin

    -- Then `2 ∈ ℓ01`, contradicting `not012_on_same_pdsLine` for `ℓ01`.
    have h2ℓ01 : (2 : ZMod v) ∈ pdsLine B v ℓ01 := by
      simpa [hℓ01eqℓ2p] using h2ℓ2p
    have hNo := not012_on_same_pdsLine (B := B) (v := v) h hv ℓ01
    exact (hNo ⟨h0ℓ01, h1ℓ01, h2ℓ01⟩).elim
  · -- p₂ ∉ l₁ :  1 ∉ ℓ02   (follows from `not012_on_same_pdsLine`)
    -- The line `ℓ02` already contains `0` and `2`, so it cannot contain `1`.
    have hNo := not012_on_same_pdsLine (B := B) (v := v) h hv ℓ02
    exact fun h1 => (hNo ⟨h0ℓ02, h1, h2ℓ02⟩).elim
  · -- p₂ ∈ l₂ :  1 ∈ ℓ01
    exact h1ℓ01
  · -- p₂ ∈ l₃ :  1 ∈ ℓ12
    exact h1ℓ12
  · -- p₃ ∉ l₁ :  p ∉ ℓ02
    -- If `p ∈ ℓ02`, then `{0,p}` lies on both `ℓ01` and `ℓ02`,
    -- so collapse gives `ℓ01 = ℓ02` (since `p ≠ 0`), hence `1 ∈ ℓ02`,
    -- contradicting `not012_on_same_pdsLine` on `ℓ02`.
    intro hpℓ02
    have hcollapse :=
      pds_points_lines_collapse (B := B) (v := v) h
        (p₁ := (0 : ZMod v)) (p₂ := p) (l₁ := ℓ01) (l₂ := ℓ02)
        h0ℓ01 hpℓ01 h0ℓ02 hpℓ02
    have hℓ01eqℓ02 : ℓ01 = ℓ02 := by
      rcases hcollapse with h0p | hleq
      · exact (hp0 h0p.symm).elim
      · exact hleq
    -- then `1 ∈ ℓ02`
    have h1ℓ02 : (1 : ZMod v) ∈ pdsLine B v ℓ02 := by
      simpa [hℓ01eqℓ02] using h1ℓ01
    -- contradiction with "no 0,1,2 on the same line" for `ℓ02`
    have hNo := not012_on_same_pdsLine (B := B) (v := v) h hv ℓ02
    exact (hNo ⟨h0ℓ02, h1ℓ02, h2ℓ02⟩).elim
  · -- p₃ ∈ l₂ :  p ∈ ℓ01
    exact hpℓ01
  · -- p₃ ∉ l₃ :  p ∉ ℓ12
    -- If `p ∈ ℓ12`, then `{1,p}` lies on both `ℓ01` and `ℓ12`,
    -- so collapse gives `ℓ01 = ℓ12` (since `p ≠ 1`), hence `0 ∈ ℓ12`,
    -- and with `1,2 ∈ ℓ12` we contradict `not012_on_same_pdsLine`.
    intro hpℓ12
    have hcollapse :=
      pds_points_lines_collapse (B := B) (v := v) h
        (p₁ := (1 : ZMod v)) (p₂ := p) (l₁ := ℓ01) (l₂ := ℓ12)
        h1ℓ01 hpℓ01 h1ℓ12 hpℓ12
    have hℓ01eqℓ12 : ℓ01 = ℓ12 := by
      rcases hcollapse with h1p | hleq
      · exact (hp1 h1p.symm).elim
      · exact hleq
    -- then `0 ∈ ℓ12`
    have h0ℓ12 : (0 : ZMod v) ∈ pdsLine B v ℓ12 := by
      simpa [hℓ01eqℓ12] using h0ℓ01
    -- contradiction with "no 0,1,2 on the same line" for `ℓ12`
    have hNo := not012_on_same_pdsLine (B := B) (v := v) h hv ℓ12
    exact (hNo ⟨h0ℓ12, h1ℓ12, h2ℓ12⟩).elim

/-- From a perfect difference set `B` with `|B| = q+1 ≥ 3` (hence `v = q^2+q+1 ≥ 7`),
we get a projective-plane structure on points/lines both `ZMod v`, with incidence
given by `pdsMembership B v`. -/
noncomputable def pdsProjectivePlane
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (hv : 3 ≤ v)
  (hPDS : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1) :
  @Configuration.ProjectivePlane (ZMod v) (ZMod v) (pdsMembershipFlipped B v) := by
  classical
  -- Use our PDS incidence as the `Membership` instance.
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  refine
    { ----------------------------------------------------------------
      -- Nondegenerate
      ----------------------------------------------------------------
      exists_point := ?_,
      exists_line := ?_,
      eq_or_eq := ?_,
      ----------------------------------------------------------------
      -- HasPoints
      ----------------------------------------------------------------
      mkPoint := ?_,
      mkPoint_ax := ?_,
      ----------------------------------------------------------------
      -- HasLines
      ----------------------------------------------------------------
      mkLine := ?_,
      mkLine_ax := ?_,
      ----------------------------------------------------------------
      -- ProjectivePlane extra axiom: 3 points/3 lines in general position
      ----------------------------------------------------------------
      exists_config := ?_ }

  -- (1) For every line ℓ, there is a point not on ℓ.
  · -- uses your `exists_point_not_on_pdsLine`
    intro ℓ
    obtain ⟨p, hp⟩ := exists_point_not_on_pdsLine (B := B) (v := v) hPDS hv ℓ
    exact ⟨p, by simpa [pdsMembership] using hp⟩

  -- (2) For every point p, there is a line not through p.
  · -- uses your `exists_line_not_through_point`
    intro p
    obtain ⟨ℓ, hℓ⟩ := exists_line_not_through_point (B := B) (v := v) hPDS hv p
    exact ⟨ℓ, by simpa [pdsMembership] using hℓ⟩

  -- (3) If two points lie on two lines, either the points coincide or the lines do.
  · -- uses your `pds_points_lines_collapse`
    intro p₁ p₂ ℓ₁ ℓ₂ hp1l1 hp2l1 hp1l2 hp2l2
    have hp1l1' : p₁ ∈ pdsLine B v ℓ₁ := by simpa [pdsMembership] using hp1l1
    have hp2l1' : p₂ ∈ pdsLine B v ℓ₁ := by simpa [pdsMembership] using hp2l1
    have hp1l2' : p₁ ∈ pdsLine B v ℓ₂ := by simpa [pdsMembership] using hp1l2
    have hp2l2' : p₂ ∈ pdsLine B v ℓ₂ := by simpa [pdsMembership] using hp2l2
    exact pds_points_lines_collapse (B := B) (v := v) hPDS hp1l1' hp2l1' hp1l2' hp2l2'

  -- (4) For distinct lines, provide an intersection point.
  · -- `mkPoint`
    intro l₁ l₂ hneq
    exact pdsCommonPoint (B := B) (v := v) hPDS l₁ l₂ hneq

  -- (5) Show that `mkPoint` lies on both lines.
  · -- `mkPoint_ax`
    intro l₁ l₂ hneq
    -- your lemma returns both incidences directly
    have hboth :=
      pdsCommonPoint_mem_both (B := B) (v := v) hPDS (x₁ := l₁) (x₂ := l₂) hneq
    simpa [pdsMembership] using hboth

  -- (6) For distinct points, provide the line through them.
  · -- `mkLine`
    intro p₁ p₂ hneq
    exact pdsCommonLine (B := B) (v := v) hPDS p₁ p₂ hneq

  -- (7) Show that both points lie on `mkLine`.
  · -- `mkLine_ax`
    intro p₁ p₂ hneq
    have hboth :=
      pdsCommonLine_mem_both (B := B) (v := v) hPDS (x₁ := p₁) (x₂ := p₂) hneq
    simpa [pdsMembership] using hboth

  -- (8) Provide the 3-points/3-lines configuration in general position.
  · -- uses your `exists_pattern_from_config`
    rcases
      exists_pattern_from_config (B := B) (v := v) (q := q)
        hv hPDS hfin hcard hq3
      with
      ⟨p₁, p₂, p₃, l₁, l₂, l₃,
        h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩
    refine ⟨p₁, p₂, p₃, l₁, l₂, l₃,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simpa [pdsMembership]  -- rewrite incidences back to `pdsLine`-form
      using (by assumption)

/-- `x` lies on the line `y` iff `-y` lies on the line `-x`. -/
lemma mem_pdsLine_neg_swap
    (B : Set ℤ) (v : ℕ) (x y : ZMod v) :
    x ∈ pdsLine B v y ↔ (-y) ∈ pdsLine B v (-x) := by
  classical
  constructor
  · -- `x ∈ line y  ⇒  -y ∈ line (-x)`
    intro hx
    rcases (mem_pdsLine_iff_sub_coe_mem B v x y).1 hx with ⟨b, hbB, hxy⟩
    -- use `x - y = (-y) - (-x)` to flip
    have : ((-y : ZMod v) - (-x)) = (b : ZMod v) := by
      -- rewrite `(x - y)` in `hxy` to `(-y) - (-x)`
      have hswap : (x - y : ZMod v) = (-y) - (-x) := by
        simp [sub_eq_add_neg, add_comm]   -- `x - y = (-y) - (-x)`
      simpa [hswap] using hxy
    exact (mem_pdsLine_iff_sub_coe_mem B v (-y) (-x)).2 ⟨b, hbB, this⟩
  · -- `-y ∈ line (-x)  ⇒  x ∈ line y`
    intro hneg
    rcases (mem_pdsLine_iff_sub_coe_mem B v (-y) (-x)).1 hneg with ⟨b, hbB, hnegEq⟩
    -- flip back using the same identity
    have : (x - y : ZMod v) = (b : ZMod v) := by
      have hswap : (x - y : ZMod v) = (-y) - (-x) := by
        simp [sub_eq_add_neg, add_comm]
      simpa [hswap] using hnegEq
    exact (mem_pdsLine_iff_sub_coe_mem B v x y).2 ⟨b, hbB, this⟩

/-- Packed as a `Polarity`: data and incidence preservation. -/
structure Polarity (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L] : Type _ where
  φ : P ≃ L
  preserves_incidence :
    ∀ (p : P) (ℓ : L), (p ∈ ℓ) ↔ (φ.symm ℓ ∈ φ p)

/-- Absolute points of a polarity. -/
def polarity_absolutePoints
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) : Set P :=
  {p | p ∈ C.φ p}

def polarity_absoluteLines
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) : Set L :=
  {ℓ | C.φ.symm ℓ ∈ ℓ}

/-- The “negation” map `x ↦ -x` on `ZMod v` defines a polarity for the PDS geometry:
points go to lines by `x ↦ -x`, and incidence is preserved:
`x ∈ ℓ ↔ (-ℓ) ∈ (-x)` (i.e. `x` lies on line `ℓ` iff the image of `ℓ` lies on the image of `x`). -/
noncomputable def pdsNegPolarity
  {B : Set ℤ} {v q : ℕ} [NeZero v]
  (hv : 3 ≤ v)
  (hPDS : IsPerfectDifferenceSetModulo B v)
  (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1) :
  @Polarity (ZMod v) (ZMod v)
    (pdsMembershipFlipped B v)
    (pdsProjectivePlane (B := B) (v := v) (q := q) hv hPDS hfin hcard hq3)
:= by
  classical
  -- Use our incidence for `∈`.
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  -- And the PDS projective plane structure you constructed earlier.
  letI := pdsProjectivePlane (B := B) (v := v) (q := q) hv hPDS hfin hcard hq3
  refine
  { φ :=
      { toFun := fun x : ZMod v => -x
        invFun := fun ℓ : ZMod v => -ℓ
        left_inv := by intro x; simp
        right_inv := by intro ℓ; simp },
    preserves_incidence := ?pres }
  -- Incidence preservation is exactly your “neg-swap” lemma:
  -- `x ∈ ℓ ↔ (-ℓ) ∈ (-x)`.
  · intro x ℓ
    -- i.e. `x ∈ pdsLine B v ℓ ↔ (-ℓ) ∈ pdsLine B v (-x)`
    -- proved earlier as `mem_pdsLine_neg_swap`.
    -- (Provide the proof here; keeping it `sorry` per your request.)
    simpa using (mem_pdsLine_neg_swap (B := B) (v := v) x ℓ)

/-- A point `x` lies on the line `-x` iff its “double” is the residue of some `b ∈ B`. -/
lemma mem_negLine_iff_exists_coe_eq_double
    (B : Set ℤ) (v : ℕ) (x : ZMod v) :
    x ∈ pdsLine B v (-x) ↔ ∃ b ∈ B, (b : ZMod v) = x + x := by
  classical
  constructor
  · -- `→`
    intro hx
    rcases (mem_pdsLine_iff_sub_coe_mem B v x (-x)).1 hx with ⟨b, hbB, h⟩
    -- `h : x - (-x) = (b : ZMod v)` and `x - (-x) = x + x`
    have hxsub : (x - (-x) : ZMod v) = x + x := by
      simp [sub_eq_add_neg]
    refine ⟨b, hbB, ?_⟩
    -- Flip sides to match the requested orientation `(b : ZMod v) = x + x`
    simpa [hxsub] using h.symm
  · -- `←`
    intro h
    rcases h with ⟨b, hbB, hbEq⟩
    -- Want `(x - (-x)) = (b : ZMod v)`
    have hxsub : (x - (-x) : ZMod v) = x + x := by
      simp [sub_eq_add_neg]
    have : (x - (-x) : ZMod v) = (b : ZMod v) := by
      simpa [hxsub] using hbEq.symm
    exact (mem_pdsLine_iff_sub_coe_mem B v x (-x)).2 ⟨b, hbB, this⟩

/-- If `v % 2 = 1`, then for every `b : ZMod v` there is a unique `x` with `x + x = b`. -/
lemma existsUnique_double_eq_of_mod_two_eq_one
  {v : ℕ} (hv : v % 2 = 1) (b : ZMod v) :
  ∃! x : ZMod v, x + x = b := by
  classical
  -- gcd(2,v)=1 from hv
  have hodd : Odd v := Nat.odd_iff.mpr hv
  have hcop_v2 : Nat.Coprime v 2 := (Nat.coprime_two_right).mpr hodd
  have hgcd : Nat.gcd 2 v = 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one] using hcop_v2.symm

  -- Bézout over ℤ:
  have bezout_int :
      (Nat.gcd 2 v : ℤ)
        = (2 : ℤ) * Nat.gcdA 2 v + (v : ℤ) * Nat.gcdB 2 v :=
    (Nat.gcd_eq_gcd_ab 2 v)

  -- Reduce mod v
  have bezout_zmod :
      (1 : ZMod v)
        = (2 : ZMod v) * (Nat.gcdA 2 v : ZMod v)
          + (0 : ZMod v) * (Nat.gcdB 2 v : ZMod v) := by
    have : ((Nat.gcd 2 v : ℤ) : ZMod v)
              = ((2 : ℤ) : ZMod v) * (Nat.gcdA 2 v : ℤ)
                + ((v : ℤ) : ZMod v) * (Nat.gcdB 2 v : ℤ) := by
      simpa using congrArg (fun z : ℤ => (z : ZMod v)) bezout_int
    have hv0 : ((v : ℤ) : ZMod v) = 0 := by
      simp
    simpa [hgcd, hv0, two_mul, Int.cast_ofNat, Int.cast_mul, Int.cast_add] using this

  -- Right inverse of 2 (before naming u)
  have two_right_inv :
      (2 : ZMod v) * (Nat.gcdA 2 v : ZMod v) = 1 := by
    simpa [zero_mul, add_comm] using bezout_zmod.symm

  -- Name u with the right type
  set u : ZMod v := ((Nat.gcdA 2 v : ℤ) : ZMod v) with hu
  -- Specialize the right-inverse to u
  have two_right_inv' : (2 : ZMod v) * u = 1 := by
    simpa [hu] using two_right_inv

  -- Existence: x := u * b
  refine ⟨u * b, ?hx, ?uniq⟩
  · have : ((2 : ZMod v) * u) * b = b := by simp [two_right_inv', one_mul]
    -- (2*u)*b = 2*(u*b); and 2*y = y + y in ZMod
    simpa [mul_left_comm, mul_assoc, two_mul, add_mul] using this

  -- Uniqueness: if y+y=b then (2)*y=b; multiply by u on the left, use 2*u=1.
  · intro y hy
    -- rewrite to (2 : ZMod v) * y = b
    have hy2 : (2 : ZMod v) * y = b := by
      simpa [two_mul] using hy
    -- left-multiply both sides by u
    have hmul : ((2 : ZMod v) * u) * y = u * b := by
      simpa [mul_left_comm, mul_assoc] using congrArg (fun t => u * t) hy2
    -- since (2*u) = 1, this reduces to y = u * b
    have hy_eq : y = u * b := by
      simpa [two_right_inv', one_mul] using hmul
    exact hy_eq

/-- If `v % 2 = 1`, then for any set `Bc : Set (ZMod v)`,
there is a bijection between `Bc` and the set of `x : ZMod v`
such that `x + x = b` for some `b ∈ Bc`. -/
noncomputable
def equiv_Bc_solutions_double_eq_of_mod_two_eq_one
    {v : ℕ} (hv : v % 2 = 1) (Bc : Set (ZMod v)) :
    { b : ZMod v // b ∈ Bc } ≃ { x : ZMod v // ∃ b ∈ Bc, x + x = b } :=
by
  classical
  refine
    { toFun := ?toFun
      , invFun := ?invFun
      , left_inv := ?left
      , right_inv := ?right } ;
  · -- forward map: `b ↦` the unique `x` with `x + x = b`
    intro bHb
    rcases bHb with ⟨b, hb⟩
    have hExU : ∃! x : ZMod v, x + x = b :=
      existsUnique_double_eq_of_mod_two_eq_one (v:=v) hv b
    let x := Classical.choose hExU.exists
    have hx : x + x = b := Classical.choose_spec hExU.exists
    exact ⟨x, ⟨b, hb, hx⟩⟩
  · -- inverse map: `⟨x, ∃ b ∈ Bc, x + x = b⟩ ↦ ⟨x + x, _⟩`
    intro xHx
    rcases xHx with ⟨x, hx⟩
    refine ⟨x + x, ?_⟩
    -- use the existential only to prove a `Prop`
    rcases hx with ⟨b, hb, hx⟩
    simpa [hx] using hb
  · -- left inverse: `b ↦ x ↦ (x + x)` equals `b`
    intro bHb
    rcases bHb with ⟨b, hb⟩
    -- unfold the forward map's choice for this `b`
    have hExU : ∃! x : ZMod v, x + x = b :=
      existsUnique_double_eq_of_mod_two_eq_one (v:=v) hv b
    let x := Classical.choose hExU.exists
    have hx : x + x = b := Classical.choose_spec hExU.exists
    -- the inverse sends that `x` to `x + x`, which is `b`
    apply Subtype.ext
    simp [x, hx]
  · -- right inverse: `x ↦ (x + x) ↦` the unique solution for `b = x + x` is `x`
    intro xHx
    rcases xHx with ⟨x, hx⟩
    -- set `b := x + x` and bring in uniqueness for that `b`
    let b : ZMod v := x + x
    have hExU : ∃! y : ZMod v, y + y = b :=
      existsUnique_double_eq_of_mod_two_eq_one (v:=v) hv b
    -- the forward map at `b` picks the unique `y` with `y + y = b`
    let y := Classical.choose hExU.exists
    have hy : y + y = b := Classical.choose_spec hExU.exists
    -- our original `x` also satisfies `x + x = b`
    have hx' : x + x = b := by simp [b]
    have : y = x := hExU.unique hy hx'
    -- conclude equality of subtypes
    apply Subtype.ext
    simp [y, this, b]

/-- Counting corollary: the number of `x` with `x + x = b` for some `b ∈ Bc`
equals `ncard Bc`. -/
lemma ncard_solutions_double_eq_of_mod_two_eq_one
    {v : ℕ} [NeZero v] (hv : v % 2 = 1) (Bc : Set (ZMod v)) :
    ({x : ZMod v | ∃ b ∈ Bc, x + x = b}.ncard) = Bc.ncard := by
  classical
  -- convert both `Set.ncard`s to `Nat.card` on the corresponding subtypes
  have hS :
      ({x : ZMod v | ∃ b ∈ Bc, x + x = b}.ncard)
        = Nat.card {x : ZMod v // ∃ b ∈ Bc, x + x = b} := by
    simpa using (Nat.card_coe_set_eq (s := {x : ZMod v | ∃ b ∈ Bc, x + x = b})).symm
  have hB :
      Bc.ncard = Nat.card {b : ZMod v // b ∈ Bc} := by
    simpa using (Nat.card_coe_set_eq (s := Bc)).symm
  -- the subtypes are finite (since `ZMod v` is finite), and we have an `Equiv` between them
  have hc :
      Nat.card {x : ZMod v // ∃ b ∈ Bc, x + x = b}
        = Nat.card {b : ZMod v // b ∈ Bc} := by
    -- `Finite.card_eq` ↔ `Nonempty (α ≃ β)`
    -- we need a witness that the *type* `{x // …} ≃ {b // …}` is inhabited
    have h :
      Nonempty ({x : ZMod v // ∃ b ∈ Bc, x + x = b} ≃ {b : ZMod v // b ∈ Bc}) :=
      ⟨(equiv_Bc_solutions_double_eq_of_mod_two_eq_one (v:=v) hv Bc).symm⟩
    simpa using (Finite.card_eq.mpr
      ⟨(equiv_Bc_solutions_double_eq_of_mod_two_eq_one (v:=v) hv Bc).symm⟩)
  -- finish
  exact (hS.trans hc).trans hB.symm

/-- The set of residues in `ZMod v` corresponding to a set `B ⊆ ℕ`. -/
def pdsResidues (B : Set ℤ) (v : ℕ) : Set (ZMod v) :=
  (fun b : ℤ => (b : ZMod v)) '' B

/-- The canonical map from elements of `B` to their residues in `ZMod v`,
viewed as a map between subtypes. -/
def coeToResidue (B : Set ℤ) (v : ℕ) :
    {b : ℤ // b ∈ B} → {c : ZMod v // c ∈ pdsResidues B v} :=
  fun b => ⟨(b.1 : ZMod v), ⟨b.1, b.2, rfl⟩⟩

/-- In a perfect difference set mod `v`, the map `b ↦ (b : ZMod v)` from `B`
to its residue image is bijective. -/
lemma bijective_coeToResidue_of_pds
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v) :
    Function.Bijective (coeToResidue B v) := by
  classical
  refine ⟨?inj, ?surj⟩
  · -- Injective: use `coe_injOn_of_pds`.
    intro b₁ b₂ h
    -- Pull back equality on subtypes to equality of underlying values in `ZMod v`.
    have hval : ((b₁.1 : ZMod v)) = (b₂.1 : ZMod v) := by
      simpa using congrArg Subtype.val h
    -- Injectivity of coercion on `B` from the PDS hypothesis.
    have hinj : Set.InjOn (fun b : ℤ => (b : ZMod v)) B :=
      coe_injOn_of_pds (v := v) hPDS
    -- Conclude equality in `ℤ`, then lift to the subtype.
    have : b₁.1 = b₂.1 := hinj b₁.2 b₂.2 hval
    exact Subtype.ext (by simpa using this)
  · -- Surjective: by definition of `pdsResidues` as the image.
    intro y
    rcases y with ⟨c, hc⟩
    rcases hc with ⟨b, hb, rfl⟩
    refine ⟨⟨b, hb⟩, rfl⟩

/-- If `B` is a perfect difference set mod `v`, then its residue set
`pdsResidues B v` has the same cardinality as `B`. -/
lemma ncard_pdsResidues_eq_ncard
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) :
    (pdsResidues B v).ncard = B.ncard := by
  classical
  -- finiteness of the residue image (image of a finite set)
  have hfinRes : (pdsResidues B v).Finite := by
    simpa [pdsResidues] using hfin.image (fun b : ℤ => (b : ZMod v))

  -- Fintype instances for the two subtypes `↥B` and `↥(pdsResidues B v)`
  letI := hfin.fintype
  letI := hfinRes.fintype

  -- Equivalence coming from the bijection `b ↦ (b : ZMod v)`
  let e :
      {b : ℤ // b ∈ B} ≃ {c : ZMod v // c ∈ pdsResidues B v} :=
    Equiv.ofBijective (coeToResidue B v)
      (bijective_coeToResidue_of_pds (v := v) hPDS)

  -- Bridge `ncard` to `Nat.card` on subtypes
  have h₁ :
      (pdsResidues B v).ncard = Nat.card {c : ZMod v // c ∈ pdsResidues B v} := by
    simpa using (Nat.card_coe_set_eq (s := pdsResidues B v)).symm
  have h₂ :
      B.ncard = Nat.card {b : ℤ // b ∈ B} := by
    simpa using (Nat.card_coe_set_eq (s := B)).symm

  -- Equal cardinalities via the equivalence
  have hc :
      Nat.card {c : ZMod v // c ∈ pdsResidues B v}
        = Nat.card {b : ℤ // b ∈ B} := by
    -- `Fintype.card_congr e` gives equality in the `Fintype.card` world
    simpa [Nat.card_eq_fintype_card] using (Fintype.card_congr e).symm

  exact (h₁.trans hc).trans h₂.symm

/-- In the PDS geometry from `B ⊆ ℕ` modulo `v`, the absolute points
of the **negation polarity** are exactly the set `{x | x ∈ pdsLine B v (-x)}`. -/
lemma polarity_absolutePoints_pdsNegPolarity_eq_negLine
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1) :
    @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    =
    {x : ZMod v | x ∈ pdsLine B v (-x)} := rfl

/-- Membership form of `polarity_absolutePoints_pdsNegPolarity_eq_negLine`. -/
lemma mem_polarity_absolutePoints_pdsNegPolarity_iff
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
    (x : ZMod v) :
    x ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ↔ x ∈ pdsLine B v (-x) := by
  -- This is just the pointwise version of the set equality above.
  -- You can later `simp` with it after proving the equality lemma.
  simp [polarity_absolutePoints_pdsNegPolarity_eq_negLine
           (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3]

/-- In the PDS geometry from `B ⊆ ℕ` modulo `v`, a point `x` is absolute for the
**negation polarity** iff its “double” equals the residue of some `b ∈ B`. -/
lemma mem_polarity_absolutePoints_pdsNegPolarity_iff_exists_coe_eq_double
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
    (x : ZMod v) :
    x ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ↔ ∃ b ∈ B, (b : ZMod v) = x + x := by
  classical
  -- absolute points ≡ points on the line `-x`, then use the `negLine` characterization
  simpa [polarity_absolutePoints_pdsNegPolarity_eq_negLine
           (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3]
    using (mem_negLine_iff_exists_coe_eq_double B v x)

/-- If `B` is a perfect difference set mod `v`, `v ≠ 0`, and `v` is odd,
then the number of points `x : ZMod v` lying on the line `-x`
is exactly the cardinality of `B`. -/
lemma ncard_points_on_own_negLine_eq_ncardB
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hv : v % 2 = 1)
    (hfin : B.Finite) :
    ({x : ZMod v | x ∈ pdsLine B v (-x)}.ncard) = B.ncard := by
  classical
  -- rewrite membership in the “own line” set
  have h₀ :
      {x : ZMod v | x ∈ pdsLine B v (-x)}
        = {x : ZMod v | ∃ b ∈ B, (b : ZMod v) = x + x} := by
    ext x; simpa using (mem_negLine_iff_exists_coe_eq_double B v x)

  -- switch the witness from `b ∈ B` to `c ∈ pdsResidues B v`
  let Bc : Set (ZMod v) := pdsResidues B v
  have h₁ :
      {x : ZMod v | ∃ b ∈ B, (b : ZMod v) = x + x}
        = {x : ZMod v | ∃ c ∈ Bc, x + x = c} := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨b, hb, hbxx⟩
      refine ⟨(b : ZMod v), ?_, ?_⟩
      · exact ⟨b, hb, rfl⟩
      · simp [hbxx]
    · intro hx
      rcases hx with ⟨c, hc, hxx⟩
      rcases hc with ⟨b, hb, rfl⟩
      exact ⟨b, hb, hxx.symm⟩

  -- count solutions using the “doubling” counting lemma
  have hcount :
      ({x : ZMod v | ∃ c ∈ Bc, x + x = c}.ncard) = Bc.ncard := by
    simpa using (ncard_solutions_double_eq_of_mod_two_eq_one (v:=v) hv Bc)

  -- identify the residue set’s size with `B`’s size
  have hres :
      Bc.ncard = B.ncard := by
    simpa [Bc] using (ncard_pdsResidues_eq_ncard (B:=B) (v:=v) hPDS hfin)

  -- wrap up
  calc
    ({x : ZMod v | x ∈ pdsLine B v (-x)}.ncard)
        = ({x : ZMod v | ∃ b ∈ B, (b : ZMod v) = x + x}.ncard) := by
          simp [h₀]
    _   = ({x : ZMod v | ∃ c ∈ Bc, x + x = c}.ncard) := by
          simp [h₁]
    _   = Bc.ncard := hcount
    _   = B.ncard := hres

/-- In the PDS geometry from `B ⊆ ℕ` modulo `v`, if `v` is odd and `#B = q+1`,
then the set of absolute points of the negation polarity has cardinality `q+1`. -/
lemma ncard_absolutePoints_pdsNegPolarity
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v) (hodd : v % 2 = 1)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1) :
    (
      @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ).ncard
    = q + 1 := by
  classical
  -- Absolute points are exactly the set `{x | x ∈ pdsLine B v (-x)}`
  have hAbsSet :
      @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      = {x : ZMod v | x ∈ pdsLine B v (-x)} := rfl
  have h0 :
      {x : ZMod v | x ∈ pdsLine B v (-x)}
        = {x : ZMod v | ∃ b ∈ B, (b : ZMod v) = x + x} := by
    ext x; simpa using (mem_negLine_iff_exists_coe_eq_double B v x)

  -- Switch witnesses `b ∈ B` to residues `c ∈ pdsResidues B v`
  set Bc : Set (ZMod v) := pdsResidues B v with hBcDef
  have h1 :
      {x : ZMod v | ∃ b ∈ B, (b : ZMod v) = x + x}
        = {x : ZMod v | ∃ c ∈ Bc, x + x = c} := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨b, hb, hbxx⟩
      refine ⟨(b : ZMod v), ?_, ?_⟩
      · exact ⟨b, hb, rfl⟩
      · simp [hbxx]
    · intro hx
      rcases hx with ⟨c, hc, hxx⟩
      rcases hc with ⟨b, hb, rfl⟩
      exact ⟨b, hb, hxx.symm⟩

  -- Count solutions by “doubling is bijective” over odd `v`
  have hcount :
      ({x : ZMod v | ∃ c ∈ Bc, x + x = c}.ncard) = Bc.ncard := by
    simpa using (ncard_solutions_double_eq_of_mod_two_eq_one (v := v) hodd Bc)

  -- Identify residue-set size with `B.ncard`
  have hres : Bc.ncard = B.ncard := by
    simpa [hBcDef] using (ncard_pdsResidues_eq_ncard (B := B) (v := v) hPDS hfin)

  -- Wrap up
  calc
    (
      @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ).ncard
        = ({x : ZMod v | x ∈ pdsLine B v (-x)}.ncard) := by
          simp [hAbsSet]
    _   = ({x : ZMod v | ∃ b ∈ B, (b : ZMod v) = x + x}.ncard) := by
          simp [h0]
    _   = ({x : ZMod v | ∃ c ∈ Bc, x + x = c}.ncard) := by
          simp [h1]
    _   = Bc.ncard := hcount
    _   = B.ncard := hres
    _   = q + 1 := hcard

/-- **An absolute line carries exactly one absolute point.** -/
lemma polarity_absLine_unique_absPoint
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) (ℓ : L)
    (hℓ : ℓ ∈ polarity_absoluteLines C) :
    ∃! p : P, p ∈ ℓ ∧ p ∈ polarity_absolutePoints C := by
  classical
  have hPole_on_ℓ : C.φ.symm ℓ ∈ ℓ := hℓ
  refine ⟨C.φ.symm ℓ, ?ex, ?uniq⟩
  · -- existence
    have hφ : C.φ (C.φ.symm ℓ) = ℓ := by simp
    refine And.intro hPole_on_ℓ ?_
    -- absolute: p0 ∈ φ p0 since φ p0 = ℓ and p0 ∈ ℓ
    simpa [polarity_absolutePoints, hφ] using hPole_on_ℓ
  · -- uniqueness
    intro q hq
    rcases hq with ⟨hqℓ, hqabs : q ∈ C.φ q⟩
    have hPole_on_phi_q : C.φ.symm ℓ ∈ C.φ q :=
      (C.preserves_incidence q ℓ).1 hqℓ
    by_cases hqp : q = C.φ.symm ℓ
    · subst hqp
      -- then φ q = ℓ
      simp
    · -- unique line through two distinct points q and the pole
      obtain ⟨m, hm, huniq⟩ :=
        Configuration.HasLines.existsUnique_line (P:=P) (L:=L) q (C.φ.symm ℓ) hqp
      -- both φ q and ℓ contain those two points ⇒ they are that unique line
      have h1 : C.φ q = m := huniq _ ⟨hqabs, hPole_on_phi_q⟩
      have h2 : ℓ = m       := huniq _ ⟨hqℓ,  hPole_on_ℓ⟩
      have hLines : C.φ q = ℓ := by simpa [h2] using h1
      -- conclude q = pole by applying φ⁻¹
      simpa using congrArg C.φ.symm hLines

/-
The next big goal is to prove that if f is a fixed-point-free involution
on a finite set S, then the cardinality of S is even.
-/

/-- Our 2-element group (multiplicative wrapper on `ZMod 2`). -/
abbrev C2 := Multiplicative (ZMod 2)

/-- `C2` is a 2-group, via `IsPGroup.of_card` which takes a `Nat.card` hypothesis. -/
lemma isPGroup_C2 : IsPGroup 2 C2 := by
  classical
  -- First put the group order in `Nat.card` form.
  have hNat : Nat.card C2 = 2 := by
    -- `Nat.card` and `Fintype.card` agree when `[Fintype _]`.
    -- `ZMod.card 2 : Fintype.card (ZMod 2) = 2`.
    simp [C2, Nat.card_eq_fintype_card]
  -- Rewrite as a prime power.
  have hPow : Nat.card C2 = 2 ^ 1 := by simp
  -- Now apply the helper.
  simpa using (IsPGroup.of_card (p := 2) (G := C2) (n := 1) hPow)

/-- The `C2`-action induced by an involution `f : S → S`:
`1` acts as `id`, the nontrivial element acts as `f`. -/
def c2Action_smul {S : Type*} (f : S → S) : C2 → S → S :=
  fun g x => if g = (1 : C2) then x else f x

/-- For the `C2`-action defined by `c2Action_smul`, the identity element acts trivially. -/
lemma c2Action_one_smul {S : Type*} (f : S → S) (x : S) :
    c2Action_smul f (1 : C2) x = x := by
  -- `toAdd (1 : C2) = 0`
  have h : (Multiplicative.toAdd (1 : C2) : ZMod 2) = 0 := rfl
  simp [c2Action_smul]

/-- `mul_smul` special case: `g = 1`. -/
lemma c2_mul_smul_one_left
  {S : Type*} (f : S → S) (h : C2) (x : S) :
  c2Action_smul f ((1 : C2) * h) x
    = c2Action_smul f (1 : C2) (c2Action_smul f h x) := by
  -- LHS reduces to `c2Action_smul f h x`; RHS reduces to the same because `1` acts as `id`.
  simp [c2Action_smul]

/-- `mul_smul` special case: `h = 1`. -/
lemma c2_mul_smul_one_right
  {S : Type*} (f : S → S) (g : C2) (x : S) :
  c2Action_smul f (g * (1 : C2)) x
    = c2Action_smul f g (c2Action_smul f (1 : C2) x) := by
  -- LHS reduces to `c2Action_smul f g x`; RHS reduces to the same because `1` acts as `id`.
  simp [c2Action_smul]

lemma c2_mul_nontrivial_nontrivial_eq_one
  {g h : C2} (hg : g ≠ (1 : C2)) (hh : h ≠ (1 : C2)) :
  g * h = (1 : C2) := by
  classical
  -- Turn "g ≠ 1" / "h ≠ 1" into "toAdd g ≠ 0" / "toAdd h ≠ 0".
  have hg0 : Multiplicative.toAdd g ≠ (0 : ZMod 2) := by
    intro h0
    have := congrArg Multiplicative.ofAdd h0
    -- ofAdd (toAdd g) = g, ofAdd 0 = 1
    exact hg (by simpa using this)
  have hh0 : Multiplicative.toAdd h ≠ (0 : ZMod 2) := by
    intro h0
    have := congrArg Multiplicative.ofAdd h0
    exact hh (by simpa using this)

  -- In ZMod 2, nonzero elements are exactly 1. Let `decide` discharge the finite check.
  have nz_eq_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hg1 : Multiplicative.toAdd g = (1 : ZMod 2) := nz_eq_one _ hg0
  have hh1 : Multiplicative.toAdd h = (1 : ZMod 2) := nz_eq_one _ hh0

  -- Compute on the additive side: toAdd (g*h) = toAdd g + toAdd h = 1 + 1 = 0.
  have hto0 : Multiplicative.toAdd (g * h) = (0 : ZMod 2) := by
    simp [hg1, hh1, (by decide : (1 : ZMod 2) + 1 = 0)]

  -- Map back: ofAdd (toAdd (g*h)) = ofAdd 0, so g*h = 1.
  have := congrArg Multiplicative.ofAdd hto0
  simpa using this

/-- `mul_smul` special case when both group elements are non-identity,
    assuming pointwise involutivity `∀ x, f (f x) = x`. -/
lemma c2_mul_smul_nontrivial_nontrivial
  {S : Type*} (f : S → S)
  (hff : ∀ x : S, f (f x) = x)
  {g h : C2} (hg : g ≠ (1 : C2)) (hh : h ≠ (1 : C2)) (x : S) :
  c2Action_smul f (g * h) x
    = c2Action_smul f g (c2Action_smul f h x) := by
  -- In `C2`, two non-identity elements multiply to `1`.
  have hmul : g * h = (1 : C2) :=
    c2_mul_nontrivial_nontrivial_eq_one (g := g) (h := h) hg hh
  -- LHS simplifies to `x` (since `g*h = 1`);
  -- RHS simplifies to `f (f x)` (since both `g` and `h` act by `f`);
  -- then use `hff x : f (f x) = x`.
  simp [c2Action_smul, hmul, hg, hh, hff x]

/-- `mul_smul` axiom for the `C2`-action defined by `c2Action_smul`. -/
lemma c2_mul_smul
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x)
  (g h : C2) (x : S) :
  c2Action_smul f (g * h) x
    = c2Action_smul f g (c2Action_smul f h x) := by
  classical
  by_cases hg : g = (1 : C2)
  · -- reduce to the `g = 1` special case
    subst hg
    simpa using c2_mul_smul_one_left (S := S) f h x
  · by_cases hh : h = (1 : C2)
    · -- reduce to the `h = 1` special case
      subst hh
      simpa using c2_mul_smul_one_right (S := S) f g x
    · -- both non-identity: then g*h = 1, and RHS becomes f (f x) = x
      have hmul : g * h = (1 : C2) :=
        c2_mul_nontrivial_nontrivial_eq_one (g := g) (h := h) hg hh
      simp [c2Action_smul, hmul, hg, hh, hff x]

/-- If `f` is an involution (pointwise: `∀ x, f (f x) = x`), then
`c2Action_smul f` makes `S` a `MulAction` of `C2`. -/
noncomputable instance c2MulAction
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x) :
  MulAction C2 S where
  smul := c2Action_smul f
  one_smul := by
    intro x
    simpa using c2Action_one_smul (S := S) f x
  mul_smul := by
    intro g h x
    simpa using c2_mul_smul (S := S) f hff g h x

/-- For any `C2`-action on a finite type, the cardinal is congruent mod 2
to the number of fixed points. -/
lemma c2_card_modEq_card_fixedPoints_withAction
  {S : Type*} [MulAction C2 S] [Fintype S]
  [Fintype ↑(MulAction.fixedPoints C2 S)] :
  Fintype.card S ≡ Fintype.card ↑(MulAction.fixedPoints C2 S) [MOD 2] := by
  -- deduce from the generic `IsPGroup` theorem for `G=C2, p=2`
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using
    (IsPGroup.card_modEq_card_fixedPoints
      (p := 2) (G := C2) (α := S) isPGroup_C2)

/-- For the `C2`-action coming from an involution `f`, the number of points is
congruent mod 2 to the number of fixed points. -/
lemma c2_card_modEq_card_fixedPoints
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x)
  [Fintype S]
  [Fintype (↥(@MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff)))] :
  Fintype.card S ≡
    Fintype.card
      (↥(@MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff))) [MOD 2] := by
  -- Install the specific action `c2MulAction f hff` for this proof.
  letI : MulAction C2 S := c2MulAction (S := S) f hff
  -- Now `MulAction.fixedPoints C2 S` is definitionally the same as the explicit one above.
  simpa using (c2_card_modEq_card_fixedPoints_withAction (S := S))

/-- For the `C2`-action on `S` induced by `f`, if `x` is fixed by the action
(i.e. by every `g : C2`), then `x` is fixed by `f`. -/
lemma c2_action_fixed_implies_f_fixed
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x)
  {x : S}
  (hx :
    x ∈ @MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff)) :
  f x = x := by
  classical
  -- Ensure `•` uses the action induced by `f`.
  letI : MulAction C2 S := c2MulAction (S := S) f hff
  -- Unpack the fixed-point predicate.
  have hx' : ∀ g : C2, g • x = x := hx
  -- Pick the nontrivial element of `C2`.
  let t : C2 := Multiplicative.ofAdd (1 : ZMod 2)
  -- Show it's not the identity.
  have hne : t ≠ (1 : C2) := by
    intro h
    -- push the equality to the additive side
    have ht' := congrArg Multiplicative.toAdd h
    -- simplify both sides: `toAdd t = 1`, `toAdd 1 = 0`
    simp [t] at ht'   -- now: ht' : (1 : ZMod 2) = 0
  -- Apply the fixed-point condition at `t`, and compute its action.
  have htx : t • x = x := hx' t
  simpa [c2Action_smul, hne] using htx

/-- For the `C2`-action induced by `f`, if `f x = x` then every group element fixes `x`
(in terms of the action function `c2Action_smul`). -/
lemma c2_all_g_fix_of_fx_eq_x
  {S : Type*} (f : S → S) {x : S} (hfix : f x = x) :
  ∀ g : C2, c2Action_smul f g x = x := by
  intro g
  by_cases hg : g = (1 : C2)
  · -- identity case
    simp [c2Action_smul, hg]
  · -- non-identity acts by `f`
    simp [c2Action_smul, hg, hfix]

/-- For the `C2`-action on `S` induced by `f`, if `f x = x` then `x` is fixed by the action
(i.e. by every `g : C2`).  This proof reuses `c2_all_g_fix_of_fx_eq_x`. -/
lemma c2_f_fixed_implies_action_fixed
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x)
  {x : S} (hfix : f x = x) :
  x ∈ @MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff) := by
  -- ensure the `•` here is the action coming from `f`
  letI : MulAction C2 S := c2MulAction (S := S) f hff
  -- Unfold membership in the fixed-points set to the pointwise condition
  change ∀ g : C2, g • x = x
  -- Apply the helper lemma and identify `•` with `c2Action_smul f`
  intro g
  simpa using (c2_all_g_fix_of_fx_eq_x (S := S) f (x := x) hfix g)

/-- For the `C2`-action on `S` induced by `f`, a point `x` is fixed by the action
iff it is a fixed point of `f`. (Note: `hff` is only needed to build the action.) -/
lemma c2_fixedPoints_iff_pointwise
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x) (x : S) :
  x ∈ (@MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff)) ↔
    f x = x := by
  constructor
  · -- (→) fixed by the action ⇒ fixed by `f`
    intro hx
    exact c2_action_fixed_implies_f_fixed (S := S) f hff (x := x) hx
  · -- (←) fixed by `f` ⇒ fixed by the action
    intro hfix
    exact c2_f_fixed_implies_action_fixed (S := S) f hff (x := x) hfix

/-- If `f` has no fixed points (i.e. `∀ x, f x ≠ x`), then the fixed-point set for the
`C2`-action induced by `f` is empty. -/
lemma c2_fixedPoints_empty_of_no_pointwise_fixes
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x)
  (hno : ∀ x : S, f x ≠ x) :
  @MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff)
    = (∅ : Set S) := by
  -- Use the new name: `Set.eq_empty_iff_forall_notMem`
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' : f x = x :=
    (c2_fixedPoints_iff_pointwise (S := S) f hff x).mp hx
  exact (hno x) hx'

/-- If `f` has no fixed points (i.e. `∀ x, f x ≠ x`), then we have
`card S ≡ 0 [MOD 2]`. -/
lemma c2_card_modEq_zero_of_no_pointwise_fixes
  {S : Type*} (f : S → S) (hff : ∀ x : S, f (f x) = x)
  (hno : ∀ x : S, f x ≠ x)
  [Fintype S] :
  Fintype.card S ≡ 0 [MOD 2] := by
  classical
  -- The fixed-point set for this action is empty.
  have hEmpty :
      @MulAction.fixedPoints (M := C2) (α := S) _ (c2MulAction (S := S) f hff)
        = (∅ : Set S) :=
    c2_fixedPoints_empty_of_no_pointwise_fixes (S := S) f hff hno

  -- Provide a `Fintype` instance for that (empty) fixed-points subtype.
  -- We rewrite to `↥(∅ : Set S)`, which is finitely enumerable.
  haveI :
      Fintype
        (↥(@MulAction.fixedPoints (M := C2) (α := S) _
              (c2MulAction (S := S) f hff))) := by
    simpa [hEmpty] using
      (inferInstance : Fintype (↥(∅ : Set S)))

  -- Apply the specialized congruence and collapse RHS to `0`.
  have hc := c2_card_modEq_card_fixedPoints (S := S) f hff
  simpa [hEmpty] using hc

/- Done with even cardinality involution stuff and back to our
regularly-scheduled programming. -/

/-- Absolute points lying on a given line `ℓ`. -/
def absOnLine
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) (ℓ : L) : Set P :=
  {p | p ∈ ℓ ∧ p ∈ polarity_absolutePoints C}

/-- Non-absolute points on a fixed line `ℓ`. -/
def nonAbsOn
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) (ℓ : L) : Set P :=
  {p | p ∈ ℓ ∧ p ∉ C.φ p}

/-- The unique intersection of two distinct lines. -/
private noncomputable
def meet
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (ℓ m : L) (h : ℓ ≠ m) : P :=
  -- choose from the `∃`-part of the `∃!`:
  Classical.choose
    (Configuration.HasPoints.existsUnique_point (P:=P) (L:=L) ℓ m h).exists

/-- Spec for `meet`: it lies on both lines, and it is the unique such point. -/
private lemma meet_spec
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (ℓ m : L) (h : ℓ ≠ m) :
    (meet ℓ m h) ∈ ℓ ∧ (meet ℓ m h) ∈ m ∧
      ∀ q : P, q ∈ ℓ → q ∈ m → q = meet ℓ m h := by
  classical
  -- shorthand for the `∃!` package
  set E := Configuration.HasPoints.existsUnique_point (P:=P) (L:=L) ℓ m h
  -- the chosen point
  let q : P := Classical.choose E.exists
  -- its incidence facts come from `choose_spec`
  have hq : q ∈ ℓ ∧ q ∈ m := Classical.choose_spec E.exists
  rcases hq with ⟨hqℓ, hqm⟩
  -- uniqueness: any other point in both lines must equal `q`
  have huniq :
      ∀ r : P, r ∈ ℓ → r ∈ m → r = q := by
    intro r hrℓ hrm
    -- NOTE: supply the *proofs* of membership, not `r` and `q` themselves
    exact E.unique ⟨hrℓ, hrm⟩ ⟨hqℓ, hqm⟩
  -- repackage in terms of `meet`
  simpa [meet, E] using And.intro hqℓ (And.intro hqm huniq)

/-- The partner of a non-absolute point `p ∈ ℓ`: the unique point of `ℓ ∩ C.φ p`. -/
noncomputable def mate
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) (ℓ : L)
    (p : P) (hpℓ : p ∈ ℓ) (hpNon : p ∉ C.φ p) : P :=
by
  -- key: if `ℓ = C.φ p` then from `hpℓ` we get `p ∈ C.φ p`, contradicting `hpNon`
  have hneq : ℓ ≠ C.φ p := by
    intro h
    exact hpNon (by simpa [h] using hpℓ)
  exact meet ℓ (C.φ p) hneq

lemma mate_mem
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) (ℓ : L)
    {p} (hpℓ : p ∈ ℓ) (hpNon : p ∉ C.φ p) :
    mate C ℓ p hpℓ hpNon ∈ ℓ ∧ mate C ℓ p hpℓ hpNon ∈ C.φ p := by
  classical
  -- same `hneq` as above
  have hneq : ℓ ≠ C.φ p := by
    intro h
    exact hpNon (by simpa [h] using hpℓ)
  -- now use the spec of `meet`
  rcases meet_spec ℓ (C.φ p) hneq with ⟨hℓ', hm, _⟩
  -- and unfold `mate` (which was defined with this very `hneq`)
  simpa [mate, hneq] using And.intro hℓ' hm

/-- If the line `ℓ` is **not** absolute, `mate` is a fixed-point-free **involution**
on the non-absolute points of `ℓ`. -/
lemma mate_involutive_and_derangement
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    (C : Polarity P L) (ℓ : L)
    (hℓ_nonabs : ℓ ∉ polarity_absoluteLines C) :
    let S := {p : P // p ∈ nonAbsOn C ℓ}
    ∃ f : S → S,
      (∀ x, f (f x) = x) ∧ (∀ x, f x ≠ x) := by
  classical
  let S := {p : P // p ∈ nonAbsOn C ℓ}

  -- pairing map: p ↦ the unique point of ℓ ∩ φ p
  let f : S → S := fun x =>
    let p    : P := x.1
    let hpℓ  : p ∈ ℓ := x.2.1
    let hpNA : p ∉ C.φ p := x.2.2
    let q : P := mate C ℓ p hpℓ hpNA
    have hqℓ  : q ∈ ℓ     := (mate_mem C ℓ hpℓ hpNA).1
    have hqφp : q ∈ C.φ p := (mate_mem C ℓ hpℓ hpNA).2
    -- q is non-absolute; otherwise ℓ would be absolute
    have hqNA : q ∉ C.φ q := by
      intro hAbs
      -- from q ∈ φ p move across the polarity: p ∈ φ q
      have p_in_phi_q : p ∈ C.φ q := by
        have := (C.preserves_incidence q (C.φ p)).1 hqφp
        simpa using this
      -- p ≠ q because p ∉ φ p but q ∈ φ p
      have hpq : p ≠ q := by
        intro h
        have : p ∈ C.φ p := by simpa [h] using hqφp
        exact hpNA this
      -- the unique line through p and q is both ℓ and φ q
      obtain ⟨m, hm, huniq⟩ :=
        Configuration.HasLines.existsUnique_line (P:=P) (L:=L) p q hpq
      have hℓ_eq_m  : ℓ     = m := huniq _ ⟨hpℓ,  hqℓ⟩
      have hφq_eq_m : C.φ q = m := huniq _ ⟨p_in_phi_q, hAbs⟩
      -- the pole lies on φ q (from q ∈ ℓ); rewrite to conclude it lies on ℓ
      have pole_on_φq : C.φ.symm ℓ ∈ C.φ q := (C.preserves_incidence q ℓ).1 hqℓ
      have : C.φ.symm ℓ ∈ ℓ := by simpa [hℓ_eq_m, hφq_eq_m] using pole_on_φq
      exact hℓ_nonabs this
    ⟨q, And.intro hqℓ hqNA⟩

  refine ⟨f, ?hinv, ?hfix⟩

  -- involution: f (f x) = x
  · intro x
    rcases x with ⟨p, hp⟩
    rcases hp with ⟨hpℓ, hpNA⟩
    -- abbreviations
    let q : P := mate C ℓ p hpℓ hpNA
    have hqℓ  : q ∈ ℓ     := (mate_mem C ℓ hpℓ hpNA).1
    have hqφp : q ∈ C.φ p := (mate_mem C ℓ hpℓ hpNA).2
    -- q is non-absolute (same argument as above)
    have hqNA : q ∉ C.φ q := by
      intro hAbs
      have p_in_phi_q : p ∈ C.φ q := by
        have := (C.preserves_incidence q (C.φ p)).1 hqφp
        simpa using this
      have hpq : p ≠ q := by
        intro h
        have : p ∈ C.φ p := by simpa [h] using hqφp
        exact hpNA this
      obtain ⟨m, hm, huniq⟩ :=
        Configuration.HasLines.existsUnique_line (P:=P) (L:=L) p q hpq
      have hℓ_eq_m  : ℓ     = m := huniq _ ⟨hpℓ,  hqℓ⟩
      have hφq_eq_m : C.φ q = m := huniq _ ⟨p_in_phi_q, hAbs⟩
      have pole_on_φq : C.φ.symm ℓ ∈ C.φ q := (C.preserves_incidence q ℓ).1 hqℓ
      have : C.φ.symm ℓ ∈ ℓ := by simpa [hℓ_eq_m, hφq_eq_m] using pole_on_φq
      exact hℓ_nonabs this
    -- show mate q = p using uniqueness of the intersection ℓ ∩ φ q
    have p_in_phi_q : p ∈ C.φ q := by
      have := (C.preserves_incidence q (C.φ p)).1 hqφp
      simpa using this
    have hneq : ℓ ≠ C.φ q := by
      intro h
      have : C.φ.symm ℓ ∈ ℓ := by
        have := (C.preserves_incidence q ℓ).1 hqℓ
        simpa [h] using this
      exact hℓ_nonabs this
    have mate_q_eq_p : mate C ℓ q hqℓ hqNA = p := by
      rcases meet_spec ℓ (C.φ q) hneq with ⟨_, _, huniqPt⟩
      -- `huniqPt p hpℓ p_in_phi_q : p = meet …`
      simpa [mate, hneq] using (huniqPt p hpℓ p_in_phi_q).symm
    -- conclude `f (f x) = x` by value extensionality on the subtype
    apply Subtype.ext
    -- unfold both f-applications to compare values
    simp [f, q, mate_q_eq_p]

  -- derangement: f x ≠ x
  · intro x
    rcases x with ⟨p, hp⟩
    rcases hp with ⟨hpℓ, hpNA⟩
    let q : P := mate C ℓ p hpℓ hpNA
    have hqφp : q ∈ C.φ p := (mate_mem C ℓ hpℓ hpNA).2
    intro hEq
    -- compare values and rewrite the membership
    have hval : q = p := congrArg Subtype.val hEq
    have : p ∈ C.φ p := by simpa [q, hval] using hqφp
    exact hpNA this

/-- **Parity on a non-absolute line (finite-order plane).**
[A lemma in Baer.]
Assuming the projective plane has a (finite) order (i.e. the usual finite-plane setup that
provides `ProjectivePlane.order P L`), if `ℓ` is not absolute then the set of
non-absolute points on `ℓ` has even cardinality. -/
lemma even_ncard_nonAbsOn_of_order
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Finite P] [Finite L]
    (C : Polarity P L) (ℓ : L)
    (hℓ_nonabs : ℓ ∉ polarity_absoluteLines C) :
    Even ((nonAbsOn C ℓ).ncard) := by
  classical
  -- Materialize Fintype instances from `Finite`
  let _ := Fintype.ofFinite P
  let S := {p : P // p ∈ nonAbsOn C ℓ}

  -- mate gives a fixed-point-free involution on S
  obtain ⟨f, hinv, hfix⟩ :=
    mate_involutive_and_derangement (C := C) (ℓ := ℓ) hℓ_nonabs

  -- parity modulo 2 from the C2 lemma
  have hmod : Fintype.card S ≡ 0 [MOD 2] :=
    c2_card_modEq_zero_of_no_pointwise_fixes (S := S) f hinv hfix

  -- turn mod ≡ 0 into Even by unfolding definitions (avoid name-sensitive lemmas)
  have hEvenS : Even (Fintype.card S) := by
    -- `a ≡ 0 [MOD 2]` implies `2 ∣ a`
    rcases (Nat.modEq_zero_iff_dvd.mp hmod) with ⟨k, hk⟩
    -- Even n := ∃ k, n = k + k
    exact ⟨k, by simpa [Nat.two_mul] using hk⟩

  -- identify ncard of the set with the card of its subtype
  have hcard : (nonAbsOn C ℓ).ncard = Fintype.card S := by
    classical
    -- card of the subtype via a filter on univ
    have hSub :
        Fintype.card S
          = (Finset.filter (fun x : P => x ∈ nonAbsOn C ℓ) (Finset.univ : Finset P)).card :=
      Fintype.card_subtype (p := nonAbsOn C ℓ)
    -- ncard of the set via its toFinset, then identify that to a filtered-univ
    have hToFin :
        (nonAbsOn C ℓ).toFinset
          = Finset.filter (fun x : P => x ∈ nonAbsOn C ℓ) (Finset.univ : Finset P) := by
      ext x; by_cases hx : x ∈ nonAbsOn C ℓ
      · simp [Set.mem_toFinset, hx]
      · simp [Set.mem_toFinset, hx]
    have hNcard :
        (nonAbsOn C ℓ).ncard
          = (Finset.filter (fun x : P => x ∈ nonAbsOn C ℓ) (Finset.univ : Finset P)).card := by
      simpa [hToFin] using (Set.ncard_eq_toFinset_card (s := nonAbsOn C ℓ))
    -- tie the two equalities together
    exact hNcard.trans hSub.symm

  simpa [hcard] using hEvenS

lemma ncard_nonAbsOn_mod2_zero_of_order
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L) (ℓ : L)
    (hℓ_nonabs : ℓ ∉ polarity_absoluteLines C) :
    (nonAbsOn C ℓ).ncard % 2 = 0 := by
  classical
  -- subtype of non-absolute points on ℓ
  let S := {p : P // p ∈ nonAbsOn C ℓ}

  -- fixed-point-free involution on S from `mate`
  obtain ⟨f, hinv, hfix⟩ :=
    mate_involutive_and_derangement (C := C) (ℓ := ℓ) hℓ_nonabs

  -- parity modulo 2 for the subtype
  have hmod : Fintype.card S ≡ 0 [MOD 2] :=
    c2_card_modEq_zero_of_no_pointwise_fixes (S := S) f hinv hfix

  -- identify `ncard` with `Fintype.card` of the subtype
  have hcard : (nonAbsOn C ℓ).ncard = Fintype.card S := by
    -- both sides become the same filtered `univ` card
    have hSub :
        Fintype.card S
          = (Finset.filter (fun x : P => x ∈ nonAbsOn C ℓ) (Finset.univ : Finset P)).card :=
      Fintype.card_subtype (p := nonAbsOn C ℓ)
    have hToFin :
        (nonAbsOn C ℓ).toFinset
          = Finset.filter (fun x : P => x ∈ nonAbsOn C ℓ) (Finset.univ : Finset P) := by
      ext x; by_cases hx : x ∈ nonAbsOn C ℓ
      · simp [Set.mem_toFinset, hx]
      · simp [Set.mem_toFinset, hx]
    have hNcard :
        (nonAbsOn C ℓ).ncard
          = (Finset.filter (fun x : P => x ∈ nonAbsOn C ℓ) (Finset.univ : Finset P)).card := by
      simpa [hToFin] using (Set.ncard_eq_toFinset_card (s := nonAbsOn C ℓ))
    exact hNcard.trans hSub.symm

  -- from `a ≡ 0 [MOD 2]` we get `a % 2 = 0`; unfold `Nat.ModEq`
  have : (Fintype.card S) % 2 = 0 := by
    simpa [Nat.ModEq, Nat.zero_mod] using hmod

  -- rewrite back to `ncard`
  simpa [hcard] using this

/-- If the order `q` is even (i.e. `q % 2 = 0`), then **every** line carries an odd number
of absolute points (i.e. the remainder mod 2 is `1`). -/
lemma absOnLine_ncard_mod2_eq_one_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_even : Configuration.ProjectivePlane.order P L % 2 = 0)
    (ℓ : L) :
    (absOnLine C ℓ).ncard % 2 = 1 := by
  classical
  set q := Configuration.ProjectivePlane.order P L with hqdef

  have h_total :
      ({p : P | p ∈ ℓ}).ncard = q + 1 := by
    classical
    simpa [Set.ncard_subtype, hqdef]
      using Configuration.ProjectivePlane.pointCount_eq (P:=P) (l:=ℓ)

  -- You already have: q := ProjectivePlane.order P L
  have hq0 : q % 2 = 0 := by simpa [hqdef] using hq_even

  -- compute (q + 1) % 2 from q % 2 = 0
  have hq1 : (q + 1) % 2 = 1 := by
    calc
      (q + 1) % 2
          = ((q % 2) + (1 % 2)) % 2 := by
              -- (a + b) % 2 = ((a % 2) + (b % 2)) % 2
              simp [Nat.add_mod]
      _   = (0 + 1) % 2 := by simp [hq0]
      _   = 1 := by decide   -- or: by simp

  -- split cases: absolute vs non-absolute line
  by_cases hℓ_abs : ℓ ∈ polarity_absoluteLines C
  · -- absolute line ⇒ exactly one absolute point
    rcases polarity_absLine_unique_absPoint C ℓ hℓ_abs with ⟨p, hp, huniq⟩
    have hsingle : absOnLine C ℓ = {p} := by
      ext x; constructor
      · intro hx
        have hx' : x = p := huniq x ⟨hx.1, hx.2⟩
        simp [hx']
      · intro hx; rcases hx with rfl; simpa using hp
    -- ncard {p} = 1, so remainder mod 2 is 1
    simp [hsingle]

  · -- non-absolute line: partition points on ℓ into absolute vs non-absolute
    have h_nonabs_mod0 : (nonAbsOn C ℓ).ncard % 2 = 0 :=
      ncard_nonAbsOn_mod2_zero_of_order (P:=P) (L:=L) C ℓ hℓ_abs

    have hdisj : Disjoint (absOnLine C ℓ) (nonAbsOn C ℓ) := by
      refine Set.disjoint_left.mpr ?_
      intro p hpabs hpnon; exact hpnon.2 hpabs.2

    have hcover :
        (absOnLine C ℓ) ∪ (nonAbsOn C ℓ) = {p : P | p ∈ ℓ} := by
      ext p; constructor
      · intro hp; rcases hp with hp | hp <;> exact hp.1
      · intro hpℓ
        by_cases hpabs : p ∈ C.φ p
        · exact Or.inl ⟨hpℓ, hpabs⟩
        · exact Or.inr ⟨hpℓ, hpabs⟩

    -- additivity of `ncard` on a disjoint union
    have hsum :
        (absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard
          = ({p : P | p ∈ ℓ}).ncard := by
      -- via `ncard_union_add_ncard_inter` and disjointness
      have hU :=
        Set.ncard_union_add_ncard_inter (absOnLine C ℓ) (nonAbsOn C ℓ)
      have hinter_zero :
          ((absOnLine C ℓ) ∩ (nonAbsOn C ℓ)).ncard = 0 := by
        have : (absOnLine C ℓ ∩ nonAbsOn C ℓ) = (∅ : Set P) := by
          ext p; constructor
          · intro hp; exact (hdisj.le_bot hp).elim
          · intro hp; simp at hp
        simp [this]
      have : (absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard
            = ((absOnLine C ℓ) ∪ (nonAbsOn C ℓ)).ncard := by
        -- from `(s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard`
        -- rearrange and use `hinter_zero`
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hinter_zero] using hU.symm
      simpa [hcover] using this

    -- take mod 2 on both sides and simplify
    have hsum_mod :
        ((absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard) % 2
          = ((q + 1) % 2) := by
      simpa [h_total] using congrArg (fun n : ℕ => n % 2) hsum

    -- LHS: (a + b) % 2 = ((a % 2) + (b % 2)) % 2
    have : (absOnLine C ℓ).ncard % 2 = 1 := by
      -- rewrite with `Nat.add_mod`, then plug in `h_nonabs_mod0` and `hq1`
      have := hsum_mod
      -- replace RHS by `1`
      have : ((absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard) % 2 = 1 := by
        simpa [hq1]
          using this
      -- expand LHS modulo and simplify
      -- ((a%2) + (b%2)) % 2 = 1, with b%2 = 0 ⇒ (a%2) % 2 = 1 ⇒ a%2 = 1
      have := by
        simpa [Nat.add_mod, h_nonabs_mod0] using this
      -- now we have `((absOnLine C ℓ).ncard % 2) % 2 = 1`
      -- but `n % 2 < 2`, so `(n % 2) % 2 = n % 2`
      have hlt : (absOnLine C ℓ).ncard % 2 < 2 := Nat.mod_lt _ (by decide)
      simpa [Nat.mod_eq_of_lt hlt] using this
    exact this

/-- If the order `q` of a finite projective plane is odd (i.e. `q % 2 = 1`), then
a line is absolute **iff** it carries exactly one absolute point. -/
lemma absLine_iff_one_absPoint_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_odd : Configuration.ProjectivePlane.order P L % 2 = 1)
    (ℓ : L) :
    ℓ ∈ polarity_absoluteLines C ↔ (absOnLine C ℓ).ncard = 1 := by
  classical
  set q := Configuration.ProjectivePlane.order P L with hqdef

  -- Total points on a line: q + 1
  have h_total :
      ({p : P | p ∈ ℓ}).ncard = q + 1 := by
    simpa [Set.ncard_subtype, hqdef]
      using Configuration.ProjectivePlane.pointCount_eq (P:=P) (l:=ℓ)

  -- From q odd: (q + 1) is even ⇒ (q + 1) % 2 = 0
  have hq0 : (q + 1) % 2 = 0 := by
    have : q % 2 = 1 := by simpa [hqdef] using hq_odd
    calc
      (q + 1) % 2
          = ((q % 2) + (1 % 2)) % 2 := by
              simp [Nat.add_mod]
      _   = (1 + 1) % 2 := by simp [this]
      _   = 0 := by decide

  constructor
  · -- (→) absolute ⇒ exactly one absolute point
    intro hℓ_abs
    obtain ⟨p, hp, huniq⟩ := polarity_absLine_unique_absPoint C ℓ hℓ_abs
    have hsingle : absOnLine C ℓ = {p} := by
      ext x; constructor
      · intro hx
        have hx' : x = p := huniq x ⟨hx.1, hx.2⟩
        simp [hx']
      · intro hx; rcases hx with rfl; exact hp
    simp [hsingle]

  · -- (←) if exactly one absolute point lies on ℓ, then ℓ is absolute
    intro hcount
    by_contra hℓ_nonabs
    -- Non-absolute points on ℓ are even (mod 2 = 0)
    have h_nonabs_mod0 : (nonAbsOn C ℓ).ncard % 2 = 0 :=
      ncard_nonAbsOn_mod2_zero_of_order (P:=P) (L:=L) C ℓ hℓ_nonabs

    -- Partition points on ℓ into absolute vs non-absolute
    have hdisj : Disjoint (absOnLine C ℓ) (nonAbsOn C ℓ) := by
      refine Set.disjoint_left.mpr ?_
      intro p hpabs hpnon; exact hpnon.2 hpabs.2

    have hcover :
        (absOnLine C ℓ) ∪ (nonAbsOn C ℓ) = {p : P | p ∈ ℓ} := by
      ext p; constructor
      · intro hp; rcases hp with hp | hp <;> exact hp.1
      · intro hpℓ
        by_cases hpabs : p ∈ C.φ p
        · exact Or.inl ⟨hpℓ, hpabs⟩
        · exact Or.inr ⟨hpℓ, hpabs⟩

    -- Additivity of `ncard` on disjoint union
    have hsum :
        (absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard
          = ({p : P | p ∈ ℓ}).ncard := by
      have hU :=
        Set.ncard_union_add_ncard_inter (absOnLine C ℓ) (nonAbsOn C ℓ)
      have hinter_zero :
          ((absOnLine C ℓ) ∩ (nonAbsOn C ℓ)).ncard = 0 := by
        have : (absOnLine C ℓ ∩ nonAbsOn C ℓ) = (∅ : Set P) := by
          ext p; constructor
          · intro hp; exact (hdisj.le_bot hp).elim
          · intro hp; simp at hp
        simp [this]
      have : (absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard
            = ((absOnLine C ℓ) ∪ (nonAbsOn C ℓ)).ncard := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hinter_zero] using hU.symm
      simpa [hcover] using this

    -- Take mod 2 on both sides; RHS is 0 by `hq0`
    have hsum_mod :
        ((absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard) % 2 = 0 := by
      simpa [h_total, hq0] using congrArg (fun n : ℕ => n % 2) hsum

    -- LHS modulo 2 computed from the two parts
    have labs_mod : (absOnLine C ℓ).ncard % 2 = 1 := by simp [hcount]
    have hLHS1 :
        ((absOnLine C ℓ).ncard + (nonAbsOn C ℓ).ncard) % 2 = 1 := by
      simp [Nat.add_mod, labs_mod, h_nonabs_mod0]

    -- Contradiction: 1 = 0
    have h10 : (1 : ℕ) = 0 := by simp [hLHS1]
      at hsum_mod
    have ne10 : (1 : ℕ) ≠ 0 := by decide
    exact ne10 h10

/-- If the order is odd, `p` is an absolute point, `ℓ = C.φ p` is its absolute line,
and `m ≠ ℓ` is another line through `p`, then `m` is not absolute. -/
lemma nonAbs_of_absPoint_other_line
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    {p : P} (hp : p ∈ polarity_absolutePoints C)
    {ℓ m : L} (hℓ : ℓ = C.φ p) (hp_mem_m : p ∈ m) (hm_ne : m ≠ ℓ) :
    m ∉ polarity_absoluteLines C := by
  classical
  -- Suppose, for contradiction, that `m` is absolute.
  intro h_abs_m

  -- Let p' be the point `C.φ.symm m`. Since `m` is absolute, p' ∈ m.
  set p' : P := C.φ.symm m
  have hp'_mem_m : p' ∈ m := by
    -- `m` absolute means `C.φ.symm m ∈ m`.
    simpa [polarity_absoluteLines, p'] using h_abs_m

  -- From incidence preservation, `p ∈ m` implies `p' ∈ C.φ p`.
  have hp'_mem_phi_p : p' ∈ C.φ p := by
    -- `C.preserves_incidence p m : p ∈ m ↔ C.φ.symm m ∈ C.φ p`
    have h := (C.preserves_incidence p m).mp hp_mem_m
    simpa [p'] using h

  -- Since `p` is an absolute point, `p ∈ C.φ p`.
  have hp_mem_phi_p : p ∈ C.φ p := by
    -- `hp : p ∈ polarity_absolutePoints C` is definitionally `p ∈ C.φ p`.
    simpa [polarity_absolutePoints] using hp

  -- If `p' = p` then applying `C.φ` gives `m = C.φ p`, contradicting `hm_ne`.
  have hp'nep : p' ≠ p := by
    intro h
    apply hm_ne
    -- Apply `C.φ` to `p' = p`, then identify `C.φ p' = m`.
    have : m = C.φ p := by
      -- `congrArg C.φ h : C.φ p' = C.φ p`
      -- Rewrite `C.φ p'` as `m` using `p' := C.φ.symm m`.
      simpa [p', Equiv.apply_symm_apply] using congrArg C.φ h
    -- Now `m = C.φ p`, hence `m = ℓ` by `hℓ : ℓ = C.φ p`.
    simpa [hℓ] using this

  -- Uniqueness of the line through two distinct points in a projective plane:
  -- both `m` and `C.φ p` contain `p` and `p'`, hence they are equal.
  have hm_eq_phi_p : m = C.φ p := by
    classical
    -- `eq_or_eq` : (p ∈ m) → (p' ∈ m) → (p ∈ C.φ p) → (p' ∈ C.φ p) →
    --              p = p' ∨ m = C.φ p
    have h :=
      (Configuration.Nondegenerate.eq_or_eq
        (P := P) (L := L)
        (p₁ := p) (p₂ := p')
        (l₁ := m) (l₂ := C.φ p)
        hp_mem_m hp'_mem_m hp_mem_phi_p hp'_mem_phi_p)
    rcases h with hpp' | hlin
    · exact (hp'nep hpp'.symm).elim
    · exact hlin

  -- Contradiction with `m ≠ ℓ`.
  exact hm_ne (by simpa [hℓ] using hm_eq_phi_p)

/-- If the order is odd, `p` is an absolute point, `ℓ = C.φ p` is its absolute line,
and `m ≠ ℓ` is another line through `p`, then `m` contains another absolute point
distinct from `p`. -/
lemma exists_other_absPoint_on_line_through_absPoint_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_odd : Configuration.ProjectivePlane.order P L % 2 = 1)
    {p : P} (hp : p ∈ polarity_absolutePoints C)
    {ℓ m : L} (hℓ : ℓ = C.φ p) (hp_mem_m : p ∈ m) (hm_ne : m ≠ ℓ) :
    ∃ p' : P, p' ≠ p ∧ p' ∈ m ∧ p' ∈ polarity_absolutePoints C := by
  classical
  -- First, `m` is not absolute (your previous lemma).
  have h_nonabs_m : m ∉ polarity_absoluteLines C :=
    nonAbs_of_absPoint_other_line C hp hℓ hp_mem_m hm_ne

  -- Let S be the set of absolute points on m.
  set S : Set P := absOnLine C m

  -- p is an absolute point on m, so p ∈ S.
  have hpS : p ∈ S := by
    -- S = {x | x ∈ m ∧ x ∈ absolutePoints}
    simpa [S, absOnLine] using And.intro hp_mem_m hp

  -- We prove by contradiction: assume there is no other absolute point on m.
  by_contra h
  -- h : ¬ ∃ p', p' ≠ p ∧ p' ∈ m ∧ p' ∈ absolutePoints

  -- Then every element of S must be p, hence S ⊆ {p}.
  have hsubset : S ⊆ ({p} : Set P) := by
    intro x hxS
    have hx_line : x ∈ m := hxS.left
    have hx_abs  : x ∈ polarity_absolutePoints C := hxS.right
    have hx_eq_p : x = p := by
      by_contra hx_ne
      exact h ⟨x, hx_ne, hx_line, hx_abs⟩
    simp [Set.mem_singleton_iff, hx_eq_p]

  -- And since p ∈ S, we have {p} ⊆ S, hence S = {p}.
  have hsup : ({p} : Set P) ⊆ S := by
    intro x hx
    -- x = p, so x ∈ S because hpS : p ∈ S.
    simpa [Set.mem_singleton_iff] using hx ▸ hpS
  have hS : S = ({p} : Set P) := by
    exact Set.Subset.antisymm hsubset hsup

  -- Hence the number of absolute points on m is exactly 1.
  have h_ncard_one : (absOnLine C m).ncard = 1 := by
    simp [S, hS]

  -- By the odd-order characterization, that means m is absolute — contradiction.
  have : m ∈ polarity_absoluteLines C := by
    have := (absLine_iff_one_absPoint_of_order_odd C hq_odd m).mpr h_ncard_one
    exact this
  exact h_nonabs_m this

/-- In a projective plane, if `m₁ ≠ m₂` are two distinct lines through a point `p`,
and `p₁ ≠ p` lies on `m₁` while `p₂ ≠ p` lies on `m₂`, then `p₁ ≠ p₂`. -/
lemma ne_of_points_on_distinct_lines_through
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    {p p₁ p₂ : P} {m₁ m₂ : L}
    (hp_m₁ : p ∈ m₁) (hp₁_m₁ : p₁ ∈ m₁) (hp₁_ne_p : p₁ ≠ p)
    (hp_m₂ : p ∈ m₂) (hp₂_m₂ : p₂ ∈ m₂) --(hp₂_ne_p : p₂ ≠ p)
    (hm₁_ne_m₂ : m₁ ≠ m₂) :
    p₁ ≠ p₂ := by
  classical
  by_contra h
  -- From `p₂ ∈ m₂` and `p₁ = p₂`, we also have `p₁ ∈ m₂`.
  have hp₁_m₂ : p₁ ∈ m₂ := by simpa [h] using hp₂_m₂
  -- Apply the "two points on two lines" lemma:
  -- either the points are equal or the lines are equal.
  have h' :=
    (Configuration.Nondegenerate.eq_or_eq
      (P := P) (L := L)
      (p₁ := p) (p₂ := p₁)
      (l₁ := m₁) (l₂ := m₂)
      hp_m₁ hp₁_m₁ hp_m₂ hp₁_m₂)
  rcases h' with hpp | hll
  · exact hp₁_ne_p hpp.symm
  · exact hm₁_ne_m₂ hll

/-- If the order is odd and `p` is an absolute point, then there exists an injective map
from the set of lines through `p` to the set of absolute points **such that the image point
lies on the originating line**. -/
lemma exists_injective_map_linesThrough_to_absPoints_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_odd : Configuration.ProjectivePlane.order P L % 2 = 1)
    {p : P} (hp : p ∈ polarity_absolutePoints C) :
  ∃ f :
      ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C},
      Function.Injective f
      ∧ ∀ (m : {m : L // p ∈ m}), (f m : P) ∈ (m : L) := by
  classical
  -- absolute line of `p`
  let ℓ : L := C.φ p
  have hp_mem_ℓ : p ∈ ℓ := by simpa [polarity_absolutePoints] using hp

  -- Choose a *different* absolute point on a non-absolute line through `p`.
  -- This exists by your earlier lemma (use whatever name you have for it).
  have chooseOther :
      ∀ (m : {m : L // p ∈ m}), m.val ≠ ℓ →
        ∃ x : P, x ≠ p ∧ x ∈ m.val ∧ x ∈ polarity_absolutePoints C :=
    by
      intro m hne
      -- apply the lemma that guarantees another absolute point on `m` (since `m ≠ ℓ`)
      obtain ⟨x, hx_ne, hx_mem, hx_abs⟩ :=
        exists_other_absPoint_on_line_through_absPoint_of_order_odd
          C hq_odd hp (rfl : ℓ = C.φ p) (m.property) hne
      exact ⟨x, hx_ne, hx_mem, hx_abs⟩

  -- Define the map:
  --  * If m = ℓ, send m ↦ p.
  --  * If m ≠ ℓ, send m ↦ some other absolute point on m (guaranteed to be ≠ p).
  let f : ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C} :=
    fun m =>
      if h : m.val = ℓ then
        ⟨p, hp⟩
      else
        let hExist := chooseOther m h
        let x := Classical.choose hExist
        let hx := Classical.choose_spec hExist
        -- hx : x ≠ p ∧ x ∈ m.val ∧ x ∈ polarity_absolutePoints C
        ⟨x, hx.right.right⟩

  refine ⟨f, ?inj, ?onLine⟩

  -- Injectivity: if f m₁ = f m₂, then m₁ = m₂.
  · intro m₁ m₂ hEq
    by_cases h1 : m₁.val = ℓ
    · -- m₁ maps to p
      by_cases h2 : m₂.val = ℓ
      · -- both map to p → lines equal
        have : m₁.val = m₂.val := by simp [h1, h2]
        exact Subtype.ext (by simp [this])
      · -- m₂ ≠ ℓ, so f m₂ is "other" ≠ p, contradiction
        let hExist := chooseOther m₂ h2
        let x2 := Classical.choose hExist
        have hx2 :
            x2 ≠ p ∧ x2 ∈ m₂.val ∧ x2 ∈ polarity_absolutePoints C :=
          Classical.choose_spec hExist
        have hx2_abs : x2 ∈ polarity_absolutePoints C := hx2.right.right
        dsimp [f] at hEq
        have : p = x2 := by
          simpa [dif_neg h2, dif_pos h1, hx2_abs]
            using congrArg Subtype.val hEq
        exact (hx2.left this.symm).elim
    · -- m₁ ≠ ℓ
      by_cases h2 : m₂.val = ℓ
      · -- symmetric to the previous case
        let hExist1 := chooseOther m₁ h1
        let x1 := Classical.choose hExist1
        have hx1 :
            x1 ≠ p ∧ x1 ∈ m₁.val ∧ x1 ∈ polarity_absolutePoints C :=
          Classical.choose_spec hExist1
        have hx1_abs : x1 ∈ polarity_absolutePoints C := hx1.right.right
        dsimp [f] at hEq
        have : x1 = p := by
          simpa [dif_neg h1, dif_pos h2, hx1_abs]
            using congrArg Subtype.val hEq
        exact (hx1.left this).elim
      · -- both m₁, m₂ are ≠ ℓ: both map to "other" absolute points x₁, x₂
        let hExist1 := chooseOther m₁ h1
        let x1 := Classical.choose hExist1
        have hx1 :
            x1 ≠ p ∧ x1 ∈ m₁.val ∧ x1 ∈ polarity_absolutePoints C :=
          Classical.choose_spec hExist1
        have hx1_mem : x1 ∈ m₁.val := hx1.right.left
        have hx1_abs : x1 ∈ polarity_absolutePoints C := hx1.right.right

        let hExist2 := chooseOther m₂ h2
        let x2 := Classical.choose hExist2
        have hx2 :
            x2 ≠ p ∧ x2 ∈ m₂.val ∧ x2 ∈ polarity_absolutePoints C :=
          Classical.choose_spec hExist2
        have hx2_mem : x2 ∈ m₂.val := hx2.right.left
        have hx2_abs : x2 ∈ polarity_absolutePoints C := hx2.right.right

        dsimp [f] at hEq
        -- Equality of subtypes ⇒ equality of underlying values.
        have hx : x1 = x2 := by
          simpa [dif_neg h1, dif_neg h2] using congrArg Subtype.val hEq

        -- Now use uniqueness of the line through two distinct points `p` and `x1`.
        have hm_eq : m₁.val = m₂.val := by
          have h :=
            (Configuration.Nondegenerate.eq_or_eq
              (P := P) (L := L)
              (p₁ := p) (p₂ := x1)
              (l₁ := m₁.val) (l₂ := m₂.val)
              (m₁.property)            -- p ∈ m₁
              (by simpa using hx1_mem)  -- x1 ∈ m₁
              (m₂.property)             -- p ∈ m₂
              (by simpa [hx] using hx2_mem)) -- x1 ∈ m₂ via x2 and hx
          rcases h with hx1_eq_p | hlines
          · exact (hx1.left hx1_eq_p.symm).elim
          · exact hlines
        exact Subtype.ext (by simpa using hm_eq)

  -- For every m, the chosen point lies on m.
  · intro m
    by_cases h : m.val = ℓ
    · -- `f m = ⟨p, _⟩`, and `p ∈ ℓ = m.val`
      -- turn `p ∈ ℓ` into `p ∈ m.val` via `h`
      have : p ∈ m.val := by simpa [h] using hp_mem_ℓ
      -- now unfold `f` and coe; the point is `p`
      simpa [f, h] using this
    · -- `f m = ⟨x, _⟩` for some `x ∈ m.val`
      let hExist := chooseOther m h
      let x := Classical.choose hExist
      have hx :
          x ≠ p ∧ x ∈ m.val ∧ x ∈ polarity_absolutePoints C :=
        Classical.choose_spec hExist
      have hx_mem : x ∈ m.val := hx.right.left
      simpa [f, dif_neg h] using hx_mem

/-- If `f : α → β` is injective between finite types of the same cardinality,
then `f` is bijective. -/
lemma bijective_of_injective_card_eq
  {α β : Type*} [Fintype α] [Fintype β]
  (f : α → β) (hf : Function.Injective f)
  (h : Fintype.card α = Fintype.card β) :
  Function.Bijective f := by
  classical
  refine ⟨hf, ?_⟩
  -- From `card α = card β` we get an equivalence `α ≃ β`.
  obtain ⟨e⟩ := Fintype.card_eq.mp h  -- `e : α ≃ β`
  -- Make an injective endomap on `β`.
  let g : β → β := fun y => f (e.symm y)
  have hg_inj : Function.Injective g := hf.comp e.symm.injective
  -- On a finite type, injective endomap is surjective.
  have hg_surj : Function.Surjective g :=
    (Finite.injective_iff_surjective (f := g)).1 hg_inj
  -- Unpack surjectivity of `g` to get surjectivity of `f`.
  intro y
  rcases hg_surj y with ⟨y₀, hy₀⟩
  exact ⟨e.symm y₀, hy₀⟩

/-- If `Nat.card` of a type equals `x`, then `Fintype.card` also equals `x`. -/
lemma fintype_card_eq_of_nat_card_eq
  {α : Type*} [Fintype α] {x : ℕ}
  (h : Nat.card α = x) : Fintype.card α = x := by
  exact (Fintype.card_eq_nat_card (α := α)).trans h

/-- In a projective plane, the number of lines through `p` is `order + 1` (as a `Nat.card`). -/
lemma nat_card_linesThrough_eq_order_add_one
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (p : P) :
  Nat.card {m : L // p ∈ m} = Configuration.ProjectivePlane.order P L + 1 := by
  -- `lineCount L p` *is* this `Nat.card`, and `lineCount_eq` says it's `order+1`.
  simpa [Configuration.lineCount, Configuration.ProjectivePlane.order]
    using Configuration.ProjectivePlane.lineCount_eq (P := P) (L := L) (p := p)

/-- If `order = q`, then there are `q+1` lines through `p` (as a `Fintype.card`). -/
lemma card_linesThrough_eq_q_add_one
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (p : P) (q : ℕ)
    [DecidablePred (fun m : L => p ∈ m)]
    (horder : Configuration.ProjectivePlane.order P L = q) :
  Fintype.card {m : L // p ∈ m} = q + 1 := by
  -- First get the `Nat.card` statement, then switch to `Fintype.card` and rewrite `order`.
  have h₁ : Nat.card {m : L // p ∈ m} = Configuration.ProjectivePlane.order P L + 1 :=
    nat_card_linesThrough_eq_order_add_one (P := P) (L := L) p
  have h₂ : Fintype.card {m : L // p ∈ m} = Configuration.ProjectivePlane.order P L + 1 :=
    fintype_card_eq_of_nat_card_eq (α := {m : L // p ∈ m}) h₁
  simpa [horder] using h₂

/-- If a set `s` has `s.ncard = x`, then the subtype `s` has `Fintype.card = x`. -/
lemma Set.fintype_card_of_ncard_eq
  {α : Type*} (s : Set α) [Fintype s] {x : ℕ}
  (h : s.ncard = x) : Fintype.card s = x := by
  have h1 : Fintype.card s = Nat.card s :=
    Fintype.card_eq_nat_card (α := s)
  have h2 : Nat.card s = s.ncard :=
    _root_.Nat.card_coe_set_eq (s := s)
  exact (h1.trans h2).trans h

/-- If the plane has order `q`, there are `q+1` absolute points, and
`f` is an injective map from the lines through `p` to the absolute points,
then `f` is bijective. -/
lemma bijective_linesThrough_to_absPoints
  {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
  (C : Polarity P L) (q : ℕ) {p : P}
  [DecidablePred (fun m : L => p ∈ m)]
  (horder : Configuration.ProjectivePlane.order P L = q)
  (f : ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C})
  (hf : Function.Injective f)
  (hAbsPts : (polarity_absolutePoints C).ncard = q + 1) :
  Function.Bijective f := by
  classical
  -- Give `Fintype` instance for absolute points (no decidability required).
  letI : Fintype ↥(polarity_absolutePoints C) := Fintype.ofFinite _
  -- |lines through p| = q + 1
  have hLines :
      Fintype.card {m : L // p ∈ m} = q + 1 :=
    card_linesThrough_eq_q_add_one (p := p) (q := q) (horder := horder)
  -- |absolute points| = q + 1  (from `ncard` → `Fintype.card`)
  have hAbsCard :
      Fintype.card ↥(polarity_absolutePoints C) = q + 1 :=
    Set.fintype_card_of_ncard_eq (s := polarity_absolutePoints C) hAbsPts
  -- Equal cardinalities
  have hcard :
      Fintype.card {m : L // p ∈ m}
        = Fintype.card ↥(polarity_absolutePoints C) :=
    hLines.trans hAbsCard.symm
  -- Injective + equal finite cardinals ⇒ bijective
  exact bijective_of_injective_card_eq f hf hcard

/-- If the order is odd and `p` is an absolute point, then there exists a **bijective** map
from the set of lines through `p` to the set of absolute points, and the image point lies
on the originating line. We assume there are exactly `q+1` absolute points and that
`q` is the order. -/
lemma exists_bijective_map_linesThrough_to_absPoints_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_odd : q % 2 = 1)
    {p : P} (hp : p ∈ polarity_absolutePoints C)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1) :
  ∃ f :
      ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C},
      Function.Bijective f
      ∧ ∀ (m : {m : L // p ∈ m}), (f m : P) ∈ (m : L) := by
  classical
  -- decidability so `{m : L // p ∈ m}` has the canonical `Subtype.fintype`
  haveI : DecidablePred (fun m : L => p ∈ m) := Classical.decPred _
  -- 1) get an injective map with the on-line property
  obtain ⟨f, hf_inj, hf_on⟩ :=
    exists_injective_map_linesThrough_to_absPoints_of_order_odd
      C (by simpa [horder] using hq_odd) hp
  -- 2) upgrade to bijection using equal cardinalities
  have hbij :
      Function.Bijective f :=
    bijective_linesThrough_to_absPoints
      C q (p := p) (horder := horder) (f := f) (hf := hf_inj)
      (hAbsPts := hAbsPts)
  exact ⟨f, hbij, hf_on⟩

/-- From the bijection `linesThrough p ↔ absolute points` (with the on-line property),
build the inverse bijection `absolute points ↔ linesThrough p`, which sends each absolute
point to a line **containing** it. -/
lemma exists_bijective_map_absPoints_to_linesThrough_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_odd : q % 2 = 1)
    {p : P} (hp : p ∈ polarity_absolutePoints C)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    [DecidablePred (fun m : L => p ∈ m)] :
  ∃ f :
      ({x : P // x ∈ polarity_absolutePoints C}) → {m : L // p ∈ m},
      Function.Bijective f
      ∧ ∀ (x : {x : P // x ∈ polarity_absolutePoints C}), (x : P) ∈ (f x : L) := by
  letI : Fintype ↥(polarity_absolutePoints C) := Fintype.ofFinite _

  obtain ⟨f, hf_bij, hf_on⟩ :=
    exists_bijective_map_linesThrough_to_absPoints_of_order_odd
      (C := C) (q := q) (horder := horder) (hq_odd := hq_odd) (hp := hp)
      (hAbsPts := hAbsPts)

  -- Package `f` as an equivalence and take its inverse.
  let e : ({m : L // p ∈ m}) ≃ {x : P // x ∈ polarity_absolutePoints C} :=
    Equiv.ofBijective f hf_bij
  let g : ({x : P // x ∈ polarity_absolutePoints C}) → {m : L // p ∈ m} := e.symm

  -- e : linesThrough p ≃ absPoints,  g := e.symm
  refine ⟨g, e.symm.bijective, ?_⟩
  intro x
  -- `e.right_inv x : e (g x) = x`
  have hx₀ : e (g x) = x := e.right_inv x
  -- move to underlying points in `P`
  have hx' : (f (g x) : P) = (x : P) := by
    change (e (g x) : P) = (x : P)
    exact congrArg Subtype.val hx₀
  -- rewrite the membership statement
  simpa [hx'] using hf_on (g x)

/-- If `f` sends each absolute point `x` to a line through `p` that contains `x`,
then for any absolute point `q`, the line `f ⟨q, _⟩` contains both `p` and `q`. -/
lemma image_line_contains_p_and_q'
  {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
  (C : Polarity P L) (p q : P)
  (f : ({x : P // x ∈ polarity_absolutePoints C}) → {m : L // p ∈ m})
  (hf_on : ∀ x, (x : P) ∈ (f x : L))
  (hq_abs : q ∈ polarity_absolutePoints C) :
  p ∈ (f ⟨q, hq_abs⟩ : L) ∧ q ∈ (f ⟨q, hq_abs⟩ : L) := by
  -- `p` lies on the image line by the subtype property of `f ⟨q, hq_abs⟩`.
  have hp_on : p ∈ (f ⟨q, hq_abs⟩ : L) := (f ⟨q, hq_abs⟩).property
  -- `q` lies on the image line by the on-line hypothesis `hf_on`.
  have hq_on : q ∈ (f ⟨q, hq_abs⟩ : L) := by
    simpa using (hf_on ⟨q, hq_abs⟩)
  exact ⟨hp_on, hq_on⟩

/-- **Uniqueness of the other absolute point on a line through an absolute point**.
If the projective plane has odd order `q`, there are exactly `q+1` absolute points,
and `p` is an absolute point, then on any line `ℓ` through `p` there is at most one
other absolute point. In particular, if `p₁` and `p₂` are absolute points on `ℓ`
with `p₁ ≠ p` and `p₂ ≠ p`, then `p₁ = p₂`. -/
lemma unique_other_absPoint_on_line_through_absPoint_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_odd : q % 2 = 1)
    {p : P} (hp : p ∈ polarity_absolutePoints C)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    (ℓ : L) (hpℓ : p ∈ ℓ)
    {p₁ p₂ : P}
    (hp₁_abs : p₁ ∈ polarity_absolutePoints C) (hp₁ℓ : p₁ ∈ ℓ) (hp₁_ne : p₁ ≠ p)
    (hp₂_abs : p₂ ∈ polarity_absolutePoints C) (hp₂ℓ : p₂ ∈ ℓ) (hp₂_ne : p₂ ≠ p) :
  p₁ = p₂ := by
  classical
  -- We will use the bijection `abs points ↔ lines through p` with the on-line property.
  haveI : DecidablePred (fun m : L => p ∈ m) := Classical.decPred _
  obtain ⟨g, hbij, h_on⟩ :=
    exists_bijective_map_absPoints_to_linesThrough_of_order_odd
      (C := C) (q := q) (horder := horder) (hq_odd := hq_odd)
      (hp := hp) (hAbsPts := hAbsPts)

  -- Package the absolute points `p₁, p₂` as subtypes.
  let x₁ : {x : P // x ∈ polarity_absolutePoints C} := ⟨p₁, hp₁_abs⟩
  let x₂ : {x : P // x ∈ polarity_absolutePoints C} := ⟨p₂, hp₂_abs⟩

  -- Show that `g x₁` is exactly the line `ℓ` (equality in the subtype comes from equality of vals).
  have g_x₁_eq : (g x₁ : L) = ℓ := by
    -- `p ∈ g x₁` from subtype property; `p₁ ∈ g x₁` from the on-line property.
    have hp_on : p ∈ (g x₁ : L) := (g x₁).property
    have hp₁_on : p₁ ∈ (g x₁ : L) := by simpa using h_on x₁
    -- Uniqueness of the line through the two distinct points `p` and `p₁`.
    -- Either `p₁ = p` (ruled out) or the two lines coincide.
    have h :=
      (Configuration.Nondegenerate.eq_or_eq
        (P := P) (L := L)
        (p₁ := p) (p₂ := p₁)
        (l₁ := (g x₁ : L)) (l₂ := ℓ)
        (hp_on) (by simpa using hp₁_on)
        (hpℓ)   (hp₁ℓ))
    rcases h with h_eq | h_lines
    · exact (hp₁_ne h_eq.symm).elim
    · exact h_lines

  -- Similarly for `g x₂`.
  have g_x₂_eq : (g x₂ : L) = ℓ := by
    have hp_on : p ∈ (g x₂ : L) := (g x₂).property
    have hp₂_on : p₂ ∈ (g x₂ : L) := by simpa using h_on x₂
    have h :=
      (Configuration.Nondegenerate.eq_or_eq
        (P := P) (L := L)
        (p₁ := p) (p₂ := p₂)
        (l₁ := (g x₂ : L)) (l₂ := ℓ)
        (hp_on) (by simpa using hp₂_on)
        (hpℓ)   (hp₂ℓ))
    rcases h with h_eq | h_lines
    · exact (hp₂_ne h_eq.symm).elim
    · exact h_lines

  -- From `(g x₁ : L) = ℓ = (g x₂ : L)`, we get equality in the subtype:
  have g_x₁_eq_g_x₂ : g x₁ = g x₂ := by
    apply Subtype.ext
    simp [g_x₁_eq, g_x₂_eq]

  -- Injectivity of `g` forces `x₁ = x₂`, hence `p₁ = p₂`.
  have inj := hbij.1
  have : x₁ = x₂ := inj g_x₁_eq_g_x₂
  simpa [x₁, x₂] using congrArg Subtype.val this

/-- If `q` is odd and there are exactly `q+1` absolute points, then no line contains
three *distinct* absolute points. Equivalently, among any three absolute points on a line,
two must be equal. -/
lemma no_three_distinct_absPoints_on_a_line_of_order_odd
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L) (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_odd : q % 2 = 1)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1) :
  ∀ ℓ : L, ∀ {a b c : P},
    a ∈ polarity_absolutePoints C → b ∈ polarity_absolutePoints C →
    c ∈ polarity_absolutePoints C → a ∈ ℓ → b ∈ ℓ → c ∈ ℓ →
    a = b ∨ a = c ∨ b = c := by
  classical
  intro ℓ a b c ha hb hc haℓ hbℓ hcℓ
  -- If `a=b` or `a=c`, done.
  by_cases h_ab : a = b
  · exact Or.inl h_ab
  by_cases h_ac : a = c
  · exact Or.inr (Or.inl h_ac)
  -- Otherwise, use uniqueness of the *other* absolute point on a line through `a`.
  have h_unique :
      b = c :=
    unique_other_absPoint_on_line_through_absPoint_of_order_odd
      (C := C) (q := q) (horder := horder) (hq_odd := hq_odd)
      (p := a) (hp := ha) (hAbsPts := hAbsPts)
      (ℓ := ℓ) (hpℓ := haℓ)
      (p₁ := b) (hp₁_abs := hb) (hp₁ℓ := hbℓ)
        (hp₁_ne := by intro h; exact h_ab (h.symm))
      (p₂ := c) (hp₂_abs := hc) (hp₂ℓ := hcℓ)
        (hp₂_ne := by intro h; exact h_ac (h.symm))
  exact Or.inr (Or.inr h_unique)

/-- If the double of `x` (as a residue mod `v`) is represented by some `b ∈ B`,
then `x` is an absolute point for the negation polarity in the PDS geometry
from `B ⊆ ℕ` modulo `v`. -/
lemma mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
    (x : ZMod v)
    (hxx : ∃ b ∈ B, (b : ZMod v) = x + x) :
    x ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3) := by
  classical
  -- convert the hypothesis to membership in the line `-x`
  have hxline : x ∈ pdsLine B v (-x) :=
    (mem_negLine_iff_exists_coe_eq_double B v x).2 hxx
  -- identify absolute points with `{x | x ∈ pdsLine B v (-x)}`
  simpa [polarity_absolutePoints_pdsNegPolarity_eq_negLine
           (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3,
         Set.mem_setOf_eq]
    using hxline

/-- If `1, 2, 4, 8 ∈ B`, then:
1. the points `1, 2, 4 : ZMod v` are **absolute** for the negation polarity, and
2. they lie on the **same line**, namely `pdsLine B v 0`. -/
lemma abs_1_2_4_and_collinear_of_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    (1 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ∧
    (2 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ∧
    (4 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ∧
    (1 : ZMod v) ∈ pdsLine B v 0
    ∧ (2 : ZMod v) ∈ pdsLine B v 0
    ∧ (4 : ZMod v) ∈ pdsLine B v 0 := by
  classical
  -- (A) absoluteness
  have h_abs1 :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (1 : ZMod v))
      ⟨2, h2, by norm_num⟩
  have h_abs2 :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (2 : ZMod v))
      ⟨4, h4, by norm_num⟩
  have h_abs4 :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (4 : ZMod v))
      ⟨8, h8, by norm_num⟩
  -- (B) collinearity
  have h_on1 : (1 : ZMod v) ∈ pdsLine B v 0 := ⟨1, h1, by simp⟩
  have h_on2 : (2 : ZMod v) ∈ pdsLine B v 0 := ⟨2, h2, by simp⟩
  have h_on4 : (4 : ZMod v) ∈ pdsLine B v 0 := ⟨4, h4, by simp⟩
  exact ⟨h_abs1, h_abs2, h_abs4, h_on1, h_on2, h_on4⟩

/-- In the PDS projective plane from `B ⊆ ℕ` modulo `v` with `#B = q+1`,
the line `ℓ = 0` has exactly `q+1` points. -/
lemma pointCount_pdsLine_zero_eq_q_add_one
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1) :
    @Configuration.pointCount (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (0 : ZMod v)
    = q + 1 := by
  classical
  -- From your line-size lemma:
  have h_line : (pdsLine B v (0 : ZMod v)).ncard = q + 1 :=
    ncard_pdsLine_of_card (B := B) (v := v) (q := q) hPDS hfin hcard (0 : ZMod v)

  -- Turn `Set.ncard` into `Fintype.card` for the subtype over the *explicit* predicate
  have hF :
      Fintype.card { p : ZMod v // p ∈ pdsLine B v (0 : ZMod v) } = q + 1 := by
    simpa using
      (Set.fintype_card_of_ncard_eq (s := pdsLine B v (0 : ZMod v)) (x := q + 1) h_line)

  -- Rewrite `pointCount` to that same `Fintype.card` by unfolding the PDS incidence
  simpa [Configuration.pointCount, Nat.card_eq_fintype_card,
         pdsMembershipFlipped, pdsMembership]
    using hF

/-- The projective plane `pdsProjectivePlane` built from a perfect difference set
`B ⊆ ℕ` modulo `v`, with `#B = q+1`, has order `q`. -/
lemma pdsProjectivePlane_order_eq
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1) :
    @Configuration.ProjectivePlane.order (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    = q := by
  classical
  -- put instances in scope
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  -- (1) Your concrete point count on ℓ = 0
  have h_pc0 :
      @Configuration.pointCount (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v) (0 : ZMod v) = q + 1 :=
    pointCount_pdsLine_zero_eq_q_add_one
      (B := B) (v := v) (q := q) hPDS hfin hcard

  -- (2) General projective-plane identity: every line has `order + 1` points
  have h_pc0_eq :
      Configuration.pointCount (P := ZMod v) (l := (0 : ZMod v))
      = Configuration.ProjectivePlane.order (ZMod v) (ZMod v) + 1 :=
    Configuration.ProjectivePlane.pointCount_eq
      (P := ZMod v) (L := ZMod v) (l := (0 : ZMod v))

  -- (3) Compare and cancel `+ 1`
  have hsucc :
      Configuration.ProjectivePlane.order (ZMod v) (ZMod v) + 1 = q + 1 := by
    simpa [h_pc0] using h_pc0_eq.symm
  exact Nat.succ.inj hsucc

/-- In the PDS geometry from `B ⊆ ℕ` modulo `v`, if
- `IsPerfectDifferenceSetModulo B v`,
- `#B = q+1` with `3 ≤ q+1`,
- `q` is odd,
- and `1,2,4,8 ∈ B`,

then among the residues `1,2,4 : ZMod v` at least two are equal (so they cannot be
three *distinct* absolute points on the same line). -/
lemma two_of_one_two_four_equal_mod_v_of_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    (hq_odd : q % 2 = 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    (1 : ZMod v) = 2 ∨ (1 : ZMod v) = 4 ∨ (2 : ZMod v) = 4 := by
  classical
  -- Put the PDS incidence and plane instances in scope.
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  -- `v` is odd from the PDS size relation.
  have hodd : v % 2 = 1 :=
    IsPerfectDifferenceSetModulo.mod_two_eq_one (B := B) (v := v) (q := q) hPDS hfin hcard

  -- Number of absolute points of the negation polarity is `q + 1`.
  have hAbsPtsCard :
      (polarity_absolutePoints
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)).ncard
      = q + 1 :=
    ncard_absolutePoints_pdsNegPolarity
      (B := B) (v := v) (q := q) hv3 hodd hPDS hfin hcard hq3

  -- `1,2,4` are absolute and lie on the same line (`ℓ = 0`).
  rcases
    abs_1_2_4_and_collinear_of_mem_1_2_4_8
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 h1 h2 h4 h8
    with ⟨hAbs1, hAbs2, hAbs4, hℓ1, hℓ2, hℓ4⟩

  -- The PDS projective plane has order `q`.
  have horder :
      Configuration.ProjectivePlane.order (ZMod v) (ZMod v) = q :=
    pdsProjectivePlane_order_eq (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3

  -- Apply the “no three distinct absolute points on a line (odd order)” lemma
  -- with C = pdsNegPolarity, ℓ = 0, and a=1, b=2, c=4.
  have :=
    no_three_distinct_absPoints_on_a_line_of_order_odd
      (P := ZMod v) (L := ZMod v)
      (C := pdsNegPolarity (B := B) (v := v) (q := q)
              hv3 hPDS hfin hcard hq3)
      (q := q)
      horder hq_odd hAbsPtsCard
      (0 : ZMod v)
      (a := (1 : ZMod v)) (b := (2 : ZMod v)) (c := (4 : ZMod v))
      hAbs1 hAbs2 hAbs4 hℓ1 hℓ2 hℓ4

  -- The lemma gives exactly the desired disjunction.
  exact this

/-- If a finite set `B : Set ℕ` has size `q + 1` and contains `1, 2, 4, 8`,
then `q ≥ 3`. -/
lemma q_ge_three_of_mem_1_2_4_8
    {B : Set ℤ} {q : ℕ}
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    3 ≤ q := by
  classical
  let T : Finset ℤ := {1, 2, 4, 8}
  have hT_card : T.card = 4 := by simp [T]

  -- `T ⊆ hfin.toFinset`
  have hT_subset : T ⊆ hfin.toFinset := by
    intro x hx
    have hx_cases : x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 := by
      simpa [T, Finset.mem_insert, Finset.mem_singleton] using hx
    have hxB : x ∈ B := by
      rcases hx_cases with rfl | rfl | rfl | rfl
      · simpa using h1
      · simpa using h2
      · simpa using h4
      · simpa using h8
    simpa [Set.mem_toFinset] using hxB

  -- From the subset, deduce `4 ≤ (hfin.toFinset).card`
  have h4le_toFin : 4 ≤ (hfin.toFinset).card := by
    have := Finset.card_mono hT_subset
    simpa [hT_card] using this

  -- Bridge `ncard` and `toFinset.card`
  have hBcard : B.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card (α := ℤ) (s := B) (hs := hfin)

  -- Hence `4 ≤ B.ncard`
  have h4le_ncard : 4 ≤ B.ncard := by
    simpa [hBcard] using h4le_toFin

  -- And thus `4 ≤ q + 1`, i.e. `3 ≤ q`
  have : 4 ≤ q + 1 := by simpa [hcard] using h4le_ncard
  exact Nat.succ_le_succ_iff.mp this

/-- If a finite set `B : Set ℤ` has size `x` and contains `1`,
then `x ≥ 1`. -/
lemma x_ge_1_of_mem_1
    {B : Set ℤ} {x : ℕ}
    (hfin : B.Finite)
    (hcard : B.ncard = x)
    (h1 : 1 ∈ B) :
    1 ≤ x := by
  classical
  let T : Finset ℤ := {1}
  have hT_card : T.card = 1 := by simp [T]

  -- `T ⊆ hfin.toFinset`
  have hT_subset : T ⊆ hfin.toFinset := by
    intro x hx
    have hx_cases : x = 1 := by
      simpa [T, Finset.mem_insert, Finset.mem_singleton] using hx
    have hxB : x ∈ B := by
      rcases hx_cases with rfl
      · simpa using h1
    simpa [Set.mem_toFinset] using hxB

  -- From the subset, deduce `1 ≤ (hfin.toFinset).card`
  have h1le_toFin : 1 ≤ (hfin.toFinset).card := by
    have := Finset.card_mono hT_subset
    simpa [hT_card] using this

  -- Bridge `ncard` and `toFinset.card`
  have hBcard : B.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card (α := ℤ) (s := B) (hs := hfin)

  -- Hence `1 ≤ B.ncard`
  have h1le_ncard : 1 ≤ B.ncard := by
    simpa [hBcard] using h1le_toFin

  -- And thus `1 ≤ x`
  have : 1 ≤ x := by simpa [hcard] using h1le_ncard
  exact this

/-- If `4 ≤ v`, then `1` is not congruent to `2` modulo `v`. -/
lemma not_modEq_one_two_of_le_four {v : ℕ} (hv : 4 ≤ v) :
    ¬ (1 ≡ 2 [MOD v]) := by
  intro h
  -- From `4 ≤ v` we get `2 < v`
  have hbv : 2 < v := lt_of_lt_of_le (by decide : 2 < 4) hv
  -- `mod_ne_of_lt_chain` says `1 % v ≠ 2 % v`
  have hneq : 1 % v ≠ 2 % v :=
    mod_ne_of_lt_chain (a := 1) (b := 2) (v := v)
      (hab := by decide) (hbv := hbv)
  -- But `1 ≡ 2 [MOD v]` means `1 % v = 2 % v`
  have heq : 1 % v = 2 % v := by simpa [Nat.ModEq] using h
  exact hneq heq

/-- If `4 ≤ v`, then `1` is not congruent to `4` modulo `v`. -/
lemma not_modEq_one_four_of_le_four {v : ℕ} (hv : 4 ≤ v) :
    ¬ (1 ≡ 4 [MOD v]) := by
  intro h
  have hrem : 1 % v = 4 % v := by simpa [Nat.ModEq] using h
  -- Split into `v = 4` or `4 < v`.
  rcases lt_or_eq_of_le hv with hlt | rfl
  · -- `4 < v`: use `mod_ne_of_lt_chain` with `a=1`, `b=4`
    have : 1 % v ≠ 4 % v :=
      mod_ne_of_lt_chain (a := 1) (b := 4) (v := v)
        (hab := by decide) (hbv := hlt)
    exact this hrem
  · -- `v = 4`: remainders are `1` and `0`
    -- `simp` computes both remainders directly.
    simp at hrem

/-- If `4 ≤ v`, then `2` is not congruent to `4` modulo `v`. -/
lemma not_modEq_two_four_of_le_four {v : ℕ} (hv : 4 ≤ v) :
    ¬ (2 ≡ 4 [MOD v]) := by
  intro h
  have hrem : 2 % v = 4 % v := by simpa [Nat.ModEq] using h
  rcases lt_or_eq_of_le hv with hlt | rfl
  · -- `4 < v`: use `mod_ne_of_lt_chain` with `a=2`, `b=4`
    have : 2 % v ≠ 4 % v :=
      mod_ne_of_lt_chain (a := 2) (b := 4) (v := v)
        (hab := by decide) (hbv := hlt)
    exact this hrem
  · -- `v = 4`: remainders are `2` and `0`
    simp at hrem

/-- If `4 ≤ v`, then `1, 2, 4 : ZMod v` are pairwise distinct. -/
lemma one_two_four_pairwise_distinct_mod {v : ℕ} (hv : 4 ≤ v) :
    (1 : ZMod v) ≠ 2 ∧ (1 : ZMod v) ≠ 4 ∧ (2 : ZMod v) ≠ 4 := by
  -- (1 ≠ 2)
  have h12 : (1 : ZMod v) ≠ 2 := by
    intro h
    have h' : ((1 : ℕ) : ZMod v) = (2 : ℕ) := by simpa using h
    have : 1 ≡ 2 [MOD v] := (ZMod.natCast_eq_natCast_iff 1 2 v).1 h'
    exact (not_modEq_one_two_of_le_four hv) this
  -- (1 ≠ 4)
  have h14 : (1 : ZMod v) ≠ 4 := by
    intro h
    have h' : ((1 : ℕ) : ZMod v) = (4 : ℕ) := by simpa using h
    have : 1 ≡ 4 [MOD v] := (ZMod.natCast_eq_natCast_iff 1 4 v).1 h'
    exact (not_modEq_one_four_of_le_four hv) this
  -- (2 ≠ 4)
  have h24 : (2 : ZMod v) ≠ 4 := by
    intro h
    have h' : ((2 : ℕ) : ZMod v) = (4 : ℕ) := by simpa using h
    have : 2 ≡ 4 [MOD v] := (ZMod.natCast_eq_natCast_iff 2 4 v).1 h'
    exact (not_modEq_two_four_of_le_four hv) this
  exact ⟨h12, h14, h24⟩

/-- If `B` is a perfect difference set modulo `v`, `B` is finite of size `q+1`,
and `1,2,4,8 ∈ B`, then `q` is even.
From your ingredients, we first show `q % 2 = 0`. -/
lemma q_mod_two_eq_zero_of_pds_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    q % 2 = 0 := by
  -- First, `q ≥ 3` from the 4 memberships.
  have hq_ge3 : 3 ≤ q :=
    q_ge_three_of_mem_1_2_4_8 (B := B) (q := q) hfin hcard h1 h2 h4 h8
  -- `v = q^2 + q + 1`
  have hv_eq : q * q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ
      (B := B) (v := v) (q := q) hPDS hfin hcard
  -- From `q ≥ 3`, we get `13 ≤ q^2 + q + 1`, hence `4 ≤ v` and `3 ≤ v`.
  have h9 : 9 ≤ q*q := by
    have := Nat.mul_le_mul hq_ge3 hq_ge3
    -- `3*3 ≤ q*q`
    simpa using this
  have h12 : 12 ≤ q*q + q := by
    -- `9 + 3 ≤ q*q + q`
    simpa using Nat.add_le_add h9 hq_ge3
  have hv_ge13 : 13 ≤ v := by
    -- `13 ≤ q*q + q + 1 = v`
    simpa [hv_eq] using Nat.succ_le_succ h12
  have hv4 : 4 ≤ v := le_trans (by decide : 4 ≤ 13) hv_ge13
  have hv3 : 3 ≤ v := le_trans (by decide : 3 ≤ 4) hv4
  -- Also `3 ≤ q+1` from `3 ≤ q`
  have hq3 : 3 ≤ q + 1 := le_trans hq_ge3 (Nat.le_succ _)

  -- Now split `q % 2` into `0` or `1` and rule out the `1` case.
  refine (Nat.mod_two_eq_zero_or_one q).elim (fun h0 => h0) (fun h1mod => ?_)
  -- If `q % 2 = 1`, your lemma forces an equality among `1,2,4 : ZMod v`.
  have hEq :=
    two_of_one_two_four_equal_mod_v_of_mem_1_2_4_8
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 h1mod h1 h2 h4 h8
  -- But for `4 ≤ v`, those three residues are pairwise distinct.
  have hpair := one_two_four_pairwise_distinct_mod (v := v) hv4
  rcases hpair with ⟨h12ne, h14ne, h24ne⟩
  rcases hEq with h12 | h14 | h24
  · exact (h12ne h12).elim
  · exact (h14ne h14).elim
  · exact (h24ne h24).elim

/-- If `B` is a perfect difference set modulo `v`, `B` is finite of size `q+1`,
and `1,2,4,8 ∈ B`, then `q` is even.  (Packaged as `Even q`.) -/
lemma q_even_of_pds_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    Even q := by
  -- `Even q ↔ q % 2 = 0`
  exact (Nat.even_iff.mpr
    (q_mod_two_eq_zero_of_pds_mem_1_2_4_8
      (B := B) (v := v) (q := q) hPDS hfin hcard h1 h2 h4 h8))

/-- If `q` is prime and `3 ≤ q`, then `q` is *not* even. -/
lemma not_even_of_prime_of_three_le {q : ℕ}
    (hq : Nat.Prime q) (h3 : 3 ≤ q) : ¬ Even q := by
  -- If `q` were even, then `2 ∣ q`, so by primality we would have `q = 2`,
  -- contradicting `3 ≤ q`.
  intro hEven
  -- From evenness we get `2 ∣ q`.
  have h2dvd : 2 ∣ q := by
    rcases hEven with ⟨k, hk⟩
    exact ⟨k, by simp [hk, two_mul]⟩
  -- For a prime, any divisor is `1` or the number itself.
  have h2eq : 2 = q := by
    rcases (Nat.dvd_prime hq).1 h2dvd with h2eq1 | h2eq2
    · cases h2eq1 -- impossible: `2 = 1`
    · exact h2eq2
  -- But `3 ≤ q` implies `2 < q`, contradiction with `2 = q`.
  have hlt : 2 < q := Nat.lt_of_lt_of_le (by decide : 2 < 3) h3
  exact (ne_of_gt hlt) h2eq.symm

/-- If `p^2 + p + 1 = q^2 + q + 1`, then `p = q`. -/
lemma eq_of_sq_add_linear_succ_eq {p q : ℕ}
    (h : p * p + p + 1 = q * q + q + 1) : p = q := by
  -- cancel `+ 1`
  have h0 : p * p + p = q * q + q :=
    Nat.add_right_cancel (by simpa [Nat.add_assoc] using h)
  -- move to `ℤ`
  have hZ : (p : ℤ) * (p : ℤ) + p = (q : ℤ) * (q : ℤ) + q := by
    exact_mod_cast h0
  -- subtract and factor over `ℤ`
  have hz : (p : ℤ) * p + p - ((q : ℤ) * q + q) = 0 := by
    simpa using sub_eq_zero.mpr hZ
  have hfac : ((p : ℤ) - q) * ((p : ℤ) + q + 1) = 0 := by
    have hf :
        (p : ℤ) * p + p - ((q : ℤ) * q + q)
          = ((p : ℤ) - q) * ((p : ℤ) + q + 1) := by
      ring
    simpa [hf] using hz
  -- product zero ⇒ one factor zero
  rcases mul_eq_zero.mp hfac with hsub | hsum
  · -- `p - q = 0` ⇒ `p = q`
    exact Int.ofNat.inj (sub_eq_zero.mp hsub)
  · -- `(p : ℤ) + q + 1 = 0` is impossible for naturals
    have : 0 < (p : ℤ) + q + 1 := by
      have hnonneg : 0 ≤ (p : ℤ) + q :=
        add_nonneg (by exact_mod_cast (Nat.zero_le p))
                   (by exact_mod_cast (Nat.zero_le q))
      exact add_pos_of_nonneg_of_pos hnonneg (by decide : (0 : ℤ) < 1)
    -- turn the contradiction into the required goal
    cases (ne_of_gt this) hsum

/-- If `p` is prime and `1,2,4,8 ∈ B`, there is no perfect difference set modulo `p^2+p+1`. -/
lemma no_pds_with_1_2_4_8_members
    {B : Set ℤ} {p : ℕ}
    (hp : Nat.Prime p)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B)
    (hPDS : IsPerfectDifferenceSetModulo B (p * p + p + 1)) :
    False := by
  -- Name the modulus and note it's nonzero: `v = (_)+1`.
  let v : ℕ := p * p + p + 1
  haveI : NeZero v := ⟨by
    simp [v, Nat.add_left_comm, Nat.add_assoc]
  ⟩

  -- Finite `B`.
  have hfin : B.Finite := IsPerfectDifferenceSetModulo.finite (v := v) hPDS

  -- Choose `q := #B - 1`, and record `#B = q + 1`.
  let q : ℕ := B.ncard - 1

  -- Use your lemma to get `1 ≤ B.ncard`.
  have hpos : 1 ≤ B.ncard := by
    have hx : 1 ≤ (B.ncard) :=
      x_ge_1_of_mem_1 (B := B) (x := B.ncard) hfin (by rfl) h1
    simpa using hx

  have hcard : B.ncard = q + 1 := by
    have := Nat.sub_add_cancel hpos
    simpa [q, Nat.add_comm] using this.symm

  -- 1) `{1,2,4,8} ⊆ B` forces `q` even.
  have hq_even : Even q :=
    q_even_of_pds_mem_1_2_4_8 (v := v) (q := q)
      hPDS hfin hcard h1 h2 h4 h8

  -- 2) Identify the modulus parameter: `q^2 + q + 1 = v = p^2 + p + 1`.
  have hparam : q*q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ
      (v := v) (q := q) hPDS hfin hcard

  -- 3) From `q^2+q+1 = p^2+p+1` we get `q = p`.
  have hqp : q = p := by
    have : p*p + p + 1 = q*q + q + 1 := by
      simpa [v, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
             Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hparam.symm
    exact (eq_of_sq_add_linear_succ_eq this).symm

  -- 4) Use your lemma to get `3 ≤ q`.
  have hq3 : 3 ≤ q :=
    q_ge_three_of_mem_1_2_4_8 (B := B) (q := q) hfin hcard h1 h2 h4 h8

  -- 5) A prime ≥ 3 is not even; rewrite via `q = p`.
  have hq_prime : Nat.Prime q := by simpa [hqp] using hp
  have hnot : ¬ Even q := not_even_of_prime_of_three_le hq_prime hq3

  -- Contradiction: `Even q` and `¬ Even q`.
  exact hnot hq_even

/-- If the order `q` is even (i.e. `q % 2 = 0`), then **every** line carries
at least one absolute point. -/
lemma exists_absPoint_on_line_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_even : Configuration.ProjectivePlane.order P L % 2 = 0)
    (ℓ : L) :
    (absOnLine C ℓ).Nonempty := by
  classical
  -- From your lemma: the parity of the count is `1`.
  have hmod :
      (absOnLine C ℓ).ncard % 2 = 1 :=
    absOnLine_ncard_mod2_eq_one_of_order_even
      (C := C) (hq_even := hq_even) (ℓ := ℓ)
  -- Show the set cannot be empty (since empty would give `ncard = 0` hence mod 2 = 0).
  have hne : (absOnLine C ℓ) ≠ (∅ : Set P) := by
    intro hempty
    have hzero : (absOnLine C ℓ).ncard = 0 := by
      simp [hempty]
    have : 0 = 1 := by simp [hzero] at hmod
    exact Nat.zero_ne_one this
  exact (Set.nonempty_iff_ne_empty).mpr hne

/-- Existential version of `exists_absPoint_on_line_of_order_even`. -/
lemma exists_mem_absOnLine_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_even : Configuration.ProjectivePlane.order P L % 2 = 0)
    (ℓ : L) :
    ∃ p : P, p ∈ absOnLine C ℓ := by
  have h := exists_absPoint_on_line_of_order_even (C := C) (hq_even := hq_even) (ℓ := ℓ)
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp⟩

/-- Even-order version: if the order is EVEN and `p` is NOT an absolute point, then there exists
an injective map from the set of lines through `p` to the set of absolute points such that the
image point lies on the originating line. -/
lemma exists_injective_map_linesThrough_to_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (hq_even : Configuration.ProjectivePlane.order P L % 2 = 0)
    {p : P} (hp_notabs : p ∉ polarity_absolutePoints C) :
  ∃ f :
      ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C},
      Function.Injective f
      ∧ ∀ (m : {m : L // p ∈ m}), (f m : P) ∈ (m : L) := by
  classical

  ----------------------------------------------------------------------
  -- Step 1: Every line has at least one absolute point.
  -- Option A (Nonempty version):
  have nonempty_absOn :
      ∀ ℓ : L, (absOnLine C ℓ).Nonempty :=
    fun ℓ => exists_absPoint_on_line_of_order_even (C := C) (hq_even := hq_even) (ℓ := ℓ)

  -- Option B (explicit ∃ version). If you prefer this, comment out Option A and use this:
  -- have exists_absOn :
  --     ∀ ℓ : L, ∃ x : P, x ∈ absOnLine C ℓ :=
  --   fun ℓ => exists_mem_absOnLine_of_order_even (C := C) (hq_even := hq_even) (ℓ := ℓ)
  ----------------------------------------------------------------------

  -- Step 2: For each line through `p`, choose an absolute point on it.
  have hex : ∀ m : {m : L // p ∈ m}, ∃ x : P, x ∈ absOnLine C (m : L) := by
    intro m
    -- If you used Option A:
    rcases nonempty_absOn (m : L) with ⟨x, hx⟩
    exact ⟨x, hx⟩
    -- If you used Option B instead, just:
    -- exact exists_absOn (m : L)

  let g : ({m : L // p ∈ m}) → P := fun m => Classical.choose (hex m)
  have hg : ∀ m : {m : L // p ∈ m}, g m ∈ absOnLine C (m : L) := by
    intro m; exact Classical.choose_spec (hex m)

  -- Package the chosen points as absolute points (first conjunct is "on the line",
  -- second conjunct is "absolute").
  let f : ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C} :=
    fun m =>
      let hx := hg m
      have hx_abs : g m ∈ polarity_absolutePoints C := hx.2
      ⟨g m, hx_abs⟩

  -- Image point lies on its originating line: use the first conjunct now.
  have f_on_line : ∀ m : {m : L // p ∈ m}, (f m : P) ∈ (m : L) := by
    intro m
    have hx := hg m
    simpa using hx.1

  -- Injectivity: points on distinct lines through `p` are distinct.
  have f_inj : Function.Injective f := by
    intro m₁ m₂ h
    -- If carriers differ, chosen points must differ by your lemma; contradiction.
    by_contra h_m_ne
    have h_lines_ne : (m₁ : L) ≠ (m₂ : L) := by
      intro hcar
      apply h_m_ne
      exact Subtype.ext (by simpa using hcar)

    -- Names and basic facts.
    let p₁ : P := (f m₁ : P)
    let p₂ : P := (f m₂ : P)
    have hp₁_abs : p₁ ∈ polarity_absolutePoints C := (f m₁).property
    have hp₂_abs : p₂ ∈ polarity_absolutePoints C := (f m₂).property
    have hp₁_ne_p : p₁ ≠ p := by
      intro h'; exact hp_notabs (h' ▸ hp₁_abs)
    have hp₂_ne_p : p₂ ≠ p := by
      intro h'; exact hp_notabs (h' ▸ hp₂_abs)
    have hp₁m₁ : p₁ ∈ (m₁ : L) := by simpa using f_on_line m₁
    have hp₂m₂ : p₂ ∈ (m₂ : L) := by simpa using f_on_line m₂

    -- Distinct lines through `p` carry distinct non-`p` points.
    have hne : p₁ ≠ p₂ :=
      ne_of_points_on_distinct_lines_through
        (hp_m₁ := m₁.property) (hp₁_m₁ := hp₁m₁) (hp₁_ne_p := hp₁_ne_p)
        (hp_m₂ := m₂.property) (hp₂_m₂ := hp₂m₂)
        (hm₁_ne_m₂ := h_lines_ne)

    -- But `h` says the subtypes are equal, so their values in `P` are equal.
    have : p₁ = p₂ := by simpa [p₁, p₂] using congrArg Subtype.val h
    exact hne this

  exact ⟨f, f_inj, f_on_line⟩

/-- If the order is even and `p` is **not** an absolute point, then there exists a **bijective**
map from the set of lines through `p` to the set of absolute points, and the image point lies
on the originating line. We assume there are exactly `q+1` absolute points and that `q`
is the order. -/
lemma exists_bijective_map_linesThrough_to_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    {p : P} (hp_notabs : p ∉ polarity_absolutePoints C)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1) :
  ∃ f :
      ({m : L // p ∈ m}) → {x : P // x ∈ polarity_absolutePoints C},
      Function.Bijective f
      ∧ ∀ (m : {m : L // p ∈ m}), (f m : P) ∈ (m : L) := by
  classical
  -- Ensure canonical fintype instance on the subtype `{m : L // p ∈ m}`.
  haveI : DecidablePred (fun m : L => p ∈ m) := Classical.decPred _
  -- 1) obtain an injective selector with the "lies on the line" property (even-order,
  -- p not absolute)
  obtain ⟨f, hf_inj, hf_on⟩ :=
    exists_injective_map_linesThrough_to_absPoints_of_order_even
      (C := C)
      (hq_even := by simpa [horder] using hq_even)
      (p := p) (hp_notabs := hp_notabs)
  -- 2) upgrade injective to bijective using equal cardinalities (`q+1` on both sides)
  have hbij : Function.Bijective f :=
    bijective_linesThrough_to_absPoints
      (C := C) (q := q) (p := p) (horder := horder) (f := f) (hf := hf_inj)
      (hAbsPts := hAbsPts)
  exact ⟨f, hbij, hf_on⟩

/-- From the bijection `linesThrough p ↔ absolute points` (with the on-line property),
build the inverse bijection `absolute points ↔ linesThrough p`, which sends each absolute
point to a line **containing** it. (Even-order version with `p` not absolute.) -/
lemma exists_bijective_map_absPoints_to_linesThrough_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    {p : P} (hp_notabs : p ∉ polarity_absolutePoints C)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    [DecidablePred (fun m : L => p ∈ m)] :
  ∃ f :
      ({x : P // x ∈ polarity_absolutePoints C}) → {m : L // p ∈ m},
      Function.Bijective f
      ∧ ∀ (x : {x : P // x ∈ polarity_absolutePoints C}), (x : P) ∈ (f x : L) := by
  classical
  -- Give the absolute-points subtype a `Fintype` instance.
  letI : Fintype ↥(polarity_absolutePoints C) := Fintype.ofFinite _

  -- Obtain the bijection `linesThrough p → absPoints` with the on-line property.
  obtain ⟨f, hf_bij, hf_on⟩ :=
    exists_bijective_map_linesThrough_to_absPoints_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even)
      (p := p) (hp_notabs := hp_notabs) (hAbsPts := hAbsPts)

  -- Package `f` as an equivalence and take its inverse.
  let e : ({m : L // p ∈ m}) ≃ {x : P // x ∈ polarity_absolutePoints C} :=
    Equiv.ofBijective f hf_bij
  let g : ({x : P // x ∈ polarity_absolutePoints C}) → {m : L // p ∈ m} := e.symm

  -- Return the inverse map, its bijectivity, and the "point lies on its image line" property.
  refine ⟨g, e.symm.bijective, ?_⟩
  intro x
  -- From `e.right_inv x : e (g x) = x`, pass to underlying `P`-points.
  have hx₀ : e (g x) = x := e.right_inv x
  have hx' : (f (g x) : P) = (x : P) := by
    change (e (g x) : P) = (x : P)
    exact congrArg Subtype.val hx₀
  -- Use the on-line property for `f (g x)` and rewrite.
  simpa [hx'] using hf_on (g x)

/-- Even-order, three-point formulation with global cardinalities:
If `p₁` and `p₂` are distinct absolute points on the same line `ℓ` and `p` is a third point on `ℓ`
distinct from both `p₁` and `p₂`, then `p` is also absolute.

We assume the plane has order `q` and there are exactly `q+1` absolute points. -/
lemma abs_of_third_point_on_line_with_two_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    {ℓ : L} {p p₁ p₂ : P}
    (hp₁_abs : p₁ ∈ polarity_absolutePoints C)
    (hp₂_abs : p₂ ∈ polarity_absolutePoints C)
    (hp₁ℓ : p₁ ∈ ℓ) (hp₂ℓ : p₂ ∈ ℓ)
    (hp₁_ne_hp₂ : p₁ ≠ p₂)
    (hpℓ : p ∈ ℓ) (hp_ne₁ : p ≠ p₁) (hp_ne₂ : p ≠ p₂)
    [DecidablePred (fun m : L => p ∈ m)] :
    p ∈ polarity_absolutePoints C := by
  classical
  -- Give the absolute-points subtype a `Fintype` instance.
  letI : Fintype ↥(polarity_absolutePoints C) := Fintype.ofFinite _

  -- Suppose `p` is not absolute; we derive a contradiction.
  by_contra hp_notabs
  have hp_notabs' : p ∉ polarity_absolutePoints C := hp_notabs

  -- Even-order inverse bijection: absolute points ↔ lines through `p`,
  -- with the property that each absolute point lies on its image line.
  obtain ⟨g, hg_bij, hg_on⟩ :=
    exists_bijective_map_absPoints_to_linesThrough_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even)
      (p := p) (hp_notabs := hp_notabs') (hAbsPts := hAbsPts)

  -- Package `p₁, p₂` as absolute-point subtypes.
  set x₁ : {x : P // x ∈ polarity_absolutePoints C} := ⟨p₁, hp₁_abs⟩
  set x₂ : {x : P // x ∈ polarity_absolutePoints C} := ⟨p₂, hp₂_abs⟩

  -- Show `g x₁ = ⟨ℓ, hpℓ⟩` using your "distinct lines through p" lemma (for uniqueness).
  have gx₁_eq : g x₁ = ⟨ℓ, hpℓ⟩ := by
    -- Both lines `g x₁` and `ℓ` pass through `p`, and both contain `p₁`.
    -- If they were distinct, we'd get `p₁ ≠ p₁`, contradiction.
    have hp_mem_gx₁ : p ∈ (g x₁ : L) := (g x₁).property
    have hp₁_mem_gx₁ : p₁ ∈ (g x₁ : L) := by simpa using hg_on x₁
    have : (g x₁ : L) = ℓ := by
      by_contra hneq
      have hneq' : (g x₁ : L) ≠ ℓ := hneq
      have contra :=
        ne_of_points_on_distinct_lines_through
          (hp_m₁ := hp_mem_gx₁) (hp₁_m₁ := hp₁_mem_gx₁) (hp₁_ne_p := by exact hp_ne₁.symm)
          (hp_m₂ := hpℓ) (hp₂_m₂ := hp₁ℓ) (hm₁_ne_m₂ := hneq')
      exact (contra rfl).elim
    -- upgrade to equality of subtypes
    exact Subtype.ext (by simpa using this)

  -- Similarly, `g x₂ = ⟨ℓ, hpℓ⟩`.
  have gx₂_eq : g x₂ = ⟨ℓ, hpℓ⟩ := by
    have hp_mem_gx₂ : p ∈ (g x₂ : L) := (g x₂).property
    have hp₂_mem_gx₂ : p₂ ∈ (g x₂ : L) := by simpa using hg_on x₂
    have : (g x₂ : L) = ℓ := by
      by_contra hneq
      have hneq' : (g x₂ : L) ≠ ℓ := hneq
      have contra :=
        ne_of_points_on_distinct_lines_through
          (hp_m₁ := hp_mem_gx₂) (hp₁_m₁ := hp₂_mem_gx₂) (hp₁_ne_p := by exact hp_ne₂.symm)
          (hp_m₂ := hpℓ) (hp₂_m₂ := hp₂ℓ) (hm₁_ne_m₂ := hneq')
      exact (contra rfl).elim
    exact Subtype.ext (by simpa using this)

  -- Injectivity of `g` now forces `x₁ = x₂`, contradicting `p₁ ≠ p₂`.
  have : x₁ = x₂ := by
    -- `g` is injective since it's bijective.
    have hinj : Function.Injective g := hg_bij.injective
    exact hinj (gx₁_eq.trans gx₂_eq.symm)
  have : p₁ = p₂ := by
    -- equal subtypes ⇒ equal underlying points
    simpa using congrArg Subtype.val this

  exact hp₁_ne_hp₂ this

/-- Even-order version with global cardinalities:
If a line `ℓ` contains two distinct absolute points, then **every** point of `ℓ` is absolute.
We assume the plane has order `q` and there are exactly `q+1` absolute points. -/
lemma all_points_on_line_abs_of_two_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    {ℓ : L} {p₁ p₂ : P}
    (hp₁_abs : p₁ ∈ polarity_absolutePoints C)
    (hp₂_abs : p₂ ∈ polarity_absolutePoints C)
    (hp₁ℓ : p₁ ∈ ℓ) (hp₂ℓ : p₂ ∈ ℓ)
    (hp₁_ne_hp₂ : p₁ ≠ p₂) :
    ∀ p : P, p ∈ ℓ → p ∈ polarity_absolutePoints C := by
  classical
  intro p hpℓ
  -- If `p` is one of the given absolute points, we are done.
  by_cases h1 : p = p₁
  · simpa [h1] using hp₁_abs
  by_cases h2 : p = p₂
  · simpa [h2] using hp₂_abs
  -- Otherwise, apply the 3-point lemma to `p, p₁, p₂` on the same line `ℓ`.
  -- Provide a local decidable instance for `{m : L // p ∈ m}`.
  letI : DecidablePred (fun m : L => p ∈ m) := Classical.decPred _
  exact
    abs_of_third_point_on_line_with_two_absPoints_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even) (hAbsPts := hAbsPts)
      (ℓ := ℓ) (p := p) (p₁ := p₁) (p₂ := p₂)
      (hp₁_abs := hp₁_abs) (hp₂_abs := hp₂_abs)
      (hp₁ℓ := hp₁ℓ) (hp₂ℓ := hp₂ℓ) (hp₁_ne_hp₂ := hp₁_ne_hp₂)
      (hpℓ := hpℓ) (hp_ne₁ := h1) (hp_ne₂ := h2)

/-- **Converse.** If `x` is an absolute point for the negation polarity in the PDS geometry,
then the double of `x` (as a residue mod `v`) is represented by some `b ∈ B`. -/
lemma exists_coe_eq_double_of_mem_polarity_absolutePoints_pdsNegPolarity
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
    (x : ZMod v)
    (hx_abs :
      x ∈
        @polarity_absolutePoints (ZMod v) (ZMod v)
          (pdsMembershipFlipped B v)
          (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
          (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)) :
    ∃ b ∈ B, (b : ZMod v) = x + x := by
  -- Unfold “absolute” for the negation polarity: `x ∈ φ x` with `φ x = -x`,
  -- i.e. `x ∈ pdsLine B v (-x)`.
  have hx_on_neg :
      x ∈ pdsLine B v (-x) := by
    simpa [polarity_absolutePoints, pdsNegPolarity] using hx_abs
  -- Now use your characterization of membership on the `-x` line.
  exact (mem_negLine_iff_exists_coe_eq_double B v x).1 hx_on_neg

/-- From PDS + `#B = q+1` + `1,2,4,8 ∈ B` and `v ≥ 3`, we get:
- `1,2,4` are absolute and lie on `pdsLine B v 0`,
- and `q % 2 = 0`. -/
lemma abs_collinear_and_q_mod2_zero_of_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    ((1 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3))
    ∧
    ((2 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3))
    ∧
    ((4 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3))
    ∧
    ((1 : ZMod v) ∈ pdsLine B v 0
     ∧ (2 : ZMod v) ∈ pdsLine B v 0
     ∧ (4 : ZMod v) ∈ pdsLine B v 0)
    ∧
    q % 2 = 0 := by
  -- put instances in scope if needed
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  -- absoluteness + collinearity
  obtain ⟨h1abs, h2abs, h4abs, h1on0, h2on0, h4on0⟩ :=
    abs_1_2_4_and_collinear_of_mem_1_2_4_8
      (hv3 := hv3) (hPDS := hPDS) (hfin := hfin) (hcard := hcard) (hq3 := hq3)
      (h1 := h1) (h2 := h2) (h4 := h4) (h8 := h8)

  -- evenness
  have hqEven : Even q :=
    q_even_of_pds_mem_1_2_4_8 (hPDS := hPDS) (hfin := hfin) (hcard := hcard)
      (h1 := h1) (h2 := h2) (h4 := h4) (h8 := h8)
  have hq_mod2_zero : q % 2 = 0 := by
    rcases hqEven with ⟨k, hk⟩
    -- turn `q = k + k` into `q = 2 * k`
    have : 2 ∣ q := ⟨k, by simpa [two_mul] using hk⟩
    exact Nat.mod_eq_zero_of_dvd this

  exact ⟨h1abs, h2abs, h4abs, ⟨h1on0, h2on0, h4on0⟩, hq_mod2_zero⟩

/-- If a finite set `B : Set ℕ` has size `q + 1` and contains `1, 2, 4, 8, 13`,
then `q ≥ 4`. -/
lemma q_ge_four_of_mem_1_2_4_8_13
    {B : Set ℤ} {q : ℕ}
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) (h13 : 13 ∈ B) :
    4 ≤ q := by
  classical
  -- package the five required elements into a finset
  let T : Finset ℤ := {1, 2, 4, 8, 13}
  have hT_card : T.card = 5 := by simp [T]

  -- `T ⊆ hfin.toFinset`
  have hT_subset : T ⊆ hfin.toFinset := by
    intro x hx
    have hx_cases : x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 13 := by
      simpa [T, Finset.mem_insert, Finset.mem_singleton] using hx
    have hxB : x ∈ B := by
      rcases hx_cases with rfl | rfl | rfl | rfl | rfl
      · simpa using h1
      · simpa using h2
      · simpa using h4
      · simpa using h8
      · simpa using h13
    simpa [Set.mem_toFinset] using hxB

  -- From the subset, deduce `5 ≤ (hfin.toFinset).card`
  have h5le_toFin : 5 ≤ (hfin.toFinset).card := by
    have := Finset.card_mono hT_subset
    simpa [hT_card] using this

  -- Bridge `ncard` and `toFinset.card`
  have hBcard : B.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card (α := ℤ) (s := B) (hs := hfin)

  -- Hence `5 ≤ B.ncard`
  have h5le_ncard : 5 ≤ B.ncard := by
    simpa [hBcard] using h5le_toFin

  -- And thus `5 ≤ q + 1`, i.e. `4 ≤ q`
  have h5le : 5 ≤ q + 1 := by simpa [hcard] using h5le_ncard
  exact (Nat.succ_le_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using h5le))

/-- If `B` is a PDS mod `v`, `#B = q+1`, and `1,2,4,8 ∈ B`, then `8` is absolute. -/
lemma eight_abs_of_pds_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    -- we assume we have this for the PDS geometry; if you have a named lemma, use it here
    (hAbsPts :
      (@polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q)
          hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q)
          hv3 hPDS hfin hcard hq3)).ncard = q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    ((8 : ZMod v) ∈
      @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q)
          hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q)
          hv3 hPDS hfin hcard hq3)) := by
  classical
  -- Freeze the instances behind names and use them consistently
  let PP :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) := PP
  let C :=
    pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3
  -- Use your packed lemma: 1,2,4 absolute; 1,2,4 on the zero-translate line; and q % 2 = 0.
  have hpack :=
    abs_collinear_and_q_mod2_zero_of_mem_1_2_4_8
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 h1 h2 h4 h8
  rcases hpack with ⟨h1abs, h2abs, _h4abs, h_on_line, hq_even⟩
  rcases h_on_line with ⟨h1_on_set, h2_on_set, _h4_on_set⟩

  -- Work with the line parameter 0 : ZMod v (not the set)
  let ℓ : ZMod v := 0
  -- Convert set-membership `p ∈ pdsLine B v 0` into line-membership `p ∈ ℓ`
  have h1ℓ : (1 : ZMod v) ∈ ℓ := by simpa [ℓ, pdsMembershipFlipped] using h1_on_set
  have h2ℓ : (2 : ZMod v) ∈ ℓ := by simpa [ℓ, pdsMembershipFlipped] using h2_on_set

  -- Put 8 on that line using your translate lemma at t=0, then convert
  have h8_on_set : (8 : ZMod v) ∈ pdsLine B v 0 :=
    (mem_pdsLine_iff_sub_coe_mem B v (8 : ZMod v) (0 : ZMod v)).2 ⟨8, h8, by simp⟩
  have h8ℓ : (8 : ZMod v) ∈ ℓ := by simpa [ℓ, pdsMembershipFlipped, sub_zero] using h8_on_set

  -- The plane has order q
  have horder :
      @Configuration.ProjectivePlane.order (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q)
          hv3 hPDS hfin hcard hq3)
      = q :=
    pdsProjectivePlane_order_eq
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  -- helper: 1 ≠ 2 in ZMod v (since v ≥ 3)
  have h12 : (1 : ZMod v) ≠ 2 := by
    simpa using (one_ne_two_zmod_of_three_le (v := v) hv3)

  -- Build the "all points on ℓ are absolute" function,
  -- then apply it to `8` with the membership proof `h8ℓ`.
  have all_on_line :
      ∀ p : ZMod v, p ∈ ℓ →
        p ∈ polarity_absolutePoints C :=
    all_points_on_line_abs_of_two_absPoints_of_order_even
      (C := C) (q := q) (horder := horder)
      (hq_even := by simpa using hq_even)
      (hAbsPts := hAbsPts)
      (ℓ := ℓ) (p₁ := (1 : ZMod v)) (p₂ := (2 : ZMod v))
      (hp₁_abs := h1abs) (hp₂_abs := h2abs)
      (hp₁ℓ := h1ℓ) (hp₂ℓ := h2ℓ)
      (hp₁_ne_hp₂ := h12)

  exact all_on_line (8 : ZMod v) h8ℓ

/-- Under the PDS hypotheses and `1,2,4,8 ∈ B`, the residue `16 (mod v)` is
represented by an element of `B`. -/
lemma residue16_in_B_of_pds_mem_1_2_4_8
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) :
    ∃ b ∈ B, (b : ZMod v) = (16 : ZMod v) := by
  classical
  -- Fix instances/structures to avoid definally-unequal instance issues
  let PP :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) := PP
  let C :=
    pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  -- `v` is odd from the PDS size/finition hypotheses
  have hodd : v % 2 = 1 :=
    IsPerfectDifferenceSetModulo.mod_two_eq_one
      (B := B) (v := v) (q := q) hPDS hfin hcard

  -- Cardinality of absolute points = q+1 (for negation polarity in this geometry)
  have hAbsPts :
      (@polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v) PP C).ncard = q + 1 := by
    simpa [PP, C] using
      ncard_absolutePoints_pdsNegPolarity
        (B := B) (v := v) (q := q)
        hv3 hodd hPDS hfin hcard hq3

  -- 8 is absolute by your previous result
  have h8_abs :
      (8 : ZMod v) ∈
        @polarity_absolutePoints (ZMod v) (ZMod v)
          (pdsMembershipFlipped B v) PP C :=
    eight_abs_of_pds_mem_1_2_4_8
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 hAbsPts h1 h2 h4 h8

  -- Absolute ↔ “double is represented”: specialize at x = 8
  have hiff :=
    (mem_polarity_absolutePoints_pdsNegPolarity_iff_exists_coe_eq_double
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 (x := (8 : ZMod v)))

  -- Extract the witness and finish
  obtain ⟨b, hbB, hb⟩ := hiff.mp h8_abs
  refine ⟨b, hbB, ?_⟩
  -- Turn `(8 : ZMod v) + 8` into a cast of a Nat sum
  have h_add_cast :
      (8 : ZMod v) + (8 : ZMod v) = ((8 + 8 : ℕ) : ZMod v) := by
    -- `((8+8 : ℕ) : ZMod v) = (8 : ZMod v) + (8 : ZMod v)` is `Nat.cast_add`;
    -- we just use its symmetry.
    simpa [Nat.cast_add] using (Nat.cast_add (R := ZMod v) 8 8).symm
  -- Fold `8 + 8` to `16` in ℕ, then cast
  have h_fold : ((8 + 8 : ℕ) : ZMod v) = (16 : ZMod v) := by
    have h88n : (8 + 8 : ℕ) = 16 := by decide
    simp [h88n]
  -- Chain the equalities
  exact hb.trans (h_add_cast.trans h_fold)

/-- If `v = q^2 + q + 1` and `4 ≤ q`, then `21 ≤ v`. -/
lemma twentyone_le_of_v_eq_qsq_add_q_add_one
    {q v : ℕ} (hv : v = q * q + q + 1) (hq : 4 ≤ q) : 21 ≤ v := by
  -- From `4 ≤ q` we get `16 ≤ q*q`
  have h16 : 16 ≤ q*q := by
    -- this is `4*4 ≤ q*q`
    simpa using Nat.mul_le_mul hq hq
  -- Add `4 ≤ q` to both sides: `20 ≤ q*q + q`
  have h20 : 20 ≤ q*q + q := by
    have := Nat.add_le_add h16 hq
    -- `16 + 4 = 20`
    simpa using this
  -- Add 1 to both sides: `21 ≤ q*q + q + 1`
  have h21 : 21 ≤ q*q + q + 1 := Nat.succ_le_succ h20
  -- Rewriting `v`
  simpa [hv, Nat.add_assoc] using h21

/-- If `21 ≤ v`, then the residues `1` and `13` are distinct modulo `v`. -/
lemma mod_ne_one_thirteen_of_twentyone_le {v : ℕ} (hv : 21 ≤ v) :
    1 % v ≠ 13 % v := by
  -- `1 < 13`
  have h1lt13 : 1 < 13 := by decide
  -- From `21 ≤ v` we get `13 < v`
  have h13ltv : 13 < v := lt_of_lt_of_le (by decide : 13 < 21) hv
  -- Apply your lemma with `a = 1`, `b = 13`
  exact mod_ne_of_lt_chain (a := 1) (b := 13) h1lt13 h13ltv

/-- In `ZMod v`, `a - b = c - d` iff `a + d = c + b` (same order as mathlib). -/
lemma zmod_sub_eq_sub_iff_add_eq_add {v : ℕ}
    (a b c d : ZMod v) :
    a - b = c - d ↔ a + d = c + b := by
  -- Specialize the mathlib lemma by annotating its type.
  simpa using
    (sub_eq_sub_iff_add_eq_add : a - b = c - d ↔ a + d = c + b)

/-- In `ZMod v`, we have `(1 + 16) = (13 + 4)`. -/
lemma one_add_sixteen_eq_thirteen_add_four (v : ℕ) :
    ((1 : ZMod v) + (16 : ZMod v)) = (13 : ZMod v) + (4 : ZMod v) := by
  -- `Nat` equality: `1 + 16 = 13 + 4`
  have hnat : (1 + 16 : ℕ) = 13 + 4 := by decide
  calc
    (1 : ZMod v) + 16
        = ((1 + 16 : ℕ) : ZMod v) := by
            -- use `Nat.cast_add` in the symmetric direction
            simpa [Nat.cast_add] using
              (Nat.cast_add (R := ZMod v) 1 16).symm
    _   = ((13 + 4 : ℕ) : ZMod v) := by
            simp [hnat]
    _   = (13 : ZMod v) + 4 := by
            simpa [Nat.cast_add] using
              (Nat.cast_add (R := ZMod v) 13 4)

/-- In `ZMod v`, we have `(1 - 4) = (13 - 16)`. -/
lemma one_sub_four_eq_thirteen_sub_sixteen (v : ℕ) :
    ((1 : ZMod v) - (4 : ZMod v)) = (13 : ZMod v) - (16 : ZMod v) := by
  -- From `a - b = c - d ↔ a + d = c + b`, apply the ⇒ direction (mpr) with the sum equality.
  have hadd : (1 : ZMod v) + 16 = (13 : ZMod v) + 4 :=
    one_add_sixteen_eq_thirteen_add_four v
  exact
    (zmod_sub_eq_sub_iff_add_eq_add
        (v := v) (a := (1 : ZMod v)) (b := (4 : ZMod v))
        (c := (13 : ZMod v)) (d := (16 : ZMod v))).mpr hadd

/-- If `1,4,13,16 ∈ B`, then `B` is **not** a perfect difference set modulo `v`. -/
lemma not_pds_of_mem_1_4_13_16
    {B : Set ℤ} {v : ℕ}
    (h1 : 1 ∈ B) (h4 : 4 ∈ B)
    (h13 : 13 ∈ B) (h16 : 16 ∈ B) :
    ¬ IsPerfectDifferenceSetModulo B v := by
  classical
  intro hPDS
  -- The PDS hypothesis is exactly a `BijOn` for `f (a,b) = (a - b : ZMod v)`
  have hBij :
      B.offDiag.BijOn (fun (a, b) => (a - b : ZMod v)) {x : ZMod v | x ≠ 0} := hPDS
  have hInj : Set.InjOn (fun (a, b) => (a - b : ZMod v)) B.offDiag := hBij.injOn

  -- Both pairs `(1,4)` and `(13,16)` lie in `B.offDiag`
  have h14_off : (1, 4) ∈ B.offDiag := by
    -- `Set.offDiag` = `{(a,b) | a ∈ B ∧ b ∈ B ∧ a ≠ b}`
    simp [Set.offDiag, Set.mem_setOf_eq, h1, h4]
  have h1316_off : (13, 16) ∈ B.offDiag := by
    simp [Set.offDiag, Set.mem_setOf_eq, h13, h16]

  -- Their images under `f (a,b) = a - b` are equal, by your lemma:
  have h_sub :
      ((1 : ZMod v) - (4 : ZMod v)) = (13 : ZMod v) - (16 : ZMod v) :=
    one_sub_four_eq_thirteen_sub_sixteen (v := v)

  -- Transport to the lambda-applied form
  have himg_eq :
      (fun (p : ℤ × ℤ) => (p.1 - p.2 : ZMod v)) (1, 4)
        =
      (fun (p : ℤ × ℤ) => (p.1 - p.2 : ZMod v)) (13, 16) := by
    simpa using h_sub

  -- Injectivity on `B.offDiag` now forces the pairs to be equal — contradiction.
  have : ((1 : ℤ), (4 : ℤ)) = (13, 16) := hInj h14_off h1316_off himg_eq
  exact by cases this

/-- If `16` is represented in `B` modulo `v` and `21 ≤ v`, then that representative
is not `13`.  Here `b : ℤ` while `v : ℕ`. -/
lemma ne_thirteen_of_rep16_of_twentyone_le {v : ℕ} {b : ℤ}
    (hv21 : 21 ≤ v) (hb16 : (b : ZMod v) = (16 : ZMod v)) :
    b ≠ 13 := by
  intro hb
  subst hb
  -- we need `v ≠ 0` and the chain `13 < 16 < v`
  have hv_pos : 0 < v := Nat.lt_of_lt_of_le (by decide : 0 < 21) hv21
  haveI : NeZero v := ⟨ne_of_gt hv_pos⟩
  have h16v : 16 < v := Nat.lt_of_lt_of_le (by decide : 16 < 21) hv21
  have h13lt16 : 13 < 16 := by decide
  -- `(13 : ZMod v) ≠ (16 : ZMod v)` since `0 ≤ 13 < 16 < v`
  have hne : (13 : ZMod v) ≠ (16 : ZMod v) :=
    zmod_coe_ne_of_lt_chain (a := 13) (b := 16) (v := v) h13lt16 h16v
  -- After `subst`, `(b : ZMod v)` is `((13 : ℤ) : ZMod v)`; simplify it to `(13 : ZMod v)`.
  have hb16' : (13 : ZMod v) = (16 : ZMod v) := by
    simpa using hb16
  exact hne hb16'

/-- Existential packaging: if `16` is represented in `B` modulo `v` and `21 ≤ v`,
then that representative is not `13`. -/
lemma exists_rep16_implies_ne_thirteen_of_twentyone_le
    {B : Set ℤ} {v : ℕ}
    (hv21 : 21 ≤ v) :
    ∀ {b}, b ∈ B → (b : ZMod v) = (16 : ZMod v) → b ≠ 13 := by
  intro b _ hb16
  exact ne_thirteen_of_rep16_of_twentyone_le (hv21 := hv21) (hb16 := hb16)

/-- If `1,4,13 ∈ B` and `16` is represented in `B` modulo `v`, then `B` is **not**
a perfect difference set modulo `v`.  We assume `21 ≤ v` so that a representative of
`16` cannot be `13`, ensuring `(13,b) ∈ B.offDiag`. -/
lemma not_pds_of_mem_1_4_13_and_rep16
    {B : Set ℤ} {v : ℕ}
    (hv21 : 21 ≤ v)
    (h1 : 1 ∈ B) (h4 : 4 ∈ B) (h13 : 13 ∈ B)
    (h16rep : ∃ b ∈ B, (b : ZMod v) = (16 : ZMod v)) :
    ¬ IsPerfectDifferenceSetModulo B v := by
  classical
  intro hPDS
  -- `IsPerfectDifferenceSetModulo` is a `BijOn` for `f(a,b) = (a - b : ZMod v)` on `B.offDiag`
  have hBij :
      B.offDiag.BijOn (fun (a, b) => (a - b : ZMod v)) {x : ZMod v | x ≠ 0} := hPDS
  have hInj : Set.InjOn (fun (a, b) => (a - b : ZMod v)) B.offDiag := hBij.injOn

  -- Choose a representative `b ∈ B` with `(b : ZMod v) = 16`
  obtain ⟨b, hbB, hb16⟩ := h16rep

  -- Use the provided lemma to exclude `b = 13`
  have hb_ne_13 : b ≠ 13 :=
    ne_thirteen_of_rep16_of_twentyone_le (v := v) (b := b) hv21 hb16
  have h13_ne_b : 13 ≠ b := by simpa [ne_comm] using hb_ne_13

  -- Both pairs `(1,4)` and `(13,b)` lie in `B.offDiag`
  have h14_off : (1, 4) ∈ B.offDiag := by
    simp [Set.offDiag, Set.mem_setOf_eq, h1, h4]
  have h13b_off : (13, b) ∈ B.offDiag := by
    simp [Set.offDiag, Set.mem_setOf_eq, h13, hbB, h13_ne_b]

  -- Their images under `f(a,b) = a - b` are equal:
  -- Use `(1 - 4) = (13 - 16)` and rewrite `16` to `b` via `hb16`.
  have h_sub :
      ((1 : ZMod v) - (4 : ZMod v))
        = (13 : ZMod v) - (b : ZMod v) := by
    simpa [hb16.symm] using one_sub_four_eq_thirteen_sub_sixteen (v := v)

  -- Put in lambda form
  have himg_eq :
      (fun (p : ℤ × ℤ) => (p.1 - p.2 : ZMod v)) (1, 4)
        =
      (fun (p : ℤ × ℤ) => (p.1 - p.2 : ZMod v)) (13, b) := by
    simpa using h_sub

  -- Injectivity on `B.offDiag` forces `(1,4) = (13,b)`, contradiction (`1 ≠ 13`).
  have : ((1 : ℤ), 4) = (13, b) := hInj h14_off h13b_off himg_eq
  have : (1 : ℤ) = 13 := congrArg Prod.fst this
  exact (by decide : (1 : ℤ) ≠ 13) this

/-- If `B` is finite of size `q+1`, contains `1,2,4,8,13`, and `v ≠ 0`,
then `B` is **not** a perfect difference set modulo `v`. -/
lemma not_pds_of_mem_1_2_4_8_13_no_v_eq
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) (h13 : 13 ∈ B) :
    ¬ IsPerfectDifferenceSetModulo B v := by
  intro hPDS
  -- From the five specific elements we get `q ≥ 4`.
  have hq4 : 4 ≤ q :=
    q_ge_four_of_mem_1_2_4_8_13 (hfin := hfin) (hcard := hcard)
      (h1 := h1) (h2 := h2) (h4 := h4) (h8 := h8) (h13 := h13)

  -- From PDS + `v ≠ 0` + `#B = q+1`, we get `q*q + q + 1 = v`.
  have hv_eq : q*q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ
      (B := B) (v := v) (q := q) (h := hPDS) (hfin := hfin) (hcard := hcard)

  -- Hence `21 ≤ v`.
  have hv21 : 21 ≤ v :=
    twentyone_le_of_v_eq_qsq_add_q_add_one (hv := hv_eq.symm) (hq := hq4)

  -- We also need `3 ≤ v` and `3 ≤ q+1` for the residue-16 lemma.
  have hv3 : 3 ≤ v := le_trans (by decide : 3 ≤ 21) hv21
  have hq2 : 2 ≤ q := le_trans (by decide : 2 ≤ 4) hq4
  have hq3 : 3 ≤ q + 1 := Nat.succ_le_succ hq2

  -- From PDS and `1,2,4,8 ∈ B`, the residue `16` is represented in `B`.
  obtain ⟨b, hbB, hb16⟩ :
      ∃ b ∈ B, (b : ZMod v) = (16 : ZMod v) :=
    residue16_in_B_of_pds_mem_1_2_4_8
      (hv3 := hv3) (hPDS := hPDS) (hfin := hfin) (hcard := hcard)
      (hq3 := hq3) (h1 := h1) (h2 := h2) (h4 := h4) (h8 := h8)

  -- Now contradict PDS using the 1-4-13-and-rep16 obstruction at `21 ≤ v`.
  exact (not_pds_of_mem_1_4_13_and_rep16
            (hv21 := hv21) (h1 := h1) (h4 := h4) (h13 := h13)
            (h16rep := ⟨b, hbB, hb16⟩)) hPDS

/-- If `v ≠ 0` and `1,2,4,8,13 ∈ B`, then assuming `B` is a perfect difference set modulo `v`
leads to a contradiction. -/
lemma no_pds_with_1_2_4_8_13_members_false
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (h1 : 1 ∈ B) (h2 : 2 ∈ B) (h4 : 4 ∈ B) (h8 : 8 ∈ B) (h13 : 13 ∈ B)
    (hPDS : IsPerfectDifferenceSetModulo B v) :
    False := by
  classical
  -- `B` is finite under a PDS hypothesis.
  have hfin : B.Finite := IsPerfectDifferenceSetModulo.finite (B := B) (v := v) hPDS
  -- Since `1 ∈ B`, we know `1 ≤ B.ncard`.
  have hpos : 1 ≤ B.ncard :=
    x_ge_1_of_mem_1 (hfin := hfin) (hcard := rfl) (h1 := h1)
  -- Write `B.ncard = q + 1` with `q := B.ncard - 1`.
  let q : ℕ := B.ncard - 1
  have hcard' : B.ncard = q + 1 := by
    have : (B.ncard - 1) + 1 = B.ncard := Nat.sub_add_cancel hpos
    simpa [q] using this.symm
  -- Apply your obstruction lemma to contradict `hPDS`.
  have hnot :
      ¬ IsPerfectDifferenceSetModulo B v :=
    not_pds_of_mem_1_2_4_8_13_no_v_eq
      (v := v) (q := q)
      (hfin := hfin) (hcard := hcard') (h1 := h1) (h2 := h2) (h4 := h4) (h8 := h8) (h13 := h13)
  exact hnot hPDS

/-- If `-8, -6, 0, 4 ∈ B`, then `-4, -3, 0, 2 : ZMod v` are **absolute**
for the negation polarity. -/
lemma abs_neg4_neg3_0_2_of_mem_neg8_neg6_0_4
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite) (hcard : B.ncard = q + 1) (hq3 : 3 ≤ q + 1)
    (hneg8 : (-8 : ℤ) ∈ B) (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B) (h4 : (4 : ℤ) ∈ B) :
    (-4 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ∧
    (-3 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ∧
    (0 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
    ∧
    (2 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
      (pdsMembershipFlipped B v)
      (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
      (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3) := by
  classical
  -- use the “double witness” lemma four times with the obvious witnesses
  have h_abs_neg4 :
      (-4 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3) :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (-4 : ZMod v))
      ⟨(-8 : ℤ), hneg8, by norm_num⟩

  have h_abs_neg3 :
      (-3 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3) :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (-3 : ZMod v))
      ⟨(-6 : ℤ), hneg6, by norm_num⟩

  have h_abs_0 :
      (0 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3) :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (0 : ZMod v))
      ⟨(0 : ℤ), h0, by norm_num⟩

  have h_abs_2 :
      (2 : ZMod v) ∈ @polarity_absolutePoints (ZMod v) (ZMod v)
        (pdsMembershipFlipped B v)
        (pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3)
        (pdsNegPolarity (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3) :=
    mem_polarity_absolutePoints_pdsNegPolarity_of_exists_coe_eq_double
      (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3 (x := (2 : ZMod v))
      ⟨(4 : ℤ), h4, by norm_num⟩

  exact ⟨h_abs_neg4, h_abs_neg3, h_abs_0, h_abs_2⟩

/-- If `0, 1, 4 ∈ B`, then `-4, -3, 0 : ZMod v` all lie on the line `pdsLine B v (-4)`. -/
lemma neg4_neg3_0_mem_pdsLine_neg4_of_mem
    {B : Set ℤ} {v : ℕ}
    (h0 : (0 : ℤ) ∈ B) (h1 : (1 : ℤ) ∈ B) (h4 : (4 : ℤ) ∈ B) :
    (-4 : ZMod v) ∈ pdsLine B v (-4)
    ∧ (-3 : ZMod v) ∈ pdsLine B v (-4)
    ∧ (0 : ZMod v) ∈ pdsLine B v (-4) := by
  classical
  -- Using the difference characterization: s ∈ line(-4) ↔ ∃ b∈B, s - (-4) = b (in ZMod v).

  -- s = -4, choose b = 0
  have h_neg4 :
      (-4 : ZMod v) ∈ pdsLine B v (-4) :=
    (mem_pdsLine_iff_sub_coe_mem B v (-4) (-4)).mpr
      ⟨(0 : ℤ), h0, by simp⟩

  -- s = -3, choose b = 1
  have h_neg3 :
      (-3 : ZMod v) ∈ pdsLine B v (-4) :=
    (mem_pdsLine_iff_sub_coe_mem B v (-3) (-4)).mpr
      ⟨(1 : ℤ), h1, by
        -- goal: (-3 : ZMod v) - (-4) = (1 : ZMod v)
        have : ((-3 : ZMod v) + 4) = (1 : ZMod v) := by ring
        simpa [sub_eq_add_neg] using this
      ⟩

  -- s = 0, choose b = 4
  have h_zero :
      (0 : ZMod v) ∈ pdsLine B v (-4) :=
    (mem_pdsLine_iff_sub_coe_mem B v (0 : ZMod v) (-4)).mpr
      ⟨(4 : ℤ), h4, by simp⟩

  exact ⟨h_neg4, h_neg3, h_zero⟩

/-- General step: if `s ∈ pdsLine B v t`, then `(s - t) ∈ pdsLine B v 0`. -/
lemma mem_line_t_imp_mem_line_zero
    {B : Set ℤ} {v : ℕ} {s t : ZMod v}
    (h : s ∈ pdsLine B v t) :
    (s - t) ∈ pdsLine B v 0 := by
  classical
  rcases (mem_pdsLine_iff_sub_coe_mem B v s t).mp h with ⟨b, hbB, hs⟩
  -- We already have `(s - t) = (b : ZMod v)`. Use the characterization at `0`.
  exact (mem_pdsLine_iff_sub_coe_mem B v (s - t) 0).mpr
    ⟨b, hbB, by simpa [sub_eq_add_neg] using hs⟩

/-- Special case: if `2 ∈ pdsLine B v (-4)`, then `6 ∈ pdsLine B v 0`. -/
lemma two_on_line_neg4_implies_six_on_line_zero
    {B : Set ℤ} {v : ℕ}
    (h : (2 : ZMod v) ∈ pdsLine B v (-4)) :
    (6 : ZMod v) ∈ pdsLine B v 0 := by
  classical
  -- Step 1: move from line `-4` to line `0` with `s - t`
  have h0 : (2 : ZMod v) - (-4) ∈ pdsLine B v 0 :=
    mem_line_t_imp_mem_line_zero (B := B) (v := v) (s := (2 : ZMod v)) (t := (-4)) h
  -- Turn `s - t` into `s + 4` under membership
  have h0' : ((2 : ZMod v) + 4) ∈ pdsLine B v 0 := by
    simpa [sub_eq_add_neg] using h0
  -- Step 2: `2 + 4 = 6` in `ZMod v`
  have h6 : ((2 : ZMod v) + 4) = (6 : ZMod v) := by
    ring
  -- Rewriting the point finishes it
  simpa [h6] using h0'

/-- If `-6, 0 ∈ B` and `6` is *represented* by some `b ∈ B` (i.e. `(6 : ZMod v) = (b : ZMod v)`),
then `B` cannot be a perfect difference set modulo `v`. -/
lemma not_pds_of_mem_neg6_0_and_rep6
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hneg6 : (-6 : ℤ) ∈ B) (h0 : (0 : ℤ) ∈ B)
    (hrep6 : ∃ b ∈ B, (6 : ZMod v) = (b : ZMod v)) :
    False := by
  classical
  -- Two off-diagonal pairs we want to compare: (0,-6) and (b,0).
  have hA : ((0 : ℤ), (-6 : ℤ)) ∈ B.offDiag := ⟨h0, hneg6, by decide⟩

  -- The PDS difference map used in the definition
  let g : ℤ × ℤ → ZMod v := fun p => ( (p.1 : ZMod v) - (p.2 : ZMod v) )

  rcases hrep6 with ⟨b, hbB, h6b⟩
  by_cases hb0 : b = 0
  · -- Case 1: the representative is `b = 0`, so `(6 : ZMod v) = 0`.
    -- Then `g (0,-6) = 0`, but the codomain of the PDS map excludes `0` — contradiction.
    have himg0 : g (0, -6) = 0 := by
      -- g(0,-6) = 0 - (-6) = 6; and (6 : ZMod v) = 0 by h6b and hb0
      have : ((6 : ℤ) : ZMod v) = (0 : ZMod v) := by simpa [hb0] using h6b
      simpa [g, sub_eq_add_neg] using this
    -- From `BijOn`, the map sends `B.offDiag` into `{x | x ≠ 0}`
    have hmaps : Set.MapsTo g B.offDiag {x | x ≠ 0} := hPDS.mapsTo
    have : g (0, -6) ∈ {x : ZMod v | x ≠ 0} := hmaps hA
    -- But its value is 0, contradiction.
    simp [himg0] at this

  · -- Case 2: the representative `b` is nonzero, so `(b,0) ∈ B.offDiag`.
    have hB : (b, 0) ∈ B.offDiag := ⟨hbB, h0, by simp [hb0]⟩
    -- Their images under `g` coincide: g(0,-6) = 6 and g(b,0) = b, and (6 : ZMod v) = (b : ZMod v).
    have himg_eq : g (0, -6) = g (b, 0) := by
      unfold g
      -- 0 - (-6) = 6 ; b - 0 = b
      simpa [sub_eq_add_neg] using h6b
    -- Injectivity on `B.offDiag` (from the PDS BijOn) gives equality of the pairs
    have hEQ : (0, -6) = (b, 0) := hPDS.injOn hA hB himg_eq
    -- Compare second coordinates: `-6 = 0`, absurd
    have : (-6 : ℤ) = 0 := congrArg Prod.snd hEQ
    norm_num at this

/-- In the PDS geometry from `B ⊆ ℤ` modulo `v`, if
- `IsPerfectDifferenceSetModulo B v`,
- `#B = q + 1` with `3 ≤ q + 1`,
- `q` is odd`,
- and `-8, -6, 0, 1, 4 ∈ B`,

then among the residues `-4, -3, 0 : ZMod v` at least two are equal
(so they cannot be three *distinct* absolute points on the same line). -/
lemma two_of_neg4_neg3_0_equal_mod_v_of_mem_neg8_neg6_0_1_4
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    (hq_odd : q % 2 = 1)
    (hneg8 : (-8 : ℤ) ∈ B)
    (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B)
    (h1 : (1 : ℤ) ∈ B)
    (h4 : (4 : ℤ) ∈ B) :
    (-4 : ZMod v) = (-3 : ZMod v)
    ∨ (-4 : ZMod v) = (0 : ZMod v)
    ∨ (-3 : ZMod v) = (0 : ZMod v) := by
  classical
  -- Put the PDS incidence and projective plane instances in scope.
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  -- `v` is odd from the PDS size relation.
  have hodd : v % 2 = 1 :=
    IsPerfectDifferenceSetModulo.mod_two_eq_one (B := B) (v := v) (q := q)
      hPDS hfin hcard

  -- The number of absolute points for the negation polarity is `q + 1`.
  have hAbsPtsCard :
      (polarity_absolutePoints
        (pdsNegPolarity (B := B) (v := v) (q := q)
            hv3 hPDS hfin hcard hq3)).ncard
      = q + 1 :=
    ncard_absolutePoints_pdsNegPolarity
      (B := B) (v := v) (q := q) hv3 hodd hPDS hfin hcard hq3

  -- From `-8, -6, 0 ∈ B`, we get that `-4, -3, 0` are absolute points.
  rcases
    abs_neg4_neg3_0_2_of_mem_neg8_neg6_0_4
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 hneg8 hneg6 h0 h4
    with ⟨hAbs_neg4, hAbs_neg3, hAbs_0, _hAbs_2⟩

  -- From `0, 1, 4 ∈ B`, we get that `-4, -3, 0` lie on the line `pdsLine B v (-4)`.
  rcases
    neg4_neg3_0_mem_pdsLine_neg4_of_mem
      (B := B) (v := v) h0 h1 h4
    with ⟨hℓ_neg4, hℓ_neg3, hℓ_0⟩

  -- The projective plane has order `q`.
  have horder :
      Configuration.ProjectivePlane.order (ZMod v) (ZMod v) = q :=
    pdsProjectivePlane_order_eq (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3

  -- Apply the “no three distinct absolute points on one line (odd order)” lemma.
  have :=
    no_three_distinct_absPoints_on_a_line_of_order_odd
      (P := ZMod v) (L := ZMod v)
      (C := pdsNegPolarity (B := B) (v := v) (q := q)
              hv3 hPDS hfin hcard hq3)
      (q := q)
      horder hq_odd hAbsPtsCard
      (-4 : ZMod v)
      (a := (-4 : ZMod v))
      (b := (-3 : ZMod v))
      (c := (0 : ZMod v))
      hAbs_neg4 hAbs_neg3 hAbs_0
      hℓ_neg4 hℓ_neg3 hℓ_0

  -- That lemma yields exactly the desired disjunction.
  exact this

/-- If a finite set `B : Set ℕ` has size `q + 1` and contains `-8, -6, 0, 1, 4`,
then `q ≥ 4`. -/
lemma q_ge_three_of_mem_hall
    {B : Set ℤ} {q : ℕ}
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hneg8 : (-8 : ℤ) ∈ B)
    (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B)
    (h1 : (1 : ℤ) ∈ B)
    (h4 : (4 : ℤ) ∈ B) :
    4 ≤ q := by
  classical
  let T : Finset ℤ := {-8, -6, 0, 1, 4}
  have hT_card : T.card = 5 := by simp [T]

  -- `T ⊆ hfin.toFinset`
  have hT_subset : T ⊆ hfin.toFinset := by
    intro x hx
    have hx_cases : x = -8 ∨ x = -6 ∨ x = 0 ∨ x = 1 ∨ x = 4 := by
      simpa [T, Finset.mem_insert, Finset.mem_singleton] using hx
    have hxB : x ∈ B := by
      rcases hx_cases with rfl | rfl | rfl | rfl | rfl
      · simpa using hneg8
      · simpa using hneg6
      · simpa using h0
      · simpa using h1
      · simpa using h4
    simpa [Set.mem_toFinset] using hxB

  -- From the subset, deduce `5 ≤ (hfin.toFinset).card`
  have h5le_toFin : 5 ≤ (hfin.toFinset).card := by
    have := Finset.card_mono hT_subset
    simpa [hT_card] using this

  -- Bridge `ncard` and `toFinset.card`
  have hBcard : B.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card (α := ℤ) (s := B) (hs := hfin)

  -- Hence `5 ≤ B.ncard`
  have h4le_ncard : 5 ≤ B.ncard := by
    simpa [hBcard] using h5le_toFin

  -- And thus `5 ≤ q + 1`, i.e. `4 ≤ q`
  have : 5 ≤ q + 1 := by simpa [hcard] using h4le_ncard
  exact Nat.succ_le_succ_iff.mp this

/-- If `21 ≤ v`, then `0` is not congruent to `3` modulo `v`. -/
lemma not_modEq_zero_three_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    ¬ (0 ≡ 3 [MOD v]) := by
  intro h
  -- From `21 ≤ v` we get `3 < v`
  have hbv : 3 < v := lt_of_lt_of_le (by decide : 3 < 21) hv
  -- Distinct residues since `0 < 3 < v`
  have hneq : 0 % v ≠ 3 % v :=
    mod_ne_of_lt_chain (a := 0) (b := 3) (v := v)
      (hab := by decide) (hbv := hbv)
  -- But `0 ≡ 3 [MOD v]` means equal remainders
  have heq : 0 % v = 3 % v := by simpa [Nat.ModEq] using h
  exact hneq heq

/-- If `21 ≤ v`, then `0` is not congruent to `4` modulo `v`. -/
lemma not_modEq_zero_four_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    ¬ (0 ≡ 4 [MOD v]) := by
  intro h
  -- From `21 ≤ v` we get `4 < v`
  have hbv : 4 < v := lt_of_lt_of_le (by decide : 4 < 21) hv
  -- Distinct residues since `0 < 4 < v`
  have hneq : 0 % v ≠ 4 % v :=
    mod_ne_of_lt_chain (a := 0) (b := 4) (v := v)
      (hab := by decide) (hbv := hbv)
  -- But `0 ≡ 4 [MOD v]` means equal remainders
  have heq : 0 % v = 4 % v := by simpa [Nat.ModEq] using h
  exact hneq heq

/-- If `21 ≤ v`, then `3` is not congruent to `4` modulo `v`. -/
lemma not_modEq_three_four_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    ¬ (3 ≡ 4 [MOD v]) := by
  intro h
  -- From `21 ≤ v` we get `4 < v`
  have hbv : 4 < v := lt_of_lt_of_le (by decide : 4 < 21) hv
  -- Distinct residues since `3 < 4 < v`
  have hneq : 3 % v ≠ 4 % v :=
    mod_ne_of_lt_chain (a := 3) (b := 4) (v := v)
      (hab := by decide) (hbv := hbv)
  -- But `3 ≡ 4 [MOD v]` means equal remainders
  have heq : 3 % v = 4 % v := by simpa [Nat.ModEq] using h
  exact hneq heq

/-- Helper lemma for negation in addition groups like mod v. -/
lemma neg_eq_iff {α} [AddGroup α] (x y : α) : (-x = -y) ↔ (x = y) := by
  constructor
  · intro h
    -- negate both sides: -(-x) = -(-y) ⇒ x = y
    simpa [neg_neg] using congrArg (fun t : α => -t) h
  · intro h
    simp [h]

/-- Allows negation of modular inequalities. -/
lemma zmod_neg_ne_of_ne {v a b : ℕ}
    (h : (a : ZMod v) ≠ (b : ZMod v)) :
    (-(a : ZMod v)) ≠ (-(b : ZMod v)) := by
  intro hneg
  have : (a : ZMod v) = (b : ZMod v) := by
    -- negate both sides
    simpa [neg_neg] using congrArg (fun x : ZMod v => -x) hneg
  exact h this

/-- If `21 ≤ v`, then `(0 : ZMod v) ≠ (-3 : ZMod v)`. -/
lemma not_modEq_zero_neg_three_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    (0 : ZMod v) ≠ (-3 : ZMod v) := by
  classical
  -- 1) From your lemma: ¬ (0 ≡ 3 [MOD v])
  have h03_mod : ¬ (0 ≡ 3 [MOD v]) :=
    not_modEq_zero_three_of_le_twentyone (v := v) hv

  -- 2) Turn that into (0 : ZMod v) ≠ (3 : ZMod v) using the iff.
  have h03 : (0 : ZMod v) ≠ (3 : ZMod v) := by
    intro hEqZ
    -- Force the equality to the exact shape ↑0 = ↑3
    have hEqZ_natcast :
        ((0 : ℕ) : ZMod v) = ((3 : ℕ) : ZMod v) := by
      simpa using hEqZ
    -- Now apply your bridge lemma
    have : 0 ≡ 3 [MOD v] :=
      (ZMod.natCast_eq_natCast_iff (0) (3) (v)).1 hEqZ_natcast
    exact h03_mod this

  -- 3) Negation preserves inequality: from 0 ≠ 3 get 0 ≠ -3.
  intro h0eqm3
  have : (0 : ZMod v) = (3 : ZMod v) := by
    -- apply `-` to both sides of `0 = -3`
    simpa [neg_neg] using congrArg (fun x : ZMod v => -x) h0eqm3
  exact h03 this

/-- If `21 ≤ v`, then `(0 : ZMod v) ≠ (-4 : ZMod v)`. -/
lemma not_modEq_zero_neg_four_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    (0 : ZMod v) ≠ (-4 : ZMod v) := by
  -- From your lemma: ¬ (0 ≡ 4 [MOD v])
  have h04_mod : ¬ (0 ≡ 4 [MOD v]) :=
    not_modEq_zero_four_of_le_twentyone (v := v) hv

  -- Turn that into (0 : ZMod v) ≠ (4 : ZMod v) using the bridge iff.
  have h04 : (0 : ZMod v) ≠ (4 : ZMod v) := by
    intro hEqZ
    -- force the equality to the nat-cast shape ↑0 = ↑4
    have hEqZ_natcast :
        ((0 : ℕ) : ZMod v) = ((4 : ℕ) : ZMod v) := by simpa using hEqZ
    have : 0 ≡ 4 [MOD v] :=
      (ZMod.natCast_eq_natCast_iff 0 4 v).1 hEqZ_natcast
    exact h04_mod this

  -- Negation preserves inequality: from 0 ≠ 4 get 0 ≠ -4
  intro h0eqm4
  have : (0 : ZMod v) = (4 : ZMod v) := by
    -- negate both sides of `0 = -4`
    simpa [neg_neg] using congrArg (fun x : ZMod v => -x) h0eqm4
  exact h04 this

/-- If `21 ≤ v`, then `(-3 : ZMod v) ≠ (-4 : ZMod v)`. -/
lemma not_modEq_neg_three_neg_four_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    (-3 : ZMod v) ≠ (-4 : ZMod v) := by
  -- From your lemma: ¬ (3 ≡ 4 [MOD v])
  have h34_mod : ¬ (3 ≡ 4 [MOD v]) :=
    not_modEq_three_four_of_le_twentyone (v := v) hv

  -- Turn that into (3 : ZMod v) ≠ (4 : ZMod v) using the bridge iff.
  have h34 : (3 : ZMod v) ≠ (4 : ZMod v) := by
    intro hEqZ
    have hEqZ_natcast :
        ((3 : ℕ) : ZMod v) = ((4 : ℕ) : ZMod v) := by simpa using hEqZ
    have : 3 ≡ 4 [MOD v] :=
      (ZMod.natCast_eq_natCast_iff 3 4 v).1 hEqZ_natcast
    exact h34_mod this

  -- Negation preserves inequality: from -3 = -4 ⇒ 3 = 4, contradiction
  intro hneg
  have : (3 : ZMod v) = (4 : ZMod v) := by
    -- apply `-` to both sides of `-3 = -4`
    simpa [neg_neg] using congrArg (fun x : ZMod v => -x) hneg
  exact h34 this

/-- If `21 ≤ v`, then `0, -3, -4 : ZMod v` are pairwise distinct. -/
lemma distinct_zero_neg3_neg4_of_le_twentyone {v : ℕ} (hv : 21 ≤ v) :
    (0 : ZMod v) ≠ (-3 : ZMod v) ∧
    (0 : ZMod v) ≠ (-4 : ZMod v) ∧
    (-3 : ZMod v) ≠ (-4 : ZMod v) := by
  exact
    ⟨ not_modEq_zero_neg_three_of_le_twentyone (v := v) hv
    , not_modEq_zero_neg_four_of_le_twentyone (v := v) hv
    , not_modEq_neg_three_neg_four_of_le_twentyone (v := v) hv ⟩

/-- If a finite set `B : Set ℤ` has size `x` and contains `0`,
then `x ≥ 1`. -/
lemma x_ge_1_of_mem_0
    {B : Set ℤ} {x : ℕ}
    (hfin : B.Finite)
    (hcard : B.ncard = x)
    (h1 : 0 ∈ B) :
    1 ≤ x := by
  classical
  let T : Finset ℤ := {0}
  have hT_card : T.card = 1 := by simp [T]

  -- `T ⊆ hfin.toFinset`
  have hT_subset : T ⊆ hfin.toFinset := by
    intro x hx
    have hx_cases : x = 0 := by
      simpa [T, Finset.mem_insert, Finset.mem_singleton] using hx
    have hxB : x ∈ B := by
      rcases hx_cases with rfl
      · simpa using h1
    simpa [Set.mem_toFinset] using hxB

  -- From the subset, deduce `1 ≤ (hfin.toFinset).card`
  have h1le_toFin : 1 ≤ (hfin.toFinset).card := by
    have := Finset.card_mono hT_subset
    simpa [hT_card] using this

  -- Bridge `ncard` and `toFinset.card`
  have hBcard : B.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card (α := ℤ) (s := B) (hs := hfin)

  -- Hence `1 ≤ B.ncard`
  have h1le_ncard : 1 ≤ B.ncard := by
    simpa [hBcard] using h1le_toFin

  -- And thus `1 ≤ x`
  have : 1 ≤ x := by simpa [hcard] using h1le_ncard
  exact this

/-- If `B` is a perfect difference set modulo `v`, `B` is finite with `#B = q+1`,
and `-8, -6, 0, 1, 4 ∈ B`, then `q` is even. -/
lemma q_even_of_pds_mem_neg8_neg6_0_1_4
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hneg8 : (-8 : ℤ) ∈ B) (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B) (h1mem : (1 : ℤ) ∈ B) (h4 : (4 : ℤ) ∈ B) :
    Even q := by
  classical
  -- From the membership pattern we know `4 ≤ q`.
  have hq4 : 4 ≤ q :=
    q_ge_three_of_mem_hall (B := B) (q := q) hfin hcard hneg8 hneg6 h0 h1mem h4

  -- From PDS and the size relation we have `v = q^2 + q + 1`.
  have hv_eq : q*q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ
      (B := B) (v := v) (q := q) hPDS hfin hcard

  -- Hence `21 ≤ v` (since `4 ≤ q`).
  have hv21 : 21 ≤ v :=
    twentyone_le_of_v_eq_qsq_add_q_add_one
      (q := q) (v := v) (hv := hv_eq.symm) (hq := hq4)

  -- Small bounds for the geometry lemma.
  have hv3 : 3 ≤ v := le_trans (by decide : 3 ≤ 21) hv21
  have hq3 : 3 ≤ q + 1 := by
    have : 2 ≤ q := le_trans (by decide : 2 ≤ 4) hq4
    exact Nat.succ_le_succ this

  -- When `21 ≤ v`, the residues 0, -3, -4 are pairwise distinct in `ZMod v`.
  have hdist := distinct_zero_neg3_neg4_of_le_twentyone (v := v) hv21
  have h0_ne_m3   : (0  : ZMod v) ≠ (-3 : ZMod v) := hdist.1
  have h0_ne_m4   : (0  : ZMod v) ≠ (-4 : ZMod v) := hdist.2.1
  have hm3_ne_m4  : (-3 : ZMod v) ≠ (-4 : ZMod v) := hdist.2.2

  -- Show `q % 2 = 0` by excluding the odd case via the “two-of-three equal” lemma.
  have hq_mod2_zero : q % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
    · exact hq0
    · have hdisj :=
        two_of_neg4_neg3_0_equal_mod_v_of_mem_neg8_neg6_0_1_4
          (B := B) (v := v) (q := q)
          hv3 hPDS hfin hcard hq3 (hq_odd := hq1)
          hneg8 hneg6 h0 h1mem h4
      rcases hdisj with hEq₁ | hEq₂ | hEq₃
      · exact (hm3_ne_m4 (by simpa using hEq₁.symm)).elim
      · exact (h0_ne_m4 (by simpa using hEq₂.symm)).elim
      · exact (h0_ne_m3 (by simpa using hEq₃.symm)).elim

  -- Convert `q % 2 = 0` to `Even q`.
  exact (Nat.even_iff.mpr hq_mod2_zero)

/-- Even-order consequence with global cardinalities:
If `2 ≤ q`, `q` is even, and there are exactly `q+1` absolute points,
then there exists a line all of whose points are absolute. -/
lemma exists_line_all_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    (hq_ge2 : 2 ≤ q) :
  ∃ ℓ : L, ∀ p : P, p ∈ ℓ → p ∈ polarity_absolutePoints C := by
  classical
  -- A finite witness for the absolute-points set (subset of a finite type)
  have hFin : (polarity_absolutePoints C).Finite :=
    (Set.finite_univ : (Set.univ : Set P).Finite).subset (by intro x _; trivial)

  -- Work with the absolute-points finset coming from that witness
  let S : Finset P := hFin.toFinset

  -- First, turn `ncard` into `S.card`
  have h_ncard_eq_Scard :
      (polarity_absolutePoints C).ncard = S.card := by
    simpa [S] using ncard_toFinset (α := P) (S := polarity_absolutePoints C) (hS := hFin)

  -- Now rewrite your hypothesis to a `Finset.card` statement
  have hScard : S.card = q + 1 := by
    -- `hAbsPts : (polarity_absolutePoints C).ncard = q + 1`
    -- rewrite the left side using `h_ncard_eq_Scard`
    simpa [h_ncard_eq_Scard] using hAbsPts

  -- `q ≥ 2` ⇒ `S.card = q+1 ≥ 3`, hence certainly `≥ 2`
  have hScard_ge3 : 3 ≤ S.card := by
    have : 3 ≤ q + 1 := Nat.succ_le_succ hq_ge2
    simpa [hScard] using this
  have hScard_ge2 : 2 ≤ S.card :=
    le_trans (by decide : 2 ≤ 3) hScard_ge3

  -- From `2 ≤ S.card` we get `0 < S.card`, hence `S.Nonempty`.
  have hS_pos : 0 < S.card := lt_of_lt_of_le (by decide : 0 < 2) hScard_ge2
  have hS_nonempty : S.Nonempty := Finset.card_pos.mp hS_pos

  -- from `0 < S.card` get `S.Nonempty`, then pick `p₁ ∈ S`
  have hS_nonempty : S.Nonempty := Finset.card_pos.mp hS_pos
  rcases hS_nonempty with ⟨p₁, hp₁S⟩

  -- since `2 ≤ S.card`, we also have `1 < S.card`
  have h1lt : 1 < S.card := lt_of_lt_of_le (by decide : 1 < 2) hScard_ge2

  -- pick a second, distinct element `p₂ ∈ S`
  obtain ⟨p₂, hp₂S, hp₁_ne_hp₂⟩ :
      ∃ p₂, p₂ ∈ S ∧ p₂ ≠ p₁ :=
    S.exists_mem_ne h1lt p₁

  -- Unpack to set-membership: both are absolute points
  have hp₁_abs : p₁ ∈ polarity_absolutePoints C := (hFin.mem_toFinset).1 hp₁S
  have hp₂_abs : p₂ ∈ polarity_absolutePoints C := (hFin.mem_toFinset).1 hp₂S

  -- The line determined by p₁ and p₂
  let ℓ : L :=
    Configuration.HasLines.mkLine (P := P) (L := L) (p₁ := p₁) (p₂ := p₂)
      hp₁_ne_hp₂.symm

  -- Both points lie on that line (from the axiom)
  have hp₁ℓ : p₁ ∈ ℓ :=
    (Configuration.HasLines.mkLine_ax (p₁ := p₁) (p₂ := p₂)
      (h := hp₁_ne_hp₂.symm)).1
  have hp₂ℓ : p₂ ∈ ℓ :=
    (Configuration.HasLines.mkLine_ax (p₁ := p₁) (p₂ := p₂)
      (h := hp₁_ne_hp₂.symm)).2
  -- Now apply the 2⇒all lemma
  refine ⟨ℓ, ?_⟩
  intro p hpℓ
  have hall :=
    all_points_on_line_abs_of_two_absPoints_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even) (hAbsPts := hAbsPts)
      (ℓ := ℓ) (p₁ := p₁) (p₂ := p₂)
      (hp₁_abs := hp₁_abs) (hp₂_abs := hp₂_abs)
      (hp₁ℓ := hp₁ℓ) (hp₂ℓ := hp₂ℓ) (hp₁_ne_hp₂ := hp₁_ne_hp₂.symm)
  exact hall p hpℓ

/-- If `2 ≤ q`, `q` is even, and there are exactly `q+1` absolute points, then
there exists a line that contains **all** absolute points. -/
lemma exists_line_containing_all_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L] [Finite P] [Finite L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    (hq_ge2 : 2 ≤ q) :
  ∃ ℓ : L, polarity_absolutePoints C ⊆ {p : P | p ∈ ℓ} := by
  classical
  -- 1) pick a line all of whose points are absolute
  obtain ⟨ℓ, hall⟩ :=
    exists_line_all_absPoints_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even)
      (hAbsPts := hAbsPts) (hq_ge2 := hq_ge2)

  -- We'll show equality of sets by two inclusions; we already have `{p | p ∈ ℓ} ⊆ abs` via `hall`.
  -- Define `Sℓ := {p | p ∈ ℓ}` as a set of points.
  let Sℓ : Set P := {p : P | p ∈ ℓ}

  -- (i) `Sℓ ⊆ absolutePoints`
  have h₁ : Sℓ ⊆ polarity_absolutePoints C := by
    intro p hp
    exact hall p hp

  -- (ii) Cardinalities match: `#Sℓ = q+1 = #(absolutePoints)`
  -- Use your `pointCount_eq` and the usual identification `pointCount P ℓ = (Sℓ).ncard`.
  have hSℓ_card : Sℓ.ncard = q + 1 := by
    simpa [horder] using (Configuration.ProjectivePlane.pointCount_eq (P := P) (L := L) (l := ℓ))

  -- Since `Sℓ ⊆ absolutePoints` and both have the same finite cardinality, they are equal.
  have h_eq : Sℓ = polarity_absolutePoints C := by
    apply Set.Subset.antisymm
    · exact h₁
    · -- show `abs ⊆ Sℓ`
      intro x hx_abs
      by_contra hx_not
      -- `Sℓ ⊆ abs \ {x}`
      have h_sub : Sℓ ⊆ (polarity_absolutePoints C \ {x}) := by
        intro y hyℓ
        refine And.intro (h₁ hyℓ) ?_
        -- `y ≠ x` since `x ∉ Sℓ`
        have : y ≠ x := by
          intro h; subst h; exact hx_not hyℓ
        simp [Set.mem_singleton_iff, this]
      -- cardinalities: `Sℓ.ncard ≤ (abs \ {x}).ncard`
      have h_le : Sℓ.ncard ≤ (polarity_absolutePoints C \ {x}).ncard :=
        Set.ncard_mono h_sub
      -- compute `ncard (abs \ {x}) = q`
      have h_fin_abs : (polarity_absolutePoints C).Finite :=
        (Set.finite_univ : (Set.univ : Set P).Finite).subset (by intro _ _; trivial)
      -- `x ∈ abs` so removing `x` drops the count by exactly 1
      have h_diff :
          (polarity_absolutePoints C \ {x}).ncard = q := by
        -- first: (abs \ {x}).ncard + 1 = abs.ncard
        have hx_add :
            (polarity_absolutePoints C \ {x}).ncard + 1
              = (polarity_absolutePoints C).ncard := by
          -- your lemma:
          simpa using
            (Set.ncard_diff_singleton_add_one
              (s := polarity_absolutePoints C) (a := x) (h := hx_abs))
        -- now cancel the +1 using succ-injectivity
        -- since `n + 1 = succ n`
        have hx_succ :
            ((polarity_absolutePoints C \ {x}).ncard).succ = (q).succ := by
          simpa [Nat.succ_eq_add_one, hAbsPts] using hx_add
        exact Nat.succ.inj hx_succ
      -- contradiction with `Sℓ.ncard = q+1`
      have : q + 1 ≤ q := by
        simp [hSℓ_card, h_diff] at h_le
      exact Nat.not_succ_le_self q this

  -- Return the line and the (now trivial) inclusion
  refine ⟨ℓ, ?_⟩
  -- rewrite the goal using `h_eq : Sℓ = polarity_absolutePoints C`
  have : polarity_absolutePoints C ⊆ Sℓ := by
    simp [h_eq]
  simpa [Sℓ] using this

/-- If `2 ≤ q`, `q` is even, and there are exactly `q+1` absolute points, then:
whenever `ℓ` contains two distinct absolute points `p₁, p₂`, **every**
absolute point lies on `ℓ`. -/
lemma absPoint_mem_line_of_two_absPoints_of_order_even
    {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L] [Finite P] [Finite L]
    (C : Polarity P L)
    (q : ℕ)
    (horder : Configuration.ProjectivePlane.order P L = q)
    (hq_even : q % 2 = 0)
    (hAbsPts : (polarity_absolutePoints C).ncard = q + 1)
    (hq_ge2 : 2 ≤ q)
    {ℓ : L} {p p₁ p₂ : P}
    (hp₁_abs : p₁ ∈ polarity_absolutePoints C)
    (hp₂_abs : p₂ ∈ polarity_absolutePoints C)
    (hp₁ℓ : p₁ ∈ ℓ) (hp₂ℓ : p₂ ∈ ℓ)
    (hp₁_ne_hp₂ : p₁ ≠ p₂)
    (hp_abs : p ∈ polarity_absolutePoints C) :
    p ∈ ℓ := by
  classical
  -- 1) A line containing *all* absolute points
  obtain ⟨ℓ₀, hAbs_sub_ℓ₀⟩ :=
    exists_line_containing_all_absPoints_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even)
      (hAbsPts := hAbsPts) (hq_ge2 := hq_ge2)
  -- 2) Every point of `ℓ` is absolute (since `ℓ` has two distinct absolute points)
  have hall_on_ℓ :
      ∀ x : P, x ∈ ℓ → x ∈ polarity_absolutePoints C :=
    all_points_on_line_abs_of_two_absPoints_of_order_even
      (C := C) (q := q) (horder := horder) (hq_even := hq_even) (hAbsPts := hAbsPts)
      (ℓ := ℓ) (p₁ := p₁) (p₂ := p₂)
      (hp₁_abs := hp₁_abs) (hp₂_abs := hp₂_abs)
      (hp₁ℓ := hp₁ℓ) (hp₂ℓ := hp₂ℓ) (hp₁_ne_hp₂ := hp₁_ne_hp₂)

  -- 3) Regard the point sets of `ℓ` and `ℓ₀` as actual `Set P`
  let Sℓ  : Set P := {x | x ∈ ℓ}
  let Sℓ₀ : Set P := {x | x ∈ ℓ₀}

  -- `Sℓ ⊆ abs` and `abs ⊆ Sℓ₀` ⇒ `Sℓ ⊆ Sℓ₀`
  have h_sub : Sℓ ⊆ Sℓ₀ := by
    intro x hx
    exact hAbs_sub_ℓ₀ (hall_on_ℓ x hx)

  -- 4) Both lines have `q+1` points (by `pointCount_eq`)
  have h_card_ℓ  : Sℓ.ncard  = q + 1 := by
    simpa [horder] using (Configuration.ProjectivePlane.pointCount_eq (P := P) (L := L) (l := ℓ))
  have h_card_ℓ₀ : Sℓ₀.ncard = q + 1 := by
    simpa [horder] using (Configuration.ProjectivePlane.pointCount_eq (P := P) (L := L) (l := ℓ₀))

  -- 5) From `Sℓ ⊆ Sℓ₀` and equal finite cardinalities, we get `Sℓ = Sℓ₀`
  have h_eq : Sℓ = Sℓ₀ := by
    apply Set.Subset.antisymm
    · exact h_sub
    · -- `Sℓ₀ ⊆ Sℓ` by a standard `ncard` contradiction if not
      intro x hxℓ₀
      by_contra hx_not
      -- Then `Sℓ ⊆ Sℓ₀ \ {x}`
      have h_sub' : Sℓ ⊆ (Sℓ₀ \ {x}) := by
        intro y hyℓ
        refine And.intro (h_sub hyℓ) ?_
        have : y ≠ x := by intro h; subst h; exact hx_not hyℓ
        simp [Set.mem_singleton_iff, this]
      -- Compare cards: `Sℓ.ncard ≤ (Sℓ₀ \ {x}).ncard = q`
      have h_le : Sℓ.ncard ≤ (Sℓ₀ \ {x}).ncard := Set.ncard_mono h_sub'
      -- compute `(Sℓ₀ \ {x}).ncard = q` from `h_card_ℓ₀`
      have hx_add :
          (Sℓ₀ \ {x}).ncard + 1 = Sℓ₀.ncard :=
        Set.ncard_diff_singleton_add_one
          (s := Sℓ₀) (a := x) (h := hxℓ₀)
      have hx_succ :
          ((Sℓ₀ \ {x}).ncard).succ = (q).succ := by
        simpa [Nat.succ_eq_add_one, h_card_ℓ₀] using hx_add
      have h_diff : (Sℓ₀ \ {x}).ncard = q := Nat.succ.inj hx_succ
      -- contradiction with `Sℓ.ncard = q+1`
      have : q + 1 ≤ q := by simp [h_card_ℓ, h_diff] at h_le
      exact Nat.not_succ_le_self q this

  -- 6) Any absolute point lies on `ℓ₀`, hence (by `h_eq`) on `ℓ`
  have hp_on_ℓ₀ : p ∈ ℓ₀ := hAbs_sub_ℓ₀ hp_abs
  -- rewrite the goal via `h_eq`
  have : p ∈ Sℓ := by simpa [h_eq] using hp_on_ℓ₀
  simpa [Sℓ] using this

/-- If `B` is a PDS modulo `v`, `B` is finite with `#B = q+1`, `q` is even,
and `-8, -6, 0, 1, 4 ∈ B`, then `(6 : ZMod v)` lies on the line `pdsLine B v 0`. -/
lemma six_on_line_zero_of_two_abs_on_line_neg4_even
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    (hq_even : q % 2 = 0)
    (hneg8 : (-8 : ℤ) ∈ B) (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B) (h1 : (1 : ℤ) ∈ B) (h4 : (4 : ℤ) ∈ B) :
    (6 : ZMod v) ∈ pdsLine B v 0 := by
  classical
  -- Put the PDS plane structure in scope
  letI : Membership (ZMod v) (ZMod v) := pdsMembershipFlipped B v
  letI : Configuration.ProjectivePlane (ZMod v) (ZMod v) :=
    pdsProjectivePlane (B := B) (v := v) (q := q) hv3 hPDS hfin hcard hq3

  ------------------------------------------------------------------------------
  -- (1) Absolute points: from `-8,-6,0,4 ∈ B` we get `-4,-3,0,2` are absolute
  ------------------------------------------------------------------------------
  have ⟨hAbs_m4, hAbs_m3, hAbs_0, hAbs_2⟩ :=
    abs_neg4_neg3_0_2_of_mem_neg8_neg6_0_4
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 hneg8 hneg6 h0 h4

  ------------------------------------------------------------------------------
  -- (2) Collinearity: from `0,1,4 ∈ B` we get `-4,-3,0` lie on `ℓ := pdsLine (-4)`
  ------------------------------------------------------------------------------
  have ⟨hℓ_m4, hℓ_m3, hℓ_0⟩ :=
    neg4_neg3_0_mem_pdsLine_neg4_of_mem (B := B) (v := v) h0 h1 h4
  let ℓ : ZMod v := (-4 : ZMod v)

  ------------------------------------------------------------------------------
  -- (3) Plane order and absolute-point count
  ------------------------------------------------------------------------------
  -- Order is `q`
  have horder :
      Configuration.ProjectivePlane.order (ZMod v) (ZMod v) = q :=
    pdsProjectivePlane_order_eq (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3

  -- In PDS geometry (neg polarity), there are exactly `q+1` absolute points.
  -- (This uses `v % 2 = 1`, which holds for PDS parameters.)
  have hodd_v : v % 2 = 1 :=
    IsPerfectDifferenceSetModulo.mod_two_eq_one (B := B) (v := v) (q := q)
      hPDS hfin hcard
  have hAbsPtsCard :
      (polarity_absolutePoints
        (pdsNegPolarity (B := B) (v := v) (q := q)
            hv3 hPDS hfin hcard hq3)).ncard = q + 1 :=
    ncard_absolutePoints_pdsNegPolarity
      (B := B) (v := v) (q := q) hv3 hodd_v hPDS hfin hcard hq3

  -- From `3 ≤ q+1` we get `2 ≤ q`
  have hq_ge2 : 2 ≤ q := by
    -- `Nat.succ_le_succ_iff` on `3 ≤ q+1` gives `2 ≤ q`
    simpa using (Nat.succ_le_succ_iff.mp hq3)

  ------------------------------------------------------------------------------
  -- (4) Distinctness of the two absolute points on ℓ: need `(-4) ≠ 0` in `ZMod v`
  ------------------------------------------------------------------------------
  -- From membership pattern we can ensure `q ≥ 4`, hence `v = q^2+q+1 ≥ 21`,
  -- so `0, -3, -4` are pairwise distinct mod `v`.
  have hq4 : 4 ≤ q :=
    q_ge_three_of_mem_hall (B := B) (q := q) hfin hcard hneg8 hneg6 h0 h1 h4
  have hv_eq : q*q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ (B := B) (v := v) (q := q)
      hPDS hfin hcard
  have hv21 : 21 ≤ v :=
    twentyone_le_of_v_eq_qsq_add_q_add_one (q := q) (v := v)
      (hv := hv_eq.symm) (hq := hq4)
  have h0_ne_m4 : (0 : ZMod v) ≠ (-4 : ZMod v) :=
    (distinct_zero_neg3_neg4_of_le_twentyone (v := v) hv21).2.1
  have h_m4_ne_0 : (-4 : ZMod v) ≠ (0 : ZMod v) := by
    simpa [ne_comm] using h0_ne_m4

  ------------------------------------------------------------------------------
  -- (5) Use the even-order lemma: every absolute point lies on ℓ
  --     once two distinct absolutes `-4` and `0` lie on ℓ.
  ------------------------------------------------------------------------------
  have h2_on_ℓ :
      (2 : ZMod v) ∈ pdsLine B v ℓ :=
    absPoint_mem_line_of_two_absPoints_of_order_even
      (P := ZMod v) (L := ZMod v)
      (C := pdsNegPolarity (B := B) (v := v) (q := q)
              hv3 hPDS hfin hcard hq3)
      (q := q)
      horder hq_even hAbsPtsCard hq_ge2
      (ℓ := ℓ) (p := (2 : ZMod v)) (p₁ := (-4 : ZMod v)) (p₂ := (0 : ZMod v))
      (hp₁_abs := hAbs_m4) (hp₂_abs := hAbs_0)
      (hp₁ℓ := by simpa using hℓ_m4)
      (hp₂ℓ := by simpa using hℓ_0)
      (hp₁_ne_hp₂ := h_m4_ne_0)
      (hp_abs := hAbs_2)

  ------------------------------------------------------------------------------
  -- (6) Translate from ℓ = -4 to 0: `2 ∈ line(-4)` ⇒ `6 ∈ line(0)`
  ------------------------------------------------------------------------------
  have h6_on0 : (6 : ZMod v) ∈ pdsLine B v 0 :=
    two_on_line_neg4_implies_six_on_line_zero (B := B) (v := v) h2_on_ℓ
  simpa using h6_on0

lemma exists_b_of_on_line_zero
    {B : Set ℤ} {v : ℕ} {s : ZMod v}
    (h : s ∈ pdsLine B v 0) :
    ∃ b ∈ B, s = (b : ZMod v) := by
  classical
  rcases (mem_pdsLine_iff_sub_coe_mem B v s 0).mp h with ⟨b, hbB, hs⟩
  exact ⟨b, hbB, by simpa [sub_eq_add_neg] using hs⟩

/-- If `B` is a PDS modulo `v`, `B` is finite with `#B = q+1`, `q` is even,
and `-8, -6, 0, 1, 4 ∈ B`, then we get a contradiction. -/
lemma no_pds_even_q_of_mem_neg8_neg6_0_1_4
    {B : Set ℤ} {v q : ℕ} [NeZero v]
    (hv3 : 3 ≤ v)
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hfin : B.Finite)
    (hcard : B.ncard = q + 1)
    (hq3 : 3 ≤ q + 1)
    (hq_even : q % 2 = 0)
    (hneg8 : (-8 : ℤ) ∈ B) (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B) (h1 : (1 : ℤ) ∈ B) (h4 : (4 : ℤ) ∈ B) :
    False := by
  classical
  -- From the even-order line lemma, 6 lies on the 0-line.
  have h6_on0 : (6 : ZMod v) ∈ pdsLine B v 0 :=
    six_on_line_zero_of_two_abs_on_line_neg4_even
      (B := B) (v := v) (q := q)
      hv3 hPDS hfin hcard hq3 hq_even hneg8 hneg6 h0 h1 h4
  -- Membership on the 0-line gives a representing `b ∈ B` for 6.
  rcases exists_b_of_on_line_zero (s := 6) (B := B) (v := v) h6_on0 with ⟨b, hbB, h6eq⟩
  -- But having -6, 0 ∈ B and a representative for 6 contradicts PDS.
  exact
    not_pds_of_mem_neg6_0_and_rep6
      (B := B) (v := v) hPDS hneg6 h0 ⟨b, hbB, h6eq⟩

/-- If `B` is a PDS modulo `v` and `-8,-6,0,1,4 ∈ B`, then contradiction.
This version *derives* the needed bounds `3 ≤ v` and `3 ≤ q+1` using the
three helper lemmas you provided. -/
lemma no_pds_of_mem_neg8_neg6_0_1_4_autobounds
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (hneg8 : (-8 : ℤ) ∈ B) (hneg6 : (-6 : ℤ) ∈ B)
    (h0 : (0 : ℤ) ∈ B) (h1 : (1 : ℤ) ∈ B) (h4 : (4 : ℤ) ∈ B) :
    False := by
  -- Finite from PDS
  have hfin : B.Finite := IsPerfectDifferenceSetModulo.finite (B := B) (v := v) (h := hPDS)

  -- Let q := #B - 1, and get `#B = q+1`
  let q : ℕ := B.ncard - 1
  -- From `0 ∈ B`, we know `1 ≤ #B`, so `#B = q+1`.
  have hpos : 1 ≤ B.ncard :=
    x_ge_1_of_mem_0 (B := B) (x := B.ncard) (hfin := hfin) (hcard := rfl) (h1 := h0)
  have hcard : B.ncard = q + 1 := by
    have hpos' : 0 < B.ncard := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hpos
    simpa [q, Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hpos').symm

  -- q is even (your parity lemma)
  have hq_even' : Even q :=
    q_even_of_pds_mem_neg8_neg6_0_1_4
      (B := B) (v := v) (q := q)
      (hPDS := hPDS) (hfin := hfin) (hcard := hcard)
      (hneg8 := hneg8) (hneg6 := hneg6) (h0 := h0) (h1mem := h1) (h4 := h4)
  -- Convert to `q % 2 = 0`
  have hq_even : q % 2 = 0 := by
    rcases hq_even' with ⟨k, hk⟩
    have : 2 ∣ q := ⟨k, by simp [two_mul, hk]⟩
    exact Nat.mod_eq_zero_of_dvd this

  -- Lower bound on q from your counting lemma on members
  have hq_ge4 : 4 ≤ q :=
    q_ge_three_of_mem_hall
      (B := B) (q := q)
      (hfin := hfin) (hcard := hcard)
      (hneg8 := hneg8) (hneg6 := hneg6) (h0 := h0) (h1 := h1) (h4 := h4)

  -- From 4 ≤ q get 2 ≤ q
  have h2q : 2 ≤ q := le_trans (by decide : 2 ≤ 4) hq_ge4

  -- Hence 3 ≤ q+1
  have hq3 : 3 ≤ q + 1 := Nat.succ_le_succ h2q

  -- Identify `v = q^2 + q + 1` from your cardinality-param lemma
  have hv_eq : q*q + q + 1 = v :=
    IsPerfectDifferenceSetModulo.card_param_eq_succ
      (B := B) (v := v) (q := q) (h := hPDS) (hfin := hfin) (hcard := hcard)

  -- From `4 ≤ q`, deduce `21 ≤ v`, hence `3 ≤ v`
  have hv21 : 21 ≤ v :=
    twentyone_le_of_v_eq_qsq_add_q_add_one (hv := hv_eq.symm) (hq := hq_ge4)
  have hv3  : 3 ≤ v := le_trans (by decide : 3 ≤ 21) hv21

  -- Conclude by your “even q ⇒ contradiction” lemma
  exact
    no_pds_even_q_of_mem_neg8_neg6_0_1_4
      (B := B) (v := v) (q := q)
      (hv3 := hv3) (hPDS := hPDS) (hfin := hfin) (hcard := hcard)
      (hq3 := hq3) (hq_even := hq_even)
      (hneg8 := hneg8) (hneg6 := hneg6)
      (h0 := h0) (h1 := h1) (h4 := h4)

/-- Translating a perfect difference set by an integer preserves the property. -/
lemma IsPerfectDifferenceSetModulo.translate_right
    {B : Set ℤ} {v : ℕ} (h : IsPerfectDifferenceSetModulo B v) (c : ℤ) :
    IsPerfectDifferenceSetModulo ((fun x : ℤ => x + c) '' B) v := by
  classical
  -- Abbreviations
  let A  : Set (ℤ × ℤ) := B.offDiag
  let A' : Set (ℤ × ℤ) := ((fun x : ℤ => x + c) '' B).offDiag
  let f  : ℤ × ℤ → ZMod v := fun p => (p.1 - p.2 : ZMod v)

  -- `h` is the original bijection statement on `A` to `{x | x ≠ 0}`
  rcases h with ⟨h_maps, h_inj, h_surj⟩

  -- We’ll show `BijOn f A' {x | x ≠ 0}` by giving the three fields.
  refine ⟨?maps, ?inj, ?surj⟩

  -- 1) MapsTo: `f` sends `A'` into `{x | x ≠ 0}`
  · intro p hp
    -- A' membership, but you've (likely) simplified image-membership to preimage form
    obtain ⟨hp1, hp2, hpne⟩ :=
      (by simpa [A', Set.offDiag, Set.mem_setOf] using hp)
      -- here `hp1 : p.1 - c ∈ B` and `hp2 : p.2 - c ∈ B`

    -- name the canonical preimages
    set a : ℤ := p.1 - c with ha_def
    set b : ℤ := p.2 - c with hb_def

    have haB : a ∈ B := by simpa [ha_def] using hp1
    have hbB : b ∈ B := by simpa [hb_def] using hp2

    -- equalities cancelling the translate
    have h1 : a + c = p.1 := by
      -- (p.1 - c) + c = p.1
      simp [ha_def, sub_eq_add_neg]
    have h2 : b + c = p.2 := by
      simp [hb_def, sub_eq_add_neg]

    -- if a=b then (a+c)=(b+c), hence p.1=p.2, contradicting `hpne`
    have hne_ab : a ≠ b := by
      intro h
      -- from `a = b` get `(a + c) = (b + c)`
      have habc : a + c = b + c := by simp [h]
      -- rewrite to `p.1 = p.2` using `h1 : a + c = p.1` and `h2 : b + c = p.2`
      have h12 : p.1 = p.2 := by simpa [h1, h2] using habc
      exact hpne h12

    -- back in the original offDiag
    have hA : (a, b) ∈ A := by
      simpa [A, Set.offDiag, Set.mem_setOf] using And.intro haB (And.intro hbB hne_ab)

    -- relate `f p` to `f (a,b)` and use the original MapsTo
    have hfp_eq : f p = f (a + c, b + c) := by
      rcases p with ⟨p1, p2⟩
      simp [f, h1, h2]

    have hcancel : f (a + c, b + c) = f (a, b) := by
      dsimp [f]
      -- goal: ↑(a + c) - ↑(b + c) = ↑a - ↑b
      calc
        (↑(a + c) - ↑(b + c) : ZMod v)
            = ((↑a + ↑c) - (↑b + ↑c)) := by
                simp [Int.cast_add]
        _   = (↑a - ↑b) := by
                abel_nf

    -- Now close the MapsTo goal:
    have hAB : f (a, b) ∈ {x : ZMod v | x ≠ 0} := h_maps hA
    -- We already have:
    -- hfp_eq   : f p = f (a + c, b + c)
    -- hcancel  : f (a + c, b + c) = f (a, b)
    -- hAB      : f (a, b) ∈ {x | x ≠ 0}  i.e.  f (a, b) ≠ 0

    -- Step 1: move the `≠ 0` fact back to `f p`
    have hrewrite : f p = f (a, b) := hfp_eq.trans hcancel
    have hfp_ne : f p ≠ 0 := by
      simpa [hrewrite] using hAB  -- now `hfp_ne : f p ≠ 0`

    -- Step 2: unfold `f` at `p` to reach the goal `¬ (↑p.1 - ↑p.2) = 0`
    simpa [f] using hfp_ne

  -- 2) Injective on `A'`
  · intro p₁ hp₁ p₂ hp₂ hfeq
    -- unpack membership in the translated offDiag into preimage form
    obtain ⟨hp₁₁, hp₁₂, hp₁ne⟩ :=
      (by simpa [A', Set.offDiag, Set.mem_setOf] using hp₁)
    obtain ⟨hp₂₁, hp₂₂, hp₂ne⟩ :=
      (by simpa [A', Set.offDiag, Set.mem_setOf] using hp₂)
    -- where:
    -- hp₁₁ : p₁.1 - c ∈ B,  hp₁₂ : p₁.2 - c ∈ B
    -- hp₂₁ : p₂.1 - c ∈ B,  hp₂₂ : p₂.2 - c ∈ B

    -- choose canonical preimages
    classical
    set a₁ : ℤ := p₁.1 - c with ha₁def
    set b₁ : ℤ := p₁.2 - c with hb₁def
    set a₂ : ℤ := p₂.1 - c with ha₂def
    set b₂ : ℤ := p₂.2 - c with hb₂def

    have ha₁B : a₁ ∈ B := by simpa [ha₁def] using hp₁₁
    have hb₁B : b₁ ∈ B := by simpa [hb₁def] using hp₁₂
    have ha₂B : a₂ ∈ B := by simpa [ha₂def] using hp₂₁
    have hb₂B : b₂ ∈ B := by simpa [hb₂def] using hp₂₂

    -- undo the translate on coordinates
    have ha₁c : a₁ + c = p₁.1 := by simp [ha₁def, sub_eq_add_neg]
    have hb₁c : b₁ + c = p₁.2 := by simp [hb₁def, sub_eq_add_neg]
    have ha₂c : a₂ + c = p₂.1 := by simp [ha₂def, sub_eq_add_neg]
    have hb₂c : b₂ + c = p₂.2 := by simp [hb₂def, sub_eq_add_neg]

    -- non-diagonal after cancelling the translate
    have hne₁ : a₁ ≠ b₁ := by
      intro h
      exact hp₁ne (by
        -- a₁ = b₁ ⇒ a₁ + c = b₁ + c ⇒ p₁.1 = p₁.2
        simpa [ha₁c, hb₁c] using congrArg (fun t : ℤ => t + c) h)
    have hne₂ : a₂ ≠ b₂ := by
      intro h
      exact hp₂ne (by
        -- a₂ = b₂ ⇒ a₂ + c = b₂ + c ⇒ p₂.1 = p.2
        simpa [ha₂c, hb₂c] using congrArg (fun t : ℤ => t + c) h)

    -- membership in the original offDiag
    have hA₁ : (a₁, b₁) ∈ A := by
      simpa [A, Set.offDiag, Set.mem_setOf] using And.intro ha₁B (And.intro hb₁B hne₁)
    have hA₂ : (a₂, b₂) ∈ A := by
      simpa [A, Set.offDiag, Set.mem_setOf] using And.intro ha₂B (And.intro hb₂B hne₂)

    -- rewrite the given equality f p₁ = f p₂ into (a₁ - b₁) = (a₂ - b₂)
    have hfeq' : (a₁ - b₁ : ZMod v) = (a₂ - b₂ : ZMod v) := by
      -- first rewrite both sides to `(ai+ c) - (bi + c)`
      have h' := hfeq
      -- unfold and substitute coordinates
      cases p₁ with
      | mk p1 p2 =>
        cases p₂ with
        | mk q1 q2 =>
          -- turn f pᵢ into differences of (aᵢ+c) and (bᵢ+c)
          have := h'
          -- reduce to equality of those differences
          -- then cancel the translate on each side
          -- left:
          have hL :
            f (a₁ + c, b₁ + c) = (a₁ - b₁ : ZMod v) := by
            dsimp [f];  -- goal: ↑(a₁ + c) - ↑(b₁ + c) = ↑a₁ - ↑b₁
            calc
              (↑(a₁ + c) - ↑(b₁ + c) : ZMod v)
                  = ((↑a₁ + ↑c) - (↑b₁ + ↑c)) := by simp [Int.cast_add]
              _ = (↑a₁ - ↑b₁) := by abel_nf
          -- right:
          have hR :
            f (a₂ + c, b₂ + c) = (a₂ - b₂ : ZMod v) := by
            dsimp [f]
            calc
              (↑(a₂ + c) - ↑(b₂ + c) : ZMod v)
                  = ((↑a₂ + ↑c) - (↑b₂ + ↑c)) := by simp [Int.cast_add]
              _ = (↑a₂ - ↑b₂) := by abel_nf

          -- now use the original equality, rewritten via coordinate identities
          -- f p₁ = f p₂  ⇒  f (a₁+c,b₁+c) = f (a₂+c,b₂+c)
          have h'' : f (a₁ + c, b₁ + c) = f (a₂ + c, b₂ + c) := by
            simp [f, ha₁c, hb₁c, ha₂c, hb₂c] at h' ⊢
            exact h'
          -- cancel the translates using hL, hR
          simpa [hL, hR] using h''

    -- now injectivity back on `A`
    have hf_pre : f (a₁, b₁) = f (a₂, b₂) := by
      dsimp [f]; simpa using hfeq'
    have hpair : (a₁, b₁) = (a₂, b₂) := h_inj hA₁ hA₂ hf_pre
    -- conclude p₁ = p₂ by re-adding `c` componentwise
    apply Prod.ext
    · -- first coordinates
      have hfst : a₁ = a₂ := congrArg Prod.fst hpair
      -- add c and rewrite to p₁.1 = p₂.1
      have hfstc : a₁ + c = a₂ + c := by
        simpa using congrArg (fun t : ℤ => t + c) hfst
      simpa [ha₁c, ha₂c] using hfstc
    · -- second coordinates
      have hsnd : b₁ = b₂ := congrArg Prod.snd hpair
      have hsndc : b₁ + c = b₂ + c := by
        simpa using congrArg (fun t : ℤ => t + c) hsnd
      simpa [hb₁c, hb₂c] using hsndc

  -- 3) Surjective onto `{x | x ≠ 0}`
  · intro y hy
    -- Pull back along the inverse translation using surjectivity of `h`
    rcases h_surj hy with ⟨q, hqA, hqy⟩
    -- Write `q = (a, b)`
    rcases q with ⟨a, b⟩
    have hab :
        a ∈ B ∧ b ∈ B ∧ a ≠ b := by
      simpa [A, Set.offDiag, Set.mem_setOf] using hqA

    -- Build each conjunct explicitly, then package and `simpa`.
    have ha_img : (a + c) ∈ (fun x : ℤ => x + c) '' B :=
      ⟨a, hab.1, by simp⟩
    have hb_img : (b + c) ∈ (fun x : ℤ => x + c) '' B :=
      ⟨b, hab.2.1, by simp⟩
    have hne'   : (a + c) ≠ (b + c) := by
      intro h; exact hab.2.2 (add_right_cancel h)

    have hTriple :
        (a + c) ∈ (fun x : ℤ => x + c) '' B ∧
        (b + c) ∈ (fun x : ℤ => x + c) '' B ∧
        (a + c) ≠ (b + c) :=
      ⟨ha_img, hb_img, hne'⟩

    -- The translated pair lies in `A'`
    -- Now the membership in A' = (image B).offDiag
    have hA' : (a + c, b + c) ∈ A' := by
      simpa [A', Set.offDiag, Set.mem_setOf] using hTriple
    -- And its image under `f` is still `y`
    have hval : f (a + c, b + c) = y := by
      -- cancel translation inside ZMod
      have hcancel : f (a + c, b + c) = f (a, b) := by
        dsimp [f]
        -- goal: ↑(a + c) - ↑(b + c) = ↑a - ↑b
        calc
          (↑(a + c) - ↑(b + c) : ZMod v)
              = ((↑a + ↑c) - (↑b + ↑c)) := by
                  simp [Int.cast_add]
          _   = (↑a - ↑b) := by
                  abel_nf   -- or: simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      -- `hqy : f (a, b) = y` from surjectivity
      simpa [hcancel] using hqy

    exact ⟨(a + c, b + c), hA', hval⟩

/-- If `B` is a PDS modulo `v` and `1,3,9,10,13 ∈ B`, then contradiction. -/
lemma no_pds_of_mem_1_3_9_10_13
    {B : Set ℤ} {v : ℕ} [NeZero v]
    (hPDS : IsPerfectDifferenceSetModulo B v)
    (h1 : (1 : ℤ) ∈ B)
    (h3 : (3 : ℤ) ∈ B)
    (h9 : (9 : ℤ) ∈ B)
    (h10 : (10 : ℤ) ∈ B)
    (h13 : (13 : ℤ) ∈ B) :
    False := by
  -- Translate `B` by `-9`.
  let C : Set ℤ := (fun x : ℤ => x + (-9)) '' B
  -- Translation preserves the PDS property.
  have hPDS_C : IsPerfectDifferenceSetModulo C v :=
    IsPerfectDifferenceSetModulo.translate_right (B := B) (v := v) hPDS (-9)

  -- Show the five shifted members land in `C` as desired:
  have hC_neg8 : (-8 : ℤ) ∈ C := by
    refine ⟨(1 : ℤ), h1, ?_⟩
    simp

  have hC_neg6 : (-6 : ℤ) ∈ C := by
    refine ⟨(3 : ℤ), h3, ?_⟩
    simp

  have hC_0 : (0 : ℤ) ∈ C := by
    refine ⟨(9 : ℤ), h9, ?_⟩
    simp

  have hC_1 : (1 : ℤ) ∈ C := by
    refine ⟨(10 : ℤ), h10, ?_⟩
    simp

  have hC_4 : (4 : ℤ) ∈ C := by
    refine ⟨(13 : ℤ), h13, ?_⟩
    simp

  -- Now apply the `{−8, −6, 0, 1, 4}` autobounds-lemma to `C`.
  exact
    no_pds_of_mem_neg8_neg6_0_1_4_autobounds
      (B := C) (v := v)
      (hPDS := hPDS_C)
      (hneg8 := hC_neg8) (hneg6 := hC_neg6)
      (h0 := hC_0) (h1 := hC_1) (h4 := hC_4)

/-
Now we do prove a few things are Sidon sets and such.
-/
def counterexampleP : Set ℕ := {1, 2, 4, 8}
def counterexamplePFin : Finset ℕ := {1, 2, 4, 8}
def counterexampleAM : Set ℕ := {1, 2, 4, 8, 13}
def counterexampleAMFin : Finset ℕ := {1, 2, 4, 8, 13}
def counterexampleH : Set ℤ := {-8, -6, 0, 1, 4}
def counterexampleHFin : Finset ℤ := {-8, -6, 0, 1, 4}
def counterexampleH2 : Set ℕ := {1, 3, 9, 10, 13}
def counterexampleH2Fin : Finset ℕ := {1, 3, 9, 10, 13}

/-- `{1, 2, 4, 8}` is finite. -/
lemma counterexampleP_finite : counterexampleP.Finite := by
  classical
  simp [counterexampleP]-- using (counterexamplePFin.finite_toSet)

/-- `{1, 2, 4, 8, 13}` is finite. -/
lemma counterexampleAM_finite : counterexampleAM.Finite := by
  classical
  simp [counterexampleAM]

/-- `{-8, -6, 0, 1, 4}` is finite. -/
lemma counterexampleH_finite : counterexampleH.Finite := by
  classical
  simp [counterexampleH]

/-- `{1, 3, 9, 10, 13}` is finite. -/
lemma counterexampleH2_finite : counterexampleH2.Finite := by
  classical
  simp [counterexampleH2]

/--
The set `{1, 2, 4, 8}` is a Sidon set.
-/
lemma counterexampleP_Sidon : IsSidon (counterexampleP : Set ℕ) := by
  classical

  have quad :
      ∀ (i₁ i₂ j₁ j₂ : {x // x ∈ counterexamplePFin}),
        i₁.1 + i₂.1 = j₁.1 + j₂.1 →
        (i₁.1 = j₁.1 ∧ i₂.1 = j₂.1) ∨ (i₁.1 = j₂.1 ∧ i₂.1 = j₁.1) := by
    decide

  have toSetOfA : ∀ {x}, x ∈ counterexampleP → x ∈ counterexamplePFin := by
    intro x hx
    simpa [counterexamplePFin, Set.mem_insert, Set.mem_singleton_iff] using hx

  intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ hsum
  simpa using
    quad ⟨i₁, by simpa [Finset.mem_coe] using toSetOfA hi₁⟩
         ⟨i₂, by simpa [Finset.mem_coe] using toSetOfA hi₂⟩
         ⟨j₁, by simpa [Finset.mem_coe] using toSetOfA hj₁⟩
         ⟨j₂, by simpa [Finset.mem_coe] using toSetOfA hj₂⟩
         hsum

/--
The set `{1, 2, 4, 8, 13}` is a Sidon set.
-/
lemma counterexampleAM_Sidon : IsSidon (counterexampleAM : Set ℕ) := by
  classical

  have quad :
      ∀ (i₁ i₂ j₁ j₂ : {x // x ∈ counterexampleAMFin}),
        i₁.1 + i₂.1 = j₁.1 + j₂.1 →
        (i₁.1 = j₁.1 ∧ i₂.1 = j₂.1) ∨ (i₁.1 = j₂.1 ∧ i₂.1 = j₁.1) := by
    decide

  have toSetOfA : ∀ {x}, x ∈ counterexampleAM → x ∈ counterexampleAMFin := by
    intro x hx
    simpa [counterexampleAMFin, Set.mem_insert, Set.mem_singleton_iff] using hx

  intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ hsum
  simpa using
    quad ⟨i₁, by simpa [Finset.mem_coe] using toSetOfA hi₁⟩
         ⟨i₂, by simpa [Finset.mem_coe] using toSetOfA hi₂⟩
         ⟨j₁, by simpa [Finset.mem_coe] using toSetOfA hj₁⟩
         ⟨j₂, by simpa [Finset.mem_coe] using toSetOfA hj₂⟩
         hsum

/--
The set `{-8, -6, 0, 1, 4}` is a Sidon set.
-/
lemma counterexampleH_Sidon : IsSidon (counterexampleH : Set ℤ) := by
  classical

  have quad :
      ∀ (i₁ i₂ j₁ j₂ : {x // x ∈ counterexampleHFin}),
        i₁.1 + i₂.1 = j₁.1 + j₂.1 →
        (i₁.1 = j₁.1 ∧ i₂.1 = j₂.1) ∨ (i₁.1 = j₂.1 ∧ i₂.1 = j₁.1) := by
    decide

  have toSetOfA : ∀ {x}, x ∈ counterexampleH → x ∈ counterexampleHFin := by
    intro x hx
    simpa [counterexampleHFin, Set.mem_insert, Set.mem_singleton_iff] using hx

  intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ hsum
  simpa using
    quad ⟨i₁, by simpa [Finset.mem_coe] using toSetOfA hi₁⟩
         ⟨i₂, by simpa [Finset.mem_coe] using toSetOfA hi₂⟩
         ⟨j₁, by simpa [Finset.mem_coe] using toSetOfA hj₁⟩
         ⟨j₂, by simpa [Finset.mem_coe] using toSetOfA hj₂⟩
         hsum

/--
The set `{1, 3, 9, 10, 13}` is a Sidon set.
-/
lemma counterexampleH2_Sidon : IsSidon (counterexampleH2 : Set ℕ) := by
  classical

  have quad :
      ∀ (i₁ i₂ j₁ j₂ : {x // x ∈ counterexampleH2Fin}),
        i₁.1 + i₂.1 = j₁.1 + j₂.1 →
        (i₁.1 = j₁.1 ∧ i₂.1 = j₂.1) ∨ (i₁.1 = j₂.1 ∧ i₂.1 = j₁.1) := by
    decide

  have toSetOfA : ∀ {x}, x ∈ counterexampleH2 → x ∈ counterexampleH2Fin := by
    intro x hx
    simpa [counterexampleH2Fin, Set.mem_insert, Set.mem_singleton_iff] using hx

  intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ hsum
  simpa using
    quad ⟨i₁, by simpa [Finset.mem_coe] using toSetOfA hi₁⟩
         ⟨i₂, by simpa [Finset.mem_coe] using toSetOfA hi₂⟩
         ⟨j₁, by simpa [Finset.mem_coe] using toSetOfA hj₁⟩
         ⟨j₂, by simpa [Finset.mem_coe] using toSetOfA hj₂⟩
         hsum


/--
`{1,2,4,8}` does not extend to a perfect difference set of order `p^2+p+1`
for any prime `p`.
-/
lemma counterexampleP_noExt
    : ∀ (B : Set ℤ) (p : ℕ),
        ¬ (Nat.Prime p ∧ (↑) '' counterexampleP ⊆ B
           ∧ IsPerfectDifferenceSetModulo B (p * p + p + 1)) := by
  intro B p h
  rcases h with ⟨hp, hsub, hPDS⟩
  have h1B : 1 ∈ B := hsub (by simp [counterexampleP])
  have h2B : 2 ∈ B := hsub (by simp [counterexampleP])
  have h4B : 4 ∈ B := hsub (by simp [counterexampleP])
  have h8B : 8 ∈ B := hsub (by simp [counterexampleP])
  exact no_pds_with_1_2_4_8_members (B := B) (p := p)
    hp h1B h2B h4B h8B hPDS

/--
The set `{1, 2, 4, 8, 13}` cannot be embedded in a perfect difference set
(modulo v for some nonzero v).
-/
lemma counterexampleAM_noExt :
    ∀ B v, ¬ (v ≠ 0 ∧ (↑) '' counterexampleAM ⊆ B ∧ IsPerfectDifferenceSetModulo B v) := by
  intro B v h
  rcases h with ⟨hvnz, hsub, hPDS⟩
  -- turn `v ≠ 0` into a typeclass
  haveI : NeZero v := ⟨hvnz⟩
  -- pull the five elements into `B` via the subset hypothesis
  have h1  : 1  ∈ B := hsub (by simp [counterexampleAM])
  have h2  : 2  ∈ B := hsub (by simp [counterexampleAM])
  have h4  : 4  ∈ B := hsub (by simp [counterexampleAM])
  have h8  : 8  ∈ B := hsub (by simp [counterexampleAM])
  have h13 : 13 ∈ B := hsub (by simp [counterexampleAM])
  -- contradict the PDS assumption using your lemma
  exact
    no_pds_with_1_2_4_8_13_members_false
      (h1 := h1) (h2 := h2) (h4 := h4) (h8 := h8) (h13 := h13) (hPDS := hPDS)

/--
The set `{-8, -6, 0, 1, 4}` cannot be embedded in a perfect difference set
(modulo v for some nonzero v).
-/
lemma counterexampleH_noExt :
    ∀ B v, ¬ (v ≠ 0 ∧ counterexampleH ⊆ B ∧ IsPerfectDifferenceSetModulo B v) := by
  intro B v h
  rcases h with ⟨hv, hsub, hPDS⟩
  -- Use `v ≠ 0` to get the typeclass instance needed by the lemma.
  haveI : NeZero v := ⟨hv⟩

  -- Pull the five memberships into `B` via the subset hypothesis.
  have hneg8 : (-8 : ℤ) ∈ B := hsub (by simp [counterexampleH])
  have hneg6 : (-6 : ℤ) ∈ B := hsub (by simp [counterexampleH])
  have h0    : (0 : ℤ) ∈ B := hsub (by simp [counterexampleH])
  have h1    : (1 : ℤ) ∈ B := hsub (by simp [counterexampleH])
  have h4    : (4 : ℤ) ∈ B := hsub (by simp [counterexampleH])

  -- Conclude by your combined contradiction lemma.
  exact
    no_pds_of_mem_neg8_neg6_0_1_4_autobounds
      (B := B) (v := v)
      (hPDS := hPDS)
      (hneg8 := hneg8) (hneg6 := hneg6)
      (h0 := h0) (h1 := h1) (h4 := h4)

/--
The set `{1, 3, 9, 10, 13}` cannot be embedded in a perfect difference set
(modulo v for some nonzero v).
-/
lemma counterexampleH2_noExt :
    ∀ B v, ¬ (v ≠ 0 ∧ (↑) '' counterexampleH2 ⊆ B ∧ IsPerfectDifferenceSetModulo B v) := by
  intro B v h
  rcases h with ⟨hv, hsub, hPDS⟩
  -- Use `v ≠ 0` to get the typeclass instance needed by the lemma.
  haveI : NeZero v := ⟨hv⟩

  -- Pull the five memberships into `B` via the subset hypothesis.
  have h1  : 1  ∈ B := hsub (by simp [counterexampleH2])
  have h3  : 3  ∈ B := hsub (by simp [counterexampleH2])
  have h9  : 9  ∈ B := hsub (by simp [counterexampleH2])
  have h10 : 10 ∈ B := hsub (by simp [counterexampleH2])
  have h13 : 13 ∈ B := hsub (by simp [counterexampleH2])

  -- Conclude by your combined contradiction lemma.
  exact
    no_pds_of_mem_1_3_9_10_13
      (B := B) (v := v)
      (hPDS := hPDS)
      (h1 := h1) (h3 := h3)
      (h9 := h9) (h10 := h10) (h13 := h13)

/-
MAIN THEOREMS
-/

/--
**Erd\H{o}s problem 707**:
Any finite Sidon set of natural numbers can be embedded in a perfect difference
set modulo `v` for some `v ≠ 0`.
-/
def erdos_707 : Prop :=
  ∀ A : Set ℕ, A.Finite → IsSidon A →
    ∃ (B : Set ℤ) (v : ℕ),
      v ≠ 0 ∧
      (↑) '' A ⊆ B ∧
      IsPerfectDifferenceSetModulo B v

/--
**Erdős problem 707 (prime-modulus version)**:
Any finite Sidon set (of natural numbers) embeds in a perfect difference set
modulo `p^2 + p + 1` for some prime `p`.
-/
def erdos_707_prime : Prop :=
  ∀ (A : Set ℕ), A.Finite → IsSidon A →
    ∃ (B : Set ℤ) (p : ℕ),
      Nat.Prime p ∧
      (↑) '' A ⊆ B ∧
      IsPerfectDifferenceSetModulo B (p * p + p + 1)

/--
**Erdős problem 707 (allowing negatives)**:
Any finite Sidon set (of integers, possibly negative) can be embedded in
a perfect difference set modulo `v` for some `v ≠ 0`.
-/
def erdos_707_integer : Prop :=
  ∀ A : Set ℤ, A.Finite → IsSidon A →
    ∃ (B : Set ℤ) (v : ℕ),
      v ≠ 0 ∧
      A ⊆ B ∧
      IsPerfectDifferenceSetModulo B v

/-- If there exists a finite Sidon set `A` that does *not* extend to any perfect
difference set modulo any `v`, then `erdos_707` is false. -/
lemma not_erdos_707_given_counterexample
    (A : Set ℕ)
    (hA_fin : A.Finite)
    (hA_sidon : IsSidon A)
    (noExt : ∀ (B : Set ℤ) (v : ℕ),
               ¬ (v ≠ 0 ∧ (↑) '' A ⊆ B ∧ IsPerfectDifferenceSetModulo B v)) :
  ¬ erdos_707 := by
  intro h
  obtain ⟨B, v, hs⟩ := h A hA_fin hA_sidon
  exact noExt B v hs

/--
If there exists a finite Sidon set `A` that does *not* extend
to any perfect difference set modulo `p^2 + p + 1` for any prime `p`,
then `erdos_707_prime` is false.
-/
lemma not_erdos_707_prime_given_counterexample
    (A : Set ℕ)
    (hA_fin : A.Finite)
    (hA_sidon : IsSidon A)
    (noExt :
      ∀ (B : Set ℤ) (p : ℕ),
        ¬ (Nat.Prime p ∧ (↑) '' A ⊆ B ∧ IsPerfectDifferenceSetModulo B (p * p + p + 1))) :
  ¬ erdos_707_prime := by
  intro h
  obtain ⟨B, p, hs⟩ := h A hA_fin hA_sidon
  exact noExt B p hs

/-- If there exists a finite Sidon set `A` that does *not* extend to any perfect
difference set modulo any `v`, then `erdos_707` is false. -/
lemma not_erdos_707_integer_given_counterexample
    (A : Set ℤ)
    (hA_fin : A.Finite)
    (hA_sidon : IsSidon A)
    (noExt : ∀ (B : Set ℤ) (v : ℕ),
               ¬ (v ≠ 0 ∧ A ⊆ B ∧ IsPerfectDifferenceSetModulo B v)) :
  ¬ erdos_707_integer := by
  intro h
  obtain ⟨B, v, hs⟩ := h A hA_fin hA_sidon
  exact noExt B v hs

/--
The Sidon set {1, 2, 4, 8} does not extend to a perfect difference set
modulo p * p + p + 1 for any prime p.
-/
theorem not_erdos_707P : ¬ erdos_707_prime :=
  not_erdos_707_prime_given_counterexample
    counterexampleP
    counterexampleP_finite
    counterexampleP_Sidon
    counterexampleP_noExt

/--
(Hall 1947)
The Sidon set {-8, -6, 0, 1, 4} does not extend to a perfect difference set
modulo v for any nonnegative v.
-/
theorem not_erdos_707H : ¬ erdos_707_integer :=
  not_erdos_707_integer_given_counterexample
    counterexampleH
    counterexampleH_finite
    counterexampleH_Sidon
    counterexampleH_noExt

/--
(This is the previous example, translated into the positive integers.)
The Sidon set {1, 3, 9, 10, 13} = 9 + {-8, -6, 0, 1, 4} does not extend
to a perfect difference set modulo v for any nonnegative v.
-/
theorem not_erdos_707H2 : ¬ erdos_707 :=
  not_erdos_707_given_counterexample
    counterexampleH2
    counterexampleH2_finite
    counterexampleH2_Sidon
    counterexampleH2_noExt

/--
The Sidon set {1, 2, 4, 8, 13} does not extend to a perfect difference set
modulo v for any nonnegative v.
-/
theorem not_erdos_707AM : ¬ erdos_707 :=
  not_erdos_707_given_counterexample
    counterexampleAM
    counterexampleAM_finite
    counterexampleAM_Sidon
    counterexampleAM_noExt
