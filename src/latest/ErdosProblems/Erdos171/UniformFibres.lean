import ErdosProblems.Erdos171.Basic

/-!
# Uniform fibres by a finite energy-increment argument

This file proves the elementary uniform-fibres lemma used in the Dodos--
Kanellopoulos--Tyros proof of density Hales--Jewett.  The exact argument is
carried out with Mathlib's rational `Finset.dens`; a wrapper supplies real
inequalities for the rest of the development.
-/

namespace Erdos171

open scoped BigOperators

abbrev BlockTower.{u} (X Y : Type u) : Nat → Type u
  | 0 => Y
  | n + 1 => X × BlockTower X Y n

namespace BlockTower

variable {X Y : Type u} [Fintype X] [Fintype Y]

noncomputable instance instFintype : ∀ r, Fintype (BlockTower X Y r)
  | 0 => inferInstanceAs (Fintype Y)
  | n + 1 => @instFintypeProd X (BlockTower X Y n) inferInstance (instFintype n)

noncomputable def fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1))) (x : X) :
    Finset (BlockTower X Y r) := by
  classical exact Finset.univ.filter (fun z ↦ (x, z) ∈ A)

@[simp] theorem mem_fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1)))
    (x : X) (z : BlockTower X Y r) : z ∈ fibre A x ↔ (x, z) ∈ A := by
  classical simp [fibre]

theorem card_eq_sum_card_fibre {r : ℕ} (A : Finset (BlockTower X Y (r + 1))) :
    A.card = ∑ x : X, (fibre A x).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := A) (t := Finset.univ)
    (f := fun z ↦ z.1) (by simp)]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.card_bij (fun z hz ↦ z.2)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzA, hzx⟩
    simpa [fibre, ← hzx] using hzA
  · intro a ha b hb hab
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  · intro z hz
    exact ⟨(x, z), by simpa [fibre] using hz, rfl⟩

theorem dens_eq_average_fibre [Nonempty X] {r : ℕ}
    (A : Finset (BlockTower X Y (r + 1))) :
    (A.dens : ℚ) = (∑ x : X, ((fibre A x).dens : ℚ)) / Fintype.card X := by
  rw [Finset.dens, card_eq_sum_card_fibre]
  simp only [Nat.cast_sum, Finset.dens, Nat.cast_mul, Fintype.card_prod]
  push_cast
  simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- Split a word at a block boundary. -/
def wordAddEquiv (t m n : ℕ) :
    Word t (m + n) ≃ Word t m × Word t n :=
  (Equiv.piCongrLeft (fun _ : Fin (m + n) ↦ Fin t) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) (Fin t))

/-- Flatten an iterated tower of `m`-letter blocks followed by an `s`-letter
suffix into an ordinary word. -/
def wordEquiv (t m s : ℕ) : ∀ r : ℕ,
    BlockTower (Word t m) (Word t s) r ≃ Word t (r * m + s)
  | 0 => by simpa using Equiv.refl (Word t s)
  | r + 1 =>
      ((Equiv.refl (Word t m)).prodCongr (wordEquiv t m s r)).trans <|
        (wordAddEquiv t m (r * m + s)).symm.trans <|
          Equiv.piCongrLeft (fun _ : Fin ((r + 1) * m + s) ↦ Fin t) <|
            finCongr (by simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

@[simp] theorem dens_map_wordEquiv (t m s r : ℕ)
    (A : Finset (BlockTower (Word t m) (Word t s) r)) :
    (A.map (wordEquiv t m s r).toEmbedding).dens = A.dens := by
  exact Finset.dens_map_equiv _

end BlockTower

namespace UniformFibres

open BlockTower

variable {X : Type u} [Fintype X]

/-- If one value lies `ε` below a lower bound for the average, another value
lies at least `ε/(|X|-1)` above the average. -/
theorem exists_average_add_le [Nonempty X] (hX : 1 < Fintype.card X)
    (f : X → ℚ) (d e mu : ℚ)
    (havg : mu = (∑ x : X, f x) / Fintype.card X)
    (hd : d ≤ mu) (x : X) (hx : f x ≤ d - e) :
    ∃ y : X, mu + e / (Fintype.card X - 1) ≤ f y := by
  classical
  let q : ℚ := Fintype.card X
  let rho : ℚ := e / (q - 1)
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast hX
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hqm1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hrho : (q - 1) * rho = e := by
    dsimp [rho]
    field_simp
  have hsum : ∑ y : X, f y = q * mu := by
    rw [havg]
    field_simp
    simp [q]
  have hxin : x ∈ (Finset.univ : Finset X) := Finset.mem_univ x
  have hsplit : ∑ y : X, f y = f x + ∑ y ∈ (Finset.univ.erase x), f y := by
    calc
      ∑ y : X, f y = (∑ y ∈ (Finset.univ.erase x), f y) + f x :=
        (Finset.sum_erase_add _ _ hxin).symm
      _ = f x + ∑ y ∈ (Finset.univ.erase x), f y := add_comm _ _
  have herase : (q - 1) * (mu + rho) ≤
      ∑ y ∈ (Finset.univ.erase x), f y := by
    linarith
  have hne : (Finset.univ.erase x : Finset X).Nonempty := by
    exact (Finset.one_lt_card_iff_nontrivial.mp (by simpa using hX)).erase_nonempty
  obtain ⟨y, hy, hyf⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ : X ↦ mu + rho) (g := f) (by
      simpa [q, Finset.card_erase_of_mem hxin, Nat.cast_sub (by omega : 1 ≤ Fintype.card X),
        mul_add] using herase)
  exact ⟨y, by simpa [rho, q] using hyf⟩

variable {Y : Type u} [Fintype Y]

/-- Along some initial chain of frozen blocks there is a next block all of
whose fibres lie above the indicated threshold.  This recursive formulation
retains the unused blocks as part of the suffix. -/
def HasUniformBlock (d e : ℚ) : {r : ℕ} →
    Finset (BlockTower X Y r) → Prop
  | 0, _ => False
  | _r + 1, A =>
      (∀ x : X, d - e ≤ ((BlockTower.fibre A x).dens : ℚ)) ∨
      ∃ x : X, HasUniformBlock d e (BlockTower.fibre A x)

/-- Real-valued interface to `HasUniformBlock`, matching the density
convention used by the rest of the Erdős 171 development. -/
def HasUniformBlockReal (d e : ℝ) : {r : ℕ} →
    Finset (BlockTower X Y r) → Prop
  | 0, _ => False
  | _r + 1, A =>
      (∀ x : X, d - e ≤ ((BlockTower.fibre A x).dens : ℝ)) ∨
      ∃ x : X, HasUniformBlockReal d e (BlockTower.fibre A x)

theorem HasUniformBlock.toReal {d e : ℚ} : ∀ {r : ℕ}
    {A : Finset (BlockTower X Y r)}, HasUniformBlock d e A →
      HasUniformBlockReal (d : ℝ) (e : ℝ) A := by
  intro r
  induction r with
  | zero => simp [HasUniformBlock]
  | succ r ih =>
      intro A h
      rw [HasUniformBlock] at h
      rw [HasUniformBlockReal]
      rcases h with h | ⟨x, hx⟩
      · left
        intro x
        exact_mod_cast h x
      · exact Or.inr ⟨x, ih hx⟩

theorem HasUniformBlockReal.mono_error {d e e' : ℝ} (hee : e ≤ e') :
    ∀ {r : ℕ} {A : Finset (BlockTower X Y r)},
      HasUniformBlockReal d e A → HasUniformBlockReal d e' A := by
  intro r
  induction r with
  | zero => simp [HasUniformBlockReal]
  | succ r ih =>
      intro A h
      rw [HasUniformBlockReal] at h ⊢
      rcases h with h | ⟨x, hx⟩
      · left
        intro x
        exact (sub_le_sub_left hee d).trans (h x)
      · exact Or.inr ⟨x, ih hx⟩

/-- A record of the initial blocks frozen before the uniform block.  The two
indices are the original and remaining tower heights. -/
inductive FrozenPrefix (X : Type u) : ℕ → ℕ → Type u
  | nil (r : ℕ) : FrozenPrefix X r r
  | cons {r q : ℕ} (x : X) (p : FrozenPrefix X r q) : FrozenPrefix X (r + 1) q

namespace FrozenPrefix

/-- Insert the frozen blocks in front of a remaining tower word. -/
def prepend {X Y : Type u} : {r q : ℕ} → FrozenPrefix X r q →
    BlockTower X Y q → BlockTower X Y r
  | _, _, .nil _, z => z
  | _, _, .cons x p, z => (x, prepend p z)

theorem prepend_injective {X Y : Type u} : ∀ {r q : ℕ}
    (p : FrozenPrefix X r q), Function.Injective (prepend (Y := Y) p)
  | _, _, .nil _ => Function.injective_id
  | _, _, .cons _ p => fun _ _ h ↦ prepend_injective p (congrArg Prod.snd h)

noncomputable def iterFibre {X Y : Type u} [Fintype X] [Fintype Y] :
    {r q : ℕ} → FrozenPrefix X r q → Finset (BlockTower X Y r) →
      Finset (BlockTower X Y q)
  | _, _, .nil _, A => A
  | _, _, .cons x p, A => iterFibre p (BlockTower.fibre A x)

@[simp] theorem iterFibre_nil {X Y : Type u} [Fintype X] [Fintype Y]
    (r : ℕ) (A : Finset (BlockTower X Y r)) :
    iterFibre (.nil r : FrozenPrefix X r r) A = A := rfl

@[simp] theorem iterFibre_cons {X Y : Type u} [Fintype X] [Fintype Y]
    {r q : ℕ} (x : X) (p : FrozenPrefix X r q)
    (A : Finset (BlockTower X Y (r + 1))) :
    iterFibre (.cons x p) A = iterFibre p (BlockTower.fibre A x) := rfl

@[simp] theorem mem_iterFibre {X Y : Type u} [Fintype X] [Fintype Y] :
    ∀ {r q : ℕ} (p : FrozenPrefix X r q)
      (A : Finset (BlockTower X Y r)) (z : BlockTower X Y q),
      z ∈ p.iterFibre A ↔ prepend p z ∈ A
  | _, _, .nil _, A, z => Iff.rfl
  | _, _, .cons x p, A, z => by
      rw [iterFibre_cons, mem_iterFibre, mem_fibre]
      rfl

end FrozenPrefix

/-- Extract the concrete frozen prefix and the next uniform block from the
recursive stopping predicate. -/
theorem HasUniformBlockReal.exists_frozenPrefix {d e : ℝ} : ∀ {r : ℕ}
    {A : Finset (BlockTower X Y r)}, HasUniformBlockReal d e A →
      ∃ q : ℕ, ∃ p : FrozenPrefix X r (q + 1),
        ∀ x : X, d - e ≤
          ((BlockTower.fibre (p.iterFibre A) x).dens : ℝ) := by
  intro r
  induction r with
  | zero => simp [HasUniformBlockReal]
  | succ r ih =>
      intro A h
      rw [HasUniformBlockReal] at h
      rcases h with h | ⟨x, hx⟩
      · refine ⟨r, .nil (r + 1), ?_⟩
        intro x
        change d - e ≤ ((BlockTower.fibre A x).dens : ℝ)
        exact h x
      · obtain ⟨q, p, hp⟩ := ih hx
        refine ⟨q, .cons x p, ?_⟩
        intro y
        change d - e ≤
          ((BlockTower.fibre (p.iterFibre (BlockTower.fibre A x)) y).dens : ℝ)
        exact hp y

/-- The finite energy-increment argument.  If there are `R+1` available
blocks and `b + R * (ε/(|X|-1)) > 1`, a uniform block must occur before
the possible density increments exhaust the interval `[0,1]`. -/
theorem hasUniformBlock_of_growth [Nonempty X] (hX : 1 < Fintype.card X)
    (d b e : ℚ) (he : 0 ≤ e) (hdb : d ≤ b) : ∀ (R : ℕ)
    (A : Finset (BlockTower X Y (R + 1))),
    b ≤ (A.dens : ℚ) →
    1 < b + R * (e / (Fintype.card X - 1)) →
    HasUniformBlock d e A := by
  intro R
  induction R generalizing b with
  | zero =>
      intro A hA hcap
      exfalso
      have hle : (A.dens : ℚ) ≤ 1 := by exact_mod_cast A.dens_le_one
      norm_num at hcap
      linarith
  | succ R ih =>
      intro A hA hcap
      rw [HasUniformBlock]
      by_cases hunif : ∀ x : X, d - e ≤ ((BlockTower.fibre A x).dens : ℚ)
      · exact Or.inl hunif
      · right
        push Not at hunif
        obtain ⟨x, hx⟩ := hunif
        let mu : ℚ := (A.dens : ℚ)
        let rho : ℚ := e / (Fintype.card X - 1)
        have hrho : 0 ≤ rho := by
          dsimp [rho]
          apply div_nonneg he
          have : (1 : ℚ) < Fintype.card X := by exact_mod_cast hX
          linarith
        obtain ⟨y, hy⟩ := exists_average_add_le hX
          (fun z : X ↦ ((BlockTower.fibre A z).dens : ℚ)) d e mu
          (BlockTower.dens_eq_average_fibre A) (hdb.trans hA) x hx.le
        refine ⟨y, ih (b := b + rho) (by linarith) (BlockTower.fibre A y) ?_ ?_⟩
        · dsimp [mu, rho] at hy ⊢
          linarith
        · dsimp [rho]
          push_cast at hcap ⊢
          ring_nf at hcap ⊢
          exact hcap

/-- Qualitative form of uniformization: the number of available blocks can
be chosen from `X` and `ε` alone, independently of the terminal suffix and
of the set. -/
theorem exists_blockCount_uniform [Nonempty X] (hX : 1 < Fintype.card X)
    (e : ℚ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (BlockTower X Y (R + 1)),
      HasUniformBlock (A.dens : ℚ) e A := by
  let rho : ℚ := e / (Fintype.card X - 1)
  have hden : (0 : ℚ) < Fintype.card X - 1 := by
    have : (1 : ℚ) < Fintype.card X := by exact_mod_cast hX
    linarith
  have hrho : 0 < rho := div_pos he hden
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / rho)
  have hRrho : (1 : ℚ) < R * rho := by
    apply (div_lt_iff₀ hrho).mp
    simpa [div_eq_mul_inv, mul_comm] using hR
  refine ⟨R, fun A ↦ hasUniformBlock_of_growth hX
    (A.dens : ℚ) (A.dens : ℚ) e he.le le_rfl R A le_rfl ?_⟩
  have hdens : (0 : ℚ) ≤ (A.dens : ℚ) := by positivity
  dsimp [rho] at hRrho ⊢
  linarith

/-- Real-density wrapper.  It chooses a smaller positive rational error,
runs the exact rational argument, and weakens the resulting estimate to the
requested real error. -/
theorem exists_blockCount_uniform_real [Nonempty X] (hX : 1 < Fintype.card X)
    (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (BlockTower X Y (R + 1)),
      HasUniformBlockReal (A.dens : ℝ) e A := by
  obtain ⟨q : ℚ, hq, hqe⟩ := exists_pos_rat_lt he
  obtain ⟨R, hR⟩ := exists_blockCount_uniform (X := X) (Y := Y) hX q hq
  refine ⟨R, fun A ↦ ?_⟩
  have hreal := (hR A).toReal
  exact hreal.mono_error hqe.le

/-- The directly consumable real-density form: after freezing some initial
blocks, every value of the next block has a suffix fibre whose density is at
least the original density minus `e`. -/
theorem exists_uniform_frozenPrefix_real [Nonempty X]
    (hX : 1 < Fintype.card X) (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (BlockTower X Y (R + 1)),
      ∃ q : ℕ, ∃ p : FrozenPrefix X (R + 1) (q + 1),
        ∀ x : X, (A.dens : ℝ) - e ≤
          ((BlockTower.fibre (p.iterFibre A) x).dens : ℝ) := by
  obtain ⟨R, hR⟩ := exists_blockCount_uniform_real (X := X) (Y := Y) hX e he
  exact ⟨R, fun A ↦ (hR A).exists_frozenPrefix⟩

end UniformFibres

end Erdos171
