/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic
import ErdosProblems.Erdos171.Density
import ErdosProblems.Erdos171.SubspaceOps

/-!
# Finitary density-Hales--Jewett frameworks

The density of a finset in Mathlib is an exact nonnegative rational number.
This file records two equivalent quantifier arrangements for density
Hales--Jewett: it is enough to obtain one dimension for each positive density,
because a dense fibre in every larger cube contains the same line.  We also
state the corresponding finite-dimensional-subspace property.
-/

namespace Erdos171

open scoped BigOperators

/-- A set of words contains an `m`-dimensional combinatorial subspace. -/
def ContainsSubspace (m : ℕ) {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n), Set.range U ⊆ A

theorem containsSubspace_iff (m : ℕ) {t n : ℕ} {A : Set (Word t n)} :
    ContainsSubspace m A ↔
      ∃ U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n),
        ∀ x : Word t m, U x ∈ A := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, fun x ↦ hU ⟨x, rfl⟩⟩
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hU x

/-- One-witness formulation of density Hales--Jewett. -/
def FiniteDensityHJ (t : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsLine (A : Set (Word t n))

/-- Eventual formulation of density Hales--Jewett. -/
def EventualDensityHJ (t : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsLine (A : Set (Word t n))

/-- The one-witness formulation for an `m`-dimensional subspace. -/
def FiniteDensityMDHJ (t m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsSubspace m (A : Set (Word t n))

/-- The eventual formulation for an `m`-dimensional subspace. -/
def EventualDensityMDHJ (t m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word t n),
      δ ≤ density A → ContainsSubspace m (A : Set (Word t n))

/-- Split a word into an initial and a final block. -/
def wordAddEquiv (t m r : ℕ) : Word t (m + r) ≃ Word t m × Word t r :=
  (Equiv.piCongrLeft (fun _ : Fin (m + r) ↦ Fin t) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) (Fin t))

@[simp] theorem wordAddEquiv_apply_fst (t m r : ℕ) (w : Word t (m + r))
    (i : Fin m) : (wordAddEquiv t m r w).1 i = w (Fin.castAdd r i) := by
  simp [wordAddEquiv]

@[simp] theorem wordAddEquiv_apply_snd (t m r : ℕ) (w : Word t (m + r))
    (i : Fin r) : (wordAddEquiv t m r w).2 i = w (Fin.natAdd m i) := by
  simp [wordAddEquiv]

/-- Split a word, with the final block placed first for fibrewise counting. -/
def wordFiberEquiv (t m r : ℕ) : Word t (m + r) ≃ Word t r × Word t m :=
  (wordAddEquiv t m r).trans (Equiv.prodComm _ _)

/-- A line on an initial block, extended by a fixed final block. -/
def extendLineRight {t m r : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin m)) (z : Word t r) :
    Combinatorics.Line (Fin t) (Fin (m + r)) where
  idxFun i := match finSumFinEquiv.symm i with
    | Sum.inl j => l.idxFun j
    | Sum.inr j => some (z j)
  proper := by
    obtain ⟨j, hj⟩ := l.proper
    exact ⟨Fin.castAdd r j, by simp [hj]⟩

@[simp] theorem extendLineRight_apply {t m r : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin m)) (z : Word t r) (a : Fin t) :
    wordFiberEquiv t m r (extendLineRight l z a) = (z, l a) := by
  apply Prod.ext
  · funext i
    change extendLineRight l z a (Fin.natAdd m i) = z i
    simp [extendLineRight, Combinatorics.Line.coe_apply]
  · funext i
    change extendLineRight l z a (Fin.castAdd r i) = l a i
    simp [extendLineRight, Combinatorics.Line.coe_apply]

/-- Regard a combinatorial line as a one-dimensional subspace. -/
def lineSubspace {α ι : Type*} (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι where
  idxFun i := (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi, Fin.eq_zero e]⟩

@[simp] theorem lineSubspace_apply {α ι : Type*} (l : Combinatorics.Line α ι)
    (x : Fin 1 → α) : lineSubspace l x = l (x 0) := by
  funext i
  cases hi : l.idxFun i <;>
    simp [lineSubspace, Combinatorics.Line.coe_apply,
      Combinatorics.Subspace.coe_apply, hi]

/-- Independently join an `m`-subspace on an initial coordinate block and a
line on a final coordinate block. -/
def appendSubspaceLine {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    (l : Combinatorics.Line (Fin t) (Fin r)) :
    Combinatorics.Subspace (Fin (m + 1)) (Fin t) (Fin (n + r)) :=
  (U.sum (lineSubspace l)).reindex finSumFinEquiv (Equiv.refl _) finSumFinEquiv

@[simp] theorem wordAddEquiv_appendSubspaceLine_apply {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n))
    (l : Combinatorics.Line (Fin t) (Fin r))
    (x : Word t (m + 1)) :
    wordAddEquiv t n r (appendSubspaceLine U l x) =
      (U (fun i ↦ x (Fin.castAdd 1 i)), l (x (Fin.last m))) := by
  apply Prod.ext
  · funext i
    simp only [wordAddEquiv_apply_fst, appendSubspaceLine,
      Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, finSumFinEquiv_symm_apply_castAdd,
      Combinatorics.Subspace.sum_apply_inl, Function.comp_apply,
      finSumFinEquiv_apply_left]
    have hf :
        ((⇑(Equiv.refl (Fin t)) ∘ x ∘ ⇑finSumFinEquiv) ∘ Sum.inl) =
          (fun j : Fin m ↦ x (Fin.castAdd 1 j)) := by
      funext j
      simp
    rw [hf]
  · funext i
    simp only [wordAddEquiv_apply_snd, appendSubspaceLine,
      Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, finSumFinEquiv_symm_apply_natAdd,
      Combinatorics.Subspace.sum_apply_inr, Function.comp_apply,
      lineSubspace_apply]
    have hz : Fin.natAdd m (0 : Fin 1) = Fin.last m := by ext; simp
    rw [finSumFinEquiv_apply_right, hz]

/-- Extend a subspace on an initial coordinate block by a fixed final word. -/
def extendSubspaceRight {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n)) (z : Word t r) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin (n + r)) :=
  (U.extendRightWord z).reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv

@[simp] theorem extendSubspaceRight_apply {t m n r : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin n)) (z : Word t r)
    (x : Word t m) :
    wordFiberEquiv t n r (extendSubspaceRight U z x) = (z, U x) := by
  apply Prod.ext
  · funext i
    change extendSubspaceRight U z x (Fin.natAdd n i) = z i
    simp [extendSubspaceRight, Combinatorics.Subspace.reindex_apply]
  · funext i
    change extendSubspaceRight U z x (Fin.castAdd r i) = U x i
    simp [extendSubspaceRight, Combinatorics.Subspace.reindex_apply]

/-- Some fibre of a nonempty finite product has density at least the density of
the whole set.  This is the exact finite averaging principle needed for
cylinder lifting. -/
theorem exists_fiber_density_ge {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : Finset (X × Y)) :
    ∃ x : X, density A ≤ density (fiber A x) := by
  rw [density_eq_average_fiber]
  exact exists_average_le _

/-- The graph of a finite colouring, restricted to a finset. -/
noncomputable def colorGraph {X C : Type*} (D : Finset X) (color : X → C) :
    Finset (C × X) := by
  classical
  exact D.map
    ⟨fun x ↦ (color x, x), fun _ _ h ↦ congrArg Prod.snd h⟩

@[simp] theorem mem_colorGraph {X C : Type*} (D : Finset X) (color : X → C)
    (c : C) (x : X) :
    (c, x) ∈ colorGraph D color ↔ x ∈ D ∧ color x = c := by
  classical
  constructor
  · rw [colorGraph, Finset.mem_map]
    rintro ⟨y, hy, hpair⟩
    have hyx : y = x := congrArg Prod.snd hpair
    subst y
    exact ⟨hy, congrArg Prod.fst hpair⟩
  · rintro ⟨hx, hcolor⟩
    rw [colorGraph, Finset.mem_map]
    exact ⟨x, hx, Prod.ext hcolor rfl⟩

theorem density_colorGraph {X C : Type*} [Fintype X] [Fintype C]
    (D : Finset X) (color : X → C) :
    density (colorGraph D color) = density D / Fintype.card C := by
  classical
  simp only [density_eq_card_div_card, colorGraph, Finset.card_map, Fintype.card_prod]
  push_cast
  ring

/-- One colour class, regarded as a finset in the original ambient type. -/
noncomputable def colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X → C) (c : C) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ D ∧ color x = c

@[simp] theorem mem_colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X → C) (c : C) (x : X) :
    x ∈ colorClass D color c ↔ x ∈ D ∧ color x = c := by
  classical
  simp [colorClass]

/-- A finite colouring has a colour class whose ambient density is at least
the density of the coloured set divided by the number of colours. -/
theorem exists_dense_colorClass {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] [Nonempty C] (D : Finset X) (color : X → C) :
    ∃ c : C, density D / Fintype.card C ≤
      density (colorClass D color c) := by
  classical
  obtain ⟨c, hc⟩ := exists_fiber_density_ge (colorGraph D color)
  have hfiber : fiber (colorGraph D color) c = colorClass D color c := by
    ext x
    simp
  refine ⟨c, ?_⟩
  rw [density_colorGraph] at hc
  simpa only [hfiber] using hc

/-- A single witnessing dimension for every positive density automatically
works in every larger dimension. -/
theorem FiniteDensityHJ.eventual {t : ℕ} (h : FiniteDensityHJ t) (ht : 0 < t) :
    EventualDensityHJ t := by
  intro δ hδ
  obtain ⟨m, hm⟩ := h δ hδ
  refine ⟨m, ?_⟩
  intro n hmn A hA
  let : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  classical
  let e := wordFiberEquiv t m r
  let B : Finset (Word t r × Word t m) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨l, hl⟩ := hm (fiber B z) (hB.trans hz)
  refine ⟨extendLineRight l z, ?_⟩
  rintro _ ⟨a, rfl⟩
  have hmemB : (z, l a) ∈ B := (mem_fiber B z (l a)).1 (hl ⟨a, rfl⟩)
  have hmemA : e.symm (z, l a) ∈ A := by simpa [B] using hmemB
  have heq : e.symm (z, l a) = extendLineRight l z a := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

/-- Density Hales--Jewett implies its finite-dimensional version.  The proof
is the standard dense-fibre induction: choose a line in every dense suffix
fibre, pigeonhole a common line, find an `m`-subspace in its prefix colour
class, and take the independent sum. -/
theorem FiniteDensityHJ.finiteDensityMDHJ {t : ℕ} (h : FiniteDensityHJ t)
    (ht : 0 < t) (m : ℕ) : FiniteDensityMDHJ t m := by
  let : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  induction m with
  | zero =>
      intro δ hδ
      refine ⟨0, ?_⟩
      intro A hA
      have hApos : 0 < density A := hδ.trans_le hA
      have hAne : A.Nonempty := (density_pos A).1 hApos
      let U : Combinatorics.Subspace (Fin 0) (Fin t) (Fin 0) :=
        { idxFun := Fin.elim0
          proper := fun e ↦ Fin.elim0 e }
      refine ⟨U, ?_⟩
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hAne
      change U x ∈ A
      rw [Subsingleton.elim (U x) w]
      exact hw
  | succ m ih =>
      intro δ hδ
      by_cases hδ1 : δ ≤ 1
      swap
      · refine ⟨0, ?_⟩
        intro A hA
        exfalso
        exact hδ1 (hA.trans (density_le_one A))
      have hδhalf : 0 < δ / 2 := half_pos hδ
      obtain ⟨r, hr⟩ := h (δ / 2) hδhalf
      have huniv : δ / 2 ≤ density (Finset.univ : Finset (Word t r)) := by
        rw [density_univ]
        linarith
      obtain ⟨l₀, hl₀⟩ := hr Finset.univ huniv
      let : Nonempty (Combinatorics.Line (Fin t) (Fin r)) := ⟨l₀⟩
      have hq : (0 : ℝ) < Fintype.card (Combinatorics.Line (Fin t) (Fin r)) := by
        positivity
      have htheta : 0 <
          δ / (2 * Fintype.card (Combinatorics.Line (Fin t) (Fin r))) := by
        exact div_pos hδ (mul_pos (by norm_num) hq)
      obtain ⟨n, hn⟩ := ih _ htheta
      refine ⟨n + r, ?_⟩
      intro A hA
      classical
      let e := wordAddEquiv t n r
      let B : Finset (Word t n × Word t r) := A.map e.toEmbedding
      have hB : δ ≤ density B := by
        change δ ≤ density (A.map e.toEmbedding)
        rw [density_map_equiv]
        exact hA
      let f : Word t n → ℝ := fun x ↦ density (fiber B x)
      let D : Finset (Word t n) := superlevel f (δ / 2)
      have havg : δ ≤ average f := by
        change δ ≤ average fun x ↦ density (fiber B x)
        rw [← density_eq_average_fiber]
        exact hB
      have hD : δ / 2 ≤ density D := by
        apply half_le_density_superlevel f (le_of_lt hδ) havg
        intro x
        exact density_le_one _
      let selected : Word t n → Combinatorics.Line (Fin t) (Fin r) := fun x ↦
        if hx : x ∈ D then
          Classical.choose (hr (fiber B x) ((mem_superlevel f (δ / 2) x).1 hx))
        else l₀
      have hselected (x : Word t n) (hx : x ∈ D) :
          Set.range (selected x) ⊆ (fiber B x : Set (Word t r)) := by
        dsimp only [selected]
        rw [dif_pos hx]
        exact Classical.choose_spec
          (hr (fiber B x) ((mem_superlevel f (δ / 2) x).1 hx))
      obtain ⟨l, hl⟩ := exists_dense_colorClass D selected
      have hclass :
          δ / (2 * Fintype.card (Combinatorics.Line (Fin t) (Fin r))) ≤
            density (colorClass D selected l) := by
        have hdiv := div_le_div_of_nonneg_right hD (le_of_lt hq)
        have heq :
            δ / (2 * Fintype.card (Combinatorics.Line (Fin t) (Fin r))) =
              (δ / 2) / Fintype.card (Combinatorics.Line (Fin t) (Fin r)) := by
          ring
        rw [heq]
        exact hdiv.trans hl
      obtain ⟨U, hU⟩ := hn (colorClass D selected l) hclass
      refine ⟨appendSubspaceLine U l, ?_⟩
      rintro _ ⟨x, rfl⟩
      let xp : Word t m := fun i ↦ x (Fin.castAdd 1 i)
      have hprefix : U xp ∈ colorClass D selected l := hU ⟨xp, rfl⟩
      have hprefix' : U xp ∈ D ∧ selected (U xp) = l :=
        (mem_colorClass D selected l (U xp)).1 hprefix
      have hsuffix : l (x (Fin.last m)) ∈ fiber B (U xp) := by
        rw [← hprefix'.2]
        exact hselected (U xp) hprefix'.1 ⟨x (Fin.last m), rfl⟩
      have hpair : (U xp, l (x (Fin.last m))) ∈ B :=
        (mem_fiber B (U xp) (l (x (Fin.last m)))).1 hsuffix
      have hmemA : e.symm (U xp, l (x (Fin.last m))) ∈ A := by
        simpa [B] using hpair
      have heval :
          e.symm (U xp, l (x (Fin.last m))) = appendSubspaceLine U l x := by
        apply e.injective
        simpa [e, xp] using wordAddEquiv_appendSubspaceLine_apply U l x
      simpa [heval] using hmemA

/-- As for lines, a single witnessing dimension for an `m`-subspace works in
every larger dimension by fixing a dense fibre. -/
theorem FiniteDensityMDHJ.eventual {t m : ℕ} (h : FiniteDensityMDHJ t m)
    (ht : 0 < t) : EventualDensityMDHJ t m := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn A hA
  let : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  classical
  let e := wordFiberEquiv t n₀ r
  let B : Finset (Word t r × Word t n₀) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨U, hU⟩ := hn₀ (fiber B z) (hB.trans hz)
  refine ⟨extendSubspaceRight U z, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmemB : (z, U x) ∈ B := (mem_fiber B z (U x)).1 (hU ⟨x, rfl⟩)
  have hmemA : e.symm (z, U x) ∈ A := by simpa [B] using hmemB
  have heq : e.symm (z, U x) = extendSubspaceRight U z x := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

end Erdos171
