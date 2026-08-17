/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Binary
import ErdosProblems.Erdos185.DHJ.Cube
import ErdosProblems.Erdos185.DHJ.Density

/-!
# Multidimensional density Hales--Jewett for the binary alphabet

This is the finite, exact-dimension version of the elementary implication
`DHJ(2) -> MDHJ(2)`.  The successor step splits the cube into two blocks.
On a positive-density set of prefixes the final-block section contains a
line.  Pigeonholing the finitely many possible lines, and applying the
induction hypothesis to one colour class, supplies a common line over an
`m`-dimensional subspace of prefixes.  Its independent product with that
line is the required `(m+1)`-subspace.
-/

namespace Erdos185.DHJ

open scoped BigOperators

private noncomputable def colorGraph {X C : Type*}
    (D : Finset X) (color : X -> C) : Finset (C × X) := by
  classical
  exact D.map
    ⟨fun x => (color x, x), fun _ _ h => congrArg Prod.snd h⟩

private theorem mem_colorGraph {X C : Type*}
    (D : Finset X) (color : X -> C) (c : C) (x : X) :
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

private theorem density_colorGraph {X C : Type*} [Fintype X] [Fintype C]
    (D : Finset X) (color : X -> C) :
    density (colorGraph D color) = density D / Fintype.card C := by
  classical
  simp only [density_eq_card_div_card, colorGraph, Finset.card_map,
    Fintype.card_prod]
  push_cast
  ring

private noncomputable def colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X -> C) (c : C) : Finset X := by
  classical
  exact Finset.univ.filter fun x => x ∈ D ∧ color x = c

@[simp] private theorem mem_colorClass {X C : Type*} [Fintype X]
    (D : Finset X) (color : X -> C) (c : C) (x : X) :
    x ∈ colorClass D color c ↔ x ∈ D ∧ color x = c := by
  classical
  simp [colorClass]

private theorem exists_dense_colorClass {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] [Nonempty C] (D : Finset X) (color : X -> C) :
    ∃ c : C, density D / Fintype.card C ≤
      density (colorClass D color c) := by
  classical
  obtain ⟨c, hc⟩ := exists_fiber_density_ge (colorGraph D color)
  have hfiber : fiber (colorGraph D color) c = colorClass D color c := by
    ext x
    simp [mem_colorGraph]
  refine ⟨c, ?_⟩
  rw [density_colorGraph] at hc
  simpa only [hfiber] using hc

/-- Regard a line as a one-dimensional subspace. -/
private def lineSubspace {α ι : Type*} (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι where
  idxFun i := (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi, Fin.eq_zero e]⟩

@[simp] private theorem lineSubspace_apply {α ι : Type*}
    (l : Combinatorics.Line α ι) (x : Fin 1 -> α) :
    lineSubspace l x = l (x 0) := by
  funext i
  cases hi : l.idxFun i <;>
    simp [lineSubspace, Combinatorics.Line.coe_apply,
      Combinatorics.Subspace.coe_apply, hi]

private theorem wordSplitEquiv_finSum_line_apply {m q p : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin 2) (Fin q))
    (l : Combinatorics.Line (Fin 2) (Fin p)) (x : Word 2 (m + 1)) :
    wordSplitEquiv 2 q p (U.finSum (lineSubspace l) x) =
      (U (fun i => x (Fin.castAdd 1 i)), l (x (Fin.last m))) := by
  apply Prod.ext
  · funext i
    simp [wordSplitEquiv_apply_fst, Function.comp_def]
  · funext i
    simp only [wordSplitEquiv_apply_snd,
      Combinatorics.Subspace.finSum_apply_natAdd, lineSubspace_apply]
    have hzero : Fin.natAdd m (0 : Fin 1) = Fin.last m := by
      ext
      simp
    rw [Function.comp_apply, hzero]

/-- A density lower bound, in the local normalized-density convention,
supplies a binary line using the Sperner proof in `Erdos171.Binary`. -/
private theorem exists_binary_line_of_density (delta : ℝ) (hdelta : 0 < delta) :
    ∃ p : ℕ, 0 < p ∧ ∀ A : Finset (Word 2 p), delta ≤ density A ->
      ∃ l : Combinatorics.Line (Fin 2) (Fin p), ∀ a, l a ∈ A := by
  obtain ⟨N, hN⟩ :=
    Erdos171.exists_containsLine_of_dense_binary_finset delta hdelta
  refine ⟨N + 1, by omega, ?_⟩
  intro A hA
  have hcard : delta * (2 : ℝ) ^ (N + 1) ≤ A.card := by
    have hden : delta ≤ (A.card : ℝ) / (2 : ℝ) ^ (N + 1) := by
      simpa [density, Word] using hA
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (N + 1))).mp hden
  have hline := hN (N + 1) (by omega) A hcard
  exact Erdos171.containsLine_coe_finset_iff.mp hline

/-- Every positive-density subset of a suitably chosen binary cube contains
an `m`-dimensional combinatorial subspace.  The dimension `N` is an exact
witness; no monotonicity in the ambient dimension is needed here. -/
theorem binary_multidimensional (m : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ A : Finset (Word 2 N), delta ≤ density A ->
      ∃ U : Combinatorics.Subspace (Fin m) (Fin 2) (Fin N),
        ∀ x : Word 2 m, U x ∈ A := by
  classical
  induction m generalizing delta with
  | zero =>
      refine ⟨0, ?_⟩
      intro A hA
      have hpos : 0 < density A := hdelta.trans_le hA
      have hne : A.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hAempty
        subst A
        simpa using hpos
      obtain ⟨a, ha⟩ := hne
      let U : Combinatorics.Subspace (Fin 0) (Fin 2) (Fin 0) :=
        { idxFun := Fin.elim0
          proper := fun e => Fin.elim0 e }
      refine ⟨U, ?_⟩
      intro x
      convert ha using 1
  | succ m ih =>
      obtain ⟨p, hp0, hp⟩ :=
        exists_binary_line_of_density (delta / 2) (by positivity)
      let LineType := Combinatorics.Line (Fin 2) (Fin p)
      let K := Fintype.card LineType
      haveI : Nonempty LineType := by
        let i : Fin p := ⟨0, hp0⟩
        exact ⟨{ idxFun := fun _ => none, proper := ⟨i, rfl⟩ }⟩
      have hK : 0 < K := Fintype.card_pos
      have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
      let delta' : ℝ := delta / (2 * (K : ℝ))
      have hdelta' : 0 < delta' := by
        dsimp [delta']
        exact div_pos hdelta (mul_pos (by norm_num) hKreal)
      obtain ⟨q, hq⟩ := ih delta' hdelta'
      refine ⟨q + p, ?_⟩
      intro A hA
      let G : Finset (Word 2 q) := largePrefixSections A (delta / 2)
      have hG : delta / 2 ≤ density G := by
        exact half_le_density_largePrefixSections (k := 2) (m := q) (r := p)
          (by omega) A hdelta.le hA
      have hline : ∀ x ∈ G,
          ∃ l : LineType, ∀ a : Fin 2, l a ∈ prefixSection A x := by
        intro x hx
        apply hp
        simpa only [G, mem_largePrefixSections] using hx
      let chosenLine : Word 2 q -> LineType := fun x =>
        if hx : x ∈ G then Classical.choose (hline x hx)
        else Classical.choice inferInstance
      have chosenLine_spec (x : Word 2 q) (hx : x ∈ G) :
          ∀ a : Fin 2, chosenLine x a ∈ prefixSection A x := by
        dsimp only [chosenLine]
        rw [dif_pos hx]
        exact Classical.choose_spec (hline x hx)
      obtain ⟨l, hl⟩ := exists_dense_colorClass G chosenLine
      have hclass : delta' ≤ density (colorClass G chosenLine l) := by
        calc
          delta' = (delta / 2) / (K : ℝ) := by
            dsimp [delta', K]
            ring
          _ ≤ density G / (K : ℝ) := by
            gcongr
          _ ≤ density (colorClass G chosenLine l) := by
            simpa only [K, LineType] using hl
      obtain ⟨U, hU⟩ := hq (colorClass G chosenLine l) hclass
      refine ⟨U.finSum (lineSubspace l), ?_⟩
      intro z
      let x : Word 2 m := fun i => z (Fin.castAdd 1 i)
      let a : Fin 2 := z (Fin.last m)
      have hUx : U x ∈ G ∧ chosenLine (U x) = l := by
        simpa only [mem_colorClass] using hU x
      have hsection : l a ∈ prefixSection A (U x) := by
        rw [← hUx.2]
        exact chosenLine_spec (U x) hUx.1 a
      rw [mem_prefixSection] at hsection
      have hsplit : wordSplitEquiv 2 q p (U.finSum (lineSubspace l) z) =
          (U x, l a) := by
        simpa only [x, a] using wordSplitEquiv_finSum_line_apply U l z
      have hjoin : (wordSplitEquiv 2 q p).symm (U x, l a) =
          U.finSum (lineSubspace l) z := by
        apply (wordSplitEquiv 2 q p).injective
        simp [hsplit]
      simpa only [hjoin] using hsection

end Erdos185.DHJ
