/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Framework
import ErdosProblems.Erdos171.GrahamRothschild
import ErdosProblems.Erdos171.IncrementArithmetic
import ErdosProblems.Erdos171.SubspaceDensity

/-!
# Correlated sections and many restricted lines

This file formalizes Lemmas 7 and 8 in the Dodos--Kanellopoulos--Tyros
density-increment proof.  The key convention is that the constants are chosen
at a fixed density floor `δ₀`, while `ρ` denotes the actual density of the set
under consideration and may be larger than `δ₀`.

The first part is a purely finite averaging argument.  It says that if the
average density of a family of fibres is close to `ρ`, no fibre has a density
increment, and the average fraction of restricted internal lines is at least
`θ`, then one fibre is simultaneously dense and line-rich.  The second part
connects this statement with combinatorial subspaces and correlated tail
sections.
-/

open scoped BigOperators

namespace Erdos171

/-! ## Pure finite averaging (DKT Lemma 8) -/

/-- The strict superlevel set of a real-valued function on a finite type. -/
noncomputable def strictSuperlevel {X : Type*} [Fintype X]
    (f : X → ℝ) (c : ℝ) : Finset X :=
  Finset.univ.filter fun x ↦ c < f x

@[simp] theorem mem_strictSuperlevel {X : Type*} [Fintype X]
    (f : X → ℝ) (c : ℝ) (x : X) :
    x ∈ strictSuperlevel f c ↔ c < f x := by
  simp [strictSuperlevel]

/-- The numerical averaging core of DKT Lemma 8.

The function `f` is the density of a fixed-tail extension and `g` is the
fraction of restricted internal lines contained in the set.  The upper bound
on `f` is exactly the negation of the density-increment alternative. -/
theorem exists_dense_and_lineRich_of_averages
    {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → ℝ) (ρ η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hηθ : η < θ / 2)
    (hfavg : ρ - η ^ 2 / 2 ≤ average f)
    (hfupper : ∀ x, f x ≤ ρ + η ^ 2 / 2)
    (hgavg : θ ≤ average g)
    (hgupper : ∀ x, g x ≤ 1) :
    ∃ x, ρ - 2 * η < f x ∧ θ / 2 < g x := by
  classical
  let H₁ : Finset X := strictSuperlevel f (ρ - 2 * η)
  let H₂ : Finset X := strictSuperlevel g (θ / 2)
  have hH₁ : 1 - η < density H₁ := by
    by_contra hnot
    have hH₁le : density H₁ ≤ 1 - η := le_of_not_gt hnot
    have hfavgUpper :
        average f ≤ density H₁ * (ρ + η ^ 2 / 2) +
          (1 - density H₁) * (ρ - 2 * η) := by
      apply average_le_density_mul_add H₁ f
      · intro x _
        exact hfupper x
      · intro x hx
        exact le_of_not_gt (by simpa [H₁] using hx)
    have hweighted :
        density H₁ * (ρ + η ^ 2 / 2) +
            (1 - density H₁) * (ρ - 2 * η) ≤
          (1 - η) * (ρ + η ^ 2 / 2) + η * (ρ - 2 * η) := by
      have hH₁nonneg := density_nonneg H₁
      nlinarith [sq_nonneg η]
    have hscalar := IncrementArithmetic.bad_fiber_average_lt (δ := ρ) hη
    have havglt : average f < ρ - η ^ 2 / 2 := by
      calc
        average f ≤ density H₁ * (ρ + η ^ 2 / 2) +
            (1 - density H₁) * (ρ - 2 * η) := hfavgUpper
        _ ≤ (1 - η) * (ρ + η ^ 2 / 2) +
            η * (ρ - 2 * η) := hweighted
        _ = η * (ρ - 2 * η) +
            (1 - η) * (ρ + η ^ 2 / 2) := by ring
        _ < ρ - η ^ 2 / 2 := hscalar
    exact (not_lt_of_ge hfavg) havglt
  have hθone : θ ≤ 1 := by
    exact hgavg.trans (average_le_const hgupper)
  have hH₂ : θ / 2 < density H₂ := by
    by_contra hnot
    have hH₂le : density H₂ ≤ θ / 2 := le_of_not_gt hnot
    have hgavgUpper :
        average g ≤ density H₂ * 1 +
          (1 - density H₂) * (θ / 2) := by
      apply average_le_density_mul_add H₂ g
      · intro x _
        exact hgupper x
      · intro x hx
        exact le_of_not_gt (by simpa [H₂] using hx)
    have hweighted :
        density H₂ * 1 + (1 - density H₂) * (θ / 2) ≤
          θ / 2 + (1 - θ / 2) * (θ / 2) := by
      have hH₂nonneg := density_nonneg H₂
      nlinarith
    have hscalar := IncrementArithmetic.line_rich_average_lt hθ
    have havglt : average g < θ := by
      calc
        average g ≤ density H₂ * 1 +
            (1 - density H₂) * (θ / 2) := hgavgUpper
        _ ≤ θ / 2 + (1 - θ / 2) * (θ / 2) := hweighted
        _ < θ := hscalar
    exact (not_lt_of_ge hgavg) havglt
  have hinterPos : 0 < density (H₁ ∩ H₂) := by
    have hinter := density_add_sub_one_le_density_inter H₁ H₂
    have hsum : 0 < density H₁ + density H₂ - 1 := by
      nlinarith
    exact hsum.trans_le hinter
  obtain ⟨x, hx⟩ := (density_pos (H₁ ∩ H₂)).1 hinterPos
  have hx₁ : x ∈ H₁ := (Finset.mem_inter.1 hx).1
  have hx₂ : x ∈ H₂ := (Finset.mem_inter.1 hx).2
  exact ⟨x, (mem_strictSuperlevel f _ x).1 hx₁,
    (mem_strictSuperlevel g _ x).1 hx₂⟩

/-! ## Restricted internal lines and tail sections -/

/-- Restricted parameter lines all of whose old-alphabet points map into
`A`.  The ambient subspace uses the enlarged alphabet `Fin (k+1)`, while the
line itself and its parameters use only `Fin k`. -/
noncomputable def restrictedInternalLines {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    Finset (Combinatorics.Line (Fin k) η) := by
  classical
  exact Finset.univ.filter fun l ↦
    ∀ a : Fin k, U (liftWord (l a)) ∈ A

@[simp] theorem mem_restrictedInternalLines {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η) :
    l ∈ restrictedInternalLines U A ↔
      ∀ a : Fin k, U (liftWord (l a)) ∈ A := by
  simp [restrictedInternalLines]

/-- Fraction of the restricted internal lines of `U` that are wholly
contained in `A`. -/
noncomputable def restrictedInternalLineFraction {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) : ℝ :=
  density (restrictedInternalLines U A)

theorem restrictedInternalLineFraction_nonneg {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    0 ≤ restrictedInternalLineFraction U A :=
  density_nonneg _

theorem restrictedInternalLineFraction_le_one {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) :
    restrictedInternalLineFraction U A ≤ 1 :=
  density_le_one _

/-- Tails for which the section at a fixed parameter word belongs to `A`. -/
noncomputable def sectionTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : η → Fin (k + 1)) : Finset (κ → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun y ↦
    Combinatorics.Subspace.sumWord (U x) y ∈ A

@[simp] theorem mem_sectionTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : η → Fin (k + 1)) (y : κ → Fin (k + 1)) :
    y ∈ sectionTails U A x ↔
      Combinatorics.Subspace.sumWord (U x) y ∈ A := by
  simp [sectionTails]

@[simp] theorem sectionTails_comp {η ζ ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (V : Combinatorics.Subspace ζ (Fin (k + 1)) η)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (x : ζ → Fin (k + 1)) :
    sectionTails (U.comp V) A x = sectionTails U A (V x) := by
  ext y
  simp [Combinatorics.Subspace.comp_apply]

/-- Tails on which all old-alphabet points of a fixed restricted parameter
line belong to `A`.  This is the finite section intersection appearing in
DKT Lemma 7. -/
noncomputable def restrictedLineTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η) :
    Finset (κ → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun y ↦
    ∀ a : Fin k,
      Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A

@[simp] theorem mem_restrictedLineTails {η ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) η)
    (y : κ → Fin (k + 1)) :
    y ∈ restrictedLineTails U A l ↔
      ∀ a : Fin k,
        Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A := by
  simp [restrictedLineTails]

/-- Old-alphabet parameter words whose images under a large-alphabet
subspace belong to `A`. -/
noncomputable def restrictedPullbackFinset {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) : Finset (η → Fin k) := by
  classical
  exact Finset.univ.filter fun x ↦ U (liftWord x) ∈ A

@[simp] theorem mem_restrictedPullbackFinset {η ι : Type*} {k : ℕ}
    [Fintype η]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι → Fin (k + 1))) (x : η → Fin k) :
    x ∈ restrictedPullbackFinset U A ↔ U (liftWord x) ∈ A := by
  simp [restrictedPullbackFinset]

/-- Fubini identity for point sections: averaging the densities of the
fixed-tail extensions is the same as averaging the densities of the tail
sections at parameter words. -/
theorem average_extensionDensity_eq_average_sectionTails
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    average (fun y : κ → Fin (k + 1) ↦
        subspaceDensityFinset (U.extendRightWord y) A) =
      average (fun x : η → Fin (k + 1) ↦ density (sectionTails U A x)) := by
  rw [← density_extensionPullback_eq_average,
    density_eq_average_columnFiber]
  apply congrArg average
  funext x
  congr 1
  ext y
  simp

/-- Fubini identity for restricted lines: the average line fraction on a
fixed-tail extension equals the average density of the correlated tail
intersections, one for each restricted parameter line. -/
theorem average_restrictedLineFraction_eq_average_restrictedLineTails
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    average (fun y : κ → Fin (k + 1) ↦
        restrictedInternalLineFraction (U.extendRightWord y) A) =
      average (fun l : Combinatorics.Line (Fin k) η ↦
        density (restrictedLineTails U A l)) := by
  let R : Combinatorics.Line (Fin k) η → (κ → Fin (k + 1)) → Prop :=
    fun l y ↦ ∀ a : Fin k,
      Combinatorics.Subspace.sumWord (U (liftWord (l a))) y ∈ A
  have hfubini := average_setDensity_relationRow_eq_relationColumn R
  have hrow (l : Combinatorics.Line (Fin k) η) :
      setFinset (relationRow R l) = restrictedLineTails U A l := by
    ext y
    simp [R, relationRow]
  have hcolumn (y : κ → Fin (k + 1)) :
      setFinset (relationColumn R y) =
        restrictedInternalLines (U.extendRightWord y) A := by
    ext l
    simp [R, relationColumn,
      Combinatorics.Subspace.extendRightWord_apply]
  simpa only [setDensity, restrictedInternalLineFraction, hrow, hcolumn] using
    hfubini.symm

/-- Fubini identity for the old-alphabet pullbacks of fixed-tail extensions. -/
theorem average_restrictedPullbackDensity_eq_average_sectionTails
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    average (fun y : κ → Fin (k + 1) ↦
        density (restrictedPullbackFinset (U.extendRightWord y) A)) =
      average (fun x : η → Fin k ↦ density (sectionTails U A (liftWord x))) := by
  let R : (η → Fin k) → (κ → Fin (k + 1)) → Prop :=
    fun x y ↦ Combinatorics.Subspace.sumWord (U (liftWord x)) y ∈ A
  have hfubini := average_setDensity_relationRow_eq_relationColumn R
  have hrow (x : η → Fin k) :
      setFinset (relationRow R x) = sectionTails U A (liftWord x) := by
    ext y
    simp [R, relationRow]
  have hcolumn (y : κ → Fin (k + 1)) :
      setFinset (relationColumn R y) =
        restrictedPullbackFinset (U.extendRightWord y) A := by
    ext x
    simp [R, relationColumn,
      Combinatorics.Subspace.extendRightWord_apply]
  simpa only [setDensity, hrow, hcolumn] using hfubini.symm

/-- The pigeonhole step at the heart of DKT Lemma 7.  If every old-alphabet
point section has density at least `δ₀/2`, and density Hales--Jewett is known
at density `δ₀/4` in this parameter cube, then one restricted line has a tail
intersection of density at least `theta δ₀ q`, where `q` is the exact number
of line templates. -/
theorem exists_correlated_restricted_line
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Nonempty η]
    [Fintype κ] [DecidableEq κ] [Nonempty (Fin k)]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hsection : ∀ x : η → Fin k,
      δ₀ / 2 ≤ density (sectionTails U A (liftWord x)))
    (hDHJ : ∀ B : Finset (η → Fin k),
      δ₀ / 4 ≤ density B →
        ∃ l : Combinatorics.Line (Fin k) η, ∀ a, l a ∈ B) :
    ∃ l : Combinatorics.Line (Fin k) η,
      IncrementArithmetic.theta δ₀
          (Fintype.card (Combinatorics.Line (Fin k) η)) ≤
        density (restrictedLineTails U A l) := by
  classical
  let f : (κ → Fin (k + 1)) → ℝ := fun y ↦
    density (restrictedPullbackFinset (U.extendRightWord y) A)
  let D : Finset (κ → Fin (k + 1)) := superlevel f (δ₀ / 4)
  have hfavg : δ₀ / 2 ≤ average f := by
    rw [average_restrictedPullbackDensity_eq_average_sectionTails]
    exact const_le_average hsection
  have hD : δ₀ / 4 ≤ density D := by
    have hhalf := half_le_density_superlevel f
      (δ := δ₀ / 2) (by positivity) hfavg
      (fun y ↦ density_le_one _)
    have hthreshold : (δ₀ / 2) / 2 = δ₀ / 4 := by ring
    simpa only [hthreshold, D] using hhalf
  let chosen : (κ → Fin (k + 1)) → Combinatorics.Line (Fin k) η :=
    fun y ↦ if hy : y ∈ D then
      Classical.choose (hDHJ (restrictedPullbackFinset (U.extendRightWord y) A)
        ((mem_superlevel f (δ₀ / 4) y).1 (by simpa [D] using hy)))
    else default
  have hchosen (y : κ → Fin (k + 1)) (hy : y ∈ D) :
      ∀ a, chosen y a ∈ restrictedPullbackFinset (U.extendRightWord y) A := by
    dsimp [chosen]
    rw [dif_pos hy]
    exact Classical.choose_spec
      (hDHJ (restrictedPullbackFinset (U.extendRightWord y) A)
        ((mem_superlevel f (δ₀ / 4) y).1 (by simpa [D] using hy)))
  obtain ⟨l, hl⟩ := exists_dense_colorClass D chosen
  refine ⟨l, ?_⟩
  have hclassSubset : colorClass D chosen l ⊆ restrictedLineTails U A l := by
    intro y hy
    have hy' := (mem_colorClass D chosen l y).1 hy
    apply (mem_restrictedLineTails U A l y).2
    intro a
    have hmem := (mem_restrictedPullbackFinset
      (U.extendRightWord y) A (chosen y a)).1 (hchosen y hy'.1 a)
    simpa [Combinatorics.Subspace.extendRightWord_apply, hy'.2] using hmem
  have hmono : density (colorClass D chosen l) ≤
      density (restrictedLineTails U A l) := density_mono hclassSubset
  have hcardpos : (0 : ℝ) <
      Fintype.card (Combinatorics.Line (Fin k) η) := by positivity
  have hdiv : (δ₀ / 4) /
        Fintype.card (Combinatorics.Line (Fin k) η) ≤
      density D / Fintype.card (Combinatorics.Line (Fin k) η) := by
    exact div_le_div_of_nonneg_right hD hcardpos.le
  unfold IncrementArithmetic.theta
  calc
    δ₀ / (4 * Fintype.card (Combinatorics.Line (Fin k) η)) =
        (δ₀ / 4) / Fintype.card (Combinatorics.Line (Fin k) η) := by ring
    _ ≤ density D / Fintype.card (Combinatorics.Line (Fin k) η) := hdiv
    _ ≤ density (colorClass D chosen l) := hl
    _ ≤ density (restrictedLineTails U A l) := hmono

/-- Restricted correlated-tail sets are natural under composition with the
lift of an old-alphabet subspace. -/
@[simp] theorem restrictedLineTails_comp_finLift
    {η ζ ι κ : Type*} {k : ℕ}
    [Fintype κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (V : Combinatorics.Subspace ζ (Fin k) η)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) ζ) :
    restrictedLineTails (U.comp V.finLift) A l =
      restrictedLineTails U A (V.lineMap l) := by
  ext y
  simp [Combinatorics.Subspace.comp_apply,
    Combinatorics.Subspace.lineMap_apply]

/-! ## Correlated restricted lines (DKT Lemma 7) -/

/-- DKT Lemma 7, starting from a prefix subspace whose point sections have
already been uniformized.  The constants `η₀` and `theta` are selected at the
fixed density floor `δ₀`, while the section bound tracks the actual density
`ρ ≥ δ₀`.

The proof colors a restricted line good when its common tail section has
density at least `theta`.  Finite Graham--Rothschild gives an `m`-subspace on
which all lines have one color.  The all-bad color is excluded by applying the
assumed density-Hales--Jewett statement in an `m₀`-face, then pigeonholing the
line supplied on each dense tail. -/
theorem exists_correlated_subspace_of_uniform_sections
    (k m₀ m : ℕ) (hk : 0 < k) (hm₀ : 0 < m₀) (hm₀m : m₀ ≤ m)
    (δ₀ η₀ : ℝ) (hδ₀ : 0 < δ₀) (herror : η₀ ^ 2 / 2 ≤ δ₀ / 2)
    (hDHJ : ∀ B : Finset (Word k m₀),
      δ₀ / 4 ≤ density B → ContainsLine (B : Set (Word k m₀))) :
    ∃ N : ℕ, ∀ {ι κ : Type*} [Fintype κ] [DecidableEq κ], ∀ r ≥ N,
      ∀ (U : Combinatorics.Subspace (Fin r) (Fin (k + 1)) ι)
        (A : Finset (ι ⊕ κ → Fin (k + 1))) (ρ : ℝ),
        δ₀ ≤ ρ →
        (∀ x : Word (k + 1) r,
          ρ - η₀ ^ 2 / 2 ≤ density (sectionTails U A x)) →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
          (∀ x : Word (k + 1) m,
            ρ - η₀ ^ 2 / 2 ≤ density (sectionTails V A x)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin m),
            IncrementArithmetic.theta δ₀
                (Fintype.card (Combinatorics.Line (Fin k) (Fin m₀))) ≤
              density (restrictedLineTails V A l) := by
  classical
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
  let : Nonempty (Fin m₀) := Fin.pos_iff_nonempty.mp hm₀
  obtain ⟨N, hN⟩ :=
    GrahamRothschild.exists_subspace_lines_subset_or_disjoint (Fin k) m
  refine ⟨N, ?_⟩
  intro ι κ _ _
  intro r hr U A ρ hρ hsection
  let θ : ℝ := IncrementArithmetic.theta δ₀
    (Fintype.card (Combinatorics.Line (Fin k) (Fin m₀)))
  let good : Set (Combinatorics.Line (Fin k) (Fin r)) :=
    {l | θ ≤ density (restrictedLineTails U A l)}
  obtain ⟨Y, hYgood | hYbad⟩ := hN r hr good
  · let V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι :=
      U.comp Y.finLift
    refine ⟨V, ?_, ?_⟩
    · intro x
      change ρ - η₀ ^ 2 / 2 ≤
        density (sectionTails (U.comp Y.finLift) A x)
      rw [sectionTails_comp]
      exact hsection (Y.finLift x)
    · intro l
      have hgood := hYgood l
      change θ ≤ density (restrictedLineTails U A (Y.lineMap l)) at hgood
      simpa [V, θ] using hgood
  · exfalso
    let F : Combinatorics.Subspace (Fin m₀) (Fin k) (Fin m) :=
      Combinatorics.Subspace.coordinateFace hm₀m
    let Zold : Combinatorics.Subspace (Fin m₀) (Fin k) (Fin r) := Y.comp F
    let Z : Combinatorics.Subspace (Fin m₀) (Fin (k + 1)) ι :=
      U.comp Zold.finLift
    have hbase : δ₀ / 2 ≤ ρ - η₀ ^ 2 / 2 := by linarith
    have hZsection : ∀ x : Word k m₀,
        δ₀ / 2 ≤ density (sectionTails Z A (liftWord x)) := by
      intro x
      apply hbase.trans
      change ρ - η₀ ^ 2 / 2 ≤
        density (sectionTails (U.comp Zold.finLift) A (liftWord x))
      rw [sectionTails_comp]
      exact hsection (Zold.finLift (liftWord x))
    have hDHJ' : ∀ B : Finset (Word k m₀),
        δ₀ / 4 ≤ density B →
          ∃ l : Combinatorics.Line (Fin k) (Fin m₀), ∀ a, l a ∈ B := by
      intro B hB
      exact (containsLine_coe_finset_iff.mp (hDHJ B hB))
    have hcorr : ∃ l : Combinatorics.Line (Fin k) (Fin m₀),
        IncrementArithmetic.theta δ₀
            (Fintype.card (Combinatorics.Line (Fin k) (Fin m₀))) ≤
          density (restrictedLineTails Z A l) := by
      apply exists_correlated_restricted_line
      · exact hδ₀
      · exact hZsection
      · exact hDHJ'
    obtain ⟨l, hl⟩ := hcorr
    have hl' : θ ≤ density
        (restrictedLineTails U A (Y.lineMap (F.lineMap l))) := by
      change θ ≤ density (restrictedLineTails (U.comp Zold.finLift) A l) at hl
      rw [restrictedLineTails_comp_finLift] at hl
      change θ ≤ density (restrictedLineTails U A (Zold.lineMap l)) at hl
      rw [show Zold = Y.comp F from rfl,
        Combinatorics.Subspace.lineMap_comp] at hl
      exact hl
    have hbad := hYbad (F.lineMap l)
    change ¬θ ≤ density
      (restrictedLineTails U A (Y.lineMap (F.lineMap l))) at hbad
    exact hbad hl'

/-! ## Many restricted lines from correlated sections -/

/-- DKT Lemma 8 for a fixed subspace of prefixes.  Point-section density and
restricted-line correlation are hypotheses; the conclusion supplies one fixed
tail on which both the density and the restricted-line fraction are large,
provided no such extension already gives the prescribed increment. -/
theorem exists_dense_extension_with_many_restricted_lines
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Nonempty η]
    [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (ρ η₀ θ : ℝ)
    (hη₀ : 0 < η₀) (hθ : 0 < θ) (hηθ : η₀ < θ / 2)
    (hsection : ∀ x : η → Fin (k + 1),
      ρ - η₀ ^ 2 / 2 ≤ density (sectionTails U A x))
    (hupper : ∀ y : κ → Fin (k + 1),
      subspaceDensityFinset (U.extendRightWord y) A ≤
        ρ + η₀ ^ 2 / 2)
    (hcorrelation : ∀ l : Combinatorics.Line (Fin k) η,
      θ ≤ density (restrictedLineTails U A l)) :
    ∃ y : κ → Fin (k + 1),
      ρ - 2 * η₀ < subspaceDensityFinset (U.extendRightWord y) A ∧
        θ / 2 < restrictedInternalLineFraction (U.extendRightWord y) A := by
  let f : (κ → Fin (k + 1)) → ℝ := fun y ↦
    subspaceDensityFinset (U.extendRightWord y) A
  let g : (κ → Fin (k + 1)) → ℝ := fun y ↦
    restrictedInternalLineFraction (U.extendRightWord y) A
  have hfavg : ρ - η₀ ^ 2 / 2 ≤ average f := by
    rw [average_extensionDensity_eq_average_sectionTails]
    exact const_le_average hsection
  have hgavg : θ ≤ average g := by
    rw [average_restrictedLineFraction_eq_average_restrictedLineTails]
    exact const_le_average hcorrelation
  exact exists_dense_and_lineRich_of_averages f g ρ η₀ θ hη₀ hθ hηθ
    hfavg hupper hgavg fun y ↦ restrictedInternalLineFraction_le_one _ _

/-- The disjunctive form of DKT Lemma 8 used by the density-increment
iteration.  The first branch is a genuine density increment on an arbitrary
`η`-dimensional subspace.  If it fails, every fixed-tail extension of `U` has
the upper bound needed by the finite averaging lemma, yielding the second
branch.

The parameters `η₀` and `θ` are normally selected using a fixed lower density
`δ₀`; the density `ρ` in this statement is the actual density and is not
silently replaced by `δ₀`. -/
theorem density_increment_or_many_restricted_lines
    {η ι κ : Type*} {k : ℕ}
    [Fintype η] [DecidableEq η] [Nonempty η]
    [Fintype κ] [DecidableEq κ]
    (U : Combinatorics.Subspace η (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (ρ η₀ θ : ℝ)
    (hη₀ : 0 < η₀) (hθ : 0 < θ) (hηθ : η₀ < θ / 2)
    (hsection : ∀ x : η → Fin (k + 1),
      ρ - η₀ ^ 2 / 2 ≤ density (sectionTails U A x))
    (hcorrelation : ∀ l : Combinatorics.Line (Fin k) η,
      θ ≤ density (restrictedLineTails U A l)) :
    (∃ W : Combinatorics.Subspace η (Fin (k + 1)) (ι ⊕ κ),
        ρ + η₀ ^ 2 / 2 < subspaceDensityFinset W A) ∨
      ∃ W : Combinatorics.Subspace η (Fin (k + 1)) (ι ⊕ κ),
        ρ - 2 * η₀ < subspaceDensityFinset W A ∧
          θ / 2 < restrictedInternalLineFraction W A := by
  classical
  by_cases hinc : ∃ W : Combinatorics.Subspace η (Fin (k + 1)) (ι ⊕ κ),
      ρ + η₀ ^ 2 / 2 < subspaceDensityFinset W A
  · exact Or.inl hinc
  · right
    push Not at hinc
    obtain ⟨y, hyDensity, hyLines⟩ :=
      exists_dense_extension_with_many_restricted_lines U A ρ η₀ θ
        hη₀ hθ hηθ hsection
        (fun y ↦ hinc (U.extendRightWord y)) hcorrelation
    exact ⟨U.extendRightWord y, hyDensity, hyLines⟩

end Erdos171
