/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.PartialConstruction
import ErdosProblems.Erdos136.Hypergraph
import ErdosProblems.Erdos136.AuxConcentration

/-!
# Counts for the alternating-cycle conflict system in Erdős 136

The four members of a conflict are precisely four auxiliary triangle blocks
which paint a properly alternating two-coloured four-cycle.  This file keeps
that semantic definition and supplies the finite cardinal estimates used to
put the conflict system into the `IsBounded` interface of the specialized
conflict-free matching theorem.

The main counting device is exact and reusable.  If every conflict has `r`
members and a root `s` is prescribed, erasing `s` injects conflicts containing
`s` into the `(r - |s|)`-subsets of the host hypergraph.  For the present
four-uniform system this gives

* conflict degree at most `choose |H| 3`;
* conflict codegree of a pair at most `choose |H| 2`;
* conflict codegree of a triple at most `|H|`.

For the application, the file also performs the sharp geometric charging.
If `A` bounds the constant-size oriented paint traces of one host edge and
`L` bounds every local paint fibre, then

* the conflict degree is at most `A * n² * k * L³`;
* every two-root codegree is at most `3 * A² * (n + k) * L²`;
* every three-root codegree is at most `6 * A³ * L`.

Eight-uniformity gives `A = 512`, while a host pair-codegree bound gives the
required `L`.  The final constructor inserts these bounds into `IsBounded`
and deals with the empty conflict layers automatically.
-/

namespace Erdos136

open Finset

variable {V : Type*} [DecidableEq V]

/-! ## Root-erasure counting -/

/-- Conflicts containing `s`, with the prescribed root erased. -/
def erasedConflictRoots (C : ConflictSystem V) (s : Hypergraph V) :
    ConflictSystem V :=
  (C.filter fun Q => s ⊆ Q).image fun Q => Q \ s

/-- On families containing a fixed root, erasing that root is injective. -/
theorem sdiff_injective_on_supersets (s : Hypergraph V) :
    Set.InjOn (fun Q : Hypergraph V => Q \ s) {Q | s ⊆ Q} := by
  intro A hA B hB hEq
  ext e
  by_cases he : e ∈ s
  · exact iff_of_true (hA he) (hB he)
  · have hmem : e ∈ A \ s ↔ e ∈ B \ s := by
      have hsets : A \ s = B \ s := hEq
      rw [hsets]
    simpa [he] using hmem

/-- Erasing a root preserves the number of unprescribed members. -/
theorem card_sdiff_of_conflict_root {C : ConflictSystem V} {r : ℕ}
    (huniform : ∀ Q ∈ C, Q.card = r) {s Q : Hypergraph V}
    (hQ : Q ∈ C) (hsQ : s ⊆ Q) :
    (Q \ s).card = r - s.card := by
  rw [Finset.card_sdiff_of_subset hsQ, huniform Q hQ]

/-- A uniform conflict system has at most `choose |H| (r-|s|)` conflicts
containing a prescribed root `s`.  No asymptotics or real arithmetic enter
this finite injection. -/
theorem codegree_le_choose_of_uniform
    {H : Hypergraph V} {C : ConflictSystem V} {r : ℕ}
    (hC : IsConflictSystem H C)
    (huniform : ∀ Q ∈ C, Q.card = r) (s : Hypergraph V) :
    codegree C s ≤ Nat.choose H.card (r - s.card) := by
  let F : ConflictSystem V := C.filter fun Q => s ⊆ Q
  let E : ConflictSystem V := F.image fun Q => Q \ s
  have hinj : Set.InjOn (fun Q : Hypergraph V => Q \ s) (↑F : Set (Hypergraph V)) := by
    apply (sdiff_injective_on_supersets s).mono
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  have hcardE : E.card = F.card := by
    simpa [E] using Finset.card_image_iff.mpr hinj
  have hsub : E ⊆ H.powersetCard (r - s.card) := by
    intro T hT
    obtain ⟨Q, hQF, rfl⟩ := Finset.mem_image.mp hT
    have hQ : Q ∈ C := (Finset.mem_filter.mp hQF).1
    have hsQ : s ⊆ Q := (Finset.mem_filter.mp hQF).2
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, card_sdiff_of_conflict_root huniform hQ hsQ⟩
    intro e he
    exact hC Q hQ (Finset.mem_sdiff.mp he).1
  have hle := Finset.card_le_card hsub
  rw [Finset.card_powersetCard, hcardE] at hle
  simpa [codegree, F] using hle

/-- Degree is the one-member instance of the root-erasure count. -/
theorem degree_le_choose_of_uniform
    {H : Hypergraph V} {C : ConflictSystem V} {r : ℕ}
    (hC : IsConflictSystem H C)
    (huniform : ∀ Q ∈ C, Q.card = r) (e : Finset V) :
    degree C e ≤ Nat.choose H.card (r - 1) := by
  rw [← codegree_singleton]
  simpa using codegree_le_choose_of_uniform hC huniform ({e} : Hypergraph V)

/-! ## The concrete alternating-cycle system -/

variable {n k : ℕ}

/-! ## Local paint fibres -/

/-- An oriented graph edge together with the old colour painted on it. -/
structure OrientedPaint (n k : ℕ) where
  left : Fin n
  right : Fin n
  color : Fin k
  deriving DecidableEq, Fintype

namespace OrientedPaint

/-- The three auxiliary vertices forced by an oriented painted edge: its
graph edge and the two endpoint/colour labels. -/
def auxTriple (p : OrientedPaint n k) :
    AuxVertex n k × AuxVertex n k × AuxVertex n k :=
  (Sum.inl s(p.left, p.right),
    Sum.inr (p.left, p.color), Sum.inr (p.right, p.color))

theorem auxTriple_injective :
    Function.Injective (auxTriple : OrientedPaint n k →
      AuxVertex n k × AuxVertex n k × AuxVertex n k) := by
  intro p q h
  have hleft : Sum.inr (p.left, p.color) =
      (Sum.inr (q.left, q.color) : AuxVertex n k) :=
    congrArg (fun z => z.2.1) h
  have hright : Sum.inr (p.right, p.color) =
      (Sum.inr (q.right, q.color) : AuxVertex n k) :=
    congrArg (fun z => z.2.2) h
  have hleft' : (p.left, p.color) = (q.left, q.color) := Sum.inr.inj hleft
  have hright' : (p.right, p.color) = (q.right, q.color) := Sum.inr.inj hright
  cases p
  cases q
  simp_all

@[ext] theorem ext {p q : OrientedPaint n k}
    (hleft : p.left = q.left) (hright : p.right = q.right)
    (hcolor : p.color = q.color) : p = q := by
  cases p
  cases q
  simp_all

end OrientedPaint

/-- Host hyperedges which can paint the oriented edge/colour `p`.  The
definition uses only the three forced auxiliary vertices, so it is at least
as large as the actual set of triangle blocks painting `p`; this direction
is the useful one for upper bounds. -/
def paintFiber (H : Hypergraph (AuxVertex n k)) (p : OrientedPaint n k) :
    Hypergraph (AuxVertex n k) :=
  H.filter fun e =>
    p.auxTriple.1 ∈ e ∧ p.auxTriple.2.1 ∈ e ∧ p.auxTriple.2.2 ∈ e

/-- Actual painting by a block places its support in the corresponding
local paint fibre. -/
theorem auxSupport_mem_paintFiber {H : Hypergraph (AuxVertex n k)}
    {b : TriangleBlock n k} {x y : Fin n} {c : Fin k}
    (hbH : b.auxSupport ∈ H) (hp : b.Paints x y c) :
    b.auxSupport ∈ paintFiber H ⟨x, y, c⟩ := by
  classical
  refine Finset.mem_filter.mpr ⟨hbH, ?_⟩
  exact ⟨b.paints_graph_mem hp, b.paints_label_mem hp,
    b.paints_other_label_mem hp⟩

/-- A paint fibre is contained in the link of the graph-edge/left-label
pair.  This is the local `O(d/n)` codegree used in the Joos--Mubayi count. -/
theorem paintFiber_card_le_codegree
    (H : Hypergraph (AuxVertex n k)) (p : OrientedPaint n k) :
    (paintFiber H p).card ≤
      codegree H {p.auxTriple.1, p.auxTriple.2.1} := by
  classical
  apply Finset.card_le_card
  intro e he
  have he' := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨he'.1, ?_⟩
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
    ⟨he'.2.1, he'.2.2.1⟩

/-- A paint fibre is also contained in the codegree fibre through its two
same-colour endpoint labels.  This is the inclusion used for the sharp
retention-dependent bound; the graph/label codegree can live at the larger
ambient `O(n^2)` scale. -/
theorem paintFiber_card_le_sameColorCodegree
    (H : Hypergraph (AuxVertex n k)) (p : OrientedPaint n k) :
    (paintFiber H p).card ≤
      codegree H {p.auxTriple.2.1, p.auxTriple.2.2} := by
  classical
  apply Finset.card_le_card
  intro e he
  have he' := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨he'.1, ?_⟩
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
    ⟨he'.2.2.1, he'.2.2.2⟩

/-- The retained-host same-colour estimate bounds every local paint fibre.
Diagonal oriented pairs have empty paint fibre because the auxiliary host
contains no diagonal graph-edge vertex. -/
theorem paintFiber_card_le_jmPairCodegreeCeil_of_host
    {n k : ℕ} {q delta : ℝ} {R : RetainedLabels n k}
    (hhost : AuxConcentration.UniversalRetainedHostEstimates q R)
    (hscale : ∀ a : AuxConcentration.SameColorIndex n k,
      AuxConcentration.universalSameColorTarget n k q a +
          AuxConcentration.universalCodegreeDeviation n a ≤
        5 * (n : ℝ) ^ (2 - delta))
    (p : OrientedPaint n k) :
    (paintFiber
        (auxiliaryHypergraph
          (AuxConcentration.allTriangleBlocks n k) R) p).card ≤
      jmPairCodegreeCeil 5 0 delta n := by
  classical
  let H := auxiliaryHypergraph (AuxConcentration.allTriangleBlocks n k) R
  by_cases hxy : p.left = p.right
  · have hempty : paintFiber H p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have he' := Finset.mem_filter.mp he
      have hv : p.auxTriple.1 ∈ vertexFinset H :=
        mem_vertexFinset.mpr ⟨e, he'.1, he'.2.1⟩
      have ha := AuxConcentration.active_of_mem_vertexFinset_auxiliaryHypergraph hv
      simp [AuxConcentration.ActiveAuxVertex, OrientedPaint.auxTriple, hxy] at ha
    rw [hempty]
    simp
  · let a : AuxConcentration.SameColorIndex n k :=
      ⟨p.color, p.left, p.right⟩
    by_cases hempty : paintFiber H p = ∅
    · rw [hempty]
      simp
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have he' := Finset.mem_filter.mp he
      have hleftVertex : p.auxTriple.2.1 ∈ vertexFinset H :=
        mem_vertexFinset.mpr ⟨e, he'.1, he'.2.2.1⟩
      have hrightVertex : p.auxTriple.2.2 ∈ vertexFinset H :=
        mem_vertexFinset.mpr ⟨e, he'.1, he'.2.2.2⟩
      have hleft :=
        AuxConcentration.active_of_mem_vertexFinset_auxiliaryHypergraph hleftVertex
      have hright :=
        AuxConcentration.active_of_mem_vertexFinset_auxiliaryHypergraph hrightVertex
      have hcodeg := AuxConcentration.sameColor_codegree_le_ceiling_of_host
        hhost a hxy (by
          simpa [a, AuxConcentration.ActiveAuxVertex,
            OrientedPaint.auxTriple] using hleft) (by
          simpa [a, AuxConcentration.ActiveAuxVertex,
            OrientedPaint.auxTriple] using hright) (hscale a)
      calc
        (paintFiber H p).card ≤
            codegree H {p.auxTriple.2.1, p.auxTriple.2.2} :=
          paintFiber_card_le_sameColorCodegree H p
        _ ≤ jmPairCodegreeCeil 5 0 delta n := by
          simpa [H, a, OrientedPaint.auxTriple] using hcodeg

@[simp] theorem graph_leftLabel_pair_card (p : OrientedPaint n k) :
    ({p.auxTriple.1, p.auxTriple.2.1} :
      Finset (AuxVertex n k)).card = 2 := by
  classical
  simp [OrientedPaint.auxTriple]

/-- Consequently a host pair-codegree bound immediately bounds every local
paint fibre. -/
theorem paintFiber_card_le_of_maxCodegree
    {H : Hypergraph (AuxVertex n k)} {L : ℕ}
    (hcodeg : MaxCodegreeLE H 2 L) (p : OrientedPaint n k) :
    (paintFiber H p).card ≤ L :=
  (paintFiber_card_le_codegree H p).trans
    (hcodeg _ (graph_leftLabel_pair_card p))

/-- The oriented paint traces supported by one auxiliary edge. -/
def paintTraces (e : Finset (AuxVertex n k)) : Finset (OrientedPaint n k) :=
  Finset.univ.filter fun p =>
    p.auxTriple.1 ∈ e ∧ p.auxTriple.2.1 ∈ e ∧ p.auxTriple.2.2 ∈ e

/-- An actual block painting supplies one of the traces of its support. -/
theorem mem_paintTraces_of_paints {b : TriangleBlock n k}
    {x y : Fin n} {c : Fin k} (hp : b.Paints x y c) :
    (⟨x, y, c⟩ : OrientedPaint n k) ∈ paintTraces b.auxSupport := by
  classical
  simp only [paintTraces, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b.paints_graph_mem hp, b.paints_label_mem hp,
    b.paints_other_label_mem hp⟩

/-- A fixed auxiliary edge has at most `|e|^3` oriented paint traces.  For
an 8-uniform host this is the absolute constant `512`; this removes any
spurious factor of `n` or `k` when one member of a conflict is rooted. -/
theorem paintTraces_card_le_cube (e : Finset (AuxVertex n k)) :
    (paintTraces e).card ≤ e.card ^ 3 := by
  classical
  let T := e.product (e.product e)
  have hinj : Function.Injective
      (OrientedPaint.auxTriple : OrientedPaint n k →
        AuxVertex n k × AuxVertex n k × AuxVertex n k) :=
    OrientedPaint.auxTriple_injective
  have hcardImage :
      ((paintTraces e).image OrientedPaint.auxTriple).card =
        (paintTraces e).card := by
    exact Finset.card_image_of_injective _ hinj
  have hsub : (paintTraces e).image OrientedPaint.auxTriple ⊆ T := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hp' := (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.mpr ⟨hp'.1,
      Finset.mem_product.mpr ⟨hp'.2.1, hp'.2.2⟩⟩
  have hle := Finset.card_le_card hsub
  rw [hcardImage] at hle
  simpa [T, pow_succ, mul_assoc] using hle

theorem paintTraces_card_le_512
    {H : Hypergraph (AuxVertex n k)} (huniform : IsUniform H 8)
    {e : Finset (AuxVertex n k)} (he : e ∈ H) :
    (paintTraces e).card ≤ 512 := by
  calc
    (paintTraces e).card ≤ e.card ^ 3 := paintTraces_card_le_cube e
    _ = 512 := by rw [huniform e he]; norm_num

@[simp] theorem mem_alternatingCycleConflicts
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {Q : Hypergraph (AuxVertex n k)} :
    Q ∈ alternatingCycleConflicts candidates R ↔
      Q ⊆ auxiliaryHypergraph candidates R ∧ Q.card = 4 ∧
        IsAlternatingCycleConflict Q := by
  classical
  simp [alternatingCycleConflicts, and_assoc]

/-- Every declared conflict retains the literal alternating two-colour
four-cycle witnesses from `IsAlternatingCycleConflict`. -/
theorem alternatingCycleConflicts_witness
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {Q : Hypergraph (AuxVertex n k)}
    (hQ : Q ∈ alternatingCycleConflicts candidates R) :
    ∃ (x₀ x₁ x₂ x₃ : Fin n) (c d : Fin k)
        (b₀ b₁ b₂ b₃ : TriangleBlock n k),
      FourDistinct x₀ x₁ x₂ x₃ ∧ c ≠ d ∧
      b₀.Paints x₀ x₁ c ∧ b₁.Paints x₁ x₂ d ∧
      b₂.Paints x₂ x₃ c ∧ b₃.Paints x₃ x₀ d ∧
      Q = {b₀.auxSupport, b₁.auxSupport, b₂.auxSupport, b₃.auxSupport} := by
  exact (mem_alternatingCycleConflicts.mp hQ).2.2

/-- A cyclically rooted form of an alternating conflict witness. -/
structure RootedAlternatingWitness
    (e : Finset (AuxVertex n k)) (Q : Hypergraph (AuxVertex n k)) where
  x₀ : Fin n
  x₁ : Fin n
  x₂ : Fin n
  x₃ : Fin n
  c : Fin k
  d : Fin k
  b₀ : TriangleBlock n k
  b₁ : TriangleBlock n k
  b₂ : TriangleBlock n k
  b₃ : TriangleBlock n k
  distinct : FourDistinct x₀ x₁ x₂ x₃
  colors_ne : c ≠ d
  paint₀ : b₀.Paints x₀ x₁ c
  paint₁ : b₁.Paints x₁ x₂ d
  paint₂ : b₂.Paints x₂ x₃ c
  paint₃ : b₃.Paints x₃ x₀ d
  root_support : b₀.auxSupport = e
  family_eq : Q = {e, b₁.auxSupport, b₂.auxSupport, b₃.auxSupport}

/-- Any member can be moved to the first position by a cyclic rotation. -/
theorem exists_rootedAlternatingWitness
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (hAlt : IsAlternatingCycleConflict Q) (heQ : e ∈ Q) :
    Nonempty (RootedAlternatingWitness e Q) := by
  classical
  rcases hAlt with
    ⟨x₀, x₁, x₂, x₃, c, d, b₀, b₁, b₂, b₃,
      hD, hcd, hp₀, hp₁, hp₂, hp₃, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at heQ
  rcases heQ with he | he | he | he
  · subst e
    exact ⟨{
      x₀ := x₀, x₁ := x₁, x₂ := x₂, x₃ := x₃,
      c := c, d := d, b₀ := b₀, b₁ := b₁, b₂ := b₂, b₃ := b₃,
      distinct := hD, colors_ne := hcd,
      paint₀ := hp₀, paint₁ := hp₁, paint₂ := hp₂, paint₃ := hp₃,
      root_support := rfl, family_eq := rfl }⟩
  · subst e
    refine ⟨{
      x₀ := x₁, x₁ := x₂, x₂ := x₃, x₃ := x₀,
      c := d, d := c, b₀ := b₁, b₁ := b₂, b₂ := b₃, b₃ := b₀,
      distinct := ?_, colors_ne := hcd.symm,
      paint₀ := hp₁, paint₁ := hp₂, paint₂ := hp₃, paint₃ := hp₀,
      root_support := rfl, family_eq := ?_ }⟩
    · unfold FourDistinct at hD ⊢
      aesop
    · ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
  · subst e
    refine ⟨{
      x₀ := x₂, x₁ := x₃, x₂ := x₀, x₃ := x₁,
      c := c, d := d, b₀ := b₂, b₁ := b₃, b₂ := b₀, b₃ := b₁,
      distinct := ?_, colors_ne := hcd,
      paint₀ := hp₂, paint₁ := hp₃, paint₂ := hp₀, paint₃ := hp₁,
      root_support := rfl, family_eq := ?_ }⟩
    · unfold FourDistinct at hD ⊢
      aesop
    · ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
  · subst e
    refine ⟨{
      x₀ := x₃, x₁ := x₀, x₂ := x₁, x₃ := x₂,
      c := d, d := c, b₀ := b₃, b₁ := b₀, b₂ := b₁, b₃ := b₂,
      distinct := ?_, colors_ne := hcd.symm,
      paint₀ := hp₃, paint₁ := hp₀, paint₂ := hp₁, paint₃ := hp₂,
      root_support := rfl, family_eq := ?_ }⟩
    · unfold FourDistinct at hD ⊢
      aesop
    · ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop

/-! ### One-root charging -/

/-- A canonical finite embedding of a finset of size at most `L` into
`Fin L`.  It is used only as a code; no choice made here affects the
combinatorial predicate. -/
noncomputable def finsetCode {X : Type*} [DecidableEq X]
    (S : Finset X) {L : ℕ} (hS : S.card ≤ L) : {x // x ∈ S} ↪ Fin L :=
  (Fintype.equivFin {x // x ∈ S}).toEmbedding.trans
    (Fin.castLEEmb (by simpa using hS))

/-- Equal finite domains make their local codes comparable; equality of
the codes then recovers equality of the underlying values. -/
theorem finsetCode_value_eq_of_finset_eq
    {X : Type*} [DecidableEq X] {S T : Finset X} {L : ℕ}
    (hS : S.card ≤ L) (hT : T.card ≤ L) (hST : S = T)
    (x : {x // x ∈ S}) (y : {x // x ∈ T})
    (hcode : finsetCode S hS x = finsetCode T hT y) : x.1 = y.1 := by
  subst T
  exact congrArg Subtype.val ((finsetCode S hS).injective hcode)

/-- Conflicts containing the distinguished auxiliary edge `e`. -/
def rootedConflicts (C : ConflictSystem (AuxVertex n k))
    (e : Finset (AuxVertex n k)) : ConflictSystem (AuxVertex n k) :=
  C.filter fun Q => e ∈ Q

@[simp] theorem rootedConflicts_card
    (C : ConflictSystem (AuxVertex n k)) (e : Finset (AuxVertex n k)) :
    (rootedConflicts C e).card = degree C e := by
  rfl

/-- Canonically select the cyclically rooted witness of a rooted declared
conflict. -/
noncomputable def rootedConflictWitness
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e : Finset (AuxVertex n k))
    (Q : ↑(rootedConflicts (alternatingCycleConflicts candidates R) e)) :
    RootedAlternatingWitness e Q.1 := by
  classical
  have hQ : Q.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q.2).1
  have heQ : e ∈ Q.1 := (Finset.mem_filter.mp Q.2).2
  exact Classical.choice
    (exists_rootedAlternatingWitness
      (mem_alternatingCycleConflicts.mp hQ).2.2 heQ)

/-- The fixed product in which a one-root charge lives: a constant-size
trace code, the two still-free vertices and other colour, and three local
paint-fibre codes. -/
abbrev OneRootCharge (n k A L : ℕ) :=
  Fin A × Fin n × Fin n × Fin k × Fin L × Fin L × Fin L

/-- The explicit charge of a conflict containing `e`. -/
noncomputable def oneRootCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e : Finset (AuxVertex n k))
    (Q : ↑(rootedConflicts (alternatingCycleConflicts candidates R) e)) :
    OneRootCharge n k A L := by
  classical
  let H := auxiliaryHypergraph candidates R
  let w := rootedConflictWitness candidates R e Q
  have hQconf : Q.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q.2).1
  have hQH : Q.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q.1 hQconf
  have heH : e ∈ H := hQH (Finset.mem_filter.mp Q.2).2
  let p₀ : OrientedPaint n k := ⟨w.x₀, w.x₁, w.c⟩
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  have hp₀ : p₀ ∈ paintTraces e := by
    rw [← w.root_support]
    exact mem_paintTraces_of_paints w.paint₀
  have hb₁Q : w.b₁.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₁.auxSupport ∈ T) w.family_eq
    simpa using h
  have hb₂Q : w.b₂.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₂.auxSupport ∈ T) w.family_eq
    simpa using h
  have hb₃Q : w.b₃.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₃.auxSupport ∈ T) w.family_eq
    simpa using h
  have hp₁ : w.b₁.auxSupport ∈ paintFiber H p₁ :=
    auxSupport_mem_paintFiber (hQH hb₁Q) w.paint₁
  have hp₂ : w.b₂.auxSupport ∈ paintFiber H p₂ :=
    auxSupport_mem_paintFiber (hQH hb₂Q) w.paint₂
  have hp₃ : w.b₃.auxSupport ∈ paintFiber H p₃ :=
    auxSupport_mem_paintFiber (hQH hb₃Q) w.paint₃
  exact
    (finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
      w.x₂, w.x₃, w.d,
      finsetCode (paintFiber H p₁) (hpaint p₁) ⟨w.b₁.auxSupport, hp₁⟩,
      finsetCode (paintFiber H p₂) (hpaint p₂) ⟨w.b₂.auxSupport, hp₂⟩,
      finsetCode (paintFiber H p₃) (hpaint p₃) ⟨w.b₃.auxSupport, hp₃⟩)

/-- The one-root charge is injective: equality of trace codes recovers the
rooted painted edge, and equality of the three local fibre codes recovers
the other three members, hence the entire conflict. -/
theorem oneRootCharge_injective
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e : Finset (AuxVertex n k)) :
    Function.Injective (oneRootCharge candidates R A L htrace hpaint e) := by
  classical
  intro Q Q' hcharge
  let H := auxiliaryHypergraph candidates R
  let w := rootedConflictWitness candidates R e Q
  let w' := rootedConflictWitness candidates R e Q'
  have hQconf : Q.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q.2).1
  have hQconf' : Q'.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q'.2).1
  have hQH : Q.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q.1 hQconf
  have hQH' : Q'.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q'.1 hQconf'
  have heH : e ∈ H := hQH (Finset.mem_filter.mp Q.2).2
  have heH' : e ∈ H := hQH' (Finset.mem_filter.mp Q'.2).2
  simp only [oneRootCharge] at hcharge
  have ht := congrArg (fun z => z.1) hcharge
  have hx₂ := congrArg (fun z => z.2.1) hcharge
  have hx₃ := congrArg (fun z => z.2.2.1) hcharge
  have hd := congrArg (fun z => z.2.2.2.1) hcharge
  have hi₁ := congrArg (fun z => z.2.2.2.2.1) hcharge
  have hi₂ := congrArg (fun z => z.2.2.2.2.2.1) hcharge
  have hi₃ := congrArg (fun z => z.2.2.2.2.2.2) hcharge
  change w.x₂ = w'.x₂ at hx₂
  change w.x₃ = w'.x₃ at hx₃
  change w.d = w'.d at hd
  change finsetCode (paintTraces e) (htrace e heH) _ =
    finsetCode (paintTraces e) (htrace e heH') _ at ht
  have hp₀ : (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) =
      ⟨w'.x₀, w'.x₁, w'.c⟩ := by
    exact congrArg Subtype.val ((finsetCode (paintTraces e)
      (htrace e heH)).injective ht)
  have hx₀ : w.x₀ = w'.x₀ := congrArg OrientedPaint.left hp₀
  have hx₁ : w.x₁ = w'.x₁ := congrArg OrientedPaint.right hp₀
  have hc : w.c = w'.c := congrArg OrientedPaint.color hp₀
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₁' : OrientedPaint n k := ⟨w'.x₁, w'.x₂, w'.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₂' : OrientedPaint n k := ⟨w'.x₂, w'.x₃, w'.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  let p₃' : OrientedPaint n k := ⟨w'.x₃, w'.x₀, w'.d⟩
  have hp₁eq : p₁ = p₁' := by
    apply OrientedPaint.ext <;> assumption
  have hp₂eq : p₂ = p₂' := by
    apply OrientedPaint.ext <;> assumption
  have hp₃eq : p₃ = p₃' := by
    apply OrientedPaint.ext <;> assumption
  have wb₁Q : w.b₁.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₁.auxSupport ∈ T) w.family_eq
    simpa using h
  have wb₂Q : w.b₂.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₂.auxSupport ∈ T) w.family_eq
    simpa using h
  have wb₃Q : w.b₃.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₃.auxSupport ∈ T) w.family_eq
    simpa using h
  have wb₁Q' : w'.b₁.auxSupport ∈ Q'.1 := by
    have h := congrArg (fun T => w'.b₁.auxSupport ∈ T) w'.family_eq
    simpa using h
  have wb₂Q' : w'.b₂.auxSupport ∈ Q'.1 := by
    have h := congrArg (fun T => w'.b₂.auxSupport ∈ T) w'.family_eq
    simpa using h
  have wb₃Q' : w'.b₃.auxSupport ∈ Q'.1 := by
    have h := congrArg (fun T => w'.b₃.auxSupport ∈ T) w'.family_eq
    simpa using h
  have wp₁ : w.b₁.auxSupport ∈ paintFiber H p₁ :=
    auxSupport_mem_paintFiber (hQH wb₁Q) w.paint₁
  have wp₂ : w.b₂.auxSupport ∈ paintFiber H p₂ :=
    auxSupport_mem_paintFiber (hQH wb₂Q) w.paint₂
  have wp₃ : w.b₃.auxSupport ∈ paintFiber H p₃ :=
    auxSupport_mem_paintFiber (hQH wb₃Q) w.paint₃
  have wp₁' : w'.b₁.auxSupport ∈ paintFiber H p₁' :=
    auxSupport_mem_paintFiber (hQH' wb₁Q') w'.paint₁
  have wp₂' : w'.b₂.auxSupport ∈ paintFiber H p₂' :=
    auxSupport_mem_paintFiber (hQH' wb₂Q') w'.paint₂
  have wp₃' : w'.b₃.auxSupport ∈ paintFiber H p₃' :=
    auxSupport_mem_paintFiber (hQH' wb₃Q') w'.paint₃
  have hb₁ : w.b₁.auxSupport = w'.b₁.auxSupport := by
    change finsetCode (paintFiber H p₁) (hpaint p₁) _ =
      finsetCode (paintFiber H p₁') (hpaint p₁') _ at hi₁
    exact finsetCode_value_eq_of_finset_eq (hpaint p₁) (hpaint p₁')
      (congrArg (paintFiber H) hp₁eq) _ _ hi₁
  have hb₂ : w.b₂.auxSupport = w'.b₂.auxSupport := by
    change finsetCode (paintFiber H p₂) (hpaint p₂) _ =
      finsetCode (paintFiber H p₂') (hpaint p₂') _ at hi₂
    exact finsetCode_value_eq_of_finset_eq (hpaint p₂) (hpaint p₂')
      (congrArg (paintFiber H) hp₂eq) _ _ hi₂
  have hb₃ : w.b₃.auxSupport = w'.b₃.auxSupport := by
    change finsetCode (paintFiber H p₃) (hpaint p₃) _ =
      finsetCode (paintFiber H p₃') (hpaint p₃') _ at hi₃
    exact finsetCode_value_eq_of_finset_eq (hpaint p₃) (hpaint p₃')
      (congrArg (paintFiber H) hp₃eq) _ _ hi₃
  apply Subtype.ext
  rw [w.family_eq, w'.family_eq, hb₁, hb₂, hb₃]

/-- Sharp one-root conflict-degree bound obtained from the explicit charge. -/
theorem alternatingCycleConflict_degree_le_local
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e : Finset (AuxVertex n k)) :
    degree (alternatingCycleConflicts candidates R) e ≤
      A * n * n * k * L * L * L := by
  rw [← rootedConflicts_card]
  rw [← Fintype.card_coe]
  have hcard := Fintype.card_le_of_embedding
    (Function.Embedding.mk
      (oneRootCharge candidates R A L htrace hpaint e)
      (oneRootCharge_injective candidates R A L htrace hpaint e))
  simpa [OneRootCharge, mul_assoc] using hcard

/-- In the concrete 8-uniform auxiliary host, a pair-codegree bound `L`
gives the sharp polynomial maximum conflict-degree estimate. -/
theorem alternatingCycleConflict_degree_le_of_maxCodegree
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (L : ℕ)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (e : Finset (AuxVertex n k)) :
    degree (alternatingCycleConflicts candidates R) e ≤
      512 * n * n * k * L * L * L := by
  apply alternatingCycleConflict_degree_le_local candidates R 512 L
  · intro f hf
    exact paintTraces_card_le_512
      (fun a ha => auxiliaryHypergraph_uniform candidates R ha) hf
  · exact paintFiber_card_le_of_maxCodegree hcodeg

/-! ### Two-root charging -/

/-- Conflicts containing both distinguished auxiliary edges. -/
def twoRootConflicts (C : ConflictSystem (AuxVertex n k))
    (e f : Finset (AuxVertex n k)) : ConflictSystem (AuxVertex n k) :=
  C.filter fun Q => e ∈ Q ∧ f ∈ Q

theorem twoRootConflicts_card_eq_codegree
    (C : ConflictSystem (AuxVertex n k))
    (e f : Finset (AuxVertex n k)) :
    (twoRootConflicts C e f).card = codegree C {e, f} := by
  classical
  apply congrArg Finset.card
  ext Q
  simp only [twoRootConflicts, Finset.mem_filter,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- Forgetting the second root gives a one-root conflict. -/
def twoRootToOneRoot
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (Q : ↑(twoRootConflicts (alternatingCycleConflicts candidates R) e f)) :
    ↑(rootedConflicts (alternatingCycleConflicts candidates R) e) :=
  ⟨Q.1, by
    rw [rootedConflicts, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp Q.2).1, (Finset.mem_filter.mp Q.2).2.1⟩⟩

noncomputable def twoRootConflictWitness
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (Q : ↑(twoRootConflicts (alternatingCycleConflicts candidates R) e f)) :
    RootedAlternatingWitness e Q.1 :=
  rootedConflictWitness candidates R e
    (twoRootToOneRoot candidates R e f Q)

/-- Once the first member is rooted, a distinct second member occupies one
of the three remaining cycle positions. -/
theorem twoRootWitness_second_position
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)} (hef : e ≠ f)
    (Q : ↑(twoRootConflicts (alternatingCycleConflicts candidates R) e f)) :
    let w := twoRootConflictWitness candidates R e f Q
    f = w.b₁.auxSupport ∨ f = w.b₂.auxSupport ∨ f = w.b₃.auxSupport := by
  classical
  let w := twoRootConflictWitness candidates R e f Q
  have hfQ : f ∈ Q.1 := (Finset.mem_filter.mp Q.2).2.2
  have hmem := congrArg (fun T => f ∈ T) w.family_eq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem.mp hfQ with hfe | hf₁ | hf₂ | hf₃
  · exact (hef hfe.symm).elim
  · exact Or.inl hf₁
  · exact Or.inr (Or.inl hf₂)
  · exact Or.inr (Or.inr hf₃)

/-- Branch, root trace, second-root trace, the single remaining vertex or
colour, and the two unrooted local paint-fibre codes. -/
abbrev TwoRootCharge (n k A L : ℕ) :=
  Fin 3 × Fin A × Fin A × Fin (n + k) × Fin L × Fin L

/-- The sharp two-root charge, split according to the cyclic position of the second root. -/
noncomputable def twoRootCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k)) (hef : e ≠ f)
    (Q : ↑(twoRootConflicts (alternatingCycleConflicts candidates R) e f)) :
    TwoRootCharge n k A L := by
  classical
  let H := auxiliaryHypergraph candidates R
  let w := twoRootConflictWitness candidates R e f Q
  have hQconf : Q.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q.2).1
  have hQH : Q.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q.1 hQconf
  have heQ : e ∈ Q.1 := (Finset.mem_filter.mp Q.2).2.1
  have hfQ : f ∈ Q.1 := (Finset.mem_filter.mp Q.2).2.2
  have heH : e ∈ H := hQH heQ
  have hfH : f ∈ H := hQH hfQ
  have hb₁Q : w.b₁.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₁.auxSupport ∈ T) w.family_eq
    simpa using h
  have hb₂Q : w.b₂.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₂.auxSupport ∈ T) w.family_eq
    simpa using h
  have hb₃Q : w.b₃.auxSupport ∈ Q.1 := by
    have h := congrArg (fun T => w.b₃.auxSupport ∈ T) w.family_eq
    simpa using h
  let p₀ : OrientedPaint n k := ⟨w.x₀, w.x₁, w.c⟩
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  have hp₀ : p₀ ∈ paintTraces e := by
    rw [← w.root_support]
    exact mem_paintTraces_of_paints w.paint₀
  have hp₁ : w.b₁.auxSupport ∈ paintFiber H p₁ :=
    auxSupport_mem_paintFiber (hQH hb₁Q) w.paint₁
  have hp₂ : w.b₂.auxSupport ∈ paintFiber H p₂ :=
    auxSupport_mem_paintFiber (hQH hb₂Q) w.paint₂
  have hp₃ : w.b₃.auxSupport ∈ paintFiber H p₃ :=
    auxSupport_mem_paintFiber (hQH hb₃Q) w.paint₃
  if hf₁ : f = w.b₁.auxSupport then
    have htf : p₁ ∈ paintTraces f := by
      rw [hf₁]
      exact mem_paintTraces_of_paints w.paint₁
    exact
      (⟨0, by omega⟩,
        finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
        finsetCode (paintTraces f) (htrace f hfH) ⟨p₁, htf⟩,
        Fin.castAdd k w.x₃,
        finsetCode (paintFiber H p₂) (hpaint p₂) ⟨w.b₂.auxSupport, hp₂⟩,
        finsetCode (paintFiber H p₃) (hpaint p₃) ⟨w.b₃.auxSupport, hp₃⟩)
  else if hf₂ : f = w.b₂.auxSupport then
    have htf : p₂ ∈ paintTraces f := by
      rw [hf₂]
      exact mem_paintTraces_of_paints w.paint₂
    exact
      (⟨1, by omega⟩,
        finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
        finsetCode (paintTraces f) (htrace f hfH) ⟨p₂, htf⟩,
        Fin.natAdd n w.d,
        finsetCode (paintFiber H p₁) (hpaint p₁) ⟨w.b₁.auxSupport, hp₁⟩,
        finsetCode (paintFiber H p₃) (hpaint p₃) ⟨w.b₃.auxSupport, hp₃⟩)
  else
    have hf₃ : f = w.b₃.auxSupport := by
      rcases twoRootWitness_second_position candidates R hef Q with h | h | h
      · exact (hf₁ h).elim
      · exact (hf₂ h).elim
      · exact h
    have htf : p₃ ∈ paintTraces f := by
      rw [hf₃]
      exact mem_paintTraces_of_paints w.paint₃
    exact
      (⟨2, by omega⟩,
        finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
        finsetCode (paintTraces f) (htrace f hfH) ⟨p₃, htf⟩,
        Fin.castAdd k w.x₂,
        finsetCode (paintFiber H p₁) (hpaint p₁) ⟨w.b₁.auxSupport, hp₁⟩,
        finsetCode (paintFiber H p₂) (hpaint p₂) ⟨w.b₂.auxSupport, hp₂⟩)


noncomputable section

variable {n k : ℕ}

/-- Conflicts containing two prescribed auxiliary edges. -/
def pairRootedConflicts (C : ConflictSystem (AuxVertex n k))
    (e f : Finset (AuxVertex n k)) : ConflictSystem (AuxVertex n k) :=
  C.filter fun Q => e ∈ Q ∧ f ∈ Q

@[simp] theorem pairRootedConflicts_card
    (C : ConflictSystem (AuxVertex n k)) (e f : Finset (AuxVertex n k)) :
    (pairRootedConflicts C e f).card = codegree C {e, f} := by
  classical
  unfold pairRootedConflicts codegree
  congr 1
  ext Q
  simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- Regard a two-rooted conflict as a conflict rooted at its first edge. -/
def pairAsFirstRoot
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    ↑(rootedConflicts (alternatingCycleConflicts candidates R) e) :=
  ⟨Q.1, (Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp Q.2).1, (Finset.mem_filter.mp Q.2).2.1⟩)⟩

/-- The selected cyclic witness, rooted at the first prescribed edge. -/
def pairRootedWitness
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    RootedAlternatingWitness e Q.1 :=
  rootedConflictWitness candidates R e (pairAsFirstRoot candidates R e f Q)

/-- The three possible cyclic positions of the second root. -/
abbrev SecondRootPosition := Fin 3

/-- Position of the second root in the witness rooted at the first. -/
def secondRootPosition
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    SecondRootPosition :=
  let w := pairRootedWitness candidates R e f Q
  if f = w.b₁.auxSupport then 0
  else if f = w.b₂.auxSupport then 1
  else 2

private theorem second_root_member_cases
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)} (hef : e ≠ f)
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    let w := pairRootedWitness candidates R e f Q
    f = w.b₁.auxSupport ∨ f = w.b₂.auxSupport ∨ f = w.b₃.auxSupport := by
  let w := pairRootedWitness candidates R e f Q
  have hfQ : f ∈ Q.1 := (Finset.mem_filter.mp Q.2).2.2
  have hf : f = e ∨ f = w.b₁.auxSupport ∨
      f = w.b₂.auxSupport ∨ f = w.b₃.auxSupport := by
    rw [w.family_eq] at hfQ
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hfQ
  exact hf.resolve_left (fun h => hef h.symm)

private theorem secondRootPosition_next
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f))
    (h : secondRootPosition candidates R e f Q = 0) :
    f = (pairRootedWitness candidates R e f Q).b₁.auxSupport := by
  simp only [secondRootPosition] at h
  split at h
  · assumption
  · split at h <;> contradiction

private theorem secondRootPosition_opposite
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f))
    (h : secondRootPosition candidates R e f Q = 1) :
    f = (pairRootedWitness candidates R e f Q).b₂.auxSupport := by
  simp only [secondRootPosition] at h
  split at h
  · contradiction
  · split at h
    · assumption
    · contradiction

private theorem secondRootPosition_previous
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)} (hef : e ≠ f)
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f))
    (h : secondRootPosition candidates R e f Q = 2) :
    f = (pairRootedWitness candidates R e f Q).b₃.auxSupport := by
  have hcases := second_root_member_cases candidates R hef Q
  simp only [secondRootPosition] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · exact hcases.resolve_left ‹f ≠ _› |>.resolve_left ‹f ≠ _›

/-- The fiber of two-rooted conflicts having a fixed cyclic position. -/
abbrev PositionFiber
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k)) (i : Fin 3) :=
  {Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f) //
    secondRootPosition candidates R e f Q = i}

private theorem pair_conflict_subset_host
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    Q.1 ⊆ auxiliaryHypergraph candidates R := by
  exact alternatingCycleConflicts_isConflictSystem candidates R Q.1
    (Finset.mem_filter.mp Q.2).1

private theorem pair_first_mem_host
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    e ∈ auxiliaryHypergraph candidates R :=
  pair_conflict_subset_host candidates R Q (Finset.mem_filter.mp Q.2).2.1

private theorem pair_second_mem_host
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    f ∈ auxiliaryHypergraph candidates R :=
  pair_conflict_subset_host candidates R Q (Finset.mem_filter.mp Q.2).2.2

private theorem witness_b₁_mem
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    (pairRootedWitness candidates R e f Q).b₁.auxSupport ∈ Q.1 := by
  let w := pairRootedWitness candidates R e f Q
  have h := congrArg (fun T => w.b₁.auxSupport ∈ T) w.family_eq
  simpa using h

private theorem witness_b₂_mem
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    (pairRootedWitness candidates R e f Q).b₂.auxSupport ∈ Q.1 := by
  let w := pairRootedWitness candidates R e f Q
  have h := congrArg (fun T => w.b₂.auxSupport ∈ T) w.family_eq
  simpa using h

private theorem witness_b₃_mem
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)}
    (Q : ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)) :
    (pairRootedWitness candidates R e f Q).b₃.auxSupport ∈ Q.1 := by
  let w := pairRootedWitness candidates R e f Q
  have h := congrArg (fun T => w.b₃.auxSupport ∈ T) w.family_eq
  simpa using h

abbrev AdjacentPairCharge (n A L : ℕ) :=
  Fin A × Fin A × Fin n × Fin L × Fin L

abbrev OppositePairCharge (k A L : ℕ) :=
  Fin A × Fin A × Fin k × Fin L × Fin L

/-- Charge for the case in which `f` is the successor of `e` around the
alternating four-cycle. -/
def nextPairCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k))
    (Q : PositionFiber candidates R e f 0) : AdjacentPairCharge n A L := by
  classical
  let H := auxiliaryHypergraph candidates R
  let q := Q.1
  let w := pairRootedWitness candidates R e f q
  have heH : e ∈ H := pair_first_mem_host candidates R q
  have hfH : f ∈ H := pair_second_mem_host candidates R q
  have hf : f = w.b₁.auxSupport :=
    secondRootPosition_next candidates R q Q.2
  let p₀ : OrientedPaint n k := ⟨w.x₀, w.x₁, w.c⟩
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  have hp₀ : p₀ ∈ paintTraces e := by
    rw [← w.root_support]
    exact mem_paintTraces_of_paints w.paint₀
  have hp₁ : p₁ ∈ paintTraces f := by
    rw [hf]
    exact mem_paintTraces_of_paints w.paint₁
  have hp₂ : w.b₂.auxSupport ∈ paintFiber H p₂ :=
    auxSupport_mem_paintFiber
      (pair_conflict_subset_host candidates R q (witness_b₂_mem candidates R q)) w.paint₂
  have hp₃ : w.b₃.auxSupport ∈ paintFiber H p₃ :=
    auxSupport_mem_paintFiber
      (pair_conflict_subset_host candidates R q (witness_b₃_mem candidates R q)) w.paint₃
  exact
    (finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
      finsetCode (paintTraces f) (htrace f hfH) ⟨p₁, hp₁⟩,
      w.x₃,
      finsetCode (paintFiber H p₂) (hpaint p₂) ⟨w.b₂.auxSupport, hp₂⟩,
      finsetCode (paintFiber H p₃) (hpaint p₃) ⟨w.b₃.auxSupport, hp₃⟩)

theorem nextPairCharge_injective
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k)) :
    Function.Injective (nextPairCharge candidates R A L htrace hpaint e f) := by
  classical
  intro Q Q' hcharge
  let H := auxiliaryHypergraph candidates R
  let q := Q.1
  let q' := Q'.1
  let w := pairRootedWitness candidates R e f q
  let w' := pairRootedWitness candidates R e f q'
  have heH : e ∈ H := pair_first_mem_host candidates R q
  have heH' : e ∈ H := pair_first_mem_host candidates R q'
  have hfH : f ∈ H := pair_second_mem_host candidates R q
  have hfH' : f ∈ H := pair_second_mem_host candidates R q'
  have hf : f = w.b₁.auxSupport :=
    secondRootPosition_next candidates R q Q.2
  have hf' : f = w'.b₁.auxSupport :=
    secondRootPosition_next candidates R q' Q'.2
  simp only [nextPairCharge] at hcharge
  have ht₀ := congrArg (fun z => z.1) hcharge
  have ht₁ := congrArg (fun z => z.2.1) hcharge
  have hx₃ := congrArg (fun z => z.2.2.1) hcharge
  have hi₂ := congrArg (fun z => z.2.2.2.1) hcharge
  have hi₃ := congrArg (fun z => z.2.2.2.2) hcharge
  change w.x₃ = w'.x₃ at hx₃
  change finsetCode (paintTraces e) (htrace e heH) _ =
    finsetCode (paintTraces e) (htrace e heH') _ at ht₀
  have hp₀ : (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) =
      ⟨w'.x₀, w'.x₁, w'.c⟩ :=
    congrArg Subtype.val ((finsetCode (paintTraces e) (htrace e heH)).injective ht₀)
  have hx₀ : w.x₀ = w'.x₀ := congrArg OrientedPaint.left hp₀
  have hx₁ : w.x₁ = w'.x₁ := congrArg OrientedPaint.right hp₀
  have hc : w.c = w'.c := congrArg OrientedPaint.color hp₀
  change finsetCode (paintTraces f) (htrace f hfH) _ =
    finsetCode (paintTraces f) (htrace f hfH') _ at ht₁
  have hp₁ : (⟨w.x₁, w.x₂, w.d⟩ : OrientedPaint n k) =
      ⟨w'.x₁, w'.x₂, w'.d⟩ :=
    congrArg Subtype.val ((finsetCode (paintTraces f) (htrace f hfH)).injective ht₁)
  have hx₂ : w.x₂ = w'.x₂ := congrArg OrientedPaint.right hp₁
  have hd : w.d = w'.d := congrArg OrientedPaint.color hp₁
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₂' : OrientedPaint n k := ⟨w'.x₂, w'.x₃, w'.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  let p₃' : OrientedPaint n k := ⟨w'.x₃, w'.x₀, w'.d⟩
  have hp₂eq : p₂ = p₂' := by
    apply OrientedPaint.ext <;> assumption
  have hp₃eq : p₃ = p₃' := by
    apply OrientedPaint.ext <;> assumption
  have hb₂ : w.b₂.auxSupport = w'.b₂.auxSupport := by
    change finsetCode (paintFiber H p₂) (hpaint p₂) _ =
      finsetCode (paintFiber H p₂') (hpaint p₂') _ at hi₂
    exact finsetCode_value_eq_of_finset_eq (hpaint p₂) (hpaint p₂')
      (congrArg (paintFiber H) hp₂eq) _ _ hi₂
  have hb₃ : w.b₃.auxSupport = w'.b₃.auxSupport := by
    change finsetCode (paintFiber H p₃) (hpaint p₃) _ =
      finsetCode (paintFiber H p₃') (hpaint p₃') _ at hi₃
    exact finsetCode_value_eq_of_finset_eq (hpaint p₃) (hpaint p₃')
      (congrArg (paintFiber H) hp₃eq) _ _ hi₃
  apply Subtype.ext
  apply Subtype.ext
  rw [w.family_eq, w'.family_eq, ← hf, ← hf', hb₂, hb₃]

/-- Charge for the case in which the two roots are opposite. -/
def oppositePairCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k))
    (Q : PositionFiber candidates R e f 1) : OppositePairCharge k A L := by
  classical
  let H := auxiliaryHypergraph candidates R
  let q := Q.1
  let w := pairRootedWitness candidates R e f q
  have heH : e ∈ H := pair_first_mem_host candidates R q
  have hfH : f ∈ H := pair_second_mem_host candidates R q
  have hf : f = w.b₂.auxSupport :=
    secondRootPosition_opposite candidates R q Q.2
  let p₀ : OrientedPaint n k := ⟨w.x₀, w.x₁, w.c⟩
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  have hp₀ : p₀ ∈ paintTraces e := by
    rw [← w.root_support]
    exact mem_paintTraces_of_paints w.paint₀
  have hp₂ : p₂ ∈ paintTraces f := by
    rw [hf]
    exact mem_paintTraces_of_paints w.paint₂
  have hp₁ : w.b₁.auxSupport ∈ paintFiber H p₁ :=
    auxSupport_mem_paintFiber
      (pair_conflict_subset_host candidates R q (witness_b₁_mem candidates R q)) w.paint₁
  have hp₃ : w.b₃.auxSupport ∈ paintFiber H p₃ :=
    auxSupport_mem_paintFiber
      (pair_conflict_subset_host candidates R q (witness_b₃_mem candidates R q)) w.paint₃
  exact
    (finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
      finsetCode (paintTraces f) (htrace f hfH) ⟨p₂, hp₂⟩,
      w.d,
      finsetCode (paintFiber H p₁) (hpaint p₁) ⟨w.b₁.auxSupport, hp₁⟩,
      finsetCode (paintFiber H p₃) (hpaint p₃) ⟨w.b₃.auxSupport, hp₃⟩)

theorem oppositePairCharge_injective
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k)) :
    Function.Injective (oppositePairCharge candidates R A L htrace hpaint e f) := by
  classical
  intro Q Q' hcharge
  let H := auxiliaryHypergraph candidates R
  let q := Q.1
  let q' := Q'.1
  let w := pairRootedWitness candidates R e f q
  let w' := pairRootedWitness candidates R e f q'
  have heH : e ∈ H := pair_first_mem_host candidates R q
  have heH' : e ∈ H := pair_first_mem_host candidates R q'
  have hfH : f ∈ H := pair_second_mem_host candidates R q
  have hfH' : f ∈ H := pair_second_mem_host candidates R q'
  have hf : f = w.b₂.auxSupport :=
    secondRootPosition_opposite candidates R q Q.2
  have hf' : f = w'.b₂.auxSupport :=
    secondRootPosition_opposite candidates R q' Q'.2
  simp only [oppositePairCharge] at hcharge
  have ht₀ := congrArg (fun z => z.1) hcharge
  have ht₂ := congrArg (fun z => z.2.1) hcharge
  have hd := congrArg (fun z => z.2.2.1) hcharge
  have hi₁ := congrArg (fun z => z.2.2.2.1) hcharge
  have hi₃ := congrArg (fun z => z.2.2.2.2) hcharge
  change w.d = w'.d at hd
  change finsetCode (paintTraces e) (htrace e heH) _ =
    finsetCode (paintTraces e) (htrace e heH') _ at ht₀
  have hp₀ : (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) =
      ⟨w'.x₀, w'.x₁, w'.c⟩ :=
    congrArg Subtype.val ((finsetCode (paintTraces e) (htrace e heH)).injective ht₀)
  have hx₀ : w.x₀ = w'.x₀ := congrArg OrientedPaint.left hp₀
  have hx₁ : w.x₁ = w'.x₁ := congrArg OrientedPaint.right hp₀
  have hc : w.c = w'.c := congrArg OrientedPaint.color hp₀
  change finsetCode (paintTraces f) (htrace f hfH) _ =
    finsetCode (paintTraces f) (htrace f hfH') _ at ht₂
  have hp₂ : (⟨w.x₂, w.x₃, w.c⟩ : OrientedPaint n k) =
      ⟨w'.x₂, w'.x₃, w'.c⟩ :=
    congrArg Subtype.val ((finsetCode (paintTraces f) (htrace f hfH)).injective ht₂)
  have hx₂ : w.x₂ = w'.x₂ := congrArg OrientedPaint.left hp₂
  have hx₃ : w.x₃ = w'.x₃ := congrArg OrientedPaint.right hp₂
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₁' : OrientedPaint n k := ⟨w'.x₁, w'.x₂, w'.d⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  let p₃' : OrientedPaint n k := ⟨w'.x₃, w'.x₀, w'.d⟩
  have hp₁eq : p₁ = p₁' := by
    apply OrientedPaint.ext <;> assumption
  have hp₃eq : p₃ = p₃' := by
    apply OrientedPaint.ext <;> assumption
  have hb₁ : w.b₁.auxSupport = w'.b₁.auxSupport := by
    change finsetCode (paintFiber H p₁) (hpaint p₁) _ =
      finsetCode (paintFiber H p₁') (hpaint p₁') _ at hi₁
    exact finsetCode_value_eq_of_finset_eq (hpaint p₁) (hpaint p₁')
      (congrArg (paintFiber H) hp₁eq) _ _ hi₁
  have hb₃ : w.b₃.auxSupport = w'.b₃.auxSupport := by
    change finsetCode (paintFiber H p₃) (hpaint p₃) _ =
      finsetCode (paintFiber H p₃') (hpaint p₃') _ at hi₃
    exact finsetCode_value_eq_of_finset_eq (hpaint p₃) (hpaint p₃')
      (congrArg (paintFiber H) hp₃eq) _ _ hi₃
  apply Subtype.ext
  apply Subtype.ext
  rw [w.family_eq, w'.family_eq, hb₁, ← hf, ← hf', hb₃]

/-- Charge for the case in which `f` is the predecessor of `e`. -/
def previousPairCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k)) (hef : e ≠ f)
    (Q : PositionFiber candidates R e f 2) : AdjacentPairCharge n A L := by
  classical
  let H := auxiliaryHypergraph candidates R
  let q := Q.1
  let w := pairRootedWitness candidates R e f q
  have heH : e ∈ H := pair_first_mem_host candidates R q
  have hfH : f ∈ H := pair_second_mem_host candidates R q
  have hf : f = w.b₃.auxSupport :=
    secondRootPosition_previous candidates R hef q Q.2
  let p₀ : OrientedPaint n k := ⟨w.x₀, w.x₁, w.c⟩
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  have hp₀ : p₀ ∈ paintTraces e := by
    rw [← w.root_support]
    exact mem_paintTraces_of_paints w.paint₀
  have hp₃ : p₃ ∈ paintTraces f := by
    rw [hf]
    exact mem_paintTraces_of_paints w.paint₃
  have hp₁ : w.b₁.auxSupport ∈ paintFiber H p₁ :=
    auxSupport_mem_paintFiber
      (pair_conflict_subset_host candidates R q (witness_b₁_mem candidates R q)) w.paint₁
  have hp₂ : w.b₂.auxSupport ∈ paintFiber H p₂ :=
    auxSupport_mem_paintFiber
      (pair_conflict_subset_host candidates R q (witness_b₂_mem candidates R q)) w.paint₂
  exact
    (finsetCode (paintTraces e) (htrace e heH) ⟨p₀, hp₀⟩,
      finsetCode (paintTraces f) (htrace f hfH) ⟨p₃, hp₃⟩,
      w.x₂,
      finsetCode (paintFiber H p₁) (hpaint p₁) ⟨w.b₁.auxSupport, hp₁⟩,
      finsetCode (paintFiber H p₂) (hpaint p₂) ⟨w.b₂.auxSupport, hp₂⟩)

theorem previousPairCharge_injective
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k)) (hef : e ≠ f) :
    Function.Injective (previousPairCharge candidates R A L htrace hpaint e f hef) := by
  classical
  intro Q Q' hcharge
  let H := auxiliaryHypergraph candidates R
  let q := Q.1
  let q' := Q'.1
  let w := pairRootedWitness candidates R e f q
  let w' := pairRootedWitness candidates R e f q'
  have heH : e ∈ H := pair_first_mem_host candidates R q
  have heH' : e ∈ H := pair_first_mem_host candidates R q'
  have hfH : f ∈ H := pair_second_mem_host candidates R q
  have hfH' : f ∈ H := pair_second_mem_host candidates R q'
  have hf : f = w.b₃.auxSupport :=
    secondRootPosition_previous candidates R hef q Q.2
  have hf' : f = w'.b₃.auxSupport :=
    secondRootPosition_previous candidates R hef q' Q'.2
  simp only [previousPairCharge] at hcharge
  have ht₀ := congrArg (fun z => z.1) hcharge
  have ht₃ := congrArg (fun z => z.2.1) hcharge
  have hx₂ := congrArg (fun z => z.2.2.1) hcharge
  have hi₁ := congrArg (fun z => z.2.2.2.1) hcharge
  have hi₂ := congrArg (fun z => z.2.2.2.2) hcharge
  change w.x₂ = w'.x₂ at hx₂
  change finsetCode (paintTraces e) (htrace e heH) _ =
    finsetCode (paintTraces e) (htrace e heH') _ at ht₀
  have hp₀ : (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) =
      ⟨w'.x₀, w'.x₁, w'.c⟩ :=
    congrArg Subtype.val ((finsetCode (paintTraces e) (htrace e heH)).injective ht₀)
  have hx₀ : w.x₀ = w'.x₀ := congrArg OrientedPaint.left hp₀
  have hx₁ : w.x₁ = w'.x₁ := congrArg OrientedPaint.right hp₀
  have hc : w.c = w'.c := congrArg OrientedPaint.color hp₀
  change finsetCode (paintTraces f) (htrace f hfH) _ =
    finsetCode (paintTraces f) (htrace f hfH') _ at ht₃
  have hp₃ : (⟨w.x₃, w.x₀, w.d⟩ : OrientedPaint n k) =
      ⟨w'.x₃, w'.x₀, w'.d⟩ :=
    congrArg Subtype.val ((finsetCode (paintTraces f) (htrace f hfH)).injective ht₃)
  have hx₃ : w.x₃ = w'.x₃ := congrArg OrientedPaint.left hp₃
  have hd : w.d = w'.d := congrArg OrientedPaint.color hp₃
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₁' : OrientedPaint n k := ⟨w'.x₁, w'.x₂, w'.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₂' : OrientedPaint n k := ⟨w'.x₂, w'.x₃, w'.c⟩
  have hp₁eq : p₁ = p₁' := by
    apply OrientedPaint.ext <;> assumption
  have hp₂eq : p₂ = p₂' := by
    apply OrientedPaint.ext <;> assumption
  have hb₁ : w.b₁.auxSupport = w'.b₁.auxSupport := by
    change finsetCode (paintFiber H p₁) (hpaint p₁) _ =
      finsetCode (paintFiber H p₁') (hpaint p₁') _ at hi₁
    exact finsetCode_value_eq_of_finset_eq (hpaint p₁) (hpaint p₁')
      (congrArg (paintFiber H) hp₁eq) _ _ hi₁
  have hb₂ : w.b₂.auxSupport = w'.b₂.auxSupport := by
    change finsetCode (paintFiber H p₂) (hpaint p₂) _ =
      finsetCode (paintFiber H p₂') (hpaint p₂') _ at hi₂
    exact finsetCode_value_eq_of_finset_eq (hpaint p₂) (hpaint p₂')
      (congrArg (paintFiber H) hp₂eq) _ _ hi₂
  apply Subtype.ext
  apply Subtype.ext
  rw [w.family_eq, w'.family_eq, hb₁, hb₂, ← hf, ← hf']

/-- Sharp pair-codegree estimate obtained by partitioning according to the
cyclic position of the second prescribed edge. -/
theorem alternatingCycleConflict_pair_codegree_le_local
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f : Finset (AuxVertex n k)) (hef : e ≠ f) :
    codegree (alternatingCycleConflicts candidates R) {e, f} ≤
      3 * A * A * (n + k) * L * L := by
  classical
  let D :=
    ↑(pairRootedConflicts (alternatingCycleConflicts candidates R) e f)
  let pos : D → Fin 3 := secondRootPosition candidates R e f
  have hpartition : Fintype.card D =
      ∑ i : Fin 3, Fintype.card (PositionFiber candidates R e f i) := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv pos)
    rw [Fintype.card_sigma] at h
    exact h.symm
  have h₀ : Fintype.card (PositionFiber candidates R e f 0) ≤
      A * A * n * L * L := by
    have h := Fintype.card_le_of_embedding
      (Function.Embedding.mk
        (nextPairCharge candidates R A L htrace hpaint e f)
        (nextPairCharge_injective candidates R A L htrace hpaint e f))
    simpa [AdjacentPairCharge, mul_assoc] using h
  have h₁ : Fintype.card (PositionFiber candidates R e f 1) ≤
      A * A * k * L * L := by
    have h := Fintype.card_le_of_embedding
      (Function.Embedding.mk
        (oppositePairCharge candidates R A L htrace hpaint e f)
        (oppositePairCharge_injective candidates R A L htrace hpaint e f))
    simpa [OppositePairCharge, mul_assoc] using h
  have h₂ : Fintype.card (PositionFiber candidates R e f 2) ≤
      A * A * n * L * L := by
    have h := Fintype.card_le_of_embedding
      (Function.Embedding.mk
        (previousPairCharge candidates R A L htrace hpaint e f hef)
        (previousPairCharge_injective candidates R A L htrace hpaint e f hef))
    simpa [AdjacentPairCharge, mul_assoc] using h
  rw [← pairRootedConflicts_card, ← Fintype.card_coe, hpartition]
  have hsum : (∑ i : Fin 3,
      Fintype.card (PositionFiber candidates R e f i)) =
      Fintype.card (PositionFiber candidates R e f 0) +
        Fintype.card (PositionFiber candidates R e f 1) +
        Fintype.card (PositionFiber candidates R e f 2) := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  rw [hsum]
  nlinarith

end


noncomputable def tripleRootedConflicts
    (C : ConflictSystem (AuxVertex n k))
    (e f g : Finset (AuxVertex n k)) : ConflictSystem (AuxVertex n k) :=
  by
    classical
    exact C.filter fun Q => e ∈ Q ∧ f ∈ Q ∧ g ∈ Q

@[simp] theorem tripleRootedConflicts_card
    (C : ConflictSystem (AuxVertex n k))
    (e f g : Finset (AuxVertex n k)) :
    (tripleRootedConflicts C e f g).card = codegree C {e, f, g} := by
  simp only [tripleRootedConflicts, codegree]
  congr 1
  ext Q
  simp only [Finset.mem_filter, Finset.insert_subset_iff,
    Finset.singleton_subset_iff]

inductive ThreeRootOrder where
  | one_two
  | one_three
  | two_one
  | two_three
  | three_one
  | three_two
  deriving DecidableEq

instance : Fintype ThreeRootOrder where
  elems := {.one_two, .one_three, .two_one, .two_three, .three_one, .three_two}
  complete x := by cases x <;> simp

namespace ThreeRootOrder

variable {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}

def basePaint (w : RootedAlternatingWitness e Q) : OrientedPaint n k :=
  ⟨w.x₀, w.x₁, w.c⟩

def firstSupport (w : RootedAlternatingWitness e Q) :
    ThreeRootOrder → Finset (AuxVertex n k)
  | .one_two | .one_three => w.b₁.auxSupport
  | .two_one | .two_three => w.b₂.auxSupport
  | .three_one | .three_two => w.b₃.auxSupport

def firstPaint (w : RootedAlternatingWitness e Q) :
    ThreeRootOrder → OrientedPaint n k
  | .one_two | .one_three => ⟨w.x₁, w.x₂, w.d⟩
  | .two_one | .two_three => ⟨w.x₂, w.x₃, w.c⟩
  | .three_one | .three_two => ⟨w.x₃, w.x₀, w.d⟩

def secondSupport (w : RootedAlternatingWitness e Q) :
    ThreeRootOrder → Finset (AuxVertex n k)
  | .one_two => w.b₂.auxSupport
  | .one_three => w.b₃.auxSupport
  | .two_one => w.b₁.auxSupport
  | .two_three => w.b₃.auxSupport
  | .three_one => w.b₁.auxSupport
  | .three_two => w.b₂.auxSupport

def secondPaint (w : RootedAlternatingWitness e Q) :
    ThreeRootOrder → OrientedPaint n k
  | .one_two => ⟨w.x₂, w.x₃, w.c⟩
  | .one_three => ⟨w.x₃, w.x₀, w.d⟩
  | .two_one => ⟨w.x₁, w.x₂, w.d⟩
  | .two_three => ⟨w.x₃, w.x₀, w.d⟩
  | .three_one => ⟨w.x₁, w.x₂, w.d⟩
  | .three_two => ⟨w.x₂, w.x₃, w.c⟩

def missingSupport (w : RootedAlternatingWitness e Q) :
    ThreeRootOrder → Finset (AuxVertex n k)
  | .one_two | .two_one => w.b₃.auxSupport
  | .one_three | .three_one => w.b₂.auxSupport
  | .two_three | .three_two => w.b₁.auxSupport

def missingPaint (w : RootedAlternatingWitness e Q) :
    ThreeRootOrder → OrientedPaint n k
  | .one_two | .two_one => ⟨w.x₃, w.x₀, w.d⟩
  | .one_three | .three_one => ⟨w.x₂, w.x₃, w.c⟩
  | .two_three | .three_two => ⟨w.x₁, w.x₂, w.d⟩

theorem basePaint_mem_traces (w : RootedAlternatingWitness e Q) :
    basePaint w ∈ paintTraces e := by
  have h := mem_paintTraces_of_paints w.paint₀
  simpa only [basePaint, w.root_support] using h

theorem firstPaint_mem_traces (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) : firstPaint w o ∈ paintTraces (firstSupport w o) := by
  cases o
  · exact mem_paintTraces_of_paints w.paint₁
  · exact mem_paintTraces_of_paints w.paint₁
  · exact mem_paintTraces_of_paints w.paint₂
  · exact mem_paintTraces_of_paints w.paint₂
  · exact mem_paintTraces_of_paints w.paint₃
  · exact mem_paintTraces_of_paints w.paint₃

theorem secondPaint_mem_traces (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) :
    secondPaint w o ∈ paintTraces (secondSupport w o) := by
  cases o
  · exact mem_paintTraces_of_paints w.paint₂
  · exact mem_paintTraces_of_paints w.paint₃
  · exact mem_paintTraces_of_paints w.paint₁
  · exact mem_paintTraces_of_paints w.paint₃
  · exact mem_paintTraces_of_paints w.paint₁
  · exact mem_paintTraces_of_paints w.paint₂

theorem missingPaint_paints (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) :
    ∃ b : TriangleBlock n k, b.auxSupport = missingSupport w o ∧
      b.Paints (missingPaint w o).left (missingPaint w o).right
        (missingPaint w o).color := by
  cases o
  <;> first
    | exact ⟨w.b₃, rfl, w.paint₃⟩
    | exact ⟨w.b₂, rfl, w.paint₂⟩
    | exact ⟨w.b₁, rfl, w.paint₁⟩

theorem firstSupport_mem_family (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) : firstSupport w o ∈ Q := by
  have h := congrArg (fun T => firstSupport w o ∈ T) w.family_eq
  cases o <;> simpa [firstSupport] using h

theorem secondSupport_mem_family (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) : secondSupport w o ∈ Q := by
  have h := congrArg (fun T => secondSupport w o ∈ T) w.family_eq
  cases o <;> simpa [secondSupport] using h

theorem missingSupport_mem_family (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) : missingSupport w o ∈ Q := by
  have h := congrArg (fun T => missingSupport w o ∈ T) w.family_eq
  cases o <;> simpa [missingSupport] using h

theorem family_eq_ordered (w : RootedAlternatingWitness e Q)
    (o : ThreeRootOrder) :
    Q = {e, firstSupport w o, secondSupport w o, missingSupport w o} := by
  calc
    Q = {e, w.b₁.auxSupport, w.b₂.auxSupport, w.b₃.auxSupport} := w.family_eq
    _ = {e, firstSupport w o, secondSupport w o, missingSupport w o} := by
      cases o <;> ext z <;>
        simp only [firstSupport, secondSupport, missingSupport,
          Finset.mem_insert, Finset.mem_singleton] <;> aesop

end ThreeRootOrder

structure IsThreeRootOrder
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q)
    (f g : Finset (AuxVertex n k)) (o : ThreeRootOrder) : Prop where
  first_eq : ThreeRootOrder.firstSupport w o = f
  second_eq : ThreeRootOrder.secondSupport w o = g

theorem exists_threeRootOrder
    {e f g : Finset (AuxVertex n k)}
    {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q)
    (hfQ : f ∈ Q) (hgQ : g ∈ Q)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∃ o, IsThreeRootOrder w f g o := by
  have hf' : f ∈ ({e, w.b₁.auxSupport, w.b₂.auxSupport,
      w.b₃.auxSupport} : Hypergraph (AuxVertex n k)) := by rwa [← w.family_eq]
  have hg' : g ∈ ({e, w.b₁.auxSupport, w.b₂.auxSupport,
      w.b₃.auxSupport} : Hypergraph (AuxVertex n k)) := by rwa [← w.family_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf' hg'
  rcases hf' with hfe | hf₁ | hf₂ | hf₃
  · exact (hef hfe.symm).elim
  · rcases hg' with hge | hg₁ | hg₂ | hg₃
    · exact (heg hge.symm).elim
    · exact (hfg (hf₁.trans hg₁.symm)).elim
    · exact ⟨.one_two, ⟨hf₁.symm, hg₂.symm⟩⟩
    · exact ⟨.one_three, ⟨hf₁.symm, hg₃.symm⟩⟩
  · rcases hg' with hge | hg₁ | hg₂ | hg₃
    · exact (heg hge.symm).elim
    · exact ⟨.two_one, ⟨hf₂.symm, hg₁.symm⟩⟩
    · exact (hfg (hf₂.trans hg₂.symm)).elim
    · exact ⟨.two_three, ⟨hf₂.symm, hg₃.symm⟩⟩
  · rcases hg' with hge | hg₁ | hg₂ | hg₃
    · exact (heg hge.symm).elim
    · exact ⟨.three_one, ⟨hf₃.symm, hg₁.symm⟩⟩
    · exact ⟨.three_two, ⟨hf₃.symm, hg₂.symm⟩⟩
    · exact (hfg (hf₃.trans hg₃.symm)).elim

noncomputable def chosenThreeRootOrder
    {e f g : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) (hfQ : f ∈ Q) (hgQ : g ∈ Q)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : ThreeRootOrder :=
  Classical.choose (exists_threeRootOrder w hfQ hgQ hef heg hfg)

theorem chosenThreeRootOrder_spec
    {e f g : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) (hfQ : f ∈ Q) (hgQ : g ∈ Q)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    IsThreeRootOrder w f g
      (chosenThreeRootOrder w hfQ hgQ hef heg hfg) :=
  Classical.choose_spec (exists_threeRootOrder w hfQ hgQ hef heg hfg)

abbrev ThreeRootCharge (A L : ℕ) :=
  ThreeRootOrder × Fin A × Fin A × Fin A × Fin L

@[simp] theorem card_threeRootOrder : Fintype.card ThreeRootOrder = 6 := by
  decide

def tripleRootAsRooted
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f g : Finset (AuxVertex n k))
    (Q : ↑(tripleRootedConflicts
      (alternatingCycleConflicts candidates R) e f g)) :
    ↑(rootedConflicts (alternatingCycleConflicts candidates R) e) := by
  classical
  refine ⟨Q.1, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp Q.2).1, ?_⟩⟩
  exact (Finset.mem_filter.mp Q.2).2.1

noncomputable def tripleRootWitness
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f g : Finset (AuxVertex n k))
    (Q : ↑(tripleRootedConflicts
      (alternatingCycleConflicts candidates R) e f g)) :
    RootedAlternatingWitness e Q.1 :=
  rootedConflictWitness candidates R e
    (tripleRootAsRooted candidates R e f g Q)

noncomputable def tripleRootOrder
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f g : Finset (AuxVertex n k))
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (Q : ↑(tripleRootedConflicts
      (alternatingCycleConflicts candidates R) e f g)) : ThreeRootOrder :=
  by
    classical
    exact chosenThreeRootOrder (tripleRootWitness candidates R e f g Q)
      (Finset.mem_filter.mp Q.2).2.2.1
      (Finset.mem_filter.mp Q.2).2.2.2 hef heg hfg

theorem tripleRootOrder_spec
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f g : Finset (AuxVertex n k))
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (Q : ↑(tripleRootedConflicts
      (alternatingCycleConflicts candidates R) e f g)) :
    IsThreeRootOrder (tripleRootWitness candidates R e f g Q) f g
      (tripleRootOrder candidates R e f g hef heg hfg Q) :=
  by
    classical
    exact chosenThreeRootOrder_spec (tripleRootWitness candidates R e f g Q)
      (Finset.mem_filter.mp Q.2).2.2.1
      (Finset.mem_filter.mp Q.2).2.2.2 hef heg hfg

noncomputable def threeRootCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ)
    (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f g : Finset (AuxVertex n k))
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (Q : ↑(tripleRootedConflicts
      (alternatingCycleConflicts candidates R) e f g)) :
    ThreeRootCharge A L := by
  classical
  let H := auxiliaryHypergraph candidates R
  let w := tripleRootWitness candidates R e f g Q
  let o := tripleRootOrder candidates R e f g hef heg hfg Q
  have hQconf : Q.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q.2).1
  have hQH : Q.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q.1 hQconf
  have heH : e ∈ H := hQH (Finset.mem_filter.mp Q.2).2.1
  have hfirstH : ThreeRootOrder.firstSupport w o ∈ H :=
    hQH (ThreeRootOrder.firstSupport_mem_family w o)
  have hsecondH : ThreeRootOrder.secondSupport w o ∈ H :=
    hQH (ThreeRootOrder.secondSupport_mem_family w o)
  have hmissingH : ThreeRootOrder.missingSupport w o ∈ H :=
    hQH (ThreeRootOrder.missingSupport_mem_family w o)
  have hmissingFiber : ThreeRootOrder.missingSupport w o ∈
      paintFiber H (ThreeRootOrder.missingPaint w o) := by
    obtain ⟨b, hb, hp⟩ := ThreeRootOrder.missingPaint_paints w o
    have hbH : b.auxSupport ∈ H := by simpa only [hb] using hmissingH
    have h := auxSupport_mem_paintFiber hbH hp
    simpa only [hb] using h
  exact
    (o,
      finsetCode (paintTraces e) (htrace e heH)
        ⟨ThreeRootOrder.basePaint w,
          ThreeRootOrder.basePaint_mem_traces w⟩,
      finsetCode (paintTraces (ThreeRootOrder.firstSupport w o))
        (htrace _ hfirstH)
        ⟨ThreeRootOrder.firstPaint w o,
          ThreeRootOrder.firstPaint_mem_traces w o⟩,
      finsetCode (paintTraces (ThreeRootOrder.secondSupport w o))
        (htrace _ hsecondH)
        ⟨ThreeRootOrder.secondPaint w o,
          ThreeRootOrder.secondPaint_mem_traces w o⟩,
      finsetCode (paintFiber H (ThreeRootOrder.missingPaint w o))
        (hpaint _)
        ⟨ThreeRootOrder.missingSupport w o, hmissingFiber⟩)

theorem ThreeRootOrder.missingPaint_eq
    {e e' : Finset (AuxVertex n k)}
    {Q Q' : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q)
    (w' : RootedAlternatingWitness e' Q') (o : ThreeRootOrder)
    (hbase : ThreeRootOrder.basePaint w = ThreeRootOrder.basePaint w')
    (hfirst : ThreeRootOrder.firstPaint w o =
      ThreeRootOrder.firstPaint w' o)
    (hsecond : ThreeRootOrder.secondPaint w o =
      ThreeRootOrder.secondPaint w' o) :
    ThreeRootOrder.missingPaint w o =
      ThreeRootOrder.missingPaint w' o := by
  cases o
  · apply OrientedPaint.ext
    · simpa [missingPaint, secondPaint] using congrArg OrientedPaint.right hsecond
    · simpa [missingPaint, basePaint] using congrArg OrientedPaint.left hbase
    · simpa [missingPaint, firstPaint] using congrArg OrientedPaint.color hfirst
  · apply OrientedPaint.ext
    · simpa [missingPaint, firstPaint] using congrArg OrientedPaint.right hfirst
    · simpa [missingPaint, secondPaint] using congrArg OrientedPaint.left hsecond
    · simpa [missingPaint, basePaint] using congrArg OrientedPaint.color hbase
  · apply OrientedPaint.ext
    · simpa [missingPaint, firstPaint] using congrArg OrientedPaint.right hfirst
    · simpa [missingPaint, basePaint] using congrArg OrientedPaint.left hbase
    · simpa [missingPaint, secondPaint] using congrArg OrientedPaint.color hsecond
  · apply OrientedPaint.ext
    · simpa [missingPaint, basePaint] using congrArg OrientedPaint.right hbase
    · simpa [missingPaint, firstPaint] using congrArg OrientedPaint.left hfirst
    · simpa [missingPaint, secondPaint] using congrArg OrientedPaint.color hsecond
  · apply OrientedPaint.ext
    · simpa [missingPaint, secondPaint] using congrArg OrientedPaint.right hsecond
    · simpa [missingPaint, firstPaint] using congrArg OrientedPaint.left hfirst
    · simpa [missingPaint, basePaint] using congrArg OrientedPaint.color hbase
  · apply OrientedPaint.ext
    · simpa [missingPaint, basePaint] using congrArg OrientedPaint.right hbase
    · simpa [missingPaint, secondPaint] using congrArg OrientedPaint.left hsecond
    · simpa [missingPaint, firstPaint] using congrArg OrientedPaint.color hfirst

theorem ThreeRootOrder.missingPaint_eq_of_order_eq
    {e e' : Finset (AuxVertex n k)}
    {Q Q' : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q)
    (w' : RootedAlternatingWitness e' Q') {o o' : ThreeRootOrder}
    (ho : o = o')
    (hbase : ThreeRootOrder.basePaint w = ThreeRootOrder.basePaint w')
    (hfirst : ThreeRootOrder.firstPaint w o =
      ThreeRootOrder.firstPaint w' o')
    (hsecond : ThreeRootOrder.secondPaint w o =
      ThreeRootOrder.secondPaint w' o') :
    ThreeRootOrder.missingPaint w o =
      ThreeRootOrder.missingPaint w' o' := by
  subst o'
  exact ThreeRootOrder.missingPaint_eq w w' o hbase hfirst hsecond

theorem threeRootCharge_injective
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ)
    (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f g : Finset (AuxVertex n k))
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Function.Injective
      (threeRootCharge candidates R A L htrace hpaint e f g hef heg hfg) := by
  classical
  intro Q Q' hcharge
  let H := auxiliaryHypergraph candidates R
  let w := tripleRootWitness candidates R e f g Q
  let w' := tripleRootWitness candidates R e f g Q'
  let o := tripleRootOrder candidates R e f g hef heg hfg Q
  let o' := tripleRootOrder candidates R e f g hef heg hfg Q'
  have hQconf : Q.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q.2).1
  have hQconf' : Q'.1 ∈ alternatingCycleConflicts candidates R :=
    (Finset.mem_filter.mp Q'.2).1
  have hQH : Q.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q.1 hQconf
  have hQH' : Q'.1 ⊆ H :=
    alternatingCycleConflicts_isConflictSystem candidates R Q'.1 hQconf'
  have heH : e ∈ H := hQH (Finset.mem_filter.mp Q.2).2.1
  have heH' : e ∈ H := hQH' (Finset.mem_filter.mp Q'.2).2.1
  have hfirstH : ThreeRootOrder.firstSupport w o ∈ H :=
    hQH (ThreeRootOrder.firstSupport_mem_family w o)
  have hfirstH' : ThreeRootOrder.firstSupport w' o' ∈ H :=
    hQH' (ThreeRootOrder.firstSupport_mem_family w' o')
  have hsecondH : ThreeRootOrder.secondSupport w o ∈ H :=
    hQH (ThreeRootOrder.secondSupport_mem_family w o)
  have hsecondH' : ThreeRootOrder.secondSupport w' o' ∈ H :=
    hQH' (ThreeRootOrder.secondSupport_mem_family w' o')
  have hmissingH : ThreeRootOrder.missingSupport w o ∈ H :=
    hQH (ThreeRootOrder.missingSupport_mem_family w o)
  have hmissingH' : ThreeRootOrder.missingSupport w' o' ∈ H :=
    hQH' (ThreeRootOrder.missingSupport_mem_family w' o')
  have hmissingFiber : ThreeRootOrder.missingSupport w o ∈
      paintFiber H (ThreeRootOrder.missingPaint w o) := by
    obtain ⟨b, hb, hp⟩ := ThreeRootOrder.missingPaint_paints w o
    have hbH : b.auxSupport ∈ H := by simpa only [hb] using hmissingH
    have h := auxSupport_mem_paintFiber hbH hp
    simpa only [hb] using h
  have hmissingFiber' : ThreeRootOrder.missingSupport w' o' ∈
      paintFiber H (ThreeRootOrder.missingPaint w' o') := by
    obtain ⟨b, hb, hp⟩ := ThreeRootOrder.missingPaint_paints w' o'
    have hbH : b.auxSupport ∈ H := by simpa only [hb] using hmissingH'
    have h := auxSupport_mem_paintFiber hbH hp
    simpa only [hb] using h
  have horder : IsThreeRootOrder w f g o :=
    tripleRootOrder_spec candidates R e f g hef heg hfg Q
  have horder' : IsThreeRootOrder w' f g o' :=
    tripleRootOrder_spec candidates R e f g hef heg hfg Q'
  have ho := congrArg (fun z => z.1) hcharge
  have hi₀ := congrArg (fun z => z.2.1) hcharge
  have hi₁ := congrArg (fun z => z.2.2.1) hcharge
  have hi₂ := congrArg (fun z => z.2.2.2.1) hcharge
  have hi₃ := congrArg (fun z => z.2.2.2.2) hcharge
  change o = o' at ho
  have hfirstSupport : ThreeRootOrder.firstSupport w o =
      ThreeRootOrder.firstSupport w' o' :=
    horder.first_eq.trans horder'.first_eq.symm
  have hsecondSupport : ThreeRootOrder.secondSupport w o =
      ThreeRootOrder.secondSupport w' o' :=
    horder.second_eq.trans horder'.second_eq.symm
  have hbase : ThreeRootOrder.basePaint w =
      ThreeRootOrder.basePaint w' := by
    exact finsetCode_value_eq_of_finset_eq
      (htrace e heH) (htrace e heH') rfl
      ⟨ThreeRootOrder.basePaint w, ThreeRootOrder.basePaint_mem_traces w⟩
      ⟨ThreeRootOrder.basePaint w', ThreeRootOrder.basePaint_mem_traces w'⟩
      (by simpa only [threeRootCharge] using hi₀)
  have hfirst : ThreeRootOrder.firstPaint w o =
      ThreeRootOrder.firstPaint w' o' := by
    exact finsetCode_value_eq_of_finset_eq
      (htrace _ hfirstH) (htrace _ hfirstH')
      (congrArg paintTraces hfirstSupport)
      ⟨ThreeRootOrder.firstPaint w o,
        ThreeRootOrder.firstPaint_mem_traces w o⟩
      ⟨ThreeRootOrder.firstPaint w' o',
        ThreeRootOrder.firstPaint_mem_traces w' o'⟩
      (by simpa only [threeRootCharge] using hi₁)
  have hsecond : ThreeRootOrder.secondPaint w o =
      ThreeRootOrder.secondPaint w' o' := by
    exact finsetCode_value_eq_of_finset_eq
      (htrace _ hsecondH) (htrace _ hsecondH')
      (congrArg paintTraces hsecondSupport)
      ⟨ThreeRootOrder.secondPaint w o,
        ThreeRootOrder.secondPaint_mem_traces w o⟩
      ⟨ThreeRootOrder.secondPaint w' o',
        ThreeRootOrder.secondPaint_mem_traces w' o'⟩
      (by simpa only [threeRootCharge] using hi₂)
  have hmissingPaint : ThreeRootOrder.missingPaint w o =
      ThreeRootOrder.missingPaint w' o' :=
    ThreeRootOrder.missingPaint_eq_of_order_eq w w' ho hbase hfirst hsecond
  have hmissingSupport : ThreeRootOrder.missingSupport w o =
      ThreeRootOrder.missingSupport w' o' := by
    exact finsetCode_value_eq_of_finset_eq
      (hpaint (ThreeRootOrder.missingPaint w o))
      (hpaint (ThreeRootOrder.missingPaint w' o'))
      (congrArg (paintFiber H) hmissingPaint)
      ⟨ThreeRootOrder.missingSupport w o, hmissingFiber⟩
      ⟨ThreeRootOrder.missingSupport w' o', hmissingFiber'⟩
      (by simpa only [threeRootCharge] using hi₃)
  apply Subtype.ext
  calc
    Q.1 = {e, ThreeRootOrder.firstSupport w o,
        ThreeRootOrder.secondSupport w o,
        ThreeRootOrder.missingSupport w o} :=
      ThreeRootOrder.family_eq_ordered w o
    _ = {e, f, g, ThreeRootOrder.missingSupport w o} := by
      rw [horder.first_eq, horder.second_eq]
    _ = {e, f, g, ThreeRootOrder.missingSupport w' o'} := by
      rw [hmissingSupport]
    _ = {e, ThreeRootOrder.firstSupport w' o',
        ThreeRootOrder.secondSupport w' o',
        ThreeRootOrder.missingSupport w' o'} := by
      rw [horder'.first_eq, horder'.second_eq]
    _ = Q'.1 := (ThreeRootOrder.family_eq_ordered w' o').symm

theorem alternatingCycleConflict_triple_codegree_le_local
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ)
    (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (e f g : Finset (AuxVertex n k))
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    codegree (alternatingCycleConflicts candidates R) {e, f, g} ≤
      6 * A ^ 3 * L := by
  rw [← tripleRootedConflicts_card, ← Fintype.card_coe]
  have hcard := Fintype.card_le_of_embedding
    (Function.Embedding.mk
      (threeRootCharge candidates R A L htrace hpaint e f g hef heg hfg)
      (threeRootCharge_injective candidates R A L htrace hpaint e f g
        hef heg hfg))
  simpa [ThreeRootCharge, pow_succ, mul_assoc] using hcard


@[simp] theorem conflictLayer_alternatingCycleConflicts_four
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k) :
    conflictLayer (alternatingCycleConflicts candidates R) 4 =
      alternatingCycleConflicts candidates R := by
  classical
  ext Q
  simp only [mem_conflictLayer]
  constructor
  · exact And.left
  · intro hQ
    exact ⟨hQ, alternatingCycleConflicts_uniform candidates R hQ⟩

theorem conflictLayer_alternatingCycleConflicts_eq_empty
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {j : ℕ} (hj : j ≠ 4) :
    conflictLayer (alternatingCycleConflicts candidates R) j = ∅ := by
  classical
  ext Q
  constructor
  · intro hQ
    have hjQ := (mem_conflictLayer.mp hQ).2
    have h4Q := alternatingCycleConflicts_uniform candidates R
      (mem_conflictLayer.mp hQ).1
    exact (hj (hjQ.symm.trans h4Q)).elim
  · simp

/-- Explicit maximum conflict-degree count obtained by fixing one auxiliary
edge and choosing the other three members of the conflict. -/
theorem alternatingCycleConflict_degree_le_choose_three
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e : Finset (AuxVertex n k)) :
    degree (alternatingCycleConflicts candidates R) e ≤
      Nat.choose (auxiliaryHypergraph candidates R).card 3 := by
  classical
  simpa using degree_le_choose_of_uniform
    (alternatingCycleConflicts_isConflictSystem candidates R)
    (fun Q hQ => alternatingCycleConflicts_uniform candidates R hQ) e

/-- Explicit pair-codegree count: after prescribing two auxiliary edges,
only two further host edges remain to be selected. -/
theorem alternatingCycleConflict_pair_codegree_le_choose_two
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (s : Hypergraph (AuxVertex n k)) (hs : s.card = 2) :
    codegree (alternatingCycleConflicts candidates R) s ≤
      Nat.choose (auxiliaryHypergraph candidates R).card 2 := by
  classical
  have h := codegree_le_choose_of_uniform
    (alternatingCycleConflicts_isConflictSystem candidates R)
    (fun Q hQ => alternatingCycleConflicts_uniform candidates R hQ) s
  simpa [hs] using h

/-- Explicit triple-codegree count: a prescribed triple has at most one
freely chosen host edge left. -/
theorem alternatingCycleConflict_triple_codegree_le_card
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (s : Hypergraph (AuxVertex n k)) (hs : s.card = 3) :
    codegree (alternatingCycleConflicts candidates R) s ≤
      (auxiliaryHypergraph candidates R).card := by
  classical
  have h := codegree_le_choose_of_uniform
    (alternatingCycleConflicts_isConflictSystem candidates R)
    (fun Q hQ => alternatingCycleConflicts_uniform candidates R hQ) s
  simpa [hs] using h

/-! ### Sharp codegrees for arbitrary roots -/

/-- The position-wise two-root charge, restated for an arbitrary root of
cardinality two. -/
theorem alternatingCycleConflict_pair_codegree_le_local_set
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (s : Hypergraph (AuxVertex n k)) (hs : s.card = 2) :
    codegree (alternatingCycleConflicts candidates R) s ≤
      3 * A * A * (n + k) * L * L := by
  obtain ⟨e, f, hef, rfl⟩ := s.card_eq_two.mp hs
  exact alternatingCycleConflict_pair_codegree_le_local
    candidates R A L htrace hpaint e f hef

/-- In the concrete auxiliary host, 8-uniformity bounds each root trace by
`512`, while a host pair-codegree bound controls every paint fibre. -/
theorem alternatingCycleConflict_pair_codegree_le_of_maxCodegree
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (L : ℕ)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (s : Hypergraph (AuxVertex n k)) (hs : s.card = 2) :
    codegree (alternatingCycleConflicts candidates R) s ≤
      3 * 512 * 512 * (n + k) * L * L := by
  apply alternatingCycleConflict_pair_codegree_le_local_set
    candidates R 512 L
  · intro e he
    exact paintTraces_card_le_512
      (fun a ha => auxiliaryHypergraph_uniform candidates R ha) he
  · exact paintFiber_card_le_of_maxCodegree hcodeg
  · exact hs

/-- The six possible cyclic orders of three roots, restated for an arbitrary
root of cardinality three. -/
theorem alternatingCycleConflict_triple_codegree_le_local_set
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (A L : ℕ) (htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ A)
    (hpaint : ∀ p, (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (s : Hypergraph (AuxVertex n k)) (hs : s.card = 3) :
    codegree (alternatingCycleConflicts candidates R) s ≤
      6 * A ^ 3 * L := by
  obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := s.card_eq_three.mp hs
  exact alternatingCycleConflict_triple_codegree_le_local
    candidates R A L htrace hpaint e f g hef heg hfg

/-- Concrete three-root conflict-codegree bound from the host pair-codegree. -/
theorem alternatingCycleConflict_triple_codegree_le_of_maxCodegree
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (L : ℕ)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (s : Hypergraph (AuxVertex n k)) (hs : s.card = 3) :
    codegree (alternatingCycleConflicts candidates R) s ≤
      6 * 512 ^ 3 * L := by
  apply alternatingCycleConflict_triple_codegree_le_local_set
    candidates R 512 L
  · intro e he
    exact paintTraces_card_le_512
      (fun a ha => auxiliaryHypergraph_uniform candidates R ha) he
  · exact paintFiber_card_le_of_maxCodegree hcodeg
  · exact hs

/-! ## Adapter to `IsBounded` and to (P3) -/

/-- For a four-uniform conflict system, the only nonempty layer in
`IsBounded` is layer four.  Thus explicit degree, pair-codegree, and
triple-codegree estimates suffice. -/
theorem alternatingCycleConflicts_isBounded_of_counts
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (d eta : ℝ) (ell : ℕ) (hd : 0 ≤ d) (hell : 4 ≤ ell)
    (hdegree : ∀ e,
      (degree (alternatingCycleConflicts candidates R) e : ℝ) ≤
        (ell : ℝ) * Real.rpow d 3)
    (hpair : ∀ s, s.card = 2 →
      (codegree (alternatingCycleConflicts candidates R) s : ℝ) ≤
        Real.rpow d (2 - eta))
    (htriple : ∀ s, s.card = 3 →
      (codegree (alternatingCycleConflicts candidates R) s : ℝ) ≤
        Real.rpow d (1 - eta)) :
    IsBounded (alternatingCycleConflicts candidates R) d ell eta := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    rw [alternatingCycleConflicts_uniform candidates R hQ]
    exact ⟨by omega, hell⟩
  · intro j hj3 hjell e
    by_cases hj : j = 4
    · subst j
      rw [conflictLayer_alternatingCycleConflicts_four]
      convert hdegree e using 1
      all_goals norm_num
    · rw [conflictLayer_alternatingCycleConflicts_eq_empty candidates R hj,
        degree_empty]
      norm_num only [Nat.cast_zero]
      apply mul_nonneg (Nat.cast_nonneg ell)
      rw [Real.rpow_eq_pow]
      exact Real.rpow_nonneg hd ((j : ℝ) - 1)
  · intro j hj3 hjell j' hj'2 hj'j s hs
    by_cases hj : j = 4
    · subst j
      rw [conflictLayer_alternatingCycleConflicts_four]
      interval_cases j'
      · convert hpair s hs using 1
        all_goals norm_num
      · convert htriple s hs using 1
        all_goals norm_num
    · rw [conflictLayer_alternatingCycleConflicts_eq_empty candidates R hj,
        codegree_empty_family]
      norm_num only [Nat.cast_zero]
      rw [Real.rpow_eq_pow]
      exact Real.rpow_nonneg hd ((j : ℝ) - (j' : ℝ) - eta)

/-- The concrete sharp-count adapter used in `IsSpecializedCFMInstance`.
The three displayed numerical hypotheses are exactly the comparisons needed
to turn the local host pair-codegree `L` into the conflict bounds
`Δ₁ = O(n²kL³)`, `Δ₂ = O((n+k)L²)`, and `Δ₃ = O(L)`. -/
theorem alternatingCycleConflicts_isBounded_of_maxCodegree
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (d eta : ℝ) (ell L : ℕ) (hd : 0 ≤ d) (hell : 4 ≤ ell)
    (hcodeg : MaxCodegreeLE (auxiliaryHypergraph candidates R) 2 L)
    (hdegree : ((512 * n * n * k * L * L * L : ℕ) : ℝ) ≤
      (ell : ℝ) * Real.rpow d 3)
    (hpair : ((3 * 512 * 512 * (n + k) * L * L : ℕ) : ℝ) ≤
      Real.rpow d (2 - eta))
    (htriple : ((6 * 512 ^ 3 * L : ℕ) : ℝ) ≤
      Real.rpow d (1 - eta)) :
    IsBounded (alternatingCycleConflicts candidates R) d ell eta := by
  apply alternatingCycleConflicts_isBounded_of_counts
    candidates R d eta ell hd hell
  · intro e
    calc
      (degree (alternatingCycleConflicts candidates R) e : ℝ) ≤
          ((512 * n * n * k * L * L * L : ℕ) : ℝ) := by
        exact_mod_cast
          alternatingCycleConflict_degree_le_of_maxCodegree
            candidates R L hcodeg e
      _ ≤ (ell : ℝ) * Real.rpow d 3 := hdegree
  · intro s hs
    calc
      (codegree (alternatingCycleConflicts candidates R) s : ℝ) ≤
          ((3 * 512 * 512 * (n + k) * L * L : ℕ) : ℝ) := by
        exact_mod_cast
          alternatingCycleConflict_pair_codegree_le_of_maxCodegree
            candidates R L hcodeg s hs
      _ ≤ Real.rpow d (2 - eta) := hpair
  · intro s hs
    calc
      (codegree (alternatingCycleConflicts candidates R) s : ℝ) ≤
          ((6 * 512 ^ 3 * L : ℕ) : ℝ) := by
        exact_mod_cast
          alternatingCycleConflict_triple_codegree_le_of_maxCodegree
            candidates R L hcodeg s hs
      _ ≤ Real.rpow d (1 - eta) := htriple

/-- Sharp-count adapter from the local same-colour paint-fibre estimate.

The retained auxiliary host has two genuinely different pair-codegree
scales.  Its ambient maximum pair-codegree is only `O(n^2)`, whereas the
paint fibres occurring in alternating-cycle conflicts enjoy the smaller
retention-dependent bound.  This theorem lets the conflict calculation use
that local bound directly, without incorrectly asserting the same estimate
for every auxiliary-vertex pair. -/
theorem alternatingCycleConflicts_isBounded_of_paintFiber
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (d eta : ℝ) (ell L : ℕ) (hd : 0 ≤ d) (hell : 4 ≤ ell)
    (hpaint : ∀ p,
      (paintFiber (auxiliaryHypergraph candidates R) p).card ≤ L)
    (hdegree : ((512 * n * n * k * L * L * L : ℕ) : ℝ) ≤
      (ell : ℝ) * Real.rpow d 3)
    (hpair : ((3 * 512 * 512 * (n + k) * L * L : ℕ) : ℝ) ≤
      Real.rpow d (2 - eta))
    (htriple : ((6 * 512 ^ 3 * L : ℕ) : ℝ) ≤
      Real.rpow d (1 - eta)) :
    IsBounded (alternatingCycleConflicts candidates R) d ell eta := by
  have htrace : ∀ e ∈ auxiliaryHypergraph candidates R,
      (paintTraces e).card ≤ 512 := by
    intro e he
    exact paintTraces_card_le_512
      (fun a ha => auxiliaryHypergraph_uniform candidates R ha) he
  apply alternatingCycleConflicts_isBounded_of_counts
    candidates R d eta ell hd hell
  · intro e
    calc
      (degree (alternatingCycleConflicts candidates R) e : ℝ) ≤
          ((512 * n * n * k * L * L * L : ℕ) : ℝ) := by
        exact_mod_cast alternatingCycleConflict_degree_le_local
          candidates R 512 L htrace hpaint e
      _ ≤ (ell : ℝ) * Real.rpow d 3 := hdegree
  · intro s hs
    calc
      (codegree (alternatingCycleConflicts candidates R) s : ℝ) ≤
          ((3 * 512 * 512 * (n + k) * L * L : ℕ) : ℝ) := by
        exact_mod_cast alternatingCycleConflict_pair_codegree_le_local_set
          candidates R 512 L htrace hpaint s hs
      _ ≤ Real.rpow d (2 - eta) := hpair
  · intro s hs
    calc
      (codegree (alternatingCycleConflicts candidates R) s : ℝ) ≤
          ((6 * 512 ^ 3 * L : ℕ) : ℝ) := by
        exact_mod_cast alternatingCycleConflict_triple_codegree_le_local_set
          candidates R 512 L htrace hpaint s hs
      _ ≤ Real.rpow d (1 - eta) := htriple

/-- Direct adapter from conflict-freeness of the explicit alternating-cycle
system to property (P3) of the induced partial colouring.  This restates the
semantic endpoint next to the numerical conflict estimates. -/
theorem alternatingCycleConflictFree_implies_P3
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (MH : Hypergraph (AuxVertex n k))
    (hmatch : IsMatching (auxiliaryHypergraph candidates R) MH)
    (hfree : ConflictFree (alternatingCycleConflicts candidates R) MH) :
    let BM := blocksOfAuxFamily candidates R MH hmatch.1
    OldFourCyclesUseThree (inducedColor BM) :=
  matching_oldFourCyclesUseThree candidates R MH hmatch hfree

/-! ## Deterministic common-three-link counting -/

attribute [local instance] Classical.propDecidable

noncomputable section

variable {n k : ℕ}

/-- The three underlying graph vertices of a triangle block. -/
def blockVertices (b : TriangleBlock n k) : Finset (Fin n) :=
  {b.apex, b.left, b.right}

@[simp] theorem apex_mem_blockVertices (b : TriangleBlock n k) :
    b.apex ∈ blockVertices b := by simp [blockVertices]

@[simp] theorem left_mem_blockVertices (b : TriangleBlock n k) :
    b.left ∈ blockVertices b := by simp [blockVertices]

@[simp] theorem right_mem_blockVertices (b : TriangleBlock n k) :
    b.right ∈ blockVertices b := by simp [blockVertices]

theorem left_mem_blockVertices_of_paints {b : TriangleBlock n k}
    {x y : Fin n} {c : Fin k} (h : b.Paints x y c) :
    x ∈ blockVertices b := by
  rcases h with (⟨h, -⟩ | ⟨h, -⟩)
  · rcases h with h | h <;> rw [Sym2.eq_iff] at h <;>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [blockVertices]
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [blockVertices]

theorem right_mem_blockVertices_of_paints {b : TriangleBlock n k}
    {x y : Fin n} {c : Fin k} (h : b.Paints x y c) :
    y ∈ blockVertices b :=
  left_mem_blockVertices_of_paints (b.paints_symm h)

/-- Once a painted edge is fixed, there is a unique third triangle vertex. -/
def IsPaintThird (b : TriangleBlock n k) (x y z : Fin n) : Prop :=
  z ≠ x ∧ z ≠ y ∧ blockVertices b = {x, y, z}

theorem isPaintThird_unique {b : TriangleBlock n k} {x y z z' : Fin n}
    (h : IsPaintThird b x y z) (h' : IsPaintThird b x y z') : z' = z := by
  have hz : z ∈ ({x, y, z'} : Finset (Fin n)) := by
    rw [← h'.2.2, h.2.2]
    simp
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with hz | hz | hz
  · exact (h.1 hz).elim
  · exact (h.2.1 hz).elim
  · exact hz.symm

theorem existsUnique_isPaintThird {b : TriangleBlock n k}
    {x y : Fin n} {c : Fin k} (h : b.Paints x y c) :
    ∃! z, IsPaintThird b x y z := by
  have hxy := b.paints_ne h
  rcases h with (⟨h, -⟩ | ⟨h, -⟩)
  · rcases h with h | h <;> rw [Sym2.eq_iff] at h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨b.right, ?_, ?_⟩
        · exact ⟨b.apex_ne_right.symm, b.left_ne_right.symm, by
            ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩
        · intro z hz
          exact isPaintThird_unique
            ⟨b.apex_ne_right.symm, b.left_ne_right.symm, by
              ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩ hz
      · refine ⟨b.right, ?_, ?_⟩
        · exact ⟨b.left_ne_right.symm, b.apex_ne_right.symm, by
            ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩
        · intro z hz
          exact isPaintThird_unique
            ⟨b.left_ne_right.symm, b.apex_ne_right.symm, by
              ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩ hz
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨b.left, ?_, ?_⟩
        · exact ⟨b.apex_ne_left.symm, b.left_ne_right, by
            ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩
        · intro z hz
          exact isPaintThird_unique
            ⟨b.apex_ne_left.symm, b.left_ne_right, by
              ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩ hz
      · refine ⟨b.left, ?_, ?_⟩
        · exact ⟨b.left_ne_right, b.apex_ne_left.symm, by
            ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩
        · intro z hz
          exact isPaintThird_unique
            ⟨b.left_ne_right, b.apex_ne_left.symm, by
              ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩ hz
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨b.apex, ?_, ?_⟩
      · exact ⟨b.apex_ne_left, b.apex_ne_right, by
          ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩
      · intro z hz
        exact isPaintThird_unique
          ⟨b.apex_ne_left, b.apex_ne_right, by
            ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩ hz
    · refine ⟨b.apex, ?_, ?_⟩
      · exact ⟨b.apex_ne_right, b.apex_ne_left, by
          ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩
      · intro z hz
        exact isPaintThird_unique
          ⟨b.apex_ne_right, b.apex_ne_left, by
            ext z; simp [blockVertices, or_assoc, or_left_comm, or_comm]⟩ hz

/-- A proof-independent canonical third vertex. -/
noncomputable def paintThird (b : TriangleBlock n k) (x y : Fin n)
    (c : Fin k) (h : b.Paints x y c) : Fin n :=
  Classical.choose (existsUnique_isPaintThird h)

theorem paintThird_spec (b : TriangleBlock n k) (x y : Fin n)
    (c : Fin k) (h : b.Paints x y c) :
    IsPaintThird b x y (paintThird b x y c h) :=
  (Classical.choose_spec (existsUnique_isPaintThird h)).1

/-- Blocks painting one fixed oriented edge. -/
abbrev PaintedBlock (p : OrientedPaint n k) :=
  {b : TriangleBlock n k // b.Paints p.left p.right p.color}

/-- Which of `left`, `right`, and `third` is the apex. -/
def apexRole (p : OrientedPaint n k) (b : PaintedBlock p) : Fin 3 :=
  if b.1.apex = p.left then 0 else if b.1.apex = p.right then 1 else 2

def vertexOfRole (p : OrientedPaint n k) (z : Fin n) (r : Fin 3) : Fin n :=
  if r = 0 then p.left else if r = 1 then p.right else z

theorem vertexOfRole_apexRole (p : OrientedPaint n k) (b : PaintedBlock p) :
    vertexOfRole p (paintThird b.1 p.left p.right p.color b.2)
      (apexRole p b) = b.1.apex := by
  by_cases hl : b.1.apex = p.left
  · simp [vertexOfRole, apexRole, hl]
  · by_cases hr : b.1.apex = p.right
    · have hrl : p.right ≠ p.left := (b.1.paints_ne b.2).symm
      simp [vertexOfRole, apexRole, hl, hr, hrl]
    · have hm : b.1.apex =
          paintThird b.1 p.left p.right p.color b.2 := by
        have h := congrArg (fun S => b.1.apex ∈ S)
          (paintThird_spec b.1 p.left p.right p.color b.2).2.2
        simp only [mem_insert, mem_singleton] at h
        aesop
      simp [vertexOfRole, apexRole, hl, hr, ← hm]

/-- Whether the displayed paint is the repeated rather than singleton colour. -/
def repeatedRole (p : OrientedPaint n k) (b : PaintedBlock p) : Bool :=
  decide (b.1.repeated = p.color)

def otherColor (p : OrientedPaint n k) (b : PaintedBlock p) : Fin k :=
  if b.1.repeated = p.color then b.1.singleton else b.1.repeated

/-- Six roles, one third vertex, and one other colour. -/
abbrev PaintedBlockCode (n k : ℕ) := Fin 3 × Bool × Fin n × Fin k

noncomputable def paintedBlockCode (p : OrientedPaint n k)
    (b : PaintedBlock p) : PaintedBlockCode n k :=
  (apexRole p b, repeatedRole p b,
    paintThird b.1 p.left p.right p.color b.2, otherColor p b)

theorem triangleBlock_eq_of_data {b b' : TriangleBlock n k}
    (hv : blockVertices b = blockVertices b')
    (ha : b.apex = b'.apex) (hr : b.repeated = b'.repeated)
    (hs : b.singleton = b'.singleton) : b = b' := by
  have hlmem : b.left = b'.apex ∨ b.left = b'.left ∨ b.left = b'.right := by
    have := congrArg (fun S => b.left ∈ S) hv
    simpa [blockVertices] using this
  have hrmem : b.right = b'.apex ∨ b.right = b'.left ∨ b.right = b'.right := by
    have := congrArg (fun S => b.right ∈ S) hv
    simpa [blockVertices] using this
  have hl : b.left = b'.left ∨ b.left = b'.right := by
    rcases hlmem with hl | hl | hl
    · exact (b.apex_ne_left (ha.trans hl.symm)).elim
    · exact Or.inl hl
    · exact Or.inr hl
  have hright : b.right = b'.left ∨ b.right = b'.right := by
    rcases hrmem with hright | hright | hright
    · exact (b.apex_ne_right (ha.trans hright.symm)).elim
    · exact Or.inl hright
    · exact Or.inr hright
  have hlr : b.left = b'.left ∧ b.right = b'.right := by
    rcases hl with hl | hl <;> rcases hright with hright | hright
    · exact (b.left_ne_right (hl.trans hright.symm)).elim
    · exact ⟨hl, hright⟩
    · have : b'.right < b'.left := by simpa [hl, hright] using b.left_lt_right
      exact (not_lt_of_ge (le_of_lt b'.left_lt_right) this).elim
    · exact (b.left_ne_right (hl.trans hright.symm)).elim
  cases b
  cases b'
  simp_all

theorem paintedBlockCode_injective (p : OrientedPaint n k) :
    Function.Injective (paintedBlockCode p) := by
  intro b b' hcode
  have hrole : apexRole p b = apexRole p b' := congrArg (fun z => z.1) hcode
  have hrep : repeatedRole p b = repeatedRole p b' :=
    congrArg (fun z => z.2.1) hcode
  have hthird : paintThird b.1 p.left p.right p.color b.2 =
      paintThird b'.1 p.left p.right p.color b'.2 :=
    congrArg (fun z => z.2.2.1) hcode
  have hother : otherColor p b = otherColor p b' :=
    congrArg (fun z => z.2.2.2) hcode
  have hv : blockVertices b.1 = blockVertices b'.1 := by
    rw [(paintThird_spec b.1 p.left p.right p.color b.2).2.2,
      (paintThird_spec b'.1 p.left p.right p.color b'.2).2.2, hthird]
  have ha : b.1.apex = b'.1.apex := by
    rw [← vertexOfRole_apexRole p b, ← vertexOfRole_apexRole p b',
      hrole, hthird]
  have hcolors (q : PaintedBlock p) :
      (q.1.repeated = p.color ∧ otherColor p q = q.1.singleton) ∨
      (q.1.singleton = p.color ∧ otherColor p q = q.1.repeated) := by
    by_cases h : q.1.repeated = p.color
    · exact Or.inl ⟨h, by simp [otherColor, h]⟩
    · have hc : p.color = q.1.singleton :=
        (q.1.paint_color_cases q.2).resolve_left (Ne.symm h)
      exact Or.inr ⟨hc.symm, by simp [otherColor, h]⟩
  have hr : b.1.repeated = b'.1.repeated := by
    by_cases hb : b.1.repeated = p.color
    · have hb' : b'.1.repeated = p.color := by
        by_contra hb'
        simp [repeatedRole, hb, hb'] at hrep
      exact hb.trans hb'.symm
    · have hb' : b'.1.repeated ≠ p.color := by
        intro hb'
        simp [repeatedRole, hb, hb'] at hrep
      rcases hcolors b with h | h
      · exact (hb h.1).elim
      · rcases hcolors b' with h' | h'
        · exact (hb' h'.1).elim
        · exact h.2.symm.trans (hother.trans h'.2)
  have hs : b.1.singleton = b'.1.singleton := by
    by_cases hb : b.1.repeated = p.color
    · have hb' : b'.1.repeated = p.color := by
        simpa [repeatedRole, hb] using hrep
      simpa [otherColor, hb, hb'] using hother
    · have hb' : b'.1.repeated ≠ p.color := by
        simpa [repeatedRole, hb] using hrep
      have hc := (b.1.paint_color_cases b.2).resolve_left (Ne.symm hb)
      have hc' := (b'.1.paint_color_cases b'.2).resolve_left (Ne.symm hb')
      exact hc.symm.trans hc'
  exact Subtype.ext (triangleBlock_eq_of_data hv ha hr hs)


/-! ### Geometry forced by two disjoint root supports -/

theorem auxGraph_mem_of_mem_blockVertices {b : TriangleBlock n k}
    {x y : Fin n} (hx : x ∈ blockVertices b) (hy : y ∈ blockVertices b)
    (hxy : x ≠ y) : Sum.inl s(x, y) ∈ b.auxSupport := by
  simp only [blockVertices, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals try { exact (hxy rfl).elim }
  all_goals simp [TriangleBlock.auxSupport, TriangleBlock.graphEdges,
    Sym2.eq_swap]

theorem endpoints_mem_blockVertices_of_auxGraph_mem {b : TriangleBlock n k}
    {x y : Fin n} (h : Sum.inl s(x, y) ∈ b.auxSupport) :
    x ∈ blockVertices b ∧ y ∈ blockVertices b := by
  simp only [TriangleBlock.auxSupport, mem_union, mem_image] at h
  rcases h with ⟨g, hg, heq⟩ | ⟨z, hz, heq⟩
  · have he : g = s(x, y) := Sum.inl.inj heq
    subst g
    simp only [TriangleBlock.graphEdges, mem_insert, mem_singleton] at hg
    rcases hg with hg | hg | hg <;> rw [Sym2.eq_iff] at hg <;>
      rcases hg with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      simp only [blockVertices, mem_insert, mem_singleton] <;> aesop
  · cases heq

/-- A painted edge of one root cannot have both endpoints in a block whose
auxiliary support is disjoint from that root. -/
theorem painted_endpoint_outside_of_auxSupport_disjoint
    {b a : TriangleBlock n k} {x y : Fin n} {c : Fin k}
    (hd : Disjoint b.auxSupport a.auxSupport) (hp : a.Paints x y c) :
    x ∉ blockVertices b ∨ y ∉ blockVertices b := by
  by_contra h
  simp only [not_or, not_not] at h
  have hb : Sum.inl s(x, y) ∈ b.auxSupport :=
    auxGraph_mem_of_mem_blockVertices h.1 h.2 (a.paints_ne hp)
  exact (Finset.disjoint_left.mp hd hb (a.paints_graph_mem hp)).elim

/-! ### Canonical common-link conflicts and witnesses -/

abbrev CommonThreeLink
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k)) :=
  {T // T ∈
    (conflictLinkLayer (alternatingCycleConflicts candidates R) e 3 ∩
      conflictLinkLayer (alternatingCycleConflicts candidates R) f 3)}

theorem insert_root_mem_of_link
    {C : ConflictSystem (AuxVertex n k)} {e : Finset (AuxVertex n k)}
    {T : Hypergraph (AuxVertex n k)} {j : ℕ}
    (hT : T ∈ conflictLinkLayer C e j) : insert e T ∈ C := by
  obtain ⟨⟨Q, hQC, heQ, hQT⟩, -⟩ := mem_conflictLinkLayer.mp hT
  have hQ : Q = insert e T := by
    calc
      Q = insert e (Q.erase e) := (Finset.insert_erase heQ).symm
      _ = insert e T := by rw [hQT]
  rwa [← hQ]

def commonLeftConflict
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (T : CommonThreeLink candidates R e f) :
    ↑(rootedConflicts (alternatingCycleConflicts candidates R) e) :=
  ⟨insert e T.1, by
    rw [rootedConflicts, mem_filter]
    exact ⟨insert_root_mem_of_link (mem_inter.mp T.2).1, mem_insert_self _ _⟩⟩

def commonRightConflict
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (T : CommonThreeLink candidates R e f) :
    ↑(rootedConflicts (alternatingCycleConflicts candidates R) f) :=
  ⟨insert f T.1, by
    rw [rootedConflicts, mem_filter]
    exact ⟨insert_root_mem_of_link (mem_inter.mp T.2).2, mem_insert_self _ _⟩⟩

noncomputable def commonLeftWitness
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (T : CommonThreeLink candidates R e f) :
    RootedAlternatingWitness e (insert e T.1) :=
  rootedConflictWitness candidates R e (commonLeftConflict candidates R e f T)

noncomputable def commonRightWitness
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k))
    (T : CommonThreeLink candidates R e f) :
    RootedAlternatingWitness f (insert f T.1) :=
  rootedConflictWitness candidates R f (commonRightConflict candidates R e f T)

theorem root_not_mem_commonLink
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) : e ∉ T.1 := by
  have hcardT : T.1.card = 3 :=
    (mem_conflictLinkLayer.mp (mem_inter.mp T.2).1).2
  have hconf := insert_root_mem_of_link (mem_inter.mp T.2).1
  have hcardQ : (insert e T.1).card = 4 :=
    (mem_alternatingCycleConflicts.mp hconf).2.1
  intro he
  rw [insert_eq_of_mem he, hcardT] at hcardQ
  omega

theorem commonLink_subset_other_supports
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    let w := commonLeftWitness candidates R e f T
    T.1 ⊆ {w.b₁.auxSupport, w.b₂.auxSupport, w.b₃.auxSupport} := by
  dsimp only
  let w := commonLeftWitness candidates R e f T
  have h := congrArg (Finset.erase · e) w.family_eq
  simp only [erase_insert_eq_erase] at h
  have herase : T.1.erase e = T.1 := erase_eq_self.mpr (root_not_mem_commonLink T)
  rw [herase] at h
  intro s hs
  rw [h] at hs
  exact Finset.erase_subset _ _ hs

theorem commonLink_subset_right_other_supports
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    let w := commonRightWitness candidates R e f T
    T.1 ⊆ {w.b₁.auxSupport, w.b₂.auxSupport, w.b₃.auxSupport} := by
  -- The preceding argument is root-symmetric.
  let T' : CommonThreeLink candidates R f e :=
    ⟨T.1, by simpa [inter_comm] using T.2⟩
  simpa [commonLeftWitness, commonRightWitness, commonLeftConflict,
    commonRightConflict] using
    (commonLink_subset_other_supports T')

theorem triple_finset_card_le_three {X : Type*} [DecidableEq X]
    (a b c : X) : ({a, b, c} : Finset X).card ≤ 3 := by
  calc
    ({a, b, c} : Finset X).card ≤ ({b, c} : Finset X).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ ({c} : Finset X).card + 1 + 1 :=
      Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ ≤ 3 := by simp

theorem rootedWitness_other_ne_root
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) (hcard : Q.card = 4) :
    w.b₁.auxSupport ≠ e ∧ w.b₂.auxSupport ≠ e ∧
    w.b₃.auxSupport ≠ e := by
  have hfull : ({e, w.b₁.auxSupport, w.b₂.auxSupport,
      w.b₃.auxSupport} : Hypergraph (AuxVertex n k)).card = 4 :=
    (congrArg Finset.card w.family_eq).symm.trans hcard
  have h₁ : w.b₁.auxSupport ≠ e := by
    intro h
    have hc : ({e, w.b₂.auxSupport, w.b₃.auxSupport} :
        Hypergraph (AuxVertex n k)).card = 4 := by
      simpa [h] using hfull
    have := triple_finset_card_le_three e w.b₂.auxSupport w.b₃.auxSupport
    omega
  have h₂ : w.b₂.auxSupport ≠ e := by
    intro h
    have hc : ({e, w.b₁.auxSupport, w.b₃.auxSupport} :
        Hypergraph (AuxVertex n k)).card = 4 := by
      have hset : ({e, w.b₁.auxSupport, w.b₃.auxSupport} :
          Hypergraph (AuxVertex n k)) =
          {e, w.b₁.auxSupport, w.b₂.auxSupport, w.b₃.auxSupport} := by
        ext z
        simp only [mem_insert, mem_singleton]
        aesop
      rw [hset]
      exact hfull
    have := triple_finset_card_le_three e w.b₁.auxSupport w.b₃.auxSupport
    omega
  have h₃ : w.b₃.auxSupport ≠ e := by
    intro h
    have hc : ({e, w.b₁.auxSupport, w.b₂.auxSupport} :
        Hypergraph (AuxVertex n k)).card = 4 := by
      have hset : ({e, w.b₁.auxSupport, w.b₂.auxSupport} :
          Hypergraph (AuxVertex n k)) =
          {e, w.b₁.auxSupport, w.b₂.auxSupport, w.b₃.auxSupport} := by
        ext z
        simp only [mem_insert, mem_singleton]
        aesop
      rw [hset]
      exact hfull
    have := triple_finset_card_le_three e w.b₁.auxSupport w.b₂.auxSupport
    omega
  exact ⟨h₁, h₂, h₃⟩

theorem right_b₁_mem_commonLink
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    (commonRightWitness candidates R e f T).b₁.auxSupport ∈ T.1 := by
  let v := commonRightWitness candidates R e f T
  have hconf := insert_root_mem_of_link (mem_inter.mp T.2).2
  have hcard : (insert f T.1).card = 4 :=
    (mem_alternatingCycleConflicts.mp hconf).2.1
  have hne := (rootedWitness_other_ne_root v hcard).1
  have hm : v.b₁.auxSupport ∈ insert f T.1 := by
    have h := congrArg (fun S => v.b₁.auxSupport ∈ S) v.family_eq
    simpa using h
  simpa [hne] using hm

theorem right_b₃_mem_commonLink
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    (commonRightWitness candidates R e f T).b₃.auxSupport ∈ T.1 := by
  let v := commonRightWitness candidates R e f T
  have hconf := insert_root_mem_of_link (mem_inter.mp T.2).2
  have hcard : (insert f T.1).card = 4 :=
    (mem_alternatingCycleConflicts.mp hconf).2.1
  have hne := (rootedWitness_other_ne_root v hcard).2.2
  have hm : v.b₃.auxSupport ∈ insert f T.1 := by
    have h := congrArg (fun S => v.b₃.auxSupport ∈ S) v.family_eq
    simpa using h
  simpa [hne] using hm

def fiveCoords {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) : Fin 5 → Fin n :=
  ![w.x₂, w.x₃,
    paintThird w.b₁ w.x₁ w.x₂ w.d w.paint₁,
    paintThird w.b₂ w.x₂ w.x₃ w.c w.paint₂,
    paintThird w.b₃ w.x₃ w.x₀ w.d w.paint₃]

def rootAnchor {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) (side : Bool) : Fin n :=
  if side then w.x₁ else w.x₀

theorem free_coordinate_of_mem_b₁
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) {z : Fin n}
    (hz : z ∈ blockVertices w.b₁) (hout : z ∉ blockVertices w.b₀) :
    ∃ i, fiveCoords w i = z := by
  have hs := (paintThird_spec w.b₁ w.x₁ w.x₂ w.d w.paint₁).2.2
  rw [hs] at hz
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact (hout (right_mem_blockVertices_of_paints w.paint₀)).elim
  · exact ⟨0, by simp [fiveCoords]⟩
  · exact ⟨2, by simp [fiveCoords]⟩

theorem free_coordinate_of_mem_b₂
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) {z : Fin n}
    (hz : z ∈ blockVertices w.b₂) : ∃ i, fiveCoords w i = z := by
  have hs := (paintThird_spec w.b₂ w.x₂ w.x₃ w.c w.paint₂).2.2
  rw [hs] at hz
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨0, by simp [fiveCoords]⟩
  · exact ⟨1, by simp [fiveCoords]⟩
  · exact ⟨3, by simp [fiveCoords]⟩

theorem free_coordinate_of_mem_b₃
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) {z : Fin n}
    (hz : z ∈ blockVertices w.b₃) (hout : z ∉ blockVertices w.b₀) :
    ∃ i, fiveCoords w i = z := by
  have hs := (paintThird_spec w.b₃ w.x₃ w.x₀ w.d w.paint₃).2.2
  rw [hs] at hz
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨1, by simp [fiveCoords]⟩
  · exact (hout (left_mem_blockVertices_of_paints w.paint₀)).elim
  · exact ⟨4, by simp [fiveCoords]⟩

theorem free_coordinate_of_auxGraph_mem_other_supports
    {e : Finset (AuxVertex n k)} {Q : Hypergraph (AuxVertex n k)}
    (w : RootedAlternatingWitness e Q) {z t : Fin n}
    (hout : z ∉ blockVertices w.b₀)
    {a : TriangleBlock n k}
    (ha : a.auxSupport = w.b₁.auxSupport ∨
      a.auxSupport = w.b₂.auxSupport ∨
      a.auxSupport = w.b₃.auxSupport)
    (hp : Sum.inl s(z, t) ∈ a.auxSupport) :
    ∃ i, fiveCoords w i = z := by
  rcases ha with ha | ha | ha
  · exact free_coordinate_of_mem_b₁ w
      (endpoints_mem_blockVertices_of_auxGraph_mem (ha ▸ hp)).1 hout
  · exact free_coordinate_of_mem_b₂ w
      (endpoints_mem_blockVertices_of_auxGraph_mem (ha ▸ hp)).1
  · exact free_coordinate_of_mem_b₃ w
      (endpoints_mem_blockVertices_of_auxGraph_mem (ha ▸ hp)).1 hout

/-- The paper's key saving: one of the five first-witness vertex coordinates
is an endpoint of the fixed painted edge of the second root. -/
theorem exists_forced_fiveCoordinate
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)} (hef : Disjoint e f)
    (T : CommonThreeLink candidates R e f) :
    let w := commonLeftWitness candidates R e f T
    let v := commonRightWitness candidates R e f T
    ∃ (side : Bool) (i : Fin 5), fiveCoords w i = rootAnchor v side := by
  let w := commonLeftWitness candidates R e f T
  let v := commonRightWitness candidates R e f T
  have hd : Disjoint w.b₀.auxSupport v.b₀.auxSupport := by
    rw [w.root_support, v.root_support]
    exact hef
  rcases painted_endpoint_outside_of_auxSupport_disjoint hd v.paint₀ with h₀ | h₁
  · have hmem := right_b₃_mem_commonLink T
    have hcases := commonLink_subset_other_supports T hmem
    simp only [mem_insert, mem_singleton] at hcases
    obtain ⟨i, hi⟩ := free_coordinate_of_auxGraph_mem_other_supports w h₀
      hcases (v.b₃.paints_graph_mem (v.b₃.paints_symm v.paint₃))
    exact ⟨false, i, by simpa [rootAnchor] using hi⟩
  · have hmem := right_b₁_mem_commonLink T
    have hcases := commonLink_subset_other_supports T hmem
    simp only [mem_insert, mem_singleton] at hcases
    obtain ⟨i, hi⟩ := free_coordinate_of_auxGraph_mem_other_supports w h₁
      hcases (v.b₁.paints_graph_mem v.paint₁)
    exact ⟨true, i, by simpa [rootAnchor] using hi⟩

noncomputable def forcedSide
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)} (hef : Disjoint e f)
    (T : CommonThreeLink candidates R e f) : Bool :=
  Classical.choose (exists_forced_fiveCoordinate hef T)

noncomputable def forcedIndex
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)} (hef : Disjoint e f)
    (T : CommonThreeLink candidates R e f) : Fin 5 :=
  Classical.choose (Classical.choose_spec (exists_forced_fiveCoordinate hef T))

theorem forcedIndex_spec
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)} (hef : Disjoint e f)
    (T : CommonThreeLink candidates R e f) :
    fiveCoords (commonLeftWitness candidates R e f T) (forcedIndex hef T) =
      rootAnchor (commonRightWitness candidates R e f T) (forcedSide hef T) :=
  Classical.choose_spec
    (Classical.choose_spec (exists_forced_fiveCoordinate hef T))

theorem commonLeftRoot_mem_host
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    e ∈ auxiliaryHypergraph candidates R := by
  have hc := insert_root_mem_of_link (mem_inter.mp T.2).1
  exact (alternatingCycleConflicts_isConflictSystem candidates R _ hc)
    (mem_insert_self _ _)

theorem commonRightRoot_mem_host
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    f ∈ auxiliaryHypergraph candidates R := by
  have hc := insert_root_mem_of_link (mem_inter.mp T.2).2
  exact (alternatingCycleConflicts_isConflictSystem candidates R _ hc)
    (mem_insert_self _ _)

theorem commonLeftTrace_mem
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    let w := commonLeftWitness candidates R e f T
    (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) ∈ paintTraces e := by
  let w := commonLeftWitness candidates R e f T
  have hm := mem_paintTraces_of_paints w.paint₀
  have hs : paintTraces w.b₀.auxSupport = paintTraces e :=
    congrArg paintTraces w.root_support
  rw [hs] at hm
  exact hm

theorem commonRightTrace_mem
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {e f : Finset (AuxVertex n k)}
    (T : CommonThreeLink candidates R e f) :
    let w := commonRightWitness candidates R e f T
    (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) ∈ paintTraces f := by
  let w := commonRightWitness candidates R e f T
  have hm := mem_paintTraces_of_paints w.paint₀
  have hs : paintTraces w.b₀.auxSupport = paintTraces f :=
    congrArg paintTraces w.root_support
  rw [hs] at hm
  exact hm

abbrev CommonLinkCharge (n k : ℕ) :=
  Fin 512 × Fin 512 × Bool × Fin 5 × (Fin 4 → Fin n) ×
    (Fin 4 → Fin k) × (Fin 3 → Fin 3 × Bool)

noncomputable def commonLinkCharge
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)} (hef : Disjoint e f)
    (T : CommonThreeLink candidates R e f) : CommonLinkCharge n k := by
  let w := commonLeftWitness candidates R e f T
  let v := commonRightWitness candidates R e f T
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  let q₁ : PaintedBlock p₁ := ⟨w.b₁, w.paint₁⟩
  let q₂ : PaintedBlock p₂ := ⟨w.b₂, w.paint₂⟩
  let q₃ : PaintedBlock p₃ := ⟨w.b₃, w.paint₃⟩
  have he := commonLeftRoot_mem_host T
  have hf := commonRightRoot_mem_host T
  have hte : (paintTraces e).card ≤ 512 :=
    paintTraces_card_le_512
      (fun a ha => auxiliaryHypergraph_uniform candidates R ha) he
  have htf : (paintTraces f).card ≤ 512 :=
    paintTraces_card_le_512
      (fun a ha => auxiliaryHypergraph_uniform candidates R ha) hf
  exact
    (finsetCode (paintTraces e) hte
        ⟨⟨w.x₀, w.x₁, w.c⟩, commonLeftTrace_mem T⟩,
      finsetCode (paintTraces f) htf
        ⟨⟨v.x₀, v.x₁, v.c⟩, commonRightTrace_mem T⟩,
      forcedSide hef T,
      forcedIndex hef T,
      Fin.removeNth (forcedIndex hef T) (fiveCoords w),
      ![w.d, otherColor p₁ q₁, otherColor p₂ q₂,
        otherColor p₃ q₃],
      ![(apexRole p₁ q₁, repeatedRole p₁ q₁),
        (apexRole p₂ q₂, repeatedRole p₂ q₂),
        (apexRole p₃ q₃, repeatedRole p₃ q₃)])

theorem paintedBlock_val_eq_of_components
    {p p' : OrientedPaint n k} (b : PaintedBlock p) (b' : PaintedBlock p')
    (hp : p = p')
    (ha : apexRole p b = apexRole p' b')
    (hr : repeatedRole p b = repeatedRole p' b')
    (hz : paintThird b.1 p.left p.right p.color b.2 =
      paintThird b'.1 p'.left p'.right p'.color b'.2)
    (ho : otherColor p b = otherColor p' b') : b.1 = b'.1 := by
  subst p'
  have hcode : paintedBlockCode p b = paintedBlockCode p b' := by
    apply Prod.ext ha
    apply Prod.ext hr
    apply Prod.ext hz
    exact ho
  exact congrArg Subtype.val (paintedBlockCode_injective p hcode)

theorem commonLinkCharge_injective
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    {e f : Finset (AuxVertex n k)} (hef : Disjoint e f) :
    Function.Injective (commonLinkCharge candidates R hef) := by
  intro T T' hcharge
  let w := commonLeftWitness candidates R e f T
  let w' := commonLeftWitness candidates R e f T'
  let v := commonRightWitness candidates R e f T
  let v' := commonRightWitness candidates R e f T'
  have htₑ := congrArg (fun z : CommonLinkCharge n k => z.1) hcharge
  have htᵣ := congrArg (fun z : CommonLinkCharge n k => z.2.1) hcharge
  have hside := congrArg (fun z : CommonLinkCharge n k => z.2.2.1) hcharge
  have hindex := congrArg (fun z : CommonLinkCharge n k => z.2.2.2.1) hcharge
  have hverts := congrArg (fun z : CommonLinkCharge n k => z.2.2.2.2.1) hcharge
  have hcolors := congrArg (fun z : CommonLinkCharge n k => z.2.2.2.2.2.1) hcharge
  have hroles := congrArg (fun z : CommonLinkCharge n k => z.2.2.2.2.2.2) hcharge
  dsimp only [commonLinkCharge] at htₑ htᵣ hside hindex hverts hcolors hroles
  have hp₀ : (⟨w.x₀, w.x₁, w.c⟩ : OrientedPaint n k) =
      ⟨w'.x₀, w'.x₁, w'.c⟩ := by
    exact finsetCode_value_eq_of_finset_eq _ _ rfl _ _ htₑ
  have hq₀ : (⟨v.x₀, v.x₁, v.c⟩ : OrientedPaint n k) =
      ⟨v'.x₀, v'.x₁, v'.c⟩ := by
    exact finsetCode_value_eq_of_finset_eq _ _ rfl _ _ htᵣ
  have hx₀ : w.x₀ = w'.x₀ := congrArg OrientedPaint.left hp₀
  have hx₁ : w.x₁ = w'.x₁ := congrArg OrientedPaint.right hp₀
  have hc : w.c = w'.c := congrArg OrientedPaint.color hp₀
  have hy₀ : v.x₀ = v'.x₀ := congrArg OrientedPaint.left hq₀
  have hy₁ : v.x₁ = v'.x₁ := congrArg OrientedPaint.right hq₀
  have hanchor : rootAnchor v (forcedSide hef T) =
      rootAnchor v' (forcedSide hef T') := by
    cases hs : forcedSide hef T <;> cases hs' : forcedSide hef T'
    · simpa [rootAnchor, hs, hs'] using hy₀
    · simp [hs, hs'] at hside
    · simp [hs, hs'] at hside
    · simpa [rootAnchor, hs, hs'] using hy₁
  have hcoords : fiveCoords w = fiveCoords w' := by
    have hw : fiveCoords w = Fin.insertNth (forcedIndex hef T)
        (rootAnchor v (forcedSide hef T))
        (Fin.removeNth (forcedIndex hef T) (fiveCoords w)) := by
      apply (Fin.eq_insertNth_iff).2
      exact ⟨forcedIndex_spec hef T, rfl⟩
    have hw' : fiveCoords w' = Fin.insertNth (forcedIndex hef T')
        (rootAnchor v' (forcedSide hef T'))
        (Fin.removeNth (forcedIndex hef T') (fiveCoords w')) := by
      apply (Fin.eq_insertNth_iff).2
      exact ⟨forcedIndex_spec hef T', rfl⟩
    rw [hw, hw', hanchor, hverts, hindex]
  have hx₂ : w.x₂ = w'.x₂ := by
    simpa [fiveCoords] using congrFun hcoords 0
  have hx₃ : w.x₃ = w'.x₃ := by
    simpa [fiveCoords] using congrFun hcoords 1
  have hd : w.d = w'.d := by
    simpa using congrFun hcolors 0
  let p₁ : OrientedPaint n k := ⟨w.x₁, w.x₂, w.d⟩
  let p₁' : OrientedPaint n k := ⟨w'.x₁, w'.x₂, w'.d⟩
  let p₂ : OrientedPaint n k := ⟨w.x₂, w.x₃, w.c⟩
  let p₂' : OrientedPaint n k := ⟨w'.x₂, w'.x₃, w'.c⟩
  let p₃ : OrientedPaint n k := ⟨w.x₃, w.x₀, w.d⟩
  let p₃' : OrientedPaint n k := ⟨w'.x₃, w'.x₀, w'.d⟩
  let b₁ : PaintedBlock p₁ := ⟨w.b₁, w.paint₁⟩
  let b₁' : PaintedBlock p₁' := ⟨w'.b₁, w'.paint₁⟩
  let b₂ : PaintedBlock p₂ := ⟨w.b₂, w.paint₂⟩
  let b₂' : PaintedBlock p₂' := ⟨w'.b₂, w'.paint₂⟩
  let b₃ : PaintedBlock p₃ := ⟨w.b₃, w.paint₃⟩
  let b₃' : PaintedBlock p₃' := ⟨w'.b₃, w'.paint₃⟩
  have hp₁ : p₁ = p₁' := by apply OrientedPaint.ext <;> assumption
  have hp₂ : p₂ = p₂' := by apply OrientedPaint.ext <;> assumption
  have hp₃ : p₃ = p₃' := by apply OrientedPaint.ext <;> assumption
  have hrole₁ := congrFun hroles 0
  have hrole₂ := congrFun hroles 1
  have hrole₃ := congrFun hroles 2
  have hother₁ := congrFun hcolors 1
  have hother₂ := congrFun hcolors 2
  have hother₃ := congrFun hcolors 3
  have hthird₁ := congrFun hcoords 2
  have hthird₂ := congrFun hcoords 3
  have hthird₃ := congrFun hcoords 4
  have hb₁ : w.b₁ = w'.b₁ := by
    apply paintedBlock_val_eq_of_components b₁ b₁' hp₁
    · exact congrArg Prod.fst hrole₁
    · exact congrArg Prod.snd hrole₁
    · simpa [fiveCoords, p₁, p₁', b₁, b₁'] using hthird₁
    · simpa [p₁, p₁', b₁, b₁'] using hother₁
  have hb₂ : w.b₂ = w'.b₂ := by
    apply paintedBlock_val_eq_of_components b₂ b₂' hp₂
    · exact congrArg Prod.fst hrole₂
    · exact congrArg Prod.snd hrole₂
    · simpa [fiveCoords, p₂, p₂', b₂, b₂'] using hthird₂
    · simpa [p₂, p₂', b₂, b₂'] using hother₂
  have hb₃ : w.b₃ = w'.b₃ := by
    apply paintedBlock_val_eq_of_components b₃ b₃' hp₃
    · exact congrArg Prod.fst hrole₃
    · exact congrArg Prod.snd hrole₃
    · simpa [fiveCoords, p₃, p₃', b₃, b₃'] using hthird₃
    · simpa [p₃, p₃', b₃, b₃'] using hother₃
  apply Subtype.ext
  have hins : insert e T.1 = insert e T'.1 := by
    calc
      insert e T.1 = {e, w.b₁.auxSupport, w.b₂.auxSupport,
          w.b₃.auxSupport} := w.family_eq
      _ = {e, w'.b₁.auxSupport, w'.b₂.auxSupport,
          w'.b₃.auxSupport} := by rw [hb₁, hb₂, hb₃]
      _ = insert e T'.1 := w'.family_eq.symm
  have herase := congrArg (Finset.erase · e) hins
  simpa [root_not_mem_commonLink T, root_not_mem_commonLink T'] using herase

/-- Explicit deterministic common-three-link bound.  Its only geometric
hypothesis is disjointness of the two eight-vertex auxiliary root edges. -/
theorem alternatingCycle_commonThreeLink_le_disjoint
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k)) (hef : Disjoint e f) :
    ((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
      conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card ≤
        566231040 * n ^ 4 * k ^ 4 := by
  rw [← Fintype.card_coe]
  change Fintype.card (CommonThreeLink candidates R e f) ≤ _
  have hcard := Fintype.card_le_of_embedding
    (Function.Embedding.mk (commonLinkCharge candidates R hef)
      (commonLinkCharge_injective candidates R hef))
  calc
    Fintype.card (CommonThreeLink candidates R e f) ≤
        Fintype.card (CommonLinkCharge n k) := hcard
    _ = 566231040 * n ^ 4 * k ^ 4 := by
      simp [CommonLinkCharge]
      ring

/-- In the construction the old-colour palette has size at most `n`, so the
preceding literal polynomial is `O(n^8)` with the displayed absolute constant. -/
theorem alternatingCycle_commonThreeLink_le_disjoint_n8
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (e f : Finset (AuxVertex n k)) (hef : Disjoint e f) (hk : k ≤ n) :
    ((conflictLinkLayer (alternatingCycleConflicts candidates R) e 3) ∩
      conflictLinkLayer (alternatingCycleConflicts candidates R) f 3).card ≤
        566231040 * n ^ 8 := by
  refine (alternatingCycle_commonThreeLink_le_disjoint candidates R e f hef).trans ?_
  have hk4 : k ^ 4 ≤ n ^ 4 := pow_le_pow_left' hk 4
  calc
    566231040 * n ^ 4 * k ^ 4 ≤ 566231040 * n ^ 4 * n ^ 4 :=
      Nat.mul_le_mul_left _ hk4
    _ = 566231040 * n ^ 8 := by ring

end

end Erdos136
