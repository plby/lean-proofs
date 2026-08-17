/-
# Abstract iteration for the Reiher--Rödl--Sales pictures

The incidence geometry of a single partite amalgamation is isolated in
`Erdos847Pictures`.  This file formalizes the other half of the argument:
successive amalgamations over the fibers of the projection, followed by the
backward color-focusing argument.

The only input left abstract is `oneFiberAmalgamate`.  It is an ordinary
parameter of the iteration theorem, with no global declaration: supplied with a sparse,
high-chromatic family over one fiber, it returns a new picture together with
its standard copies.  Everything after that construction is proved here.
-/

import ErdosProblems.Erdos847.Pictures

namespace Erdos847Iteration

open Function Set
open Erdos847Pictures

set_option autoImplicit false

universe uV uP uC uK

variable {V : Type uV} [DecidableEq V]
variable {G : ThreeGraph V}

/-! ## Ramsey and independence predicates -/

namespace ThreeGraph

/-- Every coloring of the vertices by `K` has a monochromatic edge. -/
def RamseyFor (G : ThreeGraph V) (K : Type uK) : Prop :=
  ∀ color : V → K,
    ∃ e : G.Edge, ∃ k : K, ∀ v ∈ e.1, color v = k

/-- A finite vertex set containing no edge of `G`. -/
def Independent (G : ThreeGraph V) (I : Finset V) : Prop :=
  ∀ e ∈ G.edges, ¬e ⊆ I

/-- The weighted independent-set property used in the RRS construction. -/
def Fractional (G : ThreeGraph V) [Fintype V] (μ : ℝ) : Prop :=
  ∀ weight : V → ℝ, (∀ v, 0 ≤ weight v) →
    ∃ I : Finset V, ThreeGraph.Independent G I ∧
      μ * ∑ v, weight v ≤ ∑ v ∈ I, weight v

end ThreeGraph

section PicturePredicates

variable {P : Type uP} {C : Type uC}

/-- A picture has a monochromatic combinatorial line in every `K`-coloring. -/
def PictureRamseyFor (picture : Picture G P C) (K : Type uK) : Prop :=
  ∀ color : P → K,
    ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
      ∃ k : K, ∀ a, color (l a) = k

/-- The initial picture must contain a selected line above every base edge. -/
def RealizesEveryEdge (picture : Picture G P C) : Prop :=
  ∀ e : G.Edge,
    ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
      Set.range (fun a => picture.proj (l a)) = (e.1 : Set V)

/-- An independent point set contains no combinatorial line of the picture. -/
def LineIndependent (picture : Picture G P C) (I : Finset P) : Prop :=
  ∀ l : Alphabet → P, IsCombinatorialLine picture.embed l →
    ¬∀ a, l a ∈ I

/-- Every combinatorial line is, after forgetting its coherent ordering, a
quasiline. -/
theorem isQuasiline_of_isCombinatorialLine
    {embed : P → C → Alphabet} {l : Alphabet → P}
    (hl : IsCombinatorialLine embed l) : IsQuasiline embed l := by
  rcases hl with ⟨hinj, σ, hσ⟩
  refine ⟨hinj, ?_⟩
  intro c
  rcases hσ c with hconst | hmoving
  · exact Or.inl hconst
  · exact Or.inr <| by
      intro a b hab
      exact σ.injective (by simpa [hmoving] using hab)

end PicturePredicates

/-! ## The one-fiber construction interface -/

section SparseFamilies

variable {P : Type uP} {C : Type uC}

/-- The fiber (music line) of a picture above a base vertex. -/
abbrev Fiber (picture : Picture G P C) (x : V) :=
  {p : P // picture.proj p = x}

/-- The exact RRS tripod pattern, stated for an abstract moving-support map:
three pairwise distinct lines have a common word and, after relabeling, the
moving support of the first is the disjoint union of the other two. -/
def HasTripod {W I M : Type*} (line : I → Set W)
    (movingSupport : I → Set M) : Prop :=
  ∃ i j k : I, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    (∃ w, w ∈ line i ∧ w ∈ line j ∧ w ∈ line k) ∧
    movingSupport i = movingSupport j ∪ movingSupport k ∧
    Disjoint (movingSupport j) (movingSupport k)

/-- Three members of a set system with three distinct pairwise intersection
points.  This is the triangle configuration excluded by the sparse line
system in the ternary amalgamation. -/
def HasTriangle {W I : Type*} (line : I → Set W) : Prop :=
  ∃ i j k : I, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    (line i ∩ line j).Nonempty ∧
    (line j ∩ line k).Nonempty ∧
    (line k ∩ line i).Nonempty ∧
    line i ∩ line j ∩ line k = ∅

/--
The abstract output of the sparse Hales--Jewett lemma over one fiber.
`highChromatic` is precisely the property used by backward focusing; the two
remaining fields record the incidence hypotheses used by the one-fiber
amalgamation theorem.
-/
structure SparseFiberLineFamily
    (picture : Picture G P C) (x : V) (K : Type uK) where
  Word : Type uP
  Index : Type uP
  Move : Type uP
  line : Index → Fiber picture x → Word
  movingSupport : Index → Set Move
  line_injective : ∀ i, Injective (line i)
  highChromatic : ∀ color : Word → K,
    ∃ i : Index, ∃ k : K, ∀ a, color (line i a) = k
  noTripod : ¬HasTripod (fun i => Set.range (line i)) movingSupport
  noTriangle : ¬HasTriangle (fun i => Set.range (line i))

end SparseFamilies

section StandardCopies

variable {P : Type uP} {C : Type uC}
variable {Q : Type uP} {D : Type uC}

/-- A standard copy preserves the projection and transports all selected
combinatorial lines. -/
structure StandardCopy (source : Picture G P C) (target : Picture G Q D)
    (copy : P → Q) : Prop where
  injective : Injective copy
  proj_copy : ∀ p, target.proj (copy p) = source.proj p
  transports_lines : ∀ l,
    IsCombinatorialLine source.embed l →
      IsCombinatorialLine target.embed (fun a => copy (l a))

namespace StandardCopy

theorem refl (picture : Picture G P C) :
    StandardCopy picture picture id where
  injective := injective_id
  proj_copy := by intro p; rfl
  transports_lines := by intro l hl; simpa using hl

theorem comp {R : Type uP} {E : Type uC}
    {source : Picture G P C} {middle : Picture G Q D}
    {target : Picture G R E} {f : P → Q} {g : Q → R}
    (hf : StandardCopy source middle f)
    (hg : StandardCopy middle target g) :
    StandardCopy source target (g ∘ f) where
  injective := hg.injective.comp hf.injective
  proj_copy := by
    intro p
    exact (hg.proj_copy (f p)).trans (hf.proj_copy p)
  transports_lines := by
    intro l hl
    simpa only [Function.comp_apply] using
      hg.transports_lines (fun a => f (l a)) (hf.transports_lines l hl)

/-- A standard copy transports nontriviality of every source fiber to the
corresponding target fiber.  This is the convenient way for a concrete
one-fiber amalgamation to fill `FiberExtension.targetFiberNontrivial`. -/
theorem targetFiberNontrivial
    {source : Picture G P C} {target : Picture G Q D} {copy : P → Q}
    (hcopy : StandardCopy source target copy)
    (hsource : ∀ x : V, Nontrivial (Fiber source x)) (x : V) :
    Nontrivial (Fiber target x) := by
  let copyFiber : Fiber source x → Fiber target x := fun p =>
    ⟨copy p.1, (hcopy.proj_copy p.1).trans p.2⟩
  have hinjective : Injective copyFiber := by
    intro p q hpq
    apply Subtype.ext
    exact hcopy.injective (congrArg Subtype.val hpq)
  exact @Function.Injective.nontrivial _ _ (hsource x) copyFiber hinjective

end StandardCopy

/--
Abstract result of one actual RRS amalgamation.  The sparse family and the
incidence proof are consumed by the construction producing this structure.
For each coloring, `focus` selects a standard copy on which the chosen fiber
is monochromatic.
-/
structure FiberExtension (source : Picture G P C) (x : V) (K : Type uK) where
  Point : Type uP
  Coord : Type uC
  pointFintype : Fintype Point
  coordFintype : Fintype Coord
  target : Picture G Point Coord
  targetFiberNontrivial : ∀ y : V, Nontrivial (Fiber target y)
  focus : ∀ color : Point → K,
    ∃ copy : P → Point, StandardCopy source target copy ∧
      ∃ k : K, ∀ p, source.proj p = x → color (copy p) = k

/-- A composite standard copy in which all fibers listed in `vertices` have
already been focused. -/
structure FocusedExtension
    (source : Picture G P C) (vertices : List V) (K : Type uK) where
  Point : Type uP
  Coord : Type uC
  pointFintype : Fintype Point
  coordFintype : Fintype Coord
  target : Picture G Point Coord
  targetFiberNontrivial : ∀ x : V, Nontrivial (Fiber target x)
  focused : ∀ color : Point → K,
    ∃ copy : P → Point, StandardCopy source target copy ∧
      ∀ x ∈ vertices, ∃ k : K, ∀ p,
        source.proj p = x → color (copy p) = k

/-- Before any amalgamation, the identity copy focuses the empty list. -/
noncomputable def FocusedExtension.nil
    [Fintype P] [Fintype C]
    (source : Picture G P C) (K : Type uK)
    (sourceFiberNontrivial : ∀ x : V, Nontrivial (Fiber source x)) :
    FocusedExtension source [] K where
  Point := P
  Coord := C
  pointFintype := inferInstance
  coordFintype := inferInstance
  target := source
  targetFiberNontrivial := sourceFiberNontrivial
  focused := by
    intro color
    exact ⟨id, StandardCopy.refl source, by simp⟩

/-- One backward-focusing step.  Old fiber colors survive because a standard
copy commutes with the projection. -/
noncomputable def FocusedExtension.cons
    {source : Picture G P C} {K : Type uK}
    {vertices : List V} {x : V}
    (old : FocusedExtension source vertices K)
    (step : FiberExtension old.target x K) :
    FocusedExtension source (x :: vertices) K where
  Point := step.Point
  Coord := step.Coord
  pointFintype := step.pointFintype
  coordFintype := step.coordFintype
  target := step.target
  targetFiberNontrivial := step.targetFiberNontrivial
  focused := by
    intro color
    obtain ⟨f, hf, kx, hx⟩ := step.focus color
    obtain ⟨g, hg, hold⟩ := old.focused (fun q => color (f q))
    refine ⟨f ∘ g, hg.comp hf, ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨kx, ?_⟩
      intro p hp
      exact hx (g p) ((hg.proj_copy p).trans hp)
    · obtain ⟨ky, hky⟩ := hold y hy
      exact ⟨ky, by simpa only [Function.comp_apply] using hky⟩

end StandardCopies

/-! ## Finite iteration and the Ramsey conclusion -/

section Iteration

variable {P : Type uP} {C : Type uC}

/-- Iterate the supplied one-fiber construction over a finite list of base
vertices.  The construction hypothesis is explicitly parameterized by the
sparse family it consumes. -/
noncomputable def iterate
    [Fintype P] [Fintype C]
    (source : Picture G P C) (K : Type uK) (vertices : List V)
    (sourceFiberNontrivial : ∀ x : V, Nontrivial (Fiber source x))
    (family : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C') (x : V)
      [Nontrivial (Fiber picture x)],
        SparseFiberLineFamily picture x K)
    (oneFiberAmalgamate : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C')
      (sourceFibers : ∀ y : V, Nontrivial (Fiber picture y))
      (x : V)
      [Nontrivial (Fiber picture x)]
      (_lines : SparseFiberLineFamily picture x K),
        FiberExtension picture x K) :
    FocusedExtension source vertices K := by
  induction vertices with
  | nil => exact FocusedExtension.nil source K sourceFiberNontrivial
  | cons x xs ih =>
      let old := ih
      letI : Fintype old.Point := old.pointFintype
      letI : Fintype old.Coord := old.coordFintype
      letI : Nontrivial (Fiber old.target x) :=
        old.targetFiberNontrivial x
      let lines := family old.target x
      exact FocusedExtension.cons old
        (oneFiberAmalgamate old.target old.targetFiberNontrivial x lines)

/-- Focusing every base vertex transfers the base Ramsey property to the
final picture. -/
theorem focusedExtension_ramsey [Fintype V]
    {source : Picture G P C} (hrealizes : RealizesEveryEdge source)
    {vertices : List V} (hall : ∀ x : V, x ∈ vertices)
    {K : Type uK} (hG : ThreeGraph.RamseyFor G K)
    (result : FocusedExtension source vertices K) :
    PictureRamseyFor result.target K := by
  intro color
  obtain ⟨copy, hcopy, hfocused⟩ := result.focused color
  have hfiber : ∀ x : V, ∃ k : K, ∀ p,
      source.proj p = x → color (copy p) = k := by
    intro x
    exact hfocused x (hall x)
  let vertexColor : V → K := fun x => Classical.choose (hfiber x)
  obtain ⟨e, k, he⟩ := hG vertexColor
  obtain ⟨l, hline, hproj⟩ := hrealizes e
  refine ⟨fun a => copy (l a), hcopy.transports_lines l hline, k, ?_⟩
  intro a
  have hmem : source.proj (l a) ∈ e.1 := by
    change source.proj (l a) ∈ (e.1 : Set V)
    rw [← hproj]
    exact ⟨a, rfl⟩
  have hpoint := Classical.choose_spec (hfiber (source.proj (l a)))
  calc
    color (copy (l a)) = vertexColor (source.proj (l a)) :=
      hpoint (l a) rfl
    _ = k := he _ hmem

/-- The finite backward-focusing construction, packaged as an existential
final picture. -/
theorem exists_ramsey_final_picture [Fintype V]
    [Fintype P] [Fintype C]
    (source : Picture G P C) (K : Type uK)
    (sourceFiberNontrivial : ∀ x : V, Nontrivial (Fiber source x))
    (hrealizes : RealizesEveryEdge source)
    (hG : ThreeGraph.RamseyFor G K)
    (family : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C') (x : V)
      [Nontrivial (Fiber picture x)],
        SparseFiberLineFamily picture x K)
    (oneFiberAmalgamate : ∀ {P' : Type uP} {C' : Type uC}
      [Fintype P'] [Fintype C']
      (picture : Picture G P' C')
      (sourceFibers : ∀ y : V, Nontrivial (Fiber picture y))
      (x : V)
      [Nontrivial (Fiber picture x)]
      (_lines : SparseFiberLineFamily picture x K),
        FiberExtension picture x K) :
    ∃ (Q : Type uP) (D : Type uC)
      (_ : Fintype Q) (_ : Fintype D) (final : Picture G Q D),
      (∀ x : V, Nontrivial (Fiber final x)) ∧
        PictureRamseyFor final K := by
  let vertices := (Finset.univ : Finset V).toList
  let result := iterate source K vertices sourceFiberNontrivial
    family oneFiberAmalgamate
  refine ⟨result.Point, result.Coord, result.pointFintype,
    result.coordFintype, result.target, result.targetFiberNontrivial, ?_⟩
  apply focusedExtension_ramsey hrealizes (hG := hG) (result := result)
  intro x
  simp [vertices]

end Iteration

/-! ## Picture zero realizes every base edge -/

section PictureZero

theorem pictureZero_realizesEveryEdge (G : ThreeGraph V) :
    RealizesEveryEdge (pictureZero G) := by
  intro e
  let l : Alphabet → ZeroPoint G := fun a => (e, a)
  have hline : IsCombinatorialLine (zeroWord G) l := by
    refine ⟨?_, Equiv.refl Alphabet, ?_⟩
    · intro a b hab
      exact congrArg Prod.snd hab
    · intro c
      cases c with
      | inl e' =>
          by_cases he : e' = e
          · right
            intro a
            subst e'
            simp [l, zeroWord]
          · left
            refine ⟨1, ?_⟩
            intro a
            simp [l, zeroWord, he]
      | inr e' =>
          by_cases he : e' = e
          · left
            refine ⟨2, ?_⟩
            intro a
            subst e'
            simp [l, zeroWord]
          · left
            refine ⟨1, ?_⟩
            intro a
            simp [l, zeroWord, he]
  refine ⟨l, hline, Set.ext ?_⟩
  intro v
  constructor
  · rintro ⟨a, rfl⟩
    exact ThreeGraph.edgeEquiv_mem G e a
  · intro hv
    let ev : {v : V // v ∈ e.1} := ⟨v, hv⟩
    obtain ⟨a, ha⟩ := (G.edgeEquiv e).surjective ev
    refine ⟨a, ?_⟩
    exact congrArg Subtype.val ha

end PictureZero

/-! ## Weighted independent sets pull back along the projection -/

section FractionalPullback

variable {P : Type uP} {C : Type uC}

/-- The inverse image of a base independent set contains no picture line. -/
theorem lineIndependent_preimage [Fintype P]
    (picture : Picture G P C) {I : Finset V}
    (hI : ThreeGraph.Independent G I) :
    LineIndependent picture (Finset.univ.filter fun p => picture.proj p ∈ I) := by
  intro l hline hall
  have hquasi := isQuasiline_of_isCombinatorialLine hline
  obtain ⟨e, he⟩ := picture.quasiline_maps_edge l hquasi
  apply hI e.1 e.2
  intro v hv
  have hv' : v ∈ Set.range (fun a => picture.proj (l a)) := by
    rw [he]
    exact hv
  obtain ⟨a, rfl⟩ := hv'
  simpa using hall a

/-- Reindex the weight of a pullback by the fibers of the projection. -/
theorem sum_weight_preimage [Fintype V] [Fintype P]
    (picture : Picture G P C) (I : Finset V) (weight : P → ℝ) :
    (∑ v ∈ I, ∑ p, if picture.proj p = v then weight p else 0) =
      ∑ p ∈ Finset.univ.filter (fun p => picture.proj p ∈ I), weight p := by
  classical
  rw [Finset.sum_comm]
  simp [Finset.sum_filter, eq_comm]

/-- The total pushed weight is the original total weight. -/
theorem sum_fiber_weights [Fintype V] [Fintype P]
    (picture : Picture G P C) (weight : P → ℝ) :
    (∑ v, ∑ p, if picture.proj p = v then weight p else 0) = ∑ p, weight p := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp

/--
The projection of any finite picture transfers the full weighted fractional
independence property from the base graph to the picture line hypergraph.
-/
theorem fractional_pullback [Fintype V] [Fintype P]
    (picture : Picture G P C) {μ : ℝ}
    (hfrac : ThreeGraph.Fractional G μ) :
    ∀ weight : P → ℝ, (∀ p, 0 ≤ weight p) →
      ∃ I : Finset P, LineIndependent picture I ∧
        μ * ∑ p, weight p ≤ ∑ p ∈ I, weight p := by
  intro weight hweight
  let pushed : V → ℝ := fun v =>
    ∑ p, if picture.proj p = v then weight p else 0
  have hpushed : ∀ v, 0 ≤ pushed v := by
    intro v
    exact Finset.sum_nonneg fun p hp => by
      split
      · exact hweight p
      · exact le_rfl
  obtain ⟨J, hJ, hbound⟩ := hfrac pushed hpushed
  let I := Finset.univ.filter fun p => picture.proj p ∈ J
  refine ⟨I, lineIndependent_preimage picture hJ, ?_⟩
  rw [← sum_weight_preimage picture J weight]
  rw [← sum_fiber_weights picture weight]
  exact hbound

end FractionalPullback

end Erdos847Iteration
