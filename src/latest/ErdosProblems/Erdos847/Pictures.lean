/-
# Pictures for the Reiher--Rödl--Sales construction (the ternary case)

This file isolates the finite, purely structural part of the ``picture''
construction used in the negative solution of Erdős problem 847.  It has no
dependencies on the analytic estimates used to produce a sparse Hales--Jewett
line system.

There are two results here.

* `pictureZero` is the explicit initial picture.  Its points are the three
  labelled vertices of every edge of the base hypergraph.  Two copies of the
  edge set are used as coordinates; the second copy is a signature which
  prevents a quasiline from using points belonging to different edges.
* `amalgamation_preserves` is the reusable formal core of partite
  amalgamation.  The genuinely difficult incidence argument is exposed as
  `EveryQuasilineConfined`: every quasiline in the amalgamated object is
  contained in one standard copy.  Once this is known, preservation of the
  picture invariant is formal.

The alphabet is fixed to `Fin 3`.  A quasiline is represented by an ordering
of its three points; in every coordinate the three entries must be constant
or pairwise distinct.  A combinatorial line is a quasiline for which one
global permutation of the alphabet gives the order in every moving
coordinate.
-/

import Mathlib

namespace Erdos847Pictures

open Function Set

set_option autoImplicit false

abbrev Alphabet := Fin 3

/-- A finite simple `3`-uniform hypergraph. -/
structure ThreeGraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

namespace ThreeGraph

variable {V : Type*} [DecidableEq V]

/-- The finite type of edges of `G`. -/
abbrev Edge (G : ThreeGraph V) := {e : Finset V // e ∈ G.edges}

/--
The form of `K₄³-minus-freeness used in the ternary RRS amalgamation:
among any four vertices there are at most two edges of the hypergraph.
-/
def K4MinusFree (G : ThreeGraph V) : Prop :=
  ∀ s : Finset V, s.card = 4 →
    (G.edges.filter fun e => e ⊆ s).card ≤ 2

/-- A simple hypergraph is linear when two edges sharing two vertices agree. -/
def Linear (G : ThreeGraph V) : Prop :=
  ∀ e f : G.Edge, 2 ≤ (e.1 ∩ f.1).card → e = f

/-- A noncomputable labelling of every `3`-edge by the ternary alphabet. -/
noncomputable def edgeEquiv (G : ThreeGraph V) (e : G.Edge) :
    Alphabet ≃ {v : V // v ∈ (e.1 : Finset V)} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact (G.uniform e.1 e.2).symm

@[simp]
theorem edgeEquiv_mem (G : ThreeGraph V) (e : G.Edge) (a : Alphabet) :
    (G.edgeEquiv e a : V) ∈ e.1 :=
  (G.edgeEquiv e a).2

end ThreeGraph

section Lines

variable {P C : Type*}

/--
An unordered ternary quasiline, represented by an injective enumeration.
At each coordinate its three entries are either constant or pairwise
distinct.
-/
def IsQuasiline (embed : P → C → Alphabet) (l : Alphabet → P) : Prop :=
  Injective l ∧
    ∀ c, (∃ a, ∀ i, embed (l i) c = a) ∨ Injective (fun i => embed (l i) c)

/--
The three enumerated points form a genuine combinatorial line.  The
permutation `σ` accounts for the arbitrary ordering of an unordered line.
-/
def IsCombinatorialLine (embed : P → C → Alphabet)
    (l : Alphabet → P) : Prop :=
  Injective l ∧
    ∃ σ : Equiv.Perm Alphabet,
      ∀ c, (∃ a, ∀ i, embed (l i) c = a) ∨ ∀ i, embed (l i) c = σ i

theorem range_fin3 (f : Alphabet → P) :
    Set.range f = ({f 0, f 1, f 2} : Set P) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hp | hp | hp
    · exact ⟨0, hp.symm⟩
    · exact ⟨1, hp.symm⟩
    · exact ⟨2, hp.symm⟩

/-- Two combinatorial lines in a cube which share two distinct points have
the same point set. -/
theorem combinatorialLine_range_eq_of_two_points
    (embed : P → C → Alphabet) (hembed : Injective embed)
    (l m : Alphabet → P)
    (hl : IsCombinatorialLine embed l)
    (hm : IsCombinatorialLine embed m)
    {i₀ i₁ j₀ j₁ : Alphabet} (hi : i₀ ≠ i₁)
    (h₀ : l i₀ = m j₀) (h₁ : l i₁ = m j₁) :
    Set.range l = Set.range m := by
  rcases hl with ⟨hlinj, σ, hσ⟩
  rcases hm with ⟨hminj, τ, hτ⟩
  have hj : j₀ ≠ j₁ := by
    intro hj
    apply hi
    apply hlinj
    rw [h₀, h₁, hj]
  let ρ : Equiv.Perm Alphabet := σ.trans τ.symm
  have hpoint : ∀ i, l i = m (ρ i) := by
    intro i
    apply hembed
    funext c
    rcases hσ c with ⟨a, ha⟩ | hmove
    · rcases hτ c with ⟨b, hb⟩ | kmove
      · calc
          embed (l i) c = a := ha i
          _ = embed (l i₀) c := (ha i₀).symm
          _ = embed (m j₀) c := congrArg (fun p => embed p c) h₀
          _ = b := hb j₀
          _ = embed (m (ρ i)) c := (hb (ρ i)).symm
      · exfalso
        apply hj
        apply τ.injective
        calc
          τ j₀ = embed (m j₀) c := (kmove j₀).symm
          _ = embed (l i₀) c := congrArg (fun p => embed p c) h₀.symm
          _ = a := ha i₀
          _ = embed (l i₁) c := (ha i₁).symm
          _ = embed (m j₁) c := congrArg (fun p => embed p c) h₁
          _ = τ j₁ := kmove j₁
    · rcases hτ c with ⟨b, hb⟩ | kmove
      · exfalso
        apply hi
        apply σ.injective
        calc
          σ i₀ = embed (l i₀) c := (hmove i₀).symm
          _ = embed (m j₀) c := congrArg (fun p => embed p c) h₀
          _ = b := hb j₀
          _ = embed (m j₁) c := (hb j₁).symm
          _ = embed (l i₁) c := congrArg (fun p => embed p c) h₁.symm
          _ = σ i₁ := hmove i₁
      · calc
          embed (l i) c = σ i := hmove i
          _ = τ (ρ i) := by simp [ρ]
          _ = embed (m (ρ i)) c := (kmove (ρ i)).symm
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨ρ i, (hpoint i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hiρ⟩ := ρ.surjective j
    exact ⟨i, (hpoint i).trans (congrArg m hiρ)⟩

theorem combinatorialLine_range_inter_subsingleton
    (embed : P → C → Alphabet) (hembed : Injective embed)
    (l m : Alphabet → P)
    (hl : IsCombinatorialLine embed l)
    (hm : IsCombinatorialLine embed m)
    (hne : Set.range l ≠ Set.range m) :
    (Set.range l ∩ Set.range m).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨i₀, hi₀⟩ := hp.1
  obtain ⟨j₀, hj₀⟩ := hp.2
  obtain ⟨i₁, hi₁⟩ := hq.1
  obtain ⟨j₁, hj₁⟩ := hq.2
  have hii : i₀ ≠ i₁ := by
    intro h
    apply hpq
    rw [← hi₀, ← hi₁, h]
  apply hne
  exact combinatorialLine_range_eq_of_two_points embed hembed l m hl hm hii
    (hi₀.trans hj₀.symm) (hi₁.trans hj₁.symm)

end Lines

section Pictures

variable {V : Type*} [DecidableEq V]

/-- The images of the three points enumerated by `l` are precisely one edge. -/
def MapsOntoEdge {P : Type*} (G : ThreeGraph V) (proj : P → V)
    (l : Alphabet → P) : Prop :=
  ∃ e : G.Edge, Set.range (fun i => proj (l i)) = (e.1 : Set V)

/--
A picture over `G`: every quasiline among its points is a genuine
combinatorial line and projects onto an edge of `G`.
-/
structure Picture (G : ThreeGraph V) (P C : Type*) where
  embed : P → C → Alphabet
  embed_injective : Injective embed
  proj : P → V
  quasiline_is_line : ∀ l, IsQuasiline embed l → IsCombinatorialLine embed l
  quasiline_maps_edge : ∀ l, IsQuasiline embed l → MapsOntoEdge G proj l

end Pictures

section PictureZero

variable {V : Type*} [DecidableEq V]
variable (G : ThreeGraph V)

/-- The point and coordinate types of picture zero. -/
abbrev ZeroPoint := G.Edge × Alphabet
abbrev ZeroCoord := G.Edge ⊕ G.Edge

/--
The explicit word belonging to the `a`th vertex of edge `e`.  The left
coordinate `e` carries the moving value; the right coordinate `e` is the
edge signature.  We use the three values `0,1,2`, with signatures only using
`1,2`.
-/
def zeroWord (p : ZeroPoint G) : ZeroCoord G → Alphabet
  | Sum.inl e => if e = p.1 then p.2 else 1
  | Sum.inr e => if e = p.1 then 2 else 1

@[simp]
theorem zeroWord_inl_same (p : ZeroPoint G) :
    zeroWord G p (Sum.inl p.1) = p.2 := by
  simp [zeroWord]

@[simp]
theorem zeroWord_inr_same (p : ZeroPoint G) :
    zeroWord G p (Sum.inr p.1) = 2 := by
  simp [zeroWord]

theorem zeroWord_right_ne_zero (p : ZeroPoint G) (e : G.Edge) :
    zeroWord G p (Sum.inr e) ≠ 0 := by
  simp only [zeroWord]
  split <;> decide

theorem zeroWord_injective : Injective (zeroWord G) := by
  intro p q hpq
  have hr := congrFun hpq (Sum.inr p.1)
  have he : p.1 = q.1 := by
    by_contra hne
    simp [zeroWord, hne] at hr
  have hl := congrFun hpq (Sum.inl p.1)
  have ha : p.2 = q.2 := by
    simpa [zeroWord, he] using hl
  exact Prod.ext he ha

/-- The projection from picture zero to the labelled vertices of its edge. -/
noncomputable def zeroProj (p : ZeroPoint G) : V :=
  G.edgeEquiv p.1 p.2

/--
Every quasiline in picture zero lies over one edge.  This is the signature
coordinate argument from the RRS construction.
-/
theorem zero_quasiline_has_one_edge
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    ∀ i, (l i).1 = (l 0).1 := by
  let e₀ : G.Edge := (l 0).1
  have hconstant : ∃ a, ∀ i, zeroWord G (l i) (Sum.inr e₀) = a := by
    rcases hl.2 (Sum.inr e₀) with hconst | hinj
    · exact hconst
    · exfalso
      have hsurj : Surjective (fun i => zeroWord G (l i) (Sum.inr e₀)) :=
        (Finite.injective_iff_surjective.mp hinj)
      obtain ⟨i, hi⟩ := hsurj 0
      exact zeroWord_right_ne_zero G (l i) e₀ hi
  obtain ⟨a, ha⟩ := hconstant
  intro i
  have hi0 : zeroWord G (l i) (Sum.inr e₀) =
      zeroWord G (l 0) (Sum.inr e₀) := (ha i).trans (ha 0).symm
  change (l i).1 = e₀
  by_contra hne
  have hreverse : (l 0).1 = (l i).1 := by
    simpa [zeroWord, e₀] using hi0
  exact hne hreverse.symm

/-- The alphabet labels occurring on a picture-zero quasiline are distinct. -/
theorem zero_quasiline_labels_injective
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    Injective (fun i => (l i).2) := by
  intro i j hij
  apply hl.1
  apply Prod.ext
  · exact (zero_quasiline_has_one_edge G l hl i).trans
      (zero_quasiline_has_one_edge G l hl j).symm
  · exact hij

/-- Every quasiline in picture zero is one of its selected lines. -/
theorem zero_quasiline_is_line
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    IsCombinatorialLine (zeroWord G) l := by
  let σ : Equiv.Perm Alphabet := Equiv.ofBijective (fun i => (l i).2) ⟨
    zero_quasiline_labels_injective G l hl,
    Finite.injective_iff_surjective.mp (zero_quasiline_labels_injective G l hl)
  ⟩
  refine ⟨hl.1, σ, ?_⟩
  intro c
  cases c with
  | inl e =>
      by_cases he : e = (l 0).1
      · right
        intro i
        have hei : e = (l i).1 :=
          he.trans (zero_quasiline_has_one_edge G l hl i).symm
        simp only [zeroWord, hei, if_pos]
        rfl
      · left
        refine ⟨1, ?_⟩
        intro i
        have hei : e ≠ (l i).1 := by
          intro h
          exact he (h.trans (zero_quasiline_has_one_edge G l hl i))
        simp [zeroWord, hei]
  | inr e =>
      by_cases he : e = (l 0).1
      · left
        refine ⟨2, ?_⟩
        intro i
        have hei : e = (l i).1 :=
          he.trans (zero_quasiline_has_one_edge G l hl i).symm
        simp [zeroWord, hei]
      · left
        refine ⟨1, ?_⟩
        intro i
        have hei : e ≠ (l i).1 := by
          intro h
          exact he (h.trans (zero_quasiline_has_one_edge G l hl i))
        simp [zeroWord, hei]

/-- Every picture-zero quasiline projects onto its indexing edge. -/
theorem zero_quasiline_maps_edge
    (l : Alphabet → ZeroPoint G)
    (hl : IsQuasiline (zeroWord G) l) :
    MapsOntoEdge G (zeroProj G) l := by
  let e₀ : G.Edge := (l 0).1
  let σ : Equiv.Perm Alphabet := Equiv.ofBijective (fun i => (l i).2) ⟨
    zero_quasiline_labels_injective G l hl,
    Finite.injective_iff_surjective.mp (zero_quasiline_labels_injective G l hl)
  ⟩
  refine ⟨e₀, Set.ext ?_⟩
  intro v
  constructor
  · rintro ⟨i, rfl⟩
    change (G.edgeEquiv (l i).1 (l i).2 : V) ∈ e₀.1
    rw [zero_quasiline_has_one_edge G l hl i]
    exact ThreeGraph.edgeEquiv_mem G e₀ (l i).2
  · intro hv
    let w : {v : V // v ∈ e₀.1} := ⟨v, hv⟩
    obtain ⟨a, ha⟩ := (G.edgeEquiv e₀).surjective w
    obtain ⟨i, hi⟩ := σ.surjective a
    refine ⟨i, ?_⟩
    change G.edgeEquiv (l i).1 (l i).2 = v
    rw [zero_quasiline_has_one_edge G l hl i]
    have hlabel : (l i).2 = a := by
      change σ i = a
      exact hi
    rw [hlabel]
    exact congrArg Subtype.val ha

/-- The explicit initial RRS picture over an arbitrary finite 3-graph. -/
noncomputable def pictureZero : Picture G (ZeroPoint G) (ZeroCoord G) where
  embed := zeroWord G
  embed_injective := zeroWord_injective G
  proj := zeroProj G
  quasiline_is_line := zero_quasiline_is_line G
  quasiline_maps_edge := zero_quasiline_maps_edge G

end PictureZero

section Amalgamation

variable {V P C Q D I : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

/--
Data common to all partite amalgamations of a picture.  The incidence proof
which uses a sparse line system is deliberately not included as a field:
it is the separate predicate `EveryQuasilineConfined` below.
-/
structure AmalgamationData (source : Picture G P C) (Q D I : Type*) where
  embed : Q → D → Alphabet
  embed_injective : Injective embed
  proj : Q → V
  copy : I → P → Q
  copy_injective : ∀ i, Injective (copy i)
  proj_copy : ∀ i p, proj (copy i p) = source.proj p
  transports_lines : ∀ i l,
    IsCombinatorialLine source.embed l →
      IsCombinatorialLine embed (fun a => copy i (l a))

/--
The exact geometric output needed from the tripod/triangle-free sparse line
system: each quasiline in the amalgamation is the image of a quasiline in
one standard copy.
-/
def EveryQuasilineConfined (source : Picture G P C)
    (A : AmalgamationData source Q D I) : Prop :=
  ∀ l, IsQuasiline A.embed l →
    ∃ i lp, IsQuasiline source.embed lp ∧ ∀ a, l a = A.copy i (lp a)

/--
A certificate recording both hypotheses used in the ternary RRS incidence
argument.  `K4MinusFree` rules out its exceptional four-vertex pattern; the
sparse (tripod- and triangle-free) line system must establish confinement.
-/
structure TernaryConfinementCertificate (source : Picture G P C)
    (A : AmalgamationData source Q D I) : Prop where
  k4MinusFree : G.K4MinusFree
  confined : EveryQuasilineConfined source A

/--
Once sparse incidence gives confinement, a partite amalgamation is again a
picture.  This is the formal transport step of the RRS proof.
-/
noncomputable def amalgamationPicture (source : Picture G P C)
    (A : AmalgamationData source Q D I)
    (hconf : EveryQuasilineConfined source A) : Picture G Q D where
  embed := A.embed
  embed_injective := A.embed_injective
  proj := A.proj
  quasiline_is_line := by
    intro l hl
    obtain ⟨i, lp, hlp, hcopy⟩ := hconf l hl
    have hline := A.transports_lines i lp (source.quasiline_is_line lp hlp)
    have hl_eq : l = fun a => A.copy i (lp a) := funext hcopy
    rw [hl_eq]
    exact hline
  quasiline_maps_edge := by
    intro l hl
    obtain ⟨i, lp, hlp, hcopy⟩ := hconf l hl
    obtain ⟨e, he⟩ := source.quasiline_maps_edge lp hlp
    refine ⟨e, ?_⟩
    have hl_eq : l = fun a => A.copy i (lp a) := funext hcopy
    rw [hl_eq]
    simpa only [A.proj_copy] using he

/--
The ternary, `K₄³-minus-free` formulation used by RRS.  The first field of
the certificate is consumed by the incidence proof which constructs the
second; preservation itself only transports the second field.
-/
theorem amalgamation_preserves (source : Picture G P C)
    (A : AmalgamationData source Q D I)
    (h : TernaryConfinementCertificate source A) :
    ∃ result : Picture G Q D,
      result.embed = A.embed ∧ result.proj = A.proj := by
  let result := amalgamationPicture source A h.confined
  exact ⟨result, rfl, rfl⟩

end Amalgamation

section RawPartiteAmalgamation

/-!
The remainder of this file constructs the actual union of standard copies
used in Proposition 4.5 of Reiher--Rödl--Sales.  Unlike `AmalgamationData`,
the point type below is literally a subtype of the outer word cube.
-/

variable {V P C N : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

/-- The music line over `x`, regarded as an alphabet in its own right. -/
abbrev MusicFiber (source : Picture G P C) (x : V) :=
  {p : P // source.proj p = x}

/--
At outer coordinate `s`, a standard copy either uses the source point `p`
(a moving coordinate of `U`) or the fixed music-line point stored by `U`.
-/
def sectionPoint (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N) : P :=
  ((U.idxFun s).map Subtype.val).getD p

/-- The coordinate-block extension `η⁺_U` of a line over the music line. -/
def extendWord (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) :
    N × C → Alphabet :=
  fun sc => source.embed (sectionPoint source x U p sc.1) sc.2

@[simp]
theorem sectionPoint_none (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N)
    (hs : U.idxFun s = none) :
    sectionPoint source x U p s = p := by
  simp [sectionPoint, hs]

@[simp]
theorem sectionPoint_some (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N)
    (f : MusicFiber source x) (hs : U.idxFun s = some f) :
    sectionPoint source x U p s = f.1 := by
  simp [sectionPoint, hs]

theorem sectionPoint_mem_fiber_or_eq (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P) (s : N) :
    source.proj (sectionPoint source x U p s) = x ∨
      sectionPoint source x U p s = p := by
  cases hs : U.idxFun s with
  | none => exact Or.inr (sectionPoint_none source x U p s hs)
  | some f =>
      left
      rw [sectionPoint_some source x U p s f hs]
      exact f.2

theorem moving_iff_sectionPoint_eq (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p : P)
    (hp : source.proj p ≠ x) (s : N) :
    U.idxFun s = none ↔ sectionPoint source x U p s = p := by
  constructor
  · exact sectionPoint_none source x U p s
  · intro hsec
    cases hs : U.idxFun s with
    | none => rfl
    | some f =>
        exfalso
        have hfp : f.1 = p := by
          simpa [sectionPoint, hs] using hsec
        exact hp (hfp.symm ▸ f.2)

theorem fixed_value_of_sectionPoint_eq (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) (p q : P)
    (hp : source.proj p ≠ x) (hq : source.proj q = x) (s : N)
    (hsec : sectionPoint source x U p s = q) :
    ∃ f : MusicFiber source x, U.idxFun s = some f ∧ f.1 = q := by
  cases hs : U.idxFun s with
  | none =>
      exfalso
      have hpq : p = q := by simpa [sectionPoint, hs] using hsec
      exact hp (hpq ▸ hq)
  | some f =>
      exact ⟨f, rfl, by simpa [sectionPoint, hs] using hsec⟩

theorem extendWord_section_injective (source : Picture G P C) (x : V)
    {U W : Combinatorics.Line (MusicFiber source x) N} {p q : P}
    (h : extendWord source x U p = extendWord source x W q) (s : N) :
    sectionPoint source x U p s = sectionPoint source x W q s := by
  apply source.embed_injective
  funext c
  exact congrFun h (s, c)

/-- Every standard-copy embedding is injective. -/
theorem extendWord_injective (source : Picture G P C) (x : V)
    (U : Combinatorics.Line (MusicFiber source x) N) :
    Injective (extendWord source x U) := by
  intro p q hpq
  obtain ⟨s, hs⟩ := U.proper
  have hsec := extendWord_section_injective source x hpq s
  simpa [sectionPoint, hs] using hsec

/--
If two extended words agree and the first source point is not on the music
line, then the two line indices and the two source points agree.  This is the
uniqueness assertion behind Fact 4.4(ii).
-/
theorem extendWord_eq_of_not_mem_fiber (source : Picture G P C) (x : V)
    {U W : Combinatorics.Line (MusicFiber source x) N} {p q : P}
    (hp : source.proj p ≠ x)
    (h : extendWord source x U p = extendWord source x W q) :
    U = W ∧ p = q := by
  obtain ⟨s, hs⟩ := U.proper
  have hsecs := extendWord_section_injective source x h s
  have hWs : W.idxFun s = none := by
    cases hcase : W.idxFun s with
    | none => rfl
    | some f =>
        exfalso
        have hp_eq : p = f.1 := by
          simpa [sectionPoint, hs, hcase] using hsecs
        exact hp (hp_eq ▸ f.2)
  have hpq : p = q := by
    simpa [sectionPoint, hs, hWs] using hsecs
  subst q
  have hidx : U.idxFun = W.idxFun := by
    funext t
    have ht := extendWord_section_injective source x h t
    cases hU : U.idxFun t with
    | none =>
        cases hW : W.idxFun t with
        | none => rfl
        | some f =>
            exfalso
            have hp_eq : p = f.1 := by
              simpa [sectionPoint, hU, hW] using ht
            exact hp (hp_eq ▸ f.2)
    | some f =>
        cases hW : W.idxFun t with
        | none =>
            exfalso
            have hp_eq : f.1 = p := by
              simpa [sectionPoint, hU, hW] using ht
            exact hp (hp_eq.symm ▸ f.2)
        | some g =>
            have hfg : f = g := Subtype.ext <| by
              simpa [sectionPoint, hU, hW] using ht
            simp [hU, hW, hfg]
  have hUW : U = W := by
    cases U
    cases W
    simp_all only [Combinatorics.Line.mk.injEq]
  exact ⟨hUW, rfl⟩

/-- Fact 4.4(ii), in its representative form. -/
theorem standard_copies_intersect_only_in_fiber
    (source : Picture G P C) (x : V)
    {U W : Combinatorics.Line (MusicFiber source x) N} {p q : P}
    (hUW : U ≠ W)
    (h : extendWord source x U p = extendWord source x W q) :
    source.proj p = x ∧ source.proj q = x := by
  constructor
  · by_contra hp
    exact hUW (extendWord_eq_of_not_mem_fiber source x hp h).1
  · by_contra hq
    have h' : extendWord source x W q = extendWord source x U p := h.symm
    exact hUW (extendWord_eq_of_not_mem_fiber source x hq h').1.symm

/-- The literal union of all selected standard-copy word images. -/
def IsAmalgamWord (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (w : N × C → Alphabet) : Prop :=
  ∃ U, U ∈ lines ∧ ∃ p, w = extendWord source x U p

abbrev RawAmalgamPoint (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N)) :=
  {w : N × C → Alphabet // IsAmalgamWord source x lines w}

/-- A chosen source representative of a point in the union. -/
noncomputable def rawRepresentative (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) : P :=
  Classical.choose (Classical.choose_spec q.2).2

/-- The line index chosen together with `rawRepresentative`. -/
noncomputable def rawRepresentativeLine (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) :
    Combinatorics.Line (MusicFiber source x) N :=
  Classical.choose q.2

theorem rawRepresentativeLine_mem (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) :
    rawRepresentativeLine source x lines q ∈ lines :=
  (Classical.choose_spec q.2).1

theorem rawRepresentative_spec (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) :
    q.1 = extendWord source x (rawRepresentativeLine source x lines q)
      (rawRepresentative source x lines q) :=
  Classical.choose_spec (Classical.choose_spec q.2).2

/-- The projection on the union, defined using an arbitrary representative. -/
noncomputable def rawProj (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) : V :=
  source.proj (rawRepresentative source x lines q)

/-- The embedding of a selected standard copy into the literal union. -/
def standardCopy (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (p : P) : RawAmalgamPoint source x lines :=
  ⟨extendWord source x U p, U, hU, p, rfl⟩

theorem standardCopy_injective (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines) :
    Injective (standardCopy source x lines U hU) := by
  intro p q hpq
  exact extendWord_injective source x U (congrArg Subtype.val hpq)

/-- The projection is independent of the representative used to define it. -/
theorem rawProj_standardCopy (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (p : P) :
    rawProj source x lines (standardCopy source x lines U hU p) = source.proj p := by
  unfold rawProj
  let W := rawRepresentativeLine source x lines
    (standardCopy source x lines U hU p)
  let q := rawRepresentative source x lines
    (standardCopy source x lines U hU p)
  have heq : extendWord source x W q = extendWord source x U p := by
    exact (rawRepresentative_spec source x lines
      (standardCopy source x lines U hU p)).symm
  by_cases hWU : W = U
  · have hqp : q = p := extendWord_injective source x U <| by
      simpa [W, hWU] using heq
    simpa [q, hqp]
  · obtain ⟨hq, hp⟩ := standard_copies_intersect_only_in_fiber source x hWU heq
    exact hq.trans hp.symm

/-- The ambient-word embedding of the literal union. -/
def rawEmbed (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (q : RawAmalgamPoint source x lines) : N × C → Alphabet := q.1

theorem rawEmbed_injective (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N)) :
    Injective (rawEmbed source x lines) :=
  Subtype.val_injective

/-- A source combinatorial line remains a line in every standard copy. -/
theorem standardCopy_transports_line (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (l : Alphabet → P) (hl : IsCombinatorialLine source.embed l) :
    IsCombinatorialLine (rawEmbed source x lines)
      (fun a => standardCopy source x lines U hU (l a)) := by
  rcases hl with ⟨hlinj, σ, hσ⟩
  refine ⟨(standardCopy_injective source x lines U hU).comp hlinj, σ, ?_⟩
  rintro ⟨s, c⟩
  cases hs : U.idxFun s with
  | none =>
      rcases hσ c with hconst | hmove
      · left
        obtain ⟨a, ha⟩ := hconst
        exact ⟨a, fun i => by simpa [rawEmbed, standardCopy, extendWord,
          sectionPoint, hs] using ha i⟩
      · right
        intro i
        simpa [rawEmbed, standardCopy, extendWord, sectionPoint, hs] using hmove i
  | some f =>
      left
      refine ⟨source.embed f.1 c, ?_⟩
      intro i
      simp [rawEmbed, standardCopy, extendWord, sectionPoint, hs]

/-- A quasiline contained in a standard copy reflects to the source picture. -/
theorem standardCopy_reflects_quasiline (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (U : Combinatorics.Line (MusicFiber source x) N) (hU : U ∈ lines)
    (l : Alphabet → P)
    (hl : IsQuasiline (rawEmbed source x lines)
      (fun a => standardCopy source x lines U hU (l a))) :
    IsQuasiline source.embed l := by
  obtain ⟨s, hs⟩ := U.proper
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply hl.1
    simp [hij]
  · intro c
    simpa [rawEmbed, standardCopy, extendWord, sectionPoint, hs] using hl.2 (s, c)

/-- The raw construction supplies the formal standard-copy transport data. -/
noncomputable def rawAmalgamationData (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N)) :
    AmalgamationData source (RawAmalgamPoint source x lines) (N × C)
      {U // U ∈ lines} where
  embed := rawEmbed source x lines
  embed_injective := rawEmbed_injective source x lines
  proj := rawProj source x lines
  copy U := standardCopy source x lines U.1 U.2
  copy_injective U := standardCopy_injective source x lines U.1 U.2
  proj_copy U := rawProj_standardCopy source x lines U.1 U.2
  transports_lines U := standardCopy_transports_line source x lines U.1 U.2

/-- Intersection of two combinatorial lines, as sets of words. -/
def RawLinesIntersect {A I : Type*}
    (U W : Combinatorics.Line A I) : Prop :=
  ∃ a b, U a = W b

/-- Three lines have a common point. -/
def RawLinesCommonPoint {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  ∃ a b c, U a = W b ∧ W b = Z c

/-- The moving-coordinate set of a raw Hales--Jewett line. -/
def RawMovingSet {A I : Type*} (U : Combinatorics.Line A I) : Set I :=
  {i | U.idxFun i = none}

/-- `U` has moving set equal to the disjoint union of those of `W` and `Z`. -/
def RawMovingDisjointUnion {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  RawMovingSet U = RawMovingSet W ∪ RawMovingSet Z ∧
    Disjoint (RawMovingSet W) (RawMovingSet Z)

/--
The exact RRS tripod (Definition 3.6): three distinct concurrent lines, with
the moving set of one line the disjoint union of the other two.  Since a
line system is unordered, any of the three lines may be the union line.
-/
def IsRawTripod {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  U ≠ W ∧ U ≠ Z ∧ W ≠ Z ∧ RawLinesCommonPoint U W Z ∧
    (RawMovingDisjointUnion U W Z ∨ RawMovingDisjointUnion W U Z ∨
      RawMovingDisjointUnion Z U W)

/-- A triangle consists of three distinct pairwise-intersecting lines with no
common point. -/
def IsRawTriangle {A I : Type*}
    (U W Z : Combinatorics.Line A I) : Prop :=
  U ≠ W ∧ U ≠ Z ∧ W ≠ Z ∧
    RawLinesIntersect U W ∧ RawLinesIntersect U Z ∧ RawLinesIntersect W Z ∧
    ¬ RawLinesCommonPoint U W Z

def RawLineSystemHasNoTripod {A I : Type*}
    (lines : Set (Combinatorics.Line A I)) : Prop :=
  ∀ ⦃U W Z⦄, U ∈ lines → W ∈ lines → Z ∈ lines → ¬ IsRawTripod U W Z

def RawLineSystemHasNoTriangle {A I : Type*}
    (lines : Set (Combinatorics.Line A I)) : Prop :=
  ∀ ⦃U W Z⦄, U ∈ lines → W ∈ lines → Z ∈ lines → ¬ IsRawTriangle U W Z

/-- The direct way the no-tripod hypothesis is consumed later. -/
theorem selected_lines_not_raw_tripod {A I : Type*}
    {lines : Set (Combinatorics.Line A I)}
    (htripod : RawLineSystemHasNoTripod lines)
    {U W Z : Combinatorics.Line A I}
    (hU : U ∈ lines) (hW : W ∈ lines) (hZ : Z ∈ lines)
    (hcommon : RawLinesCommonPoint U W Z)
    (hmoving : RawMovingDisjointUnion U W Z ∨
      RawMovingDisjointUnion W U Z ∨ RawMovingDisjointUnion Z U W) :
    U = W ∨ U = Z ∨ W = Z := by
  by_contra hdistinct
  push Not at hdistinct
  rcases hdistinct with ⟨hneUW, hneUZ, hneWZ⟩
  exact htripod hU hW hZ
    ⟨hneUW, hneUZ, hneWZ, hcommon, hmoving⟩

/-- The direct way the no-triangle hypothesis is consumed later. -/
theorem selected_lines_not_raw_triangle {A I : Type*}
    {lines : Set (Combinatorics.Line A I)}
    (htriangle : RawLineSystemHasNoTriangle lines)
    {U W Z : Combinatorics.Line A I}
    (hU : U ∈ lines) (hW : W ∈ lines) (hZ : Z ∈ lines)
    (hUW : RawLinesIntersect U W) (hUZ : RawLinesIntersect U Z)
    (hWZ : RawLinesIntersect W Z)
    (hcommon : ¬ RawLinesCommonPoint U W Z) :
    U = W ∨ U = Z ∨ W = Z := by
  by_contra hdistinct
  push Not at hdistinct
  rcases hdistinct with ⟨hneUW, hneUZ, hneWZ⟩
  exact htriangle hU hW hZ
    ⟨hneUW, hneUZ, hneWZ, hUW, hUZ, hWZ, hcommon⟩

/-- Projection along an indexed source quasiline is injective, since it maps
onto a three-element edge. -/
theorem mapsOntoEdge_proj_injective (source : Picture G P C)
    {l : Alphabet → P} (hl : MapsOntoEdge G source.proj l) :
    Injective (fun i => source.proj (l i)) := by
  obtain ⟨e, he⟩ := hl
  let f : Alphabet → {v : V // v ∈ e.1} := fun i =>
    ⟨source.proj (l i), by
      have hi : source.proj (l i) ∈ Set.range (fun j => source.proj (l j)) :=
        Set.mem_range_self i
      rw [he] at hi
      exact hi⟩
  have hsurj : Surjective f := by
    intro v
    have hv : (v.1 : V) ∈ Set.range (fun i => source.proj (l i)) := by
      rw [he]
      exact v.2
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, Subtype.ext hi⟩
  have hinj : Injective f :=
    hsurj.injective_of_finite (G.edgeEquiv e)
  intro i j hij
  apply hinj
  exact Subtype.ext hij

/-- In a linear base 3-graph, two projected ternary lines which share two
projected vertices also share their third projected vertex. -/
theorem linear_forces_third_projection (source : Picture G P C)
    (hlinear : G.Linear) (k t : Alphabet → P)
    (hk : MapsOntoEdge G source.proj k)
    (ht : MapsOntoEdge G source.proj t)
    (hcommon₀ : source.proj (k 0) = source.proj (t 0))
    (hcommon₁ : source.proj (k 2) = source.proj (t 1)) :
    source.proj (k 1) = source.proj (t 2) := by
  have hkinj := mapsOntoEdge_proj_injective source hk
  have htinj := mapsOntoEdge_proj_injective source ht
  obtain ⟨e, he⟩ := hk
  obtain ⟨f, hf⟩ := ht
  have hkIn (i : Alphabet) : source.proj (k i) ∈ e.1 := by
    have hi : source.proj (k i) ∈ Set.range (fun j => source.proj (k j)) :=
      Set.mem_range_self i
    rw [he] at hi
    exact hi
  have htIn (i : Alphabet) : source.proj (t i) ∈ f.1 := by
    have hi : source.proj (t i) ∈ Set.range (fun j => source.proj (t j)) :=
      Set.mem_range_self i
    rw [hf] at hi
    exact hi
  have hxy : source.proj (k 0) ≠ source.proj (k 2) := by
    intro h
    exact (by decide : (0 : Alphabet) ≠ 2) (hkinj h)
  have hsub : ({source.proj (k 0), source.proj (k 2)} : Finset V) ⊆
      e.1 ∩ f.1 := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_inter]
    rcases hy with rfl | rfl
    · exact ⟨hkIn 0, hcommon₀ ▸ htIn 0⟩
    · exact ⟨hkIn 2, hcommon₁ ▸ htIn 1⟩
  have hef : e = f := hlinear e f <| by
    calc
      2 = ({source.proj (k 0), source.proj (k 2)} : Finset V).card := by
        simp [hxy]
      _ ≤ (e.1 ∩ f.1).card := Finset.card_le_card hsub
  have hzIn : source.proj (k 1) ∈
      Set.range (fun j => source.proj (t j)) := by
    rw [hf]
    rw [← hef]
    exact hkIn 1
  obtain ⟨j, hj⟩ := hzIn
  fin_cases j
  · exfalso
    have heq : source.proj (k 0) = source.proj (k 1) := hcommon₀.trans hj
    exact (by decide : (0 : Alphabet) ≠ 1) (hkinj heq)
  · exfalso
    have heq : source.proj (k 2) = source.proj (k 1) := hcommon₁.trans hj
    exact (by decide : (2 : Alphabet) ≠ 1) (hkinj heq)
  · exact hj.symm

/--
For a quasiline in the outer cube, every outer-coordinate section is either
constant or a source quasiline.  This is the first reduction in Proposition
4.5.
-/
theorem raw_quasiline_section (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (U : Alphabet → Combinatorics.Line (MusicFiber source x) N)
    (p : Alphabet → P)
    (hword : ∀ i, (l i).1 = extendWord source x (U i) (p i))
    (hl : IsQuasiline (rawEmbed source x lines) l) (s : N) :
    (∃ q, ∀ i, sectionPoint source x (U i) (p i) s = q) ∨
      IsQuasiline source.embed
        (fun i => sectionPoint source x (U i) (p i) s) := by
  let sec : Alphabet → P := fun i => sectionPoint source x (U i) (p i) s
  by_cases hinj : Injective sec
  · right
    refine ⟨hinj, ?_⟩
    intro c
    simpa [rawEmbed, sec, hword, extendWord] using hl.2 (s, c)
  · left
    rw [not_injective_iff] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have hconst_coord : ∀ c, ∃ a, ∀ k, source.embed (sec k) c = a := by
      intro c
      rcases hl.2 (s, c) with hconst | hcoordinj
      · simpa [rawEmbed, sec, hword, extendWord] using hconst
      · exfalso
        apply hne
        apply hcoordinj
        simpa [rawEmbed, sec, hword, extendWord] using
          congrArg (fun q => source.embed q c) hij
    refine ⟨sec 0, ?_⟩
    intro k
    apply source.embed_injective
    funext c
    obtain ⟨a, ha⟩ := hconst_coord c
    exact (ha k).trans (ha 0).symm

theorem raw_quasiline_has_source_section (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (U : Alphabet → Combinatorics.Line (MusicFiber source x) N)
    (p : Alphabet → P)
    (hword : ∀ i, (l i).1 = extendWord source x (U i) (p i))
    (hl : IsQuasiline (rawEmbed source x lines) l) :
    ∃ s, IsQuasiline source.embed
      (fun i => sectionPoint source x (U i) (p i) s) := by
  by_contra hnone
  push Not at hnone
  have hconstant : ∀ s, ∃ q, ∀ i,
      sectionPoint source x (U i) (p i) s = q := by
    intro s
    rcases raw_quasiline_section source x lines l U p hword hl s with hconst | hline
    · exact hconst
    · exact False.elim (hnone s hline)
  have h01 : l 0 = l 1 := by
    apply Subtype.ext
    funext sc
    obtain ⟨q, hq⟩ := hconstant sc.1
    rw [hword 0, hword 1]
    simp only [extendWord]
    rw [hq 0, hq 1]
  exact Fin.zero_ne_one (hl.1 h01)

/-- If a predicate holds for at most one ternary index, a permutation puts
two indices where it fails into positions `0` and `1`. -/
theorem exists_perm_two_not {R : Alphabet → Prop}
    (hatMostOne : ∀ i j, R i → R j → i = j) :
    ∃ σ : Equiv.Perm Alphabet, ¬ R (σ 0) ∧ ¬ R (σ 1) := by
  classical
  have hpairs : ∃ i j : Alphabet, i ≠ j ∧ ¬ R i ∧ ¬ R j := by
    by_cases h0 : R 0
    · by_cases h1 : R 1
      · exact False.elim (Fin.zero_ne_one (hatMostOne 0 1 h0 h1))
      · by_cases h2 : R 2
        · exact False.elim (by
            have h02 : (0 : Alphabet) = 2 := hatMostOne 0 2 h0 h2
            exact (by decide : (0 : Alphabet) ≠ 2) h02)
        · exact ⟨1, 2, by decide, h1, h2⟩
    · by_cases h1 : R 1
      · by_cases h2 : R 2
        · exact False.elim (by
            have h12 : (1 : Alphabet) = 2 := hatMostOne 1 2 h1 h2
            exact (by decide : (1 : Alphabet) ≠ 2) h12)
        · exact ⟨0, 2, by decide, h0, h2⟩
      · exact ⟨0, 1, by decide, h0, h1⟩
  obtain ⟨i, j, hij, hi, hj⟩ := hpairs
  let f : Fin 2 → Alphabet := fun a => ⟨a.1, by omega⟩
  let g : Fin 2 → Alphabet := Fin.cases i (fun _ => j)
  have hf : Injective f := by
    intro a b hab
    exact Fin.ext (Fin.mk.inj_iff.mp hab)
  have hg : Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      change i = j at hab
      exact hij hab
    · exfalso
      change j = i at hab
      exact hij hab.symm
    · rfl
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_⟩
  · simpa [f, g] using hσ 0 ▸ hi
  · simpa [f, g] using hσ 1 ▸ hj

/-- Normal form used at the start of the ternary proof of Proposition 4.5. -/
structure NormalizedRawQuasiline (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines) where
  perm : Equiv.Perm Alphabet
  line : Alphabet → Combinatorics.Line (MusicFiber source x) N
  point : Alphabet → P
  coordinate : N
  line_mem : ∀ i, line i ∈ lines
  word_eq : ∀ i, (l (perm i)).1 = extendWord source x (line i) (point i)
  outer_quasiline : IsQuasiline (rawEmbed source x lines) (fun i => l (perm i))
  source_section : IsQuasiline source.embed
    (fun i => sectionPoint source x (line i) (point i) coordinate)
  point_zero_not_fiber : source.proj (point 0) ≠ x
  point_one_not_fiber : source.proj (point 1) ≠ x
  section_zero : sectionPoint source x (line 0) (point 0) coordinate = point 0
  section_one : sectionPoint source x (line 1) (point 1) coordinate = point 1

theorem normalize_raw_quasiline (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (hl : IsQuasiline (rawEmbed source x lines) l) :
    Nonempty (NormalizedRawQuasiline source x lines l) := by
  classical
  let U : Alphabet → Combinatorics.Line (MusicFiber source x) N :=
    fun i => rawRepresentativeLine source x lines (l i)
  let p : Alphabet → P := fun i => rawRepresentative source x lines (l i)
  have hU (i : Alphabet) : U i ∈ lines :=
    rawRepresentativeLine_mem source x lines (l i)
  have hword (i : Alphabet) :
      (l i).1 = extendWord source x (U i) (p i) :=
    rawRepresentative_spec source x lines (l i)
  obtain ⟨s, hs⟩ := raw_quasiline_has_source_section source x lines l U p hword hl
  let sec : Alphabet → P := fun i => sectionPoint source x (U i) (p i) s
  have hprojInj : Injective (fun i => source.proj (sec i)) :=
    mapsOntoEdge_proj_injective source (source.quasiline_maps_edge sec hs)
  have hatMostOne : ∀ i j, source.proj (sec i) = x →
      source.proj (sec j) = x → i = j := by
    intro i j hi hj
    exact hprojInj (hi.trans hj.symm)
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_two_not hatMostOne
  let U' : Alphabet → Combinatorics.Line (MusicFiber source x) N := fun i => U (σ i)
  let p' : Alphabet → P := fun i => p (σ i)
  have hsec0 : sectionPoint source x (U' 0) (p' 0) s = p' 0 := by
    apply (sectionPoint_mem_fiber_or_eq source x (U' 0) (p' 0) s).resolve_left
    exact hσ0
  have hsec1 : sectionPoint source x (U' 1) (p' 1) s = p' 1 := by
    apply (sectionPoint_mem_fiber_or_eq source x (U' 1) (p' 1) s).resolve_left
    exact hσ1
  have hp0 : source.proj (p' 0) ≠ x := by simpa [sec, U', p', hsec0] using hσ0
  have hp1 : source.proj (p' 1) ≠ x := by simpa [sec, U', p', hsec1] using hσ1
  have houter : IsQuasiline (rawEmbed source x lines) (fun i => l (σ i)) := by
    refine ⟨hl.1.comp σ.injective, ?_⟩
    intro c
    rcases hl.2 c with ⟨a, ha⟩ | hinj
    · exact Or.inl ⟨a, fun i => ha (σ i)⟩
    · exact Or.inr (hinj.comp σ.injective)
  have hsource : IsQuasiline source.embed
      (fun i => sectionPoint source x (U' i) (p' i) s) := by
    refine ⟨hs.1.comp σ.injective, ?_⟩
    intro c
    rcases hs.2 c with ⟨a, ha⟩ | hinj
    · exact Or.inl ⟨a, fun i => ha (σ i)⟩
    · exact Or.inr (hinj.comp σ.injective)
  exact ⟨{
    perm := σ
    line := U'
    point := p'
    coordinate := s
    line_mem := fun i => hU (σ i)
    word_eq := fun i => hword (σ i)
    outer_quasiline := houter
    source_section := hsource
    point_zero_not_fiber := hp0
    point_one_not_fiber := hp1
    section_zero := hsec0
    section_one := hsec1
  }⟩

end RawPartiteAmalgamation

end Erdos847Pictures
