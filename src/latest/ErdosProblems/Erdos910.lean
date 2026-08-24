/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the precise cardinal consequence of M. E. Rudin's 1958
CH construction and isolates the additional statement needed for the
homeomorphism question in Erdős Problem 910.

Reference:
M. E. Rudin, A connected subset of the plane,
Fundamenta Mathematicae 46 (1958), 15--24.
https://eudml.org/doc/213487

Rudin's published theorem supplies the countable-complement clause used for
the cardinality question.  It does not state the homeomorphism clause used by
the other question.  The deductions from each clause are proved below, but no
unproved existence declaration is introduced.
-/

import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Connected

open Set Function
open scoped Cardinal

namespace Erdos910

noncomputable section

/-- The Euclidean plane, used because a planar counterexample suffices. -/
abbrev Plane := ℝ × ℝ

/-- Coordinate presentation of finite-dimensional Euclidean space. -/
abbrev Euclidean (n : ℕ) := Fin n → ℝ

/-- The coordinate presentation of one-dimensional Euclidean space is
homeomorphic to the real line by evaluation at its unique coordinate. -/
def finOneArrowHomeomorph : Euclidean 1 ≃ₜ ℝ where
  toFun f := f 0
  invFun x := fun _ => x
  left_inv f := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  continuous_toFun := continuous_apply 0
  continuous_invFun := continuous_pi fun _ => continuous_id

/-- A set is nondegenerate when it has at least two points. -/
def Nondegenerate {α : Type*} (s : Set α) : Prop :=
  ¬s.Subsingleton

/-- The connected subsets of `M`, represented as an honest type so that its
cardinality can be compared with the continuum. -/
def ConnectedSubsets (M : Set Plane) :=
  {N : Set Plane // N ⊆ M ∧ IsConnected N}

/-- Connected subsets of a set in coordinate Euclidean `n`-space. -/
def EuclideanConnectedSubsets (n : ℕ) (M : Set (Euclidean n)) :=
  {N : Set (Euclidean n) // N ⊆ M ∧ IsConnected N}

/-- The type of countable subsets of a type. -/
def CountableSubsets (α : Type*) :=
  {s : Set α // s.Countable}

/-- The continuum hypothesis in Mathlib's cardinal notation. -/
def ContinuumHypothesis : Prop :=
  Cardinal.continuum.{0} = Cardinal.aleph 1

/-- The first (nondegenerate) question from Problem 910, restricted to the
plane.  `Nonempty (M ≃ₜ N)` means that the subspaces are homeomorphic. -/
def FirstQuestion : Prop :=
  ∀ M : Set Plane, IsConnected M → Nondegenerate M →
    ∃ N : Set Plane,
      N ⊆ M ∧ IsConnected N ∧ Nondegenerate N ∧ ¬Nonempty (M ≃ₜ N)

/-- The first question with the ambient Euclidean dimension universally
quantified.  A counterexample in coordinate dimension two refutes it. -/
def FirstQuestionAllDimensions : Prop :=
  ∀ n : ℕ, ∀ M : Set (Euclidean n), IsConnected M → Nondegenerate M →
    ∃ N : Set (Euclidean n),
      N ⊆ M ∧ IsConnected N ∧ Nondegenerate N ∧ ¬Nonempty (M ≃ₜ N)

/-- The second question from Problem 910 in the plane. -/
def SecondQuestion : Prop :=
  ∀ M : Set Plane, IsConnected M → Nondegenerate M →
    Cardinal.continuum < Cardinal.mk (ConnectedSubsets M)

/-- The literal modern statement with both the ambient dimension and the set
universally quantified.  Its negation follows already in dimension two. -/
def SecondQuestionAllDimensions : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ M : Set (Euclidean n), IsConnected M → Nondegenerate M →
    Cardinal.continuum < Cardinal.mk (EuclideanConnectedSubsets n M)

/-- The property explicitly stated in Rudin's 1958 paper. -/
structure RudinCountableComplement (M : Set Plane) : Prop where
  connected : IsConnected M
  nondegenerate : Nondegenerate M
  countable_complement : ∀ N : Set Plane, N ⊆ M → IsConnected N → Nondegenerate N →
    (M \ N).Countable

/-- A transparent formulation of the theorem actually stated by Rudin. -/
def Rudin1958Statement : Prop :=
  ContinuumHypothesis → ∃ M : Set Plane, RudinCountableComplement M

/-- The strictly stronger witness required to refute the homeomorphism
question.  This clause is not stated in Rudin's 1958 theorem. -/
structure FullCounterexample (M : Set Plane) : Prop extends RudinCountableComplement M where
  homeomorphic : ∀ N : Set Plane, N ⊆ M → IsConnected N → Nondegenerate N →
    Nonempty (M ≃ₜ N)

/-! ### A countable difference does not imply homeomorphism -/

/-- Connected subsets may differ by one point without being homeomorphic.
Thus the pointwise conclusion in Rudin's theorem cannot simply be replaced by
homeomorphism: `Icc 0 1` is compact, whereas `Ioc 0 1` is not.  This example
does not rule out a separate argument using all global features of Rudin's
witness; no such argument is stated in the cited paper. -/
theorem countable_difference_does_not_force_homeomorphism :
    (Icc (0 : ℝ) 1 \ Ioc (0 : ℝ) 1).Countable ∧
      IsConnected (Icc (0 : ℝ) 1) ∧ IsConnected (Ioc (0 : ℝ) 1) ∧
      ¬Nonempty ((Icc (0 : ℝ) 1) ≃ₜ (Ioc (0 : ℝ) 1)) := by
  refine ⟨?_, isConnected_Icc (by norm_num), isConnected_Ioc (by norm_num), ?_⟩
  · have hdiff : Icc (0 : ℝ) 1 \ Ioc (0 : ℝ) 1 = {0} := by
      ext x
      simp
    rw [hdiff]
    exact Set.countable_singleton 0
  · rintro ⟨e⟩
    let _ : CompactSpace (Icc (0 : ℝ) 1) :=
      isCompact_iff_compactSpace.mp isCompact_Icc
    have hsource : IsCompact (Set.univ : Set (Icc (0 : ℝ) 1)) := isCompact_univ
    have htarget : IsCompact (Set.univ : Set (Ioc (0 : ℝ) 1)) := by
      rw [← e.isCompact_preimage]
      simpa using hsource
    let _ : CompactSpace (Ioc (0 : ℝ) 1) := isCompact_univ_iff.mp htarget
    have hIoc : IsCompact (Ioc (0 : ℝ) 1) :=
      isCompact_iff_compactSpace.mpr inferInstance
    rw [isCompact_Ioc_iff] at hIoc
    norm_num at hIoc

/-! ### Every nondegenerate connected `T₁` set has a proper one

This is the Knaster--Kuratowski lemma cited by Erdős.  Its proof makes the
logical status of the first question precise: a candidate proper connected
subset always exists.  What is missing from the cited 1958 theorem is the
claim that every such candidate in Rudin's particular set is homeomorphic to
the whole set. -/

/-- A union of two nonempty separated sets is not preconnected.  Here the two
displayed disjointness assumptions are the standard closure formulation of
separation. -/
lemma not_isPreconnected_union_of_separated {α : Type*} [TopologicalSpace α]
    {a b : Set α} (hab : Disjoint (closure a) b)
    (hba : Disjoint a (closure b)) (ha : a.Nonempty) (hb : b.Nonempty) :
    ¬ IsPreconnected (a ∪ b) := by
  intro hconn
  have hcover : a ∪ b ⊆ (closure b)ᶜ ∪ (closure a)ᶜ := by
    intro x hx
    rcases hx with hxa | hxb
    · exact Or.inl (Set.disjoint_left.mp hba hxa)
    · exact Or.inr (Set.disjoint_right.mp hab hxb)
  have hleft : ((a ∪ b) ∩ (closure b)ᶜ).Nonempty := by
    rcases ha with ⟨x, hxa⟩
    exact ⟨x, Or.inl hxa, Set.disjoint_left.mp hba hxa⟩
  have hright : ((a ∪ b) ∩ (closure a)ᶜ).Nonempty := by
    rcases hb with ⟨x, hxb⟩
    exact ⟨x, Or.inr hxb, Set.disjoint_right.mp hab hxb⟩
  rcases hconn (closure b)ᶜ (closure a)ᶜ isClosed_closure.isOpen_compl
      isClosed_closure.isOpen_compl hcover hleft hright with
    ⟨x, hx, hxcb, hxca⟩
  rcases hx with hxa | hxb
  · exact hxca (subset_closure hxa)
  · exact hxcb (subset_closure hxb)

/-- Knaster--Kuratowski: every nondegenerate connected subset of a `T₁`
space contains a proper nondegenerate connected subset. -/
theorem exists_proper_nondegenerate_connected_subset {α : Type*}
    [TopologicalSpace α] [T1Space α] {m : Set α} (hm : IsConnected m)
    (hmnd : Nondegenerate m) :
    ∃ n : Set α, n ⊂ m ∧ IsConnected n ∧ Nondegenerate n := by
  classical
  obtain ⟨p, hp⟩ := hm.nonempty
  let s : Set α := m \ {p}
  have hminf : m.Infinite :=
    hm.isPreconnected.infinite_of_nontrivial (Set.not_subsingleton_iff.mp hmnd)
  have hsinf : s.Infinite := by
    exact hminf.sdiff (Set.finite_singleton p)
  have hsne : s.Nonempty := hsinf.nonempty
  have hssub : s ⊆ m := sdiff_subset
  have hsnd : Nondegenerate s := Set.not_subsingleton_iff.mpr hsinf.nontrivial
  by_cases hsconn : IsConnected s
  · refine ⟨s, Set.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩, hsconn, hsnd⟩
    intro hsm
    have : p ∈ s := hsm ▸ hp
    exact this.2 rfl
  · have hsnpre : ¬ IsPreconnected s := by
      intro hpre
      exact hsconn ⟨hsne, hpre⟩
    simp only [IsPreconnected] at hsnpre
    push Not at hsnpre
    obtain ⟨u, v, hu, hv, hcover, hsu, hsv, hinter⟩ := hsnpre
    have hinter' : ¬ (s ∩ (u ∩ v)).Nonempty :=
      Set.not_nonempty_iff_eq_empty.mpr hinter
    let a : Set α := s ∩ u
    let b : Set α := s ∩ v
    have ha : a.Nonempty := hsu
    have hb : b.Nonempty := hsv
    have hsep : Disjoint a v := by
      rw [Set.disjoint_left]
      intro x hxa hxv
      exact hinter' ⟨x, hxa.1, hxa.2, hxv⟩
    have hsep' : Disjoint u b := by
      rw [Set.disjoint_left]
      intro x hxu hxb
      exact hinter' ⟨x, hxb.1, hxu, hxb.2⟩
    have hclab : Disjoint (closure a) b :=
      (hsep.closure_left hv).mono_right inter_subset_right
    have haclb : Disjoint a (closure b) :=
      (hsep'.closure_right hu).mono_left inter_subset_right
    have hsab : s = a ∪ b := by
      ext x
      constructor
      · intro hxs
        rcases hcover hxs with hxu | hxv
        · exact Or.inl ⟨hxs, hxu⟩
        · exact Or.inr ⟨hxs, hxv⟩
      · rintro (hxa | hxb)
        · exact hxa.1
        · exact hxb.1
    let t : Set α := a ∪ {p}
    have hpt : p ∈ t := Or.inr (mem_singleton p)
    have hpa : p ∉ a := by
      intro hpa'
      exact hpa'.1.2 rfl
    have htconn : IsConnected t := by
      refine ⟨⟨p, hpt⟩, ?_⟩
      by_contra htpre
      simp only [IsPreconnected] at htpre
      push Not at htpre
      obtain ⟨r, q, hr, hq, htcov, htr, htq, htinter⟩ := htpre
      have htinter0 : ¬ (t ∩ (r ∩ q)).Nonempty :=
        Set.not_nonempty_iff_eq_empty.mpr htinter
      have hpcover : p ∈ r ∨ p ∈ q := htcov hpt
      have hside : ∀ (r q : Set α), IsOpen r → IsOpen q → t ⊆ r ∪ q →
          (t ∩ r).Nonempty → (t ∩ q).Nonempty →
          ¬ (t ∩ (r ∩ q)).Nonempty → p ∈ r → False := by
        intro r q hr hq htcov htr htq htinter hpr
        have hpnq : p ∉ q := by
          intro hpq
          exact htinter ⟨p, hpt, hpr, hpq⟩
        let c : Set α := t ∩ r
        let d : Set α := t ∩ q
        have hc : c.Nonempty := htr
        have hd : d.Nonempty := htq
        have hcd : Disjoint c q := by
          rw [Set.disjoint_left]
          intro x hxc hxq
          exact htinter ⟨x, hxc.1, hxc.2, hxq⟩
        have hrcd : Disjoint r d := by
          rw [Set.disjoint_left]
          intro x hxr hxd
          exact htinter ⟨x, hxd.1, hxr, hxd.2⟩
        have hcldc : Disjoint (closure d) c := by
          exact (hrcd.closure_right hr).symm.mono_right inter_subset_right
        have hdclc : Disjoint d (closure c) := by
          exact (hcd.closure_left hq).symm.mono_left inter_subset_right
        have hdsuba : d ⊆ a := by
          intro x hxd
          rcases hxd.1 with hxa | hxp
          · exact hxa
          · have : x = p := hxp
            subst x
            exact False.elim (hpnq hxd.2)
        have hcldb : Disjoint (closure d) b :=
          hclab.mono_left (closure_mono hdsuba)
        have hdclb : Disjoint d (closure b) :=
          haclb.mono_left hdsuba
        have hsepD : Disjoint (closure d) (c ∪ b) :=
          hcldc.union_right hcldb
        have hsepD' : Disjoint d (closure (c ∪ b)) := by
          rw [closure_union]
          exact hdclc.union_right hdclb
        have hmdecomp : m = d ∪ (c ∪ b) := by
          ext x
          constructor
          · intro hxm
            by_cases hxp : x = p
            · subst x
              exact Or.inr (Or.inl ⟨hpt, hpr⟩)
            · have hxs : x ∈ s := ⟨hxm, by simpa using hxp⟩
              have hxab : x ∈ a ∪ b := hsab ▸ hxs
              rcases hxab with hxa | hxb
              · have hxt : x ∈ t := Or.inl hxa
                rcases htcov hxt with hxr | hxq
                · exact Or.inr (Or.inl ⟨hxt, hxr⟩)
                · exact Or.inl ⟨hxt, hxq⟩
              · exact Or.inr (Or.inr hxb)
          · rintro (hxd | hxc | hxb)
            · exact hxd.1.elim (fun hxa => hssub hxa.1) (fun hxp => hxp ▸ hp)
            · exact hxc.1.elim (fun hxa => hssub hxa.1) (fun hxp => hxp ▸ hp)
            · exact hssub hxb.1
        have hother : (c ∪ b).Nonempty := hc.mono subset_union_left
        have hnpre := not_isPreconnected_union_of_separated hsepD hsepD' hd hother
        exact hnpre (hmdecomp ▸ hm.isPreconnected)
      rcases hpcover with hpr | hpq
      · exact hside r q hr hq htcov htr htq htinter0 hpr
      · have htinter' : ¬ (t ∩ (q ∩ r)).Nonempty := by
          intro h
          rcases h with ⟨x, hxt, hxq, hxr⟩
          exact htinter0 ⟨x, hxt, hxr, hxq⟩
        exact hside q r hq hr (by simpa [union_comm] using htcov) htq htr htinter' hpq
    have htsub : t ⊆ m := by
      rintro x (hxa | hxp)
      · exact hxa.1.1
      · simpa using hxp ▸ hp
    have htnd : Nondegenerate t := Set.not_subsingleton_iff.mpr ⟨p, hpt, ha.some,
      Or.inl ha.some_mem, by
        intro h
        exact hpa (by simpa [h] using ha.some_mem)⟩
    have htne : t ≠ m := by
      intro htm
      rcases hb with ⟨x, hxb⟩
      have hxt : x ∈ t := htm ▸ hxb.1.1
      rcases hxt with hxa | hxp
      · exact Set.disjoint_left.mp (hclab.mono_left subset_closure) hxa hxb
      · subst x
        exact hxb.1.2 rfl
    exact ⟨t, Set.ssubset_iff_subset_ne.mpr ⟨htsub, htne⟩, htconn, htnd⟩

/-! ### Compact connected sets with a non-cut point

If deleting a point from a compact connected set leaves a connected set,
that deletion is a noncompact connected subset and therefore cannot be
homeomorphic to the original set.  Thus an exact counterexample to the first
question would have to evade this standard source of candidates as well. -/

/-- A connected point deletion from a nondegenerate compact set supplies the
candidate required by the first question. -/
theorem compact_connected_noncut_has_nonhomeomorphic_subset {α : Type*}
    [TopologicalSpace α] [T2Space α] {m : Set α} (hmcompact : IsCompact m)
    (hm : IsConnected m) (hmnd : Nondegenerate m) {p : α} (hp : p ∈ m)
    (hdelete : IsConnected (m \ {p})) :
    ∃ n : Set α, n ⊆ m ∧ IsConnected n ∧ Nondegenerate n ∧
      ¬ Nonempty (m ≃ₜ n) := by
  classical
  let n : Set α := m \ {p}
  have hminf : m.Infinite :=
    hm.isPreconnected.infinite_of_nontrivial (Set.not_subsingleton_iff.mp hmnd)
  have hninf : n.Infinite := hminf.sdiff (Set.finite_singleton p)
  have hnnd : Nondegenerate n := Set.not_subsingleton_iff.mpr hninf.nontrivial
  have hncompact : ¬ IsCompact n := by
    intro hcompact
    have hnclosed : IsClosed n := hcompact.isClosed
    have hresult := hm.isPreconnected ({p}ᶜ) nᶜ isClosed_singleton.isOpen_compl
      hnclosed.isOpen_compl
    have hcover : m ⊆ {p}ᶜ ∪ nᶜ := by
      intro x hxm
      by_cases hxp : x = p
      · right
        simp [n, hxp]
      · left
        simpa using hxp
    have hleft : (m ∩ {p}ᶜ).Nonempty := by
      obtain ⟨x, hxm, hxp⟩ := hninf.nonempty
      exact ⟨x, hxm, by simpa using hxp⟩
    have hright : (m ∩ nᶜ).Nonempty := by
      refine ⟨p, hp, ?_⟩
      simp [n]
    obtain ⟨x, hxm, hxp, hxn⟩ := hresult hcover hleft hright
    exact hxn ⟨hxm, by simpa using hxp⟩
  refine ⟨n, sdiff_subset, hdelete, hnnd, ?_⟩
  rintro ⟨e⟩
  let _ : CompactSpace m := isCompact_iff_compactSpace.mp hmcompact
  have hsource : IsCompact (Set.univ : Set m) := isCompact_univ
  have htarget : IsCompact (Set.univ : Set n) := by
    rw [← e.isCompact_preimage]
    simpa using hsource
  let _ : CompactSpace n := isCompact_univ_iff.mp htarget
  exact hncompact (isCompact_iff_compactSpace.mpr inferInstance)

/-! ### The first question in one dimension

The first assertion is true for subsets of the real line.  If the original
connected set is compact, a half-open interval inside it is a noncompact
connected subset.  If the original set is noncompact, a closed interval
inside it is compact.  Thus any counterexample to the universal question
must use ambient dimension at least two. -/

/-- Every nondegenerate connected subset of the real line contains a
nondegenerate connected subset of a different homeomorphism type. -/
theorem real_has_nonhomeomorphic_connected_subset {m : Set ℝ}
    (hm : IsConnected m) (hmnd : Nondegenerate m) :
    ∃ n : Set ℝ, n ⊆ m ∧ IsConnected n ∧ Nondegenerate n ∧
      ¬ Nonempty (m ≃ₜ n) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hmnd
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℝ, a ∈ m ∧ b ∈ m ∧ a < b := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact ⟨x, y, hx, hy, hlt⟩
    · exact ⟨y, x, hy, hx, hgt⟩
  by_cases hcompact : IsCompact m
  · let n : Set ℝ := Ioc a b
    have hnsub : n ⊆ m := by
      intro z hz
      exact hm.2.ordConnected.out ha hb ⟨hz.1.le, hz.2⟩
    have hnconn : IsConnected n := isConnected_Ioc hab
    have hmid : (a + b) / 2 ∈ n := by
      exact ⟨by linarith, by linarith⟩
    have hbn : b ∈ n := by
      exact ⟨hab, le_rfl⟩
    have hnnd : Nondegenerate n := Set.not_subsingleton_iff.mpr
      ⟨(a + b) / 2, hmid, b, hbn, by linarith⟩
    refine ⟨n, hnsub, hnconn, hnnd, ?_⟩
    rintro ⟨e⟩
    let _ : CompactSpace m := isCompact_iff_compactSpace.mp hcompact
    have hsource : IsCompact (Set.univ : Set m) := isCompact_univ
    have htarget : IsCompact (Set.univ : Set n) := by
      rw [← e.isCompact_preimage]
      simpa using hsource
    let _ : CompactSpace n := isCompact_univ_iff.mp htarget
    have hncompact : IsCompact n := isCompact_iff_compactSpace.mpr inferInstance
    dsimp [n] at hncompact
    rw [isCompact_Ioc_iff] at hncompact
    exact (not_le_of_gt hab) hncompact
  · let n : Set ℝ := Icc a b
    have hnsub : n ⊆ m := hm.2.ordConnected.out ha hb
    have hnconn : IsConnected n := isConnected_Icc hab.le
    have han : a ∈ n := by exact ⟨le_rfl, hab.le⟩
    have hbn : b ∈ n := by exact ⟨hab.le, le_rfl⟩
    have hnnd : Nondegenerate n := Set.not_subsingleton_iff.mpr
      ⟨a, han, b, hbn, ne_of_lt hab⟩
    refine ⟨n, hnsub, hnconn, hnnd, ?_⟩
    rintro ⟨e⟩
    have hncompact : IsCompact n := isCompact_Icc
    have hmcompact : IsCompact m := by
      let _ : CompactSpace n := isCompact_iff_compactSpace.mp hncompact
      have hsource : IsCompact (Set.univ : Set n) := isCompact_univ
      have htarget : IsCompact (Set.univ : Set m) := by
        rw [← e.symm.isCompact_preimage]
        simpa using hsource
      let _ : CompactSpace m := isCompact_univ_iff.mp htarget
      exact isCompact_iff_compactSpace.mpr inferInstance
    exact hcompact hmcompact

/-- Transport a candidate for the first question across a homeomorphism of
ambient spaces. -/
lemma transport_first_candidate {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {m : Set X}
    (h : ∃ n : Set Y, n ⊆ e '' m ∧ IsConnected n ∧ Nondegenerate n ∧
      ¬ Nonempty ((e '' m) ≃ₜ n)) :
    ∃ n : Set X, n ⊆ m ∧ IsConnected n ∧ Nondegenerate n ∧
      ¬ Nonempty (m ≃ₜ n) := by
  obtain ⟨n, hnsub, hnconn, hnnd, hnnot⟩ := h
  let p : Set X := e ⁻¹' n
  have hpsub : p ⊆ m := by
    intro x hx
    obtain ⟨y, hy, hey⟩ := hnsub hx
    exact e.injective hey ▸ hy
  have hpconn : IsConnected p := e.isConnected_preimage.mpr hnconn
  have hpnd : Nondegenerate p :=
    ((Set.not_subsingleton_iff.mp hnnd).preimage e.surjective).not_subsingleton
  refine ⟨p, hpsub, hpconn, hpnd, ?_⟩
  rintro ⟨hmp⟩
  let hpreN : p ≃ₜ n :=
    (e.image p).trans (Homeomorph.setCongr (e.image_preimage n))
  exact hnnot ⟨(e.image m).symm |>.trans hmp |>.trans hpreN⟩

/-- The exact coordinate-space instance of the first question in dimension
one. -/
theorem firstQuestion_dimension_one :
    ∀ m : Set (Euclidean 1), IsConnected m → Nondegenerate m →
      ∃ n : Set (Euclidean 1), n ⊆ m ∧ IsConnected n ∧ Nondegenerate n ∧
        ¬ Nonempty (m ≃ₜ n) := by
  intro m hm hmnd
  apply transport_first_candidate finOneArrowHomeomorph
  apply real_has_nonhomeomorphic_connected_subset
  · exact finOneArrowHomeomorph.isConnected_image.mpr hm
  · exact ((Set.not_subsingleton_iff.mp hmnd).image
      finOneArrowHomeomorph.injective).not_subsingleton

/-! ### The literal ambient-dimension version of the second question

Erdős's 1944 paper asks about sets of topological dimension greater than
one.  The modern problem page instead says merely that the ambient Euclidean
dimension is at least two.  A line segment in the plane refutes that literal
modern statement in ZFC.  The next lemmas give a fully formal cardinal count:
a connected subset of a real interval is determined by its infimum, supremum,
and the two endpoint-membership flags. -/

/-- Connected subsets of the unit interval, as a type. -/
def IccConnectedSubsets :=
  {s : Set ℝ // s ⊆ Icc (0 : ℝ) 1 ∧ IsConnected s}

/-- Endpoint data for a connected subset of the unit interval. -/
noncomputable def intervalCode (s : IccConnectedSubsets) :
    Bool × ℝ × ℝ × Bool × Bool := by
  classical
  exact if h : s.1.Nonempty then
    (true, sInf s.1, sSup s.1, decide (sInf s.1 ∈ s.1), decide (sSup s.1 ∈ s.1))
  else
    (false, 0, 0, false, false)

/-- An interior point between the infimum and supremum of a nonempty
order-connected real set belongs to the set. -/
lemma mem_of_sInf_lt_of_lt_sSup {s : Set ℝ} (hne : s.Nonempty)
    (hord : s.OrdConnected) {x : ℝ} (hix : sInf s < x) (hxs : x < sSup s) : x ∈ s := by
  rcases exists_lt_of_csInf_lt hne hix with ⟨a, haS, hax⟩
  rcases exists_lt_of_lt_csSup hne hxs with ⟨b, hbS, hxb⟩
  exact hord.out haS hbS ⟨hax.le, hxb.le⟩

/-- Two nonempty bounded order-connected real sets with the same two
endpoints and endpoint-membership flags are equal. -/
lemma interval_eq_of_data {s t : Set ℝ}
    (hsne : s.Nonempty) (htne : t.Nonempty)
    (hsb : BddBelow s) (hsa : BddAbove s)
    (htb : BddBelow t) (hta : BddAbove t)
    (hsord : s.OrdConnected) (htord : t.OrdConnected)
    (hinf : sInf s = sInf t) (hsup : sSup s = sSup t)
    (hinfmem : sInf s ∈ s ↔ sInf t ∈ t)
    (hsupmem : sSup s ∈ s ↔ sSup t ∈ t) : s = t := by
  ext x
  constructor
  · intro hxs
    have hil : sInf s ≤ x := csInf_le hsb hxs
    have hiu : x ≤ sSup s := le_csSup hsa hxs
    rcases hil.eq_or_lt with hix | hix
    · subst x
      rw [hinf]
      exact hinfmem.mp hxs
    · rcases hiu.eq_or_lt with hxu | hxu
      · subst x
        rw [hsup]
        exact hsupmem.mp hxs
      · apply mem_of_sInf_lt_of_lt_sSup htne htord
        · simpa [hinf] using hix
        · simpa [hsup] using hxu
  · intro hxt
    have hil : sInf t ≤ x := csInf_le htb hxt
    have hiu : x ≤ sSup t := le_csSup hta hxt
    rcases hil.eq_or_lt with hix | hix
    · subst x
      rw [← hinf]
      exact hinfmem.mpr hxt
    · rcases hiu.eq_or_lt with hxu | hxu
      · subst x
        rw [← hsup]
        exact hsupmem.mpr hxt
      · apply mem_of_sInf_lt_of_lt_sSup hsne hsord
        · simpa [hinf] using hix
        · simpa [hsup] using hxu

/-- Endpoint data injectively codes connected subsets of the unit interval. -/
lemma intervalCode_injective : Function.Injective intervalCode := by
  classical
  intro s t hcode
  by_cases hs : s.1.Nonempty
  · by_cases ht : t.1.Nonempty
    · have hinf : sInf s.1 = sInf t.1 := by
        simpa [intervalCode, hs, ht] using congrArg (fun p => p.2.1) hcode
      have hsup : sSup s.1 = sSup t.1 := by
        simpa [intervalCode, hs, ht] using congrArg (fun p => p.2.2.1) hcode
      have hleft : (sInf s.1 ∈ s.1) ↔ (sInf t.1 ∈ t.1) := by
        have hbool : decide (sInf s.1 ∈ s.1) = decide (sInf t.1 ∈ t.1) := by
          simpa [intervalCode, hs, ht] using congrArg (fun p => p.2.2.2.1) hcode
        simpa only [decide_eq_decide] using hbool
      have hright : (sSup s.1 ∈ s.1) ↔ (sSup t.1 ∈ t.1) := by
        have hbool : decide (sSup s.1 ∈ s.1) = decide (sSup t.1 ∈ t.1) := by
          simpa [intervalCode, hs, ht] using congrArg (fun p => p.2.2.2.2) hcode
        simpa only [decide_eq_decide] using hbool
      apply Subtype.ext
      exact interval_eq_of_data hs ht
        (bddBelow_def.mpr ⟨0, fun x hx => (s.2.1 hx).1⟩)
        (bddAbove_def.mpr ⟨1, fun x hx => (s.2.1 hx).2⟩)
        (bddBelow_def.mpr ⟨0, fun x hx => (t.2.1 hx).1⟩)
        (bddAbove_def.mpr ⟨1, fun x hx => (t.2.1 hx).2⟩)
        s.2.2.2.ordConnected t.2.2.2.ordConnected hinf hsup hleft hright
    · have htag : true = false := by
        simpa [intervalCode, hs, ht] using congrArg Prod.fst hcode
      contradiction
  · by_cases ht : t.1.Nonempty
    · have htag : false = true := by
        simpa [intervalCode, hs, ht] using congrArg Prod.fst hcode
      contradiction
    · apply Subtype.ext
      exact (Set.not_nonempty_iff_eq_empty.mp hs).trans
        (Set.not_nonempty_iff_eq_empty.mp ht).symm

/-- There are at most continuum many connected subsets of the unit interval. -/
theorem mk_IccConnectedSubsets_le_continuum :
    Cardinal.mk IccConnectedSubsets ≤ Cardinal.continuum := by
  calc
    Cardinal.mk IccConnectedSubsets ≤ Cardinal.mk (Bool × ℝ × ℝ × Bool × Bool) :=
      Cardinal.mk_le_of_injective intervalCode_injective
    _ = Cardinal.continuum := by simp [Cardinal.mk_prod, Cardinal.mk_real]

/-- The closed horizontal unit interval in the plane. -/
def planeInterval : Set Plane := Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)

/-- Projecting a connected subset of the horizontal segment onto the first
coordinate produces a connected subset of the real unit interval. -/
noncomputable def projectConnectedSubset :
    ConnectedSubsets planeInterval → IccConnectedSubsets := fun N =>
  ⟨Prod.fst '' N.1,
    ⟨by
      rintro x ⟨p, hpN, rfl⟩
      exact (N.2.1 hpN).1,
     N.2.2.image Prod.fst continuous_fst.continuousOn⟩⟩

/-- Projection is injective because the segment's second coordinate is zero. -/
lemma projectConnectedSubset_injective : Function.Injective projectConnectedSubset := by
  intro N K h
  apply Subtype.ext
  have himage : Prod.fst '' N.1 = Prod.fst '' K.1 :=
    congrArg (fun S : IccConnectedSubsets => S.1) h
  ext p
  constructor
  · intro hpN
    have hp : p.1 ∈ Prod.fst '' N.1 := ⟨p, hpN, rfl⟩
    rw [himage] at hp
    rcases hp with ⟨q, hqK, hqp⟩
    have hp0 : p.2 = 0 := (N.2.1 hpN).2
    have hq0 : q.2 = 0 := (K.2.1 hqK).2
    have hpq : p = q := by
      apply Prod.ext
      · exact hqp.symm
      · exact hp0.trans hq0.symm
    simpa [hpq] using hqK
  · intro hpK
    have hp : p.1 ∈ Prod.fst '' K.1 := ⟨p, hpK, rfl⟩
    rw [← himage] at hp
    rcases hp with ⟨q, hqN, hqp⟩
    have hp0 : p.2 = 0 := (K.2.1 hpK).2
    have hq0 : q.2 = 0 := (N.2.1 hqN).2
    have hpq : p = q := by
      apply Prod.ext
      · exact hqp.symm
      · exact hp0.trans hq0.symm
    simpa [hpq] using hqN

/-- The horizontal segment has at most continuum many connected subsets. -/
theorem mk_connectedSubsets_planeInterval_le_continuum :
    Cardinal.mk (ConnectedSubsets planeInterval) ≤ Cardinal.continuum := by
  exact (Cardinal.mk_le_of_injective projectConnectedSubset_injective).trans
    mk_IccConnectedSubsets_le_continuum

lemma planeInterval_connected : IsConnected planeInterval := by
  exact (isConnected_Icc (by norm_num)).prod isConnected_singleton

lemma planeInterval_nondegenerate : Nondegenerate planeInterval := by
  intro h
  have h01 := h (show ((0 : ℝ), (0 : ℝ)) ∈ planeInterval by simp [planeInterval])
    (show ((1 : ℝ), (0 : ℝ)) ∈ planeInterval by simp [planeInterval])
  norm_num at h01

/-! Every nondegenerate connected planar set has cardinality at least the
continuum.  The distance from one fixed point has a nondegenerate interval in
its image.  Singleton subsets then give the same lower bound for the family
of connected subsets. -/

/-- A nondegenerate connected subset of the plane has cardinality at least
continuum. -/
theorem continuum_le_mk_connected_plane_set {M : Set Plane}
    (hM : IsConnected M) (hMnon : Nondegenerate M) :
    Cardinal.continuum ≤ Cardinal.mk M := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.mp hMnon
  let f : Plane → ℝ := fun x ↦ dist p x
  have hf : Continuous f := continuous_const.dist continuous_id
  have himage : IsConnected (f '' M) := hM.image f hf.continuousOn
  have hzero : (0 : ℝ) ∈ f '' M := by
    exact ⟨p, hp, by simp [f]⟩
  have hdist : dist p q ∈ f '' M := ⟨q, hq, rfl⟩
  have hinterval : Icc (0 : ℝ) (dist p q) ⊆ f '' M := by
    intro x hx
    exact himage.2.ordConnected.out hzero hdist hx
  calc
    Cardinal.continuum = Cardinal.mk (Icc (0 : ℝ) (dist p q)) := by
      symm
      exact Cardinal.mk_Icc_real (dist_pos.mpr hpq)
    _ ≤ Cardinal.mk (f '' M) := Cardinal.mk_le_mk_of_subset hinterval
    _ ≤ Cardinal.mk M := Cardinal.mk_image_le

/-- Send a point of `M` to its singleton, regarded as a connected subset. -/
def singletonConnectedSubset {M : Set Plane} (x : M) : ConnectedSubsets M :=
  ⟨{x.1}, by
    constructor
    · rintro y (rfl : y = x.1)
      exact x.2
    · exact isConnected_singleton⟩

lemma singletonConnectedSubset_injective {M : Set Plane} :
    Function.Injective (singletonConnectedSubset : M → ConnectedSubsets M) := by
  intro x y hxy
  apply Subtype.ext
  have hsets : ({x.1} : Set Plane) = {y.1} :=
    congrArg (fun N : ConnectedSubsets M ↦ N.1) hxy
  have hxmem : x.1 ∈ ({y.1} : Set Plane) := by
    rw [← hsets]
    exact mem_singleton x.1
  exact mem_singleton_iff.mp hxmem

/-- Every nondegenerate connected planar set has at least continuum many
connected subsets (already among its singleton subsets). -/
theorem continuum_le_mk_connectedSubsets {M : Set Plane}
    (hM : IsConnected M) (hMnon : Nondegenerate M) :
    Cardinal.continuum ≤ Cardinal.mk (ConnectedSubsets M) :=
  (continuum_le_mk_connected_plane_set hM hMnon).trans
    (Cardinal.mk_le_of_injective singletonConnectedSubset_injective)

/-- The horizontal segment has exactly continuum many connected subsets. -/
theorem mk_connectedSubsets_planeInterval_eq_continuum :
    Cardinal.mk (ConnectedSubsets planeInterval) = Cardinal.continuum :=
  le_antisymm mk_connectedSubsets_planeInterval_le_continuum
    (continuum_le_mk_connectedSubsets planeInterval_connected planeInterval_nondegenerate)

/-! The same segment in the coordinate presentation `Fin 2 → ℝ` gives an
exact counterexample to the version quantifying over every `n ≥ 2`. -/

/-- The horizontal segment transported to `Fin 2 → ℝ`. -/
def finTwoInterval : Set (Euclidean 2) :=
  (Homeomorph.finTwoArrow (X := ℝ)) ⁻¹' planeInterval

/-- Transport a connected subset of `finTwoInterval` to the product
presentation of the plane. -/
noncomputable def mapFinTwoConnectedSubset :
    EuclideanConnectedSubsets 2 finTwoInterval → ConnectedSubsets planeInterval := fun N =>
  ⟨(Homeomorph.finTwoArrow (X := ℝ)) '' N.1,
    ⟨by
      rintro _ ⟨x, hx, rfl⟩
      exact N.2.1 hx,
     ((Homeomorph.finTwoArrow (X := ℝ)).isConnected_image.mpr N.2.2)⟩⟩

lemma mapFinTwoConnectedSubset_injective : Function.Injective mapFinTwoConnectedSubset := by
  intro N K h
  apply Subtype.ext
  exact (Homeomorph.finTwoArrow (X := ℝ)).injective.image_injective
    (congrArg (fun S : ConnectedSubsets planeInterval => S.1) h)

lemma finTwoInterval_connected : IsConnected finTwoInterval := by
  rw [finTwoInterval, (Homeomorph.finTwoArrow (X := ℝ)).isConnected_preimage]
  exact planeInterval_connected

lemma finTwoInterval_nondegenerate : Nondegenerate finTwoInterval := by
  intro hsub
  let e := Homeomorph.finTwoArrow (X := ℝ)
  have h0 : e.symm ((0 : ℝ), (0 : ℝ)) ∈ finTwoInterval := by
    simp [finTwoInterval, planeInterval, e]
  have h1 : e.symm ((1 : ℝ), (0 : ℝ)) ∈ finTwoInterval := by
    simp [finTwoInterval, planeInterval, e]
  have heq := hsub h0 h1
  have hpair := congrArg e heq
  simp [e] at hpair

/-- The exact literal modern formulation, quantified over all ambient
dimensions `n ≥ 2`, is false in ZFC. -/
theorem planeInterval_refutes_second_all_dimensions : ¬SecondQuestionAllDimensions := by
  intro hsecond
  have hlt := hsecond 2 (by norm_num) finTwoInterval finTwoInterval_connected
    finTwoInterval_nondegenerate
  have hle : Cardinal.mk (EuclideanConnectedSubsets 2 finTwoInterval) ≤
      Cardinal.continuum :=
    (Cardinal.mk_le_of_injective mapFinTwoConnectedSubset_injective).trans
      mk_connectedSubsets_planeInterval_le_continuum
  exact (not_lt_of_ge hle) hlt

/-! ### Coding countable subsets by sequences -/

/-- A countable set is coded by a sequence of optional elements.  `none`
codes the empty set.  For a nonempty set, `Set.enumerateCountable` enumerates
the set and `some` distinguishes this case from the empty one. -/
noncomputable def countableSetCode {α : Type*} (s : CountableSubsets α) :
    ℕ → Option α := by
  classical
  exact if h : s.1.Nonempty then
      fun n => some (s.1.enumerateCountable s.2 (Classical.choose h) n)
    else
      fun _ => none

/-- Membership in a countable set can be recovered from the range of its
sequence code. -/
lemma some_mem_range_countableSetCode_iff {α : Type*}
    (s : CountableSubsets α) (x : α) :
    some x ∈ Set.range (countableSetCode s) ↔ x ∈ s.1 := by
  by_cases h : s.1.Nonempty
  · rw [countableSetCode, dif_pos h]
    let d : α := Classical.choose h
    have hd : d ∈ s.1 := Classical.choose_spec h
    have hrange : Set.range (s.1.enumerateCountable s.2 d) = s.1 :=
      Set.range_enumerateCountable_of_mem s.2 hd
    constructor
    · rintro ⟨n, hn⟩
      have hx : s.1.enumerateCountable s.2 d n = x := Option.some.inj hn
      rw [← hx]
      exact Set.enumerateCountable_mem s.2 hd n
    · intro hx
      rw [← hrange] at hx
      rcases hx with ⟨n, hn⟩
      exact ⟨n, congrArg some hn⟩
  · have hs : s.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [countableSetCode, hs]

/-- The sequence code for countable sets is injective. -/
lemma countableSetCode_injective {α : Type*} :
    Function.Injective (countableSetCode : CountableSubsets α → ℕ → Option α) := by
  intro s t hst
  apply Subtype.ext
  ext x
  rw [← some_mem_range_countableSetCode_iff s x,
    ← some_mem_range_countableSetCode_iff t x, hst]

/-- The Euclidean plane has cardinality continuum. -/
lemma mk_plane : Cardinal.mk Plane = Cardinal.continuum := by
  simp [Plane, Cardinal.mk_prod, Cardinal.mk_real]

/-- There are at most continuum many countable subsets of the plane. -/
lemma mk_countableSubsets_plane_le :
    Cardinal.mk (CountableSubsets Plane) ≤ Cardinal.continuum := by
  calc
    Cardinal.mk (CountableSubsets Plane)
        ≤ Cardinal.mk (ℕ → Option Plane) :=
      Cardinal.mk_le_of_injective countableSetCode_injective
    _ = Cardinal.continuum := by
      simp only [Cardinal.mk_arrow, Cardinal.mk_option, Cardinal.mk_nat, mk_plane]
      simp only [Cardinal.lift_id]
      have hadd : Cardinal.continuum + (1 : Cardinal) = Cardinal.continuum := by
        simpa using Cardinal.continuum_add_nat 1
      rw [hadd, Cardinal.continuum_power_aleph0]

/-! ### Coding connected subsets of a Rudin witness -/

/-- A connected subset is tagged as degenerate or nondegenerate.  In the
first case it is itself countable; in the second case Rudin's clause says its
complement in `M` is countable. -/
noncomputable def connectedSubsetCode {M : Set Plane}
    (hcount : ∀ N : Set Plane, N ⊆ M → IsConnected N → Nondegenerate N →
      (M \ N).Countable)
    (N : ConnectedSubsets M) : Bool × CountableSubsets Plane := by
  classical
  exact if h : N.1.Subsingleton then
      (false, ⟨N.1, h.countable⟩)
    else
      (true, ⟨M \ N.1, hcount N.1 N.2.1 N.2.2 h⟩)

/-- The tagged connected-subset code is injective. -/
lemma connectedSubsetCode_injective {M : Set Plane}
    (hcount : ∀ N : Set Plane, N ⊆ M → IsConnected N → Nondegenerate N →
      (M \ N).Countable) :
    Function.Injective (connectedSubsetCode hcount) := by
  intro N K hNK
  by_cases hN : N.1.Subsingleton
  · by_cases hK : K.1.Subsingleton
    · apply Subtype.ext
      have hvals := congrArg (fun c : CountableSubsets Plane => c.1)
        (congrArg Prod.snd hNK)
      simpa only [connectedSubsetCode, dif_pos hN, dif_pos hK] using hvals
    · have htags : false = true := by
        simpa only [connectedSubsetCode, dif_pos hN, dif_neg hK] using
          congrArg Prod.fst hNK
      exact Bool.noConfusion htags
  · by_cases hK : K.1.Subsingleton
    · have htags : true = false := by
        simpa only [connectedSubsetCode, dif_neg hN, dif_pos hK] using
          congrArg Prod.fst hNK
      exact Bool.noConfusion htags
    · apply Subtype.ext
      have hdiff : M \ N.1 = M \ K.1 := by
        have hvals := congrArg (fun c : CountableSubsets Plane => c.1)
          (congrArg Prod.snd hNK)
        simpa only [connectedSubsetCode, dif_neg hN, dif_neg hK] using hvals
      ext x
      constructor
      · intro hxN
        have hxM : x ∈ M := N.2.1 hxN
        by_contra hxK
        have hxDiff : x ∈ M \ K.1 := ⟨hxM, hxK⟩
        rw [← hdiff] at hxDiff
        exact hxDiff.2 hxN
      · intro hxK
        have hxM : x ∈ M := K.2.1 hxK
        by_contra hxN
        have hxDiff : x ∈ M \ N.1 := ⟨hxM, hxN⟩
        rw [hdiff] at hxDiff
        exact hxDiff.2 hxK

/-- Rudin's countable-complement property implies that the family of all
connected subsets has cardinality at most continuum. -/
theorem mk_connectedSubsets_le_continuum {M : Set Plane}
    (hcount : ∀ N : Set Plane, N ⊆ M → IsConnected N → Nondegenerate N →
      (M \ N).Countable) :
    Cardinal.mk (ConnectedSubsets M) ≤ Cardinal.continuum := by
  calc
    Cardinal.mk (ConnectedSubsets M)
        ≤ Cardinal.mk (Bool × CountableSubsets Plane) :=
      Cardinal.mk_le_of_injective (connectedSubsetCode_injective hcount)
    _ = 2 * Cardinal.mk (CountableSubsets Plane) := by
      simp [Cardinal.mk_prod]
    _ ≤ 2 * Cardinal.continuum :=
      mul_le_mul_right mk_countableSubsets_plane_le 2
    _ = Cardinal.continuum := Cardinal.nat_mul_continuum (by decide)

/-! ### Consequences for the two questions -/

/-- The literal modern ambient-dimension formulation of the second question
is false in ZFC: a horizontal line segment in the plane has at most continuum
many connected subsets.  This does not address Erdős's stronger 1944
topological-dimension formulation. -/
theorem planeInterval_refutes_second : ¬SecondQuestion := by
  intro hsecond
  have hlt := hsecond planeInterval planeInterval_connected planeInterval_nondegenerate
  exact (not_lt_of_ge mk_connectedSubsets_planeInterval_le_continuum) hlt

/-- A witness having both clauses refutes both universal assertions. -/
theorem fullCounterexample_resolves {M : Set Plane} (hM : FullCounterexample M) :
    ¬FirstQuestion ∧ ¬SecondQuestion := by
  constructor
  · intro hfirst
    rcases hfirst M hM.toRudinCountableComplement.connected
      hM.toRudinCountableComplement.nondegenerate with
      ⟨N, hNM, hNconnected, hNnondegenerate, hnotHomeomorphic⟩
    exact hnotHomeomorphic
      (hM.homeomorphic N hNM hNconnected hNnondegenerate)
  · intro hsecond
    have hlt := hsecond M hM.toRudinCountableComplement.connected
      hM.toRudinCountableComplement.nondegenerate
    exact (not_lt_of_ge
      (mk_connectedSubsets_le_continuum
        hM.toRudinCountableComplement.countable_complement)) hlt

/-- A planar full witness also refutes the first question in its exact form
quantified over every finite Euclidean dimension. -/
theorem fullCounterexample_refutes_first_all_dimensions {M : Set Plane}
    (hM : FullCounterexample M) : ¬FirstQuestionAllDimensions := by
  intro hfirst
  let e := Homeomorph.finTwoArrow (X := ℝ)
  have hpreconn : IsConnected (e ⁻¹' M) :=
    e.isConnected_preimage.mpr hM.toRudinCountableComplement.connected
  have hprenon : Nondegenerate (e ⁻¹' M) :=
    ((Set.not_subsingleton_iff.mp hM.toRudinCountableComplement.nondegenerate).preimage
      e.surjective).not_subsingleton
  rcases hfirst 2 (e ⁻¹' M) hpreconn hprenon with
    ⟨N, hNsub, hNconn, hNnon, hnot⟩
  have himageSub : e '' N ⊆ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNsub hx
  have himageConn : IsConnected (e '' N) := e.isConnected_image.mpr hNconn
  have himageNon : Nondegenerate (e '' N) :=
    ((Set.not_subsingleton_iff.mp hNnon).image e.injective).not_subsingleton
  rcases hM.homeomorphic (e '' N) himageSub himageConn himageNon with ⟨hMN⟩
  let hpreM : (e ⁻¹' M) ≃ₜ M :=
    (e.image (e ⁻¹' M)).trans (Homeomorph.setCongr (e.image_preimage M))
  exact hnot ⟨hpreM.trans hMN |>.trans (e.image N).symm⟩

/-- Exact two-part reduction: a planar witness with the missing
homeomorphism clause settles both universally quantified modern questions. -/
theorem fullCounterexample_resolves_all_dimensions {M : Set Plane}
    (hM : FullCounterexample M) :
    ¬FirstQuestionAllDimensions ∧ ¬SecondQuestionAllDimensions :=
  ⟨fullCounterexample_refutes_first_all_dimensions hM,
    planeInterval_refutes_second_all_dimensions⟩

/-- Knaster--Kuratowski supplies a proper nondegenerate connected candidate
inside a Rudin set, and Rudin's published property makes its complement
countable.  No homeomorphism conclusion follows from these facts alone. -/
theorem rudinCountableComplement_has_proper_candidate {M : Set Plane}
    (hM : RudinCountableComplement M) :
    ∃ N : Set Plane, N ⊂ M ∧ IsConnected N ∧ Nondegenerate N ∧ (M \ N).Countable := by
  obtain ⟨N, hNM, hNconnected, hNnondegenerate⟩ :=
    exists_proper_nondegenerate_connected_subset hM.connected hM.nondegenerate
  exact ⟨N, hNM, hNconnected, hNnondegenerate,
    hM.countable_complement N hNM.subset hNconnected hNnondegenerate⟩

/-- The published Rudin property is sufficient for the cardinality question. -/
theorem rudinCountableComplement_refutes_second {M : Set Plane}
    (hM : RudinCountableComplement M) : ¬SecondQuestion := by
  intro hsecond
  have hlt := hsecond M hM.connected hM.nondegenerate
  exact (not_lt_of_ge
    (mk_connectedSubsets_le_continuum hM.countable_complement)) hlt

/-- Rudin's published countable-complement property determines the number of
connected subsets sharply: it is exactly the continuum. -/
theorem rudinCountableComplement_mk_connectedSubsets_eq {M : Set Plane}
    (hM : RudinCountableComplement M) :
    Cardinal.mk (ConnectedSubsets M) = Cardinal.continuum :=
  le_antisymm (mk_connectedSubsets_le_continuum hM.countable_complement)
    (continuum_le_mk_connectedSubsets hM.connected hM.nondegenerate)

/-- The theorem stated in Rudin's paper, once supplied, gives the historical
CH-conditional negative answer to the planar cardinality question. -/
theorem rudin1958Statement_refutes_second (hRudin : Rudin1958Statement) :
    ContinuumHypothesis → ¬SecondQuestion := by
  intro hCH
  obtain ⟨M, hM⟩ := hRudin hCH
  exact rudinCountableComplement_refutes_second hM

/-! ### Canonical corrected theorem

The modern page conflates Rudin's countable-complement theorem with a
homeomorphism assertion absent from the cited paper, and it replaces
Erdős's topological-dimension hypothesis by an ambient-dimension hypothesis.
The theorem below packages the strongest version proved here without either
overstatement: the first assertion in dimension one, the exact cardinality
of the segment counterexample to the literal modern second assertion, and
the sharp consequences of the property Rudin actually published. -/

/-- Corrected formal resolution of the statements supported by the cited
source and of the literal modern ambient-dimension formulation. -/
theorem not_erdos_910 :
    (∀ m : Set (Euclidean 1), IsConnected m → Nondegenerate m →
      ∃ n : Set (Euclidean 1),
        n ⊆ m ∧ IsConnected n ∧ Nondegenerate n ∧ ¬ Nonempty (m ≃ₜ n)) ∧
    Cardinal.mk (ConnectedSubsets planeInterval) = Cardinal.continuum ∧
    ¬ (∀ n : ℕ, 2 ≤ n → ∀ M : Set (Erdos910.Euclidean n), IsConnected M → Erdos910.Nondegenerate M →
  Cardinal.continuum < Cardinal.mk (Erdos910.EuclideanConnectedSubsets n M)) ∧
    ∀ M : Set Plane, RudinCountableComplement M →
      Cardinal.mk (ConnectedSubsets M) = Cardinal.continuum ∧
      ∃ N : Set Plane,
        N ⊂ M ∧ IsConnected N ∧ Nondegenerate N ∧ (M \ N).Countable := by
  refine ⟨firstQuestion_dimension_one,
    mk_connectedSubsets_planeInterval_eq_continuum,
    planeInterval_refutes_second_all_dimensions, ?_⟩
  intro M hM
  exact ⟨rudinCountableComplement_mk_connectedSubsets_eq hM,
    rudinCountableComplement_has_proper_candidate hM⟩

end

end Erdos910

#print axioms Erdos910.mk_connectedSubsets_le_continuum
#print axioms Erdos910.countable_difference_does_not_force_homeomorphism
#print axioms Erdos910.exists_proper_nondegenerate_connected_subset
#print axioms Erdos910.compact_connected_noncut_has_nonhomeomorphic_subset
#print axioms Erdos910.real_has_nonhomeomorphic_connected_subset
#print axioms Erdos910.firstQuestion_dimension_one
#print axioms Erdos910.planeInterval_refutes_second
#print axioms Erdos910.planeInterval_refutes_second_all_dimensions
#print axioms Erdos910.fullCounterexample_resolves
#print axioms Erdos910.fullCounterexample_refutes_first_all_dimensions
#print axioms Erdos910.fullCounterexample_resolves_all_dimensions
#print axioms Erdos910.rudinCountableComplement_has_proper_candidate
#print axioms Erdos910.rudin1958Statement_refutes_second
#print axioms Erdos910.rudinCountableComplement_mk_connectedSubsets_eq
#print axioms Erdos910.not_erdos_910

alias _root_.Erdos910.erdos_910 := _root_.Erdos910.not_erdos_910
