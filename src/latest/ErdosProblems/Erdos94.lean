/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 94.
https://www.erdosproblems.com/forum/thread/94

Informal authors:
- Peter C. Fishburn
- Hanno Lefmann
- Torsten Thiele
- ChatGPT 5.2 Thinking

Formal authors:
- ChatGPT 5.2 Thinking
- Codex
- Li Ding

URLs:
- https://www.erdosproblems.com/forum/thread/94#post-3208
- https://github.com/SpringSense-Innovation-Institute/ai-for-math-lean/blob/main/erdos-problems/erdos94/erdos94.lean
-/
import Mathlib

set_option linter.deprecated false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open scoped BigOperators
open Finset

namespace Erdos94

abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable section

-- Distance set: distances from all ordered pairs in `P.offDiag`.
def DistSet (P : Finset Point) : Finset ℝ :=
  (P.offDiag.image (fun pq => dist pq.1 pq.2))

-- m(u,p): number of other points in P at distance u from p.
def m (P : Finset Point) (u : ℝ) (p : Point) : ℕ :=
  ((P.erase p).filter (fun q => dist p q = u)).card

-- g(u): number of ordered pairs in `P.offDiag` at distance u.
-- NOTE: the original f(u) counts unordered pairs, so g(u) = 2 * f(u).
def g (P : Finset Point) (u : ℝ) : ℕ :=
  ((P.offDiag.filter (fun pq => dist pq.1 pq.2 = u)).card)

-- Distance on unordered pairs (Sym2).
def distSym2 (z : Sym2 Point) : ℝ :=
  Sym2.lift ⟨fun a b => dist a b, by
    intro a b
    simp [dist_comm]⟩ z

@[simp]
lemma distSym2_mk (a b : Point) : distSym2 (Sym2.mk a b) = dist a b := by
  simp [distSym2]

-- f(u): number of unordered, non-diagonal pairs at distance u.
def f (P : Finset Point) (u : ℝ) : ℕ :=
  ((P.sym2.filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)).card)

-- S(P) from the original statement.
def S (P : Finset Point) : ℝ :=
  ∑ u ∈ DistSet P, ((f P u : ℝ)^2)

def BigO_n3 (P : Finset Point) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ S P ≤ C * (P.card : ℝ)^3

syntax "S(" term ")=O(n^3)" : term
macro_rules
  | `(S($P)=O(n^3)) => `(BigO_n3 $P)

-- Ordered isosceles triples: (z,x,y) pairwise distinct with dist z x = dist z y.
def IsoTriples (P : Finset Point) : Finset (Point × Point × Point) :=
  (P.product (P.product P)).filter (fun t =>
    let z := t.1
    let x := t.2.1
    let y := t.2.2
    z ≠ x ∧ z ≠ y ∧ x ≠ y ∧ dist z x = dist z y)

def Δ (P : Finset Point) : ℕ := (IsoTriples P).card

-- General position: no three collinear.
def NoThreeCollinear (P : Finset Point) : Prop :=
  ∀ ⦃x y z : Point⦄, x ∈ P → y ∈ P → z ∈ P →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set Point)

-- Convex position: all points are extreme points of their convex hull.
def ConvexPosition (P : Finset Point) : Prop :=
  (P : Set Point) ⊆ (convexHull ℝ (P : Set Point)).extremePoints ℝ

def GeneralPosition (P : Finset Point) : Prop :=
  ConvexPosition P ∧ NoThreeCollinear P

-- Convex position implies no three collinear (otherwise one point lies on a segment).
theorem convexPosition_noThreeCollinear (P : Finset Point) (hconv : ConvexPosition P) :
    NoThreeCollinear P := by
  intro x y z hx hy hz hxy hyz hxz hcol
  classical
  let E : Set Point := (convexHull ℝ (P : Set Point)).extremePoints ℝ
  have hconvex : Convex ℝ (convexHull ℝ (P : Set Point)) := by
    simpa using (convex_convexHull (𝕜 := ℝ) (s := (P : Set Point)))
  have hci : ConvexIndependent ℝ ((↑) : E → Point) := by
    simpa [E] using
      (Convex.convexIndependent_extremePoints (s := convexHull ℝ (P : Set Point)) hconvex)
  have hci_set : ∀ x ∈ E, x ∉ convexHull ℝ (E \ {x}) := by
    simpa [E] using (convexIndependent_set_iff_notMem_convexHull_diff.mp hci)
  have hxP : x ∈ (P : Set Point) := by simpa using hx
  have hyP : y ∈ (P : Set Point) := by simpa using hy
  have hzP : z ∈ (P : Set Point) := by simpa using hz
  have hxE : x ∈ E := hconv hxP
  have hyE : y ∈ E := hconv hyP
  have hzE : z ∈ E := hconv hzP
  have hsubsetE_diff : ∀ a : Point, (P : Set Point) \ {a} ⊆ E \ {a} := by
    intro a t ht
    exact ⟨hconv ht.1, ht.2⟩
  have hcases := (Collinear.wbtw_or_wbtw_or_wbtw (R := ℝ) (x := x) (y := y) (z := z) hcol)
  rcases hcases with hxyw | hrest
  · have hy_seg : y ∈ segment ℝ x z := hxyw.mem_segment
    have hy_pair : y ∈ convexHull ℝ ({x, z} : Set Point) := by
      simpa [convexHull_pair] using hy_seg
    have hsubset_pair : ({x, z} : Set Point) ⊆ (P : Set Point) \ {y} := by
      intro t ht
      have ht' : t = x ∨ t = z := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
      rcases ht' with rfl | rfl
      · exact ⟨hxP, by simpa [Set.mem_singleton_iff] using hxy⟩
      · exact ⟨hzP, by simpa [Set.mem_singleton_iff] using hyz.symm⟩
    have hy_in : y ∈ convexHull ℝ ((P : Set Point) \ {y}) :=
      (convexHull_mono hsubset_pair) hy_pair
    have hy_inE : y ∈ convexHull ℝ (E \ {y}) :=
      (convexHull_mono (hsubsetE_diff y)) hy_in
    exact (hci_set y hyE) hy_inE
  · rcases hrest with hyzw | hzxy
    · have hz_seg : z ∈ segment ℝ y x := hyzw.mem_segment
      have hz_pair : z ∈ convexHull ℝ ({y, x} : Set Point) := by
        simpa [convexHull_pair, Set.pair_comm] using hz_seg
      have hsubset_pair : ({y, x} : Set Point) ⊆ (P : Set Point) \ {z} := by
        intro t ht
        have ht' : t = y ∨ t = x := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
        rcases ht' with rfl | rfl
        · exact ⟨hyP, by simpa [Set.mem_singleton_iff] using hyz⟩
        · exact ⟨hxP, by simpa [Set.mem_singleton_iff] using hxz⟩
      have hz_in : z ∈ convexHull ℝ ((P : Set Point) \ {z}) :=
        (convexHull_mono hsubset_pair) hz_pair
      have hz_inE : z ∈ convexHull ℝ (E \ {z}) :=
        (convexHull_mono (hsubsetE_diff z)) hz_in
      exact (hci_set z hzE) hz_inE
    · have hx_seg : x ∈ segment ℝ z y := hzxy.mem_segment
      have hx_pair : x ∈ convexHull ℝ ({z, y} : Set Point) := by
        simpa [convexHull_pair, Set.pair_comm] using hx_seg
      have hsubset_pair : ({z, y} : Set Point) ⊆ (P : Set Point) \ {x} := by
        intro t ht
        have ht' : t = z ∨ t = y := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
        rcases ht' with rfl | rfl
        · exact ⟨hzP, by simpa [Set.mem_singleton_iff] using hxz.symm⟩
        · exact ⟨hyP, by simpa [Set.mem_singleton_iff] using hxy.symm⟩
      have hx_in : x ∈ convexHull ℝ ((P : Set Point) \ {x}) :=
        (convexHull_mono hsubset_pair) hx_pair
      have hx_inE : x ∈ convexHull ℝ (E \ {x}) :=
        (convexHull_mono (hsubsetE_diff x)) hx_in
      exact (hci_set x hxE) hx_inE

-- Ordered leg-endpoint pairs for fixed apex p and distance u.
def IsoPairsAt (P : Finset Point) (p : Point) (u : ℝ) : Finset (Point × Point) :=
  ((P.erase p).filter (fun q => dist p q = u)).offDiag

-- Auxiliary geometric property (derived from general position below).
-- For fixed base x ≠ y, there are at most two vertices z with dist z x = dist z y.
def PerpBisectorAtMostTwo (P : Finset Point) : Prop :=
  ∀ ⦃x y : Point⦄, x ∈ P → y ∈ P → x ≠ y →
    ((P.filter (fun z => dist z x = dist z y)).card ≤ 2)

-- The perpendicular bisector is a line: a collinear set in the plane.
lemma perpBisector_collinear (x y : Point) (hxy : x ≠ y) :
    Collinear ℝ ((AffineSubspace.perpBisector x y : AffineSubspace ℝ Point) : Set Point) := by
  classical
  haveI : Fact (Module.finrank ℝ Point = 2) := ⟨by
    simp [finrank_euclideanSpace_fin]⟩
  have hv : (y -ᵥ x : Point) ≠ 0 := by
    intro h
    have hyx : y = x := (vsub_eq_zero_iff_eq).1 h
    exact hxy hyx.symm
  have hdir' : Module.finrank ℝ ((Submodule.span ℝ {y -ᵥ x})ᗮ) = 1 := by
    exact
      (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := Point) (n := 1)
        (v := (y -ᵥ x)) hv)
  have hdir_sub :
      (AffineSubspace.perpBisector x y).direction =
        (Submodule.span ℝ {y -ᵥ x})ᗮ := by
    exact AffineSubspace.direction_perpBisector (p₁ := x) (p₂ := y)
  have hdir_eq :
      Module.finrank ℝ (AffineSubspace.perpBisector x y).direction =
        Module.finrank ℝ ((Submodule.span ℝ {y -ᵥ x})ᗮ) := by
    simpa using
      congrArg (fun s : Submodule ℝ Point => Module.finrank ℝ (s : Type _)) hdir_sub
  have hdir : Module.finrank ℝ (AffineSubspace.perpBisector x y).direction = 1 := by
    calc
      Module.finrank ℝ (AffineSubspace.perpBisector x y).direction
          = Module.finrank ℝ ((Submodule.span ℝ {y - x})ᗮ) := hdir_eq
      _ = 1 := hdir'
  have hspan :
      vectorSpan ℝ ((AffineSubspace.perpBisector x y : AffineSubspace ℝ Point) : Set Point) =
        (AffineSubspace.perpBisector x y).direction := by
    simpa using
      (AffineSubspace.direction_eq_vectorSpan (s := AffineSubspace.perpBisector x y)).symm
  have hfinrank :
      Module.finrank ℝ
        (vectorSpan ℝ ((AffineSubspace.perpBisector x y : AffineSubspace ℝ Point) : Set Point)) ≤ 1 := by
    simpa [hspan] using (le_of_eq hdir)
  exact (collinear_iff_finrank_le_one).2 hfinrank

-- From convex/no-three-collinear to the perpendicular bisector bound (geometric fact).
theorem perpBisectorAtMostTwo_of_general_position (P : Finset Point) :
    GeneralPosition P → PerpBisectorAtMostTwo P := by
  intro hgp x y hx hy hxy
  classical
  have hnc : NoThreeCollinear P := hgp.2
  let s : Finset Point := P.filter (fun z => dist z x = dist z y)
  have hs_mem : ∀ {z}, z ∈ s → z ∈ P := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  by_contra hcard
  have hcard' : 2 < s.card := Nat.lt_of_not_ge hcard
  rcases (Finset.two_lt_card.mp hcard') with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have ha_dist : dist a x = dist a y := (Finset.mem_filter.mp ha).2
  have hb_dist : dist b x = dist b y := (Finset.mem_filter.mp hb).2
  have hc_dist : dist c x = dist c y := (Finset.mem_filter.mp hc).2
  have ha_perp : a ∈ AffineSubspace.perpBisector x y := by
    exact (AffineSubspace.mem_perpBisector_iff_dist_eq).2 ha_dist
  have hb_perp : b ∈ AffineSubspace.perpBisector x y := by
    exact (AffineSubspace.mem_perpBisector_iff_dist_eq).2 hb_dist
  have hc_perp : c ∈ AffineSubspace.perpBisector x y := by
    exact (AffineSubspace.mem_perpBisector_iff_dist_eq).2 hc_dist
  have hsubset :
      ({a, b, c} : Set Point) ⊆
        (AffineSubspace.perpBisector x y : Set Point) := by
    intro z hz
    have hz' : z = a ∨ z = b ∨ z = c := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hz' with rfl | rfl | rfl
    · exact ha_perp
    · exact hb_perp
    · exact hc_perp
  have hcol :
      Collinear ℝ ({a, b, c} : Set Point) := by
    exact (Collinear.subset hsubset (perpBisector_collinear x y hxy))
  have hnot :
      ¬ Collinear ℝ ({a, b, c} : Set Point) :=
    hnc (x := a) (y := b) (z := c) (hs_mem ha) (hs_mem hb) (hs_mem hc) hab hbc hac
  exact hnot hcol

--------------------------------------------------------------------------------
-- The three core lemmas (interfaces).
--------------------------------------------------------------------------------

-- (L1) Double counting: ∑_p m(u,p) = g(u).
lemma sum_m_eq_g (P : Finset Point) (u : ℝ) :
    (∑ p ∈ P, m P u p) = g P u := by
  classical
  let s : Finset (Point × Point) :=
    P.offDiag.filter (fun pq => dist pq.1 pq.2 = u)
  have hsum :
      ∑ p ∈ P, #{pq ∈ s | pq.1 = p} = s.card := by
    -- Fiber counting: stratify by the first coordinate.
    have h :=
      (Finset.sum_card_fiberwise_eq_card_filter
        (s := s) (t := P) (g := fun pq => pq.1))
    -- Right filter is trivial (offDiag ensures pq.1 ∈ P).
    have h' : s.filter (fun pq => pq.1 ∈ P) = s := by
      refine Finset.filter_eq_self.2 ?_
      intro pq hpq
      have hpq' : pq ∈ P.offDiag := (Finset.mem_filter.mp hpq).1
      exact (Finset.mem_offDiag.mp hpq').1
    simpa [h'] using h
  have hfiber :
      ∀ p ∈ P, #{pq ∈ s | pq.1 = p} = m P u p := by
    intro p hp
    let A : Finset Point := (P.erase p).filter (fun q => dist p q = u)
    have hA : A.card = m P u p := by rfl
    have hA_inj : Function.Injective (fun q : Point => (p, q)) := by
      intro q₁ q₂ h
      exact (Prod.mk.inj h).2
    have hA_eq :
        A.image (fun q => (p, q)) = {pq ∈ s | pq.1 = p} := by
      ext pq
      constructor
      · intro hpq
        rcases (Finset.mem_image.mp hpq) with ⟨q, hqA, rfl⟩
        have hqA' : q ∈ P.erase p := (Finset.mem_filter.mp hqA).1
        have hqne : q ≠ p := (Finset.mem_erase.mp hqA').1
        have hqP : q ∈ P := (Finset.mem_erase.mp hqA').2
        have hdist : dist p q = u := (Finset.mem_filter.mp hqA).2
        have hpqmem : (p, q) ∈ s := by
          have hpqne : p ≠ q := by
            simpa [ne_comm] using hqne
          simp [s, Finset.mem_offDiag, hp, hqP, hpqne, hdist]
        exact by
          simp [hpqmem]
      · intro hpq
        have hpqmem : pq ∈ s := (Finset.mem_filter.mp hpq).1
        have hpqeq : pq.1 = p := (Finset.mem_filter.mp hpq).2
        have hpqmem' : pq ∈ P.offDiag := (Finset.mem_filter.mp hpqmem).1
        have hdist : dist pq.1 pq.2 = u := (Finset.mem_filter.mp hpqmem).2
        have hmem : pq.1 ∈ P ∧ pq.2 ∈ P ∧ pq.1 ≠ pq.2 := by
          simp [Finset.mem_offDiag] at hpqmem'
          exact hpqmem'
        have hqP : pq.2 ∈ P := hmem.2.1
        have hqne : pq.2 ≠ p := by
          have hneq : pq.1 ≠ pq.2 := hmem.2.2
          intro hqp
          apply hneq
          simp [hpqeq, hqp]
        have hqerase : pq.2 ∈ P.erase p := by
          simp [Finset.mem_erase, hqP, hqne]
        have hqA : pq.2 ∈ A := by
          have hdist' : dist p pq.2 = u := by
            simp [hpqeq] at hdist
            exact hdist
          simp [A, hqerase, hdist']
        cases pq with
        | mk a b =>
          have hpqeq' : a = p := by simpa using hpqeq
          apply Finset.mem_image.mpr
          refine ⟨b, hqA, ?_⟩
          simp [hpqeq']
    calc
      #{pq ∈ s | pq.1 = p} = #(A.image (fun q => (p, q))) := by
        simp [hA_eq]
      _ = A.card := by
        simpa using (Finset.card_image_of_injective (s := A) (f := fun q => (p, q)) hA_inj)
      _ = m P u p := hA
  calc
    (∑ p ∈ P, m P u p) = ∑ p ∈ P, #{pq ∈ s | pq.1 = p} := by
      refine sum_congr rfl ?_
      intro p hp
      exact (hfiber p hp).symm
    _ = s.card := hsum
    _ = g P u := by
      rfl

-- (L2) Combinatorial identity: ∑_{p,u} m(u,p)^2 = Δ + n(n-1)
--      (Δ counts ordered isosceles triples).
-- TODO: Use fiberwise counting, grouping IsoTriples by (apex, distance).
lemma sum_m_eq_card_erase (P : Finset Point) (p : Point) (hp : p ∈ P) :
    (∑ u ∈ DistSet P, m P u p) = (P.erase p).card := by
  classical
  have h :=
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := P.erase p) (t := DistSet P) (g := fun q => dist p q))
  have h' : (P.erase p).filter (fun q => dist p q ∈ DistSet P) = P.erase p := by
    refine Finset.filter_eq_self.2 ?_
    intro q hq
    have hqP : q ∈ P := (Finset.mem_erase.mp hq).2
    have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
    have hmem : (p, q) ∈ P.offDiag := by
      have hpqne : p ≠ q := by
        exact ne_comm.mp hqne
      exact Finset.mem_offDiag.mpr ⟨hp, hqP, hpqne⟩
    exact mem_image_of_mem (fun pq => dist pq.1 pq.2) hmem
  have h'' :
      (∑ u ∈ DistSet P, m P u p) =
        ((P.erase p).filter (fun q => dist p q ∈ DistSet P)).card := by
    simpa [m] using h
  -- Apply the filtered-sum identity.
  simpa [h'] using h''

lemma isoPairsAt_card (P : Finset Point) (p : Point) (u : ℝ) :
    (IsoPairsAt P p u).card = m P u p * (m P u p - 1) := by
  classical
  let A : Finset Point := (P.erase p).filter (fun q => dist p q = u)
  have h : (IsoPairsAt P p u).card = A.card * A.card - A.card := by
    simp [IsoPairsAt, A]
  have hm : A.card * (A.card - 1) = A.card * A.card - A.card := by
    simpa [Nat.mul_one] using (Nat.mul_sub_left_distrib A.card A.card 1)
  calc
    (IsoPairsAt P p u).card = A.card * A.card - A.card := h
    _ = A.card * (A.card - 1) := hm.symm
    _ = m P u p * (m P u p - 1) := by
          simp [m, A]

lemma delta_eq_sum_isoPairsAt (P : Finset Point) :
    Δ P = ∑ p ∈ P, ∑ u ∈ DistSet P, (IsoPairsAt P p u).card := by
  classical
  let f : (Point × Point × Point) → Point × ℝ := fun t =>
    (t.1, dist t.1 t.2.1)
  have hmap : (IsoTriples P).toSet.MapsTo f (P.product (DistSet P)) := by
    intro t ht
    rcases (Finset.mem_filter.mp ht) with ⟨htprod, hpred⟩
    rcases (Finset.mem_product.mp htprod) with ⟨hzP, ht2⟩
    rcases (Finset.mem_product.mp ht2) with ⟨hxP, hyP⟩
    rcases hpred with ⟨hzx, hzy, hxy, hdist⟩
    have hmem : (t.1, t.2.1) ∈ P.offDiag := by
      exact Finset.mem_offDiag.mpr ⟨hzP, hxP, hzx⟩
    have hdist_mem : dist t.1 t.2.1 ∈ DistSet P := by
      exact mem_image_of_mem (fun pq => dist pq.1 pq.2) hmem
    simp [Finset.mem_product, f, hzP, hdist_mem]
  have h_fiber :=
    (Finset.card_eq_sum_card_fiberwise (s := IsoTriples P)
      (t := P.product (DistSet P)) (f := f) hmap)
  have h_fiber' :
      (IsoTriples P).card =
        ∑ p ∈ P, ∑ u ∈ DistSet P, #{t ∈ IsoTriples P | f t = (p, u)} := by
    simpa [Finset.sum_product] using h_fiber
  have h_fiber_card :
      ∀ p ∈ P, ∀ u ∈ DistSet P,
        #{t ∈ IsoTriples P | f t = (p, u)} = (IsoPairsAt P p u).card := by
    intro p hp u hu
    let g : Point × Point → Point × Point × Point := fun xy => (p, xy.1, xy.2)
    have hg_inj : Function.Injective g := by
      intro x y hxy
      exact (Prod.mk.inj hxy).2
    have h_eq :
        {t ∈ IsoTriples P | f t = (p, u)} = (IsoPairsAt P p u).image g := by
      ext t
      constructor
      · intro ht
        rcases (Finset.mem_filter.mp ht) with ⟨htIso, htft⟩
        have hz : t.1 = p := by
          have := congrArg Prod.fst htft
          simpa [f] using this
        have hdx : dist t.1 t.2.1 = u := by
          have := congrArg Prod.snd htft
          simpa [f] using this
        rcases (Finset.mem_filter.mp htIso) with ⟨htprod, hpred⟩
        rcases (Finset.mem_product.mp htprod) with ⟨hzP, ht2⟩
        rcases (Finset.mem_product.mp ht2) with ⟨hxP, hyP⟩
        rcases hpred with ⟨hzx, hzy, hxy, hdist⟩
        have hxne : t.2.1 ≠ p := by
          have hzx' : t.2.1 ≠ t.1 := ne_comm.mp hzx
          simpa [hz] using hzx'
        have hxerase : t.2.1 ∈ P.erase p := by
          simp [Finset.mem_erase, hxP, hxne]
        have hxA : t.2.1 ∈ (P.erase p).filter (fun q => dist p q = u) := by
          have hdist' : dist p t.2.1 = u := by
            simpa [hz] using hdx
          simp [hxerase, hdist']
        have hyne : t.2.2 ≠ p := by
          have hzy' : t.2.2 ≠ t.1 := ne_comm.mp hzy
          simpa [hz] using hzy'
        have hyerase : t.2.2 ∈ P.erase p := by
          simp [Finset.mem_erase, hyP, hyne]
        have hyA : t.2.2 ∈ (P.erase p).filter (fun q => dist p q = u) := by
          have hdist' : dist t.1 t.2.2 = u := by
            calc
              dist t.1 t.2.2 = dist t.1 t.2.1 := hdist.symm
              _ = u := hdx
          have hdisty : dist p t.2.2 = u := by
            simpa [hz] using hdist'
          simp [hyerase, hdisty]
        have hmem : (t.2.1, t.2.2) ∈ IsoPairsAt P p u := by
          simp [IsoPairsAt, Finset.mem_offDiag, hxA, hyA, hxy]
        apply Finset.mem_image.mpr
        refine ⟨(t.2.1, t.2.2), hmem, ?_⟩
        ext <;> simp [g, hz]
      · intro ht
        rcases (Finset.mem_image.mp ht) with ⟨xy, hxy, rfl⟩
        -- xy ∈ IsoPairsAt P p u
        rcases (by
          simpa [IsoPairsAt, Finset.mem_offDiag] using hxy
        ) with ⟨hxA, hyA, hxy'⟩
        rcases hxA with ⟨⟨hpx, hxP⟩, hdx⟩
        rcases hyA with ⟨⟨hpy, hyP⟩, hdy⟩
        have hpx' : p ≠ xy.1 := by
          exact ne_comm.mp hpx
        have hpy' : p ≠ xy.2 := by
          exact ne_comm.mp hpy
        have hIso : (p, xy.1, xy.2) ∈ IsoTriples P := by
          simp [IsoTriples, hp, hxP, hyP, hpx', hpy', hxy', hdx, hdy]
        have hf : f (p, xy.1, xy.2) = (p, u) := by
          simp [f, hdx]
        simp [g, hIso, hf]
    calc
      #{t ∈ IsoTriples P | f t = (p, u)} =
          ((IsoPairsAt P p u).image g).card := by
            simp [h_eq]
      _ = (IsoPairsAt P p u).card := by
            simpa using
              (Finset.card_image_of_injective (s := IsoPairsAt P p u) (f := g) hg_inj)
  calc
    Δ P = (IsoTriples P).card := rfl
    _ = ∑ p ∈ P, ∑ u ∈ DistSet P, #{t ∈ IsoTriples P | f t = (p, u)} := h_fiber'
    _ = ∑ p ∈ P, ∑ u ∈ DistSet P, (IsoPairsAt P p u).card := by
          refine sum_congr rfl ?_
          intro p hp
          refine sum_congr rfl ?_
          intro u hu
          exact h_fiber_card p hp u hu

lemma sum_sq_m_eq (P : Finset Point) :
    (∑ p ∈ P, ∑ u ∈ DistSet P, ((m P u p : ℝ)^2))
      =
    (Δ P : ℝ) + ((P.card * (P.card - 1)) : ℝ) := by
  classical
  -- First prove in ℕ, then cast to ℝ.
  have h_sum_m :
      ∑ p ∈ P, ∑ u ∈ DistSet P, m P u p = P.card * (P.card - 1) := by
    calc
      ∑ p ∈ P, ∑ u ∈ DistSet P, m P u p
          = ∑ p ∈ P, (P.erase p).card := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              simpa using sum_m_eq_card_erase P p hp
      _ = ∑ p ∈ P, (P.card - 1) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              simpa using (Finset.card_erase_of_mem (s := P) (a := p) hp)
      _ = P.card * (P.card - 1) := by
              simp [Finset.sum_const_nat, Nat.mul_comm]
  have h_delta :
      Δ P = ∑ p ∈ P, ∑ u ∈ DistSet P, m P u p * (m P u p - 1) := by
    calc
      Δ P = ∑ p ∈ P, ∑ u ∈ DistSet P, (IsoPairsAt P p u).card := delta_eq_sum_isoPairsAt P
      _ = ∑ p ∈ P, ∑ u ∈ DistSet P, m P u p * (m P u p - 1) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            refine Finset.sum_congr rfl ?_
            intro u hu
            simpa using isoPairsAt_card P p u
  have h_sq :
      ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p)^2
        =
      ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p * (m P u p - 1) + m P u p) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    refine Finset.sum_congr rfl ?_
    intro u hu
    -- m^2 = m*(m-1) + m, by cases on m.
    set k := m P u p
    cases k with
    | zero =>
        simp [pow_two]
    | succ k =>
        simp [pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have h_nat :
      ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p)^2
        = Δ P + P.card * (P.card - 1) := by
    calc
      ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p)^2
          = ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p * (m P u p - 1) + m P u p) := h_sq
      _ = (∑ p ∈ P, ∑ u ∈ DistSet P, m P u p * (m P u p - 1))
          + (∑ p ∈ P, ∑ u ∈ DistSet P, m P u p) := by
            simp [sum_add_distrib, add_comm, add_left_comm, add_assoc]
      _ = Δ P + P.card * (P.card - 1) := by
            simp [h_delta, h_sum_m]
  -- Cast the ℕ identity to ℝ.
  have h_cast :
      ((∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p)^2 : ℕ) : ℝ)
        = ((Δ P + P.card * (P.card - 1) : ℕ) : ℝ) := by
    exact congrArg (fun x : ℕ => (x : ℝ)) h_nat
  calc
    (∑ p ∈ P, ∑ u ∈ DistSet P, ((m P u p : ℝ)^2))
        =
      ((∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p)^2 : ℕ) : ℝ) := by
        simp [Nat.cast_sum, Nat.cast_pow]
    _ = ((Δ P + P.card * (P.card - 1) : ℕ) : ℝ) := by
        simpa using h_cast
    _ = (Δ P : ℝ) + ((P.card * (P.card - 1)) : ℝ) := by
        -- Avoid rewriting the subtraction inside the cast.
        rw [Nat.cast_add]
        have hmul :
            ((P.card * (P.card - 1) : ℕ) : ℝ) = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
          by_cases hP : P.card = 0
          · simp [hP]
          · have hP' : 1 ≤ P.card := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hP)
            calc
              ((P.card * (P.card - 1) : ℕ) : ℝ)
                  = (P.card : ℝ) * ((P.card - 1 : ℕ) : ℝ) := by
                      simp [Nat.cast_mul]
              _ = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
                      simp [Nat.cast_sub, hP']
        -- Rewrite the product term.
        simp [hmul]

-- (L3) From PerpBisectorAtMostTwo derive Δ ≤ 2*n(n-1).
lemma Δ_le_two_n_n1 (P : Finset Point) (h : PerpBisectorAtMostTwo P) :
    (Δ P : ℝ) ≤ 2 * ((P.card * (P.card - 1)) : ℝ) := by
  classical
  let g : (Point × Point × Point) → (Point × Point) := fun t => (t.2.1, t.2.2)
  have hmap : (IsoTriples P).toSet.MapsTo g (P.offDiag) := by
    intro t ht
    rcases (Finset.mem_filter.mp ht) with ⟨htprod, hpred⟩
    rcases (Finset.mem_product.mp htprod) with ⟨hzP, ht2⟩
    rcases (Finset.mem_product.mp ht2) with ⟨hxP, hyP⟩
    rcases hpred with ⟨hzx, hzy, hxy, hdist⟩
    exact Finset.mem_offDiag.mpr ⟨hxP, hyP, hxy⟩
  have h_fiber :=
    (Finset.card_eq_sum_card_fiberwise (s := IsoTriples P)
      (t := P.offDiag) (f := g) hmap)
  have h_fiber' :
      (IsoTriples P).card =
        ∑ xy ∈ P.offDiag, #{t ∈ IsoTriples P | g t = xy} := by
    simpa using h_fiber
  have h_fiber_le :
      ∀ xy ∈ P.offDiag, #{t ∈ IsoTriples P | g t = xy} ≤ 2 := by
    intro xy hxy
    let F : Finset (Point × Point × Point) :=
      (IsoTriples P).filter (fun t => g t = xy)
    have hF : #{t ∈ IsoTriples P | g t = xy} = F.card := by
      rfl
    have h_inj : Set.InjOn (fun t : Point × Point × Point => t.1) F := by
      intro t1 ht1 t2 ht2 h1
      have ht1' : g t1 = xy := (Finset.mem_filter.mp ht1).2
      have ht2' : g t2 = xy := (Finset.mem_filter.mp ht2).2
      -- t1.2 = xy = t2.2, and t1.1 = t2.1, so t1 = t2.
      have h2 : t1.2 = t2.2 := by
        simpa [g] using ht1'.trans ht2'.symm
      exact Prod.ext h1 h2
    have himg :
        F.image (fun t : Point × Point × Point => t.1) ⊆
          (P.filter (fun z => dist z xy.1 = dist z xy.2)) := by
      intro z hz
      rcases (Finset.mem_image.mp hz) with ⟨t, ht, rfl⟩
      have htIso : t ∈ IsoTriples P := (Finset.mem_filter.mp ht).1
      have htg : g t = xy := (Finset.mem_filter.mp ht).2
      rcases (Finset.mem_filter.mp htIso) with ⟨htprod, hpred⟩
      rcases (Finset.mem_product.mp htprod) with ⟨hzP, ht2⟩
      rcases (Finset.mem_product.mp ht2) with ⟨hxP, hyP⟩
      rcases hpred with ⟨hzx, hzy, hxy', hdist⟩
      have hxy1 : t.2.1 = xy.1 := by
        have := congrArg Prod.fst htg
        simpa [g] using this
      have hxy2 : t.2.2 = xy.2 := by
        have := congrArg Prod.snd htg
        simpa [g] using this
      have hdist' : dist t.1 xy.1 = dist t.1 xy.2 := by
        simpa [hxy1, hxy2] using hdist
      simp [hzP, hdist']
    have hcard_le :
        F.card ≤ (P.filter (fun z => dist z xy.1 = dist z xy.2)).card := by
      have hcard_eq :
          F.card = (F.image (fun t : Point × Point × Point => t.1)).card := by
        symm
        exact Finset.card_image_of_injOn (s := F) (f := fun t => t.1) h_inj
      calc
        F.card = (F.image (fun t : Point × Point × Point => t.1)).card := hcard_eq
        _ ≤ (P.filter (fun z => dist z xy.1 = dist z xy.2)).card := by
              exact Finset.card_le_card himg
    have hperp : (P.filter (fun z => dist z xy.1 = dist z xy.2)).card ≤ 2 := by
      have hxP : xy.1 ∈ P := (Finset.mem_offDiag.mp hxy).1
      have hyP : xy.2 ∈ P := (Finset.mem_offDiag.mp hxy).2.1
      have hxy' : xy.1 ≠ xy.2 := (Finset.mem_offDiag.mp hxy).2.2
      exact h hxP hyP hxy'
    exact (hF ▸ (hcard_le.trans hperp))
  have hsum_le :
      (IsoTriples P).card ≤ 2 * P.offDiag.card := by
    calc
      (IsoTriples P).card
          = ∑ xy ∈ P.offDiag, #{t ∈ IsoTriples P | g t = xy} := h_fiber'
      _ ≤ ∑ _ ∈ P.offDiag, 2 := by
            refine Finset.sum_le_sum ?_
            intro xy hxy
            exact h_fiber_le xy hxy
      _ = 2 * P.offDiag.card := by
            simp [Finset.sum_const_nat, Nat.mul_comm]
  have h_offdiag : P.offDiag.card = P.card * (P.card - 1) := by
    have h' := Finset.offDiag_card (s := P)
    have hm : P.card * (P.card - 1) = P.card * P.card - P.card := by
      simpa [Nat.mul_one] using (Nat.mul_sub_left_distrib P.card P.card 1)
    exact h'.trans hm.symm
  have hnat : (IsoTriples P).card ≤ 2 * (P.card * (P.card - 1)) := by
    -- Rewrite using h_offdiag.
    simpa [h_offdiag] using hsum_le
  -- Cast to ℝ without expanding the subtraction.
  have hcast : (Δ P : ℝ) ≤ ((2 * (P.card * (P.card - 1)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  set n : ℕ := P.card * (P.card - 1)
  have hcast' : (Δ P : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    simpa [n] using hcast
  have hmul : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
    simp [Nat.cast_mul]
  have hmul2 :
      ((P.card * (P.card - 1) : ℕ) : ℝ) = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    by_cases hP : P.card = 0
    · simp [hP]
    · have hP' : 1 ≤ P.card := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hP)
      calc
        ((P.card * (P.card - 1) : ℕ) : ℝ)
            = (P.card : ℝ) * ((P.card - 1 : ℕ) : ℝ) := by
                simp [Nat.cast_mul]
        _ = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
                simp [Nat.cast_sub, hP']
  calc
    (Δ P : ℝ) ≤ ((2 * n : ℕ) : ℝ) := hcast'
    _ = 2 * (n : ℝ) := hmul
    _ = 2 * ((P.card * (P.card - 1)) : ℝ) := by
          dsimp [n]
          simp [hmul2]

-- Relation between ordered and unordered pair counts.
lemma g_eq_two_f (P : Finset Point) (u : ℝ) : g P u = 2 * f P u := by
  classical
  let s : Finset (Point × Point) :=
    P.offDiag.filter (fun pq => dist pq.1 pq.2 = u)
  let t : Finset (Sym2 Point) :=
    P.sym2.filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)
  have hmap : (s : Set (Point × Point)).MapsTo (fun pq => Sym2.mk pq.1 pq.2) t := by
    intro pq hpq
    have hpq' : pq ∈ P.offDiag := (Finset.mem_filter.mp hpq).1
    have hdist : dist pq.1 pq.2 = u := (Finset.mem_filter.mp hpq).2
    have hp : pq.1 ∈ P := (Finset.mem_offDiag.mp hpq').1
    have hq : pq.2 ∈ P := (Finset.mem_offDiag.mp hpq').2.1
    have hneq : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp hpq').2.2
    have hmem : Sym2.mk pq.1 pq.2 ∈ P.sym2 := by
      refine (Finset.mem_sym2_iff).2 ?_
      intro a ha
      rcases (Sym2.mem_iff.mp ha) with rfl | rfl
      · exact hp
      · exact hq
    have hdiag : ¬ Sym2.IsDiag (Sym2.mk pq.1 pq.2) := by
      simpa [Sym2.mk_isDiag_iff] using hneq
    have hdist' : distSym2 (Sym2.mk pq.1 pq.2) = u := by
      simp [distSym2_mk, hdist]
    exact Finset.mem_filter.mpr ⟨hmem, And.intro hdiag hdist'⟩
  have h_fiber :=
    (Finset.card_eq_sum_card_fiberwise (s := s) (t := t)
      (f := fun pq => Sym2.mk pq.1 pq.2) hmap)
  have h_fiber_card :
      ∀ z ∈ t, #{pq ∈ s | Sym2.mk pq.1 pq.2 = z} = 2 := by
    intro z hz
    revert hz
    refine Sym2.ind ?_ z
    intro a b hz'
    rcases (Finset.mem_filter.mp hz') with ⟨hzsym, hzpred⟩
    have hab : a ≠ b := by
      have : ¬ Sym2.IsDiag (Sym2.mk a b) := hzpred.1
      simpa [Sym2.mk_isDiag_iff] using this
    have hdist : dist a b = u := by
      simpa [distSym2_mk] using hzpred.2
    have ha : a ∈ P := (Finset.mk_mem_sym2_iff.mp hzsym).1
    have hb : b ∈ P := (Finset.mk_mem_sym2_iff.mp hzsym).2
    have hpair :
        {pq ∈ s | pq = (a, b) ∨ pq = (b, a)} = {(a, b), (b, a)} := by
      ext pq
      constructor
      · intro hpq
        rcases (Finset.mem_filter.mp hpq) with ⟨hpq_s, hpq_eq⟩
        rcases hpq_eq with hpq_eq | hpq_eq
        · simp [hpq_eq]
        · simp [hpq_eq]
      · intro hpq
        have hpq' : pq = (a, b) ∨ pq = (b, a) := by
          simpa using hpq
        rcases hpq' with rfl | rfl
        · have hmem : (a, b) ∈ s := by
            simp [s, Finset.mem_offDiag, ha, hb, hab, hdist]
          simp [hmem]
        · have hmem : (b, a) ∈ s := by
            have hdist' : dist b a = u := by simpa [dist_comm] using hdist
            have hne : b ≠ a := ne_comm.mp hab
            simp [s, Finset.mem_offDiag, hb, ha, hne, hdist']
          simp [hmem]
    have hpair' :
        {pq ∈ s | Sym2.mk pq.1 pq.2 = Sym2.mk a b} =
          {pq ∈ s | pq = (a, b) ∨ pq = (b, a)} := by
      ext pq
      constructor
      · intro hpq
        rcases (Finset.mem_filter.mp hpq) with ⟨hpq_s, hpq_eq⟩
        rcases ((Sym2.mk_eq_mk_iff (p := pq) (q := (a, b))).mp hpq_eq) with hpq_eq | hpq_eq
        · exact Finset.mem_filter.mpr ⟨hpq_s, Or.inl hpq_eq⟩
        · exact Finset.mem_filter.mpr ⟨hpq_s, Or.inr hpq_eq⟩
      · intro hpq
        rcases (Finset.mem_filter.mp hpq) with ⟨hpq_s, hpq_eq⟩
        rcases hpq_eq with hpq_eq | hpq_eq
        · exact Finset.mem_filter.mpr
            ⟨hpq_s, ((Sym2.mk_eq_mk_iff (p := pq) (q := (a, b))).mpr (Or.inl hpq_eq))⟩
        · exact Finset.mem_filter.mpr
            ⟨hpq_s, ((Sym2.mk_eq_mk_iff (p := pq) (q := (a, b))).mpr (Or.inr hpq_eq))⟩
    have hcard : #{pq ∈ s | Sym2.mk pq.1 pq.2 = Sym2.mk a b} = 2 := by
      calc
        #{pq ∈ s | Sym2.mk pq.1 pq.2 = Sym2.mk a b}
            = ({pq ∈ s | pq = (a, b) ∨ pq = (b, a)} : Finset (Point × Point)).card := by
                rw [hpair']
        _ = ({(a, b), (b, a)} : Finset (Point × Point)).card := by
                simp [hpair]
        _ = 2 := by
              simp [hab]
    simpa using hcard
  have hcard :
      s.card = ∑ z ∈ t, 2 := by
    calc
      s.card = ∑ z ∈ t, #{pq ∈ s | Sym2.mk pq.1 pq.2 = z} := h_fiber
      _ = ∑ z ∈ t, 2 := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            exact h_fiber_card z hz
  have hsum : ∑ z ∈ t, 2 = 2 * t.card := by
    simp [Finset.sum_const_nat, Nat.mul_comm]
  have hs : g P u = s.card := by rfl
  have ht : f P u = t.card := by rfl
  calc
    g P u = s.card := hs
    _ = ∑ z ∈ t, 2 := hcard
    _ = 2 * t.card := hsum
    _ = 2 * f P u := by simp [ht]

-- Main theorem: S(P) = O(n^3) with an explicit constant.
theorem erdos94 (P : Finset Point) (h : PerpBisectorAtMostTwo P) :
    S P ≤ (3 / 4 : ℝ) * (P.card : ℝ)^2 * ((P.card : ℝ) - 1) := by
  classical
  -- Cauchy–Schwarz on each distance level.
  have h_cauchy :
      ∀ u, (g P u : ℝ)^2 ≤ (P.card : ℝ) * (∑ p ∈ P, (m P u p : ℝ)^2) := by
    intro u
    have hsum : (∑ p ∈ P, (m P u p : ℝ)) = g P u := by
      exact_mod_cast (sum_m_eq_g P u)
    have hcs :=
      (sq_sum_le_card_mul_sum_sq (s := P) (f := fun p => (m P u p : ℝ)))
    simpa [hsum] using hcs
  have hsumg :
      ∑ u ∈ DistSet P, (g P u : ℝ)^2 ≤
        ∑ u ∈ DistSet P, (P.card : ℝ) * (∑ p ∈ P, (m P u p : ℝ)^2) := by
    refine Finset.sum_le_sum ?_
    intro u hu
    exact h_cauchy u
  have hsumg' :
      ∑ u ∈ DistSet P, (g P u : ℝ)^2 ≤
        (P.card : ℝ) * ∑ u ∈ DistSet P, ∑ p ∈ P, (m P u p : ℝ)^2 := by
    refine (le_trans hsumg ?_)
    have h' :
        ∑ u ∈ DistSet P, (P.card : ℝ) * (∑ p ∈ P, (m P u p : ℝ)^2)
          = (P.card : ℝ) * ∑ u ∈ DistSet P, ∑ p ∈ P, (m P u p : ℝ)^2 := by
        simp [mul_sum]
    exact le_of_eq h'
  have hsum_m2 :
      ∑ u ∈ DistSet P, ∑ p ∈ P, (m P u p : ℝ)^2 =
        ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p : ℝ)^2 := by
    simpa using (sum_comm (s := DistSet P) (t := P)
      (f := fun u p => (m P u p : ℝ)^2))
  have hsumg'' :
      ∑ u ∈ DistSet P, (g P u : ℝ)^2 ≤
        (P.card : ℝ) * ((Δ P : ℝ) + (P.card * (P.card - 1) : ℝ)) := by
    calc
      ∑ u ∈ DistSet P, (g P u : ℝ)^2
          ≤ (P.card : ℝ) * ∑ u ∈ DistSet P, ∑ p ∈ P, (m P u p : ℝ)^2 := hsumg'
      _ = (P.card : ℝ) * ∑ p ∈ P, ∑ u ∈ DistSet P, (m P u p : ℝ)^2 := by
            simp [hsum_m2]
      _ = (P.card : ℝ) * ((Δ P : ℝ) + (P.card * (P.card - 1) : ℝ)) := by
            simp [sum_sq_m_eq, add_assoc, add_left_comm, add_comm]
  have hDelta : (Δ P : ℝ) ≤ 2 * ((P.card * (P.card - 1)) : ℝ) :=
    Δ_le_two_n_n1 P h
  have hsumg_final :
      ∑ u ∈ DistSet P, (g P u : ℝ)^2 ≤
        3 * (P.card : ℝ) * (P.card * (P.card - 1) : ℝ) := by
    have := hsumg''
    nlinarith [hDelta]
  -- Relate g and f, then finish.
  have hgf :
      ∀ u, (g P u : ℝ)^2 = 4 * (f P u : ℝ)^2 := by
    intro u
    have h' : (g P u : ℝ) = (2 : ℝ) * (f P u : ℝ) := by
      have h0 := congrArg (fun n : ℕ => (n : ℝ)) (g_eq_two_f P u)
      simpa [Nat.cast_mul, mul_comm] using h0
    nlinarith [h']
  have hS :
      S P = (1 / 4 : ℝ) * ∑ u ∈ DistSet P, (g P u : ℝ)^2 := by
    unfold S
    simp [hgf, mul_sum, mul_comm, mul_left_comm, mul_assoc]
  calc
    S P = (1 / 4 : ℝ) * ∑ u ∈ DistSet P, (g P u : ℝ)^2 := hS
    _ ≤ (1 / 4 : ℝ) * (3 * (P.card : ℝ) * (P.card * (P.card - 1) : ℝ)) := by
          nlinarith [hsumg_final]
    _ = (3 / 4 : ℝ) * (P.card : ℝ)^2 * ((P.card : ℝ) - 1) := by
          ring

-- Main theorem with the geometric hypothesis derived from general position.
theorem erdos94_general_position (P : Finset Point) (hgp : GeneralPosition P) :
    S P ≤ (3 / 4 : ℝ) * (P.card : ℝ)^2 * ((P.card : ℝ) - 1) := by
  have hperp : PerpBisectorAtMostTwo P := perpBisectorAtMostTwo_of_general_position P hgp
  exact erdos94 P hperp

-- Convenience wrapper combining convex + no-three-collinear into GeneralPosition.
theorem erdos94_convex_no3collinear (P : Finset Point)
    (hconv : ConvexPosition P) (hnc : NoThreeCollinear P) :
    S P ≤ (3 / 4 : ℝ) * (P.card : ℝ)^2 * ((P.card : ℝ) - 1) := by
  exact erdos94_general_position P ⟨hconv, hnc⟩

-- Big-O form with an explicit constant.
theorem erdos94_bigO (P : Finset Point) (h : PerpBisectorAtMostTwo P) :
    ∃ C : ℝ, 0 ≤ C ∧ S P ≤ C * (P.card : ℝ)^3 := by
  refine ⟨(3 / 4 : ℝ), by nlinarith, ?_⟩
  have hmain := erdos94 P h
  by_cases h0 : P.card = 0
  · simp [S, h0] at hmain
    simpa [S, h0] using hmain
  · have hpos : (1 : ℝ) ≤ (P.card : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h0))
    have hle : (P.card : ℝ) - 1 ≤ (P.card : ℝ) := by nlinarith
    have hpow :
        (P.card : ℝ)^2 * ((P.card : ℝ) - 1) ≤ (P.card : ℝ)^3 := by
      have hnonneg : 0 ≤ (P.card : ℝ)^2 := by nlinarith
      calc
        (P.card : ℝ)^2 * ((P.card : ℝ) - 1)
            ≤ (P.card : ℝ)^2 * (P.card : ℝ) := by
                exact mul_le_mul_of_nonneg_left hle hnonneg
        _ = (P.card : ℝ)^3 := by
                ring
    nlinarith [hmain, hpow]

-- Big-O form with convex/no-three-collinear premise (via GeneralPosition).
theorem erdos94_bigO_general_position (P : Finset Point) (hgp : GeneralPosition P) :
    S(P)=O(n^3) := by
  have hperp : PerpBisectorAtMostTwo P :=
    perpBisectorAtMostTwo_of_general_position P hgp
  simpa using (erdos94_bigO P hperp)

-- Convenience wrapper combining convex + no-three-collinear into GeneralPosition.
theorem erdos94_bigO_convex_no3collinear (P : Finset Point)
    (hconv : ConvexPosition P) (hnc : NoThreeCollinear P) :
    S(P)=O(n^3) := by
  exact erdos94_bigO_general_position P ⟨hconv, hnc⟩

#print axioms erdos94_convex_no3collinear
-- 'Erdos94.erdos94_convex_no3collinear' depends on axioms: [propext, Classical.choice, Quot.sound]

end
end Erdos94
