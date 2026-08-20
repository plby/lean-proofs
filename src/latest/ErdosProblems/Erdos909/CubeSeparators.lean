/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.ProjIcc
import ErdosProblems.Erdos909.External.Econlib.Brouwer

open Set Topology

namespace Erdos909.CubeSeparators

/-- The closed `n`-cube.  This is deliberately the same presentation used by
the vendored Econlib proof of Brouwer's fixed-point theorem. -/
abbrev Cube (n : ℕ) := Set.Icc (0 : Fin n → ℝ) 1

def lowerFace {n : ℕ} (i : Fin n) : Set (Cube n) := {x | x.1 i = 0}

def upperFace {n : ℕ} (i : Fin n) : Set (Cube n) := {x | x.1 i = 1}

/-- A formulation of Poincare--Miranda on the product cube which does not commit
to any particular proof (degree, Brouwer, or cubical Sperner). -/
def PoincareMiranda (n : ℕ) : Prop :=
  ∀ f : Cube n → (Fin n → ℝ), Continuous f →
    (∀ i x, x ∈ lowerFace i → f x i ≤ 0) →
    (∀ i x, x ∈ upperFace i → 0 ≤ f x i) →
    ∃ x, ∀ i, f x i = 0

private lemma projIcc_eq_interior_iff {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (Set.projIcc 0 1 zero_le_one y : ℝ) = x ↔ y = x := by
  constructor
  · intro h
    by_cases hy0 : y ≤ 0
    · rw [Set.projIcc_of_le_left zero_le_one hy0] at h
      norm_num at h
      linarith
    by_cases hy1 : 1 ≤ y
    · rw [Set.projIcc_of_right_le zero_le_one hy1] at h
      norm_num at h
      linarith
    · have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_ge hy0, le_of_not_ge hy1⟩
      simpa [Set.projIcc_of_mem zero_le_one hy] using h
  · intro hyx
    subst y
    rw [Set.projIcc_of_mem zero_le_one ⟨hx0.le, hx1.le⟩]

/-- The exact Brouwer-to-Poincare--Miranda reduction.  The premise is the
fixed-point theorem in precisely the form supplied by Econlib's
`fixedPointUnitCube`. -/
theorem poincareMiranda_of_fixedPointUnitCube {n : ℕ}
    (brouwer : ∀ g : C(Cube n, Cube n), ∃ x, g x = x) : PoincareMiranda n := by
  intro f hf hlo hhi
  let g : Cube n → Cube n := fun x ↦
    ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (x.1 i - f x i) : ℝ),
      ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (x.1 i - f x i)).2.1,
       fun i ↦ (Set.projIcc 0 1 zero_le_one (x.1 i - f x i)).2.2⟩⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    rw [continuous_pi_iff]
    intro i
    exact continuous_subtype_val.comp (continuous_projIcc.comp
      (((continuous_apply i).comp continuous_subtype_val).sub
        ((continuous_apply i).comp hf)))
  obtain ⟨x, hx⟩ := brouwer ⟨g, hg⟩
  refine ⟨x, fun i ↦ ?_⟩
  have hfix : (Set.projIcc 0 1 zero_le_one (x.1 i - f x i) : ℝ) = x.1 i := by
    exact congr_fun (congrArg Subtype.val hx) i
  rcases lt_trichotomy (x.1 i) 0 with hneg | hzero | hpos
  · exact False.elim (not_lt_of_ge (x.2.1 i) hneg)
  · have hf_le : f x i ≤ 0 := hlo i x (by simpa [lowerFace] using hzero)
    have harg : x.1 i - f x i ≤ 0 := by
      have hz : (Set.projIcc 0 1 zero_le_one (x.1 i - f x i) : ℝ) = 0 :=
        hfix.trans hzero
      have := (Set.projIcc_eq_left zero_lt_one).1 (Subtype.ext hz)
      exact this
    linarith
  · rcases lt_trichotomy (x.1 i) 1 with hlt | hone | hgt
    · have heq := (projIcc_eq_interior_iff hpos hlt).1 hfix
      linarith
    · have hf_ge : 0 ≤ f x i := hhi i x (by simpa [upperFace] using hone)
      have harg : 1 ≤ x.1 i - f x i := by
        have hz : (Set.projIcc 0 1 zero_le_one (x.1 i - f x i) : ℝ) = 1 :=
          hfix.trans hone
        have := (Set.projIcc_eq_right zero_lt_one).1 (Subtype.ext hz)
        exact this
      linarith
    · exact False.elim (not_lt_of_ge (x.2.2 i) hgt)

/-- Poincare--Miranda, instantiated with the fully proved cubical Sperner/Brouwer
development vendored from Econlib. -/
theorem poincareMiranda (n : ℕ) : PoincareMiranda n :=
  poincareMiranda_of_fixedPointUnitCube fixedPointUnitCube

/-- `L` separates the two faces normal to coordinate `i`: its complement is
the union of two disjoint relatively open sets containing the faces. -/
def SeparatesFaces {n : ℕ} (i : Fin n) (L : Set (Cube n)) : Prop :=
  ∃ U V : Set (Cube n), IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
    U ∪ V = Lᶜ ∧ lowerFace i ⊆ U ∧ upperFace i ⊆ V

private lemma lowerFace_nonempty {n : ℕ} (i : Fin n) :
    (lowerFace i).Nonempty := by
  let x : Cube n := ⟨0, by constructor <;> simp⟩
  exact ⟨x, by simp [lowerFace, x]⟩

private lemma upperFace_nonempty {n : ℕ} (i : Fin n) :
    (upperFace i).Nonempty := by
  let x : Cube n := ⟨1, by constructor <;> simp⟩
  exact ⟨x, by simp [upperFace, x]⟩

private lemma signedDistance_continuous {X : Type*} [PseudoMetricSpace X]
    (U V : Set X) :
    Continuous (fun x ↦ Metric.infDist x Vᶜ - Metric.infDist x Uᶜ) :=
  (Metric.continuous_infDist_pt Vᶜ).sub (Metric.continuous_infDist_pt Uᶜ)

private lemma signedDistance_neg_of_mem_left {X : Type*} [MetricSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hUc : Uᶜ.Nonempty) {x : X} (hx : x ∈ U) :
    Metric.infDist x Vᶜ - Metric.infDist x Uᶜ < 0 := by
  have hxVc : x ∈ Vᶜ := by
    exact fun hxV ↦ Set.disjoint_left.1 hUV hx hxV
  rw [Metric.infDist_zero_of_mem hxVc]
  have hpos : 0 < Metric.infDist x Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (by simpa using hx)
  linarith

private lemma signedDistance_pos_of_mem_right {X : Type*} [MetricSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hVc : Vᶜ.Nonempty) {x : X} (hx : x ∈ V) :
    0 < Metric.infDist x Vᶜ - Metric.infDist x Uᶜ := by
  have hxUc : x ∈ Uᶜ := by
    exact fun hxU ↦ Set.disjoint_left.1 hUV hxU hx
  rw [Metric.infDist_zero_of_mem hxUc]
  have hpos : 0 < Metric.infDist x Vᶜ :=
    (hV.isClosed_compl.notMem_iff_infDist_pos hVc).1 (by simpa using hx)
  linarith

private lemma signedDistance_zero_mem_separator {X : Type*} [MetricSpace X]
    {L U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (hUc : Uᶜ.Nonempty) (hVc : Vᶜ.Nonempty)
    {x : X} (hx : Metric.infDist x Vᶜ - Metric.infDist x Uᶜ = 0) : x ∈ L := by
  by_contra hxL
  have hxUV : x ∈ U ∪ V := by simpa [hcover] using hxL
  rcases hxUV with hxU | hxV
  · have := signedDistance_neg_of_mem_left hU hV hUV hUc hxU
    linarith
  · have := signedDistance_pos_of_mem_right hU hV hUV hVc hxV
    linarith

/-- Poincare--Miranda implies the standard partition-intersection theorem:
one separator for every coordinate direction has a common point. -/
theorem iInter_separators_nonempty {n : ℕ} (hPM : PoincareMiranda n)
    (L : Fin n → Set (Cube n)) (hL : ∀ i, SeparatesFaces i (L i)) :
    (⋂ i, L i).Nonempty := by
  choose U V hU hV hUV hcover hlower hupper using hL
  have hUc : ∀ i, (U i)ᶜ.Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := upperFace_nonempty i
    exact ⟨x, fun hxU ↦ Set.disjoint_left.1 (hUV i) hxU (hupper i hx)⟩
  have hVc : ∀ i, (V i)ᶜ.Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := lowerFace_nonempty i
    exact ⟨x, fun hxV ↦ Set.disjoint_left.1 (hUV i) (hlower i hx) hxV⟩
  let f : Cube n → (Fin n → ℝ) := fun x i ↦
    Metric.infDist x (V i)ᶜ - Metric.infDist x (U i)ᶜ
  have hf : Continuous f := by
    rw [continuous_pi_iff]
    exact fun i ↦ signedDistance_continuous (U i) (V i)
  have hflo : ∀ i x, x ∈ lowerFace i → f x i ≤ 0 := by
    intro i x hx
    exact (signedDistance_neg_of_mem_left (hU i) (hV i) (hUV i) (hUc i)
      (hlower i hx)).le
  have hfhi : ∀ i x, x ∈ upperFace i → 0 ≤ f x i := by
    intro i x hx
    exact (signedDistance_pos_of_mem_right (hU i) (hV i) (hUV i) (hVc i)
      (hupper i hx)).le
  obtain ⟨x, hx⟩ := hPM f hf hflo hfhi
  refine ⟨x, Set.mem_iInter.2 fun i ↦ ?_⟩
  exact signedDistance_zero_mem_separator (hU i) (hV i) (hUV i) (hcover i)
    (hUc i) (hVc i) (hx i)

/-- A finite-cover consequence of the partition-intersection theorem.  If one
can choose, for each coordinate, a *different* member of a family which
contains a separator in that coordinate, then some point belongs to at least
`n` members of the family.  The conclusion is stated as an embedding so it
does not require the indexing type to be finite. -/
theorem exists_point_with_n_cover_members {n : ℕ} (hPM : PoincareMiranda n)
    {I : Type*} (C : I → Set (Cube n)) (j : Fin n → I) (hj : Function.Injective j)
    (L : Fin n → Set (Cube n)) (hL : ∀ i, SeparatesFaces i (L i))
    (hsub : ∀ i, L i ⊆ C (j i)) :
    ∃ x, Nonempty (Fin n ↪ {a : I // x ∈ C a}) := by
  obtain ⟨x, hx⟩ := iInter_separators_nonempty hPM L hL
  have hxL : ∀ i, x ∈ L i := Set.mem_iInter.1 hx
  refine ⟨x, ⟨⟨fun i ↦ ⟨j i, hsub i (hxL i)⟩, ?_⟩⟩⟩
  intro i k hik
  exact hj (congrArg Subtype.val hik)

/-- The same cover consequence expressed as the number of members containing
the common point.  `Finite I` is enough; no decidable membership predicate is
needed because `Nat.card` is noncomputable. -/
theorem exists_point_cover_natCard_ge {n : ℕ} (hPM : PoincareMiranda n)
    {I : Type*} [Finite I] (C : I → Set (Cube n))
    (j : Fin n → I) (hj : Function.Injective j)
    (L : Fin n → Set (Cube n)) (hL : ∀ i, SeparatesFaces i (L i))
    (hsub : ∀ i, L i ⊆ C (j i)) :
    ∃ x, n ≤ Nat.card {a : I // x ∈ C a} := by
  obtain ⟨x, hx⟩ := iInter_separators_nonempty hPM L hL
  have hxL : ∀ i, x ∈ L i := Set.mem_iInter.1 hx
  refine ⟨x, ?_⟩
  simpa using Nat.card_le_card_of_injective
    (fun i ↦ ⟨j i, hsub i (hxL i)⟩)
    (fun i k hik ↦ hj (congrArg Subtype.val hik))

end Erdos909.CubeSeparators
