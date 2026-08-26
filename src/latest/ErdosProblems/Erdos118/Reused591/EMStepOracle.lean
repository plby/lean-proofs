import ErdosProblems.Erdos118.Reused591.K4Core
import ErdosProblems.Erdos118.Reused591.CNFCellK4
import ErdosProblems.Erdos118.Reused591.FixedReindex
import ErdosProblems.Erdos118.Reused591.StrongIteration

namespace Erdos118.Reused591

open Set Ordinal

namespace Erdos591.Schipperus.EMStepOracle

open K4Core
open Erdos591.StrongIteration

universe u v w

theorem large_range {D : Type u} {X : Type v}
    [LinearOrder D] [LinearOrder X] (e : D ↪o X) :
    Large D (Set.range e) := by
  refine ⟨
    { toFun := fun d ↦ ⟨e d, d, rfl⟩
      inj' := by
        intro a b h
        exact e.injective (congrArg Subtype.val h)
      map_rel_iff' := by
        intro a b
        exact e.le_iff_le }⟩

theorem large_of_isEmpty {D : Type u} {X : Type v}
    [LinearOrder D] [LinearOrder X] [IsEmpty D] (s : Set X) :
    Large D s := by
  refine ⟨OrderEmbedding.ofStrictMono (fun d ↦ isEmptyElim d) ?_⟩
  intro d
  exact isEmptyElim d

/-- The image under an order embedding of a bounded initial segment cannot
contain a full copy if bounded initial segments of the domain cannot. -/
theorem embedded_Iic_not_large
    {Y : Type v} {X : Type w}
    [LinearOrder Y] [LinearOrder X]
    (hinit : ∀ a : Y, ¬ Large Y (Set.Iic a))
    (e : Y ↪o X) (a : Y) :
    ¬ Large Y {z : X | z ∈ Set.range e ∧ z ≤ e a} := by
  classical
  rintro ⟨f⟩
  let coord (y : Y) : Y := Classical.choose (f y).2.1
  have hcoord (y : Y) : e (coord y) = (f y : X) :=
    Classical.choose_spec (f y).2.1
  have hcoord_le (y : Y) : coord y ≤ a := by
    rw [← e.le_iff_le, hcoord]
    exact (f y).2.2
  let g : Y ↪o Set.Iic a :=
    { toFun := fun y ↦ ⟨coord y, hcoord_le y⟩
      inj' := by
        intro p q hpq
        apply f.injective
        apply Subtype.ext
        rw [← hcoord p, ← hcoord q]
        exact congrArg e (congrArg Subtype.val hpq)
      map_rel_iff' := by
        intro p q
        change coord p ≤ coord q ↔ p ≤ q
        rw [← e.le_iff_le, hcoord, hcoord]
        exact f.le_iff_le }
  exact hinit a ⟨g⟩

/-- The complete one-step construction needed by `StrongIteration`.

The hypotheses say that the within-block order is finitely indivisible, its
bounded initial segments are small, and every omega-power CNF piece up to the
block-index bound is finitely indivisible. -/
theorem stepOracle_of_k4_core
    {B Y X : Type}
    [LinearOrder B] [WellFoundedLT B]
    [LinearOrder Y] [Nonempty Y]
    [LinearOrder X]
    (kappa : Ordinal)
    (hBtype : typeLT B ≤ ω ^ kappa)
    (hindY : FinitelyIndivisible Y)
    (hindPiece : ∀ {P : Type} [LinearOrder P] [WellFoundedLT P]
      (e : Ordinal), typeLT P = ω ^ e → e ≤ kappa →
        FinitelyIndivisible P)
    (hinit : ∀ a : Y, ¬ Large Y (Set.Iic a))
    (hsmall : ∀ x : X, ¬ Large Y ({x} : Set X))
    (red blue : SimpleGraph X) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set X, red.IsClique s ∧ Large Y s)
    (hnoK4 : blue.CliqueFree 4) :
    StepOracle (B := B) (Y := Y) blue := by
  classical
  intro A F mu hmu
  let L : Set X := Set.range (A.embedding mu)
  let T : B → Set X := fun b ↦ Set.range (A.embedding b)
  have hL : Large Y L := large_range (A.embedding mu)
  have hT : ∀ b, Large Y (T b) := fun b ↦ large_range (A.embedding b)
  have hT_old (b : B) {q : X} (hq : q ∈ T b) :
      ∃ y, q = A.embedding b y := by
    rcases hq with ⟨y, rfl⟩
    exact ⟨y, rfl⟩

  let PEnd : B → X → Prop := fun b x ↦
    Large Y {z | z ∈ T b ∧ red.Adj x z}
  have hbadEnd : ∀ b ∈ F,
      ¬ Large Y {x | x ∈ L ∧ ¬ PEnd b x} := by
    intro b hb
    have hbad := K4Core.one_block_bad_not_large_overlap
      hindY red blue hcompl hnoRed hnoK4 hsmall L (T b) (hT b)
    simpa [PEnd] using hbad
  have hEnd : Large Y
      {x | x ∈ L ∧ ∀ b ∈ F, PEnd b x} :=
    K4Core.large_all_finset hindY L hL PEnd F hbadEnd
  let E : Set X := {x | x ∈ L ∧ ∀ b ∈ F, PEnd b x}

  let PCell : Finset B → X → Prop := fun s x ↦
    typeLT {d : FixedReindex.Cell F s |
      Large Y {z | z ∈ T d.1 ∧ red.Adj x z}} =
        typeLT (FixedReindex.Cell F s)
  have hbadCell : ∀ s ∈ F.powerset,
      ¬ Large Y {x | x ∈ L ∧ ¬ PCell s x} := by
    intro s hs
    have hCellLe : typeLT (FixedReindex.Cell F s) ≤ ω ^ kappa := by
      exact (Ordinal.type_set_le
        {b : B | b ∉ F ∧ FixedReindex.cut F b = s}).trans hBtype
    have hbad := CNFCellK4.cell_bad_not_large_cnf
      kappa hCellLe hindY hindPiece red blue hcompl hnoRed hnoK4 hsmall
      L (fun d : FixedReindex.Cell F s ↦ T d.1)
      (fun d : FixedReindex.Cell F s ↦ hT d.1)
    simpa [PCell] using hbad
  have hbadCellE : ∀ s ∈ F.powerset,
      ¬ Large Y {x | x ∈ E ∧ ¬ PCell s x} := by
    intro s hs hbad
    apply hbadCell s hs
    exact K4Core.Large.mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩) hbad
  have hAll : Large Y
      {x | x ∈ E ∧ ∀ s ∈ F.powerset, PCell s x} :=
    K4Core.large_all_finset hindY E hEnd PCell F.powerset hbadCellE
  rcases hAll.nonempty with ⟨x, hx⟩

  let M : Set B := {b | PEnd b x}
  have hFM : ∀ b ∈ F, b ∈ M := by
    intro b hb
    exact hx.1.2 b hb
  have hlarge : ∀ s : Finset B,
      typeLT (FixedReindex.Cell F s) =
        typeLT (FixedReindex.MCell F M s) := by
    intro s
    by_cases hs : s ∈ F.powerset
    · have hsFull := hx.2 s hs
      change typeLT (FixedReindex.MCell F M s) =
        typeLT (FixedReindex.Cell F s) at hsFull
      exact hsFull.symm
    · have hempty : ¬ Nonempty (FixedReindex.Cell F s) := by
        rintro ⟨d⟩
        apply hs
        rw [Finset.mem_powerset]
        intro b hb
        rw [← d.2.2] at hb
        exact (Finset.mem_filter.mp hb).1
      letI : IsEmpty (FixedReindex.Cell F s) := not_nonempty_iff.mp hempty
      haveI : IsEmpty (FixedReindex.MCell F M s) := inferInstance
      rw [Ordinal.type_eq_zero_of_empty, Ordinal.type_eq_zero_of_empty]
  let g : B ↪o B := FixedReindex.fixedReindex F M hlarge
  have hgfix : ∀ b ∈ F, g b = b := by
    intro b hb
    exact FixedReindex.fixedReindex_fixes F M hlarge hb
  have hgrange : ∀ b, g b ∈ M := by
    intro b
    exact FixedReindex.fixedReindex_range F M hlarge hFM b
  have hgoodg (b : B) :
      Large Y {z : X | z ∈ T (g b) ∧ red.Adj x z} := by
    change PEnd (g b) x
    exact hgrange b
  have hgmu : g mu = mu := hgfix mu hmu
  obtain ⟨a, ha⟩ := hx.1.1
  let Prefix : Set X := {z | z ∈ T mu ∧ z ≤ x}
  have hPrefixSmall : ¬ Large Y Prefix := by
    simpa [Prefix, T, ha] using
      (embedded_Iic_not_large hinit (A.embedding mu) a)
  let R : B → Set X := fun b ↦
    {z | z ∈ T (g b) ∧ red.Adj x z}
  let N : B → Set X := fun b ↦
    if b = mu then R b \ Prefix else R b
  have hN : ∀ b, Large Y (N b) := by
    intro b
    by_cases hb : b = mu
    · subst b
      have hraw : Large Y (R mu) := by
        simpa [R] using hgoodg mu
      have htail := K4Core.Large.diff_of_not_large hindY hraw hPrefixSmall
      simpa [N] using htail
    · simpa [N, R, hb] using hgoodg b
  have hN_T (b : B) {z : X} (hz : z ∈ N b) : z ∈ T (g b) := by
    have hzR : z ∈ R b := by
      by_cases hb : b = mu
      · have : z ∈ R b \ Prefix := by simpa [N, hb] using hz
        exact this.1
      · simpa [N, hb] using hz
    exact hzR.1
  have hN_red (b : B) {z : X} (hz : z ∈ N b) : red.Adj x z := by
    have hzR : z ∈ R b := by
      by_cases hb : b = mu
      · have : z ∈ R b \ Prefix := by simpa [N, hb] using hz
        exact this.1
      · simpa [N, hb] using hz
    exact hzR.2
  let redEmb (b : B) :
      Y ↪o N b := Classical.choice (hN b)
  -- `redEmb` chooses a full within-block copy in the red neighbourhood.
  let nextEmb : B → Y ↪o X := fun b ↦
    redEmb b |>.trans (OrderEmbedding.subtype _)
  have hnext_old : ∀ b y, ∃ z,
      nextEmb b y = A.embedding (g b) z := by
    intro b y
    exact hT_old (g b) (hN_T b (redEmb b y).2)
  let next : BlockFamily B Y X :=
    { embedding := nextEmb
      separated := by
        intro b c hbc y z
        obtain ⟨y', hy'⟩ := hnext_old b y
        obtain ⟨z', hz'⟩ := hnext_old c z
        rw [hy', hz']
        exact A.separated (g.strictMono hbc) y' z' }
  refine ⟨
    { point := x
      reindex := g
      fixes := hgfix
      point_mem := by
        exact ⟨a, ha⟩
      next := next
      next_sub := by
        intro b y
        exact hnext_old b y
      not_adj := by
        intro b y
        intro hb
        have hr := hN_red b (redEmb b y).2
        have hboth : (red ⊓ blue).Adj x (nextEmb b y) := ⟨hr, hb⟩
        rw [hcompl.inf_eq_bot] at hboth
        exact hboth
      point_below := by
        intro y
        change x < nextEmb mu y
        apply lt_of_not_ge
        intro hyx
        have hyN := (redEmb mu y).2
        have hyPrefix : (redEmb mu y : X) ∈ Prefix := by
          exact ⟨by simpa [hgmu] using hN_T mu hyN, hyx⟩
        have hyNotPrefix : (redEmb mu y : X) ∉ Prefix := by
          have : (redEmb mu y : X) ∈ R mu \ Prefix := by
            simpa [N] using hyN
          exact this.2
        exact hyNotPrefix hyPrefix }⟩

end Erdos591.Schipperus.EMStepOracle


end Erdos118.Reused591
