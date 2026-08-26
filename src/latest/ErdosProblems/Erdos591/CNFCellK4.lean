import ErdosProblems.Erdos591.CNFStrong
import ErdosProblems.Erdos591.K4Core

open Set Ordinal

namespace Erdos591.Schipperus.CNFCellK4

open K4Core

theorem large_inter_of_large_subtype
    {D : Type*} [LinearOrder D]
    (p m : Set D)
    (h : Large p {q : p | q.1 ∈ m}) :
    Large p (m ∩ p) := by
  rcases h with ⟨e⟩
  refine ⟨
    { toFun := fun d ↦ ⟨(e d).1.1, (e d).2, (e d).1.2⟩
      inj' := by
        intro a b hab
        have hv : (e a).1.1 = (e b).1.1 :=
          congrArg (fun z : (m ∩ p : Set D) ↦ (z : D)) hab
        apply e.injective
        apply Subtype.ext
        exact Subtype.ext hv
      map_rel_iff' := by
        intro a b
        exact e.le_iff_le }⟩

/-- CNF-piece refinement of the K4 bad-locus lemma.  It does not assume
that the whole index order `D` is finitely indivisible: it partitions `D`
into finitely many omega-power pieces and applies `bad_not_large` on each. -/
theorem cell_bad_not_large_cnf
    {D Y X : Type}
    [LinearOrder D] [WellFoundedLT D]
    [LinearOrder Y] [Nonempty Y]
    [LinearOrder X]
    (kappa : Ordinal)
    (hDle : typeLT D ≤ ω ^ kappa)
    (hindY : FinitelyIndivisible Y)
    (hindPiece : ∀ {P : Type} [LinearOrder P] [WellFoundedLT P]
      (e : Ordinal), typeLT P = ω ^ e → e ≤ kappa →
        FinitelyIndivisible P)
    (red blue : SimpleGraph X) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set X, red.IsClique s ∧ Large Y s)
    (hnoK4 : blue.CliqueFree 4)
    (hsmall : ∀ x : X, ¬ Large Y ({x} : Set X))
    (A : Set X)
    (block : D → Set X) (hblock : ∀ d, Large Y (block d)) :
    ¬ Large Y {x | x ∈ A ∧
      typeLT {d : D | Large Y {z | z ∈ block d ∧ red.Adj x z}} ≠
        typeLT D} := by
  classical
  obtain ⟨pieces, hcon, hunion, hpower, hreconstruct⟩ :=
    CNFStrong.exists_omegaPowerPartition_reconstruct D
  let Bad : Set X := {x | x ∈ A ∧
    typeLT {d : D | Large Y {z | z ∈ block d ∧ red.Adj x z}} ≠
      typeLT D}
  intro hBad
  have hpieceBad : ∀ p ∈ pieces.toFinset,
      ¬ Large Y {x | x ∈ Bad ∧
        ¬ Large p {d : p |
          Large Y {z | z ∈ block d.1 ∧ red.Adj x z}}} := by
    intro p hp
    have hpList : p ∈ pieces := List.mem_toFinset.mp hp
    obtain ⟨e, hpe⟩ : ∃ e : Ordinal, typeLT p = ω ^ e :=
      (hpower p hpList : CNFStrong.IsOmegaPowerType p)
    have hpNonempty : Nonempty p := by
      apply (@Ordinal.type_ne_zero_iff_nonempty p (· < ·) inferInstance).mp
      rw [hpe]
      exact Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero
    letI : Nonempty p := hpNonempty
    have he : e ≤ kappa :=
      CNFStrong.omegaPower_exponent_le_of_ambient hpe hDle
    exact K4Core.bad_not_large_overlap hindY (hindPiece e hpe he)
      red blue hcompl hnoRed hnoK4 hsmall Bad
      (fun d : p ↦ block d.1) (fun d ↦ hblock d.1)
  let PieceGood : Set D → X → Prop := fun p x ↦
    Large p {d : p | Large Y {z | z ∈ block d.1 ∧ red.Adj x z}}
  have hAll : Large Y
      {x | x ∈ Bad ∧ ∀ p ∈ pieces.toFinset, PieceGood p x} :=
    K4Core.large_all_finset hindY Bad hBad PieceGood
      pieces.toFinset hpieceBad
  rcases hAll.nonempty with ⟨x, hx⟩
  let m : Set D :=
    {d | Large Y {z | z ∈ block d ∧ red.Adj x z}}
  have hfull : ∀ p : Set D, p ∈ pieces →
      typeLT (↑(m ∩ p : Set D)) = typeLT (↑p) := by
    intro p hp
    have hlargeP := hx.2 p (List.mem_toFinset.mpr hp)
    change Large p {d : p | d.1 ∈ m} at hlargeP
    rcases large_inter_of_large_subtype p m hlargeP with ⟨e⟩
    apply le_antisymm
    · let incl : (↑(m ∩ p : Set D)) ↪o (↑p) :=
        { toFun := fun d ↦ ⟨d.1, d.2.2⟩
          inj' := by
            intro a b hab
            apply Subtype.ext
            exact congrArg (fun z : p ↦ (z : D)) hab
          map_rel_iff' := by intro a b; rfl }
      exact incl.ltEmbedding.ordinal_type_le
    · exact e.ltEmbedding.ordinal_type_le
  exact hx.1.2 (hreconstruct m hfull)

end Erdos591.Schipperus.CNFCellK4
