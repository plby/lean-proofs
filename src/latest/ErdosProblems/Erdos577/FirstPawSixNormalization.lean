import ErdosProblems.Erdos577.FirstPawSixCaseUpper
import ErdosProblems.Erdos577.FirstPawSixNormalizationModel
import ErdosProblems.Erdos577.LocalChainSupport

/-! Transport the two case reductions to actual feasible chains, retaining every outside block. -/

namespace Erdos577.FirstPawSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma normalization_data (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q) (second : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (NormalizationModel.source second)))
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    ∃ (l : LocalChain G (p.support ∪ q.support)) (p' : Paw G) (q' : Quadrilateral G),
      p'.support = l.remainder ∧ q'.support = l.block ∧ PawBlock.OnlyFirst q' ∧
      PawBlock.ExactRows p' q' (caseRows (NormalizationModel.target second)) := by
  classical
  let f := CaseModel.copy p q hd hdiag.1 (NormalizationModel.source second) hrows
  let p' := (NormalizationModel.paw second).image f
  let q' : Quadrilateral G := f.comp (NormalizationModel.quad second)
  let l := ((NormalizationModel.chain second).image f).withSupport
    (CaseModel.copy_image p q hd hdiag.1 (NormalizationModel.source second) hrows)
  have hp' : p'.support = l.remainder := by
    rw [Paw.image_support, Paw.support_eq, image_insert]
    rfl
  have hq' : q'.support = l.block := Quadrilateral.support_copy_comp _ _
  refine ⟨l, p', q', hp', hq', ?_, ?_⟩
  · refine ⟨f.toHom.map_rel' (NormalizationModel.only_first second).1, ?_⟩
    intro hlow
    exact (NormalizationModel.only_first second).2
      (CaseModel.adj_upper p q hd hdiag _ hrows hleaf _ _ hlow)
  · intro i j
    exact (CaseModel.adj_iff p q hd hdiag _ hrows hleaf _ _).trans
      (NormalizationModel.exact_rows second i j)

variable [Fintype V] [DecidableRel G.Adj]

theorem exists_normalized_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (second : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (NormalizationModel.source second))) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G), d.Feasible ∧
      p'.support = d.remainder ∧ q'.support ∈ d.blocks ∧ Disjoint p'.support q'.support ∧
      PawBlock.OnlyFirst q' ∧
      PawBlock.ExactRows p' q' (caseRows (NormalizationModel.target second)) ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  obtain ⟨l₀, p', q', hp', hq', hdiag', hrows'⟩ :=
    normalization_data p q hd hdiag second hrows (c.paw_nonadjacent hcard hn p hp)
  let l := l₀.withSupport (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let d := c.replaceBlock b hb l
  have hscore : edgeCount G q'.support = edgeCount G q.support := by
    rw [q'.edgeCount_eq, q.edgeCount_eq, if_pos hdiag'.1, if_neg hdiag'.2,
      if_pos hdiag.1, if_neg hdiag.2]
  have hdf : d.Feasible := hc.replaceBlock_feasible hb l
    ((congrArg (edgeCount G) hq').symm.trans (hscore.trans (congrArg (edgeCount G) hq)))
  refine ⟨d, p', q', hdf, hp', mem_union_right _ (mem_singleton.mpr hq'),
    ?_, hdiag', hrows', ?_⟩
  · rw [hp', hq']
    exact l₀.disjoint
  · intro a ha hab
    exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

end Erdos577.FirstPawSix
