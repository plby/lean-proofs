import ErdosProblems.Erdos599.LadderFrontierInvariants
import ErdosProblems.Erdos599.LadderSuccessorSelfRoof

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u}

/-- A finite essential member of a roof-maximal wave stays essential after
adjoining one vertex outside the wave.  Full source coverage is not needed:
the wave's cut property already roofs every initial vertex needed by the
arrow comparison. -/
theorem essential_terminal_insert_of_roofMaximal_wave
    (Q : DWeb V) {W : Set Q.DPath} (hW : Q.IsWave W)
    (hmax : ∀ U : Set Q.DPath, Q.IsWave U → Q.RoofLE U W)
    {r : Q.DPath} (hrW : r ∈ W) {z y : V}
    (hrz : Q.terminal? r = some z)
    (hrEss : r ∈ Q.essentialWarpPart W)
    (hyReach : y ∈ Q.reachableToTarget)
    (hyOutside : y ∉ Q.vertexSet W) :
    z ∈ Q.essential (Q.terminalFrontier W ∪ {y}) := by
  let T : Set V := Q.terminalFrontier W
  have hzT : z ∈ T := ⟨r, hrW, hrz⟩
  have hzEssT : z ∈ Q.essential T := by
    obtain ⟨_, t, hrt, ht⟩ := hrEss
    have htz : t = z := Option.some.inj (hrt.symm.trans hrz)
    exact htz ▸ ht
  have hyNotT : y ∉ T := by
    intro hyT
    obtain ⟨s, hsW, hsy⟩ := hyT
    exact hyOutside ⟨s, hsW, Q.terminal_mem_support hsy⟩
  have hyne : y ≠ z := by
    intro hyz
    exact hyNotT (hyz ▸ hzT)
  refine ⟨Or.inl hzT, ?_⟩
  intro hzRoof
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Q.not_mem_roof_iff (T \ {z}) z).1 hzEssT.2
  have hpstart : p.start = z := hpTarget.1
  have hpMeetY : Q.Meets p {y} := by
    have hmeet := hzRoof p hpTarget
    obtain ⟨x, hxp, hx⟩ := hmeet
    have hxy : x = y := by
      rcases hx.1 with hxT | hxy
      · exact False.elim
          (Set.disjoint_left.1 hpAvoid hxp ⟨hxT, hx.2⟩)
      · simpa using hxy
    exact ⟨y, by simpa [hxy] using hxp, Set.mem_singleton y⟩
  have hyp : y ∈ p.support := by
    obtain ⟨x, hxp, hx⟩ := hpMeetY
    have hxy : x = y := by simpa using hx
    exact hxy ▸ hxp
  have hyNotRoofT : y ∉ Q.roof T := by
    apply RelationalRoof.not_mem_roof_of_later_mem_targetPath
      Q.graph.Adj Q.target p hpTarget
    · intro x hxp hxT
      exact Set.disjoint_left.1 hpAvoid hxp (by simpa [hpstart] using hxT)
    · exact hyp
    · exact fun hyz' ↦ hyne (hyz'.trans hpstart)
  let s : DirectedPath.FinitePath Q.graph := p.firstHit {y} hpMeetY
  have hsstart : s.start = z := by
    change p.start = z
    exact hpstart
  have hsfinish : s.finish = y := by
    exact Set.mem_singleton_iff.1 (p.firstHit_finish_mem {y} hpMeetY)
  have hsAvoid : Q.Avoids s (T \ {z}) := by
    apply Set.disjoint_left.2
    intro x hxs hxT
    exact Set.disjoint_left.1 hpAvoid
      (p.firstHit_support_subset {y} hpMeetY hxs) hxT
  let C : Set Q.DPath :=
    ({(Sum.inl s : Q.DPath)} : Set Q.DPath) ∪
      Q.trivialPath '' (T \ {z})
  have hCwarp : Q.IsWarp C := by
    apply Set.PairwiseDisjoint.union
    · exact Set.pairwiseDisjoint_singleton _ _
    · exact Q.isWarp_trivialPaths _
    · intro q hq q' hq' _hne
      have hqs : q = (Sum.inl s : Q.DPath) := by simpa using hq
      obtain ⟨x, hxT, rfl⟩ := hq'
      subst q
      rw [Q.support_trivialPath]
      apply Set.disjoint_singleton_right.2
      intro hxs
      exact Set.disjoint_left.1 hsAvoid hxs hxT
  have hCinitial : Q.initialSet C = T := by
    rw [Q.initialSet_union, Q.initialSet_trivialPaths]
    have hsingle : Q.initialSet ({(Sum.inl s : Q.DPath)} : Set Q.DPath) =
        {z} := by
      ext x
      simp only [Q.mem_initialSet, Set.mem_singleton_iff]
      constructor
      · rintro ⟨q, rfl, hqx⟩
        exact hqx.symm.trans hsstart
      · rintro rfl
        exact ⟨Sum.inl s, rfl, hsstart⟩
    rw [hsingle]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff]
    constructor
    · rintro (rfl | ⟨hxT, _⟩)
      · exact hzT
      · exact hxT
    · intro hxT
      by_cases hxz : x = z
      · exact Or.inl hxz
      · exact Or.inr ⟨hxT, hxz⟩
  have hCterminal : Q.terminalFrontier C = (T \ {z}) ∪ {y} := by
    rw [Q.terminalFrontier_union, Q.terminalFrontier_trivialPaths]
    have hsingle : Q.terminalFrontier
        ({(Sum.inl s : Q.DPath)} : Set Q.DPath) = {y} := by
      ext x
      simp only [Q.mem_terminalFrontier, Set.mem_singleton_iff]
      constructor
      · rintro ⟨q, rfl, hqx⟩
        exact Option.some.inj (hqx.symm.trans (by simp [hsfinish]))
      · rintro rfl
        exact ⟨Sum.inl s, rfl, by simp [hsfinish]⟩
    rw [hsingle, Set.union_comm]
  have hTsub : T ⊆ Q.roof ((T \ {z}) ∪ {y}) := by
    intro x hxT
    by_cases hxz : x = z
    · subst x
      have heq : (T ∪ {y}) \ {z} = (T \ {z}) ∪ {y} := by
        ext v
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
        aesop
      change z ∈ Q.roof ((T ∪ {y}) \ {z}) at hzRoof
      rwa [heq] at hzRoof
    · exact Q.subset_roof _ (Or.inl ⟨hxT, hxz⟩)
  have hCwave : ({ graph := Q.graph, source := T, target := Q.target } : DWeb V).IsWave C := by
    refine ⟨hCwarp, ?_, ?_⟩
    · change Q.initialSet C ⊆ T
      rw [hCinitial]
    · change T ⊆ Q.roof (Q.terminalFrontier C)
      rw [hCterminal]
      exact hTsub
  let R : Set Q.DPath := Q.arrow W C
  have hWself : Q.vertexSet W ⊆ Q.roof T := hW.self_roofing
  have hCself : Q.vertexSet C ⊆ Q.roof (Q.terminalFrontier C) := by
    exact hCwave.self_roofing
  have hUroof : Q.initialSet (W ∪ C) ⊆ Q.roof T := by
    rw [Q.initialSet_union, hCinitial]
    exact Set.union_subset (hW.2.1.trans hW.2.2) (Q.subset_roof T)
  have hVroof : Q.initialSet (W ∪ C) ⊆
      Q.roof (Q.terminalFrontier C) := by
    rw [Q.initialSet_union, hCinitial]
    exact Set.union_subset
      (hW.2.1.trans (hW.2.2.trans (Q.roof_cut hCwave.2.2))) hCwave.2.2
  have hRroof : Q.roof (Q.terminalFrontier R) =
      Q.roof (T ∪ Q.terminalFrontier C) := by
    exact Q.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
      hW.1 hCwarp hWself hCself hUroof hVroof
  have hRwave : Q.IsWave R := by
    refine ⟨Q.isWarp_arrow hW.1 hCwarp, ?_, ?_⟩
    · rw [← Q.initialSet_eq_of_forwardExtension (Q.forwardExtension_arrow W C)]
      exact hW.2.1
    · rw [hRroof]
      exact hW.2.2.trans (Q.roof_mono Set.subset_union_left)
  have hyEssUnion : y ∈ Q.essential (T ∪ Q.terminalFrontier C) := by
    refine ⟨Or.inr ?_, ?_⟩
    · rw [hCterminal]
      exact Or.inr rfl
    · have hsimp : (T ∪ Q.terminalFrontier C) \ {y} = T := by
        rw [hCterminal]
        ext x
        simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hx, hxne⟩
          rcases hx with hxT | hxT | hxy
          · exact hxT
          · exact hxT.1
          · exact (hxne hxy).elim
        · intro hxT
          exact ⟨Or.inl hxT, fun hxy ↦ hyNotT (hxy ▸ hxT)⟩
      simpa only [hsimp] using hyNotRoofT
  have hyRterm : y ∈ Q.terminalFrontier R := by
    apply Q.essential_union_subset_terminalFrontier_arrow_of_crossRoof
      hW.1 hCwarp hWself hCself hUroof
    exact hyEssUnion
  have hyRoofW : y ∈ Q.roof T :=
    hmax R hRwave (Q.subset_roof _ hyRterm)
  exact hyNotRoofT hyRoofW

/-- Full-wave specialization retained for callers that already have source
equality. -/
theorem essential_terminal_insert_of_roofMaximal
    (Q : DWeb V) {W : Set Q.DPath} (hW : Q.IsWave W)
    (_hfull : Q.initialSet W = Q.source)
    (hmax : ∀ U : Set Q.DPath, Q.IsWave U → Q.RoofLE U W)
    {r : Q.DPath} (hrW : r ∈ W) {z y : V}
    (hrz : Q.terminal? r = some z)
    (hrEss : r ∈ Q.essentialWarpPart W)
    (hyReach : y ∈ Q.reachableToTarget)
    (hyOutside : y ∉ Q.vertexSet W) :
    z ∈ Q.essential (Q.terminalFrontier W ∪ {y}) :=
  essential_terminal_insert_of_roofMaximal_wave Q hW hmax hrW hrz
    hrEss hyReach hyOutside

/-- Every vertex of a finite path in an essential quotient stage stays in
the vertex region of the underlying quotient, provided its initial vertex
does. -/
theorem essentialQuotientFinitePath_support_subset_quotientVertexSet
    (G : DWeb V) (X : Set V)
    (p : DirectedPath.FinitePath (G.quotient X).essentialPart.graph)
    (hstart : p.start ∈ G.quotientVertexSet X) :
    p.support ⊆ G.quotientVertexSet X := by
  have hwalk : ∀ {a b : V}
      (w : DirectedPath.Walk (G.quotient X).essentialPart.graph a b),
      a ∈ G.quotientVertexSet X →
      ∀ {x}, x ∈ w.support → x ∈ G.quotientVertexSet X := by
    intro a b w ha x hx
    induction w with
    | nil =>
        simp only [DirectedPath.Walk.support_nil, List.mem_singleton] at hx
        subst x
        exact ha
    | @cons a c b e w ih =>
        simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact ih
            ((G.quotient_adj_endpoints
              ((G.quotient X).essentialPart_adj_imp e)).2.1) hx
  exact fun x hx ↦ hwalk p.walk hstart hx

/-- Essentiality in the stage web transports to the full successor
frontier once every extra successor terminal is old strict-roof noise.
The witness target path is lifted through the essential part and quotient;
quotient-vertex membership makes it avoid that noise. -/
theorem stageEssential_mem_successorEssential_of_terminal_noise
    (G : DWeb V) (X T M S : Set V)
    {z : V}
    (hcore : T ∪ M ⊆ S)
    (hnoise : S ⊆ (T ∪ M) ∪ G.strictRoof X)
    (hzSurvives : z ∈ G.quotientVertexSet X)
    (hz : z ∈ (G.quotient X).essentialPart.essential (T ∪ M)) :
    z ∈ G.essential S := by
  refine ⟨hcore hz.1, ?_⟩
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    ((G.quotient X).essentialPart.not_mem_roof_iff
      ((T ∪ M) \ {z}) z).1 hz.2
  let pQ : DirectedPath.FinitePath (G.quotient X).graph :=
    p.lift (G.quotient X).essentialPart_adj_imp
  let pG : DirectedPath.FinitePath G.graph :=
    pQ.lift (fun {_ _} e ↦ G.quotient_adj_imp e)
  apply (G.not_mem_roof_iff (S \ {z}) z).2
  refine ⟨pG, ⟨hpTarget.1, hpTarget.2⟩, ?_⟩
  apply Set.disjoint_left.2
  intro x hxp hxS
  have hxpStage : x ∈ p.support := by
    simpa only [pG, pQ, DirectedPath.FinitePath.support_lift] using hxp
  rcases hnoise hxS.1 with hxCore | hxStrict
  · exact Set.disjoint_left.1 hpAvoid hxpStage ⟨hxCore, hxS.2⟩
  · have hxSurvives : x ∈ G.quotientVertexSet X :=
      G.essentialQuotientFinitePath_support_subset_quotientVertexSet X p
        (by rw [hpTarget.1]; exact hzSurvives) hxpStage
    exact hxSurvives hxStrict

end DWeb
end Erdos599
