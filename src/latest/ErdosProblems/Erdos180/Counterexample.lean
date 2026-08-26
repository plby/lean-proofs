/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Coordinates

set_option linter.mathlibStandardSet false

namespace Erdos180

section JQuotientAvoidanceReduction

open SimpleGraph

lemma jQuotient_free_of_template_avoidance
    {V : Type*} (host : SimpleGraph V)
    (havoid : ∀ hom : jTemplate →g host,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (quotientGraph jTemplate f).Free host := by
  rintro ⟨copy⟩
  let hom : jTemplate →g host :=
    copy.toHom.comp (jQuotientProjectionHom hf)
  apply havoid hom
  · intro first second heq
    change
      copy (⟨f (.inl (.inl first)),
        .inl (.inl first), rfl⟩ : Set.range f) =
        copy (⟨f (.inl (.inl second)),
          .inl (.inl second), rfl⟩ : Set.range f)
      at heq
    apply hf.2.1
    exact congrArg Subtype.val (copy.injective heq)
  · intro index first hfirst second hsecond heq
    change
      copy (⟨f first, first, rfl⟩ : Set.range f) =
        copy (⟨f second, second, rfl⟩ : Set.range f)
      at heq
    apply hf.2.2 index hfirst hsecond
    exact congrArg Subtype.val (copy.injective heq)

theorem symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance
    (K : Type*) [Field K]
    (havoid : ∀ hom : jTemplate →g symplecticQuadrangle K,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) := by
  exact
    (symplecticQuadrangle_encodeFiniteGraph_free_iff K
      (quotientGraph jTemplate f)).mpr
      (jQuotient_free_of_template_avoidance
        (symplecticQuadrangle K) havoid hf)

end JQuotientAvoidanceReduction

section JTemplateLineAvoidanceReduction

open SimpleGraph

variable (K : Type*) [Field K]

def CharTwoLinePairAvoidance : Prop :=
  ∀ (Y Z X X' : SymplecticLine K),
    Disjoint Y.1 Z.1 →
    Disjoint X.1 Y.1 →
    Disjoint X.1 Z.1 →
    Disjoint X'.1 Y.1 →
    Disjoint X'.1 Z.1 →
    X ≠ X' →
    ∀ (C C' : Fin 2 → SymplecticLine K),
      Function.Injective C →
      Function.Injective C' →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) →
      Disjoint X.1 X'.1

theorem symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    (havoid : CharTwoLinePairAvoidance K)
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun i : Fin 4 => hom (.inl (.inl i))))
    (hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v | InJCopy i v}) :
    False := by
  classical
  let θ (i : Fin 2) := jThetaHomCopy hom hcopies i
  obtain ⟨X, hX⟩ :=
    symplecticQuadrangle_jTemplate_first_base_is_line
      K hom hbase_inj hcopies
  have hθ0X :
      θ 0 (.inl (.inl (0 : Fin 3))) = .inr X := by
    change
      hom (jThetaVertex 0 (.inl (.inl (0 : Fin 3)))) =
        .inr X
    simpa [jThetaVertex, jBase] using hX
  obtain ⟨Y, hθ0Y⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (1 : Fin 3)) (0 : Fin 2) hθ0X
  have hY :
      hom (.inl (.inl (2 : Fin 4))) = .inr Y := by
    change
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) =
        .inr Y at hθ0Y
    simpa [jThetaVertex, jBase] using hθ0Y
  obtain ⟨Z, hθ0Z⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (2 : Fin 3)) (0 : Fin 2) hθ0X
  have hZ :
      hom (.inl (.inl (3 : Fin 4))) = .inr Z := by
    change
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) =
        .inr Z at hθ0Z
    simpa [jThetaVertex, jBase] using hθ0Z
  have hθ1Y :
      θ 1 (.inl (.inl (1 : Fin 3))) = .inr Y := by
    change
      hom (jThetaVertex 1 (.inl (.inl (1 : Fin 3)))) =
        .inr Y
    simpa [jThetaVertex, jBase] using hY
  obtain ⟨X', hθ1X'⟩ :=
    subdivisionLine_base_of_line_base K (θ 1)
      (otherBase := (0 : Fin 3)) (0 : Fin 2) hθ1Y
  have hX' :
      hom (.inl (.inl (1 : Fin 4))) = .inr X' := by
    change
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) =
        .inr X' at hθ1X'
    simpa [jThetaVertex, jBase] using hθ1X'
  let B : Fin 3 → SymplecticLine K := ![X, Y, Z]
  let B' : Fin 3 → SymplecticLine K := ![X', Y, Z]
  have hθ1Z :
      θ 1 (.inl (.inl (2 : Fin 3))) = .inr Z := by
    change
      hom (jThetaVertex 1 (.inl (.inl (2 : Fin 3)))) =
        .inr Z
    simpa [jThetaVertex, jBase] using hZ
  have hB : ∀ i : Fin 3,
      θ 0 (.inl (.inl i)) = .inr (B i) := by
    intro i
    fin_cases i
    · simpa [B] using hθ0X
    · simpa [B] using hθ0Y
    · simpa [B] using hθ0Z
  have hB' : ∀ i : Fin 3,
      θ 1 (.inl (.inl i)) = .inr (B' i) := by
    intro i
    fin_cases i
    · simpa [B'] using hθ1X'
    · simpa [B'] using hθ1Y
    · simpa [B'] using hθ1Z
  have hC_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 0 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 0)
      (base := (0 : Fin 3)) (center := i) (hB 0)
  choose C hC using hC_exists
  have hC'_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 1 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 1)
      (base := (0 : Fin 3)) (center := i) (hB' 0)
  choose C' hC' using hC'_exists
  have hXX' : X ≠ X' := by
    intro heq
    have hbaseeq : (0 : Fin 4) = 1 := by
      apply hbase_inj
      change
        hom (.inl (.inl (0 : Fin 4))) =
          hom (.inl (.inl (1 : Fin 4)))
      rw [hX, hX', heq]
    exact (by decide : (0 : Fin 4) ≠ 1) hbaseeq
  have hYZ : Disjoint Y.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (1 : Fin 3) ≠ 2) (0 : Fin 2)
  have hXY : Disjoint X.1 Y.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hXZ : Disjoint X.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hX'Y : Disjoint X'.1 Y.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hX'Z : Disjoint X'.1 Z.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hdisjoint : Disjoint X.1 X'.1 := by
    apply havoid Y Z X X'
      hYZ hXY hXZ hX'Y hX'Z hXX' C C'
      (subdivisionLine_centers_injective K (θ 0) C hC)
      (subdivisionLine_centers_injective K (θ 1) C' hC')
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 1) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 2) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 0) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 1) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 2) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 0) (hC' i)
      exact ⟨p, hpB, hpC⟩
  have hjoinX : jTemplate.Adj
      (.inl (.inl (0 : Fin 4))) (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoinX' : jTemplate.Adj
      (.inl (.inl (1 : Fin 4))) (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hadjX := hom.map_rel hjoinX
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX
  rw [hX] at hadjX
  obtain ⟨p, hpjoin, hpX⟩ :=
    symplecticQuadrangle_adjacent_to_line K hadjX
  have hadjX' := hom.map_rel hjoinX'
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX'
  rw [hX', hpjoin] at hadjX'
  have hpX' : p.1 ≤ X'.1 :=
    (symplecticQuadrangle_incidence_adj K p X').mp
      hadjX'.symm
  have hpzero :
      p.1 = (⊥ : Submodule K (SymplecticVector K)) :=
    eq_bot_iff.mpr
      ((le_inf hpX hpX').trans hdisjoint.le_bot)
  have hdim := p.2
  rw [hpzero] at hdim
  simp at hdim

end JTemplateLineAvoidanceReduction

section CharacteristicTwoLineAvoidance

open SimpleGraph

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

lemma symplecticLine_char_two_canonical_zero_diagonal
    (X : SymplecticLine K)
    (hXH : Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV : Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 2 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    ∃ b : K, X = symmetricGraphLine K 0 b 0 := by
  classical
  obtain ⟨a, b, c, hXgraph, _⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 2) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hind : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy 0) (hxy 1)
    intro heq
    have hindex : (0 : Fin 2) = 1 := by
      apply hcenters
      exact (hrepr 0).trans (heq.trans (hrepr 1).symm)
    exact (by decide : (0 : Fin 2) ≠ 1) hindex
  have hfirst :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 0) (y 0)
              (projectiveDirection_nonzero_left K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  have hsecond :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 1) (y 1)
              (projectiveDirection_nonzero_right K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  obtain ⟨ha, hc⟩ :=
    symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
      K hind hfirst hsecond
  refine ⟨b, ?_⟩
  simpa [ha, hc] using hXgraph

omit [CharP K 2] [Finite K] in
lemma symplecticAutomorphism_commonPoint
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K)
    (hpoint : ∃ p : SymplecticPoint K,
      p.1 ≤ L.1 ∧ p.1 ≤ M.1) :
    ∃ p : SymplecticPoint K,
      p.1 ≤ (symplecticAutomorphismLine K e L).1 ∧
        p.1 ≤ (symplecticAutomorphismLine K e M).1 := by
  obtain ⟨p, hpL, hpM⟩ := hpoint
  exact ⟨symplecticAutomorphismPoint K e p,
    (symplecticAutomorphism_incidence_iff K e p L).mpr hpL,
    (symplecticAutomorphism_incidence_iff K e p M).mpr hpM⟩

lemma symplecticLine_char_two_disjoint_of_two_common_center_pairs
    (Y Z X X' : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (hX'Y : Disjoint X'.1 Y.1)
    (hX'Z : Disjoint X'.1 Z.1)
    (hXX' : X ≠ X')
    (C C' : Fin 2 → SymplecticLine K)
    (hCinj : Function.Injective C)
    (hC'inj : Function.Injective C')
    (hCY : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1)
    (hCZ : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1)
    (hCX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (C i).1)
    (hC'Y : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1)
    (hC'Z : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1)
    (hC'X : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) :
    Disjoint X.1 X'.1 := by
  classical
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  let Xn : SymplecticLine K := symplecticAutomorphismLine K e X
  let X'n : SymplecticLine K := symplecticAutomorphismLine K e X'
  let Cn : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C i)
  let C'n : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C' i)
  have hXH : Disjoint Xn.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  have hXV : Disjoint Xn.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  have hX'H : Disjoint X'n.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Y).mpr hX'Y
  have hX'V : Disjoint X'n.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Z).mpr hX'Z
  have hCn : Function.Injective Cn := by
    intro i j hij
    apply hCinj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hC'n : Function.Injective C'n := by
    intro i j hij
    apply hC'inj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hCnH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hCY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hCZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ Xn.1 ∧ p.1 ≤ (Cn i).1 := by
    exact symplecticAutomorphism_commonPoint K e X (C i) (hCX i)
  have hC'nH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hC'Y i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hC'Z i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'n.1 ∧ p.1 ≤ (C'n i).1 := by
    exact symplecticAutomorphism_commonPoint K e X' (C' i) (hC'X i)
  obtain ⟨b, hb⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K Xn hXH hXV Cn hCn hCnH hCnV hCnX
  obtain ⟨b', hb'⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K X'n hX'H hX'V C'n hC'n hC'nH hC'nV hC'nX
  have hbb : b ≠ b' := by
    intro heq
    apply hXX'
    apply (symplecticAutomorphismLineEquiv K e).injective
    simp only [symplecticAutomorphismLineEquiv_apply]
    change Xn = X'n
    rw [hb, hb', heq]
  apply (symplecticAutomorphism_disjoint_iff K e X X').mp
  change Disjoint Xn.1 X'n.1
  rw [hb, hb']
  exact symmetricGraphLine_zero_diagonal_disjoint K hbb

lemma symplecticLine_char_two_pair_avoidance :
    CharTwoLinePairAvoidance K :=
  symplecticLine_char_two_disjoint_of_two_common_center_pairs K

theorem symplecticQuadrangle_no_jTemplate_of_char_two
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {vertex | InJCopy copy vertex}) :
    False :=
  symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    K (symplecticLine_char_two_pair_avoidance K) hom hbase hcopies

theorem symplecticQuadrangle_no_encoded_jQuotient_of_char_two
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance K
    (symplecticQuadrangle_no_jTemplate_of_char_two K) hf

end CharacteristicTwoLineAvoidance

section UpperBoundReduction

open Filter Finset SimpleGraph
open scoped Classical Topology

theorem familyExtremal_real_le_of_forall_free
    (family : Finset FiniteGraph) (n : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hfree : ∀ host : SimpleGraph (Fin n),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ≤ bound) :
    (familyExtremal family n : ℝ) ≤ bound := by
  classical
  have hnat : familyExtremal family n ≤ ⌊bound⌋₊ := by
    unfold familyExtremal
    apply Finset.sup_le
    intro host hhost
    apply Nat.le_floor
    simpa only [edgeFinset_card_eq_natCard] using
      hfree host (Finset.mem_filter.mp hhost).2
  have hcast : (familyExtremal family n : ℝ) ≤ (⌊bound⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le hbound)

lemma familyLittleO_of_eventual_host_bounds
    (family : Finset FiniteGraph)
    (hhost : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ host : SimpleGraph (Fin n),
          FamilyFree family host →
            (host.edgeFinset.card : ℝ) ≤ ε * extremalScale n) :
    FamilyLittleO family := by
  intro ε hε
  filter_upwards [hhost ε hε] with n hn
  exact familyExtremal_real_le_of_forall_free family n
    (mul_nonneg hε.le (extremalScale_nonneg n)) hn

end UpperBoundReduction

section AsymptoticExtraction

open Filter Finset SimpleGraph
open scoped Classical Topology

lemma familyFree_of_embedded_subgraph
    {family : Finset FiniteGraph}
    {n N : ℕ} (host : SimpleGraph (Fin n))
    (subgraph : SimpleGraph (Fin N))
    (embedding : Fin N ↪ Fin n)
    (hsub : subgraph.map embedding ≤ host)
    (hfree : FamilyFree family host) :
    FamilyFree family subgraph := by
  intro forbidden hforbidden hcontained
  exact hfree forbidden hforbidden
    ((hcontained.trans
      ⟨(SimpleGraph.Embedding.map embedding subgraph).toCopy⟩).mono_right hsub)

lemma eventually_constant_le_positive_nat_rpow
    (constant coefficient exponent : ℝ)
    (hcoefficient : 0 < coefficient)
    (hexponent : 0 < exponent) :
    ∀ᶠ n : ℕ in Filter.atTop,
      constant ≤ coefficient * (n : ℝ) ^ exponent := by
  have hpower :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ exponent)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexponent).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpower.eventually
    (Filter.eventually_ge_atTop (constant / coefficient))]
    with n hn
  calc
    constant = coefficient * (constant / coefficient) := by
      field_simp
    _ ≤ coefficient * (n : ℝ) ^ exponent :=
      mul_le_mul_of_nonneg_left hn hcoefficient.le

lemma extremalScale_sixteenth_power
    {n : ℕ} (hn : 0 < n) :
    (extremalScale n) ^ 16 =
      (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extremalScale
  calc
    ((n : ℝ) ^ ((4 : ℝ) / 3)) ^ 16 =
        (n : ℝ) ^ (((4 : ℝ) / 3) * (16 : ℝ)) := by
      exact (Real.rpow_mul_natCast hnreal.le
        ((4 : ℝ) / 3) 16).symm
    _ = (n : ℝ) ^ ((21 : ℝ) + (1 : ℝ) / 3) := by
      congr 1
      norm_num
    _ = (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      simp [Real.rpow_add hnreal]

lemma familyLittleO_of_sixteenth_power_host_bound
    (family : Finset FiniteGraph) (constant : ℝ)
    (hbound : ∀ (n : ℕ) (host : SimpleGraph (Fin n)),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21) :
    FamilyLittleO family := by
  apply familyLittleO_of_eventual_host_bounds
  intro ε hε
  have hεpow : 0 < ε ^ (16 : ℕ) := pow_pos hε _
  have hconstant := eventually_constant_le_positive_nat_rpow
    constant (ε ^ (16 : ℕ)) ((1 : ℝ) / 3)
    hεpow (by norm_num)
  filter_upwards [hconstant, Filter.eventually_gt_atTop 0]
    with n hn hnpositive
  intro host hfree
  have hhost := hbound n host hfree
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have htarget :
      (host.edgeFinset.card : ℝ) ^ 16 ≤
        (ε * extremalScale n) ^ 16 := by
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21 := hhost
      _ ≤ (ε ^ (16 : ℕ) * (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (n : ℝ) ^ 21 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (ε * extremalScale n) ^ 16 := by
        rw [mul_pow, extremalScale_sixteenth_power hnpositive]
        ring
  have hresult :
      (Nat.card host.edgeSet : ℝ) ≤ ε * extremalScale n := by
    apply le_of_pow_le_pow_left₀
      (by norm_num : (16 : ℕ) ≠ 0)
      (mul_nonneg hε.le (extremalScale_nonneg n))
    simpa only [edgeFinset_card_eq_natCard] using htarget
  simpa only [edgeFinset_card_eq_natCard] using hresult

noncomputable def compactnessDegreePowerConstant : ℝ :=
  (48 : ℝ) ^ (4 : ℕ) + 1769472 + 1

theorem proposedFamilyFree_minDegree_ambient_sixteenth_power_le
    {N n : ℕ} (host : SimpleGraph (Fin N))
    (hN : 0 < N) (hn : 0 < n) (hNn : N ≤ n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin N, d ≤ host.degree v) :
    (d : ℝ) ^ 16 ≤
      compactnessDegreePowerConstant * (n : ℝ) ^ 5 := by
  classical
  have hNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoefLow :
      (48 : ℝ) ^ (4 : ℕ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefHigh :
      (1769472 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefOne : (1 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  by_cases hd : 2 ≤ d
  · by_cases hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)
    · have hhigh := proposedFamilyFree_minDegree_sixteenth_power_le
        host hN hfree hbip d hd hdegree hthreshold
      calc
        (d : ℝ) ^ 16 ≤ 1769472 * (N : ℝ) ^ 5 := hhigh
        _ ≤ 1769472 * (n : ℝ) ^ 5 := by
          gcongr
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefHigh (by positivity)
    · have hlow := fourPathHeavyThreshold_low_degree_fourth_le
        N d hN hd hthreshold
      have hfour :
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        calc
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by gcongr
          _ = (n : ℝ) ^ 4 * 1 := by ring
          _ ≤ (n : ℝ) ^ 4 * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnreal (by positivity)
          _ = (n : ℝ) ^ 5 := by ring
      calc
        (d : ℝ) ^ 16 = ((d : ℝ) ^ 4) ^ 4 := by ring
        _ ≤ (48 * (N : ℝ)) ^ 4 := by gcongr
        _ = (48 : ℝ) ^ 4 * (N : ℝ) ^ 4 := by ring
        _ ≤ (48 : ℝ) ^ 4 * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_left hfour (by positivity)
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefLow (by positivity)
  · have hdNat : d ≤ 1 := by omega
    have hdReal : (d : ℝ) ≤ 1 := by exact_mod_cast hdNat
    calc
      (d : ℝ) ^ 16 ≤ (1 : ℝ) ^ 16 := by gcongr
      _ = 1 ^ (5 : ℕ) := by norm_num
      _ ≤ (n : ℝ) ^ 5 := by gcongr
      _ = 1 * (n : ℝ) ^ 5 := by ring
      _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hcoefOne (by positivity)

noncomputable def compactnessHostPowerConstant : ℝ :=
  (2 : ℝ) ^ (16 : ℕ) * compactnessDegreePowerConstant

theorem proposedFamilyFree_sixteenth_power_host_bound
    (n : ℕ) (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host) :
    (host.edgeFinset.card : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  by_cases hzero : host.edgeFinset.card = 0
  · simp only [hzero, Nat.cast_zero, zero_pow (by norm_num : 16 ≠ 0)]
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  · have hpositive : 0 < host.edgeFinset.card :=
      Nat.pos_of_ne_zero hzero
    obtain ⟨N, B, f, hN, hNn, hBbip, hmap, hminimum,
      _hminimum_pointwise⟩ :=
      exists_bipartite_min_degree_subgraph host hpositive
    have hn : 0 < n := by
      omega
    have hBfree : FamilyFree proposedFamily B :=
      familyFree_of_embedded_subgraph host B f hmap hfree
    let d : ℕ := B.minDegree
    have hdegree : ∀ v : Fin N, d ≤ B.degree v := by
      intro v
      exact B.minDegree_le_degree v
    have hminimumNat :
        host.edgeFinset.card ≤ 2 * n * d := by
      simpa only [d] using hminimum
    have hminimumReal :
        (host.edgeFinset.card : ℝ) ≤
          2 * (n : ℝ) * (d : ℝ) := by
      exact_mod_cast hminimumNat
    have hdPower := proposedFamilyFree_minDegree_ambient_sixteenth_power_le
      B hN hn hNn hBfree hBbip d hdegree
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          (2 * (n : ℝ) * (d : ℝ)) ^ 16 := by
        gcongr
      _ = (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 * (d : ℝ) ^ 16 := by
        ring
      _ ≤ (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 *
          (compactnessDegreePowerConstant * (n : ℝ) ^ 5) := by
        gcongr
      _ = compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
        unfold compactnessHostPowerConstant
        ring

theorem proposedFamily_familyLittleO :
    FamilyLittleO proposedFamily :=
  familyLittleO_of_sixteenth_power_host_bound
    proposedFamily compactnessHostPowerConstant
    proposedFamilyFree_sixteenth_power_host_bound

end AsymptoticExtraction

section CycleBounds

open Filter Finset SimpleGraph
open scoped Topology

theorem four_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    four_cycle_uniform_manuscript_lower hn

theorem six_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    six_cycle_uniform_manuscript_lower hn

theorem member_eventual_lower_of_prime_power_avoidance
    {forbidden : FiniteGraph}
    (hmember : forbidden ∈ proposedFamily)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.graph.Free
        (symplecticQuadrangle (GaloisField t j))) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount t)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    quadrangle_uniform_lower_of_prime_power_avoidance
      forbidden.graph
      (proposedFamily_member_no_isolated hmember)
      t ht htgap hfree hn

theorem uniformMemberLower_of_characteristic_avoidance
    (hj : ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)))
    (hk : ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j))) :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  proposedFamily_induction
    (P := fun graph => ∀ᶠ n : ℕ in Filter.atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n graph.graph : ℝ))
    (by simpa [finiteCycle] using four_cycle_eventual_manuscript_lower)
    (by simpa [finiteCycle] using six_cycle_eventual_manuscript_lower)
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (jQuotient_mem_proposedFamily hf)
      2 (by norm_num) (by norm_num) (hj f hf))
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (kQuotient_mem_proposedFamily hf)
      3 (by norm_num) (by norm_num) (hk f hf))

end CycleBounds

section Counterexample

open SimpleGraph

theorem proposedFamily_odd_characteristic_avoidance :
    ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j)) := by
  intro f hf j _
  exact symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (GaloisField 3 j)
    ((CharP.cast_eq_zero_iff (GaloisField 3 j) 3 2).not.mpr (by norm_num)) hf

theorem proposedFamily_even_characteristic_avoidance :
    ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)) :=
  fun _ hf j _ =>
    symplecticQuadrangle_no_encoded_jQuotient_of_char_two
      (GaloisField 2 j) hf

theorem proposedFamily_uniformMemberLower :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  uniformMemberLower_of_characteristic_avoidance
    proposedFamily_even_characteristic_avoidance
    proposedFamily_odd_characteristic_avoidance

theorem proposedFamily_not_compact :
    ¬ IsCompactFamily proposedFamily :=
  proposedFamily_not_compact_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower

theorem not_erdos_180_source :
    ¬ CompactnessConjectureStatement :=
  not_compactnessConjecture_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower

end Counterexample

end Erdos180
