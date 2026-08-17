import ErdosProblems.Erdos59.Core

/-!
# Four-fold matching blowups

This is the four-point-fibre analogue of the Morris--Saxton matching blowup.
There are exactly `209` matchings in `K_{4,4}`.  Choosing one independently
over every edge of a triangle-free, `C₆`-free base graph produces distinct
labelled `C₆`-free graphs.
-/

namespace Erdos59

open SimpleGraph

/-! ## Matchings in `K_{4,4}` -/

/-- Either four-element fibre of the local bipartite graph. -/
abbrev FibreFour := Fin 4

/-- A possible local edge between two four-element fibres. -/
abbrev EdgeFour := FibreFour × FibreFour

/-- Edges incident to a fixed left vertex. -/
def leftEdgesFour (s : Finset EdgeFour) (i : FibreFour) : Finset EdgeFour :=
  s.filter fun e ↦ e.1 = i

/-- Edges incident to a fixed right vertex. -/
def rightEdgesFour (s : Finset EdgeFour) (j : FibreFour) : Finset EdgeFour :=
  s.filter fun e ↦ e.2 = j

/-- The local edge set has degree at most one at every vertex on both sides. -/
def IsMatchingFour (s : Finset EdgeFour) : Prop :=
  (∀ i : FibreFour, (leftEdgesFour s i).card ≤ 1) ∧
    ∀ j : FibreFour, (rightEdgesFour s j).card ≤ 1

instance (s : Finset EdgeFour) : Decidable (IsMatchingFour s) := by
  unfold IsMatchingFour
  exact inferInstance

/-- Matchings between two labelled four-element fibres. -/
def MatchingFour := {s : Finset EdgeFour // IsMatchingFour s}

deriving instance DecidableEq for MatchingFour
deriving instance Fintype for MatchingFour

namespace MatchingFour

/-- The edge set underlying a four-fibre matching. -/
def edges (M : MatchingFour) : Finset EdgeFour := M.1

/-- The incidence relation of a four-fibre matching. -/
def Rel (M : MatchingFour) (i j : FibreFour) : Prop := (i, j) ∈ M.edges

instance (M : MatchingFour) : DecidableRel M.Rel := fun _ _ ↦ by
  unfold Rel edges
  exact inferInstance

/-- A matching is determined by its incidence relation. -/
@[ext] theorem ext {M N : MatchingFour}
    (h : ∀ i j, M.Rel i j ↔ N.Rel i j) : M = N := by
  apply Subtype.ext
  ext e
  exact h e.1 e.2

/-- A fixed left vertex has at most one partner. -/
theorem left_unique (M : MatchingFour) {i j j' : FibreFour}
    (h : M.Rel i j) (h' : M.Rel i j') : j = j' := by
  have hp : (i, j) = (i, j') :=
    Finset.card_le_one_iff.mp (M.2.1 i)
      (by simpa [leftEdgesFour, Rel, edges] using h)
      (by simpa [leftEdgesFour, Rel, edges] using h')
  exact congrArg Prod.snd hp

/-- A fixed right vertex has at most one partner. -/
theorem right_unique (M : MatchingFour) {i i' j : FibreFour}
    (h : M.Rel i j) (h' : M.Rel i' j) : i = i' := by
  have hp : (i, j) = (i', j) :=
    Finset.card_le_one_iff.mp (M.2.2 j)
      (by simpa [rightEdgesFour, Rel, edges] using h)
      (by simpa [rightEdgesFour, Rel, edges] using h')
  exact congrArg Prod.fst hp

end MatchingFour

/-- The set of left vertices used by a four-fibre matching. -/
def MatchingFour.leftSupport (M : MatchingFour) : Finset FibreFour :=
  M.edges.image Prod.fst

lemma MatchingFour.exists_partner_of_mem_leftSupport (M : MatchingFour)
    {i : FibreFour} (hi : i ∈ M.leftSupport) : ∃ j, M.Rel i j := by
  rcases Finset.mem_image.mp hi with ⟨e, he, hei⟩
  refine ⟨e.2, ?_⟩
  change (i, e.2) ∈ M.edges
  simpa [← hei] using he

/-- The matching which is the graph of an embedding defined on a subset of
the left fibre. -/
def matchingFourOfEmbedding (S : Finset FibreFour)
    (f : (S : Type) ↪ FibreFour) : MatchingFour := by
  refine ⟨Finset.image (fun i : (S : Type) ↦ (i.1, f i)) S.attach, ?_⟩
  constructor
  · intro i
    rw [Finset.card_le_one_iff]
    intro e e' he he'
    obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
    obtain ⟨he', hei'⟩ := Finset.mem_filter.mp he'
    rcases Finset.mem_image.mp he with ⟨x, -, rfl⟩
    rcases Finset.mem_image.mp he' with ⟨x', -, rfl⟩
    have hxx' : x = x' := Subtype.ext <|
      hei.trans hei'.symm
    subst x'
    rfl
  · intro j
    rw [Finset.card_le_one_iff]
    intro e e' he he'
    obtain ⟨he, hfx⟩ := Finset.mem_filter.mp he
    obtain ⟨he', hfx'⟩ := Finset.mem_filter.mp he'
    rcases Finset.mem_image.mp he with ⟨x, -, rfl⟩
    rcases Finset.mem_image.mp he' with ⟨x', -, rfl⟩
    have hxx' : x = x' := f.injective (hfx.trans hfx'.symm)
    subst x'
    rfl

@[simp] lemma matchingFourOfEmbedding_rel (S : Finset FibreFour)
    (f : (S : Type) ↪ FibreFour) (i j : FibreFour) :
    (matchingFourOfEmbedding S f).Rel i j ↔
      ∃ hi : i ∈ S, f ⟨i, hi⟩ = j := by
  simp [matchingFourOfEmbedding, MatchingFour.Rel, MatchingFour.edges]

@[simp] lemma matchingFourOfEmbedding_leftSupport (S : Finset FibreFour)
    (f : (S : Type) ↪ FibreFour) :
    (matchingFourOfEmbedding S f).leftSupport = S := by
  ext i
  simp [MatchingFour.leftSupport, matchingFourOfEmbedding,
    MatchingFour.edges]

/-- The right partner selected by a matching whose left support is `S`. -/
noncomputable def matchingFourFiberPartner (S : Finset FibreFour)
    (M : {M : MatchingFour // M.leftSupport = S}) (i : (S : Type)) :
    FibreFour :=
  Classical.choose <| M.1.exists_partner_of_mem_leftSupport <| by
    rw [M.2]
    exact i.2

lemma matchingFourFiberPartner_spec (S : Finset FibreFour)
    (M : {M : MatchingFour // M.leftSupport = S}) (i : (S : Type)) :
    M.1.Rel i.1 (matchingFourFiberPartner S M i) :=
  Classical.choose_spec <| M.1.exists_partner_of_mem_leftSupport <| by
    rw [M.2]
    exact i.2

/-- A matching with prescribed left support is the same as an embedding of
that support in the right fibre. -/
noncomputable def matchingFourFiberEquiv (S : Finset FibreFour) :
    {M : MatchingFour // M.leftSupport = S} ≃ ((S : Type) ↪ FibreFour) where
  toFun M :=
    ⟨matchingFourFiberPartner S M, by
      intro i i' hii'
      apply Subtype.ext
      apply M.1.right_unique (matchingFourFiberPartner_spec S M i)
      have hi' := matchingFourFiberPartner_spec S M i'
      rwa [← hii'] at hi'⟩
  invFun f := ⟨matchingFourOfEmbedding S f,
    matchingFourOfEmbedding_leftSupport S f⟩
  left_inv M := by
    apply Subtype.ext
    apply MatchingFour.ext
    intro i j
    constructor
    · intro hij
      rw [matchingFourOfEmbedding_rel] at hij
      rcases hij with ⟨hiS, hij⟩
      exact hij ▸ matchingFourFiberPartner_spec S M ⟨i, hiS⟩
    · intro hij
      have hiS : i ∈ S := by
        rw [← M.2]
        apply Finset.mem_image.mpr
        refine ⟨(i, j), ?_, rfl⟩
        exact hij
      rw [matchingFourOfEmbedding_rel]
      refine ⟨hiS, ?_⟩
      exact M.1.left_unique
        (matchingFourFiberPartner_spec S M ⟨i, hiS⟩) hij
  right_inv f := by
    apply DFunLike.ext _ _
    intro i
    apply (matchingFourOfEmbedding S f).left_unique
      (matchingFourFiberPartner_spec S
        ⟨matchingFourOfEmbedding S f,
          matchingFourOfEmbedding_leftSupport S f⟩ i)
    exact matchingFourOfEmbedding_rel S f i.1 (f i) |>.2 ⟨i.2, rfl⟩

/-- Decompose a matching according to its left support. -/
noncomputable def matchingFourEquiv :
    MatchingFour ≃ Σ S : Finset FibreFour, ((S : Type) ↪ FibreFour) :=
  (Equiv.sigmaFiberEquiv MatchingFour.leftSupport).symm.trans <|
    Equiv.sigmaCongrRight matchingFourFiberEquiv

/-- There are exactly `209` matchings in the labelled `K_{4,4}`. -/
theorem matchingFour_card : Fintype.card MatchingFour = 209 := by
  rw [Fintype.card_congr matchingFourEquiv, Fintype.card_sigma]
  simp only [Fintype.card_embedding_eq, Fintype.card_coe]
  decide

/-! ## The matching blowup and recovery of its choices -/

/-- Independently choose a four-fibre matching for every base edge. -/
abbrev MatchingChoiceFour {V : Type*} (G : SimpleGraph V) :=
  G.edgeSet → MatchingFour

/-- Package an adjacency proof as its unordered certified base edge. -/
def certifiedEdgeFour {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) : G.edgeSet := ⟨s(u, v), h⟩

/-- Read the selected matching in the orientation `u → v`. -/
def matchingChoiceRelFour {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoiceFour G) {u v : V} (h : G.Adj u v)
    (i j : FibreFour) : Prop :=
  if u < v then (C (certifiedEdgeFour h)).Rel i j
  else (C (certifiedEdgeFour h)).Rel j i

lemma matchingChoiceRelFour_symmetric {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) (i j : FibreFour) :
    matchingChoiceRelFour C h i j ↔
      matchingChoiceRelFour C h.symm j i := by
  by_cases huv : u < v
  · have hvu : ¬ v < u := not_lt_of_ge huv.le
    have he : certifiedEdgeFour h.symm = certifiedEdgeFour h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRelFour, huv, hvu, he]
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) h.ne.symm
    have he : certifiedEdgeFour h.symm = certifiedEdgeFour h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRelFour, huv, hvu, he]

lemma matchingChoiceRelFour_left_unique {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) {i j j' : FibreFour}
    (hj : matchingChoiceRelFour C h i j)
    (hj' : matchingChoiceRelFour C h i j') : j = j' := by
  by_cases huv : u < v
  · exact (C (certifiedEdgeFour h)).left_unique
      (by simpa [matchingChoiceRelFour, huv] using hj)
      (by simpa [matchingChoiceRelFour, huv] using hj')
  · exact (C (certifiedEdgeFour h)).right_unique
      (by simpa [matchingChoiceRelFour, huv] using hj)
      (by simpa [matchingChoiceRelFour, huv] using hj')

lemma matchingChoiceRelFour_right_unique {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) {i i' j : FibreFour}
    (hi : matchingChoiceRelFour C h i j)
    (hi' : matchingChoiceRelFour C h i' j) : i = i' := by
  have hr : matchingChoiceRelFour C h.symm j i :=
    (matchingChoiceRelFour_symmetric C h i j).mp hi
  have hr' : matchingChoiceRelFour C h.symm j i' :=
    (matchingChoiceRelFour_symmetric C h i' j).mp hi'
  exact matchingChoiceRelFour_left_unique C h.symm hr hr'

/-- The graph obtained by replacing each base vertex by four points and each
base edge by its chosen matching. -/
def matchingBlowupFour {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (C : MatchingChoiceFour G) :
    SimpleGraph (V × FibreFour) where
  Adj x y := ∃ h : G.Adj x.1 y.1, matchingChoiceRelFour C h x.2 y.2
  symm := ⟨by
    rintro x y ⟨h, hC⟩
    exact ⟨h.symm, (matchingChoiceRelFour_symmetric C h _ _).mp hC⟩⟩
  loopless := ⟨by
    rintro x ⟨h, -⟩
    exact h.ne rfl⟩

@[simp] lemma matchingBlowupFour_adj {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G)
    (x y : V × FibreFour) :
    (matchingBlowupFour G C).Adj x y ↔
      ∃ h : G.Adj x.1 y.1, matchingChoiceRelFour C h x.2 y.2 :=
  Iff.rfl

lemma matchingRelFour_iff_adj {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) {u v : V}
    (h : G.Adj u v) (i j : FibreFour) :
    matchingChoiceRelFour C h i j ↔
      (matchingBlowupFour G C).Adj (u, i) (v, j) := by
  constructor
  · exact fun hij ↦ ⟨h, hij⟩
  · rintro ⟨h', hij⟩
    simpa only [Subsingleton.elim h' h] using hij

/-- The blowup retains every independent local matching choice. -/
theorem matchingBlowupFour_injective {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} : Function.Injective (matchingBlowupFour G) := by
  intro A B hAB
  funext e
  apply MatchingFour.ext
  intro i j
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := he
      by_cases hlt : u < v
      · calc
          (A ⟨s(u, v), he⟩).Rel i j ↔ matchingChoiceRelFour A huv i j := by
            simp [matchingChoiceRelFour, hlt, certifiedEdgeFour]
          _ ↔ (matchingBlowupFour G A).Adj (u, i) (v, j) :=
            matchingRelFour_iff_adj A huv i j
          _ ↔ (matchingBlowupFour G B).Adj (u, i) (v, j) := by rw [hAB]
          _ ↔ matchingChoiceRelFour B huv i j :=
            (matchingRelFour_iff_adj B huv i j).symm
          _ ↔ (B ⟨s(u, v), he⟩).Rel i j := by
            simp [matchingChoiceRelFour, hlt, certifiedEdgeFour]
      · have hgt : v < u := lt_of_le_of_ne (le_of_not_gt hlt) huv.ne.symm
        calc
          (A ⟨s(u, v), he⟩).Rel i j ↔
              matchingChoiceRelFour A huv.symm i j := by
            simp [matchingChoiceRelFour, hgt, certifiedEdgeFour, Sym2.eq_swap]
          _ ↔ (matchingBlowupFour G A).Adj (v, i) (u, j) :=
            matchingRelFour_iff_adj A huv.symm i j
          _ ↔ (matchingBlowupFour G B).Adj (v, i) (u, j) := by rw [hAB]
          _ ↔ matchingChoiceRelFour B huv.symm i j :=
            (matchingRelFour_iff_adj B huv.symm i j).symm
          _ ↔ (B ⟨s(u, v), he⟩).Rel i j := by
            simp [matchingChoiceRelFour, hgt, certifiedEdgeFour, Sym2.eq_swap]

/-- Projection from the blowup to its base graph. -/
def matchingBlowupFourProjection {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G) :
    matchingBlowupFour G C →g G where
  toFun := Prod.fst
  map_rel' := by
    rintro x y ⟨h, -⟩
    exact h

lemma eq_of_adj_adj_of_fst_eq_four {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {C : MatchingChoiceFour G}
    {x y z : V × FibreFour}
    (hxy : (matchingBlowupFour G C).Adj x y)
    (hyz : (matchingBlowupFour G C).Adj y z)
    (hxz : x.1 = z.1) : x = z := by
  rcases x with ⟨xv, xi⟩
  rcases y with ⟨yv, yi⟩
  rcases z with ⟨zv, zi⟩
  change xv = zv at hxz
  subst zv
  rcases hxy with ⟨h, hC⟩
  rcases hyz with ⟨h', hC'⟩
  have hidx : xi = zi := by
    apply matchingChoiceRelFour_right_unique C h hC
    have hC'' : matchingChoiceRelFour C h.symm yi zi := by
      simpa only [Subsingleton.elim h' h.symm] using hC'
    exact (matchingChoiceRelFour_symmetric C h _ _).mpr hC''
  exact Prod.ext rfl hidx

lemma fst_ne_of_adj_adj_of_ne_four {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {C : MatchingChoiceFour G}
    {x y z : V × FibreFour}
    (hxy : (matchingBlowupFour G C).Adj x y)
    (hyz : (matchingBlowupFour G C).Adj y z) (hxz : x ≠ z) :
    x.1 ≠ z.1 := by
  intro h
  exact hxz (eq_of_adj_adj_of_fst_eq_four hxy hyz h)

/-! ## Preservation of triangle- and six-cycle-freeness -/

/-- Edge-oriented triangle-freeness. -/
def TriangleFreeFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj c a

/-- Six-cycle-freeness in the explicit six-vertex presentation. -/
def C6FreeFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d e f : V⦄,
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → G.Adj f a →
    ¬ [a, b, c, d, e, f].Nodup

lemma projected_six_nodup_four {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {C : MatchingChoiceFour G}
    (htriangle : TriangleFreeFour G)
    {x₀ x₁ x₂ x₃ x₄ x₅ : V × FibreFour}
    (h₀₁ : (matchingBlowupFour G C).Adj x₀ x₁)
    (h₁₂ : (matchingBlowupFour G C).Adj x₁ x₂)
    (h₂₃ : (matchingBlowupFour G C).Adj x₂ x₃)
    (h₃₄ : (matchingBlowupFour G C).Adj x₃ x₄)
    (h₄₅ : (matchingBlowupFour G C).Adj x₄ x₅)
    (h₅₀ : (matchingBlowupFour G C).Adj x₅ x₀)
    (hnodup : [x₀, x₁, x₂, x₃, x₄, x₅].Nodup) :
    [x₀.1, x₁.1, x₂.1, x₃.1, x₄.1, x₅.1].Nodup := by
  have b₀₁ : G.Adj x₀.1 x₁.1 := (matchingBlowupFourProjection C).map_rel h₀₁
  have b₁₂ : G.Adj x₁.1 x₂.1 := (matchingBlowupFourProjection C).map_rel h₁₂
  have b₂₃ : G.Adj x₂.1 x₃.1 := (matchingBlowupFourProjection C).map_rel h₂₃
  have b₃₄ : G.Adj x₃.1 x₄.1 := (matchingBlowupFourProjection C).map_rel h₃₄
  have b₄₅ : G.Adj x₄.1 x₅.1 := (matchingBlowupFourProjection C).map_rel h₄₅
  have b₅₀ : G.Adj x₅.1 x₀.1 := (matchingBlowupFourProjection C).map_rel h₅₀
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    or_false, not_or] at hnodup ⊢
  rcases hnodup with ⟨h₀, h₁, h₂, h₃, n₄₅, -, -⟩
  rcases h₀ with ⟨n₀₁, n₀₂, n₀₃, n₀₄, n₀₅⟩
  rcases h₁ with ⟨n₁₂, n₁₃, n₁₄, n₁₅⟩
  rcases h₂ with ⟨n₂₃, n₂₄, n₂₅⟩
  rcases h₃ with ⟨n₃₄, n₃₅⟩
  have p₀₁ : x₀.1 ≠ x₁.1 := b₀₁.ne
  have p₀₂ : x₀.1 ≠ x₂.1 := fst_ne_of_adj_adj_of_ne_four h₀₁ h₁₂ n₀₂
  have p₀₄ : x₀.1 ≠ x₄.1 :=
    (fst_ne_of_adj_adj_of_ne_four h₄₅ h₅₀ (Ne.symm n₀₄)).symm
  have p₀₅ : x₀.1 ≠ x₅.1 := b₅₀.ne.symm
  have p₁₂ : x₁.1 ≠ x₂.1 := b₁₂.ne
  have p₁₃ : x₁.1 ≠ x₃.1 := fst_ne_of_adj_adj_of_ne_four h₁₂ h₂₃ n₁₃
  have p₁₅ : x₁.1 ≠ x₅.1 :=
    (fst_ne_of_adj_adj_of_ne_four h₅₀ h₀₁ (Ne.symm n₁₅)).symm
  have p₂₃ : x₂.1 ≠ x₃.1 := b₂₃.ne
  have p₂₄ : x₂.1 ≠ x₄.1 := fst_ne_of_adj_adj_of_ne_four h₂₃ h₃₄ n₂₄
  have p₃₄ : x₃.1 ≠ x₄.1 := b₃₄.ne
  have p₃₅ : x₃.1 ≠ x₅.1 := fst_ne_of_adj_adj_of_ne_four h₃₄ h₄₅ n₃₅
  have p₄₅ : x₄.1 ≠ x₅.1 := b₄₅.ne
  have p₀₃ : x₀.1 ≠ x₃.1 := by
    intro h
    apply htriangle b₀₁ b₁₂
    simpa [h] using b₂₃
  have p₁₄ : x₁.1 ≠ x₄.1 := by
    intro h
    apply htriangle b₁₂ b₂₃
    simpa [h] using b₃₄
  have p₂₅ : x₂.1 ≠ x₅.1 := by
    intro h
    apply htriangle b₂₃ b₃₄
    simpa [h] using b₄₅
  exact ⟨⟨p₀₁, p₀₂, p₀₃, p₀₄, p₀₅⟩,
    ⟨p₁₂, p₁₃, p₁₄, p₁₅⟩, ⟨p₂₃, p₂₄, p₂₅⟩,
    ⟨p₃₄, p₃₅⟩, p₄₅, trivial, List.nodup_nil⟩

/-- Four-fold matching blowups preserve `C₆`-freeness under the necessary
triangle-free hypothesis on the base. -/
theorem matchingBlowupFour_c6Free {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G)
    (htriangle : TriangleFreeFour G) (hC6 : C6FreeFour G) :
    C6FreeFour (matchingBlowupFour G C) := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ hnodup
  apply hC6
    ((matchingBlowupFourProjection C).map_rel h₀₁)
    ((matchingBlowupFourProjection C).map_rel h₁₂)
    ((matchingBlowupFourProjection C).map_rel h₂₃)
    ((matchingBlowupFourProjection C).map_rel h₃₄)
    ((matchingBlowupFourProjection C).map_rel h₄₅)
    ((matchingBlowupFourProjection C).map_rel h₅₀)
  exact projected_six_nodup_four htriangle h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ hnodup

/-- The edge-oriented triangle predicate is standard triangle-freeness. -/
theorem triangleFreeFour_iff_cliqueFree_three {V : Type*}
    (G : SimpleGraph V) : TriangleFreeFour G ↔ G.CliqueFree 3 := by
  classical
  constructor
  · intro h s hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    exact False.elim (h hab hbc hac.symm)
  · intro h a b c hab hbc hca
    exact h {a, b, c}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩)

/-- The explicit six-tuple predicate is Mathlib's standard `C₆`-freeness. -/
theorem c6FreeFour_iff_cycleGraph_six_free {V : Type*}
    (G : SimpleGraph V) :
    C6FreeFour G ↔ (SimpleGraph.cycleGraph 6).Free G := by
  rw [cycleGraph_six_free_iff_forall_not_isC6]
  constructor
  · intro h v hv
    rcases hv with ⟨hinj, hadj⟩
    apply h (by simpa using hadj 0) (by simpa using hadj 1)
      (by simpa using hadj 2) (by simpa using hadj 3)
      (by simpa using hadj 4) (by simpa using hadj 5)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, or_false, not_or]
    exact ⟨⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
        hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide)⟩,
      hinj.ne (by decide), trivial, List.nodup_nil⟩
  · intro h a b c d e f hab hbc hcd hde hef hfa hnodup
    apply h ![a, b, c, d, e, f]
    exact ⟨by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all,
      fun i ↦ by
        fin_cases i
        · simpa using hab
        · simpa using hbc
        · simpa using hcd
        · simpa using hde
        · simpa using hef
        · simpa using hfa⟩

/-- Standard-form preservation theorem. -/
theorem matchingBlowupFour_cycleGraph_six_free {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoiceFour G)
    (htriangle : G.CliqueFree 3)
    (hC6 : (SimpleGraph.cycleGraph 6).Free G) :
    (SimpleGraph.cycleGraph 6).Free (matchingBlowupFour G C) := by
  rw [← c6FreeFour_iff_cycleGraph_six_free]
  exact matchingBlowupFour_c6Free C
    ((triangleFreeFour_iff_cliqueFree_three G).mpr htriangle)
    ((c6FreeFour_iff_cycleGraph_six_free G).mpr hC6)

/-! ## Exact family size and canonical labelling -/

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The exact number of independent four-fibre matching choices. -/
theorem matchingChoiceFour_card (B : SimpleGraph V) [DecidableRel B.Adj] :
    Fintype.card (MatchingChoiceFour B) = 209 ^ B.edgeFinset.card := by
  rw [Fintype.card_fun, matchingFour_card, SimpleGraph.card_edgeSet]

/-- The finite family of all four-fold matching blowups of `B`. -/
noncomputable def blowupFourFamily (B : SimpleGraph V) [DecidableRel B.Adj] :
    Finset (SimpleGraph (V × FibreFour)) := by
  classical
  exact Finset.univ.image (matchingBlowupFour B)

/-- The family of distinct blowups has exactly `209 ^ e(B)` members. -/
theorem blowupFourFamily_card (B : SimpleGraph V) [DecidableRel B.Adj] :
    (blowupFourFamily B).card = 209 ^ B.edgeFinset.card := by
  classical
  rw [blowupFourFamily,
    Finset.card_image_of_injective _ (matchingBlowupFour_injective (G := B)),
    Finset.card_univ, matchingChoiceFour_card]

/-- The standard four-fold fibre labelling. -/
def finFourEquiv (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

/-- Relabel a four-fold graph on the canonical `Fin (4*n)` vertex set. -/
def relabelFinFourGraph {n : ℕ} (G : SimpleGraph (Fin n × Fin 4)) :
    SimpleGraph (Fin (4 * n)) :=
  (finFourEquiv n).simpleGraph G

/-- Four-fold relabelling is injective on graphs. -/
def graphFinFourEquiv (n : ℕ) :
    SimpleGraph (Fin n × Fin 4) ≃ SimpleGraph (Fin (4 * n)) :=
  (finFourEquiv n).simpleGraph

/-- A graph is isomorphic to its four-fold relabelling. -/
def relabelFinFourGraphIso {n : ℕ} (G : SimpleGraph (Fin n × Fin 4)) :
    G ≃g relabelFinFourGraph G :=
  (SimpleGraph.Iso.comap (finFourEquiv n).symm G).symm

/-- Relabelling preserves every forbidden-subgraph predicate. -/
theorem relabelFinFourGraph_free_iff {W : Type*} (H : SimpleGraph W)
    {n : ℕ} (G : SimpleGraph (Fin n × Fin 4)) :
    H.Free (relabelFinFourGraph G) ↔ H.Free G :=
  (SimpleGraph.free_congr_right (relabelFinFourGraphIso G)).symm

/-- Each independent matching choice gives a distinct canonically labelled
`C₆`-free graph. -/
noncomputable def matchingChoiceFourFreeEmbedding {n : ℕ}
    (B : SimpleGraph (Fin n)) [DecidableRel B.Adj]
    (htriangle : B.CliqueFree 3)
    (hC6 : (SimpleGraph.cycleGraph 6).Free B) :
    MatchingChoiceFour B ↪
      LabelledFreeGraphs (SimpleGraph.cycleGraph 6) (4 * n) where
  toFun C := ⟨relabelFinFourGraph (matchingBlowupFour B C),
    (relabelFinFourGraph_free_iff _ _).mpr
      (matchingBlowupFour_cycleGraph_six_free C htriangle hC6)⟩
  inj' A C h := by
    apply matchingBlowupFour_injective
    apply (graphFinFourEquiv n).injective
    exact Subtype.ext_iff.mp h

/-- The four-fold matching construction supplies `209 ^ e(B)` distinct
labelled `C₆`-free graphs on `4*n` vertices. -/
theorem matchingBlowupFour_labelledFreeGraphCount_lower_bound {n : ℕ}
    (B : SimpleGraph (Fin n)) [DecidableRel B.Adj]
    (htriangle : B.CliqueFree 3)
    (hC6 : (SimpleGraph.cycleGraph 6).Free B) :
    209 ^ B.edgeFinset.card ≤
      labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * n) := by
  calc
    209 ^ B.edgeFinset.card = Nat.card (MatchingChoiceFour B) := by
      rw [Nat.card_eq_fintype_card, matchingChoiceFour_card]
    _ ≤ Nat.card (LabelledFreeGraphs (SimpleGraph.cycleGraph 6) (4 * n)) :=
      Nat.card_le_card_of_injective
        (matchingChoiceFourFreeEmbedding B htriangle hC6)
        (matchingChoiceFourFreeEmbedding B htriangle hC6).injective
    _ = labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (4 * n) := rfl

end Erdos59
