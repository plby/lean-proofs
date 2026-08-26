import ErdosProblems.Erdos117.Spread
import ErdosProblems.Erdos117.TernaryClique

/-!
# Scalar alternating-form cliques

Orthogonal anchor composition adds clique sizes minus one. The scalar plane
provides the basic credit, and the ternary rank-six configuration supplies the
improved credit at the prime three.
-/

namespace Erdos117

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def NonorthogonalFamily (B : LinearMap.BilinForm K V) {ι : Type*} (f : ι → V) : Prop :=
  ∀ i j, i ≠ j → B (f i) (f j) ≠ 0

theorem NonorthogonalFamily.injective {B : LinearMap.BilinForm K V} (halt : B.IsAlt)
    {ι : Type*} {f : ι → V} (hf : NonorthogonalFamily B f) : Function.Injective f := by
  intro i j hij
  by_contra hne
  exact hf i j hne (hij ▸ halt (f j))

theorem NonorthogonalFamily.comp {B : LinearMap.BilinForm K V}
    {ι κ : Type*} {f : ι → V} (hf : NonorthogonalFamily B f)
    {e : κ → ι} (he : Function.Injective e) : NonorthogonalFamily B (f ∘ e) := by
  intro i j hij
  exact hf _ _ (fun h => hij (he h))

def orthogonalSum (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K (V × W) :=
  B.comp (LinearMap.fst K V W) (LinearMap.fst K V W) +
    C.comp (LinearMap.snd K V W) (LinearMap.snd K V W)

@[simp] theorem orthogonalSum_apply (B : LinearMap.BilinForm K V)
    (C : LinearMap.BilinForm K W) (x y : V × W) :
    orthogonalSum B C x y = B x.1 y.1 + C x.2 y.2 := rfl

def orthogonalAnchorFamily {ι κ : Type*} (u : ι → V) (v : κ → W) (a : ι) :
    {i : ι // i ≠ a} ⊕ κ → V × W
  | .inl i => (u i, 0)
  | .inr j => (u a, v j)

/-- Lemma 4.3, in an indexed form that also makes the cardinality calculation
and injectivity available without a separate disjointness argument. -/
theorem nonorthogonal_orthogonalAnchorFamily (B : LinearMap.BilinForm K V)
    (C : LinearMap.BilinForm K W) (halt : B.IsAlt) {ι κ : Type*}
    {u : ι → V} {v : κ → W} (hu : NonorthogonalFamily B u)
    (hv : NonorthogonalFamily C v) (a : ι) :
    NonorthogonalFamily (orthogonalSum B C) (orthogonalAnchorFamily u v a) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hne : (i : ι) ≠ j := fun h => hij (congrArg Sum.inl (Subtype.ext h))
      simpa [orthogonalAnchorFamily] using hu i j hne
    | inr j =>
      simpa [orthogonalAnchorFamily] using hu i a i.2
  | inr i =>
    cases j with
    | inl j =>
      simpa [orthogonalAnchorFamily] using hu a j (Ne.symm j.2)
    | inr j =>
      have hne : i ≠ j := fun h => hij (congrArg Sum.inr h)
      simpa [orthogonalAnchorFamily, halt (u a)] using hv i j hne

def scalarPlaneClique : Option K → K × K
  | none => (0, 1)
  | some t => (1, t)

theorem scalarPlaneClique_nonorthogonal :
    NonorthogonalFamily (fieldPlaneForm (LinearMap.id : K →ₗ[K] K))
      (scalarPlaneClique (K := K)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some t => simp [scalarPlaneClique]
  | some s =>
    cases j with
    | none => simp [scalarPlaneClique]
    | some t =>
      have hne : t ≠ s := fun h => hij (congrArg Option.some h.symm)
      simpa [scalarPlaneClique] using sub_ne_zero.mpr hne

/-- Each hyperbolic plane contributes `|K|` to the clique size minus one. -/
theorem exists_scalar_clique_nondegenerate [Fintype K] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    {m : ℕ} (hdim : finrank K V = 2 * m) :
    ∃ f : Fin (Fintype.card K * m + 1) → V, NonorthogonalFamily B f := by
  classical
  induction m generalizing V with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    intro i j hij
    apply (hij ?_).elim
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  | succ m ih =>
    obtain ⟨e, f, hef, hcompl, hQ, hdimP, hdimQ⟩ :=
      exists_hyperbolic_complement B halt hB (by omega)
    let P := (hyperbolicPlaneMap (K := K) e f).range
    let Q := B.orthogonal P
    have hdQ : finrank K Q = 2 * m := by dsimp [Q, P]; omega
    obtain ⟨v, hv⟩ := ih (B.restrict Q) (fun x => halt x) hQ hdQ
    let u : Option K → P := fun i =>
      ⟨hyperbolicPlaneMap e f (scalarPlaneClique i), LinearMap.mem_range_self _ _⟩
    have hu : NonorthogonalFamily (B.restrict P) u := by
      intro i j hij
      have h := scalarPlaneClique_nonorthogonal (K := K) i j hij
      change B (hyperbolicPlaneMap e f (scalarPlaneClique i))
        (hyperbolicPlaneMap e f (scalarPlaneClique j)) ≠ 0
      rw [hyperbolicPlaneMap_pairing B halt hef]
      simpa only [fieldPlaneForm_apply, LinearMap.id_apply, mul_comm] using h
    let a := orthogonalAnchorFamily u v none
    have ha := nonorthogonal_orthogonalAnchorFamily (B.restrict P) (B.restrict Q)
      (fun x => halt x) hu hv none
    let j : ({i : Option K // i ≠ none} ⊕ Fin (Fintype.card K * m + 1)) ≃
        Fin (Fintype.card K * (m + 1) + 1) := Fintype.equivFinOfCardEq (by
      simp only [Fintype.card_sum, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, Fintype.card_option, Nat.add_sub_cancel,
        Fintype.card_fin]
      ring)
    let w : (P × Q) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl P Q hcompl
    refine ⟨fun i => w (a (j.symm i)), ?_⟩
    intro i k hik
    have h := ha (j.symm i) (j.symm k) (fun h => hik (j.symm.injective h))
    change B (((a (j.symm i)).1 : V) + (a (j.symm i)).2)
      (((a (j.symm k)).1 : V) + (a (j.symm k)).2) ≠ 0
    rw [pairing_add_orthogonal B halt.isRefl P]
    exact h

theorem exists_scalar_clique_of_rank [Fintype K] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) :
    ∃ f : Fin (Fintype.card K * (finrank K B.range / 2) + 1) → V,
      NonorthogonalFamily B f := by
  obtain ⟨W, π, hW, hdim, hπ⟩ := exists_nondegenerate_model B halt
  obtain ⟨m, hm⟩ := even_rank_of_alt B halt
  have hdimW : finrank K W = 2 * (finrank K B.range / 2) := by omega
  obtain ⟨f, hf⟩ := exists_scalar_clique_nondegenerate (B.restrict W)
    (fun x => halt x) hW hdimW
  exact ⟨fun i => f i, hf⟩

/-- Rank-six ternary blocks contribute twelve, while any leftover planes
contribute three apiece. -/
theorem exists_ternary_clique_blocks {V : Type*} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    {k m : ℕ} (hdim : finrank (ZMod 3) V = 6 * k + 2 * m) :
    ∃ f : Fin (12 * k + 3 * m + 1) → V, NonorthogonalFamily B f := by
  classical
  induction k generalizing V with
  | zero =>
    have h := exists_scalar_clique_nondegenerate B halt hB (m := m) (by simpa using hdim)
    rw [ZMod.card] at h
    have hc : 12 * 0 + 3 * m + 1 = 3 * m + 1 := by omega
    rw [hc]
    exact h
  | succ k ih =>
    obtain ⟨i, hi, hP, hcompl, hQ, hdimP, hdimQ⟩ :=
      exists_isometric_complement ternaryForm B ternaryForm_isAlt halt
        ternaryForm_nondegenerate hB (by simp; omega)
    let P := i.range
    let Q := B.orthogonal P
    have hdQ : finrank (ZMod 3) Q = 6 * k + 2 * m := by
      dsimp [Q, P]
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdimQ
      omega
    obtain ⟨v, hv⟩ := ih (B.restrict Q) (fun x => halt x) hQ hdQ
    let u : Fin 13 → P := fun j => ⟨i (ternaryClique j), LinearMap.mem_range_self _ _⟩
    have hu : NonorthogonalFamily (B.restrict P) u := by
      intro j k hjk
      change B (i (ternaryClique j)) (i (ternaryClique k)) ≠ 0
      rw [hi]
      exact ternaryClique_pairwise j k hjk
    let a := orthogonalAnchorFamily u v 0
    have ha := nonorthogonal_orthogonalAnchorFamily (B.restrict P) (B.restrict Q)
      (fun x => halt x) hu hv 0
    let j : ({i : Fin 13 // i ≠ 0} ⊕ Fin (12 * k + 3 * m + 1)) ≃
        Fin (12 * (k + 1) + 3 * m + 1) := Fintype.equivFinOfCardEq (by
      simp only [Fintype.card_sum, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, Fintype.card_fin]
      omega)
    let w : (P × Q) ≃ₗ[ZMod 3] V := Submodule.prodEquivOfIsCompl P Q hcompl
    refine ⟨fun i => w (a (j.symm i)), ?_⟩
    intro i k hik
    have h := ha (j.symm i) (j.symm k) (fun h => hik (j.symm.injective h))
    change B (((a (j.symm i)).1 : V) + (a (j.symm i)).2)
      (((a (j.symm k)).1 : V) + (a (j.symm k)).2) ≠ 0
    rw [pairing_add_orthogonal B halt.isRefl P]
    exact h

/-- The improved ternary scalar estimate, including forms with a radical. -/
theorem exists_ternary_clique_of_rank {V : Type*} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (halt : B.IsAlt) :
    ∃ (c : ℕ) (f : Fin (c + 1) → V), NonorthogonalFamily B f ∧
      2 * finrank (ZMod 3) B.range ≤ c + 2 := by
  obtain ⟨W, π, hW, hdim, hπ⟩ := exists_nondegenerate_model B halt
  obtain ⟨m, hm⟩ := even_rank_of_alt B halt
  have hdW : finrank (ZMod 3) W = 6 * (m / 3) + 2 * (m % 3) := by omega
  obtain ⟨f, hf⟩ := exists_ternary_clique_blocks (B.restrict W)
    (fun x => halt x) hW hdW
  refine ⟨12 * (m / 3) + 3 * (m % 3), fun i => f i, hf, ?_⟩
  omega

/-- Clique credit per hyperbolic plane. -/
def scalarCreditRate (p : ℕ) : ℕ := if p = 3 then 4 else p

def scalarDefect (p : ℕ) : ℕ := if p = 3 then 2 else 0

/-- One integer-valued formulation of all scalar clique estimates. The
ternary defect is the only correction term. -/
theorem exists_scalar_credit {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) (halt : B.IsAlt) :
    ∃ (c : ℕ) (f : Fin (c + 1) → V), NonorthogonalFamily B f ∧
      scalarCreditRate p * (finrank (ZMod p) B.range / 2) ≤ c + scalarDefect p := by
  by_cases hp : p = 3
  · subst p
    obtain ⟨c, f, hf, hrank⟩ := exists_ternary_clique_of_rank B halt
    refine ⟨c, f, hf, ?_⟩
    change 4 * (finrank (ZMod 3) B.range / 2) ≤ c + 2
    omega
  · have h := exists_scalar_clique_of_rank B halt
    rw [ZMod.card] at h
    obtain ⟨f, hf⟩ := h
    refine ⟨p * (finrank (ZMod p) B.range / 2), f, hf, ?_⟩
    simp [scalarCreditRate, scalarDefect, hp]

end Erdos117
