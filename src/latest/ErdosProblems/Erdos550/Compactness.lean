import Mathlib
import ErdosProblems.Erdos550.Rounding
import ErdosProblems.Erdos550.NullBlocker
import ErdosProblems.Erdos550.CubeEncoding
import ErdosProblems.Erdos550.Shadow

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Null-blocker compactness (Theorem `thm:compactness` of the paper)

This file states and proves the paper's **null-blocker compactness theorem**.
The cube-encoding basics live in `RequestProject.CubeEncoding`; the shadow
hypergraph / finite-transfer machinery lives in `RequestProject.Shadow`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Erdos550

open Filter Topology in
/-- **Null-blocker compactness, normal form.**  The same statement as
`null_blocker_compactness`, but specialised to systems already living on the
fixed Boolean cube `ℕ → Bool` with vertex set `ℕ` and events the coordinate
cylinders.  Every general finite system reduces to this case via the cube
encoding `cube_pushforward_nat`, so this implies the general theorem. -/
theorem null_blocker_compactness_normal
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a) (rStar : ℕ) (_hr : 1 ≤ rStar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (V : Finset ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
        (C : Fin q → Set (Finset ℕ)) (ε : ℝ),
        0 ≤ ε → ε ≤ ε₀ →
        (∀ i, ∀ E ∈ C i, E.Nonempty ∧ E.card ≤ rStar ∧ E ⊆ V) →
        (∀ x ∈ V, (q : ℝ) - 1 - ε ≤ ∑ i, cdens q ρ i {x}) →
        (∀ S : Finset ℕ, S ⊆ V → S.card = a → ∃ i, cdens q ρ i S ≤ ε) →
        (∀ i : Fin q, ∀ E ∈ C i, ∃ j, j ≠ i ∧ cdens q ρ j E ≤ ε) →
        ∃ (Z : Finset ℕ) (φ : ℕ → Fin q), Z ⊆ V ∧ Z.card ≤ a - 1 ∧
          ∀ i : Fin q, ∀ E ∈ C i, ¬ (∀ x ∈ E, x ∉ Z ∧ φ x = i) := by
  by_contra hcon
  classical
  push_neg at hcon
  -- Extract a counterexample family indexed by `n`, with slack `≤ 1/(n+1)`.
  choose! V ρ C ε hε0 hεle hEdge hA1 hA2 hA3 hNoValid using
    fun n : ℕ => hcon (1 / (n + 1)) (by positivity)
  -- Impurity-decreasing enumeration `s n` of each ground set `V n`.
  choose s hs_inj hs_mem hs_surj hs_mono using
    fun n : ℕ => exists_impurity_enum q (V n) (ρ n)
  -- Pushforward relabelled systems `ρ' n` on the ordered ground set `range (V n).card`.
  choose ρ' hρ'cd hρ'dead using
    fun n : ℕ => exists_pushforward_relabel q (V n).card (s n) (ρ n)
  -- The inverse relabelling on `V n`.
  set invS : ℕ → ℕ → ℕ :=
    fun n x => if h : x ∈ V n then (hs_surj n x h).choose else 0 with hinvS_def
  have hinvS_lt : ∀ n x, x ∈ V n → invS n x < (V n).card := by
    intro n x hx
    simp only [hinvS_def, dif_pos hx]; exact (hs_surj n x hx).choose_spec.1
  have hinvS_s : ∀ n x, x ∈ V n → s n (invS n x) = x := by
    intro n x hx
    simp only [hinvS_def, dif_pos hx]; exact (hs_surj n x hx).choose_spec.2
  -- The relabelled edge families.
  set C' : ℕ → Fin q → Set (Finset ℕ) :=
    fun n i => {F | ∃ E, E ∈ C n i ∧ F = E.image (invS n)} with hC'_def
  -- `cimp` transfers along the relabelling.
  have hcimp' : ∀ n ℓ, ℓ < (V n).card → cimp q (ρ' n) ℓ = cimp q (ρ n) (s n ℓ) := by
    intro n ℓ hℓ
    unfold cimp
    apply iInf_congr
    intro i
    rw [hρ'cd n i {ℓ} (by intro x hx; simp only [Finset.mem_singleton] at hx; omega),
      Finset.image_singleton]
  -- The relabelled hypotheses.
  have hEdge' : ∀ n i, ∀ F ∈ C' n i, F.Nonempty ∧ F.card ≤ rStar ∧ ∀ x ∈ F, x < (V n).card := by
    intro n i F hF
    obtain ⟨E, hE, rfl⟩ := hF
    obtain ⟨hne, hcard, hsub⟩ := hEdge n i E hE
    refine ⟨hne.image _, le_trans Finset.card_image_le hcard, ?_⟩
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hinvS_lt n y (hsub hy)
  have hA1' : ∀ n ℓ, ℓ < (V n).card → (q : ℝ) - 1 - ε n ≤ ∑ i, cdens q (ρ' n) i {ℓ} := by
    intro n ℓ hℓ
    have hrw : ∀ i, cdens q (ρ' n) i {ℓ} = cdens q (ρ n) i {s n ℓ} := by
      intro i
      rw [hρ'cd n i {ℓ} (by intro x hx; simp only [Finset.mem_singleton] at hx; omega),
        Finset.image_singleton]
    simp_rw [hrw]
    exact hA1 n (s n ℓ) (hs_mem n ℓ hℓ)
  have hA2' : ∀ n (S : Finset ℕ), (∀ x ∈ S, x < (V n).card) → S.card = a →
      ∃ i, cdens q (ρ' n) i S ≤ ε n := by
    intro n S hS hcard
    have hsub : S.image (s n) ⊆ V n := by
      intro y hy; simp only [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
      exact hs_mem n x (hS x hx)
    have hcardim : (S.image (s n)).card = a := by
      rw [Finset.card_image_of_injOn ?_]
      · exact hcard
      · intro x hx y hy hxy
        exact hs_inj n (Set.mem_Iio.mpr (hS x hx)) (Set.mem_Iio.mpr (hS y hy)) hxy
    obtain ⟨i, hi⟩ := hA2 n (S.image (s n)) hsub hcardim
    exact ⟨i, by rw [hρ'cd n i S hS]; exact hi⟩
  have hA3' : ∀ n i, ∀ F ∈ C' n i, ∃ j, j ≠ i ∧ cdens q (ρ' n) j F ≤ ε n := by
    intro n i F hF
    obtain ⟨E, hE, rfl⟩ := hF
    obtain ⟨j, hj, hjle⟩ := hA3 n i E hE
    refine ⟨j, hj, ?_⟩
    have hFlt : ∀ x ∈ E.image (invS n), x < (V n).card := by
      intro x hx; simp only [Finset.mem_image] at hx; obtain ⟨y, hy, rfl⟩ := hx
      exact hinvS_lt n y ((hEdge n i E hE).2.2 hy)
    rw [hρ'cd n j (E.image (invS n)) hFlt]
    have himg : (E.image (invS n)).image (s n) = E := by
      rw [Finset.image_image]
      have heq : Set.EqOn (s n ∘ invS n) id (↑E : Set ℕ) := by
        intro y hy
        simp only [Function.comp_apply, id_eq]
        exact hinvS_s n y ((hEdge n i E hE).2.2 (Finset.mem_coe.mp hy))
      rw [Finset.image_congr heq, Finset.image_id]
    rw [himg]; exact hjle
  have hmono : ∀ n ℓ₁ ℓ₂, ℓ₁ ≤ ℓ₂ → ℓ₂ < (V n).card →
      cimp q (ρ' n) ℓ₂ ≤ cimp q (ρ' n) ℓ₁ := by
    intro n ℓ₁ ℓ₂ h12 h2
    have h1 : ℓ₁ < (V n).card := lt_of_le_of_lt h12 h2
    rw [hcimp' n ℓ₂ h2, hcimp' n ℓ₁ h1]
    exact hs_mono n ℓ₁ ℓ₂ h12 h2
  have hNoValid' : ∀ n (Z : Finset ℕ) (φ : ℕ → Fin q), (∀ x ∈ Z, x < (V n).card) →
      Z.card ≤ a - 1 → ∃ i, ∃ F ∈ C' n i, ∀ x ∈ F, x ∉ Z ∧ φ x = i := by
    intro n Z φ hZlt hZcard
    set Z₀ : Finset ℕ := Z.image (s n) with hZ0
    set φ₀ : ℕ → Fin q := fun v => φ (invS n v) with hφ0
    have hZ0sub : Z₀ ⊆ V n := by
      intro y hy; rw [hZ0] at hy; simp only [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
      exact hs_mem n x (hZlt x hx)
    have hZ0card : Z₀.card ≤ a - 1 := le_trans Finset.card_image_le hZcard
    obtain ⟨i, E, hE, hEviol⟩ := hNoValid n Z₀ φ₀ hZ0sub hZ0card
    refine ⟨i, E.image (invS n), ⟨E, hE, rfl⟩, ?_⟩
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨hvZ0, hvφ⟩ := hEviol v hv
    have hvV : v ∈ V n := (hEdge n i E hE).2.2 hv
    refine ⟨?_, ?_⟩
    · intro hcontra
      apply hvZ0
      rw [hZ0]; simp only [Finset.mem_image]
      exact ⟨invS n v, hcontra, hinvS_s n v hvV⟩
    · simpa only [hφ0] using! hvφ
  -- A non-principal ultrafilter on `ℕ`.
  set U : Ultrafilter ℕ := Filter.hyperfilter ℕ with hU
  have hUatTop : (↑U : Filter ℕ) ≤ Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop, hU]; exact Filter.hyperfilter_le_cofinite
  -- Weak ultrafilter limit `L` of the relabelled tuples.
  obtain ⟨L, -, hLle⟩ :=
    (isCompact_univ (X := Fin q → ProbabilityMeasure (ℕ → Bool))).ultrafilter_le_nhds
      (U.map (fun n => ρ' n)) (by simp)
  have hLtend : Filter.Tendsto (fun n => ρ' n) (↑U) (𝓝 L) := hLle
  have hLi : ∀ i, Filter.Tendsto (fun n => ρ' n i) (↑U) (𝓝 (L i)) := by
    intro i; exact (tendsto_pi_nhds.mp hLtend) i
  have hcd : ∀ (i : Fin q) (S : Finset ℕ),
      Filter.Tendsto (fun n => cdens q (ρ' n) i S) (↑U) (𝓝 (cdens q L i S)) :=
    fun i S => cdens_tendsto (fun n => ρ' n) L hLi i S
  have hεU : Filter.Tendsto ε (↑U) (𝓝 0) := by
    refine (?_ : Filter.Tendsto ε Filter.atTop (𝓝 0)).mono_left hUatTop
    exact squeeze_zero hε0 hεle tendsto_one_div_add_atTop_nhds_zero_nat
  -- Conclude via the shadow finite-transfer core.
  exact shadow_finish q hq a ha rStar ρ' (fun n => (V n).card) ε hε0 U hεU L hcd C'
    hEdge' hA1' hA2' hA3' hmono (fun n i ℓ hℓ => hρ'dead n i ℓ hℓ) hNoValid'

/-
**Null-blocker compactness (Theorem `thm:compactness`).**

Fix `q ≥ 2`, `a ≥ 1`, and a rank bound `r⋆ ≥ 1`.  There is a threshold
`ε₀ > 0` such that for *every* finite ground set `X`, every family of finite
probability spaces `(Ω i, μ i)` with sets `A i x ⊆ Ω i`, every family of
rank-`≤ r⋆` hypergraphs `C i` of nonempty edges, and every slack
`0 ≤ ε ≤ ε₀` for which

* (A1) `∑ ρ_i(x) ≥ q - 1 - ε` for all `x`,
* (A2) for every `a`-set `S`, `min_i μ_i(⋂_{x∈S} A_i(x)) ≤ ε`,
* (A3) for every `i` and `E ∈ C i`, `min_{j≠i} μ_j(⋂_{x∈E} A_j(x)) ≤ ε`,

there are a deletion set `Z` with `|Z| ≤ a - 1` and a colouring
`φ : X → [q]` such that no edge `E ∈ C i` is monochromatic in colour `i` with
all vertices undeleted.

The proof reduces the system to its Boolean-cube normal form through
`cube_pushforward_nat`; `null_blocker_compactness_normal` then supplies the
shadow-hypergraph finite transfer.
-/
theorem null_blocker_compactness
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a) (rStar : ℕ) (hr : 1 ≤ rStar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (X : Type) [Fintype X]
        (Ω : Fin q → Type) [∀ i, MeasurableSpace (Ω i)]
        (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
        (A : ∀ i, X → Set (Ω i)) (_hA : ∀ i x, MeasurableSet (A i x))
        (C : Fin q → Set (Finset X)) (ε : ℝ),
        0 ≤ ε → ε ≤ ε₀ →
        (∀ i, ∀ E ∈ C i, E.Nonempty ∧ E.card ≤ rStar) →
        (∀ x : X, (q : ℝ) - 1 - ε ≤ ∑ i, dens μ A i x) →
        (∀ S : Finset X, S.card = a → ∃ i, (μ i (⋂ x ∈ S, A i x)).toReal ≤ ε) →
        (∀ i : Fin q, ∀ E ∈ C i, ∃ j, j ≠ i ∧ (μ j (⋂ x ∈ E, A j x)).toReal ≤ ε) →
        ∃ (Z : Finset X) (φ : X → Fin q), Z.card ≤ a - 1 ∧
          ∀ i : Fin q, ∀ E ∈ C i, ¬ (∀ x ∈ E, x ∉ Z ∧ φ x = i) := by
  obtain ⟨ ε₀, hε₀ ⟩ := null_blocker_compactness_normal q hq a ha rStar hr;
  refine' ⟨ ε₀, hε₀.1, fun X _ Ω _ μ _ A hA C ε hε₁ hε₂ hC hN1 hN2 hN3 => _ ⟩;
  obtain ⟨e, he⟩ : ∃ e : X ↪ ℕ, True := by
    exact ⟨ Fintype.equivFin X |> Equiv.toEmbedding |> (fun e => e.trans (Fin.valEmbedding)), trivial ⟩;
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin q → ProbabilityMeasure (ℕ → Bool), ∀ i, ∀ S : Finset X, ((ρ i).toMeasure {σ : ℕ → Bool | ∀ x ∈ S, σ (e x) = true}).toReal = (μ i (⋂ x ∈ S, A i x)).toReal := by
    have h_cube_pushforward : ∀ i, ∃ ρ : Measure (ℕ → Bool), IsProbabilityMeasure ρ ∧ ∀ S : Finset X, ρ {σ : ℕ → Bool | ∀ x ∈ S, σ (e x) = true} = μ i (⋂ x ∈ S, A i x) := by
      exact fun i => cube_pushforward_nat ( μ i ) e ( A i ) ( hA i );
    choose ρ hρ₁ hρ₂ using h_cube_pushforward;
    exact ⟨ fun i => ⟨ ρ i, hρ₁ i ⟩, fun i S => by simp +decide [ hρ₂ i S ] ⟩;
  obtain ⟨Z, φ, hZ, hφ⟩ := hε₀.2 (Finset.image e Finset.univ) ρ (fun i => {E.image e | E ∈ C i}) ε hε₁ hε₂ (by
  simp +zetaDelta only [Set.mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    image_nonempty] at *;
  exact fun i E hE => ⟨ hC i E hE |>.1, by rw [ Finset.card_image_of_injective _ e.injective ] ; exact hC i E hE |>.2, Finset.image_subset_image <| Finset.subset_univ _ ⟩) (by
  simp +decide only [mem_image, mem_univ, true_and, tsub_le_iff_right, forall_exists_index,
    forall_apply_eq_imp_iff];
  intro x; specialize hN1 x; simp +decide [ dens ] at hN1 ⊢;
  convert! hN1 using 1;
  exact congr_arg₂ _ ( congr_arg₂ _ ( Finset.sum_congr rfl fun i _ => by simpa using! hρ i { x } ) rfl ) rfl) (by
  intro S hS₁ hS₂
  obtain ⟨S', hS'⟩ : ∃ S' : Finset X, S = S'.image e := by
    use Finset.filter (fun x => e x ∈ S) Finset.univ;
    grind
  generalize_proofs at *;
  obtain ⟨ i, hi ⟩ := hN2 S' ( by simpa [ hS', Finset.card_image_of_injective _ e.injective ] using! hS₂ ) ; use i; simp +decide [ *, cdens ] ;) (by
  intro i E hE
  obtain ⟨E', hE', rfl⟩ := hE
  obtain ⟨j, hj₁, hj₂⟩ := hN3 i E' hE';
  unfold cdens; simp +decide [ *, Finset.image ] ;);
  refine' ⟨ Finset.filter ( fun x => e x ∈ Z ) Finset.univ, fun x => φ ( e x ), _, _ ⟩;
  · convert! hφ.1 using 1;
    refine' Finset.card_bij ( fun x hx => e x ) _ _ _ <;> simp +decide [ e.injective.eq_iff ];
    exact fun x hx => by have := hZ hx; rw [ Finset.mem_image ] at this; obtain ⟨ y, _, rfl ⟩ := this; exact ⟨ y, by simpa using! hx, rfl ⟩ ;
  · intro i E hE h; specialize hφ; have := hφ.2 i ( Finset.image e E ) ⟨ E, hE, rfl ⟩ ; simp +decide [  ] at this;
    grind +splitIndPred


end Erdos550
