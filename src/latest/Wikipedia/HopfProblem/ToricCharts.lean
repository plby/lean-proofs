import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Holomorphic monomial charts for the cusp filling

The affine charts in §4 of `tex/s6.tex` have integral monomial transition
functions. Negative exponents are allowed only where the corresponding
coordinate is nonzero. This file constructs the resulting partial
biholomorphisms, including their inverses on boundary strata. No global toric
space or Hausdorff gluing is assumed here.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricCharts

variable {d : ℕ}

abbrev CoordinateSpace (d : ℕ) := Fin d → ℂ

def torus : Set (CoordinateSpace d) := {z | ∀ j, z j ≠ 0}

theorem torus_open : IsOpen (torus : Set (CoordinateSpace d)) := by
  unfold torus
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_ne_fun (continuous_apply j) continuous_const

theorem torus_dense : Dense (torus : Set (CoordinateSpace d)) := by
  simpa [torus, Set.pi] using
    (dense_pi (Set.univ : Set (Fin d)) fun _ _ => dense_compl_singleton (0 : ℂ))

/-- An integral matrix acts by monomials, with rows indexing the outputs. -/
def monomial (A : Matrix (Fin d) (Fin d) ℤ) (z : CoordinateSpace d) :
    CoordinateSpace d := fun i => ∏ j, z j ^ A i j

/-- The natural holomorphic domain of the displayed Laurent monomials. -/
def domain (A : Matrix (Fin d) (Fin d) ℤ) : Set (CoordinateSpace d) :=
  {z | ∀ i j, A i j < 0 → z j ≠ 0}

theorem domain_open (A : Matrix (Fin d) (Fin d) ℤ) : IsOpen (domain A) := by
  unfold domain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : A i j < 0
  · simpa [h] using isOpen_ne_fun (continuous_apply j) continuous_const
  · simp [h]

theorem torus_subset_domain (A : Matrix (Fin d) (Fin d) ℤ) : torus ⊆ domain A :=
  fun _ hz _ j _ => hz j

theorem monomial_mapsTo_torus (A : Matrix (Fin d) (Fin d) ℤ) :
    MapsTo (monomial A) torus torus := by
  intro z hz i
  exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hz j)

theorem monomial_contDiffOn (A : Matrix (Fin d) (Fin d) ℤ) (n : ℕ∞ω) :
    ContDiffOn ℂ n (monomial A) (domain A) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_prod
  intro j _
  cases h : A i j with
  | ofNat k =>
      simpa only [h, Int.ofNat_eq_natCast, zpow_natCast] using
        (contDiff_apply ℂ ℂ j).contDiffOn.pow k
  | negSucc k =>
      have hn : A i j < 0 := by omega
      intro z hz
      simpa only [h, zpow_negSucc] using
        ((contDiff_apply ℂ ℂ j).contDiffWithinAt.pow (k + 1)).fun_inv
          (pow_ne_zero _ (hz i j hn))

private theorem prod_zpow_eq (a : ℂ) (ha : a ≠ 0) (s : Finset (Fin d))
    (k : Fin d → ℤ) : (∏ i ∈ s, a ^ k i) = a ^ ∑ i ∈ s, k i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

theorem monomial_mul_on_torus (A B : Matrix (Fin d) (Fin d) ℤ)
    {z : CoordinateSpace d} (hz : z ∈ torus) :
    monomial A (monomial B z) = monomial (A * B) z := by
  funext i
  simp only [monomial, Matrix.mul_apply]
  calc
    (∏ k, (∏ j, z j ^ B k j) ^ A i k)
        = ∏ k, ∏ j, z j ^ (A i k * B k j) := by
            apply Finset.prod_congr rfl
            intro k _
            rw [← Finset.prod_zpow]
            apply Finset.prod_congr rfl
            intro j _
            rw [← zpow_mul, mul_comm]
    _ = ∏ j, ∏ k, z j ^ (A i k * B k j) := Finset.prod_comm
    _ = ∏ j, z j ^ ∑ k, A i k * B k j := by
          apply Finset.prod_congr rfl
          intro j _
          exact prod_zpow_eq (z j) (hz j) _ _

@[simp] theorem monomial_one (z : CoordinateSpace d) : monomial 1 z = z := by
  funext i
  simp [monomial, Matrix.one_apply]

theorem monomial_mul (A : Matrix (Fin d) (Fin d) ℤ) (z w : CoordinateSpace d) :
    monomial A (z * w) = monomial A z * monomial A w := by
  funext i
  simp [monomial, mul_zpow, Finset.prod_mul_distrib]

@[simp] theorem monomial_ones (A : Matrix (Fin d) (Fin d) ℤ) : monomial A 1 = 1 := by
  funext i
  simp [monomial]

/-- Both directions must be defined; this includes the boundary strata on
which an integral change of toric coordinates is a local isomorphism. -/
def overlap (A B : Matrix (Fin d) (Fin d) ℤ) : Set (CoordinateSpace d) :=
  domain A ∩ monomial A ⁻¹' domain B

theorem overlap_open (A B : Matrix (Fin d) (Fin d) ℤ) : IsOpen (overlap A B) :=
  (monomial_contDiffOn A 0).continuousOn.isOpen_inter_preimage
    (domain_open A) (domain_open B)

theorem torus_subset_overlap (A B : Matrix (Fin d) (Fin d) ℤ) :
    torus ⊆ overlap A B := fun _ hz =>
  ⟨torus_subset_domain A hz, torus_subset_domain B (monomial_mapsTo_torus A hz)⟩

theorem monomial_inverse_on_overlap (A B : Matrix (Fin d) (Fin d) ℤ)
    (hBA : B * A = 1) : EqOn (monomial B ∘ monomial A) id (overlap A B) := by
  have h : EqOn (monomial B ∘ monomial A) id (overlap A B ∩ torus) := by
    intro z hz
    simpa [hBA] using monomial_mul_on_torus B A hz.2
  refine h.of_subset_closure ?_ continuousOn_id inter_subset_left
    (torus_dense.open_subset_closure_inter (overlap_open A B))
  exact (monomial_contDiffOn B 0).continuousOn.comp
    ((monomial_contDiffOn A 0).continuousOn.mono inter_subset_left)
    (fun _ hz => hz.2)

/-- The actual partial homeomorphism defined by mutually inverse integral
monomial substitutions. The holomorphic assertions are proved below. -/
def changeOfCoordinates (A B : Matrix (Fin d) (Fin d) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    OpenPartialHomeomorph (CoordinateSpace d) (CoordinateSpace d) where
  toFun := monomial A
  invFun := monomial B
  source := overlap A B
  target := overlap B A
  map_source' z hz := ⟨hz.2, by
    change (monomial B ∘ monomial A) z ∈ domain A
    rw [monomial_inverse_on_overlap A B hBA hz]
    exact hz.1⟩
  map_target' z hz := ⟨hz.2, by
    change (monomial A ∘ monomial B) z ∈ domain B
    rw [monomial_inverse_on_overlap B A hAB hz]
    exact hz.1⟩
  left_inv' := monomial_inverse_on_overlap A B hBA
  right_inv' := monomial_inverse_on_overlap B A hAB
  open_source := overlap_open A B
  open_target := overlap_open B A
  continuousOn_toFun := (monomial_contDiffOn A 0).continuousOn.mono inter_subset_left
  continuousOn_invFun := (monomial_contDiffOn B 0).continuousOn.mono inter_subset_left

theorem changeOfCoordinates_holomorphic (A B : Matrix (Fin d) (Fin d) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ContDiffOn ℂ ω (changeOfCoordinates A B hAB hBA)
      (changeOfCoordinates A B hAB hBA).source :=
  (monomial_contDiffOn A ω).mono inter_subset_left

theorem changeOfCoordinates_symm_holomorphic (A B : Matrix (Fin d) (Fin d) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ContDiffOn ℂ ω (changeOfCoordinates A B hAB hBA).symm
      (changeOfCoordinates A B hAB hBA).target :=
  (monomial_contDiffOn B ω).mono inter_subset_left

/-- Exponent matrices between height-one bases have every column sum equal
to one. This controls which coordinate hyperplanes can meet an overlap. -/
def HeightOne (A : Matrix (Fin 3) (Fin 3) ℤ) : Prop := ∀ j, ∑ i, A i j = 1

theorem column_single_of_zero {A : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) {z : CoordinateSpace 3} (hz : z ∈ domain A)
    {j : Fin 3} (hj : z j = 0) :
    ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 := by
  have hn (i : Fin 3) : 0 ≤ A i j := by
    by_contra h
    exact hz i j (lt_of_not_ge h) hj
  have hsum := hA j
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.sum_univ_zero, add_zero] at hsum
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have hcases : A 0 j = 1 ∨ A 1 j = 1 ∨ A 2 j = 1 := by omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega

theorem monomial_zero_of_column_single {A : Matrix (Fin 3) (Fin 3) ℤ}
    {z : CoordinateSpace 3} {j k : Fin 3} (hj : z j = 0)
    (hc : ∀ i, A i j = if i = k then 1 else 0) : monomial A z k = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj, hc]

theorem inverse_mapsTo_domain {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) (hBA : B * A = 1) :
    MapsTo (monomial A) (domain A) (domain B) := by
  intro z hz i k hB hzero
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hzj : z j = 0 := eq_zero_of_zpow_eq_zero hj
  have hAj : A k j ≠ 0 := by
    intro he
    simp [he] at hj
  obtain ⟨l, hl⟩ := column_single_of_zero hA hz hzj
  have hkl : k = l := by
    by_contra h
    exact hAj (by simp [hl, h])
  subst l
  have hentry := congrFun (congrFun hBA i) j
  have hnonneg : 0 ≤ B i k := by
    have he : B i k = (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
      simpa [Matrix.mul_apply, hl] using hentry
    rw [he, Matrix.one_apply]
    split_ifs <;> norm_num
  exact (not_lt_of_ge hnonneg) hB

theorem overlap_eq_domain {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) (hBA : B * A = 1) : overlap A B = domain A := by
  exact inter_eq_left.mpr (inverse_mapsTo_domain hA hBA)

theorem domain_composition {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) : overlap A B ⊆ domain (B * A) := by
  intro z hz i j hC hzj
  obtain ⟨k, hk⟩ := column_single_of_zero hA hz.1 hzj
  have hzAk : monomial A z k = 0 := monomial_zero_of_column_single hzj hk
  have hBk : B i k < 0 := by
    simpa [Matrix.mul_apply, hk] using hC
  exact hz.2 i k hBk hzAk

/-- Cocycle identities hold on the entire overlap, not only on its torus. -/
theorem monomial_mul_on_overlap {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) : EqOn (monomial B ∘ monomial A)
      (monomial (B * A)) (overlap A B) := by
  have h : EqOn (monomial B ∘ monomial A) (monomial (B * A))
      (overlap A B ∩ torus) := fun _ hz => monomial_mul_on_torus B A hz.2
  refine h.of_subset_closure ?_ ?_ inter_subset_left
    (torus_dense.open_subset_closure_inter (overlap_open A B))
  · exact (monomial_contDiffOn B 0).continuousOn.comp
      ((monomial_contDiffOn A 0).continuousOn.mono inter_subset_left)
      (fun _ hz => hz.2)
  · exact (monomial_contDiffOn (B * A) 0).continuousOn.mono (domain_composition hA)

end Wikipedia.HopfProblem.ToricCharts
