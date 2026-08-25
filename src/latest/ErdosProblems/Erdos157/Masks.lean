import ErdosProblems.Erdos157.Parabola
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Exponential

/-!
# Independent mask sums

Disjoint nonconstant triple supports induce a surjective homomorphism from
all tag masks to the vector of trial sums. The finite fibers therefore have
equal cardinality. This is the algebraic source of the independent uniform
trials used in the construction.
-/

namespace Erdos157.Elementary.Masks

open Parabola
open scoped BigOperators

variable {K G : Type*} [DecidableEq K] [AddCommGroup G]

/-- The mask sum at an ordered tag triple. -/
def maskSum (t : K × K × K) : (K → G) →+ G where
  toFun τ := τ t.1 + τ t.2.1 + τ t.2.2
  map_zero' := by simp
  map_add' τ σ := by simp only [Pi.add_apply]; abel

omit [DecidableEq K] in
theorem maskSum_apply (t : K × K × K) (τ : K → G) :
    maskSum t τ = τ t.1 + τ t.2.1 + τ t.2.2 := rfl

theorem maskSum_single_of_not_mem {t : K × K × K} {a : K}
    (ha : a ∉ support t) (y : G) : maskSum t (Pi.single a y) = 0 := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  simp [maskSum_apply, Ne.symm ha.1, Ne.symm ha.2.1, Ne.symm ha.2.2]

/-- Choose one tag that occurs exactly once. -/
theorem exists_single_coordinate {t : K × K × K} (ht : 2 ≤ (support t).card) :
    ∃ a ∈ support t, ∀ y : G, maskSum t (Pi.single a y) = y := by
  rcases singleton_coordinate_of_two_le_card ht with h | h | h
  · refine ⟨t.1, by simp [support], ?_⟩
    intro y
    simp [maskSum_apply, Ne.symm h.1, Ne.symm h.2]
  · refine ⟨t.2.1, by simp [support], ?_⟩
    intro y
    simp [maskSum_apply, Ne.symm h.1, Ne.symm h.2]
  · refine ⟨t.2.2, by simp [support], ?_⟩
    intro y
    simp [maskSum_apply, Ne.symm h.1, Ne.symm h.2]

/-- All trial mask sums at once. -/
def maskSums {ι : Type*} (T : ι → K × K × K) : (K → G) →+ (ι → G) where
  toFun τ i := maskSum (T i) τ
  map_zero' := by ext i; exact map_zero _
  map_add' τ σ := by ext i; exact map_add _ _ _

/-- Each prescribed vector of trial sums can be attained independently. -/
theorem maskSums_surjective {ι : Type*} [Fintype ι] (T : ι → K × K × K)
    (hcard : ∀ i, 2 ≤ (support (T i)).card)
    (hdisj : Pairwise (fun i j => Disjoint (support (T i)) (support (T j)))) :
    Function.Surjective (maskSums (G := G) T) := by
  classical
  choose a ha hsingle using fun i => exists_single_coordinate (G := G) (hcard i)
  intro y
  refine ⟨∑ i, Pi.single (a i) (y i), ?_⟩
  ext j
  change maskSum (T j) (∑ i, Pi.single (a i) (y i)) = y j
  rw [map_sum]
  rw [Finset.sum_eq_single j]
  · exact hsingle j (y j)
  · intro i _ hij
    apply maskSum_single_of_not_mem
    intro hmem
    exact Finset.disjoint_left.mp (hdisj hij) (ha i) hmem
  · simp

section FiniteCounting

variable {A B : Type*} [AddGroup A] [AddGroup B] [Fintype A] [Fintype B]
  [DecidableEq B]

omit [Fintype B] in
/-- A surjective homomorphism has equal finite fibers. -/
theorem card_hom_fibers_eq (f : A →+ B) (hf : Function.Surjective f) (x y : B) :
    (Finset.univ.filter fun a => f a = x).card =
      (Finset.univ.filter fun a => f a = y).card := by
  classical
  have h := Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hf x y)
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, Fintype.card_subtype] using h

/-- Exact pullback counting, with no division or nonzero-denominator side conditions. -/
theorem card_hom_preimage_mul (f : A →+ B) (hf : Function.Surjective f) (s : Finset B) :
    (Finset.univ.filter fun a => f a ∈ s).card * Fintype.card B =
      Fintype.card A * s.card := by
  classical
  let c := (Finset.univ.filter fun a => f a = 0).card
  have hfib : ∀ b, (Finset.univ.filter fun a => f a = b).card = c :=
    fun b => card_hom_fibers_eq f hf b 0
  have hall : Fintype.card A = Fintype.card B * c := by
    calc
      _ = ∑ b : B, (Finset.univ.filter fun a => f a = b).card := by
        exact Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      _ = _ := by simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hs : (Finset.univ.filter fun a => f a ∈ s).card = s.card * c := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ s f]
    simp only [hfib, Finset.sum_const, smul_eq_mul]
  rw [hs, hall]
  ring

end FiniteCounting

/-- Under the uniform distribution on masks, the full trial vector is uniform.
This cardinal identity also supplies independence of all its coordinates. -/
theorem maskSums_uniform_count [Fintype K] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → K × K × K)
    (hcard : ∀ i, 2 ≤ (support (T i)).card)
    (hdisj : Pairwise (fun i j => Disjoint (support (T i)) (support (T j))))
    (s : Finset (ι → G)) :
    (Finset.univ.filter fun τ : K → G => maskSums T τ ∈ s).card * Fintype.card (ι → G) =
      Fintype.card (K → G) * s.card := by
  let f : (K → G) →+ (ι → G) := maskSums T
  have hf : Function.Surjective f := maskSums_surjective (G := G) T hcard hdisj
  exact card_hom_preimage_mul f hf s

section FailureCount

variable [Fintype K] [Fintype G] [DecidableEq G]

/-- Masks for which none of the indexed trials hits the desired set. -/
def missedMasks {n : ℕ} (T : Fin n → K × K × K) (s : Finset G) : Finset (K → G) :=
  Finset.univ.filter fun τ => ∀ i, maskSum (T i) τ ∉ s

/-- The exact count of simultaneous failures. -/
theorem missedMasks_card {n : ℕ} (T : Fin n → K × K × K)
    (hcard : ∀ i, 2 ≤ (support (T i)).card)
    (hdisj : Pairwise (fun i j => Disjoint (support (T i)) (support (T j))))
    (s : Finset G) :
    (missedMasks T s).card * Fintype.card G ^ n =
      Fintype.card G ^ Fintype.card K * (Fintype.card G - s.card) ^ n := by
  have h := maskSums_uniform_count T hcard hdisj
    (Fintype.piFinset (fun _ : Fin n => sᶜ))
  simpa only [Fintype.mem_piFinset, Finset.mem_compl, maskSums,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_piFinset_const, Finset.card_compl, missedMasks] using h

/-- Dividing the finite count gives the familiar independent-trial failure probability. -/
theorem missedMasks_density {n : ℕ} (T : Fin n → K × K × K)
    (hcard : ∀ i, 2 ≤ (support (T i)).card)
    (hdisj : Pairwise (fun i j => Disjoint (support (T i)) (support (T j))))
    (s : Finset G) :
    ((missedMasks T s).card : ℝ) / (Fintype.card G : ℝ) ^ Fintype.card K =
      (1 - (s.card : ℝ) / Fintype.card G) ^ n := by
  have h := missedMasks_card T hcard hdisj s
  have hsub : s.card ≤ Fintype.card G := Finset.card_le_univ s
  have hr : ((missedMasks T s).card : ℝ) * (Fintype.card G : ℝ) ^ n =
      (Fintype.card G : ℝ) ^ Fintype.card K * ((Fintype.card G : ℝ) - s.card) ^ n := by
    exact_mod_cast h
  have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hratio : 1 - (s.card : ℝ) / Fintype.card G =
      ((Fintype.card G : ℝ) - s.card) / Fintype.card G := by
    rw [sub_div, div_self hpos.ne']
  rw [hratio, div_pow]
  apply (div_eq_div_iff (pow_ne_zero _ hpos.ne') (pow_ne_zero _ hpos.ne')).mpr
  simpa only [mul_comm] using hr

/-- The exponential failure estimate used in the union bound over all targets. -/
theorem missedMasks_density_le_exp {n : ℕ} (T : Fin n → K × K × K)
    (hcard : ∀ i, 2 ≤ (support (T i)).card)
    (hdisj : Pairwise (fun i j => Disjoint (support (T i)) (support (T j))))
    (s : Finset G) :
    ((missedMasks T s).card : ℝ) / (Fintype.card G : ℝ) ^ Fintype.card K ≤
      Real.exp (-(n : ℝ) * ((s.card : ℝ) / Fintype.card G)) := by
  rw [missedMasks_density T hcard hdisj s]
  have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hsub : (s.card : ℝ) ≤ Fintype.card G := by exact_mod_cast Finset.card_le_univ s
  have hnonneg : 0 ≤ 1 - (s.card : ℝ) / Fintype.card G := by
    have := (div_le_one hpos).mpr hsub
    linarith
  calc
    _ ≤ (Real.exp (-((s.card : ℝ) / Fintype.card G))) ^ n :=
      pow_le_pow_left₀ hnonneg (Real.one_sub_le_exp_neg _) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end FailureCount

end Erdos157.Elementary.Masks
