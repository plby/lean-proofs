import Wikipedia.NoExoticSixSphere.FiniteEnergyMovement
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.ContinuousOn

/-!
# Prefix data for a finite controlled lowering construction

A prefix records its actual continuous endpoint families, relative homotopy,
and all one-step energy and movement bounds. The movement theorem proves
membership in a later crossing neighborhood for high-energy parameters.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [PseudoMetricSpace Y]

structure Prefix (energy : Y → ℝ) (admissible : Set Y) (p₀ : C(M, Y))
    (F : ℕ → Set Y) (k : ℕ → ℝ) (floor A cap ξ ζ ρ : ℝ) (i : ℕ) where
  family : ℕ → C(M, Y)
  initial : family 0 = p₀
  mem : ∀ j ≤ i, ∀ x, family j x ∈ admissible
  gain : ∀ j < i, ∀ x, energy (family (j + 1) x) ≤ energy (family j x) + ξ
  movement : ∀ j < i, ∀ x,
    energy (family j x) - energy (family (j + 1) x) ≤ 2 * ζ →
      dist (family (j + 1) x) (family j x) ≤ ρ
  lowered : ∀ j < i, ∀ x, p₀ x ∈ F j → A ≤ energy (family j x) →
    energy (family (j + 1) x) < k j
  homotopy : ContinuousMap.HomotopyRel p₀ (family i) {x | energy (p₀ x) ≤ floor}
  control : ∀ t x, homotopy (t, x) ∈ admissible ∧
    energy (homotopy (t, x)) ≤ max (energy (p₀ x)) cap

def initialPrefix (energy : Y → ℝ) (admissible : Set Y) (p₀ : C(M, Y))
    (F : ℕ → Set Y) (k : ℕ → ℝ) (floor A cap ξ ζ ρ : ℝ)
    (hp₀ : ∀ x, p₀ x ∈ admissible) : Prefix energy admissible p₀ F k floor A cap ξ ζ ρ 0 where
  family _ := p₀
  initial := rfl
  mem := fun _ _ x ↦ hp₀ x
  gain := fun _ hj ↦ (Nat.not_lt_zero _ hj).elim
  movement := fun _ hj ↦ (Nat.not_lt_zero _ hj).elim
  lowered := fun _ hj ↦ (Nat.not_lt_zero _ hj).elim
  homotopy := ContinuousMap.HomotopyRel.refl p₀ _
  control := fun _ x ↦ ⟨hp₀ x, le_max_left _ _⟩

namespace Prefix

variable {energy : Y → ℝ} {admissible : Set Y} {p₀ : C(M, Y)}
  {F : ℕ → Set Y} {k : ℕ → ℝ} {floor A cap ξ ζ ρ : ℝ} {i : ℕ}
  (P : Prefix energy admissible p₀ F k floor A cap ξ ζ ρ i)

theorem endpoint_cap (x : M) : energy (P.family i x) ≤ max (energy (p₀ x)) cap := by
  simpa only [P.homotopy.apply_one] using (P.control 1 x).2

theorem endpoint_fixed {x : M} (hx : energy (p₀ x) ≤ floor) : P.family i x = p₀ x :=
  (P.homotopy.fst_eq_snd hx).symm

theorem mem_domain_of_high {n : ℕ} (hin : i ≤ n) (hξ : 0 ≤ ξ) (hρ : 0 ≤ ρ)
    (B : ℝ) (hstart : ∀ x, energy (p₀ x) ≤ B)
    (hbudget : B - A + 2 * (n : ℝ) * ξ ≤ 2 * ζ)
    (K V : Set Y) (hfit : ∀ y ∈ K, ∀ z, dist z y ≤ (n : ℝ) * ρ → z ∈ V)
    {x : M} (hx : p₀ x ∈ K) (hhigh : A ≤ energy (P.family i x)) : P.family i x ∈ V := by
  have hiξ : (i : ℝ) * ξ ≤ (n : ℝ) * ξ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hin) hξ
  have hiρ : (i : ℝ) * ρ ≤ (n : ℝ) * ρ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hin) hρ
  have hbudget' : B - A + 2 * (i : ℝ) * ξ ≤ 2 * ζ := by linarith
  have hstart' : energy (P.family 0 x) ≤ B := by rw [P.initial]; exact hstart x
  have hd := FiniteEnergyMovement.displacement_le_of_high_endpoint energy (fun j ↦ P.family j x)
    i ξ ζ ρ A B hξ (fun j hj ↦ P.gain j hj x) (fun j hj ↦ P.movement j hj x)
    hstart' hhigh hbudget'
  rw [P.initial] at hd
  exact hfit (p₀ x) hx (P.family i x) (hd.trans hiρ)

end Prefix

end NoExoticSixSphere.FiniteControlledLowering
