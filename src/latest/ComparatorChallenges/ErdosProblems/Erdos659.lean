import Mathlib

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise

structure BinQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ
namespace BinQuadForm

def eval (f : BinQuadForm) (x y : ℤ) : ℤ :=
  f.a * x * x + f.b * x * y + f.c * y * y

def discr (f : BinQuadForm) : ℤ :=
  f.b * f.b - 4 * f.a * f.c

def Primitive (f : BinQuadForm) : Prop :=
  Int.gcd f.a (Int.gcd f.b f.c) = 1

def PosDef (f : BinQuadForm) : Prop :=
  0 < f.a ∧ f.discr < 0

noncomputable def B (f : BinQuadForm) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)}
end BinQuadForm

axiom bernays
    (Δ : ℤ) (hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ) :
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x))

namespace Erdos659

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 50000000

open scoped Real

open Filter

open Asymptotics

open Finset Real

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card
end Erdos659

attribute [local instance] Classical.propDecidable

open scoped Real
open Filter
open Asymptotics
open EuclideanGeometry Finset Real

namespace Erdos659

theorem erdos_659 : ∃ A : ℕ → Finset ℝ²,
   (∀ n, #(A n) = n ∧ ∀ S ⊆ A n, #S = 4 → 3 ≤ distinctDistances S) ∧
    (fun n ↦ distinctDistances (A n)) ≪ fun n ↦ n / sqrt (log n) := by
  sorry

end Erdos659
