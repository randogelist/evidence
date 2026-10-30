import Mathlib

/-!
# Exact source-model of the coupled odd-zeta determinant

This is a purposefully limited, NO-SORRY extraction of the user's uploaded
Formalization Blueprint. Definitions of the rational moments, Hankel kernel,
coupled pencil, and primitive integer polynomial use the source formulas.

No analytic Gram identity or arithmetic decay estimate is asserted here.
In the original source, the coupled weight-five/three case is `k = 1`.
No local Lean compilation has been performed for this package.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ZetaBetaHankel.Repaired

/-- Source Definition 0: the genuine real zeta Dirichlet series. -/
noncomputable def riemannZetaReal (s : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else (n : ℝ) ^ (-s)

/-- Source generalized rational harmonic number. -/
def harmonicGen (s j : ℕ) : ℚ :=
  ∑ ν ∈ Finset.Icc 1 j, ((ν : ℚ) ^ s)⁻¹

/-- The source square-pole factors. -/
def D_poly (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.Icc 1 N, (Polynomial.X + Polynomial.C ((j : ℚ) ^ 2))

/-- The source tail denominator. -/
def D_tail (N K : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.Icc (N + 1) K, (Polynomial.X + Polynomial.C ((j : ℚ) ^ 2))

/-- Normal-form input for the Q-linear functional. -/
structure RatInV where
  polyPart : ℚ[X]
  poleSupport : Finset ℕ
  poleSupport_pos : ∀ j ∈ poleSupport, 1 ≤ j
  residue : ℕ → ℚ

/-- Definition 2.1, monomial moments. -/
def muMonomial (k e : ℕ) : ℚ :=
  ((-1 : ℚ) ^ e) * _root_.bernoulli (2 * e + 2) *
    (Nat.factorial (2 * e + 2 * k + 1) : ℚ) /
      ((Nat.factorial (2 * k) : ℚ) * (Nat.factorial (2 * e + 2) : ℚ))

/-- Definition 2.1, simple square-pole moments. -/
def muPole (k j : ℕ) : ℚ[X] :=
  Polynomial.C ((j : ℚ) ^ (2 * k)) *
    (Polynomial.X - Polynomial.C (harmonicGen (2 * k + 1) j)) +
  Polynomial.C (1 / (2 * (j : ℚ)) - 1 / (2 * (k : ℚ)))

/-- Definition 2.1, the rational functional in normal-form coordinates. -/
def muFunctional (k : ℕ) (R : RatInV) : ℚ[X] :=
  (∑ e ∈ R.polyPart.support,
    Polynomial.C (R.polyPart.coeff e * muMonomial k e)) +
  (∑ j ∈ R.poleSupport,
    Polynomial.C (R.residue j) * muPole k j)

/-- Euclidean quotient plus the residues at all simple tail poles. -/
def ofNumOverTail (N K : ℕ) (P : ℚ[X]) : RatInV where
  polyPart := P /ₘ (D_tail N K)
  poleSupport := Finset.Icc (N + 1) K
  poleSupport_pos := by
    intro j hj
    have hj' := (Finset.mem_Icc.mp hj).1
    omega
  residue := fun a =>
    if N + 1 ≤ a ∧ a ≤ K then
      ((P %ₘ (D_tail N K)).eval (- ((a : ℚ) ^ 2))) /
        ((Polynomial.derivative (D_tail N K)).eval (- ((a : ℚ) ^ 2)))
    else 0

/-- The exact source kernel D_N^(2m) t^(i+j) / D_K. -/
def hankelKernel (N K m i j : ℕ) : RatInV :=
  ofNumOverTail N K ((D_poly N) ^ (2 * m - 1) * Polynomial.X ^ (i + j))

/-- The kernel multiplied by t, represented by its exact numerator. -/
def shiftedHankelKernel (N K m i j : ℕ) : RatInV :=
  ofNumOverTail N K ((D_poly N) ^ (2 * m - 1) * Polynomial.X ^ (i + j + 1))

/-- The derivative matrix of the higher odd weight s+2 = 2k+3. -/
def M_high (k N K m : ℕ) : Matrix (Fin (K - N)) (Fin (K - N)) ℚ :=
  fun i j => (muFunctional (k + 1) (hankelKernel N K m i.1 j.1)).coeff 1

/-- Its rational constant matrix. -/
def A_high (k N K m : ℕ) : Matrix (Fin (K - N)) (Fin (K - N)) ℚ :=
  fun i j => (muFunctional (k + 1) (hankelKernel N K m i.1 j.1)).eval 0

/-- The original coupled matrix as a Q[X]-valued affine pencil. -/
def G_coupled (k : ℕ) (a b : ℤ) (N K m : ℕ) :
    Matrix (Fin (K - N)) (Fin (K - N)) ℚ[X] :=
  fun i j =>
    let R := hankelKernel N K m i.1 j.1
    let tR := shiftedHankelKernel N K m i.1 j.1
    let c : ℚ :=
      (b : ℚ) * (muFunctional (k + 1) R).eval 0 -
      (a : ℚ) * (muFunctional k tR).eval 0
    Polynomial.C c + Polynomial.C (M_high k N K m i j) * Polynomial.X

/-- Exact determinant of the coupled pencil. -/
def Delta_coupled (k : ℕ) (a b : ℤ) (N K m : ℕ) : ℚ[X] :=
  (G_coupled k a b N K m).det

/-- Original blueprint rational content. -/
def ratContent (P : ℚ[X]) : ℚ :=
  let d : ℕ := P.support.lcm (fun j => (P.coeff j).den)
  let g : ℕ := P.support.gcd (fun j => ((P.coeff j) * (d : ℚ)).num.natAbs)
  (g : ℚ) / (d : ℚ)

/-- The exact blueprint's integer primitive normalization, not an axiom. -/
def primitiveNorm (P : ℚ[X]) : ℤ[X] :=
  if P = 0 then 0
  else
    let c := ratContent P
    ∑ j ∈ P.support, Polynomial.monomial j ((P.coeff j / c).num)

/-- Fixed geometric family: N=3n, K=40n, m=3. -/
def canonicalCoupled (k n : ℕ) (a b : ℤ) : ℤ[X] :=
  primitiveNorm (Delta_coupled k a b (3 * n) (40 * n) 3)

/-- Target constant with the *original* odd zeta series on both weights. -/
noncomputable def xiCoupled (k : ℕ) (a b : ℤ) : ℝ :=
  (b : ℝ) * riemannZetaReal ((2 * k + 3 : ℕ) : ℝ) +
  (a : ℝ) * riemannZetaReal ((2 * k + 1 : ℕ) : ℝ)

/-- Strict positive cone from the B-tier analytic density argument. -/
def InPositiveCone (k : ℕ) (a b : ℤ) : Prop :=
  0 < b ∧
    (a : ℝ) <
      (4 * Real.pi ^ 2 /
        (((2 * k + 1 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ))) * (b : ℝ)

end ZetaBetaHankel.Repaired
