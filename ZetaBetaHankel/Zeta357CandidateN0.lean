import ZetaBetaHankel.USPDCore

/-!
# Finite n=0 admission interface for the Zeta(3), Zeta(5), Zeta(7) miner

This module does not assert cofinality, USPD, or irrationality.  It installs the
exact standalone rational pencils used by the C miner and fixes a conservative
rate packet supported by the first finite search point:

  epsilon3 = 89/100,
  alpha35 = alpha57 = 0,
  C35 = 10,
  C57 = 11.

`N0Admission` is an explicit unresolved finite-point premise.  Its fields say
that the three exact primitive polynomials have degree 37 and satisfy the three
finite inequalities at the profile N=3, K=40, m=3.  The theorem
`good_zero_of_admission` checks that these fields inhabit the common point
predicate with the canonical degree-dominating scale.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open Polynomial

namespace ZetaBetaHankel.Zeta357CandidateN0

/-- Standalone order-(2k+1) rational moment pencil used by the C miner. -/
def singlePencil (k N K m : ℕ) :
    Matrix (Fin (K - N)) (Fin (K - N)) ℚ[X] :=
  fun i j =>
    ZetaBetaHankel.Repaired.muFunctional k
      (ZetaBetaHankel.Repaired.hankelKernel N K m i.1 j.1)

/-- Exact rational determinant of the standalone pencil. -/
def singleDelta (k N K m : ℕ) : ℚ[X] :=
  (singlePencil k N K m).det

/-- Canonical primitive polynomial at N=3(n+1), K=40(n+1), m=3. -/
def primitivePolynomial (k n : ℕ) : ℤ[X] :=
  ZetaBetaHankel.Repaired.primitiveNorm
    (singleDelta k (3 * (n + 1)) (40 * (n + 1)) 3)

/-- Actual odd-zeta centre for the standalone order k. -/
noncomputable def actualZeta (k : ℕ) : ℝ :=
  ZetaBetaHankel.Repaired.riemannZetaReal ((2 * k + 1 : ℕ) : ℝ)

/-- Exact primitive polynomial value at its actual odd-zeta centre. -/
noncomputable def value (k n : ℕ) : ℝ :=
  ZetaBetaHankel.USPD.evalIntPoly (primitivePolynomial k n) (actualZeta k)

/-- Common scale dominating K_n and all three exact polynomial degrees. -/
def scale (n : ℕ) : ℕ :=
  max (40 * (n + 1))
    (max ((primitivePolynomial 1 n).natDegree + 1)
      (max ((primitivePolynomial 2 n).natDegree + 1)
        ((primitivePolynomial 3 n).natDegree + 1)))

/-- Conservative fixed rate packet derived from the first C-miner point. -/
def epsilon3 : ℝ := 89 / 100

def alpha35 : ℝ := 0

def alpha57 : ℝ := 0

def C35 : ℝ := 10

def C57 : ℝ := 11

/-- Weight-three seed inequality at one index. -/
def Seed3At (n : ℕ) : Prop :=
  0 < |value 1 n| ∧
    |value 1 n| ≤ Real.exp (-epsilon3 * ((scale n : ℝ) ^ 2))

/-- Adjacent weight-three to weight-five transfer at one index. -/
def Transfer35At (n : ℕ) : Prop :=
  0 < |value 2 n| ∧
    |value 2 n| ≤
      Real.exp
        (alpha35 * ((scale n : ℝ) ^ 2) +
          C35 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) *
        |value 1 n|

/-- Adjacent weight-five to weight-seven transfer at one index. -/
def Transfer57At (n : ℕ) : Prop :=
  0 < |value 3 n| ∧
    |value 3 n| ≤
      Real.exp
        (alpha57 * ((scale n : ℝ) ^ 2) +
          C57 * (scale n : ℝ) * Real.log ((scale n : ℝ) + 2)) *
        |value 2 n|

/-- Simultaneous finite point predicate. -/
def GoodAt (n : ℕ) : Prop :=
  Seed3At n ∧ Transfer35At n ∧ Transfer57At n

/-- The exact unresolved finite admission corresponding to the first miner hit.
    The inequalities are written at S=40, while the degree fields prove that
    the canonical scale at n=0 is exactly 40. -/
structure N0Admission : Prop where
  degree3 : (primitivePolynomial 1 0).natDegree = 37
  degree5 : (primitivePolynomial 2 0).natDegree = 37
  degree7 : (primitivePolynomial 3 0).natDegree = 37
  seed3_40 :
    0 < |value 1 0| ∧
      |value 1 0| ≤ Real.exp (-epsilon3 * ((40 : ℝ) ^ 2))
  transfer35_40 :
    0 < |value 2 0| ∧
      |value 2 0| ≤
        Real.exp
          (alpha35 * ((40 : ℝ) ^ 2) +
            C35 * (40 : ℝ) * Real.log (42 : ℝ)) *
          |value 1 0|
  transfer57_40 :
    0 < |value 3 0| ∧
      |value 3 0| ≤
        Real.exp
          (alpha57 * ((40 : ℝ) ^ 2) +
            C57 * (40 : ℝ) * Real.log (42 : ℝ)) *
          |value 2 0|

/-- The candidate packet has a strict positive quadratic margin. -/
theorem strict_margin : alpha35 + alpha57 < epsilon3 := by
  norm_num [alpha35, alpha57, epsilon3]

/-- The candidate constants satisfy all sign requirements. -/
theorem rate_signs :
    0 < epsilon3 ∧ 0 ≤ alpha35 ∧ 0 ≤ alpha57 ∧ 0 ≤ C35 ∧ 0 ≤ C57 := by
  norm_num [epsilon3, alpha35, alpha57, C35, C57]

/-- The admitted degree equalities identify the candidate scale with K_0=40. -/
theorem scale_zero_eq_40 (h : N0Admission) : scale 0 = 40 := by
  simp [scale, h.degree3, h.degree5, h.degree7]

/-- The finite admission is accepted by the exact common point interface. -/
theorem good_zero_of_admission (h : N0Admission) : GoodAt 0 := by
  have hs : scale 0 = 40 := scale_zero_eq_40 h
  refine ⟨?_, ?_, ?_⟩
  · simpa [Seed3At, hs] using h.seed3_40
  · have h42 : (40 : ℝ) + 2 = 42 := by norm_num
    simpa [Transfer35At, hs, h42] using h.transfer35_40
  · have h42 : (40 : ℝ) + 2 = 42 := by norm_num
    simpa [Transfer57At, hs, h42] using h.transfer57_40

/-- Future cofinal extension target.  A single `N0Admission` does not inhabit it. -/
def CofinalGood : Prop :=
  ∀ L : ℕ, ∃ n : ℕ, L ≤ n ∧ GoodAt n

/-- A finite point admission and a cofinal extension are deliberately separate. -/
structure CandidateExtension : Prop where
  finite_point : N0Admission
  cofinal_good : CofinalGood

/-- Projection of a completed extension to its cofinal component. -/
theorem cofinal_of_extension (h : CandidateExtension) : CofinalGood :=
  h.cofinal_good

end ZetaBetaHankel.Zeta357CandidateN0
