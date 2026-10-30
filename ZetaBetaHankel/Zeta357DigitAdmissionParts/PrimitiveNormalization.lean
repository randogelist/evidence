import ZetaBetaHankel.Zeta357DigitAdmissionParts.Base

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Literal rational coefficient normalization, tied to the original primitiveNorm. -/
namespace ZetaBetaHankel.Zeta357CanonicalArithmetic

open scoped BigOperators
open Polynomial ZetaBetaHankel.Zeta357DigitAdmission

def ratAt : List ℚ → ℕ → ℚ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n + 1 => ratAt as n

theorem ratAt_out (cs : List ℚ) (j : ℕ) (hj : cs.length ≤ j) : ratAt cs j = 0 := by
  induction cs generalizing j with
  | nil => rfl
  | cons a cs ih =>
    cases j with
    | zero => simp at hj
    | succ j =>
      change ratAt cs j = 0
      apply ih
      simpa only [List.length_cons, Nat.succ_le_succ_iff] using hj

def rationalLiteral (cs : List ℚ) : ℚ[X] :=
  ∑ j ∈ Finset.range cs.length, Polynomial.monomial j (ratAt cs j)

theorem rationalLiteral_coeff (cs : List ℚ) (j : ℕ) :
    (rationalLiteral cs).coeff j = ratAt cs j := by
  classical
  unfold rationalLiteral
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · exact Polynomial.coeff_monomial_same j (ratAt cs j)
  · intro b hb hbj
    simp only [Polynomial.coeff_monomial, if_neg hbj]
  · intro hj
    rw [Polynomial.coeff_monomial_same]
    apply ratAt_out
    exact Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))

theorem rationalLiteral_support (cs : List ℚ)
    (hne : ∀ j : Fin cs.length, ratAt cs j.val ≠ 0) :
    (rationalLiteral cs).support = Finset.range cs.length := by
  ext j
  rw [Polynomial.mem_support_iff, rationalLiteral_coeff, Finset.mem_range]
  constructor
  · intro hj
    by_contra h
    exact hj (ratAt_out cs j (Nat.le_of_not_gt h))
  · intro hj
    exact hne ⟨j, hj⟩

def coordinateDenominator (cs : List ℚ) : ℕ :=
  (Finset.range cs.length).lcm (fun j => (ratAt cs j).den)

def coordinateGCD (cs : List ℚ) : ℕ :=
  (Finset.range cs.length).gcd
    (fun j => ((ratAt cs j) * (coordinateDenominator cs : ℚ)).num.natAbs)

def coordinateContent (cs : List ℚ) : ℚ :=
  (coordinateGCD cs : ℚ) / (coordinateDenominator cs : ℚ)

theorem ratContent_literal (cs : List ℚ)
    (hne : ∀ j : Fin cs.length, ratAt cs j.val ≠ 0) :
    ZetaBetaHankel.Repaired.ratContent (rationalLiteral cs) = coordinateContent cs := by
  unfold ZetaBetaHankel.Repaired.ratContent coordinateContent coordinateGCD coordinateDenominator
  rw [rationalLiteral_support cs hne]
  simp only [rationalLiteral_coeff]

/-- All arithmetic hypotheses are finite checks on literal lists.
The conclusion uses the unchanged source primitive normalization. -/
theorem primitiveNorm_literal (rs : List ℚ) (zs : List ℤ)
    (hl : rs.length = zs.length)
    (hz : 0 < zs.length)
    (hne : ∀ j : Fin rs.length, ratAt rs j.val ≠ 0)
    (hc : ∀ j : Fin rs.length,
      ((ratAt rs j.val) / coordinateContent rs).num = coeffAt zs j.val) :
    ZetaBetaHankel.Repaired.primitiveNorm (rationalLiteral rs) = polyOfCoeffs zs := by
  classical
  have hr : 0 < rs.length := by omega
  have hp : rationalLiteral rs ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : ℚ[X] => p.coeff 0) h
    rw [rationalLiteral_coeff, Polynomial.coeff_zero] at h0
    exact hne ⟨0, hr⟩ h0
  unfold ZetaBetaHankel.Repaired.primitiveNorm
  rw [if_neg hp, rationalLiteral_support rs hne, ratContent_literal rs hne]
  apply Polynomial.ext
  intro j
  rw [Polynomial.finsetSum_coeff, coeff_polyOfCoeffs]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_monomial_same, rationalLiteral_coeff]
    by_cases hj : j < rs.length
    · exact hc ⟨j, hj⟩
    · rw [ratAt_out rs j (Nat.le_of_not_gt hj), zero_div, Rat.num_zero]
      symm
      apply coeffAt_eq_zero_of_length_le
      omega
  · intro b hb hbj
    simp only [Polynomial.coeff_monomial, if_neg hbj]
  · intro hj
    rw [Polynomial.coeff_monomial_same, rationalLiteral_coeff]
    have ho : rs.length ≤ j :=
      Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    rw [ratAt_out rs j ho, zero_div, Rat.num_zero]

end ZetaBetaHankel.Zeta357CanonicalArithmetic
