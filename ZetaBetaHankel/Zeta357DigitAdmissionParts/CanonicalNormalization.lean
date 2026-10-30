import ZetaBetaHankel.Zeta357DigitAdmissionParts.PrimitiveNormalization
import ZetaBetaHankel.Zeta357DigitAdmissionParts.CanonicalData3
import ZetaBetaHankel.Zeta357DigitAdmissionParts.CanonicalData5
import ZetaBetaHankel.Zeta357DigitAdmissionParts.CanonicalData7

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Exact normalization of the certified rational source determinant. -/
namespace ZetaBetaHankel.Zeta357CanonicalArithmetic

open Polynomial ZetaBetaHankel.Zeta357DigitAdmission
open ZetaBetaHankel.Zeta357Canonical

theorem ratAt_scaled_int (q : ℚ) (cs : List ℤ) (j : ℕ) :
    ratAt (cs.map (fun z => q * (z : ℚ))) j = q * (coeffAt cs j : ℚ) := by
  induction cs generalizing j with
  | nil => simp [ratAt, coeffAt]
  | cons a cs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

theorem scaled_poly_eq_rationalLiteral (q : ℚ) (cs : List ℤ) :
    Polynomial.C q * (polyOfCoeffs cs).map (Int.castRingHom ℚ) =
      rationalLiteral (cs.map (fun z => q * (z : ℚ))) := by
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, coeff_polyOfCoeffs,
    rationalLiteral_coeff, ratAt_scaled_int]

def sourceRationalCoeffs (D : ℤ) (cs : List ℤ) : List ℚ :=
  cs.map (fun z => ((D : ℚ)⁻¹) ^ 37 * (z : ℚ))

theorem source_scaled_normalization (D : ℤ) (raw cs : List ℤ)
    (hl : (sourceRationalCoeffs D raw).length = cs.length)
    (hz : 0 < cs.length)
    (hne : ∀ j : Fin (sourceRationalCoeffs D raw).length,
      ratAt (sourceRationalCoeffs D raw) j.val ≠ 0)
    (hc : ∀ j : Fin (sourceRationalCoeffs D raw).length,
      ((ratAt (sourceRationalCoeffs D raw) j.val) /
        coordinateContent (sourceRationalCoeffs D raw)).num = coeffAt cs j.val) :
    ZetaBetaHankel.Repaired.primitiveNorm
      (Polynomial.C (((D : ℚ)⁻¹) ^ 37) *
        (polyOfCoeffs raw).map (Int.castRingHom ℚ)) = polyOfCoeffs cs := by
  rw [scaled_poly_eq_rationalLiteral]
  exact primitiveNorm_literal (sourceRationalCoeffs D raw) cs hl hz hne hc


theorem normalization3_checked :
    ZetaBetaHankel.Repaired.primitiveNorm
      (Polynomial.C (((commonDen3 : ℚ)⁻¹) ^ 37) *
        (polyOfCoeffs rawCoeffs3).map (Int.castRingHom ℚ)) = polyOfCoeffs coeff3 := by
  exact source_scaled_normalization commonDen3 rawCoeffs3 coeff3
    (by decide) (by decide) (by decide) (by decide)

theorem normalization5_checked :
    ZetaBetaHankel.Repaired.primitiveNorm
      (Polynomial.C (((commonDen5 : ℚ)⁻¹) ^ 37) *
        (polyOfCoeffs rawCoeffs5).map (Int.castRingHom ℚ)) = polyOfCoeffs coeff5 := by
  exact source_scaled_normalization commonDen5 rawCoeffs5 coeff5
    (by decide) (by decide) (by decide) (by decide)

theorem normalization7_checked :
    ZetaBetaHankel.Repaired.primitiveNorm
      (Polynomial.C (((commonDen7 : ℚ)⁻¹) ^ 37) *
        (polyOfCoeffs rawCoeffs7).map (Int.castRingHom ℚ)) = polyOfCoeffs coeff7 := by
  exact source_scaled_normalization commonDen7 rawCoeffs7 coeff7
    (by decide) (by decide) (by decide) (by decide)

end ZetaBetaHankel.Zeta357CanonicalArithmetic
