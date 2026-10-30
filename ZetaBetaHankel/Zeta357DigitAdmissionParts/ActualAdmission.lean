import ZetaBetaHankel.Zeta357DigitAdmissionParts.CanonicalLiteralData
import ZetaBetaHankel.Zeta357DigitAdmissionParts.CanonicalNormalization
import ZetaBetaHankel.Zeta357DigitAdmissionParts.MomentCoordinates
import ZetaBetaHankel.Zeta357DigitAdmissionParts.ActualZetaBrackets

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Final finite admission from the original computed coordinates.
Every source/analytic bridge is supplied by a theorem in this file.
These declarations have no user-supplied semantic premises.
External compilation and axiom audit are still required for acceptance. -/
namespace ZetaBetaHankel.Zeta357DigitAdmission

open ZetaBetaHankel.Zeta357CandidateN0
open ZetaBetaHankel.Zeta357Canonical
open ZetaBetaHankel.Zeta357CanonicalArithmetic
open ZetaBetaHankel.Zeta357Analytic

theorem canonicalPolynomial3 : primitivePolynomial 1 0 = polyOfCoeffs coeff3 := by
  change ZetaBetaHankel.Repaired.primitiveNorm (singleDelta 1 3 40 3) = _
  rw [singleDelta_of_integer_det 1 matrixA3 matrixB3 (polyOfCoeffs rawCoeffs3)
    commonDen3 sourcePencil3 raw_determinant3_identity]
  exact normalization3_checked

theorem canonicalPolynomial5 : primitivePolynomial 2 0 = polyOfCoeffs coeff5 := by
  change ZetaBetaHankel.Repaired.primitiveNorm (singleDelta 2 3 40 3) = _
  rw [singleDelta_of_integer_det 2 matrixA5 matrixB5 (polyOfCoeffs rawCoeffs5)
    commonDen5 sourcePencil5 raw_determinant5_identity]
  exact normalization5_checked

theorem canonicalPolynomial7 : primitivePolynomial 3 0 = polyOfCoeffs coeff7 := by
  change ZetaBetaHankel.Repaired.primitiveNorm (singleDelta 3 3 40 3) = _
  rw [singleDelta_of_integer_det 3 matrixA7 matrixB7 (polyOfCoeffs rawCoeffs7)
    commonDen7 sourcePencil7 raw_determinant7_identity]
  exact normalization7_checked

theorem actualCanonicalSemantics : CanonicalSemantics :=
  ⟨canonicalPolynomial3, canonicalPolynomial5, canonicalPolynomial7,
    actual_zeta3_enclosed, actual_zeta5_enclosed, actual_zeta7_enclosed⟩

theorem actualN0Admission : N0Admission :=
  admission_of_semantics actualCanonicalSemantics

theorem goodAt_zero : GoodAt 0 :=
  good_zero_of_admission actualN0Admission

end ZetaBetaHankel.Zeta357DigitAdmission
