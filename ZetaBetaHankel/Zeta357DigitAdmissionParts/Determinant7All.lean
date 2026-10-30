import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample00
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample01
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample02
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample03
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample04
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample05
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample06
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample07
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample08
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample09
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample10
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample11
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample12
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample13
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample14
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample15
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample16
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample17
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample18
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample19
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample20
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample21
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample22
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample23
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample24
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample25
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample26
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample27
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample28
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample29
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample30
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample31
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample32
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample33
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample34
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample35
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample36
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant7Sample37

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

namespace ZetaBetaHankel.Zeta357Canonical
open scoped BigOperators

def multipliers7 : List (Matrix (Fin 37) (Fin 37) ℤ) := [
  multiplier7_0,
  multiplier7_1,
  multiplier7_2,
  multiplier7_3,
  multiplier7_4,
  multiplier7_5,
  multiplier7_6,
  multiplier7_7,
  multiplier7_8,
  multiplier7_9,
  multiplier7_10,
  multiplier7_11,
  multiplier7_12,
  multiplier7_13,
  multiplier7_14,
  multiplier7_15,
  multiplier7_16,
  multiplier7_17,
  multiplier7_18,
  multiplier7_19,
  multiplier7_20,
  multiplier7_21,
  multiplier7_22,
  multiplier7_23,
  multiplier7_24,
  multiplier7_25,
  multiplier7_26,
  multiplier7_27,
  multiplier7_28,
  multiplier7_29,
  multiplier7_30,
  multiplier7_31,
  multiplier7_32,
  multiplier7_33,
  multiplier7_34,
  multiplier7_35,
  multiplier7_36,
  multiplier7_37
]

def multiplierFamily7 (i : Fin 38) : Matrix (Fin 37) (Fin 37) ℤ :=
  multipliers7.getD i.val 0

theorem determinant7_all_checked : ∀ i : Fin 38,
    detCertificateCheck (numericPencil matrixA7 matrixB7 (i.val : ℤ))
      (multiplierFamily7 i) (intHorner rawCoeffs7 (i.val : ℤ)) = true := by
  intro i
  fin_cases i
  · exact determinant7_0_checked
  · exact determinant7_1_checked
  · exact determinant7_2_checked
  · exact determinant7_3_checked
  · exact determinant7_4_checked
  · exact determinant7_5_checked
  · exact determinant7_6_checked
  · exact determinant7_7_checked
  · exact determinant7_8_checked
  · exact determinant7_9_checked
  · exact determinant7_10_checked
  · exact determinant7_11_checked
  · exact determinant7_12_checked
  · exact determinant7_13_checked
  · exact determinant7_14_checked
  · exact determinant7_15_checked
  · exact determinant7_16_checked
  · exact determinant7_17_checked
  · exact determinant7_18_checked
  · exact determinant7_19_checked
  · exact determinant7_20_checked
  · exact determinant7_21_checked
  · exact determinant7_22_checked
  · exact determinant7_23_checked
  · exact determinant7_24_checked
  · exact determinant7_25_checked
  · exact determinant7_26_checked
  · exact determinant7_27_checked
  · exact determinant7_28_checked
  · exact determinant7_29_checked
  · exact determinant7_30_checked
  · exact determinant7_31_checked
  · exact determinant7_32_checked
  · exact determinant7_33_checked
  · exact determinant7_34_checked
  · exact determinant7_35_checked
  · exact determinant7_36_checked
  · exact determinant7_37_checked

theorem raw_determinant7_identity :
    (affinePencil matrixA7 matrixB7).det =
      ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs rawCoeffs7 := by
  exact affinePencil_det_eq_of_literal_certificates matrixA7 matrixB7
    rawCoeffs7 (by decide) (by decide) multiplierFamily7 determinant7_all_checked


end ZetaBetaHankel.Zeta357Canonical
