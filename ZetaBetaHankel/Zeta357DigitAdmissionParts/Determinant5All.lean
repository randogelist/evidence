import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample00
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample01
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample02
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample03
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample04
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample05
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample06
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample07
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample08
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample09
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample10
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample11
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample12
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample13
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample14
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample15
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample16
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample17
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample18
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample19
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample20
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample21
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample22
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample23
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample24
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample25
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample26
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample27
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample28
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample29
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample30
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample31
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample32
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample33
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample34
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample35
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample36
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant5Sample37

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

namespace ZetaBetaHankel.Zeta357Canonical
open scoped BigOperators

def multipliers5 : List (Matrix (Fin 37) (Fin 37) ℤ) := [
  multiplier5_0,
  multiplier5_1,
  multiplier5_2,
  multiplier5_3,
  multiplier5_4,
  multiplier5_5,
  multiplier5_6,
  multiplier5_7,
  multiplier5_8,
  multiplier5_9,
  multiplier5_10,
  multiplier5_11,
  multiplier5_12,
  multiplier5_13,
  multiplier5_14,
  multiplier5_15,
  multiplier5_16,
  multiplier5_17,
  multiplier5_18,
  multiplier5_19,
  multiplier5_20,
  multiplier5_21,
  multiplier5_22,
  multiplier5_23,
  multiplier5_24,
  multiplier5_25,
  multiplier5_26,
  multiplier5_27,
  multiplier5_28,
  multiplier5_29,
  multiplier5_30,
  multiplier5_31,
  multiplier5_32,
  multiplier5_33,
  multiplier5_34,
  multiplier5_35,
  multiplier5_36,
  multiplier5_37
]

def multiplierFamily5 (i : Fin 38) : Matrix (Fin 37) (Fin 37) ℤ :=
  multipliers5.getD i.val 0

theorem determinant5_all_checked : ∀ i : Fin 38,
    detCertificateCheck (numericPencil matrixA5 matrixB5 (i.val : ℤ))
      (multiplierFamily5 i) (intHorner rawCoeffs5 (i.val : ℤ)) = true := by
  intro i
  fin_cases i
  · exact determinant5_0_checked
  · exact determinant5_1_checked
  · exact determinant5_2_checked
  · exact determinant5_3_checked
  · exact determinant5_4_checked
  · exact determinant5_5_checked
  · exact determinant5_6_checked
  · exact determinant5_7_checked
  · exact determinant5_8_checked
  · exact determinant5_9_checked
  · exact determinant5_10_checked
  · exact determinant5_11_checked
  · exact determinant5_12_checked
  · exact determinant5_13_checked
  · exact determinant5_14_checked
  · exact determinant5_15_checked
  · exact determinant5_16_checked
  · exact determinant5_17_checked
  · exact determinant5_18_checked
  · exact determinant5_19_checked
  · exact determinant5_20_checked
  · exact determinant5_21_checked
  · exact determinant5_22_checked
  · exact determinant5_23_checked
  · exact determinant5_24_checked
  · exact determinant5_25_checked
  · exact determinant5_26_checked
  · exact determinant5_27_checked
  · exact determinant5_28_checked
  · exact determinant5_29_checked
  · exact determinant5_30_checked
  · exact determinant5_31_checked
  · exact determinant5_32_checked
  · exact determinant5_33_checked
  · exact determinant5_34_checked
  · exact determinant5_35_checked
  · exact determinant5_36_checked
  · exact determinant5_37_checked

theorem raw_determinant5_identity :
    (affinePencil matrixA5 matrixB5).det =
      ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs rawCoeffs5 := by
  exact affinePencil_det_eq_of_literal_certificates matrixA5 matrixB5
    rawCoeffs5 (by decide) (by decide) multiplierFamily5 determinant5_all_checked


end ZetaBetaHankel.Zeta357Canonical
