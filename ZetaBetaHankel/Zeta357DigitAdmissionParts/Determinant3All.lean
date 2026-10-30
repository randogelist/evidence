import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample00
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample01
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample02
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample03
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample04
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample05
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample06
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample07
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample08
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample09
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample10
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample11
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample12
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample13
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample14
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample15
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample16
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample17
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample18
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample19
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample20
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample21
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample22
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample23
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample24
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample25
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample26
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample27
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample28
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample29
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample30
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample31
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample32
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample33
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample34
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample35
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample36
import ZetaBetaHankel.Zeta357DigitAdmissionParts.Determinant3Sample37

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

namespace ZetaBetaHankel.Zeta357Canonical
open scoped BigOperators

def multipliers3 : List (Matrix (Fin 37) (Fin 37) ℤ) := [
  multiplier3_0,
  multiplier3_1,
  multiplier3_2,
  multiplier3_3,
  multiplier3_4,
  multiplier3_5,
  multiplier3_6,
  multiplier3_7,
  multiplier3_8,
  multiplier3_9,
  multiplier3_10,
  multiplier3_11,
  multiplier3_12,
  multiplier3_13,
  multiplier3_14,
  multiplier3_15,
  multiplier3_16,
  multiplier3_17,
  multiplier3_18,
  multiplier3_19,
  multiplier3_20,
  multiplier3_21,
  multiplier3_22,
  multiplier3_23,
  multiplier3_24,
  multiplier3_25,
  multiplier3_26,
  multiplier3_27,
  multiplier3_28,
  multiplier3_29,
  multiplier3_30,
  multiplier3_31,
  multiplier3_32,
  multiplier3_33,
  multiplier3_34,
  multiplier3_35,
  multiplier3_36,
  multiplier3_37
]

def multiplierFamily3 (i : Fin 38) : Matrix (Fin 37) (Fin 37) ℤ :=
  multipliers3.getD i.val 0

theorem determinant3_all_checked : ∀ i : Fin 38,
    detCertificateCheck (numericPencil matrixA3 matrixB3 (i.val : ℤ))
      (multiplierFamily3 i) (intHorner rawCoeffs3 (i.val : ℤ)) = true := by
  intro i
  fin_cases i
  · exact determinant3_0_checked
  · exact determinant3_1_checked
  · exact determinant3_2_checked
  · exact determinant3_3_checked
  · exact determinant3_4_checked
  · exact determinant3_5_checked
  · exact determinant3_6_checked
  · exact determinant3_7_checked
  · exact determinant3_8_checked
  · exact determinant3_9_checked
  · exact determinant3_10_checked
  · exact determinant3_11_checked
  · exact determinant3_12_checked
  · exact determinant3_13_checked
  · exact determinant3_14_checked
  · exact determinant3_15_checked
  · exact determinant3_16_checked
  · exact determinant3_17_checked
  · exact determinant3_18_checked
  · exact determinant3_19_checked
  · exact determinant3_20_checked
  · exact determinant3_21_checked
  · exact determinant3_22_checked
  · exact determinant3_23_checked
  · exact determinant3_24_checked
  · exact determinant3_25_checked
  · exact determinant3_26_checked
  · exact determinant3_27_checked
  · exact determinant3_28_checked
  · exact determinant3_29_checked
  · exact determinant3_30_checked
  · exact determinant3_31_checked
  · exact determinant3_32_checked
  · exact determinant3_33_checked
  · exact determinant3_34_checked
  · exact determinant3_35_checked
  · exact determinant3_36_checked
  · exact determinant3_37_checked

theorem raw_determinant3_identity :
    (affinePencil matrixA3 matrixB3).det =
      ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs rawCoeffs3 := by
  exact affinePencil_det_eq_of_literal_certificates matrixA3 matrixB3
    rawCoeffs3 (by decide) (by decide) multiplierFamily3 determinant3_all_checked


end ZetaBetaHankel.Zeta357Canonical
