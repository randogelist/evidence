import ZetaBetaHankel.Zeta357DigitAdmissionParts.DeterminantCore

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Transfer an integer polynomial determinant certificate back to the exact
rational source pencil. Matrix-entry equalities are separate finite arithmetic
theorems; this theorem does not replace them by a determinant assumption. -/
namespace ZetaBetaHankel.Zeta357Canonical

noncomputable def intPolynomialToRat : Polynomial ℤ →+* Polynomial ℚ :=
  Polynomial.mapRingHom (Int.castRingHom ℚ)

theorem rational_source_det_of_integer_det {n : ℕ}
    (S : Matrix (Fin n) (Fin n) (Polynomial ℚ))
    (Z : Matrix (Fin n) (Fin n) (Polynomial ℤ))
    (P : Polynomial ℤ) (D : ℤ)
    (hS : S = Polynomial.C ((D : ℚ)⁻¹) • intPolynomialToRat.mapMatrix Z)
    (hZ : Z.det = P) :
    S.det = Polynomial.C (((D : ℚ)⁻¹) ^ n) *
      P.map (Int.castRingHom ℚ) := by
  rw [hS, Matrix.det_smul]
  rw [← intPolynomialToRat.map_det Z, hZ]
  have hC : (Polynomial.C ((D : ℚ)⁻¹) : Polynomial ℚ) ^ n =
      Polynomial.C (((D : ℚ)⁻¹) ^ n) :=
    (Polynomial.C.map_pow ((D : ℚ)⁻¹) n).symm
  simp only [Fintype.card_fin, hC, intPolynomialToRat,
    Polynomial.coe_mapRingHom]

theorem singleDelta_of_integer_det
    (k : ℕ) (A B : Matrix (Fin 37) (Fin 37) ℤ)
    (P : Polynomial ℤ) (D : ℤ)
    (hS : ZetaBetaHankel.Zeta357CandidateN0.singlePencil k 3 40 3 =
      Polynomial.C ((D : ℚ)⁻¹) •
        intPolynomialToRat.mapMatrix (affinePencil A B))
    (hZ : (affinePencil A B).det = P) :
    ZetaBetaHankel.Zeta357CandidateN0.singleDelta k 3 40 3 =
      Polynomial.C (((D : ℚ)⁻¹) ^ 37) * P.map (Int.castRingHom ℚ) := by
  exact rational_source_det_of_integer_det
    (ZetaBetaHankel.Zeta357CandidateN0.singlePencil k 3 40 3)
    (affinePencil A B) P D hS hZ

/- Executable Horner evaluation of literal coefficient arrays. -/
def intHorner : List ℤ → ℤ → ℤ
  | [], _ => 0
  | c :: cs, x => c + x * intHorner cs x

theorem eval_polyOfCoeffs_int (cs : List ℤ) (x : ℤ) :
    (ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs cs).eval x = intHorner cs x := by
  induction cs with
  | nil => simp [ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs, intHorner]
  | cons c cs ih =>
      simp [ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs, intHorner, ih]

theorem affinePencil_det_eq_of_literal_certificates {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (cs : List ℤ)
    (hlen : cs.length = n + 1)
    (hlast : ZetaBetaHankel.Zeta357DigitAdmission.coeffAt cs n ≠ 0)
    (L : Fin (n + 1) → Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i : Fin (n + 1),
      detCertificateCheck (numericPencil A B (i.val : ℤ)) (L i)
        (intHorner cs (i.val : ℤ)) = true) :
    (affinePencil A B).det = ZetaBetaHankel.Zeta357DigitAdmission.polyOfCoeffs cs := by
  apply affinePencil_det_eq_of_certificates A B _
    (le_of_eq (ZetaBetaHankel.Zeta357DigitAdmission.natDegree_polyOfCoeffs cs n hlen hlast)) L
  intro i
  rw [eval_polyOfCoeffs_int]
  exact h i

end ZetaBetaHankel.Zeta357Canonical
