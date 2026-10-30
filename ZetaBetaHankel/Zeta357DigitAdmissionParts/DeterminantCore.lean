import ZetaBetaHankel.Zeta357DigitAdmissionParts.Base

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

/- A finite, exact integer determinant certificate.  The checker evaluates
matrix products and diagonal products only; it never unfolds Matrix.det. -/
namespace ZetaBetaHankel.Zeta357Canonical

open scoped BigOperators

def matrixOfRows {n : ℕ} (rows : List (List ℤ)) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (rows.getD i.val []).getD j.val 0

def hankelPencil {n : ℕ} (a b : List ℤ) (x : ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => a.getD (i.val + j.val) 0 + x * b.getD (i.val + j.val) 0

def diagProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∏ i : Fin n, A i i

def DetCertificateChecks {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℤ)
    (d : ℤ) : Prop :=
  (∀ i j : Fin n, i < j → L i j = 0) ∧
  (∀ i j : Fin n, j < i → (L * A) i j = 0) ∧
  diagProduct L ≠ 0 ∧
  diagProduct (L * A) = diagProduct L * d

instance {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) :
    Decidable (DetCertificateChecks A L d) := by
  unfold DetCertificateChecks
  infer_instance

def detCertificateCheck {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℤ)
    (d : ℤ) : Bool := decide (DetCertificateChecks A L d)

theorem detCertificateChecks_sound {n : ℕ}
    (A L : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (h : DetCertificateChecks A L d) : A.det = d := by
  rcases h with ⟨hlower, hupper, hnz, hproduct⟩
  have hlower' : L.IsLowerTriangular := by
    intro i j hij
    exact hlower i j hij
  have hupper' : (L * A).IsUpperTriangular := by
    intro i j hij
    exact hupper i j hij
  have hdetL : L.det = diagProduct L :=
    Matrix.det_of_lowerTriangular L hlower'
  have hdetLA : (L * A).det = diagProduct (L * A) :=
    Matrix.det_of_upperTriangular hupper'
  apply mul_left_cancel₀ hnz
  calc
    diagProduct L * A.det = L.det * A.det := by rw [hdetL]
    _ = (L * A).det := (Matrix.det_mul L A).symm
    _ = diagProduct (L * A) := hdetLA
    _ = diagProduct L * d := hproduct

theorem detCertificateCheck_sound {n : ℕ}
    (A L : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (h : detCertificateCheck A L d = true) : A.det = d := by
  apply detCertificateChecks_sound A L d
  exact of_decide_eq_true h

/- The zero-through-d integer evaluation grid has d+1 distinct points. -/
theorem integer_polynomial_eq_of_evaluations (d : ℕ)
    (P Q : Polynomial ℤ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (heval : ∀ i : Fin (d + 1), P.eval (i.val : ℤ) = Q.eval (i.val : ℤ)) :
    P = Q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q
    (f := fun i : Fin (d + 1) => (i.val : ℤ))
  · intro i j hij
    apply Fin.ext
    exact_mod_cast hij
  · exact heval
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le (max_le hP hQ)

def affinePencil {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) (Polynomial ℤ) :=
  Polynomial.X • B.map Polynomial.C + A.map Polynomial.C

def numericPencil {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) (x : ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => A i j + x * B i j

theorem affinePencil_natDegree_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) :
    (affinePencil A B).det.natDegree ≤ n := by
  simpa only [affinePencil, Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le B A

theorem affinePencil_eval_det {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (x : ℤ) :
    (affinePencil A B).det.eval x = (numericPencil A B x).det := by
  calc
    (affinePencil A B).det.eval x =
        ((Polynomial.evalRingHom x).mapMatrix (affinePencil A B)).det :=
      (Polynomial.evalRingHom x).map_det (affinePencil A B)
    _ = (numericPencil A B x).det := by
      congr 1
      ext i j
      simp [affinePencil, numericPencil, Matrix.map_apply, Matrix.smul_apply,
        Matrix.add_apply, smul_eq_mul, add_comm]

theorem affinePencil_det_eq_of_certificates {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (P : Polynomial ℤ)
    (hP : P.natDegree ≤ n)
    (L : Fin (n + 1) → Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i : Fin (n + 1),
      detCertificateCheck (numericPencil A B (i.val : ℤ)) (L i)
        (P.eval (i.val : ℤ)) = true) :
    (affinePencil A B).det = P := by
  apply integer_polynomial_eq_of_evaluations n _ _
    (affinePencil_natDegree_le A B) hP
  intro i
  rw [affinePencil_eval_det]
  exact detCertificateCheck_sound _ _ _ (h i)

end ZetaBetaHankel.Zeta357Canonical
