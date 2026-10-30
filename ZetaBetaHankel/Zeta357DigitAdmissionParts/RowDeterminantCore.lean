import ZetaBetaHankel.Zeta357DigitAdmissionParts.DeterminantCore

set_option maxHeartbeats 0
set_option pp.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Each row certificate is checked independently.  The final determinant proof
combines these opaque facts with one product identity between literal diagonals.
No elimination recurrence or external arithmetic result is trusted. -/
namespace ZetaBetaHankel.Zeta357Canonical

open scoped BigOperators

def DetRowChecks {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (row : Fin n → ℤ) (i : Fin n) (ld ud : ℤ) : Prop :=
  (∀ j : Fin n, i < j → row j = 0) ∧
  (∀ j : Fin n, j < i → (∑ r : Fin n, row r * A r j) = 0) ∧
  row i = ld ∧
  (∑ r : Fin n, row r * A r i) = ud

instance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (row : Fin n → ℤ) (i : Fin n) (ld ud : ℤ) :
    Decidable (DetRowChecks A row i ld ud) := by
  unfold DetRowChecks
  infer_instance

def detRowCheck {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (row : Fin n → ℤ) (i : Fin n) (ld ud : ℤ) : Bool :=
  decide (DetRowChecks A row i ld ud)

theorem detCertificateChecks_of_rows {n : ℕ}
    (A L : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (ld ud : Fin n → ℤ)
    (hrows : ∀ i : Fin n,
      detRowCheck A (L i) i (ld i) (ud i) = true)
    (hnz : ∀ i : Fin n, ld i ≠ 0)
    (hproduct : (∏ i : Fin n, ud i) = (∏ i : Fin n, ld i) * d) :
    DetCertificateChecks A L d := by
  have hr : ∀ i : Fin n, DetRowChecks A (L i) i (ld i) (ud i) := by
    intro i
    exact of_decide_eq_true (hrows i)
  have hdiagL : diagProduct L = ∏ i : Fin n, ld i := by
    apply Finset.prod_congr rfl
    intro i _
    exact (hr i).2.2.1
  have hdiagU : diagProduct (L * A) = ∏ i : Fin n, ud i := by
    apply Finset.prod_congr rfl
    intro i _
    exact (hr i).2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hr i).1 j hij
  · intro i j hij
    exact (hr i).2.1 j hij
  · rw [hdiagL]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hnz i)
  · rw [hdiagU, hdiagL]
    exact hproduct

theorem detCertificateCheck_of_rows {n : ℕ}
    (A L : Matrix (Fin n) (Fin n) ℤ) (d : ℤ)
    (ld ud : Fin n → ℤ)
    (hrows : ∀ i : Fin n,
      detRowCheck A (L i) i (ld i) (ud i) = true)
    (hnz : ∀ i : Fin n, ld i ≠ 0)
    (hproduct : (∏ i : Fin n, ud i) = (∏ i : Fin n, ld i) * d) :
    detCertificateCheck A L d = true := by
  have h := detCertificateChecks_of_rows A L d ld ud hrows hnz hproduct
  simp only [detCertificateCheck, h, decide_true]

end ZetaBetaHankel.Zeta357Canonical
