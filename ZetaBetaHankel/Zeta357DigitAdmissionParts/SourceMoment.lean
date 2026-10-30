import ZetaBetaHankel.Zeta357DigitAdmissionParts.PolynomialCoordinates
import ZetaBetaHankel.Zeta357DigitAdmissionParts.BernoulliTable

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Exact source moment reduction from finite quotient/remainder and residue
coordinates. The original muFunctional and hankelKernel definitions are used.
No source-pencil identity is assumed. No Lean execution was performed. -/
namespace ZetaBetaHankel.Zeta357CanonicalArithmetic

open scoped BigOperators
open Polynomial

def finiteMuMonomial (k e : ℕ) : ℚ :=
  ((-1 : ℚ) ^ e) * bernoulliValue (2 * e + 2) *
    (Nat.factorial (2 * e + 2 * k + 1) : ℚ) /
      ((Nat.factorial (2 * k) : ℚ) * (Nat.factorial (2 * e + 2) : ℚ))

theorem muMonomial_eq_finite (k e : ℕ) (he : e < 51) :
    ZetaBetaHankel.Repaired.muMonomial k e = finiteMuMonomial k e := by
  unfold ZetaBetaHankel.Repaired.muMonomial finiteMuMonomial
  rw [bernoulli_table ⟨2 * e + 2, by omega⟩]

def residueAt (rs : List ℚ) (j : ℕ) : ℚ := ratAt rs (j - 4)

def poleConstant (k j : ℕ) : ℚ :=
  -((j : ℚ) ^ (2 * k)) * ZetaBetaHankel.Repaired.harmonicGen (2 * k + 1) j +
    (1 / (2 * (j : ℚ)) - 1 / (2 * (k : ℚ)))

def coordinateMomentA (k : ℕ) (qs rs : List ℚ) : ℚ :=
  (∑ e ∈ Finset.range qs.length, ratAt qs e * finiteMuMonomial k e) +
    ∑ j ∈ Finset.Icc 4 40, residueAt rs j * poleConstant k j

def coordinateMomentB (k : ℕ) (rs : List ℚ) : ℚ :=
  ∑ j ∈ Finset.Icc 4 40, residueAt rs j * (j : ℚ) ^ (2 * k)

theorem rationalLiteral_support_subset (cs : List ℚ) :
    (rationalLiteral cs).support ⊆ Finset.range cs.length := by
  intro j hj
  have hne : ratAt cs j ≠ 0 := by
    simpa only [rationalLiteral_coeff] using (Polynomial.mem_support_iff.mp hj)
  apply Finset.mem_range.mpr
  by_contra h
  exact hne (ratAt_out cs j (Nat.le_of_not_gt h))

theorem polynomial_part_moment (k : ℕ) (qs : List ℚ) (hlen : qs.length ≤ 51) :
    (∑ e ∈ (rationalLiteral qs).support,
      Polynomial.C ((rationalLiteral qs).coeff e *
        ZetaBetaHankel.Repaired.muMonomial k e)) =
      Polynomial.C (∑ e ∈ Finset.range qs.length,
        ratAt qs e * finiteMuMonomial k e) := by
  classical
  calc
    _ = ∑ e ∈ Finset.range qs.length,
        Polynomial.C ((rationalLiteral qs).coeff e *
          ZetaBetaHankel.Repaired.muMonomial k e) := by
      apply Finset.sum_subset (rationalLiteral_support_subset qs)
      intro e he hnot
      have hz : (rationalLiteral qs).coeff e = 0 := by
        by_contra hne
        exact hnot (Polynomial.mem_support_iff.mpr hne)
      simp only [hz, zero_mul, Polynomial.C_0]
    _ = ∑ e ∈ Finset.range qs.length,
        Polynomial.C (ratAt qs e * finiteMuMonomial k e) := by
      apply Finset.sum_congr rfl
      intro e he
      have he' : e < 51 := lt_of_lt_of_le (Finset.mem_range.mp he) hlen
      rw [rationalLiteral_coeff, muMonomial_eq_finite k e he']
    _ = _ := (map_sum Polynomial.C _ _).symm

theorem pole_moment_affine (k j : ℕ) (r : ℚ) :
    Polynomial.C r * ZetaBetaHankel.Repaired.muPole k j =
      Polynomial.C (r * poleConstant k j) +
        Polynomial.C (r * (j : ℚ) ^ (2 * k)) * Polynomial.X := by
  unfold ZetaBetaHankel.Repaired.muPole poleConstant
  simp only [map_add, map_sub, map_mul, map_neg]
  ring

theorem sum_affine {α : Type*} (s : Finset α) (a b : α → ℚ) :
    (∑ j ∈ s, Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) =
      Polynomial.C (∑ j ∈ s, a j) +
        Polynomial.C (∑ j ∈ s, b j) * Polynomial.X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj, ih, map_add]
      ring

theorem muFunctional_from_parts (k : ℕ) (R : ZetaBetaHankel.Repaired.RatInV)
    (qs rs : List ℚ) (hlen : qs.length ≤ 51)
    (hq : R.polyPart = rationalLiteral qs)
    (hs : R.poleSupport = Finset.Icc 4 40)
    (hr : ∀ j ∈ Finset.Icc 4 40, R.residue j = residueAt rs j) :
    ZetaBetaHankel.Repaired.muFunctional k R =
      Polynomial.C (coordinateMomentA k qs rs) +
        Polynomial.C (coordinateMomentB k rs) * Polynomial.X := by
  classical
  have hp : (∑ j ∈ Finset.Icc 4 40,
      Polynomial.C (R.residue j) * ZetaBetaHankel.Repaired.muPole k j) =
      Polynomial.C (∑ j ∈ Finset.Icc 4 40, residueAt rs j * poleConstant k j) +
        Polynomial.C (∑ j ∈ Finset.Icc 4 40,
          residueAt rs j * (j : ℚ) ^ (2 * k)) * Polynomial.X := by
    calc
      _ = ∑ j ∈ Finset.Icc 4 40,
          (Polynomial.C (residueAt rs j * poleConstant k j) +
            Polynomial.C (residueAt rs j * (j : ℚ) ^ (2 * k)) * Polynomial.X) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hr j hj]
        exact pole_moment_affine k j (residueAt rs j)
      _ = _ := sum_affine _ _ _
  unfold ZetaBetaHankel.Repaired.muFunctional
  rw [hq, hs, polynomial_part_moment k qs hlen, hp]
  unfold coordinateMomentA coordinateMomentB
  simp only [map_add, add_assoc]

theorem source_tail_monic (N K : ℕ) :
    (ZetaBetaHankel.Repaired.D_tail N K).Monic := by
  unfold ZetaBetaHankel.Repaired.D_tail
  apply Polynomial.monic_prod_of_monic
  intro j hj
  exact Polynomial.monic_X_add_C _

/-- The quotient/remainder equation and the small-remainder condition uniquely
identify the original noncomputable division operations. -/
theorem source_division_of_coordinates (i j : ℕ) (qs rem : List ℚ)
    (hd : rationalLiteral rem + ZetaBetaHankel.Repaired.D_tail 3 40 *
      rationalLiteral qs =
        (ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j))
    (hr : (rationalLiteral rem).degree <
      (ZetaBetaHankel.Repaired.D_tail 3 40).degree) :
    (((ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j)) /ₘ
      ZetaBetaHankel.Repaired.D_tail 3 40 = rationalLiteral qs) ∧
    (((ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j)) %ₘ
      ZetaBetaHankel.Repaired.D_tail 3 40 = rationalLiteral rem) :=
  Polynomial.div_modByMonic_unique (rationalLiteral qs) (rationalLiteral rem)
    (source_tail_monic 3 40) ⟨hd, hr⟩

theorem source_moment_of_coordinates (k i j : ℕ) (qs rem rs : List ℚ)
    (hlen : qs.length ≤ 51)
    (hd : rationalLiteral rem + ZetaBetaHankel.Repaired.D_tail 3 40 *
      rationalLiteral qs =
        (ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j))
    (hrdeg : (rationalLiteral rem).degree <
      (ZetaBetaHankel.Repaired.D_tail 3 40).degree)
    (hr : ∀ a ∈ Finset.Icc 4 40,
      (rationalLiteral rem).eval (-((a : ℚ) ^ 2)) /
        (Polynomial.derivative (ZetaBetaHankel.Repaired.D_tail 3 40)).eval
          (-((a : ℚ) ^ 2)) = residueAt rs a) :
    ZetaBetaHankel.Repaired.muFunctional k
      (ZetaBetaHankel.Repaired.hankelKernel 3 40 3 i j) =
      Polynomial.C (coordinateMomentA k qs rs) +
        Polynomial.C (coordinateMomentB k rs) * Polynomial.X := by
  have hdiv := source_division_of_coordinates i j qs rem hd hrdeg
  apply muFunctional_from_parts k
    (ZetaBetaHankel.Repaired.hankelKernel 3 40 3 i j) qs rs hlen
  · change (((ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j)) /ₘ
        ZetaBetaHankel.Repaired.D_tail 3 40) = rationalLiteral qs
    exact hdiv.1
  · rfl
  · intro a ha
    change (if 4 ≤ a ∧ a ≤ 40 then
        ((((ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j)) %ₘ
          ZetaBetaHankel.Repaired.D_tail 3 40).eval (-((a : ℚ) ^ 2))) /
          (Polynomial.derivative (ZetaBetaHankel.Repaired.D_tail 3 40)).eval
            (-((a : ℚ) ^ 2)) else 0) = residueAt rs a
    rw [if_pos (Finset.mem_Icc.mp ha), hdiv.2]
    exact hr a ha

theorem source_moment_of_integer_checks (k i j : ℕ) (qs rem rs : List ℚ)
    (D A B : ℤ) (hlen : qs.length ≤ 51)
    (hd : rationalLiteral rem + ZetaBetaHankel.Repaired.D_tail 3 40 *
      rationalLiteral qs =
        (ZetaBetaHankel.Repaired.D_poly 3) ^ 5 * Polynomial.X ^ (i + j))
    (hrdeg : (rationalLiteral rem).degree <
      (ZetaBetaHankel.Repaired.D_tail 3 40).degree)
    (hr : ∀ a ∈ Finset.Icc 4 40,
      (rationalLiteral rem).eval (-((a : ℚ) ^ 2)) /
        (Polynomial.derivative (ZetaBetaHankel.Repaired.D_tail 3 40)).eval
          (-((a : ℚ) ^ 2)) = residueAt rs a)
    (hA : coordinateMomentA k qs rs = (A : ℚ) / (D : ℚ))
    (hB : coordinateMomentB k rs = (B : ℚ) / (D : ℚ)) :
    ZetaBetaHankel.Repaired.muFunctional k
      (ZetaBetaHankel.Repaired.hankelKernel 3 40 3 i j) =
      Polynomial.C ((D : ℚ)⁻¹) *
        (Polynomial.C (A : ℚ) + Polynomial.C (B : ℚ) * Polynomial.X) := by
  rw [source_moment_of_coordinates k i j qs rem rs hlen hd hrdeg hr, hA, hB]
  simp only [div_eq_mul_inv, map_mul]
  ring


end ZetaBetaHankel.Zeta357CanonicalArithmetic
