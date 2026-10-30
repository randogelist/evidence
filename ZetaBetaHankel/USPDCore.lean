import ZetaBetaHankel.ExactModel

/-!
# Singular universal primitive decay on the exact canonical coupled family

The admissible-ray type is the family `F` in the USPD formula.  Every ray
already carries the corrected positive-cone condition, so the zero ray and
other inadmissible rational centres are not silently included.

For a ray `theta` and index `n`, `cutoffScale theta n` is the canonical
complexity scale

  max (40 * (n + 1)) (natDegree (P_theta,n) + 1).

Thus the scale dominates both the source cutoff and the integer-polynomial
degree.  USPD is the only conditional proposition introduced in this module.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open Polynomial

namespace ZetaBetaHankel.USPD

/-- An exact admissible adjacent-odd-zeta ray of the source model. -/
structure Ray where
  k : ℕ
  hk : 1 ≤ k
  a : ℤ
  b : ℤ
  cone : ZetaBetaHankel.Repaired.InPositiveCone k a b

/-- The exact primitive integer determinant attached to an admissible ray. -/
def canonicalPolynomial (ray : Ray) (n : ℕ) : ℤ[X] :=
  ZetaBetaHankel.Repaired.canonicalCoupled ray.k n ray.a ray.b

/-- The genuine adjacent odd-zeta value at which the determinant is evaluated. -/
noncomputable def actualValue (ray : Ray) : ℝ :=
  ZetaBetaHankel.Repaired.xiCoupled ray.k ray.a ray.b

/-- Integer-polynomial evaluation in the reals. -/
noncomputable def evalIntPoly (P : ℤ[X]) (x : ℝ) : ℝ :=
  (P.map (algebraMap ℤ ℝ)).eval x

/-- The actual primitive determinant evaluated at its actual zeta centre. -/
noncomputable def evaluatedValue (ray : Ray) (n : ℕ) : ℝ :=
  evalIntPoly (canonicalPolynomial ray n) (actualValue ray)

/-- Degree-dominating canonical cutoff used as `K_n` in the singular obligation. -/
def cutoffScale (ray : Ray) (n : ℕ) : ℕ :=
  max (40 * (n + 1)) ((canonicalPolynomial ray n).natDegree + 1)

/-- Eventual positive quadratic-exponential primitive decay on one admissible ray. -/
def DecaysAt (ray : Ray) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < |evaluatedValue ray n| ∧
      |evaluatedValue ray n| ≤
        Real.exp (-ε * ((cutoffScale ray n : ℝ) ^ 2))

/-- Singular final conditional obligation. -/
def USPD : Prop :=
  ∀ ray : Ray, DecaysAt ray

/-- The scale strictly dominates the polynomial degree. -/
theorem degree_lt_cutoffScale (ray : Ray) (n : ℕ) :
    (canonicalPolynomial ray n).natDegree < cutoffScale ray n := by
  unfold cutoffScale
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- The scale tends to infinity because it strictly dominates its index. -/
theorem index_lt_cutoffScale (ray : Ray) (n : ℕ) :
    n < cutoffScale ray n := by
  unfold cutoffScale
  apply lt_of_lt_of_le (b := 40 * (n + 1))
  · omega
  · exact le_max_left _ _

/-- The pure higher-odd ray belongs to the corrected positive cone. -/
theorem zero_one_in_positive_cone (k : ℕ) :
    ZetaBetaHankel.Repaired.InPositiveCone k 0 1 := by
  unfold ZetaBetaHankel.Repaired.InPositiveCone
  constructor
  · norm_num
  · have h1 : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * k + 1 by omega)
    have h2 : (0 : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * k + 2 by omega)
    have hpi : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
    have hdiv : (0 : ℝ) <
        4 * Real.pi ^ 2 /
          (((2 * k + 1 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ)) := by
      exact div_pos (mul_pos (by norm_num) hpi) (mul_pos h1 h2)
    simpa using hdiv

/-- Canonical pure odd-zeta ray, representing zeta(2k+3). -/
def pureHigherRay (k : ℕ) (hk : 1 ≤ k) : Ray where
  k := k
  hk := hk
  a := 0
  b := 1
  cone := zero_one_in_positive_cone k

/-- At k=1 the general cone is exactly the corrected pi^2/3 cone. -/
theorem coupled35_in_positive_cone (a b : ℤ)
    (hb : 0 < b)
    (ha : (a : ℝ) < (Real.pi ^ 2 / 3) * (b : ℝ)) :
    ZetaBetaHankel.Repaired.InPositiveCone 1 a b := by
  unfold ZetaBetaHankel.Repaired.InPositiveCone
  constructor
  · exact hb
  · change (a : ℝ) < (4 * Real.pi ^ 2 / (3 * 4)) * (b : ℝ)
    have hcoeff : 4 * Real.pi ^ 2 / (3 * 4) = Real.pi ^ 2 / 3 := by
      ring
    simpa [hcoeff] using ha

/-- Canonical coupled zeta(3)/zeta(5) ray in the corrected positive cone. -/
def coupled35Ray (a b : ℤ)
    (hb : 0 < b)
    (ha : (a : ℝ) < (Real.pi ^ 2 / 3) * (b : ℝ)) : Ray where
  k := 1
  hk := by omega
  a := a
  b := b
  cone := coupled35_in_positive_cone a b hb ha

/-- Universal projection of the singular input. -/
theorem universal_decay (h : USPD) (ray : Ray) : DecaysAt ray :=
  h ray

/-- Pure weight-five projection. -/
theorem weight_five_decay (h : USPD) :
    DecaysAt (pureHigherRay 1 (by omega)) :=
  h (pureHigherRay 1 (by omega))

/-- Every higher odd pure ray is a projection of the same input. -/
theorem higher_odd_decay (h : USPD) (k : ℕ) (hk : 1 ≤ k) :
    DecaysAt (pureHigherRay k hk) :=
  h (pureHigherRay k hk)

/-- Every corrected zeta(3)/zeta(5) cone ray is a projection of the same input. -/
theorem coupled_decay (h : USPD) (a b : ℤ)
    (hb : 0 < b)
    (ha : (a : ℝ) < (Real.pi ^ 2 / 3) * (b : ℝ)) :
    DecaysAt (coupled35Ray a b hb ha) :=
  h (coupled35Ray a b hb ha)

/-- An integer polynomial cannot have a nonzero rational evaluation this small. -/
theorem integer_polynomial_squeeze (P : ℤ[X]) (a : ℤ) (b : ℕ)
    (hb : 0 < b)
    (hne : evalIntPoly P ((a : ℝ) / b) ≠ 0)
    (hsmall : (b : ℝ) ^ P.natDegree *
      |evalIntPoly P ((a : ℝ) / b)| < 1) : False := by
  have hlow := one_le_pow_mul_abs_eval_div
    (K := ℝ) (f := P) (a := a) (b := (b : ℤ))
    (by exact_mod_cast hb)
    (by simpa [evalIntPoly] using hne)
  have hlow' : (1 : ℝ) ≤ (b : ℝ) ^ P.natDegree *
      |evalIntPoly P ((a : ℝ) / b)| := by
    simpa [evalIntPoly] using hlow
  exact (not_lt_of_ge hlow') hsmall

/-- One USPD ray implies irrationality of its actual zeta centre. -/
theorem irrational_of_decay (ray : Ray) (h : DecaysAt ray) :
    Irrational (actualValue ray) := by
  obtain ⟨ε, hε, n₀, hdecay⟩ := h
  rw [Irrational]
  rintro ⟨q, hq⟩
  have hb : 0 < q.den := q.pos
  have hbR : (0 : ℝ) < q.den := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ q.den := by exact_mod_cast hb
  have hlog : 0 ≤ Real.log (q.den : ℝ) := Real.log_nonneg hb1
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (Real.log q.den / ε)
  let n : ℕ := max n₀ n₁
  let K : ℕ := cutoffScale ray n
  have hn0 : n₀ ≤ n := le_max_left _ _
  have hn1 : n₁ ≤ n := le_max_right _ _
  have hnK : n < K := by
    dsimp [K]
    exact index_lt_cutoffScale ray n
  have hn1Knat : n₁ < K := lt_of_le_of_lt hn1 hnK
  have hn1K : (n₁ : ℝ) < (K : ℝ) := by exact_mod_cast hn1Knat
  have hratioK : Real.log q.den / ε < (K : ℝ) := hn₁.trans hn1K
  have hchoice0 : Real.log q.den < (K : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hratioK
  have hchoice : Real.log q.den < ε * (K : ℝ) := by
    simpa [mul_comm] using hchoice0
  have hKposNat : 0 < K := lt_of_le_of_lt (Nat.zero_le n) hnK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hKposNat
  have hdegreeNat : (canonicalPolynomial ray n).natDegree ≤ K :=
    (degree_lt_cutoffScale ray n).le
  have hdegree : ((canonicalPolynomial ray n).natDegree : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hdegreeNat
  have hstrict :
      ((canonicalPolynomial ray n).natDegree : ℝ) * Real.log q.den <
        ε * (K : ℝ) ^ 2 := by
    calc
      ((canonicalPolynomial ray n).natDegree : ℝ) * Real.log q.den
          ≤ (K : ℝ) * Real.log q.den :=
            mul_le_mul_of_nonneg_right hdegree hlog
      _ < (K : ℝ) * (ε * (K : ℝ)) :=
            mul_lt_mul_of_pos_left hchoice hKpos
      _ = ε * (K : ℝ) ^ 2 := by ring
  have hnegative :
      ((canonicalPolynomial ray n).natDegree : ℝ) * Real.log q.den -
        ε * (K : ℝ) ^ 2 < 0 :=
    sub_neg.mpr hstrict
  have hdata := hdecay n hn0
  have hnonzero :
      evalIntPoly (canonicalPolynomial ray n) (actualValue ray) ≠ 0 := by
    exact abs_pos.mp (by simpa [evaluatedValue] using hdata.1)
  have hupper :
      |evalIntPoly (canonicalPolynomial ray n) (actualValue ray)| ≤
        Real.exp (-ε * (K : ℝ) ^ 2) := by
    simpa [evaluatedValue, K] using hdata.2
  have hrat :
      (q.num : ℝ) / (q.den : ℝ) = actualValue ray :=
    (Rat.cast_def q).symm.trans hq
  apply integer_polynomial_squeeze
    (canonicalPolynomial ray n) q.num q.den hb
  · rw [hrat]
    exact hnonzero
  · rw [hrat]
    calc
      (q.den : ℝ) ^ (canonicalPolynomial ray n).natDegree *
          |evalIntPoly (canonicalPolynomial ray n) (actualValue ray)|
          ≤ (q.den : ℝ) ^ (canonicalPolynomial ray n).natDegree *
              Real.exp (-ε * (K : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hupper
              (le_of_lt (pow_pos hbR _))
      _ = Real.exp
          (((canonicalPolynomial ray n).natDegree : ℝ) * Real.log q.den -
            ε * (K : ℝ) ^ 2) := by
            rw [show (q.den : ℝ) ^ (canonicalPolynomial ray n).natDegree =
              Real.exp (((canonicalPolynomial ray n).natDegree : ℝ) *
                Real.log q.den) by
              rw [← Real.log_pow, Real.exp_log (pow_pos hbR _)]]
            rw [← Real.exp_add]
            congr 1
            ring
      _ < 1 := Real.exp_lt_one_iff.mpr hnegative

/-- Every admissible ray is irrational under the one singular input. -/
theorem universal_irrational (h : USPD) (ray : Ray) :
    Irrational (actualValue ray) :=
  irrational_of_decay ray (h ray)

end ZetaBetaHankel.USPD
