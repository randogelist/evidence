import ZetaBetaHankel.Zeta357DigitAdmissionParts.Base

set_option maxHeartbeats 0
set_option format.width 100000
set_option maxRecDepth 200000
noncomputable section

/- Finite Euler-eta arithmetic certificate. No analytic zeta identity assumed here. -/
namespace ZetaBetaHankel.Zeta357EtaArithmetic

open ZetaBetaHankel.Zeta357DigitAdmission

private theorem and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := Eq.mp (Bool.and_eq_true a b) h

def addBox (a b : Box) : Box := ⟨a.lo + b.lo, a.hi + b.hi⟩

theorem addBox_sound {D : ℤ} {a b : Box} {x y : ℝ}
    (ha : Contains D a x) (hb : Contains D b y) :
    Contains D (addBox a b) (x + y) := by
  constructor
  · change ((a.lo + b.lo : ℤ) : ℝ) ≤ (D : ℝ) * (x + y)
    push_cast
    rw [mul_add]
    exact add_le_add ha.1 hb.1
  · change (D : ℝ) * (x + y) ≤ ((a.hi + b.hi : ℤ) : ℝ)
    push_cast
    rw [mul_add]
    exact add_le_add ha.2 hb.2

def ceilDiv (a b : ℤ) : ℤ := -((-a) / b)

def mulBox (D : ℤ) (a b : Box) : Box :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨min (min p1 p2) (min p3 p4) / D,
    ceilDiv (max (max p1 p2) (max p3 p4)) D⟩

def reciprocalBox (D : ℤ) (j : ℕ) : Box :=
  ⟨D / (j : ℤ), ceilDiv D (j : ℤ)⟩

def ReciprocalOK (D : ℤ) (j : ℕ) (b : Box) : Prop :=
  b.lo * (j : ℤ) ≤ D ∧ D ≤ b.hi * (j : ℤ)

instance (D : ℤ) (j : ℕ) (b : Box) : Decidable (ReciprocalOK D j b) := by
  unfold ReciprocalOK
  infer_instance

theorem reciprocal_sound {D : ℤ} {j : ℕ} {b : Box}
    (hj : 0 < j) (h : ReciprocalOK D j b) :
    Contains D b (1 / (j : ℝ)) := by
  have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h1 : (b.lo : ℝ) * (j : ℝ) ≤ (D : ℝ) := by exact_mod_cast h.1
  have h2 : (D : ℝ) ≤ (b.hi : ℝ) * (j : ℝ) := by exact_mod_cast h.2
  constructor
  · change (b.lo : ℝ) ≤ (D : ℝ) * (1 / (j : ℝ))
    rw [mul_one_div]
    exact (le_div_iff₀ hjr).2 h1
  · change (D : ℝ) * (1 / (j : ℝ)) ≤ (b.hi : ℝ)
    rw [mul_one_div]
    exact (div_le_iff₀ hjr).2 h2

def divBox (a : Box) (j : ℕ) : Box :=
  ⟨a.lo / (j : ℤ), ceilDiv a.hi (j : ℤ)⟩

def DivOK (a : Box) (j : ℕ) (b : Box) : Prop :=
  b.lo * (j : ℤ) ≤ a.lo ∧ a.hi ≤ b.hi * (j : ℤ)

instance (a : Box) (j : ℕ) (b : Box) : Decidable (DivOK a j b) := by
  unfold DivOK
  infer_instance

theorem divBox_sound {D : ℤ} {a b : Box} {x : ℝ} {j : ℕ}
    (hj : 0 < j) (ha : Contains D a x) (hc : DivOK a j b) :
    Contains D b (x / (j : ℝ)) := by
  have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h1 : (b.lo : ℝ) * (j : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast hc.1
  have h2 : (a.hi : ℝ) ≤ (b.hi : ℝ) * (j : ℝ) := by exact_mod_cast hc.2
  constructor
  · change (b.lo : ℝ) ≤ (D : ℝ) * (x / (j : ℝ))
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hjr).2 (h1.trans ha.1)
  · change (D : ℝ) * (x / (j : ℝ)) ≤ (b.hi : ℝ)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hjr).2 (ha.2.trans h2)

def lastOr {α : Type*} (fallback : α) : List α → α
  | [] => fallback
  | a :: as => lastOr a as

theorem lastOr_sound {D : ℤ} {bs : List Box} {ys : List ℝ}
    (h : List.Forall₂ (Contains D) bs ys) {fallback : Box} {v : ℝ}
    (hf : Contains D fallback v) :
    Contains D (lastOr fallback bs) (lastOr v ys) := by
  induction h generalizing fallback v with
  | nil => exact hf
  | @cons a y as ys ha ht ih => exact ih (fallback := a) (v := y) ha

def updateReal (x prev : ℝ) : List ℝ → List ℝ
  | [] => []
  | a :: as =>
      let b := a + x * prev
      b :: updateReal x b as

def updateBoxes (D : ℤ) (x prev : Box) : List Box → List Box × Bool
  | [] => ([], true)
  | a :: as =>
      let p := mulBox D x prev
      let b := addBox a p
      let tail := updateBoxes D x b as
      (b :: tail.1, decide (StepOK D x prev 0 p) && tail.2)

theorem updateBoxes_sound {D : ℤ} {xb prev : Box} {x v : ℝ}
    (hD : 0 < D) (hx : Contains D xb x) (hp : Contains D prev v)
    {bs : List Box} {ys : List ℝ} (h : List.Forall₂ (Contains D) bs ys)
    (hc : (updateBoxes D xb prev bs).2 = true) :
    List.Forall₂ (Contains D) (updateBoxes D xb prev bs).1 (updateReal x v ys) := by
  induction h generalizing prev v with
  | nil => exact List.Forall₂.nil
  | @cons a y as ys ha ht ih =>
      change (decide (StepOK D xb prev 0 (mulBox D xb prev)) &&
        (updateBoxes D xb (addBox a (mulBox D xb prev)) as).2) = true at hc
      have hb := and_true hc
      have hprod : Contains D (mulBox D xb prev) (x * v) := by
        have hs : StepOK D xb prev 0 (mulBox D xb prev) := of_decide_eq_true hb.1
        simpa only [Int.cast_zero, zero_add] using step_sound hD hx hp hs
      have hn : Contains D (addBox a (mulBox D xb prev)) (y + x * v) :=
        addBox_sound ha hprod
      change List.Forall₂ (Contains D)
        (addBox a (mulBox D xb prev) ::
          (updateBoxes D xb (addBox a (mulBox D xb prev)) as).1)
        ((y + x * v) :: updateReal x (y + x * v) ys)
      exact List.Forall₂.cons hn
        (ih (prev := addBox a (mulBox D xb prev)) (v := y + x * v) hn hb.2)

structure BoxState where
  hs : List Box
  sum : Box
  deriving DecidableEq

structure RealState where
  hs : List ℝ
  sum : ℝ

def StateContains (D : ℤ) (b : BoxState) (r : RealState) : Prop :=
  List.Forall₂ (Contains D) b.hs r.hs ∧ Contains D b.sum r.sum

def oneBox (D : ℤ) : Box := ⟨D, D⟩

theorem oneBox_sound (D : ℤ) : Contains D (oneBox D) 1 := by
  constructor <;> simp [oneBox]

def advanceReal (j : ℕ) (old : RealState) : RealState :=
  let hs := updateReal (1 / (j : ℝ)) 1 old.hs
  { hs := hs, sum := old.sum + lastOr 1 hs / ((j * 2 ^ j : ℕ) : ℝ) }

def advanceBoxes (D : ℤ) (j : ℕ) (old : BoxState) : BoxState × Bool :=
  let x := reciprocalBox D j
  let update := updateBoxes D x (oneBox D) old.hs
  let top := lastOr (oneBox D) update.1
  let den := j * 2 ^ j
  let term := divBox top den
  ({hs := update.1, sum := addBox old.sum term},
    (decide (ReciprocalOK D j x) && update.2) && decide (DivOK top den term))

theorem advanceBoxes_sound {D : ℤ} {j : ℕ} {b : BoxState} {r : RealState}
    (hD : 0 < D) (hj : 0 < j) (h : StateContains D b r)
    (hc : (advanceBoxes D j b).2 = true) :
    StateContains D (advanceBoxes D j b).1 (advanceReal j r) := by
  change ((decide (ReciprocalOK D j (reciprocalBox D j)) &&
      (updateBoxes D (reciprocalBox D j) (oneBox D) b.hs).2) &&
    decide (DivOK
      (lastOr (oneBox D) (updateBoxes D (reciprocalBox D j) (oneBox D) b.hs).1)
      (j * 2 ^ j)
      (divBox (lastOr (oneBox D)
        (updateBoxes D (reciprocalBox D j) (oneBox D) b.hs).1) (j * 2 ^ j)))) = true at hc
  have hsplit := and_true hc
  have hfirst := and_true hsplit.1
  have hx := reciprocal_sound hj (of_decide_eq_true hfirst.1)
  have hu := updateBoxes_sound hD hx (oneBox_sound D) h.1 hfirst.2
  have ht := lastOr_sound hu (oneBox_sound D)
  have hden : 0 < j * 2 ^ j := Nat.mul_pos hj (pow_pos (by decide) j)
  have hterm := divBox_sound hden ht (of_decide_eq_true hsplit.2)
  exact ⟨hu, addBox_sound h.2 hterm⟩

def boxRun (D : ℤ) (r : ℕ) : ℕ → BoxState × Bool
  | 0 => ({hs := List.replicate r zeroBox, sum := zeroBox}, true)
  | n + 1 =>
      let old := boxRun D r n
      let next := advanceBoxes D (n + 1) old.1
      (next.1, old.2 && next.2)

def realRun (r : ℕ) : ℕ → RealState
  | 0 => {hs := List.replicate r 0, sum := 0}
  | n + 1 => advanceReal (n + 1) (realRun r n)

theorem zeroBox_sound (D : ℤ) : Contains D zeroBox 0 := by
  constructor <;> simp [zeroBox]

theorem replicate_zero_sound (D : ℤ) (r : ℕ) :
    List.Forall₂ (Contains D) (List.replicate r zeroBox) (List.replicate r (0 : ℝ)) := by
  induction r with
  | zero => exact List.Forall₂.nil
  | succ n ih =>
      simpa only [List.replicate_succ] using List.Forall₂.cons (zeroBox_sound D) ih

theorem boxRun_sound {D : ℤ} (hD : 0 < D) (r J : ℕ)
    (hc : (boxRun D r J).2 = true) :
    StateContains D (boxRun D r J).1 (realRun r J) := by
  revert hc
  induction J with
  | zero =>
      intro hc
      exact ⟨replicate_zero_sound D r, zeroBox_sound D⟩
  | succ n ih =>
      intro hc
      change ((boxRun D r n).2 &&
        (advanceBoxes D (n + 1) (boxRun D r n).1).2) = true at hc
      have hs := and_true hc
      exact advanceBoxes_sound hD (Nat.succ_pos n) (ih hs.1) hs.2

def finiteEta (s J : ℕ) : ℝ := (realRun (s - 1) J).sum

theorem finiteEta_enclosed {D : ℤ} (hD : 0 < D) (s J : ℕ)
    (hc : (boxRun D (s - 1) J).2 = true) :
    Contains D (boxRun D (s - 1) J).1.sum (finiteEta s J) :=
  (boxRun_sound hD (s - 1) J hc).2

open scoped BigOperators

/-- Complete homogeneous reciprocal sums, recursively in their degree. -/
def homogeneous : ℕ → ℕ → ℝ
  | 0, _ => 1
  | r + 1, j => ∑ i ∈ Finset.range j, homogeneous r (i + 1) / ((i + 1 : ℕ) : ℝ)

theorem homogeneous_succ (r j : ℕ) :
    homogeneous (r + 1) (j + 1) = homogeneous (r + 1) j +
      homogeneous r (j + 1) / ((j + 1 : ℕ) : ℝ) := by
  simp only [homogeneous, Finset.sum_range_succ]

def hList (start j : ℕ) : ℕ → List ℝ
  | 0 => []
  | r + 1 => homogeneous (start + 1) j :: hList (start + 1) j r

theorem updateReal_hList (start r j : ℕ) :
    updateReal (1 / ((j + 1 : ℕ) : ℝ)) (homogeneous start (j + 1))
      (hList start j r) = hList start (j + 1) r := by
  induction r generalizing start with
  | zero => rfl
  | succ r ih =>
      have heq : homogeneous (start + 1) j +
          (1 / ((j + 1 : ℕ) : ℝ)) * homogeneous start (j + 1) =
          homogeneous (start + 1) (j + 1) := by
        rw [homogeneous_succ]
        ring
      change (homogeneous (start + 1) j +
          (1 / ((j + 1 : ℕ) : ℝ)) * homogeneous start (j + 1)) ::
        updateReal (1 / ((j + 1 : ℕ) : ℝ))
          (homogeneous (start + 1) j +
            (1 / ((j + 1 : ℕ) : ℝ)) * homogeneous start (j + 1))
          (hList (start + 1) j r) =
        homogeneous (start + 1) (j + 1) :: hList (start + 1) (j + 1) r
      rw [heq]
      exact congrArg (List.cons _) (ih (start + 1))

theorem hList_zero (start r : ℕ) : hList start 0 r = List.replicate r (0 : ℝ) := by
  induction r generalizing start with
  | zero => rfl
  | succ r ih => simp [hList, homogeneous, ih, List.replicate_succ]

theorem lastOr_hList (start r j : ℕ) :
    lastOr (homogeneous start j) (hList start j r) = homogeneous (start + r) j := by
  induction r generalizing start with
  | zero => simp [hList, lastOr]
  | succ r ih =>
      change lastOr (homogeneous (start + 1) j) (hList (start + 1) j r) =
        homogeneous (start + (r + 1)) j
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (start + 1)

theorem realRun_hs (r j : ℕ) : (realRun r j).hs = hList 0 j r := by
  induction j with
  | zero => exact (hList_zero 0 r).symm
  | succ j ih =>
      change updateReal (1 / ((j + 1 : ℕ) : ℝ)) 1 (realRun r j).hs = hList 0 (j + 1) r
      rw [ih]
      exact updateReal_hList 0 r j

theorem realRun_last (r j : ℕ) : lastOr 1 (realRun r j).hs = homogeneous r j := by
  rw [realRun_hs]
  simpa only [homogeneous, Nat.zero_add] using lastOr_hList 0 r j

theorem realRun_sum_succ (r j : ℕ) :
    (realRun r (j + 1)).sum = (realRun r j).sum +
      homogeneous r (j + 1) / (((j + 1) * 2 ^ (j + 1) : ℕ) : ℝ) := by
  change (realRun r j).sum +
    lastOr 1 (realRun r (j + 1)).hs / (((j + 1) * 2 ^ (j + 1) : ℕ) : ℝ) = _
  rw [realRun_last]

theorem finiteEta_eq_sum (s J : ℕ) :
    finiteEta s J = ∑ j ∈ Finset.range J,
      homogeneous (s - 1) (j + 1) / (((j + 1) * 2 ^ (j + 1) : ℕ) : ℝ) := by
  induction J with
  | zero => simp [finiteEta, realRun]
  | succ J ih =>
      change (realRun (s - 1) (J + 1)).sum = _
      rw [realRun_sum_succ, Finset.sum_range_succ]
      exact congrArg (fun z : ℝ => z +
        homogeneous (s - 1) (J + 1) / (((J + 1) * 2 ^ (J + 1) : ℕ) : ℝ)) ih

/-- A short block starts from an explicit checkpoint, so separate checked blocks
    do not repeatedly reduce the entire preceding computation. -/
def runFrom (D : ℤ) (start : ℕ) (initial : BoxState) : ℕ → BoxState × Bool
  | 0 => (initial, true)
  | n + 1 =>
      let old := runFrom D start initial n
      let next := advanceBoxes D (start + n + 1) old.1
      (next.1, old.2 && next.2)

def ChunkCheck (D : ℤ) (start length : ℕ) (initial final : BoxState) : Bool :=
  let run := runFrom D start initial length
  run.2 && decide (run.1 = final)

theorem runFrom_sound {D : ℤ} (hD : 0 < D) (r start length : ℕ) (initial : BoxState)
    (h : StateContains D initial (realRun r start))
    (hc : (runFrom D start initial length).2 = true) :
    StateContains D (runFrom D start initial length).1 (realRun r (start + length)) := by
  revert hc
  induction length with
  | zero =>
      intro hc
      exact h
  | succ n ih =>
      intro hc
      change ((runFrom D start initial n).2 &&
        (advanceBoxes D (start + n + 1) (runFrom D start initial n).1).2) = true at hc
      have hs := and_true hc
      exact advanceBoxes_sound hD (Nat.succ_pos (start + n)) (ih hs.1) hs.2

theorem ChunkCheck_sound {D : ℤ} (hD : 0 < D) (r start length : ℕ)
    (initial final : BoxState) (h : StateContains D initial (realRun r start))
    (hc : ChunkCheck D start length initial final = true) :
    StateContains D final (realRun r (start + length)) := by
  change ((runFrom D start initial length).2 &&
    decide ((runFrom D start initial length).1 = final)) = true at hc
  have hs := and_true hc
  have he : (runFrom D start initial length).1 = final := of_decide_eq_true hs.2
  rw [← he]
  exact runFrom_sound hD r start length initial h hs.1

def ratLower (D : ℤ) (b : Box) : ℚ := (b.lo : ℚ) / (D : ℚ)
def ratUpper (D : ℤ) (b : Box) : ℚ := (b.hi : ℚ) / (D : ℚ)

theorem rational_enclosure {D : ℤ} {b : Box} {x : ℝ}
    (hD : 0 < D) (h : Contains D b x) :
    (ratLower D b : ℝ) ≤ x ∧ x ≤ (ratUpper D b : ℝ) := by
  have hd : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  constructor
  · change (((b.lo : ℚ) / (D : ℚ) : ℚ) : ℝ) ≤ x
    push_cast
    exact (div_le_iff₀ hd).2 (by simpa only [mul_comm] using h.1)
  · change x ≤ (((b.hi : ℚ) / (D : ℚ) : ℚ) : ℝ)
    push_cast
    exact (le_div_iff₀ hd).2 (by simpa only [mul_comm] using h.2)

/-- The final admission uses an actual analytic approximation theorem plus
    exact rational comparisons. Neither actual-zeta enclosure is assumed. -/
theorem bracket_of_approximation {G D : ℤ} {eb zb : Box} {eta z : ℝ}
    (hG : 0 < G) (hD : 0 < D) (factor tail : ℚ) (hf : 0 < factor)
    (he : Contains G eb eta)
    (ha : eta ≤ (factor : ℝ) * z ∧ (factor : ℝ) * z ≤ eta + (tail : ℝ))
    (hl : ratLower D zb ≤ ratLower G eb / factor)
    (hu : (ratUpper G eb + tail) / factor ≤ ratUpper D zb) :
    Contains D zb z := by
  have hfr : (0 : ℝ) < (factor : ℝ) := by exact_mod_cast hf
  have hdr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have heq := rational_enclosure hG he
  have hlr : (ratLower D zb : ℝ) ≤ (ratLower G eb : ℝ) / (factor : ℝ) := by
    exact_mod_cast hl
  have hur : ((ratUpper G eb : ℝ) + (tail : ℝ)) / (factor : ℝ) ≤
      (ratUpper D zb : ℝ) := by exact_mod_cast hu
  have low : (ratLower D zb : ℝ) ≤ z := by
    apply hlr.trans
    apply (div_le_iff₀ hfr).2
    simpa only [mul_comm] using heq.1.trans ha.1
  have high : z ≤ (ratUpper D zb : ℝ) := by
    apply le_trans _ hur
    apply (le_div_iff₀ hfr).2
    simpa only [mul_comm] using ha.2.trans (add_le_add_right heq.2 (tail : ℝ))
  constructor
  · change (((zb.lo : ℚ) / (D : ℚ) : ℚ) : ℝ) ≤ z at low
    push_cast at low
    simpa only [mul_comm] using (div_le_iff₀ hdr).1 low
  · change z ≤ (((zb.hi : ℚ) / (D : ℚ) : ℚ) : ℝ) at high
    push_cast at high
    simpa only [mul_comm] using (le_div_iff₀ hdr).1 high

end ZetaBetaHankel.Zeta357EtaArithmetic
