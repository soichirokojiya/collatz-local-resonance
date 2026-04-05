/-
  Local Resonance in Block-Compressed Collatz Dynamics
  Formalization of "Strong sketch" components

  Reference: Kojiya, S. (April 2026)
-/
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-! ## Lemma 6.1: Frozen irreversibility -/

theorem frozen_irreversibility (gap width : ℚ) (hgap : gap > 2 * width)
    (x y center : ℚ)
    (hx : |x - center| ≤ width) (hy : |y - center| ≤ width) :
    |x - y| < gap := by
  have h1 : x - center ≤ width := (abs_le.mp hx).2
  have h2 : -(x - center) ≤ width := by linarith [(abs_le.mp hx).1]
  have h3 : y - center ≤ width := (abs_le.mp hy).2
  have h4 : -(y - center) ≤ width := by linarith [(abs_le.mp hy).1]
  rw [abs_lt]
  constructor <;> linarith

theorem frozen_unique_in_window (gap width : ℚ) (hgap : gap > 2 * width)
    (x y center : ℚ)
    (hx : |x - center| ≤ width) (hy : |y - center| ≤ width)
    (hsep : |x - y| ≥ gap) : False := by
  linarith [frozen_irreversibility gap width hgap x y center hx hy]

/-! ## Lemma 6.2: Freezing monitor monotonicity -/

theorem freezing_monitor_mono (base coeff scale₁ scale₂ : ℚ)
    (hcoeff : 0 < coeff) (hscale : scale₂ ≤ scale₁) :
    base - coeff * scale₁ ≤ base - coeff * scale₂ := by
  nlinarith

theorem freezing_persists (base coeff scale₁ scale₂ : ℚ)
    (hcoeff : 0 < coeff) (hscale : scale₂ ≤ scale₁)
    (hpos : 0 < base - coeff * scale₁) :
    0 < base - coeff * scale₂ := by
  nlinarith [freezing_monitor_mono base coeff scale₁ scale₂ hcoeff hscale]

/-! ## Proposition 5.2: Deterministic tail principle -/

theorem deterministic_tail (width spacing : ℚ)
    (hlt : width < spacing) (x y center : ℚ)
    (hx : |x - center| ≤ width / 2) (hy : |y - center| ≤ width / 2)
    (hsep : |x - y| ≥ spacing) : False := by
  have h1 : x - center ≤ width / 2 := (abs_le.mp hx).2
  have h2 : -(x - center) ≤ width / 2 := by linarith [(abs_le.mp hx).1]
  have h3 : y - center ≤ width / 2 := (abs_le.mp hy).2
  have h4 : -(y - center) ≤ width / 2 := by linarith [(abs_le.mp hy).1]
  have h5 : |x - y| ≤ width := by rw [abs_le]; constructor <;> linarith
  linarith

/-! ## Corollary 7.4: Well-founded depletion of new block supply -/

abbrev BlockRank := Nat × Nat × Nat

theorem blockRank_wf : WellFounded
    (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) : BlockRank → BlockRank → Prop) :=
  WellFounded.prod_lex Nat.lt_wfRel.wf
    (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

theorem finite_descending_nat (f : Nat → Nat) (hf : ∀ n, f (n + 1) < f n) :
    ∃ k, f k = 0 := by
  by_contra h
  push_neg at h
  have : ∀ n, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => linarith [hf k]
  linarith [this (f 0 + 1)]

/-! ## Fixed-stage trichotomy (Proposition 6.5) -/

inductive FixedStageRegime where
  | frozen : FixedStageRegime
  | periodic : FixedStageRegime
  | degenerate : FixedStageRegime
  deriving Repr, DecidableEq

theorem fixed_stage_exhaustive (r : FixedStageRegime) :
    r = .frozen ∨ r = .periodic ∨ r = .degenerate := by
  cases r <;> simp
